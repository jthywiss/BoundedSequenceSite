//
// BoundedSequence.scala -- Scala object BoundedSequence, class BoundedSequenceInstance, and object BoundedSequenceType
// Project OrcScala
//
// $Id$
//
// Copyright (c) 2015 The University of Texas at Austin. All rights reserved.
//
// Use and redistribution of this file is governed by the license terms in
// the LICENSE file found in the project's top-level directory and also found at
// URL: http://orc.csres.utexas.edu/license.shtml .
//
package orc.lib.state

import orc.Handle
import orc.error.runtime.{ ArgumentTypeMismatchException, NoSuchMemberException }
import orc.types.{ BooleanType, FunctionType, Invariant, NumberType, RecordType, SignalType, SimpleFunctionType, SimpleTypeConstructor, Top, TupleType, Type, TypeVariable }
import orc.values.{ Field, OrcTuple, Signal }
import orc.values.sites.{ Site0, Site1, TotalSite0, TotalSite1, TypedSite }

/** Orc constructor site for the BoundedSequence class
  *
  * @author jthywiss
  */
object BoundedSequence extends TotalSite1 with TypedSite {
//  {
//    Logger.julLogger.setLevel(java.util.logging.Level.ALL)
//    val ch = new java.util.logging.ConsoleHandler()
//    ch.setLevel(java.util.logging.Level.ALL)
//    ch.setFormatter(new orc.SyslogishFormatter())
//    Logger.julLogger.addHandler(ch)
//  }

  def eval(arg: AnyRef): AnyRef = {
    arg match {
      case size: BigInt => {
        if (!size.isValidInt) throw new IllegalArgumentException(s"BoundedSequence maximum size is ${Int.MaxValue}")
        new BoundedSequenceInstance(size.intValue())
      }
      case _ => throw new ArgumentTypeMismatchException(0, "Integer", arg.getClass().toString())
    }
  }

  def orcType = BoundedSequenceType.getBuilder

}

/** An instance of the BoundedSequence Orc class
  *
  * @author jthywiss
  */
class BoundedSequenceInstance(val size: Int) extends TotalSite1 {
  val store = new Array[AnyRef](size)
  var trailingReadIndex = 0
  var nextWriteIndex = 0
  var available = size
  var closed = false
  val blockedWrites = new scala.collection.mutable.Queue[(AnyRef, Handle)]
  val blockedReads = new scala.collection.mutable.Queue[(ReadPoint, Handle)]
  val blockedCloses = new scala.collection.mutable.Queue[Handle]
  val openReadPoints = new scala.collection.mutable.HashSet[ReadPoint]

  {
    Logger.entering(getClass.getName, "<init>", Seq(new Integer(size)))
    require(size > 0, s"BoundedSequence size must be positive: $size")
  }

  override def toString() = getClass().getName() + "@" + Integer.toHexString(hashCode()) + s"(size=$size, $trailingReadIndex=$trailingReadIndex, $nextWriteIndex=$nextWriteIndex, available=$available, closed=$closed, blockedWrites.size=${blockedWrites.size}, blockedReads.size=${blockedReads.size}, blockedCloses.size=${blockedCloses.size}, openReadPoints.size=${openReadPoints.size})"

  def assertClassInvariants() = try {
    assert(nextWriteIndex >= 0 && nextWriteIndex < size, s"nextWrite out of range: $nextWriteIndex")
    assert(trailingReadIndex >= 0 && trailingReadIndex < size, s"trailingRead out of range: $trailingReadIndex")
    assert(openReadPoints.isEmpty || trailingReadIndex == openReadPoints.map(_.readIndex).min, s"trailingReadIndex=$trailingReadIndex, but min readIndex=${openReadPoints.map(_.readIndex).min}")
    assert(available >= 0 && available <= size, s"available out of range: $available")
    assert((nextWriteIndex + available) % size == trailingReadIndex, s"(nextWrite + available) % size == trailingRead: ($nextWriteIndex + $available) % $size == $trailingReadIndex")
    assert(blockedWrites.isEmpty || available == 0, s"blocked writes, but $available available slots: ${blockedWrites.map(_._2)}")
    assert(blockedReads.isEmpty || blockedReads.forall(p => p._1.readIndex == nextWriteIndex), s"${blockedReads.size} blocked reads, but not all waiting for nextWrite $nextWriteIndex: ${blockedReads}")
    assert(blockedCloses.isEmpty || closed, s"${blockedCloses.size} blocked closes, but not closed")
    assert(blockedCloses.isEmpty || available != size || blockedReads.nonEmpty, s"${blockedCloses.size} blocked closes, but no data remains unread")
  } catch {
    case e: AssertionError => {
      dumpState()
      throw e
    }
  }

  def dumpState(): AnyRef = synchronized {
    Logger.finest("BoundedSequenceInstance state dump: " + this.toString())
    blockedWrites map { e => Logger.finest("Blocked write: " + e.toString()) }
    blockedReads map { e => Logger.finest("Blocked read: " + e.toString()) }
    blockedCloses map { e => Logger.finest("Blocked close: " + e.toString()) }
    openReadPoints map { e => Logger.finest("Open read point: " + e.toString()) }
    Signal
  }

  class ReadPoint(private[BoundedSequenceInstance] val readIndex: Int) extends TotalSite1 {
    var closed = false

    BoundedSequenceInstance.this synchronized {
      Logger.entering(getClass.getName, "<init>", Seq(new Integer(readIndex)))
      require(readIndex >= 0 && readIndex < size, s"ReadPoint readIndex must be ≥ 0 and < size: $readIndex")
      openReadPoints += this

      /* Can't assertClassInvariants() here, because ReadPoints are
       * constructed by other methods when invariants may not hold. */
    }

    override def toString() = getClass().getName() + "@" + Integer.toHexString(hashCode()) + s"(readIndex=$readIndex, closed=$closed)"

    def assertClassInvariants() = try {
      BoundedSequenceInstance.this.assertClassInvariants()
      assert(closed || (trailingReadIndex <= readIndex && readIndex <= nextWriteIndex) || (nextWriteIndex <= trailingReadIndex && trailingReadIndex <= readIndex) || (readIndex <= nextWriteIndex && nextWriteIndex <= trailingReadIndex), s"Indicies out of order: trailingRead=$trailingReadIndex, readIndex=$readIndex, nextWrite=$nextWriteIndex (available=$available)")
    } catch {
      case e: AssertionError => {
        Logger.finest("ReadPoint state dump: " + this.toString())
        dumpState()
        throw e
      }
    }

    protected[BoundedSequenceInstance] def notifyAppend(reader: Handle): Unit = BoundedSequenceInstance.this synchronized {
      doRead(reader)
    }

    protected def doRead(reader: Handle): Unit = BoundedSequenceInstance.this synchronized {
      Logger.entering(getClass.getName, "doRead", Seq(reader))
      assert((trailingReadIndex <= readIndex && readIndex <= nextWriteIndex) || (nextWriteIndex <= trailingReadIndex && trailingReadIndex <= readIndex) || (readIndex <= nextWriteIndex && nextWriteIndex <= trailingReadIndex), s"Indicies out of order: trailingRead=$trailingReadIndex, readIndex=$readIndex, nextWrite=$nextWriteIndex (available=$available)")
      val readElement = store(readIndex)
      val newReadIndex = (readIndex + 1) % size
      reader.publish(OrcTuple(List(readElement, new ReadPoint(newReadIndex))))
      Logger.exiting(getClass.getName, "doRead")
    }

    def read(reader: Handle): Unit = BoundedSequenceInstance.this synchronized {
      Logger.entering(getClass.getName, "read", Seq(reader))
      Logger.finest(s"BoundedSequenceInstance.this.hashCode() = ${BoundedSequenceInstance.this.hashCode()}")
      assertClassInvariants()
      if (closed) { reader.halt; Logger.exiting(getClass.getName, "read"); return }
      if (readIndex == nextWriteIndex) {
        // At current end of sequence, so block this read
        Logger.finest(s"Blocking read by $reader until data available")
        reader.setQuiescent()
        blockedReads += ((this, reader))
        Logger.exiting(getClass.getName, "read")
        assertClassInvariants()
        return
      }
      doRead(reader)
      assertClassInvariants()
      Logger.exiting(getClass.getName, "read")
    }

    def readD(reader: Handle): Unit = BoundedSequenceInstance.this synchronized {
      Logger.entering(getClass.getName, "readD", Seq(reader))
      assertClassInvariants()
      if (closed) { reader.halt; Logger.exiting(getClass.getName, "readD"); return }
      // If at current end of sequence, halt silently
      if (readIndex == nextWriteIndex) { reader.halt; Logger.exiting(getClass.getName, "readD"); return }
      doRead(reader)
      assertClassInvariants()
      Logger.exiting(getClass.getName, "readD")
    }

    def close() = BoundedSequenceInstance.this synchronized {
      Logger.entering(getClass.getName, "close")
      assertClassInvariants()
      closed = true
      val ourBlockedReads = blockedReads.dequeueAll(_._1 == this)
      Logger.finest(s"Halting ${ourBlockedReads.size} blocked reads: ${ourBlockedReads}")
      ourBlockedReads.map(_._2.halt)
      openReadPoints -= this
      if (readIndex == trailingReadIndex) {
        cleanUpTrailing()
      }
      assertClassInvariants()
      Logger.exiting(getClass.getName, "close")
    }

    override def eval(arg: AnyRef) = {
      dumpState()
      arg match {
        case Field(name) =>
          entries.get(name) match {
            case Some(v) => v
            case None => throw new NoSuchMemberException(this, name)
          }
        case _ => throw new ArgumentTypeMismatchException(0, "Field", if (arg != null) arg.getClass().toString() else "null")
      }
    }

    val entries = Map(
      "read" -> new Site0 { override def call(h: Handle) = read(h) },
      "readD" -> new Site0 { override def call(h: Handle) = readD(h) },
      "close" -> new TotalSite0 { override def eval() = BoundedSequenceInstance.this synchronized { close; Signal } },
      "isClosed" -> new TotalSite0 { override def eval() = BoundedSequenceInstance.this synchronized { new java.lang.Boolean(closed) } })

    Logger.exiting(getClass.getName, "<init>")
  }

  protected def notifyAvailable(newElement: AnyRef, writer: Handle): Unit = synchronized {
    doWrite(newElement, writer)
  }

  protected def doWrite(newElement: AnyRef, writer: Handle): Unit = synchronized {
    Logger.entering(getClass.getName, "doWrite", Seq(newElement, writer))
    assert(available > 0)
    store(nextWriteIndex) = newElement
    nextWriteIndex = (nextWriteIndex + 1) % size
    available -= 1
    writer.publish()
    Logger.finest(s"Notifying ${blockedReads.size} blocked reads; New nextWrite=$nextWriteIndex: ${blockedReads}")
    blockedReads.dequeueAll(_ => true).map(p => p._1.notifyAppend(p._2))
    Logger.exiting(getClass.getName, "doWrite")
  }

  def append(newElement: AnyRef, writer: Handle): Unit = synchronized {
    Logger.entering(getClass.getName, "append", Seq(newElement, writer))
    assertClassInvariants()
    if (closed) { writer.halt; Logger.exiting(getClass.getName, "append"); return }
    if (available == 0) {
      Logger.finest(s"Blocking append by $writer until space available")
      writer.setQuiescent()
      blockedWrites += ((newElement, writer))
      assertClassInvariants()
      return
    }
    doWrite(newElement, writer)
    assertClassInvariants()
    Logger.exiting(getClass.getName, "append")
  }

  def appendD(newElement: AnyRef, writer: Handle): Unit = synchronized {
    Logger.entering(getClass.getName, "appendD", Seq(newElement, writer))
    assertClassInvariants()
    if (closed) { writer.halt; Logger.exiting(getClass.getName, "appendD"); return }
    if (available == 0) { writer.halt; Logger.exiting(getClass.getName, "appendD"); return }
    doWrite(newElement, writer)
    assertClassInvariants()
    Logger.exiting(getClass.getName, "appendD")
  }

  def newReadPoint(reader: Handle): Unit = synchronized {
    Logger.entering(getClass.getName, "newReadPoint", Seq(reader))
    assertClassInvariants()
    if (closed) { reader.halt; Logger.exiting(getClass.getName, "newReadPoint"); return }
    reader.publish(new ReadPoint(trailingReadIndex))
    assertClassInvariants()
    Logger.exiting(getClass.getName, "newReadPoint")
  }

  protected def cleanUpTrailing() {
    while (trailingReadIndex != nextWriteIndex && openReadPoints.forall(_.readIndex != trailingReadIndex)) {
      Logger.finest(s"No more readers at $trailingReadIndex, advancing.  State: $this")
      store(trailingReadIndex) = null
      trailingReadIndex = (trailingReadIndex + 1) % size
      available += 1
      if (blockedWrites.nonEmpty) {
        val nextWriter = blockedWrites.dequeue()
        Logger.finest(s"Notifying next blocked writer: $nextWriter")
        notifyAvailable(nextWriter._1, nextWriter._2)
      }
    }
  }

  def close(closer: Handle): Unit = synchronized {
    Logger.entering(getClass.getName, "close", Seq(closer))
    assertClassInvariants()
    closed = true
    blockedWrites.dequeueAll(_ => true).map(_._2.halt)
    openReadPoints map { rp => if (rp.readIndex == nextWriteIndex) rp.close() }
    if (available == size) {
      closer.publish()
      cleanUpAtClose()
    } else {
      Logger.finest(s"Blocking close by $closer until all readers finished")
      blockedCloses += closer
    }
    assertClassInvariants()
    Logger.exiting(getClass.getName, "close")
  }

  protected def notifyReaderAtEnd() {
    if (openReadPoints.forall(_.closed)) {
      Logger.finest("Readers all finished; BoundedSequence.close() call publishing")
      blockedCloses.dequeueAll(_ => true).map(_.publish())
      cleanUpAtClose()
    }
  }

  def closeD(closer: Handle): Unit = synchronized {
    Logger.entering(getClass.getName, "closeD", Seq(closer))
    assertClassInvariants()
    closed = true
    blockedWrites.dequeueAll(_ => true).map(_._2.halt)
    openReadPoints map { rp => if (rp.readIndex == nextWriteIndex) rp.close() }
    closer.publish()
    assertClassInvariants()
  }

  def cleanUpAtClose() {
    assert(closed)
    for {
      i <- store.indices
    } store(i) = null
    assert(blockedReads.isEmpty)
    assert(blockedWrites.isEmpty)
    assert(blockedCloses.isEmpty)
    assert(openReadPoints.isEmpty)
  }

  override def eval(arg: AnyRef) = {
    dumpState()
    arg match {
      case Field(name) =>
        entries.get(name) match {
          case Some(v) => v
          case None => throw new NoSuchMemberException(this, name)
        }
      case _ => throw new ArgumentTypeMismatchException(0, "Field", if (arg != null) arg.getClass().toString() else "null")
    }
  }

  val entries = Map(
    "dumpState" -> new TotalSite0 { override def eval() = dumpState() },
    "append" -> new Site1 { override def call(a: AnyRef, h: Handle) = append(a, h) },
    "appendD" -> new Site1 { override def call(a: AnyRef, h: Handle) = appendD(a, h) },
    "ReadPoint" -> new Site0 { override def call(h: Handle) = newReadPoint(h) },
    "getSize" -> new TotalSite0 { override def eval() = synchronized { BigInt(size) } },
    "close" -> new Site0 { override def call(h: Handle) = close(h) },
    "closeD" -> new Site0 { override def call(h: Handle) = closeD(h) },
    "isClosed" -> new TotalSite0 { override def eval() = synchronized { new java.lang.Boolean(closed) } })

  Logger.exiting(getClass.getName, "<init>")
}

/** Orc type constructor for the BoundedSequence Orc class
  *
  * @author jthywiss
  */
object BoundedSequenceType extends SimpleTypeConstructor("BoundedSequence", Invariant) {

  def getBuilder: Type = {
    val E = new TypeVariable()
    FunctionType(List(E), Nil, this(E))
  }

  override def instance(ts: List[Type]) = {
    val List(e) = ts
    new RecordType(
      "append" -> SimpleFunctionType(e, SignalType),
      "appendD" -> SimpleFunctionType(e, SignalType),
      "ReadPoint" -> new RecordType(
        "read" -> SimpleFunctionType(TupleType(List(e, /*ReadPoint*/ Top))),
        "readD" -> SimpleFunctionType(TupleType(List(e, /*ReadPoint*/ Top))),
        "close" -> SimpleFunctionType(SignalType),
        "isClosed" -> SimpleFunctionType(BooleanType)),
      "getSize" -> SimpleFunctionType(NumberType),
      "close" -> SimpleFunctionType(SignalType),
      "closeD" -> SimpleFunctionType(SignalType),
      "isClosed" -> SimpleFunctionType(BooleanType))
  }

}
