--------------------------- MODULE RaceBuffer ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
  BufCapacity, (* Capacity of backing storage *)
  (* Wrapping modulus for sequence numbers - once sequence numbers reach this number, they wrap to 0. 
     Usually, this would be the closest multiple of BufCapacity to the integer maximum, but it can 
     be lowered for testing. *)
  SeqNMod, 
  TotalNumWrites  (* Number of writes to execute *)

ASSUME BufCapacity \in (Nat \ 0..2) (* Buffer capacity is at least 3 *)
ASSUME SeqNMod % BufCapacity = 0 (* Sequence number modulus must be a multiple of buffer capacity *)
ASSUME SeqNMod >= BufCapacity * 2 (* Sequence number modulus must be at least twice buffer capacity *)

-----------------------------------------------------------------------------

VARIABLES 
  wpc, (* Writer's program counter *)
  buf, (* Backing storage *)
  writeSeqN, (* Write sequence number - Sequence number of next written entry *)
  overwriteSeqN, (* Overwrite sequence number - Sequence number of next entry to be overwritten *)
  numWrites, (* Total number of writes that have occurred *)

  rpc, (* Reader's program counter *)
  rbuf, (* Buffer of entries already read *)
  bufSnap, (* Intermediate buffer used to store a snapshot of entries being read *)
  readSeqN, (* Read sequence number - Points to next read position *)
  overwriteSeqNSnap, (* Value of overwrite sequence number observed at beginning of/right after read *)
  writeSeqNSnap, (* Value of write sequence number observed at beginning of/right after read *)
  storedPrefix, (* Prefix to be written to read buffer once suffix is read *)
  processingIndex (* Index of next entry in bufSnap to process *)

-----------------------------------------------------------------------------

(* Construct an entry structure - Index field is only used to check *)
(* ordering in the reader's output buffer *)
Entry(sn, t) == [seqn |-> sn, type |-> t]

(* Get index in backing storage based on given sequence number *)
BufIndex(seqn) == seqn % BufCapacity

(* Add increment to sequence number, looping at the sequence number modulus.
   The increment will always be less than the modulus. *)
SeqNAdd(seqn, incr) == 
  IF SeqNMod - seqn > incr
  THEN seqn + incr
  ELSE incr - (SeqNMod - seqn)

(* Subtract decr to sequence number, looping at the sequence number modulus.
   The decrement will always be less than the modulus. *)
SeqNSub(seqn, decr) == 
  IF seqn >= decr
  THEN seqn - decr
  ELSE SeqNMod - (decr - seqn)

-----------------------------------------------------------------------------

(* Writer helpers *)

(* Get entry in storage position of given sequence number *)
Read(i) == buf[BufIndex(i)]

(* Write a single entry of given type at given index *)
Write(i, t) == buf' = (BufIndex(i) :> Entry(i,t)) @@ buf

(* Either write a single entry or the prefix of a double entry *)
WriteNewEntry(i) == 
  \/ Write(i, "SINGLE")
  \/ Write(i, "PREFIX")

(* Write the appropriately typed entry at the given index *)
WriteEntry(i) == 
  IF i = 0 
  THEN WriteNewEntry(i) 
  ELSE IF Read(i - 1).type = "PREFIX"
       THEN Write(i, "SUFFIX")
       ELSE WriteNewEntry(i)

(* Overwrite old entry by incrementing overwrite sequence number *)
OverwriteOldEntry == 
    IF Read(overwriteSeqN).type = "PREFIX" 
    THEN overwriteSeqN' = SeqNAdd(overwriteSeqN, 2)
    ELSE overwriteSeqN' = SeqNAdd(overwriteSeqN, 1)

-----------------------------------------------------------------------------

(* Writer steps *)

(* If the write sequence number has looped around the buffer to reach the overwrite sequence number (mod buffer capacity), 
   then another entry must be overwritten to allocate space for more writes *)
Overwrite == 
    /\ wpc = "overwrite"
    /\ IF writeSeqN = SeqNAdd(overwriteSeqN, BufCapacity)
       THEN OverwriteOldEntry
       ELSE UNCHANGED overwriteSeqN
    /\ wpc' = "writeStep"
    /\ UNCHANGED writeSeqN
    /\ UNCHANGED buf
    /\ UNCHANGED numWrites

(* Write a single entry or half of a double entry *)
WriteStep == 
  /\ wpc = "writeStep"
  /\ WriteEntry(numWrites)
  /\ wpc' = "incrWriteSeqN"
  /\ UNCHANGED writeSeqN
  /\ UNCHANGED overwriteSeqN
  /\ numWrites' = numWrites + 1

(* Increment the write sequence number by 1 *)
IncrWriteSeqN ==
  /\ wpc = "incrWriteSeqN"
  /\ writeSeqN' = SeqNAdd(writeSeqN, 1)
  /\ wpc'= "overwrite"
  /\ UNCHANGED overwriteSeqN
  /\ UNCHANGED buf
  /\ UNCHANGED numWrites


-----------------------------------------------------------------------------

(* Writer *)

WriterInit == 
  /\ wpc = "overwrite"
  /\ writeSeqN = 0
  /\ overwriteSeqN = 0
  /\ buf = <<>>
  /\ numWrites = 0

(* Wait when reader takes steps *)
WriterWait ==
  /\ UNCHANGED wpc
  /\ UNCHANGED writeSeqN
  /\ UNCHANGED buf
  /\ UNCHANGED overwriteSeqN
  /\ UNCHANGED numWrites

(* Take appropriate step based on wpc *)
WriterStep ==
  \/ Overwrite
  \/ WriteStep
  \/ IncrWriteSeqN

-----------------------------------------------------------------------------

(* Reader helpers *)

(* Return number of keys in a function *)
Size(f) == Cardinality(DOMAIN f)

(* Calculate the sequence number value of the first item read during this read *)
FirstRead(rc, snapLen) == SeqNSub(rc, snapLen)

(* Return number of entries past rc overwritten based on given owc *)
NMissed(rsn, owsn, wsn) == 
  IF owsn <= wsn /\ wsn < rsn
  THEN owsn + (SeqNMod - rsn)
  ELSE IF rsn < owsn /\ (owsn < wsn \/ wsn < rsn)
       THEN owsn - rsn
       ELSE 0

(* Return number of entries past first read overwritten (Maximum is snap buffer size) *)
NMissedDuringRead(rsn, owsn, wsn, snapLen) == 
  IF NMissed(FirstRead(rsn, snapLen), owsn, wsn) <= snapLen 
  THEN NMissed(FirstRead(rsn, snapLen), owsn, wsn)
  ELSE snapLen

(* Append given entry to reader's buffer *)
AppendEntry(rb, entry) == 
  rb @@ (Size(rb) :> entry)

(* Append n missed entries to read buffer *)
RECURSIVE AppendMissed(_,_)
AppendMissed(rb, n) == 
  IF n = 0 THEN rb ELSE AppendMissed(AppendEntry(rb, Entry(0, "MISSED")), n-1)

-----------------------------------------------------------------------------

(* Reader Steps*)
  
(* At the start of a read, reader takes a snapshot of the overwrite sequence number *)
SnapOverwriteSeqN == 
  /\ rpc = "snapOverwriteSeqN"
  /\ overwriteSeqNSnap' = overwriteSeqN
  /\ UNCHANGED writeSeqNSnap
  /\ UNCHANGED rbuf
  /\ UNCHANGED readSeqN
  /\ rpc' = "snapWriteSeqN"
  /\ bufSnap' = <<>>
  /\ UNCHANGED storedPrefix
  /\ UNCHANGED processingIndex

(* Observe the current value of the write sequence number, and based on that value,
   append any missed entries to reader's buffer and update reader's sequence number *)
SnapWriteSeqN ==
  /\ rpc = "snapWriteSeqN"
  /\ UNCHANGED overwriteSeqNSnap
  /\ writeSeqNSnap' = writeSeqN
  /\ IF NMissed(readSeqN, overwriteSeqNSnap, writeSeqN) > 0 /\ ~(storedPrefix.type = "NONE")
     THEN /\ rbuf' = AppendMissed(rbuf, NMissed(readSeqN, overwriteSeqNSnap, writeSeqN) + 1)
          /\ storedPrefix' = Entry(0, "NONE")
     ELSE /\ rbuf' = AppendMissed(rbuf, NMissed(readSeqN, overwriteSeqNSnap, writeSeqN))
          /\ UNCHANGED storedPrefix
  /\ readSeqN' = SeqNAdd(readSeqN, NMissed(readSeqN, overwriteSeqNSnap, writeSeqN))
  /\ rpc' = "snapEntry"
  /\ bufSnap' = <<>>
  /\ UNCHANGED processingIndex

(* Take a snapshot of a single entry, then move on to next entry until read sequence number reaches
   write sequence number *)
SnapEntry == 
  /\ rpc = "snapEntry"
  /\ IF readSeqN = writeSeqNSnap
     THEN /\ rpc' = "snapOverwriteSeqNAfter"
          /\ UNCHANGED bufSnap
          /\ UNCHANGED readSeqN
     ELSE /\ UNCHANGED rpc
          /\ bufSnap' = (Size(bufSnap) :> Read(readSeqN)) @@ bufSnap
          /\ readSeqN' = SeqNAdd(readSeqN, 1)
  /\ UNCHANGED overwriteSeqNSnap
  /\ UNCHANGED writeSeqNSnap
  /\ UNCHANGED rbuf
  /\ UNCHANGED processingIndex
  /\ UNCHANGED storedPrefix

(* Immediately after a read, reader takes a snapshot of the overwrite sequence number *)
SnapOverwriteSeqNAfter == 
  /\ rpc = "snapOverwriteSeqNAfter"
  /\ overwriteSeqNSnap' = overwriteSeqN
  /\ UNCHANGED rbuf
  /\ UNCHANGED readSeqN
  /\ rpc' = "processOverwritten"
  /\ UNCHANGED bufSnap
  /\ UNCHANGED storedPrefix
  /\ UNCHANGED processingIndex
  /\ UNCHANGED writeSeqNSnap

(* Calculate how entries from previous read might have been overwritten based
   on snapshots of write and overwrite sequence numbers. Append that many missed values to the
   reader's buffer, potentially replacing a stored prefix with a missed value *)
ProcessOverwritten == 
  /\ rpc = "processOverwritten"
  /\ rpc' = "processEntry"
  /\ processingIndex' = NMissedDuringRead(readSeqN, overwriteSeqNSnap, writeSeqN, Size(bufSnap))
  /\ IF /\ ~(storedPrefix.type = "NONE") 
        /\ NMissedDuringRead(readSeqN, overwriteSeqNSnap, writeSeqN, Size(bufSnap)) > 0
     THEN /\ rbuf' = AppendMissed(
                       rbuf, 
                       NMissedDuringRead(readSeqN, overwriteSeqNSnap, writeSeqN, Size(bufSnap)) + 1
                     )
          /\ storedPrefix' = Entry(0, "NONE")
     ELSE /\ rbuf' = AppendMissed(
                       rbuf, 
                       NMissedDuringRead(readSeqN, overwriteSeqNSnap, writeSeqN, Size(bufSnap))
                     )
          /\ UNCHANGED storedPrefix
  /\ UNCHANGED bufSnap
  /\ UNCHANGED readSeqN
  /\ UNCHANGED overwriteSeqNSnap
  /\ UNCHANGED writeSeqNSnap
  
(* Process a single entry in the buffer snapshot by either storing it in the reader's 
   buffer or as a stored prefix *)
ProcessEntry == 
  /\ rpc = "processEntry"
  /\ IF processingIndex = Size(bufSnap)
     THEN /\ rpc' = "snapOverwriteSeqN"
          /\ UNCHANGED processingIndex
          /\ UNCHANGED rbuf
          /\ UNCHANGED storedPrefix
     ELSE /\ UNCHANGED rpc
          /\ processingIndex' = processingIndex + 1
          /\ IF storedPrefix.type = "NONE"
             THEN IF ~(bufSnap[processingIndex].type = "SINGLE")
                  THEN /\ storedPrefix' = bufSnap[processingIndex]
                       /\ UNCHANGED rbuf
                  ELSE /\ rbuf' = AppendEntry(rbuf, bufSnap[processingIndex])
                       /\ UNCHANGED storedPrefix
             ELSE /\ rbuf' = AppendEntry(AppendEntry(rbuf, storedPrefix), bufSnap[processingIndex])
                  /\ storedPrefix' = Entry(0, "NONE")
  /\ UNCHANGED bufSnap
  /\ UNCHANGED readSeqN
  /\ UNCHANGED overwriteSeqNSnap
  /\ UNCHANGED writeSeqNSnap

-----------------------------------------------------------------------------

(* Reader *)

ReaderInit ==
  /\ rpc = "snapWriteSeqN"
  /\ rbuf = <<>>
  /\ bufSnap = <<>>
  /\ readSeqN = 0
  /\ overwriteSeqNSnap = 0
  /\ writeSeqNSnap = 0 
  /\ storedPrefix = Entry(0, "NONE")
  /\ processingIndex = 0

(* Wait when writer takes a step *)
ReaderWait ==
  /\ UNCHANGED rpc
  /\ UNCHANGED rbuf
  /\ UNCHANGED bufSnap
  /\ UNCHANGED readSeqN
  /\ UNCHANGED overwriteSeqNSnap
  /\ UNCHANGED writeSeqNSnap
  /\ UNCHANGED storedPrefix
  /\ UNCHANGED processingIndex

(* Take appropriate step based on rpc *)
ReaderStep == 
  \/ SnapWriteSeqN
  \/ SnapOverwriteSeqN
  \/ SnapEntry
  \/ SnapOverwriteSeqNAfter
  \/ ProcessOverwritten
  \/ ProcessEntry  

-----------------------------------------------------------------------------

Init == 
  /\ ReaderInit
  /\ WriterInit

(* Either take reader step or writer step. Stop writer after writeSeqN reaches numWrites *)
Next ==
  \/ (WriterWait /\ ReaderStep) 
  \/ /\ ReaderWait 
     /\ WriterStep 
     /\ numWrites < TotalNumWrites 
     /\ numWrites - Size(rbuf) < SeqNMod - 1
     /\ ~(SeqNAdd(writeSeqN, 1) = overwriteSeqNSnap)

-----------------------------------------------------------------------------

(* Invariants *)

(* Since suffixes could possibly be interpreted as prefixes, ensure that suffixes
   are stored as a prefix *)
InvStoredPrefixNotSuffix == 
  storedPrefix.type = "NONE" \/ storedPrefix.type = "PREFIX"

(* The overwrite sequence number is incremented by 2 when overwriting a double entry.
   Therefore, it should never point to a suffix. *)
InvOverwriteSeqNNotOnSuffix ==
    IF overwriteSeqN > BufCapacity 
    THEN ~(Read(overwriteSeqN).type = "SUFFIX")
    ELSE TRUE

(* Check that every non-nil entry is at the correct index in the read buffer *)
InvCorrectIndices == 
  IF Size(rbuf) > 0 
  THEN \A i \in 0..(Size(rbuf)-1): rbuf[i].seqn = i \/ rbuf[i].type = "MISSED"
  ELSE TRUE

(* Check that every prefix has a suffix and vice versa *)
InvConsistentDoubles == 
  CASE Size(rbuf) = 0 -> TRUE
  [] Size(rbuf) = 1 -> ~(rbuf[0].type = "SUFFIX" \/ rbuf[Size(rbuf)-1].type = "PREFIX")
  [] Size(rbuf) >= 2 -> 
    /\ ~(rbuf[0].type = "SUFFIX" \/ rbuf[Size(rbuf)-1].type = "PREFIX")
    /\ \A i \in 0..(Size(rbuf)-2): 
          rbuf[i].type = "PREFIX" <=> rbuf[i+1].type = "SUFFIX"

=============================================================================