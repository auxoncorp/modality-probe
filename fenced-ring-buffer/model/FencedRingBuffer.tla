--------------------------- MODULE FencedRingBuffer ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
  BufCapacity, (* Capacity of backing storage *)
  NumWrites  (* Number of writes to execute *)

ASSUME Assumption == BufCapacity \in (Nat \ 0..2) (* Buffer capacity is at least 3 *)

-----------------------------------------------------------------------------

VARIABLES 
  wpc, (* Writer's program counter *)
  buf, (* Backing storage *)
  writeSeqN, (* Write sequence number - Points to next write position *)
  overwriteSeqN, (* Overwrite sequence number - Marks where space is allocated for the writer to write freely *)

  rpc, (* Reader's program counter *)
  rbuf, (* Buffer of entries already read *)
  bufSnap, (* Intermediate buffer used to store a snapshot of entries being read *)
  readSeqN, (* Read sequence number - Points to next read position *)
  writeSeqNSnap, (* Value of write sequence number observed at beginning of read *)
  storedPrefix, (* Prefix to be written to read buffer once suffix is read *)
  processingIndex (* Index of next entry in bufSnap to process *)

-----------------------------------------------------------------------------

(* Writer helpers *)

(* Construct an entry structure - Index field is only used to check *)
(* ordering in the reader's output buffer *)
Entry(i, t) == [index |-> i, type |-> t]

(* Get index in backing storage based on given sequence number *)
BufIndex(i) == i % BufCapacity

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
    IF overwriteSeqN < BufCapacity 
    THEN overwriteSeqN' = overwriteSeqN + 1
    ELSE IF Read(overwriteSeqN).type = "PREFIX" 
         THEN overwriteSeqN' = overwriteSeqN + 2
         ELSE overwriteSeqN' = overwriteSeqN + 1

-----------------------------------------------------------------------------

(* Writer steps *)

(* If the write sequence number has reached the overwrite sequence number, then another entry 
   must be overwritten to allocate space for more writes *)
Overwrite == 
    /\ wpc = "overwrite"
    /\ IF writeSeqN = overwriteSeqN 
       THEN OverwriteOldEntry
       ELSE UNCHANGED overwriteSeqN
    /\ wpc' = "write"
    /\ UNCHANGED writeSeqN
    /\ UNCHANGED buf

(* Writer either writes nil entry at writeSeqN or transitions to OverwriteSuf in
   the case that a double entry is being overwritten *)
WriteStep == 
  /\ wpc = "write"
  /\ WriteEntry(writeSeqN)
  /\ wpc' = "incrWriteSeqN"
  /\ UNCHANGED writeSeqN
  /\ UNCHANGED overwriteSeqN

(* Increment the write sequence number by 1 *)
IncrWriteSeqN ==
  /\ wpc = "incrWriteSeqN"
  /\ writeSeqN' = writeSeqN + 1
  /\ wpc'= "overwrite"
  /\ UNCHANGED overwriteSeqN
  /\ UNCHANGED buf

-----------------------------------------------------------------------------

(* Writer *)

WriterInit == 
  /\ wpc = "overwrite"
  /\ writeSeqN = 0
  /\ overwriteSeqN = 0
  /\ buf = <<>>

(* Wait when reader takes steps *)
WriterWait ==
  /\ UNCHANGED wpc
  /\ UNCHANGED writeSeqN
  /\ UNCHANGED buf
  /\ UNCHANGED overwriteSeqN

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
FirstRead(rc, snapLen) == rc - snapLen

(* Return number of entries past rc overwritten based on given owc *)
NMissed(owc, rc) == IF owc < (rc + BufCapacity) THEN 0 ELSE owc - (rc + BufCapacity)

(* Return number of entries past first read overwritten (Maximum is snap buffer size) *)
NMissedDuringRead(owc, rc, snapLen) == IF NMissed(owc, FirstRead(rc, snapLen)) <= snapLen 
                                 THEN NMissed(owc, FirstRead(rc, snapLen)) 
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
  
(* Observe the current value of the overwrite sequence number, and based on that value,
   append any missed entries to reader's buffer and update reader's sequence number *)
SnapOverwriteSeqN ==
  /\ rpc = "snapOverwriteSeqN"
  /\ UNCHANGED writeSeqNSnap
  /\ IF NMissed(overwriteSeqN, readSeqN) > 0 /\ ~(storedPrefix.type = "NONE")
     THEN /\ rbuf' = AppendMissed(rbuf, NMissed(overwriteSeqN, readSeqN) + 1)
          /\ storedPrefix' = Entry(0, "NONE")
     ELSE /\ rbuf' = AppendMissed(rbuf, NMissed(overwriteSeqN, readSeqN))
          /\ UNCHANGED storedPrefix
  /\ readSeqN' = readSeqN + NMissed(overwriteSeqN, readSeqN)
  /\ rpc' = "snapWriteSeqN"
  /\ bufSnap' = <<>>
  /\ UNCHANGED processingIndex

(* At the start of a read, reader takes a snapshot of the write sequence number and appends
   nil entries to the read buffer if any entries were missed between reads *)
SnapWriteSeqN == 
  /\ rpc = "snapWriteSeqN"
  /\ writeSeqNSnap' = writeSeqN
  /\ UNCHANGED rbuf
  /\ UNCHANGED readSeqN
  /\ rpc' = "snapEntry"
  /\ bufSnap' = <<>>
  /\ UNCHANGED storedPrefix
  /\ UNCHANGED processingIndex

(* Take a snapshot of a single entry, then move on to next entry until read sequence number reaches
   write sequence number *)
SnapEntry == 
  /\ rpc = "snapEntry"
  /\ IF readSeqN >= writeSeqNSnap
     THEN /\ rpc' = "processOverwritten"
          /\ UNCHANGED bufSnap
          /\ UNCHANGED readSeqN
     ELSE /\ UNCHANGED rpc
          /\ bufSnap' = (Size(bufSnap) :> Read(readSeqN)) @@ bufSnap
          /\ readSeqN' = readSeqN + 1
  /\ UNCHANGED writeSeqNSnap
  /\ UNCHANGED rbuf
  /\ UNCHANGED processingIndex
  /\ UNCHANGED storedPrefix

(* Calculate how entries from previous read might have been overwritten based
   on current value of overwrite sequence number. Append that many missed values to the
   reader's buffer, potentially replacing a stored prefix with a missed value *)
ProcessOverwritten == 
  /\ rpc = "processOverwritten"
  /\ rpc' = "processEntry"
  /\ processingIndex' = NMissedDuringRead(overwriteSeqN, readSeqN, Size(bufSnap))
  /\ IF ~(storedPrefix.type = "NONE") /\ NMissedDuringRead(overwriteSeqN, readSeqN, Size(bufSnap)) > 0
     THEN /\ rbuf' = AppendMissed(rbuf, NMissedDuringRead(overwriteSeqN, readSeqN, Size(bufSnap)) + 1)
          /\ storedPrefix' = Entry(0, "NONE")
     ELSE /\ rbuf' = AppendMissed(rbuf, NMissedDuringRead(overwriteSeqN, readSeqN, Size(bufSnap)))
          /\ UNCHANGED storedPrefix
  /\ UNCHANGED bufSnap
  /\ UNCHANGED readSeqN
  /\ UNCHANGED writeSeqNSnap
  
(* Process a single entry in the buffer snapshot by either storing it in the reader's 
   buffer or as a stored prefix *)
ProcessEntry == 
  /\ rpc = "processEntry"
  /\ IF processingIndex = Size(bufSnap)
     THEN /\ rpc' = "snapWriteSeqN"
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
  /\ UNCHANGED writeSeqNSnap

-----------------------------------------------------------------------------

(* Reader *)

ReaderInit ==
  /\ rpc = "snapWriteSeqN"
  /\ rbuf = <<>>
  /\ bufSnap = <<>>
  /\ readSeqN = 0
  /\ writeSeqNSnap = 0
  /\ storedPrefix = Entry(0, "NONE")
  /\ processingIndex = 0

(* Wait when writer takes a step *)
ReaderWait ==
  /\ UNCHANGED rpc
  /\ UNCHANGED rbuf
  /\ UNCHANGED bufSnap
  /\ UNCHANGED readSeqN
  /\ UNCHANGED writeSeqNSnap
  /\ UNCHANGED storedPrefix
  /\ UNCHANGED processingIndex

(* Take appropriate step based on rpc *)
ReaderStep == 
  \/ SnapWriteSeqN
  \/ SnapOverwriteSeqN
  \/ SnapEntry
  \/ ProcessOverwritten
  \/ ProcessEntry  

-----------------------------------------------------------------------------

Init == 
  /\ ReaderInit
  /\ WriterInit

(* Either take reader step or writer step. Stop writer after writeSeqN reaches numWrites *)
Next ==
  \/ WriterWait /\ ReaderStep 
  \/ ReaderWait /\ WriterStep /\ writeSeqN < NumWrites

-----------------------------------------------------------------------------

(* Invariants *)

(* Read sequence number cannot overtake write sequence number *)
InvReadSeqNBehindWriteSeqN ==
  readSeqN <= writeSeqN

(* Write sequence number cannot overtake overwrite sequence number *)
InvWriteSeqNBehindOverwriteSeqN ==
  writeSeqN <= overwriteSeqN

(* Reader's buffer cannot contain more elements than reader's sequence number value *)
InvReadBufferNotTooBig ==
  Size(rbuf) <= readSeqN

(* The overwrite sequence number is incremented by 2 when overwriting a double entry.
   Therefore, it should never point to a suffix. *)
InvOverwriteSeqNNotOnSuffix ==
    IF overwriteSeqN > BufCapacity 
    THEN ~(Read(overwriteSeqN).type = "SUFFIX")
    ELSE TRUE

(* Since suffixes could possibly be interpreted as prefixes, ensure that suffixes
   are stored as a prefix *)
InvStoredPrefixNotSuffix == 
  storedPrefix.type = "NONE" \/ storedPrefix.type = "PREFIX"

(* Check that every non-nil entry is at the correct index in the read buffer *)
InvCorrectIndices == 
  IF Size(rbuf) > 0 
  THEN \A i \in 0..(Size(rbuf)-1): rbuf[i].index = i \/ rbuf[i].type = "MISSED"
  ELSE TRUE

(* Check that every prefix has a suffix and vice versa*)
InvConsistentDoubles == 
  CASE Size(rbuf) = 0 -> TRUE
  [] Size(rbuf) = 1 -> ~(rbuf[0].type = "SUFFIX" \/ rbuf[Size(rbuf)-1].type = "PREFIX")
  [] Size(rbuf) >= 2 -> 
    /\ ~(rbuf[0].type = "SUFFIX" \/ rbuf[Size(rbuf)-1].type = "PREFIX")
    /\ \A i \in 0..(Size(rbuf)-2): 
          rbuf[i].type = "PREFIX" <=> rbuf[i+1].type = "SUFFIX"

=============================================================================
