--------------------------- MODULE RaceBuffer ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
  BufCapacity, (* Capacity of backing storage *)

  NumWrites  (* Number of writes to execute *)

ASSUME Assumption == BufCapacity \in (Nat \ 0..2) (* Buffer capacity is at least 3 *)

-----------------------------------------------------------------------------

VARIABLES 
  wpc, (* Writer's program counter *)
  buf, (* Backing storage *)
  wcurs, (* Write cursor - Points to next write position *)
  owcurs, (* Overwrite cursor - Marks where space is allocated for the writer to write freely *)

  rpc, (* Reader's program counter *)
  rbuf, (* Buffer of entries already read *)
  bufSnap, (* Intermediate buffer used to store a snapshot of entries being read *)
  rcurs, (* Read cursor - Points to next read position *)
  wcursSnap, (* Value of write cursor observed at beginning of read *)
  storedPrefix, (* Prefix to be written to read buffer once suffix is read *)
  processingIndex (* Index of next entry in bufSnap to process *)

-----------------------------------------------------------------------------

(* Writer helpers *)

(* Construct an entry structure - Index field is only used to check *)
(* ordering in the reader's output buffer *)
Entry(i, t) == [index |-> i, type |-> t]

(* Get index in backing storage based on given cursor *)
BufIndex(i) == i % BufCapacity

(* Get entry in storage position of given cursor *)
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

(* Overwrite old entry by incrementing overwrite cursor *)
OverwriteOldEntry == 
    IF owcurs < BufCapacity 
    THEN owcurs' = owcurs + 1
    ELSE IF Read(owcurs).type = "PREFIX" 
         THEN owcurs' = owcurs + 2
         ELSE owcurs' = owcurs + 1

-----------------------------------------------------------------------------

(* Writer steps *)

(* If the write cursor has reached the overwrite cursor, then another entry 
   must be overwritten to allocate space for more writes *)
Overwrite == 
    /\ wpc = "overwrite"
    /\ IF wcurs = owcurs 
       THEN OverwriteOldEntry
       ELSE UNCHANGED owcurs
    /\ wpc' = "write"
    /\ UNCHANGED wcurs
    /\ UNCHANGED buf

(* Writer either writes nil entry at wcurs or transitions to OverwriteSuf in
   the case that a double entry is being overwritten *)
WriteStep == 
  /\ wpc = "write"
  /\ WriteEntry(wcurs)
  /\ wpc' = "incrWriteCursor"
  /\ UNCHANGED wcurs
  /\ UNCHANGED owcurs

(* Increment the write cursor by 1 *)
IncrWriteCursor ==
  /\ wpc = "incrWriteCursor"
  /\ wcurs' = wcurs + 1
  /\ wpc'= "overwrite"
  /\ UNCHANGED owcurs
  /\ UNCHANGED buf

-----------------------------------------------------------------------------

(* Writer *)

WriterInit == 
  /\ wpc = "overwrite"
  /\ wcurs = 0
  /\ owcurs = 0
  /\ buf = <<>>

(* Wait when reader takes steps *)
WriterWait ==
  /\ UNCHANGED wpc
  /\ UNCHANGED wcurs
  /\ UNCHANGED buf
  /\ UNCHANGED owcurs

(* Take appropriate step based on wpc *)
WriterStep ==
  \/ Overwrite
  \/ WriteStep
  \/ IncrWriteCursor

-----------------------------------------------------------------------------

(* Reader helpers *)

(* Return number of keys in a function *)
Size(f) == Cardinality(DOMAIN f)

(* Calculate the cursor value of the first item read during this read *)
FirstRead(rc, snapLen) == rc - snapLen

(* Return number of entries past rc overwritten based on given owc *)
Overlap(owc, rc) == IF owc < (rc + BufCapacity) THEN 0 ELSE owc - (rc + BufCapacity)

(* Return number of entries past first read overwritten (Maximum is snap buffer size) *)
OverlapRead(owc, rc, snapLen) == IF Overlap(owc, FirstRead(rc, snapLen)) <= snapLen 
                                 THEN Overlap(owc, FirstRead(rc, snapLen)) 
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
  
(* At the start of a read, reader takes a snapshot of the write cursor and appends
   nil entries to the read buffer if any entries were missed between reads *)
SnapWriteCursor == 
  /\ rpc = "snapWriteCursor"
  /\ wcursSnap' = wcurs
  /\ UNCHANGED rbuf
  /\ UNCHANGED rcurs
  /\ rpc' = "snapOverwriteCursor"
  /\ bufSnap' = <<>>
  /\ UNCHANGED storedPrefix
  /\ UNCHANGED processingIndex

(* Observe the current value of the overwrite cursor, and based on that value,
   append any missed entries to reader's buffer and update reader's cursor *)
SnapOverwriteCursor ==
  /\ rpc = "snapOverwriteCursor"
  /\ UNCHANGED wcursSnap
  /\ IF Overlap(owcurs, rcurs) > 0 /\ ~(storedPrefix.type = "NONE")
     THEN /\ rbuf' = AppendMissed(rbuf, Overlap(owcurs, rcurs) + 1)
          /\ storedPrefix' = Entry(0, "NONE")
     ELSE /\ rbuf' = AppendMissed(rbuf, Overlap(owcurs, rcurs))
          /\ UNCHANGED storedPrefix
  /\ rcurs' = rcurs + Overlap(owcurs, rcurs)
  /\ rpc' = "snapEntry"
  /\ bufSnap' = <<>>
  /\ UNCHANGED processingIndex

(* Take a snapshot of a single entry, then move on to next entry until read cursor reaches
   write cursor *)
SnapEntry == 
  /\ rpc = "snapEntry"
  /\ IF rcurs >= wcursSnap
     THEN /\ rpc' = "processOverwritten"
          /\ UNCHANGED bufSnap
          /\ UNCHANGED rcurs
     ELSE /\ UNCHANGED rpc
          /\ bufSnap' = (Size(bufSnap) :> Read(rcurs)) @@ bufSnap
          /\ rcurs' = rcurs + 1
  /\ UNCHANGED wcursSnap
  /\ UNCHANGED rbuf
  /\ UNCHANGED processingIndex
  /\ UNCHANGED storedPrefix

(* Calculate how entries from previous read might have been overwritten based
   on current value of overwrite cursor. Append that many missed values to the
   reader's buffer, potentially replacing a stored prefix with a missed value *)
ProcessOverwritten == 
  /\ rpc = "processOverwritten"
  /\ rpc' = "processEntry"
  /\ processingIndex' = OverlapRead(owcurs, rcurs, Size(bufSnap))
  /\ IF ~(storedPrefix.type = "NONE") /\ OverlapRead(owcurs, rcurs, Size(bufSnap)) > 0
     THEN /\ rbuf' = AppendMissed(rbuf, OverlapRead(owcurs, rcurs, Size(bufSnap)) + 1)
          /\ storedPrefix' = Entry(0, "NONE")
     ELSE /\ rbuf' = AppendMissed(rbuf, OverlapRead(owcurs, rcurs, Size(bufSnap)))
          /\ UNCHANGED storedPrefix
  /\ UNCHANGED bufSnap
  /\ UNCHANGED rcurs
  /\ UNCHANGED wcursSnap
  
(* Process a single entry in the buffer snapshot by either storing it in the reader's 
   buffer or as a stored prefix *)
ProcessEntry == 
  /\ rpc = "processEntry"
  /\ IF processingIndex = Size(bufSnap)
     THEN /\ rpc' = "snapWriteCursor"
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
  /\ UNCHANGED rcurs
  /\ UNCHANGED wcursSnap

-----------------------------------------------------------------------------

(* Reader *)

ReaderInit ==
  /\ rpc = "snapWriteCursor"
  /\ rbuf = <<>>
  /\ bufSnap = <<>>
  /\ rcurs = 0
  /\ wcursSnap = 0
  /\ storedPrefix = Entry(0, "NONE")
  /\ processingIndex = 0

(* Wait when writer takes a step *)
ReaderWait ==
  /\ UNCHANGED rpc
  /\ UNCHANGED rbuf
  /\ UNCHANGED bufSnap
  /\ UNCHANGED rcurs
  /\ UNCHANGED wcursSnap
  /\ UNCHANGED storedPrefix
  /\ UNCHANGED processingIndex

(* Take appropriate step based on rpc *)
ReaderStep == 
  \/ SnapWriteCursor
  \/ SnapOverwriteCursor
  \/ SnapEntry
  \/ ProcessOverwritten
  \/ ProcessEntry  

-----------------------------------------------------------------------------

Init == 
  /\ ReaderInit
  /\ WriterInit

(* Either take reader step or writer step. Stop writer after wcurs reaches numWrites *)
Next ==
  \/ WriterWait /\ ReaderStep 
  \/ ReaderWait /\ WriterStep /\ wcurs < NumWrites

-----------------------------------------------------------------------------

(* Invariants *)

(* Read cursor cannot overtake write cursor *)
InvRcursBehindWcurs ==
  rcurs <= wcurs

(* Write cursor cannot overtake overwrite cursor *)
InvWcursBehindOwcurs ==
  wcurs <= owcurs

(* Reader's buffer cannot contain more elements than reader's cursor value *)
InvReadBufferNotTooBig ==
  Size(rbuf) <= rcurs

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