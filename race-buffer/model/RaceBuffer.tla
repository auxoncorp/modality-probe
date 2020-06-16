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
  wcurs, (* Write cursor - Equal to number of entries already written *)

  writes, (* Number of entries written (used to limit state space) *)

  rpc, (* Reader's program counter *)
  rbuf, (* Buffer of entries already read *)
  bufSnap, (* Intermediate buffer used to store a snapshot of entries being read *)
  rcurs, (* Read cursor - Equal to number of entries already read*)
  wcursSnap (* Value of wcurs observed at beginning of read *)

-----------------------------------------------------------------------------

(* Writer helpers *)

(* Construct an entry structure - Index field is only used to check *)
(* ordering in the read buffer of non-nil entries. *)
Entry(i, t) == [index |-> i, type |-> t]

(* Get index in backing storage based on entry index *)
BufIndex(i) == i % BufCapacity

(* Get entry in storage position of given index *)
Read(i) == buf[BufIndex(i)]

(* Write a single entry of given type at given index *)
Write(i, t) == buf' = (BufIndex(i) :> Entry(i,t)) @@ buf

(* Write the appropriately typed non-nil entry at the given index *)
WriteEntry(i) == 
  /\ IF Read(i - 1).type = "PREFIX"
     THEN Write(i, "SUFFIX")
     ELSE \/ Write(i, "SINGLE")
          \/ Write(i, "PREFIX")
  /\ writes' = writes + 1

-----------------------------------------------------------------------------

(* Writer steps *)


(* Writer either writes nil entry at wcurs or transitions to OverwriteSuf in
   the case that a double entry is being overwritten *)
Overwrite == 
  /\ wpc = "overwrite"
  /\ IF Read(wcurs).type = "PREFIX" 
     THEN /\ wpc' = "overwriteSuf"
          /\ UNCHANGED buf
     ELSE /\ Write(wcurs, "NIL")
          /\ wpc' = "incrementWCursor"
  /\ UNCHANGED wcurs
  /\ UNCHANGED writes

(* Writer must overwrite a double entry. First, the suffix is replaced with 
   a nil entry. *)
OverwriteSuf == 
  /\ wpc = "overwriteSuf"
  /\ Write(wcurs + 1, "NIL")
  /\ wpc' = "overwritePre"
  /\ UNCHANGED wcurs
  /\ UNCHANGED writes

(* Overwrite the prefix of a double entry with a nil value *)
OverwritePre == 
  /\ wpc = "overwritePre"
  /\ Write(wcurs, "NIL")
  /\ wpc' = "doubleIncrementWCursor"
  /\ UNCHANGED wcurs
  /\ UNCHANGED writes

(* Increment the write cursor by 1 *)
IncrementWCursor ==
  /\ wpc = "incrementWCursor"
  /\ wcurs' = wcurs + 1
  /\ wpc'= "writeSuf"
  /\ UNCHANGED buf
  /\ UNCHANGED writes

(* Increment the write cursor by 2 *)
DoubleIncrementWCursor ==
  /\ wpc = "doubleIncrementWCursor"
  /\ wcurs' = wcurs + 2
  /\ wpc'= "writePre"
  /\ UNCHANGED buf
  /\ UNCHANGED writes

(* Write the prefix of double entry *)
WritePre ==
  /\ wpc = "writePre"
  /\ WriteEntry(wcurs - 2)
  /\ wpc' = "writeSuf"
  /\ UNCHANGED wcurs

(* Write a single entry, or the suffix of double entry *)
WriteSuf == 
  /\ wpc = "writeSuf"
  /\ WriteEntry(wcurs - 1)
  /\ wpc' = "overwrite"
  /\ UNCHANGED wcurs

-----------------------------------------------------------------------------

(* Writer *)

WriterInit == 
  /\ wpc = "overwrite"
  /\ wcurs = 0
  /\ buf = [i \in 0..BufCapacity-1 |-> Entry(0, "NIL")]

(* Wait when reader takes steps *)
WriterWait ==
  /\ UNCHANGED wpc
  /\ UNCHANGED wcurs
  /\ UNCHANGED buf
  /\ UNCHANGED writes

(* Take appropriate step based on wpc *)
WriterStep ==
  \/ Overwrite
  \/ OverwriteSuf
  \/ OverwritePre
  \/ IncrementWCursor
  \/ DoubleIncrementWCursor
  \/ WritePre
  \/ WriteSuf

-----------------------------------------------------------------------------

(* Reader helpers *)

(* Return number of keys in a function *)
Size(f) == Cardinality(DOMAIN f)

(* Return (maximum index + 1) of integer keyed function, or 0 if no keys *)
NextIndex(f) == IF Size(f) = 0 THEN 0 ELSE (CHOOSE i \in DOMAIN f: \A j \in DOMAIN f: i >= j)+1

(* Return minimum of integer keyed function, or 0 if no keys *)
MinIndex(f) == IF Size(f) = 0 THEN 0 ELSE CHOOSE i \in DOMAIN f: \A j \in DOMAIN f: i <= j

(* Return number of entries past rc overwritten based on given wc *)
Overlap(wc, rc) == IF wc < (rc + BufCapacity) THEN 0 ELSE wc - (rc + BufCapacity)

(* If the last entry of read buffer is a prefix entry, replace it with a nil entry. *)
(* This is used whenever a nil entry is appended to the read buffer to prevent *)
(* prefixes with missing suffixes from occurring. *)
ReplacePrefixNil(rb) == 
  IF Size(rb) > 0
  THEN IF rb[NextIndex(rb)-1].type = "PREFIX"
       THEN [rb EXCEPT ![NextIndex(rb)-1] = Entry(0, "NIL")]
       ELSE rb
  ELSE rb

(* Remove the entries from the snapshot that may have been overwritten based on the write cursor *)
RemoveOverlap(snap) == 
  [i \in (MinIndex(snap)+Overlap(wcurs, rcurs-Size(bufSnap)))..(NextIndex(snap)-1)
   |-> snap[i]]

(* Append given entry to read buffer, replacing last prefix with nil if suffix is lost *)
AppendEntry(rb, entry) == 
  (IF entry.type = "NIL" THEN ReplacePrefixNil(rb) ELSE rb) @@ (Size(rb) :> entry)

(* Append n nils to read buffer *)
RECURSIVE AppendNils(_,_)
AppendNils(rb, n) == 
  IF n = 0 THEN rb ELSE AppendNils(AppendEntry(rb, Entry(0, "NIL")), n-1)

(* Append snapshot to read buffer *)
RECURSIVE AppendSnap(_,_,_,_)
AppendSnap(rb, snap, start, end) == 
  IF start >= end THEN rb 
  ELSE AppendSnap(AppendEntry(rb, snap[start]), snap, start+1, end)

(* Return 1 if last entry of snap is nil, else 0 *)
CheckNilEnd(snap) == 
  IF snap[NextIndex(snap)-1].type = "NIL"
  THEN 1
  ELSE 0

(* Return number of nils at end of snap for snaps of length 2 or more *)
CheckDoubleNilEnd(snap) ==
  IF snap[NextIndex(snap)-2].type = "NIL" 
  THEN 2
  ELSE CheckNilEnd(snap)

(* Return number of nils at end of snap *)
NumNilsEnd(snap) == 
  CASE Size(snap) >= 2 -> CheckDoubleNilEnd(snap)
    [] Size(snap) = 1 -> CheckNilEnd(snap)
    [] Size(snap) = 0 -> 0

-----------------------------------------------------------------------------

(* Reader Steps*)
  
(* At the start of a read, reader takes a snapshot of the write cursor and appends
   nil entries to the read buffer if any entries were missed between reads *)
SnapWCurs == 
  /\ rpc = "snapWCurs"
  /\ wcursSnap' = wcurs
  /\ rbuf' = AppendNils(rbuf, Overlap(wcurs, rcurs))
  /\ rcurs' = rcurs + Overlap(wcurs, rcurs)
  /\ rpc' = "snapEntry"
  /\ bufSnap' = <<>>

(* Take a snapshot of a single entry, then move on to next entry until read cursor reaches
   snapshot of write cursor *)
SnapEntry == 
  /\ rpc = "snapEntry"
  /\ IF rcurs = wcursSnap
     THEN /\ rpc' = "processSnap"
          /\ UNCHANGED bufSnap
          /\ UNCHANGED rcurs
     ELSE /\ bufSnap' = (rcurs :> Read(rcurs)) @@ bufSnap
          /\ rcurs' = rcurs + 1
          /\ UNCHANGED rpc
  /\ UNCHANGED wcursSnap
  /\ UNCHANGED rbuf

(* Process entries in snapshot buffer, appending entries that have not been overwritten
   to read buffer. If the write cursor has lapped the read cursor, than all entries in the 
   snapshot buffer have been overwritten. *)
ProcessSnap == 
  /\ rpc = "processSnap"
  /\ rpc' = "snapWCurs"
  /\ IF wcurs >= rcurs + BufCapacity
     THEN /\ rbuf' = AppendNils(rbuf, Size(bufSnap))
          /\ UNCHANGED rcurs
     ELSE /\ rbuf' = AppendSnap(
               AppendNils(rbuf, Overlap(wcurs, rcurs-Size(bufSnap))),
               RemoveOverlap(bufSnap), 
               MinIndex(RemoveOverlap(bufSnap)),
               NextIndex(bufSnap) - NumNilsEnd(RemoveOverlap(bufSnap))
             )
          /\ rcurs' = rcurs - NumNilsEnd(RemoveOverlap(bufSnap))
  /\ UNCHANGED bufSnap
  /\ UNCHANGED wcursSnap

-----------------------------------------------------------------------------

(* Reader *)

ReaderInit ==
  /\ rpc = "snapWCurs"
  /\ rbuf = <<>>
  /\ bufSnap = <<>>
  /\ rcurs = 0
  /\ wcursSnap = 0

(* Wait when writer takes a step *)
ReaderWait ==
  /\ UNCHANGED rpc
  /\ UNCHANGED rbuf
  /\ UNCHANGED bufSnap
  /\ UNCHANGED rcurs
  /\ UNCHANGED wcursSnap

(* Take appropriate step based on rpc *)
ReaderStep == 
  \/ SnapWCurs
  \/ SnapEntry
  \/ ProcessSnap  

-----------------------------------------------------------------------------

Init == 
  /\ ReaderInit
  /\ WriterInit
  /\ writes = 0

(* Either take reader step or writer step. Stop writer after writes reaches numWrites *)
Next ==
  \/ WriterWait /\ ReaderStep 
  \/ ReaderWait /\ WriterStep /\ writes < NumWrites

-----------------------------------------------------------------------------

(* Invariants *)

(* Check that every non-nil entry is at the correct index in the read buffer *)
InvCorrectIndeces == 
  IF Size(rbuf) > 0 
  THEN \A i \in 0..(NextIndex(rbuf)-1): rbuf[i].index = i \/ rbuf[i].type = "NIL"
  ELSE TRUE

(* Check that every prefix has a suffix and vice versa*)
InvConsistentDoubles == 
  CASE Size(rbuf) = 0 -> TRUE
  [] Size(rbuf) = 1 -> ~(rbuf[0].type = "SUFFIX")
  [] Size(rbuf) >= 2 -> 
    /\ ~(rbuf[0].type = "SUFFIX")
    /\ \A i \in 0..(NextIndex(rbuf)-2): 
          rbuf[i].type = "PREFIX" <=> rbuf[i+1].type = "SUFFIX"

=============================================================================