--------------------------- MODULE SequenceNumbers ---------------------------
EXTENDS Naturals

CONSTANTS 
  IntModulus, (* Modulus of integers (maximum value + 1) *)

  IncrementTo  (* The value of the sequence number that the writer should stop at *)

ASSUME IntModulus \in (Nat \ 0..2) (* Integer modulus at least 3 *)
-----------------------------------------------------------------------------

VARIABLES 
  wpc, (* Writer's program counter *)
  written_low, (* Low word of sequence number written in memory *)
  written_high, (* High word of sequence number written in memory *)
  next_increment, (* The next increment size *)
  new_low, (* What the low word will be set to after rollover *)

  rpc, (* Reader's program counter *)
  snapped_low, (* Snapshot of the low word *)
  snapped_high, (* Snapshot of the high word *)
  read_seqn, (* The last sequence number successfully read *)
  (* The last recorded in-memory sequence number before the start of the last read
     (Not actually known by reader, just used for invariants) *)
  seqn_before_read

-----------------------------------------------------------------------------

(* Writer helpers *)

(* Calculate the integer-valued sequence number based on the high and low words *)
SeqNum(high, low) == (high.val * IntModulus) + low 

(* Structure used to store a word and a boolean set to true when the value is getting edited.
   In reality, the high bit of the high word is used instead of a separate boolean *)
ProgressValStruct(val, in_progress) == [val |-> val, in_progress |-> in_progress]

(* Create ProgressValStruct not in progress *)
ProgressVal(val) == ProgressValStruct(val, FALSE)

(* Set ProgressVal structure to be in progress *)
SetInProgress(progress_struct) == ProgressValStruct(progress_struct.val, TRUE)

-----------------------------------------------------------------------------

(* Writer steps *)

(* The low word of the writer is incremented until it reaches the integer maximum *)
IncrementLow ==
  /\ wpc = "IncrementLow"
  /\ \/ IF written_low + next_increment >= IntModulus
        THEN /\ UNCHANGED written_low
             /\ wpc' = "SetHighInProgress"
             /\ new_low' = (written_low + next_increment) - IntModulus
        ELSE /\ written_low' = written_low + 1
             /\ UNCHANGED wpc
             /\ UNCHANGED new_low
  /\ UNCHANGED written_high
  /\ UNCHANGED next_increment
  
(* Before rolling over the low word and incrementing the high, a flag in the high word
   is set to ensure that the reader does not use an inconsistent state *)
SetHighInProgress ==
  /\ wpc = "SetHighInProgress"
  /\ written_high' = SetInProgress(written_high)
  /\ wpc' = "ResetLow"
  /\ UNCHANGED written_low
  /\ UNCHANGED new_low
  /\ UNCHANGED next_increment
  
(* Set the low word to zero *)
ResetLow == 
  /\ wpc = "ResetLow"
  /\ written_low' = new_low
  /\ wpc' = "IncrementHigh"
  /\ UNCHANGED written_high
  /\ UNCHANGED new_low
  /\ UNCHANGED next_increment

(* Increment the high word, with the "in progress" flag no longer set *)
IncrementHigh ==
  /\ wpc = "IncrementHigh"
  /\ written_high' = ProgressVal(written_high.val + 1)
  /\ wpc' = "IncrementLow"
  /\ UNCHANGED written_low
  /\ UNCHANGED new_low
  /\ \/ next_increment' = 1
     \/ next_increment' = 2

-----------------------------------------------------------------------------

(* Writer *)

WriterInit == 
  /\ wpc = "IncrementLow"
  /\ written_low = 0
  /\ written_high = ProgressVal(0)
  /\ new_low = 0
  /\ \/ next_increment = 1
     \/ next_increment = 2
    
(* Wait when reader takes steps *)
WriterWait ==
  /\ UNCHANGED wpc
  /\ UNCHANGED written_high
  /\ UNCHANGED written_low
  /\ UNCHANGED new_low
  /\ UNCHANGED next_increment
  
(* Take appropriate step based on wpc *)
WriterStep ==
  \/ IncrementLow
  \/ SetHighInProgress
  \/ ResetLow
  \/ IncrementHigh

-----------------------------------------------------------------------------

(* Reader Steps*)

(* Take a snapshot of the high word, repeating this step if the "in progress" flag is set *)
SnapHighBefore ==
  /\ rpc = "SnapHighBefore"
  /\ IF written_high.in_progress
     THEN /\ rpc' = "SnapHighBefore"
          /\ UNCHANGED seqn_before_read
          /\ UNCHANGED snapped_high
          /\ UNCHANGED read_seqn
     ELSE /\ rpc' = "SnapLow"
          /\ seqn_before_read' = SeqNum(written_high, written_low)
          /\ snapped_high' = written_high
          /\ read_seqn' = SetInProgress(read_seqn)
  /\ UNCHANGED snapped_low

(* Take a snapshot of the low word *)
SnapLow ==
  /\ rpc = "SnapLow"
  /\ snapped_low' = written_low
  /\ rpc' = "SnapHighAfter"
  /\ UNCHANGED snapped_high
  /\ UNCHANGED read_seqn
  /\ UNCHANGED seqn_before_read

(* Take another snapshot of the high word. If it has not changed since the first snapshot,
   Then the sequence number can be used. Otherwise, the reader must start over to try
   reading the entire sequence number again *)
SnapHighAfter == 
  /\ rpc = "SnapHighAfter"
  /\ IF written_high = snapped_high 
     THEN read_seqn' = ProgressVal(SeqNum(snapped_high, snapped_low))
     ELSE UNCHANGED read_seqn    
  /\ rpc' = "SnapHighBefore"
  /\ UNCHANGED snapped_low
  /\ UNCHANGED snapped_high
  /\ UNCHANGED seqn_before_read

-----------------------------------------------------------------------------

(* Reader *)

ReaderInit ==
  /\ rpc = "SnapHighBefore"
  /\ snapped_low = 0
  /\ snapped_high = ProgressVal(0)
  /\ read_seqn = ProgressVal(0)
  /\ seqn_before_read = 0
  
(* Wait when writer takes a step *)
ReaderWait ==
  /\ UNCHANGED rpc
  /\ UNCHANGED snapped_low
  /\ UNCHANGED snapped_high
  /\ UNCHANGED read_seqn
  /\ UNCHANGED seqn_before_read
  

(* Take appropriate step based on rpc *)
ReaderStep == 
  \/ SnapHighBefore
  \/ SnapLow
  \/ SnapHighAfter
  
-----------------------------------------------------------------------------

Init == 
  /\ ReaderInit
  /\ WriterInit

(* Either take reader step or writer step. Stop writer after wcurs reaches numWrites *)
Next ==
  \/ WriterWait /\ ReaderStep 
  \/ ReaderWait /\ WriterStep /\ SeqNum(written_high, written_low) < IncrementTo

-----------------------------------------------------------------------------

(* Invariants *)

ReadNotLessThanReadStart == 
  read_seqn.in_progress \/ read_seqn.val >= seqn_before_read 

ReadNotGreaterThanWritten == 
  written_high.in_progress \/ read_seqn.val <= SeqNum(written_high, written_low)

=============================================================================