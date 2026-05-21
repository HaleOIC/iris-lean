module

@[expose] public section

namespace Iris.ProofMode.Aesop

universe u

/--
Append-only log with depth-indexed marks.

`entries` stores the accumulated payloads. `marks` stores `(depth, position)`,
where `position` is an index into `entries`.
-/
structure MarkedLog (α : Type u) where
  entries : Array α
  marks : Array (Nat × Nat)
  deriving Inhabited, Repr

namespace MarkedLog

variable {α : Type _ }

@[inline]
def empty : MarkedLog α :=
  { entries := #[], marks := #[] }

@[inline]
def push (log : MarkedLog α) (entry : α) : MarkedLog α :=
  { log with entries := log.entries.push entry }

@[inline]
def pushMany (log : MarkedLog α) (entries : Array α) : MarkedLog α :=
  { log with entries := log.entries ++ entries }

@[inline]
def mark (log : MarkedLog α) (depth : Nat) : MarkedLog α :=
  { log with marks := log.marks.push (depth, log.entries.size) }

def popDeeperMarks (depth : Nat)
    (marks : Array (Nat × Nat)) : Array (Nat × Nat) :=
  (marks.toList.reverse.dropWhile fun mark => depth < mark.1).reverse.toArray

@[inline]
def currentStart (log : MarkedLog α) : Nat :=
  match log.marks.back? with
  | some (_, pos) => min pos log.entries.size
  | none => 0

/--
Collect the entries since the nearest surviving mark and then insert a new mark.

Before collecting, marks whose depth is larger than `depth` are popped from the
top of the mark stack. The returned array is `entries[start:]`, where `start`
is the position stored in the new top mark, or `0` if no mark remains.
-/
def collect (log : MarkedLog α) (depth : Nat) : Array α × MarkedLog α :=
  let marks := popDeeperMarks depth log.marks
  let log := { log with marks }
  let collected := log.entries.extract log.currentStart log.entries.size
  (collected, log.mark depth)

private def testLog : MarkedLog Nat :=
  MarkedLog.empty
    |>.mark 0
    |>.push 10
    |>.push 20
    |>.mark 2
    |>.push 30
    |>.mark 3
    |>.push 40

#guard (MarkedLog.collect testLog 2).1 == #[30, 40]

#guard (MarkedLog.collect testLog 2).2.marks ==
  #[(0, 0), (2, 2), (2, 4)]

#guard (MarkedLog.collect testLog 3).1 == #[40]

#guard (MarkedLog.collect testLog 0).1 == #[10, 20, 30, 40]

end MarkedLog
