module

public meta import Iris.ProofMode.Aesop.Search.Bubble.Group

namespace IAesopTest.Basic.BubblePlatform

open Iris.ProofMode.Aesop.Search.Bubble

private meta def candidate (id child : Nat) (consumed : Array Nat)
    (pre : Option BubbleId := none) (constituents : Array BubbleId := #[]) : Candidate Nat :=
  {
    id := ⟨id⟩
    childIndex := child
    consumed
    pre
    constituents
  }

/- Metavariable sharing forms transitive connected components. -/
#guard
  let groups := dependencyComponents #[#[1], #[1, 2], #[2], #[3], #[]]
  groups.size == 3 && groups.any fun group =>
    group.size == 3 && group.contains 0 && group.contains 1 && group.contains 2

/- Goals without shared metavariables stay independent. -/
#guard
  let groups := dependencyComponents #[#[1], #[2], #[]]
  groups.size == 3 && groups.all fun group => group.size == 1

/- A refined group remains an alternative for the same outer root and records
the group that generated it. -/
#guard
  let original : GoalGroupData Unit := {
    id := ⟨4⟩
    rootIndex := 1
    members := #[{ originalIndex := 2, goal := () }]
    platform := Platform.empty 1
  }
  let residual : GoalGroupData Unit := {
    id := ⟨5⟩
    rootIndex := original.rootIndex
    members := #[{ originalIndex := 2, goal := () }]
    preGroup? := some original.id
    platform := Platform.empty 1
  }
  residual.rootIndex == original.rootIndex && residual.preGroup? == some original.id

/- A bubble is retained while it waits for another child. -/
#guard
  let platform := Platform.empty (Resource := Nat) 2
  let (platform, emitted) := arrive platform (candidate 0 0 #[1])
  emitted.isEmpty && platform.byChild[0]!.size == 1

/- A conflicting sibling does not emit a total combination. -/
#guard
  let platform := Platform.empty (Resource := Nat) 2
  let (platform, _) := arrive platform (candidate 0 0 #[1])
  let (_, emitted) := arrive platform (candidate 1 1 #[1])
  emitted.isEmpty

/- A later compatible sibling unlocks a previously blocked bubble. -/
#guard
  let platform := Platform.empty (Resource := Nat) 2
  let (platform, _) := arrive platform (candidate 0 0 #[1])
  let (platform, blocked) := arrive platform (candidate 1 1 #[1])
  let (_, emitted) := arrive platform (candidate 2 1 #[2])
  blocked.isEmpty && emitted.size == 1

/- Only combinations containing the newly arrived bubble are enumerated. -/
#guard
  let platform := Platform.empty (Resource := Nat) 2
  let (platform, _) := arrive platform (candidate 0 0 #[1])
  let (platform, _) := arrive platform (candidate 1 0 #[2])
  let (platform, first) := arrive platform (candidate 2 1 #[2])
  let (_, second) := arrive platform (candidate 3 1 #[3])
  first.size == 1 && second.size == 2

/- A dependent bubble composes only with its exact predecessor. -/
#guard
  let platform := Platform.empty (Resource := Nat) 2
  let (platform, _) := arrive platform (candidate 0 0 #[] (some ⟨2⟩))
  let (platform, wrong) := arrive platform (candidate 1 1 #[])
  let (_, exact) := arrive platform (candidate 2 1 #[])
  wrong.isEmpty && exact.size == 1

/- Provenance remains valid after the predecessor has been wrapped in a
higher-level bubble. -/
#guard
  let platform := Platform.empty (Resource := Nat) 2
  let dependent := candidate 3 0 #[] (some ⟨2⟩)
  let carrier := candidate 4 1 #[] none #[⟨2⟩]
  let (platform, _) := arrive platform dependent
  let (_, emitted) := arrive platform carrier
  emitted.size == 1

/- A dependent candidate cannot discharge its own prefix requirement merely
because it remembers that prefix in its ancestry. -/
#guard
  let platform := Platform.empty (Resource := Nat) 1
  let selfCarrier := candidate 4 0 #[] (some ⟨2⟩) #[⟨2⟩]
  let (_, emitted) := arrive platform selfCarrier
  emitted.isEmpty

end IAesopTest.Basic.BubblePlatform
