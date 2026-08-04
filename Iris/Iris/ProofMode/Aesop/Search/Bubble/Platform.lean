module

public import Iris.ProofMode.Aesop.Search.Bubble.Types

public section

namespace Iris.ProofMode.Aesop.Search.Bubble

private def disjoint [BEq Resource] (xs ys : Array Resource) : Bool :=
  xs.all fun x => !ys.contains x

private def appendFresh [BEq Resource]
    (xs ys : Array Resource) : Option (Array Resource) :=
  if disjoint xs ys then some (xs ++ ys) else none

private def appendShared [BEq Resource]
    (xs ys : Array Resource) : Array Resource :=
  ys.foldl (init := xs) fun acc resource =>
    if acc.contains resource then acc else acc.push resource

private def appendCompatible [BEq Resource] (policy : ResourcePolicy)
    (xs ys : Array Resource) : Option (Array Resource) :=
  match policy with
  | .disjoint => appendFresh xs ys
  | .shared => some (appendShared xs ys)

private def allProvenanceCompatible
    (selected : Array (Candidate Resource)) : Bool :=
  selected.all fun bubble =>
    match bubble.pre with
    | none => true
    | some predecessor => selected.any fun carrier =>
        carrier.id != bubble.id &&
          (carrier.id == predecessor || carrier.constituents.contains predecessor)

private def combinationKey (selected : Array (Candidate Resource)) : CombinationKey :=
  selected.map (fun bubble => bubble.id)

private partial def enumerateFrom [BEq Resource]
    (policy : ResourcePolicy) (candidates : Array (Array (Candidate Resource))) (index : Nat)
    (selected : Array (Candidate Resource)) (consumed : Array Resource) :
    Array (Combination Resource) :=
  if h : index < candidates.size then
    candidates[index].foldl (init := #[]) fun combinations candidate =>
      match appendCompatible policy consumed candidate.consumed with
      | none => combinations
      | some consumed' =>
          combinations ++ enumerateFrom policy candidates (index + 1)
            (selected.push candidate) consumed'
  else if allProvenanceCompatible selected then
    #[{ selected, consumed }]
  else
    #[]

/- Record a new bubble and incrementally enumerate only total combinations that
contain it.  Bubbles that currently participate in no total combination remain
stored in `byChild`. -/
def arrive [BEq Resource]
    (platform : Platform Resource) (bubble : Candidate Resource) :
    Platform Resource × Array (Combination Resource) :=
  if bubble.childIndex < platform.childCount then
    let oldChild := platform.byChild[bubble.childIndex]?
      |>.getD #[]
    let byChild := platform.byChild.set! bubble.childIndex (oldChild.push bubble)
    let candidates := byChild.mapIdx fun index bubbles =>
      if index == bubble.childIndex then #[bubble] else bubbles
    let combinations := enumerateFrom platform.resourcePolicy candidates 0 #[] #[]
    let (emitted, fresh) := combinations.foldl
      (init := (platform.emitted, #[])) fun (emitted, fresh) combination =>
        let key := combinationKey combination.selected
        if emitted.contains key then
          (emitted, fresh)
        else
          (emitted.push key, fresh.push combination)
    ({ platform with byChild, emitted }, fresh)
  else
    (platform, #[])

end Iris.ProofMode.Aesop.Search.Bubble
