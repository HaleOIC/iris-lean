module

public import Iris.ProofMode.Aesop.Rule.Types
public import Iris.ProofMode.Aesop.Index.Types

public meta section

namespace Iris.ProofMode.Aesop

structure Rule (α : Type) where
  id : RuleId
  indexingMode : IndexingMode
  payload : α
  -- [TODO] Pattern/RulePattern
  -- [Note] Unknown whether we need this: "tac : RuleTacDescr"
  deriving Inhabited

namespace Rule

variable {α : Type}

instance : BEq (Rule α) where
  beq r s := r.id == s.id

instance : Ord (Rule α) where
  compare r s := compare r.id s.id

instance : Hashable (Rule α) where
  hash r := hash r.id

def compareByPriority [Ord α] (r s : Rule α) : Ordering :=
  compare r.payload s.payload

def compareById (r s : Rule α) : Ordering :=
  r.id.compare s.id

def compareByPriorityThenName [Ord α] (r s : Rule α) : Ordering :=
  compareByPriority r s |>.then $ compareById r s

@[inline]
protected def map (f : α → β) (r : Rule α) : Rule β :=
  { r with payload := f r.payload }

@[inline]
protected def mapM [Monad m] (f : α → m β) (r : Rule α) : m (Rule β) :=
  return { r with payload := ← f r.payload }

end Rule
