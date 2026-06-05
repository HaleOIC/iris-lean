module

public section

namespace Iris.ProofMode.Aesop

open Lean Std

/-
Invariant: between 0 and 1.0
-/
structure Percent where
  toFloat : Float
  deriving Inhabited

namespace Percent

protected def ofFloat (f : Float) : Option Percent :=
  if 0 <= f && f <= 1.0 then some ⟨f⟩ else none

instance : Mul Percent where
  mul p q := ⟨p.toFloat * q.toFloat⟩

@[inline]
def δ : Percent :=
  ⟨0.00001⟩

instance : BEq Percent where
  beq | ⟨p⟩, ⟨q⟩ => if p > q then p - q < δ.toFloat else q - p < δ.toFloat

instance : Ord Percent where
  compare p q :=
    if p == q then Ordering.eq
    else if p.toFloat < q.toFloat then Ordering.lt
    else Ordering.gt

instance : LT Percent :=
  ltOfOrd

instance : LE Percent :=
  leOfOrd

instance : ToString Percent where
  toString p := toString p.toFloat

instance : HPow Percent Nat Percent where
  hPow | ⟨p⟩, n => ⟨p ^ n.toFloat⟩

def hundred : Percent := ⟨1⟩
def almost  : Percent := ⟨0.99⟩
def high    : Percent := ⟨0.75⟩
def medium  : Percent := ⟨0.5⟩
def low     : Percent := ⟨0.25⟩
def last    : Percent := ⟨0.01⟩

protected def ofNat (n : Nat) : Option Percent :=
  Percent.ofFloat $ n.toFloat / 100

end Percent
