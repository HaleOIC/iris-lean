module

public import Iris.ProofMode.Aesop.Util.Percent

public section

namespace Iris.ProofMode.Aesop

open Lean Std

/--
A bit-mask recording which positions have been proved.

Convention:
* bit `i = 1`: position `i` is proved
* bit `i = 0`: position `i` is still missing
-/
structure ProgressMask where
  n : Nat
  mask : BitVec n
  complete : Bool
  deriving Inhabited, Repr

namespace ProgressMask

@[inline]
def ofMask {n : Nat} (mask : BitVec n) : ProgressMask :=
  { n := n
    mask := mask
    complete := mask == BitVec.allOnes n }

@[inline]
def empty (n : Nat) : ProgressMask :=
  ofMask (BitVec.zero n)

@[inline]
def full (n : Nat) : ProgressMask :=
  ofMask (BitVec.allOnes n)

@[inline]
def size (p : ProgressMask) : Nat :=
  p.n

@[inline]
def onlyOne (p : ProgressMask) : Bool :=
  p.mask.cpop == 1

@[inline]
def isComplete (p : ProgressMask) : Bool :=
  p.complete

@[inline]
def progress (p : ProgressMask) : Percent :=
  if p.n == 0 then
    .hundred
  else
    ⟨p.mask.cpop.toNat.toFloat / p.n.toFloat⟩

@[inline]
def contains (p : ProgressMask) (i : Nat) : Bool :=
  p.mask.getLsbD i


@[inline]
def oneAt (n i : Nat) : BitVec n :=
  BitVec.twoPow n i

@[inline]
def mark (p : ProgressMask) (i : Nat) : ProgressMask :=
  ofMask (p.mask ||| oneAt p.n i)

@[inline]
def unmark (p : ProgressMask) (i : Nat) : ProgressMask :=
  ofMask (p.mask &&& ~~~(oneAt p.n i))

@[inline]
def onlyOneIndex? (p : ProgressMask) : Option Nat :=
  if p.onlyOne then
    let i := p.mask.ctz.toNat
    if i < p.n then some i else none
  else
    none

@[inline]
def diff (new old : ProgressMask) : ProgressMask :=
  if h : new.n = old.n then
    have : old.n = new.n := h.symm
    ofMask (new.mask &&& ~~~(h ▸ old.mask))
  else
    empty new.n

@[inline]
def firstNewBit? (new old : ProgressMask) : Option Nat :=
  (diff new old).onlyOneIndex?

end ProgressMask
