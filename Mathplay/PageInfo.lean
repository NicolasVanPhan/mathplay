
import Mathlib
import Lean
import Std

namespace Helpers

theorem even_halves : forall w, Even w → w = w / 2 + w / 2 := by grind

def bor_red (b : BitVec w) : Bool := b != BitVec.zero w
def or_red (b : BitVec w) : BitVec 1 := if bor_red b then 1#1 else 0#1

end Helpers

/- ---------------------------------------------------------------------------------------------- -/

def slice (mask : BitVec w) (lo len : Nat) : BitVec len :=
  BitVec.truncate len (mask >>> lo)

example : slice 0xdead_beef#32 8 20  = 0xeadbe#20 := by rfl
example : slice 0xdead_beef#32 24 12 = 0x0de#12 := by rfl
example : slice 0xdead_beef#32 24 0  = 0x0#0 := by rfl
example : slice 0xdead_beef#32 31 42 = 0x1#42 := by rfl
example : slice 0xdead_beef#32 32 42 = 0x0#42 := by rfl

/- ---------------------------------------------------------------------------------------------- -/

abbrev Bit := BitVec 1

def Bit.pp : BitVec 1 → String
| 0#1 => "0"
| 1#1 => "1"

/- ---------------------------------------------------------------------------------------------- -/


namespace Half

/- Core contains the proof-friendly definition of hi and lo
   Then used to define the user-friendly hi and low right after that
-/

namespace Core

/- Halves of a bitvec are defined as such :
   They are the partitioning of the original vector into two parts of same size.
   So :
   1. They are a partitioning of the original bitvec
      (concatenating the parts give you back the original vec)
      (proven by `partition` )
   2. They have the same size (proven by `same_size`)
   3. They are defined only on vector of even length (proven by construction of `BitVec (w + w)`)
-/

def hi (mask : BitVec (w + w)) : BitVec w := slice mask w w
def lo (mask : BitVec (w + w)) : BitVec w := slice mask 0 w

-- NOTE : using 2*w  and w is useful for the implementor (us, proving things like sanity_half)
--        using w and w/2 is useful for the user (the one calling get_hi_half,
--        not having to provide the explicit final width)

theorem partition : ∀ w, ∀ m : BitVec (w + w),
  hi m ++ lo m = m := by
  intros w m
  simp [hi, lo, slice]
  grind

abbrev BitVec.width {w : Nat} (_ : BitVec w) : Nat := w

theorem same_size : ∀ w (m : BitVec (w + w)), BitVec.width (hi m) = BitVec.width (lo m) :=
by intro w m; simp

end Core

def hi (mask : BitVec w) (h : Even w := by decide) : BitVec (w/2) :=
  Core.hi (cast (by rw [←  Helpers.even_halves w h]) mask)

def lo (mask : BitVec w) (h : Even w := by decide) : BitVec (w/2) :=
  Core.lo (cast (by rw [←  Helpers.even_halves w h]) mask)

#eval (hi 0xdeadbeef#32).toHex
#eval (lo 0xdeadbeef#32).toHex

example : hi 0xdeadbeef#32 = 0xdead#16 := by rfl
example : lo 0xdeadbeef#32 = 0xbeef#16 := by rfl

end Half

/- ---------------------------------------------------------------------------------------------- -/

structure PageInfo where
  lo : Bit -- Indicates access to the lower half of its page
  hi : Bit -- Indicates access to the upper half of its page
  wp : Bit -- Indicates access to the upper half of the next page
  cross : Bit -- Indicates a cross-page access (accessing 2 pages)

namespace PageInfo

abbrev access_size := 16
abbrev offset_w := 5

abbrev page_size := 2 ^ offset_w

structure Access (access_size : Nat) (page_size : Nat) where
  offset : Nat
  mask : BitVec access_size
  h_offset_bound : offset < page_size

section
-- Implicit pervasive function input
abbrev I := Access access_size page_size
variable (i : I)

def b : Nat := i.offset
def e : Nat := i.offset + access_size - 1

def boffset : BitVec offset_w := b i
def eoffset : BitVec offset_w := e i

def toy : I := ⟨4, 0xcafe#16, by decide⟩
#eval (eoffset toy - boffset toy)

theorem sanity : eoffset i - boffset i + 1 = access_size := by
  simp [boffset, eoffset, offset_w, b, e]

def xmask' : BitVec (2 * page_size) := (BitVec.zeroExtend (2 * page_size) i.mask)
def xmask : BitVec (2 * page_size) := xmask' i <<< b i

#eval (xmask ⟨4, 0xcafe#16, by decide⟩).toHex
#eval (xmask ⟨8, 0x0ace#16      , by decide⟩).toHex
#eval (xmask ⟨4, 0x0ace#16 <<< 4, by decide⟩).toHex

example : xmask ⟨0 + 4, 0x0ace#16      , by decide⟩
        = xmask ⟨0    , 0x0ace#16 <<< 4, by decide⟩
        := by rfl

theorem t1 : ∀ offset, ∀ (h : offset < 1)
           , xmask ⟨ (offset + 4), 0x0ace#16      , by grind ⟩
           = xmask ⟨ (offset    ), 0x0ace#16 <<< 4, by grind ⟩
           :=
by
  intro offset hbound
  simp [xmask, xmask', b, page_size, offset_w]
  induction offset <;> grind



example : xmask ⟨0 + 1, 0x0ace#16      , by grind⟩
        = xmask ⟨0    , 0x0ace#16 <<< 1, by grind⟩
        := by rfl


theorem t2 : ∀ offset shift, ∀ (h : offset < 1) (h' : shift < 4)
           , xmask ⟨ (offset + shift), 0x0ace#16          , by grind ⟩
           = xmask ⟨ (offset        ), 0x0ace#16 <<< shift, by grind ⟩
           :=
by
  intro offset shift h h'
  simp [xmask, xmask', b, page_size, offset_w]
  sorry -- TODO
