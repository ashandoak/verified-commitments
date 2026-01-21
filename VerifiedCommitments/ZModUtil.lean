import Mathlib.Data.ZMod.Basic


lemma ZMod.eq_iff_val_modEq (n : ℕ) [NeZero n] (a b : ZMod n) : a = b ↔ a.val ≡ b.val [MOD n] := by
  constructor
  · intro h
    rw [h]
  · intro h_congr
    -- Convert to integer cast equality
    have h1 : (a.val : ZMod n) = a := ZMod.natCast_zmod_val a
    have h2 : (b.val : ZMod n) = b := ZMod.natCast_zmod_val b
    rw [← h1, ← h2]
    rw [ZMod.natCast_eq_natCast_iff]
    exact h_congr

-- Define the multiplicative subset of Z_q (Z_q without 0)
def ZModMult (q : ℕ) [NeZero q] := {a : ZMod q // a ≠ 0}

-- Helper function to extract the value from ZModMult
def val {q : ℕ} [NeZero q] (a : ZModMult q) : ZMod q := a.val

lemma ZModMult.coe_ne_zero {q : ℕ} [NeZero q] (a : ZModMult q) : (val a : ZMod q) ≠ 0 :=
    a.property


-- Fintype instance for ZModMult
instance {q : ℕ} [NeZero q] : Fintype (ZModMult q) :=
  Fintype.subtype ((Finset.univ : Finset (ZMod q)).erase 0) (by simp [Finset.mem_erase])

instance {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] : Nonempty (ZModMult q) := ⟨⟨1, one_ne_zero⟩⟩
