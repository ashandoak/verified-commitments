import Mathlib.Data.ZMod.Basic

def nonzeroElements {q : ℕ} [NeZero q] (hq_prime : Nat.Prime q) : {s : Finset (ZMod q) // s.Nonempty} :=
  let nonzero_elements := (Finset.univ : Finset (ZMod q)).erase 0
  ⟨nonzero_elements, by
    have one_ne_zero : (1 : ZMod q) ≠ 0 := by
      intro h
      have : q ∣ 1 := by
        simp only [Nat.dvd_one]
        exact ZMod.one_eq_zero_iff.mp h
      have q_eq_one : q = 1 := Nat.dvd_one.1 this
      exact (Nat.Prime.ne_one hq_prime q_eq_one)
    have mem1 : (1 : ZMod q) ∈ nonzero_elements := by
      apply Finset.mem_erase.mpr
      constructor
      · exact one_ne_zero
      · simp
    exact ⟨1, mem1⟩⟩
