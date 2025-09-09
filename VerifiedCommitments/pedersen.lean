import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.ZMod.Defs
import VerifiedCommitments.«commitment-scheme»
import VerifiedCommitments.dlog


-- Helper lemma
lemma ZMod.eq_iff_val_modEq (n : ℕ) [NeZero n] (a b : ZMod n) : a = b ↔ a.val ≡ b.val [MOD n] := by
  constructor
  · intro h
    rw [h]
  · intro h_congr
    -- Convert to integer cast equality
    have h1 : (a.val : ZMod n) = a := ZMod.natCast_zmod_val a
    have h2 : (b.val : ZMod n) = b := ZMod.natCast_zmod_val b
    rw [← h1, ← h2]
    rw [ZMod.eq_iff_modEq_nat]
    exact h_congr


namespace Pedersen

  noncomputable def scheme
    (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
      (q : ℕ) [NeZero q] (hq_prime : Nat.Prime q) :
      CommitmentScheme (ZMod q) G (ZMod q) G := {
    setup := --setup q hq g,
    do
      let nonzero_elements := (Finset.univ : Finset (ZMod q)).erase 0
      have h_nonempty : nonzero_elements.Nonempty := by
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
          exact ⟨1, mem1⟩
      let a ← PMF.uniformOfFinset nonzero_elements h_nonempty
      return g^a.val,
    commit := fun h m =>  --commit h m g,
    do
      let r ← PMF.uniformOfFintype (ZMod q)
      return (g^m.val * h^r.val, r),
    verify := fun h m c o => if c = g^m.val * h^o.val then 1 else 0  --verify h m c o g
  }

  noncomputable def adversary
    (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G]
      (q : ℕ) [NeZero q]
      (A : G → PMF (G × ZMod q × ZMod q × ZMod q × ZMod q))
      (h : G) : PMF (ZMod q) :=
    do
      let (_c, m, m', o, o') ← A h
      if o ≠ o' then
        return ((m - m') * (o' - o)⁻¹)
      else
        PMF.uniformOfFintype (ZMod q)

end Pedersen

noncomputable def DLog_game
  (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] (hq_prime : Nat.Prime q)
    (A' : G → PMF (ZMod q)) : PMF (ZMod 2) :=
  do
    let nonzero_elements := (Finset.univ : Finset (ZMod q)).erase 0
    have h_nonempty : nonzero_elements.Nonempty := by
      sorry
    let x ← PMF.uniformOfFinset nonzero_elements h_nonempty
    let h := g^x.val
    let x' ← A' h
    pure (if g^x'.val = h then 1 else 0)


lemma binding_as_hard_dlog
  (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] [CancelMonoidWithZero (ZMod q)] (hq_prime : Nat.Prime q) (ε : ENNReal)
    (G_card_q : Fintype.card G = q)
    (hg_gen : orderOf g = Fintype.card G)
    (A : G → PMF (G × ZMod q × ZMod q × ZMod q × ZMod q)) :
    comp_binding_game (Pedersen.scheme G g q hq_prime) A 1 ≤ DLog_game G g q hq_prime (Pedersen.adversary G q A) 1 := by
  unfold DLog_game
  unfold comp_binding_game
  unfold Pedersen.scheme
  unfold Pedersen.adversary
  simp only [bind_pure_comp, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not, ne_eq,
    bind_map_left, ite_not, map_bind]
  congr! 5 with x ⟨c, m, m', o, o'⟩
  simp only
  split_ifs
  · sorry -- this is a case I want to skip
  rename_i ho
  rename_i h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1] at h2
  simp only [map_pure]
  have h_noo' : o' ≠ o := by exact fun a ↦ ho (id (Eq.symm a))
  have h_coprime : (o' - o).val.Coprime q := by
    cases' Nat.coprime_or_dvd_of_prime hq_prime (o' - o).val with h_cop h_dvd
    · exact Nat.coprime_comm.mp h_cop
    · exfalso
      have h_zero : o' - o = 0 := by
        rw [← ZMod.val_eq_zero]
        have h_mod_zero : (o' - o).val % q = 0 := Nat.mod_eq_zero_of_dvd h_dvd
        have h_val_bound : (o' - o).val < q := ZMod.val_lt (o' - o)
        exact Nat.eq_zero_of_dvd_of_lt h_dvd h_val_bound
      exact h_noo' (eq_of_sub_eq_zero h_zero)

  have h_ex_inv : ∃ y, ↑(o' - o).val * y ≡ 1 [ZMOD q] := by apply Int.mod_coprime h_coprime

  have h_ord : orderOf g = q := by
    rw [← G_card_q]; exact hg_gen

  have h_pow : g ^ (m.val + x.val * o.val) = g ^ (m'.val + x.val * o'.val) := by
    simp [←pow_mul, ←pow_add] at h2
    exact h2

  have h_congr_nat : m.val + x.val * o.val ≡ m'.val + x.val * o'.val [MOD q] := by
    simpa [h_ord] using (pow_eq_pow_iff_modEq.mp h_pow)

  have h_zmod : (m + x * o : ZMod q) = (m' + x * o' : ZMod q) := by
    have eq_cast : ((m.val + x.val * o.val : ℕ) : ZMod q) =
                  ((m'.val + x.val * o'.val : ℕ) : ZMod q) :=
      (ZMod.eq_iff_modEq_nat _).mpr h_congr_nat
    simp at eq_cast
    exact eq_cast

  have h_lin : x * (o' - o) = m - m' := by grind

  have h_unit : o' - o ≠ 0 := sub_ne_zero.mpr h_noo'

  have h_solve_x : x = (m - m') * (o' - o)⁻¹ := by
     calc x = x * 1                                 := by rw [mul_one]
       _ = x * ((o' - o) * (o' - o)⁻¹)              := by
        haveI : Fact (Nat.Prime q) := ⟨hq_prime⟩
        rw [← one_mul x]
        congr 1
        have h_field_inv : (o' - o) * (o' - o)⁻¹ = 1 := by
          apply Field.mul_inv_cancel
          exact h_unit
        exact h_field_inv.symm
       _ = (x * (o' - o)) * (o' - o)⁻¹              := by rw [mul_assoc]
       _ = (m - m') * (o' - o)⁻¹                    := by rw [h_lin]

  have h_congr_final : ((m - m') * (o' - o)⁻¹).val ≡ x.val [MOD q] := by
    have h1 : (((m - m') * (o' - o)⁻¹).val : ZMod q) = (m - m') * (o' - o)⁻¹ :=
      ZMod.natCast_zmod_val ((m - m') * (o' - o)⁻¹)
    have h2 : (x.val : ZMod q) = x := ZMod.natCast_zmod_val x
    rw [← ZMod.eq_iff_modEq_nat]
    rw [h1, h2]
    exact h_solve_x.symm

  have h_eq : g ^ ((m - m') * (o' - o)⁻¹).val = g ^ x.val :=
    (pow_eq_pow_iff_modEq.mpr (by rwa [h_ord]))

  rw [h_eq]
  simp only [↓reduceIte]
  · sorry -- cases I want to skip
  · sorry


theorem Pedersen.computational_binding :
  ∀ (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] [CancelMonoidWithZero (ZMod q)] (hq_prime : Nat.Prime q) (ε : ENNReal)
    (G_card_q : Fintype.card G = q)
    (hg_gen : orderOf g = Fintype.card G),
    (∀ (A : G → PMF (ZMod q)), DLog_game G g q hq_prime A 1 ≤ ε) →
    (∀ (A : G → PMF (G × ZMod q × ZMod q × ZMod q × ZMod q)),
    comp_binding_game (Pedersen.scheme G g q hq_prime) A 1 ≤ ε) := by
  intro G _ _ _ _ g q _ _ hq_prime ε G_card_q hg_gen hdlog A
  exact le_trans (binding_as_hard_dlog G g q hq_prime ε G_card_q hg_gen A) (hdlog (Pedersen.adversary G q A))


-- Incomplete
theorem Pedersen.perfect_hiding : ∀ (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
  (q : ℕ) [NeZero q] (hq_prime : Nat.Prime q),
  perfect_hiding (Pedersen.scheme G g q hq_prime) := by
  intro G _ _ _ _ g q _ hq_prime
  unfold _root_.perfect_hiding
  intros m m' c
  unfold do_commit
  unfold Pedersen.scheme
  congr!
