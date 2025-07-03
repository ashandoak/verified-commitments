import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.ZMod.Defs
import VerifiedCommitments.«commitment-scheme»
import VerifiedCommitments.dlog

namespace Pedersen

  noncomputable def scheme (G : Type) [Fintype G] [Group G] [DecidableEq G]
    (q : ℕ) [NeZero q] (hq : q > 1) (g : G) : CommitmentScheme (ZMod q) G (ZMod q) G := {
    setup := --setup q hq g,
      do
        let k := Finset.Icc 1 (q-1)
        have k_nonempty : k.Nonempty := by
          refine Finset.nonempty_Icc.mpr ?_
          omega
        let a ← PMF.uniformOfFinset k k_nonempty
        return g^a,
    commit := fun h m =>  --commit h m g,
      do
        let r ← PMF.uniformOfFintype (ZMod q)
        return (g^m.val * h^r.val, r),
    verify := fun h m c o => if c = g^m.val * h^o.val then 1 else 0  --verify h m c o g
  }
end Pedersen

noncomputable def DLog_game (G : Type) [Group G] [DecidableEq G] (q : ℕ) (hq : q > 1) [NeZero q] (g : G) (A' : G → PMF (ZMod q)) : PMF (ZMod 2) :=
do
  let k := Finset.Icc 1 (q-1)   -- let x ← PMF.uniformOfFintype (ZMod q)
  have k_nonempty : k.Nonempty := by
    refine Finset.nonempty_Icc.mpr ?_
    omega
  let x ← PMF.uniformOfFinset k k_nonempty
  let h := g^x
  let x' ← A' h
  pure (if g^x'.val = h then 1 else 0)

noncomputable def pedersen_pmf (G : Type) [Fintype G] [Group G] [DecidableEq G]
    (q : ℕ) [NeZero q]
    (A : G → PMF (G × ZMod q × ZMod q × ZMod q × ZMod q))
    (h : G) : PMF (ZMod q) := do
  let (_c, m, m', o, o') ← A h
  if o ≠ o' then
    return ((m - m') * (o' - o)⁻¹)
  else
    PMF.uniformOfFintype (ZMod q)


lemma binding_as_hard_dlog (G : Type) [Fintype G] [Group G] [DecidableEq G]
  (q : ℕ) [NeZero q] (hq : q > 1) (g : G) (ε : ENNReal)
  (A : G → PMF (G × ZMod q × ZMod q × ZMod q × ZMod q)) :
  comp_binding_game (Pedersen.scheme G q hq g) A 1 ≤ DLog_game G q hq g (pedersen_pmf G q A) 1 := by
  unfold DLog_game
  unfold comp_binding_game
  unfold Pedersen.scheme
  unfold pedersen_pmf
  simp
  congr! 5 with a ⟨c, m, m', o, o'⟩
  simp
  split_ifs
  · sorry
  rename_i ho
  rename_i h
  obtain ⟨h1, h2, h3⟩ := h
  subst_vars
  simp
  have h_eq : g ^ ((m - m') * (o' - o)⁻¹).val = g ^ a := by
    rw [← mul_right_inj (g ^ m'.val)⁻¹] at h2
    rw [← mul_assoc, ← mul_assoc] at h2
    rw [← mul_left_inj ((g ^ a) ^ o.val)⁻¹] at h2
    simp at h2
    group at h2
    rw [zpow_eq_zpow_iff_modEq] at h2
    simp at h2
    have h_cong : (m - m').val ≡ a * (o' - o).val [MOD orderOf g] := by
      sorry
    have h_solve : ((m - m') * (o' - o)⁻¹).val ≡ a [MOD orderOf g] := by
      sorry
    rw [pow_eq_pow_iff_modEq]
    exact h_solve
  rw [h_eq]
  simp
  · sorry
  · sorry

theorem Pedersen.computational_binding : ∀ (G : Type) [Fintype G] [Group G] [DecidableEq G]
  (q : ℕ) [NeZero q] (hq : q > 1) (g : G) (ε : ENNReal),
  (∀ (A : G → PMF (ZMod q)), DLog_game G q hq g A 1 ≤ ε) →
  (∀ (A : G → PMF (G × ZMod q × ZMod q × ZMod q × ZMod q)),
   comp_binding_game (Pedersen.scheme G q hq g) A 1 ≤ ε) := by
  intro G _ _ _ q _ hq g ε hdlog A
  exact le_trans (binding_as_hard_dlog G q hq g ε A) (hdlog (pedersen_pmf G q A))
