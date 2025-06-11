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


lemma binding_as_hard_dlog : ∀ (G : Type) [Fintype G] [Group G] [DecidableEq G]
  (q : ℕ) [NeZero q] (hq : q > 1) (g : G) (ε : ENNReal),
  ∀ (A : G → PMF (G × ZMod q × ZMod q × ZMod q × ZMod q)),
  ∃ (A' : G → PMF (ZMod q)),
  comp_binding_game (Pedersen.scheme G q hq g) A 1 ≤ DLog_game G q hq g A' 1 := by
  intro G _ _ _ q _ hq g ε A
  let A' := fun h => do
    let (c, m, m', o, o') ← A h
    if o ≠ o' then
      return ((m - m') * (o' - o)⁻¹)
    else
      PMF.uniformOfFintype (ZMod q)
  use A'
  unfold DLog_game
  unfold comp_binding_game
  unfold Pedersen.scheme
  simp

theorem Pedersen.computational_binding : ∀ (G : Type) [Fintype G] [Group G] [DecidableEq G]
  (q : ℕ) [NeZero q] (hq : q > 1) (g : G) (ε : ENNReal),
  (∀ (A : G → PMF (ZMod q)), DLog_game G q hq g A 1 ≤ ε) →
  (∀ (A : G → PMF (G × ZMod q × ZMod q × ZMod q × ZMod q)),
   comp_binding_game (Pedersen.scheme G q hq g) A 1 ≤ ε) := by
  intro G _ _ _ q _ hq g ε hdlog A
  have h₀ : ∃ A₀, comp_binding_game (Pedersen.scheme G q hq g) A 1 ≤ DLog_game G q hq g A₀ 1 :=
    binding_as_hard_dlog G q hq g ε A
  obtain ⟨A₀, hA₀⟩ := h₀
  have h₁ : DLog_game G q hq g A₀ 1 ≤ ε := hdlog A₀
  exact le_trans hA₀ h₁
