import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.ZMod.Basic
import VerifiedCommitments.ProofUtils
import VerifiedCommitments.CommitmentScheme

namespace DLog

noncomputable section

-- Modification of Attack game and advantage as specified in Boneh 10.4 to account for check between generated x and x'
def attack_game (G : Type) [Group G] (q : ℕ) [NeZero q] (g : G) (A : G → PMF (ZMod q)) : PMF (ZMod 2) :=
do
  let x ← PMF.uniformOfFintype (ZMod q)
  let x' ← A (g^x.val)
  pure (if x = x' then 1 else 0)

-- The advantage of an attacker A in the DLog problem
-- attack_game returns a PMF ()
def advantage (G : Type) [Group G] (q : ℕ) [NeZero q] (g : G) (A : G → PMF (ZMod q)) : ENNReal := attack_game G q g A 1

noncomputable def experiment
  (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] (hq_prime : Nat.Prime q)
    (A' : G → PMF (ZMod q)) : PMF (ZMod 2) :=
  do
    let x ← PMF.uniformOfFinset (nonzeroElements hq_prime).1 (nonzeroElements hq_prime).2
    let h := g^x.val
    let x' ← A' h
    pure (if g^x'.val = h then 1 else 0)

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

  noncomputable def adversary'
    (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G]
      (q : ℕ) [NeZero q]
      (A' : G → PMF (Adversary.guess (ZMod q) G (ZMod q)))
      (h : G) : PMF (ZMod q) :=
    do
      let guess ← A' h
      if guess.o ≠ guess.o' then
        return ((guess.m - guess.m') * (guess.o' - guess.o)⁻¹)
      else
        PMF.uniformOfFintype (ZMod q)
end
end DLog
