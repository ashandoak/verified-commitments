-- From cryptolib licensed under Apache 2.0
-- https://github.com/joeylupo/cryptolib

import Mathlib.Probability.ProbabilityMassFunction.Monad

variable {α β : Type}

lemma bind_skip' (p : PMF α) (f g : α → PMF β) : (∀ (a : α), f a = g a) → p.bind f = p.bind g := by
  intro ha
  ext
  simp only [PMF.bind_apply, ha]

lemma bind_skip_const' (pa : PMF α) (pb : PMF β) (f : α → PMF β) : (∀ (a : α), f a = pb) → pa.bind f = pb := by
  intros ha
  ext
  simp
  simp_rw [ha]
  simp [ENNReal.tsum_mul_right]
