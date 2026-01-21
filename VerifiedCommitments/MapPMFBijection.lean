-- formalmethods.io © 2025 by William DeMeo is licensed under CC BY-NC-SA 4.0
-- https://formalmethods.io/

import Mathlib.Probability.Distributions.Uniform

open Classical

lemma map_uniformOfFintype_equiv
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) :
    PMF.map e (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := by
  ext b
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply]
  have h_equiv : (∑' (a : α), if b = e a then (↑(Fintype.card α : ENNReal))⁻¹ else 0) =
                 (∑' (a : α), if a = e.symm b then (↑(Fintype.card α))⁻¹ else 0) := by
    congr 1
    ext a
    by_cases h : b = e a
    · rw [if_pos h, if_pos]
      rw [←Equiv.symm_apply_apply e a]
      rw [h]
    · rw [if_neg h, if_neg]
      intro contra
      subst contra
      rw [Equiv.apply_symm_apply e] at h
      apply h
      rfl
  rw [h_equiv]
  rw [tsum_ite_eq]
  congr 1
  rw [Fintype.card_congr e]
