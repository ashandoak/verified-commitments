import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import VerifiedCommitments.«commitment-scheme»
import VerifiedCommitments.dlog

-- temporary
import VerifiedCommitments.scratch_api
import VerifiedCommitments.«scratch-skip-bind»
-- set_option maxHeartbeats 0


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
      return ⟨g^m.val * h^r.val, r⟩,
    verify := fun h m c o => if c = g^m.val * h^o.val then 1 else 0  --verify h m c o g
  }

end Pedersen

namespace DLog

noncomputable def experiment
  (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] (hq_prime : Nat.Prime q)
    (A' : G → PMF (ZMod q)) : PMF (ZMod 2) :=
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
    let x ← PMF.uniformOfFinset nonzero_elements h_nonempty
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

end DLog

lemma binding_as_hard_dlog
  (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] [CancelMonoidWithZero (ZMod q)] (hq_prime : Nat.Prime q) (ε : ENNReal)
    (G_card_q : Fintype.card G = q)
    (hg_gen : orderOf g = Fintype.card G)
    (A : G → PMF (Adversary.guess (ZMod q) G (ZMod q))) :
    comp_binding_game' (Pedersen.scheme G g q hq_prime) A 1 ≤ DLog.experiment G g q hq_prime (DLog.adversary' G q A) 1 := by
  simp only [DLog.experiment, comp_binding_game', Pedersen.scheme, DLog.adversary']
  simp only [bind_pure_comp, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not, ne_eq,
    bind_map_left, ite_not, map_bind]
  congr! 5 with x ⟨c, m, m', o, o'⟩
  simp
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
    (∀ (A : G → PMF (ZMod q)), DLog.experiment G g q hq_prime A 1 ≤ ε) →
    (∀ (A : G → PMF (Adversary.guess (ZMod q) G (ZMod q))),
    comp_binding_game' (Pedersen.scheme G g q hq_prime) A 1 ≤ ε) := by
  intro G _ _ _ _ g q _ _ hq_prime ε G_card_q hg_gen hdlog A
  exact le_trans (binding_as_hard_dlog G g q hq_prime ε G_card_q hg_gen A) (hdlog (DLog.adversary' G q A))




-- Define the multiplicative subset of Z_q (Z_q without 0)
def ZModMult (q : ℕ) [NeZero q] := {a : ZMod q // a ≠ 0}

-- Helper function to extract the value from ZModMult
def val {q : ℕ} [NeZero q] (a : ZModMult q) : ZMod q := a.val


variable {G: Type} [Fintype G] [Group G]
variable (q : ℕ) [Fact (Nat.Prime q)]
variable (G_card_q : Fintype.card G = q)
variable (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)
include G_card_q
include g_gen_G

lemma ordg_eq_q : orderOf g = q := by
  have h_card_zpow : Fintype.card (Subgroup.zpowers g) = orderOf g := Fintype.card_zpowers
    -- zpowers g has the same cardinality as G since g generates G
  have h_card_eq : Fintype.card (Subgroup.zpowers g) = Fintype.card G := by
      -- Every element of G is in zpowers g, so they're in bijection
    have : Function.Bijective (Subtype.val : Subgroup.zpowers g → G) := by
      constructor
      · exact Subtype.val_injective
      · intro x
        use ⟨x, g_gen_G x⟩
    exact Fintype.card_of_bijective this
  rw [← h_card_zpow, h_card_eq, G_card_q]

lemma exp_bij (a : ZModMult q) (m : ZMod q) : Function.Bijective fun (r : ZMod q) => g^((m + (val a) * r : ZMod q).val : ℤ) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  simp [G_card_q]
  intro y
  obtain ⟨k, hk⟩ := g_gen_G y
  simp only at hk
  simp only

  let k' : ZMod q := (k : ZMod q)
  have hk' : g ^ (k'.val : ℤ) = y := by
    rw [←hk]
    simp only [ZMod.natCast_val]
    rw [ZMod.coe_intCast]
    rw [← G_card_q]
    rw [@zpow_mod_card]

  let a_unit := Units.mk0 (a.val : ZMod q) a.2
  let r : ZMod q := (a_unit⁻¹ : ZMod q) * (k' - m)
  have h_mod : (m + a_unit * r) = k' := by
    subst r
    rw [IsUnit.mul_inv_cancel_left (Exists.intro a_unit rfl) (k' - m)]
    simp

  have h_pow : g^((m + a_unit * r).val : ℤ) = y := by
    rw [←hk']
    subst r
    rw [h_mod]

  rw [←ZMod.cast_eq_val] at h_pow -- Transfer ↑ and .val back to .cast
  exact Exists.intro (r) h_pow

lemma pedersen_uniform_for_fixed_a
   {a : ZMod q} (ha : a ≠ 0) (m : ZMod q) [DecidableEq G] (c : G) :
   (Finset.card { t : ZMod q | g ^ ((m + a * t : ZMod q).val : ℤ) = c }) / (Finset.card ( (⊤ : Finset G) ) : ℚ)
   = 1 / (Fintype.card G) := by
    have h_bij := exp_bij q G_card_q g g_gen_G ⟨a, ha⟩ m
    have h_card : Finset.card { t : ZMod q | g ^ ((m + a * t : ZMod q).val : ℤ) = c } = 1 := by
      rw [Finset.card_eq_one]
      obtain ⟨r, hr⟩ := h_bij.surjective c
      use r
      ext t
      simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ht
        have : g ^ ((m + a * t : ZMod q).val : ℤ) = g ^ ((m + a * r : ZMod q).val : ℤ) := by
          rw [ht, ← hr]
          simp only [val]
        exact h_bij.injective this
      · intro ht
        rw [ht, ← hr]
        simp only [val]
    rw [h_card]
    exact rfl

lemma pedersen_uniform_for_fixed_a'
  {a : ZMod q} (ha : a ≠ 0) (m : ZMod q) [DecidableEq G] (c : G) :
  Finset.card { r : ZMod q | c = g ^ m.val * (g ^ a.val) ^ r.val } = 1 := by
    have h_ratio := pedersen_uniform_for_fixed_a q G_card_q g g_gen_G ha m c
    have h_card : Finset.card { t : ZMod q | g ^ ((m + a * t : ZMod q).val : ℤ) = c } = 1 := by
      have h_pos : (0 : ℚ) < Finset.card (⊤ : Finset G) := by simp; exact Fintype.card_pos
      have h_eq : (Finset.card { t : ZMod q | g ^ ((m + a * t : ZMod q).val : ℤ) = c } : ℚ) =
             (Finset.card (⊤ : Finset G) : ℚ) / (Fintype.card G : ℚ) := by
        grind --only [= Finset.card_univ, usr Finset.card_filter_le, cases Or]
      have h_top : Finset.card (⊤ : Finset G) = Fintype.card G := by rfl
      have : (Finset.card { t : ZMod q | g ^ ((m + a * t : ZMod q).val : ℤ) = c } : ℚ) = (1 : ℚ) := by
        grind
      exact Nat.cast_injective (R := ℚ) this
    convert h_card using 2
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have key : g ^ ((m + a * t).val : ℤ) = g ^ m.val * (g ^ a.val) ^ t.val := by
      have : (g ^ m.val * (g ^ a.val) ^ t.val : G) = g ^ m.val * g ^ (a.val * t.val) := by
        rw [← pow_mul]
      rw [this]
      rw [← pow_add]
      have h_order : orderOf g = q := by
        · expose_names; exact ordg_eq_q q G_card_q g g_gen_G
      have h_val_eq : (m + a * t).val = (m.val + a.val * t.val) % q := by
        have h_eq : (m + a * t : ZMod q) = ((m.val + a.val * t.val) : ℕ) := by
          simp only [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id', id_eq, Nat.cast_mul]
        rw [h_eq, ZMod.val_natCast]
      rw [h_val_eq]
      show g ^ (((m.val + a.val * t.val) % q : ℕ) : ℤ) = g ^ (m.val + a.val * t.val : ℕ)
      rw [← zpow_natCast]
      have : (g : G) ^ (((m.val + a.val * t.val) % q : ℕ) : ℤ) = g ^ ((m.val + a.val * t.val : ℕ) : ℤ) := by
        have : ((m.val + a.val * t.val : ℕ) : ℤ) % (orderOf g : ℤ) = ((m.val + a.val * t.val) % q : ℕ) := by
          grind
        rw [← this, zpow_mod_orderOf]
      assumption
    rw [key, eq_comm]


-- Temporary?
variable [IsCyclic G] [DecidableEq G] (hq_prime : Nat.Prime q)

-- This is presumably a more convenient approach rather than including the do-block directly in a the type of pedersen_commitment_uniform
noncomputable def generate_a : PMF $ ZMod q :=
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
    return a

-- lemma sum_indicator_uniform {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] (h : (Finset.filter p Finset.univ).card = 1) :
--   ∑' (x : α), if p x then (↑(Fintype.card α))⁻¹ else 0 = (↑(Fintype.card α))⁻¹ := by
--     sorry


lemma pedersen_commitment_uniform' (m : ZMod q) [DecidableEq G] (c : G) :
  (PMF.bind (generate_a q hq_prime)
    (fun a => PMF.bind (PMF.uniformOfFintype (ZMod q))
      (fun r => PMF.pure (g^m.val * (g^a.val)^r.val)))) c = 1 / Fintype.card G := by
      -- The key insight: for each non-zero a, the inner distribution is uniform over G
      -- We'll show that the result doesn't depend on which a we sample
      have h_uniform_inner : ∀ (a : ZMod q), a ≠ 0 →
        (PMF.bind (PMF.uniformOfFintype (ZMod q))
          (fun r => PMF.pure (g^m.val * (g^a.val)^r.val))) c = 1 / Fintype.card G := by
        intro a ha
        rw [PMF.bind_apply]
        conv_lhs => arg 1; ext r; rw [PMF.pure_apply]
        simp only [PMF.uniformOfFintype_apply, ZMod.card]
        -- Need to show: ∑' r, (1/q) * (if c = g^m.val * (g^a.val)^r.val then 1 else 0) = 1 / |G|
        -- Since |G| = q, this reduces to showing the sum of indicators equals 1
        rw [ENNReal.tsum_mul_left, G_card_q, one_div]
        -- Now need to show: q^{-1} * (sum of indicators) = q^{-1}
        -- Equivalently: sum of indicators = 1
        -- Convert to finset sum
        rw [tsum_eq_sum (s := {r : ZMod q | c = g ^ m.val * (g ^ a.val) ^ r.val}.toFinset)]
        swap
        · simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and,
          ite_eq_right_iff, one_ne_zero, imp_false, imp_self, implies_true]--intro r hr
        -- The sum equals the cardinality
        trans ((q : ENNReal)⁻¹ * ↑{r : ZMod q | c = g ^ m.val * (g ^ a.val) ^ r.val}.toFinset.card)
        · congr 1
          trans (∑ b ∈ {r : ZMod q | c = g ^ m.val * (g ^ a.val) ^ r.val}.toFinset, (1 : ENNReal))
          · apply Finset.sum_congr rfl
            intro b hb
            simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hb
            simp [hb]
          · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [Set.toFinset_card]
        -- Now use pedersen_uniform_for_fixed_a to show the cardinality is 1
        -- The cardinality of the set is 1, so q^{-1} * 1 = q^{-1}
        have h_card : Fintype.card {r : ZMod q | c = g ^ m.val * (g ^ a.val) ^ r.val} = 1 := by
          have h_finset : ({r : ZMod q | c = g ^ m.val * (g ^ a.val) ^ r.val} : Set (ZMod q)).toFinset.card = 1 := by
            convert pedersen_uniform_for_fixed_a' q G_card_q g g_gen_G ha m c using 2
            ext r
            simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
          have : Fintype.card {r : ZMod q | c = g ^ m.val * (g ^ a.val) ^ r.val} =
                 ({r : ZMod q | c = g ^ m.val * (g ^ a.val) ^ r.val} : Set (ZMod q)).toFinset.card := by
            simp only [Set.toFinset_card]
          grind only
        simp_all

      -- Now use bind_skip_const' since the inner bind always gives the same distribution
      have h_uniform_inner_gen : ∀ (a : ZMod q) (c' : G), a ≠ 0 →
        (PMF.bind (PMF.uniformOfFintype (ZMod q))
          (fun r => PMF.pure (g^m.val * (g^a.val)^r.val))) c' = 1 / Fintype.card G := by
        intro a c' ha
        -- This is the same proof as h_uniform_inner but for c' instead of c
        rw [PMF.bind_apply]
        conv_lhs => arg 1; ext r; rw [PMF.pure_apply]
        simp only [PMF.uniformOfFintype_apply, ZMod.card]
        rw [ENNReal.tsum_mul_left, G_card_q, one_div]
        rw [tsum_eq_sum (s := {r : ZMod q | c' = g ^ m.val * (g ^ a.val) ^ r.val}.toFinset)]
        swap
        · intro r hr
          simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hr
          simp [hr]
        trans ((q : ENNReal)⁻¹ * ↑{r : ZMod q | c' = g ^ m.val * (g ^ a.val) ^ r.val}.toFinset.card)
        · congr 1
          trans (∑ b ∈ {r : ZMod q | c' = g ^ m.val * (g ^ a.val) ^ r.val}.toFinset, (1 : ENNReal))
          · apply Finset.sum_congr rfl
            intro b hb
            simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hb
            simp [hb]
          · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [Set.toFinset_card]
        have h_card : Fintype.card {r : ZMod q | c' = g ^ m.val * (g ^ a.val) ^ r.val} = 1 := by
          have h_finset : ({r : ZMod q | c' = g ^ m.val * (g ^ a.val) ^ r.val} : Set (ZMod q)).toFinset.card = 1 := by
            convert pedersen_uniform_for_fixed_a' q G_card_q g g_gen_G ha m c' using 2
            ext r
            simp [Set.mem_toFinset]
          have : Fintype.card {r : ZMod q | c' = g ^ m.val * (g ^ a.val) ^ r.val} =
                 ({r : ZMod q | c' = g ^ m.val * (g ^ a.val) ^ r.val} : Set (ZMod q)).toFinset.card := by
            simp only [Set.toFinset_card]
          rw [this, h_finset]
        rw [h_card]
        simp
      have h_const : ∀ a, a ∈ ((Finset.univ : Finset (ZMod q)).erase 0) →
        (PMF.bind (PMF.uniformOfFintype (ZMod q))
          (fun r => PMF.pure (g^m.val * (g^a.val)^r.val))) = PMF.uniformOfFintype G := by
        intro a ha
        ext c'
        simp [Finset.mem_erase] at ha
        rw [h_uniform_inner_gen a c' ha]
        simp [PMF.uniformOfFintype_apply]
      rw [generate_a]
      rw [bind_pure_comp]
      rw [id_map']
      -- The bind of uniformOfFinset with a function that's constant on the finset equals that constant
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
      have : (PMF.uniformOfFinset nonzero_elements h_nonempty).bind
          (fun a => (PMF.uniformOfFintype (ZMod q)).bind fun r => PMF.pure (g^m.val * (g^a.val)^r.val)) =
        PMF.uniformOfFintype G := by
        ext x
        rw [PMF.bind_apply]
        simp only [PMF.uniformOfFinset_apply]
        trans (∑' a, (if a ∈ nonzero_elements then (nonzero_elements.card : ENNReal)⁻¹ * (PMF.uniformOfFintype G) x else 0))
        · apply tsum_congr
          intro a
          by_cases ha : a ∈ nonzero_elements
          · simp only [ha, ite_true]
            rw [h_const a ha]
          · simp only [ha, ite_false, zero_mul]
        · rw [tsum_eq_sum (s := nonzero_elements)]
          · have : ∑ b ∈ nonzero_elements, (if b ∈ nonzero_elements then (nonzero_elements.card : ENNReal)⁻¹ * (PMF.uniformOfFintype G) x else 0) =
                   ∑ b ∈ nonzero_elements, (nonzero_elements.card : ENNReal)⁻¹ * (PMF.uniformOfFintype G) x := by
              apply Finset.sum_congr rfl
              intro b hb
              simp only [hb, ite_true]
            rw [this, Finset.sum_const, nsmul_eq_mul, PMF.uniformOfFintype_apply]
            -- Goal: nonzero_elements.card * ((nonzero_elements.card)⁻¹ * (Fintype.card G)⁻¹) = (Fintype.card G)⁻¹
            calc (nonzero_elements.card : ENNReal) * ((nonzero_elements.card : ENNReal)⁻¹ * (Fintype.card G : ENNReal)⁻¹)
              _ = ((nonzero_elements.card : ENNReal) * (nonzero_elements.card : ENNReal)⁻¹) * (Fintype.card G : ENNReal)⁻¹ := by
                ring_nf
              _ = 1 * (Fintype.card G : ENNReal)⁻¹ := by
                congr 1
                apply ENNReal.mul_inv_cancel
                · simp
                  exact Finset.Nonempty.ne_empty h_nonempty
                · exact ENNReal.natCast_ne_top _
              _ = (Fintype.card G : ENNReal)⁻¹ := by rw [one_mul]
          · intro a ha
            simp [ha]
      conv_lhs => rw [this]
      simp [PMF.uniformOfFintype_apply]



lemma pedersen_commitment_uniform (m : ZMod q) [DecidableEq G] (c : G) :
  (do
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
    let r ← PMF.uniformOfFintype (ZMod q)
    return g^m.val * (g^a.val)^r.val : PMF G) c = 1 / Fintype.card G := by
      sorry


theorem Pedersen.perfect_hiding : ∀ (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
  (q : ℕ) [NeZero q] (hq_prime : Nat.Prime q),
  perfect_hiding (Pedersen.scheme G g q hq_prime) := by
    intros G _ _ _ _ g q _ hq_prime
    simp only [Pedersen.scheme, _root_.perfect_hiding, do_commit]
    simp only [bind_pure_comp, Functor.map_map, bind_map_left]
    intro m m' c
    rw [bind, Functor.map]
    simp only [PMF]
    rw [Monad.toBind, PMF.instMonad]

    sorry


-- Collection of uniform distrbutions and need to choose uniformly among them
-- Seems that this is the work of a bind to map across two distributions
