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


-- Incomplete
theorem Pedersen.perfect_hiding : ∀ (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
  (q : ℕ) [NeZero q] (hq_prime : Nat.Prime q),
  perfect_hiding (Pedersen.scheme G g q hq_prime) := by
  intro G _ _ _ _ g q _ hq_prime
  simp [_root_.perfect_hiding, do_commit, Pedersen.scheme]
  -- unfold _root_.perfect_hiding
  -- intros m m' c
  -- unfold do_commit
  -- unfold Pedersen.scheme
  congr! with m m' c o o'
  sorry



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
    have h_ordg : orderOf g = q := by
      apply orderOf_eq_prime
      · rw [←G_card_q]
        apply pow_card_eq_one
      have g_ne_one : g ≠ 1 := by
        by_contra hg
        subst hg
        rw [Subgroup.zpowers_one_eq_bot] at g_gen_G
        simp_rw [Subgroup.mem_bot] at g_gen_G
        have card_G_one : Fintype.card G = 1 := by
          rw [Fintype.card_eq_one_iff]
          subst hk G_card_q
          simp_all only [implies_true, exists_const]
        rw [card_G_one] at G_card_q
        have q_prime : Nat.Prime q := Fact.out
        have : 1 < q := Nat.Prime.one_lt (Fact.out)
        grind
      exact g_ne_one
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

-- lemma pedersen_uniform_for_fixed_a'
--   {a : ZMod q} (ha : a ≠ 0) (h : G) (m : ZMod q) [DecidableEq G] (c : G) :
-- CommitmentScheme.commit h m) c = 1/q := by sorry--

-- Temporary?
variable [IsCyclic G] [DecidableEq G] (hq_prime : Nat.Prime q)

lemma pedersen_commitment_uniform (m : ZMod q) [DecidableEq G] (c : G) :
  (do
    let h ← (Pedersen.scheme G g q hq_prime).setup
    let r ← PMF.uniformOfFintype (ZMod q)
    return g^m.val * h^r.val : PMF G) c = 1 / Fintype.card G := by sorry
