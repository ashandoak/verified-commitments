import VerifiedCommitments.CommitmentScheme
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.OrderOfElement
import VerifiedCommitments.ZModUtil
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Algebra.Field.ZMod
import VerifiedCommitments.MapPMFBijection
import VerifiedCommitments.cryptolib
import Mathlib.Tactic

namespace Pedersen

/- ========================================
   PUBLIC PARAMETERS
   ======================================== -/

class PedersenScheme (G : Type) extends
  Fintype G, Group G, IsCyclic G where
  [decidable_G : DecidableEq G]
  q : ℕ
  [neZero_q : NeZero q]
  prime_q : Nat.Prime q
  g : G
  card_eq : Fintype.card G = q
  gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g

-- Make instances available
variable {G : Type} [params : PedersenScheme G]
instance : DecidableEq G := params.decidable_G
instance : Fact (Nat.Prime params.q) := ⟨params.prime_q⟩

/- ========================================
   CORE LEMMAS
   ======================================== -/

lemma ordg_eq_q : orderOf params.g = params.q := by
  have h_card_zpow : Fintype.card (Subgroup.zpowers params.g) = orderOf params.g := Fintype.card_zpowers
  have h_card_eq : Fintype.card (Subgroup.zpowers params.g) = Fintype.card G := by
    have : Function.Bijective (Subtype.val : Subgroup.zpowers params.g → G) := by
      constructor
      · exact Subtype.val_injective
      · intro x
        use ⟨x, params.gen_G x⟩
    exact Fintype.card_of_bijective this
  rw [← h_card_zpow, h_card_eq, params.card_eq]


/- ========================================
   SCHEME DEFINITION
   ======================================== -/

noncomputable def setup : PMF (G × (ZMod params.q)) :=
  PMF.bind (PMF.uniformOfFintype (ZModMult params.q)) (fun a => return ⟨params.g^(val a).val, val a⟩)

noncomputable def commit (h : G) (m : ZMod params.q) : PMF (G × (ZMod params.q)) :=
  PMF.bind (PMF.uniformOfFintype (ZMod params.q)) (fun r => return ⟨params.g^m.val * h^r.val, r⟩)

def verify (h : G) (m : ZMod params.q) (c : G) (o : ZMod params.q) : ZMod 2 :=
  if c = params.g^m.val * h^o.val then 1 else 0

noncomputable def scheme : CommitmentScheme (ZMod params.q) G (ZMod params.q) G :=
  {
    setup := setup,
    commit := commit,
    verify := verify
  }

noncomputable def generate_a : PMF (ZModMult params.q) := PMF.uniformOfFintype (ZModMult params.q)

/- ========================================
   DLOG EXPERIMENT
   ======================================== -/

section DLog

noncomputable def experiment (A : G → PMF (ZMod params.q)) : PMF (ZMod 2) :=
  PMF.bind scheme.setup (fun h =>
  PMF.bind (A h.1) (fun x' => pure (if params.g^x'.val = params.g^(h.2).val then 1 else 0)))

noncomputable def constructDlogAdversary
      (A : G → PMF (Adversary.guess (ZMod params.q) G (ZMod params.q)))
      (h : G) : PMF (ZMod params.q) :=
    PMF.bind (A h) (fun guess =>
      if guess.o ≠ guess.o' then
        return ((guess.m - guess.m') * (guess.o' - guess.o)⁻¹)
      else
        PMF.uniformOfFintype (ZMod params.q))

end DLog

/- ========================================
   HIDING PROPERTY
   ======================================== -/

section Hiding

lemma exp_bij (a : ZModMult params.q) (m : ZMod params.q) : Function.Bijective fun (r : ZMod params.q) =>
    params.g^((m + (val a) * r : ZMod params.q).val : ℤ) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  simp [params.card_eq]
  intro c
  obtain ⟨k, hk⟩ := params.gen_G c
  simp only at hk
  simp only

  let z : ZMod params.q := (k : ZMod params.q)
  have hk : params.g ^ (z.val : ℤ) = c := by
    simp only [ZMod.natCast_val]
    rw [←hk]
    rw [ZMod.coe_intCast]
    rw [← params.card_eq]
    rw [@zpow_mod_card]

  let a_inv : ZMod params.q := (val a)⁻¹
  let r : ZMod params.q := a_inv * (z - m)

  have h_mod : (m + val a * r) = z := by
    subst r a_inv
    rw [←mul_assoc, mul_inv_cancel₀, one_mul]
    · exact add_sub_cancel m z
    · exact ZModMult.coe_ne_zero a

  have h_pow : params.g^((m + val a * r).val : ℤ) = c := by
    rw [←hk]
    subst r
    rw [h_mod]

  rw [←ZMod.cast_eq_val] at h_pow -- Transfer ↑ and .val back to .cast
  exact Exists.intro (r) h_pow

noncomputable def expEquiv (a : ZModMult params.q) (m : ZMod params.q) : ZMod params.q ≃ G :=
Equiv.ofBijective (fun (r : ZMod params.q) => params.g^((m + (val a) * r : ZMod params.q).val : ℤ)) (exp_bij a m)

lemma expEquiv_unfold (a : ZModMult params.q) (m r : ZMod params.q) :
    expEquiv a m r = params.g^m.val * (params.g^(val a).val)^r.val := by
  unfold expEquiv
  simp only [Equiv.ofBijective, Equiv.coe_fn_mk]

  have h_pow : (params.g^(val a).val)^r.val = params.g^((val a).val * r.val) := (pow_mul params.g (val a).val r.val).symm
  rw [h_pow]

  simp only [← zpow_natCast]
  rw [← zpow_add]

  have hord : orderOf params.g = params.q := ordg_eq_q
  conv_lhs => rw [← zpow_mod_orderOf, hord]

  suffices h : (((m + (val a) * r).val : ℤ) % ↑params.q) = ((m.val : ℤ) + ((val a).val * r.val : ℤ)) % ↑params.q by
    conv_rhs => rw [← zpow_mod_orderOf, hord]
    rw [h]
    congr 1

  conv_lhs => rw [ZMod.val_add, ZMod.val_mul]
  norm_cast
  rw [Nat.add_mod, Nat.mul_mod]
  simp

lemma bij_uniform_for_fixed_a (a : ZModMult params.q) (m : ZMod params.q) :
    PMF.map (expEquiv a m) (PMF.uniformOfFintype (ZMod params.q)) = (PMF.uniformOfFintype G) := by
  · expose_names;
    exact map_uniformOfFintype_equiv (expEquiv a m)

lemma bij_uniform_for_uniform_a (m : ZMod params.q) :
    (PMF.bind (generate_a)
    (fun a => PMF.map (expEquiv a m) (PMF.uniformOfFintype (ZMod params.q)))) = (PMF.uniformOfFintype G) := by
  unfold generate_a
  apply bind_skip_const'
  intro a
  · expose_names; exact bij_uniform_for_fixed_a a m

lemma pedersen_commitment_uniform (m : ZMod params.q) (c : G) :
    (PMF.map Prod.fst (PMF.bind (generate_a : PMF (ZModMult params.q))
    (fun a => commit (params.g^(val a).val) m )) c) =
    ((1 : ENNReal) / (Fintype.card G)) := by
  unfold commit
  simp only [PMF.map_bind, pure, PMF.pure_map]
  have h_eq : (PMF.bind (generate_a : PMF (ZModMult params.q))
                (fun a => PMF.bind (PMF.uniformOfFintype (ZMod params.q))
                  (fun r => PMF.pure (params.g^m.val * (params.g^(val a).val)^r.val)))) =
              (PMF.bind (generate_a : PMF (ZModMult params.q))
                (fun a => PMF.map (expEquiv a m) (PMF.uniformOfFintype (ZMod params.q)))) := by
    apply bind_skip'
    intro a
    ext x
    simp only [PMF.bind_apply, PMF.map_apply, PMF.pure_apply, PMF.uniformOfFintype_apply]
    congr 1; ext r
    by_cases h : x = params.g^m.val * (params.g^(val a).val)^r.val
    · simp only [h, ↓reduceIte]
      rw [← expEquiv_unfold a m r]
      simp
    · simp only [h, ↓reduceIte]
      have : x ≠ expEquiv a m r := by
        intro contra
        rw [expEquiv_unfold a m r] at contra
        exact h contra
      simp [this]
  rw [h_eq]
  rw [bij_uniform_for_uniform_a m]
  simp [PMF.uniformOfFintype_apply]

theorem perfect_hiding : Commitment.perfect_hiding (@scheme G params) := by
  unfold Commitment.perfect_hiding
  intros m m' c
  unfold Commitment.do_commit Pedersen.scheme
  simp only []
  unfold Pedersen.setup Pedersen.commit
  simp only [PMF.bind_bind]
  have h_lhs : ((PMF.uniformOfFintype (ZModMult params.q)).bind fun a =>
                  PMF.bind (pure (params.g^(val a).val, val a)) fun h =>
                    (PMF.uniformOfFintype (ZMod params.q)).bind fun r =>
                      PMF.bind (pure (params.g^m.val * h.1^r.val, r)) fun commit =>
                        pure commit.1) c = 1 / Fintype.card G := by
    simp only [pure, PMF.pure_bind]
    convert pedersen_commitment_uniform m c using 2
    unfold generate_a Pedersen.commit
    simp only [PMF.map_bind, pure, PMF.pure_map]
  have h_rhs : ((PMF.uniformOfFintype (ZModMult params.q)).bind fun a =>
                  PMF.bind (pure (params.g^(val a).val, val a)) fun h =>
                    (PMF.uniformOfFintype (ZMod params.q)).bind fun r =>
                      PMF.bind (pure (params.g^m'.val * h.1^r.val, r)) fun commit =>
                        pure commit.1) c = 1 / Fintype.card G := by
    simp only [pure, PMF.pure_bind]
    convert pedersen_commitment_uniform m' c using 2
    unfold generate_a Pedersen.commit
    simp only [PMF.map_bind, pure, PMF.pure_map]
  rw [h_lhs, h_rhs]

end Hiding

/- ========================================
   BINDING PROPERTY
   ======================================== -/

section Binding

lemma binding_implies_dlog (a : ZMod params.q) (guess : Adversary.guess (ZMod params.q) G (ZMod params.q)) :
    let h := params.g ^ a.val
    let verify := fun (m : ZMod params.q) (c : G) (o : ZMod params.q) => if c = params.g^m.val * h^o.val then (1 : ZMod 2) else 0
    (verify guess.m guess.c guess.o = 1 ∧ verify guess.m' guess.c guess.o' = 1 ∧ guess.m ≠ guess.m') →
    (guess.o ≠ guess.o' → params.g^(((guess.m - guess.m') * (guess.o' - guess.o)⁻¹).val) = h) := by
  intro h verify ⟨h1, h2, m_ne⟩ o_ne

  simp only [verify] at h1 h2
  split at h1 <;> split at h2
  case' isTrue.isTrue c_eq1 c_eq2 =>
    simp only [h] at c_eq1 c_eq2

    have collision : params.g^guess.m.val * (params.g^a.val)^guess.o.val = params.g^guess.m'.val * (params.g^a.val)^guess.o'.val := by
      rw [← c_eq1, c_eq2]

    conv_lhs at collision => arg 2; rw [← pow_mul]
    conv_rhs at collision => arg 2; rw [← pow_mul]
    rw [← pow_add, ← pow_add] at collision

    have h_coprime : (guess.o' - guess.o).val.Coprime params.q := by
      cases' Nat.coprime_or_dvd_of_prime params.prime_q (guess.o' - guess.o).val with h_cop h_dvd
      · exact Nat.coprime_comm.mp h_cop
      · exfalso
        have h_zero : guess.o' - guess.o = 0 := by
          rw [← ZMod.val_eq_zero]
          have h_mod_zero : (guess.o' - guess.o).val % params.q = 0 := Nat.mod_eq_zero_of_dvd h_dvd
          have h_val_bound : (guess.o' - guess.o).val < params.q := ZMod.val_lt (guess.o' - guess.o)
          exact Nat.eq_zero_of_dvd_of_lt h_dvd h_val_bound
        exact o_ne.symm (eq_of_sub_eq_zero h_zero)

    have h_congr_nat : guess.m.val + a.val * guess.o.val ≡ guess.m'.val + a.val * guess.o'.val [MOD params.q] := by
      simpa [ordg_eq_q] using (pow_eq_pow_iff_modEq.mp collision)

    have h_zmod : (guess.m + a * guess.o : ZMod params.q) = (guess.m' + a * guess.o' : ZMod params.q) := by
      have eq_cast : ((guess.m.val + a.val * guess.o.val : ℕ) : ZMod params.q) =
                    ((guess.m'.val + a.val * guess.o'.val : ℕ) : ZMod params.q) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr h_congr_nat
      simp at eq_cast
      exact eq_cast

    have h_lin : a * (guess.o' - guess.o) = guess.m - guess.m' := by grind

    have h_unit : guess.o' - guess.o ≠ 0 := sub_ne_zero.mpr o_ne.symm

    have h_solve_x : a = (guess.m - guess.m') * (guess.o' - guess.o)⁻¹ := by
      calc a = a * 1                                 := by rw [mul_one]
        _ = a * ((guess.o' - guess.o) * (guess.o' - guess.o)⁻¹)              := by
          haveI : Fact (Nat.Prime params.q) := ⟨params.prime_q⟩
          rw [← one_mul a]
          congr 1
          have h_field_inv : (guess.o' - guess.o) * (guess.o' - guess.o)⁻¹ = 1 := by
            apply Field.mul_inv_cancel
            exact h_unit
          exact h_field_inv.symm
        _ = (a * (guess.o' - guess.o)) * (guess.o' - guess.o)⁻¹              := by rw [mul_assoc]
        _ = (guess.m - guess.m') * (guess.o' - guess.o)⁻¹                    := by rw [h_lin]

    have h_congr_final : ((guess.m - guess.m') * (guess.o' - guess.o)⁻¹).val ≡ a.val [MOD params.q] := by
      have h1 : (((guess.m - guess.m') * (guess.o' - guess.o)⁻¹).val : ZMod params.q) = (guess.m - guess.m') * (guess.o' - guess.o)⁻¹ :=
        ZMod.natCast_zmod_val ((guess.m - guess.m') * (guess.o' - guess.o)⁻¹)
      have h2 : (a.val : ZMod params.q) = a := ZMod.natCast_zmod_val a
      rw [← ZMod.natCast_eq_natCast_iff]
      rw [h1, h2]
      exact h_solve_x.symm

    have h_eq : params.g ^ ((guess.m - guess.m') * (guess.o' - guess.o)⁻¹).val = params.g ^ a.val :=
      (pow_eq_pow_iff_modEq.mpr (by rwa [ordg_eq_q]))

    rw [h_eq]
  all_goals contradiction


lemma binding_as_hard_dlog
    (A : G → PMF (Adversary.guess (ZMod params.q) G (ZMod params.q))) : -- Pedersen adversary
    haveI : Fact (Nat.Prime params.q) := ⟨params.prime_q⟩;
    Commitment.comp_binding_game (scheme) A 1 ≤ experiment (constructDlogAdversary A) 1 := by
  haveI : Fact (Nat.Prime params.q) := ⟨params.prime_q⟩
  -- Unfold definitions
  unfold Commitment.comp_binding_game experiment constructDlogAdversary
  simp only [Pedersen.scheme, Pedersen.setup, Pedersen.verify]

  -- Expand the bind applications
  rw [PMF.bind_apply, PMF.bind_apply]

  -- Both sum over the same type: G × ZMod q (the pairs from setup)
  -- We need pointwise inequality
  apply ENNReal.tsum_le_tsum
  intro ⟨h, a⟩

  -- Key observation: setup only returns pairs (g^x.val, x)
  -- So if h ≠ g^a.val, the probability of this pair is 0 and inequality holds trivially
  by_cases h_case : h = params.g^a.val

  · -- Case: h = g^a.val (pair is in support of setup)
    subst h_case  -- Replace h with g^a.val everywhere

    -- Now we have h = g^a.val as needed!
    apply mul_le_mul_right

    -- Now compare the inner probabilities
    -- Continue with the proof that was already working
    -- First, use bind associativity on RHS to flatten the nested binds
    conv_rhs => rw [PMF.bind_bind]

    -- Now both have structure: (A (g^a.val)).bind (fun guess => ...) 1
    -- Expand the bind application
    rw [PMF.bind_apply, PMF.bind_apply]

    -- Now both are sums over Adversary.guess
    apply ENNReal.tsum_le_tsum
    intro guess

    apply mul_le_mul_right

    -- For each guess, show:
    -- (if [binding succeeds] then pure 1 else pure 0) 1 ≤
    -- ((if o≠o' then pure x' else uniform).bind (λ x'. pure (if g^x'=g^a then 1 else 0))) 1

    simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not, ne_eq, ite_not,
      PMF.bind_apply, tsum_fintype]
    rw [@DFunLike.ite_apply]
    split_ifs with h₁ h₂

    · -- Case 1: h₁ (binding) AND h₂ (o = o')
      -- This is the contradiction case: o = o' but binding succeeds
      exfalso
      obtain ⟨eq1, eq2, m_ne⟩ := h₁
      -- Since h₂: o = o', we have (g^a.val)^o.val = (g^a.val)^o'.val
      have ho_eq : (params.g^a.val)^guess.o.val = (params.g^a.val)^guess.o'.val := by
        rw [h₂]
      -- So: g^m.val * (g^a.val)^o.val = g^m'.val * (g^a.val)^o.val
      have collision : params.g^guess.m.val * (params.g^a.val)^guess.o.val = params.g^guess.m'.val * (params.g^a.val)^guess.o.val := by
        calc params.g^guess.m.val * (params.g^a.val)^guess.o.val
            = guess.c := eq1.symm
          _ = params.g^guess.m'.val * (params.g^a.val)^guess.o'.val := eq2
          _ = params.g^guess.m'.val * (params.g^a.val)^guess.o.val := by rw [← ho_eq]
      -- Cancel (g^a.val)^o.val from both sides
      have g_eq : params.g^guess.m.val = params.g^guess.m'.val := mul_right_cancel collision

      have h_congr : guess.m.val ≡ guess.m'.val [MOD params.q] := by
        simpa [ordg_eq_q] using (pow_eq_pow_iff_modEq.mp g_eq)
      -- Therefore m = m' in ZMod q
      have m_eq : guess.m = guess.m' := by
        have eq_cast : ((guess.m.val : ℕ) : ZMod params.q) = ((guess.m'.val : ℕ) : ZMod params.q) :=
          ZMod.natCast_eq_natCast_iff guess.m.val guess.m'.val params.q |>.mpr h_congr
        simp at eq_cast
        exact eq_cast
      exact m_ne m_eq

    · -- Case 2: Binding succeeds (h₁) AND o ≠ o' (¬h₂)
      -- This is the main case where we use binding_implies_dlog
      have h_o_ne : guess.o ≠ guess.o' := h₂
      let x' := (guess.m - guess.m') * (guess.o' - guess.o)⁻¹

      -- Convert h₁ to the form expected by binding_implies_dlog
      have h₁' : (let h := params.g^a.val;
                  let verify := fun m c o => if c = params.g^m.val * h^o.val then (1 : ZMod 2) else 0;
                  verify guess.m guess.c guess.o = 1 ∧ verify guess.m' guess.c guess.o' = 1 ∧ guess.m ≠ guess.m') := by
        obtain ⟨eq1, eq2, m_ne⟩ := h₁
        simp only []
        refine ⟨?_, ?_, m_ne⟩
        · split
          · rfl
          · contradiction
        · split
          · rfl
          · contradiction

      -- By binding_implies_dlog, g^x'.val = g^a.val
      have h_dlog : params.g^x'.val = params.g^a.val := by
        apply binding_implies_dlog a guess h₁' h_o_ne

      -- The RHS is a sum over a single-element distribution (pure x')
      -- The sum includes the term for x = x', which equals 1
      have h_term : (PMF.pure x') x' * (PMF.pure (if params.g^x'.val = params.g^a.val then (1 : ZMod 2) else 0)) (1 : ZMod 2) = 1 := by
        rw [PMF.pure_apply, PMF.pure_apply]
        simp only [h_dlog]
        norm_num
      have h_zero : ∀ x ∈ Finset.univ, x ∉ ({x'} : Finset (ZMod params.q)) →
                    (PMF.pure x') x * (PMF.pure (if params.g^x.val = params.g^a.val then (1 : ZMod 2) else 0)) (1 : ZMod 2) = 0 := by
        intros x _ hx
        rw [PMF.pure_apply]
        simp only [Finset.mem_singleton] at hx
        simp [hx]
      have h_sum_ge : (PMF.pure x') x' * (PMF.pure (if params.g^x'.val = params.g^a.val then (1 : ZMod 2) else 0)) (1 : ZMod 2) ≤
                      ∑ x, (PMF.pure x') x * (PMF.pure (if params.g^x.val = params.g^a.val then (1 : ZMod 2) else 0)) (1 : ZMod 2) := by
        rw [← Finset.sum_subset (Finset.subset_univ {x'}) h_zero]
        simp only [Finset.sum_singleton]
        rfl
      calc (PMF.pure (1 : ZMod 2)) (1 : ZMod 2)
          = 1 := by rw [PMF.pure_apply]; norm_num
        _ = (PMF.pure x') x' * (PMF.pure (if params.g^x'.val = params.g^a.val then (1 : ZMod 2) else 0)) (1 : ZMod 2) := h_term.symm
        _ ≤ ∑ x, (PMF.pure x') x * (PMF.pure (if params.g^x.val = params.g^a.val then (1 : ZMod 2) else 0)) (1 : ZMod 2) := h_sum_ge

    · -- Case 3: Binding fails (¬h₁) AND o = o' (h✝)
      show (PMF.pure (0 : ZMod 2)) (1 : ZMod 2) ≤ _
      rw [PMF.pure_apply]
      norm_num

    · -- Case 4: Binding fails (¬h₁) AND o ≠ o' (¬h✝)
      show (PMF.pure (0 : ZMod 2)) (1 : ZMod 2) ≤ _
      rw [PMF.pure_apply]
      norm_num

  · -- Case neg: h ≠ g^a.val (pair is NOT in support)
    -- Setup only returns pairs of the form (g^x.val, x)
    -- So if h ≠ g^a.val, then (h, a) has probability 0 in the setup distribution
    -- Therefore both sides are 0 * something = 0, and 0 ≤ 0
    have h_prob_zero : ((PMF.uniformOfFintype (ZModMult params.q)).bind fun a_mult => PMF.pure (params.g^(val a_mult).val, val a_mult)) (h, a) = 0 := by
      rw [PMF.bind_apply, tsum_fintype]
      apply Finset.sum_eq_zero
      intros a_mult _
      rw [PMF.pure_apply, PMF.uniformOfFintype_apply]
      split_ifs with h_eq
      · -- If (h, a) = (g^(val a_mult).val, val a_mult)
        -- Then h = g^(val a_mult).val and a = val a_mult
        exfalso
        have eq_h : h = params.g^(val a_mult).val := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
        have eq_a : a = val a_mult := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
        rw [← eq_a] at eq_h
        exact h_case eq_h
      · simp
    change ((PMF.uniformOfFintype (ZModMult params.q)).bind fun a_mult => PMF.pure (params.g^(val a_mult).val, val a_mult)) (h, a) * _ ≤
           ((PMF.uniformOfFintype (ZModMult params.q)).bind fun a_mult => PMF.pure (params.g^(val a_mult).val, val a_mult)) (h, a) * _
    rw [h_prob_zero]
    simp only [zero_mul, le_refl]

theorem computational_binding :
  ∀ (ε : ENNReal),
    (∀ (A' : G → PMF (ZMod params.q)), experiment A' 1 ≤ ε) →
    (∀ (A : G → PMF (Adversary.guess (ZMod params.q) G (ZMod params.q))),
    Commitment.comp_binding_game (@scheme G params) A 1 ≤ ε) := by
  intro ε A' A
  exact le_trans (binding_as_hard_dlog A) (A' (constructDlogAdversary A))

end Binding

end Pedersen
