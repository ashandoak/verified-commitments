import VerifiedCommitments.PedersenScheme
import VerifiedCommitments.ZModUtil
import Mathlib -- Would like to trim down this import but the Units.mk0 (a.val : ZMod q) a.2 line is a problem

-- Temporary
import VerifiedCommitments.«scratch-skip-bind»


variable {G: Type} [Fintype G] [Group G]
variable (q : ℕ) [Fact (Nat.Prime q)]
variable (G_card_q : Fintype.card G = q)
variable (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)
include G_card_q
include g_gen_G

-- Temporary?
variable [IsCyclic G] [DecidableEq G] (hq_prime : Nat.Prime q)

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


lemma exp_bij' (a : ZModMult q) (m : ZMod q) : Function.Bijective fun (r : ZMod q) => g^((m + (val a) * r : ZMod q).val : ℤ) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  simp [G_card_q]
  intro c --So take any cc ∈ GG
  obtain ⟨k, hk⟩ := g_gen_G c
  simp only at hk
  simp only

  let z : ZMod q := (k : ZMod q) -- Since g is a generator we have c = g^z for some z ∈ Zq
  have hk' : g ^ (z.val : ℤ) = c := by
    rw [←hk]
    simp only [ZMod.natCast_val]
    rw [ZMod.coe_intCast]
    rw [← G_card_q]
    rw [@zpow_mod_card]

  -- we need g^m+a^r = g^z
  -- This is the case iff m + ar ≡ z (mod q)
  -- This is the case iff t ≡ a^−1 * (z − m) (mod q)
  let a_unit := Units.mk0 (a.val : ZMod q) a.2
  let r : ZMod q := (a_unit⁻¹ : ZMod q) * (z - m)
  have h_mod : (m + a_unit * r) = z := by
    subst r
    rw [IsUnit.mul_inv_cancel_left (Exists.intro a_unit rfl) (z - m)]
    simp

  have h_pow : g^((m + a_unit * r).val : ℤ) = c := by
    rw [←hk']
    subst r
    rw [h_mod]

  rw [←ZMod.cast_eq_val] at h_pow -- Transfer ↑ and .val back to .cast
  exact Exists.intro (r) h_pow


-- Fintype instance for commit
instance {C O : Type} [Fintype C] [Fintype O] : Fintype (commit C O) :=
  Fintype.ofEquiv (C × O) {
    toFun := fun ⟨c, o⟩ => ⟨c, o⟩
    invFun := fun ⟨c, o⟩ => ⟨c, o⟩
    left_inv := fun _ => rfl
    right_inv := fun x => by cases x; rfl
  }

noncomputable def expEquiv (a : ZModMult q) (m : ZMod q) : ZMod q ≃ G :=
Equiv.ofBijective (fun (r : ZMod q) => g^((m + (val a) * r : ZMod q).val : ℤ)) (exp_bij' q G_card_q g g_gen_G a m)

variable (a' : ZMod q) (ha' : (a'.val : ZMod q) ≠ 0) (m' : ZMod q)
variable (az : ZModMult q) (mz : ZMod q)
#check (expEquiv q G_card_q g g_gen_G az mz).toFun


open Classical -- needed here or α must be DecidableEq
/-! ### 2.  Mapping a uniform PMF through a bijection stays uniform -------------/
-- Courtesy of formalmethods.io
lemma map_uniformOfFintype_equiv
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) :
    PMF.map e (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := by
  -- Prove equality of PMFs by showing they assign the same probability to each element
  ext b
  -- Goal: (PMF.map e (uniformOfFintype α)) b = (uniformOfFintype β) b

  -- Step 1: Simplify the LHS using PMF.map_apply
  rw [PMF.map_apply]
  -- This gives us: ∑' (a : α), if b = e a then (uniformOfFintype α) a else 0

  -- Step 2: Simplify the uniform distribution on α
  simp only [PMF.uniformOfFintype_apply]
  -- Goal: ∑' (a : α), if b = e a then (↑(card α))⁻¹ else 0 = (↑(card β))⁻¹

  -- Step 3: The sum has exactly one non-zero term when a = e.symm b
  -- We can rewrite this as a sum over the singleton {e.symm b}
  have h_equiv : (∑' (a : α), if b = e a then (↑(Fintype.card α : ENNReal))⁻¹ else 0) =
                 (∑' (a : α), if a = e.symm b then (↑(Fintype.card α))⁻¹ else 0) := by
    congr 1
    ext a
    -- Show: (if b = e a then (↑(card α))⁻¹ else 0) = (if a = e.symm b then (↑(card α))⁻¹ else 0)
    by_cases h : b = e a
    · -- Case: b = e a
      rw [if_pos h, if_pos]
      -- Need to show a = e.symm b
      rw [←Equiv.symm_apply_apply e a]
      rw [h]
    · -- Case: b ≠ e a
      rw [if_neg h, if_neg]
      -- Need to show a ≠ e.symm b
      intro contra
      subst contra
      rw [Equiv.apply_symm_apply e] at h
      apply h
      rfl

  -- Step 4: Apply the equivalence and simplify
  rw [h_equiv]
  rw [tsum_ite_eq]
  -- Goal: (↑(card α))⁻¹ = (↑(card β))⁻¹

  -- Step 5: Use the fact that equivalent finite types have the same cardinality
  congr 1
  rw [Fintype.card_congr e]


lemma pedersen_uniform_for_fixed_a
   {a : ZMod q} (ha : a ≠ 0) (m : ZMod q) [DecidableEq G] (c : G) :
   (Finset.card { t : ZMod q | g ^ ((m + a * t : ZMod q).val : ℤ) = c }) / (Finset.card ( (⊤ : Finset G) ) : ℚ)
   = 1 / (Fintype.card G) := by
    let a_mult : ZModMult q := ⟨a, ha⟩
    let equiv := @expEquiv G _ _ q _ G_card_q g g_gen_G _ _ a_mult m
    have h_card : Finset.card { t : ZMod q | g ^ ((m + a * t : ZMod q).val : ℤ) = c } = 1 := by
      rw [Finset.card_eq_one]
      use equiv.symm c
      ext t
      simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and]
      have h_equiv_def : ∀ r, equiv r = g^((m + (val a_mult) * r : ZMod q).val : ℤ) := fun r => rfl
      have h_val_eq : val a_mult = a := rfl
      constructor
      · intro ht
        have : equiv t = c := by rw [h_equiv_def, h_val_eq, ht]
        rw [← this, Equiv.eq_symm_apply]
      · intro ht
        subst ht
        have : equiv (equiv.symm c) = c := Equiv.apply_symm_apply equiv c
        rw [h_equiv_def, h_val_eq] at this
        exact this
    rw [h_card]
    exact rfl

lemma pedersen_uniform_for_fixed_a'
  {a : ZMod q} (ha : a ≠ 0) (m : ZMod q) [DecidableEq G] (c : G) :
  Finset.card { r : ZMod q | c = g ^ m.val * (g ^ a.val) ^ r.val } = 1 := by
    let a_mult : ZModMult q := ⟨a, ha⟩
    let equiv := @expEquiv G _ _ q _ G_card_q g g_gen_G _ _ a_mult m
    have h_equiv_def : ∀ r, equiv r = g^((m + (val a_mult) * r : ZMod q).val : ℤ) := fun r => rfl
    have h_val_eq : val a_mult = a := rfl
    -- Show the goal using equiv
    suffices Finset.card { r : ZMod q | g ^ ((m + a * r : ZMod q).val : ℤ) = c } = 1 by
      convert this using 2
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have key : g ^ ((m + a * t).val : ℤ) = g ^ m.val * (g ^ a.val) ^ t.val := by
        have : (g ^ m.val * (g ^ a.val) ^ t.val : G) = g ^ m.val * g ^ (a.val * t.val) := by
          rw [← pow_mul]
        rw [this, ← pow_add]
        have h_order : orderOf g = q := ordg_eq_q q G_card_q g g_gen_G
        have h_val_eq_local : (m + a * t).val = (m.val + a.val * t.val) % q := by
          have h_eq : (m + a * t : ZMod q) = ((m.val + a.val * t.val) : ℕ) := by
            simp only [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id', id_eq, Nat.cast_mul]
          rw [h_eq, ZMod.val_natCast]
        rw [h_val_eq_local]
        show g ^ (((m.val + a.val * t.val) % q : ℕ) : ℤ) = g ^ (m.val + a.val * t.val : ℕ)
        rw [← zpow_natCast]
        have : (g : G) ^ (((m.val + a.val * t.val) % q : ℕ) : ℤ) = g ^ ((m.val + a.val * t.val : ℕ) : ℤ) := by
          have : ((m.val + a.val * t.val : ℕ) : ℤ) % (orderOf g : ℤ) = ((m.val + a.val * t.val) % q : ℕ) := by
            grind
          rw [← this, zpow_mod_orderOf]
        assumption
      constructor
      · intro h; rw [key, h]
      · intro h; rw [← key, h]
    -- Now prove the suffices goal
    rw [Finset.card_eq_one]
    use equiv.symm c
    ext t
    simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ht
      have : equiv t = c := by rw [h_equiv_def, h_val_eq, ht]
      rw [← this, Equiv.eq_symm_apply]
    · intro ht
      subst ht
      have : equiv (equiv.symm c) = c := Equiv.apply_symm_apply equiv c
      rw [h_equiv_def, h_val_eq] at this
      exact this

-- for fixed aa ∈ {1, ... , q − 1}, and for any m ∈ Zq, if t ← Zq, then  g^m*h^r is uniformly distributed over G
-- We can do this by proving t ↦ g^m*h^r is a bijection - see exp_bij above
lemma pedersen_uniform_for_fixed_a_probablistic
  (a : ZMod q) (ha : a ≠ 0) (m : ZMod q) [DecidableEq G] (c' : G) :
  (PMF.map commit.c ((Pedersen.scheme G g q hq_prime).commit (g^a.val) m)) c' = 1 / (Fintype.card G) := by -- Should be using ZModUtils?
    unfold Pedersen.scheme
    rw [G_card_q]
    simp only [bind_pure_comp, one_div]
    have h_bij := exp_bij' q G_card_q g g_gen_G ⟨a, ha⟩ m
    obtain ⟨r, hr⟩ := h_bij.surjective c'
    --subst hr
    --simp only [ne_eq, ZMod.natCast_val]
    rw [@PMF.monad_map_eq_map] -- PMF.map_apply (fun a_1 ↦ { c := g ^ m.val * (g ^ a.val) ^ a_1.val, o := a_1 })]
    conv_lhs => arg 1; rw [PMF.map, PMF.bind]
    simp only [Function.comp_apply, PMF.pure_apply, mul_ite, mul_one, mul_zero]
    have key : ∀ r, g ^ m.val * (g ^ a.val) ^ r.val = g^((m + a * r).val : ℤ) := by
      intro r
      -- This is the same calculation as in pedersen_uniform_for_fixed_a' line 129-147
      rw [← pow_mul]
      rw [← pow_add]
      have h_order : orderOf g = q := by
        · expose_names; exact ordg_eq_q q G_card_q g g_gen_G
      have h_val_eq : (m + a * r).val = (m.val + a.val * r.val) % q := by
        have h_eq : (m + a * r : ZMod q) = ((m.val + a.val * r.val) : ℕ) := by
          simp only [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id', id_eq, Nat.cast_mul]
        rw [h_eq, ZMod.val_natCast]
      rw [h_val_eq]
      show g ^ (m.val + a.val * r.val : ℕ) = g ^ (((m.val + a.val * r.val) % q : ℕ) : ℤ)
      rw [← zpow_natCast]
      have : (g : G) ^ (((m.val + a.val * r.val) % q : ℕ) : ℤ) = g ^ ((m.val + a.val * r.val : ℕ) : ℤ) := by
        have : ((m.val + a.val * r.val : ℕ) : ℤ) % (orderOf g : ℤ) = ((m.val + a.val * r.val) % q : ℕ) := by
          grind
        rw [← this, zpow_mod_orderOf]
      grind
    simp only [PMF.map_apply, PMF.uniformOfFintype_apply, ZMod.card]
    -- Apply the PMF to c'
    simp only [PMF.instFunLike]
    -- Simplify the outer tsum
    rw [tsum_fintype]
    -- Convert inner tsums
    simp_rw [tsum_fintype]
    -- Use Finset.sum_ite to separate the outer sum
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    -- Now we have: sum over {x | c' = x.c} of (sum over a_1 of ...)
    -- Swap the summation order
    rw [Finset.sum_comm]



    -- For each a_1, the inner sum has at most one non-zero term
    -- It's non-zero when x = commit.mk (g^...) a_1 AND c' = x.c
    classical
    have h_simplify : ∀ a_1 : ZMod q,
      (∑ x ∈ Finset.filter (fun (x : commit G (ZMod q)) => c' = x.c) Finset.univ,
        if x = { c := g^m.val * (g^a.val)^a_1.val, o := a_1 } then ((↑q : ENNReal)⁻¹) else (0 : ENNReal)) =
      (if c' = g^m.val * (g^a.val)^a_1.val then ((↑q : ENNReal)⁻¹) else (0 : ENNReal)) := by
      intro a_1
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h_rewrite : (∑ a_1 : ZMod q, ∑ x ∈ Finset.filter (fun (x : commit G (ZMod q)) => c' = x.c) Finset.univ,
        if x = ({ c := g^m.val * (g^a.val)^a_1.val, o := a_1 } : commit G (ZMod q)) then ((↑q : ENNReal)⁻¹) else (0 : ENNReal)) =
      (∑ a_1 : ZMod q, if c' = g^m.val * (g^a.val)^a_1.val then ((↑q : ENNReal)⁻¹) else (0 : ENNReal)) := by
      congr 1; ext a_1; exact h_simplify a_1
    rw [h_rewrite]
    -- Use the key lemma to rewrite
    have h_key_rewrite : (∑ a_1 : ZMod q, if c' = g^m.val * (g^a.val)^a_1.val then ((↑q : ENNReal)⁻¹) else (0 : ENNReal)) =
      (∑ a_1 : ZMod q, if c' = g^((m + a * a_1).val : ℤ) then ((↑q : ENNReal)⁻¹) else (0 : ENNReal)) := by
      congr 1; ext a_1; congr 1; rw [key]
    rw [h_key_rewrite]
    -- Now we have: sum over a_1 of (if c' = g^((m + a*a_1).val) then (↑q)⁻¹ else 0)
    -- By the bijection, exactly one a_1 satisfies this (namely r)
    -- First simplify hr - note that val ⟨a, ha⟩ = a by definition
    have hr_simplified : c' = g^((m + a * r).val : ℤ) := by
      have step1 : (fun r => g ^ ((m + val ⟨a, ha⟩ * r).val : ℤ)) r = g^((m + val ⟨a, ha⟩ * r).val : ℤ) := rfl
      have step2 : g^((m + val ⟨a, ha⟩ * r).val : ℤ) = g^((m + a * r).val : ℤ) := by simp only [val]
      rw [← step2, ← step1]
      exact hr.symm
    -- We need to show that exactly one value (r) makes the condition true
    have h_unique : ∀ a_1 : ZMod q, (c' = g^((m + a * a_1).val : ℤ)) ↔ a_1 = r := by
      intro a_1
      constructor
      · intro h
        have eq1 : g^((m + a * a_1).val : ℤ) = g^((m + a * r).val : ℤ) := by rw [← h, ← hr_simplified]
        have eq2 : g^((m + val ⟨a, ha⟩ * a_1).val : ℤ) = g^((m + val ⟨a, ha⟩ * r).val : ℤ) := by
          have : val ⟨a, ha⟩ = a := by simp only [val]
          simp only [this]
          exact eq1
        apply h_bij.injective
        exact eq2
      · intro h
        rw [h]
        exact hr_simplified
    -- Rewrite the sum using this unique characterization
    have h_sum_unique : (∑ a_1 : ZMod q, if c' = g^((m + a * a_1).val : ℤ) then ((↑q : ENNReal)⁻¹) else (0 : ENNReal)) =
        (∑ a_1 : ZMod q, if a_1 = r then ((↑q : ENNReal)⁻¹) else (0 : ENNReal)) := by
      congr 1; ext a_1; congr 1; rw [h_unique]
    rw [h_sum_unique]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]


-- Temporary?
variable [IsCyclic G] [DecidableEq G] (hq_prime : Nat.Prime q)

-- This is presumably a more convenient approach rather than including the do-block directly in a the type of pedersen_commitment_uniform
noncomputable def generate_a : PMF $ ZMod q :=
  do
    let a ← PMF.uniformOfFinset (nonzeroElements hq_prime).1 (nonzeroElements hq_prime).2
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

      have : (PMF.uniformOfFinset (nonzeroElements hq_prime).1 (nonzeroElements hq_prime).2).bind
          (fun a => (PMF.uniformOfFintype (ZMod q)).bind fun r => PMF.pure (g^m.val * (g^a.val)^r.val)) =
        PMF.uniformOfFintype G := by
        ext x
        rw [PMF.bind_apply]
        simp only [PMF.uniformOfFinset_apply]
        trans (∑' a, (if a ∈ (nonzeroElements hq_prime).1 then ((nonzeroElements hq_prime).1.card : ENNReal)⁻¹ * (PMF.uniformOfFintype G) x else 0))
        · apply tsum_congr
          intro a
          by_cases ha : a ∈ (nonzeroElements hq_prime).1
          · simp only [ha, ite_true]
            rw [h_const a ha]
          · simp only [ha, ite_false, zero_mul]
        · rw [tsum_eq_sum (s := (nonzeroElements hq_prime).1)]
          · have : ∑ b ∈ (nonzeroElements hq_prime).1, (if b ∈ (nonzeroElements hq_prime).1 then ((nonzeroElements hq_prime).1.card : ENNReal)⁻¹ * (PMF.uniformOfFintype G) x else 0) =
                   ∑ b ∈ (nonzeroElements hq_prime).1, ((nonzeroElements hq_prime).1.card : ENNReal)⁻¹ * (PMF.uniformOfFintype G) x := by
              apply Finset.sum_congr rfl
              intro b hb
              simp only [hb, ite_true]
            rw [this, Finset.sum_const, nsmul_eq_mul, PMF.uniformOfFintype_apply]
            -- Goal: (nonzeroElements hq_prime).1.card * (((nonzeroElements hq_prime).1.card)⁻¹ * (Fintype.card G)⁻¹) = (Fintype.card G)⁻¹
            calc ((nonzeroElements hq_prime).1.card : ENNReal) * (((nonzeroElements hq_prime).1.card : ENNReal)⁻¹ * (Fintype.card G : ENNReal)⁻¹)
              _ = (((nonzeroElements hq_prime).1.card : ENNReal) * ((nonzeroElements hq_prime).1.card : ENNReal)⁻¹) * (Fintype.card G : ENNReal)⁻¹ := by
                ring_nf
              _ = 1 * (Fintype.card G : ENNReal)⁻¹ := by
                congr 1
                apply ENNReal.mul_inv_cancel
                · simp
                  exact Finset.Nonempty.ne_empty (nonzeroElements hq_prime).2
                · exact ENNReal.natCast_ne_top _
              _ = (Fintype.card G : ENNReal)⁻¹ := by rw [one_mul]
          · intro a ha
            simp [ha]
      conv_lhs => rw [this]
      simp [PMF.uniformOfFintype_apply]



lemma pedersen_commitment_uniform (m : ZMod q) [DecidableEq G] (c : G) :
  (do
    let a ← PMF.uniformOfFinset (nonzeroElements hq_prime).1 (nonzeroElements hq_prime).2
    let r ← PMF.uniformOfFintype (ZMod q)
    return g^m.val * (g^a.val)^r.val : PMF G) c = 1 / Fintype.card G := by
      sorry

lemma bind_eq_map
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) :
    PMF.map e (PMF.uniformOfFintype α) = PMF.bind (PMF.uniformOfFintype α) (fun a => pure (e a)) := by
    rfl


lemma pedersen_commitment_uniform'' (m : ZMod q) [DecidableEq G] (c : G) :
  (PMF.bind (generate_a q hq_prime)
    (fun a => PMF.bind (PMF.uniformOfFintype (ZMod q))
      (fun r => PMF.pure (g^m.val * (g^a.val)^r.val)))) c = 1 / Fintype.card G := by
      conv_lhs => arg 1; arg 2; ext a; rw [←@bind_eq_map _ _ (fun r ↦ PMF.pure (g ^ m.val * (g ^ a.val) ^ r.val))]

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

