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

lemma exp_bij (a : ZModMult q) (m : ZMod q) : Function.Bijective fun (r : ZMod q) => g^((m + (val a) * r : ZMod q).val : ℤ) := by
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

-- TODO: Try to use the counting proof below as a step to the probablistic proof
-- TODO: Is there a lemma somewhere that states given a bijection applied to a uniform input then the result is uniform?
  -- For any bijection from Zq to the group of order q?

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



-- for fixed aa ∈ {1, ... , q − 1}, and for any m ∈ Zq, if t ← Zq, then  g^m*h^r is uniformly distributed over G
-- We can do this by proving t ↦ g^m*h^r is a bijection - see exp_bij above
lemma pedersen_uniform_for_fixed_a_probablistic
  (a : ZMod q) (ha : a ≠ 0) (m : ZMod q) [DecidableEq G] (c' : G) :
  (PMF.map commit.c ((Pedersen.scheme G g q hq_prime).commit (g^a.val) m)) c' = 1 / (Fintype.card G) := by -- Should be using ZModUtils?
    unfold Pedersen.scheme
    rw [G_card_q]
    simp only [bind_pure_comp, one_div]
    have h_bij := exp_bij q G_card_q g g_gen_G ⟨a, ha⟩ m
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
