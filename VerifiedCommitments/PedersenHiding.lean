import VerifiedCommitments.PedersenScheme
import VerifiedCommitments.ZModUtil

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
instance {C O : Type} [Fintype C] [Fintype O] : Fintype (C × O) :=
  Fintype.ofEquiv (C × O) {
    toFun := fun ⟨c, o⟩ => ⟨c, o⟩
    invFun := fun ⟨c, o⟩ => ⟨c, o⟩
    left_inv := fun _ => rfl
    right_inv := fun x => by cases x; rfl
  }

noncomputable def expEquiv (a : ZModMult q) (m : ZMod q) : ZMod q ≃ G :=
Equiv.ofBijective (fun (r : ZMod q) => g^((m + (val a) * r : ZMod q).val : ℤ)) (exp_bij' q G_card_q g g_gen_G a m)


#check expEquiv q G_card_q g g_gen_G

lemma expEquiv_unfold (a : ZModMult q) (m r : ZMod q) :
  expEquiv q G_card_q g g_gen_G a m r = g^m.val * (g^(val a).val)^r.val := by
  unfold expEquiv
  simp only [Equiv.ofBijective, Equiv.coe_fn_mk]

  have h_pow : (g^(val a).val)^r.val = g^((val a).val * r.val) := (pow_mul g (val a).val r.val).symm
  rw [h_pow]

  simp only [← zpow_natCast]
  rw [← zpow_add]

  have hord : orderOf g = q := ordg_eq_q q G_card_q g g_gen_G
  conv_lhs => rw [← zpow_mod_orderOf, hord]

  suffices h : (((m + (val a) * r).val : ℤ) % ↑q) = ((m.val : ℤ) + ((val a).val * r.val : ℤ)) % ↑q by
    conv_rhs => rw [← zpow_mod_orderOf, hord]
    rw [h]
    congr 1

  conv_lhs => rw [ZMod.val_add, ZMod.val_mul]
  norm_cast
  rw [Nat.add_mod, Nat.mul_mod]
  simp


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

lemma bind_eq_map
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) :
    PMF.map e (PMF.uniformOfFintype α) = PMF.bind (PMF.uniformOfFintype α) (fun a => pure (e a)) := by
    rfl

lemma bind_eq_map' : ∀ (fixed_a : ZModMult q) (fixed_m : ZMod q),
  PMF.map (expEquiv q G_card_q g g_gen_G fixed_a fixed_m) (PMF.uniformOfFintype (ZMod q)) =
  PMF.bind (PMF.uniformOfFintype (ZMod q)) (fun a => PMF.pure (expEquiv q G_card_q g g_gen_G fixed_a fixed_m a))
  := by
  intros
  exact rfl


-- Temporary?
-- variable [IsCyclic G] [DecidableEq G] (hq_prime : Nat.Prime q)

noncomputable def generate_a : PMF (ZModMult q) :=
  PMF.uniformOfFintype (ZModMult q)

lemma bij_uniform_for_fixed_a (a : ZModMult q) (m : ZMod q) :
  PMF.map (expEquiv q G_card_q g g_gen_G a m) (PMF.uniformOfFintype (ZMod q)) = (PMF.uniformOfFintype G) := by
  · expose_names;
    exact map_uniformOfFintype_equiv q G_card_q g g_gen_G (expEquiv q G_card_q g g_gen_G a m)

lemma bij_uniform_for_uniform_a (m : ZMod q) :
  (PMF.bind (generate_a q)
    (fun a => PMF.map (expEquiv q G_card_q g g_gen_G a m) (PMF.uniformOfFintype (ZMod q)))) = (PMF.uniformOfFintype G) := by
  unfold generate_a
  apply bind_skip_const'
  intro a
  · expose_names; exact bij_uniform_for_fixed_a q G_card_q g g_gen_G a m


lemma pedersen_uniform_for_fixed_a_probablistic' (a : ZModMult q) (m : ZMod q) :
  (Pedersen.commit G g q (g^(val a).val) m) =
  PMF.uniformOfFintype (Commit G (ZMod q)) := by
  rw [← bij_uniform_for_fixed_a q G_card_q g g_gen_G a m]
  -- Unfold Pedersen.commit
  unfold Pedersen.commit
  simp only [bind_pure_comp]
  -- Now both sides are PMF.map over uniformOfFintype (ZMod q)
  congr 1
  funext r
  exact (expEquiv_unfold q G_card_q g g_gen_G a m r).symm


lemma bij_fixed_a_equiv_pedersen_commit (m : ZMod q) (a : ZModMult q) :
  PMF.map (expEquiv q G_card_q g g_gen_G a m) (PMF.uniformOfFintype (ZMod q)) =
  (Pedersen.commit G g q (g^(val a).val) m) := by
  rw [bij_uniform_for_fixed_a q G_card_q g g_gen_G a m]
  rw [← pedersen_uniform_for_fixed_a_probablistic' q G_card_q g g_gen_G hq_prime a m]


lemma bij_random_a_equiv_pedersen_commit (m : ZMod q) :
  PMF.bind (generate_a q)
    (fun a => PMF.map (expEquiv q G_card_q g g_gen_G a m) (PMF.uniformOfFintype (ZMod q))) =
  PMF.bind (generate_a q)
    (fun a => (Pedersen.commit G g q g^(val a).val) m)) := by
  congr 1
  funext a
  exact bij_fixed_a_equiv_pedersen_commit q G_card_q g g_gen_G hq_prime m a


-- for fixed aa ∈ {1, ... , q − 1}, and for any m ∈ Zq, if t ← Zq, then  g^m*h^r is uniformly distributed over G
-- We can do this by proving t ↦ g^m*h^r is a bijection - see exp_bij above
-- g^((m + (val a) * r : ZMod q).val : ℤ)
lemma pedersen_uniform_for_fixed_a_probablistic
  (a : ZModMult q) (m : ZMod q) [DecidableEq G] (c' : G) :
  PMF.map Commit.c ((Pedersen.scheme G g q hq_prime).commit (g^(val a).val) m) c' = 1 / (Fintype.card G) := by sorry




-- lemma pedersen_commitment_uniform'' (m : ZMod q) [DecidableEq G] (c : G) :
--   (PMF.bind (generate_a q)
--     (fun a => PMF.bind (PMF.uniformOfFintype (ZMod q))
--       (fun r => PMF.pure (g^m.val * (g^((val a).val))^r.val)))) c = 1 / Fintype.card G := by
--       --have h_expEquiv : PMF.uniformOfFintype (ZMod q)).bind fun r ↦ PMF.pure (g ^ m.val * (g ^ (val a).val) ^ r.val
--       unfold generate_a
--       simp [PMF.bind_apply]
--       rw [tsum_fintype]
--       simp_rw [tsum_fintype]
--       conv_lhs => arg 1; arg 2; rw [←bind_eq_map' q G_card_q g g_gen_G a m] --do I need to first get a version of expEquiv and unfold to match the def?

--       sorry

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
