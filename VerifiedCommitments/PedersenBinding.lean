import VerifiedCommitments.PedersenScheme
import VerifiedCommitments.dlog
import Mathlib.Tactic
import VerifiedCommitments.«scratch-skip-bind»

namespace Pedersen

-- Helper lemma: if binding succeeds, then either o = o' or we can extract the discrete log
lemma binding_implies_dlog
  (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] [CancelMonoidWithZero (ZMod q)] (hq_prime : Nat.Prime q)
    (G_card_q : Fintype.card G = q)
    (hg_gen : orderOf g = Fintype.card G)
    (a : ZMod q) (guess : Adversary.guess (ZMod q) G (ZMod q)) :
  let h := g ^ a.val
  let verify := fun (m : ZMod q) (c : G) (o : ZMod q) => if c = g^m.val * h^o.val then (1 : ZMod 2) else 0
  (verify guess.m guess.c guess.o = 1 ∧ verify guess.m' guess.c guess.o' = 1 ∧ guess.m ≠ guess.m') →
  (guess.o ≠ guess.o' → g^(((guess.m - guess.m') * (guess.o' - guess.o)⁻¹).val) = h) := by
  intro h verify ⟨h1, h2, m_ne⟩ o_ne
  -- From h1: guess.c = g^(guess.m).val * h^(guess.o).val
  -- From h2: guess.c = g^(guess.m').val * h^(guess.o').val
  simp only [verify] at h1 h2
  split at h1 <;> split at h2
  case' isTrue.isTrue c_eq1 c_eq2 =>
    simp only [h] at c_eq1 c_eq2

    have collision : g^guess.m.val * (g^a.val)^guess.o.val = g^guess.m'.val * (g^a.val)^guess.o'.val := by
      rw [← c_eq1, c_eq2]

    conv_lhs at collision => arg 2; rw [← pow_mul]
    conv_rhs at collision => arg 2; rw [← pow_mul]
    rw [← pow_add, ← pow_add] at collision

    have h_coprime : (guess.o' - guess.o).val.Coprime q := by
      cases' Nat.coprime_or_dvd_of_prime hq_prime (guess.o' - guess.o).val with h_cop h_dvd
      · exact Nat.coprime_comm.mp h_cop
      · exfalso
        have h_zero : guess.o' - guess.o = 0 := by
          rw [← ZMod.val_eq_zero]
          have h_mod_zero : (guess.o' - guess.o).val % q = 0 := Nat.mod_eq_zero_of_dvd h_dvd
          have h_val_bound : (guess.o' - guess.o).val < q := ZMod.val_lt (guess.o' - guess.o)
          exact Nat.eq_zero_of_dvd_of_lt h_dvd h_val_bound
        exact o_ne.symm (eq_of_sub_eq_zero h_zero)

    have h_ord : orderOf g = q := by
      rw [← G_card_q]; exact hg_gen

    have h_congr_nat : guess.m.val + a.val * guess.o.val ≡ guess.m'.val + a.val * guess.o'.val [MOD q] := by
      simpa [h_ord] using (pow_eq_pow_iff_modEq.mp collision)

    have h_zmod : (guess.m + a * guess.o : ZMod q) = (guess.m' + a * guess.o' : ZMod q) := by
      have eq_cast : ((guess.m.val + a.val * guess.o.val : ℕ) : ZMod q) =
                    ((guess.m'.val + a.val * guess.o'.val : ℕ) : ZMod q) :=
        (ZMod.eq_iff_modEq_nat _).mpr h_congr_nat
      simp at eq_cast
      exact eq_cast

    have h_lin : a * (guess.o' - guess.o) = guess.m - guess.m' := by grind

    have h_unit : guess.o' - guess.o ≠ 0 := sub_ne_zero.mpr o_ne.symm

    have h_solve_x : a = (guess.m - guess.m') * (guess.o' - guess.o)⁻¹ := by
      calc a = a * 1                                 := by rw [mul_one]
        _ = a * ((guess.o' - guess.o) * (guess.o' - guess.o)⁻¹)              := by
          haveI : Fact (Nat.Prime q) := ⟨hq_prime⟩
          rw [← one_mul a]
          congr 1
          have h_field_inv : (guess.o' - guess.o) * (guess.o' - guess.o)⁻¹ = 1 := by
            apply Field.mul_inv_cancel
            exact h_unit
          exact h_field_inv.symm
        _ = (a * (guess.o' - guess.o)) * (guess.o' - guess.o)⁻¹              := by rw [mul_assoc]
        _ = (guess.m - guess.m') * (guess.o' - guess.o)⁻¹                    := by rw [h_lin]

    have h_congr_final : ((guess.m - guess.m') * (guess.o' - guess.o)⁻¹).val ≡ a.val [MOD q] := by
      have h1 : (((guess.m - guess.m') * (guess.o' - guess.o)⁻¹).val : ZMod q) = (guess.m - guess.m') * (guess.o' - guess.o)⁻¹ :=
        ZMod.natCast_zmod_val ((guess.m - guess.m') * (guess.o' - guess.o)⁻¹)
      have h2 : (a.val : ZMod q) = a := ZMod.natCast_zmod_val a
      rw [← ZMod.eq_iff_modEq_nat]
      rw [h1, h2]
      exact h_solve_x.symm

    have h_eq : g ^ ((guess.m - guess.m') * (guess.o' - guess.o)⁻¹).val = g ^ a.val :=
      (pow_eq_pow_iff_modEq.mpr (by rwa [h_ord]))

    rw [h_eq]
  all_goals contradiction

lemma binding_as_hard_dlog
  (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] [CancelMonoidWithZero (ZMod q)] (hq_prime : Nat.Prime q)
    (G_card_q : Fintype.card G = q)
    (hg_gen : orderOf g = Fintype.card G)
    (A : G → PMF (Adversary.guess (ZMod q) G (ZMod q))) : -- Pedersen adversary
    haveI : Fact (Nat.Prime q) := ⟨hq_prime⟩;
    Commitment.comp_binding_game (Pedersen.scheme G g q hq_prime) A 1 ≤ DLog.experiment G g q hq_prime (DLog.adversary' G q A) 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  -- Unfold definitions
  unfold Commitment.comp_binding_game DLog.experiment DLog.adversary'
  simp only [Pedersen.scheme, Pedersen.setup, Pedersen.verify]

  -- Expand the bind applications
  rw [PMF.bind_apply, PMF.bind_apply]

  -- Both sum over the same type: G × ZMod q (the pairs from setup)
  -- We need pointwise inequality
  apply ENNReal.tsum_le_tsum
  intro ⟨h, a⟩

  -- Key observation: setup only returns pairs (g^x.val, x)
  -- So if h ≠ g^a.val, the probability of this pair is 0 and inequality holds trivially
  by_cases h_case : h = g^a.val

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
      have ho_eq : (g^a.val)^guess.o.val = (g^a.val)^guess.o'.val := by
        rw [h₂]
      -- So: g^m.val * (g^a.val)^o.val = g^m'.val * (g^a.val)^o.val
      have collision : g^guess.m.val * (g^a.val)^guess.o.val = g^guess.m'.val * (g^a.val)^guess.o.val := by
        calc g^guess.m.val * (g^a.val)^guess.o.val
            = guess.c := eq1.symm
          _ = g^guess.m'.val * (g^a.val)^guess.o'.val := eq2
          _ = g^guess.m'.val * (g^a.val)^guess.o.val := by rw [← ho_eq]
      -- Cancel (g^a.val)^o.val from both sides
      have g_eq : g^guess.m.val = g^guess.m'.val := mul_right_cancel collision
      -- Since g is a generator, this means m.val ≡ m'.val (mod q)
      have h_ord : orderOf g = q := by rw [← G_card_q]; exact hg_gen
      have h_congr : guess.m.val ≡ guess.m'.val [MOD q] := by
        simpa [h_ord] using (pow_eq_pow_iff_modEq.mp g_eq)
      -- Therefore m = m' in ZMod q
      have m_eq : guess.m = guess.m' := by
        have eq_cast : ((guess.m.val : ℕ) : ZMod q) = ((guess.m'.val : ℕ) : ZMod q) :=
          ZMod.natCast_eq_natCast_iff guess.m.val guess.m'.val q |>.mpr h_congr
        simp at eq_cast
        exact eq_cast
      exact m_ne m_eq

    · -- Case 2: Binding succeeds (h₁) AND o ≠ o' (¬h₂)
      -- This is the main case where we use binding_implies_dlog
      have h_o_ne : guess.o ≠ guess.o' := h₂
      let x' := (guess.m - guess.m') * (guess.o' - guess.o)⁻¹

      -- Convert h₁ to the form expected by binding_implies_dlog
      have h₁' : (let h := g^a.val;
                  let verify := fun m c o => if c = g^m.val * h^o.val then (1 : ZMod 2) else 0;
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
      have h_dlog : g^x'.val = g^a.val := by
        apply binding_implies_dlog G g q hq_prime G_card_q hg_gen a guess h₁' h_o_ne

      -- The RHS is a sum over a single-element distribution (pure x')
      -- The sum includes the term for x = x', which equals 1
      have h_term : (PMF.pure x') x' * (PMF.pure (if g^x'.val = g^a.val then (1 : ZMod 2) else 0)) (1 : ZMod 2) = 1 := by
        rw [PMF.pure_apply, PMF.pure_apply]
        simp only [h_dlog]
        norm_num
      have h_zero : ∀ x ∈ Finset.univ, x ∉ ({x'} : Finset (ZMod q)) →
                    (PMF.pure x') x * (PMF.pure (if g^x.val = g^a.val then (1 : ZMod 2) else 0)) (1 : ZMod 2) = 0 := by
        intros x _ hx
        rw [PMF.pure_apply]
        simp only [Finset.mem_singleton] at hx
        simp [hx]
      have h_sum_ge : (PMF.pure x') x' * (PMF.pure (if g^x'.val = g^a.val then (1 : ZMod 2) else 0)) (1 : ZMod 2) ≤
                      ∑ x, (PMF.pure x') x * (PMF.pure (if g^x.val = g^a.val then (1 : ZMod 2) else 0)) (1 : ZMod 2) := by
        rw [← Finset.sum_subset (Finset.subset_univ {x'}) h_zero]
        simp only [Finset.sum_singleton]
        rfl
      calc (PMF.pure (1 : ZMod 2)) (1 : ZMod 2)
          = 1 := by rw [PMF.pure_apply]; norm_num
        _ = (PMF.pure x') x' * (PMF.pure (if g^x'.val = g^a.val then (1 : ZMod 2) else 0)) (1 : ZMod 2) := h_term.symm
        _ ≤ ∑ x, (PMF.pure x') x * (PMF.pure (if g^x.val = g^a.val then (1 : ZMod 2) else 0)) (1 : ZMod 2) := h_sum_ge

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
    have h_prob_zero : ((PMF.uniformOfFintype (ZModMult q)).bind fun a_mult => PMF.pure (g^(val a_mult).val, val a_mult)) (h, a) = 0 := by
      rw [PMF.bind_apply, tsum_fintype]
      apply Finset.sum_eq_zero
      intros a_mult _
      rw [PMF.pure_apply, PMF.uniformOfFintype_apply]
      split_ifs with h_eq
      · -- If (h, a) = (g^(val a_mult).val, val a_mult)
        -- Then h = g^(val a_mult).val and a = val a_mult
        exfalso
        have eq_h : h = g^(val a_mult).val := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
        have eq_a : a = val a_mult := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
        rw [← eq_a] at eq_h
        exact h_case eq_h
      · simp
    change ((PMF.uniformOfFintype (ZModMult q)).bind fun a_mult => PMF.pure (g^(val a_mult).val, val a_mult)) (h, a) * _ ≤
           ((PMF.uniformOfFintype (ZModMult q)).bind fun a_mult => PMF.pure (g^(val a_mult).val, val a_mult)) (h, a) * _
    rw [h_prob_zero]
    simp only [zero_mul, le_refl]


theorem computational_binding :
  ∀ (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] [CancelMonoidWithZero (ZMod q)] [Fact (Nat.Prime q)] (hq_prime : (Nat.Prime q)) (ε : ENNReal)
    (G_card_q : Fintype.card G = q)
    (hg_gen : orderOf g = Fintype.card G),
    (∀ (A : G → PMF (ZMod q)), DLog.experiment G g q hq_prime A 1 ≤ ε) →
    (∀ (A : G → PMF (Adversary.guess (ZMod q) G (ZMod q))),
    ∃ hq_prime : Nat.Prime q, Commitment.comp_binding_game (Pedersen.scheme G g q hq_prime) A 1 ≤ ε) := by
  intro G _ _ _ _ g q _ _ _ hq_prime ε G_card_q hg_gen hdlog A
  use hq_prime
  exact le_trans (binding_as_hard_dlog G g q hq_prime G_card_q hg_gen A) (hdlog (DLog.adversary' G q A))
end Pedersen
