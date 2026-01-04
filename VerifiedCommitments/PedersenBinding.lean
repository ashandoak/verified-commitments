import VerifiedCommitments.PedersenScheme
import Mathlib.Tactic

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
    -- We have: g^m.val * h^o.val = g^m'.val * h^o'.val
    -- Substituting h = g^a.val:
    -- g^m.val * g^(a.val * o.val) = g^m'.val * g^(a.val * o'.val)
    -- g^(m.val + a.val * o.val) = g^(m'.val + a.val * o'.val)

    simp only [h] at c_eq1 c_eq2
    -- c_eq1: guess.c = g ^ guess.m.val * (g ^ a.val) ^ guess.o.val
    -- c_eq2: guess.c = g ^ guess.m'.val * (g ^ a.val) ^ guess.o'.val

    have collision : g^guess.m.val * (g^a.val)^guess.o.val = g^guess.m'.val * (g^a.val)^guess.o'.val := by
      rw [← c_eq1, c_eq2]

    -- Simplify (g^a.val)^o.val to g^(a.val * o.val)
    conv_lhs at collision => arg 2; rw [← pow_mul]
    conv_rhs at collision => arg 2; rw [← pow_mul]
    -- Combine: g^m.val * g^(a.val * o.val) = g^(m + a*o).val
    rw [← pow_add, ← pow_add] at collision

    -- From collision: g^(m.val + a.val*o.val) = g^(m'.val + a.val*o'.val)
    -- We need to extract a from this equation
    -- Strategy: show that a = (m - m') / (o' - o)

    -- First, rearrange the equation algebraically in ZMod q:
    -- m + a*o = m' + a*o' (as elements of ZMod q when viewed mod q)
    -- m - m' = a*o' - a*o
    -- m - m' = a*(o' - o)
    -- Therefore: a = (m - m') / (o' - o) = (m - m') * (o' - o)⁻¹

    -- Now we need to show g^(((m - m') * (o' - o)⁻¹).val) = g^a.val

  -- this is o_ne
    -- have h_noo' : o' ≠ o := by exact fun a ↦ ho (id (Eq.symm a))
    have h_coprime : (guess.o - guess.o').val.Coprime q := by
      cases' Nat.coprime_or_dvd_of_prime hq_prime (o' - o).val with h_cop h_dvd
      · exact Nat.coprime_comm.mp h_cop
      · exfalso
        have h_zero : guess.o - guess.o' = 0 := by
          rw [← ZMod.val_eq_zero]
          have h_mod_zero : (guess.o - guess.o').val % q = 0 := Nat.mod_eq_zero_of_dvd h_dvd
          have h_val_bound : (guess.o - guess.o').val < q := ZMod.val_lt (guess.o - guess.o')
          exact Nat.eq_zero_of_dvd_of_lt h_dvd h_val_bound
        exact o_ne (eq_of_sub_eq_zero h_zero)

    have h_ex_inv : ∃ y, ↑(guess.o - guess.o').val * y ≡ 1 [ZMOD q] := by apply Int.mod_coprime h_coprime

    have h_ord : orderOf g = q := by
      rw [← G_card_q]; exact hg_gen

  -- this is collision
    -- have h_pow : g ^ (m.val + x.val * o.val) = g ^ (m'.val + x.val * o'.val) := by
    --   simp [←pow_mul, ←pow_add] at h2
    --   exact h2

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
    (A : G → PMF (Adversary.guess (ZMod q) G (ZMod q))) :
    haveI : Fact (Nat.Prime q) := ⟨hq_prime⟩;
    Commitment.comp_binding_game' (Pedersen.scheme G g q hq_prime) A 1 ≤ DLog.experiment G g q (DLog.adversary' G q A) 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  -- Unfold definitions
  unfold Commitment.comp_binding_game' DLog.experiment DLog.adversary'
  simp only [Pedersen.scheme, Pedersen.setup, Pedersen.verify]

  -- Both games now sample from PMF.uniformOfFintype (ZModMult q)
  -- LHS: Pr[a ← ZModMult q; guess ← A(g^a); binding succeeds]
  -- RHS: Pr[a ← ZModMult q; guess ← A(g^a); adversary' extracts a correctly]

  -- The LHS sums over G, but only elements of the form g^a for a ∈ ZModMult q have nonzero weight
  -- The RHS sums over ZModMult q directly

  -- Strategy: Show that for each a ∈ ZModMult q and each guess from A(g^a):
  --   if binding succeeds with o ≠ o', then adversary' extracts a correctly
  --   if binding succeeds with o = o', we get a contradiction (m = m')
  -- Therefore: Pr[binding succeeds] ≤ Pr[adversary' extracts a]

  -- The key challenge is that we need to massage the LHS to sum over ZModMult q
  -- instead of G, using the fact that only g^a values have nonzero probability.

  sorry


theorem computational_binding :
  ∀ (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] [CancelMonoidWithZero (ZMod q)] [Fact (Nat.Prime q)] (ε : ENNReal)
    (G_card_q : Fintype.card G = q)
    (hg_gen : orderOf g = Fintype.card G),
    (∀ (A : G → PMF (ZMod q)), DLog.experiment G g q A 1 ≤ ε) →
    (∀ (A : G → PMF (Adversary.guess (ZMod q) G (ZMod q))),
    ∃ hq_prime : Nat.Prime q, Commitment.comp_binding_game' (Pedersen.scheme G g q hq_prime) A 1 ≤ ε) := by
  intro G _ _ _ _ g q _ _ _ ε G_card_q hg_gen hdlog A
  have hq_prime := Fact.out (p := Nat.Prime q)
  use hq_prime
  exact le_trans (binding_as_hard_dlog G g q hq_prime G_card_q hg_gen A) (hdlog (DLog.adversary' G q A))

end Pedersen
