-- From cryptolib licensed under Apache 2.0
-- https://github.com/joeylupo/cryptolib

/-
 -----------------------------------------------------------
  Correctness and semantic security of ElGamal public-key
  encryption scheme
 -----------------------------------------------------------
-/

import Mathlib
import VerifiedCommitments.cryptolib
import VerifiedCommitments.CommitmentScheme

namespace DDH

variable (G : Type) [Fintype G] [Group G]
          (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)
          (q : ℕ) [NeZero q] [Fact (0 < q)] (G_card_q : Fintype.card G = q)
          (D : G → G → G → PMF (ZMod 2))

include g_gen_G G_card_q

instance : Fintype (ZMod q) := ZMod.fintype q

noncomputable def Game0 : PMF (ZMod 2) :=
do
  let x ← PMF.uniformOfFintype (ZMod q)
  let y ← PMF.uniformOfFintype (ZMod q)
  let b ← D (g^x.val) (g^y.val) (g^(x.val * y.val))
  pure b

noncomputable def Game1 : PMF (ZMod 2) :=
do
  let x ← PMF.uniformOfFintype (ZMod q)
  let y ← PMF.uniformOfFintype (ZMod q)
  let z ← PMF.uniformOfFintype (ZMod q)
  let b ← D (g^x.val) (g^y.val) (g^z.val)
  pure b

-- DDH0(D) is the event that D outputs 1 upon receiving (g^x, g^y, g^(xy))
-- local notation `Pr[DDH0(D)]` := (DDH0 G g g_gen_G q G_card_q D 1 : ℝ)

-- DDH1(D) is the event that D outputs 1 upon receiving (g^x, g^y, g^z)
-- local notation `Pr[DDH1(D)]` := (DDH1 G g g_gen_G q G_card_q D 1 : ℝ)

def Assumption (ε : ENNReal) : Prop := (Game0 G g q D 1) - (Game1 G g q D 1) ≤ ε

end DDH

namespace PKE
variable {K M C O A_state: Type} [DecidableEq M]
          (setup : PMF (K × O))
          (commit : K → M → PMF (C × O))
          (verify : K → M → C → O → ZMod 2) -- This confusing C is (G × G), but also just G?
          (A1 : K → PMF ((M × M) × A_state))
          (A2 : C → A_state → PMF (ZMod 2))

/-
  Executes the a public-key protocol defined by keygen,
  encrypt, and decrypt
-/
noncomputable def commit_verify (m : M) : PMF (ZMod 2) :=
do
  let (h, _) ← setup
  let (c, o) ← commit h m
  pure (verify h m c o)

/-
  A public-key encryption protocol is correct if decryption undoes
  encryption with probability 1
-/
def pke_correctness : Prop := ∀ (m : M), commit_verify setup commit verify m = pure 1

/-
  The semantic security game.
  Returns 1 if the attacker A2 guesses the correct bit
-/
noncomputable def ComputationalHidingGame : PMF (ZMod 2):=
do
  let (h, _) ← setup
  let ((m, m'), a_state) ← A1 h
  let b ← PMF.uniformOfFintype (ZMod 2)
  let (c, _) ← commit h (if b = 0 then m else m')
  let b' ← A2 c a_state
  pure (1 + b + b')


-- SSG(A) denotes the event that A wins the semantic security game
--local notation `Pr[SSG(A)]` := (SSG keygen encrypt A1 A2 1 : ℝ)

def pke_semantic_security (ε : ENNReal) : Prop :=  (ComputationalHidingGame setup commit A1 A2 1) - 1/2 ≤ ε

end PKE

namespace Elgamal

class ElgamalParameters (G : Type) extends
  Fintype G, Group G, IsCyclic G where
  [decidable_G : DecidableEq G]
  q : ℕ
  [neZero_q : NeZero q]
  -- [fact (0 < params.q)]
  prime_q : Nat.Prime q
  g : G
  card_eq : Fintype.card G = q
  g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g
  G_card_q : Fintype.card G = q
  A_state : Type
  A1 : G → PMF ((G × G) × A_state)
  A2 : (G × G) → A_state → PMF (ZMod 2) -- what deoes this need to be? Has to match what the distinguisher needs...

-- Make instances available
variable {G : Type} [params : ElgamalParameters G]
instance : DecidableEq G := params.decidable_G
instance : Fact (Nat.Prime params.q) := ⟨params.prime_q⟩

noncomputable def setup : PMF (G × ZMod params.q) := -- Need to include x to match CommitmentScheme spec
do
  let x ← PMF.uniformOfFintype (ZMod params.q)
  return (params.g^x.val, x)

noncomputable def commit (h m : G) : PMF ((G × G) × ZMod params.q) :=
do
  let r ← PMF.uniformOfFintype (ZMod params.q)
  pure ((params.g^r.val, h^r.val * m), r)

def verify (h m : G) (c : (G × G)) (o : ZMod params.q) : ZMod 2 :=
  if c = ⟨params.g^o.val, h^o.val * m⟩ then 1 else 0

noncomputable def scheme : CommitmentScheme G (G × G) (ZMod params.q) G :=
{
  setup := setup,
  commit := commit,
  verify := verify
}

/-
  -----------------------------------------------------------
  Proof of correctness of ElGamal
  -----------------------------------------------------------
-/

theorem elgamal_pke_correctness : @PKE.pke_correctness G G (G × G) (ZMod params.q) setup commit verify := by
  intro m
  unfold setup commit verify PKE.commit_verify
  simp only [bind_pure_comp, Functor.map_map, bind_map_left]
  apply bind_skip_const'
  intro x
  apply bind_skip_const'
  intro y
  simp only [Function.comp_apply]
  rfl

theorem elgamal_commitment_correctness : Commitment.correctness (@scheme G params) := by
  intro h m
  show PMF.bind (scheme.commit h m) _ = _
  simp only [scheme]
  unfold commit verify
  simp only [bind_pure_comp, Functor.map, PMF.bind_bind, Function.comp_apply, PMF.pure_bind, ↓reduceIte, PMF.bind_const]

/-
  -----------------------------------------------------------
  Computational Hiding
  -----------------------------------------------------------
-/
theorem computational_hiding : ∀ (ε : ENNReal), Commitment.computational_hiding (@scheme G params) ε := by
  sorry


/-
  -----------------------------------------------------------
  Proof of semantic security of ElGamal
  -----------------------------------------------------------
-/

noncomputable def D (gx gy gz : G) : PMF (ZMod 2) :=
do
  let ((m₀, m₁), a_state) ← params.A1 gx
  let b ← PMF.uniformOfFintype (ZMod 2)
  let mb ← pure (if b = 0 then m₀ else m₁)
  let b' ← params.A2 ⟨gy, (gz * mb)⟩ a_state
  pure (1 + b + b')

/-
  The probability of the attacker (i.e. the composition of A1 and A2)
  winning the semantic security game (i.e. guessing the correct bit),
  w.r.t. ElGamal is equal to the probability of D winning the game DDH0.
-/
theorem ComputationalHiding_DDH0 : PKE.ComputationalHidingGame setup commit params.A1 params.A2 =  DDH.Game0 G params.g params.q D := by
  simp only [PKE.ComputationalHidingGame, DDH.Game0, bind, setup, commit, D]
  simp_rw [PMF.bind_bind (PMF.uniformOfFintype (ZMod params.q))]
  apply bind_skip'
  intro x
  simp [pure]
  simp_rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod params.q))]
  apply bind_skip'
  intro m
  apply bind_skip'
  intro b
  apply bind_skip'
  intro y
  rw [pow_mul params.g x.val y.val]

noncomputable def Game1 : PMF (ZMod 2) :=
do
  let x ← PMF.uniformOfFintype (ZMod params.q)
  let y ← PMF.uniformOfFintype (ZMod params.q)
  let ((m₀, m₁), a_state) ← params.A1 (params.g^x.val)
  let b ← PMF.uniformOfFintype (ZMod 2)
  let ζ ← (do
    let z ← PMF.uniformOfFintype (ZMod params.q)
    let mb ← pure (if b = 0 then m₀ else m₁)
    pure (params.g^z.val * mb))
  let b' ← params.A2 ⟨(params.g^y.val), ζ⟩ a_state
  pure (1 + b + b')

noncomputable def Game2 : PMF (ZMod 2) :=
do
  let x ← PMF.uniformOfFintype (ZMod params.q)
  let y ← PMF.uniformOfFintype (ZMod params.q)
  let (_, a_state) ← params.A1 (params.g^x.val)
  let b ← PMF.uniformOfFintype (ZMod 2)
  let ζ ← (do
    let z ← PMF.uniformOfFintype (ZMod params.q)
    pure (params.g^z.val))
  let b' ← params.A2 ⟨(params.g^y.val), ζ⟩ a_state
  pure (1 + b + b')


/-
  The probability of the attacker (i.e. the composition of A1 and A2)
  winning Game1 (i.e. guessing the correct bit) is equal to the
  probability of D winning the game DDH1.
-/
theorem Game1_DDH1 : @Game1 G params = DDH.Game1 G params.g params.q D := by
  simp only [DDH.Game1, Game1, bind, D]
  apply bind_skip'
  intro x
  apply bind_skip'
  intro y
  simp_rw [PMF.bind_bind (params.A1 _)]
  conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod params.q))]
  apply bind_skip'
  intro m
  simp_rw [PMF.bind_bind (PMF.uniformOfFintype (ZMod params.q))]
  conv_lhs => rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod 2))]
  apply bind_skip'
  intro z
  conv_rhs => rw [PMF.bind_bind (PMF.uniformOfFintype (ZMod 2))]
  apply bind_skip'
  intro b
  simp_rw [PMF.bind_bind]
  apply bind_skip'
  intro mb
  simp [pure]


lemma exp_bij : Function.Bijective (fun (z : ZMod params.q) => params.g ^ z.val) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  simp [params.card_eq]
  intro y
  obtain ⟨k, hk⟩ := params.g_gen_G y
  use (k : ZMod params.q)
  simp only at hk ⊢
  rw [← hk]
  suffices params.g ^ ((k : ZMod params.q).val : ℤ) = params.g ^ k by exact_mod_cast this
  simp only [ZMod.val_intCast, ← params.card_eq]
  exact zpow_mod_card params.g k


lemma exp_mb_bij (mb : G) : Function.Bijective (fun (z : ZMod params.q) => params.g ^ z.val * mb) := by
  have h : (fun (z : ZMod params.q) => params.g ^ z.val * mb) =
    (fun (m : G) => m * mb) ∘ (fun (z : ZMod params.q) => params.g ^ z.val) := by rfl
  rw [h]
  apply Function.Bijective.comp
  · -- (λ (m : G), (m * mb)) bijective
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, rfl⟩
    intros x y hxy
    exact mul_right_cancel hxy
  · -- (λ (z : ZMod params.q), g ^ z.val) bijective
    exact exp_bij


lemma G1_G2_lemma1 (x : G) (exp : ZMod params.q → G) (exp_bij : Function.Bijective exp) :
    ∑' (z : ZMod params.q), ite (x = exp z) (1 : ENNReal) 0 = 1 := by
  obtain ⟨exp_inv, hinv_left, hinv_right⟩ := Function.bijective_iff_has_inverse.mp exp_bij
  have bij_eq : ∀ (z : ZMod params.q), (x = exp z) ↔ (z = exp_inv x) := by
    intro z
    constructor
    · -- (x = exp z) → (z = exp_inv x)
      intro h
      have h1 : exp_inv x = exp_inv (exp z) := congrArg exp_inv h
      rw [hinv_left z] at h1
      exact h1.symm
    · -- (z = exp_inv x) → (x = exp z)
      intro h
      have h2 : exp z = exp (exp_inv x) := congrArg exp h
      rw [hinv_right x] at h2
      exact h2.symm
  simp_rw [bij_eq]
  simp


lemma G1_G2_lemma2 (mb : G) :
    (PMF.uniformOfFintype (ZMod params.q)).bind (fun (z : ZMod params.q) => pure (params.g^z.val * mb)) =
    (PMF.uniformOfFintype (ZMod params.q)).bind (fun (z : ZMod params.q) => pure (params.g^z.val)) := by
  ext x
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Pure.pure]
  have lhs_eq : ∑' (z : ZMod params.q), ((↑(Fintype.card (ZMod params.q)))⁻¹ : ENNReal) * (PMF.pure (params.g ^ z.val * mb)) x =
                ((↑(Fintype.card (ZMod params.q)))⁻¹ : ENNReal) * ∑' (z : ZMod params.q), ite (x = params.g ^ z.val * mb) 1 0 := by
    rw [ENNReal.tsum_mul_left]
    congr
    funext z
    simp only [PMF.pure_apply]
    split_ifs <;> ring
  have rhs_eq : ∑' (z : ZMod params.q), ((↑(Fintype.card (ZMod params.q)))⁻¹ : ENNReal) * (PMF.pure (params.g ^ z.val)) x =
                ((↑(Fintype.card (ZMod params.q)))⁻¹ : ENNReal) * ∑' (z : ZMod params.q), ite (x = params.g ^ z.val) 1 0 := by
    rw [ENNReal.tsum_mul_left]
    congr
    funext z
    simp only [PMF.pure_apply]
    split_ifs <;> ring
  rw [lhs_eq, rhs_eq]
  rw [G1_G2_lemma1 x (fun z => params.g ^ z.val * mb) (exp_mb_bij mb)]
  rw [G1_G2_lemma1 x (fun z => params.g ^ z.val) exp_bij]



lemma G1_G2_lemma3 (m : PMF G) :
    m.bind (fun (mb : G) => (PMF.uniformOfFintype (ZMod params.q)).bind (fun (z : ZMod params.q) => pure (params.g^z.val * mb))) =
    (PMF.uniformOfFintype (ZMod params.q)).bind (fun (z : ZMod params.q) => pure (params.g^z.val)) := by
  simp_rw [G1_G2_lemma2 _]
  apply bind_skip_const'
  intro m
  congr

/-
  The probability of the attacker (i.e. the composition of A1 and A2)
  winning Game1 (i.e. guessing the correct bit) is equal to the
  probability of the attacker winning Game2.
-/
theorem Game1_Game2 : @Game1 G params = @Game2 G params := by
  simp only [Game1, Game2]
  apply bind_skip'
  intro x
  apply bind_skip'
  intro y
  apply bind_skip'
  intro m
  apply bind_skip'
  intro b
  simp [bind, -PMF.bind_pure, -PMF.bind_bind]
  simp_rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod params.q))]
  rw [G1_G2_lemma3]

lemma G2_uniform_lemma (b' : ZMod 2) : (PMF.uniformOfFintype (ZMod 2)).bind (fun (b : ZMod 2) => pure (1 + b + b')) = PMF.uniformOfFintype (ZMod 2) := by
  -- The function (b ↦ 1 + b + b') is a bijection on ZMod 2
  have bij : Function.Bijective (fun b : ZMod 2 => 1 + b + b') := by
    constructor
    · intro x y hxy
      have : x + b' = y + b' := by linear_combination hxy
      linear_combination this
    · intro y
      use y - b' - 1
      ring
  -- Use the same argument as G1_G2_lemma2
  ext a
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Pure.pure, PMF.pure_apply]
  rw [tsum_fintype]
  simp only [mul_ite, mul_one, mul_zero]
  have card_eq : Fintype.card (ZMod 2) = 2 := by norm_num
  simp only [card_eq]
  norm_num
  -- Exactly one value of b makes a = 1 + b + b', namely b = a - b' - 1
  have : ∃! b : ZMod 2, a = 1 + b + b' := by
    use a - b' - 1
    constructor
    · ring
    · intro y hy
      calc y = y + 0 := by ring
        _ = y + (b' + (a - b' - 1) - (a - 1)) := by ring
        _ = (y + b') + (a - b' - 1) - (a - 1) := by ring
        _ = (1 + y + b') + (a - b' - 1) - (1 + a - 1) := by ring
        _ = a + (a - b' - 1) - a := by rw [← hy]; ring
        _ = a - b' - 1 := by ring
  obtain ⟨b₀, hb₀, huniq⟩ := this
  have sum_eq : ∑ x : ZMod 2, (if a = 1 + x + b' then (2⁻¹ : ENNReal) else 0) = 2⁻¹ := by
    have : ∑ x : ZMod 2, (if a = 1 + x + b' then (2⁻¹ : ENNReal) else 0) =
           ∑ x : ZMod 2, (if x = b₀ then (2⁻¹ : ENNReal) else 0) := by
      congr 1
      ext x
      by_cases h : a = 1 + x + b'
      · simp [h, huniq x h]
      · simp [h]
        by_cases hx : x = b₀
        · subst hx
          contradiction
        · simp [hx]
    rw [this, Finset.sum_ite_eq']
    simp
  exact sum_eq


/-
  The probability of the attacker (i.e. the composition of A1 and A2)
  winning Game2 (i.e. guessing the correct bit) is equal to a coin flip.
-/
theorem Game2_uniform : @Game2 G params = PMF.uniformOfFintype (ZMod 2) := by
  simp [Game2, bind]
  apply bind_skip_const'
  intro x
  apply bind_skip_const'
  intro m
  apply bind_skip_const'
  intro y
  rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod 2))]
  simp_rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod 2))]
  apply bind_skip_const'
  intro z
  apply bind_skip_const'
  intro ζ
  apply bind_skip_const'
  intro b'
  exact G2_uniform_lemma b'

-- parameters (ε : nnreal)
variable (ε : ENNReal)
/-
  The advantage of the attacker (i.e. the composition of A1 and A2) in
  the semantic security game `ε` is exactly equal to the advantage of D in
  the Diffie-Hellman game. Therefore, assumining the decisional Diffie-Hellman
  assumption holds for the group `G`, we conclude `ε` is negligble, and
  therefore ElGamal is, by definition, semantically secure.
-/
theorem elgamal_semantic_security (DDH_G : DDH.Assumption G params.g params.q D ε) :
    PKE.pke_semantic_security setup commit params.A1 params.A2 ε := by
  simp only [PKE.pke_semantic_security]
  rw [ComputationalHiding_DDH0]
  have h : ((PMF.uniformOfFintype (ZMod 2)) 1) = 1/2 := by
    simp only [PMF.uniformOfFintype_apply, ZMod.card, Nat.cast_ofNat, one_div]
  rw [← h]
  rw [← @Game2_uniform G params]
  rw [← Game1_Game2]
  rw [Game1_DDH1]
  exact DDH_G



end Elgamal
