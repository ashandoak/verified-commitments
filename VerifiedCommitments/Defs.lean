/-
Copyright (c) 2026 Ashley Blacquiere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashley Blacquiere
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import VerifiedCommitments.Scheme

/-!
# Commitment: Definitions

Core definitions for commitment schemes following [KatzLindell2020], Chapter 6.

## Main definitions

-/

@[expose] public section

namespace Crypto.Protocols.Commitment.Scheme

universe u
variable {M K C O : Type}

/-- The structure of binding adversary guesses for use in the computational binding game.-/
structure BindingGuess (M C O : Type) where
  c : C
  m : M
  m' : M
  o : O
  o' : O

/-- The structure of the hiding adversary for use in the computational hiding game.-/
structure TwoStageAdversary (K M C : Type) where
  state : Type
  stage1 : K → PMF ((M × M) × state)
  stage2 : C → state → PMF (ZMod 2)


/-- A commitment scheme with public parameter `h` is perfectly binding if no commitment `c` can be opened to two different messages. For two purported openings `(m,o)` and `(m',o')` both verifying for the same `c`, the messages must be equal (`m = m'`). -/
def perfect_binding (scheme : Scheme M K C O) : Prop :=
  ∀ (h : K) (c : C) (m m' : M) (o o' : O),
    scheme.verify m h c o = 1 →
      scheme.verify m' h c o' = 1 →
        m = m'

/-- A commitment scheme is perfectly hiding if for any messages `m` and `m'`, the induced distribution on commitments is the same. Sampling `h ← setup` and then committing to `m` or `m'` under `h` yields identical commitment distributions. -/
def perfect_hiding (scheme : Scheme M K C O) : Prop :=
  ∀ h m m' c,
    ((scheme.com m h).map Prod.fst) c =
    ((scheme.com m' h).map Prod.fst) c

/- Computational Binding -/

/-- For any adversary `A` that accepts `h ← setup` and outputs a single commitment `c` together with two purported openings `(m,o)` and `(m',o')`, the computational binding game outputs `1` if `c` opens to both `(m,o)` and `(m',o') and the messages differ (`m ≠ m'`). -/
noncomputable def comp_binding_game
    [DecidableEq M] (scheme : Scheme M K C O)
    (A : K → PMF (BindingGuess M C O)) : PMF (ZMod 2) := do
  let (h, _) ← scheme.gen
  let guess ← A h
  pure (
    if scheme.verify guess.m h guess.c guess.o = 1 ∧
      scheme.verify guess.m' h guess.c guess.o' = 1 ∧
        guess.m ≠ guess.m'
          then 1 else 0 )

/-- A commitment scheme is computationally binding if every adversary’s probability of winning the computational binding game is at most `ε`. -/
def computational_binding [DecidableEq M] (scheme : Scheme M K C O)
    (ε : ENNReal) : Prop :=
  ∀ (A' : K → PMF (BindingGuess M C O )), comp_binding_game scheme A' 1 ≤ ε

/- Computational Hiding -/

/-- For any `TwoStageAdversary` `A`, sample `h ← setup` and give `h` to the adversary’s first stage to produce two challenge messages `m₀, m₁. The computational hiding game samples a uniform bit `b`, computes a commitment to `m_b`, and gives the commitment `c` to the adversary’s second stage. The game outputs a bit indicating whether the adversary’s guess matches `b`. -/
noncomputable def comp_hiding_game
    (scheme : Scheme M K C O)
    (A : TwoStageAdversary K M C) := do
  let (h, _) ← scheme.gen
  let ((m₀, m₁), state) ← A.stage1 h
  let b ← PMF.uniformOfFintype (ZMod 2)
  let (c, _) ← scheme.com (if b = 0 then m₀ else m₁) h
  let b' ← A.stage2 c state
  pure (1 + b + b')

/-- A commitment scheme is computationally hiding if every adversary’s advantage
over random guessing in the hiding game is at most `ε`. -/
def computational_hiding (scheme : Scheme M K C O)
    (ε : ENNReal) : Prop :=
  ∀ (A : TwoStageAdversary K M C), comp_hiding_game scheme A 1 - 1/2 ≤ ε

end Crypto.Protocols.Commitment.Scheme
