import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.ZMod.Defs


structure CommitmentScheme (M C O K : Type) where
  (setup : PMF K)
  (commit : K → M → PMF (C × O))
  (verify : K → M → C → O → ZMod 2)

variable {M C O K : Type}

noncomputable section

def correctness (scheme : CommitmentScheme M C O K) : Prop :=
  ∀ (h : K) (m : M),
  PMF.bind (scheme.commit h m) (fun (c, o) => pure $ scheme.verify h m c o) = pure 1

-- Perfect binding
def perfect_binding (scheme : CommitmentScheme M C O K) : Prop :=
  ∀ (h : K) (c : C) (m m' : M) (o o' : O),
    scheme.verify h m c o = 1 →
    scheme.verify h m' c o' = 1 →
    m = m'
    -- Equivalent to:
    --if scheme.verify h m c o = scheme.verify h m' c o' then true else false

-- Computational binding game
-- Security depends on generating the parameters correctly, but at this level probably alright to have the group and generator fixed
-- h should be inside the game, because its unique to a specific run
def comp_binding_game (scheme : CommitmentScheme M C O K)
  (A : K → PMF (C × M × M × O × O)) [DecidableEq M] : PMF $ ZMod 2 :=
  do
    let h ← scheme.setup
    let (c, m, m', o, o') ← A h
    if scheme.verify h m c o = 1 ∧ scheme.verify h m' c o' = 1 ∧ m ≠ m' then pure 1 else pure 0

def computational_binding [DecidableEq M] (scheme : CommitmentScheme M C O K) (ε : ENNReal) : Prop :=
  ∀ (A : K → PMF (C × M × M × O × O)), comp_binding_game scheme A 1 ≤ ε

-- Perfect hiding
def do_commit (scheme: CommitmentScheme M C O K) (m : M) : PMF C :=
do
  let h ← scheme.setup
  let (c, _) ← scheme.commit h m
  return c

def perfect_hiding (scheme: CommitmentScheme M C O K) : Prop :=
  ∀ (m m' : M) (c : C), (do_commit scheme m) c = (do_commit scheme m') c


-- Computational hiding game
def comp_hiding_game (scheme : CommitmentScheme M C O K)
  (A : K → C → PMF (ZMod 2)) (m : M) : PMF (ZMod 2) :=
  do
    let h ← scheme.setup -- As above with comp_binding_game
    let (c, _) ← scheme.commit h m
    A h c

def computational_hiding (scheme : CommitmentScheme M C O K) (ε : ENNReal) : Prop :=
  ∀ (A : K → C → PMF (ZMod 2)) (m₀ m₁ : M),
  comp_hiding_game scheme A m₀ 1 - comp_hiding_game scheme A m₁ 1 ≤ ε ||
  comp_hiding_game scheme A m₁ 1 - comp_hiding_game scheme A m₀ 1 ≤ ε
