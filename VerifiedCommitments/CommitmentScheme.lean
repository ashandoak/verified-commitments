import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.ZMod.Defs

/-- A CommitmentScheme is a structure over four spaces:
M: Message space
C: Commitment space
O: Opening value space
K: Key space

And that contains three algorithms:
setup: returns a public parameter and associated randomness
commit: given the public parameter and a message produces a commitment and an opening value
verify: given the public parameter, message and associated commit and opening value returns 1 when the commit opens to the given message and 0 otherwise.-/
structure CommitmentScheme (M C O K : Type) where
  setup : PMF (K × O)
  commit : K → M → PMF (C × O)
  verify : K → M → C → O → ZMod 2


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

namespace Commitment

variable {M C O K : Type}

/-- For any public parameters `h` and any message `m` if `commit` outputs a commitment `c` and opening value `o`, then `verify h m c o` accepts with probability 1.-/
def correctness (scheme : CommitmentScheme M C O K) : Prop :=
  ∀ (h : K) (m : M), (scheme.commit h m).bind (fun (c, o) =>
    pure <| scheme.verify h m c o) = pure 1

/-- A commitment scheme with public parameter `h` is perfectly binding if no commitment `c` can be opened to two different messages. For two purported openings `(m,o)` and `(m',o')` both verifying for the same `c`, the messages must be equal (`m = m'`). -/
def perfect_binding (scheme : CommitmentScheme M C O K) : Prop :=
  ∀ (h : K) (c : C) (m m' : M) (o o' : O),
    scheme.verify h m c o = 1 →
      scheme.verify h m' c o' = 1 →
        m = m'

/-- A commitment scheme is perfectly hiding if for any messages `m` and `m'`, the induced distribution on commitments is the same. Sampling `h ← setup` and then committing to `m` or `m'` under `h` yields identical commitment distributions. -/
def perfect_hiding (scheme: CommitmentScheme M C O K) : Prop :=
  ∀ (m m' : M) (c : C),
    PMF.bind scheme.setup (fun (h, _) =>
      PMF.bind (scheme.commit h m) (fun (c, _) =>
        pure c)) c
    =
    PMF.bind scheme.setup (fun (h, _) =>
      PMF.bind (scheme.commit h m') (fun (c, _) =>
        pure c)) c

noncomputable section

/- Computational Binding -/

/-- For any adversary `A` that accepts `h ← setup` and outputs a single commitment `c` together with two purported openings `(m,o)` and `(m',o')`, the computational binding game outputs `1` if `c` opens to both `(m,o)` and `(m',o') and the messages differ (`m ≠ m'`). -/
def comp_binding_game [DecidableEq M] (scheme : CommitmentScheme M C O K)
    (A : K → PMF (BindingGuess M C O)) : PMF (ZMod 2) := do
  let (h, _) ← scheme.setup
  let guess ← A h
  pure (
    if scheme.verify h guess.m guess.c guess.o = 1 ∧
      scheme.verify h guess.m' guess.c guess.o' = 1 ∧
        guess.m ≠ guess.m'
          then 1 else 0 )

/-- A commitment scheme is computationally binding if every adversary’s probability of winning the computational binding game is at most `ε`. -/
def computational_binding [DecidableEq M] (scheme : CommitmentScheme M C O K)
    (ε : ENNReal) : Prop :=
  ∀ (A' : K → PMF (BindingGuess M C O )), comp_binding_game scheme A' 1 ≤ ε


/- Computational Hiding -/

/-- For any `TwoStageAdversary` `A`, sample `h ← setup` and give `h` to the adversary’s first stage to produce two challenge messages `m₀, m₁. The computational hiding game samples a uniform bit `b`, computes a commitment to `m_b`, and gives the commitment `c` to the adversary’s second stage. The game outputs a bit indicating whether the adversary’s guess matches `b`. -/
def comp_hiding_game
    (scheme : CommitmentScheme M C O K)
    (A : TwoStageAdversary K M C) := do
  let (h, _) ← scheme.setup
  let ((m₀, m₁), state) ← A.stage1 h
  let b ← PMF.uniformOfFintype (ZMod 2)
  let (c, _) ← scheme.commit h (if b = 0 then m₀ else m₁)
  let b' ← A.stage2 c state
  pure (1 + b + b')

/-- A commitment scheme is computationally hiding if every adversary’s advantage
over random guessing in the hiding game is at most `ε`. -/
def computational_hiding (scheme : CommitmentScheme M C O K) (ε : ENNReal) : Prop :=
  ∀ (A : TwoStageAdversary K M C), comp_hiding_game scheme A 1 - 1/2 ≤ ε

end

end Commitment
