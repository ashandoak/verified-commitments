/-
Copyright (c) 2026 Ashley Blacquiere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashley Blacquiere
-/


module

public import Mathlib.Probability.Distributions.Uniform

/-!
# Commitment Schemes

Core definitions for commitment schemes following [KatzLindell2020], Chapter 6.

## Main definitions

-/

@[expose] public section

namespace Crypto.Protocols.Commitment

structure Scheme (Message Key Commitment OpeningValue : Type*) where
  gen : PMF (Key × OpeningValue)
  com (message : Message) (key : Key) : PMF (Commitment × OpeningValue)
  verify (message : Message) (key : Key) (commitment : Commitment) (openingvalue : OpeningValue) : ZMod 2
  correct : ∀ (key : Key) (message : Message), (com message key |>.bind fun (commitment, openingvalue) =>
    pure <| verify message key commitment openingvalue) = pure 1

namespace Crypto.Protocols.Commitment
