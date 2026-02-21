import VerifiedCommitments.elgamal

variable {X Y L R : Type}

structure BindingEncryptionScheme (X Y L R : Type) where
  gen : PMF (L × L)
  enc : L → X → R → Y
  dec : L → Y → X


def correctness (scheme : BindingEncryptionScheme X Y L R) : Prop :=
  ∀ (m : X) (r : R) (sk pk : L), scheme.dec sk (scheme.enc pk m r) = m

variable {G : Type} [params : Elgamal.ElgamalParameters G]
instance : DecidableEq G := params.decidable_G
instance : Fact (Nat.Prime params.q) := ⟨params.prime_q⟩

noncomputable def setup : PMF (ZMod params.q × G) := --Elgamal.keygen
  PMF.uniformOfFintype (ZMod params.q) |>.bind (fun x => pure (x, params.g^x.val))

noncomputable def commit (h m : G) : PMF (G × ZMod params.q) := --(Elgamal.encrypt h m).map (fun (_, b) => b)
  PMF.uniformOfFintype (ZMod params.q) |>.bind (fun r => pure (h^r.val * m, r))

def verify (h m c : G) (o : ZMod params.q) : ZMod 2 := --if c = Elgamal.encrypt h m
  if c = h^o.val * m then 1 else 0

noncomputable def scheme : BindingEncryptionScheme G G G (ZMod params.q) :=
  {
    gen := setup,
    enc := commit,
    dec := verify
  }
