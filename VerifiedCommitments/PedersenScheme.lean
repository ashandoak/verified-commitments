import VerifiedCommitments.«commitment-scheme»
import VerifiedCommitments.dlog

namespace Pedersen

  noncomputable def scheme
    (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
      (q : ℕ) [NeZero q] (hq_prime : Nat.Prime q) :
      CommitmentScheme (ZMod q) G (ZMod q) G := {
    setup := --setup q hq g,
    do
      let a ← PMF.uniformOfFinset (nonzeroElements hq_prime).1 (nonzeroElements hq_prime).2
      return g^a.val,
    commit := fun h m =>  --commit h m g,
    do
      let r ← PMF.uniformOfFintype (ZMod q)
      return ⟨g^m.val * h^r.val, r⟩,
    verify := fun h m c o => if c = g^m.val * h^o.val then 1 else 0  --verify h m c o g
  }

end Pedersen
