import VerifiedCommitments.CommitmentScheme
import VerifiedCommitments.dlog

namespace Pedersen

  -- noncomputable def scheme
  --   (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
  --     (q : ℕ) [NeZero q] (hq_prime : Nat.Prime q) :
  --     CommitmentScheme (ZMod q) G (ZMod q) G := {
  --   setup := -- PMF.bind (PMF.uniformOfFinset (nonzeroElements hq_prime).1 (nonzeroElements hq_prime).2) (fun a => return g^a.val), --setup q hq g,
  --   do
  --     let a ← PMF.uniformOfFinset (nonzeroElements hq_prime).1 (nonzeroElements hq_prime).2
  --     return g^a.val,
  --   commit := fun h m =>  --commit h m g,
  --   do
  --     let r ← PMF.uniformOfFintype (ZMod q)
  --     return ⟨g^m.val * h^r.val, r⟩,
  --   verify := fun h m c o => if c = g^m.val * h^o.val then 1 else 0  --verify h m c o g
  -- }

  noncomputable def setup (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] (hq_prime : Nat.Prime q) : PMF G :=
    PMF.bind (PMF.uniformOfFinset (nonzeroElements hq_prime).1 (nonzeroElements hq_prime).2) (fun a => return g^a.val)

  noncomputable def commit (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] (h : G) (m : ZMod q) : PMF G :=
    do
      let r ← PMF.uniformOfFintype (ZMod q)
      return g^m.val * h^r.val

  noncomputable def verify (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] (h : G) (m : ZMod q) (c : G) (o : ZMod q): ZMod 2 :=
    if c = g^m.val * h^o.val then 1 else 0


  noncomputable def scheme
    (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] (hq_prime : Nat.Prime q) :
    CommitmentScheme (ZMod q) G (ZMod q) G := {
      setup := setup G g q hq_prime,
      commit (h : G) (m : ZMod q) := commit G g q h m,
      verify (h : G) (m : ZMod q) (c : G) (o : ZMod q):= verify G g q h m c o
    }

end Pedersen
