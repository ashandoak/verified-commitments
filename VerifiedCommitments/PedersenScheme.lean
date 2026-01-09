import VerifiedCommitments.CommitmentScheme
import Mathlib.Probability.Distributions.Uniform
import VerifiedCommitments.ZModUtil

namespace Pedersen

noncomputable def generate_a (q : ℕ) [NeZero q] [Fact (Nat.Prime q)] : PMF (ZModMult q) :=
  PMF.uniformOfFintype (ZModMult q)

noncomputable section

  def setup (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] [Fact (Nat.Prime q)] : PMF (G × (ZMod q)) :=
    PMF.bind (PMF.uniformOfFintype (ZModMult q)) (fun a => return ⟨g^(val a).val, val a⟩)

  def commit (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] (h : G) (m : ZMod q) : PMF (G × (ZMod q)) :=
    PMF.bind (PMF.uniformOfFintype (ZMod q)) (fun r => return ⟨g^m.val * h^r.val, r⟩)

  def verify (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] (h : G) (m : ZMod q) (c : G) (o : ZMod q): ZMod 2 :=
    if c = g^m.val * h^o.val then 1 else 0

  def scheme
    (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] [Fact (Nat.Prime q)] :
    CommitmentScheme (ZMod q) G (ZMod q) G := {
      setup := setup G g q,
      commit (h : G) (m : ZMod q) := commit G g q h m,
      verify (h : G) (m : ZMod q) (c : G) (o : ZMod q):= verify G g q h m c o
    }

end
end Pedersen

instance {G : Type} {q : ℕ} [NeZero q] : Nonempty (G × (ZMod q)) := sorry
