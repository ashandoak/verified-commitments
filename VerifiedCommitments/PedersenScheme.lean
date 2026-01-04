import VerifiedCommitments.CommitmentScheme
import VerifiedCommitments.dlog
import VerifiedCommitments.ZModUtil

namespace Pedersen

-- TODO: I'm not sure this should be here, or that
-- Setup should definitely return h, but should there be another def hanging around that computes an a independently?
-- The two alternatives below for bind in setup may have some bearing on how the binding proof progresses, unless I change the dlog definitions to match...

noncomputable def generate_a (q : ℕ) [NeZero q] : PMF (ZModMult q) :=
  PMF.uniformOfFintype (ZModMult q)


noncomputable section

  def setup (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] (hq_prime : Nat.Prime q) : PMF G :=
    PMF.bind (PMF.uniformOfFintype (ZModMult q)) (fun a => return g^(val a).val)
    -- PMF.bind (PMF.uniformOfFinset (nonzeroElements hq_prime).1 (nonzeroElements hq_prime).2) (fun a => return g^a.val)

  def commit (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] (h : G) (m : ZMod q) : PMF (G × (ZMod q)) :=
    PMF.bind (PMF.uniformOfFintype (ZMod q)) (fun r => return ⟨g^m.val * h^r.val, r⟩)

  def verify (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] (h : G) (m : ZMod q) (c : G) (o : ZMod q): ZMod 2 :=
    if c = g^m.val * h^o.val then 1 else 0

  def scheme
    (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] (hq_prime : Nat.Prime q) :
    CommitmentScheme (ZMod q) G (ZMod q) G := {
      setup := setup G g q hq_prime,
      commit (h : G) (m : ZMod q) := commit G g q h m,
      verify (h : G) (m : ZMod q) (c : G) (o : ZMod q):= verify G g q h m c o
    }

end
end Pedersen

instance {G : Type} {q : ℕ} [NeZero q] : Nonempty (G × (ZMod q)) := sorry
