import VerifiedCommitments.PedersenScheme

namespace DLog

noncomputable section

-- Modification of Attack game and advantage as specified in Boneh 10.4 to account for check between generated x and x'
def attack_game (G : Type) [Group G] (q : ℕ) [NeZero q] (g : G) (A : G → PMF (ZMod q)) : PMF (ZMod 2) :=
PMF.bind (PMF.uniformOfFintype (ZMod q)) (fun x =>
  PMF.bind (A (g^x.val)) (fun x' => pure (if x = x' then 1 else 0)))

-- The advantage of an attacker A in the DLog problem
-- attack_game returns a PMF ()
def advantage (G : Type) [Group G] (q : ℕ) [NeZero q] (g : G) (A : G → PMF (ZMod q)) : ENNReal := attack_game G q g A 1

#check Pedersen.scheme
noncomputable def experiment
  (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G] (g : G)
    (q : ℕ) [NeZero q] [Fact (Nat.Prime q)]
    (A' : G → PMF (ZMod q)) : PMF (ZMod 2) :=
  PMF.bind (Pedersen.scheme G g q).setup (fun h =>
    PMF.bind (A' h.1) (fun x' => pure (if g^x'.val = g^(h.2).val then 1 else 0)))

  noncomputable def adversary
    (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G]
      (q : ℕ) [NeZero q]
      (A : G → PMF (G × ZMod q × ZMod q × ZMod q × ZMod q))
      (h : G) : PMF (ZMod q) :=
    PMF.bind (A h) (fun (_c, m, m', o, o') =>
       if o ≠ o' then
        return ((m - m') * (o' - o)⁻¹)
      else
        PMF.uniformOfFintype (ZMod q)
    )

  noncomputable def adversary'
    (G : Type) [Fintype G] [Group G] [IsCyclic G] [DecidableEq G]
      (q : ℕ) [NeZero q]
      (A' : G → PMF (Adversary.guess (ZMod q) G (ZMod q)))
      (h : G) : PMF (ZMod q) :=
    PMF.bind (A' h) (fun guess =>
      if guess.o ≠ guess.o' then
        return ((guess.m - guess.m') * (guess.o' - guess.o)⁻¹)
      else
        PMF.uniformOfFintype (ZMod q)
      )
end
end DLog
