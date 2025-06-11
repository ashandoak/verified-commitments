import Mathlib

namespace DLog

noncomputable section

-- Modification of Attack game and advantage as specified in Boneh 10.4 to account for check between generated x and x'
def attack_game (G : Type) [Group G] (q : ℕ) [NeZero q] (g : G) (A : G → PMF (ZMod q)) : PMF (ZMod 2) :=
do
  let x ← PMF.uniformOfFintype (ZMod q)
  let x' ← A (g^x.val)
  pure (if x = x' then 1 else 0)

-- The advantage of an attacker A in the DLog problem
-- attack_game returns a PMF ()
def advantage (G : Type) [Group G] (q : ℕ) [NeZero q] (g : G) (A : G → PMF (ZMod q)) : ENNReal := attack_game G q g A 1
end

end DLog
