import YangMills.Construction.Lattice.PreparedSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ScaleLabel
variable {L m K m' k : ℕ} {c : ℕ → ℕ}
def componentBoxSites (p : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (X : Set (FourTorus L m)) : Set (SiteAtLevel L m K k) :=
  sitesIn (S.innerBoxIn p x Q X)
def componentAxialTreeRotated (r : SignedFrame) (p : ℕ) (x : ℕ → ℝ)
    (S : ScaleLabel L m K m' c k) (Q : Set (Set (FourTorus L m))) (X : Set (FourTorus L m)) :
    Set (BondAtLevel L m K k) :=
  insert (rotatedBoxEntranceBond r (levelDepth K k) (S.componentBoxSites p x Q X))
    (rotatedAxialBoxTree r (levelDepth K k) (S.componentBoxSites p x Q X))
end YangMills.Construction.PeriodicLattice.ScaleLabel
