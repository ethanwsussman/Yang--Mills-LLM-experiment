import YangMills.Construction.Lattice.PreparedSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
namespace PeriodicLattice.ScaleLabel
variable {L m K m' k : ℕ} {c : ℕ → ℕ}
def nestBaseLevel (L r : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℕ :=
  (lowerLevel L r x k + 1).toNat
def trimmedDomainThickened (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) : Set (FourTorus L m) :=
  layerEnlargement (nestedCubeIndex L r x K m' (nestBaseLevel L r x k))
    (S.trimmedDomain r x Q (nestBaseLevel L r x k)) 2
def nestCore (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (X : Set (FourTorus L m)) : Set (FourTorus L m) :=
  cubeMeet K (S.innerBoxIn r x Q X)
    (complementRegion (nestedCubeIndex L r x K m' (nestBaseLevel L r x k))
      (S.trimmedDomainThickened r x Q))
def nestShell (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (X : Set (FourTorus L m)) (i : ℕ) : Set (FourTorus L m) :=
  if i = 0 then S.innerBoxIn r x Q X
  else if i ≤ Thresholds.delayDepth L r x k then
    cubeMeet K (S.trimmedRegion r x Q (k + 1 - i)) X
  else S.nestCore r x Q X
def shellDepth (K k i : ℕ) : ℤ := levelDepth K (k + 1 - i)
def nestFixedBonds (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (X : Set (FourTorus L m)) :
    Set (Σ q : ℕ, BondAtLevel L m K q) :=
  {t | t ∈ activeBondSet K k (S.trimmedDomain r x Q) ∧ lowerLevel L r x k ≤ (t.1 : ℤ) ∧
    t.2 ∈ bondsMeeting (S.innerBoxIn r x Q X) ∧
    t.2 ∈ bondsInside (S.trimmedDomainThickened r x Q)}
end PeriodicLattice.ScaleLabel
end YangMills.Construction
