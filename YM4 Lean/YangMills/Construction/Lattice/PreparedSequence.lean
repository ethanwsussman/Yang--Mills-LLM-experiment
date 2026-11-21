import YangMills.Construction.Lattice.ConnectedDeterminingSets
import YangMills.Construction.Thresholds.DegreeFunctions
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def lowerLevel (L r : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℤ :=
  (k : ℤ) - (Thresholds.delayDepth L r x k : ℤ)
def boundaryLevel (L r : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℕ :=
  (Thresholds.delayLevel L r x k + 1).toNat
def nestedCubeIndex (L r : ℕ) (x : ℕ → ℝ) (K m' i : ℕ) : ℤ :=
  scaledCubeIndex K i (m' + Nat.log L (Thresholds.minBlockSize L r x i))
def nestedCubeSide (L r : ℕ) (x : ℕ → ℝ) (m' k i : ℕ) : ℝ :=
  (L : ℝ) ^ m' * (Thresholds.minBlockSize L r x i : ℝ) * (L : ℝ) ^ ((i : ℤ) - (k : ℤ))
def shellWidth (L r : ℕ) (x : ℕ → ℝ) (m' k i : ℕ) : ℝ :=
  if i = k then 0
  else if i = boundaryLevel L r x k then 2 * (L : ℝ) ^ m'
  else (L : ℝ) ^ m' * ∑ q ∈ Finset.Icc (i + 1) k, (L : ℝ) ^ ((q : ℤ) - (k : ℤ))
namespace ScaleLabel
variable {K m' k : ℕ} {c : ℕ → ℕ}
def largeFieldOrEmpty (S : ScaleLabel L m K m' c k) (i : ℕ) : Set (FourTorus L m) :=
  open Classical in
  if h : i ∈ Set.Icc 1 k then S.largeField ⟨i, h⟩ else ∅
def trimmedRegion (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (i : ℕ) : Set (FourTorus L m) :=
  open Classical in
  if (i : ℤ) ≤ lowerLevel L r x k then S.largeFieldOrEmpty i ∩ ⋃₀ Q
  else if (i : ℤ) ≤ Thresholds.delayLevel L r x k then
    complementRegion (nestedCubeIndex L r x K m' i)
      (layerEnlargement (nestedCubeIndex L r x K m' i) (S.domainSeq i) 5) ∩ ⋃₀ Q
  else
    {y | y ∈ ⋃₀ Q ∧ ENNReal.ofReal (5 * (L : ℝ) ^ m' + shellWidth L r x m' k i) ≤
      supDistInLevelUnits K k {y} (S.domainSeq (boundaryLevel L r x k))}
def trimmedDomain (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (i : ℕ) : Set (FourTorus L m) :=
  open Classical in
  if i = 0 ∨ (i : ℤ) ≤ lowerLevel L r x k then S.domainSeq i
  else cubeDiff (coarseCubeIndex K m' i) (⋃₀ Q) (S.trimmedRegion r x Q i) ∪
    (S.domainSeq i ∩ complementRegion (coarseCubeIndex K m' k) (⋃₀ Q))
def innerBox (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) : Set (FourTorus L m) :=
  complementRegion (nestedCubeIndex L r x K m' (boundaryLevel L r x k))
    (layerEnlargement (nestedCubeIndex L r x K m' (boundaryLevel L r x k))
      (S.domainSeq (boundaryLevel L r x k)) 4) ∩ ⋃₀ Q
def innerBoxIn (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (X : Set (FourTorus L m)) : Set (FourTorus L m) :=
  S.innerBox r x Q ∩ X
def collarRegion (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (n : ℕ) : Set (FourTorus L m) :=
  regionDiff (coarseCubeIndex K m' (lowerLevel L r x k + n + 1).toNat)
      (S.largeFieldOrEmpty (lowerLevel L r x k + n + 1).toNat)
      (S.trimmedRegion r x Q (lowerLevel L r x k + n + 1).toNat) ∩ ⋃₀ Q
end ScaleLabel
def unionThickened (K m' k : ℕ) (Q : Set (Set (FourTorus L m))) : Set (FourTorus L m) :=
  addCubeLayer (coarseCubeIndex K m' k) (⋃₀ Q)
end YangMills.Construction.PeriodicLattice
