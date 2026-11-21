import YangMills.Construction.Lattice.PreparedSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ScaleLabel
variable {L m K m' k : ℕ} {c : ℕ → ℕ}
def smallFieldRegionAt (S : ScaleLabel L m K m' c k) (i : ℕ) : Set (FourTorus L m) :=
  open Classical in
  if h : i ∈ Set.Icc 1 k then (S.atScale ⟨i, h⟩).smallFieldRegion else ∅
def stageSmallFieldOf (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Ω'' : ℕ → Set (FourTorus L m)) (Z : Set (FourTorus L m)) (n i : ℕ) : Set (FourTorus L m) :=
  open Classical in
  if lowerLevel L r x k < (i : ℤ) ∧ (i : ℤ) ≤ lowerLevel L r x k + n then
    cubeMeet K (Ω'' i) Z ∪
      cubeMeet K (S.smallFieldRegionAt i) (complementRegion (coarseCubeIndex K m' k) Z)
  else S.smallFieldRegionAt i
def stageSmallFieldRegion (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (n i : ℕ) : Set (FourTorus L m) :=
  S.stageSmallFieldOf r x (S.trimmedDomain r x Q) (⋃₀ Q) n i
end YangMills.Construction.PeriodicLattice.ScaleLabel
