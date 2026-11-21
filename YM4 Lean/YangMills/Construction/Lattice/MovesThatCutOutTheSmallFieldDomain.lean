import YangMills.Construction.Lattice.SmallFieldDomainOfAStep
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.ParameterChoice
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubesOfStep
universe u
variable (c : ChoiceUpToDegreeConstants) {m : ℕ} (K : ℕ) (x : ℕ → ℝ)
def blockFieldAt (k : ℕ) (V : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2 :=
  blockAverageStep (Averaging.smoothingRadius c.L) k V
section Outcomes
def initialDensityOutcomes : Set (Set (FourTorus c.L m)) :=
  {P | ∃ C ⊆ partitionCubesIn (densityPartitionIndex c K x 0) (univ : Set (FourTorus c.L m)),
    P = ⋃₀ C}
end Outcomes
def initialPlaquetteRegionOf (P₀ : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  complementRegion (coarsePartitionIndex c K x 0)
    (coarseCollar c K x 0 (coarseCubeHull c K x 0 P₀) 1)
def initialGaugeRegionOf (P₀ P₁ : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  gaugeFixedRegion c K x 0 P₁ (coarseCollar c K x 0 (coarseCubeHull c K x 0 P₀) 2)
end YangMills.Construction.PeriodicLattice.CubesOfStep
