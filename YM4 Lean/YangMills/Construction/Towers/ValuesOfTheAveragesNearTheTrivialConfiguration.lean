import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.OneStepSchemes
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def commonSmoothingDomain (L n k i : ℕ) : Set (Edge L n k i → Matrices.ComplexMatrix2) :=
  ⋂ c : Edge L n k (i + 1),
    PeriodicLattice.smallPlaquetteFields (Averaging.smoothingRadius L) c
variable {L n k : ℕ}
structure SmoothingValuesAt (i : ℕ) (V : Edge L n k i → Matrices.ComplexMatrix2)
    (c : Edge L n k (i + 1)) : Prop where
  isGaugeField : PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup
    (PeriodicLattice.bondsInDoubleBlock c) V
  curvature_lt : PeriodicLattice.doubleBlockCurvature V c < Averaging.smoothingRadius L
  hasContourMean : ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (i + 1))),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
      PeriodicLattice.HasContourMean V y x
  contourMean_mem : ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (i + 1))),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
      PeriodicLattice.meanContourHolonomy V y x ∈ PeriodicLattice.compactGaugeGroup
  smoothing_mem : smoothingStep L n k i V c ∈ PeriodicLattice.compactGaugeGroup
def SmoothingNearTrivialField : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    (∀ i < k, IsOpenNhdOfOne (commonSmoothingDomain L n k i) ∧
      ∀ V ∈ commonSmoothingDomain L n k i, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
        SmoothingValuesAt i V c) ∧
    ∀ r ≤ k, ∀ B ∈ edgeFormSpace L n k r, ∀ V ∈ fieldSpace L n k r,
      PeriodicLattice.expTwist B V ∈ fieldSpace L n k r
end Tower
end YangMills.Construction
end
