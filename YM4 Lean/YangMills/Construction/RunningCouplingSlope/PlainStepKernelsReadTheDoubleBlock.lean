import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import YangMills.Construction.Towers.IteratedAveragesOfSmallRegularFields
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
open Tower.IteratedSmallFieldMeans (smallFormBall)
variable {L n k : ℕ}
def cubesOfEdge {j : ℕ} (c : Edge L n k j) : Set (PeriodicLattice.FourTorus L n) :=
  PeriodicLattice.refinedBlock j c.source ∪ PeriodicLattice.refinedBlock j c.target
def StepKernelLocality : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ n k : ℕ, 0 < n → 1 ≤ k →
    (∀ j ≤ k, ∀ y : Vertex L n k j,
      (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock j y) ∧
    ∀ j < k, ∀ (ι' : Fin 3 × PositiveEdge L n k (j + 1)) (ι : Fin 3 × PositiveEdge L n k j),
      ∀ v ∈ smallFormBall L n k ρ,
        (meanStepKernel L n k (remainderGaugeField v) j ι' ι ≠ 0 →
          cubesOfEdge ι.2.1 ⊆ cubesOfEdge ι'.2.1) ∧
        ∀ v' ∈ smallFormBall L n k ρ, EqOn v v' (PeriodicLattice.bondsInside (cubesOfEdge ι'.2.1)) →
          meanStepKernel L n k (remainderGaugeField v) j ι' ι =
            meanStepKernel L n k (remainderGaugeField v') j ι' ι
end YangMills.Construction.RunningCouplingSlope
end
