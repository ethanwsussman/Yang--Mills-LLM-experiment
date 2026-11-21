import YangMills.Construction.RunningCouplingSlope.PlainSaddlesOnTheWholeLattice
import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import YangMills.Construction.Towers.LocalLinearMapsWithAPeriodicCounterpart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace FullLattice
variable {L k m : ℕ}
def normalizedMeanDifferential (V B : Tower.FullSpace.Edge L k m → Matrices.ComplexMatrix2) :
    Tower.FullSpace.Edge L k (m + 1) → Matrices.ComplexMatrix2 :=
  Tower.FullSpace.extendOddly fun c =>
    Tower.logDirectionalDeriv ℂ (fun X => normalizedMean (Tower.FullSpace.expTwist X V) c)
      (normalizedMean V c) B
end FullLattice
def NormalizedMeanDifferentialPeriodizes : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ k n : ℕ, 0 < n →
    ∀ (m : ℕ) (h : m + 1 ≤ k), ∀ V ∈ Tower.fieldsIn L n k m PeriodicLattice.complexGaugeGroup,
      (∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < ρ) →
      LocalKernels.Periodisation.IsLocalWithPeriodicCounterpart L n
        (LocalKernels.Periodisation.CellClass.edgeClass k m (Nat.le_of_succ_le h))
        (LocalKernels.Periodisation.CellClass.edgeClass k (m + 1) h)
        (3 * Tower.meshAt L k (m + 1) / 2)
        (FullLattice.normalizedMeanDifferential (LocalKernels.liftGaugeField L n k m V))
        (Tower.holLeftDifferential normalizedMean V)
end YangMills.Construction.RunningCouplingSlope
end
