import YangMills.Construction.ReflectionPositivity.FromFivePointInequalitiesAtSmallTimesToTheCone
import YangMills.Construction.ReflectionPositivity.LatticeRepresentativesAndLatticeApproximations
import YangMills.Construction.ReflectionPositivity.ReconstructionOfTheLimitOfALatticeApproximation
import Mathlib
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitMomentumBound
def MomentumBoundAssertions (L : ℕ) (σ : SeparatedTuples.TupleFunctional) : Prop :=
  ContractionFunctionals.IsAdmissible σ ∧ LimitReconstruction.ContractsAtAllTimes σ ∧
    ∃ h : HilbertSpaceBasics.IsPosSemidef (TupleForm.reflectionForm σ),
      Reconstruction.VacuumProperties σ h ∧ LimitReconstruction.TimeSemigroupProperties σ h ∧
        LimitReconstruction.SpaceShiftProperties σ h ∧ Reconstruction.MatrixElementFormula σ h ∧
        ∀ i : Fin 3,
          (∀ t : ℝ≥0, (t : ℝ) ∈ SeparatedTuples.posAdicGridPoints L →
              SmallTimeCone.HeatMomentumInequalityAt σ h i t) ∧
            PairMeasureOperators.HamiltonianDominatesMomentum σ h i ∧
            SmallTimeCone.DomainInclusion σ h i ∧ SmallTimeCone.FormBound σ h i ∧
            SmallTimeCone.GroundStateInvariance σ h i
def MomentumBoundTheorem : Prop :=
  (∀ (D : AxisMirror.MirrorData) (T : LimitConventions.ApproxTriple D.L)
      (σ : SeparatedTuples.TupleFunctional),
    ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM D T →
      LimitConventions.ApproxTriple.IsReflPos T →
      LimitConventions.ApproxTriple.ConvergesTo T σ → MomentumBoundAssertions D.L σ) ∧
  ∀ (D : AxisMirror.MirrorData) (T : LimitConventions.ApproxTriple D.L)
      (σ : SeparatedTuples.TupleFunctional),
    LimitConventions.ApproxTriple.IsReflPos T →
      LimitConventions.ApproxTriple.ConvergesTo T σ → MomentumBoundAssertions D.L σ
end YangMills.Construction.ReflectionPositivity.LimitMomentumBound
