import YangMills.Construction.ReflectionPositivity.ComplementsToTheReconstruction
import YangMills.Construction.ReflectionPositivity.ReconstructionOfTheLimitOfALatticeApproximation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open ReflectionPositivity.ReconstructionComplements
open ReflectionPositivity.Reconstruction (MatrixElementFormula VacuumProperties)
open ReflectionPositivity.LimitReconstruction (TimeSemigroupProperties SpaceShiftProperties)
open LimitConventions (octahedralGroup3 timeExtension)
def ContractionFunctionalComplements : Prop :=
  ∀ σ : SeparatedTuples.TupleFunctional, ReflectionPositivity.ContractionFunctionals.IsAdmissible σ →
    (∀ w ∈ octahedralGroup3, σ.IsInvariant (timeExtension w)) →
    ∃ h : HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm σ),
      VacuumProperties σ h ∧ TimeSemigroupProperties σ h ∧ SpaceShiftProperties σ h ∧
        MatrixElementFormula σ h ∧ MeasureClaim σ h ∧ OperatorClaim σ h ∧ SupportClaim σ h ∧
          ∀ w ∈ octahedralGroup3, UnitaryClaim σ h w ∧ IntertwiningClaim σ h w
end YangMills.Construction.TotalDensitiesGiveASystem
end
