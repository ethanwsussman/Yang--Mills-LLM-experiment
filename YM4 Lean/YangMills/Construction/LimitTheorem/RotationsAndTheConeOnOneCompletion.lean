import YangMills.Construction.Continuum.ModulusOfStrongContinuityOnOneTuple
import YangMills.Construction.LimitTheorem.AssertionsAtGivenConstants
import YangMills.Construction.ReflectionPositivity.ComplementsToTheReconstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitTheorem.RotationsAndCone
open SeparatedTuples ReflectionPositivity.TupleForm ReflectionPositivity.ReconstructionComplements
open HilbertSpaceBasics (IsPosSemidef)
open Continuum.RotationModulus (RotationHypotheses)
def spacelikeRegion : Set (Fin 4 → ℝ) := {y | y 0 < Real.sqrt (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2)}
theorem isOpen_spacelikeRegion : IsOpen spacelikeRegion := by
  unfold spacelikeRegion
  exact isOpen_lt (continuous_apply 0) (by fun_prop)
structure RotationPremises (M : ℝ) (σ : TupleFunctional) (B : ℕ → ℝ → ℝ → ℝ)
    (hpos : IsPosSemidef (reflectionForm σ)) : Prop where
  one_le : 1 ≤ M
  hyps : RotationHypotheses M σ B
  reconstruction : HasReconstruction σ hpos
  measure : MeasureClaim σ hpos
  operators : OperatorClaim σ hpos
  marginal : MarginalClaim σ hpos
def RotationsAndConeStatement : Prop :=
  ∀ (M : ℝ) (σ : TupleFunctional) (B : ℕ → ℝ → ℝ → ℝ) (hpos : IsPosSemidef (reflectionForm σ)),
    RotationPremises M σ B hpos →
    JointSpectrumInForwardCone σ ∧ HasSpatialRotationRep σ ∧
      jointMeasure σ hpos ⟨spacelikeRegion, isOpen_spacelikeRegion.measurableSet⟩ = 0
end YangMills.Construction.LimitTheorem.RotationsAndCone
end
