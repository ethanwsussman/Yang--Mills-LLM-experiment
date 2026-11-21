import YangMills.Construction.Continuum.ModulusOfStrongContinuityOnOneTuple
import YangMills.Construction.SystemsWithFiveBounds.TheoremOverASystemWithFiveBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensities
open SeparatedTuples ReflectionPositivity.TupleForm
open HilbertSpaceBasics (IsPosSemidef)
open Continuum.RotationModulus (RotationHypotheses)
namespace RotationsActOnCompletion
def Statement : Prop :=
  ∀ (M : ℝ) (σ : TupleFunctional) (B : ℕ → ℝ → ℝ → ℝ) (h : IsPosSemidef (reflectionForm σ)), 1 ≤ M →
    RotationHypotheses M σ B → LimitTheorem.HasReconstruction σ h →
      SystemsWithFiveBounds.SpatialRotationRep σ
end RotationsActOnCompletion
end YangMills.Construction.TotalDensities
end
