import YangMills.Construction.TwoPoints.FourShapesAndTheShapeConstant
import YangMills.Construction.TwoPoints.FromThePlaneKernelsToTheOrthogonalGroup
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
open Shapes (shapeConst)
def DiagonalReflectionRotationInvariance.Statement : Prop :=
  shapeConst ∈ Ioc (0 : ℝ) 1 ∧
    ∀ (Sc : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ), IsDisjointForm S →
      IsAdmissibleForm Sc S →
      IsSmallPositiveAtShape S shapeConst →
      (∀ R : Matrix.orthogonalGroup (Fin 4) ℝ, ∀ f ∈ compactC1Real, ∀ g ∈ compactC1Real,
        DisjointSupports f g →
          S (rotateFun R f) (rotateFun R g) = S f g) ∧
      ∃ s : ℝ → ℝ, IsRealAnalyticOnIoi s ∧ HasRadialProfile S s
end YangMills.Construction.TwoPoints
end
