import YangMills.Construction.TwoPoints.FourShapesAndTheShapeConstant
import YangMills.Construction.TwoPoints.FromThePlaneKernelsToTheOrthogonalGroup
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TwoPoints.Shapes (shapeConst)
def HasRotationInvarianceConditions (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) : Prop :=
  (∀ R : Matrix.orthogonalGroup (Fin 4) ℝ, ∀ f ∈ compactC1Real, ∀ g ∈ compactC1Real,
    DisjointSupports f g →
      S (rotateFun R f) (rotateFun R g) = S f g) ∧
  ∃ s : ℝ → ℝ, IsRealAnalyticOnIoi s ∧ HasRadialProfile S s
def SmallerShape.Statement : Prop :=
  ∀ θ : ℝ, 0 < θ → θ ≤ shapeConst →
    (∀ d : ℝ, 0 < d → YangMills.Construction.TestFunctions.separatedPairsR4 d shapeConst ⊆
      YangMills.Construction.TestFunctions.separatedPairsR4 d θ) ∧
    (∀ (M : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ), IsDisjointForm S →
      IsAdmissibleForm M S →
      ∀ (d₀ : ℝ) (u : ℝ → ℝ), IsSmallPositiveWith S θ d₀ u →
        IsSmallPositiveWith S shapeConst d₀ u ∧
          HasRotationInvarianceConditions S) ∧
    θ ∈ Ioc (0 : ℝ) 1 ∧
    ∀ (M : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ), IsDisjointForm S →
      IsAdmissibleForm M S →
      IsSmallPositiveAtShape S θ → HasRotationInvarianceConditions S
end YangMills.Construction.TwoPoints
end
