import YangMills.Construction.Conventions.RealPowerAndLogarithm
import YangMills.Construction.EuclideanFunctionals.PlateBoundOfAFunctionalWithReconstruction
import YangMills.Construction.EuclideanFunctionals.PlateOperatorOfALabelAProfileAndALength
import YangMills.Construction.RotationInvariance.DiscsMotionsAndComplexPositionsOfThePlane
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open RealPlane
namespace SmallDiscProduct
open ProductInsertionOp
variable {m : SharpScale} {S : ConnFamily}
def ActsWithNormBound (σ : EuclidFunctionalWithRecon m S) (p C η : ℝ)
    (α : RealPlane → ℂ) (φ : RealPlane → ℝ)
    (B : σ.space →L[ℂ] σ.space) : Prop :=
  ActsOnReconClasses σ η α φ B ∧ ‖B‖ ≤ C * RealPower.rpowPos η (-p) * profileL1Norm α
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S) (p c : ℝ)
    (hp : 0 < p) (hc : c ∈ productBoundFractions) (C : (RealPlane → ℝ) → ℝ),
    ProductBoundWithExponent σ hp hc →
    (∀ φ ∈ realLabels, ProductBoundWith σ hp hc φ (C φ)) →
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ φ ∈ realLabels, ∀ α ∈ complexProfiles,
      tsupport α ⊆ openDiscAt 0 (c * η) →
      (∀ F ∈ finCombIn upperHalf,
        MulDefined (singleComponent (liftedProduct η α φ)) (liftedElement η F) ∧
        productTimesLifted η α φ F ∈ finCombIn upperHalf ∧
        tensorCompZero (productTimesLifted η α φ F) = 0) ∧
      (∃! B : σ.space →L[ℂ] σ.space, ActsWithNormBound σ p (C φ) η α φ B) ∧
      ActsWithNormBound σ p (C φ) η α φ (productOperator σ φ α η)
end SmallDiscProduct
end YangMills.Construction.EuclideanFunctionals
