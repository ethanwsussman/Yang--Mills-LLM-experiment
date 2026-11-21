import YangMills.Construction.EuclideanFunctionals.FractionsAndConstantsOfThePlateBound
import YangMills.Construction.EuclideanFunctionals.TransportOfAReconstructionAndThePlateBoundInACoordinatePlane
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ProductBoundExponent
variable {m : SharpScale} {S : ConnFamily}
def parametrixFrac (cI c : ℝ) : ℝ := min (1 / 2 * cI) (1 / 8 - c)
def cauchyFrac (c : ℝ) : ℝ := 1 / 4 * (1 / 8 - c)
def labelConst (m : SharpScale) (p C cI c : ℝ) (φ : RealPlane → ℝ) : ℝ :=
  productConst m p C (parametrixFrac cI c) (cauchyFrac c) * l1Norm φ
theorem productExponent_pos {σ : EuclidFunctionalWithRecon m S} {p C c : ℝ}
    (hI : InsertionBoundHolds σ p C c) : 0 < productExponent p := by
  have h := hI.nonneg_exponent
  unfold productExponent
  linarith
def ExponentIffConstants (σ : EuclidFunctionalWithRecon m S) {c : ℝ}
    (hc : c ∈ productBoundFractions) : Prop :=
  ∀ (p : ℝ) (hp : 0 < p), ProductBoundWithExponent σ hp hc ↔
    ∃ C : (RealPlane → ℝ) → ℝ, ProductBoundHolds σ p C c
def FractionMonotone (σ : EuclidFunctionalWithRecon m S) : Prop :=
  ∀ p : ℝ, 0 < p → ∀ C : (RealPlane → ℝ) → ℝ, (∀ φ ∈ realLabels, 0 ≤ C φ) →
    ∀ c c' : ℝ, 0 < c' → c' ≤ c → c < 1 / 4 →
      ProductBoundHolds σ p C c → ProductBoundHolds σ p C c'
def ConeInsertionYieldsBound (σ : EuclidFunctionalWithRecon m S) {c : ℝ}
    (hc : c ∈ productBoundFractions) {p C cI : ℝ} (hI : InsertionBoundHolds σ p C cI) : Prop :=
  ProductBoundParams p C cI c (parametrixFrac cI c) (cauchyFrac c) ∧
    ProductBoundWithExponent σ (productExponent_pos hI) hc ∧
    ∀ φ ∈ realLabels,
      ProductBoundWith σ (productExponent_pos hI) hc φ (labelConst m p C cI c φ)
def ConeInsertionYieldsImagePlaneBound (σ : EuclidFunctionalWithRecon m S)
    {c : ℝ} (hc : c ∈ productBoundFractions) {p C cI : ℝ}
    (hI : InsertionBoundHolds σ p C cI) : Prop :=
  ∀ w : hyperoctahedral,
    ImagePlaneProductBound σ w (productExponent_pos hI) hc ∧
      ∀ φ ∈ realLabels,
        ImagePlaneProductBoundWith σ w (productExponent_pos hI) hc φ
          (labelConst m p C cI c φ)
def Main : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S),
    (∀ (c : ℝ) (hc : c ∈ productBoundFractions), ExponentIffConstants σ hc) ∧
    FractionMonotone σ ∧
    ∀ (c : ℝ) (hc : c ∈ productBoundFractions), c < 1 / 8 → σ.ConeCondition →
      ∀ (p C cI : ℝ) (hI : InsertionBoundHolds σ p C cI),
        ConeInsertionYieldsBound σ hc hI ∧
          ConeInsertionYieldsImagePlaneBound σ hc hI
end YangMills.Construction.EuclideanFunctionals.ProductBoundExponent
