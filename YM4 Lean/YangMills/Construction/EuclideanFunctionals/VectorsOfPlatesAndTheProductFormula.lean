import YangMills.Construction.Conventions.RealPowerAndLogarithm
import YangMills.Construction.EuclideanFunctionals.PlateVectorsAndFunctionsOnTheShiftedTubes
import YangMills.Construction.RotationInvariance.ApertureTimeGapsAndComplexAnalysisInThePlane
import YangMills.Construction.RotationInvariance.DiscsMotionsAndComplexPositionsOfThePlane
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals.PlateVectorsProduct
open ForwardTube
variable {m : SharpScale} {S : ConnFamily}
def LabelsProfilesInDisc {n : ℕ} (c η : ℝ) (α : Fin n → RealPlane → ℂ)
    (φ : Fin n → RealPlane → ℝ) : Prop :=
  ∀ a, φ a ∈ realLabels ∧ α a ∈ complexProfiles ∧ tsupport (α a) ⊆ openDiscAt 0 (c * η)
def plateFactorProduct {n : ℕ} (p η : ℝ) (C : (RealPlane → ℝ) → ℝ)
    (α : Fin n → RealPlane → ℂ) (φ : Fin n → RealPlane → ℝ) : ℝ :=
  ∏ a, C (φ a) * RealPower.rpowPos η (-p) * profileL1Norm (α a)
def TimesSpaced {n : ℕ} (η : ℝ) (z : Fin n → RealPlane) : Prop :=
  (∀ hn : 0 < n, η / 4 ≤ z ⟨0, hn⟩ 0) ∧
    ∀ (k : ℕ) (hk : k + 1 < n), η / 2 ≤ z ⟨k + 1, hk⟩ 0 - z ⟨k, by omega⟩ 0
def shiftedProducts {n : ℕ} (z : Fin n → RealPlane) (α : Fin n → RealPlane → ℂ)
    (φ : Fin n → RealPlane → ℝ) (a : Fin n) : R4 → ℂ :=
  (planeShift (z a)).actFn (productFunction (α a) (φ a))
def productsOfShiftedProfiles {n : ℕ} (w : Fin n → RealPlane)
    (α : Fin n → RealPlane → ℂ) (φ : Fin n → RealPlane → ℝ) (a : Fin n) : R4 → ℂ :=
  productFunction (translateProfile (w a) (α a)) (φ a)
def successiveDiffs {q : ℕ} (w : Fin (q + 1) → RealPlane) (k : Fin q) :
    RealPlane :=
  w k.succ - w k.castSucc
def VectorBounds (σ : EuclidFunctionalWithRecon m S) (p η : ℝ)
    (C : (RealPlane → ℝ) → ℝ) {n : ℕ} (α : Fin n → RealPlane → ℂ)
    (φ : Fin n → RealPlane → ℝ) : Prop :=
  (∀ z ∈ closedShiftedForwardTube n η, ‖σ.productVec η α φ z‖ ≤ plateFactorProduct p η C α φ) ∧
    IsOpen (shiftedForwardTube n η) ∧
    Convex ℝ (shiftedForwardTube n η) ∧
    HolomorphicVectorOnTuples (shiftedForwardTube n η) (σ.productVec η α φ) ∧
    ∀ z : Fin n → RealPlane, TimesSpaced η z →
      (Pairwise fun a b =>
        Disjoint (supp (shiftedProducts z α φ a)) (supp (shiftedProducts z α φ b))) ∧
      (∀ a, supp (shiftedProducts z α φ a) ⊆ upperHalf) ∧
      (fun a => embedPlane (z a)) ∈ closedShiftedForwardTube n η ∧
      entryProduct (shiftedProducts z α φ) ∈ finCombIn upperHalf ∧
      σ.productVec η α φ (fun a => embedPlane (z a)) =
        readClass σ.recon.cls (entryProduct (shiftedProducts z α φ))
def KernelFormula (σ : EuclidFunctionalWithRecon m S) (p η : ℝ)
    (C : (RealPlane → ℝ) → ℝ) {q : ℕ} (α : Fin (q + 1) → RealPlane → ℂ)
    (φ : Fin (q + 1) → RealPlane → ℝ) : Prop :=
  HolomorphicOnTuples (shiftedForwardTubePow q η) (σ.productKernel η α φ) ∧
    (∀ v ∈ shiftedForwardTubePow q η,
      ‖σ.productKernel η α φ v‖ ≤ plateFactorProduct p η C α φ) ∧
    ∀ w : Fin (q + 1) → RealPlane, (∀ k, η / 2 ≤ successiveDiffs w k 0) →
      (Pairwise fun a b =>
        Disjoint (supp (productsOfShiftedProfiles w α φ a))
          (supp (productsOfShiftedProfiles w α φ b))) ∧
      centeredFnFree S (complexTuple (productsOfShiftedProfiles w α φ)) =
        σ.productKernel η α φ fun k => embedPlane (successiveDiffs w k)
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S) (p c : ℝ)
    (hp : 0 < p) (hc : c ∈ productBoundFractions) (C : (RealPlane → ℝ) → ℝ),
    ProductBoundWithExponent σ hp hc →
    (∀ φ ∈ realLabels, ProductBoundWith σ hp hc φ (C φ)) →
    σ.ConeCondition →
    ∀ η : ℝ, 0 < η → η ≤ 1 →
      (∀ (n : ℕ) (α : Fin n → RealPlane → ℂ) (φ : Fin n → RealPlane → ℝ),
        LabelsProfilesInDisc c η α φ → VectorBounds σ p η C α φ) ∧
      ∀ (q : ℕ) (α : Fin (q + 1) → RealPlane → ℂ) (φ : Fin (q + 1) → RealPlane → ℝ),
        LabelsProfilesInDisc c η α φ → KernelFormula σ p η C α φ
end EuclideanFunctionals.PlateVectorsProduct
end YangMills.Construction
