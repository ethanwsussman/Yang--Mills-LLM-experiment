import YangMills.Construction.EuclideanFunctionals.GapWidthAndFractions
import YangMills.Construction.EuclideanFunctionals.InsertionBoundAndPlateBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals
def productBoundFractions : Set ℝ := Set.Ioo 0 (1 / 4)
theorem productBoundFractions_subset_stripFractionRange :
    productBoundFractions ⊆ stripFractionRange :=
  fun _ hc => ⟨hc.1, hc.2.le⟩
variable {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
def ProductBoundWith {p c : ℝ} (_hp : 0 < p) (_hc : c ∈ productBoundFractions)
    (φ : RealPlane → ℝ) (C : ℝ) : Prop :=
  ∀ η ∈ gapWidthRange, ∀ α ∈ complexProfiles, tsupport α ⊆ planeStrip c η →
    ∀ F ∈ finCombIn {y | η / 4 < y 3}, ∀ A ∈ finCombIn {y | η / 4 < y 3},
      ‖insertion S F (productFunction α φ) A‖ ≤
        C * η ^ (-p) * profileL1Norm α * heightNorm σ (η / 4) F * heightNorm σ (η / 4) A
def ProductBoundWithExponent {p c : ℝ} (hp : 0 < p) (hc : c ∈ productBoundFractions) : Prop :=
  ∀ φ ∈ realLabels, ∃ C : ℝ, ProductBoundWith σ hp hc φ C
end EuclideanFunctionals
end YangMills.Construction
