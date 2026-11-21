import YangMills.Construction.EuclideanFunctionals.InsertionBoundOfASymmetricEuclideanFunctional
import YangMills.Construction.EuclideanFunctionals.InsertionForm
import YangMills.Construction.EuclideanFunctionals.PictureOfANormal
import YangMills.Construction.EuclideanFunctionals.PulledDownElementsAndNorms
import YangMills.Construction.Rotation.ProductFunctionsOnFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals
variable {M : SharpScale} {S : ConnFamily}
def HasProductBound (σ : SymmEuclidFunctional M S) {℘ c : ℝ} (_h℘ : 0 < ℘)
    (_hc : c ∈ stripFractionRange) : Prop :=
  ∀ φ ∈ realLabels, ∃ C : ℝ, ∀ (η : ℝ) (hη : η ∈ gapWidthRange),
    ∀ α ∈ complexProfiles, tsupport α ⊆ {y : RealPlane | |y 0| < c * η} →
    ∀ F F' : freeSpanIn {x | η / 4 < x 3},
      ‖stripInsertion S F.1 (productFunction α φ) F'.1‖ ≤
        C * η ^ (-℘) * profileL1Norm α *
          loweredNorm σ (quarter_pos_of_mem_gapWidthRange hη) F *
          loweredNorm σ (quarter_pos_of_mem_gapWidthRange hη) F'
def rotatedInsertion (S : ConnFamily) (w : hyperoctahedral) (F : FreeSep) (h : R4 → ℂ)
    (F' : FreeSep) : ℂ :=
  centeredFnFree S
    (freeMul
      (freeMul ((conjReflection w).actFree (freeConj ((w : EuclidMotion).actFree F)))
        (singleComplex ((w : EuclidMotion).actFn h)))
      ((w : EuclidMotion).actFree F'))
def rotatedClass (σ : SymmEuclidFunctional M S) (w : hyperoctahedral) (A : FreeSep) :
    σ.space :=
  classOrZero σ.osData.cls ((w : EuclidMotion)⁻¹.actFree A)
def rotatedLoweredNorm (σ : SymmEuclidFunctional M S) (w : hyperoctahedral) {c : ℝ}
    (hc : 0 < c) (F : freeSpanIn {x | c < x 3}) : ℝ :=
  ‖rotatedClass σ w ((w : EuclidMotion).actFree (lowerBy hc F))‖
def HasProductBoundInRotatedPlane (σ : SymmEuclidFunctional M S) (w : hyperoctahedral)
    {℘ c : ℝ} (_h℘ : 0 < ℘) (_hc : c ∈ stripFractionRange) : Prop :=
  ∀ φ ∈ realLabels, ∃ C : ℝ, ∀ (η : ℝ) (hη : η ∈ gapWidthRange),
    ∀ α ∈ complexProfiles, tsupport α ⊆ {y : RealPlane | |y 0| < c * η} →
    ∀ F F' : freeSpanIn {x | η / 4 < x 3},
      ‖rotatedInsertion S w F.1 (productFunction α φ) F'.1‖ ≤
        C * η ^ (-℘) * profileL1Norm α *
          rotatedLoweredNorm σ w (quarter_pos_of_mem_gapWidthRange hη) F *
          rotatedLoweredNorm σ w (quarter_pos_of_mem_gapWidthRange hη) F'
end EuclideanFunctionals
end YangMills.Construction
