import YangMills.Construction.EuclideanFunctionals.InsertionBoundAndPlateBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals
structure IsLiftedProductDatum (c η : ℝ) (α : RealPlane → ℂ) (φ : RealPlane → ℝ) : Prop where
  fraction_pos : 0 < c
  fraction_lt_quarter : c < 1 / 4
  height_pos : 0 < η
  height_le_one : η ≤ 1
  label_mem : φ ∈ realLabels
  profile_mem : α ∈ complexProfiles
  tsupport_subset : tsupport α ⊆ planeStrip c η
def liftedProduct (η : ℝ) (α : RealPlane → ℂ) (φ : RealPlane → ℝ) : R4 → ℂ :=
  (EuclidMotion.transl ((η / 4) • timeVec)).actFn (productFunction α φ)
def liftedElement (η : ℝ) (A : FreeSep) : FreeSep :=
  (EuclidMotion.transl ((η / 2) • timeVec)).actFree A
def productTimesLifted (η : ℝ) (α : RealPlane → ℂ) (φ : RealPlane → ℝ) (A : FreeSep) :
    FreeSep :=
  freeMul (singleComponent (liftedProduct η α φ)) (liftedElement η A)
end EuclideanFunctionals
end YangMills.Construction
