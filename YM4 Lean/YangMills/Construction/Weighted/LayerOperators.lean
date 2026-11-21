import YangMills.Construction.Weighted.FunctionSpaces
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Weighted
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
abbrev LayerOp : Type := B.LayerFn →ₗ[ℝ] B.LayerFn
abbrev LayerMat : Type := ↥B.allSites → ↥B.allSites → ℝ
def kernel (K : B.LayerOp) : B.LayerMat :=
  fun y y' => K (({y'} : Set ↥B.allSites).indicator 1) y
def basisVec (y : ↥B.allSites) : B.LayerFn :=
  ({y} : Set ↥B.allSites).indicator fun _ => B.siteScale y ^ (-2 : ℤ)
def matrixOf (K : B.LayerOp) : B.LayerMat :=
  fun y y' => B.layerInner (B.basisVec y) (K (B.basisVec y'))
def restrictToBlocks (W : Set D.Space) : B.LayerFn →ₗ[ℝ] ↥(B.layerSpaceOn W) where
  toFun w := ⟨{y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn W}.indicator w,
    fun y hy => indicator_of_notMem
      (show y ∉ {y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn W} from hy) w⟩
  map_add' w w' := Subtype.ext (indicator_add _ w w')
  map_smul' c w := Subtype.ext (indicator_const_smul _ c w)
def extendByZeroFromBlocks (W : Set D.Space)
    (K : ↥(B.layerSpaceOn W) →ₗ[ℝ] ↥(B.layerSpaceOn W)) : B.LayerOp :=
  (B.layerSpaceOn W).subtype ∘ₗ K ∘ₗ B.restrictToBlocks W
def extendByZeroFromSubset (X : Set ↥B.allSites) (K : (↥X → ℝ) →ₗ[ℝ] (↥X → ℝ)) : B.LayerOp :=
  Function.ExtendByZero.linearMap ℝ (Subtype.val : ↥X → ↥B.allSites) ∘ₗ K ∘ₗ
    LinearMap.funLeft ℝ ℝ (Subtype.val : ↥X → ↥B.allSites)
def expWeightedMatrixNorm (δ : ℝ) (M : B.LayerMat) : ℝ :=
  max (⨆ y, ∑ᶠ y', |M y y'| * Real.exp (δ * B.weightedDistance y y'))
    (⨆ y', ∑ᶠ y, |M y y'| * Real.exp (δ * B.weightedDistance y y'))
def expWeightedOpNorm (δ : ℝ) (K : B.LayerOp) : ℝ := B.expWeightedMatrixNorm δ (B.matrixOf K)
end SeparatedChain
end Weighted
end YangMills.Construction
