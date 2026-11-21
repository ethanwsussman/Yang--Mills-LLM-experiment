import YangMills.Construction.Torus.MatrixOfThePairScaledSquare
import YangMills.Construction.Weighted.GreenSquareConstants
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def QuadFormLowerBoundOn (X : Set ↥B.allSites) (M : B.LayerMat) (c : ℝ) : Prop :=
  ∀ v : ↥X → ℝ,
    c * ∑ᶠ y : ↥X, v y ^ 2 ≤ ∑ᶠ y : ↥X, ∑ᶠ y' : ↥X, v y * M y y' * v y'
def AdmissibleAvgGreenSqLowerBoundOn (W : Set D.Space) (β : Set D.Bond)
    (X : Set ↥B.allSites) (c : ℝ) : Prop :=
  ∀ ω : B.LayerFn, (∀ y, y ∉ X → ω y = 0) →
    c * B.layerSpaceNorm (((B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ 2) ω) ^ 2 ≤
      B.layerInner ω (B.extendByZeroFromBlocks W (B.admissibleAvgGreenSq W β) ω)
def AvgGreenSqDominatesScaleFourth (c : ℝ) : Prop :=
  ∀ ω : B.LayerFn,
    c * B.layerInner ω (((B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ 4) ω) ≤
      B.layerInner ω (B.avgGreenSq ω)
end SeparatedChain
def AvgGreenSqLowerBoundStatement : Prop :=
  ∀ (D : TorusData) (B : SeparatedChain D), (B.stage 0).Nonempty →
    (∀ (W : Set D.Space) (β : Set D.Bond) (X : Set ↥B.allSites),
      B.IsAdmissiblePair W β →
      (∀ y ∈ X, (y : D.Space) ∈ B.sitesIn W) →
      (∀ y ∈ X, B.blockBondSet (y : D.Space) ⊆ β) →
        B.AdmissibleAvgGreenSqLowerBoundOn W β X (lowerBoundConst 4) ∧
          B.QuadFormLowerBoundOn X (B.admissibleScaledMatrix W β) (lowerBoundConst 4)) ∧
      B.AvgGreenSqDominatesScaleFourth (lowerBoundConst 4) ∧
        IsUnit (B.avgGreenSq : Module.End ℝ B.LayerFn)
end YangMills.Construction.Weighted
