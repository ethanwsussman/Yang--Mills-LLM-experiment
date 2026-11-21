import YangMills.Construction.Conventions.PositiveConstant
import YangMills.Construction.Torus.CoversAndLocalisationData
import YangMills.Construction.Weighted.CoverConstant
import YangMills.Construction.Weighted.InverseExpansionConstants
import YangMills.Construction.Weighted.LayerOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def restrictToSubset (X : Set ↥B.allSites) (K : B.LayerOp) : Module.End ℝ (↥X → ℝ) :=
  LinearMap.funLeft ℝ ℝ (Subtype.val : ↥X → ↥B.allSites) ∘ₗ K ∘ₗ
    Function.ExtendByZero.linearMap ℝ (Subtype.val : ↥X → ↥B.allSites)
def pieceSiteSet (m : D.CoverPiece) : Set ↥B.allSites := {y | (y : D.Space) ∈ B.pieceSites m}
namespace Localization
variable {B} {ι : Type*} {𝒟 : ι → D.CoverPiece} (δ : B.Localization 𝒟)
def localSqOnLayers (i : ι) : Module.End ℝ B.LayerFn :=
  B.extendByZeroFromBlocks (δ.region i) (δ.localAvgGreenSq i)
def cutLocalSq (i : ι) : Module.End ℝ B.LayerFn :=
  B.pieceIndicatorOp (𝒟 i) * δ.localSqOnLayers i * B.pieceIndicatorOp (𝒟 i)
def localSqOnPiece (i : ι) : Module.End ℝ (↥(B.pieceSiteSet (𝒟 i)) → ℝ) :=
  B.restrictToSubset (B.pieceSiteSet (𝒟 i)) (δ.localSqOnLayers i)
def cutLocalSqOnPiece (i : ι) : Module.End ℝ (↥(B.pieceSiteSet (𝒟 i)) → ℝ) :=
  B.restrictToSubset (B.pieceSiteSet (𝒟 i)) (δ.cutLocalSq i)
def localInv (i : ι) : Module.End ℝ B.LayerFn :=
  B.extendByZeroFromSubset (B.pieceSiteSet (𝒟 i)) (Ring.inverse (δ.localSqOnPiece i))
def approxInverse : Module.End ℝ B.LayerFn :=
  ∑ᶠ i, B.pieceCutoffOp (𝒟 i) * δ.localInv i * B.pieceCutoffOp (𝒟 i)
open Classical in
def errorBlock (i i' : ι) : Module.End ℝ B.LayerFn :=
  if i = i' then
    (B.pieceCutoffOp (𝒟 i) * δ.cutLocalSq i -
        δ.cutLocalSq i * B.pieceCutoffOp (𝒟 i)) +
      B.pieceIndicatorOp (𝒟 i) * (δ.localSqOnLayers i - B.avgGreenSq) *
        B.pieceCutoffOp (𝒟 i)
  else
    (B.pieceIndicatorOp (𝒟 i') - 1) * B.pieceCutoffOp (𝒟 i) ^ 2 *
        B.avgGreenSq * B.pieceCutoffOp (𝒟 i')
def errorTerm (i i' : ι) : Module.End ℝ B.LayerFn :=
  δ.errorBlock i i' * δ.localInv i' * B.pieceCutoffOp (𝒟 i')
def error : Module.End ℝ B.LayerFn := ∑ᶠ i, ∑ᶠ i', δ.errorTerm i i'
def neumannTerm (n : ℕ) (ϖ : Fin (2 * n + 1) → ι) : Module.End ℝ B.LayerFn :=
  B.pieceCutoffOp (𝒟 (ϖ 0)) * δ.localInv (ϖ 0) * B.pieceCutoffOp (𝒟 (ϖ 0)) *
    (List.ofFn fun k : Fin n =>
      δ.errorTerm (ϖ ⟨2 * k + 1, by omega⟩) (ϖ ⟨2 * k + 2, by omega⟩)).prod
structure InverseExpansionHolds (c : ℝ) : Prop where
  one_sub_error_isUnit : IsUnit (1 - δ.error)
  inverse_eq : Ring.inverse B.avgGreenSq = δ.approxInverse * Ring.inverse (1 - δ.error)
  hasSum_powers : ∀ y y' : ↥B.allSites,
    HasSum (fun n : ℕ => B.kernel (δ.approxInverse * δ.error ^ n) y y')
      (B.kernel (Ring.inverse B.avgGreenSq) y y')
  hasSum_terms : ∀ y y' : ↥B.allSites,
    HasSum (fun n : ℕ => B.kernel (∑ᶠ ϖ, δ.neumannTerm n ϖ) y y')
      (B.kernel (Ring.inverse B.avgGreenSq) y y')
  sum_terms_kernel_le : ∀ (n : ℕ) (y y' : ↥B.allSites),
    ∑ᶠ ϖ, |B.kernel (δ.neumannTerm n ϖ) y y'| ≤
      1 / 2 * expansionConstBound 4 D.L c * (2 : ℝ)⁻¹ ^ n * B.siteScale y ^ (-4 : ℤ) *
        Real.exp (-(1 / 2 * expansionDecayRate 4 D.L) * B.weightedDistance y y')
  inverse_kernel_le : ∀ y y' : ↥B.allSites,
    |B.kernel (Ring.inverse B.avgGreenSq) y y'| ≤
      expansionConstBound 4 D.L c * B.siteScale y ^ (-4 : ℤ) *
        Real.exp (-(1 / 2 * expansionDecayRate 4 D.L) * B.weightedDistance y y')
end Localization
end SeparatedChain
def InverseExpansionTheorem : Prop :=
  (∀ L : ℕ, Blocking.FourDimOddFactor 4 L →
    0 < expansionDecayRate 4 L ∧ expansionDecayRate 4 L ≤ 1 / 32 * greenDecayRate 4 L) ∧
  Conventions.DependsOnlyThrough
    (fun q : ℕ × ℕ =>
      (expansionConstBound q.1 q.2 (coverConst q.1 q.2),
        expansionBlockSizeFloor q.1 q.2 (coverConst q.1 q.2)))
    id ∧
  ∀ (D : TorusData) (B : SeparatedChain D), (B.stage 0).Nonempty →
    ∀ (ι : Type) (𝒟 : ι → D.CoverPiece) (c : ℝ), B.IsCover c 𝒟 →
      ∀ δ : B.Localization 𝒟,
        expansionBlockSizeFloor 4 D.L c ≤ (D.blockNumber : ℝ) →
        expansionSeparationFloor 4 D.L ≤ (D.gapNumber : ℝ) * (D.blockNumber : ℝ) →
        δ.InverseExpansionHolds c
end YangMills.Construction.Weighted
