import YangMills.Construction.ClusterExpansionOfAStep.BasesAtABlock
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace BaseTranslations
open BlockAverages LumpContours StepCosts TorusFields TorusLumps
def translateBases {L n : ℕ} (v : Fin 4 → ℤ) (b : BaseChoice L n) : BaseChoice L n :=
  fun y => b (y + siteOfCoords (stepBlockFrame L n).top v) -
    siteOfCoords (stepBlockFrame L n).depth fun i => (L : ℤ) * v i
def TranslationPreservesBaseKernel : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (x : ℝ) (n : ℕ) [NeZero n], ℓ.n₀ ≤ n →
    ∀ (v : Fin 4 → ℤ) (W : TorusField (n * ℓ.side)) (V : TorusField n) (b : BaseChoice ℓ.side n),
      (translateBases v b ∈ baseChoices ℓ
          (fineLevelField ℓ n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W)) ↔
        b ∈ baseChoices ℓ (fineLevelField ℓ n W)) ∧
      (baseChoices ℓ
          (fineLevelField ℓ n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W))).card =
        (baseChoices ℓ (fineLevelField ℓ n W)).card ∧
      (b ∈ baseChoices ℓ (fineLevelField ℓ n W) →
        ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
            bondKernel ℓ x
              (fineLevelField ℓ n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W))
              (coarseLevelField ℓ n (TorusFields.translate (siteOfInt v) V)) (translateBases v b) c =
          ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
            bondKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V) b c)
end BaseTranslations
end YangMills.Construction
end
