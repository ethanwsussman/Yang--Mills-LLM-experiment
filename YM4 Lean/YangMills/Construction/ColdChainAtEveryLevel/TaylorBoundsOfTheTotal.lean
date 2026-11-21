import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
def chartZero (F : BlockFrame) : ChainChart F := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
def chartFirstVariation (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top)
    (U A : ChainChart F) : ℝ :=
  deriv (fun τ : ℝ => chartAction a S R (chartMove U A τ) V) 0
def chartSub (U U' : ChainChart F) : ChainChart F := chartMove U U' (-1)
def chartSmul (t : ℝ) (A : ChainChart F) : ChainChart F := chartMove (chartZero F) A t
def IsExpPowerPair (F : BlockFrame) (θ δ : ℝ) (φ : F.Cell → ℝ) (θ' : ℝ) : Prop :=
  (θ' = θ ∨ θ' = 0 ∨ θ' = -θ) ∧ ∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y'
structure ActionTaylorBounds (a θ δ Ca c C s : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) : Prop where
  differentiableAt : ∀ U A : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c →
    DifferentiableAt ℝ (fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ) V) 0
  variation_add : ∀ U A A' : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c →
    chartFirstVariation a S (referenceFieldChain S V) V U (chartSum A A') =
      chartFirstVariation a S (referenceFieldChain S V) V U A +
        chartFirstVariation a S (referenceFieldChain S V) V U A'
  variation_smul : ∀ (t : ℝ) (U A : ChainChart F), supWeightedNorm S δ (referenceFieldChain S V) U ≤ c →
    chartFirstVariation a S (referenceFieldChain S V) V U (chartSmul t A) =
      t * chartFirstVariation a S (referenceFieldChain S V) V U A
  hessian_add_left : ∀ U U' A : ChainChart F,
    referenceSecondDeriv a S (referenceFieldChain S V) V (chartSum U U') A =
      referenceSecondDeriv a S (referenceFieldChain S V) V U A +
        referenceSecondDeriv a S (referenceFieldChain S V) V U' A
  hessian_smul_left : ∀ (t : ℝ) (U A : ChainChart F),
    referenceSecondDeriv a S (referenceFieldChain S V) V (chartSmul t U) A =
      t * referenceSecondDeriv a S (referenceFieldChain S V) V U A
  hessian_add_right : ∀ U A A' : ChainChart F,
    referenceSecondDeriv a S (referenceFieldChain S V) V U (chartSum A A') =
      referenceSecondDeriv a S (referenceFieldChain S V) V U A +
        referenceSecondDeriv a S (referenceFieldChain S V) V U A'
  hessian_smul_right : ∀ (t : ℝ) (U A : ChainChart F),
    referenceSecondDeriv a S (referenceFieldChain S V) V U (chartSmul t A) =
      t * referenceSecondDeriv a S (referenceFieldChain S V) V U A
  hessian_le : ∀ (φ : F.Cell → ℝ) (θ' : ℝ) (p : F.Site 0), IsExpPowerPair F θ δ φ θ' →
    ∀ U A : ChainChart F, |referenceSecondDeriv a S (referenceFieldChain S V) V U A| ≤
      C * weightedNorm S (referenceFieldChain S V) U (classWeight F φ θ' p) *
        weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p))
  linear_source : ∃ l0 : ChainChart F → ℝ,
    (∀ A A', l0 (chartSum A A') = l0 A + l0 A') ∧
    (∀ (t : ℝ) A, l0 (chartSmul t A) = t * l0 A) ∧
    ∀ (A : ChainChart F) (p : F.Site 0) (y0 : F.Cell) (θ' : ℝ), θ' = θ ∨ θ' = 0 →
      |l0 A| ≤ Ca * s * weightedNorm S (referenceFieldChain S V) A
        (invertedWeights (decayWeights F δ θ' p y0)) ∧
      |chartFirstVariation a S (referenceFieldChain S V) V (chartZero F) A - l0 A| ≤
        C * s ^ 2 * weightedNorm S (referenceFieldChain S V) A
          (invertedWeights (decayWeights F δ θ' p y0))
  variation_sub_hessian_le : ∀ U U' : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c →
    supWeightedNorm S δ (referenceFieldChain S V) U' ≤ c →
    ∀ (φ : F.Cell → ℝ) (θ' : ℝ) (p : F.Site 0), IsExpPowerPair F θ δ φ θ' → ∀ A : ChainChart F,
      |chartFirstVariation a S (referenceFieldChain S V) V U A -
          chartFirstVariation a S (referenceFieldChain S V) V U' A -
          referenceSecondDeriv a S (referenceFieldChain S V) V (chartSub U U') A| ≤
        C * (supWeightedNorm S δ (referenceFieldChain S V) U + supWeightedNorm S δ (referenceFieldChain S V) U') *
          weightedNorm S (referenceFieldChain S V) (chartSub U U') (classWeight F φ θ' p) *
          weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p))
  second_deriv_le : ∀ U A : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c →
    |deriv (deriv fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ) V) 0 -
        quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F)| ≤
      C * (s + supWeightedNorm S δ (referenceFieldChain S V) U) *
        weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ^ 2
def actionTaylorBoundStatement : Prop :=
  ∀ a θ δ : ℝ, 0 < a → 0 ≤ θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → ∃ (Ca : ℝ) (L₀ : ℕ), 0 < Ca ∧
    ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
          ActionTaylorBounds a θ δ Ca c C s S V
end BlockAverages
end YangMills.Construction
end
