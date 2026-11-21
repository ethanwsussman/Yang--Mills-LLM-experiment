import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.TotalAtAComplexTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
open ChartCoordinates
def ReferenceFormWeightedEstimate (a θ δ Ca : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) : Prop :=
  ∀ (φ : F.Cell → ℝ) (p : F.Site 0) (θ' : ℝ), (θ' = θ ∨ θ' = 0 ∨ θ' = -θ) →
    (∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y') →
    ∀ (U : ChainChart F) (f : ChainChart F → ℝ) (B : ℝ), 0 ≤ B →
      GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) U.fine →
      (∀ A : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
        referenceSecondDeriv a S (referenceFieldChain S V) V U A = f A) →
      (∀ A : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
        |f A| ≤ B * weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p))) →
      weightedNorm S (referenceFieldChain S V) U (classWeight F φ θ' p) ≤ Ca * B
def ReferenceFormWeightedEstimateHolds (a θ δ Ca : ℝ) : Prop :=
  ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c : ℝ, 0 < c ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ReferenceFormWeightedEstimate a θ δ Ca S V
structure IsComplexCriticalFamily (a θ δ C r r' s : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) {k : ℕ}
    (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (W : (Fin k → ℂ) → ComplexChainChart F) : Prop where
  mem_slice : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r' →
    GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) (W ζ).re.fine ∧
      GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) (W ζ).im.fine
  norm_le : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r' →
    complexSupWeightedNorm S δ (referenceFieldChain S V) (W ζ) ≤ C * (s + ∑ l, ‖ζ l‖)
  small : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r' →
    complexSupWeightedNorm S δ (referenceFieldChain S V) (W ζ) ≤ r
  critical : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r' → ∀ A : ChainChart F,
    GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
    complexFirstVariation a S (referenceFieldChain S V) (W ζ) (complexTwistedTop b X ζ V) A = 0
  analytic : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r' → ∀ ℓ : ChartValues S →ₗ[ℝ] ℝ,
    AnalyticAt ℂ (fun ζ' => (ℓ (chartValues S (W ζ').re) : ℂ) + Complex.I * (ℓ (chartValues S (W ζ').im) : ℂ)) ζ
  real : ∀ ζ : Fin k → ℝ, ∑ l, |ζ l| < r' →
    ChartEqOnBonds S (W fun l => (ζ l : ℂ)).im (zeroChart F)
  solve : ∀ l : ChainChart F → ℝ, (∀ A A', l (chartMove A A' 1) = l A + l A') →
    (∀ (t : ℝ) A, l (chartMove (zeroChart F) A t) = t * l A) →
    (∀ A A', ChartEqOnBonds S A A' → l A = l A') →
    ∃ U : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) U.fine ∧
      ∀ A : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
        referenceSecondDeriv a S (referenceFieldChain S V) V U A = l A
  stable : ∀ (φ : F.Cell → ℝ) (θ' : ℝ) (p : F.Site 0), (θ' = θ ∨ θ' = 0 ∨ θ' = -θ) →
    (∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y') →
    ∀ (ζ : Fin k → ℂ) (W₁ W₂ : ComplexChainChart F) (β : ℝ), ∑ l, ‖ζ l‖ < r' → 0 ≤ β →
      GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) W₁.re.fine →
      GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) W₁.im.fine →
      GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) W₂.re.fine →
      GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) W₂.im.fine →
      complexSupWeightedNorm S δ (referenceFieldChain S V) W₁ ≤ r →
      complexSupWeightedNorm S δ (referenceFieldChain S V) W₂ ≤ r →
      (∀ A : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
        ‖complexFirstVariation a S (referenceFieldChain S V) W₁ (complexTwistedTop b X ζ V) A -
            complexFirstVariation a S (referenceFieldChain S V) W₂ (complexTwistedTop b X ζ V) A‖ ≤
          β * weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p))) →
      complexWeightedNorm S (referenceFieldChain S V) (complexChartSub W₁ W₂) (classWeight F φ θ' p) ≤ C * β
def complexCriticalFamiliesStatement : Prop :=
  ∀ a θ δ Ca₄ : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca₄ →
    ReferenceFormWeightedEstimateHolds a θ δ Ca₄ → ∃ Ca : ℝ, 0 < Ca ∧
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ c₀ →
      ∃ r' s₀ : ℝ, 0 < r' ∧ r' ≤ r ∧ 0 < s₀ ∧
        ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
          IsOrthantRegular S m →
          ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ s₀ → IsCold S F.top s V →
            ∀ (k : ℕ) (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
              TwistedTotalBounds a θ δ Ca c₀ C s S V b X ∧
              ∃ W : (Fin k → ℂ) → ComplexChainChart F, IsComplexCriticalFamily a θ δ C r r' s S V b X W
end YangMills.Construction.BlockAverages
end
