import YangMills.Construction.ColdChainAtEveryLevel.TotalAtAComplexTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def topBondGaugedAverage (R : F.FieldChain) (W : ComplexChainChart F) (e : F.Site F.top × Fin 4) :
    ComplexifiedQuaternions.ComplexQuat :=
  complexGaugedContourAverage (complexChartField R W F.depth)
    (complexBalancingGauge (complexChartField R W F.depth) (R F.depth)) e
def topBondAverageVelocity (R : F.FieldChain) (W : ComplexChainChart F) (A : ChainChart F)
    (e : F.Site F.top × Fin 4) : ComplexifiedQuaternions.ComplexQuat :=
  deriv (fun z : ℂ => topBondGaugedAverage R (complexChartMove W A z) e) 0
structure ComplexChartBounds (a θ δ c C : ℝ) (S : Finset F.Cell) (U : F.GaugeField F.top) : Prop where
  analyticAt_total : ∀ (m : ℕ) (A : Fin m → ChainChart F) (w : Fin m → ℂ),
    complexSupWeightedNorm S δ (referenceFieldChain S U) (complexSpan A w) ≤ c →
    AnalyticAt ℂ (fun q : Fin m → ℂ =>
      complexTotalOverTop a S (referenceFieldChain S U) (complexSpan A q) (complexifyField U)) w
  analyticAt_average : ∀ e ∈ innerBonds S F.top, ∀ (m : ℕ) (A : Fin m → ChainChart F) (w : Fin m → ℂ),
    complexSupWeightedNorm S δ (referenceFieldChain S U) (complexSpan A w) ≤ c →
    AnalyticAt ℂ (fun q : Fin m → ℂ => topBondGaugedAverage (referenceFieldChain S U) (complexSpan A q) e) w
  firstVariation_sub_le : ∀ W W' : ComplexChainChart F,
    complexSupWeightedNorm S δ (referenceFieldChain S U) W ≤ c →
    complexSupWeightedNorm S δ (referenceFieldChain S U) W' ≤ c →
    ∀ (ψ : F.Cell → ℝ) (θ' : ℝ) (x : F.Site 0), (θ' = θ ∨ θ' = 0 ∨ θ' = -θ) →
      (∀ y y', |ψ y - ψ y'| ≤ δ * cellSupDist y y') → ∀ A : ChainChart F,
      ‖complexFirstVariation a S (referenceFieldChain S U) W (complexifyField U) A -
          complexFirstVariation a S (referenceFieldChain S U) W' (complexifyField U) A -
          complexReferenceSecondDeriv a S (referenceFieldChain S U) U (complexChartSub W W') A‖ ≤
        C * (complexSupWeightedNorm S δ (referenceFieldChain S U) W +
            complexSupWeightedNorm S δ (referenceFieldChain S U) W') *
          complexWeightedNorm S (referenceFieldChain S U) (complexChartSub W W') (classWeight F ψ θ' x) *
          weightedNorm S (referenceFieldChain S U) A (invertedWeights (classWeight F ψ θ' x))
  velocity_sub_le : ∀ e ∈ innerBonds S F.top, ∀ W W' : ComplexChainChart F,
    complexSupWeightedNorm S δ (referenceFieldChain S U) W ≤ c →
    complexSupWeightedNorm S δ (referenceFieldChain S U) W' ≤ c →
    ∀ (ψ : F.Cell → ℝ) (θ' : ℝ) (x : F.Site 0), (θ' = θ ∨ θ' = 0 ∨ θ' = -θ) →
      (∀ y y', |ψ y - ψ y'| ≤ δ * cellSupDist y y') → ∀ A : ChainChart F,
      ‖topBondAverageVelocity (referenceFieldChain S U) W A e -
          topBondAverageVelocity (referenceFieldChain S U) W' A e‖ ≤
        C * complexWeightedNorm S (referenceFieldChain S U) (complexChartSub W W') (classWeight F ψ θ' x) *
          weightedNorm S (referenceFieldChain S U) A (invertedWeights (classWeight F ψ θ' x))
  norm_velocity_le : ∀ e ∈ innerBonds S F.top, ∀ W : ComplexChainChart F,
    complexSupWeightedNorm S δ (referenceFieldChain S U) W ≤ c →
    ∀ A : ChainChart F,
      ‖topBondAverageVelocity (referenceFieldChain S U) W A e‖ ≤
        C * localNorm S (referenceFieldChain S U) A (constOneWeights F) (enclosingCell e.1)
def complexChartBoundsStatement : Prop :=
  ∃ L₀ : ℕ, ∀ (L : ℕ) (a θ δ : ℝ), Odd L → L₀ ≤ L → 0 < a → 0 ≤ θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (U : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s U →
          ComplexChartBounds a θ δ c C S U
end YangMills.Construction.BlockAverages
end
