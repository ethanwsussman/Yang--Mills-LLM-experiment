import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.ComplexChain
import YangMills.Construction.ColdChainAtEveryLevel.CoordinatesAtTheLevels
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def complexTwistedTop {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (ζ : Fin k → ℂ) (V : F.GaugeField F.top) : F.ComplexField F.top :=
  fun y i => NormedSpace.exp (∑ l, if c l = (y, i) then
      ζ l • YangMills.Construction.ComplexifiedQuaternions.ofQuat (X l : ℍ[ℝ]) else 0) * ofUnit (V y i)
def complexChainOverTop (R : F.FieldChain) (W : ComplexChainChart F) (T : F.ComplexField F.top) :
    (j : ℕ) → F.ComplexField j := by
  classical exact Function.update (complexChartField R W) F.top T
def complexBondTermOverTop (R : F.FieldChain) (W : ComplexChainChart F) (T : F.ComplexField F.top) (j : ℕ)
    (c : F.Site (j + 1) × Fin 4) : ℂ :=
  complexBlockFit (complexGaugedContourAverage (complexChainOverTop R W T j) (complexBalancingGauges R W (j + 1)) c)
    (complexChainOverTop R W T (j + 1) c.1 c.2)
def complexTotalOverTop (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (W : ComplexChainChart F)
    (T : F.ComplexField F.top) : ℂ :=
  ∑ p ∈ innerPlaquettes S 0, complexPlaquetteTerm (complexChartField R W 0) p +
    (a : ℂ) * ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1), complexBondTermOverTop R W T j c
def complexSpan {m : ℕ} (A : Fin m → ChainChart F) (t : Fin m → ℂ) : ComplexChainChart F :=
  ⟨chartShiftMulti (zeroChart F) A fun l => (t l).re, chartShiftMulti (zeroChart F) A fun l => (t l).im⟩
def complexChartMove (W : ComplexChainChart F) (A : ChainChart F) (τ : ℂ) : ComplexChainChart F :=
  ⟨chartMove W.re A τ.re, chartMove W.im A τ.im⟩
def complexChartSub (W W' : ComplexChainChart F) : ComplexChainChart F :=
  ⟨chartMove W.re W'.re (-1), chartMove W.im W'.im (-1)⟩
def complexFirstVariation (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (W : ComplexChainChart F)
    (T : F.ComplexField F.top) (A : ChainChart F) : ℂ :=
  deriv (fun τ : ℂ => complexTotalOverTop a S R (complexChartMove W A τ) T) 0
def complexReferenceSecondDeriv (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top)
    (W : ComplexChainChart F) (A : ChainChart F) : ℂ :=
  (referenceSecondDeriv a S R V W.re A : ℂ) + Complex.I * (referenceSecondDeriv a S R V W.im A : ℂ)
def complexSupWeightedNorm (S : Finset F.Cell) (δ : ℝ) (R : F.FieldChain) (W : ComplexChainChart F) : ℝ :=
  supWeightedNorm S δ R W.re + supWeightedNorm S δ R W.im
def complexWeightedNorm (S : Finset F.Cell) (R : F.FieldChain) (W : ComplexChainChart F)
    (w : F.SiteWeights) : ℝ :=
  weightedNorm S R W.re w + weightedNorm S R W.im w
structure TwistedTotalBounds (a θ δ Ca c C s : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) {k : ℕ}
    (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) : Prop where
  analytic : ∀ (m : ℕ) (A : Fin m → ChainChart F) (t : Fin m → ℂ) (ζ : Fin k → ℂ),
    complexSupWeightedNorm S δ (referenceFieldChain S V) (complexSpan A t) ≤ c → ∑ l, ‖ζ l‖ ≤ c →
    AnalyticAt ℂ (fun q : (Fin m → ℂ) × (Fin k → ℂ) =>
      complexTotalOverTop a S (referenceFieldChain S V) (complexSpan A q.1) (complexTwistedTop b X q.2 V)) (t, ζ)
  lipschitz : ∀ (W W' : ComplexChainChart F) (ζ : Fin k → ℂ),
    complexSupWeightedNorm S δ (referenceFieldChain S V) W ≤ c →
    complexSupWeightedNorm S δ (referenceFieldChain S V) W' ≤ c → ∑ l, ‖ζ l‖ ≤ c →
    ∀ (φ : F.Cell → ℝ) (θ' : ℝ) (p : F.Site 0), (θ' = θ ∨ θ' = 0 ∨ θ' = -θ) →
      (∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y') → ∀ A : ChainChart F,
      ‖complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) A -
          complexFirstVariation a S (referenceFieldChain S V) W' (complexTwistedTop b X ζ V) A -
          complexReferenceSecondDeriv a S (referenceFieldChain S V) V (complexChartSub W W') A‖ ≤
        C * (complexSupWeightedNorm S δ (referenceFieldChain S V) W +
            complexSupWeightedNorm S δ (referenceFieldChain S V) W' + ∑ l, ‖ζ l‖) *
          complexWeightedNorm S (referenceFieldChain S V) (complexChartSub W W') (classWeight F φ θ' p) *
          weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p))
  localTwist : ∀ (W : ComplexChainChart F) (ζ ζ' : Fin k → ℂ) (l : Fin k),
    complexSupWeightedNorm S δ (referenceFieldChain S V) W ≤ c → ∑ l, ‖ζ l‖ ≤ c → ∑ l, ‖ζ' l‖ ≤ c →
    (∀ l', l' ≠ l → ζ l' = ζ' l') → ∀ A : ChainChart F,
      ‖complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) A -
          complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ' V) A‖ ≤
        C * ‖ζ l - ζ' l‖ * localNorm S (referenceFieldChain S V) A (constOneWeights F) (b l).1
  twistSource : ∀ ζ : Fin k → ℝ, ∑ l, |ζ l| ≤ c → ∃ l1 : ChainChart F → ℝ,
    (∀ A A', l1 (chartMove A A' 1) = l1 A + l1 A') ∧ (∀ (t : ℝ) A, l1 (chartMove (zeroChart F) A t) = t * l1 A) ∧
    ∀ (A : ChainChart F) (p : F.Site 0) (y0 : F.Cell) (θ' : ℝ), θ' = θ ∨ θ' = 0 →
      |l1 A| ≤ Ca * (∑ l, |ζ l|) * weightedNorm S (referenceFieldChain S V) A
        (invertedWeights (decayWeights F δ θ' p y0)) ∧
      ‖complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F))
            (complexTwistedTop b X (fun l => (ζ l : ℂ)) V) A -
          complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F))
            (complexTwistedTop b X 0 V) A -
          (l1 A : ℂ)‖ ≤
        C * (s + ∑ l, |ζ l|) ^ 2 * weightedNorm S (referenceFieldChain S V) A
          (invertedWeights (decayWeights F δ θ' p y0))
end YangMills.Construction.BlockAverages
end
