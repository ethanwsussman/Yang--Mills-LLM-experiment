import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def gaugeRemainder (S : Finset F.Cell) (V : F.GaugeField F.top) (ξ : F.Site 0 → ℍ[ℝ]) : F.Site 0 → ℍ[ℝ] :=
  fun x => GaugeMap.gaugeMap S V (referenceFieldChain S V 0)
    (covariantDiff (referenceFieldChain S V 0) ξ) x + ξ x
def gaugeMapOnDifferencesStatement : Prop :=
  ∃ (c C : ℝ) (L₁ : ℕ), 0 < c ∧ 0 < C ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide →
    L₁ ≤ F.blockSide → IsAdmissibleAmbient F →
    1024 ≤ m → IsOrthantRegular S m → ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
      (∀ u : F.Site 0 → Fin 4 → ℍ[ℝ],
        GaugeMap.CellMeanFree S V (GaugeMap.gaugeMap S V (referenceFieldChain S V 0) u)) ∧
      ∀ ξ : F.Site 0 → ℍ[ℝ], GaugeMap.CellMeanFree S V ξ →
        GaugeMap.CellMeanFree S V (gaugeRemainder S V ξ) ∧
        (∀ (φ : F.Cell → ℝ) (θ δ : ℝ) (p : F.Site 0), |θ| ≤ 1 / 8 → |δ| ≤ 1 / 8 →
          (∀ y y', |φ y - φ y'| ≤ |δ| * cellSupDist y y') →
          cellwiseL4Norm S (classWeight F φ θ p 0)
              (covariantDiff (referenceFieldChain S V 0) (gaugeRemainder S V ξ)) ≤
            C * s * cellwiseL4Norm S (classWeight F φ θ p 0)
              (covariantDiff (referenceFieldChain S V 0) ξ) ∧
          Real.sqrt (∑ z ∈ S, cellSiteNorm 4 S (classWeight F φ θ p 0) ξ z ^ 2) ≤
            C * (GaugeMap.cellSideLength F : ℝ) * cellwiseL4Norm S (classWeight F φ θ p 0)
              (covariantDiff (referenceFieldChain S V 0) ξ) ∧
          (∀ z₀ ∈ S, cellBondNorm 4 S (classWeight F φ θ p 0)
              (covariantDiff (referenceFieldChain S V 0) (gaugeRemainder S V ξ)) z₀ ≤
            C * s * ∑ z ∈ cellBall S z₀ 22, cellBondNorm 4 S (classWeight F φ θ p 0)
              (covariantDiff (referenceFieldChain S V 0) ξ) z) ∧
          ∀ z ∈ S, cellSiteNorm 4 S (classWeight F φ θ p 0) ξ z ≤
            C * (GaugeMap.cellSideLength F : ℝ) * cellBondNorm 4 S (classWeight F φ θ p 0)
              (covariantDiff (referenceFieldChain S V 0) ξ) z) ∧
        (∀ B : ℝ, (∀ z ∈ S, cellBondNorm 3 S (fun _ => 1)
            (covariantDiff (referenceFieldChain S V 0) ξ) z ≤ B) →
          ∀ z ∈ S, cellBondNorm 3 S (fun _ => 1)
            (covariantDiff (referenceFieldChain S V 0) (gaugeRemainder S V ξ)) z ≤ C * s * B) ∧
        ∀ z ∈ S, cellSiteNorm 3 S (fun _ => 1) ξ z ≤
            C * (GaugeMap.cellSideLength F : ℝ) * cellBondNorm 3 S (fun _ => 1)
              (covariantDiff (referenceFieldChain S V 0) ξ) z ∧
          cellSiteNorm 12 S (fun _ => 1) ξ z ≤
            C * cellBondNorm 3 S (fun _ => 1) (covariantDiff (referenceFieldChain S V 0) ξ) z
end YangMills.Construction.BlockAverages
end
