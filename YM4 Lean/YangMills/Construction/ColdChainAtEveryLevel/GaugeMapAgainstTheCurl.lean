import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def formPlusGaugeDiff (S : Finset F.Cell) (V : F.GaugeField F.top) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) :
    F.Site 0 → Fin 4 → ℍ[ℝ] :=
  fun x i => (u x i : ℍ[ℝ]) + covariantDiff (referenceFieldChain S V 0)
    (GaugeMap.gaugeMap S V (referenceFieldChain S V 0) (fun y k => u y k)) x i
def gaugeMapCurlBoundStatement : Prop :=
  ∃ (c C : ℝ) (L1 : ℕ), 0 < c ∧ 0 < C ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide →
    L1 ≤ F.blockSide → IsAdmissibleAmbient F →
    1024 ≤ m → IsOrthantRegular S m → ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
      ∀ u : F.Site 0 → Fin 4 → imaginaryQuaternions,
        (∀ (φ : F.Cell → ℝ) (θ δ : ℝ) (p : F.Site 0), |θ| ≤ 1 / 8 → |δ| ≤ 1 / 8 →
          (∀ y y', |φ y - φ y'| ≤ |δ| * cellSupDist y y') → ∀ z₀ ∈ S,
          cellBondNorm 4 S (classWeight F φ θ p 0) (formPlusGaugeDiff S V u) z₀ +
              cellBondNorm 2 S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
                (formPlusGaugeDiff S V u) z₀ ≤
            C * ∑ z ∈ cellBall S z₀ 22,
              (cellPlaquetteNorm 2 S (classWeight F φ θ p 0) (linearizedCurl (referenceFieldChain S V 0) u) z +
                cellTopNorm S (classWeight F φ θ p F.top)
                  (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) z) +
            C * s * ∑ z ∈ cellBall S z₀ 22,
              (cellBondNorm 4 S (classWeight F φ θ p 0) (fun x i => u x i) z +
                cellBondNorm 2 S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
                  (fun x i => u x i) z)) ∧
        ∀ B : ℝ, (∀ z ∈ S, cellPlaquetteNorm (12 / 7) S (fun _ => 1)
              (linearizedCurl (referenceFieldChain S V 0) u) z +
            cellBondNorm 3 S (fun _ => 1) (fun x i => u x i) z ≤ B) →
          ∀ z ∈ S, cellBondNorm 3 S (fun _ => 1) (formPlusGaugeDiff S V u) z ≤ C * B
end YangMills.Construction.BlockAverages
end
