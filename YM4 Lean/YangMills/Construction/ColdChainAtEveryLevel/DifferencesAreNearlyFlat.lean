import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def covariantDiffNearlyFlatStatement : Prop :=
  ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ (φ : F.Cell → ℝ) (θ η : ℝ) (p : F.Site 0), |θ| ≤ 1 / 8 → |η| ≤ 1 / 8 →
          (∀ y y', |φ y - φ y'| ≤ |η| * cellSupDist y y') →
          ∀ (ξ : F.Site 0 → ℍ[ℝ]) (v : F.Site 0 → Fin 4 → imaginaryQuaternions),
            GaugeMap.CellMeanFree S V ξ →
            (∀ x i, ((v x i : imaginaryQuaternions) : ℍ[ℝ]) = covariantDiff (referenceFieldChain S V 0) ξ x i) →
            Real.sqrt (∑ q ∈ plaquettesOver S S 0, (classWeight F φ θ p 0 q.1 *
                ‖linearizedCurl (referenceFieldChain S V 0) v q‖) ^ 2) +
              Real.sqrt (∑ c ∈ innerBonds S F.top, (classWeight F φ θ p F.top c.1 *
                ‖linearPart (referenceFieldChain S V) (baseOnlyChart v) F.top c.1 c.2‖) ^ 2) ≤
            C * s * cellwiseL4Norm S (classWeight F φ θ p 0) (fun x i => v x i)
end YangMills.Construction.BlockAverages
end
