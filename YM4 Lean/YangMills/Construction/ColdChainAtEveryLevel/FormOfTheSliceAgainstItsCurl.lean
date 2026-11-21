import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def sliceFormCurlBoundStatement : Prop :=
  ∃ (c C : ℝ) (L1 : ℕ), 0 < c ∧ 0 < C ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide →
    L1 ≤ F.blockSide → IsAdmissibleAmbient F →
    1024 ≤ m → IsOrthantRegular S m → ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
      ∀ (φ : F.Cell → ℝ) (θ del : ℝ) (p : F.Site 0), |θ| ≤ 1 / 8 → |del| ≤ 1 / 8 →
        (∀ y y', |φ y - φ y'| ≤ |del| * cellSupDist y y') →
        ∀ u : F.Site 0 → Fin 4 → imaginaryQuaternions, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) u →
          cellwiseL4Norm S (classWeight F φ θ p 0) (fun x i => (u x i : ℍ[ℝ])) +
            weightedBondL2Norm S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
              (fun x i => (u x i : ℍ[ℝ])) ≤
          C * (Real.sqrt (∑ q ∈ plaquettesOver S S 0,
                (classWeight F φ θ p 0 q.1 * ‖linearizedCurl (referenceFieldChain S V 0) u q‖) ^ 2) +
              Real.sqrt (∑ b ∈ innerBonds S F.top, (classWeight F φ θ p F.top b.1 *
                ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top b.1 b.2‖) ^ 2))
end YangMills.Construction.BlockAverages
end
