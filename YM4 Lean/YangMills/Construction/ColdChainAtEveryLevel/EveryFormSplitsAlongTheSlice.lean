import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def sliceDecompositionStatement : Prop :=
  ∃ (c : ℝ) (L₁ : ℕ), 0 < c ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide →
    L₁ ≤ F.blockSide → IsAdmissibleAmbient F →
    1024 ≤ m → IsOrthantRegular S m → ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
      ∀ u : F.Site 0 → Fin 4 → imaginaryQuaternions,
        ∃ (u₁ : F.Site 0 → Fin 4 → imaginaryQuaternions) (ξ : F.Site 0 → ℍ[ℝ]),
        GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) u₁ ∧ GaugeMap.CellMeanFree S V ξ ∧
        (∀ x, (ξ x).re = 0) ∧
        ∀ x i, ((u x i : imaginaryQuaternions) : ℍ[ℝ]) =
          u₁ x i + covariantDiff (referenceFieldChain S V 0) ξ x i
end YangMills.Construction.BlockAverages
end
