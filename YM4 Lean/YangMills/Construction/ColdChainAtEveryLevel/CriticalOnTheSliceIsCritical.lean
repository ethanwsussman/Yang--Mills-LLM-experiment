import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def criticalOnSliceStatement : Prop :=
  ∀ a del : ℝ, 0 < a → 0 < del → del ≤ 1 / 8 → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c : ℝ, 0 < c ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ U : ChainChart F, supWeightedNorm S del (referenceFieldChain S V) U ≤ c →
          (∀ A : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
            IsStationaryAlong a S (referenceFieldChain S V) V U A) →
          ∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) V U A
end YangMills.Construction.BlockAverages
end
