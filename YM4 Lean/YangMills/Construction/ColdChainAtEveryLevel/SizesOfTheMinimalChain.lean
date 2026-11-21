import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
structure IsMinimalChartWithSizes (a θ δ Ca CL s : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (U : ChainChart F) : Prop where
  mem_slice : GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) U.fine
  isCritical : ∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) V U A
  action_eq : chartAction a S (referenceFieldChain S V) U V = minimalAction a S F.top V
  exists_split : ∃ Ulin Urest : ChainChart F, ChartEqOnBonds S U (chartSum Ulin Urest) ∧
    ∀ (p : F.Site 0) (y0 : F.Cell) (θ' : ℝ), θ' = θ ∨ θ' = 0 →
      weightedNorm S (referenceFieldChain S V) Ulin (decayWeights F δ θ' p y0) ≤ Ca * s ∧
      weightedNorm S (referenceFieldChain S V) Urest (decayWeights F δ θ' p y0) ≤ CL * s ^ 2
  localNorm_le : ∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ Ca * s + CL * s ^ 2
  localNorm_le_two_mul : ∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ 2 * Ca * s
def minimalChartSizesStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ θ δ Ca : ℝ, 0 < θ ∧ θ ≤ 1 / 8 ∧ 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 < Ca ∧
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ CL r0 : ℝ, 0 < CL ∧ 0 < r0 ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m →
        ∀ (r : ℝ) (V : F.GaugeField F.top), 0 < r → r ≤ r0 → IsCold S F.top r V →
          ∃ U : ChainChart F, IsMinimalChartWithSizes a θ δ Ca CL r S V U
end YangMills.Construction.BlockAverages
end
