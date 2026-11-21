import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
structure IsSliceCriticalPoint (a θ del Ca rL CL s : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (U : ChainChart F) : Prop where
  mem_slice : GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) U.fine
  small : supWeightedNorm S del (referenceFieldChain S V) U ≤ rL
  critical : ∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) V U A
  unique : ∀ U' : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) U'.fine →
    supWeightedNorm S del (referenceFieldChain S V) U' ≤ rL →
    (∀ A : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
      IsStationaryAlong a S (referenceFieldChain S V) V U' A) → ChartEqOnBonds S U U'
  split : ∃ Ulin Urest : ChainChart F, ChartEqOnBonds S U (chartSum Ulin Urest) ∧
    ∀ (p : F.Site 0) (y0 : F.Cell) (θ' : ℝ), θ' = θ ∨ θ' = 0 →
      weightedNorm S (referenceFieldChain S V) Ulin (decayWeights F del θ' p y0) ≤ Ca * s ∧
      weightedNorm S (referenceFieldChain S V) Urest (decayWeights F del θ' p y0) ≤ CL * s ^ 2
  floor : ∀ A : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
    (1 / 4) * quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F) ≤
      deriv (deriv fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ) V) 0
def sliceCriticalPointStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ θ del Ca : ℝ, 0 < θ ∧ θ ≤ 1 / 8 ∧ 0 < del ∧ del ≤ 1 / 8 ∧ 0 < Ca ∧
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ rL sL CL : ℝ, 0 < rL ∧ 0 < sL ∧ 0 < CL ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ sL → IsCold S F.top s V →
          ∃ U : ChainChart F, IsSliceCriticalPoint a θ del Ca rL CL s S V U
end BlockAverages
end YangMills.Construction
end
