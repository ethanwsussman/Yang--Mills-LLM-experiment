import YangMills.Construction.CellOfTheFlow.NoiseOfTheChain
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps TorusFields RenormalizationStepParameters StepSettings WeightedResponses BlockAverages
def cellEventIsLocalStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (S : ChainSampler T) (β : ℝ)
    (k : ℕ), IsTowerAtParametersMeasurable Tb y T β k →
    (∀ s, (S s).IsFaithful) → ∀ (m : ℕ) [NeZero m] (G : CellGrid) (κ : Fin 4 → ℤ),
      (Tb.stepParameters y).side ∣ m → 64 ≤ m → G.Compatible m →
      CellEventIsLocal T S k m (G.cell m κ)
end YangMills.Construction.CellWindows
end
