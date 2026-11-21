import YangMills.Construction.CellOfTheFlow.NoiseOfTheChain
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses ResponseInTheExpansion BlockAverages LumpContours
def lowerSumLocalStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (S : ChainSampler T)
    (β s₀ s₁ : ℝ) (k : ℕ), IsTowerAtParametersMeasurable Tb y T β k →
    (∀ s, (S s).IsFaithful) → ∀ (m : ℕ) [NeZero m] (G : CellGrid) (κ : Fin 4 → ℤ), G.Compatible m →
      (Tb.stepParameters y).side ∣ m → 64 ≤ m → LowerSumIsLocal T S s₀ s₁ k m (G.cell m κ)
end YangMills.Construction.CellWindows
end
