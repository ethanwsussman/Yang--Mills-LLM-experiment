import YangMills.Construction.CellOfTheFlow.MajorantOfAState
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps TorusFields WeightedResponses RenormalizationStepParameters
def componentDepth {q : StepParameters} (T : StageTower q) (k : ℕ) : ℕ → ℕ
  | 0 => 2 ^ 4 * stageRange T k
  | d + 1 => q.side * (componentDepth T k d - 1)
def deepComponentsInLowerHullStatement : Prop :=
  HoldsAtAdmissibleParameters fun P y => ∀ (T : StageTower (P.stepParameters y)) (β : ℝ) (k : ℕ),
    IsTowerAtParametersMeasurable P y T β k →
    ∀ (s d : ℕ), s + d = k → ∀ (m : ℕ) [NeZero m] (u : MarkedSample (P.stepParameters y) s m) (G : CellGrid)
      (i : Fin 4 → ℤ), G.Compatible m → ∀ X ∈ chainComponents (stageRange T s) (stageHull T s m u),
        X ⊆ interiorAtDepth (componentDepth T k d) (G.cell m i) →
        X ⊆ lowerHull T k s m u (G.cell m i) ∧
          ∀ s₀ s₁ : ℝ, ∀ z ∈ X, lowerScore T k s₀ s₁ s m u (G.cell m i) z = siteMajorant T s₀ s₁ s m u z
end YangMills.Construction.CellWindows
end
