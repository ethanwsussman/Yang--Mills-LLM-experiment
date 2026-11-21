import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
def stageHullInterSubsetUpperHullStatement : Prop :=
  WeightedResponses.HoldsAtAdmissibleParameters fun Tb y =>
    ∀ (T : WeightedResponses.StageTower (Tb.stepParameters y)) (β : ℝ) (k : ℕ),
    IsTowerAtParametersMeasurable Tb y T β k →
    ∀ (s : ℕ), s ≤ k → ∀ (m : ℕ) [NeZero m]
      (u : WeightedResponses.MarkedSample (Tb.stepParameters y) s m) (G : CellGrid)
      (κ : Fin 4 → ℤ),
      G.Compatible m → stageHull T s m u ∩ interiorAtDepth (windowDepth T k s) (G.cell m κ) ⊆
        upperHull T k s m u (G.cell m κ)
end YangMills.Construction.CellWindows
end
