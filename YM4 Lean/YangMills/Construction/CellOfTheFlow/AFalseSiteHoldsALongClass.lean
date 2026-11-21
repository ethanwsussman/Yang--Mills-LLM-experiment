import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps RenormalizationStepParameters WeightedResponses TorusFields
def extraHullSiteHasLongSupportStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k : ℕ),
    IsTowerAtParametersMeasurable Tb y T β k →
    ∀ (s : ℕ), s ≤ k → ∀ (m : ℕ) [NeZero m] (u : MarkedSample (Tb.stepParameters y) s m) (G : CellGrid)
      (κ : Fin 4 → ℤ),
      G.Compatible m → ∀ v ∈ upperHull T k s m u (G.cell m κ), v ∉ stageHull T s m u →
        ∃ j < s, HasLongSupport T k j s m u (G.cell m κ)
end YangMills.Construction.CellWindows
end
