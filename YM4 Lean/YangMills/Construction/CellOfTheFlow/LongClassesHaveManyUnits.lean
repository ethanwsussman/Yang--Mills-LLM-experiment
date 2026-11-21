import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps RenormalizationStepParameters WeightedResponses TorusFields
def longSupportUnitCountStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (j d : ℕ),
    IsTowerAtParametersMeasurable Tb y T β (j + 1 + d) → ∀ (e : ℕ) (G : CellGrid) (κ : Fin 4 → ℤ)
      (S : Finset (Fin 4 → ℤ)) (θ : ClusterSupport (Tb.stepParameters y).side
        (fineSide (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e))),
      G.side = baseCellSide (Tb.stepParameters y).side (stageRange T (j + 1 + d)) →
      2 * G.side ≤ 2 * (Tb.stepParameters y).side ^ e →
      S ⊆ G.sameParityIndices (2 * (Tb.stepParameters y).side ^ e) κ →
      (∀ κ' ∈ S, IsLongWithin (Tb.stepParameters y).side (stageRange T j) (windowLength T (j + 1 + d) j) θ
        (sitesInBlocks (Tb.stepParameters y).side (interiorAtDepth (blockDepth T (j + 1 + d) j)
          (cellBelow (Tb.stepParameters y).side d (2 * (Tb.stepParameters y).side ^ e)
            (G.cell (2 * (Tb.stepParameters y).side ^ e) κ'))))) →
      100 * (d + 1) * S.card ≤ supportUnitCount (Tb.stepParameters y).side (stageRange T j) θ
end YangMills.Construction.CellWindows
end
