import YangMills.Construction.CellOfTheFlow.MirrorCopiesOfAGrid
import YangMills.Construction.CellOfTheFlow.NoiseOfTheChain
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open YangMills.Construction.WeightedResponses YangMills.Construction.RenormalizationStepParameters YangMills.Construction.TorusLumps
def cellEventProbChessboardBoundStatement : Prop :=
  HoldsAtAdmissibleParameters fun P y => ∀ (T : StageTower (P.stepParameters y)) (S : ChainSampler T) (β : ℝ) (k : ℕ),
    IsTowerAtParametersMeasurable P y T β k → (∀ s, (S s).IsFaithful) → ∀ (e : ℕ) (G : CellGrid) (i : Fin 4 → ℤ),
      G.side = baseCellSide (P.stepParameters y).side (stageRange T k) →
      2 * G.side ≤ 2 * (P.stepParameters y).side ^ e →
      i ∈ G.indices (2 * (P.stepParameters y).side ^ e) →
      Measurable (cellEventProb T S k (2 * (P.stepParameters y).side ^ e)
        (G.cell (2 * (P.stepParameters y).side ^ e) i)) ∧
      (∀ U, 0 ≤ cellEventProb T S k (2 * (P.stepParameters y).side ^ e)
          (G.cell (2 * (P.stepParameters y).side ^ e) i) U ∧
        cellEventProb T S k (2 * (P.stepParameters y).side ^ e)
          (G.cell (2 * (P.stepParameters y).side ^ e) i) U ≤ 1) ∧
      DependsOnlyOn (cellBelow (P.stepParameters y).side k _ (G.cell (2 * (P.stepParameters y).side ^ e) i))
        (cellEventProb T S k (2 * (P.stepParameters y).side ^ e)
          (G.cell (2 * (P.stepParameters y).side ^ e) i)) ∧
      chessboardNorm (CellGrid.refineBy (P.stepParameters y).side k G) β i
        (cellEventProb T S k (2 * (P.stepParameters y).side ^ e)
          (G.cell (2 * (P.stepParameters y).side ^ e) i)) ≤
          Real.exp (-((T.stage k).coupling * P.κ₁ * P.threshold ^ 2 / 2 ^ 5))
end YangMills.Construction.CellWindows
end
