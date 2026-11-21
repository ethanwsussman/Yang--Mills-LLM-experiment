import YangMills.Construction.CellOfTheFlow.NoiseOfTheChain
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps TorusFields WeightedResponses RenormalizationStepParameters StepSettings
def cellEventBound (P : ParameterAssignment) (x : ℝ) : ℝ := Real.exp (-(x * P.κ₁ * P.threshold ^ 2 / 2 ^ 5))
def cellEventsRareStatement : Prop :=
  HoldsAtAdmissibleParameters fun P y => ∀ (T : StageTower (P.stepParameters y)) (β : ℝ) (k : ℕ),
    IsTowerAtParametersMeasurable P y T β k →
    ∀ (e : ℕ) (G : CellGrid) (A : Finset (Fin 4 → ℤ)),
      G.side = baseCellSide (P.stepParameters y).side (stageRange T k) →
      2 * G.side ≤ 2 * (P.stepParameters y).side ^ e →
      A ⊆ G.indices (2 * (P.stepParameters y).side ^ e) →
      markedSampleLaw T β k (2 * (P.stepParameters y).side ^ e)
          {u | ∀ i ∈ A, CellEvent T k _ u (G.cell (2 * (P.stepParameters y).side ^ e) i)} ≤
        ENNReal.ofReal (cellEventBound P (T.stage k).coupling ^ A.card) ∧
      (∀ (u : MarkedSample (P.stepParameters y) k (2 * (P.stepParameters y).side ^ e)) (i : Fin 4 → ℤ),
        (stageHull T k _ u ∩ interiorAtDepth (8 * stageRange T k)
            (G.cell (2 * (P.stepParameters y).side ^ e) i)).Nonempty →
        CellEvent T k _ u (G.cell (2 * (P.stepParameters y).side ^ e) i)) ∧
      markedSampleLaw T β k (2 * (P.stepParameters y).side ^ e)
          {u | ∀ i ∈ A, (stageHull T k _ u ∩ interiorAtDepth (8 * stageRange T k)
            (G.cell (2 * (P.stepParameters y).side ^ e) i)).Nonempty} ≤
        ENNReal.ofReal (cellEventBound P (T.stage k).coupling ^ A.card) ∧
      ∀ (S : ChainSampler T), (∀ s, (S s).IsFaithful) → ∀ i : Fin 4 → ℤ,
        CellEventIsLocal T S k (2 * (P.stepParameters y).side ^ e) (G.cell (2 * (P.stepParameters y).side ^ e) i)
end YangMills.Construction.CellWindows
end
