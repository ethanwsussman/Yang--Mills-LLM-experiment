import YangMills.Construction.LawInAState.ResponsesInOneBox
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
open TorusFields WeightedResponses BoxResponses
open InfiniteLattice (AmbientSpace)
def responseMomentsStatement : Prop :=
  HoldsForShapes fun Tb y Kr Xi vt => ∃ Cm d₀ : ℝ, 0 ≤ Cm ∧ 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
    ∀ (K : ℕ) (β : ℝ) (α : ℕ → ℝ) (T : StageTower (Tb.stepParameters y)), IsStateChain Tb y Kr Xi d K β α T →
    ∀ (k : ℕ) (x : ℝ), k = separationLevel (Tb.stepParameters y) β K d →
    x = couplingAtSeparation (Tb.stepParameters y) β K d →
      IsProbabilityMeasure (stageLaw T β K k) ∧
      Measurable (stageState T k (boxSide (Tb.stepParameters y).side K k)) ∧
      ∀ f h : AmbientSpace → ℝ, IsNormalizedTestPair d vt f h → ∀ v : Fin 4 → ℤ,
        (MemLp (centeredBoxResponse T β α K k (translateBy (Tb.stepParameters y).side K k v f)) 64 (stageLaw T β K k) ∧
          eLpNorm (centeredBoxResponse T β α K k (translateBy (Tb.stepParameters y).side K k v f)) 64
            (stageLaw T β K k) ≤ ENNReal.ofReal (x ^ Cm)) ∧
        (MemLp (centeredBoxResponse T β α K k (translateBy (Tb.stepParameters y).side K k v h)) 64 (stageLaw T β K k) ∧
          eLpNorm (centeredBoxResponse T β α K k (translateBy (Tb.stepParameters y).side K k v h)) 64
            (stageLaw T β K k) ≤ ENNReal.ofReal (x ^ Cm))
end YangMills.Construction.StateLaws
end
