import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
open InfiniteLattice (AmbientSpace)
def centeredResponseMomentsStatement : Prop :=
  HoldsForShapes fun Tb y Kr Xi vt => ∃ C d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
    ∀ (K : ℕ) (β : ℝ) (al : ℕ → ℝ) (T : WeightedResponses.StageTower (Tb.stepParameters y)),
      BoxResponses.IsStateChain Tb y Kr Xi d K β al T →
    ∀ φ : AmbientSpace → ℝ, IsSeparatedBumpFamily d vt (fun _ : Fin 1 => φ) →
      MemLp (BoxResponses.centeredBoxResponse T β al K (separationLevel (Tb.stepParameters y) β K d) φ) 32
          (BoxResponses.stageLaw T β K (separationLevel (Tb.stepParameters y) β K d)) ∧
        eLpNorm (BoxResponses.centeredBoxResponse T β al K (separationLevel (Tb.stepParameters y) β K d) φ) 32
            (BoxResponses.stageLaw T β K (separationLevel (Tb.stepParameters y) β K d)) ≤
          ENNReal.ofReal (couplingAtSeparation (Tb.stepParameters y) β K d ^ C)
end YangMills.Construction.StateLaws
end
