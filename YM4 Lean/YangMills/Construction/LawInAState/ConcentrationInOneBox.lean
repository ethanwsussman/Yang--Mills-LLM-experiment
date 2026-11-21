import YangMills.Construction.LawInAState.ResponsesInOneBox
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
open TorusLumps RenormalizationStepParameters WeightedResponses BoxResponses
open InfiniteLattice (AmbientSpace)
def boxConcentrationStatement : Prop :=
  HoldsForShapes fun Tb y Kr Xi vt => ∃ C d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
    ∀ (K : ℕ) (β : ℝ) (al : ℕ → ℝ) (T : StageTower (Tb.stepParameters y)), IsStateChain Tb y Kr Xi d K β al T →
    ∀ (k m : ℕ) (x : ℝ), k = separationLevel (Tb.stepParameters y) β K d →
    x = couplingAtSeparation (Tb.stepParameters y) β K d →
    m = averagingRadius x → ∀ f h : AmbientSpace → ℝ, IsNormalizedTestPair d vt f h →
      ∃ κ : ℝ,
        eLpNorm (fun u => shiftAveragedProduct T β al K k m (fun v => translateBy (Tb.stepParameters y).side K k v f)
            (fun v => translateBy (Tb.stepParameters y).side K k v h) u - κ) 16 (stageLaw T β K k) ≤
          ENNReal.ofReal (C * x ^ (-(2 + 1 / 130) : ℝ)) ∧
        eLpNorm (shiftAveragedResponse T β al K k m fun v => translateBy (Tb.stepParameters y).side K k v f) 16
            (stageLaw T β K k) ≤
          ENNReal.ofReal (C * x ^ (-(1 + 1 / 130) : ℝ)) ∧
        eLpNorm (shiftAveragedResponse T β al K k m fun v => translateBy (Tb.stepParameters y).side K k v h) 16
            (stageLaw T β K k) ≤
          ENNReal.ofReal (C * x ^ (-(1 + 1 / 130) : ℝ))
end YangMills.Construction.StateLaws
end
