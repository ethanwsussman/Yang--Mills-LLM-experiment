import YangMills.Construction.FourPointCondition.FourPointFunctionDefs
import YangMills.Construction.InfiniteLattice.ConnectedFourPointFunctionOfAStateAtOneSpacing
import YangMills.Construction.InfiniteLattice.PeriodicExtensionsAndTheirWeakLimitPoints
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
open InfiniteLattice.PeriodicExtensions
def fourPointBoundsInTorusLimitStates : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∀ vt : ℝ, 0 < vt → vt ≤ 1 →
    ∀ (R : CouplingEvaluation) (lam Ca d₀ : ℝ) (n₀ : ℕ), EvaluationLaws R (Tb.stepParameters y).side vt lam Ca d₀ n₀ →
      ∃ d₄ ∈ Ioc (0 : ℝ) d₀, ∀ (K : ℕ+) (β : ℝ), 0 < β → R.IsFirstPassage K β →
        ∀ ν ∈ limitsOfLiftedMeasures (Tb.stepParameters y).side (K : ℕ) β,
          ∀ d ∈ Ioc (0 : ℝ) d₄, R.IsDeepEnough (Tb.stepParameters y).side K n₀ d →
            ∀ f ∈ QuadrupleClasses.collinearQuadsR4 d vt, ∃ r : ℝ,
              fourPointUrsell ν.measure f = (r : ℂ) ∧
              FourPointBounds (fourPointLowerConst vt) fourPointUpperConst (R.coupling K β d) f r
end YangMills.Construction.FourPointCondition
end
