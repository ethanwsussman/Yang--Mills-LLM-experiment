import YangMills.Construction.LawInAState.DataOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.StateLaws
open TorusLumps RenormalizationStepParameters ResponseInTheExpansion
open InfiniteLattice (AmbientSpace)
def covarianceApproxStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∀ Xi : ℝ, (Tb.stepParameters y).y₁ + 2 * (Tb.stepParameters y).B ≤ Xi →
    ∀ vt : ℝ, 0 < vt → vt ≤ 1 →
    ∃ C d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ (K : ℕ) (β : ℝ),
    IsFlowDatum (Tb.stepParameters y) Xi K β → minimalCutoff (Tb.stepParameters y) Xi d ≤ K →
    ∀ f h : AmbientSpace → ℝ, IsNormalizedTestPair d vt f h →
    ∀ μ : Measure (LatticeConfig (Tb.stepParameters y).side K), IsAdmissibleState (Tb.stepParameters y).side K β μ →
      |cov[smearedObservable (Tb.stepParameters y).side K f, smearedObservable (Tb.stepParameters y).side K h; μ] -
          unitTorusCovariance (Tb.stepParameters y).side K β f h| ≤
        C * couplingAtSeparation (Tb.stepParameters y) β K d ^ (-(2 + 1 / 130) : ℝ)
end YangMills.Construction.StateLaws
end
