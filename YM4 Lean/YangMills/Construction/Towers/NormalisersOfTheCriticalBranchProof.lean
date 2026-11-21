import YangMills.Construction.Towers.CriticalBranchUnderTheDilation
import YangMills.Construction.Towers.GradientOfTheFixedFunctionOnAFibre
import YangMills.Construction.Towers.HessianOnAFibreOfTheCriticalBranch
import YangMills.Construction.Towers.NormaliserIsPositiveNearOne
import YangMills.Construction.Towers.NormaliserIsRealAnalyticNearOne
import YangMills.Construction.Towers.NormaliserLogarithmIsGaugeInvariant
import YangMills.Construction.Towers.NormaliserLogarithmIsInvariantUnderIsometries
import YangMills.Construction.Towers.NormaliserLogarithmIsRealAnalyticNearOne
import YangMills.Construction.Towers.NormalisersOfTheCriticalBranch
import YangMills.Construction.Towers.NormalisersUnderTheDilation
import YangMills.Construction.Towers.UniquenessOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
theorem normalisersHold_of_components
    (hg : GaugeFixedGradientOnFibre)
    (hh : FibreHessianViaQuadraticExpansion)
    (hp : GaussianNormaliserPositiveNearOne)
    (ha : GaussianNormaliserAnalyticNearIdentity)
    (hl : LogNormaliserAnalyticNearOne)
    (hga : LogNormaliserRatioGaugeInvariant)
    (hsy : LogNormaliserRatioSymmetryInvariant)
    (hu : CriticalBranchUnique)
    (hc : ChosenBranchScaling)
    (hz : NormalisersScalingCompatible) :
    NormalisersHold := by
  intro L m k h hm i hi
  refine
    { gradient_rel := hg L m k h hm i hi
      hessian_rel := ?_
      normaliser_pos := hp L m k h hm i hi
      normaliser_analytic := ha L m k h hm i hi
      logRatio_analytic := hl L m k h hm i hi
      logRatio_gauge_invariant := hga L m k h hm i hi
      logRatio_symmetry_invariant := hsy L m k h hm i hi
      energy_unique := fun e he => (hu L m k h hm e he).1
      prolong_unique := fun e he => (hu L m k h hm e he).2
      scaling :=
        { energy_eq := (hc L m k (i + 1) _ hi h hm (by omega)).1
          prolong_eq := (hc L m k (i + 1) _ hi h hm (by omega)).2
          normaliser_eq := (hz L m k (i + 1) _ hi h hm (by omega)).1
          logRatio_eq := (hz L m k (i + 1) _ hi h hm (by omega)).2 } }
  refine Filter.Eventually.mono (hh L m k h hm i hi) ?_
  rintro W ⟨hex, hall⟩ B
  exact hall _ (Classical.epsilon_spec hex) B
end YangMills.Construction.Tower
