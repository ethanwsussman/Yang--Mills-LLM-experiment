import YangMills.Construction.LawInAState.AveragesInACell
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.StateLaws
open TorusLumps ResponseInTheExpansion ChessboardTori CellAverages
open InfiniteLattice (AmbientSpace)
def covarianceBoundByAveragesStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∀ Ξ : ℝ,
    (Tb.stepParameters y).y₁ + 2 * (Tb.stepParameters y).B ≤ Ξ → ∃ R : ℝ, 1 ≤ R ∧
    ∀ D : ChessboardSetup, D.L = (Tb.stepParameters y).side → IsFlowDatum (Tb.stepParameters y) Ξ D.K D.β →
    ∀ g : ReflectionGrid D, g.q = 0 → ∀ (k m : ℕ) (d v : ℝ), k ≤ D.K → 0 < d → 0 < v → v ≤ 1 →
    ∀ f h : AmbientSpace → ℝ, IsNormalizedTestPair d v f h →
      (∀ w ∈ shiftSet m, IsDeepInCell g (translateBy D.L D.K k w f) ∧
        IsDeepInCell g (translateBy D.L D.K k w h)) →
      ∀ μ : Measure D.GaugeField, IsAdmissibleState D.L D.K D.β μ →
        |cov[smearedObservable D.L D.K f, smearedObservable D.L D.K h; μ] -
            unitTorusCovariance D.L D.K D.β f h| ≤
          R * reflectionNorm g (averagedCovarianceDefect D.L D.K k m D.β f h) +
            R ^ 2 * reflectionNorm g (averagedCenteredObservable D.L D.K k m D.β f) *
              reflectionNorm g (averagedCenteredObservable D.L D.K k m D.β h)
end YangMills.Construction.StateLaws
end
