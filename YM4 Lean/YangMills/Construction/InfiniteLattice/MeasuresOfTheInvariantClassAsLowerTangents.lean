import YangMills.Construction.InfiniteLattice.GeneratorIndicesOfAnArrayAndTheParameterZero
import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import YangMills.Construction.InfiniteLattice.SurfaceBoundBetweenBoxAndTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory NormalFamilies
namespace InfiniteLattice
namespace LocalObservableArray
def logTiltRatioPerSite (X : LocalObservableArray) (Γ : PeriodSublattice 1)
    (F : OrthogonalNormalFrame) (s : Fin 4 → ℕ+) (β t : ℝ) : ℝ :=
  1 / ((F.fundamentalBox s).ncard : ℝ) *
    Real.log (X.tiltedPartition Γ β t / X.untiltedTorusPartition Γ β)
def shellDefect (F : OrthogonalNormalFrame) (s : Fin 4 → ℕ+) (ϱ : ℕ+) (A : GaugeField 1 → ℂ)
    (β t : ℝ) : ℝ :=
  (Constants.BoxTorus.tangentNumber : ℝ) * (β + |t| * observableSupNorm A) *
    (boxCoverNumber ϱ : ℝ) *
    (((F.boundaryShell s ϱ).ncard : ℝ) / ((F.fundamentalBox s).ncard : ℝ))
def sideDefect (s : Fin 4 → ℕ+) (ϱ : ℕ+) (A : GaugeField 1 → ℂ) (β t : ℝ) : ℝ :=
  (Constants.BoxTorus.tangentSideNumber : ℝ) * (β + |t| * observableSupNorm A) *
    ((ϱ : ℕ) : ℝ) ^ 5 * ∑ i, (((s i : ℕ) : ℝ))⁻¹
def IsLowerTangent (X : LocalObservableArray) (Γ : PeriodSublattice 1)
    (F : OrthogonalNormalFrame) (s : Fin 4 → ℕ+) (ϱ : ℕ+) (A : GaugeField 1 → ℂ)
    (ν : Measure (GaugeField 1)) (β t : ℝ) : Prop :=
  t * X.invIndex * (stateEval ν A).re - shellDefect F s ϱ A β t ≤
      X.logTiltRatioPerSite Γ F s β t ∧
    t * X.invIndex * (stateEval ν A).re - sideDefect s ϱ A β t ≤
      t * X.invIndex * (stateEval ν A).re - shellDefect F s ϱ A β t
end LocalObservableArray
namespace InvariantGibbsLowerTangent
def InvariantGibbsLowerTangentClaim : Prop :=
  ∀ (d : BoxTorusComparisonData) (β : ℝ), 0 < β →
    ∀ ν ∈ subgroupInvariantGibbsClass one_pos β d.translationGroup, ∀ t : ℝ,
      d.obsArray.IsLowerTangent d.periodSublattice d.normalFrame d.sideLengths d.boxWidth d.obs
        ν β t
end InvariantGibbsLowerTangent
end InfiniteLattice
end YangMills.Construction
