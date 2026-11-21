import YangMills.Construction.InfiniteLattice.PeriodicExtensionPeriodisationAndWeakLimitPointsAtACutoff
import YangMills.Construction.InfiniteLattice.WeakLimitPointsAlongSides
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicLiftAtCutoff
def IsWeakLimitAlongSideSequence (L K : ℕ) (β : ℝ)
    (μ : ProbabilityMeasure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) :
    Prop :=
  ∃ n : ℕ → ℕ, (∀ i, 0 < n i) ∧ Tendsto (fun i => PeriodicLattice.torusSide L (n i)) atTop atTop ∧
    ∃ ρ : ℕ → ProbabilityMeasure
        (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ))),
      (∀ i, (ρ i : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) =
        InfiniteLattice.PeriodicTorusMeasures.pushforwardWilsonMeasure L (n i) K β) ∧
      Tendsto ρ atTop (@nhds _ (InfiniteLattice.probabilityMeasuresWeakTopology _) μ)
def ClusterPointsAreSequentialLimits : Prop :=
  ∀ L K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < K → ∀ β : ℝ, 0 < β →
    (∀ μ : ProbabilityMeasure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ))),
      (IsWeakClusterPoint L K β μ ↔ IsWeakLimitAlongSideSequence L K β μ) ∧
      ((μ : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) ∈
          InfiniteLattice.weakLimitsAlongSides L K β ↔
        IsWeakLimitAlongSideSequence L K β μ)) ∧
    InfiniteLattice.weakLimitsAlongSides L K β =
      (fun μ : ProbabilityMeasure
          (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ))) =>
        (μ : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ))))) ''
        weakClusterPoints L K β ∧
    InfiniteLattice.weakLimitsAlongSides L K β =
      (fun μ : ProbabilityMeasure
          (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ))) =>
        (μ : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ))))) ''
        {μ | IsWeakLimitAlongSideSequence L K β μ}
end YangMills.Construction.InfiniteLattice.PeriodicLiftAtCutoff
end
