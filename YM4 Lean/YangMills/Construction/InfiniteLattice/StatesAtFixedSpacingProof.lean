import Mathlib
import YangMills.Construction.InfiniteLattice.StatesAtFixedSpacing
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsOnTheInfiniteLattice
import YangMills.Construction.InfiniteLattice.TorusStatesAsPeriodicMeasures
import YangMills.Construction.InfiniteLattice.TorusStatesAreTheVolumeLimitPointsProof

set_option autoImplicit false

namespace YangMills.Construction

open MeasureTheory

/-- Compactness of probability measures supplies a torus limit directly. -/
theorem InfiniteLattice.torusLimitSetsNonempty_holds
    (hSpace : InfiniteLattice.GaugeFieldSpace.Statement)
    (hPeriodic : InfiniteLattice.TorusStatesAsPeriodic.Statement) :
    InfiniteLattice.TorusLimitSetsNonempty := by
  intro L K hL hK β hβ
  let s : Conventions.StandingParameters := ⟨L, hL, ⟨K, hK⟩, 1⟩
  obtain ⟨_, _, _, _, hCompact, hMetrizable⟩ :=
    (hSpace { s with coupling := 1, coupling_pos := one_pos }).1
  let a : ℝ := PeriodicLattice.meshSize L (K : ℤ)
  have : CompactSpace (InfiniteLattice.GaugeField a) := hCompact
  have : TopologicalSpace.MetrizableSpace (InfiniteLattice.GaugeField a) := hMetrizable
  have : TopologicalSpace.SeparableSpace (InfiniteLattice.GaugeField a) := by
    let := TopologicalSpace.metrizableSpaceMetric (InfiniteLattice.GaugeField a)
    infer_instance
  have hprob : ∀ i : ℕ, IsProbabilityMeasure (InfiniteLattice.liftedWilsonMeasure L (i + 1) K β) :=
    fun i => (hPeriodic ⟨L, hL, ⟨K, hK⟩, ⟨i + 1, Nat.succ_pos i⟩⟩ β hβ).2.1.1
  let P : ℕ → ProbabilityMeasure (InfiniteLattice.GaugeField a) :=
    fun i => ⟨InfiniteLattice.liftedWilsonMeasure L (i + 1) K β, hprob i⟩
  obtain ⟨ν, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq P
  have hlimit : InfiniteLattice.IsInfiniteVolumeLimit L K β (ν : Measure _) := by
    refine ⟨inferInstance, fun i => φ i + 1, fun i j hij => Nat.add_lt_add_right (hφ hij) 1, ?_⟩
    intro F
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hν) F
  have hL2 : 2 ≤ L := by have := hL.2; omega
  rw [InfiniteLattice.TorusLimitCharacterization.torusLimitsAreInfiniteVolumeLimits_holds L K β hL2]
  exact ⟨(ν : Measure _), hlimit⟩

end YangMills.Construction
