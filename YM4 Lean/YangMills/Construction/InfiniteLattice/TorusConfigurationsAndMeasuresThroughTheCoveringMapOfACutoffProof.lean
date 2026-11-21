import YangMills.Construction.InfiniteLattice.TorusConfigurationsAndMeasuresThroughTheCoveringMapOfACutoff
import YangMills.Construction.InfiniteLattice.TorusConfigurationsAsPeriodicConfigurations
import YangMills.Construction.InfiniteLattice.WeakLimitPointsOfTheFamilyAreLimitsAlongSequences
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CutoffCovering
open YangMills.Construction.CutoffLattice YangMills.Construction.InfiniteLattice.PeriodicExtensions YangMills.Construction.InfiniteLattice.TorusFieldsAsPeriodic
variable {L m K : ℕ} {β : ℝ}
theorem latticeSubgroup_torusSide_le (hL : 0 < L) :
    latticeSubgroup (PeriodicLattice.torusSide L m) ≤ latticeSubgroup (CutoffLattice.spacingAt L K) := by
  rintro x ⟨k, hk⟩
  refine ⟨fun μ => k μ * (2 * (L : ℤ) ^ (m + K)), fun μ => ?_⟩
  rw [hk μ]
  simp only [PeriodicLattice.torusSide, CutoffLattice.spacingAt, PeriodicLattice.meshSize]
  push_cast
  rw [zpow_neg, zpow_natCast, pow_add]
  field_simp
theorem translateLink_eq_linkMap {a : ℝ} (b : Link a) (v : LatticePoint a) :
    translateLink b v = (shift v).linkMap b :=
  rfl
theorem periodsAndLinks_of_projection (hL : 0 < L) (h : ProjectionOnOrientedLinks L m K) :
    PeriodsAndLinks L m K :=
  ⟨latticeSubgroup_torusSide_le hL, fun b b' => by simpa only [translateLink_eq_linkMap] using h.2.2 b b', h.2.1⟩
theorem liftIsBijective_of_lift (h : LiftOntoPeriodicFields L m K) :
    LiftIsBijective L m K := by
  obtain ⟨-, -, hinj, hrange, hset⟩ := h
  refine ⟨fun U _ => ?_, hinj.injOn, fun U hU => ?_⟩
  · rw [← hset, ← hrange]
    exact ⟨U, rfl⟩
  · rw [← hset, ← hrange] at hU
    obtain ⟨V, rfl⟩ := hU
    exact ⟨V, mem_univ _, rfl⟩
theorem liftAndMeasure_of_image (h : LiftedMeasureAsImage L m K β) :
    LiftAndMeasure L m K β :=
  ⟨fun _ => rfl, fun U b => liftCompactField_apply U b, h.1, h.2, rfl⟩
theorem limitsAreTorusStates_of_subsequential (h : SubsequentialLimitsAreTorusLimits L K β)
    (h' : weakLimitsAlongSides L K β =
      (fun ν : ProbabilityMeasure (FieldsAt L K) => (ν : Measure (FieldsAt L K))) ''
        PeriodicLiftAtCutoff.weakClusterPoints L K β) :
    LimitsAreTorusStates L K β := by
  unfold LimitsAreTorusStates
  rw [← h']
  ext μ
  constructor
  · intro hμ
    have hp : IsProbabilityMeasure μ := hμ.1
    have hν := h (⟨μ, hp⟩ : RealWeakState (CutoffLattice.spacingAt L K))
    exact hν.2.mpr (hν.1.mp hμ)
  · intro hμ
    have hp : IsProbabilityMeasure μ := hμ.1
    have hν := h (⟨μ, hp⟩ : RealWeakState (CutoffLattice.spacingAt L K))
    exact hν.1.mpr (hν.2.mp hμ)
theorem coveringIdentification_holds
    (h₁ : TorusFieldsAsPeriodic.Statement)
    (h₂ : PeriodicLiftAtCutoff.ClusterPointsAreSequentialLimits) :
    CoveringIdentification := by
  intro D
  obtain ⟨ha, hb, hc, hd, -⟩ := h₁ D.toStandingParameters D.β D.β_pos
  have hL : 0 < D.L := by
    have := D.isAdmissible.2
    omega
  exact ⟨periodsAndLinks_of_projection hL ha, liftIsBijective_of_lift hb, liftAndMeasure_of_image hc,
    limitsAreTorusStates_of_subsequential hd
      (h₂ D.L D.K D.isAdmissible D.K.pos D.β D.β_pos).2.1⟩
end YangMills.Construction.InfiniteLattice.CutoffCovering
end
