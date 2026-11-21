import YangMills.Construction.InfiniteLattice.InfiniteVolumeLimitPointsOfTheTorusStates
import YangMills.Construction.InfiniteLattice.SymmetriesOfAVolumeLimitPoint
import YangMills.Construction.InfiniteLattice.TorusConfigurationsAndMeasuresThroughTheCoveringMapOfACutoff
import YangMills.Construction.InfiniteLattice.WeakLimitPointsOfTheFamilyAreLimitsAlongSequences
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.InfiniteLattice.VolumeLimitSymmetries
theorem isInfiniteVolumeLimit_iff
    (hCov : YangMills.Construction.InfiniteLattice.CutoffCovering.CoveringIdentification)
    (hSeq : YangMills.Construction.InfiniteLattice.PeriodicLiftAtCutoff.ClusterPointsAreSequentialLimits)
    {L : ℕ} (hL : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L) (K : ℕ+)
    {β : ℝ} (hβ : 0 < β)
    (μ : MeasureTheory.Measure
      (YangMills.Construction.InfiniteLattice.GaugeField
        (YangMills.Construction.PeriodicLattice.meshSize L ((K : ℕ) : ℤ)))) :
    YangMills.Construction.InfiniteLattice.IsInfiniteVolumeLimit L K β μ ↔
      ∃ q ∈ YangMills.Construction.InfiniteLattice.cubicTorusLimitStates L K β, q.1 = μ := by
  have hA := (hCov ⟨⟨L, hL, K, ⟨1, one_pos⟩⟩, β, hβ⟩).2.2.2
  have hB := (hSeq L K hL K.pos β hβ).2.1
  have hiff : YangMills.Construction.InfiniteLattice.IsInfiniteVolumeLimit L K β μ ↔
      μ ∈ YangMills.Construction.InfiniteLattice.weakLimitsAlongSides L K β :=
    Set.ext_iff.1 (hA.trans hB.symm) μ
  rw [hiff]
  constructor
  · rintro ⟨hq, s, hs, hside, hlim⟩
    have hprob : ∀ i, MeasureTheory.IsProbabilityMeasure
        (YangMills.Construction.InfiniteLattice.liftedWilsonMeasure L (s i) K β) :=
      fun i => (hCov ⟨⟨L, hL, K, ⟨s i, hs i⟩⟩, β, hβ⟩).2.2.1.2.2.1
    refine ⟨⟨μ, hq⟩, ⟨s, fun i =>
      ⟨YangMills.Construction.InfiniteLattice.liftedWilsonMeasure L (s i) K β, hprob i⟩, hs, hside,
      fun _ => rfl, fun G hG => hlim G hG⟩, rfl⟩
  · rintro ⟨q, ⟨t, ρ, ht, hside, hρ, hlim⟩, rfl⟩
    refine ⟨q.2, t, ht, hside, fun G hG => ?_⟩
    refine (hlim G hG).congr fun i => ?_
    show ∫ U, G U ∂(ρ i).1 = _
    rw [hρ i]
theorem statement_holds
    (hCov : YangMills.Construction.InfiniteLattice.CutoffCovering.CoveringIdentification)
    (hSeq : YangMills.Construction.InfiniteLattice.PeriodicLiftAtCutoff.ClusterPointsAreSequentialLimits)
    (hTor : YangMills.Construction.InfiniteLattice.TorusStateLimitPoints)
    (hGibbs : YangMills.Construction.InfiniteLattice.PeriodicGibbsAtSpacing.Statement) :
    YangMills.Construction.InfiniteLattice.VolumeLimitSymmetries.Statement := by
  intro L hL K β hβ μ hμ
  have hprob : MeasureTheory.IsProbabilityMeasure μ := hμ.1
  obtain ⟨q, hq, rfl⟩ := (isInfiniteVolumeLimit_iff hCov hSeq hL K hβ μ).1 hμ
  obtain ⟨-, -, -, -, -, hper, -⟩ := (hTor L hL K K.pos β hβ).2.1 q hq
  have hmesh : (0 : ℝ) < YangMills.Construction.PeriodicLattice.meshSize L ((K : ℕ) : ℤ) := by
    have hL0 : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    simp only [YangMills.Construction.PeriodicLattice.meshSize]
    positivity
  exact ⟨hprob, hper, (hGibbs _ hmesh β hβ).1 q.1 hper⟩
end YangMills.Construction.InfiniteLattice.VolumeLimitSymmetries
end
