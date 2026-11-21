import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsOnTheInfiniteLattice
import YangMills.Construction.InfiniteLattice.WeaklyConvergentSubsequencesOfStates
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicExtensions
theorem tendsto_pnatNatPred_atTop : Tendsto PNat.natPred (atTop : Filter ℕ+) atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b.succPNat, fun c hc => by
    simpa using PNat.natPred_le_natPred.2 hc⟩
theorem EveryStateSequenceHasWeaklyConvergentSubsequence.holds
    (hSpace : GaugeFieldSpace.Statement) :
    EveryStateSequenceHasWeaklyConvergentSubsequence.Statement := by
  intro s μ
  obtain ⟨-, -, -, -, hCompact, hMetrisable⟩ :=
    (hSpace { s with coupling := 1, coupling_pos := one_pos }).1
  let a : ℝ := PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)
  have : CompactSpace (GaugeField a) := hCompact
  have : TopologicalSpace.MetrizableSpace (GaugeField a) := hMetrisable
  have : TopologicalSpace.SeparableSpace (GaugeField a) := by
    let := TopologicalSpace.metrizableSpaceMetric (GaugeField a)
    infer_instance
  let P : ℕ → ProbabilityMeasure (GaugeField a) :=
    fun n => ⟨(μ n.succPNat).measure, inferInstance⟩
  obtain ⟨Q, φ, hφ, hQ⟩ := CompactSpace.tendsto_subseq P
  refine ⟨fun k => (φ k.natPred).succPNat, ⟨(Q : Measure _), inferInstance⟩, ?_, ?_⟩
  · intro k l hkl
    exact Nat.succPNat_strictMono (hφ (PNat.natPred_lt_natPred.2 hkl))
  · intro F
    have hF := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hQ)
      (BoundedContinuousFunction.mkOfCompact F)
    exact hF.comp tendsto_pnatNatPred_atTop
end YangMills.Construction.InfiniteLattice.PeriodicExtensions
