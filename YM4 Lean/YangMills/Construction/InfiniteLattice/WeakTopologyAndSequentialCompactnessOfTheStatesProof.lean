import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsAtACutoff
import YangMills.Construction.InfiniteLattice.WeakTopologyAndSequentialCompactnessOfTheStates
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set YangMills.Construction.InfiniteLattice
open scoped Topology
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing
variable {a : ℝ}
private def evalMap (ν : BorelProb a) : continuousFns a → ℂ := fun F => ν.integral F.1
private theorem isInducing_evalMap : Topology.IsInducing (evalMap (a := a)) := by
  refine ⟨?_⟩
  change (⨅ F : continuousFns a,
      TopologicalSpace.induced (fun ν : BorelProb a => ν.integral F.1) inferInstance) = _
  rw [Pi.topologicalSpace, induced_iInf]
  simp only [induced_compose]
  rfl
private theorem continuous_integral_of_continuous {F : GaugeField a → ℂ} (hF : Continuous F) :
    Continuous fun ν : BorelProb a => ν.integral F :=
  (continuous_apply (⟨F, hF⟩ : continuousFns a)).comp
    (isInducing_evalMap (a := a)).continuous
private theorem isOpen_basicWeakSet (ν : BorelProb a) {q : ℕ} (H : Fin q → C(GaugeField a, ℂ))
    (ε : ℝ) : IsOpen (ν.basicWeakSet H ε) := by
  have hset : ν.basicWeakSet H ε =
      ⋂ r, {ν' : BorelProb a | ‖ν'.integral (H r) - ν.integral (H r)‖ < ε} := by
    ext ν'
    simp [BorelProb.basicWeakSet]
  rw [hset]
  refine isOpen_iInter_of_finite fun r => ?_
  exact isOpen_lt
    (((continuous_integral_of_continuous (H r).continuous).sub continuous_const).norm)
    continuous_const
private theorem exists_basicWeakSet_subset (ν : BorelProb a) {U : Set (BorelProb a)} (hU : U ∈ 𝓝 ν) :
    ∃ q : ℕ, 1 ≤ q ∧ ∃ H : Fin q → C(GaugeField a, ℂ), ∃ ε : ℝ, 0 < ε ∧
      ν.basicWeakSet H ε ⊆ U := by
  rw [(isInducing_evalMap (a := a)).nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨t, ht, htU⟩ := hU
  rw [nhds_pi, Filter.mem_pi] at ht
  obtain ⟨I, hI, s, hs, hsub⟩ := ht
  have hev : ∀ F ∈ I, ∀ᶠ ε in 𝓝[>] (0 : ℝ), Metric.ball (evalMap ν F) ε ⊆ s F := by
    intro F _
    obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.mp (hs F)
    filter_upwards [Ioc_mem_nhdsGT hε₀] with ε hε
    exact (Metric.ball_subset_ball hε.2).trans hball
  obtain ⟨ε, hεs, hε⟩ :=
    (((Filter.eventually_all_finite hI).mpr hev).and self_mem_nhdsWithin).exists
  let zero : continuousFns a := ⟨fun _ => 0, continuous_const⟩
  let l : List (continuousFns a) := zero :: hI.toFinset.toList
  refine ⟨l.length, by simp [l], fun r => ⟨(l.get r).1, (l.get r).2⟩, ε, hε, ?_⟩
  intro ν' hν'
  apply htU
  apply hsub
  intro F hF
  have hFl : F ∈ l := by simp [l, hI.mem_toFinset.mpr hF]
  obtain ⟨r, rfl⟩ := List.mem_iff_get.mp hFl
  apply hεs _ hF
  rw [Metric.mem_ball, dist_eq_norm]
  exact hν' r
private theorem tendstoWeak_iff_tendsto (ρ : ℕ → BorelProb a) (ν : BorelProb a) :
    BorelProb.TendstoWeak ρ ν ↔ Tendsto ρ atTop (𝓝 ν) := by
  rw [(isInducing_evalMap (a := a)).tendsto_nhds_iff, tendsto_pi_nhds]
  exact ⟨fun h F => h F.1 F.2, fun h F hF => h ⟨F, hF⟩⟩
private def toProbabilityMeasure (ν : BorelProb a) : ProbabilityMeasure (GaugeField a) :=
  ⟨ν.1, ν.2⟩
private def ofProbabilityMeasure (ν : ProbabilityMeasure (GaugeField a)) : BorelProb a :=
  ⟨ν.1, ν.2⟩
private theorem exists_tendstoWeak_subseq [CompactSpace (GaugeField a)]
    [TopologicalSpace.MetrizableSpace (GaugeField a)] (ρ : ℕ → BorelProb a) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, 1 ≤ φ k) ∧ ∃ ν : BorelProb a,
      BorelProb.TendstoWeak (ρ ∘ φ) ν := by
  let _ := TopologicalSpace.metrizableSpaceMetric (GaugeField a)
  obtain ⟨μ, φ, hφ, hlim⟩ :=
    CompactSpace.tendsto_subseq fun i => toProbabilityMeasure (ρ (i + 1))
  refine ⟨fun k => φ k + 1, fun i j hij => Nat.add_lt_add_right (hφ hij) 1,
    fun k => Nat.le_add_left 1 (φ k), ofProbabilityMeasure μ, ?_⟩
  intro F hF
  have key := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim
    (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩)
  exact key
theorem weakTopologyAndSeqCompactness_holds (hspace : InfiniteLattice.FieldSpace.Statement) :
    WeakTopologyAndSeqCompactness := by
  intro s a ha
  subst ha
  obtain ⟨⟨-, -, hcompact, hmetric⟩, -, -⟩ := hspace s
  refine ⟨fun ν => ⟨fun U hU => exists_basicWeakSet_subset ν hU, fun q _ H ε hε => ?_⟩,
    fun ρ ν => ?_, fun ρ => exists_tendstoWeak_subseq ρ⟩
  · refine ⟨isOpen_basicWeakSet ν H ε, fun r => ?_⟩
    simpa using hε
  · rw [tendstoWeak_iff_tendsto]
    exact tendsto_def
end YangMills.Construction.GibbsAtFixedSpacing
end
