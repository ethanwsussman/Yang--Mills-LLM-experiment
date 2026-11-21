import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndSpaceOfMeasures
import YangMills.Construction.InfiniteLattice.TorusStatesAsPeriodicMeasures
import YangMills.Construction.InfiniteLattice.WeakLimitPointsOfTheFamilyAreLimitsAlongSequences
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicLiftAtCutoff.SequentialLimits
variable {a : ℝ}
def asBorelProb (μ : ProbabilityMeasure (InfiniteLattice.GaugeField a)) :
    GibbsAtFixedSpacing.BorelProb a :=
  (Subtype.mk μ.1 μ.2 :
    {ν : Measure (InfiniteLattice.GaugeField a) // IsProbabilityMeasure ν})
theorem probabilityMeasuresWeakTopology_eq_induced :
    InfiniteLattice.probabilityMeasuresWeakTopology a =
      TopologicalSpace.induced asBorelProb GibbsAtFixedSpacing.BorelProb.instTopologicalSpace := by
  show _ = TopologicalSpace.induced asBorelProb
    (⨅ G : GibbsAtFixedSpacing.continuousFns a, TopologicalSpace.induced
      (fun μ : GibbsAtFixedSpacing.BorelProb a => μ.integral G.1) inferInstance)
  rw [induced_iInf]
  simp only [induced_compose]
  apply le_antisymm
  · exact le_iInf fun G => iInf_le_of_le ⟨G.1, G.2⟩ (le_of_eq rfl)
  · exact le_iInf fun G => iInf_le_of_le ⟨G, G.continuous⟩ (le_of_eq rfl)
theorem tendsto_probabilityMeasuresWeakTopology_iff
    (σ : ℕ → ProbabilityMeasure (InfiniteLattice.GaugeField a))
    (μ : ProbabilityMeasure (InfiniteLattice.GaugeField a)) :
    Tendsto σ atTop (@nhds _ (InfiniteLattice.probabilityMeasuresWeakTopology a) μ) ↔
      ∀ G : InfiniteLattice.GaugeField a → ℂ, Continuous G →
        Tendsto (fun k => ∫ U, G U ∂(σ k : Measure (InfiniteLattice.GaugeField a))) atTop
          (𝓝 (∫ U, G U ∂(μ : Measure (InfiniteLattice.GaugeField a)))) := by
  simp only [nhds_iInf, nhds_induced, tendsto_iInf, tendsto_comap_iff]
  constructor
  · intro h G hG
    exact h ⟨G, hG⟩
  · intro h G
    exact h G G.continuous
theorem clusterPointsAreSequentialLimits_of
    (hfields : FieldsAtSpacing.CompactFieldsAndMeasures)
    (hperiodic : InfiniteLattice.TorusStatesAsPeriodic.Statement) :
    ClusterPointsAreSequentialLimits := by
  intro L K hL hK β hβ
  have hL0 : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := lt_of_lt_of_le (by norm_num) hL.2
    exact_mod_cast this
  have hmesh : 0 < PeriodicLattice.meshSize L (K : ℤ) := zpow_pos hL0 _
  have hmetr : TopologicalSpace.MetrizableSpace
      (GibbsAtFixedSpacing.BorelProb (PeriodicLattice.meshSize L (K : ℤ))) :=
    (hfields _ hmesh).2.2.1.2
  have hprob : ∀ m : ℕ, 0 < m →
      IsProbabilityMeasure (InfiniteLattice.liftedWilsonMeasure L m K β) := fun m hm =>
    ((hperiodic ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩ β hβ).2.1).1
  have hseq : ∀ μ : ProbabilityMeasure
      (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ))),
      IsWeakClusterPoint L K β μ ↔ IsWeakLimitAlongSideSequence L K β μ := by
    intro μ
    constructor
    · intro hc
      obtain ⟨V, hV⟩ := (𝓝 (asBorelProb μ)).exists_antitone_basis
      have hW : ∀ k, asBorelProb ⁻¹' V k ∈
          @nhds _ (InfiniteLattice.probabilityMeasuresWeakTopology _) μ := by
        intro k
        rw [probabilityMeasuresWeakTopology_eq_induced, nhds_induced]
        exact preimage_mem_comap (hV.1.mem_of_mem trivial)
      have hevery := fun k : ℕ => hc _ (hW k) (k : ℝ)
      choose n hn hsides σ hσV hσ using hevery
      refine ⟨n, hn, tendsto_atTop_mono hsides tendsto_natCast_atTop_atTop, σ, hσ, ?_⟩
      rw [probabilityMeasuresWeakTopology_eq_induced, nhds_induced, tendsto_comap_iff]
      exact hV.tendsto hσV
    · rintro ⟨n, hn, hsides, σ, hσ, hlim⟩ 𝒰 h𝒰 t₀
      have h₁ : ∀ᶠ k in atTop, σ k ∈ 𝒰 := hlim h𝒰
      have h₂ := hsides.eventually_ge_atTop t₀
      obtain ⟨k, hk₁, hk₂⟩ := (h₁.and h₂).exists
      exact ⟨n k, hn k, hk₂, σ k, hk₁, hσ k⟩
  have hmem : ∀ μ : ProbabilityMeasure
      (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ))),
      (μ : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) ∈
          InfiniteLattice.weakLimitsAlongSides L K β ↔
        IsWeakLimitAlongSideSequence L K β μ := by
    intro μ
    constructor
    · intro h
      obtain ⟨-, n, hn, hsides, hG⟩ :=
        (InfiniteLattice.mem_weakLimitsAlongSides_iff L K β _).1 h
      refine ⟨n, hn, hsides,
        fun k => ⟨InfiniteLattice.liftedWilsonMeasure L (n k) K β, hprob _ (hn k)⟩,
        fun k => rfl, ?_⟩
      exact (tendsto_probabilityMeasuresWeakTopology_iff _ _).2 fun G hG' => hG G hG'
    · rintro ⟨n, hn, hsides, σ, hσ, hlim⟩
      refine (InfiniteLattice.mem_weakLimitsAlongSides_iff L K β _).2
        ⟨μ.2, n, hn, hsides, fun G hG => ?_⟩
      exact Tendsto.congr (fun k => by rw [hσ k])
        ((tendsto_probabilityMeasuresWeakTopology_iff σ μ).1 hlim G hG)
  refine ⟨fun μ => ⟨hseq μ, hmem μ⟩, ?_, ?_⟩
  · ext ν
    constructor
    · intro h
      have hp := ((InfiniteLattice.mem_weakLimitsAlongSides_iff L K β _).1 h).1
      exact ⟨⟨ν, hp⟩, (hseq _).2 ((hmem ⟨ν, hp⟩).1 h), rfl⟩
    · rintro ⟨μ, hμ, rfl⟩
      exact (hmem μ).2 ((hseq μ).1 hμ)
  · ext ν
    constructor
    · intro h
      have hp := ((InfiniteLattice.mem_weakLimitsAlongSides_iff L K β _).1 h).1
      exact ⟨⟨ν, hp⟩, (hmem ⟨ν, hp⟩).1 h, rfl⟩
    · rintro ⟨μ, hμ, rfl⟩
      exact (hmem μ).2 hμ
end YangMills.Construction.InfiniteLattice.PeriodicLiftAtCutoff.SequentialLimits
end
