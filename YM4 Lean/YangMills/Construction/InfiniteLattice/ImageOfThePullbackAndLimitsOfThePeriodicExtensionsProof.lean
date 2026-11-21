import YangMills.Construction.InfiniteLattice.BondsAndTheirVariables
import YangMills.Construction.InfiniteLattice.ConfigurationsOfTheTorusLatticeAtPositiveLinks
import YangMills.Construction.InfiniteLattice.CoveringOnAWindow
import YangMills.Construction.InfiniteLattice.ImageOfThePullbackAndLimitsOfThePeriodicExtensions
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.Measures.CompactMetricMeasuresAndContinuousFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter YangMills.Construction.InfiniteLattice
open scoped Topology
noncomputable section
namespace YangMills.Construction.CutoffLinks
namespace LiftImage
section Compact
variable {X : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
theorem integrable_of_continuousMap (μ : Measure X) [IsFiniteMeasure μ] (F : C(X, ℂ)) :
    Integrable F μ :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
theorem exists_denseSeq_continuous
    (hM : Measures.CompactMetric.measuresAndContinuousFunctions)
    [TopologicalSpace.MetrizableSpace X] [Nonempty X] :
    ∃ Φ : ℕ → C(X, ℂ), ∀ (F : C(X, ℂ)) (ε : ℝ), 0 < ε →
      ∃ (s : Finset ℕ) (c : ℕ → ℂ), ∀ y, ‖F y - ∑ t ∈ s, c t * Φ t y‖ ≤ ε := by
  let mX : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨-, -, φ, -, hφ⟩ := @hM X mX ‹CompactSpace X› ‹Nonempty X› ‹MeasurableSpace X› ‹BorelSpace X›
  refine ⟨fun t => ⟨fun y => ((φ t y : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (φ t).continuous⟩, fun F ε hε => ?_⟩
  exact hφ F ε hε
theorem tendsto_integral_of_denseSeq (Φ : ℕ → C(X, ℂ))
    (hΦ : ∀ (F : C(X, ℂ)) (ε : ℝ), 0 < ε →
      ∃ (s : Finset ℕ) (c : ℕ → ℂ), ∀ y, ‖F y - ∑ t ∈ s, c t * Φ t y‖ ≤ ε)
    (μ : ℕ → Measure X) [∀ j, IsProbabilityMeasure (μ j)] (ν : Measure X) [IsProbabilityMeasure ν]
    (h : ∀ t, Tendsto (fun j => ∫ y, Φ t y ∂μ j) atTop (𝓝 (∫ y, Φ t y ∂ν))) (F : C(X, ℂ)) :
    Tendsto (fun j => ∫ y, F y ∂μ j) atTop (𝓝 (∫ y, F y ∂ν)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨s, c, hsc⟩ := hΦ F (ε / 4) (by positivity)
  have hint : ∀ (ρ : Measure X) [IsProbabilityMeasure ρ],
      ∫ y, ∑ t ∈ s, c t * Φ t y ∂ρ = ∑ t ∈ s, c t * ∫ y, Φ t y ∂ρ := by
    intro ρ _
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun t _ => integral_const_mul _ _
    · exact fun t _ => (integrable_of_continuousMap ρ (Φ t)).const_mul _
  have hG : Tendsto (fun j => ∫ y, ∑ t ∈ s, c t * Φ t y ∂μ j) atTop
      (𝓝 (∫ y, ∑ t ∈ s, c t * Φ t y ∂ν)) := by
    simp only [hint]
    exact tendsto_finsetSum _ fun t _ => (h t).const_mul _
  have hclose : ∀ (ρ : Measure X) [IsProbabilityMeasure ρ],
      ‖(∫ y, F y ∂ρ) - ∫ y, ∑ t ∈ s, c t * Φ t y ∂ρ‖ ≤ ε / 4 := by
    intro ρ _
    have hi : Integrable (fun y => ∑ t ∈ s, c t * Φ t y) ρ :=
      integrable_finsetSum _ fun t _ => (integrable_of_continuousMap ρ (Φ t)).const_mul _
    rw [← integral_sub (integrable_of_continuousMap ρ F) hi]
    have := norm_integral_le_of_norm_le_const (μ := ρ)
      (f := fun y => F y - ∑ t ∈ s, c t * Φ t y) (C := ε / 4) (Eventually.of_forall hsc)
    simpa using this
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hG (ε / 4) (by positivity)
  refine ⟨N, fun j hj => ?_⟩
  have h1 := hclose (μ j)
  have h2 := hclose ν
  have h3 := hN j hj
  rw [dist_eq_norm] at h3 ⊢
  have e : (∫ y, F y ∂μ j) - ∫ y, F y ∂ν =
      ((∫ y, F y ∂μ j) - ∫ y, ∑ t ∈ s, c t * Φ t y ∂μ j) +
        ((∫ y, ∑ t ∈ s, c t * Φ t y ∂μ j) - ∫ y, ∑ t ∈ s, c t * Φ t y ∂ν) -
          ((∫ y, F y ∂ν) - ∫ y, ∑ t ∈ s, c t * Φ t y ∂ν) := by ring
  rw [e]
  calc _ ≤ ‖((∫ y, F y ∂μ j) - ∫ y, ∑ t ∈ s, c t * Φ t y ∂μ j) +
        ((∫ y, ∑ t ∈ s, c t * Φ t y ∂μ j) - ∫ y, ∑ t ∈ s, c t * Φ t y ∂ν)‖ +
          ‖(∫ y, F y ∂ν) - ∫ y, ∑ t ∈ s, c t * Φ t y ∂ν‖ := norm_sub_le _ _
    _ ≤ ‖(∫ y, F y ∂μ j) - ∫ y, ∑ t ∈ s, c t * Φ t y ∂μ j‖ +
        ‖(∫ y, ∑ t ∈ s, c t * Φ t y ∂μ j) - ∫ y, ∑ t ∈ s, c t * Φ t y ∂ν‖ +
          ‖(∫ y, F y ∂ν) - ∫ y, ∑ t ∈ s, c t * Φ t y ∂ν‖ := by
        gcongr
        exact norm_add_le _ _
    _ < ε := by linarith
end Compact
variable (d : CutoffData)
theorem one_lt_blockFactor : 1 < d.L := by
  have h := d.isAdmissible.2
  omega
theorem one_lt_blockFactor_real : (1 : ℝ) < d.L := by
  exact_mod_cast one_lt_blockFactor d
theorem torusSide_le_torusSide_iff {p q : ℕ} :
    PeriodicLattice.torusSide d.L p ≤ PeriodicLattice.torusSide d.L q ↔ p ≤ q := by
  simp only [PeriodicLattice.torusSide]
  rw [mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)]
  exact pow_le_pow_iff_right₀ (one_lt_blockFactor_real d)
theorem tendsto_torusSide_of_strictMono {i : ℕ → ℕ+} (hi : StrictMono i) :
    Tendsto (fun j => PeriodicLattice.torusSide d.L (i j)) atTop atTop := by
  have hnat : Tendsto (fun j => ((i j : ℕ+) : ℕ)) atTop atTop :=
    tendsto_atTop_mono (fun j => by
      have : StrictMono fun j => ((i j : ℕ+) : ℕ) := fun a b h => hi h
      exact this.le_apply) tendsto_id
  have hpow : Tendsto (fun n : ℕ => (d.L : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (one_lt_blockFactor_real d)
  exact (hpow.comp hnat).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
theorem sideExponent_sideAtExp (q : ℕ+) : d.sideExponent (d.sideAtExp q) = q :=
  (d.existsUnique_sideExponent (d.sideAtExp q).2).unique (d.torusSide_sideExponent _) rfl
theorem periodizedAtExp_eq (q : ℕ+) :
    d.periodizedAtExp q = CutoffLattice.periodizedMeasure d.L q d.K d.coupling := by
  change CutoffLattice.periodizedMeasure d.L (d.sideExponent (d.sideAtExp q) : ℕ+) d.K d.coupling = _
  rw [sideExponent_sideAtExp]
theorem withSide_periodizedWilsonMeasure (ℓ' : d.sideSet) :
    ((d.withSide ℓ').periodizedWilsonMeasure : Measure (GaugeField d.spacing)) =
      d.periodizedAtExp (d.sideExponent ℓ') :=
  (periodizedAtExp_eq d _).symm
section Wilson
variable (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
include hW
theorem isProbabilityMeasure_wilsonGibbs :
    IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure d.L d.m d.K d.coupling) :=
  (hW d.L d.m d.K d.coupling (one_lt_blockFactor d) d.m.pos d.K.pos).2.2.2.2.2.2.2.1
theorem wilsonGibbs_compl_compact :
    PeriodicLattice.wilsonGibbsMeasure d.L d.m d.K d.coupling
      (PeriodicLattice.compactGaugeFields d.L d.m ((d.K : ℕ) : ℤ))ᶜ = 0 :=
  (hW d.L d.m d.K d.coupling (one_lt_blockFactor d) d.m.pos d.K.pos).2.2.2.2.2.2.2.2.1
theorem isProbabilityMeasure_periodized :
    IsProbabilityMeasure d.periodizedWilsonMeasure := by
  haveI := isProbabilityMeasure_wilsonGibbs d hW
  exact Measure.isProbabilityMeasure_map
    (measurable_liftField d.L d.m ((d.K : ℕ) : ℤ)).aemeasurable
theorem isProbabilityMeasure_periodizedAtExp (q : ℕ+) :
    IsProbabilityMeasure (d.periodizedAtExp q) :=
  isProbabilityMeasure_periodized (d.withSide (d.sideAtExp q)) hW
end Wilson
theorem period_mem_latticeSubgroup {v : AmbientSpace} (hv : v ∈ d.periodLattice) :
    v ∈ latticeSubgroup d.spacing := by
  obtain ⟨n, rfl⟩ := hv
  have hL : (d.L : ℝ) ≠ 0 := by
    have := one_lt_blockFactor_real d
    positivity
  refine ⟨fun μ => n μ * (2 * (d.L : ℤ) ^ ((d.m : ℕ) + (d.K : ℕ))), fun μ => ?_⟩
  simp only [TestFunctions.latticeTranslate, CutoffData.spacing, PeriodicLattice.meshSize,
    Conventions.StandingParameters.side, PeriodicLattice.torusSide, zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  field_simp
theorem mem_periodLattice_iff {v : AmbientSpace} :
    v ∈ d.periodLattice ↔
      ∃ n : Fin 4 → ℤ, ∀ μ, v μ = (n μ : ℝ) * PeriodicLattice.torusSide d.L d.m := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, fun μ => mul_comm _ _⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, funext fun μ => by
      rw [hn μ]
      exact mul_comm _ _⟩
theorem projLink_translateLink (b : Link d.spacing) (v : LatticePoint d.spacing)
    (hv : (v : AmbientSpace) ∈ d.periodLattice) :
    d.projLink (CutoffLattice.translateLink b v) = d.projLink b := by
  obtain ⟨n, hn⟩ := hv
  have key : ∀ x : LatticePoint d.spacing,
      projectPoint d.L d.m ((d.K : ℕ) : ℤ) (x + v) = projectPoint d.L d.m ((d.K : ℕ) : ℤ) x := by
    intro x
    refine Subtype.ext ?_
    change TorusMetric.torusProj (PeriodicLattice.torusSide d.L d.m)
      ((x : AmbientSpace) + (v : AmbientSpace)) = _
    rw [← hn]
    exact TestFunctions.torusProj_add_latticeTranslate _ _ _
  exact PeriodicLattice.Bond.ext (key b.initial) (key b.terminal)
theorem shift_linkMap (b : Link d.spacing) (v : LatticePoint d.spacing) :
    (shift v).linkMap b = CutoffLattice.translateLink b v :=
  Link.ext (Subtype.ext rfl) (Subtype.ext rfl)
theorem periodInvariantFields_eq_periodicFields :
    d.periodInvariantFields = periodicFields d.L d.m ((d.K : ℕ) : ℤ) := by
  ext U
  constructor
  · intro hU v hv
    refine Subtype.ext (funext fun b => ?_)
    change U ((shift v).linkMap b) = U b
    rw [shift_linkMap]
    exact hU b v ((mem_periodLattice_iff d).mpr hv)
  · intro hU b v hv
    have h := congrArg (fun W : GaugeField d.spacing => W b)
      (hU v ((mem_periodLattice_iff d).mp hv))
    change U ((shift v).linkMap b) = U b at h
    rwa [shift_linkMap] at h
theorem isClosed_periodInvariantFields : IsClosed d.periodInvariantFields := by
  have hev : ∀ b : Link d.spacing, Continuous fun U : GaugeField d.spacing => U b := fun b =>
    (continuous_apply b).comp continuous_subtype_val
  have hset : d.periodInvariantFields =
      ⋂ (b : Link d.spacing) (v : LatticePoint d.spacing) (_ : (v : AmbientSpace) ∈ d.periodLattice),
        {U : GaugeField d.spacing | U (CutoffLattice.translateLink b v) = U b} := by
    ext U
    simp only [CutoffData.periodInvariantFields, mem_setOf_eq, mem_iInter]
  rw [hset]
  exact isClosed_iInter fun b => isClosed_iInter fun v => isClosed_iInter fun _ =>
    isClosed_eq (hev _) (hev _)
theorem liftField_mem_periodInvariantFields (U : d.PeriodicFields) :
    d.liftField U ∈ d.periodInvariantFields := by
  intro b v hv
  have h1 := liftCompactField_apply (m := d.m) U (CutoffLattice.translateLink b v)
  have h2 := liftCompactField_apply (m := d.m) U b
  have h3 := projLink_translateLink d b v hv
  exact h1.trans ((congrArg _ h3).trans h2.symm)
theorem trivialField_mem_periodInvariantFields :
    trivialField d.spacing ∈ d.periodInvariantFields := fun _ _ _ => rfl
theorem gaugeField_ext_of_links (hV : LinksAndTheirVariables.Statement)
    {U U' : GaugeField d.spacing} (h : ∀ b ∈ d.links, U b = U' b) : U = U' := by
  refine Subtype.ext (funext fun b => ?_)
  rcases (hV d).1.1 b with ⟨hb, -⟩ | ⟨⟨b', hb', rfl⟩, -⟩
  · exact h b hb
  · change U b'.opposite = U' b'.opposite
    rw [U.2, U'.2, h b' hb']
section Image
variable (hV : LinksAndTheirVariables.Statement)
  (hL : PeriodicFieldsAtPositiveLinks)
  (hC : WindowProjectionProperties)
include hL hC in
theorem liftField_injective : Function.Injective d.liftField := by
  intro U U' h
  apply (hL d).1.2.2.2.2.1
  funext l
  obtain ⟨b, -, hb⟩ : (l : d.PeriodicBond) ∈ d.projLink '' d.links := by
    rw [(hC d).1.1]
    exact l.2
  change U.linkValue l.1 = U'.linkValue l.1
  rw [← hb]
  have h1 := liftCompactField_apply (m := d.m) U b
  have h2 := liftCompactField_apply (m := d.m) U' b
  exact h1.symm.trans ((congrArg (fun W : GaugeField d.spacing => W b) h).trans h2)
include hV hL hC in
theorem periodInvariantFields_subset_range :
    d.periodInvariantFields ⊆ range d.liftField := by
  intro U' hU'
  have hsurj : ∀ l : d.positiveLinkSet, ∃ b ∈ d.links, d.projLink b = l.1 := by
    intro l
    have : (l : d.PeriodicBond) ∈ d.projLink '' d.links := by
      rw [(hC d).1.1]
      exact l.2
    exact this
  choose pick pick_mem pick_proj using hsurj
  have hproj : ∀ b ∈ d.links, d.projLink b ∈ d.positiveLinkSet := fun b hb => by
    rw [← (hC d).1.1]
    exact ⟨b, hb, rfl⟩
  have hpick : ∀ (b : Link d.spacing) (hb : b ∈ d.links),
      U' (pick ⟨d.projLink b, hproj b hb⟩) = U' b := by
    rintro b hb
    have hl := pick_proj ⟨d.projLink b, hproj b hb⟩
    obtain ⟨z, μ', hz⟩ := pick_mem ⟨d.projLink b, hproj b hb⟩
    obtain ⟨x, μ, rfl⟩ := hb
    rw [hz] at hl ⊢
    obtain ⟨rfl, hsite⟩ := ((hC d).1.2.2.2.2.2.1 x z μ μ').mp hl.symm
    have hper : ((x - z : LatticePoint d.spacing) : AmbientSpace) ∈ d.periodLattice := by
      obtain ⟨n, hn⟩ := hsite
      exact (mem_periodLattice_iff d).mpr ⟨n, hn⟩
    have hinv := hU' (Link.forwardFrom z μ) (x - z) hper
    have hlink : CutoffLattice.translateLink (Link.forwardFrom z μ) (x - z) =
        Link.forwardFrom x μ := by
      refine Link.ext ?_ ?_
      · change z + (x - z) = x
        abel
      · change z + axisStep d.spacing μ + (x - z) = x + axisStep d.spacing μ
        abel
    rw [hlink] at hinv
    exact hinv.symm
  obtain ⟨U, hU⟩ := (hL d).1.2.2.2.2.2 (fun l => U' (pick l))
  refine ⟨U, gaugeField_ext_of_links d hV fun b hb => ?_⟩
  have h1 := liftCompactField_apply (m := d.m) U b
  have h2 := congrFun hU ⟨d.projLink b, hproj b hb⟩
  exact h1.trans (h2.trans (hpick b hb))
include hV hL hC in
theorem range_liftField : range d.liftField = d.periodInvariantFields :=
  Subset.antisymm (range_subset_iff.mpr (liftField_mem_periodInvariantFields d))
    (periodInvariantFields_subset_range d hV hL hC)
end Image
theorem periodized_periodInvariantFields
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    d.periodizedWilsonMeasure d.periodInvariantFields = 1 := by
  haveI := isProbabilityMeasure_wilsonGibbs d hW
  have hmeas : MeasurableSet d.periodInvariantFields :=
    (isClosed_periodInvariantFields d).measurableSet
  have hpre : InfiniteLattice.liftField d.L d.m ((d.K : ℕ) : ℤ) ⁻¹' d.periodInvariantFields =
      univ := by
    refine eq_univ_of_forall fun U => ?_
    by_cases hU : U ∈ PeriodicLattice.compactGaugeFields d.L d.m ((d.K : ℕ) : ℤ)
    · exact liftField_mem_periodInvariantFields d ⟨U, hU⟩
    · rw [mem_preimage, liftField_of_notMem hU]
      exact trivialField_mem_periodInvariantFields d
  have h := liftedWilsonMeasure_apply d.L d.m d.K d.coupling hmeas
  change liftedWilsonMeasure d.L d.m d.K d.coupling _ = 1
  rw [h, hpre]
  exact measure_univ
theorem periodizedWilsonMeasure_apply
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (E : Set (GaugeField d.spacing)) (hE : MeasurableSet E) :
    d.periodizedWilsonMeasure E =
      PeriodicLattice.wilsonGibbsMeasure d.L d.m d.K d.coupling
        {U | ∃ h : U ∈ PeriodicLattice.compactGaugeFields d.L d.m ((d.K : ℕ) : ℤ),
          d.liftField ⟨U, h⟩ ∈ E} := by
  have h := liftedWilsonMeasure_apply d.L d.m d.K d.coupling hE
  change liftedWilsonMeasure d.L d.m d.K d.coupling E = _
  rw [h]
  have hae : ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure d.L d.m d.K d.coupling,
      U ∈ PeriodicLattice.compactGaugeFields d.L d.m ((d.K : ℕ) : ℤ) := by
    rw [ae_iff]
    exact wilsonGibbs_compl_compact d hW
  refine measure_congr (eventuallyEq_set.mpr ?_)
  filter_upwards [hae] with U hU
  exact ⟨fun h' => ⟨hU, h'⟩, fun ⟨_, h'⟩ => h'⟩
section Limits
variable (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
theorem mem_torusWeakLimits_of_isWeakLimit (ν : d.FieldProb) (h : d.IsWeakLimitAlongExps ν) :
    ν ∈ d.torusWeakLimits := by
  obtain ⟨i, ρ, hi, hρ, hconv⟩ := h
  exact ⟨fun j => d.sideAtExp (i j), ρ, tendsto_torusSide_of_strictMono d hi, hρ, hconv⟩
theorem isCluster_of_mem_torusWeakLimits (ν : d.FieldProb) (h : ν ∈ d.torusWeakLimits) :
    d.IsClusterAlongExps ν := by
  obtain ⟨ℓ, ρ, hℓ, hρ, hconv⟩ := h
  intro n _ F ε hε i₀
  have h1 : ∀ s : Fin n, ∀ᶠ j in atTop, ‖(ρ j).expect (F s) - ν.expect (F s)‖ < ε := by
    intro s
    have := Metric.tendsto_nhds.mp (hconv (F s)) ε hε
    simpa only [dist_eq_norm] using this
  have h2 : ∀ᶠ j in atTop, PeriodicLattice.torusSide d.L i₀ ≤ (ℓ j : ℝ) :=
    hℓ.eventually_ge_atTop _
  obtain ⟨j, hj1, hj2⟩ := ((eventually_all.mpr h1).and h2).exists
  refine ⟨d.sideExponent (ℓ j), ?_, fun s => ?_⟩
  · rw [← d.torusSide_sideExponent (ℓ j)] at hj2
    exact (torusSide_le_torusSide_iff d).mp hj2
  · have hm : d.periodizedAtExp (d.sideExponent (ℓ j)) = (ρ j).1 :=
      (withSide_periodizedWilsonMeasure d (ℓ j)).symm.trans (hρ j).symm
    rw [hm]
    exact hj1 s
include hW in
theorem isWeakLimit_of_isCluster
    (hV : LinksAndTheirVariables.Statement)
    (hM : Measures.CompactMetric.measuresAndContinuousFunctions)
    (ν : d.FieldProb) (h : d.IsClusterAlongExps ν) : d.IsWeakLimitAlongExps ν := by
  obtain ⟨-, hcomp, hmet, -, -⟩ := (hV d).2.1
  haveI := hcomp
  haveI := hmet
  haveI : Nonempty (GaugeField d.spacing) := ⟨trivialField d.spacing⟩
  obtain ⟨Φ, hΦ⟩ := exists_denseSeq_continuous (X := GaugeField d.spacing) hM
  let P : ℕ → ℕ → Prop := fun j k => ∀ t, t ≤ j →
    ‖(∫ U, Φ t U ∂d.periodizedAtExp k.succPNat) - ν.expect (Φ t)‖ <
      1 / ((j : ℝ) + 1)
  have hfreq : ∀ j, ∃ᶠ k in atTop, P j k := by
    intro j
    refine frequently_atTop.mpr fun N => ?_
    obtain ⟨i, hi, hs⟩ := h (j + 1) (by omega) (fun s => Φ s) (1 / ((j : ℝ) + 1))
      (by positivity) N.succPNat
    refine ⟨i.natPred, ?_, fun t ht => ?_⟩
    · have h1 : ((N.succPNat : ℕ+) : ℕ) ≤ (i : ℕ) := hi
      have h2 : i.natPred + 1 = (i : ℕ) := PNat.natPred_add_one i
      have h3 : ((N.succPNat : ℕ+) : ℕ) = N + 1 := rfl
      omega
    · rw [PNat.succPNat_natPred]
      exact hs ⟨t, by omega⟩
  obtain ⟨φ, hφ, hP⟩ := extraction_forall_of_frequently hfreq
  haveI hprob : ∀ q, IsProbabilityMeasure (d.periodizedAtExp q) :=
    isProbabilityMeasure_periodizedAtExp d hW
  let ρ : ℕ → d.FieldProb := fun j => ⟨d.periodizedAtExp (φ j).succPNat, hprob _⟩
  haveI : ∀ j, IsProbabilityMeasure (ρ j).1 := fun j => (ρ j).2
  haveI : IsProbabilityMeasure ν.1 := ν.2
  refine ⟨fun j => (φ j).succPNat, ρ, Nat.succPNat_strictMono.comp hφ, fun _ => rfl, fun F => ?_⟩
  refine tendsto_integral_of_denseSeq Φ hΦ (fun j => (ρ j).1) ν.1 (fun t => ?_) F
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop t] with j hj
  exact (hP j t hj).le
end Limits
theorem isSubseqWeakLimit_iff (ν : d.FieldProb) :
    d.IsSubseqWeakLimit ν ↔ d.IsWeakLimitAlongExps ν := by
  constructor
  · rintro ⟨φ, ρ, hφ, hρ, hconv⟩
    exact ⟨fun j => (φ j).succPNat, ρ, Nat.succPNat_strictMono.comp hφ, hρ, hconv⟩
  · rintro ⟨i, ρ, hi, hρ, hconv⟩
    refine ⟨fun j => (i j).natPred, ρ, fun a b hab => ?_, fun j => ?_, hconv⟩
    · have h1 : ((i a : ℕ+) : ℕ) < (i b : ℕ+) := hi hab
      have h2 := PNat.natPred_add_one (i a)
      have h3 := PNat.natPred_add_one (i b)
      change (i a).natPred < (i b).natPred
      omega
    · change (ρ j).1 = d.periodizedAtExp (i j).natPred.succPNat
      rw [PNat.succPNat_natPred]
      exact hρ j
end LiftImage
open LiftImage in
theorem liftImageAndPeriodizedLimits_proof
    (hV : LinksAndTheirVariables.Statement)
    (hL : PeriodicFieldsAtPositiveLinks)
    (hC : WindowProjectionProperties)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hM : Measures.CompactMetric.measuresAndContinuousFunctions) :
    LiftImageAndPeriodizedLimits := by
  intro d
  have hinj := liftField_injective d hL hC
  have hrange := range_liftField d hV hL hC
  have hper := periodInvariantFields_eq_periodicFields d
  have hweak : ∀ ν : d.FieldProb, ν ∈ d.torusWeakLimits ↔ d.IsWeakLimitAlongExps ν :=
    fun ν => ⟨fun h => isWeakLimit_of_isCluster d hW hV hM ν
        (isCluster_of_mem_torusWeakLimits d ν h), mem_torusWeakLimits_of_isWeakLimit d ν⟩
  have hclus : ∀ ν : d.FieldProb, ν ∈ d.torusWeakLimits ↔ d.IsClusterAlongExps ν :=
    fun ν => ⟨isCluster_of_mem_torusWeakLimits d ν, fun h =>
      mem_torusWeakLimits_of_isWeakLimit d ν (isWeakLimit_of_isCluster d hW hV hM ν h)⟩
  refine ⟨⟨fun b v hv => ?_, hinj, hrange, hper, isClosed_periodInvariantFields d,
      periodized_periodInvariantFields d hW⟩, fun ν => ⟨hweak ν, hclus ν⟩,
    fun U b => liftCompactField_apply U b, ?_,
    isProbabilityMeasure_periodized d hW, periodizedWilsonMeasure_apply d hW, ?_, ?_⟩
  · let w : LatticePoint d.spacing := ⟨v, period_mem_latticeSubgroup d hv⟩
    exact ⟨CutoffLattice.translateLink b w, rfl, rfl⟩
  · refine ⟨fun _ _ => ?_, hinj.injOn, fun U' hU' => ?_⟩
    · rw [← hper, ← hrange]
      exact mem_range_self _
    · rw [← hper, ← hrange] at hU'
      obtain ⟨U, rfl⟩ := hU'
      exact ⟨U, mem_univ _, rfl⟩
  · ext ν
    exact (isSubseqWeakLimit_iff d ν).trans (hweak ν).symm
  · ext ν
    exact (hclus ν).symm
end YangMills.Construction.CutoffLinks
