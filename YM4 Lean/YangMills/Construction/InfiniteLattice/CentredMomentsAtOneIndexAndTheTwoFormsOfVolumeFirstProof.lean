import YangMills.Construction.InfiniteLattice.CentredIdentityInAState
import YangMills.Construction.InfiniteLattice.CentredMomentsAtOneIndexAndTheTwoFormsOfVolumeFirst
import YangMills.Construction.InfiniteLattice.FactsOfOneLatticeAtOneSpacing
import YangMills.Construction.InfiniteLattice.PeriodisationAndThreeIdentitiesOfTheCoveringProof
import YangMills.Construction.Lattice.LatticesOfATorusAndTheProductTopologyOfConfigurations
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.CutoffLimits.CenteredMomentsAndVolumeFirst
open InfiniteLattice AmbientPoints GibbsAtFixedSpacing
theorem isBoundedRealRV_smearedEnergy (hF : FixedSpacing.BasicFacts)
    (D : FixedSpacing.Setup) {f : AmbientSpace → ℝ} (hf : f ∈ compactTestFunctions) :
    Probability.IsBoundedRealRV (smearedEnergy f : D.Fields → ℝ) := by
  obtain ⟨-, ⟨hcpt, -⟩, ⟨hsub, -⟩, -, -, -, -, hobs, -⟩ := hF D
  have hc : Continuous fun U : D.Fields => ((smearedEnergy f U : ℝ) : ℂ) :=
    hsub (hobs f hf).2
  have hr : Continuous (smearedEnergy f : D.Fields → ℝ) := Complex.continuous_re.comp hc
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hr.continuousOn
  exact ⟨hr.measurable, C, fun U => hC U (Set.mem_univ U)⟩
def centeredFactor {a : ℝ} (ν : Measure (GaugeField a)) (h : AmbientSpace → ℝ) (U : GaugeField a) :
    ℝ :=
  smearedEnergy h U - ∫ V, smearedEnergy h V ∂ν
theorem centeredProduct_eq_ofReal_prod {a : ℝ} (ν : Measure (GaugeField a)) {k : ℕ}
    (f : Fin k → AmbientSpace → ℝ) (U : GaugeField a) :
    centeredProduct ν f U = ((∏ i, centeredFactor ν (f i) U : ℝ) : ℂ) := by
  unfold centeredProduct
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [centeredFactor, Complex.ofReal_sub, Probability.complexExpectation, integral_complex_ofReal]
theorem centredMoment_eq_ofReal_integral {a : ℝ} (ν' ν : Measure (GaugeField a)) {k : ℕ}
    (f : Fin k → AmbientSpace → ℝ) :
    centredMoment ν' ν f = ((∫ U, ∏ i, centeredFactor ν (f i) U ∂ν' : ℝ) : ℂ) := by
  rw [centeredMoment_eq_expectation, Probability.complexExpectation]
  simp only [centeredProduct_eq_ofReal_prod]
  exact integral_complex_ofReal
theorem centeredFactor_measurable_bounded (hF : FixedSpacing.BasicFacts)
    (D : FixedSpacing.Setup) (ν : Measure D.Fields) {h : AmbientSpace → ℝ}
    (hh : h ∈ compactTestFunctions) :
    Measurable (centeredFactor ν h) ∧ ∃ C : ℝ, ∀ U, |centeredFactor ν h U| ≤ C := by
  obtain ⟨hm, C, hC⟩ := isBoundedRealRV_smearedEnergy hF D hh
  refine ⟨hm.sub_const _, C + |∫ V, smearedEnergy h V ∂ν|, fun U => ?_⟩
  exact (abs_sub _ _).trans (add_le_add_left (hC U) _)
theorem prod_centeredFactor_measurable_bounded (hF : FixedSpacing.BasicFacts)
    (D : FixedSpacing.Setup) (ν : Measure D.Fields) {k : ℕ}
    {f : Fin k → AmbientSpace → ℝ} (hf : ∀ i, f i ∈ compactTestFunctions) :
    Measurable (fun U : D.Fields => ∏ i, centeredFactor ν (f i) U) ∧
      ∃ C : ℝ, ∀ U : D.Fields, |∏ i, centeredFactor ν (f i) U| ≤ C := by
  choose hm C hC using fun i => centeredFactor_measurable_bounded hF D ν (hf i)
  refine ⟨Finset.measurable_prod _ fun i _ => hm i, ∏ i, C i, fun U => ?_⟩
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => hC i U
theorem integrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : Ω → ℝ} (hm : Measurable x) (hb : ∃ C : ℝ, ∀ U, |x U| ≤ C) : Integrable x μ := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
theorem centeredMomentProperties (hF : FixedSpacing.BasicFacts)
    (D : FixedSpacing.Setup) (ν ν' : Measure D.Fields) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] : CenteredMomentProperties ν' ν := by
  intro k f hf
  refine ⟨⟨fun i => isBoundedRealRV_smearedEnergy hF D (hf i), ?_, ?_⟩, ?_, ?_, ?_, rfl⟩
  · obtain ⟨hm, C, hC⟩ := prod_centeredFactor_measurable_bounded hF D ν hf
    have e : centeredProduct ν f = fun U => ((∏ i, centeredFactor ν (f i) U : ℝ) : ℂ) :=
      funext (centeredProduct_eq_ofReal_prod ν f)
    rw [e]
    refine ⟨by simpa only [Complex.ofReal_re] using hm,
      by simpa only [Complex.ofReal_im] using measurable_const, C, fun U => ?_⟩
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hC U
  · rw [centredMoment_eq_ofReal_integral]
    exact Complex.ofReal_im _
  · rintro rfl
    rw [centredMoment_eq_ofReal_integral]
    simp
  · intro ς
    rw [centredMoment_eq_ofReal_integral, centredMoment_eq_ofReal_integral]
    have e : ∀ U, ∏ i, centeredFactor ν (f (ς i)) U = ∏ i, centeredFactor ν (f i) U := fun U =>
      Equiv.prod_comp ς fun i => centeredFactor ν (f i) U
    simp only [e]
  · intro i u v hu hv t t'
    have hlin := (hF D).2.2.2.2.2.2.2.2.2
    have hupd : ∀ w, w ∈ compactTestFunctions → ∀ j,
        Function.update f i w j ∈ compactTestFunctions := by
      intro w hw j
      by_cases h : j = i
      · subst h
        simpa using hw
      · simpa [h] using hf j
    have hiO : ∀ w, w ∈ compactTestFunctions →
        Integrable (smearedEnergy w : D.Fields → ℝ) ν := by
      intro w hw
      obtain ⟨hm, hb⟩ := isBoundedRealRV_smearedEnergy hF D hw
      exact integrable_of_abs_le hm hb
    have hfac : ∀ U, centeredFactor ν (t • u + t' • v) U =
        t * centeredFactor ν u U + t' * centeredFactor ν v U := by
      intro U
      simp only [centeredFactor, hlin u hu v hv t t']
      rw [integral_add ((hiO u hu).const_mul t) ((hiO v hv).const_mul t'), integral_const_mul,
        integral_const_mul]
      ring
    have hP : ∀ (w : AmbientSpace → ℝ) (U : D.Fields),
        ∏ j, centeredFactor ν (Function.update f i w j) U =
          centeredFactor ν w U * ∏ j ∈ Finset.univ \ {i}, centeredFactor ν (f j) U := by
      intro w U
      have e : ∀ j, centeredFactor ν (Function.update f i w j) U =
          Function.update (fun j => centeredFactor ν (f j) U) i (centeredFactor ν w U) j := fun j =>
        Function.apply_update (fun _ h => centeredFactor ν h U) f i w j
      rw [Finset.prod_congr rfl fun j _ => e j, Finset.prod_update_of_mem (Finset.mem_univ i)]
    have hiP : ∀ w, w ∈ compactTestFunctions →
        Integrable (fun U : D.Fields =>
          ∏ j, centeredFactor ν (Function.update f i w j) U) ν' := by
      intro w hw
      obtain ⟨hm, hb⟩ := prod_centeredFactor_measurable_bounded hF D ν (hupd w hw)
      exact integrable_of_abs_le hm hb
    have key : ∫ U, ∏ j, centeredFactor ν (Function.update f i (t • u + t' • v) j) U ∂ν' =
        t * ∫ U, ∏ j, centeredFactor ν (Function.update f i u j) U ∂ν' +
          t' * ∫ U, ∏ j, centeredFactor ν (Function.update f i v j) U ∂ν' := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add ((hiP u hu).const_mul t) ((hiP v hv).const_mul t')]
      refine integral_congr_ae (ae_of_all _ fun U => ?_)
      simp only [hP, hfac]
      ring
    rw [centredMoment_eq_ofReal_integral, centredMoment_eq_ofReal_integral,
      centredMoment_eq_ofReal_integral, key]
    push_cast
    rfl
theorem measurable_linkValues {L m : ℕ} {k : ℤ} :
    Measurable (fun U : PeriodicLattice.CompactGaugeField L m k => U.1) := by apply _root_.YangMills.Construction.PeriodizationIdentities.measurable_compactGaugeField_val <;> assumption
theorem liftedGibbs_eq (hC : ConnectedFunctionExpansion.Statement)
    (hP : GaugeFieldProduct.Statement) (D : FixedSpacing.Setup)
    (hK : 1 ≤ D.level) :
    D.liftedGibbs = liftedWilsonMeasure D.L D.m D.level D.β := by
  obtain ⟨-, ⟨-, -, hfin⟩, -, -⟩ :=
    hP.1 D.L D.m (D.level : ℤ) D.admissible D.m.pos (Int.natCast_nonneg _)
  have := hfin.1
  have := Fintype.ofFinite (PeriodicLattice.Plaquette D.L D.m (D.level : ℤ))
  obtain ⟨-, -, -, -, hmap⟩ :=
    (hC D.L D.m D.level D.admissible D.m.pos).2.2.2.2.1 D.β
  have hmapW := (hmap hK D.β_pos).2
  have hw : ∀ U : D.TorusFields,
      Complex.exp (-PeriodicLattice.barycenterWeightedEnergy (fun _ => (D.β : ℂ)) U.1) =
        ((Real.exp (-D.β * D.wilsonEnergy U) : ℝ) : ℂ) := by
    intro U
    have e : PeriodicLattice.barycenterWeightedEnergy (fun _ => (D.β : ℂ)) U.1 =
        ((D.β * D.wilsonEnergy U : ℝ) : ℂ) := by
      simp only [PeriodicLattice.barycenterWeightedEnergy, PeriodicLattice.plaquetteWeightedEnergy,
        FixedSpacing.Setup.wilsonEnergy, PeriodicLattice.wilsonAction]
      rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [PeriodicLattice.complexPlaquetteEnergy_eq, Complex.ofReal_mul]
    rw [e, ← Complex.ofReal_neg, ← Complex.ofReal_exp, neg_mul]
  have hZ : D.partitionFunction =
      (PeriodicLattice.sourcedPartitionFunction D.L D.m D.level D.β 0).re := by
    have e : PeriodicLattice.sourcedPartitionFunction D.L D.m D.level D.β 0 =
        ((D.partitionFunction : ℝ) : ℂ) := by
      unfold PeriodicLattice.sourcedPartitionFunction FixedSpacing.Setup.partitionFunction
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (ae_of_all _ fun U => ?_)
      simpa using hw U
    rw [e, Complex.ofReal_re]
  have hmeas : D.gibbs = PeriodicLattice.normalizedActionMeasure D.L D.m D.level D.β := by
    unfold FixedSpacing.Setup.gibbs PeriodicLattice.normalizedActionMeasure
    rw [← hZ]
    simp only [hw, Complex.ofReal_re]
  unfold FixedSpacing.Setup.liftedGibbs liftedWilsonMeasure
  rw [hmeas, ← hmapW, Measure.map_map (measurable_liftField _ _ _) measurable_linkValues]
  rfl
theorem isProbabilityMeasure_of_mem_torusLimits {D : FixedSpacing.Setup} {ν : Measure D.Fields}
    (hν : ν ∈ D.torusLimits) : IsProbabilityMeasure ν := by
  obtain ⟨-, -, ρ', -, -, rfl, -⟩ := hν
  exact ρ'.2
theorem isInfiniteVolumeLimit_of_mem (hC : ConnectedFunctionExpansion.Statement)
    (hP : GaugeFieldProduct.Statement) (D : FixedSpacing.Setup)
    (hK : 1 ≤ D.level) {ν : Measure D.Fields} (hν : ν ∈ D.torusLimits) :
    IsInfiniteVolumeLimit D.L D.level D.β ν := by
  obtain ⟨n, ρ, ρ', hside, hρ, rfl, hconv⟩ := hν
  have hL : (1 : ℝ) ≤ D.L := by
    have h := D.admissible.2
    exact_mod_cast (by omega : 1 ≤ D.L)
  have hn : Tendsto (fun i => ((n i : ℕ+) : ℕ)) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [hside.eventually_gt_atTop (2 * (D.L : ℝ) ^ b)] with i hi
    by_contra h
    have h1 : (D.L : ℝ) ^ ((n i : ℕ+) : ℕ) ≤ (D.L : ℝ) ^ b :=
      pow_le_pow_right₀ hL (not_le.1 h).le
    have h2 : (D.withExponent (n i)).side = 2 * (D.L : ℝ) ^ ((n i : ℕ+) : ℕ) := by
      simp [FixedSpacing.Setup.side, FixedSpacing.Setup.withExponent, PeriodicLattice.torusSide]
    linarith
  obtain ⟨φ, hφ, hφ'⟩ := strictMono_subseq_of_tendsto_atTop hn
  refine ⟨ρ'.2, fun k => ((n (φ k) : ℕ+) : ℕ), hφ', fun F => ?_⟩
  have h1 := hconv (fun U => ((F U : ℝ) : ℂ)) (Complex.continuous_ofReal.comp F.continuous)
  have h2 := (Complex.continuous_re.tendsto _).comp (h1.comp hφ.tendsto_atTop)
  have e : ∀ μ : BorelProb D.mesh, (μ.integral fun U => ((F U : ℝ) : ℂ)).re = ∫ x, F x ∂μ.1 := by
    intro μ
    change (∫ U, ((F U : ℝ) : ℂ) ∂μ.1).re = _
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have h3 : Tendsto (fun k => ∫ x, F x ∂(ρ (φ k)).1) atTop (𝓝 (∫ x, F x ∂ρ'.1)) := by
    simpa only [Function.comp_def, e] using h2
  refine h3.congr fun k => ?_
  rw [hρ (φ k), liftedGibbs_eq hC hP (D.withExponent (n (φ k))) hK]
  rfl
theorem eventually_notMem_of_finite {B : Set ℕ+} (hB : B.Finite) : ∀ᶠ i in atTop, i ∉ B := by
  obtain ⟨M, hM⟩ := hB.bddAbove
  filter_upwards [eventually_gt_atTop M] with i hi hiB
  exact absurd (hM hiB) (not_le.2 hi)
theorem tendsto_comp_of_tendsAlong {J : Set ℕ+} {e : ℕ+ → ℕ+} (he : StrictMono e)
    (hJ : Set.range e = J) {t : J → ℂ} {t₀ : ℂ} (h : TendsAlong J t t₀) :
    Tendsto (fun i => t ⟨e i, hJ ▸ Set.mem_range_self i⟩) atTop (𝓝 t₀) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hB := (h (ε / 2) (by positivity)).preimage
    (f := fun i => (⟨e i, hJ ▸ Set.mem_range_self i⟩ : J))
    (fun x _ y _ hxy => he.injective (congrArg Subtype.val hxy))
  filter_upwards [eventually_notMem_of_finite hB] with i hi
  have h1 : ‖t ⟨e i, hJ ▸ Set.mem_range_self i⟩ - t₀‖ ≤ ε / 2 := not_not.1 hi
  rw [dist_eq_norm]
  linarith
theorem tendsAlong_of_tendsto_comp {J : Set ℕ+} {e : ℕ+ → ℕ+} (hJ : Set.range e = J) {t : J → ℂ}
    {t₀ : ℂ} (h : Tendsto (fun i => t ⟨e i, hJ ▸ Set.mem_range_self i⟩) atTop (𝓝 t₀)) :
    TendsAlong J t t₀ := by
  subst hJ
  intro ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 h ε hε)
  refine Set.Finite.subset ((Set.finite_Icc 1 M).image
    fun i => (⟨e i, Set.mem_range_self i⟩ : Set.range e)) ?_
  rintro ⟨_, i, rfl⟩ hj
  refine ⟨i, ⟨one_le, ?_⟩, rfl⟩
  by_contra hc
  apply hj
  have h1 := hM i (not_le.1 hc).le
  rw [dist_eq_norm] at h1
  exact h1.le
theorem tendsto_cutoff_comp {D : Setting} (Q : PassageSequence D) {e : ℕ+ → ℕ+} (he : StrictMono e) :
    Tendsto (fun i => ((Q.K (e i) : ℕ+) : ℕ)) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  have hB := (Q.cutoff_tend (b : ℝ)).preimage (f := e) he.injective.injOn
  filter_upwards [eventually_notMem_of_finite hB] with i hi
  have h1 : (b : ℝ) ≤ ((Q.K (e i) : ℕ) : ℝ) := not_not.1 hi
  exact_mod_cast h1
theorem isCompact_tsupport_iff_r4 (s : Conventions.StandingParameters) (g : Pt s .euclidean → ℝ) :
    IsCompact (tsupport g) ↔ IsCompact (tsupport (X := Fin 4 → ℝ) g) := by
  have hid : (homeomorphR4 s) '' tsupport g = tsupport (X := Fin 4 → ℝ) g := by
    rw [← tsupport_eq_of_r4 (s := s) g]
    ext x
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨x, hx, rfl⟩⟩
  rw [← hid, (homeomorphR4 s).isCompact_image]
theorem mem_compactTestFunctions_of_isC1c {f : AmbientSpace → ℝ} (h : SchwingerFunctions.IsC1c f) :
    f ∈ compactTestFunctions := by
  have hc : Continuous f := ContDiff.continuous (h.1 : ContDiff ℝ 1 f)
  exact ⟨hc.measurable, hc.bounded_above_of_compact_support h.2, h.2⟩
theorem isC1c_of_pt (s : Conventions.StandingParameters) {g : Pt s .euclidean → ℝ}
    (h : IsC1Fn g ∧ IsCompact (tsupport g)) : SchwingerFunctions.IsC1c g :=
  ⟨h.1, (isCompact_tsupport_iff_r4 s g).1 h.2⟩
theorem exists_pos_le_on_finset {α : Type*} (F : Finset α) (r : α → ℝ) (hr : ∀ x, 0 < r x) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ F, d ≤ r x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert x F _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    refine ⟨min d (r x), lt_min hd (hr x), fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h y hy)
theorem isSeparatedC1cTuple_of_mem (s : Conventions.StandingParameters) {n : ℕ}
    {f : Fin n → Pt s .euclidean → ℝ}
    (hf : f ∈ separatedTuples s .euclidean n) : IsSeparatedC1cTuple f := by
  have hpair : ∀ p : Fin n × Fin n, ∃ r : ℝ, 0 < r ∧ (p.1 ≠ p.2 → ENNReal.ofReal r ≤
      TestFunctions.setDistR4 (tsupport (X := Fin 4 → ℝ) (f p.1))
        (tsupport (X := Fin 4 → ℝ) (f p.2))) := by
    rintro ⟨i, k⟩
    by_cases hik : i = k
    · exact ⟨1, one_pos, fun h => absurd hik h⟩
    obtain ⟨r, hr, h⟩ := Metric.exists_pos_forall_lt_edist (hf.1 i).2 (isClosed_tsupport (f k))
      (hf.2 hik)
    refine ⟨r, by exact_mod_cast hr, fun _ => ?_⟩
    refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    rw [← tsupport_eq_of_r4 (s := s) (f i)] at hx
    rw [← tsupport_eq_of_r4 (s := s) (f k)] at hy
    have h1 : (r : ENNReal) ≤ edist (show Pt s .euclidean from x)
        (show Pt s .euclidean from y) := (h x hx y hy).le
    rw [edist_dist] at h1
    rw [ENNReal.ofReal_coe_nnreal]
    exact h1
  choose r hr hle using hpair
  obtain ⟨d, hd, hdr⟩ := exists_pos_le_on_finset Finset.univ r hr
  refine ⟨fun i => isC1c_of_pt s (hf.1 i), d, hd, fun i k hik => ?_⟩
  exact (ENNReal.ofReal_le_ofReal (hdr (i, k) (Finset.mem_univ _))).trans (hle (i, k) hik)
theorem mem_separatedTuples_of_isSeparatedC1cTuple (s : Conventions.StandingParameters) {n : ℕ}
    {f : Fin n → Pt s .euclidean → ℝ}
    (hf : IsSeparatedC1cTuple f) : f ∈ separatedTuples s .euclidean n := by
  obtain ⟨hc, d, hd, hsep⟩ := hf
  refine ⟨fun i => ⟨(hc i).1, (isCompact_tsupport_iff_r4 s (f i)).2 (hc i).2⟩, fun i k hik => ?_⟩
  have hdis : Disjoint (tsupport (X := Fin 4 → ℝ) (f i)) (tsupport (X := Fin 4 → ℝ) (f k)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    have h1 := (hsep i k hik).trans (iInf₂_le_of_le x hx (iInf₂_le x hy))
    rw [euclidNormVec_sub_self, ENNReal.ofReal_zero] at h1
    exact absurd (ENNReal.ofReal_eq_zero.1 (le_antisymm h1 bot_le)) (not_le.2 hd)
  change Disjoint (tsupport (f i)) (tsupport (f k))
  rw [tsupport_eq_of_r4 (f i), tsupport_eq_of_r4 (f k)]
  exact hdis
theorem ursellFunction_update_linear (hV : ∃ F : Submodule ℝ (AmbientSpace → ℝ),
      (F : Set (AmbientSpace → ℝ)) = compactTestFunctions) {a : ℝ} {ν : Measure (GaugeField a)}
    {n : ℕ} (h : InfiniteLattice.CenteredIdentity.UrsellIsRealSymmetricMultilinear ν n)
    {f : Fin n → AmbientSpace → ℝ} (hf : ∀ i, f i ∈ compactTestFunctions) (k : Fin n)
    {g g' : AmbientSpace → ℝ} (hg : g ∈ compactTestFunctions) (hg' : g' ∈ compactTestFunctions)
    (s t : ℝ) :
    ursellFunction ν n (Function.update f k (s • g + t • g')) =
      (s : ℂ) * ursellFunction ν n (Function.update f k g) +
        (t : ℂ) * ursellFunction ν n (Function.update f k g') := by
  obtain ⟨F, hF⟩ := hV
  have hsm : ∀ (c : ℝ) (w : AmbientSpace → ℝ), w ∈ compactTestFunctions →
      c • w ∈ compactTestFunctions := by
    intro c w hw
    rw [← hF] at hw ⊢
    exact F.smul_mem c hw
  have hupd : ∀ w, w ∈ compactTestFunctions → ∀ j,
      Function.update f k w j ∈ compactTestFunctions := by
    intro w hw j
    by_cases hj : j = k
    · subst hj
      simpa using hw
    · simpa [hj] using hf j
  have e1 := (h (Function.update f k (s • g)) (hupd _ (hsm s g hg))).2.2.1 k (t • g')
    (hsm t g' hg')
  have e2 := (h (Function.update f k g) (hupd _ hg)).2.2.2 k s
  have e3 := (h (Function.update f k g') (hupd _ hg')).2.2.2 k t
  simp only [Function.update_self, Function.update_idem] at e1 e2 e3
  rw [e1, e2, e3]
theorem isContinuumSchwingerFamily_of_tendsto {S' : (n : ℕ) → (Fin n → AmbientSpace → ℝ) → ℂ}
    {c : ℕ+ → (n : ℕ) → (Fin n → AmbientSpace → ℝ) → ℂ}
    (hlin : ∀ (i : ℕ+) (n : ℕ), 2 ≤ n → ∀ f : Fin n → AmbientSpace → ℝ,
      (∀ k, f k ∈ compactTestFunctions) → ∀ (k : Fin n) (g g' : AmbientSpace → ℝ),
      g ∈ compactTestFunctions → g' ∈ compactTestFunctions → ∀ s t : ℝ,
      c i n (Function.update f k (s • g + t • g')) =
        (s : ℂ) * c i n (Function.update f k g) + (t : ℂ) * c i n (Function.update f k g'))
    (hlim : ∀ (n : ℕ), 2 ≤ n → ∀ f : Fin n → AmbientSpace → ℝ, IsSeparatedC1cTuple f →
      Tendsto (fun i => c i n f) atTop (𝓝 (S' n f))) :
    SchwingerFunctions.IsContinuumSchwingerFamily S' := by
  intro n hn C hC hsep f hf i g h a b hg hgs hh hhs
  obtain ⟨d, hd, hdC⟩ := hsep
  have hsepW : ∀ w : Fin n → AmbientSpace → ℝ,
      (∀ k, SchwingerFunctions.IsC1c (w k) ∧ tsupport (w k) ⊆ C k) →
      IsSeparatedC1cTuple w := by
    intro w hw
    refine ⟨fun k => (hw k).1, d, hd, fun k l hkl => ?_⟩
    refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    exact (hdC k l hkl).trans (iInf₂_le_of_le x ((hw k).2 hx) (iInf₂_le y ((hw l).2 hy)))
  have hup : ∀ w, SchwingerFunctions.IsC1c w → tsupport w ⊆ C i →
      IsSeparatedC1cTuple (Function.update f i w) := by
    intro w hw hws
    refine hsepW _ fun k => ?_
    by_cases hk : k = i
    · subst hk
      simpa using ⟨hw, hws⟩
    · simpa [hk] using hf k
  have hcomb : SchwingerFunctions.IsC1c (a • g + b • h) :=
    ⟨ContDiff.add (contDiff_const.smul hg.1) (contDiff_const.smul hh.1),
      (hg.2.smul_left (f := fun _ => a)).add (hh.2.smul_left (f := fun _ => b))⟩
  have hcombs : tsupport (a • g + b • h) ⊆ C i := by
    refine closure_minimal ?_ (hC i).isClosed
    intro x hx
    by_contra hxC
    have hgx : g x = 0 := by
      by_contra h0
      exact hxC (hgs (subset_tsupport _ h0))
    have hhx : h x = 0 := by
      by_contra h0
      exact hxC (hhs (subset_tsupport _ h0))
    exact hx (by simp [hgx, hhx])
  have hent : ∀ k, f k ∈ compactTestFunctions := fun k => mem_compactTestFunctions_of_isC1c (hf k).1
  have l0 := hlim n hn _ (hup _ hcomb hcombs)
  have l1 := hlim n hn _ (hup g hg hgs)
  have l2 := hlim n hn _ (hup h hh hhs)
  refine tendsto_nhds_unique l0 (((l1.const_mul (a : ℂ)).add (l2.const_mul (b : ℂ))).congr
    fun j => ?_)
  exact (hlin j n hn f hent i g h (mem_compactTestFunctions_of_isC1c hg)
    (mem_compactTestFunctions_of_isC1c hh) a b).symm
theorem isConnectedFamily_of_tendsto {D : Setting} {S : RealFamily D}
    {c : ℕ+ → (n : ℕ) → (Fin n → AmbientSpace → ℝ) → ℂ}
    (hlin : ∀ (i : ℕ+) (n : ℕ), 2 ≤ n → ∀ f : Fin n → AmbientSpace → ℝ,
      (∀ k, f k ∈ compactTestFunctions) → ∀ (k : Fin n) (g g' : AmbientSpace → ℝ),
      g ∈ compactTestFunctions → g' ∈ compactTestFunctions → ∀ s t : ℝ,
      c i n (Function.update f k (s • g + t • g')) =
        (s : ℂ) * c i n (Function.update f k g) + (t : ℂ) * c i n (Function.update f k g'))
    (hsym : ∀ (i : ℕ+) (n : ℕ), 2 ≤ n → ∀ f : Fin n → AmbientSpace → ℝ,
      (∀ k, f k ∈ compactTestFunctions) → ∀ ς : Equiv.Perm (Fin n),
      c i n (fun k => f (ς k)) = c i n f)
    (hlim : ∀ (n : ℕ) (hn : 2 ≤ n) (X : D.SepTuples n),
      Tendsto (fun i => c i n X.1) atTop (𝓝 ((S n hn X : ℝ) : ℂ))) :
    IsConnectedFamily S := by
  have hent : ∀ {n : ℕ} (X : D.SepTuples n) (k : Fin n),
      X.1 k ∈ compactTestFunctions := fun X k =>
    mem_compactTestFunctions_of_isC1c (isC1c_of_pt D.euclideanParams (X.2.1 k))
  have hmul : ∀ (n : ℕ) (hn : 2 ≤ n), IsTupleMultilinear (S n hn) := by
    intro n hn A hA
    let val : ((i : Fin n) → c1Submodule (A i)) → Fin n → Pt D.euclideanParams .euclidean → ℝ :=
      fun m i => (m i : Pt D.euclideanParams .euclidean → ℝ)
    have hval : ∀ m, val m ∈ D.SepTuples n := fun m =>
      mem_separatedTuples_of_forall_mem_c1 hA fun i => (m i).2
    have hupd : ∀ (m : (i : Fin n) → c1Submodule (A i)) (i : Fin n)
        (x : c1Submodule (A i)),
        val (Function.update m i x) = Function.update (val m) i x.1 := by
      intro m i x
      funext j
      by_cases hj : j = i
      · subst hj
        simp [val]
      · simp [val, hj]
    have key : ∀ (m : (i : Fin n) → c1Submodule (A i)) (i : Fin n)
        (x y z : c1Submodule (A i)) (p q : ℝ), z.1 = p • x.1 + q • y.1 →
        S n hn ⟨val (Function.update m i z), hval _⟩ =
          p * S n hn ⟨val (Function.update m i x), hval _⟩ +
            q * S n hn ⟨val (Function.update m i y), hval _⟩ := by
      intro m i x y z p q hz
      apply Complex.ofReal_injective
      have l0 := hlim n hn ⟨val (Function.update m i z), hval _⟩
      have l1 := hlim n hn ⟨val (Function.update m i x), hval _⟩
      have l2 := hlim n hn ⟨val (Function.update m i y), hval _⟩
      have hx : x.1 ∈ compactTestFunctions :=
        mem_compactTestFunctions_of_isC1c (isC1c_of_pt D.euclideanParams ⟨x.2.1, x.2.2.1⟩)
      have hy : y.1 ∈ compactTestFunctions :=
        mem_compactTestFunctions_of_isC1c (isC1c_of_pt D.euclideanParams ⟨y.2.1, y.2.2.1⟩)
      push_cast
      refine tendsto_nhds_unique l0 (((l1.const_mul (p : ℂ)).add (l2.const_mul (q : ℂ))).congr
        fun j => ?_)
      change _ = c j n (val (Function.update m i z))
      simp only [hupd, hz]
      exact (hlin j n hn (val m) (hent ⟨val m, hval m⟩) i x.1 y.1 hx hy p q).symm
    refine ⟨{ toFun := fun g => S n hn ⟨val g, hval g⟩
              map_update_add' := ?_
              map_update_smul' := ?_ }, fun g => rfl⟩
    · intro inst m i x y
      obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
      have h := key m i x y (x + y) 1 1 (by simp)
      simpa using h
    · intro inst m i t x
      obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
      have h := key m i x x (t • x) t 0 (by simp)
      simpa using h
  refine ⟨fun n hn => ⟨fun f ς => ?_, hmul n hn⟩, ⟨S, hmul⟩, rfl⟩
  have l1 := hlim n hn ⟨permuteTuple ς f.1, permuteTuple_mem f.2 ς⟩
  have l2 := hlim n hn f
  refine Complex.ofReal_injective (tendsto_nhds_unique l1 (l2.congr fun i => ?_))
  exact (hsym i n hn f.1 (hent f) ς).symm
theorem statement_holds (hS : InfiniteLattice.CenteredIdentity.Statement)
    (hF : FixedSpacing.BasicFacts)
    (hC : ConnectedFunctionExpansion.Statement)
    (hP : GaugeFieldProduct.Statement) : Statement := by
  refine ⟨fun D ν ν' h h' => centeredMomentProperties hF D ν ν', fun s X hX i =>
    mem_compactTestFunctions_of_isC1c (isC1c_of_pt s (hX.1 i)), ?_⟩
  intro D Q J e he hJ ν hν S S' hS'
  have hmem : ∀ i, e i ∈ J := fun i => hJ ▸ Set.mem_range_self i
  let νe : ∀ i, Measure (Q.Fields (e i)) := fun i => ν ⟨e i, hmem i⟩
  have hprob : ∀ i, IsProbabilityMeasure (νe i) := fun i =>
    isProbabilityMeasure_of_mem_torusLimits (hν ⟨e i, hmem i⟩)
  have hvol : ∀ i, IsInfiniteVolumeLimit D.choice.L (Q.K (e i)) (Q.β (e i)) (νe i) := fun i =>
    isInfiniteVolumeLimit_of_mem hC hP (Q.latticeAt (e i)) (Q.K (e i)).pos (hν ⟨e i, hmem i⟩)
  have hV : ∃ F : Submodule ℝ (AmbientSpace → ℝ),
      (F : Set (AmbientSpace → ℝ)) = compactTestFunctions :=
    (hF (Q.latticeAt 1)).2.2.2.2.2.2.2.2.1
  have hcum : ∀ (i : ℕ+) (n : ℕ), 2 ≤ n →
      InfiniteLattice.CenteredIdentity.UrsellIsRealSymmetricMultilinear (νe i) n :=
    fun i n hn => (hS ⟨D.L, D.admissible, Q.K (e i), 1⟩ (νe i) (hprob i)).2.1 n hn
  let c : ℕ+ → (n : ℕ) → (Fin n → AmbientSpace → ℝ) → ℂ := fun i n f =>
    ursellFunction (νe i) n f
  have hlin : ∀ (i : ℕ+) (n : ℕ), 2 ≤ n → ∀ f : Fin n → AmbientSpace → ℝ,
      (∀ k, f k ∈ compactTestFunctions) → ∀ (k : Fin n) (g g' : AmbientSpace → ℝ),
      g ∈ compactTestFunctions → g' ∈ compactTestFunctions → ∀ s t : ℝ,
      c i n (Function.update f k (s • g + t • g')) =
        (s : ℂ) * c i n (Function.update f k g) + (t : ℂ) * c i n (Function.update f k g') :=
    fun i n hn f hf k g g' hg hg' s t =>
      ursellFunction_update_linear hV (hcum i n hn) hf k hg hg' s t
  have hsym : ∀ (i : ℕ+) (n : ℕ), 2 ≤ n → ∀ f : Fin n → AmbientSpace → ℝ,
      (∀ k, f k ∈ compactTestFunctions) → ∀ ς : Equiv.Perm (Fin n),
      c i n (fun k => f (ς k)) = c i n f :=
    fun i n hn f hf ς => (hcum i n hn f hf).2.1 ς
  have hlimOf : IsVolumeFirstLimitWith Q S J ν → ∀ (n : ℕ) (hn : 2 ≤ n)
      (X : D.SepTuples n), Tendsto (fun i => c i n X.1) atTop (𝓝 ((S n hn X : ℝ) : ℂ)) :=
    fun h n hn X => tendsto_comp_of_tendsAlong he hJ (h.2.2 n hn X)
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => isConnectedFamily_of_tendsto hlin hsym (hlimOf h)⟩
  · have hl : ∀ (n : ℕ), 2 ≤ n → ∀ f : Fin n → AmbientSpace → ℝ, IsSeparatedC1cTuple f →
        Tendsto (fun i => c i n f) atTop (𝓝 (S' n f)) := by
      intro n hn f hf
      have hX := mem_separatedTuples_of_isSeparatedC1cTuple D.euclideanParams hf
      have l := hlimOf h n hn ⟨f, hX⟩
      rw [← hS' n hn ⟨f, hX⟩] at l
      exact l
    exact ⟨isContinuumSchwingerFamily_of_tendsto hlin hl, tendsto_cutoff_comp Q he,
      fun i => Q.mem_window (e i), hvol, hl⟩
  · obtain ⟨_, _, _, _, hl⟩ := h
    refine ⟨hJ ▸ Set.infinite_range_of_injective he.injective, hν, fun n hn X => ?_⟩
    refine tendsAlong_of_tendsto_comp hJ ?_
    have l := hl n hn X.1 (isSeparatedC1cTuple_of_mem D.euclideanParams X.2)
    rw [hS' n hn X] at l
    exact l
end YangMills.Construction.CutoffLimits.CenteredMomentsAndVolumeFirst
end
