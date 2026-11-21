import YangMills.Construction.Torus.CellsOfATranslatedLatticeAndBallsOfTheTorusProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
noncomputable section
namespace YangMills.Construction
open TorusMetric TestFunctions TorusMeasure
namespace TorusCovering
variable {s : Conventions.StandingParameters}
theorem torusSide_pos (s : Conventions.StandingParameters) :
    0 < PeriodicLattice.torusSide s.L s.m := by apply _root_.YangMills.Construction.TorusMeasure.TranslatedLatticeCells.torusSide_pos <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem toLevelUnits_self (L K : ℕ) (θ : ℝ) : PeriodicLattice.toLevelUnits L K K θ = θ := by
  simp [PeriodicLattice.toLevelUnits, PeriodicLattice.levelDepth]
theorem isLift_iff_proj_eq (u : s.Torus) (t : Fin 4 → ℝ) : IsLift s u t ↔ proj s t = u := by
  constructor
  · rintro ⟨v, hv, ht⟩
    have htv : t = v := funext fun μ => (ht μ).trans (toLevelUnits_self _ _ _)
    subst htv
    exact funext hv
  · rintro rfl
    exact ⟨t, fun _ => rfl, fun _ => (toLevelUnits_self _ _ _).symm⟩
theorem classOf_eq_proj (t : Fin 4 → ℝ) : classOf s t = proj s t := by
  have hex : ∃ x, PeriodicLattice.IsLevelLift s.L s.m s.K s.K x t :=
    ⟨proj s t, (isLift_iff_proj_eq _ _).2 rfl⟩
  have h : IsLift s (classOf s t) t := Classical.epsilon_spec hex
  exact ((isLift_iff_proj_eq _ _).1 h).symm
theorem proj_add (t t' : Fin 4 → ℝ) :
    proj s (t + t') = proj s t + proj s t' := by apply _root_.YangMills.Construction.TorusMeasure.BallProjection.proj_map_add <;> assumption
theorem proj_zero : proj s 0 = 0 := by apply _root_.YangMills.Construction.TorusMeasure.TranslatedLatticeCells.proj_map_zero <;> assumption
theorem addVec_eq (u : s.Torus) (t : Fin 4 → ℝ) :
    addVec s u t = u + proj s t := by
  have hex : ∃ w, PeriodicLattice.IsLevelLift s.L s.m s.K s.K u w := by
    obtain ⟨w, hw⟩ := torusProj_surjective (PeriodicLattice.torusSide s.L s.m) u
    exact ⟨w, (isLift_iff_proj_eq _ _).2 hw⟩
  have hw : IsLift s u (Classical.epsilon (PeriodicLattice.IsLevelLift s.L s.m s.K s.K u)) :=
    Classical.epsilon_spec hex
  have hw' := (isLift_iff_proj_eq _ _).1 hw
  have := classOf_eq_proj (s := s) (Classical.epsilon (PeriodicLattice.IsLevelLift s.L s.m s.K s.K u) + t)
  change classOf s _ = _
  rw [this, proj_add, hw']
theorem continuous_proj : Continuous (proj s) :=
  continuous_pi fun μ => (AddCircle.continuous_mk' _).comp (continuous_apply μ)
theorem exists_lift_minimizing_norm (u : s.Torus) :
    ∃ t₁, proj s t₁ = u ∧ ∀ t, proj s t = u → euclidNormVec t₁ ≤ euclidNormVec t := by
  have : Fact (0 < PeriodicLattice.torusSide s.L s.m) := ⟨torusSide_pos s⟩
  obtain ⟨t₀, ht₀⟩ := torusProj_surjective (PeriodicLattice.torusSide s.L s.m) u
  have ht₀' : proj s t₀ = u := ht₀
  set B := euclidNormVec t₀ with hB
  have hclosed : IsClosed (proj s ⁻¹' {u}) := isClosed_singleton.preimage continuous_proj
  have hball : ∀ t, euclidNormVec t ≤ B → t ∈ Metric.closedBall (0 : Fin 4 → ℝ) B := by
    intro t ht
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (abs_apply_le_euclidNormVec t₀ 0)
    rw [Metric.mem_closedBall, dist_pi_le_iff hB0]
    intro μ
    simpa [Real.dist_eq] using (abs_apply_le_euclidNormVec t μ).trans ht
  have hcomp : IsCompact (proj s ⁻¹' {u} ∩ Metric.closedBall (0 : Fin 4 → ℝ) B) :=
    (isCompact_closedBall _ _).inter_left hclosed
  have hne : (proj s ⁻¹' {u} ∩ Metric.closedBall (0 : Fin 4 → ℝ) B).Nonempty :=
    ⟨t₀, ht₀', hball _ le_rfl⟩
  obtain ⟨t₁, ⟨ht₁, -⟩, hmin⟩ := hcomp.exists_isMinOn hne continuous_euclidNormVec.continuousOn
  refine ⟨t₁, ht₁, fun t ht => ?_⟩
  have h₁₀ : euclidNormVec t₁ ≤ B := hmin ⟨ht₀', hball _ le_rfl⟩
  by_cases htB : euclidNormVec t ≤ B
  · exact hmin ⟨ht, hball _ htB⟩
  · exact h₁₀.trans (not_le.1 htB).le
theorem projectionProperties (s : Conventions.StandingParameters) : ProjectionProperties s := by
  refine ⟨fun θ => toLevelUnits_self _ _ _, fun t => (classOf_eq_proj t).symm, fun t => ?_,
    isLift_iff_proj_eq, fun u t ht t' => ?_, proj_add,
    torusProj_surjective (PeriodicLattice.torusSide s.L s.m), fun t => ?_, addVec_eq, fun u => ?_⟩
  · ext t'
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · exact fun h => exists_latticeTranslate_of_torusProj_eq h
    · rintro ⟨k, rfl⟩
      exact torusProj_add_latticeTranslate _ _ _
  · rw [isLift_iff_proj_eq, ← (isLift_iff_proj_eq _ _).1 ht]
    constructor
    · exact fun h => exists_latticeTranslate_of_torusProj_eq h
    · rintro ⟨k, rfl⟩
      exact torusProj_add_latticeTranslate _ _ _
  · constructor
    · intro h
      obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq (h.trans proj_zero.symm)
      exact ⟨k, by simpa using hk⟩
    · rintro ⟨k, rfl⟩
      have h := torusProj_add_latticeTranslate (PeriodicLattice.torusSide s.L s.m) 0 k
      rw [zero_add] at h
      exact h.trans proj_zero
  · obtain ⟨t₁, ht₁, hmin⟩ := exists_lift_minimizing_norm u
    have hleast : IsLeast (euclidNormVec '' {t | IsLift s u t}) (euclidNormVec t₁) := by
      refine ⟨⟨t₁, (isLift_iff_proj_eq _ _).2 ht₁, rfl⟩, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      exact hmin t ((isLift_iff_proj_eq _ _).1 ht)
    have hset : euclidNormVec '' {t | IsLift s u t} =
        euclidNormVec '' (torusProj (PeriodicLattice.torusSide s.L s.m) ⁻¹' {u}) := by
      congr 1
      ext t
      exact isLift_iff_proj_eq u t
    have hnum : pointNorm u = euclidNormVec t₁ := by
      change sInf (euclidNormVec '' (torusProj (PeriodicLattice.torusSide s.L s.m) ⁻¹' {u})) = _
      rw [← hset]
      exact hleast.csInf_eq
    rw [hnum]
    exact hleast
abbrev periodCube (ℓ : ℝ) : Set (Fin 4 → ℝ) := Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) ℓ
theorem volume_periodCube_ne_top (ℓ : ℝ) : volume (periodCube ℓ) ≠ ⊤ := by
  rw [Real.volume_pi_Ico]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
theorem IsBddMeasurable.integrable {h : s.Torus → ℝ} (hh : IsBddMeasurable h) :
    Integrable (fun t => h (proj s t))
      (volume.restrict (periodCube (PeriodicLattice.torusSide s.L s.m))) := by
  obtain ⟨⟨C, hC⟩, hm⟩ := hh
  have hae : AEMeasurable (fun t => h (proj s t)) volume := NullMeasurable.aemeasurable hm
  exact Measure.integrableOn_of_bounded (M := C) (volume_periodCube_ne_top _)
    hae.aestronglyMeasurable (ae_of_all _ fun t => hC _)
theorem IsBddMeasurable.aemeasurable {h : s.Torus → ℝ} (hh : IsBddMeasurable h) :
    AEMeasurable (fun t => h (proj s t)) volume :=
  NullMeasurable.aemeasurable hh.2
theorem IsBddMeasurable.linComb {h h' : s.Torus → ℝ} (hh : IsBddMeasurable h)
    (hh' : IsBddMeasurable h') (α α' : ℝ) :
    IsBddMeasurable (fun u => α * h u + α' * h' u) := by
  obtain ⟨C, hC⟩ := hh.1
  obtain ⟨C', hC'⟩ := hh'.1
  refine ⟨⟨|α| * C + |α'| * C', fun u => ?_⟩, ?_⟩
  · calc ‖α * h u + α' * h' u‖ ≤ ‖α * h u‖ + ‖α' * h' u‖ := norm_add_le _ _
      _ = |α| * ‖h u‖ + |α'| * ‖h' u‖ := by simp [norm_mul]
      _ ≤ |α| * C + |α'| * C' := by
        gcongr
        · exact hC u
        · exact hC' u
  · exact ((hh.aemeasurable.const_mul α).add (hh'.aemeasurable.const_mul α')).nullMeasurable
theorem IsBddMeasurable.mul {h h' : s.Torus → ℝ} (hh : IsBddMeasurable h)
    (hh' : IsBddMeasurable h') : IsBddMeasurable (fun u => h u * h' u) := by
  obtain ⟨C, hC⟩ := hh.1
  obtain ⟨C', hC'⟩ := hh'.1
  refine ⟨⟨C * C', fun u => ?_⟩, ?_⟩
  · rw [norm_mul]
    exact mul_le_mul (hC u) (hC' u) (norm_nonneg _) ((norm_nonneg _).trans (hC u))
  · exact (hh.aemeasurable.mul hh'.aemeasurable).nullMeasurable
theorem torusIntegral_linComb {h h' : s.Torus → ℝ} (hh : IsBddMeasurable h)
    (hh' : IsBddMeasurable h') (α α' : ℝ) :
    torusIntegral (fun u => α * h u + α' * h' u) =
      α * torusIntegral h + α' * torusIntegral h' := by
  unfold TorusMeasure.torusIntegral
  rw [integral_add (hh.integrable.const_mul α) (hh'.integrable.const_mul α'),
    integral_const_mul, integral_const_mul]
theorem torusIntegral_mono {h h' : s.Torus → ℝ} (hh : IsBddMeasurable h)
    (hh' : IsBddMeasurable h') (hle : ∀ u, h u ≤ h' u) :
    torusIntegral h ≤ torusIntegral h' :=
  integral_mono hh.integrable hh'.integrable fun _ => hle _
theorem torusIntegral_finset_sum {k : ℕ} {g : Fin k → s.Torus → ℝ}
    (hg : ∀ i, IsBddMeasurable (g i)) :
    torusIntegral (fun u => ∑ i, g i u) = ∑ i, torusIntegral (g i) := by
  unfold TorusMeasure.torusIntegral
  exact integral_finsetSum Finset.univ fun i _ => (hg i).integrable
theorem integralProperties (s : Conventions.StandingParameters) : IntegralProperties s :=
  fun _ _ hh hh' α α' =>
    ⟨hh.linComb hh' α α', hh.mul hh', torusIntegral_linComb hh hh' α α', torusIntegral_mono hh hh'⟩
theorem isBddMeasurable_indicator {E : Set s.Torus} (hE : IsMeasurableTorusSet E) :
    IsBddMeasurable (E.indicator (1 : s.Torus → ℝ)) := by
  refine ⟨⟨1, fun u => ?_⟩, (isMeasurableTorusSet_iff_indicator E).1 hE⟩
  by_cases hu : u ∈ E <;> simp [hu]
theorem indicator_iUnion_one_eq_sum {k : ℕ} {E : Fin k → Set s.Torus}
    (hd : Pairwise (Function.onFun Disjoint E)) (u : s.Torus) :
    (⋃ i, E i).indicator (1 : s.Torus → ℝ) u = ∑ i, (E i).indicator (1 : s.Torus → ℝ) u := by
  classical
  by_cases hu : u ∈ ⋃ i, E i
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hu
    rw [indicator_of_mem hu, Finset.sum_eq_single i]
    · simp [indicator_of_mem hi]
    · intro j _ hji
      have hj : u ∉ E j := fun hj => Set.disjoint_left.1 (hd hji) hj hi
      simp [indicator_of_notMem hj]
    · simp
  · have hi : ∀ i, u ∉ E i := fun i h => hu (mem_iUnion.2 ⟨i, h⟩)
    simp [hi]
theorem volumeProperties (s : Conventions.StandingParameters) : VolumeProperties s := by
  refine ⟨fun E E' hE hE' hsub => ?_, fun k E hE hd => ?_, ?_, ?_⟩
  · exact torusIntegral_mono (isBddMeasurable_indicator hE) (isBddMeasurable_indicator hE')
      fun u => Set.indicator_le_indicator_of_subset hsub (fun _ => zero_le_one) u
  · refine ⟨?_, ?_, fun h hh => ?_⟩
    · change NullMeasurableSet (proj s ⁻¹' ⋃ i, E i) volume
      rw [preimage_iUnion]
      exact NullMeasurableSet.iUnion hE
    · unfold torusVolume
      rw [funext (indicator_iUnion_one_eq_sum hd)]
      exact torusIntegral_finset_sum fun i => isBddMeasurable_indicator (hE i)
    · unfold setTorusIntegral
      have hfun : (fun u => (⋃ i, E i).indicator (1 : s.Torus → ℝ) u * h u) =
          fun u => ∑ i, (E i).indicator (1 : s.Torus → ℝ) u * h u := by
        funext u
        rw [indicator_iUnion_one_eq_sum hd, Finset.sum_mul]
      rw [hfun]
      exact torusIntegral_finset_sum fun i => (isBddMeasurable_indicator (hE i)).mul hh
  · change NullMeasurableSet (proj s ⁻¹' univ) volume
    rw [preimage_univ]
    exact MeasurableSet.univ.nullMeasurableSet
  · have hpos := torusSide_pos s
    unfold torusVolume TorusMeasure.torusIntegral
    simp only [indicator_univ, Pi.one_apply]
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real,
      Real.volume_pi_Ico_toReal (fun _ => hpos.le)]
    simp
section Periodization
variable {ℓ : ℝ}
theorem le_euclidNormVec_latticeTranslate (hℓ : 0 < ℓ) {d : Fin 4 → ℤ} (hd : d ≠ 0) :
    ℓ ≤ euclidNormVec (latticeTranslate ℓ d) := by apply _root_.YangMills.Construction.TestPairs.le_euclidNormVec_latticeTranslate <;> assumption
variable {S : Set (Fin 4 → ℝ)} {f : (Fin 4 → ℝ) → ℝ}
theorem nonzero_shifts_subsingleton (hℓ : 0 < ℓ) (hS : HasDiameterLE S (ℓ / 2))
    (hz : ∀ t, t ∉ S → f t = 0) (t : Fin 4 → ℝ) :
    {k : Fin 4 → ℤ | f (t + latticeTranslate ℓ k) ≠ 0}.Subsingleton := by
  intro k hk k' hk'
  by_contra hne
  have h1 : t + latticeTranslate ℓ k ∈ S := by_contra fun h => hk (hz _ h)
  have h2 : t + latticeTranslate ℓ k' ∈ S := by_contra fun h => hk' (hz _ h)
  have h3 := hS _ h1 _ h2
  have h4 : t + latticeTranslate ℓ k - (t + latticeTranslate ℓ k') = latticeTranslate ℓ (k - k') := by
    funext μ
    simp [latticeTranslate]
    ring
  rw [h4] at h3
  have h5 := le_euclidNormVec_latticeTranslate hℓ (sub_ne_zero.2 hne)
  linarith
theorem summable_shifts
    (hsub : ∀ t, {k : Fin 4 → ℤ | f (t + latticeTranslate ℓ k) ≠ 0}.Subsingleton)
    (t : Fin 4 → ℝ) : Summable fun k => f (t + latticeTranslate ℓ k) := by
  by_cases h : ∃ k₀, f (t + latticeTranslate ℓ k₀) ≠ 0
  · obtain ⟨k₀, hk₀⟩ := h
    refine (hasSum_single k₀ fun k hk => ?_).summable
    by_contra h'
    exact hk (hsub t h' hk₀)
  · push Not at h
    rw [funext h]
    exact summable_zero
theorem norm_periodicSum_le
    (hsub : ∀ t, {k : Fin 4 → ℤ | f (t + latticeTranslate ℓ k) ≠ 0}.Subsingleton)
    {C : ℝ} (hC : ∀ t, ‖f t‖ ≤ C) (t : Fin 4 → ℝ) : ‖periodicSum ℓ f t‖ ≤ C := by
  unfold periodicSum
  by_cases h : ∃ k₀, f (t + latticeTranslate ℓ k₀) ≠ 0
  · obtain ⟨k₀, hk₀⟩ := h
    rw [tsum_eq_single k₀ fun k hk => ?_]
    · exact hC _
    · by_contra h'
      exact hk (hsub t h' hk₀)
  · push Not at h
    rw [funext h, tsum_zero, norm_zero]
    exact (norm_nonneg _).trans (hC 0)
theorem integrable_of_eq_zero_off (hℓ : 0 < ℓ) (hS : HasDiameterLE S (ℓ / 2))
    (hz : ∀ t, t ∉ S → f t = 0) {C : ℝ} (hC : ∀ t, ‖f t‖ ≤ C) (hf : AEMeasurable f volume) :
    Integrable f volume := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · have h0 : f = 0 := funext fun t => hz t (notMem_empty t)
    rw [h0]
    exact integrable_zero _ _ _
  · have hsub : S ⊆ Metric.closedBall t₀ (ℓ / 2) := by
      intro x hx
      rw [Metric.mem_closedBall, dist_pi_le_iff (by positivity)]
      intro μ
      simpa [Real.dist_eq] using (abs_apply_le_euclidNormVec (x - t₀) μ).trans (hS x hx t₀ ht₀)
    have hon : IntegrableOn f (Metric.closedBall t₀ (ℓ / 2)) volume :=
      Measure.integrableOn_of_bounded (M := C) Metric.isBounded_closedBall.measure_lt_top.ne
        hf.aestronglyMeasurable (ae_of_all _ hC)
    exact hon.integrable_of_forall_notMem_eq_zero fun t ht => hz t fun h => ht (hsub h)
def shiftedCube (ℓ : ℝ) (k : Fin 4 → ℤ) : Set (Fin 4 → ℝ) :=
  (fun x => x - latticeTranslate ℓ k) ⁻¹' periodCube ℓ
theorem measurableSet_shiftedCube (ℓ : ℝ) (k : Fin 4 → ℤ) :
    MeasurableSet (shiftedCube ℓ k) :=
  (MeasurableSet.univ_pi fun _ => measurableSet_Ico).preimage (measurable_id.sub_const _)
theorem int_eq_of_sub_mul_mem_Ico (hℓ : 0 < ℓ) {a : ℝ} {n n' : ℤ} (h : a - ℓ * n ∈ Ico (0 : ℝ) ℓ)
    (h' : a - ℓ * n' ∈ Ico (0 : ℝ) ℓ) : n = n' := by
  have key : ∀ {p q : ℤ}, a - ℓ * p ∈ Ico (0 : ℝ) ℓ → a - ℓ * q ∈ Ico (0 : ℝ) ℓ → p < q + 1 := by
    intro p q hp hq
    have h1 : ℓ * (p : ℝ) < ℓ * ((q : ℝ) + 1) := by
      have := hp.1
      have := hq.2
      linarith
    have h2 : (p : ℝ) < (q : ℝ) + 1 := lt_of_mul_lt_mul_left h1 hℓ.le
    exact_mod_cast h2
  have := key h h'
  have := key h' h
  omega
theorem pairwise_disjoint_shiftedCube (hℓ : 0 < ℓ) :
    Pairwise (Function.onFun Disjoint (shiftedCube ℓ)) := by
  intro k k' hne
  refine Set.disjoint_left.2 fun x hx hx' => hne ?_
  funext μ
  exact int_eq_of_sub_mul_mem_Ico (a := x μ) hℓ (by simpa [latticeTranslate] using hx μ (mem_univ μ))
    (by simpa [latticeTranslate] using hx' μ (mem_univ μ))
theorem iUnion_shiftedCube (hℓ : 0 < ℓ) : ⋃ k, shiftedCube ℓ k = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.2 ⟨fun μ => ⌊x μ / ℓ⌋, fun μ _ => ?_⟩
  have h1 := Int.floor_le (x μ / ℓ)
  have h2 := Int.lt_floor_add_one (x μ / ℓ)
  have h3 : ℓ * (x μ / ℓ) = x μ := by field_simp
  have h4 : ℓ * (⌊x μ / ℓ⌋ : ℝ) ≤ x μ := by
    calc ℓ * (⌊x μ / ℓ⌋ : ℝ) ≤ ℓ * (x μ / ℓ) := mul_le_mul_of_nonneg_left h1 hℓ.le
      _ = x μ := h3
  have h5 : x μ < ℓ * (⌊x μ / ℓ⌋ : ℝ) + ℓ := by
    calc x μ = ℓ * (x μ / ℓ) := h3.symm
      _ < ℓ * ((⌊x μ / ℓ⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left h2 hℓ
      _ = ℓ * (⌊x μ / ℓ⌋ : ℝ) + ℓ := by ring
  simp only [latticeTranslate, Pi.sub_apply, mem_Ico]
  constructor <;> linarith
theorem setIntegral_add_latticeTranslate (g : (Fin 4 → ℝ) → ℝ) (k : Fin 4 → ℤ) :
    ∫ t in periodCube ℓ, g (t + latticeTranslate ℓ k) = ∫ y in shiftedCube ℓ k, g y := by
  have h := (measurePreserving_add_right (volume : Measure (Fin 4 → ℝ))
    (latticeTranslate ℓ k)).setIntegral_preimage_emb
    (MeasurableEquiv.addRight (latticeTranslate ℓ k)).measurableEmbedding g (shiftedCube ℓ k)
  have hpre : (fun x => x + latticeTranslate ℓ k) ⁻¹' shiftedCube ℓ k = periodCube ℓ := by
    ext x
    simp [shiftedCube]
  rw [hpre] at h
  exact h
theorem integral_tsum_shifts (hℓ : 0 < ℓ) (hi : Integrable f volume) :
    ∫ t in periodCube ℓ, ∑' k, f (t + latticeTranslate ℓ k) = ∫ t, f t := by
  have hm := measurableSet_shiftedCube ℓ
  have hd := pairwise_disjoint_shiftedCube hℓ
  have hs1 := hasSum_integral_iUnion hm hd hi.integrableOn
  rw [iUnion_shiftedCube hℓ, setIntegral_univ] at hs1
  have hs3 := hasSum_integral_iUnion hm hd hi.norm.integrableOn
  have hnorm : Summable fun k : Fin 4 → ℤ =>
      ∫ t in periodCube ℓ, ‖f (t + latticeTranslate ℓ k)‖ := by
    have h := hs3.summable
    refine h.congr fun k => ?_
    exact (setIntegral_add_latticeTranslate (fun y => ‖f y‖) k).symm
  have hs2 := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (periodCube ℓ)) (F := fun k t => f (t + latticeTranslate ℓ k))
    (fun k => (hi.comp_add_right (latticeTranslate ℓ k)).restrict) hnorm
  have hs1' : HasSum (fun k : Fin 4 → ℤ => ∫ t in periodCube ℓ, f (t + latticeTranslate ℓ k))
      (∫ t, f t) := (funext fun k => setIntegral_add_latticeTranslate f k : (fun k : Fin 4 → ℤ => ∫ t in periodCube ℓ, f (t + latticeTranslate ℓ k)) = fun k => ∫ y in shiftedCube ℓ k, f y) ▸ hs1
  exact hs2.unique hs1'
end Periodization
theorem periodizationProperties (s : Conventions.StandingParameters) :
    PeriodizationProperties s := by
  intro S f hS hb hf hz
  have hℓ := torusSide_pos s
  obtain ⟨C, hC⟩ := hb
  have hsub := nonzero_shifts_subsingleton hℓ hS hz
  have hae : AEMeasurable f volume := NullMeasurable.aemeasurable hf
  have hi := integrable_of_eq_zero_off hℓ hS hz hC hae
  have hcomp : (periodize (PeriodicLattice.torusSide s.L s.m) f : s.Torus → ℝ) ∘ proj s =
      periodicSum (PeriodicLattice.torusSide s.L s.m) f :=
    funext fun t => periodize_torusProj _ f t
  refine ⟨hsub, ⟨⟨C, fun x => norm_periodicSum_le hsub hC _⟩, ?_⟩, ?_⟩
  · change NullMeasurable ((periodize (PeriodicLattice.torusSide s.L s.m) f : s.Torus → ℝ) ∘ proj s)
      volume
    rw [hcomp]
    refine AEMeasurable.nullMeasurable ?_
    refine aemeasurable_of_tendsto_metrizable_ae (u := (atTop : Filter (Finset (Fin 4 → ℤ))))
      (f := fun A t => ∑ k ∈ A, f (t + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k))
      (fun A => (integrable_finsetSum A fun k _ =>
        hi.comp_add_right (latticeTranslate (PeriodicLattice.torusSide s.L s.m) k)).aemeasurable)
      (ae_of_all _ fun t => ?_)
    have h := (summable_shifts hsub t).hasSum
    simpa [HasSum, SummationFilter.unconditional_filter, periodicSum] using h
  · have h := integral_tsum_shifts hℓ hi
    unfold TorusMeasure.torusIntegral integralR4
    rw [← h]
    refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun t _ => ?_
    exact periodize_torusProj _ f t
theorem coveringIntegralVolumeStatement_holds : CoveringIntegralVolumeStatement := fun s =>
  ⟨projectionProperties s, integralProperties s, volumeProperties s, periodizationProperties s⟩
end TorusCovering
end YangMills.Construction
