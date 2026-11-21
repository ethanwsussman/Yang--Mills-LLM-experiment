import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAtASpacingProof
import YangMills.Construction.InfiniteLattice.DilationToSpacingOneProof
import YangMills.Construction.InfiniteLattice.TransportToSpacingOne
import YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.InfiniteLattice YangMills.Construction.NormalFamilies YangMills.Construction.UnitSpacing
open scoped ComplexConjugate ComplexOrder NNReal Topology
noncomputable section
namespace YangMills.Construction.UnitSpacing
variable {a : ℝ}
theorem measurableEmbedding_fieldRescale_of_homeomorph {ha : 0 < a}
    (e : GaugeField a ≃ₜ GaugeField 1) (he : ⇑e = fieldRescale ha) :
    MeasurableEmbedding (fieldRescale ha) := by
  rw [← he]
  exact e.toMeasurableEquiv.measurableEmbedding
theorem stateEval_dilatedState {ha : 0 < a} (hemb : MeasurableEmbedding (fieldRescale ha))
    (μ : Measure (GaugeField a)) (f : GaugeField 1 → ℂ) :
    stateEval (dilatedState ha μ) f = stateEval μ (precompRescale ha f) :=
  hemb.integral_map f
theorem precompRescale_comp_symm {ha : 0 < a} (e : GaugeField a ≃ₜ GaugeField 1)
    (he : ⇑e = fieldRescale ha) (g : GaugeField a → ℂ) :
    precompRescale ha (g ∘ e.symm) = g := by
  funext A
  simp [precompRescale, ← he]
theorem map_symm_dilatedState {ha : 0 < a} (e : GaugeField a ≃ₜ GaugeField 1)
    (he : ⇑e = fieldRescale ha) (μ : Measure (GaugeField a)) :
    (dilatedState ha μ).map e.symm = μ := by
  rw [dilatedState_eq_map, ← he,
    Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
  have hcomp : ⇑e.symm ∘ ⇑e = id := funext fun A => e.symm_apply_apply A
  rw [hcomp, Measure.map_id]
theorem dilatedState_map_symm {ha : 0 < a} (e : GaugeField a ≃ₜ GaugeField 1)
    (he : ⇑e = fieldRescale ha) (μ' : Measure (GaugeField 1)) :
    dilatedState ha (μ'.map e.symm) = μ' := by
  rw [dilatedState_eq_map, ← he,
    Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
  have hcomp : ⇑e ∘ ⇑e.symm = id := funext fun A => e.apply_symm_apply A
  rw [hcomp, Measure.map_id]
theorem dilatedState_injective {ha : 0 < a} (e : GaugeField a ≃ₜ GaugeField 1)
    (he : ⇑e = fieldRescale ha) : Function.Injective (dilatedState ha) := fun μ₁ μ₂ h => by
  rw [← map_symm_dilatedState e he μ₁, h, map_symm_dilatedState e he μ₂]
theorem continuous_integral_weakTopology (g : C(GaugeField a, ℂ)) :
    Continuous[probabilityMeasuresWeakTopology a, inferInstance]
      fun μ : ProbabilityMeasure (GaugeField a) => ∫ A, g A ∂(μ : Measure (GaugeField a)) :=
  continuous_iInf_dom (i := g) continuous_induced_dom
def probabilityMeasureRescaleEquiv {ha : 0 < a} (e : GaugeField a ≃ₜ GaugeField 1)
    (he : ⇑e = fieldRescale ha) :
    ProbabilityMeasure (GaugeField a) ≃ ProbabilityMeasure (GaugeField 1) where
  toFun μ := ⟨dilatedState ha μ, inferInstance⟩
  invFun μ := ⟨(μ : Measure (GaugeField 1)).map e.symm,
    Measure.isProbabilityMeasure_map e.symm.continuous.measurable.aemeasurable⟩
  left_inv _ := Subtype.ext (map_symm_dilatedState e he _)
  right_inv _ := Subtype.ext (dilatedState_map_symm e he _)
theorem continuous_probabilityMeasureRescaleEquiv {ha : 0 < a}
    (e : GaugeField a ≃ₜ GaugeField 1) (he : ⇑e = fieldRescale ha) :
    Continuous[probabilityMeasuresWeakTopology a, probabilityMeasuresWeakTopology 1]
      (probabilityMeasureRescaleEquiv e he) := by
  refine continuous_iInf_rng.2 fun g => continuous_induced_rng.2 ?_
  have hemb := measurableEmbedding_fieldRescale_of_homeomorph e he
  have hfun : ((fun μ : ProbabilityMeasure (GaugeField 1) =>
        ∫ A, g A ∂(μ : Measure (GaugeField 1))) ∘ probabilityMeasureRescaleEquiv e he) =
      fun μ : ProbabilityMeasure (GaugeField a) =>
        ∫ A, (g.comp ⟨e, e.continuous⟩) A ∂(μ : Measure (GaugeField a)) := by
    funext μ
    change ∫ A, g A ∂(dilatedState ha (μ : Measure (GaugeField a))) = _
    rw [dilatedState_eq_map, hemb.integral_map]
    simp [he]
  rw [hfun]
  exact continuous_integral_weakTopology _
theorem continuous_probabilityMeasureRescaleEquiv_symm {ha : 0 < a}
    (e : GaugeField a ≃ₜ GaugeField 1) (he : ⇑e = fieldRescale ha) :
    Continuous[probabilityMeasuresWeakTopology 1, probabilityMeasuresWeakTopology a]
      (probabilityMeasureRescaleEquiv e he).symm := by
  refine continuous_iInf_rng.2 fun g => continuous_induced_rng.2 ?_
  have hemb : MeasurableEmbedding e.symm := e.symm.toMeasurableEquiv.measurableEmbedding
  have hfun : ((fun μ : ProbabilityMeasure (GaugeField a) =>
        ∫ A, g A ∂(μ : Measure (GaugeField a))) ∘ (probabilityMeasureRescaleEquiv e he).symm) =
      fun μ : ProbabilityMeasure (GaugeField 1) =>
        ∫ A, (g.comp ⟨e.symm, e.symm.continuous⟩) A ∂(μ : Measure (GaugeField 1)) := by
    funext μ
    change ∫ A, g A ∂((μ : Measure (GaugeField 1)).map e.symm) = _
    rw [hemb.integral_map]
    rfl
  rw [hfun]
  exact continuous_integral_weakTopology _
theorem isWeakClusterPoint_dilatedState_iff {ha : 0 < a} (e : GaugeField a ≃ₜ GaugeField 1)
    (he : ⇑e = fieldRescale ha) (μ : Measure (GaugeField a))
    (μs : ℕ → Measure (GaugeField a)) :
    IsWeakClusterPoint μs μ ↔
      IsWeakClusterPoint (fun n => dilatedState ha (μs n)) (dilatedState ha μ) := by
  have hemb := measurableEmbedding_fieldRescale_of_homeomorph e he
  constructor
  · intro h S hfin hcont δ hδ n₀ hn₀
    obtain ⟨n, hn, hf⟩ := h (precompRescale ha '' S) (hfin.image _)
      (by
        rintro _ ⟨f, hf, rfl⟩
        have : precompRescale ha f = f ∘ e := by rw [he]; rfl
        rw [this]
        exact (hcont f hf).comp e.continuous) δ hδ n₀ hn₀
    refine ⟨n, hn, fun f hfS => ?_⟩
    rw [stateEval_dilatedState hemb, stateEval_dilatedState hemb]
    exact hf _ (mem_image_of_mem _ hfS)
  · intro h S hfin hcont δ hδ n₀ hn₀
    obtain ⟨n, hn, hf⟩ := h ((fun g => g ∘ e.symm) '' S) (hfin.image _)
      (by
        rintro _ ⟨g, hg, rfl⟩
        exact (hcont g hg).comp e.symm.continuous) δ hδ n₀ hn₀
    refine ⟨n, hn, fun g hg => ?_⟩
    have := hf _ (mem_image_of_mem _ hg)
    rwa [stateEval_dilatedState hemb, stateEval_dilatedState hemb,
      precompRescale_comp_symm e he] at this
theorem latticeSymmetry_ext {σ τ : LatticeSymmetry a} (h : σ.toFun = τ.toFun) : σ = τ := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem euclidNormVec_smul_eq_abs_mul (c : ℝ) (v : AmbientSpace) :
    TorusMetric.euclidNormVec (c • v) = |c| * TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.UnitSpacing.euclidNormVec_smul <;> assumption
theorem inv_smul_mem_latticeSubgroup_one_iff (ha : 0 < a) {x : AmbientSpace} :
    a⁻¹ • x ∈ latticeSubgroup 1 ↔ x ∈ latticeSubgroup a := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, fun i => ?_⟩
    have := hm i
    simp only [Pi.smul_apply, smul_eq_mul, mul_one] at this
    rw [← this]
    field_simp
  · rintro ⟨m, hm⟩
    refine ⟨m, fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_one, hm i]
    field_simp
def symmetryAtSpacing (ha : 0 < a) (σ : LatticeSymmetry 1) : LatticeSymmetry a where
  toFun x := a • σ.toFun (a⁻¹ • x)
  preservesDist x y := by
    rw [← smul_sub, euclidNormVec_smul_eq_abs_mul, σ.preservesDist, ← smul_sub,
      euclidNormVec_smul_eq_abs_mul, abs_inv, abs_of_pos ha]
    field_simp
  image_eq := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : a⁻¹ • y ∈ latticeSubgroup 1 := (inv_smul_mem_latticeSubgroup_one_iff ha).2 hy
      have h2 : σ.toFun (a⁻¹ • y) ∈ latticeSubgroup 1 := by
        rw [SetLike.mem_coe.symm, ← σ.image_eq]
        exact mem_image_of_mem _ h1
      refine (inv_smul_mem_latticeSubgroup_one_iff ha).1 ?_
      rwa [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    · intro hx
      have h1 : a⁻¹ • x ∈ latticeSubgroup 1 := (inv_smul_mem_latticeSubgroup_one_iff ha).2 hx
      have h2 : a⁻¹ • x ∈ σ.toFun '' (latticeSubgroup 1 : Set AmbientSpace) := by
        rw [σ.image_eq]; exact h1
      obtain ⟨y, hy, hyx⟩ := h2
      refine ⟨a • y, ?_, ?_⟩
      · have : a⁻¹ • (a • y) ∈ latticeSubgroup 1 := by
          rwa [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
        exact (inv_smul_mem_latticeSubgroup_one_iff ha).1 this
      · change a • σ.toFun (a⁻¹ • (a • y)) = x
        rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul, hyx, smul_smul,
          mul_inv_cancel₀ ha.ne', one_smul]
theorem toFun_eq_conjugateByScaling_symmetryAtSpacing (ha : 0 < a) (σ : LatticeSymmetry 1) :
    σ.toFun = conjugateByScaling a (symmetryAtSpacing ha σ).toFun := by
  funext x
  change σ.toFun x = a⁻¹ • (a • σ.toFun (a⁻¹ • (a • x)))
  rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
theorem exists_nat_norm_eq_mul {x : AmbientSpace} (hx : x ∈ latticeSubgroup a) (ha : 0 < a) :
    ∃ k : ℕ, ‖x‖ = (k : ℝ) * a := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖) Finset.univ_nonempty
  have hnorm : ‖x‖ = ‖x i‖ :=
    le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => hi j (Finset.mem_univ _))
      (norm_le_pi_norm x i)
  refine ⟨(m i).natAbs, ?_⟩
  rw [hnorm, hm i, norm_mul, Real.norm_of_nonneg ha.le, Real.norm_eq_abs, Nat.cast_natAbs,
    Int.cast_abs]
theorem periodNorms_nonempty (L : PeriodSublattice a) : (periodNorms L).Nonempty := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsAtSpacing.nonzeroNorms_nonempty <;> assumption
theorem isLeast_periodNorms (ha : 0 < a) (L : PeriodSublattice a) :
    IsLeast (periodNorms L) L.minNonzeroNorm := by
  classical
  have hex : ∃ k : ℕ, (k : ℝ) * a ∈ periodNorms L := by
    obtain ⟨s, γ, hγ, h0, rfl⟩ := periodNorms_nonempty L
    obtain ⟨k, hk⟩ := exists_nat_norm_eq_mul γ.2 ha
    exact ⟨k, γ, hγ, h0, hk.symm⟩
  have hleast : IsLeast (periodNorms L) ((Nat.find hex : ℝ) * a) := by
    refine ⟨Nat.find_spec hex, ?_⟩
    rintro s ⟨γ, hγ, h0, rfl⟩
    obtain ⟨k, hk⟩ := exists_nat_norm_eq_mul γ.2 ha
    rw [hk]
    have : Nat.find hex ≤ k := Nat.find_min' hex ⟨γ, hγ, h0, hk.symm⟩
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) ha.le
  have heq : L.minNonzeroNorm = (Nat.find hex : ℝ) * a := hleast.csInf_eq
  rw [heq]
  exact hleast
theorem norm_pointRescale (ha : 0 < a) (γ : LatticePoint a) :
    ‖((pointRescale ha γ : LatticePoint 1) : AmbientSpace)‖ = a⁻¹ * ‖(γ : AmbientSpace)‖ := by
  rw [coe_pointRescale, scaleByInv, norm_smul, norm_inv, Real.norm_of_nonneg ha.le]
theorem pointRescale_ne_zero (ha : 0 < a) {γ : LatticePoint a} (h : γ ≠ 0) :
    pointRescale ha γ ≠ 0 := by
  intro h0
  refine h (Subtype.ext ?_)
  have h1 : scaleByInv a (γ : AmbientSpace) = 0 := by
    rw [← coe_pointRescale ha, h0]
    rfl
  rw [scaleByInv] at h1
  simpa [ha.ne'] using h1
theorem minNonzeroNorm_rescaled (ha : 0 < a) (L : PeriodSublattice a) (L' : PeriodSublattice 1)
    (hL : L'.periods = subgroupRescale ha L.periods) :
    L'.minNonzeroNorm = a⁻¹ * L.minNonzeroNorm := by
  have hm := isLeast_periodNorms ha L
  have hm' := isLeast_periodNorms one_pos L'
  have hs : IsLeast (periodNorms L') (a⁻¹ * L.minNonzeroNorm) := by
    constructor
    · obtain ⟨γ, hγ, h0, hm0⟩ := hm.1
      refine ⟨pointRescale ha γ, ?_, pointRescale_ne_zero ha h0, ?_⟩
      · rw [hL]
        exact AddSubgroup.mem_map_of_mem _ hγ
      · rw [norm_pointRescale, hm0]
    · rintro s ⟨γ', hγ', h0', rfl⟩
      rw [hL] at hγ'
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hγ'
      rw [norm_pointRescale]
      refine mul_le_mul_of_nonneg_left (hm.2 ⟨γ, hγ, ?_, rfl⟩) (inv_pos.2 ha).le
      rintro rfl
      exact h0' (map_zero _)
  exact hm'.unique hs
theorem rescaleLatticeAndFields_holds (hD : ScalingToUnitSpacing)
    (hC : InfiniteLattice.Dilation.DilatedStateProperties) (ha : 0 < a) :
    RescaleLatticeAndFields ha := by
  obtain ⟨⟨hpt, hlink, hpos, hface, hcb, hhomeo, hact⟩, -⟩ := hD a 1 ha one_pos
  have hV := (hC a a⁻¹ 1 ha (inv_pos.2 ha) (one_eq_inv_mul_spacing ha)).2.1.2
  exact ⟨hpt.2, hlink, hpos.image_eq, hface, fun p => (hcb p).2.symm, hhomeo,
    fieldRescale_rescaledLink ha, fun A p => (hV p A).1,
    fun p => funext fun A => hact p A⟩
theorem rescaleObservables_holds (hD : ScalingToUnitSpacing) (ha : 0 < a) :
    RescaleObservables ha := by
  obtain ⟨hL, ⟨hbij, hobs, hloc⟩, -⟩ := hD a 1 ha one_pos
  obtain ⟨e, he⟩ := hL.2.2.2.2.2.1
  refine ⟨hbij, fun f g _ _ => ⟨rfl, rfl⟩, fun z f _ => rfl, fun f _ => rfl, ?_, hobs, hloc⟩
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hpre : precompRescale ha f = f ∘ e := by rw [he]; rfl
    rw [hpre]
    exact Continuous.comp hf e.continuous
  · intro hg
    exact ⟨g ∘ e.symm, Continuous.comp hg e.symm.continuous, precompRescale_comp_symm e he g⟩
theorem rescaleSymmetries_holds (hD : ScalingToUnitSpacing) (ha : 0 < a) :
    RescaleSymmetries ha := by
  obtain ⟨-, -, hI, hK, -⟩ := hD a 1 ha one_pos
  exact ⟨hI, fun σ' => ⟨symmetryAtSpacing ha σ',
    toFun_eq_conjugateByScaling_symmetryAtSpacing ha σ'⟩, hK.1, hK.2.1⟩
theorem rescaleMirrors_holds (hD : ScalingToUnitSpacing) (ha : 0 < a) :
    RescaleMirrors ha := by
  obtain ⟨-, ⟨-, hobs, -⟩, hI, hK, ⟨-, hadm, hmir, -⟩, -⟩ := hD a 1 ha one_pos
  refine ⟨hadm, fun P P' hn hl => ?_⟩
  have hconj : conjugateByScaling a (reflectAcross P.normal P.level) =
      reflectAcross P'.normal P'.level := by
    rw [hn, hl]
    exact hK.2.2 P.normal P.normal_mem P.level
  obtain ⟨Q, -, -, -, -, -, -, -, hside⟩ := hmir P
  have hside' : ∀ ε : ℤˣ, scaleByInvImage a (closedHalfSpace P.normal P.level ε) =
      closedHalfSpace P'.normal P'.level ε := fun ε => by
    rw [hn, hl]
    exact hside ε
  refine ⟨hconj, fun ε => ⟨hside' ε, ?_⟩, fun f hf => ?_⟩
  · rw [halfSpaceObservables, ← hside' ε]
    exact hobs _
  · obtain ⟨σ', hσ', hact⟩ := hI P.reflectSymmetry
    have hσσ : σ' = P'.reflectSymmetry := latticeSymmetry_ext (hσ'.trans hconj)
    subst hσσ
    funext A
    change conj (P.reflectSymmetry.actOn (precompRescale ha f) A) =
      conj (P'.reflectSymmetry.actOn f (fieldRescale ha A))
    rw [hact f hf]
    rfl
theorem rescaleStates_holds (hD : ScalingToUnitSpacing) (ha : 0 < a) : RescaleStates ha := by
  obtain ⟨hL, -⟩ := hD a 1 ha one_pos
  obtain ⟨e, he⟩ := hL.2.2.2.2.2.1
  have hemb := measurableEmbedding_fieldRescale_of_homeomorph e he
  refine ⟨fun μ hμ => ⟨?_, fun f _ => stateEval_dilatedState hemb μ f⟩,
    ⟨fun μ hμ => ?_, (dilatedState_injective e he).injOn, fun μ' hμ' => ?_⟩, ?_,
    ⟨probabilityMeasureRescaleEquiv e he, fun μ => rfl,
      continuous_probabilityMeasureRescaleEquiv e he,
      continuous_probabilityMeasureRescaleEquiv_symm e he⟩,
    fun μ μs _ _ => isWeakClusterPoint_dilatedState_iff e he μ μs⟩
  · have : IsProbabilityMeasure μ := hμ
    exact (inferInstance : IsProbabilityMeasure (dilatedState ha μ))
  · have : IsProbabilityMeasure μ := hμ
    exact (inferInstance : IsProbabilityMeasure (dilatedState ha μ))
  · have : IsProbabilityMeasure μ' := hμ'
    exact ⟨μ'.map e.symm,
      Measure.isProbabilityMeasure_map e.symm.continuous.measurable.aemeasurable,
      dilatedState_map_symm e he μ'⟩
  · intro μ₁ μ₂ _ _ t _
    simp only [dilatedState_eq_map]
    rw [Measure.map_add _ _ (measurable_fieldRescale ha),
      Measure.map_smul, Measure.map_smul]
theorem rescaleInvarianceAndPositivity_holds (hD : ScalingToUnitSpacing) (ha : 0 < a) :
    RescaleInvarianceAndPositivity ha := by
  obtain ⟨hL, ⟨hbij, -, -⟩, hI, -⟩ := hD a 1 ha one_pos
  obtain ⟨e, he⟩ := hL.2.2.2.2.2.1
  have hemb := measurableEmbedding_fieldRescale_of_homeomorph e he
  intro μ _
  refine ⟨fun σ σ' hσ => ?_, fun P P' hn hl ε => ?_⟩
  · obtain ⟨τ, hτ, hact⟩ := hI σ
    have hττ : τ = σ' := latticeSymmetry_ext (hτ.trans hσ.symm)
    subst hττ
    have key : ∀ f : GaugeField 1 → ℂ, IsBoundedObservable f →
        ((∫ A, σ.actOn (precompRescale ha f) A ∂μ) = ∫ A, precompRescale ha f A ∂μ ↔
          (∫ A, τ.actOn f A ∂(dilatedState ha μ)) =
            ∫ A, f A ∂(dilatedState ha μ)) := fun f hf => by
      have h1 := stateEval_dilatedState hemb μ (τ.actOn f)
      have h2 := stateEval_dilatedState hemb μ f
      change (∫ A, τ.actOn f A ∂(dilatedState ha μ)) =
        ∫ A, precompRescale ha (τ.actOn f) A ∂μ at h1
      change (∫ A, f A ∂(dilatedState ha μ)) = ∫ A, precompRescale ha f A ∂μ at h2
      rw [h1, h2, hact f hf]
    constructor
    · intro h f hf
      exact (key f hf).1 (h _ (hbij.1 hf))
    · intro h g hg
      obtain ⟨f, hf, rfl⟩ := hbij.2.2 hg
      exact (key f hf).2 (h f hf)
  · obtain ⟨-, hside, hΘ⟩ := (rescaleMirrors_holds hD ha).2 P P' hn hl
    have hs := (hside ε).2
    have key : ∀ f ∈ halfSpaceObservables 1 P'.normal P'.level ε,
        stateEval μ (P.conjReflectObservable (precompRescale ha f) * precompRescale ha f) =
          stateEval (dilatedState ha μ) (P'.conjReflectObservable f * f) := fun f hf => by
      rw [stateEval_dilatedState hemb, hΘ f hf.1]
      rfl
    constructor
    · intro h f hf
      rw [← key f hf]
      exact h _ (hs ▸ mem_image_of_mem _ hf)
    · intro h g hg
      rw [← hs] at hg
      obtain ⟨f, hf, rfl⟩ := hg
      rw [key f hf]
      exact h f hf
theorem rescaleGibbsClasses_holds (hD : ScalingToUnitSpacing) (ha : 0 < a) {β : ℝ}
    (hβ : 0 < β) : RescaleGibbsClasses ha β := by
  obtain ⟨hL, -, -, -, -, -, ⟨hc1, hc2, hc3, hc4⟩, -⟩ := hD a β ha hβ
  obtain ⟨e, he⟩ := hL.2.2.2.2.2.1
  have hinj := dilatedState_injective e he
  intro μ _
  refine ⟨⟨hc1 μ, fun h => ?_⟩, fun Q => ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨μ'', hμ'', hmap, -⟩ := hc2 _ h
    rwa [← hinj hmap]
  · rw [← hc3 Q]
    exact mem_image_of_mem _ h
  · rw [← hc3 Q] at h
    obtain ⟨μ'', hμ'', hmap⟩ := h
    rwa [← hinj hmap]
  · rw [← hc4]
    exact mem_image_of_mem _ h
  · rw [← hc4] at h
    obtain ⟨μ'', hμ'', hmap⟩ := h
    rwa [← hinj hmap]
theorem rescalePeriodSublattices_holds (hD : ScalingToUnitSpacing)
    (hT : ToriArraysAndTiltedMeasuresFacts) (ha : 0 < a) {β : ℝ} (hβ : 0 < β) :
    RescalePeriodSublattices ha β := by
  obtain ⟨-, -, -, -, -, -, -, hP⟩ := hD a β ha hβ
  refine ⟨hP.1, fun L L' hL => ⟨?_, (hP.2 L L' hL).2, isLeast_periodNorms ha L,
    isLeast_periodNorms one_pos L', minNonzeroNorm_rescaled ha L L' hL⟩⟩
  exact ((hT β hβ).1 a ha L).2.2.isProbabilityMeasure_lifted
theorem transportToUnitSpacing_holds (h₁ : ScalingToUnitSpacing)
    (h₂ : InfiniteLattice.Dilation.DilatedStateProperties)
    (h₃ : ToriArraysAndTiltedMeasuresFacts) : TransportToUnitSpacing :=
  fun _ _ ha hβ => ⟨rescaleLatticeAndFields_holds h₁ h₂ ha, rescaleObservables_holds h₁ ha,
    rescaleSymmetries_holds h₁ ha, rescaleMirrors_holds h₁ ha, (h₁ _ _ ha hβ).2.2.2.2.2.1.1,
    rescaleStates_holds h₁ ha, rescaleInvarianceAndPositivity_holds h₁ ha,
    rescaleGibbsClasses_holds h₁ ha hβ, rescalePeriodSublattices_holds h₁ h₃ ha hβ⟩
end YangMills.Construction.UnitSpacing
