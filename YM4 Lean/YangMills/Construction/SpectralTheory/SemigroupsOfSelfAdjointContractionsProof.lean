import YangMills.Construction.SpectralTheory.JointMeasureOfASemigroupAndARepresentationProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.ContractionSemigroups
open BorelSpectral HilbertSpaceBasics SpectralTheorem SelfAdjointFunctions BorelCalculus
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable {T : ℝ≥0 → ℋ →L[ℂ] ℋ}
section Basics
theorem norm_semigroup_apply_le (hT : IsSelfAdjointContractionSemigroup T) (t : ℝ≥0) (ψ : ℋ) :
    ‖T t ψ‖ ≤ ‖ψ‖ := by
  have h : ‖T t‖ ≤ 1 := hT.contraction t
  calc ‖T t ψ‖ ≤ ‖T t‖ * ‖ψ‖ := (T t).le_opNorm ψ
    _ ≤ 1 * ‖ψ‖ := by gcongr
    _ = ‖ψ‖ := one_mul _
theorem semigroup_add_apply (hT : IsSelfAdjointContractionSemigroup T) (t s : ℝ≥0) (ψ : ℋ) :
    T (t + s) ψ = T t (T s ψ) := by
  rw [← hT.semigroup.2 t s]
  rfl
theorem norm_semigroup_add_sub_le (hT : IsSelfAdjointContractionSemigroup T) (t s : ℝ≥0)
    (ψ : ℋ) : ‖T (t + s) ψ - T t ψ‖ ≤ ‖T s ψ - ψ‖ := by
  rw [semigroup_add_apply hT, ← map_sub]
  exact norm_semigroup_apply_le hT t _
theorem tendsto_nhds_zero_apply (hT : IsSelfAdjointContractionSemigroup T) (ψ : ℋ) :
    Tendsto (fun s => T s ψ) (𝓝 0) (𝓝 ψ) := by
  have hc : ({0}ᶜ : Set ℝ≥0) = Ioi 0 := by
    ext s
    simp [pos_iff_ne_zero]
  rw [← pure_sup_nhdsNE (0 : ℝ≥0), hc]
  refine Tendsto.sup ?_ (hT.tendsto_zero ψ)
  have h0 : T 0 ψ = ψ := by rw [hT.semigroup.1]; rfl
  have := tendsto_pure_nhds (fun s => T s ψ) (0 : ℝ≥0)
  simpa only [h0] using this
theorem stronglyCont_of_semigroup (hT : IsSelfAdjointContractionSemigroup T) :
    IsStronglyCont T := by
  intro ψ
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ t, ‖T t ψ - T t₀ ψ‖ ≤ ‖T (nndist t t₀) ψ - ψ‖ := by
    intro t
    rcases le_total t₀ t with h | h
    · obtain ⟨s, rfl⟩ := exists_add_of_le h
      have e : nndist (t₀ + s) t₀ = s := by
        rw [NNReal.nndist_eq]
        simp only [add_tsub_cancel_left]
        simp
        exact h.trans le_add_self
      rw [e]
      exact norm_semigroup_add_sub_le hT t₀ s ψ
    · obtain ⟨s, rfl⟩ := exists_add_of_le h
      have e : nndist t (t + s) = s := by
        rw [NNReal.nndist_eq]
        simp only [add_tsub_cancel_left]
        simp
        exact h.trans le_add_self
      rw [e, norm_sub_rev]
      exact norm_semigroup_add_sub_le hT t s ψ
  have hd : Tendsto (fun t => nndist t t₀) (𝓝 t₀) (𝓝 0) := by
    have := ((continuous_id.nndist continuous_const :
      Continuous fun t : ℝ≥0 => nndist t t₀).tendsto t₀)
    simpa using this
  have hz : Tendsto (fun t => ‖T (nndist t t₀) ψ - ψ‖) (𝓝 t₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ((tendsto_nhds_zero_apply hT ψ).comp hd)
  exact squeeze_zero (fun _ => norm_nonneg _) hb hz
theorem isPositiveOp_semigroup (hpos : HilbertSpaceFacts.StarMulMulPositive)
    (hT : IsSelfAdjointContractionSemigroup T) (t : ℝ≥0) : IsPositiveOp (T t) := by
  have h := (hpos ℋ (T (t / 2))).2.1
  rw [(hT.selfAdjoint _).star_eq, hT.semigroup.2, add_halves] at h
  exact h
theorem isGE_one_semigroup (hnb : HilbertSpaceFacts.SelfAdjointNormBounds)
    (hT : IsSelfAdjointContractionSemigroup T) (t : ℝ≥0) : IsGE 1 (T t) := by
  have h := (hnb ℋ (T t) 1 (hT.selfAdjoint t) (hT.contraction t)).2
  simpa using h
theorem semigroup_ker_eq_bot (hT : IsSelfAdjointContractionSemigroup T) (t : ℝ≥0) :
    LinearMap.ker (T t : ℋ →ₗ[ℂ] ℋ) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro ψ hψ
  have hs : ∀ s : ℝ≥0, T s ψ = 0 → T (s / 2) ψ = 0 := by
    intro s h
    have hs' := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hT.selfAdjoint (s / 2))
    have e : ⟪T (s / 2) ψ, T (s / 2) ψ⟫_ℂ = 0 := by
      have := hs' ψ (T (s / 2) ψ)
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [this, ← semigroup_add_apply hT, add_halves, h, inner_zero_right]
    exact inner_self_eq_zero.mp e
  have hr : ∀ r : ℕ, T (t / 2 ^ r) ψ = 0 := by
    intro r
    induction r with
    | zero => simpa using hψ
    | succ r ih =>
      have := hs _ ih
      rwa [div_div, ← pow_succ] at this
  have hl : Tendsto (fun r : ℕ => t / 2 ^ r) atTop (𝓝 0) := by
    have h2 : Tendsto (fun r : ℕ => ((1 / 2 : ℝ≥0)) ^ r) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by simp) (by
        rw [← NNReal.coe_lt_coe]
        norm_num)
    have := h2.const_mul t
    simpa [div_eq_mul_inv, inv_pow] using this
  have hlim := (tendsto_nhds_zero_apply hT ψ).comp hl
  have h0 : (fun r : ℕ => T (t / 2 ^ r) ψ) = fun _ => 0 := funext hr
  have : Tendsto (fun _ : ℕ => (0 : ℋ)) atTop (𝓝 ψ) := by
    simpa [Function.comp_def, h0] using hlim
  exact (tendsto_nhds_unique this tendsto_const_nhds)
end Basics
section Calculus
variable {n : ℕ} {Y : Set (Fin n → ℝ)}
theorem boundedFnCalc_of (hC : BorelCalculusTheorem) (E : SpectralMeasure Y ℋ) :
    BoundedFunctionalCalculus E := ((hC ℋ n).1 Y E).1
theorem strongConvergence_of (hC : BorelCalculusTheorem) (E : SpectralMeasure Y ℋ) :
    StrongConvergence E := ((hC ℋ n).1 Y E).2.1
theorem commutesWithIntegralOps_of (hC : BorelCalculusTheorem) (E : SpectralMeasure Y ℋ) :
    CommutesWithIntegralOps E := ((hC ℋ n).1 Y E).2.2.1
theorem unboundedFnCalc_of (hC : BorelCalculusTheorem) (E : SpectralMeasure Y ℋ) :
    UnboundedFunctionalCalculus E := ((hC ℋ n).1 Y E).2.2.2.1
theorem kernelAndPositivity_of (hC : BorelCalculusTheorem) (E : SpectralMeasure Y ℋ) :
    KernelAndPositivity E := ((hC ℋ n).1 Y E).2.2.2.2.1
theorem integralOp_congr_on (hC : BorelCalculusTheorem) (E : SpectralMeasure Y ℋ)
    {g h : Y → ℂ} {c : ℝ} (hg : Measurable g) (hh : Measurable h) (hgc : ∀ y, ‖g y‖ ≤ c)
    (hhc : ∀ y, ‖h y‖ ≤ c) (Δ₀ : BorelSubsets Y) (hΔ : E.IsCarriedBy Δ₀)
    (he : ∀ y ∈ Δ₀.1, g y = h y) : E.integralOp g = E.integralOp h := by
  ext ψ
  have := ((unboundedFnCalc_of hC E).congr g h hg hh Δ₀ hΔ he).2 ψ
    (by rw [E.integralDom_eq_univ hgc]; trivial)
  rwa [E.integralApply_eq_integralOp hgc, E.integralApply_eq_integralOp hhc] at this
theorem integralOp_const_one (hC : BorelCalculusTheorem) (E : SpectralMeasure Y ℋ) :
    E.integralOp (fun _ => (1 : ℂ)) = 1 := by
  have h := (boundedFnCalc_of hC E).indicator ⟨univ, MeasurableSet.univ⟩
  have e : ((⟨univ, MeasurableSet.univ⟩ : BorelSubsets Y).1.indicator (1 : Y → ℂ)) =
      fun _ => 1 := by
    funext y
    simp
  rw [e] at h
  exact h.trans E.map_univ
theorem isSpectralIntegralOf_ofBounded (E : SpectralMeasure Y ℋ) {g : Y → ℂ} {c : ℝ}
    (hgc : ∀ y, ‖g y‖ ≤ c) : IsSpectralIntegralOf (ofBounded (E.integralOp g)) E g := by
  refine ⟨fun ψ => ?_, fun ψ => ?_⟩
  · rw [E.integralDom_eq_univ hgc]
    simp [ofBounded]
  · rw [E.integralApply_eq_integralOp hgc]
    rfl
theorem isSelfAdjointOp_ofBounded {A : ℋ →L[ℂ] ℋ} (hA : IsSelfAdjoint A) :
    IsSelfAdjointOp (ofBounded A) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  refine ⟨?_, fun φ => ?_, fun φ ψ => ?_⟩
  · simp [ofBounded]
  · exact ⟨fun _ => ⟨A φ, fun ψ => (hs φ ψ.1).symm⟩, fun _ => by simp [ofBounded]⟩
  · exact (hs φ.1 ψ.1).symm
theorem le_of_isGE {A B : ℋ →L[ℂ] ℋ} (h : IsGE A B) : B ≤ A := by apply _root_.YangMills.Construction.SemigroupRepresentation.le_of_isGE <;> assumption
end Calculus
structure Hypotheses (T : ℝ≥0 → ℋ →L[ℂ] ℋ) : Prop where
  borel : BorelCalculusTheorem
  spectral : SpectralTheoremHolds
  joint : JointSpectral.JointSpectralTheorem
  normBounds : HilbertSpaceFacts.SelfAdjointNormBounds
  starMulMul : HilbertSpaceFacts.StarMulMulPositive
  sqRoot : HilbertSpaceFacts.PositiveEqOfSqEq
  orthProj : HilbertSpaceFacts.OrthProjOntoClosed
  semigroup : IsSelfAdjointContractionSemigroup T
theorem measurable_coord_zero : Measurable fun y : RealLineSet => y.1 0 :=
  (measurable_pi_apply 0).comp measurable_subtype_coe
theorem spectralMeasure_isSpectralMeasureFor (hS : SpectralTheoremHolds)
    {A : UnboundedOp ℋ} (hA : IsSelfAdjointOp A) :
    IsSpectralMeasureFor (spectralMeasure A) A := (hS ℋ A hA).2.2.2.2.2.1
theorem spectralMeasure_eq_pushforward (hS : SpectralTheoremHolds)
    {A : UnboundedOp ℋ} (hA : IsSelfAdjointOp A) {n : ℕ} {Y : Set (Fin n → ℝ)}
    (E : SpectralMeasure Y ℋ) (g : Y → ℝ) (hg : Measurable g)
    (h : IsSpectralIntegralOf A E fun y => ((g y : ℝ) : ℂ)) :
    spectralMeasure A = pushforwardToLine E g hg ∧
      ∀ f : ℝ → ℂ, Measurable f →
        IntegralsAgree (spectralMeasure A) (fun y => f (y.1 0)) E (fun y => f (g y)) :=
  (hS ℋ A hA).2.2.2.2.2.2.1 n Y E g hg h
theorem isNonnegOp_iff (hS : SpectralTheoremHolds) {A : UnboundedOp ℋ}
    (hA : IsSelfAdjointOp A) :
    IsNonnegOp A ↔ spectralMeasure A (realLineSet negHalfLine) = 0 :=
  (hS ℋ A hA).2.2.2.2.2.2.2.1
abbrev timeOneMeasure (T : ℝ≥0 → ℋ →L[ℂ] ℋ) : SpectralMeasure RealLineSet ℋ :=
  spectralMeasure (ofBounded (T 1))
theorem isSelfAdjointOp_timeOne (c : Hypotheses T) : IsSelfAdjointOp (ofBounded (T 1)) :=
  isSelfAdjointOp_ofBounded (c.semigroup.selfAdjoint 1)
theorem timeOneMeasure_spec (c : Hypotheses T) :
    timeOneMeasure T = JointSpectral.jointMeasureOnSpace le_rfl (fun _ : Fin 1 => T 1) ∧
      (timeOneMeasure T).IsCarriedBy (realLineSet ⟨Icc 0 1, measurableSet_Icc⟩) := by
  refine (c.spectral ℋ _ (isSelfAdjointOp_timeOne c)).2.2.2.2.2.2.2.2 (T 1) 0 1 rfl
    zero_lt_one ?_ ?_
  · have e : (((0 : ℝ) : ℂ) • (1 : ℋ →L[ℂ] ℋ)) = 0 := by simp
    rw [e]
    refine ⟨c.semigroup.selfAdjoint 1, IsSelfAdjoint.zero _, ?_⟩
    rw [sub_zero]
    exact isPositiveOp_semigroup c.starMulMul c.semigroup 1
  · have e : (((1 : ℝ) : ℂ) • (1 : ℋ →L[ℂ] ℋ)) = 1 := by simp
    rw [e]
    exact isGE_one_semigroup c.normBounds c.semigroup 1
theorem commute_timeOneMeasure (c : Hypotheses T) {B : ℋ →L[ℂ] ℋ} (hB : Commute B (T 1))
    (Δ : BorelSubsets RealLineSet) : Commute B (timeOneMeasure T Δ) := by
  have hn : ‖T 1‖ ≤ ‖T 1‖ + 1 := by linarith
  have hb := c.normBounds ℋ (T 1) (‖T 1‖ + 1) (c.semigroup.selfAdjoint 1) hn
  have hbox : JointSpectral.IsCommutingInBox (fun _ : Fin 1 => T 1)
      (JointSpectral.normBoundLower fun _ => T 1)
      (JointSpectral.normBoundUpper fun _ => T 1) :=
    { selfAdjoint := fun _ => c.semigroup.selfAdjoint 1
      commute := fun _ _ => Commute.refl _
      lt := JointSpectral.normBoundLower_lt_normBoundUpper _
      lower_le := fun _ => le_of_isGE hb.1
      le_upper := fun _ => le_of_isGE hb.2 }
  have hh := (c.joint ℋ 1 le_rfl).1 _ _ _ hbox
  rw [(timeOneMeasure_spec c).1]
  exact hh.2.2.2 _ hh.2.1 B (fun _ => hB) _
def rpowIcc (t : ℝ) : ℝ → ℂ := (Icc (0 : ℝ) 1).indicator fun x => ((x ^ t : ℝ) : ℂ)
theorem measurable_rpowIcc (t : ℝ) : Measurable (rpowIcc t) :=
  (Complex.measurable_ofReal.comp (measurable_id.pow_const t)).indicator measurableSet_Icc
theorem norm_rpowIcc_le {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : ‖rpowIcc t x‖ ≤ 1 := by
  unfold rpowIcc
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx.1 t)]
    exact Real.rpow_le_one hx.1 hx.2 ht
  · rw [indicator_of_notMem hx]
    simp
theorem rpowIcc_mul_rpowIcc {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : ℝ) :
    rpowIcc s x * rpowIcc t x = rpowIcc (s + t) x := by
  unfold rpowIcc
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx,
      Real.rpow_add_of_nonneg hx.1 hs ht]
    push_cast
    rfl
  · simp [indicator_of_notMem hx]
def rpowCoord (t : ℝ) (y : RealLineSet) : ℂ := rpowIcc t (y.1 0)
theorem measurable_rpowCoord (t : ℝ) : Measurable (rpowCoord t) :=
  (measurable_rpowIcc t).comp measurable_coord_zero
theorem norm_rpowCoord_le {t : ℝ} (ht : 0 ≤ t) (y : RealLineSet) : ‖rpowCoord t y‖ ≤ 1 :=
  norm_rpowIcc_le ht _
theorem isBoundedFn_rpowCoord {t : ℝ} (ht : 0 ≤ t) : IsBoundedFn (rpowCoord t) :=
  ⟨1, norm_rpowCoord_le ht⟩
theorem timeOne_eq_integralOp (c : Hypotheses T) :
    T 1 = (timeOneMeasure T).integralOp (rpowCoord 1) := by
  ext ψ
  have hI := spectralMeasure_isSpectralMeasureFor c.spectral (isSelfAdjointOp_timeOne c)
  have hmem : ψ ∈ (ofBounded (T 1)).domain := by simp [ofBounded]
  have hd := (hI.1 ψ).mp hmem
  have hv := hI.2 ⟨ψ, hmem⟩
  have hlin : Measurable coordVar :=
    Complex.measurable_ofReal.comp measurable_coord_zero
  have hcg := (unboundedFnCalc_of c.borel (timeOneMeasure T)).congr coordVar (rpowCoord 1) hlin
    (measurable_rpowCoord 1) _ (timeOneMeasure_spec c).2 (fun y hy => by
      have hy' : y.1 0 ∈ Icc (0 : ℝ) 1 := hy
      simp [rpowCoord, rpowIcc, coordVar, indicator_of_mem hy'])
  have e := hcg.2 ψ hd
  rw [(timeOneMeasure T).integralApply_eq_integralOp (norm_rpowCoord_le zero_le_one)] at e
  exact hv.trans e
def unitIoc : BorelSubsets RealLineSet :=
  ⟨{y | y.1 0 ∈ Ioc (0 : ℝ) 1}, measurable_coord_zero measurableSet_Ioc⟩
theorem rpowCoord_one_eq_zero_iff (y : RealLineSet) :
    rpowCoord 1 y = 0 ↔ y.1 0 ∉ Ioc (0 : ℝ) 1 := by
  unfold rpowCoord rpowIcc
  by_cases hx : y.1 0 ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hx]
    simp only [Real.rpow_one, Complex.ofReal_eq_zero, mem_Ioc, not_and, not_le]
    constructor
    · intro h h'
      exact absurd h h'.ne'
    · intro h
      by_contra h0
      exact absurd hx.2 (not_le.mpr (h (lt_of_le_of_ne hx.1 (Ne.symm h0))))
  · rw [indicator_of_notMem hx]
    simp only [true_iff]
    exact fun h => hx ⟨h.1.le, h.2⟩
theorem timeOneMeasure_carried (c : Hypotheses T) : (timeOneMeasure T).IsCarriedBy unitIoc := by
  have hm := measurable_rpowCoord 1
  have hk := (kernelAndPositivity_of c.borel (timeOneMeasure T)).kernel_eq (rpowCoord 1) hm
  have hz : timeOneMeasure T (zeroLocus hm) = 0 := by
    ext ψ
    have hmem : timeOneMeasure T (zeroLocus hm) ψ ∈
        {ψ | ψ ∈ (timeOneMeasure T).integralDom (rpowCoord 1) ∧
          (timeOneMeasure T).integralApply (rpowCoord 1) ψ = 0} := by
      rw [hk]
      exact ⟨ψ, rfl⟩
    have hv := hmem.2
    rw [(timeOneMeasure T).integralApply_eq_integralOp (norm_rpowCoord_le zero_le_one),
      ← timeOne_eq_integralOp c] at hv
    have hb := semigroup_ker_eq_bot c.semigroup 1
    rw [LinearMap.ker_eq_bot'] at hb
    simpa using hb _ hv
  have e : (⟨unitIoc.1ᶜ, unitIoc.2.compl⟩ : BorelSubsets RealLineSet) = zeroLocus hm := by
    refine Subtype.ext ?_
    ext y
    simp only [zeroLocus, mem_preimage, mem_singleton_iff, rpowCoord_one_eq_zero_iff]
    rfl
  unfold SpectralMeasure.IsCarriedBy
  rw [e]
  exact hz
def rpowSemigroup (T : ℝ≥0 → ℋ →L[ℂ] ℋ) (t : ℝ≥0) : ℋ →L[ℂ] ℋ :=
  (timeOneMeasure T).integralOp (rpowCoord t)
theorem rpowSemigroup_mul (c : Hypotheses T) (s t : ℝ≥0) :
    rpowSemigroup T s * rpowSemigroup T t = rpowSemigroup T (s + t) := by
  unfold rpowSemigroup
  rw [← (boundedFnCalc_of c.borel (timeOneMeasure T)).mul _ _ (measurable_rpowCoord s)
    (isBoundedFn_rpowCoord s.2) (measurable_rpowCoord t) (isBoundedFn_rpowCoord t.2)]
  congr 1
  funext y
  simpa [rpowCoord] using rpowIcc_mul_rpowIcc s.2 t.2 (y.1 0)
theorem rpowSemigroup_one (c : Hypotheses T) : rpowSemigroup T 1 = T 1 := by
  simpa [rpowSemigroup] using (timeOne_eq_integralOp c).symm
theorem rpowSemigroup_zero (c : Hypotheses T) : rpowSemigroup T 0 = 1 := by
  rw [← integralOp_const_one c.borel (timeOneMeasure T)]
  refine integralOp_congr_on c.borel _ (c := 1) (measurable_rpowCoord _) measurable_const
    (fun y => norm_rpowIcc_le (by simp) _) (by simp) unitIoc (timeOneMeasure_carried c)
    fun y hy => ?_
  have hy' : y.1 0 ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
  simp [rpowCoord, rpowIcc, indicator_of_mem hy']
theorem isPositiveOp_rpowSemigroup (c : Hypotheses T) (t : ℝ≥0) :
    IsPositiveOp (rpowSemigroup T t) := by
  refine (boundedFnCalc_of c.borel (timeOneMeasure T)).isPositive _ (measurable_rpowCoord t)
    (isBoundedFn_rpowCoord t.2) fun y => ?_
  unfold rpowCoord rpowIcc
  by_cases hx : y.1 0 ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hx]
    exact_mod_cast Real.rpow_nonneg hx.1 _
  · rw [indicator_of_notMem hx]
theorem continuous_rpowSemigroup_apply (c : Hypotheses T) (ψ : ℋ) :
    Continuous fun t => rpowSemigroup T t ψ := by
  rw [continuous_iff_seqContinuous]
  intro u t hu
  have h := strongConvergence_of c.borel (timeOneMeasure T) (fun r => rpowCoord (u r))
    (rpowCoord t) 1 unitIoc (fun r => measurable_rpowCoord _) (measurable_rpowCoord _)
    (fun r y => norm_rpowIcc_le (u r).2 _) (timeOneMeasure_carried c) (fun y hy => ?_)
  · have h' := h.2 ψ
    rw [(timeOneMeasure T).integralApply_eq_integralOp
      (norm_rpowCoord_le (NNReal.coe_nonneg t))] at h'
    exact h'
  · have hy' : y.1 0 ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    simp only [rpowCoord, rpowIcc, indicator_of_mem hy']
    have hu' : Tendsto (fun r => ((u r : ℝ≥0) : ℝ)) atTop (𝓝 (t : ℝ)) :=
      NNReal.tendsto_coe.mpr hu
    have h₁ := ((Real.continuousAt_const_rpow (a := y.1 0) (b := (t : ℝ))
      (ne_of_gt hy.1)).tendsto).comp hu'
    exact (Complex.continuous_ofReal.tendsto _).comp h₁
theorem commute_semigroup (c : Hypotheses T) (s t : ℝ≥0) : Commute (T s) (T t) := by
  show T s * T t = T t * T s
  rw [c.semigroup.semigroup.2, c.semigroup.semigroup.2, add_comm]
theorem commute_semigroup_rpowSemigroup (c : Hypotheses T) (s t : ℝ≥0) :
    Commute (T s) (rpowSemigroup T t) :=
  commutesWithIntegralOps_of c.borel (timeOneMeasure T) (T s)
    (fun Δ => commute_timeOneMeasure c (commute_semigroup c s 1) Δ) _ (measurable_rpowCoord t)
    (isBoundedFn_rpowCoord t.2)
theorem semigroup_eq_rpowSemigroup_dyadic (c : Hypotheses T) (r : ℕ) :
    T (1 / 2 ^ r) = rpowSemigroup T (1 / 2 ^ r) := by
  induction r with
  | zero => simpa using (rpowSemigroup_one c).symm
  | succ r ih =>
    have hu : (1 / 2 ^ (r + 1) : ℝ≥0) + 1 / 2 ^ (r + 1) = 1 / 2 ^ r := by
      field_simp
      ring
    refine c.sqRoot ℋ _ _ (isPositiveOp_semigroup c.starMulMul c.semigroup _)
      (isPositiveOp_rpowSemigroup c _) (commute_semigroup_rpowSemigroup c _ _) ?_
    rw [pow_two, pow_two, c.semigroup.semigroup.2, rpowSemigroup_mul c, hu, ih]
theorem semigroup_eq_rpowSemigroup_nat_mul (c : Hypotheses T) (r k : ℕ) :
    T (k * (1 / 2 ^ r)) = rpowSemigroup T (k * (1 / 2 ^ r)) := by
  induction k with
  | zero => simpa [rpowSemigroup_zero c] using c.semigroup.semigroup.1
  | succ k ih =>
    have e : ((k + 1 : ℕ) : ℝ≥0) * (1 / 2 ^ r) = k * (1 / 2 ^ r) + 1 / 2 ^ r := by
      push_cast
      ring
    rw [e, ← c.semigroup.semigroup.2, ← rpowSemigroup_mul c, ih,
      semigroup_eq_rpowSemigroup_dyadic c]
theorem semigroup_eq_rpowSemigroup (c : Hypotheses T) (t : ℝ≥0) :
    T t = rpowSemigroup T t := by
  ext ψ
  let a : ℕ → ℝ≥0 := fun r => (⌊(t : ℝ) * 2 ^ r⌋₊ : ℝ≥0) * (1 / 2 ^ r)
  have ha : Tendsto a atTop (𝓝 t) := by
    rw [← NNReal.tendsto_coe]
    have h₁ := tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := (t : ℝ)) t.2
    have h₂ : Tendsto (fun r : ℕ => (2 : ℝ) ^ r) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    refine (h₁.comp h₂).congr fun r => ?_
    simp [a, div_eq_mul_inv]
  have h₁ := ((stronglyCont_of_semigroup c.semigroup ψ).tendsto t).comp ha
  have h₂ := ((continuous_rpowSemigroup_apply c ψ).tendsto t).comp ha
  have e : (fun t => T t ψ) ∘ a = (fun t => rpowSemigroup T t ψ) ∘ a := by
    funext r
    simp only [Function.comp, a]
    rw [semigroup_eq_rpowSemigroup_nat_mul c]
  rw [e] at h₁
  exact tendsto_nhds_unique h₁ h₂
theorem integralOp_eq_of_integralsAgree {n n' : ℕ} {Y : Set (Fin n → ℝ)}
    {Y' : Set (Fin n' → ℝ)} {E : SpectralMeasure Y ℋ} {E' : SpectralMeasure Y' ℋ}
    {f : Y → ℂ} {f' : Y' → ℂ} {b b' : ℝ}
    (h : IntegralsAgree E f E' f') (hf : ∀ y, ‖f y‖ ≤ b) (hf' : ∀ y, ‖f' y‖ ≤ b') :
    E.integralOp f = E'.integralOp f' := by
  ext ψ
  have e := h.2 ψ (by rw [E.integralDom_eq_univ hf]; trivial)
  rwa [E.integralApply_eq_integralOp hf, E'.integralApply_eq_integralOp hf'] at e
theorem op_eq_of_integralsAgree {n n' : ℕ} {Y : Set (Fin n → ℝ)}
    {Y' : Set (Fin n' → ℝ)} {E : SpectralMeasure Y ℋ} {E' : SpectralMeasure Y' ℋ}
    {f : Y → ℂ} {f' : Y' → ℂ} {A B : UnboundedOp ℋ}
    (hA : IsSpectralIntegralOf A E f) (hB : IsSpectralIntegralOf B E' f')
    (h : IntegralsAgree E f E' f') : A = B := by
  refine LinearPMap.ext ?_ fun ψ hψ hψ' => ?_
  · ext ψ
    rw [hA.1, hB.1, h.1]
  · have e₁ := hA.2 ⟨ψ, hψ⟩
    have e₂ := hB.2 ⟨ψ, hψ'⟩
    rw [e₁, e₂]
    exact h.2 ψ ((hA.1 ψ).mp hψ)
theorem isSpectralIntegralOf_spectralIntegralOp (hC : BorelCalculusTheorem) {n : ℕ}
    {Y : Set (Fin n → ℝ)} (E : SpectralMeasure Y ℋ) {g : Y → ℂ} (hg : Measurable g) :
    IsSpectralIntegralOf (spectralIntegralOp E g) E g := by
  obtain ⟨A, -, h₁, h₂⟩ := (unboundedFnCalc_of hC E).exists_op g hg
  have h : ∃ A, IsSpectralIntegralOf A E g :=
    ⟨A, fun ψ => by rw [← SetLike.mem_coe, h₁], h₂⟩
  exact Classical.epsilon_spec h
theorem semigroup_eq_integralOp_rpow (c : Hypotheses T) {n : ℕ} {Y : Set (Fin n → ℝ)}
    (F : SpectralMeasure Y ℋ) (x : Y → ℝ) (hx : Measurable x)
    (hxI : ∀ y, x y ∈ Icc (0 : ℝ) 1) (h₁ : T 1 = F.integralOp fun y => ((x y : ℝ) : ℂ)) :
    F ⟨x ⁻¹' {0}, hx (measurableSet_singleton 0)⟩ = 0 ∧
      ∀ t : ℝ≥0, T t = F.integralOp fun y => ((x y ^ (t : ℝ) : ℝ) : ℂ) := by
  have hxm : Measurable fun y => ((x y : ℝ) : ℂ) := Complex.measurable_ofReal.comp hx
  have hxb : ∀ y, ‖((x y : ℝ) : ℂ)‖ ≤ 1 := by
    intro y
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hxI y).1]
    exact (hxI y).2
  constructor
  · have hk := (kernelAndPositivity_of c.borel F).kernel_eq _ hxm
    have hz : F (zeroLocus hxm) = 0 := by
      ext ψ
      have hmem : F (zeroLocus hxm) ψ ∈
          {ψ | ψ ∈ F.integralDom (fun y => ((x y : ℝ) : ℂ)) ∧
            F.integralApply (fun y => ((x y : ℝ) : ℂ)) ψ = 0} := by
        rw [hk]
        exact ⟨ψ, rfl⟩
      have hv := hmem.2
      rw [F.integralApply_eq_integralOp hxb, ← h₁] at hv
      have hb := semigroup_ker_eq_bot c.semigroup 1
      rw [LinearMap.ker_eq_bot'] at hb
      simpa using hb _ hv
    have e : (⟨x ⁻¹' {0}, hx (measurableSet_singleton 0)⟩ : BorelSubsets Y) = zeroLocus hxm :=
      Subtype.ext (by ext y; simp [zeroLocus])
    rw [e]
    exact hz
  · intro t
    have hI : IsSpectralIntegralOf (ofBounded (T 1)) F fun y => ((x y : ℝ) : ℂ) := by
      rw [h₁]
      exact isSpectralIntegralOf_ofBounded F hxb
    have hs : IntegralsAgree (timeOneMeasure T) (rpowCoord t) F (fun y => rpowIcc t (x y)) :=
      (spectralMeasure_eq_pushforward c.spectral (isSelfAdjointOp_timeOne c) F x hx hI).2
        (rpowIcc t) (measurable_rpowIcc t)
    have hfun : (fun y => rpowIcc t (x y)) = fun y => ((x y ^ (t : ℝ) : ℝ) : ℂ) := by
      funext y
      simp [rpowIcc, indicator_of_mem (hxI y)]
    rw [semigroup_eq_rpowSemigroup c t, ← hfun]
    exact integralOp_eq_of_integralsAgree hs (norm_rpowCoord_le (NNReal.coe_nonneg t))
      (fun y => norm_rpowIcc_le (NNReal.coe_nonneg t) _)
theorem semigroup_eq_rpowOp (c : Hypotheses T) (t : ℝ≥0) : T t = rpowOp (T 1) t := by
  by_cases h : t = 0
  · subst h
    simp [rpowOp, c.semigroup.semigroup.1]
  · rw [semigroup_eq_rpowSemigroup c t]
    unfold rpowOp
    rw [if_neg (by exact_mod_cast h)]
    rfl
def negLogIocFn : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator fun x => ((-Real.log x : ℝ) : ℂ)
theorem measurable_negLogIocFn : Measurable negLogIocFn :=
  (Complex.measurable_ofReal.comp Real.measurable_log.neg).indicator measurableSet_Ioc
theorem negLogIocFn_coord (y : RealLineSet) :
    negLogIocFn (y.1 0) = ((negLogIoc y : ℝ) : ℂ) := by
  unfold negLogIocFn negLogIoc
  by_cases hy : y.1 0 ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hy, indicator_of_mem hy]
  · rw [indicator_of_notMem hy, indicator_of_notMem hy]
    simp
theorem negLogIoc_nonneg (y : RealLineSet) : 0 ≤ negLogIoc y := by
  unfold negLogIoc
  by_cases hy : y.1 0 ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hy]
    exact neg_nonneg.mpr (Real.log_nonpos hy.1.le hy.2)
  · rw [indicator_of_notMem hy]
theorem measurable_negLogIoc_ofReal :
    Measurable fun y : RealLineSet => ((negLogIoc y : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp measurable_negLogIoc
theorem semigroupGenerator_isSpectralIntegralOf (c : Hypotheses T) :
    IsSpectralIntegralOf (semigroupGenerator T) (timeOneMeasure T)
      fun y => ((negLogIoc y : ℝ) : ℂ) := by
  have e : semigroupGenerator T = spectralIntegralOp (timeOneMeasure T)
      fun y => ((negLogIoc y : ℝ) : ℂ) := by
    unfold semigroupGenerator negLogOp fnCalc
    congr 1
    funext y
    exact negLogIocFn_coord y
  rw [e]
  exact isSpectralIntegralOf_spectralIntegralOp c.borel _ measurable_negLogIoc_ofReal
theorem semigroupGenerator_isSelfAdjointOp (c : Hypotheses T) :
    IsSelfAdjointOp (semigroupGenerator T) := by
  have h := semigroupGenerator_isSpectralIntegralOf c
  exact (unboundedFnCalc_of c.borel (timeOneMeasure T)).isSelfAdjoint _
    measurable_negLogIoc_ofReal (fun y => by simp) _ ⟨Set.ext h.1, h.2⟩
theorem spectralMeasure_semigroupGenerator (c : Hypotheses T) :
    spectralMeasure (semigroupGenerator T) =
      pushforwardToLine (timeOneMeasure T) negLogIoc measurable_negLogIoc :=
  (spectralMeasure_eq_pushforward c.spectral (semigroupGenerator_isSelfAdjointOp c) _ _
    measurable_negLogIoc (semigroupGenerator_isSpectralIntegralOf c)).1
theorem semigroupGenerator_integralsAgree (c : Hypotheses T) (f : ℝ → ℂ) (hf : Measurable f) :
    IntegralsAgree (spectralMeasure (semigroupGenerator T)) (fun y => f (y.1 0))
      (timeOneMeasure T) fun y => f (negLogIoc y) :=
  (spectralMeasure_eq_pushforward c.spectral (semigroupGenerator_isSelfAdjointOp c) _ _
    measurable_negLogIoc (semigroupGenerator_isSpectralIntegralOf c)).2 f hf
theorem semigroupGenerator_isNonnegOp (c : Hypotheses T) :
    IsNonnegOp (semigroupGenerator T) := by
  rw [isNonnegOp_iff c.spectral (semigroupGenerator_isSelfAdjointOp c),
    spectralMeasure_semigroupGenerator c]
  refine (congrArg (timeOneMeasure T).toFun (Subtype.ext ?_)).trans
    (timeOneMeasure T).apply_empty
  refine eq_empty_of_forall_notMem fun y hy => ?_
  exact absurd (negLogIoc_nonneg y) (not_le.mpr hy)
def expNegIci (t : ℝ≥0) : ℝ → ℂ :=
  (Ici (0 : ℝ)).indicator fun x => Complex.exp ((-(t : ℝ) * x : ℝ) : ℂ)
def expNegCoord (t : ℝ≥0) (y : RealLineSet) : ℂ := expNegIci t (y.1 0)
theorem measurable_expNegIci (t : ℝ≥0) : Measurable (expNegIci t) := by
  refine Measurable.indicator ?_ measurableSet_Ici
  exact Complex.measurable_exp.comp
    (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id))
theorem measurable_expNegCoord (t : ℝ≥0) : Measurable (expNegCoord t) :=
  (measurable_expNegIci t).comp measurable_coord_zero
theorem norm_expNegIci_le (t : ℝ≥0) (x : ℝ) : ‖expNegIci t x‖ ≤ 1 := by
  unfold expNegIci
  by_cases hx : x ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem hx, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_one_iff.mpr ?_
    have : 0 ≤ (t : ℝ) * x := mul_nonneg t.2 hx
    linarith
  · rw [indicator_of_notMem hx]
    simp
theorem norm_expNegCoord_le (t : ℝ≥0) (y : RealLineSet) : ‖expNegCoord t y‖ ≤ 1 :=
  norm_expNegIci_le t _
theorem semigroup_eq_expNeg (c : Hypotheses T) (t : ℝ≥0) :
    T t = expNeg (semigroupGenerator T) t := by
  have hs : IntegralsAgree (spectralMeasure (semigroupGenerator T)) (expNegCoord t)
      (timeOneMeasure T) fun y => expNegIci t (negLogIoc y) :=
    semigroupGenerator_integralsAgree c _ (measurable_expNegIci t)
  have hb : ∀ y, ‖expNegIci t (negLogIoc y)‖ ≤ 1 :=
    fun y => norm_expNegIci_le t _
  have e := integralOp_eq_of_integralsAgree hs (norm_expNegCoord_le t) hb
  have e' : expNeg (semigroupGenerator T) t =
      (spectralMeasure (semigroupGenerator T)).integralOp (expNegCoord t) := rfl
  rw [e', e, semigroup_eq_rpowSemigroup c t]
  refine integralOp_congr_on c.borel _ (measurable_rpowCoord t)
    ((measurable_expNegIci t).comp measurable_negLogIoc)
    (norm_rpowCoord_le (NNReal.coe_nonneg t)) hb unitIoc (timeOneMeasure_carried c)
    fun y hy => ?_
  have hy' : y.1 0 ∈ Ioc (0 : ℝ) 1 := hy
  have hI : y.1 0 ∈ Icc (0 : ℝ) 1 := ⟨hy'.1.le, hy'.2⟩
  have hn := negLogIoc_nonneg y
  have hv : negLogIoc y = -Real.log (y.1 0) := by
    unfold negLogIoc
    rw [indicator_of_mem hy']
  simp only [rpowCoord, rpowIcc, expNegIci, indicator_of_mem hI,
    indicator_of_mem (show negLogIoc y ∈ Ici (0 : ℝ) from hn)]
  rw [Real.rpow_def_of_pos hy'.1, hv, Complex.ofReal_exp]
  congr 2
  ring
def nonnegHalfLine : BorelSubsets RealLineSet := realLineSet ⟨Ici 0, measurableSet_Ici⟩
theorem spectralMeasure_carried_nonnegHalfLine (hS : SpectralTheoremHolds)
    {A : UnboundedOp ℋ} (hA : IsNonnegOp A) :
    (spectralMeasure A).IsCarriedBy nonnegHalfLine := by
  have h := (isNonnegOp_iff hS hA.1).mp hA
  have e : (⟨nonnegHalfLine.1ᶜ, nonnegHalfLine.2.compl⟩ : BorelSubsets RealLineSet) =
      realLineSet negHalfLine := by
    refine Subtype.ext ?_
    ext y
    simp [nonnegHalfLine, realLineSet, negHalfLine]
  unfold SpectralMeasure.IsCarriedBy
  rw [e]
  exact h
def expNegIciReal (y : RealLineSet) : ℝ :=
  (Ici (0 : ℝ)).indicator (fun x => Real.exp (-x)) (y.1 0)
theorem measurable_expNegIciReal : Measurable expNegIciReal :=
  ((Real.measurable_exp.comp measurable_neg).indicator measurableSet_Ici).comp
    measurable_coord_zero
theorem expNegCoord_one (y : RealLineSet) :
    expNegCoord 1 y = ((expNegIciReal y : ℝ) : ℂ) := by
  unfold expNegCoord expNegIci expNegIciReal
  by_cases hy : y.1 0 ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem hy, indicator_of_mem hy, Complex.ofReal_exp]
    simp
  · rw [indicator_of_notMem hy, indicator_of_notMem hy]
    simp
theorem eq_semigroupGenerator (c : Hypotheses T) (A : UnboundedOp ℋ) (hA : IsNonnegOp A)
    (h₁ : expNeg A 1 = T 1) : A = semigroupGenerator T := by
  have hfun : expNegCoord 1 = fun y => ((expNegIciReal y : ℝ) : ℂ) :=
    funext expNegCoord_one
  have hb : ∀ y, ‖((expNegIciReal y : ℝ) : ℂ)‖ ≤ 1 := by
    intro y
    rw [← expNegCoord_one]
    exact norm_expNegCoord_le 1 y
  have hI : IsSpectralIntegralOf (ofBounded (T 1)) (spectralMeasure A)
      fun y => ((expNegIciReal y : ℝ) : ℂ) := by
    have e : T 1 = (spectralMeasure A).integralOp
        fun y => ((expNegIciReal y : ℝ) : ℂ) := by
      rw [← h₁, ← hfun]
      rfl
    rw [e]
    exact isSpectralIntegralOf_ofBounded _ hb
  have hs := (spectralMeasure_eq_pushforward c.spectral (isSelfAdjointOp_timeOne c) _ _
    measurable_expNegIciReal hI).2 negLogIocFn measurable_negLogIocFn
  have hG : IsSpectralIntegralOf (semigroupGenerator T) (timeOneMeasure T)
      fun y => negLogIocFn (y.1 0) := by
    have e : (fun y : RealLineSet => negLogIocFn (y.1 0)) =
        fun y => ((negLogIoc y : ℝ) : ℂ) :=
      funext negLogIocFn_coord
    rw [e]
    exact semigroupGenerator_isSpectralIntegralOf c
  have hAi := spectralMeasure_isSpectralMeasureFor c.spectral hA.1
  have hlin : Measurable (coordVar : RealLineSet → ℂ) :=
    Complex.measurable_ofReal.comp measurable_coord_zero
  have hcg := (unboundedFnCalc_of c.borel (spectralMeasure A)).congr coordVar
    (fun y => negLogIocFn (expNegIciReal y)) hlin
    (measurable_negLogIocFn.comp measurable_expNegIciReal) nonnegHalfLine
    (spectralMeasure_carried_nonnegHalfLine c.spectral hA) (fun y hy => by
      have hy' : y.1 0 ∈ Ici (0 : ℝ) := hy
      have hv : expNegIciReal y = Real.exp (-y.1 0) := by
        unfold expNegIciReal
        rw [indicator_of_mem hy']
      have hm : Real.exp (-y.1 0) ∈ Ioc (0 : ℝ) 1 :=
        ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy')⟩
      simp only [coordVar, negLogIocFn, hv, indicator_of_mem hm, Real.log_exp,
        neg_neg])
  refine op_eq_of_integralsAgree hAi hG ⟨hcg.1.trans hs.1.symm, fun ψ hψ => ?_⟩
  rw [hcg.2 ψ hψ]
  exact (hs.2 ψ (by rw [hs.1, ← hcg.1]; exact hψ)).symm
abbrev generatorSpectralMeasure (T : ℝ≥0 → ℋ →L[ℂ] ℋ) : SpectralMeasure RealLineSet ℋ :=
  spectralMeasure (semigroupGenerator T)
def indicatorZero : RealLineSet → ℂ := singletonZero.1.indicator 1
theorem mem_singletonZero (y : RealLineSet) : y ∈ singletonZero.1 ↔ y.1 0 = 0 := Iff.rfl
theorem measurable_indicatorZero : Measurable indicatorZero :=
  measurable_one.indicator singletonZero.2
theorem norm_indicatorZero_le (y : RealLineSet) : ‖indicatorZero y‖ ≤ 1 := by
  unfold indicatorZero
  by_cases hy : y ∈ singletonZero.1
  · rw [indicator_of_mem hy]
    simp
  · rw [indicator_of_notMem hy]
    simp
theorem integralOp_indicatorZero (c : Hypotheses T) :
    (generatorSpectralMeasure T).integralOp indicatorZero =
      generatorSpectralMeasure T singletonZero :=
  (boundedFnCalc_of c.borel _).indicator singletonZero
theorem expNegCoord_of_nonneg (t : ℝ≥0) {y : RealLineSet} (hy : 0 ≤ y.1 0) :
    expNegCoord t y = ((Real.exp (-(t : ℝ) * y.1 0) : ℝ) : ℂ) := by
  have hy' : y.1 0 ∈ Ici (0 : ℝ) := hy
  unfold expNegCoord expNegIci
  rw [indicator_of_mem hy', Complex.ofReal_exp]
theorem tendstoStrongly_atTop (c : Hypotheses T) :
    TendstoStrongly T atTop (generatorSpectralMeasure T singletonZero) := by
  intro ψ
  refine tendsto_of_seq_tendsto fun u hu => ?_
  have hcar := spectralMeasure_carried_nonnegHalfLine c.spectral (semigroupGenerator_isNonnegOp c)
  have h := strongConvergence_of c.borel (generatorSpectralMeasure T)
    (fun r => expNegCoord (u r)) indicatorZero 1 nonnegHalfLine
    (fun r => measurable_expNegCoord _) measurable_indicatorZero
    (fun r y => norm_expNegCoord_le _ _) hcar (fun y hy => ?_)
  · have h' := h.2 ψ
    rw [(generatorSpectralMeasure T).integralApply_eq_integralOp norm_indicatorZero_le,
      integralOp_indicatorZero c] at h'
    refine h'.congr fun r => ?_
    show (generatorSpectralMeasure T).integralOp (expNegCoord (u r)) ψ = T (u r) ψ
    rw [semigroup_eq_expNeg c]
    rfl
  · have hy' : 0 ≤ y.1 0 := hy
    rcases eq_or_lt_of_le hy' with h0 | h0
    · have e : ∀ r, expNegCoord (u r) y = 1 := by
        intro r
        rw [expNegCoord_of_nonneg _ hy', ← h0]
        simp
      have hz : indicatorZero y = 1 := by
        unfold indicatorZero
        rw [indicator_of_mem ((mem_singletonZero y).mpr h0.symm)]
        rfl
      simp only [e, hz]
      exact tendsto_const_nhds
    · have hz : indicatorZero y = 0 := by
        unfold indicatorZero
        rw [indicator_of_notMem (fun hm => h0.ne' ((mem_singletonZero y).mp hm))]
      rw [hz]
      have h₁ : Tendsto (fun r => ((u r : ℝ≥0) : ℝ) * y.1 0) atTop atTop :=
        (NNReal.tendsto_coe_atTop.mpr hu).atTop_mul_const h0
      have h₂ := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h₁)
      have h₃ := (Complex.continuous_ofReal.tendsto 0).comp h₂
      rw [Complex.ofReal_zero] at h₃
      refine h₃.congr fun r => ?_
      rw [expNegCoord_of_nonneg _ hy']
      simp [Function.comp_def]
theorem semigroup_apply_singletonZero (c : Hypotheses T) (t : ℝ≥0) (ψ : ℋ) :
    T t (generatorSpectralMeasure T singletonZero ψ) =
      generatorSpectralMeasure T singletonZero ψ := by
  have e : T t * generatorSpectralMeasure T singletonZero =
      generatorSpectralMeasure T singletonZero := by
    have ht : T t = (generatorSpectralMeasure T).integralOp (expNegCoord t) :=
      semigroup_eq_expNeg c t
    rw [ht, ← integralOp_indicatorZero c,
      ← (boundedFnCalc_of c.borel _).mul _ _ (measurable_expNegCoord t)
        ⟨1, norm_expNegCoord_le t⟩ measurable_indicatorZero ⟨1, norm_indicatorZero_le⟩]
    congr 1
    funext y
    by_cases hy : y ∈ singletonZero.1
    · have h0 : y.1 0 = 0 := (mem_singletonZero y).mp hy
      rw [Pi.mul_apply, expNegCoord_of_nonneg t h0.ge, h0]
      simp
    · simp [indicatorZero, indicator_of_notMem hy]
  exact congrArg (fun B : ℋ →L[ℂ] ℋ => B ψ) e
theorem singletonZero_apply_of_fixed (c : Hypotheses T) {ψ : ℋ} (hψ : T 1 ψ = ψ) :
    generatorSpectralMeasure T singletonZero ψ = ψ := by
  have hn : ∀ k : ℕ, T (k : ℝ≥0) ψ = ψ := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, c.semigroup.semigroup.1]
      rfl
    | succ k ih =>
      rw [Nat.cast_succ, semigroup_add_apply c.semigroup, hψ, ih]
  have h := (tendstoStrongly_atTop c ψ).comp (tendsto_natCast_atTop_atTop (R := ℝ≥0))
  have e : (fun t => T t ψ) ∘ (fun k : ℕ => (k : ℝ≥0)) = fun _ => ψ := funext hn
  rw [e] at h
  exact tendsto_nhds_unique h tendsto_const_nhds
theorem measurable_coordVar : Measurable (coordVar : RealLineSet → ℂ) :=
  Complex.measurable_ofReal.comp measurable_coord_zero
theorem opKernel_semigroupGenerator (c : Hypotheses T) :
    (opKernel (semigroupGenerator T) : Set ℋ) =
      Set.range (generatorSpectralMeasure T singletonZero) := by
  have hI := spectralMeasure_isSpectralMeasureFor c.spectral (semigroupGenerator_isSelfAdjointOp c)
  have hk := (kernelAndPositivity_of c.borel (generatorSpectralMeasure T)).kernel_eq coordVar
    measurable_coordVar
  have e : zeroLocus measurable_coordVar = singletonZero := by
    refine Subtype.ext ?_
    ext y
    simp [zeroLocus, coordVar, singletonZero, realLineSet]
  rw [e] at hk
  rw [← hk]
  ext ψ
  constructor
  · intro hψ
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hψ
    exact ⟨(hI.1 _).mp x.2, (hI.2 x).symm.trans hx⟩
  · rintro ⟨hd, hv⟩
    exact Submodule.mem_map.mpr ⟨⟨ψ, (hI.1 ψ).mpr hd⟩, (hI.2 _).trans hv, rfl⟩
theorem singletonZero_isOrthProjOnto (c : Hypotheses T) :
    IsOrthProjOnto (generatorSpectralMeasure T singletonZero)
      (opKernel (semigroupGenerator T) : Set ℋ) := by
  have hp := (generatorSpectralMeasure T).isStarProjection singletonZero
  exact ⟨⟨hp.isSelfAdjoint.star_eq.symm, hp.isIdempotentElem.eq.symm⟩,
    (opKernel_semigroupGenerator c).symm⟩
theorem singletonZero_eq_orthProjOnto (c : Hypotheses T) :
    generatorSpectralMeasure T singletonZero =
      orthProjOnto (opKernel (semigroupGenerator T) : Set ℋ) := by
  have hp := (generatorSpectralMeasure T).isStarProjection singletonZero
  have hcl : IsClosed (opKernel (semigroupGenerator T) : Set ℋ) := by
    have e : (opKernel (semigroupGenerator T) : Set ℋ) =
        {ψ | generatorSpectralMeasure T singletonZero ψ = ψ} := by
      rw [opKernel_semigroupGenerator c]
      ext ψ
      constructor
      · rintro ⟨φ, rfl⟩
        exact congrArg (fun B : ℋ →L[ℂ] ℋ => B φ) hp.isIdempotentElem.eq
      · intro h
        exact ⟨ψ, h⟩
    rw [e]
    exact isClosed_eq (generatorSpectralMeasure T singletonZero).continuous continuous_id
  obtain ⟨-, Q, -, -, huniq, hQ⟩ := c.orthProj ℋ (opKernel (semigroupGenerator T)) hcl
  rw [← hQ]
  exact huniq _ (singletonZero_isOrthProjOnto c)
theorem commute_generatorSpectralMeasure (c : Hypotheses T) {B : ℋ →L[ℂ] ℋ}
    (hB : Commute B (T 1)) (Δ : BorelSubsets RealLineSet) :
    Commute B (generatorSpectralMeasure T Δ) := by
  show Commute B (spectralMeasure (semigroupGenerator T) Δ)
  rw [spectralMeasure_semigroupGenerator c]
  exact commute_timeOneMeasure c hB _
theorem commute_semigroup_of_commute (c : Hypotheses T) {B : ℋ →L[ℂ] ℋ}
    (hB : Commute B (T 1)) (t : ℝ≥0) : Commute B (T t) := by
  rw [semigroup_eq_rpowSemigroup c t]
  exact commutesWithIntegralOps_of c.borel (timeOneMeasure T) B
    (fun Δ => commute_timeOneMeasure c hB Δ) _
    (measurable_rpowCoord t) (isBoundedFn_rpowCoord (NNReal.coe_nonneg t))
theorem unitary_apply_star_apply {U : ℋ →L[ℂ] ℋ} (hU : IsUnitaryOp U) (φ : ℋ) :
    U (star U φ) = φ :=
  congrArg (fun B : ℋ →L[ℂ] ℋ => B φ) hU.2
theorem norm_star_apply_of_unitary {U : ℋ →L[ℂ] ℋ} (hU : IsUnitaryOp U) (φ : ℋ) :
    ‖star U φ‖ = ‖φ‖ := by
  have e : ⟪star U φ, star U φ⟫_ℂ = ⟪φ, φ⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint, unitary_apply_star_apply hU]
  have h := congrArg Complex.re e
  rw [show (⟪star U φ, star U φ⟫_ℂ).re = ‖star U φ‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) _,
    show (⟪φ, φ⟫_ℂ).re = ‖φ‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) _] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
theorem star_commute_timeOne (c : Hypotheses T) {U : ℋ →L[ℂ] ℋ} (hc : Commute U (T 1)) :
    Commute (star U) (T 1) := by
  have h := congrArg star hc.eq
  rw [star_mul, star_mul, (c.semigroup.selfAdjoint 1).star_eq] at h
  exact h.symm
theorem conjByUnitary_semigroupGenerator (c : Hypotheses T) {U : ℋ →L[ℂ] ℋ}
    (hU : IsUnitaryOp U) (hc : Commute U (T 1)) :
    conjByUnitary U (semigroupGenerator T) = semigroupGenerator T := by
  have hcomm := commute_generatorSpectralMeasure c (star_commute_timeOne c hc)
  have hμ : ∀ ψ, (generatorSpectralMeasure T).diagMeasure (star U ψ) =
      (generatorSpectralMeasure T).diagMeasure ψ := by
    intro ψ
    refine Measure.ext fun s hs => ?_
    rw [(generatorSpectralMeasure T).diagMeasure_apply _ ⟨s, hs⟩,
      (generatorSpectralMeasure T).diagMeasure_apply _ ⟨s, hs⟩]
    have e : generatorSpectralMeasure T ⟨s, hs⟩ (star U ψ) =
        star U (generatorSpectralMeasure T ⟨s, hs⟩ ψ) :=
      congrArg (fun B : ℋ →L[ℂ] ℋ => B ψ) (hcomm ⟨s, hs⟩).eq.symm
    rw [e, norm_star_apply_of_unitary hU]
  have hI := spectralMeasure_isSpectralMeasureFor c.spectral (semigroupGenerator_isSelfAdjointOp c)
  have hdom : ∀ ψ, star U ψ ∈ (generatorSpectralMeasure T).integralDom coordVar ↔
      ψ ∈ (generatorSpectralMeasure T).integralDom coordVar := by
    intro ψ
    simp only [SpectralMeasure.integralDom, mem_ofPred_eq, hμ]
  have huc := unboundedFnCalc_of c.borel (generatorSpectralMeasure T)
  have hval : ∀ ψ ∈ (generatorSpectralMeasure T).integralDom coordVar,
      (generatorSpectralMeasure T).integralApply coordVar (star U ψ) =
        star U ((generatorSpectralMeasure T).integralApply coordVar ψ) := by
    intro ψ hψ
    have h₁ := huc.tendsto_truncate coordVar measurable_coordVar _ ((hdom ψ).mpr hψ)
    have h₂ := ((star U).continuous.tendsto _).comp
      (huc.tendsto_truncate coordVar measurable_coordVar ψ hψ)
    refine tendsto_nhds_unique h₁ (h₂.congr fun r => ?_)
    have hb : IsBoundedFn (truncate (coordVar : RealLineSet → ℂ) r) := by
      refine ⟨r, fun y => ?_⟩
      unfold truncate
      by_cases hy : y ∈ {y : RealLineSet | ‖coordVar y‖ ≤ r}
      · rw [indicator_of_mem hy]
        exact hy
      · rw [indicator_of_notMem hy]
        simp
    have hm : Measurable (truncate (coordVar : RealLineSet → ℂ) r) :=
      measurable_coordVar.indicator
        (measurableSet_le measurable_coordVar.norm measurable_const)
    exact congrArg (fun B : ℋ →L[ℂ] ℋ => B ψ)
      (commutesWithIntegralOps_of c.borel (generatorSpectralMeasure T) (star U) hcomm _ hm hb).eq
  refine LinearPMap.ext ?_ fun ψ h h' => ?_
  · ext ψ
    show star U ψ ∈ (semigroupGenerator T).domain ↔ ψ ∈ (semigroupGenerator T).domain
    rw [hI.1, hI.1, hdom]
  · have hm : star U ψ ∈ (semigroupGenerator T).domain := h
    show U (semigroupGenerator T ⟨star U ψ, hm⟩) = semigroupGenerator T ⟨ψ, h'⟩
    rw [hI.2, hI.2]
    show U ((generatorSpectralMeasure T).integralApply coordVar (star U ψ)) =
      (generatorSpectralMeasure T).integralApply coordVar ψ
    rw [hval ψ ((hI.1 ψ).mp h'), unitary_apply_star_apply hU]
theorem contractionSemigroupTheorem_holds (hF : HilbertSpaceFacts.Facts)
    (hC : BorelCalculusTheorem) (hB : JointSpectral.JointSpectralTheorem)
    (hS : SpectralTheoremHolds) : ContractionSemigroupTheorem := by
  obtain ⟨-, -, -, -, -, -, -, -, hproj, -, -, -, -, -, -, hnb, hpos, hsq, -, -, -⟩ := hF
  intro ℋ _ _ _ T hT
  have c : Hypotheses T := ⟨hC, hS, hB, hnb, hpos, hsq, hproj, hT⟩
  have hfix : ∀ ψ, generatorSpectralMeasure T singletonZero ψ = ψ ↔
      ψ ∈ (opKernel (semigroupGenerator T) : Set ℋ) := by
    intro ψ
    rw [opKernel_semigroupGenerator c]
    constructor
    · intro h
      exact ⟨ψ, h⟩
    · rintro ⟨φ, rfl⟩
      exact congrArg (fun B : ℋ →L[ℂ] ℋ => B φ)
        ((generatorSpectralMeasure T).isStarProjection singletonZero).isIdempotentElem.eq
  refine ⟨⟨stronglyCont_of_semigroup hT, fun t => ⟨isPositiveOp_semigroup hpos hT t,
      isGE_one_semigroup hnb hT t⟩, semigroup_ker_eq_bot hT⟩,
    ⟨fun n Y F x hx hxI h₁ => semigroup_eq_integralOp_rpow c F x hx hxI h₁,
      semigroup_eq_rpowOp c⟩,
    ⟨⟨semigroupGenerator T, ⟨semigroupGenerator_isNonnegOp c, semigroup_eq_expNeg c⟩,
        fun A hA => eq_semigroupGenerator c A hA.1 (hA.2 1).symm⟩,
      semigroupGenerator_isNonnegOp c, semigroup_eq_expNeg c,
      fun A hA h => eq_semigroupGenerator c A hA h, spectralMeasure_semigroupGenerator c⟩,
    ⟨?_, ?_, tendstoStrongly_atTop c, singletonZero_isOrthProjOnto c,
      singletonZero_eq_orthProjOnto c⟩,
    fun B hB' => ⟨commute_generatorSpectralMeasure c hB', commute_semigroup_of_commute c hB'⟩,
    fun U hU hc => conjByUnitary_semigroupGenerator c hU hc⟩
  · ext ψ
    constructor
    · intro h
      have e := (hfix ψ).mpr h
      rw [← e]
      exact semigroup_apply_singletonZero c 1 ψ
    · intro h
      exact (hfix ψ).mp (singletonZero_apply_of_fixed c h)
  · ext ψ
    constructor
    · intro h t
      have e := singletonZero_apply_of_fixed c h
      rw [← e]
      exact semigroup_apply_singletonZero c t ψ
    · intro h
      exact h 1
end YangMills.Construction.ContractionSemigroups
