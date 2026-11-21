import YangMills.Construction.ComplexMeasures.UniquenessOfMeasuresAndTheIntegralOfAComplexMeasure
import YangMills.Construction.SpectralTheory.CommutationWithBoundedIntegrals
import YangMills.Construction.SpectralTheory.MeasuresIntegralsProductsImagesAndTransportOfAProjectionValuedMeasure
import YangMills.Construction.SpectralTheory.SpectralIntegralKernelLemmas
import YangMills.Construction.SpectralTheory.UnboundedBorelCalculusFromTruncations
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.SpectralMeasureCalculus
open YangMills.Construction.BorelSpectral YangMills.Construction.BorelSpectral.SpectralMeasure
open YangMills.Construction.BorelCalculus
open YangMills.Construction.SpectralTheorem
  (IsSpectralIntegralOf spectralIntegralOp pushforwardToLine coordVar IntegralsAgree)
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
theorem diagMeasure_real_eq_norm_sq (E : SpectralMeasure Y H) (ψ : H) (Δ : BorelSubsets Y) :
    (E.diagMeasure ψ).real Δ.1 = ‖E Δ ψ‖ ^ 2 := by
  rw [Measure.real, E.diagMeasure_apply, ENNReal.toReal_ofReal (by positivity)]
theorem inner_apply_left_eq (E : SpectralMeasure Y H) (Δ : BorelSubsets Y) (φ ψ : H) :
    ⟪E Δ φ, ψ⟫_ℂ = ⟪φ, E Δ ψ⟫_ℂ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (E.isStarProjection Δ).isSelfAdjoint) φ ψ
theorem measurable_indicator_one_borel (Δ : BorelSubsets Y) :
    Measurable (Δ.1.indicator (1 : Y → ℂ)) :=
  measurable_one.indicator Δ.2
theorem isBoundedFn_indicator_one (Δ : BorelSubsets Y) : IsBoundedFn (Δ.1.indicator (1 : Y → ℂ)) := by
  refine ⟨1, fun y => ?_⟩
  by_cases h : y ∈ Δ.1 <;> simp [h]
theorem apply_union_of_disjoint (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    (A B : BorelSubsets Y) (h : Disjoint A.1 B.1) :
    E ⟨A.1 ∪ B.1, A.2.union B.2⟩ = E A + E B := by
  rw [← hE.indicator A, ← hE.indicator B, ← hE.indicator ⟨A.1 ∪ B.1, A.2.union B.2⟩,
    ← hE.add _ _ (measurable_indicator_one_borel A) (isBoundedFn_indicator_one A)
      (measurable_indicator_one_borel B) (isBoundedFn_indicator_one B)]
  congr 1
  exact indicator_union_of_disjoint h _
theorem apply_biUnion_finset {ι : Type} (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    (Δ : ι → BorelSubsets Y) (hd : Pairwise fun k l => Disjoint (Δ k).1 (Δ l).1) (s : Finset ι) :
    E ⟨⋃ k ∈ s, (Δ k).1, Finset.measurableSet_biUnion s fun k _ => (Δ k).2⟩ =
      ∑ k ∈ s, E (Δ k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (⟨⋃ k ∈ (∅ : Finset ι), (Δ k).1,
        Finset.measurableSet_biUnion ∅ fun k _ => (Δ k).2⟩ : BorelSubsets Y) =
        ⟨∅, MeasurableSet.empty⟩ := Subtype.ext (by simp)
    rw [this, E.apply_empty, Finset.sum_empty]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih, ← apply_union_of_disjoint E hE]
    · congr 1
      exact Subtype.ext (Finset.set_biUnion_insert a s _)
    · refine Set.disjoint_iUnion₂_right.mpr fun k hk => hd ?_
      rintro rfl
      exact ha hk
theorem hasSum_apply_iUnion {ι : Type} [Countable ι] (E : SpectralMeasure Y H)
    (hE : BoundedFunctionalCalculus E) (Δ : ι → BorelSubsets Y) (ψ : H)
    (hd : Pairwise fun k l => Disjoint (Δ k).1 (Δ l).1) :
    HasSum (fun k => E (Δ k) ψ) (E ⟨⋃ k, (Δ k).1, MeasurableSet.iUnion fun k => (Δ k).2⟩ ψ) := by
  classical
  set μ := E.diagMeasure ψ with hμ
  set D : BorelSubsets Y := ⟨⋃ k, (Δ k).1, MeasurableSet.iUnion fun k => (Δ k).2⟩ with hD
  have hU : μ D.1 = ∑' k, μ (Δ k).1 := measure_iUnion hd fun k => (Δ k).2
  have hne : ∑' k, μ (Δ k).1 ≠ ∞ := by rw [← hU]; exact measure_ne_top _ _
  have hsum : HasSum (fun k => μ.real (Δ k).1) (μ.real D.1) := by
    have h2 := ENNReal.hasSum_toReal hne
    have h3 : μ.real D.1 = ∑' k, (μ (Δ k).1).toReal := by
      rw [Measure.real, hU, ENNReal.tsum_toReal_eq fun k => measure_ne_top _ _]
    rw [h3]
    exact h2
  have hrest : ∀ s : Finset ι, ‖E D ψ - ∑ k ∈ s, E (Δ k) ψ‖ ^ 2 =
      μ.real D.1 - ∑ k ∈ s, μ.real (Δ k).1 := by
    intro s
    set S : BorelSubsets Y := ⟨⋃ k ∈ s, (Δ k).1, Finset.measurableSet_biUnion s fun k _ => (Δ k).2⟩
      with hS
    have hSD : S.1 ⊆ D.1 := iUnion₂_subset fun k _ => subset_iUnion (fun k => (Δ k).1) k
    have hES : E S ψ = ∑ k ∈ s, E (Δ k) ψ := by
      rw [hS, apply_biUnion_finset E hE Δ hd s, _root_.sum_apply]
    set R : BorelSubsets Y := ⟨D.1 \ S.1, D.2.diff S.2⟩ with hR
    have hDR : D = ⟨R.1 ∪ S.1, R.2.union S.2⟩ :=
      Subtype.ext (by simp [hR, sdiff_union_of_subset hSD])
    have hadd : E D = E R + E S := by
      rw [hDR]
      exact apply_union_of_disjoint E hE R S disjoint_sdiff_left
    have h1 : E D ψ - ∑ k ∈ s, E (Δ k) ψ = E R ψ := by
      rw [hadd, ← hES]
      simp
    rw [h1, ← diagMeasure_real_eq_norm_sq, ← hμ, hR]
    have h2 : μ.real (D.1 \ S.1) = μ.real D.1 - μ.real S.1 :=
      measureReal_sdiff hSD S.2
    have h3 : μ.real S.1 = ∑ k ∈ s, μ.real (Δ k).1 :=
      measureReal_biUnion_finset (fun k _ l _ hkl => hd hkl) fun k _ => (Δ k).2
    simp only [h2, h3]
  have hz : Tendsto (fun s : Finset ι => ‖E D ψ - ∑ k ∈ s, E (Δ k) ψ‖ ^ 2) atTop (𝓝 0) := by
    simp only [hrest]
    have := (tendsto_const_nhds (x := μ.real D.1)).sub hsum
    simpa using this
  have hz' : Tendsto (fun s : Finset ι => ‖E D ψ - ∑ k ∈ s, E (Δ k) ψ‖) atTop (𝓝 0) := by
    have := hz.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  rw [HasSum, SummationFilter.unconditional_filter]
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  simpa only [norm_sub_rev] using hz'
theorem inner_apply_add_smul (E : SpectralMeasure Y H) (Δ : BorelSubsets Y) (α β : H) (c : ℂ) :
    ⟪α + c • β, E Δ (α + c • β)⟫_ℂ = ⟪α, E Δ α⟫_ℂ + c * ⟪α, E Δ β⟫_ℂ +
      (starRingEnd ℂ) c * ⟪β, E Δ α⟫_ℂ + (starRingEnd ℂ) c * c * ⟪β, E Δ β⟫_ℂ := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  ring
theorem diagMeasure_real_eq_inner (E : SpectralMeasure Y H) (Δ : BorelSubsets Y) (χ : H) :
    (((E.diagMeasure χ).real Δ.1 : ℝ) : ℂ) = ⟪χ, E Δ χ⟫_ℂ :=
  (E.inner_apply_self_eq_diagMeasure χ Δ).symm
theorem matrixCoeff_eq_polarization_sum (E : SpectralMeasure Y H) (φ ψ : H) (Δ : BorelSubsets Y) :
    E.matrixCoeff φ ψ Δ = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
      Complex.I ^ k * (((E.diagMeasure (ψ + Complex.I ^ k • φ)).real Δ.1 : ℝ) : ℂ) := by
  simp only [diagMeasure_real_eq_inner, inner_apply_add_smul, Finset.sum_range_succ,
    Finset.sum_range_zero, matrixCoeff]
  have h3 : Complex.I ^ 3 = -Complex.I := Complex.I_pow_three
  simp only [pow_zero, pow_one, Complex.I_sq, h3, map_one, map_neg, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring
theorem matrixCoeff_eq_four_terms (E : SpectralMeasure Y H) (φ ψ : H) (Δ : BorelSubsets Y) :
    E.matrixCoeff φ ψ Δ = (1 / 4 : ℂ) * ((((E.diagMeasure (φ + Complex.I ^ 0 • ψ)).real Δ.1 : ℝ) : ℂ)
      - (((E.diagMeasure (φ + Complex.I ^ 2 • ψ)).real Δ.1 : ℝ) : ℂ)
      + Complex.I * ((((E.diagMeasure (φ + Complex.I ^ 3 • ψ)).real Δ.1 : ℝ) : ℂ)
        - (((E.diagMeasure (φ + Complex.I ^ 1 • ψ)).real Δ.1 : ℝ) : ℂ))) := by
  simp only [diagMeasure_real_eq_inner, inner_apply_add_smul, matrixCoeff]
  have h3 : Complex.I ^ 3 = -Complex.I := Complex.I_pow_three
  simp only [pow_zero, pow_one, Complex.I_sq, h3, map_one, map_neg, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring
theorem integralOf_matrixCoeff (hU : MeasureUniqueness.UniquenessAndIntegral)
    (E : SpectralMeasure Y H) (g : Y → ℂ) (φ ψ : H) (hg : Measurable g)
    (hi : ∀ k ∈ Finset.range 4, Integrable g (E.diagMeasure (φ + Complex.I ^ k • ψ))) :
    BorelComplexMeasures.integralOf (E.matrixCoeff φ ψ) g = E.polarizedIntegral g φ ψ := by
  have hdep := (hU.2.2.2.2.1 n E.one_le_dimension Y E.measurableSet_carrier).2
  set M : ℕ → Measure Y := fun k => E.diagMeasure (φ + Complex.I ^ k • ψ) with hM
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / 4) with hc
  have hc' : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hct : c.toReal = 1 / 4 := ENNReal.toReal_ofReal (by norm_num)
  have hfin : ∀ k, IsFiniteMeasure (c • M k) := fun k => by
    have : IsFiniteMeasure (M k) := by simp only [hM]; infer_instance
    exact Measure.smul_finite _ hc'
  have hint : ∀ k ∈ Finset.range 4, Integrable g (c • M k) := fun k hk =>
    (hi k hk).smul_measure hc'
  have hval : ∀ (k : ℕ) (Δ : Set Y), (c • M k).real Δ = (1 / 4) * (M k).real Δ := fun k Δ => by
    simp [Measure.real, hct]
  have hiv : BorelComplexMeasures.IsIntegralOf (E.matrixCoeff φ ψ) g
      (E.polarizedIntegral g φ ψ) := by
    refine ⟨c • M 0, c • M 2, c • M 3, c • M 1, ⟨hfin 0, hfin 2, hfin 3, hfin 1, fun Δ => ?_⟩, hg,
      hint 0 (by simp), hint 2 (by simp), hint 3 (by simp), hint 1 (by simp), ?_⟩
    · have hMk : ∀ k, E.diagMeasure (φ + Complex.I ^ k • ψ) = M k := fun _ => rfl
      rw [matrixCoeff_eq_four_terms]
      simp only [hMk, hval]
      push_cast
      ring
    · simp only [BorelComplexMeasures.combinedIntegral, polarizedIntegral,
        integral_smul_measure, hct, Finset.sum_range_succ, Finset.sum_range_zero, hM]
      simp only [Complex.real_smul, neg_pow (Complex.I), Complex.I_sq]
      norm_num
      ring_nf
  exact hdep _ _ _ hiv
theorem measureLaws_holds (hU : MeasureUniqueness.UniquenessAndIntegral)
    (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E) : MeasureLaws E where
  isFiniteMeasure ψ := inferInstance
  real_apply ψ Δ := diagMeasure_real_eq_norm_sq E ψ Δ
  real_univ ψ := by
    have := diagMeasure_real_eq_norm_sq E ψ ⟨univ, MeasurableSet.univ⟩
    rw [E.map_univ] at this
    simpa using this
  value_empty := E.apply_empty
  orthogonal ι _ Δ ψ hd k l hkl := by
    show ⟪E (Δ k) ψ, E (Δ l) ψ⟫_ℂ = 0
    have hi : (⟨(Δ k).1 ∩ (Δ l).1, (Δ k).2.inter (Δ l).2⟩ : BorelSubsets Y) =
        ⟨∅, MeasurableSet.empty⟩ :=
      Subtype.ext (Set.disjoint_iff_inter_eq_empty.mp (hd hkl))
    have hz : E (Δ k) * E (Δ l) = 0 := by
      rw [← E.map_inter, hi, E.apply_empty]
    have hz' : E (Δ k) (E (Δ l) ψ) = 0 := congrArg (fun T : H →L[ℂ] H => T ψ) hz
    rw [inner_apply_left_eq, hz', inner_zero_right]
  hasSum ι _ Δ ψ hd := hasSum_apply_iUnion E hE Δ ψ hd
  complexMeasure_eq φ ψ Δ := matrixCoeff_eq_polarization_sum E φ ψ Δ
  isComplexMeasure φ ψ := by
    intro A hA
    have h := hasSum_apply_iUnion E hE A ψ hA
    have h2 : HasSum (fun j => ⟪φ, E (A j) ψ⟫_ℂ)
        ⟪φ, E ⟨⋃ k, (A k).1, MeasurableSet.iUnion fun k => (A k).2⟩ ψ⟫_ℂ :=
      ((innerSL ℂ φ).hasSum h)
    exact h2.tendsto_sum_nat
  value_iUnion ι _ Δ h := hE.apply_iUnion ι Δ h
  real_add_le φ ψ Δ := by
    rw [diagMeasure_real_eq_norm_sq, diagMeasure_real_eq_norm_sq, diagMeasure_real_eq_norm_sq,
      map_add]
    have h := norm_add_le (E Δ ψ) (E Δ φ)
    have h0 := norm_nonneg (E Δ ψ + E Δ φ)
    nlinarith [sq_nonneg (‖E Δ ψ‖ - ‖E Δ φ‖), norm_nonneg (E Δ ψ), norm_nonneg (E Δ φ)]
  real_smul c ψ Δ := by
    rw [diagMeasure_real_eq_norm_sq, diagMeasure_real_eq_norm_sq, map_smul, norm_smul, mul_pow]
  integral_eq g φ ψ hg hi := integralOf_matrixCoeff hU E g φ ψ hg hi
theorem integrable_of_isBoundedFn (E : SpectralMeasure Y H) {g : Y → ℂ} (hg : Measurable g)
    (hb : IsBoundedFn g) (ψ : H) : Integrable g (E.diagMeasure ψ) := by
  obtain ⟨c, hc⟩ := hb
  exact Integrable.of_bound hg.aestronglyMeasurable c (ae_of_all _ hc)
theorem inner_integralOp_eq_integralOf (hU : MeasureUniqueness.UniquenessAndIntegral)
    (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E) {g : Y → ℂ} (hg : Measurable g)
    (hb : IsBoundedFn g) (φ ψ : H) :
    ⟪φ, E.integralOp g ψ⟫_ℂ =
      BorelComplexMeasures.integralOf (E.matrixCoeff φ ψ) g := by
  rw [hE.inner_eq g hg hb φ ψ,
    integralOf_matrixCoeff hU E g φ ψ hg fun k _ => integrable_of_isBoundedFn E hg hb _]
theorem diagMeasure_compl_eq_zero (E : SpectralMeasure Y H) {C : BorelSubsets Y}
    (hC : E.IsCarriedBy C) (ψ : H) : E.diagMeasure ψ C.1ᶜ = 0 := by
  have h := E.diagMeasure_apply ψ ⟨C.1ᶜ, C.2.compl⟩
  rw [show E ⟨C.1ᶜ, C.2.compl⟩ = 0 from hC] at h
  simpa using h
theorem ae_mem_of_isCarriedBy (E : SpectralMeasure Y H) {C : BorelSubsets Y} (hC : E.IsCarriedBy C)
    (ψ : H) : ∀ᵐ y ∂E.diagMeasure ψ, y ∈ C.1 := by
  have h := compl_mem_ae_iff.mpr (diagMeasure_compl_eq_zero E hC ψ)
  filter_upwards [h] with y hy
  simpa using hy
theorem norm_integralOp_le_iSup (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    {g : Y → ℂ} {C : BorelSubsets Y} (hg : Measurable g) (hb : IsBoundedFn g)
    (hC : E.IsCarriedBy C) : ‖E.integralOp g‖ ≤ ⨆ y : C.1, ‖g y‖ := by
  obtain ⟨c, hc⟩ := id hb
  have hs : 0 ≤ ⨆ y : C.1, ‖g y‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  have hbdd : BddAbove (range fun y : C.1 => ‖g y‖) :=
    ⟨c, by rintro _ ⟨y, rfl⟩; exact hc y⟩
  refine ContinuousLinearMap.opNorm_le_bound _ hs fun ψ => ?_
  set s := ⨆ y : C.1, ‖g y‖ with hsdef
  have hsq : ‖E.integralOp g ψ‖ ^ 2 ≤ (s * ‖ψ‖) ^ 2 := by
    rw [hE.norm_sq g hg hb ψ]
    have hle : ∫ y, ‖g y‖ ^ 2 ∂E.diagMeasure ψ ≤ ∫ _, s ^ 2 ∂E.diagMeasure ψ := by
      refine integral_mono_ae ?_ (integrable_const _) ?_
      · refine Integrable.of_bound (hg.norm.pow_const 2).aestronglyMeasurable (c ^ 2)
          (ae_of_all _ fun y => ?_)
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hc y) 2
      · filter_upwards [ae_mem_of_isCarriedBy E hC ψ] with y hy
        exact pow_le_pow_left₀ (norm_nonneg _) (le_ciSup hbdd ⟨y, hy⟩) 2
    refine hle.trans_eq ?_
    have hu : (E.diagMeasure ψ).real univ = ‖ψ‖ ^ 2 := by
      have h := diagMeasure_real_eq_norm_sq E ψ ⟨univ, MeasurableSet.univ⟩
      rw [E.map_univ] at h
      simpa using h
    rw [integral_const, Measure.real] at *
    simp only [smul_eq_mul]
    rw [hu]
    ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
theorem boundedCalculusLaws_holds (hU : MeasureUniqueness.UniquenessAndIntegral)
    (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E) (hS : StrongConvergence E)
    (hC : CommutesWithIntegralOps E) (hA : UnboundedFunctionalCalculus E) :
    BoundedCalculusLaws E where
  existsUnique_operator g hg hb := by
    refine ⟨E.integralOp g, fun φ ψ => inner_integralOp_eq_integralOf hU E hE hg hb φ ψ,
      fun T hT => ?_⟩
    refine ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => ?_
    rw [hT, inner_integralOp_eq_integralOf hU E hE hg hb]
  inner_eq g hg hb φ ψ := inner_integralOp_eq_integralOf hU E hE hg hb φ ψ
  add := hE.add
  smul := hE.smul
  mul := hE.mul
  conjugate := hE.star_eq
  indicator := hE.indicator
  norm_sq := hE.norm_sq
  norm_le g C hg hb hc := norm_integralOp_le_iSup E hE hg hb hc
  congr g g' C hg hb hg' hb' hc h := by
    obtain ⟨c, hc₁⟩ := hb
    obtain ⟨c', hc₂⟩ := hb'
    have h2 := (hA.congr g g' hg hg' C hc h).2
    refine ContinuousLinearMap.ext fun ψ => ?_
    rw [← E.integralApply_eq_integralOp hc₁ ψ, ← E.integralApply_eq_integralOp hc₂ ψ]
    exact h2 ψ (by rw [E.integralDom_eq_univ hc₁]; exact mem_univ _)
  tendsto f g c C hf hg hb hgb hc hl ψ := by
    have h := (hS f g c C hf hg hb hc hl).2 ψ
    rwa [E.integralApply_eq_integralOp hgb ψ] at h
  commute B g hB hg hb := hC B hB g hg hb
theorem integralDom_congr_norm (E : SpectralMeasure Y H) {g g' : Y → ℂ}
    (h : ∀ y, ‖g y‖ = ‖g' y‖) : E.integralDom g = E.integralDom g' := by
  have h' : ∀ y, ‖g y‖ₑ = ‖g' y‖ₑ := fun y => by rw [← ofReal_norm, ← ofReal_norm, h]
  simp only [integralDom, h']
theorem measurable_truncate {g : Y → ℂ} (hg : Measurable g) (k : ℕ) :
    Measurable (truncate g k) :=
  hg.indicator (measurableSet_le hg.norm measurable_const)
theorem norm_truncate_le (g : Y → ℂ) (k : ℕ) (y : Y) : ‖truncate g k y‖ ≤ k := by apply _root_.YangMills.Construction.BorelCalculus.Unbounded.norm_truncate_apply_le <;> assumption
theorem isBoundedFn_truncate (g : Y → ℂ) (k : ℕ) : IsBoundedFn (truncate g k) := by apply _root_.YangMills.Construction.SpectralPushforward.isBoundedFn_truncate <;> assumption
theorem eventually_truncate_eq (g : Y → ℂ) (y : Y) :
    ∀ᶠ k : ℕ in atTop, truncate g k y = g y := by
  filter_upwards [eventually_ge_atTop ⌈‖g y‖⌉₊] with k hk
  have : y ∈ {y | ‖g y‖ ≤ k} := by
    have h1 := Nat.le_ceil ‖g y‖
    have h2 : (⌈‖g y‖⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
    exact h1.trans h2
  simp [truncate, this]
theorem integrable_norm_sq_of_mem_integralDom (E : SpectralMeasure Y H) {g : Y → ℂ}
    (hg : Measurable g) {ψ : H} (hψ : ψ ∈ E.integralDom g) :
    Integrable (fun y => ‖g y‖ ^ 2) (E.diagMeasure ψ) := by apply _root_.YangMills.Construction.SpectralKernel.integrable_norm_sq_of_mem_integralDom <;> assumption
theorem integrable_of_mem_integralDom (E : SpectralMeasure Y H) {g : Y → ℂ} (hg : Measurable g)
    {ψ : H} (hψ : ψ ∈ E.integralDom g) : Integrable g (E.diagMeasure ψ) := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  have hle : ∀ y, ‖g y‖ₑ ≤ 1 + ‖g y‖ₑ ^ 2 := fun y => by
    rcases le_total ‖g y‖ₑ 1 with h | h
    · exact h.trans le_self_add
    · calc ‖g y‖ₑ = ‖g y‖ₑ * 1 := (mul_one _).symm
        _ ≤ ‖g y‖ₑ * ‖g y‖ₑ := by gcongr
        _ = ‖g y‖ₑ ^ 2 := (sq _).symm
        _ ≤ 1 + ‖g y‖ₑ ^ 2 := le_add_self
  refine ((lintegral_mono hle).trans_lt ?_)
  rw [lintegral_add_left measurable_const]
  exact ENNReal.add_lt_top.mpr ⟨by simp, hψ⟩
theorem isSpectralIntegralOf_spectralIntegralOp (E : SpectralMeasure Y H)
    (hA : UnboundedFunctionalCalculus E) {g : Y → ℂ} (hg : Measurable g) :
    IsSpectralIntegralOf (spectralIntegralOp E g) E g := by
  obtain ⟨A, -, hd, hv⟩ := hA.exists_op g hg
  have hex : ∃ A, IsSpectralIntegralOf A E g := ⟨A, fun ψ => by rw [← SetLike.mem_coe, hd], hv⟩
  exact Classical.epsilon_spec hex
theorem unboundedCalculusLaws_holds (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    (hA : UnboundedFunctionalCalculus E) : UnboundedCalculusLaws E where
  dense_domain g hg := by
    obtain ⟨A, hdense, hd, -⟩ := hA.exists_op g hg
    rwa [← hd]
  isIntegralOf g hg := isSpectralIntegralOf_spectralIntegralOp E hA hg
  range_subset_domain g hg k := by
    rintro _ ⟨ψ, rfl⟩
    have hb : IsBoundedFn (g * (normLeSet hg k).1.indicator (1 : Y → ℂ)) := by
      refine ⟨k, fun y => ?_⟩
      by_cases h : y ∈ (normLeSet hg k).1
      · have h' : ‖g y‖ ≤ k := h
        simpa [h] using h'
      · simp [h]
    have h := (hA.range_subset_dom g _ hg (measurable_indicator_one_borel _)
      (isBoundedFn_indicator_one _) hb ψ).1
    rwa [hE.indicator] at h
  domain_conjugate g _ := integralDom_congr_norm E fun y => by simp [conjFn]
  domain_modulus g _ := integralDom_congr_norm E fun y => by simp
  tendsto_truncation := hA.tendsto_truncate
  of_bounded g _ hb := by
    obtain ⟨c, hc⟩ := hb
    exact ⟨E.integralDom_eq_univ hc, E.integralApply_eq_integralOp hc⟩
  norm_sq := hA.norm_sq
  norm_sub_sq := hA.norm_sub_sq
  integrable g hg ψ hψ := integrable_of_mem_integralDom E hg hψ
  inner_self := hA.inner_eq
  inner_conjugate g hg φ hφ ψ hψ := by
    have hcg : Measurable (conjFn g) := Complex.continuous_conj.measurable.comp hg
    have hdom : E.integralDom (conjFn g) = E.integralDom g :=
      integralDom_congr_norm E fun y => by simp [conjFn]
    obtain ⟨A, -, hd, hv⟩ := hA.exists_op g hg
    obtain ⟨A', -, hd', hv'⟩ := hA.exists_op _ hcg
    have hadj := hA.adjoint g hg A A' ⟨hd, hv⟩ ⟨hd', hv'⟩
    have hψA : ψ ∈ A.domain := by rw [← SetLike.mem_coe, hd]; exact hψ
    have hφA : φ ∈ A'.domain := by rw [← SetLike.mem_coe, hd', hdom]; exact hφ
    have h := hadj.2 ⟨φ, hφA⟩ ⟨ψ, hψA⟩
    rwa [hv, hv'] at h
  congr g g' C hg hg' hc h := hA.congr g g' hg hg' C hc h
theorem diagMeasure_integralOp (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    {g' : Y → ℂ} (hg' : Measurable g') (hb : IsBoundedFn g') (ψ : H) :
    E.diagMeasure (E.integralOp g' ψ) =
      (E.diagMeasure ψ).withDensity fun y => ‖g' y‖ₑ ^ 2 :=
  Measure.ext fun s hs => by
    rw [withDensity_apply _ hs]
    exact hE.diagMeasure_eq g' hg' hb ψ ⟨s, hs⟩
theorem integralOp_mem_integralDom (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    {g g' : Y → ℂ} (hg : Measurable g) (hg' : Measurable g') (hb : IsBoundedFn g') {ψ : H}
    (hψ : ψ ∈ E.integralDom (g * g')) : E.integralOp g' ψ ∈ E.integralDom g := by
  have hm' : Measurable fun y => ‖g' y‖ₑ ^ 2 := hg'.enorm.pow_const 2
  have hm : Measurable fun y => ‖g y‖ₑ ^ 2 := hg.enorm.pow_const 2
  show ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure (E.integralOp g' ψ) < ∞
  rw [diagMeasure_integralOp E hE hg' hb ψ, lintegral_withDensity_eq_lintegral_mul _ hm' hm]
  have h : ∀ y, ((fun y => ‖g' y‖ₑ ^ 2) * fun y => ‖g y‖ₑ ^ 2) y = ‖(g * g') y‖ₑ ^ 2 := fun y => by
    simp only [Pi.mul_apply, enorm_mul, mul_pow]
    exact mul_comm _ _
  simp only [h]
  exact hψ
theorem integralApply_integralOp_eq (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    (hA : UnboundedFunctionalCalculus E) {g g' : Y → ℂ} (hg : Measurable g) (hg' : Measurable g')
    (hb : IsBoundedFn g') {ψ : H} (hψ : ψ ∈ E.integralDom (g * g')) :
    E.integralApply g (E.integralOp g' ψ) = E.integralApply (g * g') ψ := by
  have hχ := integralOp_mem_integralDom E hE hg hg' hb hψ
  have hgg' : Measurable (g * g') := hg.mul hg'
  have hkb : ∀ k, IsBoundedFn (truncate g k * g') := fun k => by
    obtain ⟨c, hc⟩ := id hb
    refine ⟨k * c, fun y => ?_⟩
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (norm_truncate_le g k y) (hc y) (norm_nonneg _) (by positivity)
  have hkm : ∀ k, Measurable (truncate g k * g') := fun k =>
    (measurable_truncate hg k).mul hg'
  have t₁ := hA.tendsto_truncate g hg _ hχ
  have t₂ : Tendsto (fun k => E.integralOp (truncate g k) (E.integralOp g' ψ)) atTop
      (𝓝 (E.integralApply (g * g') ψ)) := by
    have hrew : ∀ k, E.integralOp (truncate g k) (E.integralOp g' ψ) =
        E.integralOp (truncate g k * g') ψ := fun k => by
      rw [hE.mul _ _ (measurable_truncate hg k) (isBoundedFn_truncate g k) hg' hb]
      rfl
    simp only [hrew]
    have hsq : Tendsto (fun k : ℕ => ∫ y, ‖(g * g') y - (truncate g k * g') y‖ ^ 2
        ∂E.diagMeasure ψ) atTop (𝓝 (∫ _, (0 : ℝ) ∂E.diagMeasure ψ)) := by
      refine tendsto_integral_of_dominated_convergence (fun y => ‖(g * g') y‖ ^ 2) ?_
        (integrable_norm_sq_of_mem_integralDom E hgg' hψ) ?_ ?_
      · exact fun k => ((hgg'.sub (hkm k)).norm.pow_const 2).aestronglyMeasurable
      · refine fun k => ae_of_all _ fun y => ?_
        rw [Real.norm_of_nonneg (by positivity)]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        by_cases h : y ∈ {y | ‖g y‖ ≤ (k : ℝ)}
        · simp only [truncate, Pi.mul_apply, indicator_of_mem h, sub_self, norm_zero]
          positivity
        · simp [truncate, h]
      · refine ae_of_all _ fun y => tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_truncate_eq g y] with k hk
        simp [hk]
    simp only [integral_zero] at hsq
    have hnorm : Tendsto (fun k : ℕ => ‖E.integralApply (g * g') ψ -
        E.integralOp (truncate g k * g') ψ‖) atTop (𝓝 0) := by
      have h := hsq.sqrt
      have hrew2 : ∀ k : ℕ, √(∫ y, ‖(g * g') y - (truncate g k * g') y‖ ^ 2
          ∂E.diagMeasure ψ) = ‖E.integralApply (g * g') ψ -
            E.integralOp (truncate g k * g') ψ‖ := fun k => by
        rw [← hA.norm_sub_sq (g * g') _ hgg' (hkm k) (hkb k) ψ hψ, Real.sqrt_sq (norm_nonneg _)]
      rw [Real.sqrt_zero] at h
      exact h.congr hrew2
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    simpa only [norm_sub_rev] using hnorm
  exact tendsto_nhds_unique t₁ t₂
theorem productLaws_holds (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    (hA : UnboundedFunctionalCalculus E) : ProductLaws E where
  real_boundedIntegral g' hg' hb ψ Δ := by
    have hnn : ∀ y, (0 : ℝ) ≤ ‖g' y‖ ^ 2 := fun y => by positivity
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn)
      (hg'.norm.pow_const 2).aestronglyMeasurable, Measure.real,
      hE.diagMeasure_eq g' hg' hb ψ Δ]
    congr 1
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  real_value ψ Δ Δ' := by
    have h := diagMeasure_real_eq_norm_sq E ψ ⟨Δ.1 ∩ Δ'.1, Δ.2.inter Δ'.2⟩
    rw [diagMeasure_real_eq_norm_sq E _ Δ']
    refine Eq.trans ?_ h.symm
    have hc : (⟨Δ.1 ∩ Δ'.1, Δ.2.inter Δ'.2⟩ : BorelSubsets Y) = ⟨Δ'.1 ∩ Δ.1, Δ'.2.inter Δ.2⟩ :=
      Subtype.ext (inter_comm _ _)
    rw [hc, E.map_inter]
    rfl
  boundedIntegral_mem g g' hg hg' hb ψ hψ := integralOp_mem_integralDom E hE hg hg' hb hψ
  integralValue_boundedIntegral g g' hg hg' hb ψ hψ :=
    integralApply_integralOp_eq E hE hA hg hg' hb hψ
  boundedIntegral_integralValue g g' hg hg' hb ψ hψ hψ' := by
    rw [← integralApply_integralOp_eq E hE hA hg hg' hb hψ]
    exact hA.integralApply_integralOp g g' hg hg' hb ψ hψ'
theorem apply_eq_one_of_isCarriedBy (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    {C : BorelSubsets Y} (hC : E.IsCarriedBy C) : E C = 1 := by
  have h := apply_union_of_disjoint E hE C ⟨C.1ᶜ, C.2.compl⟩ disjoint_compl_right
  have hu : (⟨C.1 ∪ C.1ᶜ, C.2.union C.2.compl⟩ : BorelSubsets Y) = ⟨univ, MeasurableSet.univ⟩ :=
    Subtype.ext (union_compl_self _)
  rw [hu, E.map_univ, show E ⟨C.1ᶜ, C.2.compl⟩ = 0 from hC, add_zero] at h
  exact h.symm
theorem restrictTo_isSpectralMeasureLike (E : SpectralMeasure Y H)
    (hE : BoundedFunctionalCalculus E) {C : BorelSubsets Y} (hC : E.IsCarriedBy C) :
    IsSpectralMeasureLike (E.restrictTo C) where
  isStarProjection Δ := E.isStarProjection _
  map_univ := by
    have h : (⟨Subtype.val '' (univ : Set C.1), C.2.subtype_image MeasurableSet.univ⟩ :
        BorelSubsets Y) = C :=
      Subtype.ext (show Subtype.val '' (univ : Set C.1) = C.1 by
        rw [image_univ]; exact Subtype.range_coe)
    show E ⟨Subtype.val '' (univ : Set C.1), C.2.subtype_image MeasurableSet.univ⟩ = 1
    rw [h]
    exact apply_eq_one_of_isCarriedBy E hE hC
  map_inter Δ Δ' := by
    have h : (⟨Subtype.val '' (Δ.1 ∩ Δ'.1), C.2.subtype_image (Δ.2.inter Δ'.2)⟩ :
        BorelSubsets Y) =
        ⟨Subtype.val '' Δ.1 ∩ Subtype.val '' Δ'.1,
          (C.2.subtype_image Δ.2).inter (C.2.subtype_image Δ'.2)⟩ :=
      Subtype.ext (image_inter Subtype.val_injective)
    show E ⟨Subtype.val '' (Δ.1 ∩ Δ'.1), C.2.subtype_image (Δ.2.inter Δ'.2)⟩ = _
    rw [h]
    exact E.map_inter ⟨Subtype.val '' Δ.1, C.2.subtype_image Δ.2⟩
      ⟨Subtype.val '' Δ'.1, C.2.subtype_image Δ'.2⟩
  countablyAdditive ψ Δ hd := by
    have h := E.countablyAdditive ψ
      (fun k => ⟨Subtype.val '' (Δ k).1, C.2.subtype_image (Δ k).2⟩)
      fun k l hkl => (disjoint_image_iff Subtype.val_injective).mpr (hd hkl)
    have hu : (⟨Subtype.val '' ⋃ k, (Δ k).1,
        C.2.subtype_image (MeasurableSet.iUnion fun k => (Δ k).2)⟩ : BorelSubsets Y) =
        ⟨⋃ k, Subtype.val '' (Δ k).1,
          MeasurableSet.iUnion fun k => C.2.subtype_image (Δ k).2⟩ :=
      Subtype.ext (image_iUnion)
    show HasSum _ ⟪ψ, E ⟨Subtype.val '' ⋃ k, (Δ k).1,
        C.2.subtype_image (MeasurableSet.iUnion fun k => (Δ k).2)⟩ ψ⟫_ℂ
    rw [hu]
    exact h
theorem pushforwardAndSupportLaws_holds (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    (hI : PushforwardProperties E) : PushforwardAndSupportLaws E where
  scalarMeasure_image := hI.diagMeasure_pushforward
  integral_image hn' hY' κ hκ g'' hg'' := by
    have h := hI.integral_pushforward hn' hY' κ hκ g'' hg''
    exact ⟨h.1, fun ψ hψ => h.2 ψ (h.1 ▸ hψ)⟩
  value_carrier C hC := apply_eq_one_of_isCarriedBy E hE hC
  value_inter_carrier C Δ hC := by
    rw [E.map_inter, apply_eq_one_of_isCarriedBy E hE hC, mul_one]
  restriction C hC := restrictTo_isSpectralMeasureLike E hE hC
omit [CompleteSpace H] in
theorem unboundedOp_ext {A B : HilbertSpaceBasics.UnboundedOp H}
    (h : ∀ ψ, ψ ∈ A.domain ↔ ψ ∈ B.domain)
    (hv : ∀ (ψ : H) (ha : ψ ∈ A.domain) (hb : ψ ∈ B.domain), A ⟨ψ, ha⟩ = B ⟨ψ, hb⟩) : A = B := LinearPMap.ext (Submodule.ext h) fun x hx hy => hv x hx hy
theorem isDiagonalIntegral_integralOp (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    {g : Y → ℂ} (hg : Measurable g) (hb : IsBoundedFn g) :
    E.IsDiagonalIntegral g (E.integralOp g) :=
  Classical.epsilon_spec (hE.existsUnique_op g hg hb).exists
section UnitaryConjugation
variable {H' : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
def linearIsometryEquivOfUnitary {V : H →ₗ[ℂ] H'} (hV : OperatorTransport.IsUnitaryMap V) :
    H ≃ₗᵢ[ℂ] H' :=
  hV.toLinearEquiv.isometryOfInner hV.inner_map_map
def conjCLM (U : H ≃ₗᵢ[ℂ] H') (T : H →L[ℂ] H) : H' →L[ℂ] H' :=
  U.toLinearIsometry.toContinuousLinearMap.comp
    (T.comp U.symm.toLinearIsometry.toContinuousLinearMap)
omit [CompleteSpace H] [CompleteSpace H'] in
theorem conjCLM_apply (U : H ≃ₗᵢ[ℂ] H') (T : H →L[ℂ] H) (χ : H') :
    conjCLM U T χ = U (T (U.symm χ)) := rfl
omit [CompleteSpace H] [CompleteSpace H'] in
theorem conjCLM_map (U : H ≃ₗᵢ[ℂ] H') (T : H →L[ℂ] H) (ψ : H) :
    conjCLM U T (U ψ) = U (T ψ) := by
  rw [conjCLM_apply, U.symm_apply_apply]
def unitaryConjMeasure (E : SpectralMeasure Y H) (U : H ≃ₗᵢ[ℂ] H') : SpectralMeasure Y H' where
  one_le_dimension := E.one_le_dimension
  measurableSet_carrier := E.measurableSet_carrier
  toFun Δ := conjCLM U (E Δ)
  isStarProjection Δ := by
    refine ⟨?_, ?_⟩
    · refine ContinuousLinearMap.ext fun χ => ?_
      have hi : E Δ (E Δ (U.symm χ)) = E Δ (U.symm χ) :=
        congrArg (fun T : H →L[ℂ] H => T (U.symm χ)) (E.isStarProjection Δ).isIdempotentElem.eq
      show conjCLM U (E Δ) (conjCLM U (E Δ) χ) = conjCLM U (E Δ) χ
      simp only [conjCLM_apply, U.symm_apply_apply, hi]
    · refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_
      obtain ⟨a, rfl⟩ := U.surjective x
      obtain ⟨b, rfl⟩ := U.surjective y
      show ⟪conjCLM U (E Δ) (U a), U b⟫_ℂ = ⟪U a, conjCLM U (E Δ) (U b)⟫_ℂ
      rw [conjCLM_map, conjCLM_map, U.inner_map_map, U.inner_map_map, inner_apply_left_eq]
  map_univ := by
    refine ContinuousLinearMap.ext fun χ => ?_
    simp [conjCLM_apply, E.map_univ]
  map_inter Δ Δ' := by
    refine ContinuousLinearMap.ext fun χ => ?_
    show conjCLM U (E _) χ = conjCLM U (E Δ) (conjCLM U (E Δ') χ)
    simp only [conjCLM_apply, U.symm_apply_apply, E.map_inter]
    rfl
  countablyAdditive ψ Δ hd := by
    obtain ⟨a, rfl⟩ := U.surjective ψ
    have h := E.countablyAdditive a Δ hd
    have hr : ∀ D : BorelSubsets Y, ⟪U a, conjCLM U (E D) (U a)⟫_ℂ = ⟪a, E D a⟫_ℂ := fun D => by
      rw [conjCLM_map, U.inner_map_map]
    simp only [hr]
    exact h
theorem unitaryConjMeasure_apply (E : SpectralMeasure Y H) (U : H ≃ₗᵢ[ℂ] H')
    (Δ : BorelSubsets Y) (ψ : H) : unitaryConjMeasure E U Δ (U ψ) = U (E Δ ψ) :=
  conjCLM_map U (E Δ) ψ
theorem diagMeasure_unitaryConjMeasure (E : SpectralMeasure Y H) (U : H ≃ₗᵢ[ℂ] H') (ψ : H) :
    (unitaryConjMeasure E U).diagMeasure (U ψ) = E.diagMeasure ψ :=
  Measure.ext fun s hs => by
    have h₁ := (unitaryConjMeasure E U).diagMeasure_apply (U ψ) ⟨s, hs⟩
    have h₂ := E.diagMeasure_apply ψ ⟨s, hs⟩
    rw [unitaryConjMeasure_apply, U.norm_map] at h₁
    exact h₁.trans h₂.symm
theorem integralOp_unitaryConjMeasure (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    (U : H ≃ₗᵢ[ℂ] H') (hF : BoundedFunctionalCalculus (unitaryConjMeasure E U)) {g : Y → ℂ}
    (hg : Measurable g) (hb : IsBoundedFn g) (ψ : H) :
    (unitaryConjMeasure E U).integralOp g (U ψ) = U (E.integralOp g ψ) := by
  have hdiag : (unitaryConjMeasure E U).IsDiagonalIntegral g (conjCLM U (E.integralOp g)) := by
    intro χ
    obtain ⟨a, rfl⟩ := U.surjective χ
    rw [conjCLM_map, U.inner_map_map, diagMeasure_unitaryConjMeasure]
    exact isDiagonalIntegral_integralOp E hE hg hb a
  have h := (hF.existsUnique_op g hg hb).unique
    (isDiagonalIntegral_integralOp _ hF hg hb) hdiag
  rw [h, conjCLM_map]
theorem mem_integralDom_unitaryConjMeasure (E : SpectralMeasure Y H) (U : H ≃ₗᵢ[ℂ] H')
    (g : Y → ℂ) (ψ : H) :
    U ψ ∈ (unitaryConjMeasure E U).integralDom g ↔ ψ ∈ E.integralDom g := by
  show (∫⁻ y, ‖g y‖ₑ ^ 2 ∂(unitaryConjMeasure E U).diagMeasure (U ψ) < ∞) ↔
    ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure ψ < ∞
  rw [diagMeasure_unitaryConjMeasure]
theorem integralApply_unitaryConjMeasure (E : SpectralMeasure Y H)
    (hE : BoundedFunctionalCalculus E) (hA : UnboundedFunctionalCalculus E) (U : H ≃ₗᵢ[ℂ] H')
    (hF : BoundedFunctionalCalculus (unitaryConjMeasure E U))
    (hAF : UnboundedFunctionalCalculus (unitaryConjMeasure E U)) {g : Y → ℂ} (hg : Measurable g)
    {ψ : H} (hψ : ψ ∈ E.integralDom g) :
    (unitaryConjMeasure E U).integralApply g (U ψ) = U (E.integralApply g ψ) := by
  have t₁ := hAF.tendsto_truncate g hg (U ψ)
    ((mem_integralDom_unitaryConjMeasure E U g ψ).mpr hψ)
  have t₂ := (U.continuous.tendsto _).comp (hA.tendsto_truncate g hg ψ hψ)
  refine tendsto_nhds_unique t₁ (t₂.congr fun k => ?_)
  exact (integralOp_unitaryConjMeasure E hE U hF (measurable_truncate hg k)
    (isBoundedFn_truncate g k) ψ).symm
theorem unitaryConjugationLaw_holds (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    (hA : UnboundedFunctionalCalculus E) {V : H →ₗ[ℂ] H'} (hV : OperatorTransport.IsUnitaryMap V)
    (hF : BoundedFunctionalCalculus (unitaryConjMeasure E (linearIsometryEquivOfUnitary hV)))
    (hAF : UnboundedFunctionalCalculus (unitaryConjMeasure E (linearIsometryEquivOfUnitary hV))) :
    UnitaryConjugationLaw E hV := by
  set U := linearIsometryEquivOfUnitary hV with hU
  refine ⟨unitaryConjMeasure E U, fun Δ => ?_, fun ψ => ?_, fun g hg => ?_⟩
  · refine LinearMap.ext fun χ => ?_
    rfl
  · exact diagMeasure_unitaryConjMeasure E U ψ
  · have hI := isSpectralIntegralOf_spectralIntegralOp E hA hg
    have hI' := isSpectralIntegralOf_spectralIntegralOp _ hAF hg
    refine unboundedOp_ext (fun χ => ?_) fun χ ha hb => ?_
    · obtain ⟨a, rfl⟩ := U.surjective χ
      rw [hI'.1, mem_integralDom_unitaryConjMeasure, ← hI.1]
      constructor
      · intro h
        exact Submodule.mem_map_of_mem h
      · rintro ⟨b, hb, hab⟩
        have : b = a := U.injective hab
        rwa [← this]
    · obtain ⟨a, haA, rfl⟩ := hb
      have h₁ := hI'.2 ⟨_, ha⟩
      have h₂ := OperatorTransport.conjOp_apply hV (spectralIntegralOp E g) ⟨a, haA⟩
      refine h₁.trans (Eq.trans ?_ h₂.symm)
      show (unitaryConjMeasure E U).integralApply g (U a) = _
      rw [integralApply_unitaryConjMeasure E hE hA U hF hAF hg ((hI.1 a).mp haA), hI.2 ⟨a, haA⟩]
      rfl
end UnitaryConjugation
theorem isSelfAdjointUnbounded_spectralIntegralOp (E : SpectralMeasure Y H)
    (hA : UnboundedFunctionalCalculus E) {g : Y → ℂ} (hg : Measurable g) (hr : IsRealValued g) :
    OperatorTransport.IsSelfAdjointUnbounded (spectralIntegralOp E g) := by
  have hI := isSpectralIntegralOf_spectralIntegralOp E hA hg
  obtain ⟨hdense, hadj⟩ := hA.isSelfAdjoint g hg hr (spectralIntegralOp E g)
    ⟨Set.ext hI.1, hI.2⟩
  refine ⟨hdense, fun φ χ => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨hφ, rfl⟩ ψ
    exact hadj.2 ⟨φ, hφ⟩ ψ
  · have hφ := (hadj.1 φ).mpr ⟨χ, h⟩
    refine ⟨hφ, ?_⟩
    refine hdense.eq_of_inner_left ℂ fun v hv => ?_
    rw [← (hadj.2 ⟨φ, hφ⟩ ⟨v, hv⟩)]
    exact h ⟨v, hv⟩
theorem realFunctionLaws_holds (E : SpectralMeasure Y H) (hA : UnboundedFunctionalCalculus E)
    (hL : ∀ F : SpectralMeasure YangMills.Construction.SpectralTheorem.RealLineSet H,
      UnboundedFunctionalCalculus F) (hI : PushforwardProperties E) : RealFunctionLaws E where
  isSelfAdjoint g hg hr := isSelfAdjointUnbounded_spectralIntegralOp E hA hg hr
  eq_integral_lineImage g hg hr := by
    have hgr : Measurable fun y => (g y).re := Complex.measurable_re.comp hg
    have hlm : Measurable coordVar :=
      Complex.measurable_ofReal.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)
    set κ : Y → YangMills.Construction.SpectralTheorem.RealLineSet :=
      fun y => ⟨fun _ => (g y).re, mem_univ _⟩ with hκdef
    have hκ : Measurable κ := Measurable.subtype_mk (measurable_pi_iff.mpr fun _ => hgr)
    have hcomp : coordVar ∘ κ = g := funext fun y => by
      refine Complex.ext ?_ ?_
      · simp [coordVar, hκdef]
      · simpa [coordVar, hκdef] using (hr y).symm
    have hS := hI.integral_pushforward le_rfl MeasurableSet.univ κ hκ coordVar hlm
    rw [hcomp] at hS
    have hLI : pushforwardToLine E (fun y => (g y).re) hgr =
        E.pushforward le_rfl MeasurableSet.univ κ hκ := rfl
    rw [hLI]
    have i₁ := isSpectralIntegralOf_spectralIntegralOp E hA hg
    have i₂ := isSpectralIntegralOf_spectralIntegralOp
      (E.pushforward le_rfl MeasurableSet.univ κ hκ) (hL _) hlm
    refine unboundedOp_ext (fun ψ => ?_) fun ψ ha hb => ?_
    · rw [i₁.1, i₂.1, hS.1]
    · rw [i₁.2 ⟨ψ, ha⟩, i₂.2 ⟨ψ, hb⟩]
      exact (hS.2 ψ ((i₁.1 ψ).mp ha)).symm
  isNonnegative g C hg hr hC h := by
    intro ψ
    have hI' := isSpectralIntegralOf_spectralIntegralOp E hA hg
    have hψ := (hI'.1 ψ).mp ψ.2
    rw [hI'.2 ψ, hA.inner_eq g hg ψ hψ]
    have hae : g =ᵐ[E.diagMeasure ψ] fun y => (((g y).re : ℝ) : ℂ) :=
      ae_of_all _ fun y => Complex.ext (by simp) (by simpa using hr y)
    rw [integral_congr_ae hae, integral_complex_ofReal]
    refine Complex.zero_le_real.mpr (integral_nonneg_of_ae ?_)
    filter_upwards [ae_mem_of_isCarriedBy E hC ψ] with y hy
    exact (Complex.le_def.mp (h y hy)).1
theorem composedMeasureLaws_holds (hU : MeasureUniqueness.UniquenessAndIntegral)
    (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E) (hM : MeasureLaws E) :
    ComposedMeasureLaws E where
  isComplexMeasure B φ ψ := by
    have h : (fun Δ : BorelSubsets Y => ⟪φ, B (E Δ ψ)⟫_ℂ) =
        E.matrixCoeff (ContinuousLinearMap.adjoint B φ) ψ :=
      funext fun Δ => (ContinuousLinearMap.adjoint_inner_left B _ _).symm
    rw [h]
    exact hM.isComplexMeasure _ _
  integral_eq B φ ψ g hg hb := by
    have h : (fun Δ : BorelSubsets Y => ⟪φ, B (E Δ ψ)⟫_ℂ) =
        E.matrixCoeff (ContinuousLinearMap.adjoint B φ) ψ :=
      funext fun Δ => (ContinuousLinearMap.adjoint_inner_left B _ _).symm
    rw [h, ← inner_integralOp_eq_integralOf hU E hE hg hb, ContinuousLinearMap.adjoint_inner_left]
theorem calculusTheorem_holds
    (h₁ : YangMills.Construction.SpectralTheory.BoundedBorelCalculus.BoundedBorelCalculusHolds)
    (h₂ : StrongConvergenceHolds)
    (h₃ : YangMills.Construction.SpectralTheory.CommutationWithBoundedIntegrals.CommutesWithBoundedIntegralsHolds)
    (h₄ : UnboundedFunctionalCalculusHolds)
    (h₅ : SpectralPushforwardTheorem)
    (h₆ : MeasureUniqueness.UniquenessAndIntegral) : CalculusTheorem := by
  intro H _ _ _ n Y E
  have hE := h₁ H n Y E
  have hA := h₄ H n Y E
  have hI := h₅ H n Y E
  have hM := measureLaws_holds h₆ E hE
  exact ⟨hM, boundedCalculusLaws_holds h₆ E hE (h₂ H n Y E) (h₃ H n Y E) hA,
    unboundedCalculusLaws_holds E hE hA, productLaws_holds E hE hA,
    pushforwardAndSupportLaws_holds E hE hI,
    fun H' _ _ _ V hV => unitaryConjugationLaw_holds E hE hA hV (h₁ H' n Y _) (h₄ H' n Y _),
    realFunctionLaws_holds E hA (h₄ H 1 _) hI, composedMeasureLaws_holds h₆ E hE hM⟩
end YangMills.Construction.SpectralMeasureCalculus
