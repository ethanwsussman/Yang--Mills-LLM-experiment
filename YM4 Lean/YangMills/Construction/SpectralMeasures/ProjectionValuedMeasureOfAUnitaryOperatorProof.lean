import YangMills.Construction.EuclideanBorel.PVMFromScalarMeasures
import YangMills.Construction.SpectralMeasures.ProjectionValuedMeasureOfAUnitaryOperator
import YangMills.Construction.SpectralMeasures.UniquenessOfComplexMeasures
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate CompactlySupported
noncomputable section
namespace YangMills.Construction.SpectralMeasures.UnitaryOperatorPVM
open YangMills.Construction.EuclideanBorel
open YangMills.Construction.FormsOperators (Commutes UnitaryMap)
def toComplex (y : Space 2) : ℂ :=
  (y 0 : ℂ) + Complex.I * (y 1 : ℂ)
theorem norm_toComplex (y : Space 2) : ‖toComplex y‖ = ‖y‖ := by
  have h : ‖toComplex y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
    simp [toComplex]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
theorem toComplex_ne_zero {y : Space 2} (hy : y ∈ planeUnitCircle) :
    toComplex y ≠ 0 := by
  intro h
  have h1 := norm_toComplex y
  rw [h, norm_zero] at h1
  have h2 : ‖y‖ = 1 := hy
  linarith
theorem circleChar_of_mem (k : ℤ) {y : Space 2} (hy : y ∈ planeUnitCircle) :
    circleChar k y = toComplex y ^ k :=
  Set.indicator_of_mem hy _
theorem circleChar_of_not_mem (k : ℤ) {y : Space 2} (hy : y ∉ planeUnitCircle) :
    circleChar k y = 0 :=
  Set.indicator_of_notMem hy _
theorem circleChar_add (k j : ℤ) :
    circleChar (k + j) = fun y => circleChar k y * circleChar j y := by
  funext y
  by_cases hy : y ∈ planeUnitCircle
  · rw [circleChar_of_mem _ hy, circleChar_of_mem _ hy, circleChar_of_mem _ hy,
      zpow_add₀ (toComplex_ne_zero hy)]
  · simp [circleChar_of_not_mem _ hy]
theorem circleChar_neg (k : ℤ) :
    circleChar (-k) = fun y => conj (circleChar k y) := by
  funext y
  by_cases hy : y ∈ planeUnitCircle
  · rw [circleChar_of_mem _ hy, circleChar_of_mem _ hy, map_zpow₀]
    have h : ‖toComplex y‖ = 1 := (norm_toComplex y).trans hy
    rw [← Complex.inv_eq_conj h, inv_zpow']
  · simp [circleChar_of_not_mem _ hy]
theorem circleChar_zero :
    circleChar 0 = planeUnitCircle.indicator fun _ => (1 : ℂ) := by
  simp [circleChar]
def angleToCircle (θ : ℝ) : Space 2 :=
  WithLp.toLp 2 ![Real.cos θ, Real.sin θ]
theorem angleToCircle_mem (θ : ℝ) : angleToCircle θ ∈ planeUnitCircle := by
  have h : ‖toComplex (angleToCircle θ)‖ = ‖angleToCircle θ‖ := norm_toComplex _
  have h2 : toComplex (angleToCircle θ) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I]
    simp [toComplex, angleToCircle, mul_comm]
  show ‖angleToCircle θ‖ = 1
  rw [← h, h2, Complex.norm_exp_ofReal_mul_I]
theorem toComplex_angleToCircle (θ : ℝ) :
    toComplex (angleToCircle θ) = Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I]
  simp [toComplex, angleToCircle, mul_comm]
theorem circleChar_injective : Function.Injective circleChar := by
  intro k j hkj
  by_contra hne
  set θ : ℝ := Real.pi / ((k - j : ℤ) : ℝ) with hθ
  have hy := angleToCircle_mem θ
  have h1 : circleChar (k + -j) (angleToCircle θ) = circleChar 0 (angleToCircle θ) := by
    rw [circleChar_add, hkj, ← add_neg_cancel j, circleChar_add]
  rw [circleChar_of_mem _ hy, circleChar_of_mem _ hy, toComplex_angleToCircle,
    zpow_zero, ← sub_eq_add_neg, ← Complex.exp_int_mul] at h1
  have h2 : (((k - j : ℤ) : ℂ)) * ((θ : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
    have hm' : (((k - j : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
    rw [hθ]
    push_cast
    push_cast at hm'
    field_simp
  rw [h2, Complex.exp_pi_mul_I] at h1
  norm_num at h1
theorem isBoundedMeasurableFn_circleChar (k : ℤ) : IsBoundedMeasurableFn (circleChar k) := by apply _root_.YangMills.Construction.EuclideanBorel.MeasureUniqueness.isBoundedMeasurableFn_circleChar <;> assumption
theorem isStarClosedFamilyOn_range_circleChar :
    IsStarClosedFamilyOn planeUnitCircleBorel (Set.range circleChar) where
  eq_zero_off := by
    rintro _ ⟨k, rfl⟩ y hy
    exact circleChar_of_not_mem k hy
  indicator_one_mem := ⟨0, circleChar_zero⟩
  mul_mem := by
    rintro _ ⟨k, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨k + j, circleChar_add k j⟩
  star_mem := by
    rintro _ ⟨k, rfl⟩
    exact ⟨-k, circleChar_neg k⟩
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def powOp (U : UnitaryMap H H) (k : ℤ) : H →L[ℂ] H :=
  ((U ^ k : UnitaryMap H H).toContinuousLinearEquiv : H →L[ℂ] H)
theorem powOp_apply (U : UnitaryMap H H) (k : ℤ) (x : H) :
    powOp U k x = (U ^ k : UnitaryMap H H) x := rfl
theorem powOp_zero (U : UnitaryMap H H) : powOp U 0 = 1 := by
  ext x
  simp [powOp_apply]
theorem powOp_add (U : UnitaryMap H H) (k j : ℤ) :
    powOp U (k + j) = powOp U k * powOp U j := by
  ext x
  simp [powOp_apply, zpow_add]
theorem powOp_one (U : UnitaryMap H H) :
    powOp U 1 = (U.toContinuousLinearEquiv : H →L[ℂ] H) := by
  ext x
  simp [powOp_apply]
theorem star_powOp_one (U : UnitaryMap H H) :
    star (powOp U 1) = powOp U (-1) := by
  rw [powOp_one]
  have h : star (U.toContinuousLinearEquiv : H →L[ℂ] H) = (U.symm : H →L[ℂ] H) :=
    U.star_eq_symm
  rw [h]
  ext x
  simp [powOp_apply, zpow_neg]
theorem inner_powOp (U : UnitaryMap H H) (k : ℤ) (φ ψ : H) :
    ⟪φ, powOp U k ψ⟫_ℂ = ⟪powOp U (-k) φ, ψ⟫_ℂ := by
  have h : φ = (U ^ k : UnitaryMap H H) ((U ^ (-k) : UnitaryMap H H) φ) := by
    have h1 : (U ^ k * U ^ (-k) : UnitaryMap H H) = 1 := by
      rw [← zpow_add, add_neg_cancel, zpow_zero]
    exact (congrArg (fun e : UnitaryMap H H => e φ) h1).symm
  conv_lhs => rw [h]
  rw [powOp_apply, powOp_apply, LinearIsometryEquiv.inner_map_map]
def charToPow (U : UnitaryMap H H) : Set.range circleChar → H →L[ℂ] H :=
  fun u => powOp U (Classical.choose u.2)
theorem charToPow_eq (U : UnitaryMap H H) (u : Set.range circleChar) {k : ℤ}
    (h : u.1 = circleChar k) : charToPow U u = powOp U k := by
  have hk : Classical.choose u.2 = k :=
    circleChar_injective ((Classical.choose_spec u.2).trans h)
  rw [charToPow, hk]
theorem isStarHomOnFamily_charToPow (U : UnitaryMap H H) :
    IsStarHomOnFamily planeUnitCircleBorel (Set.range circleChar)
      (charToPow U) where
  map_indicator_one := by
    intro w hw
    rw [charToPow_eq U w (hw.trans circleChar_zero.symm), powOp_zero]
  map_mul := by
    rintro ⟨_, k, rfl⟩ ⟨_, j, rfl⟩ w hw
    rw [charToPow_eq U w (hw.trans (circleChar_add k j).symm),
      charToPow_eq U ⟨_, k, rfl⟩ rfl, charToPow_eq U ⟨_, j, rfl⟩ rfl, powOp_add]
  map_star := by
    rintro ⟨_, k, rfl⟩ w hw φ ψ
    rw [charToPow_eq U w (hw.trans (circleChar_neg k).symm),
      charToPow_eq U ⟨_, k, rfl⟩ rfl, inner_powOp]
section Functional
variable {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S] [MeasurableSpace S]
  [BorelSpace S]
def realToComplex (f : C(S, ℝ)) : C(S, ℂ) :=
  ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
theorem realToComplex_apply (f : C(S, ℝ)) (z : S) : realToComplex f z = (f z : ℂ) := rfl
theorem im_inner_realToComplex (Φ : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : H) (f : C(S, ℝ)) :
    (⟪ψ, Φ (realToComplex f) ψ⟫_ℂ).im = 0 := by
  have hstar : star (realToComplex f) = realToComplex f := by
    ext z
    simp [realToComplex_apply]
  have hA : star (Φ (realToComplex f)) = Φ (realToComplex f) := by
    rw [← map_star, hstar]
  have h1 : ⟪ψ, Φ (realToComplex f) ψ⟫_ℂ = ⟪Φ (realToComplex f) ψ, ψ⟫_ℂ := by
    conv_lhs => rw [← hA]
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have h2 : conj ⟪ψ, Φ (realToComplex f) ψ⟫_ℂ = ⟪Φ (realToComplex f) ψ, ψ⟫_ℂ :=
    inner_conj_symm _ _
  rw [← h2] at h1
  exact Complex.conj_eq_iff_im.1 h1.symm
theorem re_inner_realToComplex_nonneg (Φ : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : H)
    (f : C(S, ℝ)) (hf : 0 ≤ f) : 0 ≤ (⟪ψ, Φ (realToComplex f) ψ⟫_ℂ).re := by
  let g : C(S, ℂ) := realToComplex ⟨fun z => Real.sqrt (f z), by fun_prop⟩
  have hg : realToComplex f = star g * g := by
    ext z
    have hz : 0 ≤ f z := hf z
    have h : ((Real.sqrt (f z) : ℝ) : ℂ) * ((Real.sqrt (f z) : ℝ) : ℂ) = (f z : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hz]
    simpa [g, realToComplex_apply] using h.symm
  rw [hg, map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ)
def diagFunctional (Φ : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : H) : C_c(S, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => (⟪ψ, Φ (realToComplex f.toContinuousMap) ψ⟫_ℂ).re
      map_add' := by
        intro f g
        have h : realToComplex (f + g).toContinuousMap =
            realToComplex f.toContinuousMap + realToComplex g.toContinuousMap := by
          ext z
          simp [realToComplex_apply]
        rw [h, map_add, add_apply, inner_add_right, Complex.add_re]
      map_smul' := by
        intro c f
        have h : realToComplex (c • f).toContinuousMap =
            (c : ℂ) • realToComplex f.toContinuousMap := by
          ext z
          simp [realToComplex_apply]
        rw [h, map_smul, smul_apply, inner_smul_right]
        simp }
    (fun f hf => re_inner_realToComplex_nonneg Φ ψ f.toContinuousMap (fun z => hf z))
theorem exists_finiteMeasure_of_starAlgHom (Φ : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : H) :
    ∃ μ : Measure S, IsFiniteMeasure μ ∧ ∀ g : C(S, ℂ), ⟪ψ, Φ g ψ⟫_ℂ = ∫ z, g z ∂μ := by
  let μ : Measure S := RealRMK.rieszMeasure (diagFunctional Φ ψ)
  have hreal : ∀ f : C(S, ℝ), ∫ z, f z ∂μ = (⟪ψ, Φ (realToComplex f) ψ⟫_ℂ).re := by
    intro f
    exact RealRMK.integral_rieszMeasure (diagFunctional Φ ψ)
      (CompactlySupportedContinuousMap.continuousMapEquiv f)
  have hfin : IsFiniteMeasure μ := inferInstance
  refine ⟨μ, hfin, fun g => ?_⟩
  let a : C(S, ℝ) := ⟨fun z => (g z).re, by fun_prop⟩
  let b : C(S, ℝ) := ⟨fun z => (g z).im, by fun_prop⟩
  have hg : g = realToComplex a + Complex.I • realToComplex b := by
    ext z
    simp [a, b, realToComplex_apply, mul_comm Complex.I, Complex.re_add_im]
  have hint : Integrable (fun z => g z) μ :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsplit := integral_re_add_im (𝕜 := ℂ) hint
  have ha : ⟪ψ, Φ (realToComplex a) ψ⟫_ℂ = ((∫ z, a z ∂μ : ℝ) : ℂ) := by
    rw [hreal a]
    exact Complex.ext (by simp) (by simpa using im_inner_realToComplex Φ ψ a)
  have hb : ⟪ψ, Φ (realToComplex b) ψ⟫_ℂ = ((∫ z, b z ∂μ : ℝ) : ℂ) := by
    rw [hreal b]
    exact Complex.ext (by simp) (by simpa using im_inner_realToComplex Φ ψ b)
  have hlhs : ⟪ψ, Φ g ψ⟫_ℂ =
      ⟪ψ, Φ (realToComplex a) ψ⟫_ℂ + Complex.I * ⟪ψ, Φ (realToComplex b) ψ⟫_ℂ := by
    conv_lhs => rw [hg]
    rw [map_add, map_smul, add_apply, smul_apply,
      inner_add_right, inner_smul_right]
  rw [hlhs, ha, hb, ← hsplit]
  simp [a, b, mul_comm Complex.I]
end Functional
theorem powOp_one_mem_unitary (U : UnitaryMap H H) :
    powOp U 1 ∈ unitary (H →L[ℂ] H) := by
  rw [Unitary.mem_iff, star_powOp_one, ← powOp_add, ← powOp_add]
  simp [powOp_zero]
theorem exists_diagonal_measure (U : UnitaryMap H H) (ψ : H) :
    ∃ μ : Measure (Space 2), IsFiniteMeasure μ ∧
      IsSupportedOn (fun Δ => ((μ.real Δ.1 : ℝ) : ℂ)) planeUnitCircleBorel ∧
      ∀ k : ℤ, ⟪ψ, powOp U k ψ⟫_ℂ = ∫ y, circleChar k y ∂μ := by
  set T : H →L[ℂ] H := powOp U 1 with hT
  have hu : T ∈ unitary (H →L[ℂ] H) := powOp_one_mem_unitary U
  have hN : IsStarNormal T := isStarNormal_of_mem_unitary hu
  have hnorm : ∀ z : spectrum ℂ T, ‖(z : ℂ)‖ = 1 := fun z => by
    simpa using spectrum.subset_circle_of_unitary hu z.2
  have hne : ∀ z : spectrum ℂ T, (z : ℂ) ≠ 0 := fun z h => by
    have := hnorm z
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have : CompactSpace (spectrum ℂ T) := isCompact_iff_compactSpace.1 (spectrum.isCompact T)
  let Φ : C(spectrum ℂ T, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) := cfcHom hN
  let ζ : C(spectrum ℂ T, ℂ) := (ContinuousMap.id ℂ).restrict (spectrum ℂ T)
  have hζ : Φ ζ = T := cfcHom_id hN
  let g : ℤ → C(spectrum ℂ T, ℂ) := fun k =>
    ⟨fun z => (z : ℂ) ^ k, continuous_subtype_val.zpow₀ k (fun z => Or.inl (hne z))⟩
  have hg : ∀ k, Φ (g k) = powOp U k := by
    intro k
    induction k using Int.induction_on with
    | zero =>
      have h : g 0 = 1 := by
        ext z
        simp [g]
      rw [h, map_one, powOp_zero]
    | succ i ih =>
      have h : g (i + 1) = g i * ζ := by
        ext z
        simp [g, ζ, zpow_add₀ (hne z)]
      rw [h, map_mul, ih, hζ, hT, ← powOp_add]
    | pred i ih =>
      have h : g (-i - 1) = g (-i) * star ζ := by
        ext z
        have hc : conj (z : ℂ) = (z : ℂ)⁻¹ := (Complex.inv_eq_conj (hnorm z)).symm
        simp [g, ζ, hc, sub_eq_add_neg, zpow_add₀ (hne z)]
      rw [h, map_mul, ih, map_star, hζ, hT, star_powOp_one, ← powOp_add,
        sub_eq_add_neg]
  let κ : spectrum ℂ T → Space 2 := fun z => WithLp.toLp 2 ![(z : ℂ).re, (z : ℂ).im]
  have hκc : Continuous κ := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    fin_cases i
    · exact Complex.continuous_re.comp continuous_subtype_val
    · exact Complex.continuous_im.comp continuous_subtype_val
  have hκ : ∀ z, toComplex (κ z) = z := fun z => by
    simp [toComplex, κ, mul_comm Complex.I, Complex.re_add_im]
  have hκm : ∀ z, κ z ∈ planeUnitCircle := fun z => by
    show ‖κ z‖ = 1
    rw [← norm_toComplex, hκ, hnorm]
  obtain ⟨μ₀, hfin, hμ₀⟩ := exists_finiteMeasure_of_starAlgHom Φ ψ
  refine ⟨μ₀.map κ, Measure.isFiniteMeasure_map _ _, ?_, fun k => ?_⟩
  · intro Δ hΔ
    have h : κ ⁻¹' Δ.1 = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      exact fun h => hΔ h (hκm z)
    simp [measureReal_def, Measure.map_apply hκc.measurable Δ.2, h]
  · rw [← hg k, hμ₀ (g k), integral_map hκc.measurable.aemeasurable
      (isBoundedMeasurableFn_circleChar k).1.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (z : ℂ) ^ k = circleChar k (κ z)
    rw [circleChar_of_mem k (hκm z), hκ]
theorem commute_powOp (U : UnitaryMap H H) (B : H →L[ℂ] H)
    (hB : Commutes B (U.toContinuousLinearEquiv : H →L[ℂ] H)) (k : ℤ) :
    B * powOp U k = powOp U k * B := by
  have h1 : Commute B (powOp U 1) := by
    rw [powOp_one]
    exact hB
  have hl : powOp U (-1) * powOp U 1 = 1 := by
    rw [← powOp_add]
    simp [powOp_zero]
  have hr : powOp U 1 * powOp U (-1) = 1 := by
    rw [← powOp_add]
    simp [powOp_zero]
  have h2 : Commute B (powOp U (-1)) := by
    have hc : B * powOp U 1 = powOp U 1 * B := h1
    show B * powOp U (-1) = powOp U (-1) * B
    calc B * powOp U (-1)
        = (powOp U (-1) * powOp U 1) * B * powOp U (-1) := by
          rw [hl, one_mul]
      _ = powOp U (-1) * (powOp U 1 * B) * powOp U (-1) := by
          simp only [mul_assoc]
      _ = powOp U (-1) * (B * powOp U 1) * powOp U (-1) := by rw [hc]
      _ = powOp U (-1) * B * (powOp U 1 * powOp U (-1)) := by
          simp only [mul_assoc]
      _ = powOp U (-1) * B := by rw [hr, mul_one]
  exact show Commute B (powOp U k) from by
    induction k using Int.induction_on with
    | zero =>
      rw [powOp_zero]
      exact Commute.one_right B
    | succ i ih =>
      rw [powOp_add]
      exact ih.mul_right h1
    | pred i ih =>
      rw [sub_eq_add_neg, powOp_add]
      exact ih.mul_right h2
end Operators
theorem existsUnique_of_diagonalMeasures (hMeasures : PVMOfDiagonalMeasuresTheorem)
    (hDetermining : DeterminingFamiliesStatement) : UnitarySpectral.ExistsUnique := by
  intro H _ _ _ U
  have hdet : SeparatesSupportedMeasures planeUnitCircleBorel
      (Set.range circleChar) := by
    intro ν hν hc h
    exact hDetermining.2 ν hν hc (fun k => h _ ⟨k, rfl⟩)
  have hscal : HasSupportedDiagonalMeasures planeUnitCircleBorel (Set.range circleChar)
      (charToPow U) := by
    intro ψ
    obtain ⟨μ, hfin, hc, hμ⟩ := exists_diagonal_measure U ψ
    refine ⟨μ, hfin, hc, ?_⟩
    rintro ⟨_, k, rfl⟩
    rw [charToPow_eq U ⟨_, k, rfl⟩ rfl]
    exact hμ k
  have key := hMeasures 2 (by norm_num) H planeUnitCircleBorel (Set.range circleChar)
    (charToPow U) (by rintro _ ⟨k, rfl⟩; exact isBoundedMeasurableFn_circleChar k)
    isStarClosedFamilyOn_range_circleChar hdet (isStarHomOnFamily_charToPow U) hscal
  have hiff : ∀ E : BorelSubset 2 → H →L[ℂ] H,
      IsPVMRepresenting planeUnitCircleBorel (Set.range circleChar)
        (charToPow U) E ↔ IsUnitarySpectralMeasure U E := by
    intro E
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun k => ?_⟩
      have h := h3 ⟨_, k, rfl⟩
      rw [charToPow_eq U ⟨_, k, rfl⟩ rfl] at h
      exact h
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rintro ⟨_, k, rfl⟩
      rw [charToPow_eq U ⟨_, k, rfl⟩ rfl]
      exact h3 k
  obtain ⟨⟨E, hE, huniq⟩, hcomm⟩ := key
  have hspec : IsUnitarySpectralMeasure U (unitarySpectralMeasure U) :=
    Classical.epsilon_spec ⟨E, (hiff E).1 hE⟩
  refine ⟨⟨E, (hiff E).1 hE, fun E' h => huniq E' ((hiff E').2 h)⟩, hspec, fun B hB Δ => ?_⟩
  refine hcomm _ ((hiff _).2 hspec) B ?_ Δ
  rintro ⟨_, k, rfl⟩
  rw [charToPow_eq U ⟨_, k, rfl⟩ rfl]
  exact commute_powOp U B hB k
end YangMills.Construction.SpectralMeasures.UnitaryOperatorPVM
