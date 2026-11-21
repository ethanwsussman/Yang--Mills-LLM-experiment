import YangMills.Construction.FormsOnATorus.HaarInTheChartOfAHalfSphere
import YangMills.Construction.HoleBesideASecondHole.ASegmentInTheGroupProof
import YangMills.Construction.RunningCouplingSlope.EnergyAtTheLeastFieldHasKernelsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory Set Metric
namespace YangMills.Construction.GaugeCharts
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
namespace HemisphereChart
abbrev QuatCoords : Type := ℝ × imaginaryQuaternions
theorem re_imaginaryQuaternions (w : imaginaryQuaternions) : (w : ℍ[ℝ]).re = 0 := w.2
def quatEquiv : QuatCoords ≃ₗ[ℝ] ℍ[ℝ] where
  toFun p := ((p.1 : ℝ) : ℍ[ℝ]) + (p.2 : ℍ[ℝ])
  map_add' a b := by
    ext <;> simp <;> ring
  map_smul' c a := by
    ext <;> simp
  invFun q := (q.re, imaginaryPart q)
  left_inv p := by
    have h := re_imaginaryQuaternions p.2
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp [h]
    · show ((p.1 : ℝ) : ℍ[ℝ]) + (p.2 : ℍ[ℝ]) - ((((p.1 : ℝ) : ℍ[ℝ]) + (p.2 : ℍ[ℝ])).re : ℍ[ℝ]) = p.2
      ext <;> simp [h]
  right_inv q := by
    show ((q.re : ℝ) : ℍ[ℝ]) + (q - ((q.re : ℝ) : ℍ[ℝ])) = q
    abel
theorem quatEquiv_apply (p : QuatCoords) : quatEquiv p = ((p.1 : ℝ) : ℍ[ℝ]) + (p.2 : ℍ[ℝ]) := rfl
theorem continuous_quatEquiv : Continuous quatEquiv := quatEquiv.toLinearMap.continuous_of_finiteDimensional
theorem continuous_quatEquiv_symm : Continuous quatEquiv.symm :=
  quatEquiv.symm.toLinearMap.continuous_of_finiteDimensional
theorem quaternion_norm_sq (q : ℍ[ℝ]) : ‖q‖ ^ 2 = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 := by
  rw [sq ‖q‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
theorem imaginary_norm_sq (w : imaginaryQuaternions) :
    ‖w‖ ^ 2 = (w : ℍ[ℝ]).imI ^ 2 + (w : ℍ[ℝ]).imJ ^ 2 + (w : ℍ[ℝ]).imK ^ 2 := by apply _root_.YangMills.SharedProofs.p1745 <;> assumption
theorem norm_sq_quatEquiv (p : QuatCoords) : ‖quatEquiv p‖ ^ 2 = p.1 ^ 2 + ‖p.2‖ ^ 2 := by
  rw [quaternion_norm_sq, imaginary_norm_sq, quatEquiv_apply]
  simp [re_imaginaryQuaternions]
  ring
theorem mem_unitary_of_norm_eq_one {q : ℍ[ℝ]} (hq : ‖q‖ = 1) : q ∈ unitary ℍ[ℝ] := by apply _root_.YangMills.Construction.GroupPaths.unitary_mem_of_norm_eq_one <;> assumption
theorem norm_unitQuaternion (g : UnitQuaternion) : ‖((g : UnitQuaternion) : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem star_mul_self_unit (u : UnitQuaternion) : star (u : ℍ[ℝ]) * (u : ℍ[ℝ]) = 1 :=
  (Unitary.mem_iff.mp u.2).1
theorem mul_star_self_unit (u : UnitQuaternion) : (u : ℍ[ℝ]) * star (u : ℍ[ℝ]) = 1 :=
  (Unitary.mem_iff.mp u.2).2
def leftMulEquiv (u : UnitQuaternion) : ℍ[ℝ] ≃ₗ[ℝ] ℍ[ℝ] where
  toFun q := (u : ℍ[ℝ]) * q
  map_add' := mul_add _
  map_smul' c q := by simp
  invFun q := star (u : ℍ[ℝ]) * q
  left_inv q := by simp [← mul_assoc, star_mul_self_unit]
  right_inv q := by simp [← mul_assoc, mul_star_self_unit]
def leftMulCoords (u : UnitQuaternion) : QuatCoords ≃ₗ[ℝ] QuatCoords :=
  (quatEquiv.trans (leftMulEquiv u)).trans quatEquiv.symm
theorem quatEquiv_leftMulCoords (u : UnitQuaternion) (p : QuatCoords) :
    quatEquiv (leftMulCoords u p) = (u : ℍ[ℝ]) * quatEquiv p := by
  simp [leftMulCoords, leftMulEquiv]
theorem norm_quatEquiv_leftMulCoords (u : UnitQuaternion) (p : QuatCoords) :
    ‖quatEquiv (leftMulCoords u p)‖ = ‖quatEquiv p‖ := by
  rw [quatEquiv_leftMulCoords, norm_mul, norm_unitQuaternion, one_mul]
open Classical in
def radialUnit (p : QuatCoords) : UnitQuaternion :=
  if h : quatEquiv p = 0 then 1 else
    ⟨(‖quatEquiv p‖⁻¹ : ℝ) • quatEquiv p, mem_unitary_of_norm_eq_one (by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)])⟩
theorem radialUnit_leftMulCoords (u : UnitQuaternion) {p : QuatCoords} (hp : quatEquiv p ≠ 0) :
    radialUnit (leftMulCoords u p) = u * radialUnit p := by
  have h1 : quatEquiv (leftMulCoords u p) ≠ 0 := by
    intro h
    have := norm_quatEquiv_leftMulCoords u p
    rw [h, norm_zero] at this
    exact hp (norm_eq_zero.mp this.symm)
  apply Subtype.ext
  simp only [radialUnit, dif_neg hp, dif_neg h1, norm_quatEquiv_leftMulCoords]
  simp [quatEquiv_leftMulCoords]
def openShell : Set QuatCoords := {p | 0 < ‖quatEquiv p‖ ∧ ‖quatEquiv p‖ < 1}
theorem isOpen_openShell : IsOpen openShell :=
  (isOpen_lt continuous_const continuous_quatEquiv.norm).inter
    (isOpen_lt continuous_quatEquiv.norm continuous_const)
theorem openShell_nonempty : openShell.Nonempty := by
  refine ⟨quatEquiv.symm ((1 / 2 : ℝ) : ℍ[ℝ]), ?_⟩
  simp only [openShell, mem_setOf_eq, LinearEquiv.apply_symm_apply, Quaternion.norm_coe]
  norm_num
theorem leftMulCoords_preimage_openShell (u : UnitQuaternion) : leftMulCoords u ⁻¹' openShell = openShell := by
  ext p
  simp [openShell, norm_quatEquiv_leftMulCoords]
theorem continuousOn_radialUnit : ContinuousOn radialUnit {p | quatEquiv p ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun p : {p : QuatCoords | quatEquiv p ≠ 0} =>
      (⟨(‖quatEquiv p.1‖⁻¹ : ℝ) • quatEquiv p.1, mem_unitary_of_norm_eq_one (by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr p.2)])⟩ : UnitQuaternion) := by
    refine Continuous.subtype_mk ?_ _
    have hq : Continuous fun p : {p : QuatCoords | quatEquiv p ≠ 0} => quatEquiv p.1 :=
      continuous_quatEquiv.comp continuous_subtype_val
    exact Continuous.smul (Continuous.inv₀ hq.norm fun p => norm_ne_zero_iff.mpr p.2) hq
  convert hc using 1
  funext p
  have : quatEquiv p.1 ≠ 0 := p.2
  simp only [Set.domRestrict_apply, radialUnit, dif_neg this]
variable [MeasurableSpace imaginaryQuaternions] [BorelSpace imaginaryQuaternions]
theorem measurable_radialUnit : Measurable radialUnit := by
  have hs : MeasurableSet {p : QuatCoords | quatEquiv p ≠ 0} :=
    (isOpen_ne_fun continuous_quatEquiv continuous_const).measurableSet
  refine measurable_of_restrict_of_restrict_compl hs ?_ ?_
  · exact (continuousOn_iff_continuous_domRestrict.mp continuousOn_radialUnit).measurable
  · have : ({p : QuatCoords | quatEquiv p ≠ 0}ᶜ).domRestrict radialUnit = fun _ => 1 := by
      funext p
      have h : quatEquiv p.1 = 0 := by simpa using p.2
      simp only [Set.domRestrict_apply, radialUnit, dif_pos h]
    rw [this]
    exact measurable_const
theorem measure_openShell_ne_zero (lam : Measure QuatCoords) [lam.IsAddHaarMeasure] : lam openShell ≠ 0 :=
  (isOpen_openShell.measure_pos lam openShell_nonempty).ne'
theorem measure_openShell_ne_top (lam : Measure QuatCoords) [lam.IsAddHaarMeasure] : lam openShell ≠ ⊤ := by
  have hK : IsCompact (quatEquiv.symm '' closedBall (0 : ℍ[ℝ]) 1) :=
    (isCompact_closedBall _ _).image continuous_quatEquiv_symm
  refine ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono ?_)
  intro p hp
  refine ⟨quatEquiv p, ?_, by simp⟩
  simpa [Metric.mem_closedBall, dist_zero_right] using hp.2.le
theorem measurePreserving_leftMulCoords (lam : Measure QuatCoords) [lam.IsAddHaarMeasure] (u : UnitQuaternion) :
    MeasurePreserving (leftMulCoords u) lam lam := by
  have hc : Continuous (leftMulCoords u) := (leftMulCoords u).toLinearMap.continuous_of_finiteDimensional
  refine ⟨hc.measurable, ?_⟩
  let Lc : QuatCoords ≃L[ℝ] QuatCoords := (leftMulCoords u).toContinuousLinearEquiv
  have hL : lam.map (leftMulCoords u) = lam.map Lc := rfl
  rw [hL]
  have hs := Measure.isAddLeftInvariant_eq_smul (lam.map Lc) lam
  set c := Measure.addHaarScalarFactor (lam.map Lc) lam with hcdef
  have hsh : (lam.map Lc) openShell = lam openShell := by
    rw [Measure.map_apply Lc.continuous.measurable isOpen_openShell.measurableSet]
    exact congrArg lam (leftMulCoords_preimage_openShell u)
  have h1 : (c : ℝ≥0∞) * lam openShell = 1 * lam openShell := by
    rw [one_mul]
    conv_rhs => rw [← hsh, hs]
    rfl
  have hc1 : (c : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj (measure_openShell_ne_zero lam) (measure_openShell_ne_top lam)).mp h1
  have hc2 : c = 1 := by exact_mod_cast hc1
  rw [hs, hc2, one_smul]
theorem lintegral_openShell_radialUnit (lam : Measure QuatCoords) [lam.IsAddHaarMeasure]
    (f : UnitQuaternion → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p in openShell, f (radialUnit p) ∂lam = lam openShell * ∫⁻ g, f g ∂haarUnit := by
  set ν : Measure UnitQuaternion := (lam.restrict openShell).map radialUnit with hν
  have hfin : IsFiniteMeasure (lam.restrict openShell) :=
    ⟨by simpa using (measure_openShell_ne_top lam).lt_top⟩
  have hνf : IsFiniteMeasure ν := by
    rw [hν]
    infer_instance
  have hinv : ν.IsMulLeftInvariant := ⟨fun u => by
    have hm : Measurable fun g : UnitQuaternion => u * g := measurable_const_mul u
    rw [hν, Measure.map_map hm measurable_radialUnit]
    have hae : (fun g : UnitQuaternion => u * g) ∘ radialUnit =ᵐ[lam.restrict openShell]
        radialUnit ∘ leftMulCoords u := by
      refine (ae_restrict_iff' isOpen_openShell.measurableSet).mpr
        (Filter.Eventually.of_forall fun p hp => ?_)
      have : quatEquiv p ≠ 0 := norm_pos_iff.mp hp.1
      simp [radialUnit_leftMulCoords u this]
    rw [Measure.map_congr hae, ← Measure.map_map measurable_radialUnit
      (measurePreserving_leftMulCoords lam u).measurable]
    congr 1
    have := (measurePreserving_leftMulCoords lam u).restrict_preimage isOpen_openShell.measurableSet
    rw [leftMulCoords_preimage_openShell] at this
    exact this.map_eq⟩
  have hs := Measure.isMulInvariant_eq_smul_of_compactSpace ν haarUnit
  set c := Measure.haarScalarFactor ν haarUnit with hcdef
  have hνu : ν univ = lam openShell := by
    rw [hν, Measure.map_apply measurable_radialUnit MeasurableSet.univ]
    simp
  have hcv : (c : ℝ≥0∞) = lam openShell := by
    rw [← hνu]
    conv_rhs => rw [hs]
    rw [Measure.smul_apply, measure_univ]
    simp [ENNReal.smul_def]
  calc ∫⁻ p in openShell, f (radialUnit p) ∂lam = ∫⁻ g, f g ∂ν := by
        rw [hν, lintegral_map hf measurable_radialUnit]
    _ = (c : ℝ≥0∞) * ∫⁻ g, f g ∂haarUnit := by
        conv_lhs => rw [hs]
        rw [lintegral_smul_measure]
        rfl
    _ = _ := by rw [hcv]
def hemisphereHeight (y : imaginaryQuaternions) : ℝ := Real.sqrt (1 - ‖y‖ ^ 2)
theorem hemisphereHeight_pos {y : imaginaryQuaternions} (hy : ‖y‖ < 1) : 0 < hemisphereHeight y :=
  Real.sqrt_pos.mpr (by nlinarith [norm_nonneg y])
theorem hemisphereHeight_sq {y : imaginaryQuaternions} (hy : ‖y‖ < 1) :
    hemisphereHeight y ^ 2 = 1 - ‖y‖ ^ 2 :=
  Real.sq_sqrt (by nlinarith [norm_nonneg y])
def polarMap (p : QuatCoords) : QuatCoords := (p.1 * hemisphereHeight p.2, p.1 • p.2)
theorem quatEquiv_hemisphereHeight (y : imaginaryQuaternions) :
    quatEquiv (hemisphereHeight y, y) = hemispherePoint y := rfl
theorem norm_hemispherePoint {y : imaginaryQuaternions} (hy : ‖y‖ < 1) : ‖hemispherePoint y‖ = 1 := by
  have h := norm_sq_quatEquiv (hemisphereHeight y, y)
  rw [quatEquiv_hemisphereHeight] at h
  simp only at h
  rw [hemisphereHeight_sq hy] at h
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (by rw [h]; ring)
theorem hemisphereUnit_coe {y : imaginaryQuaternions} (hy : ‖y‖ < 1) :
    ((hemisphereUnit y : UnitQuaternion) : ℍ[ℝ]) = hemispherePoint y := by
  simp [hemisphereUnit, dif_pos (mem_unitary_of_norm_eq_one (norm_hemispherePoint hy))]
theorem quatEquiv_polarMap (r : ℝ) (y : imaginaryQuaternions) :
    quatEquiv (polarMap (r, y)) = r • hemispherePoint y := by
  rw [← quatEquiv_hemisphereHeight, ← map_smul]
  rfl
theorem norm_quatEquiv_polarMap {r : ℝ} (hr : 0 < r) {y : imaginaryQuaternions} (hy : ‖y‖ < 1) :
    ‖quatEquiv (polarMap (r, y))‖ = r := by
  rw [quatEquiv_polarMap, norm_smul, norm_hemispherePoint hy, mul_one, Real.norm_eq_abs, abs_of_pos hr]
theorem radialUnit_polarMap {r : ℝ} (hr : 0 < r) {y : imaginaryQuaternions} (hy : ‖y‖ < 1) :
    radialUnit (polarMap (r, y)) = hemisphereUnit y := by
  have hq : quatEquiv (polarMap (r, y)) ≠ 0 := by
    intro h
    have := norm_quatEquiv_polarMap hr hy
    rw [h, norm_zero] at this
    exact hr.ne this
  apply Subtype.ext
  rw [hemisphereUnit_coe hy]
  simp only [radialUnit, dif_neg hq]
  rw [norm_quatEquiv_polarMap hr hy, quatEquiv_polarMap, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
def polarDomain : Set QuatCoords := Ioo 0 1 ×ˢ {y : imaginaryQuaternions | ‖y‖ < 1}
def upperShell : Set QuatCoords := {p | 0 < p.1 ∧ ‖quatEquiv p‖ < 1}
theorem polarMap_image : polarMap '' polarDomain = upperShell := by
  ext p
  constructor
  · rintro ⟨⟨r, y⟩, ⟨⟨hr0, hr1⟩, hy⟩, rfl⟩
    have hy' : ‖y‖ < 1 := hy
    exact ⟨mul_pos hr0 (hemisphereHeight_pos hy'), by rw [norm_quatEquiv_polarMap hr0 hy']; exact hr1⟩
  · rintro ⟨ha, hn⟩
    obtain ⟨a, w⟩ := p
    simp only at ha
    have hsq := norm_sq_quatEquiv (a, w)
    simp only at hsq
    set r := ‖quatEquiv (a, w)‖ with hr
    have hr0 : 0 < r := by
      have : 0 < r ^ 2 := by rw [hsq]; positivity
      exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at this; norm_num at this)
    have hy : ‖r⁻¹ • w‖ ^ 2 = ‖w‖ ^ 2 / r ^ 2 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr0]
      field_simp
    have hy1 : ‖r⁻¹ • w‖ < 1 := by
      have : ‖r⁻¹ • w‖ ^ 2 < 1 := by
        rw [hy, div_lt_one (by positivity), hsq]
        nlinarith
      exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
    refine ⟨(r, r⁻¹ • w), ⟨⟨hr0, hn⟩, hy1⟩, ?_⟩
    have hm : hemisphereHeight (r⁻¹ • w) = a / r := by
      have h1 : hemisphereHeight (r⁻¹ • w) ^ 2 = (a / r) ^ 2 := by
        rw [hemisphereHeight_sq hy1, hy, div_pow, hsq]
        field_simp
        ring
      exact (pow_left_inj₀ (hemisphereHeight_pos hy1).le (by positivity) two_ne_zero).mp h1
    simp only [polarMap, hm]
    refine Prod.ext ?_ ?_
    · simp only
      field_simp
    · simp only
      rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
theorem polarMap_injOn : InjOn polarMap polarDomain := by
  rintro ⟨r, y⟩ ⟨⟨hr0, hr1⟩, hy⟩ ⟨s, z⟩ ⟨⟨hs0, hs1⟩, hz⟩ h
  have hy' : ‖y‖ < 1 := hy
  have hz' : ‖z‖ < 1 := hz
  have hrs : r = s := by
    have := congrArg (fun p => ‖quatEquiv p‖) h
    simpa only [norm_quatEquiv_polarMap hr0 hy', norm_quatEquiv_polarMap hs0 hz'] using this
  subst hrs
  have h2 : r • y = r • z := congrArg Prod.snd h
  exact Prod.ext rfl (smul_right_injective _ hr0.ne' h2)
theorem exists_hasFDerivAt_polarMap (r : ℝ) {y : imaginaryQuaternions} (hy : ‖y‖ < 1) :
    ∃ D : QuatCoords →L[ℝ] QuatCoords, HasFDerivAt polarMap D (r, y) ∧
      ∀ (a : ℝ) (w : imaginaryQuaternions), D (a, w) =
        (a * hemisphereHeight y - r * inner ℝ y w / hemisphereHeight y, a • y + r • w) := by
  have hsnd : HasFDerivAt (fun p : QuatCoords => p.2)
      (ContinuousLinearMap.snd ℝ ℝ imaginaryQuaternions) (r, y) := hasFDerivAt_snd
  have hfst : HasFDerivAt (fun p : QuatCoords => p.1)
      (ContinuousLinearMap.fst ℝ ℝ imaginaryQuaternions) (r, y) := hasFDerivAt_fst
  have hn := hsnd.norm_sq
  have hne : 1 - ‖y‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg y]
  have hm : HasFDerivAt (fun p : QuatCoords => hemisphereHeight p.2) _ (r, y) :=
    ((hasFDerivAt_const (1 : ℝ) (r, y)).sub hn).sqrt hne
  have hT := (hfst.mul hm).prodMk (hfst.smul hsnd)
  refine ⟨_, hT, fun a w => ?_⟩
  have hmy : Real.sqrt (1 - ‖y‖ ^ 2) = hemisphereHeight y := rfl
  have hmy' : Real.sqrt (1 - ‖(y : ℍ[ℝ])‖ ^ 2) = hemisphereHeight y := rfl
  have h0 := (hemisphereHeight_pos hy).ne'
  refine Prod.ext ?_ ?_
  · simp [hmy, hmy']
    field_simp
    ring
  · simp
    abel
def coordEquiv : QuatCoords ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun p := ![p.1, (p.2 : ℍ[ℝ]).imI, (p.2 : ℍ[ℝ]).imJ, (p.2 : ℍ[ℝ]).imK]
  map_add' a b := by
    funext i
    fin_cases i <;> simp
  map_smul' c a := by
    funext i
    fin_cases i <;> simp
  invFun x := (x 0, ⟨⟨0, x 1, x 2, x 3⟩, rfl⟩)
  left_inv p := by
    refine Prod.ext rfl (Subtype.ext ?_)
    ext <;> simp [re_imaginaryQuaternions]
  right_inv x := by
    funext i
    fin_cases i <;> rfl
theorem inner_imaginaryQuaternions (y w : imaginaryQuaternions) : inner ℝ y w =
    (y : ℍ[ℝ]).imI * (w : ℍ[ℝ]).imI + (y : ℍ[ℝ]).imJ * (w : ℍ[ℝ]).imJ + (y : ℍ[ℝ]).imK * (w : ℍ[ℝ]).imK := by
  rw [Submodule.coe_inner, Quaternion.inner_def]
  simp [re_imaginaryQuaternions]
theorem det_eq_of_apply (D : QuatCoords →L[ℝ] QuatCoords) (r : ℝ) {y : imaginaryQuaternions} (hy : ‖y‖ < 1)
    (hD : ∀ (a : ℝ) (w : imaginaryQuaternions), D (a, w) =
      (a * hemisphereHeight y - r * inner ℝ y w / hemisphereHeight y, a • y + r • w)) :
    D.det = r ^ 3 / hemisphereHeight y := by
  set m := hemisphereHeight y with hm
  have hm0 : m ≠ 0 := (hemisphereHeight_pos hy).ne'
  set y0 := (y : ℍ[ℝ]).imI with h0
  set y1 := (y : ℍ[ℝ]).imJ with h1
  set y2 := (y : ℍ[ℝ]).imK with h2
  have hsq : y0 ^ 2 + y1 ^ 2 + y2 ^ 2 = 1 - m ^ 2 := by
    rw [hm, hemisphereHeight_sq hy, imaginary_norm_sq]
    ring
  let Mx : Matrix (Fin 4) (Fin 4) ℝ :=
    !![m, -(r * y0 / m), -(r * y1 / m), -(r * y2 / m); y0, r, 0, 0; y1, 0, r, 0; y2, 0, 0, r]
  have hconj : coordEquiv.toLinearMap ∘ₗ (D : QuatCoords →ₗ[ℝ] QuatCoords) ∘ₗ coordEquiv.symm.toLinearMap =
      Matrix.toLin' Mx := by
    refine LinearMap.ext fun x => ?_
    have hx : coordEquiv.symm x = (x 0, ⟨⟨0, x 1, x 2, x 3⟩, rfl⟩) := rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe, hx, hD,
      inner_imaginaryQuaternions]
    have hI : ∀ (c a b d : ℝ), (c • (⟨0, a, b, d⟩ : ℍ[ℝ])).imI = c * a := fun _ _ _ _ => rfl
    have hJ : ∀ (c a b d : ℝ), (c • (⟨0, a, b, d⟩ : ℍ[ℝ])).imJ = c * b := fun _ _ _ _ => rfl
    have hK : ∀ (c a b d : ℝ), (c • (⟨0, a, b, d⟩ : ℍ[ℝ])).imK = c * d := fun _ _ _ _ => rfl
    funext i
    fin_cases i <;> simp [coordEquiv, Mx, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      ← h0, ← h1, ← h2, hI, hJ, hK] <;>
      first
        | ring1
        | (show x 0 * _ + r * x 1 = _; ring)
        | (show x 0 * _ + r * x 2 = _; ring)
        | (show x 0 * _ + r * x 3 = _; ring)
  have hdet : Mx.det = r ^ 3 / m := by
    have : Mx.det = r ^ 3 * (m + (y0 ^ 2 + y1 ^ 2 + y2 ^ 2) / m) := by
      simp only [Mx, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_three]
      simp [Fin.succAbove]
      field_simp
      ring
    rw [this, hsq]
    field_simp
    ring
  rw [ContinuousLinearMap.det, ← LinearMap.det_conj (D : QuatCoords →ₗ[ℝ] QuatCoords) coordEquiv, hconj,
    LinearMap.det_toLin', hdet]
theorem fderiv_polarMap_det {p : QuatCoords} (hp : p ∈ polarDomain) :
    HasFDerivWithinAt polarMap (fderiv ℝ polarMap p) polarDomain p ∧
      (fderiv ℝ polarMap p).det = p.1 ^ 3 / hemisphereHeight p.2 := by
  obtain ⟨r, y⟩ := p
  have hy : ‖y‖ < 1 := hp.2
  obtain ⟨D, hD, hf⟩ := exists_hasFDerivAt_polarMap r hy
  rw [hD.fderiv]
  exact ⟨hD.hasFDerivWithinAt, det_eq_of_apply D r hy hf⟩
theorem measurableSet_polarDomain : MeasurableSet polarDomain :=
  measurableSet_Ioo.prod (isOpen_lt continuous_norm continuous_const).measurableSet
theorem isOpen_upperShell : IsOpen upperShell :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_quatEquiv.norm continuous_const)
theorem continuous_hemisphereHeight : Continuous hemisphereHeight := by
  unfold hemisphereHeight
  fun_prop
theorem radialUnit_re_pos_iff {p : QuatCoords} (hp : quatEquiv p ≠ 0) :
    0 < ((radialUnit p : UnitQuaternion) : ℍ[ℝ]).re ↔ 0 < p.1 := by
  have hn : 0 < ‖quatEquiv p‖ := norm_pos_iff.mpr hp
  simp only [radialUnit, dif_neg hp]
  have : ((‖quatEquiv p‖⁻¹ • quatEquiv p : ℍ[ℝ])).re = ‖quatEquiv p‖⁻¹ * p.1 := by
    simp [quatEquiv_apply, re_imaginaryQuaternions]
  show 0 < ((‖quatEquiv p‖⁻¹ • quatEquiv p : ℍ[ℝ])).re ↔ _
  rw [this]
  exact ⟨fun h => (pos_iff_pos_of_mul_pos h).mp (inv_pos.mpr hn), fun h => mul_pos (inv_pos.mpr hn) h⟩
end HemisphereChart
open HemisphereChart in
theorem haarOnHemisphereChart_holds : HaarOnHemisphereChart := by
  intro _ _ μ _
  set lam : Measure QuatCoords := (volume : Measure ℝ).prod μ with hlam
  set R : Set UnitQuaternion := {g : UnitQuaternion | 0 < (g : ℍ[ℝ]).re} with hR
  have hRm : MeasurableSet R := (isOpen_lt continuous_const
    ((Quaternion.continuous_re).comp continuous_subtype_val)).measurableSet
  set Cr : ℝ≥0∞ := ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ 3) with hCr
  have hCr0 : Cr ≠ 0 := by
    have hmeas : Measurable fun r : ℝ => ENNReal.ofReal (r ^ 3) := by fun_prop
    have hp : 0 < Cr := by
      rw [hCr, lintegral_pos_iff_support hmeas, Measure.restrict_apply' measurableSet_Ioo]
      have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support (fun r : ℝ => ENNReal.ofReal (r ^ 3)) ∩ Ioo 0 1 :=
        fun r hr => ⟨(ENNReal.ofReal_pos.mpr (pow_pos hr.1 3)).ne', hr⟩
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      simp
    exact hp.ne'
  have hCrt : Cr ≠ ⊤ := by
    have h1 : Cr ≤ ∫⁻ _ in Ioo (0 : ℝ) 1, 1 := setLIntegral_mono' measurableSet_Ioo fun r hr => by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (pow_le_one₀ hr.1.le hr.2.le)
    refine ne_top_of_le_ne_top ?_ h1
    simp
  set Cm : ℝ≥0∞ := lam openShell with hCm
  have hCm0 : Cm ≠ 0 := measure_openShell_ne_zero lam
  have hCmt : Cm ≠ ⊤ := measure_openShell_ne_top lam
  have hcpos : 0 < (Cr / Cm).toReal :=
    ENNReal.toReal_pos (ENNReal.div_ne_zero.mpr ⟨hCr0, hCmt⟩) (ENNReal.div_ne_top hCrt hCm0)
  refine ⟨(Cr / Cm).toReal, hcpos, fun f hf => ?_⟩
  rw [ENNReal.ofReal_toReal (ENNReal.div_ne_top hCrt hCm0)]
  have hF : Measurable (R.indicator f) := hf.indicator hRm
  have h1 := lintegral_openShell_radialUnit lam (R.indicator f) hF
  rw [lintegral_indicator hRm] at h1
  have hBm : MeasurableSet upperShell := isOpen_upperShell.measurableSet
  have h3 : ∫⁻ p in openShell, R.indicator f (radialUnit p) ∂lam = ∫⁻ p in upperShell, f (radialUnit p) ∂lam := by
    have hfun : ∀ p ∈ openShell, R.indicator f (radialUnit p) =
        upperShell.indicator (fun p => f (radialUnit p)) p := by
      intro p hp
      have hq : quatEquiv p ≠ 0 := norm_pos_iff.mp hp.1
      by_cases hpos : 0 < p.1
      · have hm : radialUnit p ∈ R := (radialUnit_re_pos_iff hq).mpr hpos
        have hb : p ∈ upperShell := ⟨hpos, hp.2⟩
        rw [indicator_of_mem hm, indicator_of_mem hb]
      · have hm : radialUnit p ∉ R := fun h => hpos ((radialUnit_re_pos_iff hq).mp h)
        have hb : p ∉ upperShell := fun h => hpos h.1
        rw [indicator_of_notMem hm, indicator_of_notMem hb]
    rw [setLIntegral_congr_fun isOpen_openShell.measurableSet hfun, setLIntegral_indicator hBm]
    congr 2
    ext p
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_, h.2⟩
      have hs := norm_sq_quatEquiv p
      have : 0 < ‖quatEquiv p‖ ^ 2 := by
        rw [hs]
        have := h.1
        positivity
      exact lt_of_le_of_ne (norm_nonneg _) (fun h0 => by rw [← h0] at this; norm_num at this)
  have h4 : ∫⁻ p in upperShell, f (radialUnit p) ∂lam =
      ∫⁻ p in polarDomain, ENNReal.ofReal |(fderiv ℝ polarMap p).det| * f (radialUnit (polarMap p)) ∂lam := by
    rw [← polarMap_image]
    exact lintegral_image_eq_lintegral_abs_det_fderiv_mul lam measurableSet_polarDomain
      (fun p hp => (fderiv_polarMap_det hp).1) polarMap_injOn _
  set G : imaginaryQuaternions → ℝ≥0∞ := fun y =>
    f (radialUnit (hemisphereHeight y, y)) * ENNReal.ofReal (hemisphereDensity y) with hG
  have hGm : Measurable G := by
    refine (hf.comp (measurable_radialUnit.comp ?_)).mul ?_
    · exact (continuous_hemisphereHeight.prodMk continuous_id).measurable
    · refine ENNReal.measurable_ofReal.comp ?_
      have : Continuous fun y : imaginaryQuaternions => 1 - ‖y‖ ^ 2 := by fun_prop
      exact (this.measurable.sqrt).inv
  have hmid : ∀ {y : imaginaryQuaternions}, ‖y‖ < 1 → radialUnit (hemisphereHeight y, y) = hemisphereUnit y := by
    intro y hy
    have := radialUnit_polarMap one_pos hy
    simpa [polarMap] using this
  have h5 : ∫⁻ p in polarDomain, ENNReal.ofReal |(fderiv ℝ polarMap p).det| * f (radialUnit (polarMap p)) ∂lam =
      ∫⁻ p in polarDomain, ENNReal.ofReal (p.1 ^ 3) * G p.2 ∂lam := by
    refine setLIntegral_congr_fun measurableSet_polarDomain fun p hp => ?_
    obtain ⟨r, y⟩ := p
    have hy : ‖y‖ < 1 := hp.2
    have hr : 0 < r := hp.1.1
    simp only
    rw [(fderiv_polarMap_det hp).2, radialUnit_polarMap hr hy, hG]
    simp only
    rw [hmid hy, abs_of_pos (div_pos (pow_pos hr 3) (hemisphereHeight_pos hy)), div_eq_mul_inv,
      ENNReal.ofReal_mul (pow_pos hr 3).le]
    have hd : (hemisphereHeight y)⁻¹ = hemisphereDensity y := rfl
    rw [hd]
    ring
  have h6 : ∫⁻ p in polarDomain, ENNReal.ofReal (p.1 ^ 3) * G p.2 ∂lam =
      Cr * ∫⁻ y in {y : imaginaryQuaternions | ‖y‖ < 1}, G y ∂μ := by
    rw [polarDomain, hlam, ← Measure.prod_restrict]
    exact lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r ^ 3)) (by fun_prop) hGm.aemeasurable
  have h7 : ∫⁻ y in {y : imaginaryQuaternions | ‖y‖ < 1}, G y ∂μ =
      ∫⁻ y in {y : imaginaryQuaternions | ‖y‖ < 1}, f (hemisphereUnit y) * ENNReal.ofReal (hemisphereDensity y) ∂μ := by
    refine setLIntegral_congr_fun (isOpen_lt continuous_norm continuous_const).measurableSet fun y hy => ?_
    simp only [hG]
    rw [hmid hy]
  set I₂ := ∫⁻ y in {y : imaginaryQuaternions | ‖y‖ < 1},
    f (hemisphereUnit y) * ENNReal.ofReal (hemisphereDensity y) ∂μ
  set I₁ := ∫⁻ g in R, f g ∂haarUnit
  have heq : Cm * I₁ = Cr * I₂ := by
    rw [← h1, h3, h4, h5, h6, h7]
  calc I₁ = Cm⁻¹ * (Cm * I₁) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hCm0 hCmt, one_mul]
    _ = Cm⁻¹ * (Cr * I₂) := by rw [heq]
    _ = Cr / Cm * I₂ := by
        rw [div_eq_mul_inv]
        ring
end YangMills.Construction.GaugeCharts
end
