import YangMills.Construction.ClusterExpansionOfAStep.FreeBondsInCoordinatesProof
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeFixingOfTheStepProof
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.ColdStepAtMirrorFrames.HaarMeasureInLogarithmicCoordinates
import YangMills.Construction.HoleBesideASecondHole.ASegmentInTheGroupProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields MeasureTheory Set Real Metric
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace HaarLogCoords
abbrev EucIm : Type := EuclideanSpace ℝ (Fin 3)
abbrev EucQuat : Type := EuclideanSpace ℝ (Fin 4)
def mkQuat (a : ℝ) (w : EucIm) : ℍ[ℝ] := ⟨a, w 0, w 1, w 2⟩
theorem norm_mkQuat_sq (a : ℝ) (w : EucIm) : ‖mkQuat a w‖ ^ 2 = a ^ 2 + ‖w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, sq ‖mkQuat a w‖,
    ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  simp [mkQuat]
  ring
theorem mem_unitary_of_norm_eq_one {q : ℍ[ℝ]} (hq : ‖q‖ = 1) : q ∈ unitary ℍ[ℝ] := by apply _root_.YangMills.Construction.GroupPaths.unitary_mem_of_norm_eq_one <;> assumption
theorem norm_coe_unit (g : UnitQuaternion) : ‖((g : UnitQuaternion) : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
open Classical in
def rayPoint (q : ℍ[ℝ]) : UnitQuaternion :=
  if h : q = 0 then 1 else
    ⟨(‖q‖⁻¹ : ℝ) • q, mem_unitary_of_norm_eq_one (by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)])⟩
theorem rayPoint_smul_coe {r : ℝ} (hr : 0 < r) (g : UnitQuaternion) :
    rayPoint (r • ((g : UnitQuaternion) : ℍ[ℝ])) = g := by
  have hne : r • ((g : UnitQuaternion) : ℍ[ℝ]) ≠ 0 := by
    intro h
    have := congrArg norm h
    rw [norm_smul, norm_coe_unit, norm_zero, mul_one, Real.norm_eq_abs, abs_of_pos hr] at this
    exact hr.ne' this
  apply Subtype.ext
  simp only [rayPoint, dif_neg hne]
  rw [norm_smul, norm_coe_unit, mul_one, Real.norm_eq_abs, abs_of_pos hr, smul_smul,
    inv_mul_cancel₀ hr.ne', one_smul]
theorem rayPoint_mul (g : UnitQuaternion) {q : ℍ[ℝ]} (hq : q ≠ 0) :
    rayPoint (((g : UnitQuaternion) : ℍ[ℝ]) * q) = g * rayPoint q := by
  have hg : ((g : UnitQuaternion) : ℍ[ℝ]) ≠ 0 := by
    intro h
    have := norm_coe_unit g
    rw [h, norm_zero] at this
    exact zero_ne_one this
  apply Subtype.ext
  simp only [rayPoint, dif_neg hq, dif_neg (mul_ne_zero hg hq), norm_mul, norm_coe_unit, one_mul]
  simp
def toQuat (e : EucQuat) : ℍ[ℝ] := Quaternion.linearIsometryEquivTuple.symm e
theorem norm_toQuat (e : EucQuat) : ‖toQuat e‖ = ‖e‖ := Quaternion.linearIsometryEquivTuple.symm.norm_map e
theorem measurable_rayPoint_toQuat : Measurable fun e : EucQuat => rayPoint (toQuat e) := by
  refine measurable_of_restrict_of_restrict_compl (measurableSet_singleton (0 : EucQuat)) ?_ ?_
  · exact Subsingleton.measurable
  · have hc : Continuous fun e : ({(0 : EucQuat)}ᶜ : Set EucQuat) =>
        (⟨(‖toQuat e.1‖⁻¹ : ℝ) • toQuat e.1, mem_unitary_of_norm_eq_one (by
          have h0 : toQuat e.1 ≠ 0 := by
            intro h
            apply e.2
            have := norm_toQuat e.1
            rw [h, norm_zero] at this
            exact norm_eq_zero.mp this.symm
          rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)])⟩ : UnitQuaternion) := by
      refine Continuous.subtype_mk ?_ _
      have hq : Continuous fun e : ({(0 : EucQuat)}ᶜ : Set EucQuat) => toQuat e.1 :=
        Quaternion.linearIsometryEquivTuple.symm.continuous.comp continuous_subtype_val
      refine Continuous.smul (Continuous.inv₀ hq.norm ?_) hq
      intro e
      rw [norm_toQuat]
      exact norm_ne_zero_iff.mpr e.2
    convert hc.measurable using 1
    funext e
    have h0 : toQuat e.1 ≠ 0 := by
      intro h
      apply e.2
      have := norm_toQuat e.1
      rw [h, norm_zero] at this
      exact norm_eq_zero.mp this.symm
    simp only [Set.restrict_apply, rayPoint, dif_neg h0]
def mulLeftIsometry (g : UnitQuaternion) : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ] where
  toFun q := ((g : UnitQuaternion) : ℍ[ℝ]) * q
  invFun q := star ((g : UnitQuaternion) : ℍ[ℝ]) * q
  map_add' := mul_add _
  map_smul' := by intro c q; simp
  left_inv := by
    intro q
    simp only [← mul_assoc, Unitary.star_mul_self_of_mem g.2, one_mul]
  right_inv := by
    intro q
    simp only [← mul_assoc, Unitary.mul_star_self_of_mem g.2, one_mul]
  norm_map' := by
    intro q
    simp [norm_mul, norm_coe_unit]
def mulLeftEuc (g : UnitQuaternion) : EucQuat ≃ₗᵢ[ℝ] EucQuat :=
  (Quaternion.linearIsometryEquivTuple.symm.trans (mulLeftIsometry g)).trans Quaternion.linearIsometryEquivTuple
theorem toQuat_mulLeftEuc (g : UnitQuaternion) (e : EucQuat) :
    toQuat (mulLeftEuc g e) = ((g : UnitQuaternion) : ℍ[ℝ]) * toQuat e := by
  simp only [toQuat, mulLeftEuc, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
  rfl
def puncturedBall : Set EucQuat := {e | 0 < ‖e‖ ∧ ‖e‖ < 1}
theorem measurableSet_puncturedBall : MeasurableSet puncturedBall :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
def radialProjection : Measure UnitQuaternion :=
  (volume.restrict puncturedBall).map fun e : EucQuat => rayPoint (toQuat e)
instance : IsFiniteMeasure radialProjection := by
  have h : volume puncturedBall < ∞ := by
    refine lt_of_le_of_lt (measure_mono (t := ball (0 : EucQuat) 1) ?_) measure_ball_lt_top
    intro e he
    simpa [ball] using he.2
  haveI : IsFiniteMeasure (volume.restrict puncturedBall : Measure EucQuat) := ⟨by simpa using h⟩
  unfold radialProjection
  infer_instance
instance : radialProjection.IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  have hmul : Measurable fun h : UnitQuaternion => g * h := (continuous_const.mul continuous_id).measurable
  have hL : MeasurePreserving (mulLeftEuc g) volume volume := LinearIsometryEquiv.measurePreserving _
  have hpre : mulLeftEuc g ⁻¹' puncturedBall = puncturedBall := by
    ext e
    simp [puncturedBall]
  have hR := hL.restrict_preimage measurableSet_puncturedBall
  rw [hpre] at hR
  unfold radialProjection
  rw [Measure.map_map hmul measurable_rayPoint_toQuat]
  have hcongr : ((fun h : UnitQuaternion => g * h) ∘ fun e : EucQuat => rayPoint (toQuat e))
      =ᵐ[volume.restrict puncturedBall] (fun e : EucQuat => rayPoint (toQuat e)) ∘ mulLeftEuc g := by
    filter_upwards [ae_restrict_mem measurableSet_puncturedBall] with e he
    have h0 : toQuat e ≠ 0 := by
      intro h
      have := norm_toQuat e
      rw [h, norm_zero] at this
      exact (ne_of_gt he.1) this.symm
    simp only [Function.comp, toQuat_mulLeftEuc, rayPoint_mul g h0]
  rw [Measure.map_congr hcongr, ← Measure.map_map measurable_rayPoint_toQuat hL.measurable, hR.map_eq]
def reImSplit : EucQuat ≃ᵐ ℝ × EucIm :=
  ((MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))
theorem measurePreserving_reImSplit : MeasurePreserving reImSplit volume volume := by
  unfold reImSplit
  refine ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 4)).trans
    (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0)).trans ?_
  exact (MeasurePreserving.id _).prod (PiLp.volume_preserving_toLp (Fin 3))
theorem toQuat_eq_mkQuat (e : EucQuat) : toQuat e = mkQuat (reImSplit e).1 (reImSplit e).2 := rfl
theorem toQuat_reImSplit_symm (p : ℝ × EucIm) : toQuat (reImSplit.symm p) = mkQuat p.1 p.2 := by
  rw [toQuat_eq_mkQuat, MeasurableEquiv.apply_symm_apply]
theorem lintegral_sphere_polar (G : EucIm → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ w, G w = ∫⁻ u : sphere (0 : EucIm) 1,
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * G (r • (u : EucIm))) ∂(volume : Measure EucIm).toSphere := by
  have hdim : Module.finrank ℝ EucIm - 1 = 2 := by simp
  calc ∫⁻ w, G w = ∫⁻ w in ({(0 : EucIm)}ᶜ : Set EucIm), G w := by
        rw [restrict_compl_singleton]
    _ = ∫⁻ x : ({(0 : EucIm)}ᶜ : Set EucIm), G x.1 ∂((volume : Measure EucIm).comap (↑)) := by
        rw [lintegral_subtype_comap (measurableSet_singleton _).compl fun x => G x]
    _ = ∫⁻ x, G (x.2.1 • (x.1 : EucIm)) ∂((volume : Measure EucIm).toSphere.prod
          (.volumeIoiPow (Module.finrank ℝ EucIm - 1))) := by
        have := (volume : Measure EucIm).measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
          (Homeomorph.measurableEmbedding _) (fun x => G (x.2.1 • (x.1 : EucIm)))
        rw [← this]
        refine lintegral_congr fun x => ?_
        congr 1
        simp only [homeomorphUnitSphereProd, homeomorphSphereProd]
        simp
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr x.2), one_smul]
    _ = ∫⁻ u : sphere (0 : EucIm) 1, (∫⁻ r : Ioi (0 : ℝ), G (r.1 • (u : EucIm))
          ∂(.volumeIoiPow (Module.finrank ℝ EucIm - 1))) ∂(volume : Measure EucIm).toSphere := by
        rw [lintegral_prod]
        refine (hG.comp ?_).aemeasurable
        fun_prop
    _ = _ := by
        refine lintegral_congr fun u => ?_
        rw [hdim, Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul]
        · rw [← lintegral_subtype_comap measurableSet_Ioi fun r : ℝ => ENNReal.ofReal (r ^ 2) * G (r • (u : EucIm))]
          rfl
        · exact (measurable_subtype_coe.pow_const _).ennreal_ofReal
        · refine hG.comp ?_
          fun_prop
theorem norm_toImaginary (v : EucIm) : ‖((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
theorem continuous_toImaginary : Continuous fun v : EucIm => ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.FreeChart.continuous_toImaginary <;> assumption
theorem continuous_expUnit_toImaginary : Continuous fun v : EucIm => expUnit (toImaginary v) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeFixing.continuous_expLog <;> assumption
theorem coe_expUnit_toImaginary {θ : ℝ} (hθ : 0 < θ) (u : sphere (0 : EucIm) 1) :
    ((expUnit (toImaginary (θ • (u : EucIm))) : UnitQuaternion) : ℍ[ℝ]) = mkQuat (cos θ) (sin θ • (u : EucIm)) := by
  have hu : ‖(u : EucIm)‖ = 1 := by simpa using u.2
  have hn : ‖((toImaginary (θ • (u : EucIm)) : imaginaryQuaternions) : ℍ[ℝ])‖ = θ := by
    rw [norm_toImaginary, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos hθ]
  show NormedSpace.exp ((toImaginary (θ • (u : EucIm)) : imaginaryQuaternions) : ℍ[ℝ]) = _
  rw [Quaternion.exp_of_re_eq_zero _ (toImaginary (θ • (u : EucIm))).2, hn]
  ext
  · simp [mkQuat, toImaginary]
    change (sin θ / θ) * 0 = 0
    ring
  · simp [mkQuat, toImaginary]
    change (sin θ / θ) * (θ * _) = _
    field_simp
  · simp [mkQuat, toImaginary]
    change (sin θ / θ) * (θ * _) = _
    field_simp
  · simp [mkQuat, toImaginary]
    change (sin θ / θ) * (θ * _) = _
    field_simp
def angularIntegral (ψ : UnitQuaternion → ℝ≥0∞) (u : sphere (0 : EucIm) 1) : ℝ≥0∞ :=
  ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (sin θ ^ 2) * ψ (expUnit (toImaginary (θ • (u : EucIm))))
def ballIntegrand (ψ : UnitQuaternion → ℝ≥0∞) (p : ℝ × EucIm) : ℝ≥0∞ :=
  open Classical in
  if 0 < p.1 ^ 2 + ‖p.2‖ ^ 2 ∧ p.1 ^ 2 + ‖p.2‖ ^ 2 < 1 then ψ (rayPoint (mkQuat p.1 p.2)) else 0
theorem ballIntegrand_eq (ψ : UnitQuaternion → ℝ≥0∞) (p : ℝ × EucIm) :
    ballIntegrand ψ p = puncturedBall.indicator (fun e => ψ (rayPoint (toQuat e))) (reImSplit.symm p) := by
  have hn : ‖reImSplit.symm p‖ ^ 2 = p.1 ^ 2 + ‖p.2‖ ^ 2 := by
    rw [← norm_toQuat, toQuat_reImSplit_symm, norm_mkQuat_sq]
  have hiff : reImSplit.symm p ∈ puncturedBall ↔ 0 < p.1 ^ 2 + ‖p.2‖ ^ 2 ∧ p.1 ^ 2 + ‖p.2‖ ^ 2 < 1 := by
    rw [← hn]
    simp only [puncturedBall, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by positivity, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      have h0 : 0 < ‖reImSplit.symm p‖ := by
        rcases (norm_nonneg (reImSplit.symm p)).lt_or_eq with h | h
        · exact h
        · rw [← h] at h1
          norm_num at h1
      exact ⟨h0, by nlinarith⟩
  unfold ballIntegrand
  by_cases h : 0 < p.1 ^ 2 + ‖p.2‖ ^ 2 ∧ p.1 ^ 2 + ‖p.2‖ ^ 2 < 1
  · rw [if_pos h, indicator_of_mem (hiff.mpr h), toQuat_reImSplit_symm]
  · rw [if_neg h, indicator_of_notMem (fun hm => h (hiff.mp hm))]
theorem measurable_ballIntegrand {ψ : UnitQuaternion → ℝ≥0∞} (hψ : Measurable ψ) :
    Measurable (ballIntegrand ψ) := by
  have : ballIntegrand ψ = puncturedBall.indicator (fun e => ψ (rayPoint (toQuat e))) ∘ reImSplit.symm := by
    funext p
    exact ballIntegrand_eq ψ p
  rw [this]
  exact ((hψ.comp measurable_rayPoint_toQuat).indicator measurableSet_puncturedBall).comp
    reImSplit.symm.measurable
theorem lintegral_radialProjection {ψ : UnitQuaternion → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ g, ψ g ∂radialProjection = ∫⁻ p, ballIntegrand ψ p := by
  have hm : Measurable (puncturedBall.indicator fun e : EucQuat => ψ (rayPoint (toQuat e))) :=
    (hψ.comp measurable_rayPoint_toQuat).indicator measurableSet_puncturedBall
  unfold radialProjection
  rw [lintegral_map hψ measurable_rayPoint_toQuat, ← lintegral_indicator measurableSet_puncturedBall,
    ← measurePreserving_reImSplit.symm.lintegral_comp hm]
  exact lintegral_congr fun p => (ballIntegrand_eq ψ p).symm
def planeIntegrand (ψ : UnitQuaternion → ℝ≥0∞) (u : sphere (0 : EucIm) 1) (p : ℝ × ℝ) : ℝ≥0∞ :=
  open Classical in
  if 0 < p.2 then ENNReal.ofReal (p.2 ^ 2) * ballIntegrand ψ (p.1, p.2 • (u : EucIm)) else 0
theorem measurable_planeIntegrand {ψ : UnitQuaternion → ℝ≥0∞} (hψ : Measurable ψ) (u : sphere (0 : EucIm) 1) :
    Measurable (planeIntegrand ψ u) := by
  unfold planeIntegrand
  refine Measurable.ite (measurableSet_lt measurable_const measurable_snd) ?_ measurable_const
  refine Measurable.mul (by fun_prop) ((measurable_ballIntegrand hψ).comp ?_)
  fun_prop
theorem lintegral_planeIntegrand {ψ : UnitQuaternion → ℝ≥0∞} (hψ : Measurable ψ) (u : sphere (0 : EucIm) 1) :
    ∫⁻ p, planeIntegrand ψ u p =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * ∫⁻ a, ballIntegrand ψ (a, r • (u : EucIm)) := by
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ (measurable_planeIntegrand hψ u).aemeasurable,
    ← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun y => ?_
  by_cases hy : 0 < y
  · rw [indicator_of_mem (mem_Ioi.mpr hy),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun a => ?_
    simp [planeIntegrand, hy]
  · rw [indicator_of_notMem (by simpa using hy)]
    simp [planeIntegrand, hy]
def radialWeight (r : ℝ) : ℝ≥0∞ := (Ioo (0 : ℝ) 1).indicator (fun r => ENNReal.ofReal (r ^ 3)) r
def angularWeight (ψ : UnitQuaternion → ℝ≥0∞) (u : sphere (0 : EucIm) 1) (θ : ℝ) : ℝ≥0∞ :=
  (Ioo 0 π).indicator
    (fun θ => ENNReal.ofReal (sin θ ^ 2) * ψ (expUnit (toImaginary (θ • (u : EucIm))))) θ
theorem planeIntegrand_polar (ψ : UnitQuaternion → ℝ≥0∞) (u : sphere (0 : EucIm) 1) (p : ℝ × ℝ)
    (hp : p ∈ polarCoord.target) :
    ENNReal.ofReal p.1 • planeIntegrand ψ u (polarCoord.symm p) = radialWeight p.1 * angularWeight ψ u p.2 := by
  obtain ⟨r, θ⟩ := p
  have hr : 0 < r := hp.1
  have hθ : θ ∈ Ioo (-π) π := hp.2
  have hu : ‖(u : EucIm)‖ = 1 := by simpa using u.2
  simp only [polarCoord_symm_apply, planeIntegrand, smul_eq_mul]
  by_cases hs : θ ∈ Ioo 0 π
  · have hsin : 0 < sin θ := sin_pos_of_mem_Ioo hs
    have hpos : 0 < r * sin θ := mul_pos hr hsin
    rw [if_pos hpos]
    have hsq : (r * cos θ) ^ 2 + ‖(r * sin θ) • (u : EucIm)‖ ^ 2 = r ^ 2 := by
      rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
      nlinarith [sin_sq_add_cos_sq θ]
    have hq : mkQuat (r * cos θ) ((r * sin θ) • (u : EucIm)) =
        r • ((expUnit (toImaginary (θ • (u : EucIm))) : UnitQuaternion) : ℍ[ℝ]) := by
      rw [coe_expUnit_toImaginary hs.1 u]
      ext <;> simp [mkQuat] <;> (change _ = r * _) <;> ring
    simp only [ballIntegrand, hsq]
    rw [hq, rayPoint_smul_coe hr]
    by_cases h1 : r < 1
    · have h0 : 0 < r ^ 2 := by positivity
      have h2 : r ^ 2 < 1 := by nlinarith
      rw [if_pos ⟨h0, h2⟩, radialWeight, angularWeight,
        indicator_of_mem (show r ∈ Ioo (0 : ℝ) 1 from ⟨hr, h1⟩),
        indicator_of_mem hs, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hr.le,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring
    · have h2 : ¬ (0 < r ^ 2 ∧ r ^ 2 < 1) := by
        rintro ⟨_, h⟩
        exact h1 (by nlinarith)
      rw [if_neg h2, radialWeight, indicator_of_notMem (fun h => h1 h.2)]
      simp
  · have hle : θ ≤ 0 := by
      by_contra h
      exact hs ⟨not_le.mp h, hθ.2⟩
    have hsin : sin θ ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le hle hθ.1.le
    have hnpos : ¬ 0 < r * sin θ := by
      have := mul_nonpos_of_nonneg_of_nonpos hr.le hsin
      linarith
    rw [if_neg hnpos, angularWeight, indicator_of_notMem hs]
    simp
theorem lintegral_radialWeight : ∫⁻ r in Ioi (0 : ℝ), radialWeight r = ENNReal.ofReal (1 / 4) := by
  unfold radialWeight
  rw [setLIntegral_indicator measurableSet_Ioo]
  have : Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo 0 1 := by
    ext r
    simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
    tauto
  rw [this, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    simp
    norm_num
  · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have := hr.1
    positivity
theorem lintegral_angularWeight {ψ : UnitQuaternion → ℝ≥0∞} (u : sphere (0 : EucIm) 1) :
    ∫⁻ θ in Ioo (-π) π, angularWeight ψ u θ = angularIntegral ψ u := by
  unfold angularWeight angularIntegral
  rw [setLIntegral_indicator measurableSet_Ioo]
  have : Ioo 0 π ∩ Ioo (-π) π = Ioo 0 π := by
    ext r
    simp only [mem_inter_iff, mem_Ioo]
    constructor
    · rintro ⟨h, _⟩
      exact h
    · intro h
      exact ⟨h, by linarith [h.1, pi_pos], h.2⟩
  rw [this]
theorem lintegral_radial_ballIntegrand {ψ : UnitQuaternion → ℝ≥0∞} (hψ : Measurable ψ)
    (u : sphere (0 : EucIm) 1) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * ∫⁻ a, ballIntegrand ψ (a, r • (u : EucIm)) =
      ENNReal.ofReal (1 / 4) * angularIntegral ψ u := by
  have hexp : Measurable fun θ : ℝ => ψ (expUnit (toImaginary (θ • (u : EucIm)))) :=
    hψ.comp (continuous_expUnit_toImaginary.comp (by fun_prop)).measurable
  have hang : Measurable (angularWeight ψ u) :=
    (Measurable.mul (by fun_prop) hexp).indicator measurableSet_Ioo
  have hrad : Measurable radialWeight := (by fun_prop : Measurable fun r : ℝ =>
    ENNReal.ofReal (r ^ 3)).indicator measurableSet_Ioo
  rw [← lintegral_planeIntegrand hψ, ← lintegral_comp_polarCoord_symm,
    setLIntegral_congr_fun polarCoord.open_target.measurableSet (planeIntegrand_polar ψ u)]
  simp only [polarCoord_target]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_mul hrad.aemeasurable hang.aemeasurable,
    lintegral_radialWeight, lintegral_angularWeight]
theorem measurable_haarLogDensity : Measurable haarLogDensity := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.measurable_haarLogDensity <;> assumption
theorem haarLogDensity_nonneg (v : EucIm) : 0 ≤ haarLogDensity v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeFixing.haarLogDensity_nonneg <;> assumption
theorem measurable_expUnit_toImaginary : Measurable fun v : EucIm => expUnit (toImaginary v) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeFixing.measurable_expLog <;> assumption
theorem lintegral_radialProjection_eq_angular {ψ : UnitQuaternion → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ g, ψ g ∂radialProjection =
      ENNReal.ofReal (1 / 4) * ∫⁻ u, angularIntegral ψ u ∂(volume : Measure EucIm).toSphere := by
  have hb := measurable_ballIntegrand hψ
  rw [lintegral_radialProjection hψ, Measure.volume_eq_prod, lintegral_prod_symm _ hb.aemeasurable,
    lintegral_sphere_polar _ hb.lintegral_prod_left', ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_congr fun u => lintegral_radial_ballIntegrand hψ u
theorem lintegral_radial_density {ψ : UnitQuaternion → ℝ≥0∞} (u : sphere (0 : EucIm) 1) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) *
        (ENNReal.ofReal (haarLogDensity (r • (u : EucIm))) * ψ (expUnit (toImaginary (r • (u : EucIm))))) =
      ENNReal.ofReal (1 / (2 * π ^ 2)) * angularIntegral ψ u := by
  have hu : ‖(u : EucIm)‖ = 1 := by simpa using u.2
  unfold angularIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsub : Ioo 0 π ∩ Ioi 0 = Ioo 0 π := by
    ext r
    simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
    tauto
  rw [← hsub, ← setLIntegral_indicator measurableSet_Ioo]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : 0 < r := hr
  have hn : ‖r • (u : EucIm)‖ = r := by
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
  by_cases h : r < π
  · rw [indicator_of_mem (show r ∈ Ioo 0 π from ⟨hr0, h⟩)]
    simp only [haarLogDensity, hn, if_pos h, ← mul_assoc]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [sinc_of_ne_zero hr0.ne']
    field_simp
  · rw [indicator_of_notMem (fun hm => h hm.2)]
    simp [haarLogDensity, hn, h]
theorem lintegral_density_eq_angular {ψ : UnitQuaternion → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ v : EucIm, ENNReal.ofReal (haarLogDensity v) * ψ (expUnit (toImaginary v)) =
      ENNReal.ofReal (1 / (2 * π ^ 2)) * ∫⁻ u, angularIntegral ψ u ∂(volume : Measure EucIm).toSphere := by
  have hm : Measurable fun v : EucIm => ENNReal.ofReal (haarLogDensity v) * ψ (expUnit (toImaginary v)) :=
    measurable_haarLogDensity.ennreal_ofReal.mul (hψ.comp measurable_expUnit_toImaginary)
  rw [lintegral_sphere_polar _ hm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_congr fun u => lintegral_radial_density u
theorem angularIntegral_one (u : sphere (0 : EucIm) 1) :
    angularIntegral (fun _ => 1) u = ENNReal.ofReal (π / 2) := by
  unfold angularIntegral
  simp only [mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le pi_pos.le, integral_sin_sq]
    simp
  · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
  · exact Filter.Eventually.of_forall fun r => by positivity
theorem lintegral_angularIntegral_one :
    ∫⁻ u, angularIntegral (fun _ => 1) u ∂(volume : Measure EucIm).toSphere = ENNReal.ofReal (2 * π ^ 2) := by
  simp only [angularIntegral_one, lintegral_const]
  rw [Measure.toSphere_apply_univ, EuclideanSpace.volume_ball_fin_three]
  simp only [finrank_euclideanSpace_fin, Fintype.card_fin]
  rw [ENNReal.ofReal_one, one_pow, one_mul]
  have h3 : ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 := by simp
  rw [h3, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring
theorem lintegral_haarUnit {ψ : UnitQuaternion → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ g, ψ g ∂haarUnit = ∫⁻ v : EucIm, ENNReal.ofReal (haarLogDensity v) * ψ (expUnit (toImaginary v)) := by
  have hc := Measure.isMulLeftInvariant_eq_smul radialProjection haarUnit
  set c := Measure.haarScalarFactor radialProjection haarUnit with hcdef
  have h1 : ∫⁻ g, ψ g ∂radialProjection = (c : ℝ≥0∞) * ∫⁻ g, ψ g ∂haarUnit := by
    rw [hc, lintegral_smul_measure]
    rfl
  have h2 : ∫⁻ _ : UnitQuaternion, 1 ∂radialProjection = (c : ℝ≥0∞) := by
    rw [hc, lintegral_smul_measure]
    simp
  have hval : (c : ℝ≥0∞) = ENNReal.ofReal (π ^ 2 / 2) := by
    rw [← h2, lintegral_radialProjection_eq_angular measurable_const, lintegral_angularIntegral_one,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have hA := lintegral_radialProjection_eq_angular hψ
  rw [h1, hval] at hA
  rw [lintegral_density_eq_angular hψ]
  have hscale : ENNReal.ofReal (1 / (2 * π ^ 2)) * ENNReal.ofReal 4 * ENNReal.ofReal (π ^ 2 / 2) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    have : 1 / (2 * π ^ 2) * 4 * (π ^ 2 / 2) = 1 := by
      have := pi_pos
      field_simp
      norm_num
    rw [this, ENNReal.ofReal_one]
  have hfour : ENNReal.ofReal 4 * ENNReal.ofReal (1 / 4) = 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  calc ∫⁻ g, ψ g ∂haarUnit
      = (ENNReal.ofReal (1 / (2 * π ^ 2)) * ENNReal.ofReal 4 * ENNReal.ofReal (π ^ 2 / 2)) *
          ∫⁻ g, ψ g ∂haarUnit := by rw [hscale, one_mul]
    _ = ENNReal.ofReal (1 / (2 * π ^ 2)) * ENNReal.ofReal 4 *
          (ENNReal.ofReal (π ^ 2 / 2) * ∫⁻ g, ψ g ∂haarUnit) := by rw [mul_assoc]
    _ = ENNReal.ofReal (1 / (2 * π ^ 2)) * (ENNReal.ofReal 4 * ENNReal.ofReal (1 / 4)) *
          ∫⁻ u, angularIntegral ψ u ∂(volume : Measure EucIm).toSphere := by
        rw [hA]
        simp only [mul_assoc]
    _ = _ := by rw [hfour, mul_one]
theorem haarUnit_eq_map :
    haarUnit = ((volume : Measure EucIm).withDensity fun v => ENNReal.ofReal (haarLogDensity v)).map
      fun v => expUnit (toImaginary v) := by
  ext A hA
  rw [Measure.map_apply measurable_expUnit_toImaginary hA,
    ← lintegral_indicator_one hA,
    lintegral_haarUnit (measurable_one.indicator hA),
    ← lintegral_indicator_one (measurable_expUnit_toImaginary hA),
    lintegral_withDensity_eq_lintegral_mul _ measurable_haarLogDensity.ennreal_ofReal
      (measurable_one.indicator (measurable_expUnit_toImaginary hA))]
  rfl
end HaarLogCoords
open HaarLogCoords in
theorem haarIntegralInLogCoords_proof : HaarIntegralInLogCoords := by
  intro ψ hψ
  have hfin : ∀ᵐ v ∂(volume : Measure EucIm), ENNReal.ofReal (haarLogDensity v) < ∞ :=
    Filter.Eventually.of_forall fun v => ENNReal.ofReal_lt_top
  rw [haarUnit_eq_map, integral_map measurable_expUnit_toImaginary.aemeasurable hψ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul measurable_haarLogDensity.ennreal_ofReal hfin]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (haarLogDensity_nonneg v)]
end YangMills.Construction.ColdStepAtMirrorFrames
end
