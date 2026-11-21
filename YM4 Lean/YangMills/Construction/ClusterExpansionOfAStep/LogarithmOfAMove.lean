import YangMills.Construction.ClusterExpansionOfAStep.SecondDerivativesAlongLines
import YangMills.Construction.ColdStepAtMirrorFrames.BareActionIsCriticalAtAnAbelianFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction.QuaternionLogarithm
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
abbrev ImaginaryCoord : Type := EuclideanSpace ℝ (Fin 3)
def imaginaryCLM : ImaginaryCoord →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (⟨0, v 0, v 1, v 2⟩ : ℍ[ℝ])
      map_add' := fun v w => by
        ext <;> simp <;> first | rfl | (show (0 : ℝ) = 0 + 0; simp)
      map_smul' := fun c v => by
        ext <;> simp <;> first | rfl | (show (0 : ℝ) = c * 0; simp) }
def imPartCLM : ℍ[ℝ] →L[ℝ] ImaginaryCoord :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => WithLp.toLp 2 ![q.imI, q.imJ, q.imK]
      map_add' := fun p q => by
        ext i
        fin_cases i <;> simp
      map_smul' := fun c q => by
        ext i
        fin_cases i <;> simp }
theorem imaginaryCLM_apply (v : ImaginaryCoord) : imaginaryCLM v = (⟨0, v 0, v 1, v 2⟩ : ℍ[ℝ]) := rfl
theorem coe_toImaginary (v : ImaginaryCoord) :
    ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]) = imaginaryCLM v := rfl
theorem imPartCLM_imaginaryCLM (v : ImaginaryCoord) : imPartCLM (imaginaryCLM v) = v := by
  ext i
  fin_cases i <;> rfl
theorem contDiff_exp_quaternion : ContDiff ℝ ⊤ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) := by apply _root_.YangMills.SharedProofs.p23558 <;> assumption
def imPartExp (v : ImaginaryCoord) : ImaginaryCoord := imPartCLM (NormedSpace.exp (imaginaryCLM v))
theorem contDiff_imPartExp : ContDiff ℝ ⊤ imPartExp :=
  imPartCLM.contDiff.comp (contDiff_exp_quaternion.comp imaginaryCLM.contDiff)
theorem hasFDerivAt_imPartExp_zero :
    HasFDerivAt imPartExp ((ContinuousLinearEquiv.refl ℝ ImaginaryCoord : ImaginaryCoord ≃L[ℝ] ImaginaryCoord) :
      ImaginaryCoord →L[ℝ] ImaginaryCoord) 0 := by
  have h0 : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) (imaginaryCLM 0) := by
    rw [map_zero]
    exact hasFDerivAt_exp_zero
  have h2 := h0.comp (0 : ImaginaryCoord) imaginaryCLM.hasFDerivAt
  have h1 := (imPartCLM.hasFDerivAt (x := (NormedSpace.exp ∘ imaginaryCLM) (0 : ImaginaryCoord))).comp
    (0 : ImaginaryCoord) h2
  refine h1.congr_fderiv ?_
  ext1 v
  simp [imPartCLM_imaginaryCLM]
theorem contDiffAt_imPartExp : ContDiffAt ℝ 3 imPartExp 0 := (contDiff_imPartExp.of_le le_top).contDiffAt
def imPartExpInverse : ImaginaryCoord → ImaginaryCoord :=
  contDiffAt_imPartExp.localInverse hasFDerivAt_imPartExp_zero (by norm_num)
theorem imPartCLM_one : imPartCLM (1 : ℍ[ℝ]) = 0 := by
  ext i
  fin_cases i <;> rfl
theorem imPartExp_zero : imPartExp 0 = 0 := by simp [imPartExp, imPartCLM_one]
theorem contDiffAt_imPartExpInverse : ContDiffAt ℝ 3 imPartExpInverse 0 := by
  have := contDiffAt_imPartExp.to_localInverse hasFDerivAt_imPartExp_zero (by norm_num)
  rw [imPartExp_zero] at this
  exact this
theorem imPartExpInverse_zero : imPartExpInverse 0 = 0 := by
  have := contDiffAt_imPartExp.localInverse_apply_image hasFDerivAt_imPartExp_zero (by norm_num)
  rw [imPartExp_zero] at this
  exact this
theorem eventually_imPartExp_imPartExpInverse :
    ∀ᶠ y in 𝓝 (0 : ImaginaryCoord), imPartExp (imPartExpInverse y) = y := by
  have := (contDiffAt_imPartExp.hasStrictFDerivAt' hasFDerivAt_imPartExp_zero (by norm_num)).eventually_right_inverse
  rw [imPartExp_zero] at this
  exact this
def localLog (q : ℍ[ℝ]) : ImaginaryCoord := imPartExpInverse (imPartCLM q)
theorem localLog_one : localLog 1 = 0 := by
  rw [localLog, imPartCLM_one, imPartExpInverse_zero]
theorem contDiffAt_localLog : ContDiffAt ℝ 3 localLog 1 := by
  have h : ContDiffAt ℝ 3 imPartExpInverse (imPartCLM (1 : ℍ[ℝ])) := by
    rw [imPartCLM_one]
    exact contDiffAt_imPartExpInverse
  exact h.comp (1 : ℍ[ℝ]) imPartCLM.contDiff.contDiffAt
theorem eq_of_imPart_eq_of_re_pos {p q : ℍ[ℝ]} (hp : p ∈ unitary ℍ[ℝ]) (hq : q ∈ unitary ℍ[ℝ])
    (hi : imPartCLM p = imPartCLM q) (hpr : 0 < p.re) (hqr : 0 < q.re) : p = q := by
  have h0 : p.imI = q.imI := congrArg (fun v : ImaginaryCoord => v 0) hi
  have h1 : p.imJ = q.imJ := congrArg (fun v : ImaginaryCoord => v 1) hi
  have h2 : p.imK = q.imK := congrArg (fun v : ImaginaryCoord => v 2) hi
  have hn (u : ℍ[ℝ]) (hu : u ∈ unitary ℍ[ℝ]) : u.re ^ 2 + u.imI ^ 2 + u.imJ ^ 2 + u.imK ^ 2 = 1 := by
    have h3 := (Unitary.mem_iff.mp hu).1
    rw [Quaternion.star_mul_self] at h3
    have h4 : Quaternion.normSq u = 1 := by simpa using congrArg (fun z : ℍ[ℝ] => z.re) h3
    rw [Quaternion.normSq_def'] at h4
    exact h4
  have hr : p.re = q.re := by
    have h3 := hn p hp
    have h4 := hn q hq
    rw [h0, h1, h2] at h3
    nlinarith
  ext <;> assumption
theorem eventually_re_pos_nhds_one : ∀ᶠ q in 𝓝 (1 : ℍ[ℝ]), 0 < q.re := by
  have hc : Continuous fun q : ℍ[ℝ] => q.re := Quaternion.continuous_re
  exact hc.continuousAt.eventually (by simpa using (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
theorem eventually_exp_localLog : ∀ᶠ q in 𝓝 (1 : ℍ[ℝ]), q ∈ unitary ℍ[ℝ] →
    NormedSpace.exp (imaginaryCLM (localLog q)) = q := by
  have hc : ContinuousAt imPartCLM (1 : ℍ[ℝ]) := imPartCLM.continuous.continuousAt
  have h1 : ∀ᶠ q in 𝓝 (1 : ℍ[ℝ]), imPartExp (imPartExpInverse (imPartCLM q)) = imPartCLM q :=
    hc.eventually (by rw [imPartCLM_one]; exact eventually_imPartExp_imPartExpInverse)
  have hcl : ContinuousAt (fun q => NormedSpace.exp (imaginaryCLM (localLog q))) (1 : ℍ[ℝ]) :=
    (contDiff_exp_quaternion.continuous.continuousAt).comp
      (imaginaryCLM.continuous.continuousAt.comp contDiffAt_localLog.continuousAt)
  have hone : NormedSpace.exp (imaginaryCLM (localLog (1 : ℍ[ℝ]))) = 1 := by
    rw [localLog_one, map_zero, NormedSpace.exp_zero]
  have hre : ∀ᶠ y in 𝓝 (NormedSpace.exp (imaginaryCLM (localLog (1 : ℍ[ℝ])))), 0 < y.re := by
    rw [hone]
    exact eventually_re_pos_nhds_one
  have h2 : ∀ᶠ q in 𝓝 (1 : ℍ[ℝ]), 0 < (NormedSpace.exp (imaginaryCLM (localLog q))).re :=
    hcl.eventually hre
  filter_upwards [h1, h2, eventually_re_pos_nhds_one] with q a1 a2 a3 hq
  refine eq_of_imPart_eq_of_re_pos ?_ hq ?_ a2 a3
  · exact exp_imaginary_mem_unitary (toImaginary (localLog q))
  · exact a1
section Second
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem norm_second_fderiv_apply_le (f : E → F) (x v w : E) :
    ‖fderiv ℝ (fderiv ℝ f) x v w‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ‖v‖ * ‖w‖ := by
  have h := iteratedFDeriv_two_apply (𝕜 := ℝ) f x ![v, w]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← h]
  refine ((iteratedFDeriv ℝ 2 f x).le_opNorm _).trans ?_
  rw [Fin.prod_univ_two]
  simp [mul_assoc]
end Second
section Linear
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
theorem fderiv_clm_comp_apply (T : F →L[ℝ] G) {g : E → F} {p : E} (h : DifferentiableAt ℝ g p) (v : E) :
    fderiv ℝ (T ∘ g) p v = T (fderiv ℝ g p v) := by
  rw [fderiv_comp p T.differentiableAt h]
  simp
theorem second_fderiv_clm_comp_apply (T : F →L[ℝ] G) {g : E → F} {p : E} (h : ContDiffAt ℝ 2 g p) (v w : E) :
    fderiv ℝ (fderiv ℝ (T ∘ g)) p v w = T (fderiv ℝ (fderiv ℝ g) p v w) := by
  have hT : ContDiffAt ℝ 2 T (g p) := T.contDiff.contDiffAt
  rw [YangMills.Construction.LineCalculus.second_fderiv_of_eventuallyEq_comp
    (Filter.EventuallyEq.refl _ _) hT h v w]
  have h0 : fderiv ℝ (fderiv ℝ T) (g p) = 0 := by
    have : fderiv ℝ T = fun _ => T := by
      ext1 q
      exact T.fderiv
    rw [this]
    simp
  simp [h0]
end Linear
def leftTranslate (w : imaginaryQuaternions) (v : ImaginaryCoord) : ℍ[ℝ] :=
  NormedSpace.exp ((w : ℍ[ℝ]) + imaginaryCLM v) * NormedSpace.exp (-(w : ℍ[ℝ]))
def chartTranslate (w : imaginaryQuaternions) (v : ImaginaryCoord) : ImaginaryCoord :=
  localLog (leftTranslate w v)
theorem exp_mul_exp_neg (q : ℍ[ℝ]) : NormedSpace.exp q * NormedSpace.exp (-q) = 1 := by
  have hneg : NormedSpace.exp (-q) = (NormedSpace.exp q)⁻¹ :=
    NormedSpace.exp_neg_of_mem_ball (𝕂 := ℝ)
      ((NormedSpace.expSeries_radius_eq_top ℝ ℍ[ℝ]).symm ▸ edist_lt_top _ _)
  have hne : NormedSpace.exp q ≠ 0 :=
    (NormedSpace.isUnit_exp_of_mem_ball (𝕂 := ℝ)
      ((NormedSpace.expSeries_radius_eq_top ℝ ℍ[ℝ]).symm ▸ edist_lt_top _ _)).ne_zero
  rw [hneg, mul_inv_cancel₀ hne]
theorem leftTranslate_zero (w : imaginaryQuaternions) : leftTranslate w 0 = 1 := by
  simp [leftTranslate, exp_mul_exp_neg]
theorem contDiff_leftTranslate (w : imaginaryQuaternions) : ContDiff ℝ ⊤ (leftTranslate w) := by
  unfold leftTranslate
  exact (contDiff_exp_quaternion.comp (contDiff_const.add imaginaryCLM.contDiff)).mul contDiff_const
theorem chartTranslate_zero (w : imaginaryQuaternions) : chartTranslate w 0 = 0 := by
  rw [chartTranslate, leftTranslate_zero, localLog_one]
theorem contDiffAt_chartTranslate (w : imaginaryQuaternions) : ContDiffAt ℝ 3 (chartTranslate w) 0 := by
  have h : ContDiffAt ℝ 3 localLog (leftTranslate w 0) := by
    rw [leftTranslate_zero]
    exact contDiffAt_localLog
  exact h.comp (0 : ImaginaryCoord) ((contDiff_leftTranslate w).of_le le_top).contDiffAt
theorem leftTranslate_mem_unitary (w : imaginaryQuaternions) (v : ImaginaryCoord) :
    leftTranslate w v ∈ unitary ℍ[ℝ] := by
  exact (unitary ℍ[ℝ]).mul_mem (exp_imaginary_mem_unitary (w + toImaginary v)) (exp_imaginary_mem_unitary (-w))
theorem eventually_expUnit_add_eq (w : imaginaryQuaternions) : ∀ᶠ v in 𝓝 (0 : ImaginaryCoord),
    expUnit (w + toImaginary v) = expUnit (toImaginary (chartTranslate w v)) * expUnit w := by
  have hc : ContinuousAt (leftTranslate w) 0 := (contDiff_leftTranslate w).continuous.continuousAt
  have h1 : ∀ᶠ y in 𝓝 (leftTranslate w 0), y ∈ unitary ℍ[ℝ] →
      NormedSpace.exp (imaginaryCLM (localLog y)) = y := by
    rw [leftTranslate_zero]
    exact eventually_exp_localLog
  filter_upwards [hc.eventually h1] with v hv
  apply Subtype.ext
  have h2 := hv (leftTranslate_mem_unitary w v)
  show NormedSpace.exp (((w + toImaginary v : imaginaryQuaternions)) : ℍ[ℝ]) =
    NormedSpace.exp (imaginaryCLM (chartTranslate w v)) * NormedSpace.exp (w : ℍ[ℝ])
  rw [chartTranslate, h2, leftTranslate, mul_assoc]
  have h3 : NormedSpace.exp (-(w : ℍ[ℝ])) * NormedSpace.exp (w : ℍ[ℝ]) = 1 := by
    simpa using exp_mul_exp_neg (-(w : ℍ[ℝ]))
  rw [h3, mul_one]
  rfl
theorem norm_exp_neg_imaginary (w : imaginaryQuaternions) : ‖NormedSpace.exp (-(w : ℍ[ℝ]))‖ = 1 :=
  YangMills.Construction.TorusFields.norm_unitQuaternion (expUnit (-w))
theorem exists_chartTranslate_deriv_bounds : ∃ C : ℝ, 0 < C ∧ ∀ w : imaginaryQuaternions, ‖(w : ℍ[ℝ])‖ ≤ 1 →
    (∀ v, ‖fderiv ℝ (chartTranslate w) 0 v‖ ≤ C * ‖v‖) ∧
    ∀ v v', ‖fderiv ℝ (fderiv ℝ (chartTranslate w)) 0 v v'‖ ≤ C * ‖v‖ * ‖v'‖ := by
  have hE1 : Continuous fun q : ℍ[ℝ] => iteratedFDeriv ℝ 1 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) q :=
    contDiff_exp_quaternion.continuous_iteratedFDeriv (m := 1) (by exact_mod_cast le_top)
  have hE2 : Continuous fun q : ℍ[ℝ] => iteratedFDeriv ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) q :=
    contDiff_exp_quaternion.continuous_iteratedFDeriv (m := 2) (by exact_mod_cast le_top)
  obtain ⟨K1, hK1'⟩ := (isCompact_closedBall (0 : ℍ[ℝ]) 1).exists_bound_of_continuousOn hE1.continuousOn
  obtain ⟨K2, hK2'⟩ := (isCompact_closedBall (0 : ℍ[ℝ]) 1).exists_bound_of_continuousOn hE2.continuousOn
  have hK1 : ∀ q ∈ Metric.closedBall (0 : ℍ[ℝ]) 1, ‖fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) q‖ ≤ K1 :=
    fun q hq => by
      rw [← norm_iteratedFDeriv_one]
      exact hK1' q hq
  have hK2 : ∀ q ∈ Metric.closedBall (0 : ℍ[ℝ]) 1,
      ‖iteratedFDeriv ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) q‖ ≤ K2 := hK2'
  set A1 := ‖fderiv ℝ localLog 1‖
  set A2 := ‖iteratedFDeriv ℝ 2 localLog 1‖
  set P := ‖imaginaryCLM‖
  have key : ∀ w : imaginaryQuaternions, ‖(w : ℍ[ℝ])‖ ≤ 1 →
      (∀ v, ‖fderiv ℝ (leftTranslate w) 0 v‖ ≤ |K1| * P * ‖v‖) ∧
      ∀ v v', ‖fderiv ℝ (fderiv ℝ (leftTranslate w)) 0 v v'‖ ≤ |K2| * P * P * ‖v‖ * ‖v'‖ := by
    intro w hw
    set e := NormedSpace.exp (-(w : ℍ[ℝ]))
    set R : ℍ[ℝ] →L[ℝ] ℍ[ℝ] := (ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip e
    set A : ImaginaryCoord → ℍ[ℝ] := fun v => (w : ℍ[ℝ]) + imaginaryCLM v
    have hA : ContDiff ℝ ⊤ A := contDiff_const.add imaginaryCLM.contDiff
    have hA1 : ∀ p, fderiv ℝ A p = imaginaryCLM := fun p => by
      have : HasFDerivAt A imaginaryCLM p := (imaginaryCLM.hasFDerivAt).const_add _
      exact this.fderiv
    have hA2 : fderiv ℝ (fderiv ℝ A) 0 = 0 := by
      have : fderiv ℝ A = fun _ => imaginaryCLM := funext hA1
      rw [this]
      simp
    have hm : leftTranslate w = R ∘ (NormedSpace.exp ∘ A) := by
      ext1 v
      rfl
    have hEA : ContDiffAt ℝ 2 (NormedSpace.exp ∘ A) 0 :=
      ((contDiff_exp_quaternion.comp hA).of_le le_top).contDiffAt
    have hw0 : A 0 = (w : ℍ[ℝ]) := by simp [A]
    have hb : A 0 ∈ Metric.closedBall (0 : ℍ[ℝ]) 1 := by
      rw [hw0]
      simpa using hw
    have hR : ∀ q, ‖R q‖ ≤ ‖q‖ := fun q => by
      show ‖q * e‖ ≤ ‖q‖
      rw [norm_mul, norm_exp_neg_imaginary, mul_one]
    have hP : ∀ v, ‖imaginaryCLM v‖ ≤ P * ‖v‖ := fun v => imaginaryCLM.le_opNorm v
    constructor
    · intro v
      have h1 : DifferentiableAt ℝ (NormedSpace.exp ∘ A) 0 := hEA.differentiableAt (by norm_num)
      rw [hm, fderiv_clm_comp_apply R h1 v]
      refine (hR _).trans ?_
      have h2 : fderiv ℝ (NormedSpace.exp ∘ A) 0 v = fderiv ℝ NormedSpace.exp (A 0) (imaginaryCLM v) := by
        rw [fderiv_comp (0 : ImaginaryCoord) (contDiff_exp_quaternion.differentiable (by simp) _)
          (hA.differentiable (by simp) _)]
        simp [hA1]
      rw [h2]
      refine ((fderiv ℝ NormedSpace.exp (A 0)).le_opNorm _).trans ?_
      have h3 := hK1 _ hb
      calc ‖fderiv ℝ NormedSpace.exp (A 0)‖ * ‖imaginaryCLM v‖ ≤ |K1| * (P * ‖v‖) :=
            mul_le_mul (h3.trans (le_abs_self _)) (hP v) (norm_nonneg _) (abs_nonneg _)
        _ = |K1| * P * ‖v‖ := by ring
    · intro v v'
      rw [hm, second_fderiv_clm_comp_apply R hEA v v']
      refine (hR _).trans ?_
      have hE : ContDiffAt ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (A 0) :=
        (contDiff_exp_quaternion.of_le le_top).contDiffAt
      have hA' : ContDiffAt ℝ 2 A 0 := (hA.of_le le_top).contDiffAt
      rw [YangMills.Construction.LineCalculus.second_fderiv_of_eventuallyEq_comp
        (Filter.EventuallyEq.refl _ _) hE hA' v v', hA2]
      simp only [hA1, ContinuousLinearMap.zero_apply, map_zero, add_zero]
      have h3 := hK2 _ hb
      calc ‖fderiv ℝ (fderiv ℝ NormedSpace.exp) (A 0) (imaginaryCLM v) (imaginaryCLM v')‖
          ≤ ‖iteratedFDeriv ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (A 0)‖ * ‖imaginaryCLM v‖ *
              ‖imaginaryCLM v'‖ :=
            norm_second_fderiv_apply_le _ _ _ _
        _ ≤ |K2| * (P * ‖v‖) * (P * ‖v'‖) := by
            gcongr
            · exact h3.trans (le_abs_self _)
            · exact hP v
            · exact hP v'
        _ = |K2| * P * P * ‖v‖ * ‖v'‖ := by ring
  set B1 := |K1| * P
  set B2 := |K2| * P * P
  refine ⟨A1 * B1 + A2 * B1 * B1 + A1 * B2 + 1, by positivity, fun w hw => ?_⟩
  obtain ⟨k1, k2⟩ := key w hw
  have hL : ContDiffAt ℝ 2 localLog (leftTranslate w 0) := by
    rw [leftTranslate_zero]
    exact contDiffAt_localLog.of_le (by norm_num)
  have hQ : ContDiffAt ℝ 2 (leftTranslate w) 0 := ((contDiff_leftTranslate w).of_le le_top).contDiffAt
  have hfe : chartTranslate w = localLog ∘ leftTranslate w := rfl
  constructor
  · intro v
    have hd : fderiv ℝ (chartTranslate w) 0 v = fderiv ℝ localLog 1 (fderiv ℝ (leftTranslate w) 0 v) := by
      rw [hfe, YangMills.Construction.LineCalculus.fderiv_of_eventuallyEq_comp (Filter.EventuallyEq.refl _ _)
        (hL.differentiableAt (by norm_num)) (hQ.differentiableAt (by norm_num)), leftTranslate_zero]
      rfl
    rw [hd]
    calc ‖fderiv ℝ localLog 1 (fderiv ℝ (leftTranslate w) 0 v)‖
        ≤ A1 * ‖fderiv ℝ (leftTranslate w) 0 v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ A1 * (B1 * ‖v‖) := by gcongr; exact k1 v
      _ ≤ (A1 * B1 + A2 * B1 * B1 + A1 * B2 + 1) * ‖v‖ := by
        have : 0 ≤ (A2 * B1 * B1 + A1 * B2 + 1) * ‖v‖ := by positivity
        nlinarith
  · intro v v'
    rw [hfe, YangMills.Construction.LineCalculus.second_fderiv_of_eventuallyEq_comp
      (Filter.EventuallyEq.refl _ _) hL hQ v v', leftTranslate_zero]
    have t1 : ‖fderiv ℝ (fderiv ℝ localLog) 1 (fderiv ℝ (leftTranslate w) 0 v)
        (fderiv ℝ (leftTranslate w) 0 v')‖ ≤ A2 * (B1 * ‖v‖) * (B1 * ‖v'‖) := by
      refine (norm_second_fderiv_apply_le _ _ _ _).trans ?_
      gcongr
      · exact k1 v
      · exact k1 v'
    have t2 : ‖fderiv ℝ localLog 1 (fderiv ℝ (fderiv ℝ (leftTranslate w)) 0 v v')‖ ≤
        A1 * (B2 * ‖v‖ * ‖v'‖) := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      gcongr
      exact k2 v v'
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ A2 * (B1 * ‖v‖) * (B1 * ‖v'‖) + A1 * (B2 * ‖v‖ * ‖v'‖) := add_le_add t1 t2
      _ ≤ (A1 * B1 + A2 * B1 * B1 + A1 * B2 + 1) * ‖v‖ * ‖v'‖ := by
        have h0 : 0 ≤ ‖v‖ * ‖v'‖ := by positivity
        have h1 : 0 ≤ (A1 * B1 + 1) * (‖v‖ * ‖v'‖) := by positivity
        nlinarith
end YangMills.Construction.QuaternionLogarithm
end
