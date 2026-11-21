import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponential
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open YangMills.Construction.BlockAverages NormedSpace
namespace YangMills.Construction.ColdStepAtMirrorFrames
def imaginaryPartLinear : ℍ[ℝ] →ₗ[ℝ] imaginaryQuaternions where
  toFun q := ⟨q - (q.re : ℍ[ℝ]), by show (q - (q.re : ℍ[ℝ])).re = 0; simp⟩
  map_add' a b := by apply Subtype.ext; ext <;> simp
  map_smul' c a := by apply Subtype.ext; ext <;> simp
theorem imaginaryPartLinear_coe_of_re_eq_zero (q : ℍ[ℝ]) (hq : q.re = 0) :
    ((imaginaryPartLinear q : imaginaryQuaternions) : ℍ[ℝ]) = q := by
  show q - (q.re : ℍ[ℝ]) = q
  simp [hq]
theorem contDiff_quaternion_exp : ContDiff ℝ 3 (exp : ℍ[ℝ] → ℍ[ℝ]) :=
  contDiff_iff_contDiffAt.mpr fun x => (exp_analytic (𝕂 := ℝ) x).contDiffAt
theorem quaternion_exp_neg (x : ℍ[ℝ]) : exp (-x) = (exp x)⁻¹ :=
  exp_neg_of_mem_ball ℝ ((expSeries_radius_eq_top ℝ ℍ[ℝ]).symm ▸ edist_lt_top _ _)
theorem quaternion_exp_ne_zero (x : ℍ[ℝ]) : exp x ≠ 0 := by
  intro hx
  have hn := Quaternion.norm_exp x
  rw [hx, norm_zero, ← Real.exp_eq_exp_ℝ] at hn
  have := Real.exp_pos x.re
  rw [Real.norm_of_nonneg this.le] at hn
  linarith
theorem expUnit_neg (a : imaginaryQuaternions) : expUnit (-a) = (expUnit a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  show exp (((-a : imaginaryQuaternions)) : ℍ[ℝ]) * exp (a : ℍ[ℝ]) = 1
  have : (((-a : imaginaryQuaternions)) : ℍ[ℝ]) = -(a : ℍ[ℝ]) := rfl
  rw [this, quaternion_exp_neg, inv_mul_cancel₀ (quaternion_exp_ne_zero _)]
def conjugatedExpProduct (z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) : ℍ[ℝ] :=
  exp (z.1 : ℍ[ℝ]) * exp (z.2.1 : ℍ[ℝ]) * exp (-(z.2.2 : ℍ[ℝ]))
theorem contDiff_conjugatedExpProduct : ContDiff ℝ 3 conjugatedExpProduct := by
  have c1 : ContDiff ℝ 3
      (fun z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions => (z.1 : ℍ[ℝ])) :=
    imaginaryQuaternions.subtypeL.contDiff.comp contDiff_fst
  have c2 : ContDiff ℝ 3
      (fun z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions => (z.2.1 : ℍ[ℝ])) :=
    imaginaryQuaternions.subtypeL.contDiff.comp (contDiff_fst.comp contDiff_snd)
  have c3 : ContDiff ℝ 3
      (fun z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions => -(z.2.2 : ℍ[ℝ])) :=
    (imaginaryQuaternions.subtypeL.contDiff.comp (contDiff_snd.comp contDiff_snd)).neg
  exact ((contDiff_quaternion_exp.comp c1).mul (contDiff_quaternion_exp.comp c2)).mul
    (contDiff_quaternion_exp.comp c3)
theorem conjugatedExpProduct_diagonalTriple (a : imaginaryQuaternions) :
    conjugatedExpProduct (diagonalTriple a) = 1 := by
  simp only [conjugatedExpProduct, diagonalTriple]
  rw [quaternion_exp_neg]
  simp [quaternion_exp_ne_zero]
theorem norm_conjugatedExpProduct (z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) :
    ‖conjugatedExpProduct z‖ = 1 := by
  have hw : ∀ w : imaginaryQuaternions, ‖exp (w : ℍ[ℝ])‖ = 1 := fun w => by
    have hre : (w : ℍ[ℝ]).re = 0 := w.2
    rw [Quaternion.norm_exp, hre]
    simp
  have hneg : ‖exp (-(z.2.2 : ℍ[ℝ]))‖ = 1 := hw (-z.2.2)
  simp only [conjugatedExpProduct, norm_mul, hw, hneg, one_mul]
section Generic
variable {E G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
theorem hasFDerivAt_exp_comp_clm_zero (ℓ : E →L[ℝ] ℍ[ℝ]) : HasFDerivAt (fun z => exp (ℓ z)) ℓ 0 := by
  have h0 : HasFDerivAt (exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) (ℓ 0) := by
    rw [map_zero]; exact hasFDerivAt_exp_zero (𝕂 := ℝ)
  exact (h0.comp (0 : E) ℓ.hasFDerivAt).congr_fderiv (by ext z <;> rfl)
theorem fderiv_triple_exp_product_zero (ℓ₁ ℓ₂ ℓ₃ : E →L[ℝ] ℍ[ℝ]) (z : E) :
    fderiv ℝ (fun z => exp (ℓ₁ z) * exp (ℓ₂ z) * exp (ℓ₃ z)) 0 z = ℓ₁ z + ℓ₂ z + ℓ₃ z := by
  have hd := ((hasFDerivAt_exp_comp_clm_zero ℓ₁).mul' (hasFDerivAt_exp_comp_clm_zero ℓ₂)).mul'
    (hasFDerivAt_exp_comp_clm_zero ℓ₃)
  have hf : (fun z => exp (ℓ₁ z) * exp (ℓ₂ z) * exp (ℓ₃ z)) =
      ((fun z => exp (ℓ₁ z)) * fun z => exp (ℓ₂ z)) * fun z => exp (ℓ₃ z) := rfl
  rw [hf, hd.fderiv]
  simp
  abel
theorem norm_fderiv_sub_fderiv_zero_le_along (Θ : E → G) (ι : H →L[ℝ] E) (C : ℝ) (hι : ‖ι‖ ≤ 1)
    (hC : 0 ≤ C) (hc : ∀ r, ‖r‖ ≤ 1 → ContDiffAt ℝ 3 Θ (ι r))
    (hb : ∀ r, ‖r‖ ≤ 1 → ‖iteratedFDeriv ℝ 2 Θ (ι r)‖ ≤ C) (r : H) (z : E) (hr : ‖r‖ ≤ 1) :
    ‖fderiv ℝ Θ (ι r) z - fderiv ℝ Θ 0 z‖ ≤ C * ‖r‖ * ‖z‖ := by
  let g : H → E →L[ℝ] G := fun r => fderiv ℝ Θ (ι r)
  have hg : ∀ r ∈ Metric.closedBall (0 : H) 1, HasFDerivWithinAt g
      ((fderiv ℝ (fderiv ℝ Θ) (ι r)).comp ι) (Metric.closedBall (0 : H) 1) r := by
    intro r hr
    have hd : DifferentiableAt ℝ (fderiv ℝ Θ) (ι r) :=
      ((hc r (by simpa using hr)).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
    exact (HasFDerivAt.comp r hd.hasFDerivAt ι.hasFDerivAt).hasFDerivWithinAt
  have hbd : ∀ r ∈ Metric.closedBall (0 : H) 1, ‖(fderiv ℝ (fderiv ℝ Θ) (ι r)).comp ι‖ ≤ C := by
    intro r hr
    have e : ‖fderiv ℝ (fderiv ℝ Θ) (ι r)‖ ≤ C := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      exact hb r (by simpa using hr)
    calc _ ≤ ‖fderiv ℝ (fderiv ℝ Θ) (ι r)‖ * ‖ι‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := by gcongr
      _ = C := mul_one C
  have hmv := (convex_closedBall (0 : H) 1).norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbd
    (Metric.mem_closedBall_self zero_le_one) (show r ∈ Metric.closedBall (0 : H) 1 by simpa using hr)
  have hg0 : g 0 = fderiv ℝ Θ 0 := by
    show fderiv ℝ Θ (ι 0) = _
    rw [map_zero]
  rw [hg0, sub_zero] at hmv
  calc _ = ‖(g r - fderiv ℝ Θ 0) z‖ := rfl
    _ ≤ ‖g r - fderiv ℝ Θ 0‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ‖r‖ * ‖z‖ := by gcongr
theorem exists_bound_iteratedFDeriv_on_compact (Θ : E → G) (U K : Set E) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hc : ContDiffOn ℝ 3 Θ U) (j : ℕ) (hj : j ≤ 3) :
    ∃ C : ℝ, ∀ z ∈ K, ‖iteratedFDeriv ℝ j Θ z‖ ≤ C := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ j Θ) U :=
    (hc.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hU.uniqueDiffOn).congr
      fun x hx => (iteratedFDerivWithin_of_isOpen j hU hx).symm
  exact hK.exists_bound_of_continuousOn (hcont.mono hKU)
end Generic
theorem fderiv_conjugatedExpProduct_zero
    (z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) :
    fderiv ℝ conjugatedExpProduct 0 z = (z.1 : ℍ[ℝ]) + (z.2.1 : ℍ[ℝ]) - (z.2.2 : ℍ[ℝ]) := by
  let ℓ₁ : (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) →L[ℝ] ℍ[ℝ] :=
    imaginaryQuaternions.subtypeL.comp
      (ContinuousLinearMap.fst ℝ imaginaryQuaternions (imaginaryQuaternions × imaginaryQuaternions))
  let ℓ₂ : (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) →L[ℝ] ℍ[ℝ] :=
    imaginaryQuaternions.subtypeL.comp
      ((ContinuousLinearMap.fst ℝ imaginaryQuaternions imaginaryQuaternions).comp
        (ContinuousLinearMap.snd ℝ imaginaryQuaternions (imaginaryQuaternions × imaginaryQuaternions)))
  let ℓ₃ : (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) →L[ℝ] ℍ[ℝ] :=
    -(imaginaryQuaternions.subtypeL.comp
      ((ContinuousLinearMap.snd ℝ imaginaryQuaternions imaginaryQuaternions).comp
        (ContinuousLinearMap.snd ℝ imaginaryQuaternions (imaginaryQuaternions × imaginaryQuaternions))))
  have := fderiv_triple_exp_product_zero ℓ₁ ℓ₂ ℓ₃ z
  have hm : conjugatedExpProduct = fun z => exp (ℓ₁ z) * exp (ℓ₂ z) * exp (ℓ₃ z) := rfl
  rw [hm, this]
  simp [ℓ₁, ℓ₂, ℓ₃, sub_eq_add_neg]
theorem conjugatedExpLogSmooth_holds : ConjugatedExpLogSmooth := by
  have hA : ContDiffAt ℝ 3 (exp : ℍ[ℝ] → ℍ[ℝ]) 0 := contDiff_quaternion_exp.contDiffAt
  let f' : ℍ[ℝ] ≃L[ℝ] ℍ[ℝ] := ContinuousLinearEquiv.refl ℝ _
  have hf' : HasFDerivAt (exp : ℍ[ℝ] → ℍ[ℝ]) (f' : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) 0 := hasFDerivAt_exp_zero (𝕂 := ℝ)
  have hn : (3 : WithTop ℕ∞) ≠ 0 := by norm_num
  let Lq := hA.localInverse hf' hn
  have hL1 : Lq 1 = 0 := by
    have := hA.localInverse_apply_image hf' hn
    rwa [exp_zero] at this
  have hLc : ContDiffAt ℝ 3 Lq 1 := by
    have := hA.to_localInverse hf' hn
    rwa [exp_zero] at this
  have hRi : ∀ᶠ y in 𝓝 (1 : ℍ[ℝ]), exp (Lq y) = y := by
    have := (hA.hasStrictFDerivAt' hf' hn).eventually_right_inverse
    rw [exp_zero] at this
    exact this
  have hLd : HasFDerivAt Lq (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) 1 := by
    have := (hA.hasStrictFDerivAt' hf' hn).to_localInverse
    rw [exp_zero] at this
    exact this.hasFDerivAt
  obtain ⟨V₁, hV, hVo, h1V⟩ := mem_nhds_iff.mp ((hLc.eventually (by simp)).and hRi)
  let P : ℍ[ℝ] →L[ℝ] imaginaryQuaternions := LinearMap.toContinuousLinearMap imaginaryPartLinear
  let Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions :=
    fun z => P (Lq (conjugatedExpProduct z))
  let U : Set (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) :=
    conjugatedExpProduct ⁻¹' V₁
  have hUo : IsOpen U := hVo.preimage contDiff_conjugatedExpProduct.continuous
  have hdiag : ∀ a, diagonalTriple a ∈ U := fun a => by
    show conjugatedExpProduct _ ∈ V₁
    rw [conjugatedExpProduct_diagonalTriple]; exact h1V
  have hΘa : ∀ z ∈ U, ContDiffAt ℝ 3 Θ z := fun z hz =>
    P.contDiff.contDiffAt.comp z ((hV hz).1.comp z contDiff_conjugatedExpProduct.contDiffAt)
  have hΘc : ContDiffOn ℝ 3 Θ U := fun z hz => (hΘa z hz).contDiffWithinAt
  have hre : ∀ z ∈ U, (Lq (conjugatedExpProduct z)).re = 0 := by
    intro z hz
    have e : exp (Lq (conjugatedExpProduct z)) = conjugatedExpProduct z := (hV hz).2
    have hnorm : ‖exp (Lq (conjugatedExpProduct z))‖ = 1 := by rw [e, norm_conjugatedExpProduct]
    rw [Quaternion.norm_exp, ← Real.exp_eq_exp_ℝ, Real.norm_of_nonneg (Real.exp_pos _).le] at hnorm
    exact Real.exp_eq_one_iff _ |>.mp hnorm
  have hΘ1 : ∀ z ∈ U, ((Θ z : imaginaryQuaternions) : ℍ[ℝ]) = Lq (conjugatedExpProduct z) :=
    fun z hz => imaginaryPartLinear_coe_of_re_eq_zero _ (hre z hz)
  have hexp : ∀ z ∈ U, expUnit (Θ z) = expUnit z.1 * expUnit z.2.1 * (expUnit z.2.2)⁻¹ := by
    intro z hz
    rw [← expUnit_neg]
    apply Subtype.ext
    show exp ((Θ z : imaginaryQuaternions) : ℍ[ℝ]) =
      exp (z.1 : ℍ[ℝ]) * exp (z.2.1 : ℍ[ℝ]) * exp (((-z.2.2 : imaginaryQuaternions)) : ℍ[ℝ])
    rw [hΘ1 z hz, (hV hz).2]
    rfl
  have hΘ0 : ∀ a, Θ (diagonalTriple a) = 0 := fun a => by
    show P (Lq (conjugatedExpProduct _)) = 0
    rw [conjugatedExpProduct_diagonalTriple, hL1, map_zero]
  let ι : imaginaryQuaternions →L[ℝ] imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions :=
    (ContinuousLinearMap.id ℝ imaginaryQuaternions).prod
      ((0 : imaginaryQuaternions →L[ℝ] imaginaryQuaternions).prod
        (ContinuousLinearMap.id ℝ imaginaryQuaternions))
  have hK : IsCompact (ι '' Metric.closedBall 0 1) :=
    (isCompact_closedBall 0 1).image ι.continuous
  have hKU : ι '' Metric.closedBall 0 1 ⊆ U := by
    rintro _ ⟨a, _, rfl⟩
    exact hdiag a
  have hb : ∀ j : ℕ, j ≤ 3 → ∃ C : ℝ, ∀ z ∈ ι '' Metric.closedBall 0 1, ‖iteratedFDeriv ℝ j Θ z‖ ≤ C :=
    fun j hj => exists_bound_iteratedFDeriv_on_compact Θ U _ hUo hK hKU hΘc j hj
  obtain ⟨C0, h0⟩ := hb 0 (by norm_num)
  obtain ⟨C1, h1⟩ := hb 1 (by norm_num)
  obtain ⟨C2, h2⟩ := hb 2 (by norm_num)
  obtain ⟨C3, h3⟩ := hb 3 (by norm_num)
  let C := |C0| + |C1| + |C2| + |C3|
  have hC0 : 0 ≤ C := by positivity
  have hall : ∀ (a : imaginaryQuaternions) (j : ℕ), ‖a‖ ≤ 1 → j ≤ 3 →
      ‖iteratedFDeriv ℝ j Θ (diagonalTriple a)‖ ≤ C := by
    intro a j ha hj
    have hm : diagonalTriple a ∈ ι '' Metric.closedBall 0 1 := ⟨a, by simpa using ha, rfl⟩
    have a0 := le_abs_self C0
    have a1 := le_abs_self C1
    have a2 := le_abs_self C2
    have a3 := le_abs_self C3
    have p0 := abs_nonneg C0
    have p1 := abs_nonneg C1
    have p2 := abs_nonneg C2
    have p3 := abs_nonneg C3
    interval_cases j
    · have := h0 _ hm; simp only [C]; linarith
    · have := h1 _ hm; simp only [C]; linarith
    · have := h2 _ hm; simp only [C]; linarith
    · have := h3 _ hm; simp only [C]; linarith
  have hfd : ∀ z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions,
      fderiv ℝ Θ 0 z = z.1 + z.2.1 - z.2.2 := by
    intro z
    have hM : HasFDerivAt conjugatedExpProduct (fderiv ℝ conjugatedExpProduct 0) 0 :=
      (contDiff_conjugatedExpProduct.differentiable (by norm_num) 0).hasFDerivAt
    have hM1 : conjugatedExpProduct 0 = 1 := conjugatedExpProduct_diagonalTriple 0
    have hL' : HasFDerivAt Lq (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) (conjugatedExpProduct 0) := by rw [hM1]; exact hLd
    have hcomp := (hL'.comp (0 : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) hM)
    have hP := P.hasFDerivAt.comp (0 : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) hcomp
    have hval : fderiv ℝ Θ 0 =
        P.comp ((1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ]).comp (fderiv ℝ conjugatedExpProduct 0)) := hP.fderiv
    rw [hval]
    simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self, fderiv_conjugatedExpProduct_zero]
    apply Subtype.ext
    show (((imaginaryPartLinear _ : imaginaryQuaternions)) : ℍ[ℝ]) = _
    rw [imaginaryPartLinear_coe_of_re_eq_zero]
    · simp
    · have e1 : (z.1 : ℍ[ℝ]).re = 0 := z.1.2
      have e2 : (z.2.1 : ℍ[ℝ]).re = 0 := z.2.1.2
      have e3 : (z.2.2 : ℍ[ℝ]).re = 0 := z.2.2.2
      simp [e1, e2, e3]
  refine ⟨Θ, U, C, hUo, hC0, hdiag, hΘc, hexp, hΘ0, hall, hfd, ?_⟩
  intro a z ha
  have hιn : ‖ι‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => ?_
    simp [ι, Prod.norm_def]
  exact norm_fderiv_sub_fderiv_zero_le_along Θ ι C hιn hC0 (fun a _ => hΘa _ (hdiag a))
    (fun a ha => hall a 2 ha (by norm_num)) a z ha
end YangMills.Construction.ColdStepAtMirrorFrames
end
