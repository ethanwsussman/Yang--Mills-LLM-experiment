import YangMills.Construction.SummableBoundsOfTheFlow.SecondMomentsOfAGaussian
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.GaussianMoments
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private def coordCLM (i : ι × Fin 3) : (ι → EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ :=
  (EuclideanSpace.proj i.2).comp (ContinuousLinearMap.proj i.1)
private theorem coordCLM_apply (i : ι × Fin 3) (x : ι → EuclideanSpace ℝ (Fin 3)) :
    coordCLM i x = x i.1 i.2 := rfl
private def coordBasis (i : ι × Fin 3) : ι → EuclideanSpace ℝ (Fin 3) :=
  Pi.single i.1 (EuclideanSpace.single i.2 1)
private theorem coordCLM_coordBasis (i j : ι × Fin 3) :
    coordCLM i (coordBasis j) = if i = j then 1 else 0 := by
  rw [coordCLM_apply]
  unfold coordBasis
  by_cases h1 : i.1 = j.1
  · by_cases h2 : i.2 = j.2
    · have : i = j := Prod.ext h1 h2
      subst this
      simp
    · have hne : i ≠ j := fun h => h2 (congrArg Prod.snd h)
      rw [if_neg hne, h1, Pi.single_eq_same]
      simp [h2]
  · have hne : i ≠ j := fun h => h1 (congrArg Prod.fst h)
    rw [if_neg hne, Pi.single_eq_of_ne h1]
    simp
private theorem hasFDerivAt_quadForm (A : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (x : ι → EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (quadForm A)
      (∑ i, ∑ j, A i j • (coordCLM i x • coordCLM j + coordCLM j x • coordCLM i)) x := by
  have h : quadForm A = fun x => ∑ i, ∑ j, A i j * (coordCLM i x * coordCLM j x) := rfl
  rw [h]
  refine HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => ?_
  refine HasFDerivAt.const_mul ?_ _
  exact (coordCLM i).hasFDerivAt.mul (coordCLM j).hasFDerivAt
private theorem fderiv_quadForm_coordBasis (A : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (hA : A.IsSymm)
    (x : ι → EuclideanSpace ℝ (Fin 3)) (k : ι × Fin 3) :
    fderiv ℝ (quadForm A) x (coordBasis k) = 2 * ∑ j, A k j * x j.1 j.2 := by
  rw [(hasFDerivAt_quadForm A x).fderiv]
  have key : ∀ i j, (A i j • (coordCLM i x • coordCLM j + coordCLM j x • coordCLM i)) (coordBasis k) =
      A i j * (x i.1 i.2 * (if j = k then 1 else 0)) + A i j * (x j.1 j.2 * (if i = k then 1 else 0)) := by
    intro i j
    show A i j • ((coordCLM i x) • (coordCLM j (coordBasis k)) + (coordCLM j x) • (coordCLM i (coordBasis k))) = _
    rw [coordCLM_coordBasis, coordCLM_coordBasis, coordCLM_apply, coordCLM_apply]
    simp only [smul_eq_mul]
    ring
  have t1 : ∀ i, ∑ j, A i j * (x i.1 i.2 * (if j = k then (1 : ℝ) else 0)) = A k i * x i.1 i.2 := by
    intro i
    rw [← hA.apply k i]
    simp [mul_ite]
  have t2 : ∀ i, ∑ j, A i j * (x j.1 j.2 * (if i = k then (1 : ℝ) else 0)) =
      if i = k then ∑ j, A k j * x j.1 j.2 else 0 := by
    intro i
    split_ifs with h
    · subst h
      simp
    · simp
  simp only [ContinuousLinearMap.sum_apply, key, Finset.sum_add_distrib, t1, t2, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring
private theorem continuous_quadForm (A : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) : Continuous (quadForm A) :=
  continuous_iff_continuousAt.mpr fun x => (hasFDerivAt_quadForm A x).continuousAt
private theorem continuous_gaussianWeight (A : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) :
    Continuous (gaussianWeight A) := by
  unfold gaussianWeight
  exact Real.continuous_exp.comp (((continuous_quadForm A).const_mul _).neg)
private theorem coord_sq_le_sum_norm_sq (x : ι → EuclideanSpace ℝ (Fin 3)) (i : ι × Fin 3) :
    (x i.1 i.2) ^ 2 ≤ ∑ b, ‖x b‖ ^ 2 := by
  have h1 : |x i.1 i.2| ≤ ‖x i.1‖ := by
    have := PiLp.norm_apply_le (x i.1) i.2
    simpa using this
  have h2 : (x i.1 i.2) ^ 2 ≤ ‖x i.1‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  exact h2.trans (Finset.single_le_sum (f := fun b => ‖x b‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ i.1))
private theorem integrable_exp_neg_mul_sum_norm_sq (c : ℝ) (hc : 0 < c) :
    Integrable fun x : ι → EuclideanSpace ℝ (Fin 3) => Real.exp (-(c * ∑ b, ‖x b‖ ^ 2)) := by
  have h1 : Integrable fun v : EuclideanSpace ℝ (Fin 3) => Real.exp (-(c * ‖v‖ ^ 2)) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℝ (Fin 3))
      (b := (c : ℂ)) (by simpa using hc) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun v => ?_)
    have e : (-(c : ℂ) * (‖v‖ : ℂ) ^ 2 + 0 * ((inner ℝ (0 : EuclideanSpace ℝ (Fin 3)) v : ℝ) : ℂ)) =
        ((-(c * ‖v‖ ^ 2) : ℝ) : ℂ) := by
      push_cast
      ring
    simp only []
    rw [e, Complex.norm_exp, Complex.ofReal_re]
  have h2 := Integrable.fintype_prod (ι := ι) (f := fun _ v => Real.exp (-(c * ‖v‖ ^ 2)))
    (μ := fun _ => (volume : Measure (EuclideanSpace ℝ (Fin 3)))) fun _ => h1
  rw [← volume_pi] at h2
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
abbrev _root_.YangMills.DeltaSharedProofs.p502286 := @integrable_exp_neg_mul_sum_norm_sq
private theorem integrable_mul_gaussianWeight (A : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (m : ℝ) (hm : 0 < m)
    (hlow : ∀ x : ι → EuclideanSpace ℝ (Fin 3), m * ∑ b, ‖x b‖ ^ 2 ≤ quadForm A x)
    (f : (ι → EuclideanSpace ℝ (Fin 3)) → ℝ) (hf : Continuous f) (K : ℝ)
    (hbound : ∀ x, |f x| ≤ K * (1 + ∑ b, ‖x b‖ ^ 2)) :
    Integrable fun x => f x * gaussianWeight A x := by
  have hK : 0 ≤ K := by
    have := (abs_nonneg _).trans (hbound 0)
    by_contra hneg
    have h1 : (1 : ℝ) ≤ 1 + ∑ b, ‖(0 : ι → EuclideanSpace ℝ (Fin 3)) b‖ ^ 2 := by
      have : (0 : ℝ) ≤ ∑ b, ‖(0 : ι → EuclideanSpace ℝ (Fin 3)) b‖ ^ 2 := by positivity
      linarith
    nlinarith
  have hg := (integrable_exp_neg_mul_sum_norm_sq (ι := ι) (m / 4) (by positivity)).const_mul (K * (1 + 4 / m))
  refine hg.mono' (hf.mul (continuous_gaussianWeight A)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  set R : ℝ := ∑ b, ‖x b‖ ^ 2 with hR
  have hw : gaussianWeight A x ≤ Real.exp (-(m / 4 * R)) * Real.exp (-(m / 4 * R)) := by
    unfold gaussianWeight
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := hlow x
    nlinarith
  have hw0 : 0 ≤ gaussianWeight A x := (Real.exp_pos _).le
  have hxe : (1 + R) * Real.exp (-(m / 4 * R)) ≤ 1 + 4 / m := by
    have h1 : m / 4 * R + 1 ≤ Real.exp (m / 4 * R) := Real.add_one_le_exp _
    have h2 : Real.exp (-(m / 4 * R)) * Real.exp (m / 4 * R) = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 : 0 < Real.exp (-(m / 4 * R)) := Real.exp_pos _
    have h4 : Real.exp (-(m / 4 * R)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ m / 4 * R := by positivity
      linarith
    have h5 : R * Real.exp (-(m / 4 * R)) ≤ 4 / m := by
      have h6 : (m / 4 * R + 1) * Real.exp (-(m / 4 * R)) ≤ 1 := by
        calc (m / 4 * R + 1) * Real.exp (-(m / 4 * R)) ≤ Real.exp (m / 4 * R) * Real.exp (-(m / 4 * R)) :=
              mul_le_mul_of_nonneg_right h1 h3.le
          _ = 1 := by rw [mul_comm]; exact h2
      rw [le_div_iff₀ hm]
      nlinarith
    nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
  calc |f x| * gaussianWeight A x
      ≤ (K * (1 + R)) * (Real.exp (-(m / 4 * R)) * Real.exp (-(m / 4 * R))) :=
        mul_le_mul (hbound x) hw hw0 (by positivity)
    _ = K * ((1 + R) * Real.exp (-(m / 4 * R))) * Real.exp (-(m / 4 * R)) := by ring
    _ ≤ K * (1 + 4 / m) * Real.exp (-(m / 4 * R)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hxe hK
private theorem continuous_coord_apply (i : ι × Fin 3) :
    Continuous fun x : ι → EuclideanSpace ℝ (Fin 3) => x i.1 i.2 := (coordCLM i).continuous
theorem covarianceEqInverse_holds : CovarianceEqInverse := by
  intro ι _ _ A m hm hA hlow
  have hsq : ∀ (x : ι → EuclideanSpace ℝ (Fin 3)) (i : ι × Fin 3), |x i.1 i.2| ≤ 1 * (1 + ∑ b, ‖x b‖ ^ 2) := by
    intro x i
    have h1 := coord_sq_le_sum_norm_sq x i
    have h2 : |x i.1 i.2| ≤ 1 + (x i.1 i.2) ^ 2 := by
      rw [← sq_abs (x i.1 i.2)]
      nlinarith [abs_nonneg (x i.1 i.2), sq_nonneg (|x i.1 i.2| - 1)]
    linarith
  have hint0 : Integrable (gaussianWeight A) := by
    have := integrable_mul_gaussianWeight A m hm hlow (fun _ => 1) continuous_const 1 (fun x => by
      have : (0 : ℝ) ≤ ∑ b, ‖x b‖ ^ 2 := by positivity
      simp only [abs_one]
      linarith)
    simpa using this
  have hint1 : ∀ i : ι × Fin 3, Integrable fun x : ι → EuclideanSpace ℝ (Fin 3) =>
      x i.1 i.2 * gaussianWeight A x := fun i =>
    integrable_mul_gaussianWeight A m hm hlow _ (continuous_coord_apply i) 1 fun x => hsq x i
  have hint2 : ∀ i j : ι × Fin 3, Integrable fun x : ι → EuclideanSpace ℝ (Fin 3) =>
      x i.1 i.2 * x j.1 j.2 * gaussianWeight A x := by
    intro i j
    refine integrable_mul_gaussianWeight A m hm hlow _
      ((continuous_coord_apply i).mul (continuous_coord_apply j)) 1 fun x => ?_
    have h1 := coord_sq_le_sum_norm_sq x i
    have h2 := coord_sq_le_sum_norm_sq x j
    rw [abs_mul]
    have h3 : |x i.1 i.2| * |x j.1 j.2| ≤ ((x i.1 i.2) ^ 2 + (x j.1 j.2) ^ 2) / 2 := by
      rw [← sq_abs (x i.1 i.2), ← sq_abs (x j.1 j.2)]
      nlinarith [sq_nonneg (|x i.1 i.2| - |x j.1 j.2|)]
    linarith
  have hZ : 0 < ∫ x, gaussianWeight A x := integral_exp_pos hint0
  suffices hmain : IsUnit A.det ∧ ∀ i j : ι × Fin 3,
      (∫ x, x i.1 i.2 * x j.1 j.2 * gaussianWeight A x) / (∫ x, gaussianWeight A x) = A⁻¹ i j from
    ⟨hmain.1, hint0, hZ, hint2, hmain.2⟩
  set Z : ℝ := ∫ x, gaussianWeight A x with hZdef
  have hibp : ∀ i k : ι × Fin 3, ∑ j : ι × Fin 3, A k j * ∫ x, x i.1 i.2 * x j.1 j.2 * gaussianWeight A x =
      if i = k then Z else 0 := by
    intro i k
    have hw : ∀ x, HasFDerivAt (gaussianWeight A)
        (gaussianWeight A x • (-(1 / 2 : ℝ) • fderiv ℝ (quadForm A) x)) x := by
      intro x
      have h1 : HasFDerivAt (fun x => -(1 / 2 * quadForm A x))
          (-(1 / 2 : ℝ) • fderiv ℝ (quadForm A) x) x := by
        have := ((hasFDerivAt_quadForm A x).differentiableAt.hasFDerivAt).const_mul (-(1 / 2 : ℝ))
        refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
        simp only []
        ring
      exact h1.exp
    have hwd : ∀ x, fderiv ℝ (gaussianWeight A) x (coordBasis k) =
        -(gaussianWeight A x * ∑ j, A k j * x j.1 j.2) := by
      intro x
      rw [(hw x).fderiv]
      show gaussianWeight A x • (-(1 / 2 : ℝ) • fderiv ℝ (quadForm A) x (coordBasis k)) = _
      rw [fderiv_quadForm_coordBasis A hA]
      simp only [smul_eq_mul]
      ring
    have hfd : ∀ x, fderiv ℝ (fun x : ι → EuclideanSpace ℝ (Fin 3) => x i.1 i.2) x (coordBasis k) =
        if i = k then 1 else 0 := by
      intro x
      have : fderiv ℝ (fun x : ι → EuclideanSpace ℝ (Fin 3) => x i.1 i.2) x = coordCLM i :=
        (coordCLM i).hasFDerivAt.fderiv
      rw [this, coordCLM_coordBasis]
    have hsum : Integrable fun x => x i.1 i.2 * fderiv ℝ (gaussianWeight A) x (coordBasis k) := by
      have h1 : Integrable fun x => -∑ j, A k j * (x i.1 i.2 * x j.1 j.2 * gaussianWeight A x) :=
        (integrable_finset_sum _ fun j _ => (hint2 i j).const_mul _).neg
      refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      rw [hwd, mul_neg, Finset.mul_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hfg' : Integrable fun x => fderiv ℝ (fun x : ι → EuclideanSpace ℝ (Fin 3) => x i.1 i.2) x (coordBasis k) *
        gaussianWeight A x := by
      simp only [hfd]
      split_ifs
      · simpa using hint0
      · simp
    have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun x : ι → EuclideanSpace ℝ (Fin 3) => x i.1 i.2) (g := gaussianWeight A) (v := coordBasis k)
      hfg' hsum (hint1 i) (fun x _ => (coordCLM i).differentiableAt)
      (fun x _ => (hw x).differentiableAt)
    have hl : ∫ x, x i.1 i.2 * fderiv ℝ (gaussianWeight A) x (coordBasis k) =
        -∑ j, A k j * ∫ x, x i.1 i.2 * x j.1 j.2 * gaussianWeight A x := by
      have : (fun x : ι → EuclideanSpace ℝ (Fin 3) => x i.1 i.2 * fderiv ℝ (gaussianWeight A) x (coordBasis k)) =
          fun x => -∑ j, A k j * (x i.1 i.2 * x j.1 j.2 * gaussianWeight A x) := by
        funext x
        rw [hwd, mul_neg, Finset.mul_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [this, integral_neg, integral_finset_sum _ fun j _ => (hint2 i j).const_mul _]
      simp only [integral_const_mul]
    have hr : ∫ x, fderiv ℝ (fun x : ι → EuclideanSpace ℝ (Fin 3) => x i.1 i.2) x (coordBasis k) *
        gaussianWeight A x = if i = k then Z else 0 := by
      simp only [hfd]
      split_ifs
      · simp [hZdef]
      · simp
    rw [hl, hr] at hparts
    linarith
  have hmat : A * (Matrix.of fun i j : ι × Fin 3 => (∫ x, x i.1 i.2 * x j.1 j.2 * gaussianWeight A x) / Z) = 1 := by
    ext k i
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    have h1 := hibp i k
    have hcomm : ∀ j : ι × Fin 3, (∫ x, x j.1 j.2 * x i.1 i.2 * gaussianWeight A x) =
        ∫ x, x i.1 i.2 * x j.1 j.2 * gaussianWeight A x := by
      intro j
      congr 1
      funext x
      ring
    simp only [hcomm]
    rw [show (∑ j, A k j * ((∫ x, x i.1 i.2 * x j.1 j.2 * gaussianWeight A x) / Z)) =
        (∑ j, A k j * ∫ x, x i.1 i.2 * x j.1 j.2 * gaussianWeight A x) / Z by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring]
    rw [h1, Matrix.one_apply]
    by_cases h : i = k
    · subst h
      simp [hZ.ne']
    · simp [h, Ne.symm h]
  refine ⟨Matrix.isUnit_det_of_right_inverse hmat, fun i j => ?_⟩
  have := Matrix.inv_eq_right_inv hmat
  rw [this]
  rfl
end YangMills.Construction.GaussianMoments
end
