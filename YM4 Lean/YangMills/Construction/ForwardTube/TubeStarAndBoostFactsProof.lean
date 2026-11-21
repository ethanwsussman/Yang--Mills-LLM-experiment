import YangMills.Construction.ForwardTube.ArgumentsOfTheGramKernelProof
import YangMills.Construction.ForwardTube.ElementaryFactsOfTheTubeFramesStripSectorAndPencilsProof
import Mathlib
set_option autoImplicit false
open Complex (I)
open ComplexConjugate
noncomputable section
namespace YangMills.Construction.ForwardTube
namespace TubeBoostLemmas
theorem re_lightConePlus (v : ℂ × ℂ) : (lightConePlus v).re = v.1.re - v.2.im := by
  simp [lightConePlus, sub_eq_add_neg]
theorem re_lightConeMinus (v : ℂ × ℂ) : (lightConeMinus v).re = v.1.re + v.2.im := by
  simp [lightConeMinus]
theorem mem_forwardTube_iff (v : ℂ × ℂ) : v ∈ forwardTube ↔ v.1.re > |v.2.im| := by apply _root_.YangMills.Construction.ForwardTube.TubeGeometry.mem_forwardTube_iff_abs <;> assumption
theorem isOpen_forwardTube : IsOpen forwardTube := by
  have hp : Continuous fun v : ℂ × ℂ => (lightConePlus v).re := by
    unfold lightConePlus
    fun_prop
  have hm : Continuous fun v : ℂ × ℂ => (lightConeMinus v).re := by
    unfold lightConeMinus
    fun_prop
  exact (isOpen_lt continuous_const hp).inter (isOpen_lt continuous_const hm)
theorem add_mem_forwardTube {v w : ℂ × ℂ} (hv : v ∈ forwardTube) (hw : w ∈ forwardTube) :
    v + w ∈ forwardTube := by apply _root_.YangMills.Construction.ForwardTube.GramKernelArgs.add_mem_forwardTube <;> assumption
theorem smul_mem_forwardTube {v : ℂ × ℂ} (hv : v ∈ forwardTube) {c : ℝ} (hc : 0 < c) :
    c • v ∈ forwardTube := by
  obtain ⟨hp, hm⟩ := hv
  rw [gt_iff_lt, re_lightConePlus] at hp
  rw [gt_iff_lt, re_lightConeMinus] at hm
  refine ⟨?_, ?_⟩
  · rw [gt_iff_lt, re_lightConePlus]
    simp only [Prod.smul_fst, Prod.smul_snd, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    nlinarith [mul_pos hc hp]
  · rw [gt_iff_lt, re_lightConeMinus]
    simp only [Prod.smul_fst, Prod.smul_snd, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    nlinarith [mul_pos hc hm]
theorem forwardTube_inter_realVectors :
    forwardTube ∩ realVectors = embedPlane '' RealPlane.openRightHalf := by
  ext v
  constructor
  · rintro ⟨hv, hre, him⟩
    obtain ⟨hp, -⟩ := hv
    rw [gt_iff_lt, re_lightConePlus, him, sub_zero] at hp
    refine ⟨!₂[v.1.re, v.2.re], by simpa [RealPlane.openRightHalf] using hp, ?_⟩
    refine Prod.ext (Complex.ext ?_ ?_) (Complex.ext ?_ ?_) <;> simp [embedPlane, hre, him]
  · rintro ⟨x, hx, rfl⟩
    have hx' : 0 < x 0 := hx
    refine ⟨(mem_forwardTube_iff _).2 ?_, ?_, ?_⟩
    · simpa [embedPlane] using hx'
    · simp [embedPlane]
    · simp [embedPlane]
theorem lightConePlus_tubeStar (v : ℂ × ℂ) : lightConePlus (tubeStar v) = conj (lightConePlus v) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeSemigroup.lightConePlus_tubeStar_eq_conj <;> assumption
theorem lightConeMinus_tubeStar (v : ℂ × ℂ) :
    lightConeMinus (tubeStar v) = conj (lightConeMinus v) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeSemigroup.lightConeMinus_tubeStar_eq_conj <;> assumption
theorem tubeStar_embedPlane (x : RealPlane) :
    tubeStar (embedPlane x) = embedPlane (-RealPlane.reflectFirst x) := by
  simp [tubeStar, embedPlane, RealPlane.reflectFirst]
theorem exp_I_mul_add_I_mul (t s : ℝ) :
    Complex.exp (I * (t + I * s)) = (Real.exp (-s) : ℂ) * Complex.exp (I * t) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (s : ℂ) * Complex.I_sq
theorem exp_neg_I_mul_add_I_mul (t s : ℝ) :
    Complex.exp (-(I * (t + I * s))) = (Real.exp s : ℂ) * Complex.exp (-(I * t)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  linear_combination -(s : ℂ) * Complex.I_sq
theorem complexBoost_eq (z : ℂ) (v : ℂ × ℂ) : complexBoost z v =
    (v.1 * Complex.cos z - v.2 * Complex.sin z, v.1 * Complex.sin z + v.2 * Complex.cos z) := by
  obtain ⟨a, b⟩ := v
  have hI : (1 : ℂ) / (2 * I) = -I / 2 := by
    rw [one_div, mul_inv, Complex.inv_I]
    ring
  simp only [complexBoost, ofLightConeCoords, lightConePlus, lightConeMinus, Complex.cos,
    Complex.sin, Prod.mk.injEq, hI]
  rw [show z * I = I * z from mul_comm _ _, show -z * I = -(I * z) by ring]
  generalize Complex.exp (I * z) = p
  generalize Complex.exp (-(I * z)) = q
  constructor
  · ring
  · linear_combination (-b * (p + q) / 2) * Complex.I_sq
theorem isLinearMap_complexBoost (z : ℂ) : IsLinearMap ℂ (complexBoost z) := by
  refine ⟨fun v w => ?_, fun c v => ?_⟩
  · simp only [complexBoost_eq]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.snd_add]
      ring
    · simp only [Prod.fst_add, Prod.snd_add]
      ring
  · simp only [complexBoost_eq]
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
theorem complexBoost_eq_matrix (z : ℂ) (v : ℂ × ℂ) : complexBoost z v =
    (complexBoostMatrix z 0 0 * v.1 + complexBoostMatrix z 0 1 * v.2,
      complexBoostMatrix z 1 0 * v.1 + complexBoostMatrix z 1 1 * v.2) := by
  rw [complexBoost_eq]
  simp only [complexBoostMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine Prod.ext ?_ ?_
  · simp only
    ring
  · simp only
    ring
theorem complexBoost_ofReal_embedPlane (t : ℝ) (x : RealPlane) :
    complexBoost (t : ℂ) (embedPlane x) = embedPlane (RealPlane.rotate t x) := by
  rw [complexBoost_eq]
  simp [embedPlane, RealPlane.rotate]
theorem differentiable_complexBoostMatrix_entry (i j : Fin 2) :
    Differentiable ℂ fun z : ℂ => complexBoostMatrix z i j := by
  fin_cases i <;> fin_cases j <;> simp [complexBoostMatrix]
theorem isHolomorphicIn_complexBoostMatrix_entry (i j : Fin 2) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 1) (N' := 1) Set.univ
      fun w _ => complexBoostMatrix (w 0) i j := by
  have hd := differentiable_complexBoostMatrix_entry i j
  refine ⟨isOpen_univ, ?_, ?_⟩
  · exact (continuous_pi fun _ => hd.continuous.comp (continuous_apply 0)).continuousOn
  · intro a _ k
    refine Filter.Eventually.of_forall fun ζ => ?_
    refine differentiableAt_pi.2 fun _ => ?_
    have hline : DifferentiableAt ℂ
        (fun ζ : ℂ => (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector k) 0) ζ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    exact (hd _).comp ζ hline
theorem complexBoost_complexBoost (z w : ℂ) (v : ℂ × ℂ) :
    complexBoost z (complexBoost w v) = complexBoost (z + w) v := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeSemigroup.complexBoost_complexBoost <;> assumption
theorem complexBoost_zero (v : ℂ × ℂ) : complexBoost 0 v = v := by
  simpa [complexBoost] using ofLightConeCoords_lightConePlus_lightConeMinus v
end TubeBoostLemmas
open TubeBoostLemmas in
theorem tubeStarAndBoostFacts_holds : TubeStarAndBoostFacts :=
  ⟨⟨fun v => ⟨re_lightConePlus v, re_lightConeMinus v⟩, Set.ext mem_forwardTube_iff⟩,
    ⟨isOpen_forwardTube, fun _ hv _ hw => add_mem_forwardTube hv hw,
      fun _ hv _ hc => smul_mem_forwardTube hv hc, forwardTube_inter_realVectors⟩,
    ⟨fun v => ⟨lightConePlus_tubeStar v, lightConeMinus_tubeStar v⟩, tubeStar_embedPlane⟩,
    fun t s => ⟨exp_I_mul_add_I_mul t s, exp_neg_I_mul_add_I_mul t s⟩, isLinearMap_complexBoost,
    complexBoost_eq_matrix, complexBoost_eq, complexBoost_ofReal_embedPlane,
    isHolomorphicIn_complexBoostMatrix_entry, complexBoost_complexBoost, complexBoost_zero⟩
end YangMills.Construction.ForwardTube
end
