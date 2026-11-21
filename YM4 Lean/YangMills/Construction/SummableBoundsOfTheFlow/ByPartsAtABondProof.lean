import YangMills.Construction.SummableBoundsOfTheFlow.ByPartsAtABond
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.ColdStepAtMirrorFrames MeasureTheory
namespace YangMills.Construction.BondIntegration
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def bondBasis (i : Fin 3) : BondVector := EuclideanSpace.single i 1
theorem sum_smul_bondBasis (v : BondVector) : ∑ i, v i • bondBasis i = v := by
  ext k
  simp [bondBasis, Finset.sum_apply, Pi.single_apply]
def bondCoord (b : ι) (z : BondVector → BondVector) (i : Fin 3) (η : BondField ι) : ℝ := z (η b) i
theorem fderiv_bondCoord_apply (b : ι) {z : BondVector → BondVector} (hz : ContDiff ℝ 1 z) (i : Fin 3)
    (η : BondField ι) (e : BondField ι) :
    fderiv ℝ (bondCoord b z i) η e = (fderiv ℝ z (η b) (e b)) i := by
  have hproj : HasFDerivAt (fun ζ : BondField ι => ζ b)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b) η :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).hasFDerivAt
  have hzd : HasFDerivAt z (fderiv ℝ z (η b)) (η b) :=
    (hz.differentiable (by norm_num) (η b)).hasFDerivAt
  have hc := hzd.comp η hproj
  have hi : HasFDerivAt (fun w : BondVector => w i)
      (EuclideanSpace.proj i : BondVector →L[ℝ] ℝ) (z (η b)) :=
    (EuclideanSpace.proj i : BondVector →L[ℝ] ℝ).hasFDerivAt
  have h := hi.comp η hc
  have : fderiv ℝ (bondCoord b z i) η =
      ((EuclideanSpace.proj i : BondVector →L[ℝ] ℝ).comp ((fderiv ℝ z (η b)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b))) := h.fderiv
  rw [this]
  rfl
theorem differentiable_bondCoord (b : ι) {z : BondVector → BondVector} (hz : ContDiff ℝ 1 z) (i : Fin 3) :
    Differentiable ℝ (bondCoord (ι := ι) b z i) := by
  intro η
  have hd : Differentiable ℝ z := hz.differentiable (by norm_num)
  unfold bondCoord
  have h1 : DifferentiableAt ℝ (fun ζ : BondField ι => z (ζ b)) η :=
    (hd _).comp η (differentiableAt_apply b η)
  exact (EuclideanSpace.proj i : BondVector →L[ℝ] ℝ).differentiableAt.comp η h1
theorem integralByPartsAtBond : IntegralByPartsAtBond := by
  intro ι _ _ b z u C hz hzC hdC hu hui hdu
  have hcont : Continuous z := hz.continuous
  have hdcont : Continuous (fderiv ℝ z) := hz.continuous_fderiv (by norm_num)
  have hproj : Continuous fun η : BondField ι => η b := continuous_apply b
  set f : Fin 3 → BondField ι → ℝ := fun i η => bondCoord b z i η * u η with hf
  have hfd : ∀ i, Differentiable ℝ (f i) := fun i =>
    (differentiable_bondCoord b hz i).mul hu
  have hfderiv : ∀ i η, fderiv ℝ (f i) η (bondVariation b (bondBasis i)) =
      (fderiv ℝ z (η b) (bondBasis i)) i * u η + z (η b) i * fderiv ℝ u η (bondVariation b (bondBasis i)) := by
    intro i η
    have h1 := ((differentiable_bondCoord (ι := ι) b hz i η).hasFDerivAt).mul (hu η).hasFDerivAt
    have h2 : fderiv ℝ (f i) η = _ := h1.fderiv
    rw [h2]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_bondCoord_apply b hz i η]
    simp only [bondVariation, Pi.single_eq_same, bondCoord]
    ring
  have hzi : ∀ i, ∀ v, |z v i| ≤ C := by
    intro i v
    have := PiLp.norm_apply_le (z v) i
    exact (by simpa using this : ‖z v i‖ ≤ ‖z v‖).trans (hzC v) |>.trans' (le_of_eq rfl) |> fun h => by
      simpa [Real.norm_eq_abs] using h
  have hdz : ∀ i, ∀ v, |(fderiv ℝ z v (bondBasis i)) i| ≤ C := by
    intro i v
    have h1 : ‖(fderiv ℝ z v (bondBasis i)) i‖ ≤ ‖fderiv ℝ z v (bondBasis i)‖ := by
      simpa using PiLp.norm_apply_le (fderiv ℝ z v (bondBasis i)) i
    have h2 : ‖fderiv ℝ z v (bondBasis i)‖ ≤ ‖fderiv ℝ z v‖ * ‖bondBasis i‖ :=
      (fderiv ℝ z v).le_opNorm _
    have h3 : ‖bondBasis i‖ = 1 := by simp [bondBasis]
    rw [h3, mul_one] at h2
    have := (h1.trans h2).trans (hdC v)
    simpa [Real.norm_eq_abs] using this
  have hm1 : ∀ i, AEStronglyMeasurable (fun η : BondField ι => z (η b) i) volume := fun i =>
    ((continuous_apply (A := fun _ : Fin 3 => ℝ) i |>.comp
      ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp (hcont.comp hproj)))).aestronglyMeasurable
  have hm2 : ∀ i, AEStronglyMeasurable
      (fun η : BondField ι => (fderiv ℝ z (η b) (bondBasis i)) i) volume := fun i =>
    ((continuous_apply (A := fun _ : Fin 3 => ℝ) i |>.comp
      ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
        ((hdcont.comp hproj).clm_apply continuous_const)))).aestronglyMeasurable
  have hA : ∀ i, Integrable (fun η : BondField ι => (fderiv ℝ z (η b) (bondBasis i)) i * u η) := fun i =>
    hui.bdd_mul (c := C) (hm2 i) (Filter.Eventually.of_forall fun η => by
      simpa [Real.norm_eq_abs] using hdz i (η b))
  have hB : ∀ i, Integrable (fun η : BondField ι => z (η b) i * fderiv ℝ u η (bondVariation b (bondBasis i))) :=
    fun i => (hdu (bondBasis i)).bdd_mul (c := C) (hm1 i) (Filter.Eventually.of_forall fun η => by
      simpa [Real.norm_eq_abs] using hzi i (η b))
  have hzero : ∀ i, ∫ η, fderiv ℝ (f i) η (bondVariation b (bondBasis i)) = 0 := by
    intro i
    have hI : Integrable (fun η => fderiv ℝ (f i) η (bondVariation b (bondBasis i))) := by
      have := (hA i).add (hB i)
      refine this.congr (Filter.Eventually.of_forall fun η => ?_)
      simp only [Pi.add_apply]
      exact (hfderiv i η).symm
    have hfi : Integrable (f i) := by
      refine hui.bdd_mul (c := C) (hm1 i) (Filter.Eventually.of_forall fun η => ?_)
      simpa [Real.norm_eq_abs, bondCoord] using hzi i (η b)
    have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (BondField ι)))
      (f := f i) (g := fun _ => (1 : ℝ)) (v := bondVariation b (bondBasis i))
      (by simpa using hI) (by simp) (by simpa using hfi) (fun x _ => hfd i x)
      (fun x _ => differentiableAt_const _)
    simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, mul_zero,
      integral_zero, mul_one] at key
    linarith
  have hsum : ∀ η : BondField ι,
      fderiv ℝ u η (bondVariation b (z (η b))) + bondDivergence z (η b) * u η =
        ∑ i, fderiv ℝ (f i) η (bondVariation b (bondBasis i)) := by
    intro η
    simp only [hfderiv, Finset.sum_add_distrib]
    have e1 : bondVariation b (z (η b)) = ∑ i, (z (η b) i) • bondVariation b (bondBasis i) := by
      conv_lhs => rw [← sum_smul_bondBasis (z (η b))]
      funext c
      by_cases hc : c = b
      · subst hc
        simp [bondVariation, Finset.sum_apply]
      · simp [bondVariation, Finset.sum_apply, Pi.single_eq_of_ne hc]
    rw [e1, map_sum]
    simp only [map_smul, smul_eq_mul]
    unfold bondDivergence
    rw [Finset.sum_mul]
    simp only [bondBasis]
    ring
  simp only [hsum]
  rw [integral_finset_sum]
  · simp [hzero]
  · intro i _
    have := (hA i).add (hB i)
    refine this.congr (Filter.Eventually.of_forall fun η => ?_)
    simp only [Pi.add_apply]
    exact (hfderiv i η).symm
end YangMills.Construction.BondIntegration
end
