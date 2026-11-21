import YangMills.Construction.IdentificationOfTheOneLoopNumber.MixedVariationOfALogDeterminant
import Mathlib
set_option autoImplicit false
open Filter Topology Polynomial
noncomputable section
namespace YangMills.Construction.OneLoopCoefficient
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private def detLinearTerm (M M' : Matrix ι ι ℂ) : ℂ :=
  ∑ σ : Equiv.Perm ι, (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
    ∑ i, (∏ j ∈ Finset.univ.erase i, M (σ j) j) • M' (σ i) i
private theorem hasDerivAt_det_of_entries {M : ℝ → Matrix ι ι ℂ} {M' : Matrix ι ι ℂ} {t₀ : ℝ}
    (hM' : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) t₀) :
    HasDerivAt (fun t => (M t).det) (detLinearTerm (M t₀) M') t₀ := by
  have hexp : (fun t => (M t).det) = fun t => ∑ σ : Equiv.Perm ι,
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ∏ i, M t (σ i) i := by
    funext t
    rw [Matrix.det_apply']
  rw [hexp]
  unfold detLinearTerm
  refine HasDerivAt.fun_sum fun σ _ => ?_
  refine HasDerivAt.const_mul _ ?_
  exact HasDerivAt.fun_finset_prod fun i _ => hM' (σ i) i
private theorem hasDerivAt_det_one_add_smul (X : Matrix ι ι ℂ) :
    HasDerivAt (fun r : ℂ => ((1 : Matrix ι ι ℂ) + r • X).det) X.trace 0 := by
  have hexp : (fun r : ℂ => ((1 : Matrix ι ι ℂ) + r • X).det) = fun r =>
      1 + X.trace * r + (Polynomial.eval r
        (Matrix.det ((1 : Matrix ι ι ℂ[X]) + (Polynomial.X : ℂ[X]) • X.map Polynomial.C)).divX.divX) * r ^ 2 := by
    funext r
    exact Matrix.det_one_add_smul r X
  rw [hexp]
  set q : ℂ[X] :=
    (Matrix.det ((1 : Matrix ι ι ℂ[X]) + (Polynomial.X : ℂ[X]) • X.map Polynomial.C)).divX.divX
  have hsum := (((hasDerivAt_id (0 : ℂ)).const_mul X.trace).const_add 1).add
    ((q.hasDerivAt 0).mul ((hasDerivAt_id (0 : ℂ)).pow 2))
  refine hsum.congr_deriv ?_
  simp
private theorem detLinearTerm_eq_det_mul_trace {M X : Matrix ι ι ℂ} (hM : IsUnit M.det) :
    detLinearTerm M X = M.det * (M⁻¹ * X).trace := by
  have hline : HasDerivAt (fun t : ℝ => (M + (t : ℂ) • X).det) (detLinearTerm (M + ((0 : ℝ) : ℂ) • X) X) 0 := by
    refine hasDerivAt_det_of_entries fun i j => ?_
    have hij := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (X i j)).const_add (M i j)
    refine (hij.congr_deriv ?_)
    simp
  have hbase : (M + ((0 : ℝ) : ℂ) • X) = M := by simp
  rw [hbase] at hline
  have hfactor : (fun t : ℝ => (M + (t : ℂ) • X).det) =
      fun t : ℝ => M.det * ((1 : Matrix ι ι ℂ) + (t : ℂ) • (M⁻¹ * X)).det := by
    funext t
    rw [← Matrix.det_mul, mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv M hM, Matrix.one_mul]
  have hfactored : HasDerivAt (fun t : ℝ => M.det * ((1 : Matrix ι ι ℂ) + (t : ℂ) • (M⁻¹ * X)).det)
      (M.det * (M⁻¹ * X).trace) 0 := by
    have hreal := (hasDerivAt_det_one_add_smul (M⁻¹ * X)).comp_ofReal
    exact hreal.const_mul _
  rw [hfactor] at hline
  exact hline.unique hfactored
private theorem hasDerivAt_det_jacobi {M : ℝ → Matrix ι ι ℂ} {M' : Matrix ι ι ℂ} {t₀ : ℝ}
    (hM' : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) t₀) (hM : IsUnit (M t₀).det) :
    HasDerivAt (fun t => (M t).det) ((M t₀).det * ((M t₀)⁻¹ * M').trace) t₀ := by
  rw [← detLinearTerm_eq_det_mul_trace hM]
  exact hasDerivAt_det_of_entries hM'
private theorem differentiableAt_inv_apply {M : ℝ → Matrix ι ι ℂ} {M' : Matrix ι ι ℂ} {t₀ : ℝ}
    (hM' : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) t₀) (hM : IsUnit (M t₀).det) (i j : ι) :
    DifferentiableAt ℝ (fun t => (M t)⁻¹ i j) t₀ := by
  have hdet : DifferentiableAt ℝ (fun t => (M t).det) t₀ := (hasDerivAt_det_jacobi hM' hM).differentiableAt
  have hne : (M t₀).det ≠ 0 := hM.ne_zero
  have hadj : DifferentiableAt ℝ (fun t => Matrix.adjugate (M t) i j) t₀ := by
    have hrow : (fun t => Matrix.adjugate (M t) i j) =
        fun t => ((M t).updateRow j (Pi.single i 1)).det := by
      funext t
      rw [Matrix.adjugate_apply]
    rw [hrow]
    refine (hasDerivAt_det_of_entries (M' := M'.updateRow j 0) fun a b => ?_).differentiableAt
    by_cases hab : a = j
    · subst hab
      simpa [Matrix.updateRow_self] using hasDerivAt_const t₀ ((Pi.single i (1 : ℂ) : ι → ℂ) b)
    · simpa [Matrix.updateRow_ne hab] using hM' a b
  have hinv : (fun t => (M t)⁻¹ i j) = fun t => ((M t).det)⁻¹ * Matrix.adjugate (M t) i j := by
    funext t
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [hinv]
  exact (hdet.inv hne).mul hadj
private theorem hasDerivAt_inv_apply {M : ℝ → Matrix ι ι ℂ} {M' : Matrix ι ι ℂ} {t₀ : ℝ}
    (hM' : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) t₀) (hM : IsUnit (M t₀).det) (i j : ι) :
    HasDerivAt (fun t => (M t)⁻¹ i j) (-((M t₀)⁻¹ * M' * (M t₀)⁻¹) i j) t₀ := by
  have hd := fun a b => (differentiableAt_inv_apply hM' hM a b).hasDerivAt
  set N : Matrix ι ι ℂ := fun a b => deriv (fun t => (M t)⁻¹ a b) t₀ with hN
  have hdN : ∀ a b, HasDerivAt (fun t => (M t)⁻¹ a b) (N a b) t₀ := hd
  have hcont : ContinuousAt (fun t => (M t).det) t₀ :=
    (hasDerivAt_det_jacobi hM' hM).continuousAt
  have hunit : ∀ᶠ t in 𝓝 t₀, IsUnit (M t).det := by
    have hne := hcont.eventually_ne hM.ne_zero
    exact hne.mono fun t ht => isUnit_iff_ne_zero.2 ht
  have hprod : ∀ a b, HasDerivAt (fun t => ((M t) * (M t)⁻¹) a b) ((M' * (M t₀)⁻¹ + M t₀ * N) a b) t₀ := by
    intro a b
    have hmul : (fun t => ((M t) * (M t)⁻¹) a b) = fun t => ∑ c, M t a c * (M t)⁻¹ c b := by
      funext t
      rw [Matrix.mul_apply]
    rw [hmul, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    exact HasDerivAt.fun_sum fun c _ => (hM' a c).mul (hdN c b)
  have hzero : ∀ a b, (M' * (M t₀)⁻¹ + M t₀ * N) a b = 0 := by
    intro a b
    have hconst : HasDerivAt (fun t => ((M t) * (M t)⁻¹) a b) 0 t₀ := by
      refine (hasDerivAt_const t₀ ((1 : Matrix ι ι ℂ) a b)).congr_of_eventuallyEq ?_
      exact hunit.mono fun t ht => by
        show (M t * (M t)⁻¹) a b = (1 : Matrix ι ι ℂ) a b
        rw [Matrix.mul_nonsing_inv _ ht]
    exact (hprod a b).unique hconst
  have hsum : M' * (M t₀)⁻¹ + M t₀ * N = 0 := by
    ext a b
    exact hzero a b
  have hNeq : N = -((M t₀)⁻¹ * M' * (M t₀)⁻¹) := by
    have hMN : M t₀ * N = -(M' * (M t₀)⁻¹) := eq_neg_of_add_eq_zero_right hsum
    calc N = (M t₀)⁻¹ * (M t₀ * N) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]
      _ = _ := by rw [hMN, Matrix.mul_neg, Matrix.mul_assoc]
  have hij := hdN i j
  rw [hNeq, Matrix.neg_apply] at hij
  exact hij
theorem hasDerivAt_mixed_logDet : hasDerivAt_mixed_logDet_statement := by
  intro ι _ _ K K₁ K₁' K₂ hdiff hK₁ hK₁' hK₂ hslit
  have hne : (K 0 0).det ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hu0 : IsUnit (K 0 0).det := isUnit_iff_ne_zero.2 hne
  have hcont : ContinuousAt (fun u => (K u 0).det) 0 :=
    (hasDerivAt_det_of_entries hK₁).continuousAt
  have hslitNear : ∀ᶠ u in 𝓝 (0 : ℝ), (K u 0).det ∈ Complex.slitPlane :=
    hcont.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hslit)
  set P : ℝ → Matrix ι ι ℂ := fun u i j => deriv (fun t => K u t i j) 0 with hP
  have hlog : ∀ᶠ u in 𝓝 (0 : ℝ), HasDerivAt (fun t => Complex.log (K u t).det)
      ((K u 0)⁻¹ * P u).trace 0 := by
    filter_upwards [hdiff, hslitNear] with u hu hs
    have hun : IsUnit (K u 0).det := isUnit_iff_ne_zero.2 (Complex.slitPlane_ne_zero hs)
    have hjac := hasDerivAt_det_jacobi (M := K u) (M' := P u) (t₀ := 0)
      (fun i j => (hu i j).hasDerivAt) hun
    have hclog := hjac.clog_real hs
    refine hclog.congr_deriv ?_
    field_simp [Complex.slitPlane_ne_zero hs]
  have hfirst : (fun u => deriv (fun t => Complex.log (K u t).det) 0) =ᶠ[𝓝 0]
      fun u => ((K u 0)⁻¹ * P u).trace := hlog.mono fun u hu => hu.deriv
  refine ⟨hlog.mono fun u hu => hu.differentiableAt, HasDerivAt.congr_of_eventuallyEq ?_ hfirst⟩
  have htr : (fun u => ((K u 0)⁻¹ * P u).trace) = fun u => ∑ i, ∑ j, (K u 0)⁻¹ i j * P u j i := by
    funext u
    simp [Matrix.trace, Matrix.mul_apply]
  rw [htr]
  have hder : HasDerivAt (fun u => ∑ i, ∑ j, (K u 0)⁻¹ i j * P u j i)
      (∑ i, ∑ j, ((-((K 0 0)⁻¹ * K₁ * (K 0 0)⁻¹) i j) * P 0 j i + (K 0 0)⁻¹ i j * K₂ j i)) 0 := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    exact (hasDerivAt_inv_apply (M := fun u => K u 0) hK₁ hu0 i j).mul (hK₂ j i)
  refine hder.congr_deriv ?_
  have hP0 : P 0 = K₁' := by
    ext i j
    exact (hK₁' i j).deriv
  rw [hP0]
  have hA : ((K 0 0)⁻¹ * K₂).trace = ∑ i, ∑ j, (K 0 0)⁻¹ i j * K₂ j i := by
    simp [Matrix.trace, Matrix.mul_apply]
  have hB : ((K 0 0)⁻¹ * K₁ * ((K 0 0)⁻¹ * K₁')).trace =
      ∑ i, ∑ j, ((K 0 0)⁻¹ * K₁ * (K 0 0)⁻¹) i j * K₁' j i := by
    rw [← Matrix.mul_assoc]
    simp [Matrix.trace, Matrix.mul_apply]
  rw [hA, hB, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end YangMills.Construction.OneLoopCoefficient
