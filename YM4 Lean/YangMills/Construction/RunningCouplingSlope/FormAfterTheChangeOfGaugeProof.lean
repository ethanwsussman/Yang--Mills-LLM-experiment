import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreUnderAGaugeFunctionProof
import YangMills.Construction.RunningCouplingSlope.DriftOfALeastPointIsLinearProof
import YangMills.Construction.RunningCouplingSlope.ChainNumberReadsNoPointProof
import YangMills.Construction.RunningCouplingSlope.FibreDirectionsAtALeastPointProof
import YangMills.Construction.RunningCouplingSlope.FormAfterTheChangeOfGauge
import YangMills.Construction.Towers.QuadraticFormsAndTransposesOnTheRealSpacesProof
import Mathlib
import YangMills.Construction.Matrices.SpecialUnitaryTwo
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.GaugeChangeHessian
open Filter Tower Matrices
open scoped Topology
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
theorem hasDerivAt_mixedDeriv {Φ : E → F} {x : E} (hΦ : ContDiffAt ℝ 2 Φ x) {g : ℝ → ℝ → E}
    {v : ℝ → E} {u w : E} (h0 : g 0 0 = x) (hv : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (g s) (v s) 0)
    (hu : HasDerivAt (fun s => g s 0) u 0) (hw : HasDerivAt v w 0) :
    HasDerivAt (fun s => deriv (fun t => Φ (g s t)) 0)
      (fderiv ℝ (fderiv ℝ Φ) x u (v 0) + fderiv ℝ Φ x w) 0 := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ Φ y :=
    (hΦ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hc : Tendsto (fun s => g s 0) (𝓝 0) (𝓝 x) := by
    have := hu.continuousAt.tendsto
    simpa [h0] using this
  have heq : (fun s => deriv (fun t => Φ (g s t)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ Φ (g s 0) (v s) := by
    filter_upwards [hc.eventually hd, hv] with s h1 h2
    exact (h1.hasFDerivAt.comp_hasDerivAt 0 h2).deriv
  have hD : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) x) x :=
    ((hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hL : HasDerivAt (fun s => fderiv ℝ Φ (g s 0)) (fderiv ℝ (fderiv ℝ Φ) x u) 0 := by
    have h := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (f := fun s => g s 0)
      (l := fderiv ℝ Φ) (l' := fderiv ℝ (fderiv ℝ Φ) x) (f' := u) (by simpa [h0] using hD) hu
    exact h
  have h3 := hL.clm_apply hw
  rw [h0] at h3
  exact h3.congr_of_eventuallyEq heq
theorem hasDerivAt_mixedDeriv_line {Φ : E → F} (hΦ : ContDiffAt ℝ 2 Φ 0) (a b : E) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => Φ (s • a + t • b)) 0)
      (fderiv ℝ (fderiv ℝ Φ) 0 a b) 0 := by
  have h := hasDerivAt_mixedDeriv (g := fun s t => s • a + t • b) (v := fun _ => b) (u := a)
    (w := 0) hΦ
    (by simp) (Eventually.of_forall fun s => by
      have h1 : HasDerivAt (fun t : ℝ => t • b) ((1 : ℝ) • b) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const b
      simpa using h1.const_add (s • a))
    (by
      have h1 : HasDerivAt (fun s : ℝ => s • a) ((1 : ℝ) • a) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const a
      simpa using h1)
    (hasDerivAt_const _ _)
  simpa using h
end
section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
def expChart (x a : A) : A := NormedSpace.exp a * x
theorem contDiffAt_normedExp (a : A) : ContDiffAt ℝ 2 (NormedSpace.exp : A → A) a :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) a).contDiffAt
theorem contDiffAt_expChart (x a : A) : ContDiffAt ℝ 2 (expChart x) a :=
  (contDiffAt_normedExp a).mul contDiffAt_const
theorem expChart_zero (x : A) : expChart x 0 = x := by simp [expChart]
theorem hasDerivAt_expChart_ray (x a : A) (s : ℝ) :
    HasDerivAt (fun t : ℝ => expChart x ((s + t) • a))
      (NormedSpace.exp (s • a) * a * x) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) a s
  have h2 : HasDerivAt (fun t : ℝ => NormedSpace.exp ((s + t) • a))
      (NormedSpace.exp (s • a) * a) 0 := by
    have := HasDerivAt.comp_const_add (a := s) (x := (0 : ℝ))
      (f := fun u : ℝ => NormedSpace.exp (u • a)) (by simpa using h)
    simpa using this
  exact h2.mul_const x
variable {Φ : A → ℝ} {x : A}
def pullChart (Φ : A → ℝ) (x a : A) : ℝ := Φ (expChart x a)
theorem contDiffAt_pullChart (hΦ : ContDiffAt ℝ 2 Φ x) : ContDiffAt ℝ 2 (pullChart Φ x) 0 := by
  have h : ContDiffAt ℝ 2 Φ (expChart x 0) := by simpa [expChart_zero] using hΦ
  exact h.comp 0 (contDiffAt_expChart x 0)
theorem hessian_pullChart_diag (hΦ : ContDiffAt ℝ 2 Φ x) (a : A) :
    fderiv ℝ (fderiv ℝ (pullChart Φ x)) 0 a a =
      fderiv ℝ (fderiv ℝ Φ) x (a * x) (a * x) + fderiv ℝ Φ x (a * a * x) := by
  have hG := contDiffAt_pullChart hΦ
  have h1 := hasDerivAt_mixedDeriv (g := fun s t => (s + t) • a) (v := fun _ => a) (u := a)
    (w := 0) hG
    (by simp) (Eventually.of_forall fun s => by
      have h : HasDerivAt (fun t : ℝ => (s + t) • a) ((1 : ℝ) • a) 0 :=
        ((hasDerivAt_id (0 : ℝ)).const_add s).smul_const a
      simpa using h)
    (by
      have h : HasDerivAt (fun t : ℝ => t • a) ((1 : ℝ) • a) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const a
      simpa using h)
    (hasDerivAt_const _ _)
  have h2 := hasDerivAt_mixedDeriv (Φ := Φ) (x := x) (g := fun s t => expChart x ((s + t) • a))
    (v := fun s => NormedSpace.exp (s • a) * a * x) (u := a * x) (w := a * a * x) hΦ
    (by simp [expChart_zero]) (Eventually.of_forall fun s => hasDerivAt_expChart_ray x a s)
    (by
      have h := hasDerivAt_expChart_ray x a 0
      simp only [zero_add, zero_smul, NormedSpace.exp_zero, one_mul] at h
      have e : (fun s : ℝ => expChart x ((s + 0) • a)) = fun s => expChart x (s • a) := by simp
      simpa [e] using h)
    (by
      have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) a (0 : ℝ)).mul_const a).mul_const x
      simpa using h)
  have e : (fun s : ℝ => deriv (fun t : ℝ => pullChart Φ x ((s + t) • a)) 0) =
      fun s : ℝ => deriv (fun t : ℝ => Φ (expChart x ((s + t) • a))) 0 := rfl
  rw [e] at h1
  have := h1.unique h2
  simpa using this
theorem hessian_pullChart (hΦ : ContDiffAt ℝ 2 Φ x) (a b : A) :
    fderiv ℝ (fderiv ℝ (pullChart Φ x)) 0 a b =
      fderiv ℝ (fderiv ℝ Φ) x (a * x) (b * x) +
        (1 / 2 : ℝ) * fderiv ℝ Φ x ((a * b + b * a) * x) := by
  have hG := contDiffAt_pullChart hΦ
  have sG : fderiv ℝ (fderiv ℝ (pullChart Φ x)) 0 b a =
      fderiv ℝ (fderiv ℝ (pullChart Φ x)) 0 a b :=
    hG.isSymmSndFDerivAt (by simp) b a
  have sΦ : fderiv ℝ (fderiv ℝ Φ) x (b * x) (a * x) = fderiv ℝ (fderiv ℝ Φ) x (a * x) (b * x) :=
    hΦ.isSymmSndFDerivAt (by simp) _ _
  have d1 := hessian_pullChart_diag hΦ (a + b)
  have d2 := hessian_pullChart_diag hΦ a
  have d3 := hessian_pullChart_diag hΦ b
  have e : (a + b) * (a + b) * x = a * a * x + b * b * x + (a * b + b * a) * x := by
    noncomm_ring
  rw [e, add_mul] at d1
  simp only [map_add, add_apply] at d1
  rw [sG] at d1
  rw [sΦ] at d1
  linarith
theorem hessian_twoSided_invariance (hΦ : ContDiffAt ℝ 2 Φ x) (a α γ : A)
    (hinv : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᶠ t in 𝓝 (0 : ℝ),
      Φ (NormedSpace.exp (t • α) * expChart x (s • a) * NormedSpace.exp (t • γ)) =
        Φ (expChart x (s • a))) :
    fderiv ℝ (fderiv ℝ Φ) x (a * x) (α * x + x * γ) + fderiv ℝ Φ x (α * a * x + a * x * γ) = 0 := by
  have hc0 : ∀ s : ℝ, HasDerivAt
      (fun t : ℝ => NormedSpace.exp (t • α) * expChart x (s • a) * NormedSpace.exp (t • γ))
      (α * expChart x (s • a) + expChart x (s • a) * γ) 0 := by
    intro s
    have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) α (0 : ℝ)
    have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) γ (0 : ℝ)
    have h3 := (h1.mul_const (expChart x (s • a))).mul h2
    exact h3.congr_deriv (by simp)
  have hcs : HasDerivAt (fun s : ℝ => expChart x (s • a)) (a * x) 0 := by
    have h := hasDerivAt_expChart_ray x a 0
    simp only [zero_add, zero_smul, NormedSpace.exp_zero, one_mul] at h
    simpa using h
  have h1 := hasDerivAt_mixedDeriv (Φ := Φ) (x := x)
    (g := fun s t => NormedSpace.exp (t • α) * expChart x (s • a) * NormedSpace.exp (t • γ))
    (v := fun s => α * expChart x (s • a) + expChart x (s • a) * γ) (u := a * x)
    (w := α * (a * x) + a * x * γ) hΦ (by simp [expChart_zero])
    (Eventually.of_forall hc0) (by simpa using hcs)
    ((hcs.const_mul α).add (hcs.mul_const γ))
  have h2 : HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => Φ
      (NormedSpace.exp (t • α) * expChart x (s • a) * NormedSpace.exp (t • γ))) 0) (0 : ℝ)
      (0 : ℝ) := by
    have e : (fun s : ℝ => deriv (fun t : ℝ => Φ
        (NormedSpace.exp (t • α) * expChart x (s • a) * NormedSpace.exp (t • γ))) 0) =ᶠ[𝓝 (0 : ℝ)]
        fun _ => (0 : ℝ) := by
      filter_upwards [hinv] with s hs
      have : (fun t : ℝ => Φ (NormedSpace.exp (t • α) * expChart x (s • a) *
          NormedSpace.exp (t • γ))) =ᶠ[𝓝 (0 : ℝ)] fun _ => Φ (expChart x (s • a)) := hs
      rw [this.deriv_eq]
      simp
    exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq e
  have h3 := h1.unique h2
  simp only [zero_smul, expChart_zero] at h3
  rw [mul_assoc α a x]
  simpa using h3
theorem hasDerivAt_mixedDeriv_twisted (hΦ : ContDiffAt ℝ 2 Φ x) (a : A) {e : ℝ → A}
    (he : ContDiffAt ℝ 2 e 0) (e0 : e 0 = 1) (e1 : deriv e 0 = 0) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => Φ (e (s + t) * expChart x ((s + t) • a))) 0)
      (fderiv ℝ (fderiv ℝ Φ) x (a * x) (a * x) +
        fderiv ℝ Φ x (deriv (deriv e) 0 * x + a * a * x)) 0 := by
  have hed : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ e s :=
    (he.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have he2 : HasDerivAt (deriv e) (deriv (deriv e) 0) 0 := by
    have : ContDiffAt ℝ 1 (deriv e) 0 := by
      have h := he.fderiv_right (m := 1) (by norm_num)
      have h2 : deriv e = fun t => fderiv ℝ e t 1 := by
        funext t; simp
      rw [h2]
      exact h.clm_apply contDiffAt_const
    exact (this.differentiableAt (by norm_num)).hasDerivAt
  have hcl : ∀ s : ℝ, HasDerivAt (fun r : ℝ => expChart x (r • a))
      (NormedSpace.exp (s • a) * a * x) s := by
    intro s
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) a s
    exact h.mul_const x
  have hp : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun t : ℝ => e (s + t) * expChart x ((s + t) • a))
      (deriv e s * expChart x (s • a) + e s * (NormedSpace.exp (s • a) * a * x)) 0 := by
    filter_upwards [hed] with s hs
    have h1 : HasDerivAt (fun r : ℝ => e r * expChart x (r • a))
        (deriv e s * expChart x (s • a) + e s * (NormedSpace.exp (s • a) * a * x)) s :=
      hs.hasDerivAt.mul (hcl s)
    have := HasDerivAt.comp_const_add (a := s) (x := (0 : ℝ))
      (f := fun r : ℝ => e r * expChart x (r • a)) (by simpa using h1)
    simpa using this
  have hedz : HasDerivAt e 0 0 := by
    have := hed.self_of_nhds.hasDerivAt
    rwa [e1] at this
  have hu : HasDerivAt (fun s : ℝ => e (s + 0) * expChart x ((s + 0) • a)) (a * x) 0 := by
    have h1 := hedz.mul (hcl 0)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul, e0, zero_mul, zero_add] at h1
    have e' : (fun s : ℝ => e (s + 0) * expChart x ((s + 0) • a)) =
        fun s => e s * expChart x (s • a) := by
      simp
    rw [e']
    exact h1
  have hw : HasDerivAt
      (fun s : ℝ => deriv e s * expChart x (s • a) + e s * (NormedSpace.exp (s • a) * a * x))
      (deriv (deriv e) 0 * x + a * a * x) 0 := by
    have h1 := he2.mul (hcl 0)
    have h2 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • a) * a * x) (a * a * x) 0 := by
      have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) a (0 : ℝ)).mul_const a).mul_const x
      simpa using h
    have h3 := hedz.mul h2
    have h4 := h1.add h3
    exact h4.congr_deriv (by simp [e1, e0, expChart_zero])
  have h := hasDerivAt_mixedDeriv (Φ := Φ) (x := x)
    (g := fun s t => e (s + t) * expChart x ((s + t) • a))
    (v := fun s => deriv e s * expChart x (s • a) + e s * (NormedSpace.exp (s • a) * a * x))
    (u := a * x) (w := deriv (deriv e) 0 * x + a * a * x) hΦ
    (by simp [e0, expChart_zero]) hp hu hw
  simpa [e0, e1, expChart_zero] using h
end
section
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
theorem contDiff_entry (i j : Fin 2) : ContDiff ℝ 2 (fun M : ComplexMatrix2 => M i j) := by apply _root_.YangMills.SharedProofs.p27324 <;> assumption
theorem contDiffAt_det {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀) :
    ContDiffAt ℝ 2 (fun y => (f y).det) y₀ := by apply _root_.YangMills.SharedProofs.p38879 <;> assumption
theorem contDiffAt_matInv {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀)
    (hu : IsUnit (f y₀).det) : ContDiffAt ℝ 2 (fun y => (f y)⁻¹) y₀ := by apply _root_.YangMills.SharedProofs.p22704 <;> assumption
theorem contDiffAt_cplxSmul {f : Y → ℂ} {g : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀)
    (hg : ContDiffAt ℝ 2 g y₀) : ContDiffAt ℝ 2 (fun y => f y • g y) y₀ := by apply _root_.YangMills.SharedProofs.p3257 <;> assumption
theorem contDiffAt_cpow_half {f : Y → ℂ} (hf : ContDiffAt ℝ 2 f y₀)
    (hs : f y₀ ∈ Complex.slitPlane) : ContDiffAt ℝ 2 (fun y => f y ^ (1 / 2 : ℂ)) y₀ := by apply _root_.YangMills.SharedProofs.p3856 <;> assumption
variable {L n k j : ℕ}
theorem contDiffAt_contourMean [NeZero L] {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Edge L n k (j + 1)) : ContDiffAt ℝ 2 (fun y => contourMean (V y) c) y₀ := by apply _root_.YangMills.SharedProofs.p1840 <;> assumption
theorem contDiffAt_meanRadius [NeZero L] {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Edge L n k (j + 1)) (hs : (contourMean (V y₀) c).det ∈ Complex.slitPlane) :
    ContDiffAt ℝ 2 (fun y => meanRadius (V y) c) y₀ :=
  contDiffAt_cpow_half (contDiffAt_det (contDiffAt_contourMean hV hu c)) hs
theorem contDiffAt_normalizedMean [NeZero L] {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Edge L n k (j + 1)) (hs : (contourMean (V y₀) c).det ∈ Complex.slitPlane)
    (hl : meanRadius (V y₀) c ≠ 0) :
    ContDiffAt ℝ 2 (fun y => normalizedMean (V y) c) y₀ :=
  contDiffAt_cplxSmul ((contDiffAt_meanRadius hV hu c hs).inv hl) (contDiffAt_contourMean hV hu c)
end
section
def quaternionMatrices : Submodule ℝ ComplexMatrix2 where
  carrier := {M | M 1 1 = star (M 0 0) ∧ M 1 0 = -star (M 0 1)}
  add_mem' := by
    rintro A B ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · simp [Matrix.add_apply, h1, h3]
    · simp only [Matrix.add_apply, h2, h4, star_add]; ring
  zero_mem' := by simp
  smul_mem' := by
    rintro c A ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · simp [Matrix.smul_apply, h1]
    · simp [Matrix.smul_apply, h2]
theorem mem_quaternionMatrices_of_mem {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : g ∈ quaternionMatrices :=
  ComplexMatrix2.quaternion_entries_of_mem_specialUnitary hg
theorem det_of_mem_quaternionMatrices {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices) :
    M.det = ((Complex.normSq (M 0 0) + Complex.normSq (M 0 1) : ℝ) : ℂ) :=
  ComplexMatrix2.det_quaternionMatrix hM
theorem det_mem_slitPlane_of_quaternion {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices)
    (h : M.det ≠ 0) : M.det ∈ Complex.slitPlane :=
  ComplexMatrix2.det_quaternionMatrix_mem_slitPlane hM h
theorem normalize_mem_compact {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices) (h : M.det ≠ 0) :
    (M.det ^ (1 / 2 : ℂ))⁻¹ • M ∈ PeriodicLattice.compactGaugeGroup :=
  ComplexMatrix2.normalize_quaternionMatrix_mem_specialUnitary hM h
variable {L n k j : ℕ}
theorem compact_mul_mem {g h : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hh : h ∈ PeriodicLattice.compactGaugeGroup) : g * h ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
theorem compact_inv_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem compact_det {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem compact_isUnit_det {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem pathHolonomy_mem_compact {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy V Γ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p6330 <;> assumption
theorem contourMean_mem_quaternionMatrices [NeZero L] {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) (c : Edge L n k (j + 1)) :
    contourMean V c ∈ quaternionMatrices := by
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  have hs : ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) =
      (((1 / 24 : ℝ) * ((L : ℝ) ^ (-4 : ℤ)) : ℝ) : ℂ) := by
    simp [PeriodicLattice.inverseFourthPowerWeight]
  rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin, hs, Complex.coe_smul]
  refine quaternionMatrices.smul_mem _
    (quaternionMatrices.sum_mem fun x _ => quaternionMatrices.sum_mem fun π _ => ?_)
  exact mem_quaternionMatrices_of_mem (compact_mul_mem
    (compact_mul_mem (pathHolonomy_mem_compact hV _) (pathHolonomy_mem_compact hV _))
    (compact_inv_mem (pathHolonomy_mem_compact hV _)))
end
section
variable {L n k j : ℕ}
theorem fieldOfPositiveValues_pos (w : PositiveEdge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) : fieldOfPositiveValues w b = w ⟨b, h⟩ := by
  simp [fieldOfPositiveValues, h]
theorem fieldOfPositiveValues_neg (w : PositiveEdge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : ¬b.IsPositivelyOriented) :
    fieldOfPositiveValues w b =
      (w ⟨b.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented h⟩)⁻¹ := by
  simp [fieldOfPositiveValues, h, PeriodicLattice.Bond.opposite_isPositivelyOriented h]
theorem fieldOfPositiveValues_mem {w : PositiveEdge L n k j → ComplexMatrix2}
    (hw : ∀ c, w c ∈ PeriodicLattice.compactGaugeGroup)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    fieldOfPositiveValues w ∈ fieldSpace L n k j := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.fieldOfPositiveValues_mem_fieldSpace <;> assumption
end
section
variable {L n k : ℕ}
theorem levelField_succ_of_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
theorem meanRadius_ne_zero {X : ChainPoint L n k} (hX : IsCompactValued X) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) : meanRadius (levelField X i) c.1 ≠ 0 := by apply _root_.YangMills.SharedProofs.p17043 <;> assumption
theorem det_contourMean_ne_zero {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    {c : Edge L n k (j + 1)} (h : meanRadius V c ≠ 0) : (contourMean V c).det ≠ 0 := by apply _root_.YangMills.SharedProofs.p15699 <;> assumption
end
section
variable {L n k : ℕ} [NeZero L] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
  {Z : Y → ChainPoint L n k}
theorem isUnit_det_of_mem_fieldSpace {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (b : Edge L n k j) :
    IsUnit (V b).det := compact_isUnit_det (hV.1 b (Set.mem_univ b))
theorem contDiffAt_levelField (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀)) :
    ∀ j, j ≤ k → ∀ b, ContDiffAt ℝ 2 (fun y => levelField (Z y) j b) y₀ := by apply _root_.YangMills.SharedProofs.p4722 <;> assumption
theorem contDiffAt_levelRadius (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀))
    (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun y => meanRadius (levelField (Z y) i) c.1) y₀ := by apply _root_.YangMills.SharedProofs.p8907 <;> assumption
theorem contDiffAt_chainAction (a : ℝ) (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀)) :
    ContDiffAt ℝ 2 (fun y => chainAction a (Z y)) y₀ := by apply _root_.YangMills.SharedProofs.p6648 <;> assumption
end
section
variable {L n k : ℕ}
abbrev Coord (L n k : ℕ) : Type :=
  PositiveEdge L n k 0 ⊕ (Σ i : Fin k, PositiveEdge L n k (i + 1))
instance instFintypeCoord [NeZero L] : Fintype (Coord L n k) := Fintype.ofFinite _
def pointOfValues (w : Coord L n k → ComplexMatrix2) : ChainPoint L n k :=
  ⟨fieldOfPositiveValues fun b => w (Sum.inl b), fun i c => w (Sum.inr ⟨i, c⟩)⟩
def valuesOfPoint (X : ChainPoint L n k) : Coord L n k → ComplexMatrix2 :=
  Sum.elim (fun b => X.fine b.1) fun p => X.noise p.1 p.2
theorem pointOfValues_valuesOfPoint {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0) :
    pointOfValues (valuesOfPoint X) = X := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.ofCoordinates_toCoordinates <;> assumption
variable [NeZero L]
theorem contDiffAt_pointOfValues_fine {x : Coord L n k → ComplexMatrix2}
    (hx : ∀ b, IsUnit (x (Sum.inl b)).det) (b : Edge L n k 0) :
    ContDiffAt ℝ 2 (fun w => (pointOfValues w).fine b) x := by
  have hc : ∀ ι : Coord L n k, ContDiffAt ℝ 2 (fun w : Coord L n k → ComplexMatrix2 => w ι) x :=
    fun ι => (contDiff_apply ℝ ComplexMatrix2 ι).contDiffAt
  by_cases h : b.IsPositivelyOriented
  · simp only [pointOfValues, fieldOfPositiveValues_pos _ h]
    exact hc _
  · simp only [pointOfValues, fieldOfPositiveValues_neg _ h]
    exact contDiffAt_matInv (hc _) (hx _)
theorem contDiffAt_pointOfValues_noise {x : Coord L n k → ComplexMatrix2} (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun w => (pointOfValues w).noise i c) x :=
  (contDiff_apply ℝ ComplexMatrix2 (Sum.inr ⟨i, c⟩ : Coord L n k)).contDiffAt
theorem isUnit_det_valuesOfPoint {X : ChainPoint L n k} (hX : IsCompactValued X)
    (b : PositiveEdge L n k 0) : IsUnit (valuesOfPoint X (Sum.inl b)).det := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.isUnit_det_toCoordinates <;> assumption
theorem contDiffAt_levelField_values {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ}
    (hj : j ≤ k) (b : Edge L n k j) :
    ContDiffAt ℝ 2 (fun w => levelField (pointOfValues w) j b) (valuesOfPoint X) := by
  have h0 : pointOfValues (valuesOfPoint X) = X :=
    pointOfValues_valuesOfPoint (hX.2 0 (Nat.zero_le _))
  exact contDiffAt_levelField (Z := pointOfValues) (y₀ := valuesOfPoint X)
    (contDiffAt_pointOfValues_fine (isUnit_det_valuesOfPoint hX))
    (fun i c => contDiffAt_pointOfValues_noise i c) (by rwa [h0]) j hj b
theorem contDiffAt_chainAction_values {X : ChainPoint L n k} (hX : IsCompactValued X) (a : ℝ) :
    ContDiffAt ℝ 2 (fun w => chainAction a (pointOfValues w)) (valuesOfPoint X) := by
  have h0 : pointOfValues (valuesOfPoint X) = X :=
    pointOfValues_valuesOfPoint (hX.2 0 (Nat.zero_le _))
  exact contDiffAt_chainAction (Z := pointOfValues) (y₀ := valuesOfPoint X) a
    (contDiffAt_pointOfValues_fine (isUnit_det_valuesOfPoint hX))
    (fun i c => contDiffAt_pointOfValues_noise i c) (by rwa [h0])
end
section
theorem hasDerivAt_matInv {f : ℝ → ComplexMatrix2} {f' : ComplexMatrix2} (hf : HasDerivAt f f' 0)
    (hu : IsUnit (f 0).det) :
    HasDerivAt (fun t => (f t)⁻¹) (-((f 0)⁻¹ * f' * (f 0)⁻¹)) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.hasDerivAt_inv_matrix <;> assumption
theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
theorem matExp_I_smul_mem_compact {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
theorem normedExp_pi_apply {ι : Type*} [Fintype ι] (x : ι → ComplexMatrix2) (i : ι) :
    NormedSpace.exp x i = ComplexMatrix2.matExp (x i) := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.normedExp_pi_apply <;> assumption
theorem hasDerivAt_matExp_I_ray (X : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • X)))
      (Complex.I • X) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.hasDerivAt_matExp_smul <;> assumption
theorem matExp_I_ray_zero (X : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • (((0 : ℝ) : ℂ) • X)) = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.matExp_I_line_zero <;> assumption
end
section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem hasDerivAt_expChart_ray_zero (x a : A) :
    HasDerivAt (fun r : ℝ => expChart x (r • a)) (a * x) 0 := by
  have h := hasDerivAt_expChart_ray x a 0
  simp only [zero_add, zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h
theorem hasDerivAt_comp_expChart {Ψ : A → F} {x : A} (hΨ : ContDiffAt ℝ 2 Ψ x) (a : A) :
    HasDerivAt (fun r : ℝ => Ψ (expChart x (r • a))) (fderiv ℝ Ψ x (a * x)) 0 := by
  have h1 : DifferentiableAt ℝ Ψ x := hΨ.differentiableAt (by norm_num)
  have h3 : HasFDerivAt Ψ (fderiv ℝ Ψ x) (expChart x ((0 : ℝ) • a)) := by
    simpa [expChart_zero] using h1.hasFDerivAt
  exact h3.comp_hasDerivAt (0 : ℝ) (hasDerivAt_expChart_ray_zero x a)
end
section
variable {L n k : ℕ} [NeZero L]
instance instFintypeEdge {j : ℕ} : Fintype (Edge L n k j) := Fintype.ofFinite _
def liftForms : LevelForms L n k →ₗ[ℝ] (Coord L n k → ComplexMatrix2) where
  toFun ξ := Sum.elim (fun b => Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1) fun p =>
    Complex.I • (ξ.2 p.1 : Edge L n k (p.1 + 1) → ComplexMatrix2) p.2.1
  map_add' ξ ξ' := by
    funext ι
    rcases ι with b | p
    · simp [smul_add]
    · simp [smul_add]
  map_smul' r ξ := by
    funext ι
    rcases ι with b | p
    · change Complex.I • (r • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1) =
        r • (Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1)
      rw [smul_comm]
    · change Complex.I • (r • (ξ.2 p.1 : Edge L n k (p.1 + 1) → ComplexMatrix2) p.2.1) =
        r • (Complex.I • (ξ.2 p.1 : Edge L n k (p.1 + 1) → ComplexMatrix2) p.2.1)
      rw [smul_comm]
theorem expChart_apply (x a : Coord L n k → ComplexMatrix2) (ι : Coord L n k) :
    expChart x a ι = ComplexMatrix2.matExp (a ι) * x ι := by
  simp only [expChart, Pi.mul_apply, normedExp_pi_apply]
theorem pointOfValues_expChart {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0)
    (ξ : LevelForms L n k) : pointOfValues (expChart (valuesOfPoint X) (liftForms ξ)) = expMove ξ X := by
  simp only [pointOfValues, expMove]
  congr 1
  · funext b
    by_cases h : b.IsPositivelyOriented
    · rw [fieldOfPositiveValues_pos _ h, expChart_apply]
      simp only [PeriodicLattice.expTwist, if_pos h]
      rfl
    · rw [fieldOfPositiveValues_neg _ h, expChart_apply]
      simp only [PeriodicLattice.expTwist, if_neg h]
      rfl
  · funext i c
    rw [expChart_apply]
    rfl
theorem pointOfValues_expChart_smul {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0)
    (ξ : LevelForms L n k) (r : ℝ) :
    pointOfValues (expChart (valuesOfPoint X) (r • liftForms ξ)) = expMove (r • ξ) X := by
  rw [← pointOfValues_expChart hX, map_smul]
def actionValues (a : ℝ) (w : Coord L n k → ComplexMatrix2) : ℝ := chainAction a (pointOfValues w)
theorem leftDeriv_eq_fderiv {X : ChainPoint L n k} (hX : IsCompactValued X) (a : ℝ)
    (ξ : LevelForms L n k) :
    leftDeriv (chainAction a) X ξ =
      fderiv ℝ (actionValues a) (valuesOfPoint X) (liftForms ξ * valuesOfPoint X) := by
  have h := hasDerivAt_comp_expChart (contDiffAt_chainAction_values hX a) (liftForms ξ)
  have e : (fun t : ℝ => chainAction a (expMove (t • ξ) X)) =
      fun r : ℝ => chainAction a (pointOfValues (expChart (valuesOfPoint X) (r • liftForms ξ))) := by
    funext t
    rw [pointOfValues_expChart_smul (hX.2 0 (Nat.zero_le _))]
  rw [leftDeriv, e]
  exact h.deriv
theorem leftSecondDeriv_eq_hessian {X : ChainPoint L n k} (hX : IsCompactValued X) (a : ℝ)
    (ξ ξ' : LevelForms L n k) :
    leftSecondDeriv (chainAction a) X ξ ξ' =
      fderiv ℝ (fderiv ℝ (pullChart (actionValues a) (valuesOfPoint X))) 0 (liftForms ξ)
        (liftForms ξ') := by
  have h := hasDerivAt_mixedDeriv_line (contDiffAt_pullChart (contDiffAt_chainAction_values hX a))
    (liftForms ξ) (liftForms ξ')
  have e : (fun s : ℝ => deriv (fun t : ℝ => chainAction a (expMove (s • ξ + t • ξ') X)) 0) =
      fun s : ℝ => deriv (fun t : ℝ =>
        pullChart (actionValues a) (valuesOfPoint X) (s • liftForms ξ + t • liftForms ξ')) 0 := by
    funext s
    congr 1
    funext t
    rw [← pointOfValues_expChart (hX.2 0 (Nat.zero_le _)), map_add, map_smul, map_smul]
    rfl
  rw [leftSecondDeriv, e]
  exact h.deriv
def levelDeriv (X : ChainPoint L n k) (j : ℕ) (b : Edge L n k j) :
    (Coord L n k → ComplexMatrix2) →L[ℝ] ComplexMatrix2 :=
  fderiv ℝ (fun w => levelField (pointOfValues w) j b) (valuesOfPoint X)
theorem levelField_values_neg (w : Coord L n k → ComplexMatrix2) {j : ℕ} (hj : j ≤ k)
    {b : Edge L n k j} (hb : ¬b.IsPositivelyOriented) :
    levelField (pointOfValues w) j b = (levelField (pointOfValues w) j b.opposite)⁻¹ := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.levelField_ofCoords_opposite <;> assumption
theorem tangentTransport_succ_pos (X : ChainPoint L n k) (ξ : LevelForms L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    tangentTransport X ξ (j + 1) b =
      ComplexMatrix2.conjugateBy (X.noise ⟨j, h⟩ ⟨b, hb⟩)
        (leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) b) +
      (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) b := by
  simp only [tangentTransport, dif_pos h, extendOddly, if_pos hb, dif_pos hb]
theorem levelField_expChart_zero {X : ChainPoint L n k} (hX : IsCompactValued X)
    (a : Coord L n k → ComplexMatrix2) (j : ℕ) :
    levelField (pointOfValues (expChart (valuesOfPoint X) ((0 : ℝ) • a))) j = levelField X j := by
  rw [zero_smul, expChart_zero, pointOfValues_valuesOfPoint (hX.2 0 (Nat.zero_le _))]
theorem hasDerivAt_levelField_ray {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ}
    (hj : j ≤ k) (b : Edge L n k j) (a : Coord L n k → ComplexMatrix2) :
    HasDerivAt (fun r : ℝ => levelField (pointOfValues (expChart (valuesOfPoint X) (r • a))) j b)
      (levelDeriv X j b (a * valuesOfPoint X)) 0 :=
  hasDerivAt_comp_expChart (contDiffAt_levelField_values hX hj b) a
theorem expTwist_zero {j : ℕ} {W : Edge L n k j → ComplexMatrix2} (hW : W ∈ fieldSpace L n k j)
    (M : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • M) W = W := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.expTwist_zero <;> assumption
theorem hasDerivAt_expTwist_ray {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ}
    (hj : j ≤ k) (a : Coord L n k → ComplexMatrix2) (M : Edge L n k j → ComplexMatrix2)
    (ih : ∀ b, b.IsPositivelyOriented → levelDeriv X j b (a * valuesOfPoint X) =
      (Complex.I • M b) * levelField X j b) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • M) (levelField X j))
      (fun b => levelDeriv X j b (a * valuesOfPoint X)) 0 := by
  have hr := hX.2 j hj
  refine hasDerivAt_pi.2 fun b => ?_
  by_cases hb : b.IsPositivelyOriented
  · have e : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • M) (levelField X j) b) =
        fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • M b)) * levelField X j b := by
      funext t
      simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply]
    rw [e, ih b hb]
    exact (hasDerivAt_matExp_I_ray (M b)).mul_const _
  · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
    set c := b.opposite with hc
    have e : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • M) (levelField X j) b) =
        fun t : ℝ =>
          (ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • M c)) * levelField X j c)⁻¹ := by
      funext t
      simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply, hc]
    have h1 := (hasDerivAt_matExp_I_ray (M c)).mul_const (levelField X j c)
    have h0 : ComplexMatrix2.matExp (Complex.I • (((0 : ℝ) : ℂ) • M c)) * levelField X j c =
        levelField X j c := by
      simp only [matExp_I_ray_zero, one_mul]
    have h2 := hasDerivAt_matInv h1 (by rw [h0]; exact isUnit_det_of_mem_fieldSpace hr c)
    rw [e]
    refine h2.congr_deriv ?_
    have h3 := hasDerivAt_levelField_ray hX hj c a
    have h4 := hasDerivAt_levelField_ray hX hj b a
    have h5 := hasDerivAt_matInv h3
      (by rw [levelField_expChart_zero hX a j]; exact isUnit_det_of_mem_fieldSpace hr c)
    have e2 : (fun r : ℝ => levelField (pointOfValues (expChart (valuesOfPoint X) (r • a))) j b) =
        fun r : ℝ => (levelField (pointOfValues (expChart (valuesOfPoint X) (r • a))) j c)⁻¹ := by
      funext r
      exact levelField_values_neg _ hj hb
    rw [e2] at h4
    have h6 := h4.unique h5
    rw [h6, ih c hp, levelField_expChart_zero hX a j, h0]
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
include hd
theorem levelDeriv_liftForms {X : ChainPoint L n k} (hX : IsCompactValued X) (ξ : LevelForms L n k) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j, b.IsPositivelyOriented →
      levelDeriv X j b (liftForms ξ * valuesOfPoint X) =
        (Complex.I • tangentTransport X ξ j b) * levelField X j b := by
  intro j
  induction j with
  | zero =>
    intro _ b hb
    have e : (fun w : Coord L n k → ComplexMatrix2 => levelField (pointOfValues w) 0 b) =
        fun w => w (Sum.inl ⟨b, hb⟩) := by
      funext w
      have e0 : levelField (pointOfValues w) 0 b =
          fieldOfPositiveValues (fun b => w (Sum.inl b)) b := rfl
      rw [e0, fieldOfPositiveValues_pos _ hb]
    have h : fderiv ℝ (fun w : Coord L n k → ComplexMatrix2 => w (Sum.inl ⟨b, hb⟩))
        (valuesOfPoint X) =
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Coord L n k => ComplexMatrix2)
          (Sum.inl ⟨b, hb⟩ : Coord L n k) :=
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Coord L n k => ComplexMatrix2)
        (Sum.inl ⟨b, hb⟩ : Coord L n k) (valuesOfPoint X)).fderiv
    have e3 : tangentTransport X ξ 0 b = (ξ.1 : Edge L n k 0 → ComplexMatrix2) b := rfl
    have e4 : levelField X 0 b = X.fine b := rfl
    rw [levelDeriv, e, h, e3, e4]
    rfl
  | succ j ih =>
    intro hj b hb
    have h : j < k := hj
    have hj' : j ≤ k := h.le
    have hr := hX.2 j hj'
    have hrr : ∀ b', levelField X j b' ∈ PeriodicLattice.compactGaugeGroup :=
      fun b' => hr.1 b' (Set.mem_univ _)
    have hl := meanRadius_ne_zero hX ⟨j, h⟩ ⟨b, hb⟩
    have hs := det_mem_slitPlane_of_quaternion (contourMean_mem_quaternionMatrices hrr b)
      (det_contourMean_ne_zero hl)
    set n₀ := X.noise ⟨j, h⟩ ⟨b, hb⟩ with hn₀
    set u := normalizedMean (levelField X j) b with hu
    set d := liftForms ξ * valuesOfPoint X with hd'
    have hP : ContDiffAt ℝ 2 (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b)
        (levelField X j) :=
      contDiffAt_normalizedMean (V := fun V => V) (y₀ := levelField X j)
        (fun b' => (contDiff_apply ℝ ComplexMatrix2 b').contDiffAt)
        (isUnit_det_of_mem_fieldSpace hr) b hs hl
    have hPd := (hP.differentiableAt (by norm_num)).hasFDerivAt
    set DP := fderiv ℝ (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b)
      (levelField X j) with hDP
    set vel : Edge L n k j → ComplexMatrix2 := fun b' => levelDeriv X j b' d with hvel
    have hA := hasDerivAt_expTwist_ray hX hj' (liftForms ξ) (tangentTransport X ξ j) (ih hj')
    have hB : HasDerivAt
        (fun r : ℝ => levelField (pointOfValues (expChart (valuesOfPoint X) (r • liftForms ξ))) j)
        vel 0 :=
      hasDerivAt_pi.2 fun b' => hasDerivAt_levelField_ray hX hj' b' (liftForms ξ)
    have hPA : HasDerivAt (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist
        ((t : ℂ) • tangentTransport X ξ j) (levelField X j)) b) (DP vel) 0 := by
      have h1 : HasFDerivAt (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b) DP
          (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • tangentTransport X ξ j) (levelField X j)) := by
        rw [expTwist_zero hr]; exact hPd
      exact h1.comp_hasDerivAt (0 : ℝ) hA
    have hPB : HasDerivAt (fun r : ℝ => normalizedMean
        (levelField (pointOfValues (expChart (valuesOfPoint X) (r • liftForms ξ))) j) b)
        (DP vel) 0 := by
      have h1 : HasFDerivAt (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b) DP
          (levelField (pointOfValues (expChart (valuesOfPoint X) ((0 : ℝ) • liftForms ξ))) j) := by
        rw [levelField_expChart_zero hX]; exact hPd
      exact h1.comp_hasDerivAt (0 : ℝ) hB
    have hN : HasDerivAt (fun r : ℝ => expChart (valuesOfPoint X) (r • liftForms ξ)
        (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩ : Coord L n k)) (d (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩)) 0 :=
      (hasDerivAt_pi.1 (hasDerivAt_expChart_ray_zero (valuesOfPoint X) (liftForms ξ))) _
    have hL := hN.mul hPB
    have hL0 := hasDerivAt_levelField_ray hX hj b (liftForms ξ)
    have e1 : (fun r : ℝ =>
        levelField (pointOfValues (expChart (valuesOfPoint X) (r • liftForms ξ))) (j + 1) b) =
        (fun r : ℝ => expChart (valuesOfPoint X) (r • liftForms ξ)
          (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩ : Coord L n k)) *
          fun r : ℝ => normalizedMean
            (levelField (pointOfValues (expChart (valuesOfPoint X) (r • liftForms ξ))) j) b := by
      funext r
      rw [levelField_succ_of_pos _ h hb]
      rfl
    rw [e1] at hL0
    have hval := hL0.unique hL
    have hc0 : expChart (valuesOfPoint X) ((0 : ℝ) • liftForms ξ)
        (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩ : Coord L n k) = n₀ := by
      rw [zero_smul, expChart_zero]
      rfl
    have hu0 : normalizedMean
        (levelField (pointOfValues (expChart (valuesOfPoint X) ((0 : ℝ) • liftForms ξ))) j) b = u := by
      rw [levelField_expChart_zero hX]
    rw [hc0, hu0] at hval
    have hun : u ∈ PeriodicLattice.compactGaugeGroup := by
      have := normalize_mem_compact (contourMean_mem_quaternionMatrices hrr b)
        (det_contourMean_ne_zero hl)
      exact this
    have hnr : n₀ ∈ PeriodicLattice.compactGaugeGroup := hX.1 _ _
    have huu : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv _ (compact_isUnit_det hun)
    have huu' : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul _ (compact_isUnit_det hun)
    have hnn : n₀⁻¹ * n₀ = 1 := Matrix.nonsing_inv_mul _ (compact_isUnit_det hnr)
    have hY : HasDerivAt (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist
        ((t : ℂ) • tangentTransport X ξ j) (levelField X j)) b * u⁻¹) (DP vel * u⁻¹) 0 :=
      hPA.mul_const _
    have hY0 : (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist
        ((t : ℂ) • tangentTransport X ξ j) (levelField X j)) b * u⁻¹) 0 = 1 := by
      simp only []
      rw [expTwist_zero hr]
      exact huu
    have hlog := ((hd.1 Set.univ _ _ _ _ _ _ Filter.univ_mem hY hY hY).2.1 hY0).2.2.1
    have e2 : leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) b =
        Complex.I⁻¹ • deriv (fun t : ℝ => ComplexMatrix2.logSeries (normalizedMean
          (PeriodicLattice.expTwist ((t : ℂ) • tangentTransport X ξ j) (levelField X j)) b * u⁻¹))
          0 := by
      unfold leftDifferential extendOddly
      rw [if_pos hb]
      rfl
    have hξ : d (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩) =
        (Complex.I • (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) b) * n₀ := rfl
    rw [hval, hξ, levelField_succ_of_pos X h hb, tangentTransport_succ_pos X ξ h hb, e2,
      hlog.deriv, ComplexMatrix2.conjugateBy]
    simp only [smul_add, add_mul, smul_smul, Matrix.smul_mul, Matrix.mul_smul,
      mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
    have a1 : n₀ * (DP vel * u⁻¹) * n₀⁻¹ * (n₀ * u) = n₀ * DP vel := by
      calc n₀ * (DP vel * u⁻¹) * n₀⁻¹ * (n₀ * u)
          = n₀ * (DP vel * u⁻¹) * (n₀⁻¹ * n₀) * u := by simp only [mul_assoc]
        _ = n₀ * DP vel * (u⁻¹ * u) := by rw [hnn]; simp only [mul_one, mul_assoc]
        _ = n₀ * DP vel := by rw [huu', mul_one]
    rw [a1]
    simp only [mul_assoc]
    abel
end
section
variable {L n k : ℕ} [NeZero L]
theorem eventually_isCompactValued
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) {p : ℝ → Coord L n k → ComplexMatrix2}
    (hp : ContinuousAt p 0) (h0 : p 0 = valuesOfPoint X)
    (hr : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ ι, p r ι ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ᶠ r in 𝓝 (0 : ℝ), IsCompactValued (pointOfValues (p r)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.eventually_isCompactValued <;> assumption
theorem edgeForm_mem {j : ℕ} (B : edgeFormSpace L n k j) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    (B : Edge L n k j → ComplexMatrix2) b ∈ ComplexMatrix2.hermitianTraceless := B.2.1 b hb
theorem liftForms_smul_eq_I (ξ : LevelForms L n k) (r : ℝ) (ι : Coord L n k) :
    ∃ A ∈ ComplexMatrix2.hermitianTraceless, (r • liftForms ξ) ι = Complex.I • A := by
  rcases ι with b | p
  · refine ⟨r • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1,
      ComplexMatrix2.hermitianTraceless.smul_mem r (edgeForm_mem ξ.1 b.2), ?_⟩
    change r • (Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1) = _
    rw [smul_comm]
  · refine ⟨r • (ξ.2 p.1 : Edge L n k (p.1 + 1) → ComplexMatrix2) p.2.1,
      ComplexMatrix2.hermitianTraceless.smul_mem r (edgeForm_mem (ξ.2 p.1) p.2.2), ?_⟩
    change r • (Complex.I • (ξ.2 p.1 : Edge L n k (p.1 + 1) → ComplexMatrix2) p.2.1) = _
    rw [smul_comm]
theorem valuesOfPoint_mem_compact {X : ChainPoint L n k} (hX : IsCompactValued X) (ι : Coord L n k) :
    valuesOfPoint X ι ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.toCoordinates_mem_compact <;> assumption
theorem continuousAt_expChart_ray (x a : Coord L n k → ComplexMatrix2) :
    ContinuousAt (fun r : ℝ => expChart x (r • a)) 0 :=
  (hasDerivAt_expChart_ray_zero x a).continuousAt
theorem eventually_isCompactValued_ray
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (ξ : LevelForms L n k) :
    ∀ᶠ r in 𝓝 (0 : ℝ),
      IsCompactValued (pointOfValues (expChart (valuesOfPoint X) (r • liftForms ξ))) := by
  refine eventually_isCompactValued hxor hX (continuousAt_expChart_ray _ _) (by simp [expChart_zero])
    (Eventually.of_forall fun r ι => ?_)
  obtain ⟨A, hA, e⟩ := liftForms_smul_eq_I ξ r ι
  rw [expChart_apply, e]
  exact compact_mul_mem (matExp_I_smul_mem_compact hA) (valuesOfPoint_mem_compact hX ι)
end
section
variable {L n k : ℕ} [NeZero L]
theorem coe_toSublattice {m : ℕ} {i i' : ℤ} (h : i ≤ i') (y : PeriodicLattice.Site L m i) :
    ((y.toSublattice i' : PeriodicLattice.Site L m i') : PeriodicLattice.FourTorus L m) = y := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.coe_toSublattice <;> assumption
variable (hC : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
include hC hL hn in
theorem levelField_gaugeTransformPoint {X' : ChainPoint L n k} (hX' : IsCompactValued X')
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ j, j ≤ k → levelField (gaugeTransformPoint v X') j =
      PeriodicLattice.gaugeTransform (restrictVertexFunction j v) (levelField X' j) := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.levelField_gaugeTransformPoint <;> assumption
include hC hL hn in
theorem chainAction_gaugeTransformPoint
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (a : ℝ) {X' : ChainPoint L n k} (hX' : IsCompactValued X') {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    chainAction a (gaugeTransformPoint v X') = chainAction a X' := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.chainAction_gaugeTransformPoint <;> assumption
end
section
variable {L n k : ℕ} [NeZero L]
abbrev gaugeRay {ι : Type*} (l : ι → ComplexMatrix2) (t : ℝ) : ι → ComplexMatrix2 :=
  fun x => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • (-l x)))
theorem gaugeRay_mem {ι : Type*} {l : ι → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) (t : ℝ) (x : ι) :
    gaugeRay l t x ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerHessian.gaugeExpCurve_mem_compact <;> assumption
theorem gaugeRay_inv {ι : Type*} (l : ι → ComplexMatrix2) (t : ℝ) (x : ι) :
    (gaugeRay l t x)⁻¹ = ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • l x)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerHessian.gaugeExpCurve_inv <;> assumption
def gaugeLeftGen (l : Vertex L n k 0 → ComplexMatrix2) : Coord L n k → ComplexMatrix2 :=
  Sum.elim (fun b => -(Complex.I • l b.1.source))
    fun p => -(Complex.I • restrictVertexFunction (p.1 + 1) l p.2.1.source)
def gaugeRightGen (l : Vertex L n k 0 → ComplexMatrix2) : Coord L n k → ComplexMatrix2 :=
  Sum.elim (fun b => Complex.I • l b.1.target)
    fun p => Complex.I • restrictVertexFunction (p.1 + 1) l p.2.1.source
theorem smul_neg_I_smul (t : ℝ) (Y : ComplexMatrix2) :
    t • -(Complex.I • Y) = Complex.I • ((t : ℂ) • (-Y)) := by
  rw [Complex.coe_smul, smul_neg, smul_neg, smul_neg, smul_comm]
theorem smul_I_smul (t : ℝ) (Y : ComplexMatrix2) :
    t • (Complex.I • Y) = Complex.I • ((t : ℂ) • Y) := by
  rw [Complex.coe_smul, smul_comm]
theorem pointOfValues_twoSided (l : Vertex L n k 0 → ComplexMatrix2)
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    (w : Coord L n k → ComplexMatrix2) (t : ℝ) :
    pointOfValues (NormedSpace.exp (t • gaugeLeftGen l) * w * NormedSpace.exp (t • gaugeRightGen l)) =
      gaugeTransformPoint (gaugeRay l t) (pointOfValues w) := by
  have hval : ∀ ι : Coord L n k,
      (NormedSpace.exp (t • gaugeLeftGen l) * w * NormedSpace.exp (t • gaugeRightGen l)) ι =
        ComplexMatrix2.matExp (t • gaugeLeftGen l ι) * w ι *
          ComplexMatrix2.matExp (t • gaugeRightGen l ι) := by
    intro ι
    simp only [Pi.mul_apply, normedExp_pi_apply, Pi.smul_apply]
  simp only [pointOfValues, gaugeTransformPoint]
  congr 1
  · funext b
    by_cases hb : b.IsPositivelyOriented
    · rw [fieldOfPositiveValues_pos _ hb, fieldOfPositiveValues_pos _ hb, hval]
      change ComplexMatrix2.matExp (t • -(Complex.I • l b.source)) * w _ *
        ComplexMatrix2.matExp (t • (Complex.I • l b.target)) = _
      rw [smul_neg_I_smul, smul_I_smul, gaugeRay_inv]
    · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      rw [fieldOfPositiveValues_neg _ hb, fieldOfPositiveValues_neg _ hb, hval]
      change (ComplexMatrix2.matExp (t • -(Complex.I • l b.opposite.source)) * w _ *
        ComplexMatrix2.matExp (t • (Complex.I • l b.opposite.target)))⁻¹ = _
      rw [smul_neg_I_smul, smul_I_smul, gaugeRay_inv, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        matExp_inv, matExp_inv]
      have e1 : b.opposite.source = b.target := rfl
      have e2 : b.opposite.target = b.source := rfl
      rw [e1, e2]
      simp only [neg_neg, smul_neg, mul_assoc, gaugeRay]
  · funext i c
    rw [hval]
    change ComplexMatrix2.matExp (t • -(Complex.I • restrictVertexFunction (i + 1) l c.1.source)) *
      w _ * ComplexMatrix2.matExp (t • (Complex.I • restrictVertexFunction (i + 1) l c.1.source)) = _
    rw [smul_neg_I_smul, smul_I_smul]
    have e : restrictVertexFunction (i + 1) (gaugeRay l t) c.1.source =
        gaugeRay (restrictVertexFunction (i + 1) l) t c.1.source := rfl
    rw [e, gaugeRay_inv]
theorem hasDerivAt_twoSided_exp {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (x α γ : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • α) * x * NormedSpace.exp (t • γ))
      (α * x + x * γ) 0 := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) α (0 : ℝ)
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) γ (0 : ℝ)
  have h3 := (h1.mul_const x).mul h2
  exact h3.congr_deriv (by simp)
variable (hC : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
include hC hL hn in
theorem levelDeriv_gaugeOrbit {X : ChainPoint L n k} (hX : IsCompactValued X)
    (l : Vertex L n k 0 → ComplexMatrix2) (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    {j : ℕ} (hj : j ≤ k) (c : Edge L n k j) :
    levelDeriv X j c (gaugeLeftGen l * valuesOfPoint X + valuesOfPoint X * gaugeRightGen l) =
      levelField X j c * (Complex.I • restrictVertexFunction j l c.target) -
        (Complex.I • restrictVertexFunction j l c.source) * levelField X j c := by
  have hx0 : pointOfValues (valuesOfPoint X) = X :=
    pointOfValues_valuesOfPoint (hX.2 0 (Nat.zero_le _))
  have hc := hasDerivAt_twoSided_exp (valuesOfPoint X) (gaugeLeftGen l) (gaugeRightGen l)
  have hΨ := ((contDiffAt_levelField_values hX hj c).differentiableAt (by norm_num)).hasFDerivAt
  have hΨ' : HasFDerivAt (fun w => levelField (pointOfValues w) j c) (levelDeriv X j c)
      (NormedSpace.exp ((0 : ℝ) • gaugeLeftGen l) * valuesOfPoint X *
        NormedSpace.exp ((0 : ℝ) • gaugeRightGen l)) := by
    have hz : NormedSpace.exp ((0 : ℝ) • gaugeLeftGen l) * valuesOfPoint X *
        NormedSpace.exp ((0 : ℝ) • gaugeRightGen l) = valuesOfPoint X := by simp
    rw [hz]
    exact hΨ
  have h1 := hΨ'.comp_hasDerivAt (0 : ℝ) hc
  have e : ((fun w => levelField (pointOfValues w) j c) ∘ fun t : ℝ =>
      NormedSpace.exp (t • gaugeLeftGen l) * valuesOfPoint X *
        NormedSpace.exp (t • gaugeRightGen l)) =
      fun t : ℝ => gaugeRay (restrictVertexFunction j l) t c.source * levelField X j c *
        ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • restrictVertexFunction j l c.target)) := by
    funext t
    have e1 := _root_.YangMills.Construction.RunningCouplingSlope.GaugeChangeHessian.levelField_gaugeTransformPoint hC hL hn hX (gaugeRay_mem hl t) j hj
    simp only [Function.comp]
    rw [pointOfValues_twoSided l hl, hx0, e1]
    simp only [PeriodicLattice.gaugeTransform]
    have e2 : restrictVertexFunction j (gaugeRay l t) c.target =
        gaugeRay (restrictVertexFunction j l) t c.target := rfl
    rw [e2, gaugeRay_inv]
    rfl
  rw [e] at h1
  have h2 := ((hasDerivAt_matExp_I_ray (-restrictVertexFunction j l c.source)).mul_const
    (levelField X j c)).mul (hasDerivAt_matExp_I_ray (restrictVertexFunction j l c.target))
  have h3 := h1.unique h2
  rw [h3, matExp_I_ray_zero (restrictVertexFunction j l c.target),
    matExp_I_ray_zero (-restrictVertexFunction j l c.source)]
  simp only [one_mul, mul_one, smul_neg, neg_mul]
  abel
end
section
theorem star_I_inv_smul (A : ComplexMatrix2) : star (Complex.I⁻¹ • A) = Complex.I • star A := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.star_inv_I_smul <;> assumption
section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem eventually_differentiableAt {m : ℝ → ComplexMatrix2} (hm : ContDiffAt ℝ 2 m 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ m s :=
  (hm.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
theorem hasDerivAt_deriv_of_contDiffAt {m : ℝ → ComplexMatrix2} (hm : ContDiffAt ℝ 2 m 0) :
    HasDerivAt (deriv m) (deriv (deriv m) 0) 0 := by
  have : ContDiffAt ℝ 1 (deriv m) 0 := by
    have h := hm.fderiv_right (m := 1) (by norm_num)
    have h2 : deriv m = fun t => fderiv ℝ m t 1 := by
      funext t; simp
    rw [h2]
    exact h.clm_apply contDiffAt_const
  exact (this.differentiableAt (by norm_num)).hasDerivAt
theorem hasDerivAt_mixedDeriv_curve {Φ : ComplexMatrix2 → F} (hΦ : ContDiffAt ℝ 2 Φ 1)
    {m : ℝ → ComplexMatrix2} (hm : ContDiffAt ℝ 2 m 0) (h0 : m 0 = 1) (h1 : deriv m 0 = 0) :
    HasDerivAt (fun s => deriv (fun t => Φ (m (s + t))) 0)
      (fderiv ℝ Φ 1 (deriv (deriv m) 0)) 0 := by
  have hv : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun t => m (s + t)) (deriv m s) 0 := by
    filter_upwards [eventually_differentiableAt hm] with s hs
    have h' : HasDerivAt m (deriv m s) (s + 0) := by rw [add_zero]; exact hs.hasDerivAt
    exact HasDerivAt.comp_const_add (a := s) (x := (0 : ℝ)) (f := m) h'
  have hu : HasDerivAt (fun s => m (s + 0)) 0 0 := by
    have := (eventually_differentiableAt hm).self_of_nhds.hasDerivAt
    rw [h1] at this
    simpa using this
  have h := hasDerivAt_mixedDeriv hΦ (g := fun s t => m (s + t)) (by simpa using h0) hv hu
    (hasDerivAt_deriv_of_contDiffAt hm)
  simpa using h
theorem fderiv_secondDeriv_eq_zero {Φ : ComplexMatrix2 → F} (hΦ : ContDiffAt ℝ 2 Φ 1)
    {m : ℝ → ComplexMatrix2} (hm : ContDiffAt ℝ 2 m 0) (h0 : m 0 = 1) (h1 : deriv m 0 = 0)
    (hc : ∀ᶠ r in 𝓝 (0 : ℝ), Φ (m r) = Φ 1) : fderiv ℝ Φ 1 (deriv (deriv m) 0) = 0 := by
  have h := hasDerivAt_mixedDeriv_curve hΦ hm h0 h1
  have e : (fun s => deriv (fun t => Φ (m (s + t))) 0) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hc.eventually_nhds] with s hs
    have ht : Tendsto (fun t : ℝ => s + t) (𝓝 0) (𝓝 s) := by
      have : ContinuousAt (fun t : ℝ => s + t) 0 := by fun_prop
      simpa [ContinuousAt] using this
    have e2 : (fun t => Φ (m (s + t))) =ᶠ[𝓝 0] fun _ => Φ 1 := ht.eventually hs
    rw [e2.deriv_eq]
    simp
  have h2 : HasDerivAt (fun s : ℝ => deriv (fun t => Φ (m (s + t))) 0) (0 : F) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : F)).congr_of_eventuallyEq e
  exact h.unique h2
theorem hasDerivAt_one_add_ray (y : ComplexMatrix2) :
    HasDerivAt (fun r : ℝ => (1 : ComplexMatrix2) + r • y) y 0 := by
  have h : HasDerivAt (fun r : ℝ => r • y) ((1 : ℝ) • y) 0 := (hasDerivAt_id (0 : ℝ)).smul_const y
  simpa using h.const_add (1 : ComplexMatrix2)
theorem fderiv_at_one_of_ray {Φ : ComplexMatrix2 → F} (hΦ : ContDiffAt ℝ 2 Φ 1) (y : ComplexMatrix2)
    {D : F} (h : HasDerivAt (fun r : ℝ => Φ (1 + r • y)) D 0) : fderiv ℝ Φ 1 y = D := by
  have h1 : HasFDerivAt Φ (fderiv ℝ Φ 1) ((fun r : ℝ => (1 : ComplexMatrix2) + r • y) 0) := by
    simpa using (hΦ.differentiableAt (by norm_num)).hasFDerivAt
  exact (h1.comp_hasDerivAt (0 : ℝ) (hasDerivAt_one_add_ray y)).unique h
theorem fderiv_det_at_one (y : ComplexMatrix2) :
    fderiv ℝ (fun M : ComplexMatrix2 => M.det) 1 y = ComplexMatrix2.fullTrace y := by
  refine fderiv_at_one_of_ray (contDiffAt_det contDiffAt_id) y ?_
  have ent : ∀ i j, HasDerivAt (fun r : ℝ => ((1 : ComplexMatrix2) + r • y) i j) (y i j) 0 := by
    intro i j
    have h := ((contDiff_entry i j).differentiable (by norm_num)).differentiableAt
      (x := ((1 : ComplexMatrix2) + (0 : ℝ) • y))
    have h2 := (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j :
      ComplexMatrix2 →ₗ[ℝ] ℂ)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_one_add_ray y)
    exact h2
  simp only [Matrix.det_fin_two]
  have h := ((ent 0 0).mul (ent 1 1)).sub ((ent 0 1).mul (ent 1 0))
  refine h.congr_deriv ?_
  simp [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
theorem contDiffAt_star {M₀ : ComplexMatrix2} :
    ContDiffAt ℝ 2 (fun M : ComplexMatrix2 => star M) M₀ :=
  ((starL' ℝ : ComplexMatrix2 ≃L[ℝ] ComplexMatrix2) :
    ComplexMatrix2 →L[ℝ] ComplexMatrix2).contDiff.contDiffAt
theorem fderiv_mul_star_at_one (y : ComplexMatrix2) :
    fderiv ℝ (fun M : ComplexMatrix2 => M * star M) 1 y = y + star y := by
  have hc : ContDiffAt ℝ 2 (fun M : ComplexMatrix2 => M * star M) 1 :=
    contDiffAt_id.mul contDiffAt_star
  refine fderiv_at_one_of_ray hc y ?_
  have h1 := hasDerivAt_one_add_ray y
  have h := h1.mul h1.star
  refine h.congr_deriv ?_
  simp
theorem I_inv_smul_secondDeriv_mem {m : ℝ → ComplexMatrix2} (hm : ContDiffAt ℝ 2 m 0)
    (h0 : m 0 = 1) (h1 : deriv m 0 = 0)
    (hr : ∀ᶠ r in 𝓝 (0 : ℝ), m r ∈ PeriodicLattice.compactGaugeGroup) :
    Complex.I⁻¹ • deriv (deriv m) 0 ∈ ComplexMatrix2.hermitianTraceless := by
  set y := deriv (deriv m) 0 with hy
  have a1 : y + star y = 0 := by
    have hc : ContDiffAt ℝ 2 (fun M : ComplexMatrix2 => M * star M) 1 :=
      contDiffAt_id.mul contDiffAt_star
    have := fderiv_secondDeriv_eq_zero hc hm h0 h1 (by
      filter_upwards [hr] with r h
      have e := Matrix.mem_unitaryGroup_iff.1 (Matrix.mem_specialUnitaryGroup_iff.1 h).1
      simp [e])
    rwa [fderiv_mul_star_at_one] at this
  have a2 : ComplexMatrix2.fullTrace y = 0 := by
    have := fderiv_secondDeriv_eq_zero (Φ := fun M : ComplexMatrix2 => M.det)
      (contDiffAt_det contDiffAt_id) hm h0 h1 (by
      filter_upwards [hr] with r h
      simp [compact_det h])
    rwa [fderiv_det_at_one] at this
  have a3 : star y = -y := eq_neg_of_add_eq_zero_right a1
  refine ⟨?_, ?_⟩
  · change _ = star _
    rw [star_I_inv_smul, a3, Complex.inv_I]
    simp
  · simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul] at a2 ⊢
    rw [a2, smul_zero]
theorem fderiv_matInv_at_one (y : ComplexMatrix2) :
    fderiv ℝ (fun M : ComplexMatrix2 => M⁻¹) 1 y = -y := by
  refine fderiv_at_one_of_ray (contDiffAt_matInv contDiffAt_id (by simp)) y ?_
  have h := hasDerivAt_matInv (hasDerivAt_one_add_ray y) (by simp)
  refine h.congr_deriv ?_
  simp
theorem secondDeriv_matInv {m : ℝ → ComplexMatrix2} (hm : ContDiffAt ℝ 2 m 0) (h0 : m 0 = 1)
    (h1 : deriv m 0 = 0) :
    ContDiffAt ℝ 2 (fun r => (m r)⁻¹) 0 ∧ deriv (fun r => (m r)⁻¹) 0 = 0 ∧
      deriv (deriv fun r => (m r)⁻¹) 0 = -deriv (deriv m) 0 := by
  have hu : IsUnit (m 0).det := by rw [h0]; simp
  have hm1 := (eventually_differentiableAt hm).self_of_nhds.hasDerivAt
  refine ⟨contDiffAt_matInv hm hu, ?_, ?_⟩
  · rw [(hasDerivAt_matInv hm1 hu).deriv, h1]
    simp
  · have h := hasDerivAt_mixedDeriv_curve (Φ := fun M : ComplexMatrix2 => M⁻¹)
      (contDiffAt_matInv contDiffAt_id (by simp)) hm h0 h1
    rw [fderiv_matInv_at_one] at h
    have e : (fun s => deriv (fun t => (m (s + t))⁻¹) 0) = deriv fun r => (m r)⁻¹ := by
      funext s
      have := deriv_comp_const_add (f := fun r => (m r)⁻¹) s (0 : ℝ)
      simpa using this
    rw [e] at h
    exact h.deriv
theorem hasDerivAt_logSeries_secondDeriv (hlog : PeriodicLattice.LogSeriesNearOne)
    {m : ℝ → ComplexMatrix2} (hm : ContDiffAt ℝ 2 m 0) (h0 : m 0 = 1) (h1 : deriv m 0 = 0) :
    HasDerivAt (fun s => deriv (fun t => Complex.I⁻¹ • ComplexMatrix2.logSeries (m (s + t))) 0)
      (Complex.I⁻¹ • deriv (deriv m) 0) 0 := by
  have hmem : (1 : ComplexMatrix2) ∈ ComplexMatrix2.logBall := by simp [ComplexMatrix2.logBall]
  have hΦ0 : ContDiffAt ℝ 2 ComplexMatrix2.logSeries 1 :=
    ((hlog.1 1 hmem).contDiffAt (n := 2)).restrict_scalars ℝ
  have hΦ : ContDiffAt ℝ 2 (fun M : ComplexMatrix2 => Complex.I⁻¹ • ComplexMatrix2.logSeries M) 1 :=
    ContDiffAt.const_smul _ hΦ0
  have hD : fderiv ℝ (fun M : ComplexMatrix2 => Complex.I⁻¹ • ComplexMatrix2.logSeries M) 1
      (deriv (deriv m) 0) = Complex.I⁻¹ • deriv (deriv m) 0 := by
    have h2 : HasFDerivAt (fun M : ComplexMatrix2 => Complex.I⁻¹ • ComplexMatrix2.logSeries M) _ 1 :=
      (hlog.2.2.1.restrictScalars ℝ).const_smul Complex.I⁻¹
    rw [h2.fderiv]
    simp
  have h := hasDerivAt_mixedDeriv_curve hΦ hm h0 h1
  rwa [hD] at h
end
end
section
variable {L n k j : ℕ}
theorem edgeForm_ext {A B : edgeFormSpace L n k j}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      (A : Edge L n k j → ComplexMatrix2) b = (B : Edge L n k j → ComplexMatrix2) b) : A = B := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.edgeForm_ext <;> assumption
theorem extendOddly_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
theorem extendOddly_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Edge L n k j → ComplexMatrix2)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace L n k j := by apply _root_.YangMills.SharedProofs.p1442 <;> assumption
theorem conjugateBy_mem {g A : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy g A ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p2904 <;> assumption
theorem I_half_bracket_mem {S B : ComplexMatrix2} (hS : S ∈ ComplexMatrix2.hermitianTraceless)
    (hB : B ∈ ComplexMatrix2.hermitianTraceless) :
    (Complex.I / 2) • ⁅S, B⁆ ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.RealQuadraticTransposes.halfI_smul_bracket_mem <;> assumption
theorem formValues_injective {ξ ξ' : LevelForms L n k} (h : formValues ξ = formValues ξ') :
    ξ = ξ' := by
  refine Prod.ext (Subtype.ext (congrArg Prod.fst h)) (funext fun i => Subtype.ext ?_)
  exact congrFun (congrArg Prod.snd h) i
theorem bracket_coord_identity (U B lt lh Λ : ComplexMatrix2) (hΛ : Λ * U = U * lh) :
    (Complex.I • ((Complex.I / 2) • ⁅lt + Λ, B⁆)) * U =
      (1 / 2 : ℝ) • (((Complex.I • B) * (Complex.I • (Λ - lt)) +
          (Complex.I • (Λ - lt)) * (Complex.I • B)) * U) -
        ((-(Complex.I • lt)) * (Complex.I • B) * U + (Complex.I • B) * U * (Complex.I • lh)) := by
  have hII : ∀ A C : ComplexMatrix2, (Complex.I • A) * (Complex.I • C) = -(A * C) := by
    intro A C
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I]
    simp
  have h1 : ∀ Z : ComplexMatrix2, Complex.I • ((Complex.I / 2) • Z) = (-(1 / 2) : ℝ) • Z := by
    intro Z
    rw [smul_smul, ← Complex.coe_smul]
    congr 1
    rw [← mul_div_assoc, Complex.I_mul_I]
    push_cast
    ring
  have h2 : (Complex.I • B) * U * (Complex.I • lh) = -(B * (Λ * U)) := by
    rw [hΛ, mul_assoc, Matrix.mul_smul, hII]
  rw [h1, h2, hII, hII, neg_mul, hII, neg_neg]
  simp only [Ring.lie_def, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, smul_mul_assoc,
    mul_assoc]
  module
end
section
variable {L n k : ℕ} [NeZero L]
theorem exists_gaugeOrbit_tangent
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (l : Vertex L n k 0 → ComplexMatrix2)
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) :
    ∃ ζ : LevelForms L n k, formValues ζ = gaugeOrbitValues X l := by
  have hU : ∀ b, X.fine b ∈ PeriodicLattice.compactGaugeGroup :=
    fun b => (hX.2 0 (Nat.zero_le _)).1 b (Set.mem_univ _)
  have m0 : (gaugeOrbitValues X l).1 ∈ edgeFormSpace L n k 0 :=
    extendOddly_mem (hxor 0 (Nat.zero_le _)) _ fun b _ =>
      ComplexMatrix2.hermitianTraceless.sub_mem (conjugateBy_mem (hU b) (hl _)) (hl _)
  have m1 : ∀ i : Fin k, (gaugeOrbitValues X l).2 i ∈ edgeFormSpace L n k (i + 1) := by
    intro i
    simp only [gaugeOrbitValues]
    refine extendOddly_mem (hxor ((i : ℕ) + 1) i.2) _ fun c hc => ?_
    simp only [dif_pos hc]
    exact ComplexMatrix2.hermitianTraceless.sub_mem (conjugateBy_mem (hX.1 _ _) (hl _)) (hl _)
  exact ⟨(⟨_, m0⟩, fun i => ⟨_, m1 i⟩), rfl⟩
theorem exists_chainBracket_tangent
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (l : Vertex L n k 0 → ComplexMatrix2)
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) (ξ : LevelForms L n k) :
    ∃ ζ : LevelForms L n k, formValues ζ = chainBracket X l (formValues ξ) := by
  have hU : ∀ b, X.fine b ∈ PeriodicLattice.compactGaugeGroup :=
    fun b => (hX.2 0 (Nat.zero_le _)).1 b (Set.mem_univ _)
  have m0 : (chainBracket X l (formValues ξ)).1 ∈ edgeFormSpace L n k 0 :=
    extendOddly_mem (hxor 0 (Nat.zero_le _)) _ fun b hb =>
      I_half_bracket_mem
        (ComplexMatrix2.hermitianTraceless.add_mem (hl _) (conjugateBy_mem (hU b) (hl _)))
        (edgeForm_mem ξ.1 hb)
  have m1 : ∀ i : Fin k, (chainBracket X l (formValues ξ)).2 i ∈ edgeFormSpace L n k (i + 1) := by
    intro i
    simp only [chainBracket]
    refine extendOddly_mem (hxor ((i : ℕ) + 1) i.2) _ fun c hc => ?_
    simp only [dif_pos hc]
    exact I_half_bracket_mem
      (ComplexMatrix2.hermitianTraceless.add_mem (hl _) (conjugateBy_mem (hX.1 _ _) (hl _)))
      (edgeForm_mem (ξ.2 i) hc)
  exact ⟨(⟨_, m0⟩, fun i => ⟨_, m1 i⟩), rfl⟩
theorem liftForms_inl (ξ : LevelForms L n k) (b : PositiveEdge L n k 0) :
    liftForms ξ (Sum.inl b) = Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1 := rfl
theorem liftForms_inr (ξ : LevelForms L n k) (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    liftForms ξ (Sum.inr ⟨i, c⟩) =
      Complex.I • (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 := rfl
theorem gaugeOrbit_fine {X : ChainPoint L n k} {l : Vertex L n k 0 → ComplexMatrix2}
    {ζ : LevelForms L n k} (hζ : formValues ζ = gaugeOrbitValues X l) (b : PositiveEdge L n k 0) :
    (ζ.1 : Edge L n k 0 → ComplexMatrix2) b.1 =
      ComplexMatrix2.conjugateBy (X.fine b.1) (l b.1.target) - l b.1.source := by
  have e : (ζ.1 : Edge L n k 0 → ComplexMatrix2) = covDiff X.fine l := congrArg Prod.fst hζ
  rw [e, covDiff, extendOddly_pos _ b.2]
theorem gaugeOrbit_noise {X : ChainPoint L n k} {l : Vertex L n k 0 → ComplexMatrix2}
    {ζ : LevelForms L n k} (hζ : formValues ζ = gaugeOrbitValues X l) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    (ζ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
      ComplexMatrix2.conjugateBy (X.noise i c) (restrictVertexFunction (i + 1) l c.1.source) -
        restrictVertexFunction (i + 1) l c.1.source := by
  have e : (ζ.2 i : Edge L n k (i + 1) → ComplexMatrix2) = (gaugeOrbitValues X l).2 i :=
    congrFun (congrArg Prod.snd hζ) i
  rw [e]
  simp only [gaugeOrbitValues]
  rw [extendOddly_pos _ c.2, dif_pos c.2]
theorem chainBracket_fine {X : ChainPoint L n k} {l : Vertex L n k 0 → ComplexMatrix2}
    {ζ ξ : LevelForms L n k} (hζ : formValues ζ = chainBracket X l (formValues ξ))
    (b : PositiveEdge L n k 0) :
    (ζ.1 : Edge L n k 0 → ComplexMatrix2) b.1 = (Complex.I / 2) •
      ⁅l b.1.source + ComplexMatrix2.conjugateBy (X.fine b.1) (l b.1.target),
        (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1⁆ := by
  have e : (ζ.1 : Edge L n k 0 → ComplexMatrix2) = bracketTerm X.fine l ξ.1 := congrArg Prod.fst hζ
  rw [e, bracketTerm, extendOddly_pos _ b.2]
theorem chainBracket_noise {X : ChainPoint L n k} {l : Vertex L n k 0 → ComplexMatrix2}
    {ζ ξ : LevelForms L n k} (hζ : formValues ζ = chainBracket X l (formValues ξ)) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    (ζ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 = (Complex.I / 2) •
      ⁅restrictVertexFunction (i + 1) l c.1.source +
        ComplexMatrix2.conjugateBy (X.noise i c) (restrictVertexFunction (i + 1) l c.1.source),
        (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1⁆ := by
  have e : (ζ.2 i : Edge L n k (i + 1) → ComplexMatrix2) =
      (chainBracket X l (formValues ξ)).2 i :=
    congrFun (congrArg Prod.snd hζ) i
  rw [e]
  simp only [chainBracket]
  rw [extendOddly_pos _ c.2, dif_pos c.2]
  rfl
theorem conjugateBy_mul {g A : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    ComplexMatrix2.conjugateBy g A * g = g * A := by
  rw [ComplexMatrix2.conjugateBy, mul_assoc, Matrix.nonsing_inv_mul _ (compact_isUnit_det hg),
    mul_one]
theorem liftForms_gaugeOrbit {X : ChainPoint L n k} (hX : IsCompactValued X)
    {l : Vertex L n k 0 → ComplexMatrix2} {ζ : LevelForms L n k}
    (hζ : formValues ζ = gaugeOrbitValues X l) :
    liftForms ζ * valuesOfPoint X =
      gaugeLeftGen l * valuesOfPoint X + valuesOfPoint X * gaugeRightGen l := by
  funext ι
  rcases ι with b | ⟨i, c⟩
  · have hg := valuesOfPoint_mem_compact hX (Sum.inl b)
    have e : valuesOfPoint X (Sum.inl b) = X.fine b.1 := rfl
    simp only [Pi.mul_apply, Pi.add_apply, liftForms_inl, gaugeOrbit_fine hζ]
    rw [e] at hg ⊢
    have e1 : gaugeLeftGen l (Sum.inl b) = -(Complex.I • l b.1.source) := rfl
    have e2 : gaugeRightGen l (Sum.inl b) = Complex.I • l b.1.target := rfl
    rw [e1, e2, smul_sub, sub_mul, Matrix.smul_mul, conjugateBy_mul hg]
    simp only [Matrix.mul_smul, Matrix.smul_mul, neg_mul]
    abel
  · have hg : X.noise i c ∈ PeriodicLattice.compactGaugeGroup := hX.1 i c
    have e : valuesOfPoint X (Sum.inr ⟨i, c⟩) = X.noise i c := rfl
    simp only [Pi.mul_apply, Pi.add_apply, liftForms_inr, gaugeOrbit_noise hζ, e]
    have e1 : gaugeLeftGen l (Sum.inr ⟨i, c⟩) =
        -(Complex.I • restrictVertexFunction (i + 1) l c.1.source) := rfl
    have e2 : gaugeRightGen l (Sum.inr ⟨i, c⟩) =
        Complex.I • restrictVertexFunction (i + 1) l c.1.source := rfl
    rw [e1, e2, smul_sub, sub_mul, Matrix.smul_mul, conjugateBy_mul hg]
    simp only [Matrix.mul_smul, Matrix.smul_mul, neg_mul]
    abel
end
section
variable {L n k : ℕ} [NeZero L]
theorem leftSecondDeriv_gaugeOrbit (hC : ContourMeanGaugeCovariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (a : ℝ) (l : Vertex L n k 0 → ComplexMatrix2)
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) {J : LevelForms L n k}
    (hJ : IsLevelGradient (chainAction a) X J) (ξ ζ : LevelForms L n k)
    (hζ : formValues ζ = gaugeOrbitValues X l) :
    leftSecondDeriv (chainAction a) X ξ ζ =
      levelPairing (formValues J) (chainBracket X l (formValues ξ)) := by
  obtain ⟨ζ₂, h₂⟩ := exists_chainBracket_tangent hxor hX l hl ξ
  have hΦ : ContDiffAt ℝ 2 (actionValues a) (valuesOfPoint X) := contDiffAt_chainAction_values hX a
  have hinv : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᶠ t in 𝓝 (0 : ℝ),
      actionValues a (NormedSpace.exp (t • gaugeLeftGen l) *
        expChart (valuesOfPoint X) (s • liftForms ξ) * NormedSpace.exp (t • gaugeRightGen l)) =
        actionValues a (expChart (valuesOfPoint X) (s • liftForms ξ)) := by
    filter_upwards [eventually_isCompactValued_ray hxor hX ξ] with s hs
    refine Eventually.of_forall fun t => ?_
    simp only [actionValues]
    rw [pointOfValues_twoSided l hl]
    exact _root_.YangMills.Construction.RunningCouplingSlope.GaugeChangeHessian.chainAction_gaugeTransformPoint hC hL hn hg a hs (gaugeRay_mem hl t)
  have G := hessian_twoSided_invariance hΦ (liftForms ξ) (gaugeLeftGen l) (gaugeRightGen l) hinv
  have hpt : liftForms ζ₂ * valuesOfPoint X =
      (1 / 2 : ℝ) • ((liftForms ξ * liftForms ζ + liftForms ζ * liftForms ξ) * valuesOfPoint X) -
        (gaugeLeftGen l * liftForms ξ * valuesOfPoint X +
          liftForms ξ * valuesOfPoint X * gaugeRightGen l) := by
    funext ι
    rcases ι with b | ⟨i, c⟩
    · have hgb : X.fine b.1 ∈ PeriodicLattice.compactGaugeGroup :=
        valuesOfPoint_mem_compact hX (Sum.inl b)
      have e : valuesOfPoint X (Sum.inl b) = X.fine b.1 := rfl
      have e1 : gaugeLeftGen l (Sum.inl b) = -(Complex.I • l b.1.source) := rfl
      have e2 : gaugeRightGen l (Sum.inl b) = Complex.I • l b.1.target := rfl
      simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, liftForms_inl, e, e1, e2,
        chainBracket_fine h₂, gaugeOrbit_fine hζ]
      exact bracket_coord_identity _ _ _ _ _ (conjugateBy_mul hgb)
    · have hgb : X.noise i c ∈ PeriodicLattice.compactGaugeGroup := hX.1 i c
      have e : valuesOfPoint X (Sum.inr ⟨i, c⟩) = X.noise i c := rfl
      have e1 : gaugeLeftGen l (Sum.inr ⟨i, c⟩) =
          -(Complex.I • restrictVertexFunction (i + 1) l c.1.source) := rfl
      have e2 : gaugeRightGen l (Sum.inr ⟨i, c⟩) =
          Complex.I • restrictVertexFunction (i + 1) l c.1.source := rfl
      simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, liftForms_inr, e, e1, e2,
        chainBracket_noise h₂, gaugeOrbit_noise hζ]
      exact bracket_coord_identity _ _ _ _ _ (conjugateBy_mul hgb)
  rw [leftSecondDeriv_eq_hessian hX, hessian_pullChart hΦ, ← h₂, hJ ζ₂, leftDeriv_eq_fderiv hX, hpt,
    map_sub, map_smul, liftForms_gaugeOrbit hX hζ, smul_eq_mul]
  linarith
theorem I_smul_mul_cancel {W M N : ComplexMatrix2} (hW : IsUnit W.det)
    (h : (Complex.I • M) * W = (Complex.I • N) * W) : M = N := by apply _root_.YangMills.SharedProofs.p6717 <;> assumption
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
include hd
theorem tangentTransport_gaugeOrbit (hC : ContourMeanGaugeCovariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {X : ChainPoint L n k}
    (hX : IsCompactValued X) (l : Vertex L n k 0 → ComplexMatrix2)
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) {ζ : LevelForms L n k}
    (hζ : formValues ζ = gaugeOrbitValues X l) {j : ℕ} (hj : j ≤ k) {c : Edge L n k j}
    (hc : c.IsPositivelyOriented) :
    tangentTransport X ζ j c = covDiff (levelField X j) (restrictVertexFunction j l) c := by
  have hW : levelField X j c ∈ PeriodicLattice.compactGaugeGroup :=
    (hX.2 j hj).1 c (Set.mem_univ _)
  have h1 := levelDeriv_liftForms hd hX ζ j hj c hc
  rw [liftForms_gaugeOrbit hX hζ, levelDeriv_gaugeOrbit hC hL hn hX l hl hj c] at h1
  have e : covDiff (levelField X j) (restrictVertexFunction j l) c =
      ComplexMatrix2.conjugateBy (levelField X j c) (restrictVertexFunction j l c.target) -
        restrictVertexFunction j l c.source := by
    rw [covDiff, extendOddly_pos _ hc]
  rw [e]
  refine I_smul_mul_cancel (compact_isUnit_det hW) ?_
  rw [← h1, smul_sub, sub_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [conjugateBy_mul hW]
theorem tangentTransport_eq {X : ChainPoint L n k} (hX : IsCompactValued X) (ξ : LevelForms L n k)
    {j : ℕ} (hj : j ≤ k) {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    tangentTransport X ξ j b =
      Complex.I⁻¹ • (levelDeriv X j b (liftForms ξ * valuesOfPoint X) * (levelField X j b)⁻¹) := by
  have hW : levelField X j b ∈ PeriodicLattice.compactGaugeGroup :=
    (hX.2 j hj).1 b (Set.mem_univ _)
  rw [levelDeriv_liftForms hd hX ξ j hj b hb, mul_assoc,
    Matrix.mul_nonsing_inv _ (compact_isUnit_det hW), mul_one,
    smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
theorem tangentTransport_mem_edgeFormSpace
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (ξ : LevelForms L n k)
    {j : ℕ} (hj : j ≤ k) : tangentTransport X ξ j ∈ edgeFormSpace L n k j := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.tangentTransport_mem_edgeFormSpace <;> assumption
theorem topDeriv_spec
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) : IsTopDeriv X (topDeriv X) := by
  refine Classical.epsilon_spec (p := IsTopDeriv X) ⟨
    { toFun := fun ξ => ⟨tangentTransport X ξ k, tangentTransport_mem_edgeFormSpace hd hxor hX ξ le_rfl⟩
      map_add' := fun ξ ξ' => edgeForm_ext fun b hb => ?_
      map_smul' := fun r ξ => edgeForm_ext fun b hb => ?_ }, fun ξ => rfl⟩
  · change tangentTransport X (ξ + ξ') k b = tangentTransport X ξ k b + tangentTransport X ξ' k b
    rw [tangentTransport_eq hd hX _ le_rfl hb, tangentTransport_eq hd hX _ le_rfl hb,
      tangentTransport_eq hd hX _ le_rfl hb, map_add, add_mul, map_add, add_mul, smul_add]
  · change tangentTransport X (r • ξ) k b = r • tangentTransport X ξ k b
    rw [tangentTransport_eq hd hX _ le_rfl hb, tangentTransport_eq hd hX _ le_rfl hb, map_smul,
      smul_mul_assoc, map_smul, smul_mul_assoc, smul_comm]
end
section
variable {L n k : ℕ} [NeZero L]
theorem conjugateBy_add (g A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (A + B) =
      ComplexMatrix2.conjugateBy g A + ComplexMatrix2.conjugateBy g B := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (g : ComplexMatrix2) (r : ℝ) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (r • A) = r • ComplexMatrix2.conjugateBy g A := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.conjugateBy_real_smul <;> assumption
theorem vertexFunction_mem {j : ℕ} (l : vertexFunctionSpace L n k j) (x : Vertex L n k j) :
    (l : Vertex L n k j → ComplexMatrix2) x ∈ ComplexMatrix2.hermitianTraceless :=
  l.2 x (Set.mem_univ x)
def covDiffLinear {j : ℕ} (W : Edge L n k j → ComplexMatrix2)
    (hW : ∀ b, W b ∈ PeriodicLattice.compactGaugeGroup)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    vertexFunctionSpace L n k j →ₗ[ℝ] edgeFormSpace L n k j where
  toFun l := ⟨covDiff W l, extendOddly_mem hx _ fun b _ =>
    ComplexMatrix2.hermitianTraceless.sub_mem (conjugateBy_mem (hW b) (vertexFunction_mem l _))
      (vertexFunction_mem l _)⟩
  map_add' l l' := edgeForm_ext fun b hb => by
    change covDiff W (l + l' : vertexFunctionSpace L n k j) b = covDiff W l b + covDiff W l' b
    simp only [covDiff, extendOddly_pos _ hb]
    change ComplexMatrix2.conjugateBy (W b) ((l : Vertex L n k j → ComplexMatrix2) b.target +
      (l' : Vertex L n k j → ComplexMatrix2) b.target) -
      ((l : Vertex L n k j → ComplexMatrix2) b.source +
        (l' : Vertex L n k j → ComplexMatrix2) b.source) = _
    rw [conjugateBy_add]
    abel
  map_smul' r l := edgeForm_ext fun b hb => by
    change covDiff W (r • l : vertexFunctionSpace L n k j) b = r • covDiff W l b
    simp only [covDiff, extendOddly_pos _ hb]
    change ComplexMatrix2.conjugateBy (W b) (r • (l : Vertex L n k j → ComplexMatrix2) b.target) -
      r • (l : Vertex L n k j → ComplexMatrix2) b.source = _
    rw [conjugateBy_smul, smul_sub]
theorem levelForms_ext {ξ ξ' : LevelForms L n k}
    (h1 : ∀ b : PositiveEdge L n k 0,
      (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1 = (ξ'.1 : Edge L n k 0 → ComplexMatrix2) b.1)
    (h2 : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
        (ξ'.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1) :
    ξ = ξ' :=
  Prod.ext (edgeForm_ext fun b hb => h1 ⟨b, hb⟩)
    (funext fun i => edgeForm_ext fun b hb => h2 i ⟨b, hb⟩)
theorem exists_gaugeOrbit_linear
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) :
    ∃ O : vertexFunctionSpace L n k 0 →ₗ[ℝ] LevelForms L n k, ∀ l,
      formValues (O l) = gaugeOrbitValues X (l : Vertex L n k 0 → ComplexMatrix2) := by
  have hex := fun l : vertexFunctionSpace L n k 0 =>
    exists_gaugeOrbit_tangent hxor hX (l : Vertex L n k 0 → ComplexMatrix2) (vertexFunction_mem l)
  choose O hO using hex
  refine ⟨{ toFun := O, map_add' := fun l l' => ?_, map_smul' := fun r l => ?_ }, hO⟩
  · refine levelForms_ext (fun b => ?_) fun i c => ?_
    · change (O (l + l')).1.1 b.1 = (O l).1.1 b.1 + (O l').1.1 b.1
      rw [gaugeOrbit_fine (hO _), gaugeOrbit_fine (hO _), gaugeOrbit_fine (hO _)]
      change ComplexMatrix2.conjugateBy _ ((l : Vertex L n k 0 → ComplexMatrix2) b.1.target +
        (l' : Vertex L n k 0 → ComplexMatrix2) b.1.target) -
        ((l : Vertex L n k 0 → ComplexMatrix2) b.1.source +
          (l' : Vertex L n k 0 → ComplexMatrix2) b.1.source) = _
      rw [conjugateBy_add]
      abel
    · change ((O (l + l')).2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
        ((O l).2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 +
          ((O l').2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1
      rw [gaugeOrbit_noise (hO _), gaugeOrbit_noise (hO _), gaugeOrbit_noise (hO _)]
      have e : restrictVertexFunction ((i : ℕ) + 1)
          ((l + l' : vertexFunctionSpace L n k 0) : Vertex L n k 0 → ComplexMatrix2) c.1.source =
          restrictVertexFunction ((i : ℕ) + 1) (l : Vertex L n k 0 → ComplexMatrix2) c.1.source +
            restrictVertexFunction ((i : ℕ) + 1) (l' : Vertex L n k 0 → ComplexMatrix2)
              c.1.source := rfl
      rw [e, conjugateBy_add]
      abel
  · refine levelForms_ext (fun b => ?_) fun i c => ?_
    · change (O (r • l)).1.1 b.1 = r • (O l).1.1 b.1
      rw [gaugeOrbit_fine (hO _), gaugeOrbit_fine (hO _)]
      change ComplexMatrix2.conjugateBy _ (r • (l : Vertex L n k 0 → ComplexMatrix2) b.1.target) -
        r • (l : Vertex L n k 0 → ComplexMatrix2) b.1.source = _
      rw [conjugateBy_smul, smul_sub]
    · change ((O (r • l)).2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
        r • ((O l).2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1
      rw [gaugeOrbit_noise (hO _), gaugeOrbit_noise (hO _)]
      have e : restrictVertexFunction ((i : ℕ) + 1)
          ((r • l : vertexFunctionSpace L n k 0) : Vertex L n k 0 → ComplexMatrix2) c.1.source =
          r • restrictVertexFunction ((i : ℕ) + 1) (l : Vertex L n k 0 → ComplexMatrix2)
            c.1.source := rfl
      rw [e, conjugateBy_smul, smul_sub]
def extendByZeroLinear : vertexFunctionSpace L n k k →ₗ[ℝ] vertexFunctionSpace L n k 0 where
  toFun g := ⟨_root_.YangMills.Construction.Tower.extendByZero (g : Vertex L n k k → ComplexMatrix2), fun x _ => by
    simp only [extendByZero]
    split_ifs with h
    · exact vertexFunction_mem g _
    · exact ComplexMatrix2.hermitianTraceless.zero_mem⟩
  map_add' g g' := Subtype.ext (funext fun x => by
    change _root_.YangMills.Construction.Tower.extendByZero _ x = _root_.YangMills.Construction.Tower.extendByZero _ x + _root_.YangMills.Construction.Tower.extendByZero _ x
    simp only [extendByZero]
    split_ifs with h
    · rfl
    · simp)
  map_smul' r g := Subtype.ext (funext fun x => by
    change _root_.YangMills.Construction.Tower.extendByZero _ x = r • _root_.YangMills.Construction.Tower.extendByZero _ x
    simp only [extendByZero]
    split_ifs with h
    · rfl
    · simp)
theorem restrictVertexFunction_extendByZero (g : Vertex L n k k → ComplexMatrix2) :
    restrictVertexFunction k (_root_.YangMills.Construction.Tower.extendByZero g) = g := by
  funext y
  simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap, _root_.YangMills.Construction.Tower.extendByZero]
  have hle : PeriodicLattice.levelDepth k k ≤ PeriodicLattice.levelDepth k 0 := by
    simp only [PeriodicLattice.levelDepth]; omega
  have hc := coe_toSublattice hle y
  have hex : ∃ y' : Vertex L n k k, (y' : PeriodicLattice.FourTorus L n) =
      (y.toSublattice (PeriodicLattice.levelDepth k 0) : Vertex L n k 0) := ⟨y, hc.symm⟩
  rw [dif_pos hex]
  congr 1
  exact Subtype.ext (hex.choose_spec.trans hc)
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
  (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
include hd hxor
theorem shiftedGaugeMap_spec {X : ChainPoint L n k} (hX : IsCompactValued X)
    {T₀ : LevelForms L n k →ₗ[ℝ] vertexFunctionSpace L n k k}
    (hT : ∀ ξ, (T₀ ξ : Vertex L n k k → ComplexMatrix2) = chainDrift X ξ k) :
    IsShiftedGaugeMap X (shiftedGaugeMap X) := by
  have hW : ∀ b, levelField X k b ∈ PeriodicLattice.compactGaugeGroup :=
    fun b => (hX.2 k le_rfl).1 b (Set.mem_univ _)
  refine Classical.epsilon_spec (p := IsShiftedGaugeMap X)
    ⟨topDeriv X + covDiffLinear (levelField X k) hW (hxor k le_rfl) ∘ₗ T₀, fun ξ => ?_⟩
  have h1 := topDeriv_spec hd hxor hX ξ
  change (topDeriv X ξ : Edge L n k k → ComplexMatrix2) +
    covDiff (levelField X k) (T₀ ξ : Vertex L n k k → ComplexMatrix2) = _
  rw [h1, hT]
  rfl
theorem gaugeTransform_spec {X : ChainPoint L n k} (hX : IsCompactValued X)
    {T₀ : LevelForms L n k →ₗ[ℝ] vertexFunctionSpace L n k k}
    (hT : ∀ ξ, (T₀ ξ : Vertex L n k k → ComplexMatrix2) = chainDrift X ξ k) :
    IsGaugeTransform X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X) := by
  obtain ⟨O, hO⟩ := exists_gaugeOrbit_linear hxor hX
  refine Classical.epsilon_spec (p := IsGaugeTransform X)
    ⟨LinearMap.id + O ∘ₗ extendByZeroLinear ∘ₗ T₀, fun ξ => ?_⟩
  have h2 := hO (extendByZeroLinear (T₀ ξ))
  have h3 : ((extendByZeroLinear (T₀ ξ) : vertexFunctionSpace L n k 0) :
      Vertex L n k 0 → ComplexMatrix2) = gaugeCorrection X ξ := by
    change extendByZero (T₀ ξ : Vertex L n k k → ComplexMatrix2) = extendByZero _
    rw [hT]
  rw [h3] at h2
  change formValues (ξ + O (extendByZeroLinear (T₀ ξ))) = _
  rw [← h2]
  rfl
theorem gaugeCorrection_mem {X : ChainPoint L n k}
    {T₀ : LevelForms L n k →ₗ[ℝ] vertexFunctionSpace L n k k}
    (hT : ∀ ξ, (T₀ ξ : Vertex L n k k → ComplexMatrix2) = chainDrift X ξ k)
    (ξ : LevelForms L n k) (x) :
    gaugeCorrection X ξ x ∈ ComplexMatrix2.hermitianTraceless := by
  have h3 : ((extendByZeroLinear (T₀ ξ) : vertexFunctionSpace L n k 0) :
      Vertex L n k 0 → ComplexMatrix2) = gaugeCorrection X ξ := by
    change extendByZero (T₀ ξ : Vertex L n k k → ComplexMatrix2) = extendByZero _
    rw [hT]
  rw [← h3]
  exact vertexFunction_mem _ x
theorem topDeriv_gaugeTransform_eq_zero (hC : ContourMeanGaugeCovariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    {T₀ : LevelForms L n k →ₗ[ℝ] vertexFunctionSpace L n k k}
    (hT : ∀ ξ, (T₀ ξ : Vertex L n k k → ComplexMatrix2) = chainDrift X ξ k) {ξ : LevelForms L n k}
    (hξ : shiftedGaugeMap X ξ = 0) {ζ : LevelForms L n k}
    (hζ : formValues ζ = gaugeOrbitValues X (gaugeCorrection X ξ))
    (hη : _root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ = ξ + ζ) :
    topDeriv X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) = 0 := by
  have hs := gaugeCorrection_mem hd hxor hT ξ
  refine edgeForm_ext fun b hb => ?_
  rw [hη, map_add]
  change (topDeriv X ξ : Edge L n k k → ComplexMatrix2) b +
    (topDeriv X ζ : Edge L n k k → ComplexMatrix2) b = 0
  rw [topDeriv_spec hd hxor hX ξ, topDeriv_spec hd hxor hX ζ,
    tangentTransport_gaugeOrbit hd hC hL hn hX _ hs hζ le_rfl hb]
  have h1 : restrictVertexFunction k (gaugeCorrection X ξ) = chainDrift X ξ k :=
    restrictVertexFunction_extendByZero _
  rw [h1]
  have h2 := shiftedGaugeMap_spec hd hxor hX hT ξ
  rw [hξ] at h2
  have h3 := congrFun h2 b
  exact h3.symm
end
section
variable {L n k' : ℕ} [NeZero L]
def levelRatio (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2)
    (i : Fin (k' + 1)) (c : PositiveEdge L n (k' + 1) (i + 1)) : ComplexMatrix2 :=
  levelField (pointOfValues (expChart (valuesOfPoint X) a)) (i + 1) c.1 *
    (levelField X (i + 1) c.1)⁻¹
def topCorrection (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2) :
    Coord L n (k' + 1) → ComplexMatrix2 :=
  Sum.elim (fun _ => 1) fun p =>
    open Classical in if p.1 = Fin.last k' then (levelRatio X a p.1 p.2)⁻¹ else 1
def fibreValues (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2) :
    Coord L n (k' + 1) → ComplexMatrix2 :=
  topCorrection X a * expChart (valuesOfPoint X) a
theorem pointOfValues_fine (w : Coord L n (k' + 1) → ComplexMatrix2) :
    (pointOfValues w).fine = fieldOfPositiveValues fun b => w (Sum.inl b) := rfl
theorem fibreValues_inl (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2)
    (b : PositiveEdge L n (k' + 1) 0) :
    fibreValues X a (Sum.inl b) = expChart (valuesOfPoint X) a (Sum.inl b) := by
  simp [fibreValues, topCorrection]
theorem pointOfValues_fibreValues {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (ξ : LevelForms L n (k' + 1)) : pointOfValues (fibreValues X (liftForms ξ)) = fibreMove X ξ := by
  have hb0 := hX.2 0 (Nat.zero_le _)
  have hY := pointOfValues_expChart hb0 ξ
  have hN : ∀ (i : Fin (k' + 1)) (c : PositiveEdge L n (k' + 1) (i + 1)),
      IsUnit (expChart (valuesOfPoint X) (liftForms ξ) (Sum.inr ⟨i, c⟩)).det := by
    intro i c
    obtain ⟨A, hA, e⟩ := liftForms_smul_eq_I ξ 1 (Sum.inr ⟨i, c⟩)
    rw [one_smul] at e
    rw [expChart_apply, e]
    exact compact_isUnit_det (compact_mul_mem (matExp_I_smul_mem_compact hA)
      (valuesOfPoint_mem_compact hX _))
  have hbase : (pointOfValues (fibreValues X (liftForms ξ))).fine =
      (pointOfValues (expChart (valuesOfPoint X) (liftForms ξ))).fine := by
    rw [pointOfValues_fine, pointOfValues_fine]
    congr 1
    funext b
    exact fibreValues_inl _ _ _
  have hnoise : (pointOfValues (fibreValues X (liftForms ξ))).noise =
      fun (i : Fin (k' + 1)) (c : PositiveEdge L n (k' + 1) (i + 1)) =>
      open Classical in
        if i.val + 1 = k' + 1 then
          levelField X (i + 1) c.1 *
            (normalizedMean
              (levelField (pointOfValues (expChart (valuesOfPoint X) (liftForms ξ))) i) c.1)⁻¹
        else (pointOfValues (expChart (valuesOfPoint X) (liftForms ξ))).noise i c := by
    funext i c
    by_cases hi : i = Fin.last k'
    · have hv : i.val + 1 = k' + 1 := by rw [hi]; rfl
      rw [if_pos hv]
      change topCorrection X (liftForms ξ) (Sum.inr ⟨i, c⟩) *
        expChart (valuesOfPoint X) (liftForms ξ) (Sum.inr ⟨i, c⟩) = _
      have e1 : topCorrection X (liftForms ξ) (Sum.inr ⟨i, c⟩) =
          (levelRatio X (liftForms ξ) i c)⁻¹ := by
        simp only [topCorrection, Sum.elim_inr, if_pos hi]
      have hWr : levelField X (i + 1) c.1 ∈ PeriodicLattice.compactGaugeGroup :=
        (hX.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)
      rw [e1, levelRatio, levelField_succ_of_pos _ i.2 c.2]
      have e2 : (pointOfValues (expChart (valuesOfPoint X) (liftForms ξ))).noise ⟨i, i.2⟩
          ⟨c.1, c.2⟩ = expChart (valuesOfPoint X) (liftForms ξ) (Sum.inr ⟨i, c⟩) := rfl
      rw [e2, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ (compact_isUnit_det hWr)]
      rw [mul_assoc, mul_assoc, Matrix.nonsing_inv_mul _ (hN i c), mul_one]
    · have hv : ¬ i.val + 1 = k' + 1 := by
        intro h
        apply hi
        ext
        simpa using h
      rw [if_neg hv]
      change topCorrection X (liftForms ξ) (Sum.inr ⟨i, c⟩) *
        expChart (valuesOfPoint X) (liftForms ξ) (Sum.inr ⟨i, c⟩) = _
      have e1 : topCorrection X (liftForms ξ) (Sum.inr ⟨i, c⟩) = 1 := by
        simp only [topCorrection, Sum.elim_inr, if_neg hi]
      rw [e1, one_mul]
      rfl
  have e0 : pointOfValues (fibreValues X (liftForms ξ)) =
      (⟨(pointOfValues (fibreValues X (liftForms ξ))).fine,
        (pointOfValues (fibreValues X (liftForms ξ))).noise⟩ : ChainPoint L n (k' + 1)) := rfl
  rw [e0, hbase, hnoise, hY]
  rfl
theorem contDiffAt_levelField_expChart {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    {j : ℕ} (hj : j ≤ k' + 1) (b : Edge L n (k' + 1) j) :
    ContDiffAt ℝ 2 (fun a => levelField (pointOfValues (expChart (valuesOfPoint X) a)) j b) 0 := by
  have h : ContDiffAt ℝ 2 (fun w => levelField (pointOfValues w) j b)
      (expChart (valuesOfPoint X) 0) := by
    rw [expChart_zero]; exact contDiffAt_levelField_values hX hj b
  exact h.comp 0 (contDiffAt_expChart (valuesOfPoint X) 0)
theorem levelRatio_zero {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (i : Fin (k' + 1))
    (c : PositiveEdge L n (k' + 1) (i + 1)) : levelRatio X 0 i c = 1 := by
  have hW : levelField X (i + 1) c.1 ∈ PeriodicLattice.compactGaugeGroup :=
    (hX.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)
  rw [levelRatio, expChart_zero, pointOfValues_valuesOfPoint (hX.2 0 (Nat.zero_le _))]
  exact Matrix.mul_nonsing_inv _ (compact_isUnit_det hW)
theorem contDiffAt_levelRatio {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (i : Fin (k' + 1)) (c : PositiveEdge L n (k' + 1) (i + 1)) :
    ContDiffAt ℝ 2 (fun a => levelRatio X a i c) 0 :=
  (contDiffAt_levelField_expChart hX i.2 c.1).mul contDiffAt_const
theorem contDiffAt_topCorrection {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) :
    ContDiffAt ℝ 2 (topCorrection X) 0 := by
  refine contDiffAt_pi.2 fun ι => ?_
  rcases ι with b | ⟨i, c⟩
  · exact contDiffAt_const
  · by_cases hi : i = Fin.last k'
    · simp only [topCorrection, Sum.elim_inr, if_pos hi]
      exact contDiffAt_matInv (contDiffAt_levelRatio hX i c) (by rw [levelRatio_zero hX]; simp)
    · simp only [topCorrection, Sum.elim_inr, if_neg hi]
      exact contDiffAt_const
theorem topCorrection_zero {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) :
    topCorrection X 0 = 1 := by
  funext ι
  rcases ι with b | ⟨i, c⟩
  · rfl
  · by_cases hi : i = Fin.last k'
    · simp only [topCorrection, Sum.elim_inr, if_pos hi, Pi.one_apply]
      rw [levelRatio_zero hX]
      simp
    · simp only [topCorrection, Sum.elim_inr, if_neg hi, Pi.one_apply]
theorem contDiffAt_fibreValues {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) :
    ContDiffAt ℝ 2 (fibreValues X) 0 :=
  (contDiffAt_topCorrection hX).mul (contDiffAt_expChart (valuesOfPoint X) 0)
theorem fibreValues_zero {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) :
    fibreValues X 0 = valuesOfPoint X := by
  rw [fibreValues, topCorrection_zero hX, expChart_zero, one_mul]
def fibreAction (a : ℝ) (X : ChainPoint L n (k' + 1)) (b : Coord L n (k' + 1) → ComplexMatrix2) :
    ℝ :=
  actionValues a (fibreValues X b)
theorem contDiffAt_fibreAction {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (a : ℝ) :
    ContDiffAt ℝ 2 (fibreAction a X) 0 := by
  have h : ContDiffAt ℝ 2 (actionValues a) (fibreValues X 0) := by
    rw [fibreValues_zero hX]; exact contDiffAt_chainAction_values hX a
  exact h.comp 0 (contDiffAt_fibreValues hX)
theorem fibreSecondDeriv_eq_hessian {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (a : ℝ)
    (ξ ξ' : LevelForms L n (k' + 1)) :
    fibreSecondDeriv a X ξ ξ' =
      fderiv ℝ (fderiv ℝ (fibreAction a X)) 0 (liftForms ξ) (liftForms ξ') := by
  have h := hasDerivAt_mixedDeriv_line (contDiffAt_fibreAction hX a) (liftForms ξ) (liftForms ξ')
  have e : (fun s : ℝ => deriv (fun t : ℝ => chainAction a (fibreMove X (s • ξ + t • ξ'))) 0) =
      fun s : ℝ => deriv (fun t : ℝ =>
        fibreAction a X (s • liftForms ξ + t • liftForms ξ')) 0 := by
    funext s
    congr 1
    funext t
    rw [← pointOfValues_fibreValues hX, map_add, map_smul, map_smul]
    rfl
  rw [fibreSecondDeriv, e]
  exact h.deriv
theorem fibreHessian_eq {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (a : ℝ)
    (η : LinearMap.ker (topDeriv X)) :
    fibreHessian a X η = fderiv ℝ (fderiv ℝ (fibreAction a X)) 0
      (liftForms (η : LevelForms L n (k' + 1))) (liftForms (η : LevelForms L n (k' + 1))) := by
  set D := fderiv ℝ (fderiv ℝ (fibreAction a X)) 0 with hD
  have hex : ∃ T : QuadraticForm ℝ (LinearMap.ker (topDeriv X)), IsFibreHessian a X T := by
    refine ⟨LinearMap.BilinMap.toQuadraticMap (LinearMap.mk₂ ℝ
      (fun u v : LinearMap.ker (topDeriv X) =>
        D (liftForms (u : LevelForms L n (k' + 1))) (liftForms (v : LevelForms L n (k' + 1))))
      ?_ ?_ ?_ ?_), fun ξ => ?_⟩
    · intro u u' v
      simp [map_add]
    · intro c u v
      simp [map_smul]
    · intro u v v'
      simp [map_add]
    · intro c u v
      simp [map_smul]
    · rw [fibreSecondDeriv_eq_hessian hX]
      rfl
  have hs : IsFibreHessian a X (fibreHessian a X) := Classical.epsilon_spec hex
  rw [hs η, fibreSecondDeriv_eq_hessian hX]
end
section
theorem deriv_pi_apply_two {ι : Type*} [Fintype ι] {e : ℝ → ι → ComplexMatrix2}
    (he : ContDiffAt ℝ 2 e 0) :
    (∀ i, deriv e 0 i = deriv (fun r => e r i) 0) ∧
      ∀ i, deriv (deriv e) 0 i = deriv (deriv fun r => e r i) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerHessian.deriv_pi_apply_and_second <;> assumption
end
section
variable {L n k' : ℕ} [NeZero L]
abbrev topRatio (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2)
    (c : PositiveEdge L n (k' + 1) (k' + 1)) (r : ℝ) : ComplexMatrix2 :=
  levelField (pointOfValues (expChart (valuesOfPoint X) (r • a))) (k' + 1) c.1 *
    (levelField X (k' + 1) c.1)⁻¹
theorem contDiffAt_ray (a : Coord L n (k' + 1) → ComplexMatrix2) :
    ContDiffAt ℝ 2 (fun r : ℝ => r • a) 0 :=
  (contDiff_id.smul contDiff_const).contDiffAt
theorem contDiffAt_topRatio {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (a : Coord L n (k' + 1) → ComplexMatrix2) (c : PositiveEdge L n (k' + 1) (k' + 1)) :
    ContDiffAt ℝ 2 (topRatio X a c) 0 := by
  have h : ContDiffAt ℝ 2
      (fun a' => levelField (pointOfValues (expChart (valuesOfPoint X) a')) (k' + 1) c.1)
      ((fun r : ℝ => r • a) 0) := by
    simpa using contDiffAt_levelField_expChart hX le_rfl c.1
  exact (h.comp 0 (contDiffAt_ray a)).mul contDiffAt_const
theorem topRatio_zero {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (a : Coord L n (k' + 1) → ComplexMatrix2) (c : PositiveEdge L n (k' + 1) (k' + 1)) :
    topRatio X a c 0 = 1 := by
  have hW : levelField X (k' + 1) c.1 ∈ PeriodicLattice.compactGaugeGroup :=
    (hX.2 (k' + 1) le_rfl).1 c.1 (Set.mem_univ _)
  simp only [topRatio, levelField_expChart_zero hX]
  exact Matrix.mul_nonsing_inv _ (compact_isUnit_det hW)
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
include hd
theorem deriv_topRatio {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (ξ : LevelForms L n (k' + 1)) (c : PositiveEdge L n (k' + 1) (k' + 1))
    (hM : tangentTransport X ξ (k' + 1) c.1 = 0) : deriv (topRatio X (liftForms ξ) c) 0 = 0 := by
  have h := (hasDerivAt_levelField_ray hX le_rfl c.1 (liftForms ξ)).mul_const
    (levelField X (k' + 1) c.1)⁻¹
  have e : topRatio X (liftForms ξ) c = fun r : ℝ =>
      levelField (pointOfValues (expChart (valuesOfPoint X) (r • liftForms ξ))) (k' + 1) c.1 *
        (levelField X (k' + 1) c.1)⁻¹ := rfl
  rw [e, h.deriv, levelDeriv_liftForms hd hX ξ _ le_rfl c.1 c.2, hM]
  simp
omit hd in
theorem eventually_topRatio_mem
    (hxor : ∀ j, j ≤ k' + 1 → ∀ b : Edge L n (k' + 1) j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (ξ : LevelForms L n (k' + 1))
    (c : PositiveEdge L n (k' + 1) (k' + 1)) :
    ∀ᶠ r in 𝓝 (0 : ℝ), topRatio X (liftForms ξ) c r ∈ PeriodicLattice.compactGaugeGroup := by
  have hW : levelField X (k' + 1) c.1 ∈ PeriodicLattice.compactGaugeGroup :=
    (hX.2 (k' + 1) le_rfl).1 c.1 (Set.mem_univ _)
  filter_upwards [eventually_isCompactValued_ray hxor hX ξ] with r hr
  exact compact_mul_mem ((hr.2 (k' + 1) le_rfl).1 c.1 (Set.mem_univ _)) (compact_inv_mem hW)
theorem topSecondVariation_eq (hlog : PeriodicLattice.LogSeriesNearOne)
    {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (ξ : LevelForms L n (k' + 1))
    (c : PositiveEdge L n (k' + 1) (k' + 1)) (hM : tangentTransport X ξ (k' + 1) c.1 = 0) :
    topSecondVariation X ξ ξ c = Complex.I⁻¹ • deriv (deriv (topRatio X (liftForms ξ) c)) 0 := by
  have h := hasDerivAt_logSeries_secondDeriv hlog (contDiffAt_topRatio hX (liftForms ξ) c)
    (topRatio_zero hX _ c) (deriv_topRatio hd hX ξ c hM)
  have e : (fun s : ℝ => deriv (fun t : ℝ => topLog X (s • ξ + t • ξ) c) 0) =
      fun s : ℝ => deriv (fun t : ℝ =>
        Complex.I⁻¹ • ComplexMatrix2.logSeries (topRatio X (liftForms ξ) c (s + t))) 0 := by
    funext s
    have e1 : (fun t : ℝ => topLog X (s • ξ + t • ξ) c) =
        fun t : ℝ => Complex.I⁻¹ • ComplexMatrix2.logSeries (topRatio X (liftForms ξ) c (s + t)) := by
      funext t
      have hm : expMove ((s + t) • ξ) X =
          pointOfValues (expChart (valuesOfPoint X) ((s + t) • liftForms ξ)) :=
        (pointOfValues_expChart_smul (hX.2 0 (Nat.zero_le _)) ξ (s + t)).symm
      rw [← add_smul]
      unfold topLog
      rw [hm]
    rw [e1]
  unfold topSecondVariation
  rw [e]
  exact h.deriv
end
section
variable {L n k' : ℕ} [NeZero L]
abbrev topComponent (ζ : LevelForms L n (k' + 1)) : Edge L n (k' + 1) (k' + 1) → ComplexMatrix2 :=
  (ζ.2 (Fin.last k')).1
theorem exists_top_tangent
    (hx : ∀ b : Edge L n (k' + 1) (k' + 1),
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (q : PositiveEdge L n (k' + 1) (k' + 1) → ComplexMatrix2)
    (hq : ∀ c, q c ∈ ComplexMatrix2.hermitianTraceless) :
    ∃ ζ : LevelForms L n (k' + 1), (ζ.1 : Edge L n (k' + 1) 0 → ComplexMatrix2) = 0 ∧
      (∀ i, i ≠ Fin.last k' → (ζ.2 i : Edge L n (k' + 1) (i + 1) → ComplexMatrix2) = 0) ∧
      ∀ c : PositiveEdge L n (k' + 1) (k' + 1),
        topComponent ζ c.1 = q c := by
  classical
  let f : Edge L n (k' + 1) (k' + 1) → ComplexMatrix2 :=
    fun b => if h : b.IsPositivelyOriented then q ⟨b, h⟩ else 0
  have hf : ∀ c : PositiveEdge L n (k' + 1) (k' + 1), f c.1 = q c := by
    intro c
    simp only [f, dif_pos c.2]
  let B : edgeFormSpace L n (k' + 1) (k' + 1) := ⟨extendOddly f, extendOddly_mem hx f fun b hb => by
    simp only [f, dif_pos hb]
    exact hq _⟩
  let P : (i : Fin (k' + 1)) → edgeFormSpace L n (k' + 1) (i + 1) :=
    Pi.single (M := fun i : Fin (k' + 1) => edgeFormSpace L n (k' + 1) (i + 1)) (Fin.last k') B
  have hP : P (Fin.last k') = B := Pi.single_eq_same _ _
  refine ⟨(0, P), rfl, fun i hi => ?_, fun c => ?_⟩
  · have hP' : P i = 0 := Pi.single_eq_of_ne hi _
    change (P i : Edge L n (k' + 1) (i + 1) → ComplexMatrix2) = 0
    rw [hP']
    rfl
  · change (P (Fin.last k')).1 c.1 = q c
    rw [hP]
    change extendOddly f c.1 = q c
    rw [extendOddly_pos f c.2, hf]
theorem leftDifferential_zero {k j : ℕ} (W : Edge L n k j → ComplexMatrix2) :
    leftDifferential normalizedMean W (0 : Edge L n k j → ComplexMatrix2) = 0 := by
  have h : ∀ c : Edge L n k (j + 1), logDirectionalDeriv ℝ
      (fun X => normalizedMean (PeriodicLattice.expTwist X W) c) (normalizedMean W c)
      (0 : Edge L n k j → ComplexMatrix2) = 0 := by
    intro c
    simp [logDirectionalDeriv]
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [leftDifferential, extendOddly, if_pos hb, h]
    rfl
  · simp only [leftDifferential, extendOddly, if_neg hb, h]
    simp
theorem tangentTransport_below_top {X : ChainPoint L n (k' + 1)} {ζ : LevelForms L n (k' + 1)}
    (h1 : (ζ.1 : Edge L n (k' + 1) 0 → ComplexMatrix2) = 0)
    (h2 : ∀ i, i ≠ Fin.last k' → (ζ.2 i : Edge L n (k' + 1) (i + 1) → ComplexMatrix2) = 0) :
    ∀ j, j ≤ k' → tangentTransport X ζ j = 0 := by
  intro j
  induction j with
  | zero => intro _; exact h1
  | succ j ih =>
    intro hj
    have h : j < k' + 1 := by omega
    have hne : (⟨j, h⟩ : Fin (k' + 1)) ≠ Fin.last k' := by
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    have e2 : (ζ.2 ⟨j, h⟩ : Edge L n (k' + 1) (j + 1) → ComplexMatrix2) = 0 := h2 _ hne
    funext b
    by_cases hb : b.IsPositivelyOriented
    · rw [tangentTransport_succ_pos X ζ h hb, ih (by omega), leftDifferential_zero, e2]
      simp [ComplexMatrix2.conjugateBy]
    · simp only [tangentTransport, dif_pos h, extendOddly, if_neg hb]
      have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      rw [dif_pos hp, ih (by omega), leftDifferential_zero, e2]
      simp [ComplexMatrix2.conjugateBy]
theorem tangentTransport_top {X : ChainPoint L n (k' + 1)} {ζ : LevelForms L n (k' + 1)}
    (h1 : (ζ.1 : Edge L n (k' + 1) 0 → ComplexMatrix2) = 0)
    (h2 : ∀ i, i ≠ Fin.last k' → (ζ.2 i : Edge L n (k' + 1) (i + 1) → ComplexMatrix2) = 0)
    (c : PositiveEdge L n (k' + 1) (k' + 1)) :
    tangentTransport X ζ (k' + 1) c.1 = topComponent ζ c.1 := by
  rw [tangentTransport_succ_pos X ζ (Nat.lt_succ_self k') c.2,
    tangentTransport_below_top h1 h2 k' le_rfl, leftDifferential_zero]
  simp [ComplexMatrix2.conjugateBy]
  rfl
theorem fibreHessian_value (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hlog : PeriodicLattice.LogSeriesNearOne)
    {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (a : ℝ)
    (η : LinearMap.ker (topDeriv X))
    (hM : ∀ c : PositiveEdge L n (k' + 1) (k' + 1),
      tangentTransport X (η : LevelForms L n (k' + 1)) (k' + 1) c.1 = 0)
    {ζ : LevelForms L n (k' + 1)} (h1 : (ζ.1 : Edge L n (k' + 1) 0 → ComplexMatrix2) = 0)
    (h2 : ∀ i, i ≠ Fin.last k' → (ζ.2 i : Edge L n (k' + 1) (i + 1) → ComplexMatrix2) = 0)
    (h3 : ∀ c : PositiveEdge L n (k' + 1) (k' + 1), topComponent ζ c.1 =
      topSecondVariation X (η : LevelForms L n (k' + 1)) (η : LevelForms L n (k' + 1)) c) :
    fibreHessian a X η =
      leftSecondDeriv (chainAction a) X (η : LevelForms L n (k' + 1))
        (η : LevelForms L n (k' + 1)) - leftDeriv (chainAction a) X ζ := by
  set ξ : LevelForms L n (k' + 1) := η.1 with hξ
  set a₀ := liftForms ξ with ha₀
  have hΦ : ContDiffAt ℝ 2 (actionValues a) (valuesOfPoint X) := contDiffAt_chainAction_values hX a
  set e : ℝ → Coord L n (k' + 1) → ComplexMatrix2 := fun r => topCorrection X (r • a₀) with he_def
  have he : ContDiffAt ℝ 2 e 0 := by
    have h : ContDiffAt ℝ 2 (topCorrection X) ((fun r : ℝ => r • a₀) 0) := by
      simpa using contDiffAt_topCorrection hX
    exact ContDiffAt.comp (g := topCorrection X) (f := fun r : ℝ => r • a₀) 0 h (contDiffAt_ray a₀)
  have e0 : e 0 = 1 := by
    simp only [he_def, zero_smul, topCorrection_zero hX]
  obtain ⟨p1, p2⟩ := deriv_pi_apply_two he
  have ci : ∀ (c : PositiveEdge L n (k' + 1) (k' + 1)),
      (fun r => e r (Sum.inr ⟨Fin.last k', c⟩)) = fun r => (topRatio X a₀ c r)⁻¹ := by
    intro c
    funext r
    simp only [he_def, topCorrection, Sum.elim_inr, if_true]
    rfl
  have cn : ∀ (i : Fin (k' + 1)) (c : PositiveEdge L n (k' + 1) (i + 1)), i ≠ Fin.last k' →
      (fun r => e r (Sum.inr ⟨i, c⟩)) = fun _ => 1 := by
    intro i c hi
    funext r
    simp only [he_def, topCorrection, Sum.elim_inr, if_neg hi]
  have cb : ∀ b : PositiveEdge L n (k' + 1) 0, (fun r => e r (Sum.inl b)) = fun _ => 1 := by
    intro b
    funext r
    rfl
  have hinv := fun c : PositiveEdge L n (k' + 1) (k' + 1) =>
    secondDeriv_matInv (contDiffAt_topRatio hX a₀ c) (topRatio_zero hX a₀ c)
      (deriv_topRatio hd hX ξ c (hM c))
  have e1 : deriv e 0 = 0 := by
    funext ι
    rw [p1 ι]
    rcases ι with b | ⟨i, c⟩
    · rw [cb b]; simp
    · by_cases hi : i = Fin.last k'
      · subst hi
        rw [ci c]
        exact (hinv c).2.1
      · rw [cn i c hi]; simp
  have hE : deriv (deriv e) 0 * valuesOfPoint X = -(liftForms ζ * valuesOfPoint X) := by
    funext ι
    simp only [Pi.mul_apply, Pi.neg_apply, p2 ι]
    rcases ι with b | ⟨i, c⟩
    · rw [cb b, liftForms_inl, h1]
      simp
    · by_cases hi : i = Fin.last k'
      · subst hi
        rw [ci c, (hinv c).2.2, liftForms_inr]
        have hq := topSecondVariation_eq hd hlog hX ξ c (hM c)
        have hh : ((ζ.2 (Fin.last k')).1 : Edge L n (k' + 1) (k' + 1) → ComplexMatrix2) c.1 =
            Complex.I⁻¹ • deriv (deriv (topRatio X a₀ c)) 0 := (h3 c).trans hq
        change _ = -((Complex.I • ((ζ.2 (Fin.last k')).1 :
          Edge L n (k' + 1) (k' + 1) → ComplexMatrix2) c.1) * _)
        rw [hh, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, neg_mul]
      · rw [cn i c hi, liftForms_inr, h2 i hi]
        simp
  have hfs := hasDerivAt_mixedDeriv_twisted hΦ a₀ he e0 e1
  have hline := hasDerivAt_mixedDeriv_line (contDiffAt_fibreAction hX a) a₀ a₀
  have eqf : (fun s : ℝ => deriv (fun t : ℝ => fibreAction a X (s • a₀ + t • a₀)) 0) =
      fun s : ℝ => deriv (fun t : ℝ =>
        actionValues a (e (s + t) * expChart (valuesOfPoint X) ((s + t) • a₀))) 0 := by
    funext s
    have e2 : (fun t : ℝ => fibreAction a X (s • a₀ + t • a₀)) = fun t : ℝ =>
        actionValues a (e (s + t) * expChart (valuesOfPoint X) ((s + t) • a₀)) := by
      funext t
      rw [← add_smul]
      rfl
    rw [e2]
  rw [eqf] at hline
  have huniq := hline.unique hfs
  rw [fibreHessian_eq hX, huniq, leftSecondDeriv_eq_hessian hX, hessian_pullChart_diag hΦ,
    leftDeriv_eq_fderiv hX, hE, map_add, map_neg]
  ring
end
theorem xor_isPositive (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.xor_isPositivelyOriented_opposite <;> assumption
theorem fibreHessianAfterGaugeChange_holds (hdrift : ChainDriftLinearAtMinimizer)
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hC : ContourMeanGaugeCovariant)
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hm : PeriodicLattice.ElementaryStepFacts)
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction) :
    FibreHessianAfterGaugeChange := by
  intro a ha L hL k n hk hn
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hxor : ∀ j, j ≤ k' + 1 → ∀ b : Edge L n (k' + 1) j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := xor_isPositive hb hL hn
  have hlog : PeriodicLattice.LogSeriesNearOne :=
    (hm L n 1 0 hL hn (by norm_num)).2.2.1
  filter_upwards [hdrift a ha L hL (k' + 1) n hk hn] with V hV W hW X hLeast J μ hJ hμ ξ hξ
  obtain ⟨T₀, hT⟩ := hV W hW X hLeast
  have hX : IsCompactValued X := hLeast.compact
  have hξ0 : shiftedGaugeMap X ξ = 0 := LinearMap.mem_ker.1 hξ
  have hs := gaugeCorrection_mem hd hxor hT ξ
  obtain ⟨ζ₀, hζ₀⟩ := exists_gaugeOrbit_tangent hxor hX (gaugeCorrection X ξ) hs
  have hη : _root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ = ξ + ζ₀ := formValues_injective (by
    rw [_root_.YangMills.Construction.RunningCouplingSlope.GaugeChangeHessian.gaugeTransform_spec hd hxor hX hT ξ, ← hζ₀]
    rfl)
  have hker := _root_.YangMills.Construction.RunningCouplingSlope.GaugeChangeHessian.topDeriv_gaugeTransform_eq_zero hd hxor hC hL hn hX hT hξ0 hζ₀ hη
  refine ⟨⟨_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ, LinearMap.mem_ker.2 hker⟩, rfl, ?_⟩
  have hM : ∀ c : PositiveEdge L n (k' + 1) (k' + 1),
      tangentTransport X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) (k' + 1) c.1 = 0 := fun c => by
    rw [← topDeriv_spec hd hxor hX (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ), hker]
    rfl
  have hq : ∀ c, topSecondVariation X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) c ∈
      ComplexMatrix2.hermitianTraceless := fun c => by
    rw [topSecondVariation_eq hd hlog hX _ c (hM c)]
    exact I_inv_smul_secondDeriv_mem (contDiffAt_topRatio hX _ c) (topRatio_zero hX _ c)
      (deriv_topRatio hd hX _ c (hM c)) (eventually_topRatio_mem hxor hX _ c)
  obtain ⟨ζ, h1, h2, h3⟩ := exists_top_tangent (hxor _ le_rfl)
    (topSecondVariation X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ)) hq
  rw [fibreHessian_value hd hlog hX a ⟨_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ, LinearMap.mem_ker.2 hker⟩ hM h1 h2 h3]
  have c1 : leftDeriv (chainAction a) X ζ =
      (traceFinsumPairing
        (restrictToPositiveEdges (μ : Edge L n (k' + 1) (k' + 1) → ComplexMatrix2))
        (topSecondVariation X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ))).re := by
    rw [← hJ ζ, hμ ζ, edgeFormPairing]
    have e : restrictToPositiveEdges
        (topDeriv X ζ : Edge L n (k' + 1) (k' + 1) → ComplexMatrix2) =
        topSecondVariation X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) := by
      funext c
      change (topDeriv X ζ : Edge L n (k' + 1) (k' + 1) → ComplexMatrix2) c.1 = _
      rw [topDeriv_spec hd hxor hX ζ, tangentTransport_top h1 h2 c, h3 c]
    rw [e]
  have hΦ : ContDiffAt ℝ 2 (actionValues a) (valuesOfPoint X) := contDiffAt_chainAction_values hX a
  have sym : leftSecondDeriv (chainAction a) X ζ₀ ξ =
      leftSecondDeriv (chainAction a) X ξ ζ₀ := by
    rw [leftSecondDeriv_eq_hessian hX, leftSecondDeriv_eq_hessian hX]
    exact (contDiffAt_pullChart hΦ).isSymmSndFDerivAt (by simp) _ _
  have add : leftSecondDeriv (chainAction a) X (ξ + ζ₀) (ξ + ζ₀) =
      leftSecondDeriv (chainAction a) X ξ ξ + leftSecondDeriv (chainAction a) X ξ ζ₀ +
        (leftSecondDeriv (chainAction a) X ζ₀ ξ +
          leftSecondDeriv (chainAction a) X ζ₀ ζ₀) := by
    simp only [leftSecondDeriv_eq_hessian hX, map_add, add_apply]
    ring
  have i1 := leftSecondDeriv_gaugeOrbit hC hL hn hg hxor hX a _ hs hJ ξ ζ₀ hζ₀
  have i2 := leftSecondDeriv_gaugeOrbit hC hL hn hg hxor hX a _ hs hJ ζ₀ ζ₀ hζ₀
  rw [hζ₀] at i2
  simp only [gaugedFormValue]
  rw [c1]
  change leftSecondDeriv (chainAction a) X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) - _ = _
  rw [hη] at *
  rw [add, sym, i1, i2]
  ring
end YangMills.Construction.RunningCouplingSlope.GaugeChangeHessian
end
