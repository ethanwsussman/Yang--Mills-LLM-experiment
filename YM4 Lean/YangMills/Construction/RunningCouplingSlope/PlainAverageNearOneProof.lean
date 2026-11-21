import YangMills.Construction.RunningCouplingSlope.PlainAverageAlongComplexCurvesProof
import YangMills.Construction.RunningCouplingSlope.PlainAverageNearOne
import YangMills.Construction.Towers.PathsDifferentiableAtZeroProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.NormalizedMeanProof
open Tower
open Matrices
section AlongCurves
variable {ι : Type*} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def HasDerivAlongCurves (V g : ι → ComplexMatrix2) (f : (ι → ComplexMatrix2) → E) (D : E) : Prop :=
  ∀ γ : ℝ → ι → ComplexMatrix2, γ 0 = V → (∀ b, HasDerivAt (fun t => γ t b) (g b) 0) →
    HasDerivAt (fun t => f (γ t)) D 0
variable {V g : ι → ComplexMatrix2}
theorem hasDerivAlongCurves_apply (b : ι) : HasDerivAlongCurves V g (fun U => U b) (g b) :=
  fun _ _ h => h b
theorem hasDerivAlongCurves_const (x : E) : HasDerivAlongCurves V g (fun _ => x) 0 :=
  fun _ _ _ => hasDerivAt_const _ _
theorem hasDerivAlongCurves_mul {f₁ f₂ : (ι → ComplexMatrix2) → ComplexMatrix2}
    {D₁ D₂ : ComplexMatrix2} (h₁ : HasDerivAlongCurves V g f₁ D₁)
    (h₂ : HasDerivAlongCurves V g f₂ D₂) :
    HasDerivAlongCurves V g (fun U => f₁ U * f₂ U) (D₁ * f₂ V + f₁ V * D₂) := by
  intro γ h0 hγ
  have := (h₁ γ h0 hγ).mul (h₂ γ h0 hγ)
  rw [h0] at this
  exact this
theorem hasDerivAlongCurves_sum {α : Type*} (s : Finset α) {f : α → (ι → ComplexMatrix2) → E}
    {D : α → E} (h : ∀ a ∈ s, HasDerivAlongCurves V g (f a) (D a)) :
    HasDerivAlongCurves V g (fun U => ∑ a ∈ s, f a U) (∑ a ∈ s, D a) :=
  fun γ h0 hγ => HasDerivAt.fun_sum fun a ha => h a ha γ h0 hγ
theorem hasDerivAlongCurves_const_smul {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    {D : ComplexMatrix2} (a : ℂ) (h : HasDerivAlongCurves V g f D) :
    HasDerivAlongCurves V g (fun U => a • f U) (a • D) :=
  fun γ h0 hγ => (h γ h0 hγ).const_smul a
theorem hasDerivAlongCurves_inv (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {f : (ι → ComplexMatrix2) → ComplexMatrix2} {D : ComplexMatrix2}
    (h : HasDerivAlongCurves V g f D) (hu : IsUnit (Matrix.det (f V))) :
    HasDerivAlongCurves V g (fun U => (f U)⁻¹) (-((f V)⁻¹ * D * (f V)⁻¹)) := by
  intro γ h0 hγ
  have hF := h γ h0 hγ
  set w := (f V)⁻¹ with hw
  have hfw : f V * w = 1 := Matrix.mul_nonsing_inv _ hu
  have hwf : w * f V = 1 := Matrix.nonsing_inv_mul _ hu
  have hdw : IsUnit (Matrix.det w) := by
    have h1 : Matrix.det w * Matrix.det (f V) = 1 := by rw [← Matrix.det_mul, hwf, Matrix.det_one]
    exact IsUnit.of_mul_eq_one _ h1
  have hX : HasDerivAt (fun t => f (γ t) * w) (D * w) 0 := hF.mul_const w
  have hX0 : (fun t => f (γ t) * w) 0 = 1 := by simp only [h0, hfw]
  have hinv := ((hd.1 Set.univ _ _ _ _ _ _ Filter.univ_mem hX hX hX).2.1 hX0).2.1
  have e : (fun t => (f (γ t))⁻¹) = fun t => w * (f (γ t) * w)⁻¹ := by
    funext t
    rw [Matrix.mul_inv_rev, ← mul_assoc, Matrix.mul_nonsing_inv _ hdw, one_mul]
  rw [e]
  have := hinv.const_mul w
  exact HasDerivAt.congr_deriv this (by simp [mul_assoc])
theorem hasDerivAt_matrix_entry {W : ℝ → ComplexMatrix2} {D : ComplexMatrix2}
    (h : HasDerivAt W D 0) (a b : Fin 2) :
    HasDerivAt (fun t => W t a b) (D a b) 0 := by apply _root_.YangMills.Construction.Tower.DiffAtZeroPaths.hasDerivAt_entry <;> assumption
end AlongCurves
section LinearAlongCurves
variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def HasLinearDerivAlongCurves (V : ι → ComplexMatrix2) (f : (ι → ComplexMatrix2) → E)
    (T : (ι → ComplexMatrix2) →ₗ[ℝ] E) : Prop :=
  ∀ g, HasDerivAlongCurves V g f (T g)
variable {V : ι → ComplexMatrix2}
theorem hasLinearDerivAlongCurves_apply (b : ι) :
    HasLinearDerivAlongCurves V (fun U => U b)
      (LinearMap.proj (R := ℝ) (φ := fun _ : ι => ComplexMatrix2) b) :=
  fun _ => hasDerivAlongCurves_apply b
theorem hasLinearDerivAlongCurves_one :
    HasLinearDerivAlongCurves V (fun _ => (1 : ComplexMatrix2)) 0 :=
  fun _ => hasDerivAlongCurves_const _
theorem hasLinearDerivAlongCurves_mul {f₁ f₂ : (ι → ComplexMatrix2) → ComplexMatrix2}
    {T₁ T₂ : (ι → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2}
    (h₁ : HasLinearDerivAlongCurves V f₁ T₁) (h₂ : HasLinearDerivAlongCurves V f₂ T₂) :
    HasLinearDerivAlongCurves V (fun U => f₁ U * f₂ U)
      ((LinearMap.mulRight ℝ (f₂ V)) ∘ₗ T₁ + (LinearMap.mulLeft ℝ (f₁ V)) ∘ₗ T₂) :=
  fun g => hasDerivAlongCurves_mul (h₁ g) (h₂ g)
theorem hasLinearDerivAlongCurves_sum {α : Type*} (s : Finset α)
    {f : α → (ι → ComplexMatrix2) → E} {T : α → (ι → ComplexMatrix2) →ₗ[ℝ] E}
    (h : ∀ a ∈ s, HasLinearDerivAlongCurves V (f a) (T a)) :
    HasLinearDerivAlongCurves V (fun U => ∑ a ∈ s, f a U) (∑ a ∈ s, T a) := by
  intro g
  have := hasDerivAlongCurves_sum (V := V) (g := g) s (fun a ha => h a ha g)
  simpa [LinearMap.sum_apply] using this
theorem hasLinearDerivAlongCurves_const_smul {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    {T : (ι → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2} (a : ℂ)
    (h : HasLinearDerivAlongCurves V f T) :
    HasLinearDerivAlongCurves V (fun U => a • f U) (a • T) :=
  fun g => hasDerivAlongCurves_const_smul a (h g)
theorem hasLinearDerivAlongCurves_inv
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {f : (ι → ComplexMatrix2) → ComplexMatrix2} {T : (ι → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2}
    (h : HasLinearDerivAlongCurves V f T) (hu : IsUnit (Matrix.det (f V))) :
    HasLinearDerivAlongCurves V (fun U => (f U)⁻¹)
      (-((LinearMap.mulRight ℝ (f V)⁻¹) ∘ₗ (LinearMap.mulLeft ℝ (f V)⁻¹) ∘ₗ T)) := by
  intro g
  have := hasDerivAlongCurves_inv hd (h g) hu
  simpa using this
theorem exists_hasLinearDerivAlongCurves_list_prod (l : List ι) :
    ∃ T, HasLinearDerivAlongCurves V (fun U => (l.map U).prod) T := by
  induction l with
  | nil => exact ⟨0, by simpa using hasLinearDerivAlongCurves_one (V := V)⟩
  | cons b l ih =>
    obtain ⟨T, hT⟩ := ih
    exact ⟨_, by simpa using hasLinearDerivAlongCurves_mul (hasLinearDerivAlongCurves_apply b) hT⟩
theorem exists_hasLinearDerivAlongCurves_det {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    {T : (ι → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2} (h : HasLinearDerivAlongCurves V f T) :
    ∃ T' : (ι → ComplexMatrix2) →ₗ[ℝ] ℂ,
      HasLinearDerivAlongCurves V (fun U => Matrix.det (f U)) T' := by
  refine ⟨{ toFun := fun g => (T g 0 0 * f V 1 1 + f V 0 0 * T g 1 1) -
              (T g 0 1 * f V 1 0 + f V 0 1 * T g 1 0)
            map_add' := fun x y => by simp only [map_add, Matrix.add_apply]; ring
            map_smul' := fun a x => by
              simp only [map_smul, Matrix.smul_apply, RingHom.id_apply, Complex.real_smul]
              ring }, fun g γ h0 hγ => ?_⟩
  have hF := h g γ h0 hγ
  have e : (fun t => Matrix.det (f (γ t))) =
      fun t => f (γ t) 0 0 * f (γ t) 1 1 - f (γ t) 0 1 * f (γ t) 1 0 := by
    funext t
    exact Matrix.det_fin_two _
  rw [e]
  have := ((hasDerivAt_matrix_entry hF 0 0).mul (hasDerivAt_matrix_entry hF 1 1)).sub
    ((hasDerivAt_matrix_entry hF 0 1).mul (hasDerivAt_matrix_entry hF 1 0))
  simp only [h0] at this
  exact this
theorem exists_hasLinearDerivAlongCurves_sqrt {f : (ι → ComplexMatrix2) → ℂ}
    {T : (ι → ComplexMatrix2) →ₗ[ℝ] ℂ} (h : HasLinearDerivAlongCurves V f T)
    (hs : f V ∈ Complex.slitPlane) :
    ∃ T' : (ι → ComplexMatrix2) →ₗ[ℝ] ℂ,
      HasLinearDerivAlongCurves V (fun U => (f U) ^ (1 / 2 : ℂ)) T' := by
  have hr : HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (f V) ^ ((1 / 2 : ℂ) - 1) * 1) (f V) :=
    (hasDerivAt_id (f V)).cpow_const (c := (1 / 2 : ℂ)) hs
  refine ⟨T.smulRight ((1 / 2 : ℂ) * (f V) ^ ((1 / 2 : ℂ) - 1) * 1), fun g γ h0 hγ => ?_⟩
  have hF := h g γ h0 hγ
  have := HasDerivAt.scomp (0 : ℝ) (g₁ := fun z : ℂ => z ^ (1 / 2 : ℂ))
    (by rw [h0]; exact hr) hF
  exact this
theorem exists_hasLinearDerivAlongCurves_inv_smul {r : (ι → ComplexMatrix2) → ℂ}
    {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    {R : (ι → ComplexMatrix2) →ₗ[ℝ] ℂ} {T : (ι → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2}
    (hr : HasLinearDerivAlongCurves V r R) (hf : HasLinearDerivAlongCurves V f T)
    (h0 : r V ≠ 0) :
    ∃ T' : (ι → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2,
      HasLinearDerivAlongCurves V (fun U => (r U)⁻¹ • f U) T' := by
  refine ⟨(r V)⁻¹ • T + ((-((r V) ^ 2)⁻¹) • R).smulRight (f V), fun g γ hγ0 hγ => ?_⟩
  have h1 := hr g γ hγ0 hγ
  have h2 := hf g γ hγ0 hγ
  have h3 := h1.fun_inv (by rw [hγ0]; exact h0)
  have h4 := h3.fun_smul h2
  simp only [hγ0] at h4
  refine HasDerivAt.congr_deriv h4 ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, smul_eq_mul]
  congr 2
  field_simp
end LinearAlongCurves
section NormBounds
variable {ι : Type*}
theorem norm_list_prod_sub_one_le (U : ι → ComplexMatrix2) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (h : ∀ b, ‖U b - 1‖ ≤ ρ) (l : List ι) :
    ‖(l.map U).prod - 1‖ ≤ (1 + ρ) ^ l.length - 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.norm_list_prod_sub_one_le <;> assumption
theorem norm_entry_le_norm (A : ComplexMatrix2) (a b : Fin 2) : ‖A a b‖ ≤ ‖A‖ := by apply _root_.YangMills.SharedProofs.p14523 <;> assumption
end NormBounds
section ComplexScalars
theorem sqrt_near_one (z : ℂ) (h : ‖z - 1‖ ≤ 1 / 10) :
    z ^ (1 / 2 : ℂ) ≠ 0 ∧ (z ^ (1 / 2 : ℂ)) ^ 2 = z ∧ ‖z ^ (1 / 2 : ℂ) - 1‖ ≤ ‖z - 1‖ ∧
      z ∈ Complex.slitPlane := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.sqrt_near_one <;> assumption
end ComplexScalars
section Paths
variable {L n k j : ℕ}
theorem det_list_prod_eq_one (V : Edge L n k j → ComplexMatrix2) (hV : ∀ b, Matrix.det (V b) = 1)
    (l : List (Edge L n k j)) : Matrix.det ((l.map V).prod) = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.det_list_prod_eq_one <;> assumption
theorem inv_pathHolonomy_eq (V : Edge L n k j → ComplexMatrix2)
    (hV : ∀ b, V b.opposite = (V b)⁻¹)
    (hd : ∀ b, Matrix.det (V b) = 1) (l : List (Edge L n k j)) :
    (PeriodicLattice.pathHolonomy V l)⁻¹ =
      PeriodicLattice.pathHolonomy V (PeriodicLattice.reversePath l) := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.inv_pathHolonomy_eq <;> assumption
theorem length_stepsThroughAxes {a : ℤ} (d : Fin 4 → ℤ) (x : PeriodicLattice.Site L n a)
    (l : List (Fin 4)) :
    (PeriodicLattice.stepsThroughAxes d x l).length = (l.map fun μ => (d μ).natAbs).sum := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.length_stepsThroughAxes <;> assumption
end Paths
theorem normalizedMeanNearOne_holds (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hcf : PeriodicLattice.BlockContoursAndCombs)
    (hbb : PeriodicLattice.BlocksBoxesPaths.Statement)
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement) :
    NormalizedMeanNearOne := by
  intro L hL
  obtain ⟨ρ, hρ, hnear⟩ := ContourMeanDerivative.contourMean_near_one hcf hbb hb L hL
  refine ⟨ρ, hρ, ?_⟩
  intro n k j hn hj V hV hVρ c hc
  obtain ⟨S, w, hmean, hr0, hrclose, hu, hudet, hslit⟩ := hnear n k j hn hj V hV hVρ c hc
  have hdetV : ∀ b, Matrix.det (V b) = 1 := fun b => hV.1 b (Set.mem_univ b)
  have hinvhol : ∀ l : List (Edge L n k j), PeriodicLattice.pathHolonomy V l =
      (l.map V).prod := fun _ => rfl
  refine ⟨hr0, hrclose, hu, hudet, ?_⟩
  have hhol : ∀ l : List (Edge L n k j), ∃ T,
      HasLinearDerivAlongCurves V (fun U => PeriodicLattice.pathHolonomy U l) T :=
    fun l => exists_hasLinearDerivAlongCurves_list_prod l
  have hcvd : ∀ x π, ∃ T, HasLinearDerivAlongCurves V (fun U => contourHolonomy U c x π) T := by
    intro x π
    obtain ⟨D₁, h₁⟩ := hhol (contourLeg c.source x π)
    obtain ⟨D₂, h₂⟩ := hhol (PeriodicLattice.crossingPath c x)
    obtain ⟨D₃, h₃⟩ := hhol (contourLeg c.target (PeriodicLattice.shiftAcross c x) π)
    have hu3 : IsUnit (Matrix.det (PeriodicLattice.pathHolonomy V
        (contourLeg c.target (PeriodicLattice.shiftAcross c x) π))) := by
      rw [hinvhol, det_list_prod_eq_one V hdetV]
      exact isUnit_one
    exact ⟨_, hasLinearDerivAlongCurves_mul (hasLinearDerivAlongCurves_mul h₁ h₂)
      (hasLinearDerivAlongCurves_inv hd h₃ hu3)⟩
  choose Dc hDc using hcvd
  have hM : HasLinearDerivAlongCurves V (fun U => contourMean U c)
      (w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), Dc x π) := by
    have h1 := hasLinearDerivAlongCurves_const_smul w (hasLinearDerivAlongCurves_sum S fun x _ =>
      hasLinearDerivAlongCurves_sum Finset.univ fun π _ => hDc x π)
    intro g γ h0 hγ
    have h2 := h1 g γ h0 hγ
    have e : (fun t => contourMean (γ t) c) = fun t => w • ∑ x ∈ S,
        ∑ π : Equiv.Perm (Fin 4), contourHolonomy (γ t) c x π := by
      funext t
      exact hmean _
    rw [e]
    exact h2
  obtain ⟨Dd, hDd⟩ := exists_hasLinearDerivAlongCurves_det hM
  obtain ⟨Dr, hDr⟩ := exists_hasLinearDerivAlongCurves_sqrt hDd hslit
  obtain ⟨Du, hDu⟩ := exists_hasLinearDerivAlongCurves_inv_smul hDr hM hr0
  refine ⟨Du, fun g γ h0 hγ => ?_⟩
  exact hDu g γ h0 hγ
end YangMills.Construction.RunningCouplingSlope.NormalizedMeanProof
end
