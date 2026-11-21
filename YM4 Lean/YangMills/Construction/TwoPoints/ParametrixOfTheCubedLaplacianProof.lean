import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.FreeKernel.HeatKernelsAndTheGreensFunctionsProof
import YangMills.Construction.Towers.IntegralOfTheThirdPowersOfTheFreeSymbolsProof
import YangMills.Construction.TwoPoints.ParametrixOfTheCubedLaplacian
import Mathlib
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TestFunctions (laplacianR4 partialDerivR4)
namespace LaplacianCubeParametrix
section Derivatives
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem partialDerivR4_eq_fderiv {f : AmbientSpace → E} {x : AmbientSpace}
    (hf : DifferentiableAt ℝ f x) (μ : Fin 4) :
    partialDerivR4 μ f x = fderiv ℝ f x (Pi.single μ 1) :=
  hf.lineDeriv_eq_fderiv
theorem partialDerivR4_congr_nhds {f g : AmbientSpace → E} {x : AmbientSpace}
    (h : f =ᶠ[𝓝 x] g) (μ : Fin 4) :
    partialDerivR4 μ f x = partialDerivR4 μ g x := by
  have hc : Tendsto (fun t : ℝ => x + t • (Pi.single μ (1 : ℝ) : AmbientSpace)) (𝓝 0) (𝓝 x) := by
    have hcont : Continuous (fun t : ℝ => x + t • (Pi.single μ (1 : ℝ) : AmbientSpace)) := by
      fun_prop
    simpa using hcont.tendsto 0
  exact Filter.EventuallyEq.deriv_eq (hc.eventually h)
theorem partialDerivR4_eventuallyEq {f g : AmbientSpace → E} {x : AmbientSpace}
    (h : f =ᶠ[𝓝 x] g) (μ : Fin 4) :
    partialDerivR4 μ f =ᶠ[𝓝 x] partialDerivR4 μ g :=
  h.eventuallyEq_nhds.mono fun _ hy => partialDerivR4_congr_nhds hy μ
theorem laplacianR4_eventuallyEq {f g : AmbientSpace → E} {x : AmbientSpace}
    (h : f =ᶠ[𝓝 x] g) :
    laplacianR4 f =ᶠ[𝓝 x] laplacianR4 g := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  exact Finset.sum_congr rfl fun μ _ =>
    partialDerivR4_congr_nhds (partialDerivR4_eventuallyEq hy μ) μ
theorem laplacianR4_eqOn_of_isOpen {f g : AmbientSpace → E} {O : Set AmbientSpace}
    (hO : IsOpen O) (h : ∀ y ∈ O, f y = g y) :
    ∀ y ∈ O, laplacianR4 f y = laplacianR4 g y := by
  intro y hy
  have hev : f =ᶠ[𝓝 y] g := by
    filter_upwards [hO.mem_nhds hy] with z hz using h z hz
  exact (laplacianR4_eventuallyEq hev).eq_of_nhds
theorem contDiff_partialDerivR4 {f : AmbientSpace → E} (hf : ContDiff ℝ ∞ f) (μ : Fin 4) :
    ContDiff ℝ ∞ (partialDerivR4 μ f) := by
  have h : partialDerivR4 μ f = fun x => fderiv ℝ f x (Pi.single μ 1) :=
    funext fun x => partialDerivR4_eq_fderiv (hf.differentiable (by simp) x) μ
  rw [h]
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem contDiff_laplacianR4 {f : AmbientSpace → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (laplacianR4 f) :=
  ContDiff.sum fun μ _ => contDiff_partialDerivR4 (contDiff_partialDerivR4 hf μ) μ
theorem hasCompactSupport_partialDerivR4 {f : AmbientSpace → E} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (μ : Fin 4) : HasCompactSupport (partialDerivR4 μ f) := by
  have h : partialDerivR4 μ f = fun x => fderiv ℝ f x (Pi.single μ 1) :=
    funext fun x => partialDerivR4_eq_fderiv (hf.differentiable (by simp) x) μ
  rw [h]
  exact hc.fderiv_apply (𝕜 := ℝ) _
theorem hasCompactSupport_laplacianR4 {f : AmbientSpace → E} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : HasCompactSupport (laplacianR4 f) := by
  have h : ∀ μ : Fin 4, HasCompactSupport (partialDerivR4 μ (partialDerivR4 μ f)) := fun μ =>
    hasCompactSupport_partialDerivR4 (contDiff_partialDerivR4 hf μ)
      (hasCompactSupport_partialDerivR4 hf hc μ) μ
  have hsum : ∀ s : Finset (Fin 4),
      HasCompactSupport (fun x => ∑ μ ∈ s, partialDerivR4 μ (partialDerivR4 μ f) x) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact HasCompactSupport.zero
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a).add ih
  exact hsum Finset.univ
end Derivatives
section ByParts
theorem integrable_real_smul_of_hasCompactSupport {f : AmbientSpace → ℝ} {w : AmbientSpace → ℂ}
    (hf : Continuous f) (hw : Continuous w) (hc : HasCompactSupport w) :
    Integrable (fun x => f x • w x) :=
  (hf.smul hw).integrable_of_hasCompactSupport hc.smul_left
variable {f : AmbientSpace → ℝ} {ψ : AmbientSpace → ℂ}
theorem integral_smul_partialDerivR4 (hf : ContDiff ℝ ∞ f) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (μ : Fin 4) :
    ∫ x, f x • partialDerivR4 μ ψ x = -∫ x, partialDerivR4 μ f x • ψ x := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have e1 : partialDerivR4 μ ψ = fun x => fderiv ℝ ψ x (Pi.single μ 1) :=
    funext fun x => partialDerivR4_eq_fderiv (hψd x) μ
  have e2 : partialDerivR4 μ f = fun x => fderiv ℝ f x (Pi.single μ 1) :=
    funext fun x => partialDerivR4_eq_fderiv (hfd x) μ
  have hf' : Continuous (partialDerivR4 μ f) := (contDiff_partialDerivR4 hf μ).continuous
  have hψ' : Continuous (partialDerivR4 μ ψ) := (contDiff_partialDerivR4 hψ μ).continuous
  have i1 : Integrable (fun x => partialDerivR4 μ f x • ψ x) :=
    integrable_real_smul_of_hasCompactSupport hf' hψ.continuous hc
  have i2 : Integrable (fun x => f x • partialDerivR4 μ ψ x) :=
    integrable_real_smul_of_hasCompactSupport hf.continuous hψ'
      (hasCompactSupport_partialDerivR4 hψ hc μ)
  have i3 : Integrable (fun x => f x • ψ x) :=
    integrable_real_smul_of_hasCompactSupport hf.continuous hψ.continuous hc
  rw [e1, e2] at *
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable i1 i2 i3
    (fun x _ => hfd x) (fun x _ => hψd x)
theorem integral_smul_laplacianR4 (hf : ContDiff ℝ ∞ f) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) :
    ∫ x, f x • laplacianR4 ψ x = ∫ x, laplacianR4 f x • ψ x := by
  have hf1 := fun μ => contDiff_partialDerivR4 hf μ
  have hψ1 := fun μ => contDiff_partialDerivR4 hψ μ
  have hc1 := fun μ => hasCompactSupport_partialDerivR4 hψ hc μ
  have hf2 := fun μ => contDiff_partialDerivR4 (hf1 μ) μ
  have hψ2 := fun μ => contDiff_partialDerivR4 (hψ1 μ) μ
  have hc2 := fun μ => hasCompactSupport_partialDerivR4 (hψ1 μ) (hc1 μ) μ
  simp only [laplacianR4, Finset.smul_sum, Finset.sum_smul]
  rw [integral_finsetSum _ fun μ _ =>
      integrable_real_smul_of_hasCompactSupport hf.continuous (hψ2 μ).continuous (hc2 μ),
    integral_finsetSum _ fun μ _ =>
      integrable_real_smul_of_hasCompactSupport (hf2 μ).continuous hψ.continuous hc]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [integral_smul_partialDerivR4 hf (hψ1 μ) (hc1 μ) μ,
    integral_smul_partialDerivR4 (hf1 μ) hψ hc μ, neg_neg]
theorem integral_smul_laplacianR4_cube (hf : ContDiff ℝ ∞ f) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) :
    ∫ x, f x • laplacianR4 (laplacianR4 (laplacianR4 ψ)) x =
      ∫ x, laplacianR4 (laplacianR4 (laplacianR4 f)) x • ψ x := by
  have hψ1 := contDiff_laplacianR4 hψ
  have hc1 := hasCompactSupport_laplacianR4 hψ hc
  have hψ2 := contDiff_laplacianR4 hψ1
  have hc2 := hasCompactSupport_laplacianR4 hψ1 hc1
  have hf1 := contDiff_laplacianR4 hf
  have hf2 := contDiff_laplacianR4 hf1
  rw [integral_smul_laplacianR4 hf hψ2 hc2, integral_smul_laplacianR4 hf1 hψ1 hc1,
    integral_smul_laplacianR4 hf2 hψ hc]
end ByParts
section Radial
def sqNorm (x : AmbientSpace) : ℝ := ∑ μ, x μ ^ 2
theorem continuous_sqNorm : Continuous sqNorm := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.continuous_sumSq <;> assumption
theorem sqNorm_nonneg (x : AmbientSpace) : 0 ≤ sqNorm x := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.sumSq_nonneg <;> assumption
theorem eq_zero_of_sqNorm_eq_zero {x : AmbientSpace} (hx : sqNorm x = 0) : x = 0 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.eq_zero_of_sumSq_eq_zero <;> assumption
theorem hasDerivAt_sqNorm_add_smul_single (x : AmbientSpace) (μ : Fin 4) :
    HasDerivAt (fun t : ℝ => sqNorm (x + t • (Pi.single μ (1 : ℝ) : AmbientSpace)))
      (2 * x μ) 0 := by apply _root_.YangMills.Construction.FreeKernel.HeatKernelGreen.Continuum.hasDerivAt_sqSum_line <;> assumption
theorem partialDerivR4_radial {G : ℝ → ℝ} {G' b : ℝ} {x : AmbientSpace}
    (h : HasDerivAt G G' (sqNorm x + b)) (μ : Fin 4) :
    partialDerivR4 μ (fun y => G (sqNorm y + b)) x = G' * (2 * x μ) := by
  have h1 : HasDerivAt
      (fun t : ℝ => sqNorm (x + t • (Pi.single μ (1 : ℝ) : AmbientSpace)) + b)
      (2 * x μ) 0 := (hasDerivAt_sqNorm_add_smul_single x μ).add_const b
  have h' : HasDerivAt G G'
      ((fun t : ℝ => sqNorm (x + t • (Pi.single μ (1 : ℝ) : AmbientSpace)) + b) 0) := by
    simpa using h
  exact (h'.comp 0 h1).deriv
theorem laplacianR4_radial {G G' G'' : ℝ → ℝ} {b : ℝ}
    (h1 : ∀ t, 0 < t → HasDerivAt G (G' t) t) (h2 : ∀ t, 0 < t → HasDerivAt G' (G'' t) t)
    {x : AmbientSpace} (hx : 0 < sqNorm x + b) :
    laplacianR4 (fun y => G (sqNorm y + b)) x =
      8 * G' (sqNorm x + b) + 4 * sqNorm x * G'' (sqNorm x + b) := by
  have hopen : IsOpen {y : AmbientSpace | 0 < sqNorm y + b} :=
    isOpen_lt continuous_const (continuous_sqNorm.add continuous_const)
  have hpart : ∀ μ : Fin 4, partialDerivR4 μ (partialDerivR4 μ fun y => G (sqNorm y + b)) x =
      G'' (sqNorm x + b) * (2 * x μ) * (2 * x μ) + G' (sqNorm x + b) * 2 := by
    intro μ
    have hev : partialDerivR4 μ (fun y => G (sqNorm y + b)) =ᶠ[𝓝 x]
        fun y => G' (sqNorm y + b) * (2 * y μ) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact partialDerivR4_radial (h1 _ hy) μ
    rw [partialDerivR4_congr_nhds hev μ]
    have hq : HasDerivAt
        (fun t : ℝ => sqNorm (x + t • (Pi.single μ (1 : ℝ) : AmbientSpace)) + b)
        (2 * x μ) 0 := (hasDerivAt_sqNorm_add_smul_single x μ).add_const b
    have h' : HasDerivAt G' (G'' (sqNorm x + b))
        ((fun t : ℝ => sqNorm (x + t • (Pi.single μ (1 : ℝ) : AmbientSpace)) + b) 0) := by
      simpa using h2 _ hx
    have hG := h'.comp 0 hq
    have hl : HasDerivAt
        (fun t : ℝ => 2 * (x + t • (Pi.single μ (1 : ℝ) : AmbientSpace)) μ) 2 0 := by
      have h0 : HasDerivAt (fun t : ℝ => 2 * (x μ + t)) 2 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_add (x μ)).const_mul 2
      simpa using h0
    have hd := (hG.fun_mul hl).deriv
    simp only [Function.comp_apply] at hd
    simp only [partialDerivR4]
    rw [hd]
    simp
  simp only [laplacianR4, hpart]
  simp only [sqNorm, Fin.sum_univ_four]
  ring
theorem hasDerivAt_inv_pow_of_pos (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => s⁻¹ ^ n) (-(n : ℝ) * t⁻¹ ^ (n + 1)) t := by
  have h := (hasDerivAt_inv ht.ne').fun_pow n
  have e : (n : ℝ) * t⁻¹ ^ (n - 1) * -(t ^ 2)⁻¹ = -(n : ℝ) * t⁻¹ ^ (n + 1) := by
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
  rw [← e]
  exact h
def laplacianProfileOne (b t : ℝ) : ℝ := 8 * Real.log t + 12 - 4 * b * t⁻¹ ^ 1
def laplacianProfileTwo (b t : ℝ) : ℝ :=
  32 * t⁻¹ ^ 1 + 32 * b * t⁻¹ ^ 2 + 32 * b ^ 2 * t⁻¹ ^ 3
def shiftedLogKernel (b : ℝ) (x : AmbientSpace) : ℝ :=
  (sqNorm x + b) * Real.log (sqNorm x + b)
theorem laplacianR4_shiftedLogKernel {b : ℝ} {x : AmbientSpace} (hx : 0 < sqNorm x + b) :
    laplacianR4 (shiftedLogKernel b) x = laplacianProfileOne b (sqNorm x + b) := by
  have h1 : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log t + 1) t :=
    fun t ht => Real.hasDerivAt_mul_log ht.ne'
  have h2 : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => Real.log s + 1) (t⁻¹) t :=
    fun t ht => (Real.hasDerivAt_log ht.ne').add_const 1
  have h := laplacianR4_radial (b := b) h1 h2 hx
  have e : shiftedLogKernel b = fun y => (fun s : ℝ => s * Real.log s) (sqNorm y + b) := rfl
  rw [e, h, laplacianProfileOne]
  have hne := hx.ne'
  have hn : sqNorm x = (sqNorm x + b) - b := by ring
  rw [hn]
  simp only [sub_add_cancel]
  generalize sqNorm x + b = t at hne
  field_simp
  ring
theorem laplacianR4_profileOne {b : ℝ} {x : AmbientSpace} (hx : 0 < sqNorm x + b) :
    laplacianR4 (fun y => laplacianProfileOne b (sqNorm y + b)) x =
      laplacianProfileTwo b (sqNorm x + b) := by
  have h1 : ∀ t : ℝ, 0 < t → HasDerivAt (laplacianProfileOne b)
      (8 * t⁻¹ ^ 1 + 4 * b * t⁻¹ ^ 2) t := by
    intro t ht
    exact ((((Real.hasDerivAt_log ht.ne').const_mul 8).add_const 12).fun_sub
      ((hasDerivAt_inv_pow_of_pos 1 ht).const_mul (4 * b))).congr_deriv (by push_cast; ring)
  have h2 : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => 8 * t⁻¹ ^ 1 + 4 * b * t⁻¹ ^ 2)
      (-8 * t⁻¹ ^ 2 - 8 * b * t⁻¹ ^ 3) t := by
    intro t ht
    exact (((hasDerivAt_inv_pow_of_pos 1 ht).const_mul 8).fun_add
      ((hasDerivAt_inv_pow_of_pos 2 ht).const_mul (4 * b))).congr_deriv (by push_cast; ring)
  rw [laplacianR4_radial h1 h2 hx, laplacianProfileTwo]
  have hne := hx.ne'
  have hn : sqNorm x = (sqNorm x + b) - b := by ring
  rw [hn]
  simp only [sub_add_cancel]
  generalize sqNorm x + b = t at hne
  field_simp
  ring
theorem laplacianR4_profileTwo {b : ℝ} {x : AmbientSpace} (hx : 0 < sqNorm x + b) :
    laplacianR4 (fun y => laplacianProfileTwo b (sqNorm y + b)) x =
      -1536 * b ^ 3 * (sqNorm x + b)⁻¹ ^ 5 := by
  have h1 : ∀ t : ℝ, 0 < t → HasDerivAt (laplacianProfileTwo b)
      (-32 * t⁻¹ ^ 2 - 64 * b * t⁻¹ ^ 3 - 96 * b ^ 2 * t⁻¹ ^ 4) t := by
    intro t ht
    exact ((((hasDerivAt_inv_pow_of_pos 1 ht).const_mul 32).fun_add
      ((hasDerivAt_inv_pow_of_pos 2 ht).const_mul (32 * b))).fun_add
      ((hasDerivAt_inv_pow_of_pos 3 ht).const_mul (32 * b ^ 2))).congr_deriv
        (by push_cast; ring)
  have h2 : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun t => -32 * t⁻¹ ^ 2 - 64 * b * t⁻¹ ^ 3 - 96 * b ^ 2 * t⁻¹ ^ 4)
      (64 * t⁻¹ ^ 3 + 192 * b * t⁻¹ ^ 4 + 384 * b ^ 2 * t⁻¹ ^ 5) t := by
    intro t ht
    exact ((((hasDerivAt_inv_pow_of_pos 2 ht).const_mul (-32)).fun_sub
      ((hasDerivAt_inv_pow_of_pos 3 ht).const_mul (64 * b))).fun_sub
      ((hasDerivAt_inv_pow_of_pos 4 ht).const_mul (96 * b ^ 2))).congr_deriv
        (by push_cast; ring)
  rw [laplacianR4_radial h1 h2 hx]
  have hne := hx.ne'
  have hn : sqNorm x = (sqNorm x + b) - b := by ring
  rw [hn]
  simp only [sub_add_cancel]
  generalize sqNorm x + b = t at hne
  field_simp
  ring
theorem laplacianR4_cube_shiftedLogKernel {b : ℝ} {x : AmbientSpace} (hx : 0 < sqNorm x + b) :
    laplacianR4 (laplacianR4 (laplacianR4 (shiftedLogKernel b))) x =
      -1536 * b ^ 3 * (sqNorm x + b)⁻¹ ^ 5 := by
  have hopen : IsOpen {y : AmbientSpace | 0 < sqNorm y + b} :=
    isOpen_lt continuous_const (continuous_sqNorm.add continuous_const)
  have e1 := laplacianR4_eqOn_of_isOpen hopen
    (f := laplacianR4 (shiftedLogKernel b)) (g := fun y => laplacianProfileOne b (sqNorm y + b))
    fun y hy => laplacianR4_shiftedLogKernel hy
  have e2 := laplacianR4_eqOn_of_isOpen hopen
    (f := laplacianR4 (laplacianR4 (shiftedLogKernel b)))
    (g := fun y => laplacianProfileTwo b (sqNorm y + b))
    fun y hy => (e1 y hy).trans (laplacianR4_profileOne hy)
  exact (e2 x hx).trans (laplacianR4_profileTwo hx)
end Radial
section Fundamental
def decayKernel (y : AmbientSpace) : ℝ := (sqNorm y + 1)⁻¹ ^ 5
theorem sqNorm_add_one_pos (y : AmbientSpace) : 0 < sqNorm y + 1 := by
  have := sqNorm_nonneg y
  linarith
theorem continuous_decayKernel : Continuous decayKernel :=
  ((continuous_sqNorm.add continuous_const).inv₀ fun y => (sqNorm_add_one_pos y).ne').pow 5
theorem decayKernel_nonneg (y : AmbientSpace) : 0 ≤ decayKernel y := by
  have := sqNorm_add_one_pos y
  unfold decayKernel
  positivity
theorem sq_norm_le_sqNorm (y : AmbientSpace) : ‖y‖ ^ 2 ≤ sqNorm y := by apply _root_.YangMills.Construction.Tower.FreeResolvents.CubicSumIntegral.sq_norm_le_sum_sq <;> assumption
theorem integrable_decayKernel : Integrable decayKernel := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := AmbientSpace) (μ := volume) (r := 10)
    (by simp; norm_num)
  refine h.mono' continuous_decayKernel.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [Real.norm_of_nonneg (decayKernel_nonneg y)]
  have e : (-10 / 2 : ℝ) = -((5 : ℕ) : ℝ) := by norm_num
  have hp : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  rw [e, Real.rpow_neg hp.le, Real.rpow_natCast, ← inv_pow]
  unfold decayKernel
  have hle : 1 + ‖y‖ ^ 2 ≤ sqNorm y + 1 := by
    have := sq_norm_le_sqNorm y
    linarith
  have h0 : 0 ≤ (sqNorm y + 1)⁻¹ := (inv_pos.2 (sqNorm_add_one_pos y)).le
  exact pow_le_pow_left₀ h0 (inv_anti₀ hp hle) 5
theorem integral_decayKernel_pos : 0 < ∫ y, decayKernel y := by
  refine (integral_pos_iff_support_of_nonneg decayKernel_nonneg integrable_decayKernel).2 ?_
  have hs : Function.support decayKernel = univ := by
    ext y
    have := sqNorm_add_one_pos y
    simp only [Function.mem_support, mem_univ, iff_true]
    unfold decayKernel
    positivity
  rw [hs]
  exact isOpen_univ.measure_pos volume univ_nonempty
theorem sqNorm_smul (δ : ℝ) (y : AmbientSpace) : sqNorm (δ • y) = δ ^ 2 * sqNorm y := by
  simp only [sqNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
theorem integral_rescaled_decayKernel {δ : ℝ} (hδ : 0 < δ) (ψ : AmbientSpace → ℂ) :
    ∫ x, ((δ ^ 2) ^ 3 * (sqNorm x + δ ^ 2)⁻¹ ^ 5) • ψ x =
      ∫ y, decayKernel y • ψ (δ • y) := by
  have h := Measure.integral_comp_smul (volume : Measure AmbientSpace)
    (fun x => ((δ ^ 2) ^ 3 * (sqNorm x + δ ^ 2)⁻¹ ^ 5) • ψ x) δ
  have hfin : Module.finrank ℝ AmbientSpace = 4 := by simp
  rw [hfin] at h
  have e : ∀ y : AmbientSpace, ((δ ^ 2) ^ 3 * (sqNorm (δ • y) + δ ^ 2)⁻¹ ^ 5) • ψ (δ • y) =
      (δ ^ 4)⁻¹ • (decayKernel y • ψ (δ • y)) := by
    intro y
    rw [smul_smul, sqNorm_smul]
    congr 1
    have := sqNorm_add_one_pos y
    unfold decayKernel
    have hne : sqNorm y + 1 ≠ 0 := this.ne'
    have e2 : δ ^ 2 * sqNorm y + δ ^ 2 = δ ^ 2 * (sqNorm y + 1) := by ring
    rw [e2]
    field_simp
  simp only [e] at h
  rw [integral_smul, abs_of_pos (by positivity)] at h
  have h4 : ((δ ^ 4)⁻¹ : ℝ) ≠ 0 := by positivity
  exact (smul_right_injective ℂ h4 h).symm
theorem abs_mul_log_le_one_add_sq {t : ℝ} (ht : 0 ≤ t) : |t * Real.log t| ≤ 1 + t ^ 2 := by
  rcases ht.eq_or_lt with rfl | hpos
  · simp
  rcases le_total t 1 with h1 | h1
  · have := Real.abs_log_mul_self_lt t hpos h1
    rw [mul_comm]
    nlinarith [sq_nonneg t]
  · have hl : 0 ≤ Real.log t := Real.log_nonneg h1
    have hu : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos hpos
    rw [abs_of_nonneg (by positivity)]
    nlinarith
theorem continuous_shiftedLogKernel (b : ℝ) : Continuous (shiftedLogKernel b) :=
  Real.continuous_mul_log.comp (continuous_sqNorm.add continuous_const)
theorem contDiff_sqNorm : ContDiff ℝ ∞ sqNorm := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.contDiff_sumSq <;> assumption
theorem contDiffAt_shiftedLogKernel {b : ℝ} {x : AmbientSpace} (hx : 0 < sqNorm x + b) :
    ContDiffAt ℝ ∞ (shiftedLogKernel b) x := by
  have hq : ContDiffAt ℝ ∞ (fun y => sqNorm y + b) x :=
    (contDiff_sqNorm.add contDiff_const).contDiffAt
  exact hq.mul (hq.log hx.ne')
variable {ψ : AmbientSpace → ℂ}
theorem integral_shiftedLogKernel_zero_smul (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∫ x, shiftedLogKernel 0 x • laplacianR4 (laplacianR4 (laplacianR4 ψ)) x =
      (-(1536 * ∫ y, decayKernel y)) • ψ 0 := by
  set w := laplacianR4 (laplacianR4 (laplacianR4 ψ)) with hw
  have hwd : ContDiff ℝ ∞ w :=
    contDiff_laplacianR4 (contDiff_laplacianR4 (contDiff_laplacianR4 hψ))
  have hwc : HasCompactSupport w :=
    hasCompactSupport_laplacianR4 (contDiff_laplacianR4 (contDiff_laplacianR4 hψ))
      (hasCompactSupport_laplacianR4 (contDiff_laplacianR4 hψ)
        (hasCompactSupport_laplacianR4 hψ hc))
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδpos : ∀ n, 0 < δ n := fun n => by
    simp only [δ]
    positivity
  have hδle : ∀ n, δ n ≤ 1 := fun n => by
    simp only [δ]
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hstep : ∀ n, ∫ x, shiftedLogKernel (δ n ^ 2) x • w x =
      (-1536 : ℝ) • ∫ y, decayKernel y • ψ (δ n • y) := by
    intro n
    have hb : 0 < δ n ^ 2 := pow_pos (hδpos n) 2
    have hpos : ∀ x, 0 < sqNorm x + δ n ^ 2 := fun x => by
      have := sqNorm_nonneg x
      linarith
    have hsm : ContDiff ℝ ∞ (shiftedLogKernel (δ n ^ 2)) :=
      contDiff_iff_contDiffAt.2 fun x => contDiffAt_shiftedLogKernel (hpos x)
    rw [hw, integral_smul_laplacianR4_cube hsm hψ hc, ← integral_rescaled_decayKernel (hδpos n),
      ← integral_smul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [laplacianR4_cube_shiftedLogKernel (hpos x), smul_smul]
    congr 1
    ring
  have hleft : Tendsto (fun n => ∫ x, shiftedLogKernel (δ n ^ 2) x • w x) atTop
      (𝓝 (∫ x, shiftedLogKernel 0 x • w x)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => (1 + (sqNorm x + 1) ^ 2) * ‖w x‖) (fun n => ?_) ?_
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · exact ((continuous_shiftedLogKernel _).smul hwd.continuous).aestronglyMeasurable
    · refine Continuous.integrable_of_hasCompactSupport ?_ hwc.norm.mul_left
      exact ((continuous_const.add ((continuous_sqNorm.add continuous_const).pow 2)).mul
        hwd.continuous.norm)
    · rw [norm_smul]
      gcongr
      rw [Real.norm_eq_abs]
      have hq := sqNorm_nonneg x
      have hb : δ n ^ 2 ≤ 1 := pow_le_one₀ (hδpos n).le (hδle n)
      have hb0 : 0 ≤ δ n ^ 2 := sq_nonneg _
      refine (abs_mul_log_le_one_add_sq (by linarith)).trans ?_
      gcongr
    · refine Tendsto.smul_const ?_ _
      have hcont : Continuous fun s : ℝ => shiftedLogKernel (s ^ 2) x :=
        Real.continuous_mul_log.comp (continuous_const.add (continuous_pow 2))
      have hl : Tendsto (fun n => shiftedLogKernel (δ n ^ 2) x) atTop
          (𝓝 (shiftedLogKernel (0 ^ 2) x)) :=
        (hcont.tendsto 0).comp hδlim
      simpa using hl
  have hright : Tendsto (fun n => ∫ y, decayKernel y • ψ (δ n • y)) atTop
      (𝓝 (∫ y, decayKernel y • ψ 0)) := by
    obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hc
    refine tendsto_integral_of_dominated_convergence
      (fun y => decayKernel y * C) (fun n => ?_) (integrable_decayKernel.mul_const C)
      (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · have hcont : Continuous fun y : AmbientSpace => decayKernel y • ψ (δ n • y) :=
        continuous_decayKernel.smul (hψ.continuous.comp (continuous_const_smul (δ n)))
      exact hcont.aestronglyMeasurable
    · rw [norm_smul, Real.norm_of_nonneg (decayKernel_nonneg y)]
      exact mul_le_mul_of_nonneg_left (hC _) (decayKernel_nonneg y)
    · refine Tendsto.const_smul ?_ _
      have hl : Tendsto (fun n => δ n • y) atTop (𝓝 ((0 : ℝ) • y)) := hδlim.smul_const y
      rw [zero_smul] at hl
      exact (hψ.continuous.tendsto 0).comp hl
  have hlim := tendsto_nhds_unique hleft
    ((hright.const_smul (-1536 : ℝ)).congr fun n => (hstep n).symm)
  rw [hlim, integral_smul_const, smul_smul]
  congr 1
  ring
end Fundamental
section ClassOne
theorem hasFDerivAt_sqNorm (x : AmbientSpace) :
    HasFDerivAt sqNorm
      (∑ μ, (2 * x μ) • (ContinuousLinearMap.proj μ : AmbientSpace →L[ℝ] ℝ)) x := by
  have h : ∀ μ : Fin 4, HasFDerivAt (fun y : AmbientSpace => y μ ^ 2)
      ((2 * x μ) • (ContinuousLinearMap.proj μ : AmbientSpace →L[ℝ] ℝ)) x := by
    intro μ
    have h0 : HasFDerivAt (fun y : AmbientSpace => y μ)
        (ContinuousLinearMap.proj μ : AmbientSpace →L[ℝ] ℝ) x :=
      (ContinuousLinearMap.proj μ : AmbientSpace →L[ℝ] ℝ).hasFDerivAt
    simpa using h0.pow 2
  exact HasFDerivAt.fun_sum fun μ _ => h μ
theorem continuous_apply_mul_log_sqNorm (μ : Fin 4) :
    Continuous fun y : AmbientSpace => y μ * Real.log (sqNorm y) := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.continuous_apply_mul_log_sumSq <;> assumption
def logKernelFDeriv (x : AmbientSpace) : AmbientSpace →L[ℝ] ℝ :=
  ∑ μ, (2 * (x μ + x μ * Real.log (sqNorm x))) •
    (ContinuousLinearMap.proj μ : AmbientSpace →L[ℝ] ℝ)
theorem continuous_logKernelFDeriv : Continuous logKernelFDeriv := by
  unfold logKernelFDeriv
  refine continuous_finsetSum _ fun μ _ => ?_
  exact (continuous_const.mul ((continuous_apply μ).add (continuous_apply_mul_log_sqNorm μ))).smul
    continuous_const
theorem sqrt_sqNorm_le_two_mul_norm (y : AmbientSpace) : Real.sqrt (sqNorm y) ≤ 2 * ‖y‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
theorem sqNorm_zero : sqNorm (0 : AmbientSpace) = 0 := by
  simp [sqNorm]
theorem hasFDerivAt_shiftedLogKernel_zero (x : AmbientSpace) :
    HasFDerivAt (shiftedLogKernel 0) (logKernelFDeriv x) x := by
  by_cases hx : sqNorm x = 0
  · have hx0 : x = 0 := eq_zero_of_sqNorm_eq_zero hx
    subst hx0
    have hD : logKernelFDeriv 0 = 0 := by
      simp [logKernelFDeriv]
    rw [hD]
    refine HasFDerivAt.of_isLittleO ?_
    have hr : Continuous fun y : AmbientSpace => Real.sqrt (sqNorm y) := continuous_sqNorm.sqrt
    have hA : (fun y : AmbientSpace =>
        2 * (Real.sqrt (sqNorm y) * Real.log (Real.sqrt (sqNorm y))))
        =o[𝓝 0] fun _ => (1 : ℝ) := by
      rw [Asymptotics.isLittleO_one_iff]
      have hc : Continuous fun y : AmbientSpace =>
          2 * (Real.sqrt (sqNorm y) * Real.log (Real.sqrt (sqNorm y))) :=
        continuous_const.mul (Real.continuous_mul_log.comp hr)
      have := hc.tendsto 0
      simpa [sqNorm_zero] using this
    have hB : (fun y : AmbientSpace => Real.sqrt (sqNorm y)) =O[𝓝 0]
        fun y : AmbientSpace => ‖y‖ :=
      Asymptotics.IsBigO.of_bound 2 (Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_norm]
        exact sqrt_sqNorm_le_two_mul_norm y)
    have hAB := hA.mul_isBigO hB
    have hfin : (fun x' : AmbientSpace => shiftedLogKernel 0 x' - shiftedLogKernel 0 0 -
        (0 : AmbientSpace →L[ℝ] ℝ) (x' - 0)) =o[𝓝 0] fun y : AmbientSpace => ‖y‖ := by
      refine hAB.congr' (Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
      swap
      · simp
      have hs : Real.sqrt (sqNorm y) * Real.sqrt (sqNorm y) = sqNorm y :=
        Real.mul_self_sqrt (sqNorm_nonneg y)
      have hl : Real.log (sqNorm y) = 2 * Real.log (Real.sqrt (sqNorm y)) := by
        rw [Real.log_sqrt (sqNorm_nonneg y)]
        ring
      simp only [shiftedLogKernel, add_zero, sqNorm_zero, zero_mul, sub_zero,
        zero_apply]
      rw [hl]
      linear_combination (2 * Real.log (Real.sqrt (sqNorm y))) * hs
    exact Asymptotics.isLittleO_norm_right.1 (by simpa using hfin)
  · have hpos : 0 < sqNorm x := lt_of_le_of_ne (sqNorm_nonneg x) (Ne.symm hx)
    have h1 := (Real.hasDerivAt_mul_log hx).comp_hasFDerivAt x (hasFDerivAt_sqNorm x)
    have e : shiftedLogKernel 0 = (fun s : ℝ => s * Real.log s) ∘ sqNorm := by
      funext y
      simp [shiftedLogKernel]
    rw [e]
    refine h1.congr_fderiv ?_
    simp only [logKernelFDeriv, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1
    ring
theorem contDiff_one_shiftedLogKernel_zero : ContDiff ℝ 1 (shiftedLogKernel 0) :=
  contDiff_one_iff_hasFDerivAt.2
    ⟨logKernelFDeriv, continuous_logKernelFDeriv, hasFDerivAt_shiftedLogKernel_zero⟩
end ClassOne
section Parametrix
theorem exists_real_parametrix {ε : ℝ} (hε : 0 < ε) :
    ∃ (gs gr : AmbientSpace → ℝ), ContDiff ℝ 1 gs ∧ ContDiff ℝ ∞ gr ∧
      IsCompact (tsupport gs) ∧ tsupport gs ⊆ euclidOpenBall (0 : AmbientSpace) ε ∧
      IsCompact (tsupport gr) ∧ tsupport gr ⊆ euclidOpenBall (0 : AmbientSpace) ε ∧
      ∀ ψ : AmbientSpace → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ y, gs y • laplacianR4 (laplacianR4 (laplacianR4 ψ)) y) +
          ∫ y, gr y • ψ y = ψ 0 := by
  let χ : ContDiffBump (0 : AmbientSpace) := ⟨ε / 8, ε / 4, by positivity, by linarith⟩
  have hχs : ContDiff ℝ ∞ χ := χ.contDiff
  have hχ1 : ContDiff ℝ 1 χ := hχs.of_le (by exact_mod_cast le_top)
  have hχc : IsCompact (tsupport χ) := χ.hasCompactSupport
  have hball : tsupport χ ⊆ euclidOpenBall (0 : AmbientSpace) ε := by
    intro y hy
    rw [χ.tsupport_eq] at hy
    have h1 : ‖y‖ ≤ ε / 4 := by simpa using hy
    have h2 := sqrt_sqNorm_le_two_mul_norm y
    change euclidNorm (y - 0) < ε
    rw [sub_zero]
    change Real.sqrt (sqNorm y) < ε
    linarith
  have hnear : ∀ᶠ y in 𝓝 (0 : AmbientSpace), χ y = 1 := by
    have hp : (0 : ℝ) < ε / 8 := by positivity
    filter_upwards [Metric.closedBall_mem_nhds (0 : AmbientSpace) hp] with y hy
    exact χ.one_of_mem_closedBall hy
  set H : AmbientSpace → ℝ := fun x => (1 - χ x) * shiftedLogKernel 0 x with hH
  have hHs : ContDiff ℝ ∞ H := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : sqNorm x = 0
    · have hx0 : x = 0 := eq_zero_of_sqNorm_eq_zero hx
      subst hx0
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hnear] with y hy
      simp [hH, hy]
    · have hpos : 0 < sqNorm x + 0 := by
        have := lt_of_le_of_ne (sqNorm_nonneg x) (Ne.symm hx)
        linarith
      exact (contDiff_const.sub hχs).contDiffAt.mul (contDiffAt_shiftedLogKernel hpos)
  set R : AmbientSpace → ℝ := laplacianR4 (laplacianR4 (laplacianR4 H)) with hR
  have hRs : ContDiff ℝ ∞ R :=
    contDiff_laplacianR4 (contDiff_laplacianR4 (contDiff_laplacianR4 hHs))
  have hRsupp : tsupport R ⊆ tsupport χ := by
    refine closure_minimal ?_ (isClosed_tsupport _)
    intro y hy
    by_contra hyχ
    apply hy
    have hy0 : 0 < sqNorm y + 0 := by
      have hne : sqNorm y ≠ 0 := by
        intro h0
        have hx0 : y = 0 := eq_zero_of_sqNorm_eq_zero h0
        subst hx0
        apply hyχ
        have h1 : χ (0 : AmbientSpace) = 1 := hnear.self_of_nhds
        exact subset_tsupport _ (by simp [h1])
      have := lt_of_le_of_ne (sqNorm_nonneg y) (Ne.symm hne)
      linarith
    have hev : H =ᶠ[𝓝 y] shiftedLogKernel 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hyχ] with z hz
      have : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [hH, this]
    have h3 := (laplacianR4_eventuallyEq (laplacianR4_eventuallyEq
      (laplacianR4_eventuallyEq hev))).eq_of_nhds
    rw [hR, h3, laplacianR4_cube_shiftedLogKernel hy0]
    simp
  set K : ℝ := 1536 * ∫ y, decayKernel y with hK
  have hKpos : 0 < K := mul_pos (by norm_num) integral_decayKernel_pos
  refine ⟨fun x => -K⁻¹ * (χ x * shiftedLogKernel 0 x), fun x => -K⁻¹ * R x,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.mul (hχ1.mul contDiff_one_shiftedLogKernel_zero)
  · exact contDiff_const.mul hRs
  · refine hχc.of_isClosed_subset (isClosed_tsupport _) (closure_mono ?_)
    intro y hy hχy
    exact hy (by simp [hχy])
  · refine (closure_mono ?_).trans hball
    intro y hy hχy
    exact hy (by simp [hχy])
  · refine hχc.of_isClosed_subset (isClosed_tsupport _) ?_
    refine (closure_mono ?_).trans hRsupp
    intro y hy hRy
    exact hy (by simp [hRy])
  · refine (closure_mono ?_).trans (hRsupp.trans hball)
    intro y hy hRy
    exact hy (by simp [hRy])
  · intro ψ hψ hc
    set w := laplacianR4 (laplacianR4 (laplacianR4 ψ)) with hw
    have hws : ContDiff ℝ ∞ w :=
      contDiff_laplacianR4 (contDiff_laplacianR4 (contDiff_laplacianR4 hψ))
    have hwc : HasCompactSupport w :=
      hasCompactSupport_laplacianR4 (contDiff_laplacianR4 (contDiff_laplacianR4 hψ))
        (hasCompactSupport_laplacianR4 (contDiff_laplacianR4 hψ)
          (hasCompactSupport_laplacianR4 hψ hc))
    have hi1 : Integrable fun y => shiftedLogKernel 0 y • w y :=
      integrable_real_smul_of_hasCompactSupport (continuous_shiftedLogKernel 0) hws.continuous hwc
    have hi2 : Integrable fun y => H y • w y :=
      integrable_real_smul_of_hasCompactSupport hHs.continuous hws.continuous hwc
    have hsplit : ∫ y, (χ y * shiftedLogKernel 0 y) • w y =
        (∫ y, shiftedLogKernel 0 y • w y) - ∫ y, H y • w y := by
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [hH, ← sub_smul]
      congr 1
      ring
    have hfund := integral_shiftedLogKernel_zero_smul hψ hc
    have hbyparts : ∫ y, H y • w y = ∫ y, R y • ψ y := integral_smul_laplacianR4_cube hHs hψ hc
    have e1 : ∫ y, (-K⁻¹ * (χ y * shiftedLogKernel 0 y)) • w y =
        (-K⁻¹) • ∫ y, (χ y * shiftedLogKernel 0 y) • w y := by
      rw [← integral_smul]
      simp only [smul_smul]
    have e2 : ∫ y, (-K⁻¹ * R y) • ψ y = (-K⁻¹) • ∫ y, R y • ψ y := by
      rw [← integral_smul]
      simp only [smul_smul]
    rw [e1, e2, hsplit, hfund, hbyparts, smul_sub, smul_smul]
    have hKK : -K⁻¹ * -(1536 * ∫ y, decayKernel y) = 1 := by
      rw [← hK]
      field_simp
    rw [hKK, one_smul]
    abel
theorem partialDerivR4_comp_sub_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AmbientSpace → E) (x : AmbientSpace) (μ : Fin 4) :
    partialDerivR4 μ (fun y => f (x - y)) = fun y => -partialDerivR4 μ f (x - y) := by
  funext y
  simp only [partialDerivR4]
  have e : (fun t : ℝ => f (x - (y + t • (Pi.single μ (1 : ℝ) : AmbientSpace)))) =
      fun t : ℝ => (fun s : ℝ => f (x - y + s • (Pi.single μ (1 : ℝ) : AmbientSpace))) (-t) := by
    funext t
    simp only [neg_smul]
    congr 1
    abel
  have h := deriv_comp_neg
    (fun s : ℝ => f (x - y + s • (Pi.single μ (1 : ℝ) : AmbientSpace))) (0 : ℝ)
  rw [neg_zero] at h
  rw [e]
  exact h
theorem laplacianR4_comp_sub_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AmbientSpace → E) (x : AmbientSpace) :
    laplacianR4 (fun y => f (x - y)) = fun y => laplacianR4 f (x - y) := by
  funext y
  simp only [laplacianR4, partialDerivR4_comp_sub_left]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e : partialDerivR4 μ (fun y => -partialDerivR4 μ f (x - y)) =
      -partialDerivR4 μ (fun y => partialDerivR4 μ f (x - y)) := by
    funext z
    simp only [partialDerivR4, Pi.neg_apply]
    exact deriv.fun_neg
  rw [e, Pi.neg_apply, partialDerivR4_comp_sub_left]
  simp
end Parametrix
theorem statement_holds : LaplacianCubeParametrix.Statement := by
  intro ε hε
  obtain ⟨gs, gr, hs1, hr1, hsc, hsb, hrc, hrb, hid⟩ := exists_real_parametrix hε
  have hsup : ∀ g : AmbientSpace → ℝ, tsupport (fun x => (g x : ℂ)) ⊆ tsupport g := fun g =>
    closure_mono fun y hy hg => hy (by simp [hg])
  refine ⟨fun x => (gs x : ℂ), ?_, fun x => (gr x : ℂ), ?_, ?_⟩
  · show (fun x => (gs x : ℂ)) ∈ cc1NearZero ε ∧ ∀ x, ((gs x : ℂ)).im = 0
    refine ⟨?_, fun x => by simp⟩
    show ContDiff ℝ 1 _ ∧ IsCompact _ ∧ _
    exact ⟨Complex.ofRealCLM.contDiff.comp hs1,
      hsc.of_isClosed_subset (isClosed_tsupport _) (hsup gs), (hsup gs).trans hsb⟩
  · show (fun x => (gr x : ℂ)) ∈ ccInfIn (euclidOpenBall (0 : AmbientSpace) ε) ∧
      ∀ x, ((gr x : ℂ)).im = 0
    refine ⟨?_, fun x => by simp⟩
    show ContDiff ℝ ∞ _ ∧ IsCompact _ ∧ _
    exact ⟨Complex.ofRealCLM.contDiff.comp hr1,
      hrc.of_isClosed_subset (isClosed_tsupport _) (hsup gr), (hsup gr).trans hrb⟩
  · intro k hk
    obtain ⟨hks, hkc, -⟩ : ContDiff ℝ ∞ k ∧ IsCompact (tsupport k) ∧ _ := hk
    funext x
    have hψs : ContDiff ℝ ∞ fun y => k (x - y) := hks.comp (contDiff_const.sub contDiff_id)
    have hψc : HasCompactSupport fun y => k (x - y) :=
      HasCompactSupport.comp_homeomorph hkc (Homeomorph.subLeft x)
    have h := hid _ hψs hψc
    simp only [laplacianR4_comp_sub_left] at h
    have c1 : convolve (laplacianR4 (laplacianR4 (laplacianR4 k)))
        (fun z => (gs z : ℂ)) x =
        ∫ y, gs y • laplacianR4 (laplacianR4 (laplacianR4 k)) (x - y) := by
      simp only [convolve, lebesgueIntegral, integralWrt]
      rw [← integral_sub_left_eq_self _ volume x]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp [mul_comm]
    have c2 : convolve k (fun z => (gr z : ℂ)) x = ∫ y, gr y • k (x - y) := by
      simp only [convolve, lebesgueIntegral, integralWrt]
      rw [← integral_sub_left_eq_self _ volume x]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp [mul_comm]
    rw [Pi.add_apply, c1, c2, h]
    simp
end LaplacianCubeParametrix
end YangMills.Construction.TwoPoints
end
