import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystemProof
import YangMills.Construction.TwoPoints.LocalKernelOfAFormProof
import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrability
import Reconstruction.Continuum.KernelsThatGiveBackAFunctionFromItsThirdDerivatives
import Mathlib
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.CubeKernels
theorem isPlateauBump_plateauBump
    (hT : WightmanReconstruction.SmoothToolkit.Toolkit) :
    IsPlateauBump plateauBump := by
  obtain ⟨_, ⟨⟨Λ, hΛ⟩, hall⟩, _⟩ := hT
  obtain ⟨_, _, hs, h01, h1, h0⟩ := hall Λ hΛ
  exact Classical.epsilon_spec ⟨_, hs.1, hs.2.1, h01, h1, h0⟩
theorem deriv_eq_zero_of_eqOn_const {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ} {a : ℝ}
    (h : ∀ t ∈ U, f t = a) : ∀ t ∈ U, deriv f t = 0 := by
  intro t ht
  have hev : f =ᶠ[𝓝 t] fun _ => a := by
    filter_upwards [hU.mem_nhds ht] with s hs using h s hs
  rw [hev.deriv_eq]
  simp
set_option linter.unusedSectionVars false
section Line
variable (hχ : IsPlateauBump plateauBump)
def bumpD1 : ℝ → ℝ := deriv plateauBump
def bumpD2 : ℝ → ℝ := deriv bumpD1
def bumpD3 : ℝ → ℝ := deriv bumpD2
def halfSqBump (t : ℝ) : ℝ := 1 / 2 * t ^ 2 * plateauBump t
def halfSqBumpD1 (t : ℝ) : ℝ := t * plateauBump t + 1 / 2 * t ^ 2 * bumpD1 t
def halfSqBumpD2 (t : ℝ) : ℝ := plateauBump t + 2 * t * bumpD1 t + 1 / 2 * t ^ 2 * bumpD2 t
def halfSqBumpD3 (t : ℝ) : ℝ := 3 * bumpD1 t + 3 * t * bumpD2 t + 1 / 2 * t ^ 2 * bumpD3 t
include hχ
theorem contDiff_plateauBump : ContDiff ℝ ∞ plateauBump := hχ.1
theorem contDiff_bumpD1 : ContDiff ℝ ∞ bumpD1 := by
  have := (contDiff_infty_iff_deriv.1 (contDiff_plateauBump hχ)).2
  exact this
theorem contDiff_bumpD2 : ContDiff ℝ ∞ bumpD2 :=
  (contDiff_infty_iff_deriv.1 (contDiff_bumpD1 hχ)).2
theorem contDiff_bumpD3 : ContDiff ℝ ∞ bumpD3 :=
  (contDiff_infty_iff_deriv.1 (contDiff_bumpD2 hχ)).2
theorem hasDerivAt_plateauBump (t : ℝ) : HasDerivAt plateauBump (bumpD1 t) t :=
  ((contDiff_plateauBump hχ).differentiable (by simp)).differentiableAt.hasDerivAt
theorem hasDerivAt_bumpD1 (t : ℝ) : HasDerivAt bumpD1 (bumpD2 t) t :=
  ((contDiff_bumpD1 hχ).differentiable (by simp)).differentiableAt.hasDerivAt
theorem hasDerivAt_bumpD2 (t : ℝ) : HasDerivAt bumpD2 (bumpD3 t) t :=
  ((contDiff_bumpD2 hχ).differentiable (by simp)).differentiableAt.hasDerivAt
theorem hasDerivAt_halfSqBump (t : ℝ) : HasDerivAt halfSqBump (halfSqBumpD1 t) t := by
  have h := ((((hasDerivAt_id t).pow 2).const_mul (1 / 2 : ℝ)).mul (hasDerivAt_plateauBump hχ t))
  refine HasDerivAt.congr_deriv (f := halfSqBump) h ?_
  simp [halfSqBumpD1]
theorem hasDerivAt_halfSqBumpD1 (t : ℝ) : HasDerivAt halfSqBumpD1 (halfSqBumpD2 t) t := by
  have h := ((hasDerivAt_id t).mul (hasDerivAt_plateauBump hχ t)).add
    ((((hasDerivAt_id t).pow 2).const_mul (1 / 2 : ℝ)).mul (hasDerivAt_bumpD1 hχ t))
  refine HasDerivAt.congr_deriv (f := halfSqBumpD1) h ?_
  simp [halfSqBumpD2]
  ring
theorem hasDerivAt_halfSqBumpD2 (t : ℝ) : HasDerivAt halfSqBumpD2 (halfSqBumpD3 t) t := by
  have h := ((hasDerivAt_plateauBump hχ t).add
    (((hasDerivAt_id t).const_mul (2 : ℝ)).mul (hasDerivAt_bumpD1 hχ t))).add
    ((((hasDerivAt_id t).pow 2).const_mul (1 / 2 : ℝ)).mul (hasDerivAt_bumpD2 hχ t))
  refine HasDerivAt.congr_deriv (f := halfSqBumpD2) h ?_
  simp [halfSqBumpD3]
  ring
theorem plateauBump_eq_one_of_mem {t : ℝ} (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    plateauBump t = 1 :=
  hχ.2.2.2.1 t ⟨ht.1.le, ht.2.le⟩
theorem plateauBump_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) : plateauBump t = 0 :=
  hχ.2.2.2.2 t fun h => absurd h.2 (not_le.2 ht)
theorem bumpD1_eq_zero_of_mem {t : ℝ} (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) : bumpD1 t = 0 :=
  deriv_eq_zero_of_eqOn_const isOpen_Ioo (fun _ hs => plateauBump_eq_one_of_mem hχ hs) t ht
theorem bumpD2_eq_zero_of_mem {t : ℝ} (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) : bumpD2 t = 0 :=
  deriv_eq_zero_of_eqOn_const isOpen_Ioo (fun _ hs => bumpD1_eq_zero_of_mem hχ hs) t ht
theorem bumpD3_eq_zero_of_mem {t : ℝ} (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) : bumpD3 t = 0 :=
  deriv_eq_zero_of_eqOn_const isOpen_Ioo (fun _ hs => bumpD2_eq_zero_of_mem hχ hs) t ht
theorem bumpD1_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) : bumpD1 t = 0 :=
  deriv_eq_zero_of_eqOn_const isOpen_Ioi (fun _ hs => plateauBump_eq_zero_of_one_lt hχ hs) t ht
theorem bumpD2_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) : bumpD2 t = 0 :=
  deriv_eq_zero_of_eqOn_const isOpen_Ioi (fun _ hs => bumpD1_eq_zero_of_one_lt hχ hs) t ht
theorem bumpD3_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) : bumpD3 t = 0 :=
  deriv_eq_zero_of_eqOn_const isOpen_Ioi (fun _ hs => bumpD2_eq_zero_of_one_lt hχ hs) t ht
theorem halfSqBumpD3_eq_zero_of_mem {t : ℝ} (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    halfSqBumpD3 t = 0 := by
  simp [halfSqBumpD3, bumpD1_eq_zero_of_mem hχ ht, bumpD2_eq_zero_of_mem hχ ht,
    bumpD3_eq_zero_of_mem hχ ht]
theorem halfSqBumpD3_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) : halfSqBumpD3 t = 0 := by
  simp [halfSqBumpD3, bumpD1_eq_zero_of_one_lt hχ ht, bumpD2_eq_zero_of_one_lt hχ ht,
    bumpD3_eq_zero_of_one_lt hχ ht]
theorem thirdDerivBump_of_pos {t : ℝ} (ht : 0 < t) : thirdDerivBump t = -halfSqBumpD3 t := by
  simp only [thirdDerivBump, if_pos ht, halfSqBumpD3, bumpD1, bumpD2, bumpD3]
theorem thirdDerivBump_of_nonpos {t : ℝ} (ht : t ≤ 0) : thirdDerivBump t = 0 := by
  simp only [thirdDerivBump, if_neg (not_lt.2 ht)]
theorem quadBump_of_nonneg {t : ℝ} (ht : 0 ≤ t) : quadBump t = halfSqBump t := by
  simp only [quadBump, halfSqBump, max_eq_left ht]
theorem quadBump_of_nonpos {t : ℝ} (ht : t ≤ 0) : quadBump t = 0 := by
  simp only [quadBump, max_eq_right ht]
  simp
theorem thirdDerivBump_eq_zero_of_lt_half {t : ℝ} (ht : t < 1 / 2) : thirdDerivBump t = 0 := by
  rcases le_or_gt t 0 with h | h
  · exact thirdDerivBump_of_nonpos hχ h
  · rw [thirdDerivBump_of_pos hχ h, halfSqBumpD3_eq_zero_of_mem hχ ⟨by linarith, ht⟩, neg_zero]
theorem thirdDerivBump_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) : thirdDerivBump t = 0 := by
  rw [thirdDerivBump_of_pos hχ (by linarith), halfSqBumpD3_eq_zero_of_one_lt hχ ht, neg_zero]
theorem quadBump_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) : quadBump t = 0 := by
  simp [quadBump, plateauBump_eq_zero_of_one_lt hχ ht]
theorem contDiff_thirdDerivBump : ContDiff ℝ ∞ thirdDerivBump := by
  have hg3 : ContDiff ℝ ∞ halfSqBumpD3 := by
    have h1 := contDiff_bumpD1 hχ
    have h2 := contDiff_bumpD2 hχ
    have h3 := contDiff_bumpD3 hχ
    unfold halfSqBumpD3
    fun_prop
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge t (1 / 2) with h | h
  · have hev : thirdDerivBump =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [isOpen_Iio.mem_nhds h] with s hs using
        thirdDerivBump_eq_zero_of_lt_half hχ hs
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hev : thirdDerivBump =ᶠ[𝓝 t] fun s => -halfSqBumpD3 s := by
      filter_upwards [isOpen_Ioi.mem_nhds (show (0 : ℝ) < t by linarith)] with s hs
      exact thirdDerivBump_of_pos hχ hs
    exact hg3.contDiffAt.neg.congr_of_eventuallyEq hev
omit hχ in
theorem hasDerivAt_half_sq_max_zero (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 / 2 * max s 0 ^ 2) (max t 0) t := by
  have hne : ∀ y : ℝ, y ≠ 0 → HasDerivAt (fun s : ℝ => 1 / 2 * max s 0 ^ 2) (max y 0) y := by
    intro y hy
    rcases lt_or_gt_of_ne hy with h | h
    · have hev : (fun s : ℝ => 1 / 2 * max s 0 ^ 2) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [isOpen_Iio.mem_nhds h] with s hs
        have hs' : s < 0 := hs
        simp [max_eq_right hs'.le]
      rw [max_eq_right h.le]
      exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
    · have hev : (fun s : ℝ => 1 / 2 * max s 0 ^ 2) =ᶠ[𝓝 y] fun s => 1 / 2 * s ^ 2 := by
        filter_upwards [isOpen_Ioi.mem_nhds h] with s hs
        have hs' : 0 < s := hs
        simp [max_eq_left hs'.le]
      rw [max_eq_left h.le]
      have h2 := ((hasDerivAt_id y).pow 2).const_mul (1 / 2 : ℝ)
      refine HasDerivAt.congr_of_eventuallyEq
        (HasDerivAt.congr_deriv (f := fun s : ℝ => 1 / 2 * s ^ 2) h2 ?_) hev
      simp
  by_cases ht : t = 0
  · subst ht
    exact hasDerivAt_of_hasDerivAt_of_ne (g := fun y : ℝ => max y 0) hne (by fun_prop)
      (by fun_prop)
  · exact hne t ht
theorem contDiff_quadBump : ContDiff ℝ 1 quadBump := by
  have hP : ContDiff ℝ 1 (fun s : ℝ => 1 / 2 * max s 0 ^ 2) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hasDerivAt_half_sq_max_zero t).differentiableAt, ?_⟩
    have : deriv (fun s : ℝ => 1 / 2 * max s 0 ^ 2) = fun t => max t 0 :=
      funext fun t => (hasDerivAt_half_sq_max_zero t).deriv
    rw [this]
    fun_prop
  exact hP.mul ((contDiff_plateauBump hχ).of_le (by simp))
theorem support_quadBump_subset : Function.support quadBump ⊆ Icc 0 1 := by
  intro t ht
  by_contra hn
  apply ht
  rcases lt_or_ge t 0 with h | h
  · exact quadBump_of_nonpos hχ h.le
  · exact quadBump_eq_zero_of_one_lt hχ (not_le.1 fun h' => hn ⟨h, h'⟩)
theorem support_thirdDerivBump_subset : Function.support thirdDerivBump ⊆ Icc 0 1 := by
  intro t ht
  by_contra hn
  apply ht
  rcases lt_or_ge t 0 with h | h
  · exact thirdDerivBump_of_nonpos hχ h.le
  · exact thirdDerivBump_eq_zero_of_one_lt hχ (not_le.1 fun h' => hn ⟨h, h'⟩)
end Line
section Scale
variable (hχ : IsPlateauBump plateauBump)
include hχ
theorem continuous_quadBump : Continuous quadBump := (contDiff_quadBump hχ).continuous
theorem continuous_thirdDerivBump : Continuous thirdDerivBump :=
  (contDiff_thirdDerivBump hχ).continuous
theorem continuous_quadBumpScaled (υ : ℝ) : Continuous (quadBumpScaled υ) := by
  have := continuous_quadBump hχ
  unfold quadBumpScaled
  fun_prop
theorem continuous_thirdDerivBumpScaled (υ : ℝ) : Continuous (thirdDerivBumpScaled υ) := by
  have := continuous_thirdDerivBump hχ
  unfold thirdDerivBumpScaled
  fun_prop
theorem support_quadBumpScaled_subset {υ : ℝ} (hυ : 0 < υ) :
    Function.support (quadBumpScaled υ) ⊆ Icc 0 υ := by
  intro t ht
  have h : quadBump (t / υ) ≠ 0 := fun h => ht (by simp [quadBumpScaled, h])
  obtain ⟨h0, h1⟩ := support_quadBump_subset hχ h
  exact ⟨(div_nonneg_iff.1 h0).elim (·.1) (fun h => absurd h.2 (not_le.2 hυ)),
    (div_le_one hυ).1 h1⟩
theorem support_thirdDerivBumpScaled_subset {υ : ℝ} (hυ : 0 < υ) :
    Function.support (thirdDerivBumpScaled υ) ⊆ Icc 0 υ := by
  intro t ht
  have h : thirdDerivBump (t / υ) ≠ 0 := fun h => ht (by simp [thirdDerivBumpScaled, h])
  obtain ⟨h0, h1⟩ := support_thirdDerivBump_subset hχ h
  exact ⟨(div_nonneg_iff.1 h0).elim (·.1) (fun h => absurd h.2 (not_le.2 hυ)),
    (div_le_one hυ).1 h1⟩
theorem reproduce_on_line {υ : ℝ} (hυ : 0 < υ) {u u1 u2 u3 : ℝ → ℂ}
    (d0 : ∀ s, HasDerivAt u (u1 s) s) (d1 : ∀ s, HasDerivAt u1 (u2 s) s)
    (d2 : ∀ s, HasDerivAt u2 (u3 s) s) (hc : Continuous u3) :
    u 0 = (∫ s, (quadBumpScaled υ s : ℂ) * u3 (-s)) +
      ∫ s, (thirdDerivBumpScaled υ s : ℂ) * u (-s) := by
  have hυ' : υ ≠ 0 := hυ.ne'
  have hu : Continuous u := continuous_iff_continuousAt.2 fun s => (d0 s).continuousAt
  have hsc : ∀ s : ℝ, HasDerivAt (fun r : ℝ => r / υ) (υ⁻¹) s := fun s => by
    simpa [div_eq_mul_inv] using (hasDerivAt_id s).mul_const υ⁻¹
  have e0 : ∀ s : ℝ, HasDerivAt (fun r : ℝ => ((υ ^ 2 * halfSqBump (r / υ) : ℝ) : ℂ))
      ((υ * halfSqBumpD1 (s / υ) : ℝ) : ℂ) s := fun s => by
    have h := (((hasDerivAt_halfSqBump hχ (s / υ)).comp s (hsc s)).const_mul (υ ^ 2)).ofReal_comp
    refine HasDerivAt.congr_deriv h ?_
    congr 1
    field_simp
  have e1 : ∀ s : ℝ, HasDerivAt (fun r : ℝ => ((υ * halfSqBumpD1 (r / υ) : ℝ) : ℂ))
      ((halfSqBumpD2 (s / υ) : ℝ) : ℂ) s := fun s => by
    have h := (((hasDerivAt_halfSqBumpD1 hχ (s / υ)).comp s (hsc s)).const_mul υ).ofReal_comp
    refine HasDerivAt.congr_deriv h ?_
    congr 1
    field_simp
  have e2 : ∀ s : ℝ, HasDerivAt (fun r : ℝ => ((halfSqBumpD2 (r / υ) : ℝ) : ℂ))
      ((υ⁻¹ * halfSqBumpD3 (s / υ) : ℝ) : ℂ) s := fun s => by
    have h := ((hasDerivAt_halfSqBumpD2 hχ (s / υ)).comp s (hsc s)).ofReal_comp
    refine HasDerivAt.congr_deriv h ?_
    congr 1
    ring
  have r0 : ∀ s : ℝ, HasDerivAt (fun r : ℝ => u (-r)) (-u1 (-s)) s := fun s => by
    have h := (d0 (-s)).scomp s (hasDerivAt_neg s)
    exact HasDerivAt.congr_deriv (f := fun r : ℝ => u (-r)) h (by simp)
  have r1 : ∀ s : ℝ, HasDerivAt (fun r : ℝ => u1 (-r)) (-u2 (-s)) s := fun s => by
    have h := (d1 (-s)).scomp s (hasDerivAt_neg s)
    exact HasDerivAt.congr_deriv (f := fun r : ℝ => u1 (-r)) h (by simp)
  have r2 : ∀ s : ℝ, HasDerivAt (fun r : ℝ => u2 (-r)) (-u3 (-s)) s := fun s => by
    have h := (d2 (-s)).scomp s (hasDerivAt_neg s)
    exact HasDerivAt.congr_deriv (f := fun r : ℝ => u2 (-r)) h (by simp)
  set F : ℝ → ℂ := fun s => ((υ ^ 2 * halfSqBump (s / υ) : ℝ) : ℂ) * u2 (-s) +
    ((υ * halfSqBumpD1 (s / υ) : ℝ) : ℂ) * u1 (-s) + ((halfSqBumpD2 (s / υ) : ℝ) : ℂ) * u (-s)
    with hF
  set F' : ℝ → ℂ := fun s => -(((υ ^ 2 * halfSqBump (s / υ) : ℝ) : ℂ) * u3 (-s)) +
    ((υ⁻¹ * halfSqBumpD3 (s / υ) : ℝ) : ℂ) * u (-s) with hF'
  have hFd : ∀ s, HasDerivAt F (F' s) s := fun s => by
    have h := (((e0 s).mul (r2 s)).add ((e1 s).mul (r1 s))).add ((e2 s).mul (r0 s))
    refine HasDerivAt.congr_deriv (f := F) h ?_
    simp only [hF']
    ring
  have hg0c : Continuous halfSqBump :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_halfSqBump hχ s).continuousAt
  have hg3c : Continuous halfSqBumpD3 := by
    have h1 := (contDiff_bumpD1 hχ).continuous
    have h2 := (contDiff_bumpD2 hχ).continuous
    have h3 := (contDiff_bumpD3 hχ).continuous
    unfold halfSqBumpD3
    fun_prop
  have hF'c : Continuous F' := by
    simp only [hF']
    fun_prop (disch := exact hυ')
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * υ)
    (fun s _ => hFd s) (hF'c.intervalIntegrable _ _)
  have hend : F (2 * υ) = 0 := by
    have h2 : (2 * υ) / υ = 2 := by field_simp
    have hc0 : plateauBump 2 = 0 := plateauBump_eq_zero_of_one_lt hχ (by norm_num)
    have hc1 : bumpD1 2 = 0 := bumpD1_eq_zero_of_one_lt hχ (by norm_num)
    have hc2 : bumpD2 2 = 0 := bumpD2_eq_zero_of_one_lt hχ (by norm_num)
    simp [hF, h2, halfSqBump, halfSqBumpD1, halfSqBumpD2, hc0, hc1, hc2]
  have hstart : F 0 = u 0 := by
    have hc0 : plateauBump 0 = 1 := plateauBump_eq_one_of_mem hχ (by norm_num)
    simp [hF, halfSqBump, halfSqBumpD1, halfSqBumpD2, hc0]
  rw [hend, hstart, zero_sub, intervalIntegral.integral_of_le (by positivity)] at hFTC
  have hk : Continuous fun s => (quadBumpScaled υ s : ℂ) * u3 (-s) := by
    have := continuous_quadBumpScaled hχ υ
    fun_prop
  have hp : Continuous fun s => (thirdDerivBumpScaled υ s : ℂ) * u (-s) := by
    have := continuous_thirdDerivBumpScaled hχ υ
    fun_prop
  have hkeq : ∫ s in Ioc 0 (2 * υ), (quadBumpScaled υ s : ℂ) * u3 (-s) =
      ∫ s, (quadBumpScaled υ s : ℂ) * u3 (-s) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
    have : quadBumpScaled υ s = 0 := by
      by_contra hne
      obtain ⟨a, b⟩ := support_quadBumpScaled_subset hχ hυ hne
      rcases a.eq_or_lt with h | h
      · apply hne
        subst h
        simp [quadBumpScaled, quadBump]
      · exact hs ⟨h, by linarith⟩
    simp [this]
  have hpeq : ∫ s in Ioc 0 (2 * υ), (thirdDerivBumpScaled υ s : ℂ) * u (-s) =
      ∫ s, (thirdDerivBumpScaled υ s : ℂ) * u (-s) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
    have : thirdDerivBumpScaled υ s = 0 := by
      by_contra hne
      obtain ⟨a, b⟩ := support_thirdDerivBumpScaled_subset hχ hυ hne
      rcases a.eq_or_lt with h | h
      · apply hne
        subst h
        simp [thirdDerivBumpScaled, thirdDerivBump]
      · exact hs ⟨h, by linarith⟩
    simp [this]
  have hcongr : ∫ s in Ioc 0 (2 * υ), F' s =
      ∫ s in Ioc 0 (2 * υ), (-((quadBumpScaled υ s : ℂ) * u3 (-s)) -
        (thirdDerivBumpScaled υ s : ℂ) * u (-s)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs0 : 0 < s / υ := div_pos hs.1 hυ
    simp only [hF', quadBumpScaled, thirdDerivBumpScaled, quadBump_of_nonneg hχ hs0.le,
      thirdDerivBump_of_pos hχ hs0]
    push_cast
    ring
  have hsplit := integral_sub (μ := volume.restrict (Ioc 0 (2 * υ)))
    (f := fun s => -((quadBumpScaled υ s : ℂ) * u3 (-s)))
    (g := fun s => (thirdDerivBumpScaled υ s : ℂ) * u (-s))
    (hk.integrableOn_Ioc (a := 0) (b := 2 * υ)).neg hp.integrableOn_Ioc
  rw [hcongr, hsplit, integral_neg, hkeq, hpeq] at hFTC
  linear_combination hFTC
end Scale
section Space
open YangMills.Construction.TestFunctions
def basisVec (μ : Fin 4) : Fin 4 → ℝ := Pi.single μ 1
theorem partialDerivR4_eq_fderiv {g : (Fin 4 → ℝ) → ℂ} (hg : Differentiable ℝ g) (μ : Fin 4)
    (y : Fin 4 → ℝ) : partialDerivR4 μ g y = fderiv ℝ g y (basisVec μ) := by apply _root_.YangMills.Construction.ConfigSpace.ModeCost.partialDerivR4_eq_fderiv <;> assumption
theorem contDiff_partialDerivR4 {g : (Fin 4 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (μ : Fin 4) :
    ContDiff ℝ ∞ (partialDerivR4 μ g) := by apply _root_.YangMills.Construction.TwoPoints.LocalFormKernel.contDiff_partialDerivR4 <;> assumption
theorem hasDerivAt_comp_line {g : (Fin 4 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (μ : Fin 4)
    (x : Fin 4 → ℝ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => g (x + r • basisVec μ))
      (partialDerivR4 μ g (x + r • basisVec μ)) r := by
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  have hl : HasDerivAt (fun r : ℝ => x + r • basisVec μ) (basisVec μ) r := by
    simpa using ((hasDerivAt_id r).smul_const (basisVec μ)).const_add x
  rw [partialDerivR4_eq_fderiv hd]
  exact (hd _).hasFDerivAt.comp_hasDerivAt r hl
variable (hχ : IsPlateauBump plateauBump)
include hχ
theorem reproduce_along_axis {υ : ℝ} (hυ : 0 < υ) {g : (Fin 4 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (μ : Fin 4) (x : Fin 4 → ℝ) :
    g x = (∫ s, (quadBumpScaled υ s : ℂ) *
        partialDerivR4 μ (partialDerivR4 μ (partialDerivR4 μ g)) (x - s • basisVec μ)) +
      ∫ s, (thirdDerivBumpScaled υ s : ℂ) * g (x - s • basisVec μ) := by
  have h1 := contDiff_partialDerivR4 hg μ
  have h2 := contDiff_partialDerivR4 h1 μ
  have h3 := contDiff_partialDerivR4 h2 μ
  have := reproduce_on_line hχ hυ (u := fun r => g (x + r • basisVec μ))
    (u1 := fun r => partialDerivR4 μ g (x + r • basisVec μ))
    (u2 := fun r => partialDerivR4 μ (partialDerivR4 μ g) (x + r • basisVec μ))
    (u3 := fun r => partialDerivR4 μ (partialDerivR4 μ (partialDerivR4 μ g)) (x + r • basisVec μ))
    (hasDerivAt_comp_line hg μ x) (hasDerivAt_comp_line h1 μ x) (hasDerivAt_comp_line h2 μ x)
    (by have := h3.continuous; fun_prop)
  simpa [sub_eq_add_neg] using this
omit hχ
def axisConv (f : ℝ → ℝ) (μ : Fin 4) (g : (Fin 4 → ℝ) → ℂ) (x : Fin 4 → ℝ) : ℂ :=
  ∫ s, (f s : ℂ) * g (x - s • basisVec μ)
def axisKernel (υ : ℝ) (b : Bool) : ℝ → ℝ := if b then quadBumpScaled υ else thirdDerivBumpScaled υ
def cubedAxisPartial (b : Bool) (μ : Fin 4) (g : (Fin 4 → ℝ) → ℂ) : (Fin 4 → ℝ) → ℂ :=
  (partialDerivR4 μ)^[if b then 3 else 0] g
theorem contDiff_cubedAxisPartial {g : (Fin 4 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (b : Bool)
    (μ : Fin 4) : ContDiff ℝ ∞ (cubedAxisPartial b μ g) := by
  cases b
  · simpa [cubedAxisPartial] using hg
  · simpa [cubedAxisPartial] using
      contDiff_partialDerivR4 (contDiff_partialDerivR4 (contDiff_partialDerivR4 hg μ) μ) μ
def IsSegmentKernel (c : ℝ) (f : ℝ → ℝ) : Prop := Continuous f ∧ Function.support f ⊆ Icc 0 c
include hχ in
theorem isSegmentKernel_axisKernel {υ : ℝ} (hυ : 0 < υ) (b : Bool) :
    IsSegmentKernel υ (axisKernel υ b) := by
  cases b
  · exact ⟨continuous_thirdDerivBumpScaled hχ υ, support_thirdDerivBumpScaled_subset hχ hυ⟩
  · exact ⟨continuous_quadBumpScaled hχ υ, support_quadBumpScaled_subset hχ hυ⟩
theorem IsSegmentKernel.hasCompactSupport {c : ℝ} {f : ℝ → ℝ} (hf : IsSegmentKernel c f) :
    HasCompactSupport f :=
  HasCompactSupport.intro isCompact_Icc fun _ hs => by
    by_contra hne
    exact hs (hf.2 hne)
theorem IsSegmentKernel.integrable_mul {c : ℝ} {f : ℝ → ℝ} (hf : IsSegmentKernel c f)
    {u : ℝ → ℂ} (hu : Continuous u) : Integrable fun s => (f s : ℂ) * u s := by
  have h1 : Continuous fun s => (f s : ℂ) * u s := by
    have := hf.1
    fun_prop
  refine h1.integrable_of_hasCompactSupport ?_
  have h2 : HasCompactSupport fun s => (f s : ℂ) :=
    hf.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  exact h2.mul_right
theorem continuous_axisConv {c : ℝ} {f : ℝ → ℝ} (hf : IsSegmentKernel c f) (μ : Fin 4)
    {g : (Fin 4 → ℝ) → ℂ} (hg : Continuous g) : Continuous (axisConv f μ g) := by
  have heq : axisConv f μ g = fun x => ∫ s in Icc 0 c, (f s : ℂ) * g (x - s • basisVec μ) := by
    funext x
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_).symm
    have : f s = 0 := by
      by_contra hne
      exact hs (hf.2 hne)
    simp [this]
  rw [heq]
  have hc := hf.1
  refine continuous_parametric_integral_of_continuous ?_ isCompact_Icc
  simp only [Function.uncurry_def]
  fun_prop
theorem axisConv_add {c : ℝ} {f : ℝ → ℝ} (hf : IsSegmentKernel c f) (μ : Fin 4)
    {g₁ g₂ : (Fin 4 → ℝ) → ℂ} (h₁ : Continuous g₁) (h₂ : Continuous g₂) :
    axisConv f μ (g₁ + g₂) = axisConv f μ g₁ + axisConv f μ g₂ := by
  funext x
  simp only [axisConv, Pi.add_apply, mul_add]
  exact integral_add (hf.integrable_mul (by fun_prop)) (hf.integrable_mul (by fun_prop))
def IsAdditiveContinuous (A : ((Fin 4 → ℝ) → ℂ) → (Fin 4 → ℝ) → ℂ) : Prop :=
  (∀ g, Continuous g → Continuous (A g)) ∧
    ∀ g₁ g₂, Continuous g₁ → Continuous g₂ → A (g₁ + g₂) = A g₁ + A g₂
theorem isAdditiveContinuous_id : IsAdditiveContinuous id :=
  ⟨fun _ h => h, fun _ _ _ _ => rfl⟩
theorem IsAdditiveContinuous.comp_axisConv {A : ((Fin 4 → ℝ) → ℂ) → (Fin 4 → ℝ) → ℂ}
    (hA : IsAdditiveContinuous A) {c : ℝ} {f : ℝ → ℝ} (hf : IsSegmentKernel c f) (μ : Fin 4) :
    IsAdditiveContinuous fun g => A (axisConv f μ g) :=
  ⟨fun _ h => hA.1 _ (continuous_axisConv hf μ h), fun _ _ h₁ h₂ => by
    simp only [axisConv_add hf μ h₁ h₂]
    exact hA.2 _ _ (continuous_axisConv hf μ h₁) (continuous_axisConv hf μ h₂)⟩
include hχ in
theorem expand_along_axis {A : ((Fin 4 → ℝ) → ℂ) → (Fin 4 → ℝ) → ℂ}
    (hA : IsAdditiveContinuous A) {υ : ℝ} (hυ : 0 < υ) {g : (Fin 4 → ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (μ : Fin 4) :
    A g = ∑ b : Bool, A (axisConv (axisKernel υ b) μ (cubedAxisPartial b μ g)) := by
  have hsum : g = axisConv (axisKernel υ true) μ (cubedAxisPartial true μ g) +
      axisConv (axisKernel υ false) μ (cubedAxisPartial false μ g) := by
    funext x
    simpa [axisConv, axisKernel, cubedAxisPartial] using reproduce_along_axis hχ hυ hg μ x
  rw [Fintype.sum_bool, ← hA.2 _ _ (continuous_axisConv (isSegmentKernel_axisKernel hχ hυ true) μ
    (contDiff_cubedAxisPartial hg true μ).continuous)
    (continuous_axisConv (isSegmentKernel_axisKernel hχ hυ false) μ
    (contDiff_cubedAxisPartial hg false μ).continuous), ← hsum]
include hχ in
theorem eq_sum_sixteen {υ : ℝ} (hυ : 0 < υ) {h : (Fin 4 → ℝ) → ℂ} (hh : ContDiff ℝ ∞ h) :
    h = ∑ b₃ : Bool, ∑ b₂ : Bool, ∑ b₁ : Bool, ∑ b₀ : Bool,
      axisConv (axisKernel υ b₃) 3 (axisConv (axisKernel υ b₂) 2 (axisConv (axisKernel υ b₁) 1
        (axisConv (axisKernel υ b₀) 0 (cubedAxisPartial b₀ 0 (cubedAxisPartial b₁ 1
          (cubedAxisPartial b₂ 2 (cubedAxisPartial b₃ 3 h))))))) := by
  have k := isSegmentKernel_axisKernel hχ hυ
  have s1 := expand_along_axis hχ isAdditiveContinuous_id hυ hh 3
  refine s1.trans (Finset.sum_congr rfl fun b₃ _ => ?_)
  have t3 := contDiff_cubedAxisPartial hh b₃ 3
  have a3 := isAdditiveContinuous_id.comp_axisConv (k b₃) 3
  refine (expand_along_axis hχ a3 hυ t3 2).trans (Finset.sum_congr rfl fun b₂ _ => ?_)
  have t2 := contDiff_cubedAxisPartial t3 b₂ 2
  have a2 := a3.comp_axisConv (k b₂) 2
  refine (expand_along_axis hχ a2 hυ t2 1).trans (Finset.sum_congr rfl fun b₁ _ => ?_)
  have t1 := contDiff_cubedAxisPartial t2 b₁ 1
  have a1 := a2.comp_axisConv (k b₁) 1
  exact expand_along_axis hχ a1 hυ t1 0
end Space
section Fubini
def prodKernelIntegral {n : ℕ} (f : Fin n → ℝ → ℝ) (G : (Fin n → ℝ) → ℂ) : ℂ :=
  ∫ y, ((∏ i, f i (y i) : ℝ) : ℂ) * G y
theorem hasCompactSupport_prodKernel {n : ℕ} {c : ℝ} {f : Fin n → ℝ → ℝ}
    (hf : ∀ i, IsSegmentKernel c (f i)) :
    HasCompactSupport fun y : Fin n → ℝ => ∏ i, f i (y i) := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun _ => isCompact_Icc (a := 0) (b := c)) ?_
  intro y hy
  simp only [Set.mem_pi, not_forall] at hy
  obtain ⟨i, _, hi⟩ := hy
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  by_contra hne
  exact hi ((hf i).2 hne)
theorem continuous_prodKernel {n : ℕ} {c : ℝ} {f : Fin n → ℝ → ℝ}
    (hf : ∀ i, IsSegmentKernel c (f i)) : Continuous fun y : Fin n → ℝ => ∏ i, f i (y i) :=
  continuous_finsetProd _ fun i _ => (hf i).1.comp (continuous_apply i)
theorem integrable_prodKernel_mul {n : ℕ} {c : ℝ} {f : Fin n → ℝ → ℝ}
    (hf : ∀ i, IsSegmentKernel c (f i)) {G : (Fin n → ℝ) → ℂ} (hG : Continuous G) :
    Integrable fun y : Fin n → ℝ => ((∏ i, f i (y i) : ℝ) : ℂ) * G y := by
  have hc := continuous_prodKernel hf
  have h1 : Continuous fun y : Fin n → ℝ => ((∏ i, f i (y i) : ℝ) : ℂ) * G y := by fun_prop
  refine h1.integrable_of_hasCompactSupport ?_
  have h2 : HasCompactSupport fun y : Fin n → ℝ => ((∏ i, f i (y i) : ℝ) : ℂ) :=
    (hasCompactSupport_prodKernel hf).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  exact h2.mul_right
def snocPoint {n : ℕ} (z : Fin n → ℝ) (s : ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) z s
theorem continuous_snocPoint {n : ℕ} (s : ℝ) : Continuous fun z : Fin n → ℝ => snocPoint z s := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [snocPoint] using continuous_const
  · simpa [snocPoint] using continuous_apply j
theorem prodKernelIntegral_succ {n : ℕ} {c : ℝ} {f : Fin (n + 1) → ℝ → ℝ}
    (hf : ∀ i, IsSegmentKernel c (f i)) {G : (Fin (n + 1) → ℝ) → ℂ} (hG : Continuous G) :
    prodKernelIntegral f G = ∫ s, (f (Fin.last n) s : ℂ) *
      prodKernelIntegral (fun i => f i.castSucc) (fun z => G (snocPoint z s)) := by
  have mp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
  have hint := integrable_prodKernel_mul hf hG
  have hint' := mp.integrable_comp_of_integrable hint
  unfold prodKernelIntegral
  rw [← mp.integral_comp' (g := fun y : Fin (n + 1) → ℝ => ((∏ i, f i (y i) : ℝ) : ℂ) * G y)]
  rw [Measure.volume_eq_prod] at hint' ⊢
  refine (integral_prod _ hint').trans ?_
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [Function.comp]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  have hsymm : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
      (s, z) = snocPoint z s := by
    simp [snocPoint, MeasurableEquiv.piFinSuccAbove]
    rfl
  simp only [hsymm]
  rw [Fin.prod_univ_castSucc]
  simp only [snocPoint, Fin.snoc_castSucc, Fin.snoc_last]
  push_cast
  ring
theorem prodKernelIntegral_zero (f : Fin 0 → ℝ → ℝ) (G : (Fin 0 → ℝ) → ℂ) :
    prodKernelIntegral f G = G default := by
  have hv : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac default := by
    rw [volume_pi]
    exact Measure.pi_of_empty _ _
  simp [prodKernelIntegral, hv]
theorem axisConv_iterate_eq_prodKernelIntegral {c : ℝ} {F : Fin 4 → ℝ → ℝ}
    (hF : ∀ i, IsSegmentKernel c (F i)) {G : (Fin 4 → ℝ) → ℂ} (hG : Continuous G)
    (x : Fin 4 → ℝ) :
    axisConv (F 3) 3 (axisConv (F 2) 2 (axisConv (F 1) 1 (axisConv (F 0) 0 G))) x =
      prodKernelIntegral F fun y => G (x - y) := by
  rw [prodKernelIntegral_succ hF (by fun_prop)]
  refine integral_congr_ae (ae_of_all _ fun s₃ => ?_)
  refine congrArg₂ (· * ·) rfl ?_
  rw [prodKernelIntegral_succ (fun i => hF i.castSucc)
    (by have := continuous_snocPoint (n := 3) s₃; fun_prop)]
  refine integral_congr_ae (ae_of_all _ fun s₂ => ?_)
  refine congrArg₂ (· * ·) rfl ?_
  rw [prodKernelIntegral_succ (fun i => hF i.castSucc.castSucc)
    (by have := continuous_snocPoint (n := 3) s₃; have := continuous_snocPoint (n := 2) s₂
        fun_prop)]
  refine integral_congr_ae (ae_of_all _ fun s₁ => ?_)
  refine congrArg₂ (· * ·) rfl ?_
  rw [prodKernelIntegral_succ (fun i => hF i.castSucc.castSucc.castSucc)
    (by have := continuous_snocPoint (n := 3) s₃; have := continuous_snocPoint (n := 2) s₂
        have := continuous_snocPoint (n := 1) s₁; fun_prop)]
  refine integral_congr_ae (ae_of_all _ fun s₀ => ?_)
  refine congrArg₂ (· * ·) rfl ?_
  rw [prodKernelIntegral_zero]
  refine congrArg G ?_
  ext i
  fin_cases i <;> simp [basisVec, snocPoint, Fin.snoc, sub_eq_add_neg]
theorem cubeKernel_eq_prod (Γ : Finset (Fin 4)) (υ : ℝ) (x : Fin 4 → ℝ) :
    cubeKernel Γ υ x = ∏ μ, axisKernel υ (decide (μ ∈ Γ)) (x μ) := by
  rw [← Finset.prod_mul_prod_compl Γ, cubeKernel]
  congr 1
  · exact Finset.prod_congr rfl fun μ hμ => by simp [axisKernel, hμ]
  · exact Finset.prod_congr rfl fun μ hμ => by simp [axisKernel, Finset.mem_compl.1 hμ]
theorem sum_bool4_eq_sum_finset (T : Bool → Bool → Bool → Bool → ℂ) :
    ∑ b₃ : Bool, ∑ b₂ : Bool, ∑ b₁ : Bool, ∑ b₀ : Bool, T b₀ b₁ b₂ b₃ =
      ∑ Γ : Finset (Fin 4),
        T (decide (0 ∈ Γ)) (decide (1 ∈ Γ)) (decide (2 ∈ Γ)) (decide (3 ∈ Γ)) := by
  have hb : Function.Bijective (fun Γ : Finset (Fin 4) =>
      ((decide (3 ∈ Γ), decide (2 ∈ Γ), decide (1 ∈ Γ), decide (0 ∈ Γ)) :
        Bool × Bool × Bool × Bool)) := by decide +kernel
  rw [Fintype.sum_bijective _ hb
    (fun Γ => T (decide (0 ∈ Γ)) (decide (1 ∈ Γ)) (decide (2 ∈ Γ)) (decide (3 ∈ Γ)))
    (fun p => T p.2.2.2 p.2.2.1 p.2.1 p.1) (fun Γ => rfl)]
  simp only [Fintype.sum_prod_type]
theorem cubedPartial_eq (Γ : Finset (Fin 4)) (h : (Fin 4 → ℝ) → ℂ) :
    cubedPartial Γ h = cubedAxisPartial (decide (0 ∈ Γ)) 0 (cubedAxisPartial (decide (1 ∈ Γ)) 1
      (cubedAxisPartial (decide (2 ∈ Γ)) 2 (cubedAxisPartial (decide (3 ∈ Γ)) 3 h))) := by
  simp [cubedPartial, EuclideanFunctionals.iteratedPartial, cubedAxisPartial]
variable (hχ : IsPlateauBump plateauBump)
include hχ
theorem reproducingIdentity : ReproducingIdentity := by
  intro h hh _ υ hυ
  funext x
  have hs := congrFun (eq_sum_sixteen hχ hυ hh) x
  simp only [Finset.sum_apply] at hs
  rw [hs, sum_bool4_eq_sum_finset fun b₀ b₁ b₂ b₃ =>
    axisConv (axisKernel υ b₃) 3 (axisConv (axisKernel υ b₂) 2 (axisConv (axisKernel υ b₁) 1
      (axisConv (axisKernel υ b₀) 0 (cubedAxisPartial b₀ 0 (cubedAxisPartial b₁ 1
        (cubedAxisPartial b₂ 2 (cubedAxisPartial b₃ 3 h))))))) x,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun Γ _ => ?_
  have hk : ∀ μ : Fin 4, IsSegmentKernel υ (axisKernel υ (decide (μ ∈ Γ))) :=
    fun μ => isSegmentKernel_axisKernel hχ hυ _
  have hc : Continuous (cubedPartial Γ h) := by
    rw [cubedPartial_eq]
    exact (contDiff_cubedAxisPartial (contDiff_cubedAxisPartial (contDiff_cubedAxisPartial
      (contDiff_cubedAxisPartial hh _ _) _ _) _ _) _ _).continuous
  have := axisConv_iterate_eq_prodKernelIntegral hk hc x
  rw [cubedPartial_eq] at this ⊢
  refine this.trans ?_
  simp only [prodKernelIntegral, EuclideanFunctionals.conv, cubeKernel_eq_prod]
theorem contDiff_quadBumpScaled (υ : ℝ) : ContDiff ℝ 1 (quadBumpScaled υ) :=
  contDiff_const.mul ((contDiff_quadBump hχ).comp (contDiff_id.div_const υ))
theorem contDiff_thirdDerivBumpScaled (υ : ℝ) : ContDiff ℝ 1 (thirdDerivBumpScaled υ) :=
  contDiff_const.mul (((contDiff_thirdDerivBump hχ).of_le (by simp)).comp
    (contDiff_id.div_const υ))
theorem contDiff_axisKernel (υ : ℝ) (b : Bool) : ContDiff ℝ 1 (axisKernel υ b) := by
  cases b
  · exact contDiff_thirdDerivBumpScaled hχ υ
  · exact contDiff_quadBumpScaled hχ υ
theorem supportsInCube : SupportsInCube := by
  have hκ : tsupport quadBump ⊆ Icc 0 1 :=
    closure_minimal (support_quadBump_subset hχ) isClosed_Icc
  have hψ : tsupport thirdDerivBump ⊆ Icc 0 1 :=
    closure_minimal (support_thirdDerivBump_subset hχ) isClosed_Icc
  refine ⟨contDiff_quadBump hχ, isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hκ, hκ,
    contDiff_thirdDerivBump hχ, isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hψ, hψ, ?_⟩
  intro Γ υ hυ
  have hk : ∀ μ : Fin 4, IsSegmentKernel υ (axisKernel υ (decide (μ ∈ Γ))) :=
    fun μ => isSegmentKernel_axisKernel hχ hυ _
  have hfun : cubeKernel Γ υ = fun x : Fin 4 → ℝ => ∏ μ, axisKernel υ (decide (μ ∈ Γ)) (x μ) :=
    funext (cubeKernel_eq_prod Γ υ)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show ContDiff ℝ 1 (cubeKernel Γ υ)
    rw [hfun]
    exact contDiff_prod fun μ _ => (contDiff_axisKernel hχ υ _).comp (contDiff_apply ℝ ℝ μ)
  · rw [hfun]
    exact hasCompactSupport_prodKernel hk
  · have hcl : IsClosed {x : Fin 4 → ℝ | ∀ μ, x μ ∈ Icc 0 υ} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun μ => isClosed_Icc.preimage (continuous_apply μ)
    refine closure_minimal ?_ hcl
    intro x hx μ
    rw [Function.mem_support, cubeKernel_eq_prod, Finset.prod_ne_zero_iff] at hx
    exact (hk μ).2 (hx μ (Finset.mem_univ μ))
end Fubini
section Bound
open YangMills.Construction.TestFunctions
theorem norm_le_uniformNorm {f : ℝ → ℝ} (hc : Continuous f) (hs : HasCompactSupport f) (t : ℝ) :
    ‖f t‖ ≤ uniformNorm f :=
  le_ciSup (f := fun x => ‖f x‖) (by
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩) t
variable (hχ : IsPlateauBump plateauBump)
include hχ
def boundConst : ℝ := max 1 (max (uniformNorm quadBump) (max (uniformNorm (deriv quadBump))
  (max (uniformNorm thirdDerivBump) (uniformNorm (deriv thirdDerivBump)))))
theorem one_le_boundConst : 1 ≤ boundConst := le_max_left _ _
theorem hasCompactSupport_quadBump : HasCompactSupport quadBump :=
  HasCompactSupport.intro isCompact_Icc (K := Icc (0 : ℝ) 1) fun _ hs => by
    by_contra hne
    exact hs (support_quadBump_subset hχ hne)
theorem hasCompactSupport_thirdDerivBump : HasCompactSupport thirdDerivBump :=
  HasCompactSupport.intro isCompact_Icc (K := Icc (0 : ℝ) 1) fun _ hs => by
    by_contra hne
    exact hs (support_thirdDerivBump_subset hχ hne)
theorem abs_quadBump_le (t : ℝ) : |quadBump t| ≤ boundConst :=
  (norm_le_uniformNorm (continuous_quadBump hχ) (hasCompactSupport_quadBump hχ) t).trans
    ((le_max_left _ _).trans (le_max_right _ _))
theorem abs_deriv_quadBump_le (t : ℝ) : |deriv quadBump t| ≤ boundConst :=
  (norm_le_uniformNorm (contDiff_one_iff_deriv.1 (contDiff_quadBump hχ)).2
    (hasCompactSupport_quadBump hχ).deriv t).trans
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
theorem abs_thirdDerivBump_le (t : ℝ) : |thirdDerivBump t| ≤ boundConst :=
  (norm_le_uniformNorm (continuous_thirdDerivBump hχ) (hasCompactSupport_thirdDerivBump hχ) t).trans
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _))))
theorem abs_deriv_thirdDerivBump_le (t : ℝ) : |deriv thirdDerivBump t| ≤ boundConst :=
  (norm_le_uniformNorm (contDiff_one_iff_deriv.1 ((contDiff_thirdDerivBump hχ).of_le (by simp))).2
    (hasCompactSupport_thirdDerivBump hχ).deriv t).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _))))
def axisKernelBound (υ : ℝ) (b : Bool) : ℝ := if b then υ ^ 2 * boundConst else υ⁻¹ * boundConst
theorem axisKernelBound_nonneg {υ : ℝ} (hυ : 0 < υ) (b : Bool) : 0 ≤ axisKernelBound υ b := by
  have hM : 0 ≤ boundConst := zero_le_one.trans (one_le_boundConst hχ)
  cases b <;> simp only [axisKernelBound] <;> positivity
theorem abs_axisKernel_le {υ : ℝ} (hυ : 0 < υ) (b : Bool) (t : ℝ) :
    |axisKernel υ b t| ≤ axisKernelBound υ b := by
  cases b
  · have h : axisKernel υ false t = υ⁻¹ * thirdDerivBump (t / υ) := rfl
    rw [h, abs_mul, abs_of_pos (inv_pos.2 hυ)]
    simp only [axisKernelBound, Bool.false_eq_true, if_false]
    exact mul_le_mul_of_nonneg_left (abs_thirdDerivBump_le hχ _) (inv_pos.2 hυ).le
  · have h : axisKernel υ true t = υ ^ 2 * quadBump (t / υ) := rfl
    rw [h, abs_mul, abs_of_pos (pow_pos hυ 2)]
    simp only [axisKernelBound, if_true]
    exact mul_le_mul_of_nonneg_left (abs_quadBump_le hχ _) (pow_pos hυ 2).le
theorem abs_deriv_axisKernel_le {υ : ℝ} (hυ : 0 < υ) (b : Bool) (t : ℝ) :
    |deriv (axisKernel υ b) t| ≤ axisKernelBound υ b * υ⁻¹ := by
  have hsc : HasDerivAt (fun r : ℝ => r / υ) (υ⁻¹) t := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id t).mul_const υ⁻¹
  have hi : 0 < υ⁻¹ := inv_pos.2 hυ
  cases b
  · have hd : DifferentiableAt ℝ thirdDerivBump (t / υ) :=
      ((contDiff_thirdDerivBump hχ).differentiable (by simp)) _
    have h := (hd.hasDerivAt.comp t hsc).const_mul υ⁻¹
    have he : deriv (axisKernel υ false) t = υ⁻¹ * (deriv thirdDerivBump (t / υ) * υ⁻¹) :=
      HasDerivAt.deriv (f := axisKernel υ false) h
    rw [he]
    simp only [axisKernelBound, Bool.false_eq_true, if_false, abs_mul, abs_of_pos hi]
    have := abs_deriv_thirdDerivBump_le hχ (t / υ)
    calc υ⁻¹ * (|deriv thirdDerivBump (t / υ)| * υ⁻¹) ≤ υ⁻¹ * (boundConst * υ⁻¹) := by gcongr
      _ = _ := by ring
  · have hd : DifferentiableAt ℝ quadBump (t / υ) :=
      ((contDiff_quadBump hχ).differentiable (by simp)) _
    have h := (hd.hasDerivAt.comp t hsc).const_mul (υ ^ 2)
    have he : deriv (axisKernel υ true) t = υ ^ 2 * (deriv quadBump (t / υ) * υ⁻¹) :=
      HasDerivAt.deriv (f := axisKernel υ true) h
    rw [he]
    simp only [axisKernelBound, if_true, abs_mul, abs_of_pos hi, abs_of_pos (pow_pos hυ 2)]
    have := abs_deriv_quadBump_le hχ (t / υ)
    calc υ ^ 2 * (|deriv quadBump (t / υ)| * υ⁻¹) ≤ υ ^ 2 * (boundConst * υ⁻¹) := by gcongr
      _ = _ := by ring
def cubeKernelBound (Γ : Finset (Fin 4)) (υ : ℝ) : ℝ := ∏ μ, axisKernelBound υ (decide (μ ∈ Γ))
theorem abs_cubeKernel_le {υ : ℝ} (hυ : 0 < υ) (Γ : Finset (Fin 4)) (x : Fin 4 → ℝ) :
    |cubeKernel Γ υ x| ≤ cubeKernelBound Γ υ := by
  rw [cubeKernel_eq_prod, Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun μ _ => abs_axisKernel_le hχ hυ _ _
theorem norm_partialDerivR4_cubeKernel_le {υ : ℝ} (hυ : 0 < υ) (Γ : Finset (Fin 4)) (μ : Fin 4)
    (x : Fin 4 → ℝ) :
    ‖partialDerivR4 μ (fun y => (cubeKernel Γ υ y : ℂ)) x‖ ≤ cubeKernelBound Γ υ * υ⁻¹ := by
  set φ : Fin 4 → ℝ → ℝ := fun ν => axisKernel υ (decide (ν ∈ Γ)) with hφ
  set B : ℝ := ∏ ν ∈ Finset.univ.erase μ, φ ν (x ν) with hB
  have hline : (fun t : ℝ => cubeKernel Γ υ (x + t • Pi.single μ 1)) =
      fun t => φ μ (x μ + t) * B := by
    funext t
    rw [cubeKernel_eq_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ)]
    congr 1
    · simp [hφ]
    · refine Finset.prod_congr rfl fun ν hν => ?_
      have hne : ν ≠ μ := Finset.ne_of_mem_erase hν
      simp [hφ, Pi.single_eq_of_ne hne]
  have hd : DifferentiableAt ℝ (φ μ) (x μ + 0) :=
    ((contDiff_axisKernel hχ υ _).differentiable (by simp)) _
  have h1 : HasDerivAt (fun t : ℝ => φ μ (x μ + t) * B) (deriv (φ μ) (x μ + 0) * B) 0 :=
    (hd.hasDerivAt.comp_const_add (x μ) 0).mul_const B
  have h2 : HasDerivAt (fun t : ℝ => ((cubeKernel Γ υ (x + t • Pi.single μ 1) : ℝ) : ℂ))
      ((deriv (φ μ) (x μ + 0) * B : ℝ) : ℂ) 0 := by
    have h3 : HasDerivAt (fun t : ℝ => cubeKernel Γ υ (x + t • Pi.single μ 1))
        (deriv (φ μ) (x μ + 0) * B) 0 := by
      rw [hline]
      exact h1
    exact h3.ofReal_comp
  have he : partialDerivR4 μ (fun y => (cubeKernel Γ υ y : ℂ)) x =
      ((deriv (φ μ) (x μ + 0) * B : ℝ) : ℂ) := h2.deriv
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hBle : |B| ≤ ∏ ν ∈ Finset.univ.erase μ, axisKernelBound υ (decide (ν ∈ Γ)) := by
    rw [hB, Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun ν _ => abs_axisKernel_le hχ hυ _ _
  have hAle := abs_deriv_axisKernel_le hχ hυ (decide (μ ∈ Γ)) (x μ + 0)
  have hnn : 0 ≤ axisKernelBound υ (decide (μ ∈ Γ)) * υ⁻¹ :=
    mul_nonneg (axisKernelBound_nonneg hχ hυ _) (inv_pos.2 hυ).le
  calc |deriv (φ μ) (x μ + 0)| * |B|
      ≤ (axisKernelBound υ (decide (μ ∈ Γ)) * υ⁻¹) *
          ∏ ν ∈ Finset.univ.erase μ, axisKernelBound υ (decide (ν ∈ Γ)) :=
        mul_le_mul hAle hBle (abs_nonneg _) hnn
    _ = cubeKernelBound Γ υ * υ⁻¹ := by
        rw [cubeKernelBound, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ)]
        ring
omit hχ in
theorem cubeKernelBound_mul_inv {υ : ℝ} (hυ : 0 < υ) (Γ : Finset (Fin 4)) :
    cubeKernelBound Γ υ * υ⁻¹ = boundConst ^ 4 * υ ^ (3 * (Γ.card : ℤ) - 5) := by
  have hprod : cubeKernelBound Γ υ =
      (υ ^ 2 * boundConst) ^ Γ.card * (υ⁻¹ * boundConst) ^ (4 - Γ.card) := by
    rw [cubeKernelBound, ← Finset.prod_mul_prod_compl Γ]
    congr 1
    · rw [Finset.prod_congr rfl (g := fun _ => υ ^ 2 * boundConst) fun μ hμ => by
        simp [axisKernelBound, hμ]]
      simp
    · rw [Finset.prod_congr rfl (g := fun _ => υ⁻¹ * boundConst) fun μ hμ => by
        simp [axisKernelBound, Finset.mem_compl.1 hμ]]
      simp [Finset.card_compl]
  have hc : Γ.card ≤ 4 := by simpa using Finset.card_le_univ Γ
  rw [hprod]
  generalize Γ.card = c at hc
  have hne : υ ≠ 0 := hυ.ne'
  interval_cases c <;> norm_num [zpow_neg] <;> field_simp
theorem kernelNormBound : KernelNormBound := by
  intro Γ υ hυ hυ1
  set A : ℝ := cubeKernelBound Γ υ with hA
  have hA0 : 0 ≤ A := Finset.prod_nonneg fun μ _ => axisKernelBound_nonneg hχ hυ _
  have hi : 1 ≤ υ⁻¹ := (one_le_inv₀ hυ).2 hυ1
  have hsup : uniformNorm (fun x => (cubeKernel Γ υ x : ℂ)) ≤ A := by
    refine ciSup_le fun x => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_cubeKernel_le hχ hυ Γ x
  have hgrad : (⨆ x, Real.sqrt (∑ μ, ‖partialDerivR4 μ (fun x => (cubeKernel Γ υ x : ℂ)) x‖ ^ 2)) ≤
      2 * (A * υ⁻¹) := by
    refine ciSup_le fun x => ?_
    have hAi : 0 ≤ A * υ⁻¹ := mul_nonneg hA0 (inv_pos.2 hυ).le
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc ∑ μ, ‖partialDerivR4 μ (fun x => (cubeKernel Γ υ x : ℂ)) x‖ ^ 2
        ≤ ∑ _μ : Fin 4, (A * υ⁻¹) ^ 2 :=
          Finset.sum_le_sum fun μ _ =>
            pow_le_pow_left₀ (norm_nonneg _) (norm_partialDerivR4_cubeKernel_le hχ hυ Γ μ x) 2
      _ = (2 * (A * υ⁻¹)) ^ 2 := by
          simp
          ring
  have hconst : cubeKernelConst = 5 * boundConst ^ 4 := rfl
  rw [hconst, mul_assoc, ← cubeKernelBound_mul_inv hυ Γ, ← hA]
  have hAi : A ≤ A * υ⁻¹ := le_mul_of_one_le_right hA0 hi
  calc WightmanReconstruction.supC1Norm (fun x => (cubeKernel Γ υ x : ℂ))
      ≤ A + 2 * (A * υ⁻¹) := add_le_add hsup hgrad
    _ ≤ 5 * (A * υ⁻¹) := by linarith
end Bound
theorem kernelFacts_of_toolkit (hT : WightmanReconstruction.SmoothToolkit.Toolkit) :
    KernelFacts := by
  have hχ := isPlateauBump_plateauBump hT
  exact ⟨hχ, supportsInCube hχ, reproducingIdentity hχ, kernelNormBound hχ⟩
end YangMills.Construction.CubeKernels
