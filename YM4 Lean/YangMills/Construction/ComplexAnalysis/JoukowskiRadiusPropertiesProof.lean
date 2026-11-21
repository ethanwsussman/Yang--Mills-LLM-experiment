import YangMills.Construction.ComplexAnalysis.JoukowskiRadiusProperties
import YangMills.Construction.RealFunctions.AddInvStatement
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.JoukowskiRadius
open Ellipses
theorem joukowskiRadius_isJoukowskiRadius (h : RealFunctions.AddInvStatement) (z : ℂ) :
    IsJoukowskiRadius z (joukowskiRadius z) := by
  obtain ⟨r, hr, -⟩ := h.2.2 z
  exact Classical.epsilon_spec (p := IsJoukowskiRadius z) ⟨r, hr⟩
theorem one_le_joukowskiRadius (h : RealFunctions.AddInvStatement) (z : ℂ) :
    1 ≤ joukowskiRadius z :=
  (joukowskiRadius_isJoukowskiRadius h z).1
theorem joukowskiRadius_add_inv (h : RealFunctions.AddInvStatement) (z : ℂ) :
    joukowskiRadius z + (joukowskiRadius z)⁻¹ = ‖z + 1‖ + ‖z - 1‖ :=
  (joukowskiRadius_isJoukowskiRadius h z).2
theorem joukowskiRadius_eq_of_add_inv (h : RealFunctions.AddInvStatement) (z : ℂ) (r : ℝ)
    (hr : 1 ≤ r) (he : r + r⁻¹ = ‖z + 1‖ + ‖z - 1‖) : joukowskiRadius z = r :=
  (h.2.2 z).unique ⟨one_le_joukowskiRadius h z, joukowskiRadius_add_inv h z⟩ ⟨hr, he⟩
theorem add_inv_lt_add_inv (h : RealFunctions.AddInvStatement) {r s : ℝ} (hr : 1 ≤ r)
    (hs : 1 ≤ s) (hrs : r < s) : r + r⁻¹ < s + s⁻¹ := by
  obtain ⟨⟨e, he, hm⟩, -⟩ := h.1
  have h1 := hm (show (⟨r, hr⟩ : Set.Ici (1 : ℝ)) < ⟨s, hs⟩ from hrs)
  have h2 : ((e ⟨r, hr⟩ : Set.Ici (2 : ℝ)) : ℝ) < (e ⟨s, hs⟩ : Set.Ici (2 : ℝ)) := h1
  rwa [he, he] at h2
theorem joukowskiRadius_le_of_le (h : RealFunctions.AddInvStatement) {z w : ℂ}
    (hzw : ‖z + 1‖ + ‖z - 1‖ ≤ ‖w + 1‖ + ‖w - 1‖) : joukowskiRadius z ≤ joukowskiRadius w := by
  by_contra hc
  rw [not_le] at hc
  have h1 := add_inv_lt_add_inv h (one_le_joukowskiRadius h w) (one_le_joukowskiRadius h z) hc
  rw [joukowskiRadius_add_inv h, joukowskiRadius_add_inv h] at h1
  linarith
theorem continuous_joukowskiRadius (h : RealFunctions.AddInvStatement) :
    Continuous joukowskiRadius := by
  obtain ⟨⟨e, he, -⟩, -⟩ := h.1
  have hS : ∀ z : ℂ, (2 : ℝ) ≤ ‖z + 1‖ + ‖z - 1‖ := fun z => (h.2.1 z).1
  have hc : Continuous
      (fun z : ℂ => ((e.symm ⟨‖z + 1‖ + ‖z - 1‖, hS z⟩ : Set.Ici (1 : ℝ)) : ℝ)) := by
    refine continuous_subtype_val.comp (e.symm.continuous.comp ?_)
    exact Continuous.subtype_mk (by fun_prop) _
  have hq : joukowskiRadius =
      fun z : ℂ => ((e.symm ⟨‖z + 1‖ + ‖z - 1‖, hS z⟩ : Set.Ici (1 : ℝ)) : ℝ) := by
    funext z
    refine joukowskiRadius_eq_of_add_inv h z _ (e.symm _).2 ?_
    rw [← he, e.apply_symm_apply]
  rw [hq]
  exact hc
theorem joukowskiRadius_eq_one_iff (h : RealFunctions.AddInvStatement) (z : ℂ) :
    joukowskiRadius z = 1 ↔ z ∈ unitSegment := by
  unfold unitSegment
  rw [← (h.2.1 z).2]
  constructor
  · intro h1
    have h2 := joukowskiRadius_add_inv h z
    rw [h1] at h2
    norm_num at h2
    linarith
  · intro h2
    exact joukowskiRadius_eq_of_add_inv h z 1 le_rfl (by rw [h2]; norm_num)
theorem norm_half_add_inv_add_one_add_norm_sub_one (ω : ℂ) (hω : ω ≠ 0) :
    ‖(1 / 2 : ℂ) * (ω + ω⁻¹) + 1‖ + ‖(1 / 2 : ℂ) * (ω + ω⁻¹) - 1‖ = ‖ω‖ + ‖ω‖⁻¹ := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq ω (n := 2) (by norm_num)
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hω
    rw [← hu]
    simp
  have e1 : (1 / 2 : ℂ) * (ω + ω⁻¹) + 1 = (1 / 2 : ℂ) * (u + u⁻¹) ^ 2 := by
    rw [← hu]
    field_simp
    ring
  have e2 : (1 / 2 : ℂ) * (ω + ω⁻¹) - 1 = (1 / 2 : ℂ) * (u - u⁻¹) ^ 2 := by
    rw [← hu]
    field_simp
    ring
  have hp := parallelogram_law_with_norm ℝ u u⁻¹
  have n2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hn : ‖ω‖ = ‖u‖ ^ 2 := by rw [← hu, norm_pow]
  rw [e1, e2, norm_mul, norm_mul, norm_pow, norm_pow, n2, hn]
  rw [norm_inv] at hp
  rw [← inv_pow]
  linarith [hp]
theorem joukowskiRadius_half_add_inv (h : RealFunctions.AddInvStatement) (ω : ℂ) (hω : ω ≠ 0) :
    joukowskiRadius ((1 / 2 : ℂ) * (ω + ω⁻¹)) = max ‖ω‖ ‖ω‖⁻¹ := by
  have hp : 0 < ‖ω‖ := norm_pos_iff.mpr hω
  refine joukowskiRadius_eq_of_add_inv h _ _ ?_ ?_
  · rcases le_total 1 ‖ω‖ with h1 | h1
    · exact h1.trans (le_max_left _ _)
    · exact ((one_le_inv₀ hp).mpr h1).trans (le_max_right _ _)
  · rw [norm_half_add_inv_add_one_add_norm_sub_one ω hω]
    rcases le_total ‖ω‖ ‖ω‖⁻¹ with h1 | h1
    · rw [max_eq_right h1, inv_inv, add_comm]
    · rw [max_eq_left h1]
theorem exists_eq_half_add_inv (h : RealFunctions.AddInvStatement) (z : ℂ) :
    ∃ ω : ℂ, z = (1 / 2 : ℂ) * (ω + ω⁻¹) ∧ ‖ω‖ = joukowskiRadius z := by
  obtain ⟨ω₁, h0, hz⟩ : ∃ ω₁ : ℂ, ω₁ ≠ 0 ∧ z = (1 / 2 : ℂ) * (ω₁ + ω₁⁻¹) := by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z ^ 2 - 1) (n := 2) (by norm_num)
    have hq : (z + w) ^ 2 - 2 * z * (z + w) + 1 = 0 := by linear_combination hw
    have h0 : z + w ≠ 0 := by
      intro h0
      rw [h0] at hq
      norm_num at hq
    refine ⟨z + w, h0, ?_⟩
    field_simp
    linear_combination -hq
  subst hz
  have hp : 0 < ‖ω₁‖ := norm_pos_iff.mpr h0
  rcases le_total 1 ‖ω₁‖ with h1 | h1
  · refine ⟨ω₁, rfl, ?_⟩
    rw [joukowskiRadius_half_add_inv h ω₁ h0, max_eq_left ((inv_le_one_of_one_le₀ h1).trans h1)]
  · refine ⟨ω₁⁻¹, by rw [inv_inv, add_comm], ?_⟩
    rw [joukowskiRadius_half_add_inv h ω₁ h0, norm_inv,
      max_eq_right (h1.trans ((one_le_inv₀ hp).mpr h1))]
theorem abs_re_le_and_abs_im_le_half_add_inv (ω : ℂ) (hω : 1 ≤ ‖ω‖) :
    |((1 / 2 : ℂ) * (ω + ω⁻¹)).re| ≤ (1 / 2 : ℝ) * (‖ω‖ + ‖ω‖⁻¹) ∧
      |((1 / 2 : ℂ) * (ω + ω⁻¹)).im| ≤ (1 / 2 : ℝ) * (‖ω‖ - ‖ω‖⁻¹) := by
  have hp : 0 < ‖ω‖ := by linarith
  have hs : Complex.normSq ω = ‖ω‖ ^ 2 := Complex.normSq_eq_norm_sq ω
  have hi : ‖ω‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hω
  have hi0 : 0 < ‖ω‖⁻¹ := inv_pos.mpr hp
  have hq : (‖ω‖⁻¹) ^ 2 ≤ 1 := by nlinarith
  have hmul : ‖ω‖ * ‖ω‖⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  have hre : ((1 / 2 : ℂ) * (ω + ω⁻¹)).re = (1 / 2 : ℝ) * (ω.re * (1 + (‖ω‖⁻¹) ^ 2)) := by
    simp [Complex.inv_re, hs]
    field_simp
  have him : ((1 / 2 : ℂ) * (ω + ω⁻¹)).im = (1 / 2 : ℝ) * (ω.im * (1 - (‖ω‖⁻¹) ^ 2)) := by
    simp [Complex.inv_im, hs]
    field_simp
    ring
  have ha : |ω.re| ≤ ‖ω‖ := Complex.abs_re_le_norm ω
  have hb : |ω.im| ≤ ‖ω‖ := Complex.abs_im_le_norm ω
  constructor
  · rw [hre, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + (‖ω‖⁻¹) ^ 2)]
    have : |ω.re| * (1 + (‖ω‖⁻¹) ^ 2) ≤ ‖ω‖ * (1 + (‖ω‖⁻¹) ^ 2) :=
      mul_le_mul_of_nonneg_right ha (by positivity)
    nlinarith
  · rw [him, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - (‖ω‖⁻¹) ^ 2)]
    have : |ω.im| * (1 - (‖ω‖⁻¹) ^ 2) ≤ ‖ω‖ * (1 - (‖ω‖⁻¹) ^ 2) :=
      mul_le_mul_of_nonneg_right hb (by linarith)
    nlinarith
theorem abs_re_lt_and_abs_im_lt_of_mem_focalEllipse (h : RealFunctions.AddInvStatement) (ς : ℝ)
    (hς : 1 < ς) (z : ℂ) (hz : z ∈ focalEllipse ς hς) :
    |z.re| < (1 / 2 : ℝ) * (ς + ς⁻¹) ∧ |z.im| < (1 / 2 : ℝ) * (ς - ς⁻¹) := by
  have hlt : joukowskiRadius z < ς := hz
  have h1 := one_le_joukowskiRadius h z
  obtain ⟨ω, hzω, hn⟩ := exists_eq_half_add_inv h z
  have hb := abs_re_le_and_abs_im_le_half_add_inv ω (by rw [hn]; exact h1)
  rw [← hzω, hn] at hb
  have s1 := add_inv_lt_add_inv h h1 hς.le hlt
  have s2 : joukowskiRadius z - (joukowskiRadius z)⁻¹ < ς - ς⁻¹ :=
    h.1.2 (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr hς.le) hlt
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
theorem norm_ofReal_add_I_mul_ofReal_sq (a b : ℝ) :
    ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring
theorem joukowskiRadius_I_mul (h : RealFunctions.AddInvStatement) (y τ : ℝ) (hτ : 0 ≤ τ)
    (hs : Real.sinh τ = |y|) : joukowskiRadius (Complex.I * (y : ℂ)) = Real.exp τ := by
  refine joukowskiRadius_eq_of_add_inv h _ _ (Real.one_le_exp hτ) ?_
  have hc : Real.cosh τ ^ 2 = 1 + y ^ 2 := by
    rw [Real.cosh_sq, hs, sq_abs]
    ring
  have n1 : ‖Complex.I * (y : ℂ) + 1‖ = Real.cosh τ := by
    have e : Complex.I * (y : ℂ) + 1 = ((1 : ℝ) : ℂ) + Complex.I * (y : ℂ) := by
      push_cast
      ring
    have h2 := norm_ofReal_add_I_mul_ofReal_sq 1 y
    rw [← e] at h2
    exact (sq_eq_sq₀ (norm_nonneg _) (Real.cosh_pos τ).le).mp (by rw [h2, hc]; ring)
  have n2 : ‖Complex.I * (y : ℂ) - 1‖ = Real.cosh τ := by
    have e : Complex.I * (y : ℂ) - 1 = ((-1 : ℝ) : ℂ) + Complex.I * (y : ℂ) := by
      push_cast
      ring
    have h2 := norm_ofReal_add_I_mul_ofReal_sq (-1) y
    rw [← e] at h2
    exact (sq_eq_sq₀ (norm_nonneg _) (Real.cosh_pos τ).le).mp (by rw [h2, hc]; ring)
  rw [n1, n2, Real.cosh_eq, Real.exp_neg]
  ring
theorem joukowskiRadius_le_of_abs_im_le (h : RealFunctions.AddInvStatement) (x y y' : ℝ)
    (hy : |y| ≤ |y'|) :
    joukowskiRadius ((x : ℂ) + Complex.I * (y : ℂ)) ≤
      joukowskiRadius ((x : ℂ) + Complex.I * (y' : ℂ)) := by
  have hsq : y ^ 2 ≤ y' ^ 2 := sq_le_sq.mpr hy
  have key : ∀ a : ℝ, ‖(a : ℂ) + Complex.I * (y : ℂ)‖ ≤ ‖(a : ℂ) + Complex.I * (y' : ℂ)‖ := by
    intro a
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    rw [norm_ofReal_add_I_mul_ofReal_sq, norm_ofReal_add_I_mul_ofReal_sq]
    linarith
  have e1 : ∀ t : ℝ, (x : ℂ) + Complex.I * (t : ℂ) + 1 =
      ((x + 1 : ℝ) : ℂ) + Complex.I * (t : ℂ) := by
    intro t
    push_cast
    ring
  have e2 : ∀ t : ℝ, (x : ℂ) + Complex.I * (t : ℂ) - 1 =
      ((x - 1 : ℝ) : ℂ) + Complex.I * (t : ℂ) := by
    intro t
    push_cast
    ring
  apply joukowskiRadius_le_of_le h
  rw [e1, e1, e2, e2]
  exact add_le_add (key _) (key _)
theorem joukowskiRadius_ofReal_le_of_abs_le (h : RealFunctions.AddInvStatement) (x x' : ℝ)
    (hx : |x| ≤ |x'|) : joukowskiRadius (x : ℂ) ≤ joukowskiRadius (x' : ℂ) := by
  have e : ∀ t : ℝ, ‖(t : ℂ) + 1‖ + ‖(t : ℂ) - 1‖ = |t + 1| + |t - 1| := by
    intro t
    have e1 : (t : ℂ) + 1 = ((t + 1 : ℝ) : ℂ) := by push_cast; ring
    have e2 : (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  apply joukowskiRadius_le_of_le h
  rw [e, e]
  rcases abs_cases x with ⟨a1, _⟩ | ⟨a1, _⟩ <;> rcases abs_cases x' with ⟨a2, _⟩ | ⟨a2, _⟩ <;>
    rcases abs_cases (x + 1) with ⟨a3, _⟩ | ⟨a3, _⟩ <;>
    rcases abs_cases (x - 1) with ⟨a4, _⟩ | ⟨a4, _⟩ <;>
    rcases abs_cases (x' + 1) with ⟨a5, _⟩ | ⟨a5, _⟩ <;>
    rcases abs_cases (x' - 1) with ⟨a6, _⟩ | ⟨a6, _⟩ <;>
    linarith
theorem joukowskiRadiusProperties (h : RealFunctions.AddInvStatement) :
    JoukowskiRadiusProperties := by
  have hc := continuous_joukowskiRadius h
  refine ⟨one_le_joukowskiRadius h, hc, joukowskiRadius_eq_one_iff h, ?_, ?_,
    joukowskiRadius_half_add_inv h, exists_eq_half_add_inv h, ?_, ?_, joukowskiRadius_I_mul h,
    joukowskiRadius_le_of_abs_im_le h, joukowskiRadius_ofReal_le_of_abs_le h⟩
  · intro ς hς
    exact isOpen_lt hc continuous_const
  · intro ς hς n hn
    constructor
    · exact isOpen_lt (continuous_finsetProd _ fun j _ => hc.comp (continuous_apply j))
        continuous_const
    · intro z hz
      have h1 : ∀ j : Fin n, joukowskiRadius (z j) = 1 := fun j =>
        (joukowskiRadius_eq_one_iff h (z j)).mpr (hz j)
      show ∏ j : Fin n, joukowskiRadius (z j) < ς
      simpa [h1] using hς
  · intro ς hς z hz
    exact abs_re_lt_and_abs_im_lt_of_mem_focalEllipse h ς hς z hz
  · intro y
    refine ⟨Real.arsinh |y|, ⟨Real.arsinh_nonneg_iff.mpr (abs_nonneg y), Real.sinh_arsinh _⟩, ?_⟩
    rintro τ ⟨-, hs⟩
    exact Real.sinh_injective (by rw [hs, Real.sinh_arsinh])
end YangMills.Construction.JoukowskiRadius
