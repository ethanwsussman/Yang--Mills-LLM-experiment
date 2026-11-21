import YangMills.Construction.RealFunctions.AddInvStatement
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RealFunctions.AddInv
theorem add_inv_lt_add_inv {x y : ℝ} (hx1 : 1 ≤ x) (hxy : x < y) : x + x⁻¹ < y + y⁻¹ := by
  have hy : 0 < y := by linarith
  have key : (y + y⁻¹) - (x + x⁻¹) = (y - x) * (1 - (x * y)⁻¹) := by
    field_simp
    ring
  have hlt : (x * y)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have hpos : 0 < (y - x) * (1 - (x * y)⁻¹) := mul_pos (by linarith) (by linarith)
  linarith
theorem sub_inv_lt_sub_inv {x y : ℝ} (hx1 : 1 ≤ x) (hxy : x < y) : x - x⁻¹ < y - y⁻¹ := by
  have hx : 0 < x := by linarith
  have hy : 0 < y := by linarith
  have key : (y - y⁻¹) - (x - x⁻¹) = (y - x) * (1 + (x * y)⁻¹) := by
    field_simp
    ring
  have hinv : 0 < (x * y)⁻¹ := inv_pos.mpr (mul_pos hx hy)
  have hpos : 0 < (y - x) * (1 + (x * y)⁻¹) := mul_pos (by linarith) (by linarith)
  linarith
theorem two_le_add_inv {x : ℝ} (hx1 : 1 ≤ x) : 2 ≤ x + x⁻¹ := by
  rcases eq_or_lt_of_le hx1 with h | h
  · subst h
    norm_num
  · have := add_inv_lt_add_inv (le_refl (1 : ℝ)) h
    rw [inv_one] at this
    linarith
theorem eq_of_add_inv_eq {x y : ℝ} (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (h : x + x⁻¹ = y + y⁻¹) :
    x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (ne_of_lt (add_inv_lt_add_inv hx1 hlt))
  · exact heq
  · exact absurd h.symm (ne_of_lt (add_inv_lt_add_inv hy1 hgt))
def addInvInverse (s : ℝ) : ℝ := (s + Real.sqrt (s ^ 2 - 4)) / 2
theorem one_le_addInvInverse {s : ℝ} (hs : 2 ≤ s) : 1 ≤ addInvInverse s := by
  have := Real.sqrt_nonneg (s ^ 2 - 4)
  unfold addInvInverse
  linarith
theorem addInvInverse_add_inv {s : ℝ} (hs : 2 ≤ s) :
    addInvInverse s + (addInvInverse s)⁻¹ = s := by
  have hsq : Real.sqrt (s ^ 2 - 4) ^ 2 = s ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  have hprod : addInvInverse s * ((s - Real.sqrt (s ^ 2 - 4)) / 2) = 1 := by
    unfold addInvInverse
    linear_combination (-1 / 4) * hsq
  rw [inv_eq_of_mul_eq_one_right hprod]
  unfold addInvInverse
  ring
def addInvHomeomorph : Set.Ici (1 : ℝ) ≃ₜ Set.Ici (2 : ℝ) where
  toFun x := ⟨(x : ℝ) + (x : ℝ)⁻¹, two_le_add_inv x.2⟩
  invFun s := ⟨addInvInverse s, one_le_addInvInverse s.2⟩
  left_inv x := by
    have h1 : (1 : ℝ) ≤ x := x.2
    have h2 : (2 : ℝ) ≤ (x : ℝ) + (x : ℝ)⁻¹ := two_le_add_inv h1
    apply Subtype.ext
    exact eq_of_add_inv_eq (one_le_addInvInverse h2) h1 (addInvInverse_add_inv h2)
  right_inv s := by
    apply Subtype.ext
    exact addInvInverse_add_inv s.2
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_subtype_val.add (continuous_subtype_val.inv₀ ?_)
    intro x
    have h1 : (1 : ℝ) ≤ x := x.2
    have h0 : (0 : ℝ) < x := by linarith
    exact h0.ne'
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    unfold addInvInverse
    fun_prop
theorem re_le_norm_add_one_and_sub_one (z : ℂ) : 1 + z.re ≤ ‖z + 1‖ ∧ 1 - z.re ≤ ‖z - 1‖ := by
  have h1 := Complex.abs_re_le_norm (z + 1)
  have h2 := Complex.abs_re_le_norm (z - 1)
  rw [Complex.add_re, Complex.one_re] at h1
  rw [Complex.sub_re, Complex.one_re] at h2
  have h3 := le_abs_self (z.re + 1)
  have h4 := neg_le_abs (z.re - 1)
  constructor <;> linarith
theorem mem_image_Icc_of_norm_add_norm_eq_two {z : ℂ} (h : ‖z + 1‖ + ‖z - 1‖ = 2) :
    z ∈ (fun x : ℝ => (x : ℂ)) '' Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := re_le_norm_add_one_and_sub_one z
  have e1 : ‖z + 1‖ = 1 + z.re := by linarith
  have e2 : ‖z - 1‖ = 1 - z.re := by linarith
  have hn1 : 0 ≤ 1 + z.re := e1 ▸ norm_nonneg _
  have hn2 : 0 ≤ 1 - z.re := e2 ▸ norm_nonneg _
  have hsq : ‖z + 1‖ ^ 2 = (z + 1).re * (z + 1).re + (z + 1).im * (z + 1).im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  rw [e1, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im] at hsq
  have him : z.im = 0 := by
    have : z.im * z.im = 0 := by nlinarith
    exact mul_self_eq_zero.mp this
  refine ⟨z.re, ⟨by linarith, by linarith⟩, ?_⟩
  apply Complex.ext
  · simp
  · simp [him]
theorem norm_add_norm_eq_two_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(x : ℂ) + 1‖ + ‖(x : ℂ) - 1‖ = 2 := by
  obtain ⟨hx1, hx2⟩ := hx
  have e1 : (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  ring
theorem two_le_norm_add_norm (z : ℂ) : 2 ≤ ‖z + 1‖ + ‖z - 1‖ := by
  obtain ⟨h1, h2⟩ := re_le_norm_add_one_and_sub_one z
  linarith
theorem addInvStatement_holds : YangMills.Construction.RealFunctions.AddInvStatement := by
  refine ⟨⟨⟨addInvHomeomorph, fun x => rfl, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro a b hab
    have hab' : (a : ℝ) < (b : ℝ) := hab
    exact Subtype.coe_lt_coe.mp (add_inv_lt_add_inv a.2 hab')
  · intro a ha b _ hab
    exact sub_inv_lt_sub_inv ha hab
  · intro z
    refine ⟨two_le_norm_add_norm z, mem_image_Icc_of_norm_add_norm_eq_two, ?_⟩
    rintro ⟨x, hx, rfl⟩
    exact norm_add_norm_eq_two_of_mem_Icc hx
  · intro z
    have hs := two_le_norm_add_norm z
    refine ⟨addInvInverse (‖z + 1‖ + ‖z - 1‖),
      ⟨one_le_addInvInverse hs, addInvInverse_add_inv hs⟩, ?_⟩
    rintro x ⟨hx, he⟩
    exact eq_of_add_inv_eq hx (one_le_addInvInverse hs) (he.trans (addInvInverse_add_inv hs).symm)
end YangMills.Construction.RealFunctions.AddInv
