import YangMills.Construction.ColdChainAtEveryLevel.ReferenceAndCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def pureComponent (q : ℍ[ℝ]) : ℍ[ℝ] := (1 / 2 : ℝ) • (q - star q)
def pureComponentHom : ℍ[ℝ] →+ ℍ[ℝ] := AddMonoidHom.mk' pureComponent (fun a b => by
  simp only [pureComponent, star_add, ← smul_add]
  congr 1
  abel)
theorem pureComponentHom_apply (q : ℍ[ℝ]) : pureComponentHom q = pureComponent q := rfl
theorem norm_pureComponent_le (q : ℍ[ℝ]) : ‖pureComponent q‖ ≤ ‖q‖ := by
  unfold pureComponent
  rw [norm_smul]
  have h := norm_sub_le q (star q)
  rw [norm_star] at h
  norm_num
  linarith
theorem pureComponent_add (a b : ℍ[ℝ]) :
    pureComponent (a + b) = pureComponent a + pureComponent b := pureComponentHom.map_add a b
theorem pureComponent_sub (a b : ℍ[ℝ]) :
    pureComponent (a - b) = pureComponent a - pureComponent b := pureComponentHom.map_sub a b
theorem pureComponent_coe (r : ℝ) : pureComponent (r : ℍ[ℝ]) = 0 := by
  simp [pureComponent]
theorem pureComponent_one : pureComponent (1 : ℍ[ℝ]) = 0 := by
  simp [pureComponent]
theorem quaternion_star_real_smul (r : ℝ) (q : ℍ[ℝ]) : star (r • q) = r • star q := by
  ext <;> simp
theorem pureComponent_smul (r : ℝ) (q : ℍ[ℝ]) : pureComponent (r • q) = r • pureComponent q := by
  simp only [pureComponent, quaternion_star_real_smul, smul_sub, smul_comm r]
theorem pureComponent_eq_zero {q : ℍ[ℝ]} (h : star q = q) : pureComponent q = 0 := by
  simp [pureComponent, h]
theorem pureComponent_star (q : ℍ[ℝ]) : pureComponent (star q) = - pureComponent q := by
  simp only [pureComponent, star_star, ← smul_neg, neg_sub]
theorem pureComponent_sum {ι : Type} (s : Finset ι) (f : ι → ℍ[ℝ]) :
    pureComponent (∑ i ∈ s, f i) = ∑ i ∈ s, pureComponent (f i) := map_sum pureComponentHom f s
theorem re_add_pureComponent (q : ℍ[ℝ]) : (q.re : ℍ[ℝ]) + pureComponent q = q := by
  ext <;> simp [pureComponent] <;> ring
theorem eq_coe_re_of_star_eq {q : ℍ[ℝ]} (h : star q = q) : q = (q.re : ℍ[ℝ]) := by
  have := re_add_pureComponent q
  rw [pureComponent_eq_zero h, add_zero] at this
  exact this.symm
theorem quaternion_re_le_norm (q : ℍ[ℝ]) : q.re ≤ ‖q‖ := by
  have h1 : ‖q + star q‖ ≤ 2 * ‖q‖ := by
    have := norm_add_le q (star q)
    rw [norm_star] at this
    linarith
  have h2 : q + star q = ((2 * q.re : ℝ) : ℍ[ℝ]) := by
    ext <;> simp <;> ring
  rw [h2, Quaternion.norm_coe, Real.norm_eq_abs] at h1
  have := le_abs_self (2 * q.re)
  linarith
theorem norm_le_re_add_norm_pureComponent (q : ℍ[ℝ]) (h : 0 ≤ q.re) :
    ‖q‖ ≤ q.re + ‖pureComponent q‖ := by
  conv_lhs => rw [← re_add_pureComponent q]
  refine (norm_add_le _ _).trans ?_
  rw [Quaternion.norm_coe, Real.norm_eq_abs, abs_of_nonneg h]
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by
  have h1 : star (g : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := Unitary.star_mul_self_of_mem g.2
  rw [Quaternion.star_mul_self] at h1
  have h2 : Quaternion.normSq (g : ℍ[ℝ]) = 1 := by
    simpa using congrArg (fun q : ℍ[ℝ] => q.re) h1
  rw [Quaternion.normSq_eq_norm_mul_self] at h2
  nlinarith [norm_nonneg (g : ℍ[ℝ])]
theorem coe_unitQuaternion_ne_zero (g : UnitQuaternion) : (g : ℍ[ℝ]) ≠ 0 := by
  intro h
  have := norm_coe_unitQuaternion g
  rw [h, norm_zero] at this
  exact zero_ne_one this
theorem coe_polarUnit {q : ℍ[ℝ]} (h : q ≠ 0) :
    ((polarUnit q : UnitQuaternion) : ℍ[ℝ]) = ‖q‖⁻¹ • q := by
  simp [polarUnit, h]
theorem coe_unitQuaternion_inv (g : UnitQuaternion) :
    ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
theorem polarUnit_mul {a b : ℍ[ℝ]} (ha : a ≠ 0) (hb : b ≠ 0) :
    polarUnit (a * b) = polarUnit a * polarUnit b := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, coe_polarUnit (mul_ne_zero ha hb), coe_polarUnit ha, coe_polarUnit hb]
  rw [norm_mul, mul_inv, smul_mul_smul_comm]
theorem polarUnit_star (a : ℍ[ℝ]) : polarUnit (star a) = (polarUnit a)⁻¹ := by
  by_cases ha : a = 0
  · subst ha
    simp [polarUnit]
  · apply Subtype.ext
    have hs : star a ≠ 0 := star_ne_zero.2 ha
    rw [coe_polarUnit hs, coe_unitQuaternion_inv, coe_polarUnit ha, quaternion_star_real_smul,
      norm_star]
theorem polarUnit_coe {r : ℝ} (h : 0 < r) : polarUnit (r : ℍ[ℝ]) = 1 := by
  apply Subtype.ext
  have hn : (r : ℍ[ℝ]) ≠ 0 := fun h0 => h.ne' (by simpa using congrArg (fun q : ℍ[ℝ] => q.re) h0)
  rw [coe_polarUnit hn, Quaternion.norm_coe, Real.norm_eq_abs, abs_of_pos h]
  ext <;> simp [h.ne']
theorem pureComponent_polarUnit {q : ℍ[ℝ]} (h : q ≠ 0) :
    pureComponent ((polarUnit q : UnitQuaternion) : ℍ[ℝ]) = ‖q‖⁻¹ • pureComponent q := by
  rw [coe_polarUnit h, pureComponent_smul]
theorem norm_polarUnit_sub_one_le {q : ℍ[ℝ]} (h : 0 ≤ q.re) (h0 : q ≠ 0) :
    ‖((polarUnit q : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * ‖pureComponent q‖ / ‖q‖ := by
  have hn : 0 < ‖q‖ := norm_pos_iff.2 h0
  rw [coe_polarUnit h0]
  have e1 : ‖q‖⁻¹ • q - 1 = ‖q‖⁻¹ • (q - (‖q‖ : ℍ[ℝ])) := by
    rw [smul_sub]
    congr 1
    ext <;> simp [hn.ne']
  rw [e1, norm_smul, norm_inv, norm_norm]
  have e2 : q - (‖q‖ : ℍ[ℝ]) = ((q.re - ‖q‖ : ℝ) : ℍ[ℝ]) + pureComponent q := by
    have h1 : q - (‖q‖ : ℍ[ℝ]) = ((q.re : ℍ[ℝ]) + pureComponent q) - (‖q‖ : ℍ[ℝ]) := by
      rw [re_add_pureComponent]
    rw [h1]
    simp only [Quaternion.coe_sub]
    abel
  have e3 : ‖q - (‖q‖ : ℍ[ℝ])‖ ≤ 2 * ‖pureComponent q‖ := by
    rw [e2]
    refine (norm_add_le _ _).trans ?_
    rw [Quaternion.norm_coe, Real.norm_eq_abs,
      abs_of_nonpos (by linarith [quaternion_re_le_norm q])]
    have := norm_le_re_add_norm_pureComponent q h
    linarith
  rw [div_eq_inv_mul]
  calc ‖q‖⁻¹ * ‖q - (‖q‖ : ℍ[ℝ])‖ ≤ ‖q‖⁻¹ * (2 * ‖pureComponent q‖) :=
        mul_le_mul_of_nonneg_left e3 (inv_nonneg.2 hn.le)
    _ = _ := by ring
theorem norm_coe_mul_sub_one_le (a b : UnitQuaternion) :
    ‖((a * b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(a : ℍ[ℝ]) - 1‖ + ‖(b : ℍ[ℝ]) - 1‖ := by
  have e : ((a * b : UnitQuaternion) : ℍ[ℝ]) - 1 =
      (a : ℍ[ℝ]) * ((b : ℍ[ℝ]) - 1) + ((a : ℍ[ℝ]) - 1) := by
    rw [Submonoid.coe_mul, mul_sub, mul_one]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_coe_unitQuaternion, one_mul]
  linarith
theorem norm_coe_conj_sub_one (a b : UnitQuaternion) :
    ‖((a * b * a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(b : ℍ[ℝ]) - 1‖ := by
  have e : ((a * b * a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 =
      (a : ℍ[ℝ]) * ((b : ℍ[ℝ]) - 1) * ((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    have h1 : (a : ℍ[ℝ]) * ((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
      rw [← Submonoid.coe_mul, mul_inv_cancel]
      rfl
    simp only [Submonoid.coe_mul, mul_sub, sub_mul, mul_one, h1]
  rw [e, norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion]
  ring
theorem norm_coe_inv_sub_one (a : UnitQuaternion) :
    ‖((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(a : ℍ[ℝ]) - 1‖ := by
  rw [coe_unitQuaternion_inv]
  have : star (a : ℍ[ℝ]) - 1 = star ((a : ℍ[ℝ]) - 1) := by simp
  rw [this, norm_star]
end YangMills.Construction.BlockAverages
end
