import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.ShortMovesOfAChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ChartLipschitz
private theorem sq_le_sq_imp_le {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : a ≤ b :=
  (abs_le_of_sq_le_sq' h hb).2
private theorem exp_dist_le (u v : ℍ[ℝ]) (hu : u.re = 0) (hv : v.re = 0) :
    ‖NormedSpace.exp u - NormedSpace.exp v‖ ≤ ‖u - v‖ := by
  set r := ‖u‖ with hr
  set s := ‖v‖ with hs
  have hr0 : 0 ≤ r := norm_nonneg _
  have hs0 : 0 ≤ s := norm_nonneg _
  have e1 : ∀ q : ℍ[ℝ], ‖q‖ ^ 2 = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 := by
    intro q
    have := Quaternion.normSq_eq_norm_mul_self q
    rw [Quaternion.normSq_def'] at this
    nlinarith
  have hru : r ^ 2 = u.imI ^ 2 + u.imJ ^ 2 + u.imK ^ 2 := by
    rw [hr, e1, hu]; ring
  have hsv : s ^ 2 = v.imI ^ 2 + v.imJ ^ 2 + v.imK ^ 2 := by
    rw [hs, e1, hv]; ring
  set A := Real.sin r / r with hA
  set B := Real.sin s / s with hB
  have hAr : A * r = Real.sin r := by
    by_cases h : r = 0
    · simp [h]
    · rw [hA]; field_simp
  have hBs : B * s = Real.sin s := by
    by_cases h : s = 0
    · simp [h]
    · rw [hB]; field_simp
  have hA1 : |A| ≤ 1 := by
    by_cases h : r = 0
    · simp [hA, h]
    · have hp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm h)
      rw [hA, abs_div, abs_of_pos hp, div_le_one hp]
      exact Real.abs_sin_le_abs.trans (le_of_eq (abs_of_pos hp))
  have hB1 : |B| ≤ 1 := by
    by_cases h : s = 0
    · simp [hB, h]
    · have hp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
      rw [hB, abs_div, abs_of_pos hp, div_le_one hp]
      exact Real.abs_sin_le_abs.trans (le_of_eq (abs_of_pos hp))
  have hAB : A * B ≤ 1 := by
    have h2 : |A * B| ≤ 1 := by
      rw [abs_mul]; exact mul_le_one₀ hA1 (abs_nonneg _) hB1
    exact (le_abs_self _).trans h2
  set t := u.imI * v.imI + u.imJ * v.imJ + u.imK * v.imK with ht
  have hcs : t ≤ r * s := by
    have h1 : t ^ 2 ≤ (r * s) ^ 2 := by
      rw [mul_pow, hru, hsv, ht]
      nlinarith [sq_nonneg (u.imI * v.imJ - u.imJ * v.imI), sq_nonneg (u.imI * v.imK - u.imK * v.imI),
        sq_nonneg (u.imJ * v.imK - u.imK * v.imJ)]
    exact sq_le_sq_imp_le h1 (mul_nonneg hr0 hs0)
  have hexpu := Quaternion.exp_of_re_eq_zero u hu
  have hexpv := Quaternion.exp_of_re_eq_zero v hv
  have key : ‖NormedSpace.exp u - NormedSpace.exp v‖ ^ 2 ≤ ‖u - v‖ ^ 2 := by
    rw [e1, e1, hexpu, hexpv]
    simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
      Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
      Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe, hu, hv,
      smul_eq_mul, mul_zero, add_zero, zero_add, sub_zero]
    have e : (A * u.imI - B * v.imI) ^ 2 + (A * u.imJ - B * v.imJ) ^ 2 + (A * u.imK - B * v.imK) ^ 2 =
        (A * r) ^ 2 + (B * s) ^ 2 - 2 * (A * B) * t := by
      rw [mul_pow, mul_pow, hru, hsv, ht]; ring
    have p1 : (A * r) ^ 2 + Real.cos r ^ 2 = 1 := by rw [hAr]; exact Real.sin_sq_add_cos_sq r
    have p2 : (B * s) ^ 2 + Real.cos s ^ 2 = 1 := by rw [hBs]; exact Real.sin_sq_add_cos_sq s
    have c1 := Real.one_sub_sq_div_two_le_cos (x := r - s)
    rw [Real.cos_sub, ← hAr, ← hBs] at c1
    have h2 : 0 ≤ (1 - A * B) * (r * s - t) :=
      mul_nonneg (by linarith) (by linarith)
    have e3 : (u.imI - v.imI) ^ 2 + (u.imJ - v.imJ) ^ 2 + (u.imK - v.imK) ^ 2 = r ^ 2 + s ^ 2 - 2 * t := by
      rw [hru, hsv, ht]; ring
    nlinarith [e, e3, p1, p2, c1, h2]
  exact sq_le_sq_imp_le key (norm_nonneg _)
private theorem expUnit_dist_le (u v : imaginaryQuaternions) :
    ‖((expUnit u : UnitQuaternion) : ℍ[ℝ]) - ((expUnit v : UnitQuaternion) : ℍ[ℝ])‖ ≤ ‖u - v‖ :=
  exp_dist_le (u : ℍ[ℝ]) (v : ℍ[ℝ]) u.2 v.2
private theorem unit_mul_dist_le (a a' b b' : UnitQuaternion) :
    ‖((a * b : UnitQuaternion) : ℍ[ℝ]) - ((a' * b' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(a : ℍ[ℝ]) - (a' : ℍ[ℝ])‖ + ‖(b : ℍ[ℝ]) - (b' : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.coe_mul_sub_mul_le <;> assumption
private theorem unit_inv_dist_eq (a a' : UnitQuaternion) :
    ‖((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((a'⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(a : ℍ[ℝ]) - (a' : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
private theorem chartedField_dist_le {F : BlockFrame} (w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (ε : ℝ)
    (h : ∀ z i, ‖w z i - w' z i‖ ≤ ε) (h0 : 0 ≤ ε) (x : F.Site F.depth) (i : Fin 4) :
    ‖((chartedField w V x i : UnitQuaternion) : ℍ[ℝ]) - ((chartedField w' V x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
  unfold chartedField
  by_cases hc : IsCrossingBond (x, i)
  · simp only [hc, if_true]
    refine (unit_mul_dist_le _ _ _ _).trans ?_
    simpa using (expUnit_dist_le _ _).trans (h x i)
  · by_cases htree : IsAxialTreeBond (x, i)
    · simp only [hc, htree, if_true, if_false]
      simpa using h0
    · simp only [hc, htree, if_false]
      exact (expUnit_dist_le _ _).trans (h x i)
private theorem linkValue_dist_le {F : BlockFrame} (X X' : F.GaugeField F.depth) (ε : ℝ)
    (h : ∀ x i, ‖((X x i : UnitQuaternion) : ℍ[ℝ]) - ((X' x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε)
    (x : F.Site F.depth) (st : PathStep) :
    ‖((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) - ((linkValue X' x st : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
  unfold linkValue
  by_cases hs : st.2 = true
  · simp only [hs, if_true]; exact h _ _
  · simp only [hs]
    simp only [Bool.false_eq_true, if_false]
    rw [unit_inv_dist_eq]; exact h _ _
private theorem pathHolonomy_dist_le {F : BlockFrame} (X X' : F.GaugeField F.depth) (ε : ℝ)
    (h : ∀ x i, ‖((X x i : UnitQuaternion) : ℍ[ℝ]) - ((X' x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε) (_h0 : 0 ≤ ε)
    (l : List PathStep) :
    ∀ x : F.Site F.depth, ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) -
      ((pathHolonomy X' x l : UnitQuaternion) : ℍ[ℝ])‖ ≤ l.length * ε := by
  induction l with
  | nil => intro x; simp [pathHolonomy]
  | cons st r ih =>
    intro x
    simp only [pathHolonomy, List.length_cons]
    refine (unit_mul_dist_le _ _ _ _).trans ?_
    have h1 := linkValue_dist_le X X' ε h x st
    have h2 := ih (x + stepDisplacement F.depth st)
    push_cast
    nlinarith
theorem chartedFieldLipschitz_holds : ChartedFieldLipschitz := by
  refine ⟨expUnit_dist_le, ?_⟩
  intro F w w' V ε h h0
  have hb := chartedField_dist_le w w' V ε h h0
  refine ⟨fun x l => pathHolonomy_dist_le _ _ ε hb h0 l x, fun p => ?_⟩
  have hh := pathHolonomy_dist_le _ _ ε hb h0
    [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] p.1
  unfold plaquetteDefect plaquetteHolonomy
  calc _ ≤ ‖((pathHolonomy (chartedField w V) p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy (chartedField w' V) p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ])‖ +
        ‖((pathHolonomy (chartedField w' V) p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ]) - 1‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
        have : ((([(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : List PathStep).length : ℕ) : ℝ) = 4 := by
          simp
        rw [this] at hh
        linarith
end YangMills.Construction.ChartLipschitz
end
