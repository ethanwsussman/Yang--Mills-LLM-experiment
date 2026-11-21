import YangMills.Construction.ResponseInTheExpansion.TraceOfAProductMovesLittle
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MatrixTraces
variable {Q : Type} [Fintype Q] [DecidableEq Q]
private theorem abs_listProd_entry_le (c a b : ℝ) (hc : c = (Fintype.card Q : ℝ)) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (l l' : List (Matrix Q Q ℝ)) (hlen : l.length = l'.length) (hne : l ≠ [])
    (hl : ∀ M ∈ l, ∀ x y, |M x y| ≤ a) (hl' : ∀ M ∈ l', ∀ x y, |M x y| ≤ a)
    (hd : ∀ i (h : i < l.length) (h' : i < l'.length) x y, |l[i] x y - l'[i] x y| ≤ b) :
    (∀ x y, |l'.prod x y| ≤ c ^ (l.length - 1) * a ^ l.length) ∧
      ∀ x y, |l.prod x y - l'.prod x y| ≤ (l.length : ℝ) * c ^ (l.length - 1) * a ^ (l.length - 1) * b := by
  induction l generalizing l' with
  | nil => exact absurd rfl hne
  | cons A t ih =>
    cases l' with
    | nil => simp at hlen
    | cons A' t' =>
      have hlen' : t.length = t'.length := by simpa using hlen
      by_cases ht : t = []
      · subst ht
        have : t' = [] := List.length_eq_zero_iff.mp hlen'.symm
        subst this
        constructor
        · intro x y
          simpa using hl' A' (by simp) x y
        · intro x y
          have := hd 0 (by simp) (by simp) x y
          simpa using this
      · obtain ⟨ih1, ih2⟩ := ih t' hlen' ht (fun M hM => hl M (by simp [hM])) (fun M hM => hl' M (by simp [hM]))
          (fun i h h' x y => hd (i + 1) (by simpa using h) (by simpa using h') x y)
        have hpos : 1 ≤ t.length := List.length_pos_iff.mpr ht
        obtain ⟨r, hr⟩ : ∃ r, t.length = r + 1 := ⟨t.length - 1, by omega⟩
        have hA := hl A (by simp)
        have hA' := hl' A' (by simp)
        have hAd : ∀ x y, |A x y - A' x y| ≤ b := fun x y => hd 0 (by simp) (by simp) x y
        simp only [hr, Nat.add_sub_cancel] at ih1 ih2
        push_cast at ih2
        simp only [List.length_cons, hr, Nat.add_sub_cancel, List.prod_cons, Matrix.mul_apply]
        push_cast
        constructor
        · intro x y
          calc _ ≤ ∑ w, |A' x w * t'.prod w y| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _w : Q, a * (c ^ r * a ^ (r + 1)) := by
              refine Finset.sum_le_sum fun w _ => ?_
              rw [abs_mul]
              exact mul_le_mul (hA' x w) (ih1 w y) (abs_nonneg _) ha
            _ = _ := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hc]
              ring
        · intro x y
          rw [← Finset.sum_sub_distrib]
          calc _ ≤ ∑ w, |A x w * t.prod w y - A' x w * t'.prod w y| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _w : Q, (a * (((r : ℝ) + 1) * c ^ r * a ^ r * b) + b * (c ^ r * a ^ (r + 1))) := by
              refine Finset.sum_le_sum fun w _ => ?_
              have hs : A x w * t.prod w y - A' x w * t'.prod w y =
                  A x w * (t.prod w y - t'.prod w y) + (A x w - A' x w) * t'.prod w y := by ring
              rw [hs]
              refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [abs_mul]
                exact mul_le_mul (hA x w) (ih2 w y) (abs_nonneg _) ha
              · rw [abs_mul]
                exact mul_le_mul (hAd x w) (ih1 w y) (abs_nonneg _) hb
            _ = _ := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hc]
              ring
theorem traceProdLipschitz_holds : TraceProdLipschitz := by
  intro Q _ _ q M M' a b ha hb hM hM' hd
  have hne : List.ofFn M ≠ [] := by simp [List.ofFn_succ]
  have := (abs_listProd_entry_le (Q := Q) _ a b rfl ha hb (List.ofFn M) (List.ofFn M') (by simp) hne
    (fun A hA x y => by
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hA
      exact hM j x y)
    (fun A hA x y => by
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hA
      exact hM' j x y)
    (fun i h h' x y => by
      simpa using hd ⟨i, by simpa using h⟩ x y)).2
  simp only [List.length_ofFn, Nat.add_sub_cancel] at this
  rw [← Matrix.trace_sub]
  calc _ ≤ ∑ x, |((List.ofFn M).prod - (List.ofFn M').prod) x x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : Q, ((q + 1 : ℕ) : ℝ) * (Fintype.card Q : ℝ) ^ q * a ^ q * b :=
        Finset.sum_le_sum fun x _ => this x x
    _ = ((Fintype.card Q : ℝ)) * (((q + 1 : ℕ) : ℝ) * (Fintype.card Q : ℝ) ^ q * a ^ q * b) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by
        push_cast
        have : 1 ≤ (Fintype.card Q : ℝ) ∨ (Fintype.card Q : ℝ) = 0 := by
          rcases Nat.eq_zero_or_pos (Fintype.card Q) with h | h
          · right
            exact_mod_cast h
          · left
            exact_mod_cast h
        rcases this with h | h
        · have h2 : (Fintype.card Q : ℝ) ^ (q + 1) ≤ (Fintype.card Q : ℝ) ^ (q + 2) :=
            pow_le_pow_right₀ h (by omega)
          have h3 : 0 ≤ ((q : ℝ) + 1) * a ^ q * b := by positivity
          calc _ = (Fintype.card Q : ℝ) ^ (q + 1) * (((q : ℝ) + 1) * a ^ q * b) := by ring
            _ ≤ (Fintype.card Q : ℝ) ^ (q + 2) * (((q : ℝ) + 1) * a ^ q * b) :=
              mul_le_mul_of_nonneg_right h2 h3
            _ = _ := by ring
        · rw [h]
          simp
end YangMills.Construction.MatrixTraces
end
