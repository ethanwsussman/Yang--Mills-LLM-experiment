import YangMills.Construction.Analysis.MultilinearTelescopingBound
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Multilinear
theorem prod_erase_eq_prod_Iio_mul_prod_Ioi {n : ℕ} (a : Fin n → ℝ) (k : Fin n) :
    ∏ j ∈ Finset.univ.erase k, a j =
      (∏ j ∈ Finset.Iio k, a j) * ∏ j ∈ Finset.Ioi k, a j := by
  have hunion : Finset.univ.erase k = Finset.Iio k ∪ Finset.Ioi k := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Iio,
      Finset.mem_Ioi]
    constructor
    · exact lt_or_gt_of_ne
    · rintro (hx | hx)
      · exact hx.ne
      · exact hx.ne'
  have hdisj : Disjoint (Finset.Iio k) (Finset.Ioi k) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact lt_asymm (Finset.mem_Iio.1 hx) (Finset.mem_Ioi.1 hy)
  rw [hunion, Finset.prod_union hdisj]
theorem prod_univ_eq_mul_prod_Iio_mul_prod_Ioi {n : ℕ} (a : Fin n → ℝ) (k : Fin n) :
    ∏ j, a j = a k * ((∏ j ∈ Finset.Iio k, a j) * ∏ j ∈ Finset.Ioi k, a j) := by
  rw [← prod_erase_eq_prod_Iio_mul_prod_Ioi, Finset.mul_prod_erase Finset.univ a (Finset.mem_univ k)]
def splice {n : ℕ} {V : Fin n → Type} (f g : ∀ j, V j) (m : ℕ) : ∀ j, V j :=
  fun j => if (j : ℕ) < m then g j else f j
theorem splice_zero {n : ℕ} {V : Fin n → Type} (f g : ∀ j, V j) : splice f g 0 = f := by
  funext j
  simp [splice]
theorem splice_last {n : ℕ} {V : Fin n → Type} (f g : ∀ j, V j) : splice f g n = g := by
  funext j
  simp [splice]
theorem update_splice_left {n : ℕ} {V : Fin n → Type} (f g : ∀ j, V j) (k : Fin n) :
    Function.update (splice f g k) k (f k) = splice f g k := by
  funext i
  by_cases hik : i = k
  · subst hik
    simp [splice]
  · simp [Function.update_of_ne hik]
theorem update_splice_right {n : ℕ} {V : Fin n → Type} (f g : ∀ j, V j) (k : Fin n) :
    Function.update (splice f g k) k (g k) = splice f g ((k : ℕ) + 1) := by
  funext i
  by_cases hik : i = k
  · subst hik
    simp [splice]
  · have hne : (i : ℕ) ≠ k := fun e => hik (Fin.ext e)
    have hiff : (i : ℕ) < (k : ℕ) + 1 ↔ (i : ℕ) < k := by omega
    simp [Function.update_of_ne hik, splice, hiff]
theorem prod_seminorm_update_splice {n : ℕ} {V : Fin n → Type} [∀ j, AddCommGroup (V j)]
    [∀ j, Module ℝ (V j)] (p : ∀ j, Seminorm ℝ (V j)) (f g : ∀ j, V j) (k : Fin n) :
    ∏ j, p j (Function.update (splice f g k) k (f k - g k) j) =
      p k (f k - g k) * (∏ j ∈ Finset.Iio k, p j (g j)) * ∏ j ∈ Finset.Ioi k, p j (f j) := by
  rw [prod_univ_eq_mul_prod_Iio_mul_prod_Ioi _ k, Function.update_self, mul_assoc]
  congr 2
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hlt := Finset.mem_Iio.1 hi
    rw [Function.update_of_ne hlt.ne]
    simp [splice, Fin.lt_def.1 hlt]
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hlt := Finset.mem_Ioi.1 hi
    rw [Function.update_of_ne hlt.ne']
    have hnot : ¬ (i : ℕ) < k := not_lt.2 (Fin.lt_def.1 hlt).le
    simp [splice, hnot]
theorem multilinearTelescopingBound_holds : MultilinearTelescopingBound := by
  intro n _ V _ _ p c hc Φ hΦ f g
  constructor
  · have htel : Φ f - Φ g =
        ∑ k : Fin n, Φ (Function.update (splice f g k) k (f k - g k)) := by
      have hstep : ∀ k : Fin n, Φ (Function.update (splice f g k) k (f k - g k)) =
          Φ (splice f g k) - Φ (splice f g ((k : ℕ) + 1)) := by
        intro k
        rw [Φ.map_update_sub, update_splice_left, update_splice_right]
      simp only [hstep]
      rw [Fin.sum_univ_eq_sum_range (fun i => Φ (splice f g i) - Φ (splice f g (i + 1))) n,
        Finset.sum_range_sub', splice_zero, splice_last]
    rw [htel, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have hb := hΦ (Function.update (splice f g k) k (f k - g k))
    rw [prod_seminorm_update_splice] at hb
    rw [← mul_assoc] at hb ⊢
    simpa [mul_assoc] using hb
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hc
    rw [mul_assoc, prod_erase_eq_prod_Iio_mul_prod_Ioi]
    refine mul_le_mul_of_nonneg_left ?_ (apply_nonneg _ _)
    refine mul_le_mul ?_ ?_ ?_ ?_
    · exact Finset.prod_le_prod (fun i _ => apply_nonneg _ _)
        fun i _ => le_add_of_nonneg_left (apply_nonneg _ _)
    · exact Finset.prod_le_prod (fun i _ => apply_nonneg _ _)
        fun i _ => le_add_of_nonneg_right (apply_nonneg _ _)
    · exact Finset.prod_nonneg fun i _ => apply_nonneg _ _
    · exact Finset.prod_nonneg fun i _ => add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
end YangMills.Construction.Multilinear
