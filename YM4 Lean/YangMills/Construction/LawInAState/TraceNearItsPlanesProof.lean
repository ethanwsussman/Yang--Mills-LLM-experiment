import YangMills.Construction.LawInAState.TraceNearItsPlanes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TraceBounds
variable {X S : Type}
private theorem sum_fiberwise_plane (P : Finset X) (pl : X → Fin 4 × Fin 4) (Pl : Finset (Fin 4 × Fin 4))
    (hpl : ∀ p ∈ P, pl p ∈ Pl) (g : X → Fin 4 × Fin 4 → ℝ) :
    ∑ p ∈ P, g p (pl p) = ∑ A ∈ Pl, ∑ p ∈ P.filter (fun p => pl p = A), g p A := by
  rw [← Finset.sum_fiberwise_of_maps_to hpl]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun p hp => ?_
  rw [(Finset.mem_filter.mp hp).2]
private theorem sum_kernel_mul_planes (P : Finset X) (pl : X → Fin 4 × Fin 4) (Pl : Finset (Fin 4 × Fin 4))
    (hpl : ∀ p ∈ P, pl p ∈ Pl) (k : X → X → ℝ) (J : Fin 4 × Fin 4 → Fin 4 × Fin 4 → ℝ) :
    ∑ p ∈ P, ∑ p' ∈ P, k p p' * J (pl p) (pl p') =
      ∑ A ∈ Pl, ∑ B ∈ Pl, (∑ p ∈ P.filter (fun p => pl p = A), ∑ p' ∈ P.filter (fun p' => pl p' = B), k p p') * J A B := by
  rw [sum_fiberwise_plane P pl Pl hpl fun p A => ∑ p' ∈ P, k p p' * J A (pl p')]
  refine Finset.sum_congr rfl fun A _ => ?_
  have h1 : ∀ p, ∑ p' ∈ P, k p p' * J A (pl p') =
      ∑ B ∈ Pl, ∑ p' ∈ P.filter (fun p' => pl p' = B), k p p' * J A B := fun p =>
    sum_fiberwise_plane P pl Pl hpl fun p' B => k p p' * J A B
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]
private theorem double_sum_mul_double_sum (P : Finset X) (a c : X → X → ℝ) :
    ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, a p₁ p₂ * c p₃ p₄ =
      (∑ p₁ ∈ P, ∑ p₂ ∈ P, a p₁ p₂) * ∑ p₃ ∈ P, ∑ p₄ ∈ P, c p₃ p₄ := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p₁ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p₂ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p₃ _ => ?_
  rw [Finset.mul_sum]
private theorem trace_sum_kernels_eq (P : Finset X) (Y Z : Finset S) (κ κ' : S → X → X → ℝ) (T : X → X → ℝ) :
    ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        (∑ y ∈ Y, κ y p₁ p₂) * T p₂ p₃ * (∑ z ∈ Z, κ' z p₃ p₄) * T p₄ p₁ =
      ∑ y ∈ Y, ∑ z ∈ Z, ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        κ y p₁ p₂ * T p₂ p₃ * κ' z p₃ p₄ * T p₄ p₁ := by
  have h : ∀ p₁ p₂ p₃ p₄, (∑ y ∈ Y, κ y p₁ p₂) * T p₂ p₃ * (∑ z ∈ Z, κ' z p₃ p₄) * T p₄ p₁ =
      ∑ y ∈ Y, ∑ z ∈ Z, κ y p₁ p₂ * T p₂ p₃ * κ' z p₃ p₄ * T p₄ p₁ := by
    intro p₁ p₂ p₃ p₄
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  simp only [h]
  calc _ = ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ y ∈ Y, ∑ p₄ ∈ P, ∑ z ∈ Z, κ y p₁ p₂ * T p₂ p₃ * κ' z p₃ p₄ * T p₄ p₁ := by
        refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => Finset.sum_congr rfl fun p₃ _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ y ∈ Y, ∑ p₃ ∈ P, ∑ p₄ ∈ P, ∑ z ∈ Z, κ y p₁ p₂ * T p₂ p₃ * κ' z p₃ p₄ * T p₄ p₁ := by
        refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ p₁ ∈ P, ∑ y ∈ Y, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, ∑ z ∈ Z, κ y p₁ p₂ * T p₂ p₃ * κ' z p₃ p₄ * T p₄ p₁ := by
        refine Finset.sum_congr rfl fun p₁ _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ y ∈ Y, ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, ∑ z ∈ Z, κ y p₁ p₂ * T p₂ p₃ * κ' z p₃ p₄ * T p₄ p₁ := by
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun y _ => ?_
        calc _ = ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ z ∈ Z, ∑ p₄ ∈ P, κ y p₁ p₂ * T p₂ p₃ * κ' z p₃ p₄ * T p₄ p₁ := by
              refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => Finset.sum_congr rfl fun p₃ _ => ?_
              rw [Finset.sum_comm]
          _ = ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ z ∈ Z, ∑ p₃ ∈ P, ∑ p₄ ∈ P, κ y p₁ p₂ * T p₂ p₃ * κ' z p₃ p₄ * T p₄ p₁ := by
              refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => ?_
              rw [Finset.sum_comm]
          _ = ∑ p₁ ∈ P, ∑ z ∈ Z, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, κ y p₁ p₂ * T p₂ p₃ * κ' z p₃ p₄ * T p₄ p₁ := by
              refine Finset.sum_congr rfl fun p₁ _ => ?_
              rw [Finset.sum_comm]
          _ = _ := by rw [Finset.sum_comm]
private theorem abs_mul_sub_mul_le_of_near {t t' h h' e b w w' : ℝ} (he : 0 ≤ e) (hb : 0 ≤ b) (hw : 1 ≤ w)
    (hw' : 1 ≤ w') (h1 : |t - h| ≤ e * w) (h2 : |t' - h'| ≤ e * w') (h3 : |h| ≤ b) (h4 : |h'| ≤ b) :
    |t * t' - h * h'| ≤ e * (2 * b + e) * (w * w') := by
  have e1 : t * t' - h * h' = (t - h) * (t' - h') + (t - h) * h' + h * (t' - h') := by ring
  have k1 : |(t - h) * (t' - h')| ≤ (e * w) * (e * w') := by
    rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have k2 : |(t - h) * h'| ≤ (e * w) * b := by
    rw [abs_mul]; exact mul_le_mul h1 h4 (abs_nonneg _) (by positivity)
  have k3 : |h * (t' - h')| ≤ b * (e * w') := by
    rw [abs_mul]; exact mul_le_mul h3 h2 (abs_nonneg _) hb
  have q1 : e * w * b ≤ e * b * (w * w') := by
    have : e * b * w * 1 ≤ e * b * w * w' := mul_le_mul_of_nonneg_left hw' (by positivity)
    nlinarith
  have q2 : b * (e * w') ≤ e * b * (w * w') := by
    have : e * b * w' * 1 ≤ e * b * w' * w := mul_le_mul_of_nonneg_left hw (by positivity)
    nlinarith
  have q3 := abs_add_le ((t - h) * (t' - h') + (t - h) * h') (h * (t' - h'))
  have q4 := abs_add_le ((t - h) * (t' - h')) ((t - h) * h')
  rw [e1]
  nlinarith
private theorem abs_trace_pair_sub_le (P : Finset X) (k k' : X → X → ℝ) (T : X → X → ℝ) (h : X → X → ℝ)
    (w w' : X → ℝ) (e b M : ℝ) (he : 0 ≤ e) (hb : 0 ≤ b) (hM : 0 ≤ M) (hw : ∀ p, 1 ≤ w p) (hw' : ∀ p, 1 ≤ w' p)
    (h1 : ∀ p ∈ P, ∀ p' ∈ P, |T p p' - h p p'| ≤ e * (w p * w' p'))
    (h2 : ∀ p ∈ P, ∀ p' ∈ P, |T p' p - h p' p| ≤ e * (w p * w' p'))
    (h3 : ∀ p p', |h p p'| ≤ b)
    (hk : ∑ p ∈ P, ∑ p' ∈ P, |k p p'| * (w p * w p') ≤ M)
    (hk' : ∑ p ∈ P, ∑ p' ∈ P, |k' p p'| * (w' p * w' p') ≤ M) :
    |∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, k p₁ p₂ * T p₂ p₃ * k' p₃ p₄ * T p₄ p₁ -
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, k p₁ p₂ * h p₂ p₃ * k' p₃ p₄ * h p₄ p₁| ≤ e * (2 * b + e) * M ^ 2 := by
  simp only [← Finset.sum_sub_distrib]
  have hpt : ∀ p₁ ∈ P, ∀ p₂ ∈ P, ∀ p₃ ∈ P, ∀ p₄ ∈ P,
      |k p₁ p₂ * T p₂ p₃ * k' p₃ p₄ * T p₄ p₁ - k p₁ p₂ * h p₂ p₃ * k' p₃ p₄ * h p₄ p₁| ≤
        (e * (2 * b + e)) * ((|k p₁ p₂| * (w p₁ * w p₂)) * (|k' p₃ p₄| * (w' p₃ * w' p₄))) := by
    intro p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄
    have hf := abs_mul_sub_mul_le_of_near he hb (one_le_mul_of_one_le_of_one_le (hw p₂) (hw' p₃))
      (one_le_mul_of_one_le_of_one_le (hw p₁) (hw' p₄)) (h1 p₂ hp₂ p₃ hp₃) (h2 p₁ hp₁ p₄ hp₄) (h3 _ _) (h3 _ _)
    have e1 : k p₁ p₂ * T p₂ p₃ * k' p₃ p₄ * T p₄ p₁ - k p₁ p₂ * h p₂ p₃ * k' p₃ p₄ * h p₄ p₁ =
        k p₁ p₂ * k' p₃ p₄ * (T p₂ p₃ * T p₄ p₁ - h p₂ p₃ * h p₄ p₁) := by ring
    rw [e1, abs_mul, abs_mul]
    calc _ ≤ |k p₁ p₂| * |k' p₃ p₄| * (e * (2 * b + e) * (w p₂ * w' p₃ * (w p₁ * w' p₄))) :=
          mul_le_mul_of_nonneg_left hf (by positivity)
      _ = _ := by ring
  have hsum : |∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        (k p₁ p₂ * T p₂ p₃ * k' p₃ p₄ * T p₄ p₁ - k p₁ p₂ * h p₂ p₃ * k' p₃ p₄ * h p₄ p₁)| ≤
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        (e * (2 * b + e)) * ((|k p₁ p₂| * (w p₁ * w p₂)) * (|k' p₃ p₄| * (w' p₃ * w' p₄))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p₁ hp₁ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p₂ hp₂ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p₃ hp₃ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p₄ hp₄ => ?_)
    exact hpt p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄
  refine hsum.trans ?_
  simp only [← Finset.mul_sum]
  have hd := double_sum_mul_double_sum P (fun p₁ p₂ => |k p₁ p₂| * (w p₁ * w p₂))
    (fun p₃ p₄ => |k' p₃ p₄| * (w' p₃ * w' p₄))
  simp only [← Finset.mul_sum] at hd
  rw [hd]
  have n2 : 0 ≤ ∑ p₃ ∈ P, ∑ p₄ ∈ P, |k' p₃ p₄| * (w' p₃ * w' p₄) :=
    Finset.sum_nonneg fun p₁ _ => Finset.sum_nonneg fun p₂ _ =>
      mul_nonneg (abs_nonneg _) (mul_nonneg (zero_le_one.trans (hw' _)) (zero_le_one.trans (hw' _)))
  have : (∑ p₁ ∈ P, ∑ p₂ ∈ P, |k p₁ p₂| * (w p₁ * w p₂)) *
      (∑ p₃ ∈ P, ∑ p₄ ∈ P, |k' p₃ p₄| * (w' p₃ * w' p₄)) ≤ M ^ 2 := by
    rw [sq]
    exact mul_le_mul hk hk' n2 hM
  exact mul_le_mul_of_nonneg_left this (by positivity)
private theorem abs_trace_diagonal_sub_le (Pl : Finset (Fin 4 × Fin 4)) (τ τ' H : Fin 4 × Fin 4 → Fin 4 × Fin 4 → ℝ)
    (a c e₁ g b : ℝ) (he : 0 ≤ e₁) (hg : 0 ≤ g) (hb : 0 ≤ b) (ha : |a| ≤ g) (hc : |c| ≤ g)
    (h1 : ∀ A ∈ Pl, ∀ B ∈ Pl, |τ A B - (if A = B then a else 0)| ≤ e₁)
    (h2 : ∀ A ∈ Pl, ∀ B ∈ Pl, |τ' A B - (if A = B then c else 0)| ≤ e₁)
    (h3 : ∀ A B, |H A B| ≤ b) :
    |∑ A ∈ Pl, ∑ B ∈ Pl, τ A B * ∑ E ∈ Pl, ∑ F ∈ Pl, τ' E F * (H B E * H F A) -
      a * c * ∑ A ∈ Pl, ∑ B ∈ Pl, H A B * H B A| ≤ (Pl.card : ℝ) ^ 4 * (e₁ * (2 * g + e₁) * b ^ 2) := by
  have hdel : a * c * ∑ A ∈ Pl, ∑ B ∈ Pl, H A B * H B A =
      ∑ A ∈ Pl, ∑ B ∈ Pl, (if A = B then a else 0) *
        ∑ E ∈ Pl, ∑ F ∈ Pl, (if E = F then c else 0) * (H B E * H F A) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A hA => ?_
    have : ∀ B, (if A = B then a else 0) * ∑ E ∈ Pl, ∑ F ∈ Pl, (if E = F then c else 0) * (H B E * H F A) =
        if A = B then a * ∑ E ∈ Pl, ∑ F ∈ Pl, (if E = F then c else 0) * (H B E * H F A) else 0 := by
      intro B; split_ifs <;> simp
    simp only [this]
    rw [Finset.sum_ite_eq, if_pos hA, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun E hE => ?_
    have : ∀ F, (if E = F then c else 0) * (H A E * H F A) = if E = F then c * (H A E * H F A) else 0 := by
      intro F; split_ifs <;> simp
    simp only [this]
    rw [Finset.sum_ite_eq, if_pos hE]
    ring
  rw [hdel]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hpt : ∀ A ∈ Pl, ∀ B ∈ Pl, ∀ E ∈ Pl, ∀ F ∈ Pl,
      |τ A B * (τ' E F * (H B E * H F A)) - (if A = B then a else 0) * ((if E = F then c else 0) * (H B E * H F A))| ≤
        e₁ * (2 * g + e₁) * b ^ 2 := by
    intro A hA B hB E hE F hF
    have k1 := h1 A hA B hB
    have k2 := h2 E hE F hF
    set t := (if A = B then a else 0) with ht
    set t' := (if E = F then c else 0) with ht'
    have t1 : |t| ≤ g := by
      rw [ht]; split_ifs
      · exact ha
      · simpa using hg
    have t2 : |t'| ≤ g := by
      rw [ht']; split_ifs
      · exact hc
      · simpa using hg
    have e1 : τ A B * (τ' E F * (H B E * H F A)) - t * (t' * (H B E * H F A)) =
        (τ A B * τ' E F - t * t') * (H B E * H F A) := by ring
    have k3 : |τ A B * τ' E F - t * t'| ≤ e₁ * (2 * g + e₁) := by
      have e2 : τ A B * τ' E F - t * t' = (τ A B - t) * (τ' E F - t') + (τ A B - t) * t' + t * (τ' E F - t') := by ring
      have m1 : |(τ A B - t) * (τ' E F - t')| ≤ e₁ * e₁ := by
        rw [abs_mul]; exact mul_le_mul k1 k2 (abs_nonneg _) he
      have m2 : |(τ A B - t) * t'| ≤ e₁ * g := by
        rw [abs_mul]; exact mul_le_mul k1 t2 (abs_nonneg _) he
      have m3 : |t * (τ' E F - t')| ≤ g * e₁ := by
        rw [abs_mul]; exact mul_le_mul t1 k2 (abs_nonneg _) hg
      have q3 := abs_add_le ((τ A B - t) * (τ' E F - t') + (τ A B - t) * t') (t * (τ' E F - t'))
      have q4 := abs_add_le ((τ A B - t) * (τ' E F - t')) ((τ A B - t) * t')
      rw [e2]
      nlinarith
    have k4 : |H B E * H F A| ≤ b ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul (h3 _ _) (h3 _ _) (abs_nonneg _) hb
    rw [e1, abs_mul]
    exact mul_le_mul k3 k4 (abs_nonneg _) (by positivity)
  have c4 : ((Pl.card : ℝ)) ^ 4 * (e₁ * (2 * g + e₁) * b ^ 2) =
      ∑ _A ∈ Pl, ∑ _B ∈ Pl, ∑ _E ∈ Pl, ∑ _F ∈ Pl, e₁ * (2 * g + e₁) * b ^ 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [c4]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun A hA => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun B hB => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun E hE => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun F hF => ?_)
  exact hpt A hA B hB E hE F hF
theorem traceNearPlaneValues_holds : TraceNearPlaneValues := by
  intro X S P pl Pl Y Z κ κ' T H W α β e b e₁ g M he hb he₁ hg hM hpl hW hU hU' hC hMk hMk' hτ hτ' hα hβ
  rw [trace_sum_kernels_eq]
  have c2 : (Y.card : ℝ) * (Z.card : ℝ) * (e * (2 * b + e) * M ^ 2 + (Pl.card : ℝ) ^ 4 * (e₁ * (2 * g + e₁) * b ^ 2)) =
      ∑ _y ∈ Y, ∑ _z ∈ Z, (e * (2 * b + e) * M ^ 2 + (Pl.card : ℝ) ^ 4 * (e₁ * (2 * g + e₁) * b ^ 2)) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [c2, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y hy => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z hz => ?_)
  set τ : Fin 4 × Fin 4 → Fin 4 × Fin 4 → ℝ := fun A B =>
    ∑ p ∈ P.filter (fun p => pl p = A), ∑ p' ∈ P.filter (fun p' => pl p' = B), κ y p p' with hτd
  set τ' : Fin 4 × Fin 4 → Fin 4 × Fin 4 → ℝ := fun A B =>
    ∑ p ∈ P.filter (fun p => pl p = A), ∑ p' ∈ P.filter (fun p' => pl p' = B), κ' z p p' with hτd'
  have hpair := abs_trace_pair_sub_le P (κ y) (κ' z) T (fun p p' => H y z (pl p) (pl p')) (W y) (W z) e b M
    he hb hM (hW y) (hW z) (hU y hy z hz) (hU' y hy z hz) (fun _ _ => hC y hy z hz _ _) (hMk y hy) (hMk' z hz)
  have hdiag := abs_trace_diagonal_sub_le Pl τ τ' (H y z) (α y) (β z) e₁ g b he₁ hg hb (hα y hy) (hβ z hz)
    (hτ y hy) (hτ' z hz) (hC y hy z hz)
  have hmain : ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
      κ y p₁ p₂ * H y z (pl p₂) (pl p₃) * κ' z p₃ p₄ * H y z (pl p₄) (pl p₁) =
      ∑ A ∈ Pl, ∑ B ∈ Pl, τ A B * ∑ E ∈ Pl, ∑ F ∈ Pl, τ' E F * (H y z B E * H y z F A) := by
    have h1 : ∀ B A, ∑ p₃ ∈ P, ∑ p₄ ∈ P, κ' z p₃ p₄ * (H y z B (pl p₃) * H y z (pl p₄) A) =
        ∑ E ∈ Pl, ∑ F ∈ Pl, τ' E F * (H y z B E * H y z F A) := fun B A =>
      sum_kernel_mul_planes P pl Pl hpl (κ' z) fun E F => H y z B E * H y z F A
    have h2 := sum_kernel_mul_planes P pl Pl hpl (κ y) fun A B =>
      ∑ E ∈ Pl, ∑ F ∈ Pl, τ' E F * (H y z B E * H y z F A)
    calc _ = ∑ p₁ ∈ P, ∑ p₂ ∈ P, κ y p₁ p₂ *
            ∑ E ∈ Pl, ∑ F ∈ Pl, τ' E F * (H y z (pl p₂) E * H y z F (pl p₁)) := by
          refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => ?_
          rw [← h1, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p₃ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p₄ _ => ?_
          ring
      _ = _ := h2
  rw [hmain] at hpair
  have := abs_sub_le (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, κ y p₁ p₂ * T p₂ p₃ * κ' z p₃ p₄ * T p₄ p₁)
    (∑ A ∈ Pl, ∑ B ∈ Pl, τ A B * ∑ E ∈ Pl, ∑ F ∈ Pl, τ' E F * (H y z B E * H y z F A))
    (α y * β z * ∑ A ∈ Pl, ∑ B ∈ Pl, H y z A B * H y z B A)
  linarith
end YangMills.Construction.TraceBounds
end
