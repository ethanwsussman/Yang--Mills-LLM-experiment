import YangMills.Construction.Torus.PartitionsShellsCubes
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.Torus.GridGap
section General
variable {α β : Type} [Fintype α] [Fintype β]
def varianceSum (v : α → ℝ) : ℝ :=
  ∑ a, (v a - (Fintype.card α : ℝ)⁻¹ * ∑ b, v b) ^ 2
open Classical in
def edgeEnergy (R : α → α → Prop) (v : α → ℝ) : ℝ :=
  ∑ a, ∑ b, if R a b then (v a - v b) ^ 2 else 0
def HasPoincareConst (R : α → α → Prop) (C : ℝ) : Prop :=
  ∀ v : α → ℝ, varianceSum v ≤ C * edgeEnergy R v
def boxProductRel (R : α → α → Prop) (S : β → β → Prop) (p q : α × β) : Prop :=
  (R p.1 q.1 ∧ p.2 = q.2) ∨ (p.1 = q.1 ∧ S p.2 q.2)
theorem edgeEnergy_nonneg (R : α → α → Prop) (v : α → ℝ) : 0 ≤ edgeEnergy R v :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> positivity
theorem varianceSum_eq [Nonempty α] (v : α → ℝ) :
    varianceSum v = ∑ a, v a ^ 2 - (Fintype.card α : ℝ)⁻¹ * (∑ a, v a) ^ 2 := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold varianceSum
  have h : ∀ a, (v a - (Fintype.card α : ℝ)⁻¹ * ∑ b, v b) ^ 2 =
      v a ^ 2 - 2 * ((Fintype.card α : ℝ)⁻¹ * ∑ b, v b) * v a +
        ((Fintype.card α : ℝ)⁻¹ * ∑ b, v b) ^ 2 := fun a => by ring
  simp only [h, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring
theorem varianceSum_prod [Nonempty α] [Nonempty β] (f : α × β → ℝ) :
    varianceSum f = ∑ a, varianceSum (fun b => f (a, b)) +
      (Fintype.card β : ℝ) * varianceSum (fun a => (Fintype.card β : ℝ)⁻¹ * ∑ b, f (a, b)) := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hm : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [varianceSum_eq, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    sum_sub_distrib, mul_pow, ← mul_sum]
  field_simp
  ring
open Classical in
theorem edgeEnergy_fibres_le (R : α → α → Prop) (S : β → β → Prop) (f : α × β → ℝ) :
    ∑ a, edgeEnergy S (fun b => f (a, b)) + ∑ b, edgeEnergy R (fun a => f (a, b)) ≤
      edgeEnergy (boxProductRel R S) f := by
  have h1 : ∀ a b, ∑ a', ∑ b', (if a = a' ∧ S b b' then (f (a, b) - f (a', b')) ^ 2 else 0) =
      ∑ b', if S b b' then (f (a, b) - f (a, b')) ^ 2 else 0 := by
    intro a b
    rw [sum_eq_single a]
    · simp
    · intro a' _ hne
      simp [hne.symm]
    · simp
  have h2 : ∀ a b, ∑ a', ∑ b', (if R a a' ∧ b = b' then (f (a, b) - f (a', b')) ^ 2 else 0) =
      ∑ a', if R a a' then (f (a, b) - f (a', b)) ^ 2 else 0 := by
    intro a b
    refine sum_congr rfl fun a' _ => ?_
    rw [sum_eq_single b]
    · simp
    · intro b' _ hne
      simp [hne.symm]
    · simp
  have hE : edgeEnergy (boxProductRel R S) f =
      ∑ a, ∑ b, ∑ a', ∑ b', if boxProductRel R S (a, b) (a', b')
        then (f (a, b) - f (a', b')) ^ 2 else 0 := by
    simp only [edgeEnergy, Fintype.sum_prod_type]
  have hL : ∑ a, edgeEnergy S (fun b => f (a, b)) + ∑ b, edgeEnergy R (fun a => f (a, b)) =
      ∑ a, ∑ b, ((∑ b', if S b b' then (f (a, b) - f (a, b')) ^ 2 else 0) +
        ∑ a', if R a a' then (f (a, b) - f (a', b)) ^ 2 else 0) := by
    simp only [edgeEnergy, sum_add_distrib]
    rw [sum_comm (s := univ (α := β))]
  rw [hE, hL]
  refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
  rw [← h1, ← h2, ← sum_add_distrib]
  refine sum_le_sum fun a' _ => ?_
  rw [← sum_add_distrib]
  refine sum_le_sum fun b' _ => ?_
  by_cases hA : a = a' ∧ S b b'
  · by_cases hB : R a a' ∧ b = b'
    · have hz : (f (a, b) - f (a', b')) ^ 2 = 0 := by
        rw [← hA.1, ← hB.2]
        simp
      simp [hz]
    · have hbox : boxProductRel R S (a, b) (a', b') := Or.inr hA
      rw [if_pos hA, if_neg hB, if_pos hbox, add_zero]
  · by_cases hB : R a a' ∧ b = b'
    · have hbox : boxProductRel R S (a, b) (a', b') := Or.inl hB
      rw [if_neg hA, if_pos hB, if_pos hbox, zero_add]
    · rw [if_neg hA, if_neg hB, add_zero]
      split_ifs <;> positivity
theorem edgeEnergy_means_le [Nonempty β] (R : α → α → Prop) (f : α × β → ℝ) :
    edgeEnergy R (fun a => (Fintype.card β : ℝ)⁻¹ * ∑ b, f (a, b)) ≤
      (Fintype.card β : ℝ)⁻¹ * ∑ b, edgeEnergy R (fun a => f (a, b)) := by
  classical
  have key : ∀ a a', (if R a a' then
      ((Fintype.card β : ℝ)⁻¹ * ∑ b, f (a, b) - (Fintype.card β : ℝ)⁻¹ * ∑ b, f (a', b)) ^ 2
        else 0) ≤
      (Fintype.card β : ℝ)⁻¹ * ∑ b, if R a a' then (f (a, b) - f (a', b)) ^ 2 else 0 := by
    intro a a'
    by_cases h : R a a'
    · simp only [if_pos h]
      have hc := sq_sum_le_card_mul_sum_sq (s := (univ : Finset β))
        (f := fun b => f (a, b) - f (a', b))
      rw [card_univ] at hc
      rw [← mul_sub, ← sum_sub_distrib, mul_pow]
      calc ((Fintype.card β : ℝ)⁻¹) ^ 2 * (∑ b, (f (a, b) - f (a', b))) ^ 2
          ≤ ((Fintype.card β : ℝ)⁻¹) ^ 2 *
              ((Fintype.card β : ℝ) * ∑ b, (f (a, b) - f (a', b)) ^ 2) :=
            mul_le_mul_of_nonneg_left hc (by positivity)
        _ = (Fintype.card β : ℝ)⁻¹ * ∑ b, (f (a, b) - f (a', b)) ^ 2 := by
            field_simp
    · simp [h]
  unfold edgeEnergy
  calc _ ≤ ∑ a, ∑ a', (Fintype.card β : ℝ)⁻¹ *
          ∑ b, (if R a a' then (f (a, b) - f (a', b)) ^ 2 else 0) :=
        sum_le_sum fun a _ => sum_le_sum fun a' _ => by convert key a a'
    _ = _ := by
        simp only [← mul_sum]
        congr 1
        have h : ∀ a, ∑ a', ∑ b, (if R a a' then (f (a, b) - f (a', b)) ^ 2 else 0) =
            ∑ b, ∑ a', if R a a' then (f (a, b) - f (a', b)) ^ 2 else 0 := fun a => sum_comm
        simp only [h]
        exact sum_comm
theorem HasPoincareConst.boxProduct [Nonempty α] [Nonempty β] {R : α → α → Prop}
    {S : β → β → Prop} {C : ℝ}
    (hR : HasPoincareConst R C) (hS : HasPoincareConst S C) (hC : 0 ≤ C) :
    HasPoincareConst (boxProductRel R S) C := by
  intro f
  have hm : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : ∑ a, varianceSum (fun b => f (a, b)) ≤ C * ∑ a, edgeEnergy S (fun b => f (a, b)) := by
    rw [mul_sum]
    exact sum_le_sum fun a _ => hS _
  have h2 := hR (fun a => (Fintype.card β : ℝ)⁻¹ * ∑ b, f (a, b))
  have h3 := edgeEnergy_means_le R f
  rw [varianceSum_prod f]
  calc _ ≤ C * ∑ a, edgeEnergy S (fun b => f (a, b)) + (Fintype.card β : ℝ) *
        (C * ((Fintype.card β : ℝ)⁻¹ * ∑ b, edgeEnergy R (fun a => f (a, b)))) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left
          (h2.trans (mul_le_mul_of_nonneg_left h3 hC)) (by positivity))
    _ = C * (∑ a, edgeEnergy S (fun b => f (a, b)) + ∑ b, edgeEnergy R (fun a => f (a, b))) := by
        field_simp
    _ ≤ C * edgeEnergy (boxProductRel R S) f :=
        mul_le_mul_of_nonneg_left (edgeEnergy_fibres_le R S f) hC
theorem HasPoincareConst.of_equiv {R : α → α → Prop} {S : β → β → Prop} {C : ℝ} (e : α ≃ β)
    (hRS : ∀ a a', S (e a) (e a') → R a a') (h : HasPoincareConst S C) (hC : 0 ≤ C) :
    HasPoincareConst R C := by
  classical
  intro v
  have hs : varianceSum (fun b => v (e.symm b)) = varianceSum v := by
    unfold varianceSum
    rw [Equiv.sum_comp e.symm v, Fintype.card_congr e]
    exact Equiv.sum_comp e.symm
      (fun a => (v a - (Fintype.card β : ℝ)⁻¹ * ∑ b, v b) ^ 2)
  have he : edgeEnergy S (fun b => v (e.symm b)) ≤ edgeEnergy R v := by
    unfold edgeEnergy
    rw [← Equiv.sum_comp e]
    refine sum_le_sum fun a _ => ?_
    rw [← Equiv.sum_comp e]
    refine sum_le_sum fun a' _ => ?_
    simp only [Equiv.symm_apply_apply]
    by_cases hS : S (e a) (e a')
    · simp [hS, hRS a a' hS]
    · rw [if_neg hS]
      split_ifs <;> positivity
  rw [← hs]
  exact (h _).trans (mul_le_mul_of_nonneg_left he hC)
end General
section Path
end Path
end YangMills.Construction.Torus.GridGap
