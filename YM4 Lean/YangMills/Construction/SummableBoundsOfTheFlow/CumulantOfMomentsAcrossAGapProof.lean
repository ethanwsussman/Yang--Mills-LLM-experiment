import YangMills.Construction.SummableBoundsOfTheFlow.CumulantOfMomentsAcrossAGap
import YangMills.Construction.SummableBoundsOfTheFlow.PartitionSumOfTwoIndependentGroups
import Mathlib
set_option autoImplicit false
open Finset
namespace YangMills.Construction.Cumulants
theorem abs_prod_sub_prod_le_card_mul {β : Type} [DecidableEq β] (P : Finset β) (u v D : β → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hD : ∀ J ∈ P, 0 ≤ D J) (hu : ∀ J ∈ P, |u J| ≤ D J) (hv : ∀ J ∈ P, |v J| ≤ D J)
    (huv : ∀ J ∈ P, |u J - v J| ≤ ε * D J) :
    |∏ J ∈ P, u J - ∏ J ∈ P, v J| ≤ (P.card : ℝ) * ε * ∏ J ∈ P, D J := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert J P hJ ih =>
    have hD' : ∀ J' ∈ P, 0 ≤ D J' := fun J' h => hD J' (mem_insert_of_mem h)
    have hu' : ∀ J' ∈ P, |u J'| ≤ D J' := fun J' h => hu J' (mem_insert_of_mem h)
    have hv' : ∀ J' ∈ P, |v J'| ≤ D J' := fun J' h => hv J' (mem_insert_of_mem h)
    have huv' : ∀ J' ∈ P, |u J' - v J'| ≤ ε * D J' := fun J' h => huv J' (mem_insert_of_mem h)
    have ih' := ih hD' hu' hv' huv'
    rw [prod_insert hJ, prod_insert hJ, prod_insert hJ, card_insert_of_notMem hJ]
    have hpu : |∏ J' ∈ P, u J'| ≤ ∏ J' ∈ P, D J' := by
      rw [abs_prod]
      exact prod_le_prod (fun _ _ => abs_nonneg _) hu'
    have h1 : u J * ∏ J' ∈ P, u J' - v J * ∏ J' ∈ P, v J' =
        (u J - v J) * ∏ J' ∈ P, u J' + v J * (∏ J' ∈ P, u J' - ∏ J' ∈ P, v J') := by ring
    have h2 : |(u J - v J) * ∏ J' ∈ P, u J'| ≤ ε * D J * ∏ J' ∈ P, D J' := by
      rw [abs_mul]
      exact mul_le_mul (huv J (mem_insert_self _ _)) hpu (abs_nonneg _)
        (mul_nonneg hε (hD J (mem_insert_self _ _)))
    have h3 : |v J * (∏ J' ∈ P, u J' - ∏ J' ∈ P, v J')| ≤
        D J * ((P.card : ℝ) * ε * ∏ J' ∈ P, D J') := by
      rw [abs_mul]
      exact mul_le_mul (hv J (mem_insert_self _ _)) ih' (abs_nonneg _) (hD J (mem_insert_self _ _))
    rw [h1]
    refine (abs_add_le _ _).trans ((add_le_add h2 h3).trans (le_of_eq ?_))
    push_cast
    ring
theorem cumulantSmallAcrossGap_holds (hPart : CumulantOfIndependentGroupsZero) :
    CumulantSmallAcrossGap := by
  intro p A mo a ε hA hA' hmo ha hε hbound hnear
  have hzero := hPart p A mo mo hA hA' hmo hmo
  set w : Finpartition (univ : Finset (Fin p)) → ℝ :=
    fun π => (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) with hw
  have hsplit : ∀ J : Finset (Fin p), (∏ l ∈ J ∩ A, a l) * ∏ l ∈ J \ A, a l = ∏ l ∈ J, a l :=
    fun J => prod_inter_mul_prod_diff J A a
  have hDnn : ∀ J : Finset (Fin p), 0 ≤ ∏ l ∈ J, a l := fun J => prod_nonneg fun l _ => ha l
  have hterm : ∀ π : Finpartition (univ : Finset (Fin p)),
      |w π * (∏ J ∈ π.parts, mo J - ∏ J ∈ π.parts, (mo (J ∩ A) * mo (J \ A)))| ≤
        ((π.parts.card - 1).factorial : ℝ) * (π.parts.card : ℝ) * ε * ∏ l, a l := by
    intro π
    have hall : ∏ J ∈ π.parts, ∏ l ∈ J, a l = ∏ l, a l := by
      have h := prod_biUnion (s := π.parts) (t := id) (f := a) π.disjoint
      rw [π.biUnion_parts] at h
      exact h.symm
    have hd := abs_prod_sub_prod_le_card_mul π.parts mo (fun J => mo (J ∩ A) * mo (J \ A))
      (fun J => ∏ l ∈ J, a l) ε hε (fun J _ => hDnn J) (fun J _ => hbound J)
      (fun J _ => by
        rw [abs_mul, ← hsplit J]
        exact mul_le_mul (hbound _) (hbound _) (abs_nonneg _) (hDnn _))
      (fun J _ => hnear J)
    rw [hall] at hd
    have hwabs : |w π| = ((π.parts.card - 1).factorial : ℝ) := by
      simp only [hw, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    rw [abs_mul, hwabs]
    have hfac : (0 : ℝ) ≤ ((π.parts.card - 1).factorial : ℝ) := Nat.cast_nonneg _
    calc ((π.parts.card - 1).factorial : ℝ) *
          |∏ J ∈ π.parts, mo J - ∏ J ∈ π.parts, (mo (J ∩ A) * mo (J \ A))|
        ≤ ((π.parts.card - 1).factorial : ℝ) * ((π.parts.card : ℝ) * ε * ∏ l, a l) :=
          mul_le_mul_of_nonneg_left hd hfac
      _ = _ := by ring
  have heq : ∑ π : Finpartition (univ : Finset (Fin p)), w π * ∏ J ∈ π.parts, mo J =
      ∑ π : Finpartition (univ : Finset (Fin p)),
        w π * (∏ J ∈ π.parts, mo J - ∏ J ∈ π.parts, (mo (J ∩ A) * mo (J \ A))) := by
    simp only [mul_sub, sum_sub_distrib]
    rw [hzero, sub_zero]
  rw [heq]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun π _ => hterm π).trans (le_of_eq ?_))
  rw [partitionWeightSum, sum_mul, sum_mul]
end YangMills.Construction.Cumulants
