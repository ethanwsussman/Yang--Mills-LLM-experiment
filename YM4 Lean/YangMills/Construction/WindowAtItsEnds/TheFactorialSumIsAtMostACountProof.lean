import YangMills.Construction.WindowAtItsEnds.TheFactorialSumIsAtMostACount
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.CouplingFlow
namespace PartitionCount
open Finset
section Counting
variable {α : Type*} [DecidableEq α]
private def orderedPartitionSum (A : Finset α) : ℕ :=
  ∑ π : SetPartition.Partitions A, π.parts.card.factorial
private theorem parts_avoid_eq_erase {A : Finset α} (π : SetPartition.Partitions A) {B : Finset α}
    (hB : B ∈ π.parts) : (π.avoid B).parts = π.parts.erase B := by
  ext c
  rw [Finpartition.mem_avoid]
  constructor
  · rintro ⟨d, hd, hnle, rfl⟩
    have hne : d ≠ B := by
      rintro rfl
      exact hnle le_rfl
    have hdisj : Disjoint d B := π.disjoint hd hB hne
    rw [hdisj.sdiff_eq_left]
    exact mem_erase.2 ⟨hne, hd⟩
  · intro hc
    obtain ⟨hne, hc⟩ := mem_erase.1 hc
    have hdisj : Disjoint c B := π.disjoint hc hB hne
    exact ⟨c, hc, fun hle => π.ne_bot hc (hdisj.eq_bot_of_le hle), hdisj.sdiff_eq_left⟩
private theorem avoid_injOn_of_mem {A B : Finset α} :
    Set.InjOn (fun π : SetPartition.Partitions A => (π.avoid B : Finpartition (A \ B)))
      {π | B ∈ π.parts} := by
  intro π hπ ρ hρ h
  have hparts : π.parts.erase B = ρ.parts.erase B := by
    rw [← parts_avoid_eq_erase π hπ, ← parts_avoid_eq_erase ρ hρ]
    exact congrArg Finpartition.parts h
  apply Finpartition.ext
  rw [← insert_erase (show B ∈ π.parts from hπ), ← insert_erase (show B ∈ ρ.parts from hρ), hparts]
private theorem sum_filter_mem_le (A B : Finset α) :
    ∑ π ∈ (univ : Finset (SetPartition.Partitions A)).filter (fun π => B ∈ π.parts),
        (π.avoid B).parts.card.factorial ≤ orderedPartitionSum (A \ B) := by
  classical
  have hinj : Set.InjOn (fun π : SetPartition.Partitions A => (π.avoid B : Finpartition (A \ B)))
      ((univ : Finset (SetPartition.Partitions A)).filter (fun π => B ∈ π.parts) :
        Set (SetPartition.Partitions A)) := by
    intro π hπ ρ hρ h
    exact avoid_injOn_of_mem (by simpa using hπ) (by simpa using hρ) h
  rw [orderedPartitionSum, ← Finset.sum_image (f := fun ρ : Finpartition (A \ B) => ρ.parts.card.factorial)
    hinj]
  exact Finset.sum_le_sum_of_subset (subset_univ _)
private theorem orderedPartitionSum_le_sum_sdiff {A : Finset α} (hA : A.Nonempty) :
    orderedPartitionSum A ≤ ∑ B ∈ A.powerset.filter Finset.Nonempty, orderedPartitionSum (A \ B) := by
  have hsplit : ∀ π : SetPartition.Partitions A, π.parts.card.factorial =
      ∑ B ∈ π.parts, (π.avoid B).parts.card.factorial := by
    intro π
    have hpos : 0 < π.parts.card := by
      rw [Finset.card_pos]
      exact π.parts_nonempty hA.ne_empty
    have hterm : ∀ B ∈ π.parts, (π.avoid B).parts.card.factorial =
        (π.parts.card - 1).factorial := by
      intro B hB
      rw [parts_avoid_eq_erase π hB, card_erase_of_mem hB]
    rw [Finset.sum_congr rfl hterm, sum_const, smul_eq_mul, Nat.mul_factorial_pred hpos.ne']
  have hswap : ∑ π : SetPartition.Partitions A, ∑ B ∈ π.parts,
        (π.avoid B).parts.card.factorial =
      ∑ B ∈ A.powerset.filter Finset.Nonempty,
        ∑ π ∈ (univ : Finset (SetPartition.Partitions A)).filter (fun π => B ∈ π.parts),
          (π.avoid B).parts.card.factorial := by
    apply Finset.sum_comm'
    intro π B
    simp only [mem_univ, true_and, mem_filter, mem_powerset]
    constructor
    · intro hB
      exact ⟨hB, π.le hB, π.nonempty_of_mem_parts hB⟩
    · rintro ⟨hB, -⟩
      exact hB
  calc orderedPartitionSum A = ∑ π : SetPartition.Partitions A, ∑ B ∈ π.parts,
        (π.avoid B).parts.card.factorial := Finset.sum_congr rfl fun π _ => hsplit π
    _ = _ := hswap
    _ ≤ _ := Finset.sum_le_sum fun B _ => sum_filter_mem_le A B
private theorem orderedPartitionSum_empty : orderedPartitionSum (∅ : Finset α) = 1 := by
  have hparts : ∀ π : SetPartition.Partitions (∅ : Finset α), π.parts = ∅ :=
    SetPartition.parts_eq_empty_of_empty
  have hcard : Fintype.card (SetPartition.Partitions (∅ : Finset α)) = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⊥, fun π => Finpartition.ext (by rw [hparts π, hparts ⊥])⟩
  simp [orderedPartitionSum, hparts, hcard]
end Counting
private theorem sum_range_two_pow_pred (n : ℕ) : ∑ j ∈ range (n + 1), 2 ^ (j - 1) = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    simp only [Nat.add_sub_cancel]
    ring
private theorem sum_choose_mul_bound_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ range (n + 1), n.choose m *
        (if m = 0 then 0 else (n - m).factorial * 2 ^ (n - m - 1)) ≤
      n.factorial * 2 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ']
  simp only [if_true, mul_zero, add_zero, Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, if_false]
  calc ∑ m ∈ range (k + 1), (k + 1).choose (m + 1) *
          ((k + 1 - (m + 1)).factorial * 2 ^ (k + 1 - (m + 1) - 1))
      ≤ ∑ m ∈ range (k + 1), (k + 1).factorial * 2 ^ (k - m - 1) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmk : m + 1 ≤ k + 1 := by
          have := mem_range.1 hm
          omega
        have hfac := Nat.choose_mul_factorial_mul_factorial hmk
        have hle : (k + 1).choose (m + 1) * (k + 1 - (m + 1)).factorial ≤ (k + 1).factorial := by
          rw [← hfac, mul_right_comm]
          exact Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
        have hexp : k + 1 - (m + 1) - 1 = k - m - 1 := by omega
        rw [hexp, ← mul_assoc]
        exact Nat.mul_le_mul_right _ hle
    _ = (k + 1).factorial * ∑ m ∈ range (k + 1), 2 ^ (k - m - 1) := by
        rw [Finset.mul_sum]
    _ = (k + 1).factorial * 2 ^ k := by
        congr 1
        rw [← sum_range_two_pow_pred k, ← Finset.sum_range_reflect]
        apply Finset.sum_congr rfl
        intro m hm
        have := mem_range.1 hm
        have hexp : k - (k + 1 - 1 - m) - 1 = m - 1 := by omega
        rw [hexp]
private theorem orderedPartitionSum_le {α : Type*} [DecidableEq α] (n : ℕ) :
    ∀ A : Finset α, A.card = n → orderedPartitionSum A ≤ n.factorial * 2 ^ (n - 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hA
    rcases A.eq_empty_or_nonempty with rfl | hne
    · rw [orderedPartitionSum_empty]
      simp at hA
      subst hA
      simp
    · have hn : 1 ≤ n := by
        rw [← hA]
        exact Finset.card_pos.2 hne
      calc orderedPartitionSum A ≤ ∑ B ∈ A.powerset.filter Finset.Nonempty, orderedPartitionSum (A \ B) :=
            orderedPartitionSum_le_sum_sdiff hne
        _ ≤ ∑ B ∈ A.powerset.filter Finset.Nonempty,
              (n - B.card).factorial * 2 ^ (n - B.card - 1) := by
            apply Finset.sum_le_sum
            intro B hB
            obtain ⟨hsub, hBne⟩ := mem_filter.1 hB
            have hsub' : B ⊆ A := mem_powerset.1 hsub
            have hcard : (A \ B).card = n - B.card := by
              rw [card_sdiff_of_subset hsub', hA]
            exact ih _ (by have := Finset.card_pos.2 hBne; have := card_le_card hsub'; omega) _ hcard
        _ = ∑ B ∈ A.powerset,
              (fun m => if m = 0 then 0 else (n - m).factorial * 2 ^ (n - m - 1)) B.card := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro B _
            by_cases hB : B.Nonempty
            · have : B.card ≠ 0 := (Finset.card_pos.2 hB).ne'
              simp [hB, this]
            · have hB' : B = ∅ := Finset.not_nonempty_iff_eq_empty.1 hB
              simp [hB']
        _ = ∑ m ∈ range (n + 1), n.choose m *
              (if m = 0 then 0 else (n - m).factorial * 2 ^ (n - m - 1)) := by
            rw [Finset.sum_powerset_apply_card
              (fun m => if m = 0 then 0 else (n - m).factorial * 2 ^ (n - m - 1)) (x := A), hA]
            simp only [smul_eq_mul]
        _ ≤ n.factorial * 2 ^ (n - 1) := sum_choose_mul_bound_le n hn
end PartitionCount
theorem factorialSumBound_holds : FactorialSumBound := by
  intro n _
  calc SetPartition.blockFactorialSum n
      ≤ ∑ π : SetPartition.PartitionsFin n, π.parts.card.factorial :=
        Finset.sum_le_sum fun π _ => Nat.factorial_le (Nat.sub_le _ _)
    _ ≤ n.factorial * 2 ^ (n - 1) :=
        PartitionCount.orderedPartitionSum_le n Finset.univ (by simp)
end YangMills.Construction.CouplingFlow
