import YangMills.Construction.ColdChainAtEveryLevel.SharesOfTheCellsAtASite
import YangMills.Construction.ColdChainAtEveryLevel.SumOfTheFramedShares
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace GaugedCellShareSum
variable {F : BlockFrame} {S : Finset F.Cell}
theorem zmod_one_ne_zero_of_ne_one {n : ℕ} (hn : n ≠ 1) : (1 : ZMod n) ≠ 0 := by
  intro h
  have h1 : ((1 : ℕ) : ZMod n) = 0 := by simpa using h
  have h2 := (ZMod.natCast_eq_zero_iff 1 n).1 h1
  exact hn (Nat.dvd_one.1 h2)
theorem period_zero_ne_one (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (i : Fin 4) :
    F.period 0 i ≠ 1 := by
  unfold BlockFrame.period
  have hL : 1 ≤ F.blockSide ^ (F.top - 0) := Nat.one_le_pow _ _ hodd.pos
  rcases hamb with h | h
  · rw [h i]
    simp
  · have := h i
    nlinarith
theorem unitStep_apply (μ i : Fin 4) : (unitStep (F := F) 0 μ) i = if i = μ then 1 else 0 := by
  simp only [unitStep, siteOfCoords]
  by_cases h : i = μ
  · subst h
    simp
  · simp [h]
theorem card_plaquetteCorners (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (x : F.Site 0)
    {μ ν : Fin 4} (hμν : μ ≠ ν) :
    (plaquetteCorners (x, μ, ν)).card = 4 := by
  have h1 := zmod_one_ne_zero_of_ne_one (period_zero_ne_one hamb hodd μ)
  have h2 := zmod_one_ne_zero_of_ne_one (period_zero_ne_one hamb hodd ν)
  have a0 : unitStep (F := F) 0 μ ≠ 0 := fun h => h1 (by simpa [unitStep_apply] using congrFun h μ)
  have b0 : unitStep (F := F) 0 ν ≠ 0 := fun h => h2 (by simpa [unitStep_apply] using congrFun h ν)
  have ab0 : unitStep (F := F) 0 μ + unitStep 0 ν ≠ 0 := fun h => h1 (by
    simpa [unitStep_apply, hμν] using congrFun h μ)
  have ab : unitStep (F := F) 0 μ ≠ unitStep 0 ν := fun h => h1 (by
    simpa [unitStep_apply, hμν] using congrFun h μ)
  simp only [plaquetteCorners]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    intro h
    apply a0
    have : x + unitStep 0 ν + unitStep 0 μ = x + unitStep 0 ν + 0 := by
      rw [add_zero, add_right_comm]
      exact h.symm
    exact add_left_cancel this
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => ab (add_left_cancel h), fun h => b0 ?_⟩
    have : x + unitStep 0 μ + 0 = x + unitStep 0 μ + unitStep 0 ν := by simpa using h
    exact (add_left_cancel this).symm
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => a0 ?_, fun h => b0 ?_, fun h => ab0 ?_⟩
    · have : x + 0 = x + unitStep 0 μ := by simpa using h
      exact (add_left_cancel this).symm
    · have : x + 0 = x + unitStep 0 ν := by simpa using h
      exact (add_left_cancel this).symm
    · have : x + 0 = x + (unitStep 0 μ + unitStep 0 ν) := by simpa [add_assoc] using h
      exact (add_left_cancel this).symm
theorem sum_plaquette_weights_eq_one (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0) [DecidableEq F.Cell] :
    ∑ Y ∈ S, ∑ x ∈ plaquetteCorners p, (if enclosingCell x = Y then (1 / 4 : ℝ) else 0) = 1 := by
  have hf := Finset.mem_filter.1 hp
  rw [Finset.sum_comm]
  have e : ∀ x ∈ plaquetteCorners p,
      ∑ Y ∈ S, (if enclosingCell x = Y then (1 / 4 : ℝ) else 0) = 1 / 4 := by
    intro x hx
    rw [Finset.sum_ite_eq, if_pos (LocalPartition.enclosingCell_mem hodd (hf.2.2 hx))]
  rw [Finset.sum_congr rfl e, Finset.sum_const]
  obtain ⟨x, μ, ν⟩ := p
  have hne : μ ≠ ν := ne_of_lt hf.2.1
  rw [card_plaquetteCorners hamb hodd x hne]
  norm_num
theorem sum_bond_weights_eq_one (hodd : Odd F.blockSide) {j : ℕ} {c : F.Site j × Fin 4}
    (hc : c ∈ innerBonds S j) [DecidableEq F.Cell] :
    ∑ Y ∈ S, ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
      (if enclosingCell (c.1 + unitStep j c.2) = Y then (1 / 2 : ℝ) else 0)) = 1 := by
  have hb := Finset.mem_filter.1 hc
  have h1 : c.1 ∈ sitesOfCells S j := (Finset.mem_product.1 hb.1).1
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq,
    if_pos (LocalPartition.enclosingCell_mem hodd h1), if_pos (LocalPartition.enclosingCell_mem hodd hb.2)]
  norm_num
end GaugedCellShareSum
theorem gaugedCellShareSumStatement_holds : gaugedCellShareSumStatement := by
  classical
  intro F a S X k hamb hodd
  unfold gaugedChainAction gaugedCellShare wilsonAction
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_mul, GaugedCellShareSum.sum_plaquette_weights_eq_one hamb hodd hp, one_mul]
  · congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [← Finset.sum_mul, GaugedCellShareSum.sum_bond_weights_eq_one hodd hc, one_mul]
end YangMills.Construction.BlockAverages
end
