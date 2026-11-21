import YangMills.Construction.ColdChainAtEveryLevel.ComplexCells
import YangMills.Construction.ColdChainAtEveryLevel.TermsAgainstTheirFirstOrderProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame} {j : ℕ}
theorem enclosingCell_top (x : F.Site F.top) : enclosingCell x = x := by apply _root_.YangMills.Construction.BlockAverages.TermwiseBounds.enclosingCell_top <;> assumption
theorem card_bondsOver_singleton_top_le {S : Finset F.Cell} {z : F.Cell} {k : ℕ} (hk : k = F.top) :
    (bondsOver S {z} k).card ≤ 4 := by
  classical
  subst hk
  have hinj : Set.InjOn (fun c : F.Site F.top × Fin 4 => c.2) (bondsOver S {z} F.top : Finset _) := by
    intro c hc c' hc' e
    have h1 := Finset.mem_singleton.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
    have h2 := Finset.mem_singleton.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hc')).2
    have t1 : enclosingCell c.1 = c.1 := enclosingCell_top c.1
    have t2 : enclosingCell c'.1 = c'.1 := enclosingCell_top c'.1
    exact Prod.ext (by rw [← t1, ← t2, h1, h2]) e
  have := Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
  simpa using this
section Assembly
theorem bondsOver_singleton_subset_innerBonds (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    {S : Finset F.Cell} {z : F.Cell} {k : ℕ} (hk : k ≤ F.top) :
    bondsOver S {z} k ⊆ innerBonds (cellBall S z 1) k := fun _ hb =>
  BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hamb hL S z hk hb
theorem norm_complexCellTerms_second_diff_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (a : ℝ)
    (S : Finset F.Cell) (z : F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top)
    (W₀ W₁ W₂ W₃ : ComplexChainChart F) {Tb : ℝ} (hTb0 : 0 ≤ Tb)
    (htop : ∀ j, j + 1 = F.top → ∑ c ∈ bondsOver S {z} (j + 1),
      ‖complexBondTerm R W₃ V j c - complexBondTerm R W₁ V j c - complexBondTerm R W₂ V j c +
        complexBondTerm R W₀ V j c‖ ≤ Tb) :
    ‖complexCellTerms a S R W₃ V z - complexCellTerms a S R W₁ V z - complexCellTerms a S R W₂ V z +
        complexCellTerms a S R W₀ V z‖ ≤
      ∑ q ∈ plaquettesOver S {z} 0,
        ‖complexPlaquetteTerm (complexChartField R W₃ 0) q - complexPlaquetteTerm (complexChartField R W₁ 0) q -
          complexPlaquetteTerm (complexChartField R W₂ 0) q + complexPlaquetteTerm (complexChartField R W₀ 0) q‖ +
      |a| * (∑ x ∈ ComplexCells.lowerBonds (cellBall S z 1), ‖complexBondTerm R W₃ V x.1 x.2 -
        complexBondTerm R W₁ V x.1 x.2 - complexBondTerm R W₂ V x.1 x.2 + complexBondTerm R W₀ V x.1 x.2‖ + Tb) := by
  set D := cellBall S z 1 with hD
  set g : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℂ := fun j c =>
    complexBondTerm R W₃ V j c - complexBondTerm R W₁ V j c - complexBondTerm R W₂ V j c +
      complexBondTerm R W₀ V j c with hg
  have e : complexCellTerms a S R W₃ V z - complexCellTerms a S R W₁ V z - complexCellTerms a S R W₂ V z +
      complexCellTerms a S R W₀ V z =
      ∑ q ∈ plaquettesOver S {z} 0,
        (complexPlaquetteTerm (complexChartField R W₃ 0) q - complexPlaquetteTerm (complexChartField R W₁ 0) q -
          complexPlaquetteTerm (complexChartField R W₂ 0) q + complexPlaquetteTerm (complexChartField R W₀ 0) q) +
      (a : ℂ) * ∑ j ∈ Finset.range F.top, ∑ c ∈ bondsOver S {z} (j + 1), g j c := by
    simp only [complexCellTerms, hg, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hlev : ‖∑ j ∈ Finset.range F.top, ∑ c ∈ bondsOver S {z} (j + 1), g j c‖ ≤
      ∑ j ∈ Finset.range F.top, ∑ c ∈ bondsOver S {z} (j + 1), ‖g j c‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
  refine hlev.trans ?_
  have hmid : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S {z} (j + 1), ‖g j c‖ ≤
      ∑ x ∈ ComplexCells.lowerBonds D, ‖g x.1 x.2‖ := by
    rw [ComplexCells.lowerBonds, Finset.sum_sigma]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    exact Finset.sum_le_sum_of_subset_of_nonneg (bondsOver_singleton_subset_innerBonds hamb hodd (by omega))
      fun _ _ _ => norm_nonneg _
  have hn0 : 0 ≤ ∑ x ∈ ComplexCells.lowerBonds D, ‖g x.1 x.2‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rcases Nat.eq_zero_or_pos F.top with h0 | hpos
  · rw [h0]
    simp only [Finset.range_zero, Finset.sum_empty]
    linarith
  · have hins : Finset.range F.top = insert (F.top - 1) (Finset.range (F.top - 1)) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp)]
    have ht := htop (F.top - 1) (by omega)
    linarith
end Assembly
end YangMills.Construction.BlockAverages
end
