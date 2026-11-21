import YangMills.Construction.ClusterExpansionOfAStep.ContoursFromBases
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsPlainFarFromLumps
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusLumps.AwayFromLumps
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.TorusLumps YangMills.Construction.TorusContours
section
variable {F : BlockFrame} [∀ j i, NeZero (F.period j i)]
theorem valMinAbs_intCast_of_two_mul_abs_lt {p : ℕ} [NeZero p] {z : ℤ} (hz : 2 * |z| < (p : ℤ)) :
    ((z : ZMod p)).valMinAbs = z := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
theorem minimalOffset_cellCentre_add (hL : 1 ≤ F.blockSide) (z : F.Cell) {ξ : Fin 4 → ℤ}
    (hξ : ξ ∈ centredCube F.blockSide) :
    minimalOffset (cellCentre F.depth z : F.Site F.depth) (cellCentre F.depth z + siteOfCoords F.depth ξ) = ξ := by
  funext k
  have hmem := mem_centredCube_iff.mp hξ k
  have hside : (F.blockSide : ℤ) ≤ (F.period F.depth k : ℤ) := by
    rw [period_depth]
    have hone : 1 ≤ F.period F.top k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
    push_cast
    nlinarith
  have hlt : 2 * |ξ k| < (F.period F.depth k : ℤ) := by
    have habs : |ξ k| ≤ ((F.blockSide : ℤ) - 1) / 2 := abs_le.mpr ⟨hmem.1, hmem.2⟩
    omega
  show (((cellCentre F.depth z + siteOfCoords F.depth ξ - cellCentre F.depth z : F.Site F.depth) k)).valMinAbs = ξ k
  rw [add_sub_cancel_left]
  exact valMinAbs_intCast_of_two_mul_abs_lt hlt
theorem mergedBoxes_empty {j : ℕ} : mergedBoxes (∅ : Finset (Finset (F.Site j))) = ∅ := by
  classical
  unfold mergedBoxes
  split_ifs with hex
  · have hs := hex.choose_spec
    refine Finset.eq_empty_of_forall_notMem fun B hB => ?_
    have hc : IsSeparatedCover (∅ : Finset (Finset (F.Site j))) (∅ : Finset (Finset (F.Site j))) :=
      ⟨by simp, by simp, by simp⟩
    obtain ⟨B', hB', -⟩ := hs.2 ∅ hc B hB
    simp at hB'
  · rfl
theorem excludedBoxes_eq_empty {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))} {z : F.Cell}
    (hz : nearbyLumps h z = ∅) : excludedBoxes J₀ h z = ∅ := by
  classical
  unfold excludedBoxes
  split_ifs
  · rfl
  · rw [hz, Finset.image_empty, mergedBoxes_empty]
theorem card_centredCube {L : ℕ} (hodd : Odd L) : (centredCube L).card = L ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem contourMean_eq_contourAverage (hL : 1 ≤ F.blockSide) (hodd : Odd F.blockSide) {J₀ : ℕ}
    {h : Finset (Finset (F.Site F.depth))}
    {b : F.Cell → F.Site F.depth} {y : F.Cell} {i : Fin 4} (W : F.GaugeField F.depth)
    (h₀ : nearbyLumps h y = ∅) (h₁ : nearbyLumps h (y + unitStep F.top i) = ∅)
    (hb₀ : b y = cellCentre F.depth y)
    (hb₁ : b (y + unitStep F.top i) = cellCentre F.depth (y + unitStep F.top i)) :
    contourMean J₀ h b W (y, i) = contourAverage (j := F.depth) W (y, i) := by
  classical
  have hgood : ∀ e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4), IsGoodContour J₀ h b (y, i) e.1 e.2 := by
    intro e x _ B hB
    simp only [] at hB
    rw [excludedBoxes_eq_empty h₀, excludedBoxes_eq_empty h₁] at hB
    simp at hB
  have hused : usedContours J₀ h b (y, i) = allContours F := by
    unfold usedContours
    rw [Finset.filter_true_of_mem fun e _ => hgood e]
    split_ifs <;> rfl
  have hcard : ((allContours F).card : ℝ) = 24 * (F.blockSide : ℝ) ^ 4 := by
    unfold allContours
    rw [Finset.card_product, card_centredCube hodd, Finset.card_univ, Fintype.card_perm]
    push_cast
    norm_num
    ring
  have hpath : ∀ ξ ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      contourPath b (y, i) ξ π = bondContour F.blockSide ξ π i := by
    intro ξ hξ π
    simp only [contourPath, bondContour, hb₀, hb₁, minimalOffset_cellCentre_add hL _ hξ]
  have hrefine : b y = refineSite (j := F.depth) y := by
    rw [hb₀, cellCentre_eq]
    rfl
  unfold contourMean contourAverage
  rw [hused, hcard]
  refine congrArg _ ?_
  unfold allContours
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun ξ hξ => Finset.sum_congr rfl fun π _ => ?_
  simp only []
  rw [hpath ξ hξ π, hrefine]
end
end YangMills.Construction.TorusLumps.AwayFromLumps
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
  YangMills.Construction.TorusContours AwayFromLumps
theorem kernelPlainAwayFromLumps_holds : KernelPlainAwayFromLumps := by
  intro ℓ hfit n _ W y i h₀ h₁
  classical
  have hL : 1 ≤ ℓ.side := by have := hfit.L_ge; omega
  refine ⟨?_, fun x V b hb => ?_⟩
  · unfold baseSitesAt
    rw [if_pos (Or.inl h₀)]
    rfl
  · have hbase : IsBaseChoice ℓ.baseDepth (fineHotLumps ℓ W) b := (Finset.mem_filter.mp hb).2
    have hmean := contourMean_eq_contourAverage (F := stepBlockFrame ℓ.side n) hL hfit.L_odd
      (J₀ := ℓ.baseDepth) (b := b) W h₀ h₁ ((hbase y).1 (Or.inl h₀)) ((hbase _).1 (Or.inl h₁))
    refine ⟨hmean, ?_, ?_⟩
    · unfold contourFit blockFit
      rw [hmean]
      rfl
    · rw [bondKernel_eq_meanKernel, hmean]
      rfl
end YangMills.Construction.TorusLumps
end
