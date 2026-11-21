import YangMills.Construction.ClusterExpansionOfAStep.PlainFitsOfNearFieldsProof
import YangMills.Construction.ClusterExpansionOfAStep.TheMeanReadsItsTwoBlocks
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ContourMean
open BlockAverages LumpContours TorusLumps TorusContours ContourOffsets
variable {F : BlockFrame} [∀ j i, NeZero (F.period j i)]
theorem excludedBoxes_congr {J₀ : ℕ} {h h' : Finset (Finset (F.Site F.depth))} {z : F.Cell}
    (e : nearbyLumps h z = nearbyLumps h' z) : excludedBoxes J₀ h z = excludedBoxes J₀ h' z := by
  unfold excludedBoxes IsCrowded
  rw [e]
theorem contourPath_congr {b b' : F.Cell → F.Site F.depth} {y : F.Cell} {i : Fin 4} (hy : b y = b' y)
    (hy' : b (y + unitStep F.top i) = b' (y + unitStep F.top i)) (ξ : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    contourPath b (y, i) ξ π = contourPath b' (y, i) ξ π := by
  simp only [contourPath, hy, hy']
theorem usedContours_congr {J₀ : ℕ} {h h' : Finset (Finset (F.Site F.depth))} {b b' : F.Cell → F.Site F.depth}
    {y : F.Cell} {i : Fin 4} (hl : nearbyLumps h y = nearbyLumps h' y)
    (hl' : nearbyLumps h (y + unitStep F.top i) = nearbyLumps h' (y + unitStep F.top i))
    (hy : b y = b' y) (hy' : b (y + unitStep F.top i) = b' (y + unitStep F.top i)) :
    usedContours J₀ h b (y, i) = usedContours J₀ h' b' (y, i) := by
  classical
  have hg : ∀ ξ π, IsGoodContour J₀ h b (y, i) ξ π ↔ IsGoodContour J₀ h' b' (y, i) ξ π := by
    intro ξ π
    unfold IsGoodContour
    simp only []
    rw [contourPath_congr hy hy', hy, excludedBoxes_congr hl, excludedBoxes_congr hl']
  have hc : IsCrowded J₀ h y ↔ IsCrowded J₀ h' y := by simp only [IsCrowded, hl]
  have hc' : IsCrowded J₀ h (y + unitStep F.top i) ↔ IsCrowded J₀ h' (y + unitStep F.top i) := by
    simp only [IsCrowded, hl']
  unfold usedContours
  simp only [hg, hc, hc']
theorem fst_mem_centredCube_of_mem_usedContours {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))}
    {b : F.Cell → F.Site F.depth} {c : F.Cell × Fin 4}
    {e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)} (he : e ∈ usedContours J₀ h b c) : e.1 ∈ centredCube F.blockSide := by
  classical
  unfold usedContours at he
  split_ifs at he
  · exact (Finset.mem_product.mp he).1
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
theorem siteAtOffset_mem_sitesBelow_of_inSlab {y : F.Cell} {i : Fin 4} {u : Fin 4 → ℤ}
    (hu : InSlab F.blockSide i u) (hL : Odd F.blockSide) :
    (siteAtOffset y u : F.Site F.depth) ∈ sitesBelow F.depth y ∨
      (siteAtOffset y u : F.Site F.depth) ∈ sitesBelow F.depth (y + unitStep F.top i) := by apply _root_.YangMills.Construction.NearFields.siteAtOffset_mem_sitesBelow_of_inSlab <;> assumption
theorem siteAtOffset_add_unitStep {y : F.Cell} (i k : Fin 4) (u : Fin 4 → ℤ) :
    (siteAtOffset y u : F.Site F.depth) + unitStep F.depth k = siteAtOffset y (u + Pi.single k 1) := by
  simp only [siteAtOffset, unitStep, _root_.YangMills.Construction.TorusContours.siteOfCoords_add, add_assoc]
end YangMills.Construction.ContourMean
namespace YangMills.Construction.TorusLumps
open BlockAverages LumpContours TorusContours ContourOffsets ContourMean
theorem contourMeanReadsTwoBlocks_holds : ContourMeanReadsTwoBlocks := by
  intro L n J₀ _ _ hodd h16 h h' b b' W W' y i l₀ l₁ e₀ m₀ e₁ m₁ hW
  classical
  obtain ⟨z₀, h₀, hz₀⟩ := (_root_.YangMills.Construction.TorusContours.mem_sitesBelow_iff (F := stepBlockFrame L n) y _).mp m₀
  obtain ⟨z₁, h₁, hz₁⟩ := (_root_.YangMills.Construction.TorusContours.mem_sitesBelow_iff (F := stepBlockFrame L n) _ _).mp m₁
  have hbig : ∀ k, 2 * ((stepBlockFrame L n).blockSide : ℤ) ≤
      ((stepBlockFrame L n).period (stepBlockFrame L n).depth k : ℤ) := by
    intro k
    show 2 * (L : ℤ) ≤ ((stepBlockFrame L n).period 0 k : ℤ)
    rw [stepBlockFrame_period_zero]
    push_cast
    have h1 : (16 : ℤ) ≤ n := by exact_mod_cast h16
    have h2 : (0 : ℤ) ≤ L := by positivity
    nlinarith
  unfold contourMean
  rw [usedContours_congr (F := stepBlockFrame L n) (h' := h') (b' := b') l₀ l₁ e₀ e₁]
  refine congrArg _ (Finset.sum_congr rfl fun e he => ?_)
  have hξ := fst_mem_centredCube_of_mem_usedContours (F := stepBlockFrame L n) he
  have hs := contourPath_eq_contourSteps (F := stepBlockFrame L n) hbig (b := b) (y := y) (i := i)
    h₀ h₁ hξ hz₀ hz₁ e.2
  have hs' := contourPath_eq_contourSteps (F := stepBlockFrame L n) hbig (b := b') (y := y) (i := i)
    h₀ h₁ hξ (e₀ ▸ hz₀) (e₁ ▸ hz₁) e.2
  simp only []
  rw [hs, hs', ← e₀, hz₀]
  refine congrArg Subtype.val (pathHolonomy_eq_of_agree (F := stepBlockFrame L n) (F' := stepBlockFrame L n)
    (InSlab L i) W W' y y ?_ _ z₀ (contourSteps_inSlab h₀ h₁ hξ e.2 i))
  intro u k hu hu'
  have h3 := siteAtOffset_mem_sitesBelow_of_inSlab (F := stepBlockFrame L n) (y := y) hu' hodd
  rw [← siteAtOffset_add_unitStep (F := stepBlockFrame L n) (y := y) i k u] at h3
  exact hW _ k (siteAtOffset_mem_sitesBelow_of_inSlab (F := stepBlockFrame L n) hu hodd) h3
end YangMills.Construction.TorusLumps
end
