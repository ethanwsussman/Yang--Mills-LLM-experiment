import YangMills.Construction.ColdStepAtMirrorFrames.BlocksCoverTheLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentialOfTheLieAlgebra
import YangMills.Construction.ColdStepAtMirrorFrames.OneLeastChart
import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import YangMills.Construction.HoleBesideASecondHole.CutActionIsTheLeastActionProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace MinimizingChart
theorem mem_centredCube_iff {L : ℕ} (h : Fin 4 → ℤ) :
    h ∈ centredCube L ↔ ∀ i, -(((L : ℤ) - 1) / 2) ≤ h i ∧ h i ≤ ((L : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
theorem siteOfCoords_add {j : ℕ} (a b : Fin 4 → ℤ) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_zero {j : ℕ} : (siteOfCoords j (0 : Fin 4 → ℤ) : F.Site j) = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem isAxialTreeBond_of_offset (hS : SiteDecomposition) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (o : Fin 4 → ℤ) (ho : o ∈ centredCube F.blockSide) (i : Fin 4)
    (h1 : o i ≠ ((F.blockSide : ℤ) - 1) / 2) (h2 : ∀ l, i < l → o l = 0) :
    IsAxialTreeBond (cellCentre F.depth z + siteOfCoords F.depth o, i) := by
  have hoff := ((hS F hL hs).1 z o ho).2
  unfold IsAxialTreeBond
  simp only
  constructor
  · rw [(hS F hL hs).2.2.1, hoff]
    exact h1
  · intro l hl
    rw [hoff]
    exact h2 l hl
def offsetNorm (o : Fin 4 → ℤ) : ℕ := ∑ l, (o l).natAbs
theorem exists_last_ne_zero (o : Fin 4 → ℤ) (h : o ≠ 0) :
    ∃ i, o i ≠ 0 ∧ ∀ l, i < l → o l = 0 := by
  classical
  have hne : (Finset.univ.filter fun l => o l ≠ 0).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hc
    apply h
    funext l
    simpa using hc (Finset.mem_univ l)
  refine ⟨(Finset.univ.filter fun l => o l ≠ 0).max' hne, ?_, fun l hl => ?_⟩
  · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  · by_contra hc
    exact absurd (Finset.le_max' _ l (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hc⟩)) (not_le.mpr hl)
theorem offsetNorm_add_single_neg_one (o : Fin 4 → ℤ) (i : Fin 4) (h : 0 < o i) :
    offsetNorm (o + Pi.single i (-1)) + 1 = offsetNorm o := by
  unfold offsetNorm
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase (a := i) _ (fun l => (o l).natAbs) (Finset.mem_univ i)]
  have e : ∑ l ∈ Finset.univ.erase i, ((o + Pi.single i (-1) : Fin 4 → ℤ) l).natAbs =
      ∑ l ∈ Finset.univ.erase i, (o l).natAbs := by
    refine Finset.sum_congr rfl fun l hl => ?_
    have hne : l ≠ i := (Finset.mem_erase.mp hl).1
    simp [Pi.single_eq_of_ne hne]
  rw [e]
  simp only [Pi.add_apply, Pi.single_eq_same]
  omega
theorem offsetNorm_add_single_one (o : Fin 4 → ℤ) (i : Fin 4) (h : o i < 0) :
    offsetNorm (o + Pi.single i 1) + 1 = offsetNorm o := by
  unfold offsetNorm
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase (a := i) _ (fun l => (o l).natAbs) (Finset.mem_univ i)]
  have e : ∑ l ∈ Finset.univ.erase i, ((o + Pi.single i 1 : Fin 4 → ℤ) l).natAbs =
      ∑ l ∈ Finset.univ.erase i, (o l).natAbs := by
    refine Finset.sum_congr rfl fun l hl => ?_
    have hne : l ≠ i := (Finset.mem_erase.mp hl).1
    simp [Pi.single_eq_of_ne hne]
  rw [e]
  simp only [Pi.add_apply, Pi.single_eq_same]
  omega
theorem eq_zero_of_offsetNorm_eq_zero (o : Fin 4 → ℤ) (h : offsetNorm o = 0) : o = 0 := by
  funext l
  have h1 : (o l).natAbs ≤ offsetNorm o :=
    Finset.single_le_sum (f := fun l => (o l).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  simpa [h] using h1
theorem gauge_eq_one_of_tree (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (γ : F.Site F.depth → UnitQuaternion)
    (h1 : ∀ z, γ (cellCentre F.depth z) = 1)
    (htree : ∀ x i, IsAxialTreeBond (x, i) → γ x = γ (x + unitStep F.depth i)) (x : F.Site F.depth) :
    γ x = 1 := by
  obtain ⟨hx, ho⟩ := (hS F hL hs).2.1 x
  rw [← hx]
  obtain ⟨k, hk⟩ := hL
  have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hh : ((F.blockSide : ℤ) - 1) / 2 = k := by
    rw [hLz]
    omega
  have main : ∀ (n : ℕ) (z : F.Cell) (o : Fin 4 → ℤ), o ∈ centredCube F.blockSide → offsetNorm o = n →
      γ (cellCentre F.depth z + siteOfCoords F.depth o) = 1 := by
    intro n
    induction n with
    | zero =>
      intro z o _ hn
      rw [eq_zero_of_offsetNorm_eq_zero o hn, siteOfCoords_zero, add_zero]
      exact h1 z
    | succ n ih =>
      intro z o ho hn
      have hne : o ≠ 0 := by
        intro h0
        rw [h0] at hn
        simp [offsetNorm] at hn
      obtain ⟨i, hi, htop⟩ := exists_last_ne_zero o hne
      have hc := (mem_centredCube_iff o).mp ho
      rcases lt_or_gt_of_ne hi with hneg | hpos
      · have ho' : o + Pi.single i 1 ∈ centredCube F.blockSide := by
          rw [mem_centredCube_iff]
          intro l
          by_cases hl : l = i
          · subst hl
            have := hc l
            simp only [Pi.add_apply, Pi.single_eq_same]
            omega
          · simpa [Pi.single_eq_of_ne hl] using hc l
        have hsz := offsetNorm_add_single_one o i hneg
        have htr := isAxialTreeBond_of_offset hS ⟨k, hk⟩ hs z o ho i
          (by
            rw [hh]
            have : (0 : ℤ) ≤ k := by positivity
            omega) htop
        have e := htree _ _ htr
        have e2 : (cellCentre F.depth z + siteOfCoords F.depth o + unitStep F.depth i : F.Site F.depth) =
            cellCentre F.depth z + siteOfCoords F.depth (o + Pi.single i 1) := by
          rw [siteOfCoords_add, add_assoc]
          rfl
        rw [e, e2]
        exact ih z _ ho' (by omega)
      · have ho' : o + Pi.single i (-1) ∈ centredCube F.blockSide := by
          rw [mem_centredCube_iff]
          intro l
          by_cases hl : l = i
          · subst hl
            have := hc l
            simp only [Pi.add_apply, Pi.single_eq_same]
            omega
          · simpa [Pi.single_eq_of_ne hl] using hc l
        have hsz := offsetNorm_add_single_neg_one o i hpos
        have htr := isAxialTreeBond_of_offset hS ⟨k, hk⟩ hs z (o + Pi.single i (-1)) ho' i
          (by
            have := hc i
            simp only [Pi.add_apply, Pi.single_eq_same]
            rw [hh]
            omega)
          (fun l hl => by
            have hne : l ≠ i := ne_of_gt hl
            simp [Pi.single_eq_of_ne hne, htop l hl])
        have e := htree _ _ htr
        have e2 : (cellCentre F.depth z + siteOfCoords F.depth (o + Pi.single i (-1)) + unitStep F.depth i :
            F.Site F.depth) = cellCentre F.depth z + siteOfCoords F.depth o := by
          rw [siteOfCoords_add, add_assoc, add_assoc]
          congr 1
          have e3 : (siteOfCoords F.depth (Pi.single i (-1)) + unitStep F.depth i : F.Site F.depth) = 0 := by
            funext l
            by_cases hl : l = i
            · subst hl
              simp [siteOfCoords, unitStep]
            · simp [siteOfCoords, unitStep, Pi.single_eq_of_ne hl]
          rw [e3, add_zero]
        rw [← e2, ← e]
        exact ih z _ ho' (by omega)
  exact main _ _ _ ho rfl
end MinimizingChart
open MinimizingChart in
theorem minimizingChartUnique_holds (hcover : BlocksCoverLowerLevel) (hS : SiteDecomposition)
    (hexp : QuaternionExp.ExpUnitLipschitzInjective) : MinimizingChartUnique := by
  classical
  intro F a ρ N0 s V w hL hs hρ hOne hw
  obtain ⟨w₀, h₀, hcold, huniq⟩ := hOne
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hbond : ∀ b : F.Site F.depth × Fin 4, b ∈ innerBonds (finiteCells F) F.depth := by
    intro b
    unfold innerBonds
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hcover F hL hs0 _, hcover F hL hs0 _⟩
  have key : ∀ u, IsMinimizingChart a (finiteCells F) V ρ u → u = w₀ := by
    intro u hu
    obtain ⟨γ, hγ1, hsame⟩ := huniq (chartedField u V) hu.2.2
    have hγ : ∀ x, γ x = 1 := gauge_eq_one_of_tree hS hL hs γ hγ1 (fun x i ht => by
      have h1 := hsame (x, i) (hbond _)
      have hcr : ¬ IsCrossingBond (x, i) := ht.1
      simp only [gaugeTransform, chartedField, if_neg hcr, if_pos ht, mul_one] at h1
      exact (mul_inv_eq_one.mp h1.symm))
    have hfield : ∀ x i, chartedField u V x i = chartedField w₀ V x i := by
      intro x i
      have h1 := hsame (x, i) (hbond _)
      simp only [gaugeTransform, hγ, one_mul, inv_one, mul_one] at h1
      exact h1
    funext x i
    by_cases hb : (x, i) ∈ chordBonds (finiteCells F)
    · have hu1 := hu.2.1 _ hb
      have hw1 : ‖w₀ x i‖ ≤ ρ := (h₀.2.1 _ hb).trans (min_le_left _ _)
      have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
      apply hexp.2 _ _ (by simp only at hu1; linarith) (by linarith)
      have h1 := hfield x i
      unfold chartedField at h1
      by_cases hcr : IsCrossingBond (x, i)
      · simp only [if_pos hcr] at h1
        exact mul_right_cancel h1
      · have ht : ¬ IsAxialTreeBond (x, i) := (Finset.mem_filter.mp hb).2
        simp only [if_neg hcr, if_neg ht] at h1
        exact h1
    · have e1 := hu.1 (x, i) hb
      have e2 := h₀.1 (x, i) hb
      simp only at e1 e2
      rw [e1, e2]
  refine ⟨fun w' hw' => (key w' hw').trans (key w hw).symm, ?_⟩
  rw [key w hw]
  exact hcold
end ColdStepAtMirrorFrames
end YangMills.Construction
end
