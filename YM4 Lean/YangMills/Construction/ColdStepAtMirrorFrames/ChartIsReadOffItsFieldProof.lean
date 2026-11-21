import YangMills.Construction.ColdStepAtMirrorFrames.ChartIsReadOffItsField
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace ChartDeterminedByField
open BlockOffsets
variable {F : BlockFrame}
def blockSite (z : F.Cell) (u : Fin 4 → ℤ) : F.Site F.depth := cellCentre F.depth z + siteOfCoords F.depth u
theorem blockSite_add_unitStep (z : F.Cell) (u : Fin 4 → ℤ) (i : Fin 4) :
    blockSite z u + unitStep F.depth i = blockSite z (u + Pi.single i 1) := offset_add_unitStep z u i
theorem blockSite_zero (z : F.Cell) : blockSite z 0 = cellCentre F.depth z := by
  unfold blockSite
  funext l
  simp [siteOfCoords]
theorem isAxialTreeBond_blockSite (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    {u : Fin 4 → ℤ} (hu : u ∈ centredCube F.blockSide)
    (i : Fin 4) (hne : u i ≠ halfSide F.blockSide) (hz : ∀ l, i < l → u l = 0) :
    IsAxialTreeBond (blockSite z u, i) := by
  refine ⟨fun h => hne ((isCrossingBond_iff hL hs z u hu i).mp h), fun l hl => ?_⟩
  have e : cellOffset (blockSite z u) = u := cellOffset_offset hL hs z u hu
  simp only
  rw [e]
  exact hz l hl
theorem mem_innerBonds (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (b : F.Site F.depth × Fin 4) : b ∈ innerBonds (finiteCells F) F.depth := by
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    have := hs i
    omega
  unfold innerBonds
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hcover F hL hpos _, Finset.mem_univ _⟩, hcover F hL hpos _⟩
theorem exists_blockSite (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) : ∃ z, ∃ u ∈ centredCube F.blockSide, x = blockSite z u := by
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    have := hs i
    omega
  have h := hcover F hL hpos x
  unfold sitesOfCells at h
  obtain ⟨z, -, hz⟩ := Finset.mem_biUnion.mp h
  obtain ⟨u, hu, e⟩ := Finset.mem_image.mp hz
  rw [top_sub_depth, pow_one] at hu
  exact ⟨z, u, hu, e.symm⟩
theorem chartedField_eq_one {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    {b : F.Site F.depth × Fin 4} (ht : IsAxialTreeBond b) : chartedField w V b.1 b.2 = 1 := by
  unfold chartedField
  rw [if_neg ht.1, if_pos ht]
section gauge
variable (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
  {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
  {γ : F.Site F.depth → UnitQuaternion}
  (hsame : AgreeOnBonds (finiteCells F) F.depth (chartedField w' V) (gaugeTransform γ (chartedField w V)))
include hcover hL hs hsame
theorem gauge_eq_of_tree {b : F.Site F.depth × Fin 4} (ht : IsAxialTreeBond b) :
    γ b.1 = γ (b.1 + unitStep F.depth b.2) := by
  have h := hsame b (mem_innerBonds hcover hL hs b)
  unfold gaugeTransform at h
  rw [chartedField_eq_one ht, chartedField_eq_one ht, mul_one] at h
  exact (eq_of_mul_inv_eq_one h.symm)
theorem gauge_eq_one_along_axis (z : F.Cell) (i : Fin 4)
    (P : ∀ v ∈ centredCube F.blockSide, v i = 0 → (∀ l, i < l → v l = 0) → γ (blockSite z v) = 1) :
    ∀ u ∈ centredCube F.blockSide, (∀ l, i < l → u l = 0) → γ (blockSite z u) = 1 := by
  have key : ∀ (n : ℕ) (u : Fin 4 → ℤ), (u i).natAbs = n → u ∈ centredCube F.blockSide →
      (∀ l, i < l → u l = 0) → γ (blockSite z u) = 1 := by
    intro n
    induction n with
    | zero =>
      intro u hn hu hz
      exact P u hu (by omega) hz
    | succ n ih =>
      intro u hn hu hz
      have hc := (mem_centredCube_iff u).mp hu
      rcases lt_or_ge 0 (u i) with hp | hneg
      · set v : Fin 4 → ℤ := u - Pi.single i 1 with hv
        have hvi : v i = u i - 1 := by simp [hv]
        have hvl : ∀ l, l ≠ i → v l = u l := fun l hl => by simp [hv, Pi.single_eq_of_ne hl]
        have hvc : v ∈ centredCube F.blockSide := by
          rw [mem_centredCube_iff]
          intro l
          by_cases hl : l = i
          · subst hl
            have := hc l
            rw [hvi]
            omega
          · rw [hvl l hl]
            exact hc l
        have hvz : ∀ l, i < l → v l = 0 := fun l hl => by
          rw [hvl l (ne_of_gt hl)]
          exact hz l hl
        have h1 := ih v (by omega) hvc hvz
        have hne : v i ≠ halfSide F.blockSide := by
          have := (hc i).2
          omega
        have h2 := gauge_eq_of_tree hcover hL hs hsame (isAxialTreeBond_blockSite hL hs z hvc i hne hvz)
        simp only at h2
        rw [blockSite_add_unitStep] at h2
        have e : v + Pi.single i 1 = u := by simp [hv]
        rw [e] at h2
        rw [← h2, h1]
      · set v : Fin 4 → ℤ := u + Pi.single i 1 with hv
        have hvi : v i = u i + 1 := by simp [hv]
        have hvl : ∀ l, l ≠ i → v l = u l := fun l hl => by simp [hv, Pi.single_eq_of_ne hl]
        have hui : u i < 0 := by omega
        have hvc : v ∈ centredCube F.blockSide := by
          rw [mem_centredCube_iff]
          intro l
          by_cases hl : l = i
          · subst hl
            have := hc l
            rw [hvi]
            omega
          · rw [hvl l hl]
            exact hc l
        have hvz : ∀ l, i < l → v l = 0 := fun l hl => by
          rw [hvl l (ne_of_gt hl)]
          exact hz l hl
        have h1 := ih v (by omega) hvc hvz
        have hne : u i ≠ halfSide F.blockSide := by
          have := (hc i).1
          have := (hc i).2
          omega
        have h2 := gauge_eq_of_tree hcover hL hs hsame (isAxialTreeBond_blockSite hL hs z hu i hne hz)
        simp only at h2
        rw [blockSite_add_unitStep] at h2
        rw [h2, h1]
  intro u hu hz
  exact key _ u rfl hu hz
theorem gauge_eq_one (hc : ∀ z, γ (cellCentre F.depth z) = 1) (x : F.Site F.depth) : γ x = 1 := by
  obtain ⟨z, u, hu, rfl⟩ := exists_blockSite hcover hL hs x
  have g := gauge_eq_one_along_axis hcover hL hs hsame z
  have q0 : ∀ u ∈ centredCube F.blockSide, (∀ l, 0 < l → u l = 0) → γ (blockSite z u) = 1 :=
    g 0 fun v _ h0 hl => by
      have e : v = 0 := by
        funext l
        by_cases h : l = 0
        · rw [h]
          exact h0
        · exact hl l (Fin.pos_of_ne_zero h)
      rw [e, blockSite_zero]
      exact hc z
  have d1 : ∀ l : Fin 4, (0 : Fin 4) < l → l = 1 ∨ (1 : Fin 4) < l := by decide
  have d2 : ∀ l : Fin 4, (1 : Fin 4) < l → l = 2 ∨ (2 : Fin 4) < l := by decide
  have d3 : ∀ l : Fin 4, (2 : Fin 4) < l → l = 3 ∨ (3 : Fin 4) < l := by decide
  have q1 : ∀ u ∈ centredCube F.blockSide, (∀ l, 1 < l → u l = 0) → γ (blockSite z u) = 1 :=
    g 1 fun v hv h0 hl =>
      q0 v hv fun l hl0 => by
        rcases d1 l hl0 with e | e
        · rw [e]
          exact h0
        · exact hl l e
  have q2 : ∀ u ∈ centredCube F.blockSide, (∀ l, 2 < l → u l = 0) → γ (blockSite z u) = 1 :=
    g 2 fun v hv h0 hl =>
      q1 v hv fun l hl0 => by
        rcases d2 l hl0 with e | e
        · rw [e]
          exact h0
        · exact hl l e
  have q3 : ∀ u ∈ centredCube F.blockSide, (∀ l, 3 < l → u l = 0) → γ (blockSite z u) = 1 :=
    g 3 fun v hv h0 hl =>
      q2 v hv fun l hl0 => by
        rcases d3 l hl0 with e | e
        · rw [e]
          exact h0
        · exact hl l e
  have d4 : ∀ l : Fin 4, ¬ (3 : Fin 4) < l := by decide
  exact q3 u hu fun l hl => absurd hl (d4 l)
end gauge
end ChartDeterminedByField
open ChartDeterminedByField BlockOffsets in
theorem ChartDeterminedByField.of_blocksCover (hcover : BlocksCoverLowerLevel) :
    ChartDeterminedByField := by
  classical
  intro F w w' V γ hL hs h0 h0' h1 h1' hc hsame
  have hone := gauge_eq_one hcover hL hs hsame hc
  funext x i
  by_cases hb : (x, i) ∈ chordBonds (finiteCells F)
  · have h := hsame (x, i) (mem_innerBonds hcover hL hs _)
    simp only [gaugeTransform, hone, one_mul, inv_one, mul_one] at h
    have hnt : ¬ IsAxialTreeBond (x, i) := (Finset.mem_filter.mp hb).2
    unfold chartedField at h
    by_cases hcr : IsCrossingBond (x, i)
    · rw [if_pos hcr, if_pos hcr] at h
      exact expUnit_inj_of_norm_le_one (mul_right_cancel h) (h1' _ hb) (h1 _ hb)
    · rw [if_neg hcr, if_neg hcr, if_neg hnt, if_neg hnt] at h
      exact expUnit_inj_of_norm_le_one h (h1' _ hb) (h1 _ hb)
  · rw [show w' x i = 0 from h0' _ hb, show w x i = 0 from h0 _ hb]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
