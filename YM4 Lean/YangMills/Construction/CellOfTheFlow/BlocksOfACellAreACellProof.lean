import YangMills.Construction.CellOfTheFlow.BlocksOfACellAreACell
import YangMills.Construction.ClusterExpansionOfAStep.BlocksOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellWindows
private theorem mem_cell_iff (G : CellGrid) (n : ℕ) [NeZero n] (κ : Fin 4 → ℤ) (x : TorusFields.TorusSite n) :
    x ∈ G.cell n κ ↔ ∃ h : Fin 4 → ℤ, (∀ i, 0 ≤ h i ∧ h i < G.side) ∧
      x = TorusFields.siteOfInt fun i => G.offset i + (G.side : ℤ) * κ i + h i := by
  classical
  unfold CellGrid.cell
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
private theorem mem_refine_cell_iff (L : ℕ) (G : CellGrid) (n : ℕ) [NeZero n] (κ : Fin 4 → ℤ)
    (x : TorusFields.TorusSite n) :
    x ∈ (G.refine L).cell n κ ↔ ∃ h : Fin 4 → ℤ, (∀ i, 0 ≤ h i ∧ h i < ((G.side * L : ℕ) : ℤ)) ∧
      x = TorusFields.siteOfInt fun i =>
        (L : ℤ) * G.offset i - ((L : ℤ) - 1) / 2 + ((G.side * L : ℕ) : ℤ) * κ i + h i :=
  mem_cell_iff (G.refine L) n κ x
theorem cellBlocksEqRefinedCell : cellBlocksEqRefinedCellStatement := by
  classical
  intro L _ G n _ κ
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  ext x
  rw [mem_refine_cell_iff]
  have hbl : x ∈ TorusLumps.sitesInBlocks L (G.cell n κ) ↔ TorusLumps.parentBlock L x ∈ G.cell n κ := by
    unfold TorusLumps.sitesInBlocks
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hbl, mem_cell_iff]
  constructor
  · rintro ⟨h, hb, hx⟩
    refine ⟨fun i => (L : ℤ) * h i + (((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) % (L : ℤ), fun i => ?_, ?_⟩
    · have h0 := Int.emod_nonneg (((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) hL.ne'
      have h1 := Int.emod_lt_of_pos (((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) hL
      obtain ⟨a, b⟩ := hb i
      constructor
      · have := mul_nonneg hL.le a
        dsimp only
        omega
      · have h2 : h i + 1 ≤ (G.side : ℤ) := b
        have h3 := mul_le_mul_of_nonneg_left h2 hL.le
        dsimp only
        push_cast
        nlinarith
    · funext i
      have hi : ((((((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ)) : ZMod n) =
          ((G.offset i + (G.side : ℤ) * κ i + h i : ℤ) : ZMod n) := congrFun hx i
      obtain ⟨w, hw⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).1 hi
      have hdiv := Int.emod_add_mul_ediv (((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) (L : ℤ)
      have hcast : x i = ((((x i).cast : ℤ)) : ZMod (n * L)) := (ZMod.intCast_zmod_cast (x i)).symm
      show x i = ((_ : ℤ) : ZMod (n * L))
      rw [hcast]
      refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (n * L)).2 ⟨w, ?_⟩
      push_cast
      linear_combination (L : ℤ) * hw + hdiv
  · rintro ⟨h, hb, hx⟩
    refine ⟨fun i => h i / (L : ℤ), fun i => ?_, ?_⟩
    · obtain ⟨a, b⟩ := hb i
      refine ⟨Int.ediv_nonneg a hL.le, Int.ediv_lt_of_lt_mul hL ?_⟩
      have : h i < ((G.side * L : ℕ) : ℤ) := b
      simpa using this
    · subst hx
      funext i
      rw [TorusBlocks.parentBlock_siteOfInt]
      show _ = ((G.offset i + (G.side : ℤ) * κ i + h i / (L : ℤ) : ℤ) : ZMod n)
      congr 1
      have e : (L : ℤ) * G.offset i - ((L : ℤ) - 1) / 2 + ((G.side * L : ℕ) : ℤ) * κ i + h i +
          ((L : ℤ) - 1) / 2 = h i + (L : ℤ) * (G.offset i + (G.side : ℤ) * κ i) := by
        push_cast
        ring
      rw [e, Int.add_mul_ediv_left _ _ hL.ne']
      ring
end YangMills.Construction.CellWindows
end
