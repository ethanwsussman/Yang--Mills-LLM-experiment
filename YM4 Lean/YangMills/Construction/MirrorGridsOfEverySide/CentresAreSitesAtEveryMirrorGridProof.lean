import YangMills.Construction.MirrorGridsOfEverySide.CentresAreSitesAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.SideIsAnOddMultipleOfTheSpacingAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open ChessboardTori (ReflectionGrid)
namespace MirrorGridsAllSides
namespace CommonCentre
theorem cellSet_subset_of_cellCentre_eq {D : GridSetup} {g g' : ReflectionGrid D}
    (hs : g'.cellSide = g.cellSide) {k k' : Fin 4 → ℤ}
    (h : g.cellCentre k = g'.cellCentre k') : g.cellSet ⊆ g'.cellSet := by
  have hoff : ∀ μ, g.origin μ + g.cellSide * k μ = g'.origin μ + g.cellSide * k' μ := by
    intro μ
    have hμ := congrFun h μ
    simp only [ReflectionGrid.cellCentre, hs] at hμ
    linarith
  rintro _ ⟨j, rfl⟩
  refine ⟨j + k' - k, ?_⟩
  ext x
  simp only [ReflectionGrid.cell, mem_ofPred_eq, hs, Pi.add_apply, Pi.sub_apply]
  refine forall_congr' fun μ => ?_
  have hμ : g'.origin μ + g.cellSide * ((j μ + k' μ - k μ : ℤ) : ℝ) =
      g.origin μ + g.cellSide * (j μ : ℝ) := by
    push_cast
    linear_combination -(hoff μ)
  rw [hμ]
theorem cellSet_eq_of_cellCentre_eq {D : GridSetup} {g g' : ReflectionGrid D}
    (hs : g'.cellSide = g.cellSide) {k k' : Fin 4 → ℤ}
    (h : g.cellCentre k = g'.cellCentre k') : g.cellSet = g'.cellSet :=
  Subset.antisymm (cellSet_subset_of_cellCentre_eq hs h)
    (cellSet_subset_of_cellCentre_eq hs.symm h.symm)
end CommonCentre
theorem allGridsCellCentresInLattice_holds
    (h₁ : CellSideOddMultipleEveryGrid) :
    AllGridsCellCentresInLattice := by
  intro D g hg
  obtain ⟨⟨n, ⟨m, hm⟩, hn⟩, -⟩ := h₁ D g hg
  have ha : D.mesh ≠ 0 := by
    have h2 : D.mesh = (D.L : ℝ) ^ (-((D.K : ℕ) : ℤ)) := rfl
    rw [h2]
    exact (zpow_pos (zero_lt_one.trans D.one_lt_factor) _).ne'
  have hl : g.cellSide = (2 * (m : ℝ) + 1) * D.mesh := by
    have hn' : (n : ℝ) = 2 * (m : ℝ) + 1 := by
      rw [hm]
      push_cast
      ring
    rw [← hn', ← hn]
    field_simp
  refine ⟨fun k => ?_, fun x hx => ?_⟩
  · choose i hi using g.origin_mem
    refine ⟨fun μ => i μ + (2 * m + 1) * k μ + m + 1, fun μ => ?_⟩
    simp only [ReflectionGrid.cellCentre, hi μ, hl]
    push_cast
    ring
  · obtain ⟨j, hj⟩ := hx
    have hc : ∀ μ, ∃ i : ℤ, x μ - g.cellSide / 2 = D.mesh * ((i : ℝ) + 1 / 2) := by
      intro μ
      refine ⟨j μ - m - 1, ?_⟩
      rw [hj μ, hl]
      push_cast
      ring
    let g' : ReflectionGrid D := ⟨g.q, g.one_sub_K_le_q, fun μ => x μ - g.cellSide / 2, hc⟩
    have hs : g'.cellSide = g.cellSide := rfl
    have hcentre : g'.cellCentre 0 = x := by
      funext μ
      simp only [ReflectionGrid.cellCentre, hs]
      show x μ - g.cellSide / 2 + g.cellSide * ((0 : ℤ) : ℝ) + g.cellSide / 2 = x μ
      push_cast
      ring
    refine ⟨g'.cellSet, ⟨g', hs, rfl, 0, hcentre⟩, ?_⟩
    rintro _ ⟨g'', hs', rfl, k, hk⟩
    exact CommonCentre.cellSet_eq_of_cellCentre_eq (hs.trans hs'.symm) (hk.trans hcentre.symm)
end MirrorGridsAllSides
end YangMills.Construction
end
