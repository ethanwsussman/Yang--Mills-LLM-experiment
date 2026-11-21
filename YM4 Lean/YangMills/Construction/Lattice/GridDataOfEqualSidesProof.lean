import YangMills.Construction.LawInAState.GridDataAtEveryExponentProofForm
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open Matrices
open PeriodicLattice (torusSide meshSize pointOnAxis)
namespace EqualSideGrids
open CellGrid
variable {L m : ℕ} {κ : ℤ} {d : CellGrid L κ}
theorem spaceEquivTorus_isHomeomorph (h : d.HasEqualSides m) : IsHomeomorph (spaceEquivTorus h) := by
  have hP : IsOpenQuotientMap
      (Pi.map fun (_ : Fin 4) => (QuotientAddGroup.mk : ℝ → AddCircle (torusSide L m))) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  have hc : (spaceEquivTorus h) ∘ (BoxTorus.projection d.sideLengths) =
      Pi.map fun (_ : Fin 4) => (QuotientAddGroup.mk : ℝ → AddCircle (torusSide L m)) :=
    funext fun w => spaceEquivTorus_projection h w
  refine ⟨?_, ?_, (spaceEquivTorus h).bijective⟩
  · refine continuous_coinduced_dom.mpr ?_
    rw [hc]
    exact hP.continuous
  · intro O hO
    have himg : spaceEquivTorus h '' O =
        (Pi.map fun (_ : Fin 4) => (QuotientAddGroup.mk : ℝ → AddCircle (torusSide L m))) ''
          (BoxTorus.projection d.sideLengths ⁻¹' O) := by
      rw [← hc, Set.image_comp,
        Set.image_preimage_eq _ (BoxTorus.projection_surjective d.sideLengths)]
    rw [himg]
    exact hP.isOpenMap _ hO
theorem isForward_iff_isPositivelyOriented (h : d.HasEqualSides m) (b : d.DirectedEdge) :
    b.IsForward ↔ (edgeEquivBond h b).IsPositivelyOriented := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.isForward_iff_edgeEquivBond <;> assumption
theorem edgeEquivBond_flip (h : d.HasEqualSides m) (b : d.DirectedEdge) :
    edgeEquivBond h b.flip = (edgeEquivBond h b).opposite :=
  PeriodicLattice.Bond.ext rfl rfl
theorem sameSpaceAndEdges (h : d.HasEqualSides m) : SameSpaceAndEdges h := by
  refine ⟨spaceEquivTorus_isHomeomorph h, ?_, isForward_iff_isPositivelyOriented h,
    edgeEquivBond_flip h⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (spaceEquivTorus_mem_sublattice_iff h x).mpr hx
  · intro hy
    refine ⟨(spaceEquivTorus h).symm y, (spaceEquivTorus_mem_sublattice_iff h _).mp ?_,
      (spaceEquivTorus h).apply_symm_apply y⟩
    rw [(spaceEquivTorus h).apply_symm_apply]
    exact hy
theorem sameGaugeFields (hl : GridLattice.GaugeConfigsAsEdgeMaps d)
    (h : d.HasEqualSides m) : SameGaugeFields h := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.gaugeFields_correspond <;> assumption
theorem sameActionAndGibbsMeasure {K : ℕ} {d : CellGrid L (K : ℤ)}
    (hl : GridLattice.GaugeConfigsAsEdgeMaps d) (h : d.HasEqualSides m) (β : ℝ) :
    SameActionAndGibbsMeasure h β := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.actionAndGibbsMeasure_correspond <;> assumption
theorem statement_holds (hl : GridLattice.Properties) : Statement := by
  intro s d h β _
  have hc : GridLattice.GaugeConfigsAsEdgeMaps d := (hl _ _ d).2.2.1
  exact ⟨sameSpaceAndEdges h, sameGaugeFields hc h, sameActionAndGibbsMeasure hc h β⟩
end EqualSideGrids
end YangMills.Construction
end
