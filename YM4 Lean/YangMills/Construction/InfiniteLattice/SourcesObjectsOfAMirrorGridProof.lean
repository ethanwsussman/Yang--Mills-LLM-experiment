import YangMills.Construction.InfiniteLattice.ObservablesOfASetAsFunctionsOfItsBonds
import YangMills.Construction.InfiniteLattice.SourcesObjectsOfAMirrorGrid
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.MultipleReflections
open InfiniteLattice (AmbientSpace)
namespace GluingGrid
variable {D : Setup} (G : D.Grid)
theorem openCube_eq (i : ℕ) (h : 2 * G.edge ≤ D.side) (k : Fin 4 → ℤ) :
    (G.toCubicGrid i h).openCube k = G.tileInterior k := by
  ext x
  refine forall_congr' fun μ => ?_
  change x μ - (G.shift μ + G.edge * (k μ : ℝ)) ∈ Ioo 0 G.edge ↔
    (G.shift μ + G.edge * (k μ : ℝ)) < x μ ∧ x μ < (G.shift μ + G.edge * (k μ : ℝ)) + G.edge
  rw [mem_Ioo, sub_pos, sub_lt_iff_lt_add']
theorem cube_eq (i : ℕ) (h : 2 * G.edge ≤ D.side) (k : Fin 4 → ℤ) :
    (G.toCubicGrid i h).cube k = G.tile k := by
  ext x
  refine forall_congr' fun μ => ?_
  change x μ - (G.shift μ + G.edge * (k μ : ℝ)) ∈ Icc 0 G.edge ↔
    (G.shift μ + G.edge * (k μ : ℝ)) ≤ x μ ∧ x μ ≤ (G.shift μ + G.edge * (k μ : ℝ)) + G.edge
  rw [mem_Icc, sub_nonneg, sub_le_iff_le_add']
theorem cubeAlgebra_eq
    (hobs : InfiniteLattice.RegionObservablesAsLinkFunctions)
    (i : ℕ) (h : 2 * G.edge ≤ D.side) (k : Fin 4 → ℤ) :
    (G.toCubicGrid i h).cubeAlgebra k = Setup.Grid.tileObservables G k := by
  have ha : 0 < D.mesh := (D.toGluingSetup i).mesh_pos
  ext F
  have hT : ∀ hF : InfiniteLattice.IsBoundedObservable F,
      (F ∈ InfiniteLattice.regionObservables D.mesh (G.tileInterior k) ↔
        FieldsAtSpacing.DependsOnlyOnLinks
          (InfiniteLattice.linksWithin (G.tileInterior k)) F) :=
    fun hF => by
      have h02 := ((hobs D.mesh ha).2.2.1 (G.tileInterior k) F hF).out 0 2
      refine h02.trans ⟨fun hD U V hUV => hD U V (funext fun b => hUV b.1 b.2),
        fun hD U V hUV => hD U V fun ℓ hℓ => congrFun hUV ⟨ℓ, hℓ⟩⟩
  constructor
  · rintro ⟨hF, hR⟩
    rw [openCube_eq G i h k] at hR
    exact ⟨hF, ((hT hF).2 hR).2⟩
  · rintro ⟨hF, hM⟩
    refine ⟨hF, ?_⟩
    rw [openCube_eq G i h k]
    exact (hT hF).1 ⟨hF, hM⟩
theorem gluingGridObjectsAgree (hobs : InfiniteLattice.RegionObservablesAsLinkFunctions) :
    GluingGridObjectsAgree := by
  intro D G h i
  refine ⟨⟨G.isGridScale_edge i h, G.isTileEdge_edge.2⟩, rfl, rfl, ?_,
    cube_eq G i h, cubeAlgebra_eq G hobs i h⟩
  exact SourcesAndGluing.CubicGrid.toMirror_of_isMirrorGrid _ G.shift_mem
end GluingGrid
end YangMills.Construction.MultipleReflections
end
