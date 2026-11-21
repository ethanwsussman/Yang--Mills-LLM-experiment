import YangMills.Construction.Lattice.LatticeFieldOperations
import YangMills.Construction.Towers.DilationCarriesTheActionOfATower
import YangMills.Construction.Towers.WhatTheDilationKeeps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
theorem scalingPreservesActionAllSides_holds (hkeeps : ScalingCompatibility.Statement) :
    ScalingPreservesActionAllSides := by
  intro L hL hs k j hj n hn
  obtain ⟨hfin, -⟩ := hkeeps L hs hL k j 0 hj (Nat.zero_le j)
  have hkeep := (hfin n hn).1 univ fun _ _ => mem_univ _
  have himage : scaleEdge (n := n) hL hj 0 '' univ = univ :=
    (scaleEdge (n := n) hL hj 0).surjective.range_eq ▸ image_univ
  have hcompact : ∀ V : Edge L n k 0 → Matrices.ComplexMatrix2, V ∈ fieldSpace L n k 0 ↔
      transportTotal (scaleEdge hL hj 0) V ∈ fieldSpace L (scaledExponent n k j) j 0 := by
    intro V
    have h := hkeep.compactField_iff V
    rw [himage] at h
    exact h
  refine ⟨?_, fun U hU => ?_⟩
  · ext W
    constructor
    · rintro ⟨V, hV, rfl⟩
      exact (hcompact V).1 hV
    · intro hW
      have hback : transportTotal (scaleEdge (n := n) hL hj 0)
          (W ∘ scaleEdge (n := n) hL hj 0) = W := by
        funext b
        simp [transportTotal]
      refine ⟨W ∘ scaleEdge (n := n) hL hj 0, (hcompact _).2 ?_, hback⟩
      rw [hback]
      exact hW
  · have hcomplex : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ U :=
      ⟨fun b hb => EquivariantMaps.compactGaugeGroup_subset_complexGaugeGroup (hU.1 b hb), hU.2⟩
    have hterm : ∀ p : Face L n k 0,
        PeriodicLattice.plaquetteCost (transportTotal (scaleEdge hL hj 0) U)
            (scaleFace hL hj 0 p) = PeriodicLattice.plaquetteCost U p := by
      intro p
      simp only [PeriodicLattice.plaquetteCost]
      rw [hkeep.plaquetteHolonomy_eq U hcomplex p fun _ _ => mem_univ _]
    simp only [plaquetteAction, PeriodicLattice.wilsonAction]
    rw [← finsum_comp_equiv (scaleFace (n := n) hL hj 0)]
    exact finsum_congr hterm
end YangMills.Construction.Tower
end
