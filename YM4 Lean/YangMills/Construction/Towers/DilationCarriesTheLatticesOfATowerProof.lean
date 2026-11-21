import YangMills.Construction.Towers.DilationCarriesTheLatticesOfATower
import YangMills.Construction.Towers.PropertiesOfTheDilationOfATower
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.Tower
theorem scalingPreservesSublattices_of_scalingOnTorus {L k j n : ℕ} (hL : 0 < L) (hj : j ≤ k)
    (h : ScalingOnTorus hL hj n) : ScalingPreservesSublattices hL hj n where
  image_sublattice i hi := (h.atLevel i hi).image_sublattice
  vertex_surjective _ _ := (scaleVertex hL hj _).surjective
  edge_surjective _ _ := (scaleEdge hL hj _).surjective
  face_surjective _ _ := (scaleFace hL hj _).surjective
  bijOn_symmetries i hi := by
    refine ⟨fun s hs => ⟨(h.distancePreserving_iff s).2 hs.1,
        (h.mapsSublatticeOnto_iff i hi s).2 hs.2⟩,
      fun s _ s' _ e => (h.existsUnique_map _).unique rfl e, fun g hg => ?_⟩
    obtain ⟨s, rfl, -⟩ := h.existsUnique_map g
    exact ⟨s, ⟨(h.distancePreserving_iff s).1 hg.1, (h.mapsSublatticeOnto_iff i hi s).1 hg.2⟩, rfl⟩
theorem scalingPreservesSublattices_of_scalingOnSpace {L k j : ℕ} (hL : 0 < L) (hj : j ≤ k)
    (h : FullSpace.ScalingOnSpace hL hj) : FullSpace.ScalingPreservesSublattices hL hj where
  image_sublattice i hi := (h.atLevel i hi).image_sublattice
  vertex_surjective _ _ := (FullSpace.scaleVertex hL hj _).surjective
  edge_surjective _ _ := (FullSpace.scaleEdge hL hj _).surjective
  face_surjective _ _ := (FullSpace.scaleFace hL hj _).surjective
  bijOn_symmetries i hi := by
    refine ⟨fun s hs => ⟨(h.distancePreserving_iff s).2 hs.1,
        (h.mapsSublatticeOnto_iff i hi s).2 hs.2⟩,
      fun s _ s' _ e => (h.existsUnique_map _).unique rfl e, fun g hg => ?_⟩
    obtain ⟨s, rfl, -⟩ := h.existsUnique_map g
    exact ⟨s, ⟨(h.distancePreserving_iff s).1 hg.1, (h.mapsSublatticeOnto_iff i hi s).1 hg.2⟩, rfl⟩
theorem scalingPreservesSublatticesAllSides_holds (hProperties : ScalingPropertiesStatement) :
    ScalingPreservesSublatticesAllSides := by
  intro L hL hAdmissible k j hj
  have hP := hProperties L k j hAdmissible hj
  exact ⟨fun n hn => scalingPreservesSublattices_of_scalingOnTorus hL hj (hP.1 n hn),
    scalingPreservesSublattices_of_scalingOnSpace hL hj hP.2⟩
end YangMills.Construction.Tower
