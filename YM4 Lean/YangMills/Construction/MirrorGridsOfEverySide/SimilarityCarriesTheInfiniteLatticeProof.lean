import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesTheInfiniteLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace MirrorGridsAllSides.ScalingOnGrid
variable {D : GridSetup} (S : ScalingMap D)
theorem pointMap_injective : Function.Injective S.pointMap := fun _ _ h =>
  Subtype.ext (S.toPerm.injective (congrArg Subtype.val h))
theorem pointMap_surjective : Function.Surjective S.pointMap := by
  intro y
  obtain ⟨k, hk⟩ := y.2
  obtain ⟨u, hu⟩ := S.shift_mem
  have hs := S.scale_pos.ne'
  have hmem : S.toPerm.symm (y : AmbientSpace) ∈ D.gridPoints := by
    refine ⟨k + u, fun μ => ?_⟩
    change S.scale⁻¹ * (y : AmbientSpace) μ + S.shift μ = _
    rw [hk μ, hu μ, S.image_mesh]
    simp only [Pi.add_apply, Int.cast_add]
    field_simp
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  exact S.toPerm.apply_symm_apply (y : AmbientSpace)
theorem pointMap_add_axisStep (x : InfiniteLattice.LatticePoint D.mesh) (μ : Fin 4) :
    S.pointMap (x + InfiniteLattice.axisStep D.mesh μ) =
      S.pointMap x + InfiniteLattice.axisStep S.image.mesh μ := by
  have h := S.pointMap_sub_pointMap (x := x) (y := x + InfiniteLattice.axisStep D.mesh μ) (μ := μ)
    (add_sub_cancel_left _ _)
  rw [← h]
  abel
theorem sub_eq_axisStep_of_pointMap {x y : InfiniteLattice.LatticePoint D.mesh} {μ : Fin 4}
    (h : S.pointMap y - S.pointMap x = InfiniteLattice.axisStep S.image.mesh μ) :
    y - x = InfiniteLattice.axisStep D.mesh μ := by
  have h1 : S.pointMap y = S.pointMap (x + InfiniteLattice.axisStep D.mesh μ) := by
    rw [pointMap_add_axisStep, ← h]
    abel
  rw [pointMap_injective S h1]
  abel
theorem linkMap_injective : Function.Injective S.linkMap := fun _ _ h =>
  InfiniteLattice.Link.ext (pointMap_injective S (congrArg InfiniteLattice.Link.initial h))
    (pointMap_injective S (congrArg InfiniteLattice.Link.terminal h))
theorem linkMap_surjective : Function.Surjective S.linkMap := by
  intro e
  obtain ⟨x, hx⟩ := pointMap_surjective S e.initial
  obtain ⟨y, hy⟩ := pointMap_surjective S e.terminal
  have hadj : ∃ μ : Fin 4, y - x = InfiniteLattice.axisStep D.mesh μ ∨
      y - x = -InfiniteLattice.axisStep D.mesh μ := by
    obtain ⟨μ, h | h⟩ := e.isAdjacent
    · exact ⟨μ, Or.inl (sub_eq_axisStep_of_pointMap S (by rw [hx, hy, h]))⟩
    · refine ⟨μ, Or.inr ?_⟩
      have h' : S.pointMap x - S.pointMap y = InfiniteLattice.axisStep S.image.mesh μ := by
        rw [hx, hy, ← neg_sub, h, neg_neg]
      rw [← sub_eq_axisStep_of_pointMap S h', neg_sub]
  refine ⟨⟨x, y, hadj⟩, InfiniteLattice.Link.ext hx hy⟩
theorem isPositivelyOriented_iff (e : D.Link) :
    e.IsPositivelyOriented ↔ (S.linkMap e).IsPositivelyOriented := by
  constructor
  · rintro ⟨μ, h⟩
    exact ⟨μ, S.pointMap_sub_pointMap h⟩
  · rintro ⟨μ, h⟩
    exact ⟨μ, sub_eq_axisStep_of_pointMap S h⟩
theorem pointMap_image_faceCorners (p : D.Plaquette) :
    S.pointMap '' D.faceCorners p = S.image.faceCorners (S.faceMap p) := by
  simp only [ChessboardTori.ChessboardSetup.faceCorners, Set.image_insert_eq, Set.image_singleton,
    pointMap_add_axisStep]
  rfl
theorem image_faceCorners (p : D.Plaquette) :
    S.toFun '' (Subtype.val '' D.faceCorners p) =
      Subtype.val '' S.image.faceCorners (S.faceMap p) := by
  rw [← pointMap_image_faceCorners, Set.image_image, Set.image_image]
  rfl
theorem faceMap_bijective : Function.Bijective S.faceMap := by
  constructor
  · intro p q h
    have hc : S.pointMap p.corner = S.pointMap q.corner :=
      congrArg InfiniteLattice.ElementaryPlaquette.corner h
    have h1 : (S.faceMap p).lowAxis = (S.faceMap q).lowAxis := by rw [h]
    have h2 : (S.faceMap p).highAxis = (S.faceMap q).highAxis := by rw [h]
    exact InfiniteLattice.ElementaryPlaquette.ext (pointMap_injective S hc) h1 h2
  · intro p'
    obtain ⟨x, hx⟩ := pointMap_surjective S p'.corner
    exact ⟨⟨x, p'.lowAxis, p'.highAxis, p'.lowAxis_lt_highAxis⟩,
      InfiniteLattice.ElementaryPlaquette.ext hx rfl rfl⟩
theorem center_faceMap (p : D.Plaquette) :
    (S.faceMap p).center = S.toFun p.center := by
  funext ν
  change S.toFun (p.corner : AmbientSpace) ν + (Pi.single p.lowAxis (S.image.mesh / 2) : AmbientSpace) ν +
      (Pi.single p.highAxis (S.image.mesh / 2) : AmbientSpace) ν =
    S.scale * (((p.corner : AmbientSpace) ν + (Pi.single p.lowAxis (D.mesh / 2) : AmbientSpace) ν +
      (Pi.single p.highAxis (D.mesh / 2) : AmbientSpace) ν) - S.shift ν)
  simp only [ScalingMap.toFun, S.image_mesh, Pi.single_apply]
  split_ifs <;> ring
theorem image_gridPoints :
    S.toFun '' (D.gridPoints : Set AmbientSpace) =
      (S.image.gridPoints : Set AmbientSpace) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact S.toFun_mem hx
  · intro hy
    obtain ⟨x, hx⟩ := pointMap_surjective S ⟨y, hy⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
theorem scalingPreservesGridPoints : ScalingPreservesGridPoints := fun _ S =>
  ⟨image_gridPoints S, ⟨linkMap_injective S, linkMap_surjective S⟩, isPositivelyOriented_iff S,
    image_faceCorners S, faceMap_bijective S, center_faceMap S⟩
end MirrorGridsAllSides.ScalingOnGrid
end YangMills.Construction
end
