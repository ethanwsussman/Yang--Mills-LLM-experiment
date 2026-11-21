import YangMills.Construction.ChessboardTori.ElementsCarryingLayersOfCellsProof
import YangMills.Construction.ChessboardTori.LinksAndPlaquettesUnderLatticeIsometries
import YangMills.Construction.ChessboardTori.PeriodicRealizationOnARectangularTorusProof
import YangMills.Construction.InfiniteLattice.GroupOfLatticeIsometriesProof
import YangMills.Construction.Lattice.IsometryInvarianceOfWilsonMeasure
import YangMills.Construction.Matrices.HaarExpChartDensity
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
namespace InducedQuotientMaps
variable {D : ChessboardSetup}
theorem linearComponent_eq_of {r : AmbientSpace → AmbientSpace}
    {R : AmbientSpace →ₗ[ℝ] AmbientSpace} (h : HasLinearComponent r R) :
    linearComponent r = R := by apply _root_.YangMills.Construction.ChessboardTori.BoxTorusQuotient.linearComponent_eq <;> assumption
theorem meshAt_zero_eq (D : ChessboardSetup) : Tower.meshAt D.L D.K 0 = D.mesh := by
  rw [← Tower.meshSize_levelDepth]
  simp [ChessboardSetup.mesh, PeriodicLattice.levelDepth]
theorem L_pos (D : ChessboardSetup) : 0 < D.L := by
  have := D.isAdmissible.2
  omega
theorem exists_affine_hyperoctahedral
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (r : D.LatticeSym) :
    ∃ w ∈ InfiniteLattice.hyperoctahedralLinearGroup, ∃ v : AmbientSpace,
      ∀ x, r.toFun x = w x + v := by
  have h := (hT D.L (L_pos D) D.isAdmissible D.K).2.2.2.2.1 0
    (Nat.zero_le _) r.toFun r.preservesDist (by
      change r.toFun '' (InfiniteLattice.latticeSubgroup _ : Set AmbientSpace) =
        InfiniteLattice.latticeSubgroup _
      rw [meshAt_zero_eq]
      exact r.image_eq)
  obtain ⟨⟨w, hw, v, -, hv⟩, -⟩ := h
  exact ⟨w, hw, v, hv⟩
theorem euclidNormVec_hyperoctahedral {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    (hw : w ∈ InfiniteLattice.hyperoctahedralLinearGroup)
    (z : AmbientSpace) : euclidNormVec (w z) = euclidNormVec z := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetryGroup.euclidNormVec_hyperoctahedral <;> assumption
namespace OnQuotient
variable (P : PeriodSubgroup D)
theorem proj_surjective : Function.Surjective P.proj :=
  BoxTorus.projection_surjective P.sideLengths
theorem proj_eq_iff (x y : AmbientSpace) :
    P.proj x = P.proj y ↔ x - y ∈ P.subgroup := by
  rw [← sub_eq_zero, ← map_sub]
  change BoxTorus.projection P.sideLengths (x - y) = 0 ↔ _
  rw [← AddMonoidHom.mem_ker, BoxTorus.projection_ker]
  rfl
structure IsSignedMotion (r : D.LatticeSym) (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace)
    (v : AmbientSpace) : Prop where
  mem_group : w ∈ InfiniteLattice.hyperoctahedralLinearGroup
  eq_apply : ∀ x, r.toFun x = w x + v
  image_subgroup : w '' (P.subgroup : Set AmbientSpace) = P.subgroup
variable {P}
theorem exists_isSignedMotion
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    {r : D.LatticeSym} (h : P.IsStableUnder r) : ∃ w v, IsSignedMotion P r w v := by
  obtain ⟨w, hw, v, hv⟩ := exists_affine_hyperoctahedral hT r
  refine ⟨w, v, hw, hv, ?_⟩
  have e : linearComponent r.toFun = (w : AmbientSpace →ₗ[ℝ] AmbientSpace) :=
    linearComponent_eq_of ⟨v, hv⟩
  have h' : linearComponent r.toFun '' (P.subgroup : Set AmbientSpace) = P.subgroup := h
  rw [e] at h'
  exact h'
theorem IsSignedMotion.inv {r i : D.LatticeSym} {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    {v : AmbientSpace} (h : IsSignedMotion P r w v) (hi : ∀ x, r.toFun (i.toFun x) = x) :
    IsSignedMotion P i w⁻¹ (-(w.symm v)) := by
  refine ⟨inv_mem h.mem_group, fun x => ?_, ?_⟩
  · have h1 : w (i.toFun x) = x - v :=
      eq_sub_of_add_eq ((h.eq_apply (i.toFun x)).symm.trans (hi x))
    have h2 : i.toFun x = w.symm (x - v) := by
      rw [← h1]
      simp
    rw [h2, map_sub]
    change _ = w.symm x + _
    abel
  · change w.symm '' (P.subgroup : Set AmbientSpace) = P.subgroup
    conv_lhs => rw [← h.image_subgroup]
    rw [image_image]
    simp
theorem IsSignedMotion.sub_mem_subgroup {r : D.LatticeSym}
    {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace} {v : AmbientSpace}
    (h : IsSignedMotion P r w v) {x y : AmbientSpace} (hxy : x - y ∈ P.subgroup) :
    r.toFun x - r.toFun y ∈ P.subgroup := by
  have e : r.toFun x - r.toFun y = w (x - y) := by
    rw [h.eq_apply, h.eq_apply, map_sub]
    abel
  rw [e]
  have : w (x - y) ∈ w '' (P.subgroup : Set AmbientSpace) := mem_image_of_mem _ hxy
  rw [h.image_subgroup] at this
  exact this
theorem inducesMap_apply {r : D.LatticeSym} {f : P.TorusSpace → P.TorusSpace}
    (hf : P.InducesMap r f) (x : AmbientSpace) : f (P.proj x) = P.proj (r.toFun x) :=
  (congrFun hf x).symm
theorem IsSignedMotion.exists_inducesMap {r : D.LatticeSym}
    {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace} {v : AmbientSpace}
    (h : IsSignedMotion P r w v) : ∃ f, P.InducesMap r f := by
  refine ⟨fun u => P.proj (r.toFun (Function.surjInv (proj_surjective P) u)), ?_⟩
  funext x
  refine (proj_eq_iff P _ _).mpr (h.sub_mem_subgroup ((proj_eq_iff P _ _).mp ?_))
  rw [Function.surjInv_eq (proj_surjective P)]
theorem inducesMap_quotientMap {r : D.LatticeSym} (h : ∃ f, P.InducesMap r f) :
    P.InducesMap r (P.quotientMap r) := by
  have : Nonempty (P.TorusSpace → P.TorusSpace) := ⟨id⟩
  exact Classical.epsilon_spec h
theorem mapEdge_eq_of {s : P.TorusSpace → P.TorusSpace} {b c : P.DirectedEdge}
    (ht : (c.source : P.TorusSpace) = s b.source) (hh : (c.target : P.TorusSpace) = s b.target) :
    P.mapEdge s b = c := by
  have h : ((P.mapEdge s b).source : P.TorusSpace) = s b.source ∧
      ((P.mapEdge s b).target : P.TorusSpace) = s b.target :=
    Classical.epsilon_spec (p := fun b' : P.DirectedEdge =>
      (b'.source : P.TorusSpace) = s b.source ∧ (b'.target : P.TorusSpace) = s b.target)
      ⟨c, ht, hh⟩
  exact BoxTorus.DirectedEdge.ext (Subtype.ext (h.1.trans ht.symm))
    (Subtype.ext (h.2.trans hh.symm))
theorem mapEdge_projEdge {r : D.LatticeSym} {f : P.TorusSpace → P.TorusSpace}
    (hf : P.InducesMap r f) (b : D.Link) : P.mapEdge f (P.projEdge b) = P.projEdge (r.linkMap b) :=
  mapEdge_eq_of (inducesMap_apply hf b.initial).symm (inducesMap_apply hf b.terminal).symm
variable (hQF : ProjOnEdgesAndFaces.Statement)
include hQF
theorem projEdge_surjective (P : PeriodSubgroup D) : Function.Surjective P.projEdge :=
  (hQF D P).1.2.1
theorem projFace_surjective (P : PeriodSubgroup D) : Function.Surjective P.projFace :=
  (hQF D P).1.2.2.2.1
theorem mapEdge_source {r : D.LatticeSym} {f : P.TorusSpace → P.TorusSpace}
    (hf : P.InducesMap r f) (b : P.DirectedEdge) :
    ((P.mapEdge f b).source : P.TorusSpace) = f b.source := by
  obtain ⟨b, rfl⟩ := projEdge_surjective hQF P b
  rw [mapEdge_projEdge hf]
  exact (inducesMap_apply hf b.initial).symm
theorem mapEdge_target {r : D.LatticeSym} {f : P.TorusSpace → P.TorusSpace}
    (hf : P.InducesMap r f) (b : P.DirectedEdge) :
    ((P.mapEdge f b).target : P.TorusSpace) = f b.target := by
  obtain ⟨b, rfl⟩ := projEdge_surjective hQF P b
  rw [mapEdge_projEdge hf]
  exact (inducesMap_apply hf b.terminal).symm
theorem mapEdge_flip {r : D.LatticeSym} {f : P.TorusSpace → P.TorusSpace}
    (hf : P.InducesMap r f) (b : P.DirectedEdge) : P.mapEdge f b.flip = (P.mapEdge f b).flip :=
  mapEdge_eq_of (mapEdge_target hQF hf b) (mapEdge_source hQF hf b)
theorem mapEdge_comp {r r' : D.LatticeSym} {f g : P.TorusSpace → P.TorusSpace}
    (hf : P.InducesMap r f) (hg : P.InducesMap r' g) (b : P.DirectedEdge) :
    P.mapEdge (f ∘ g) b = P.mapEdge f (P.mapEdge g b) :=
  mapEdge_eq_of
    (by rw [mapEdge_source hQF hf, mapEdge_source hQF hg]; rfl)
    (by rw [mapEdge_target hQF hf, mapEdge_target hQF hg]; rfl)
omit hQF
def pointHom (P : PeriodSubgroup D) : InfiniteLattice.LatticePoint D.mesh →+ P.GridPoint where
  toFun := P.projPoint
  map_zero' := Subtype.ext P.proj.map_zero
  map_add' x y := Subtype.ext (P.proj.map_add x y)
theorem pointHom_surjective (P : PeriodSubgroup D) : Function.Surjective (pointHom P) := by
  rintro ⟨x, n, rfl⟩
  exact ⟨D.gridVector n, Subtype.ext rfl⟩
theorem face_eq_of_vertexSet (hQ : LatticeQuotients.Statement) {p q : P.Face}
    (h : p.vertexSet = q.vertexSet) : p = q := by apply _root_.YangMills.Construction.ChessboardTori.BoxTorusQuotient.face_eq_of_vertexSet <;> assumption
def torusVertices (p : P.Face) : Set P.TorusSpace :=
  (fun x : P.GridPoint => (x : P.TorusSpace)) '' p.vertexSet
theorem mapFace_eq_of (hQ : LatticeQuotients.Statement) {s : P.TorusSpace → P.TorusSpace}
    {p c : P.Face} (h : torusVertices c = s '' torusVertices p) : P.mapFace s p = c := by apply _root_.YangMills.Construction.ChessboardTori.BoxTorusQuotient.mapFace_eq_of <;> assumption
theorem torusVertices_projFace (hQF : ProjOnEdgesAndFaces.Statement) (p : D.Plaquette) :
    torusVertices (P.projFace p) =
      (fun x : InfiniteLattice.LatticePoint D.mesh => P.proj x) '' D.faceCorners p := by apply _root_.YangMills.Construction.ChessboardTori.BoxTorusQuotient.vertexImage_projFace <;> assumption
section Actions
variable (hQF : ProjOnEdgesAndFaces.Statement) (hQ : LatticeQuotients.Statement)
  (hL : LatticeSymmetryAction.Statement)
  {r r' : D.LatticeSym} {f g : P.TorusSpace → P.TorusSpace}
include hQF hL in
theorem torusVertices_projFace_imageFace (hf : P.InducesMap r f) (p : D.Plaquette) :
    torusVertices (P.projFace (D.imageFace r p)) = f '' torusVertices (P.projFace p) := by
  rw [torusVertices_projFace hQF, torusVertices_projFace hQF, (hL D r).2.2.1 p,
    image_image, image_image]
  exact image_congr fun x _ => (inducesMap_apply hf x).symm
include hQF hQ hL in
theorem mapFace_projFace (hf : P.InducesMap r f) (p : D.Plaquette) :
    P.mapFace f (P.projFace p) = P.projFace (D.imageFace r p) :=
  mapFace_eq_of hQ (torusVertices_projFace_imageFace hQF hL hf p)
include hQF hQ hL in
theorem torusVertices_mapFace (hf : P.InducesMap r f) (p : P.Face) :
    torusVertices (P.mapFace f p) = f '' torusVertices p := by
  obtain ⟨p, rfl⟩ := projFace_surjective hQF P p
  rw [mapFace_projFace hQF hQ hL hf]
  exact torusVertices_projFace_imageFace hQF hL hf p
include hQF hQ hL in
theorem mapFace_leftInverse (hf : P.InducesMap r f) (hgf : ∀ u, g (f u) = u) :
    Function.LeftInverse (P.mapFace g) (P.mapFace f) := fun p =>
  mapFace_eq_of hQ (by
    rw [torusVertices_mapFace hQF hQ hL hf, image_image]
    simp [hgf])
include hQF in
theorem mapEdge_leftInverse (hf : P.InducesMap r f) (hgf : ∀ u, g (f u) = u) :
    Function.LeftInverse (P.mapEdge g) (P.mapEdge f) := fun b =>
  mapEdge_eq_of (by rw [mapEdge_source hQF hf, hgf]) (by rw [mapEdge_target hQF hf, hgf])
include hQF hQ hL in
theorem faceCenter_mapFace (hf : P.InducesMap r f) (p : P.Face) :
    P.faceCenter (P.mapFace f p) = f (P.faceCenter p) := by
  obtain ⟨p, rfl⟩ := projFace_surjective hQF P p
  rw [mapFace_projFace hQF hQ hL hf, (hQF D P).1.2.2.2.2.2.2,
    (hQF D P).1.2.2.2.2.2.2, inducesMap_apply hf, (hL D r).2.2.2.1]
theorem IsSignedMotion.isTorusIsometry {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace} {v : AmbientSpace}
    (h : IsSignedMotion P r w v) (hf : P.InducesMap r f) : P.IsTorusIsometry f := by
  intro u u'
  obtain ⟨y, rfl⟩ := proj_surjective P u
  obtain ⟨y', rfl⟩ := proj_surjective P u'
  rw [inducesMap_apply hf, inducesMap_apply hf, P.torusDist_proj, P.torusDist_proj]
  have e : ∀ z, r.toFun y - r.toFun y' + w z = w (y - y' + z) := fun z => by
    rw [h.eq_apply, h.eq_apply, map_add, map_sub]
    abel
  unfold ChessboardSetup.periodicDistance
  congr 1
  ext t
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ w '' (P.subgroup : Set AmbientSpace) := by
      rw [h.image_subgroup]
      exact hz
    obtain ⟨z', hz', rfl⟩ := hz'
    exact ⟨z', hz', by simp only [e, euclidNormVec_hyperoctahedral h.mem_group]⟩
  · rintro ⟨z, hz, rfl⟩
    have hz' : w z ∈ (P.subgroup : Set AmbientSpace) := by
      rw [← h.image_subgroup]
      exact mem_image_of_mem _ hz
    exact ⟨w z, hz', by simp only [e, euclidNormVec_hyperoctahedral h.mem_group]⟩
theorem image_gridSubgroup (hf : P.InducesMap r f) :
    f '' (P.gridSubgroup : Set P.TorusSpace) = P.gridSubgroup := by
  ext u
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨x, hx⟩ := pointHom_surjective P ⟨u, hu⟩
    have e : u = P.proj x := (congrArg Subtype.val hx).symm
    rw [e, inducesMap_apply hf]
    exact (P.projPoint (r.pointMap x)).2
  · intro hu
    obtain ⟨x, hx⟩ := pointHom_surjective P ⟨u, hu⟩
    have hx' : (x : AmbientSpace) ∈
        r.toFun '' (InfiniteLattice.latticeSubgroup D.mesh : Set AmbientSpace) := by
      rw [r.image_eq]
      exact x.2
    obtain ⟨y, hy, e⟩ := hx'
    refine ⟨P.proj y, (P.projPoint ⟨y, hy⟩).2, ?_⟩
    rw [inducesMap_apply hf, e]
    exact congrArg Subtype.val hx
include hQF hQ hL in
theorem respectsLatticeStructure {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace} {v : AmbientSpace}
    (h : IsSignedMotion P r w v) (hf : P.InducesMap r f) (hg : P.InducesMap r' g)
    (hfg : ∀ u, f (g u) = u) (hgf : ∀ u, g (f u) = u) :
    P.RespectsLatticeStructure f :=
  ⟨h.isTorusIsometry hf, image_gridSubgroup hf,
    fun b => ⟨mapEdge_source hQF hf b, mapEdge_target hQF hf b⟩,
    Function.bijective_iff_has_inverse.mpr
      ⟨P.mapEdge g, mapEdge_leftInverse hQF hf hgf, mapEdge_leftInverse hQF hg hfg⟩,
    mapEdge_flip hQF hf, torusVertices_mapFace hQF hQ hL hf,
    Function.bijective_iff_has_inverse.mpr
      ⟨P.mapFace g, mapFace_leftInverse hQF hQ hL hf hgf,
        mapFace_leftInverse hQF hQ hL hg hfg⟩,
    faceCenter_mapFace hQF hQ hL hf⟩
include hQ in
theorem not_isForward_flip {c : P.DirectedEdge} (h : c.IsForward) : ¬ c.flip.IsForward := by apply _root_.YangMills.Construction.ChessboardTori.BoxTorusQuotient.not_isForward_flip <;> assumption
include hQ in
theorem edgeVariable_flip (U : P.GaugeConfig) (c : P.DirectedEdge) :
    BoxTorus.edgeVariable U c.flip = (BoxTorus.edgeVariable U c)⁻¹ := by
  by_cases h : c.IsForward
  · have h' := not_isForward_flip hQ h
    simp only [BoxTorus.edgeVariable, dif_pos h, dif_neg h']
    rfl
  · have h' := BoxTorus.DirectedEdge.flip_isForward h
    simp only [BoxTorus.edgeVariable, dif_pos h', dif_neg h, inv_inv]
include hQF hQ in
theorem edgeVariable_pullback (hf : P.InducesMap r f) (U : P.GaugeConfig) (b : P.DirectedEdge) :
    BoxTorus.edgeVariable (P.pullback f U) b = BoxTorus.edgeVariable U (P.mapEdge f b) := by
  by_cases h : b.IsForward
  · rw [BoxTorus.edgeVariable, dif_pos h]
    rfl
  · rw [BoxTorus.edgeVariable, dif_neg h]
    change (BoxTorus.edgeVariable U (P.mapEdge f b.flip))⁻¹ = _
    rw [mapEdge_flip hQF hf, edgeVariable_flip hQ, inv_inv]
include hQF hQ in
theorem pullback_comp (hf : P.InducesMap r f) (hg : P.InducesMap r' g) (U : P.GaugeConfig) :
    P.pullback g (P.pullback f U) = P.pullback (f ∘ g) U := by
  funext b
  change BoxTorus.edgeVariable (P.pullback f U) (P.mapEdge g b.1) =
    BoxTorus.edgeVariable U (P.mapEdge (f ∘ g) b.1)
  rw [edgeVariable_pullback hQF hQ hf, mapEdge_comp hQF hf hg]
theorem pullback_id (U : P.GaugeConfig) : P.pullback id U = U := by apply _root_.YangMills.Construction.ChessboardTori.LayerCarryingElements.OnTorus.pullback_id <;> assumption
include hQF hQ in
theorem liftField_pullback (hf : P.InducesMap r f) (U : P.GaugeConfig) (b : D.Link) :
    P.liftField U (r.linkMap b) = P.liftField (P.pullback f U) b := by
  change BoxTorus.edgeVariable U (P.projEdge (r.linkMap b)) =
    BoxTorus.edgeVariable (P.pullback f U) (P.projEdge b)
  rw [edgeVariable_pullback hQF hQ hf, mapEdge_projEdge hf]
include hQF hQ in
theorem liftGaugeField_pullback (hf : P.InducesMap r f) (U : P.GaugeConfig) :
    P.liftGaugeField (P.pullback f U) = r.pullbackField (P.liftGaugeField U) := by
  have h1 : ∀ V, P.liftGaugeField V = ⟨P.liftField V, (hQF D P).2.2.1 V⟩ :=
    fun V => dif_pos _
  rw [h1, h1]
  exact Subtype.ext (funext fun b => (liftField_pullback hQF hQ hf U b).symm)
include hQF hQ hL in
theorem faceEnergy_pullback (hf : P.InducesMap r f) (U : P.GaugeConfig) (p : P.Face) :
    P.faceEnergy (P.pullback f U) p = P.faceEnergy U (P.mapFace f p) := by
  obtain ⟨p, rfl⟩ := projFace_surjective hQF P p
  have hE : ∀ (V : P.GaugeConfig) (p : D.Plaquette),
      InfiniteLattice.faceEnergy (P.liftGaugeField V) p = P.faceEnergy V (P.projFace p) :=
    fun V p => ((hQF D P).2.2.2.2 V p).2
  rw [← hE, liftGaugeField_pullback hQF hQ hf, (hL D r).2.2.2.2, hE,
    mapFace_projFace hQF hQ hL hf]
end Actions
theorem haarPi_map_reindex_inv (hH : Matrices.ComplexMatrix2.HaarExpChartProperties) {ι : Type}
    [Countable ι] (e : ι ≃ ι)
    (j : ι → Matrices.ComplexMatrix2.specialUnitary → Matrices.ComplexMatrix2.specialUnitary)
    (hj : ∀ i, j i = id ∨ j i = Inv.inv) :
    (Matrices.ComplexMatrix2.haarPi ι).map (fun u i => j i (u (e i))) =
      Matrices.ComplexMatrix2.haarPi ι := by
  have hjm : ∀ i, Measurable (j i) := fun i => by
    rcases hj i with h | h <;> rw [h]
    · exact measurable_id
    · exact continuous_inv.measurable
  have hjh : ∀ i, Matrices.ComplexMatrix2.haarProb.map (j i) =
      Matrices.ComplexMatrix2.haarProb := fun i => by
    rcases hj i with h | h <;> rw [h]
    · exact Measure.map_id
    · exact hH.2.2.2
  have hR : (fun (u : ι → Matrices.ComplexMatrix2.specialUnitary) i => u (e i)) =
      MeasurableEquiv.piCongrLeft (fun _ : ι => Matrices.ComplexMatrix2.specialUnitary) e.symm := by
    funext u i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have h₁ : (Matrices.ComplexMatrix2.haarPi ι).map
      (fun (u : ι → Matrices.ComplexMatrix2.specialUnitary) i => u (e i)) =
      Matrices.ComplexMatrix2.haarPi ι := by
    rw [hR]
    exact Measure.infinitePi_map_piCongrLeft
      (μ := fun _ : ι => Matrices.ComplexMatrix2.haarProb) e.symm
  have hRm : Measurable fun (u : ι → Matrices.ComplexMatrix2.specialUnitary) i => u (e i) := by
    fun_prop
  have hGm : Measurable fun (u : ι → Matrices.ComplexMatrix2.specialUnitary) i => j i (u i) :=
    measurable_pi_iff.2 fun i => (hjm i).comp (measurable_pi_apply i)
  have h₂ : (Matrices.ComplexMatrix2.haarPi ι).map
      (fun (u : ι → Matrices.ComplexMatrix2.specialUnitary) i => j i (u i)) =
      Matrices.ComplexMatrix2.haarPi ι := by
    have := Measure.infinitePi_map_pi (μ := fun _ : ι => Matrices.ComplexMatrix2.haarProb) hjm
    simp only [hjh] at this
    exact this
  have hc : (fun (u : ι → Matrices.ComplexMatrix2.specialUnitary) i => j i (u (e i))) =
      (fun (u : ι → Matrices.ComplexMatrix2.specialUnitary) i => j i (u i)) ∘
        (fun (u : ι → Matrices.ComplexMatrix2.specialUnitary) i => u (e i)) := rfl
  rw [hc, ← Measure.map_map hGm hRm, h₁, h₂]
open Classical in
def forwardPart (c : P.DirectedEdge) : P.ForwardEdge :=
  if h : c.IsForward then ⟨c, h⟩ else ⟨c.flip, BoxTorus.DirectedEdge.flip_isForward h⟩
theorem forwardPart_val (c : P.DirectedEdge) :
    (forwardPart c).1 = c ∨ (forwardPart c).1 = c.flip := by
  unfold forwardPart
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl
theorem forwardPart_forward (b : P.ForwardEdge) : forwardPart b.1 = b := dif_pos b.2
theorem forwardPart_flip (hQ : LatticeQuotients.Statement) (c : P.DirectedEdge) :
    forwardPart c.flip = forwardPart c := by
  by_cases h : c.IsForward
  · have h' := not_isForward_flip hQ h
    rw [forwardPart, forwardPart, dif_neg h', dif_pos h]
    rfl
  · have h' := BoxTorus.DirectedEdge.flip_isForward h
    rw [forwardPart, forwardPart, dif_pos h', dif_neg h]
section Measure
variable (hQF : ProjOnEdgesAndFaces.Statement) (hQ : LatticeQuotients.Statement)
  (hL : LatticeSymmetryAction.Statement)
  (hH : Matrices.ComplexMatrix2.HaarExpChartProperties)
  {r r' : D.LatticeSym} {f g : P.TorusSpace → P.TorusSpace}
include hQF hQ in
theorem forwardPart_mapEdge_forwardPart (hg : P.InducesMap r' g) (c : P.DirectedEdge) :
    forwardPart (P.mapEdge g (forwardPart c).1) = forwardPart (P.mapEdge g c) := by
  rcases forwardPart_val c with e | e <;> rw [e]
  rw [mapEdge_flip hQF hg, forwardPart_flip hQ]
include hQF hQ in
theorem forwardPart_leftInverse (hf : P.InducesMap r f) (hg : P.InducesMap r' g)
    (hgf : ∀ u, g (f u) = u) :
    Function.LeftInverse (fun b : P.ForwardEdge => forwardPart (P.mapEdge g b.1))
      (fun b : P.ForwardEdge => forwardPart (P.mapEdge f b.1)) := fun b => by
  change forwardPart (P.mapEdge g (forwardPart (P.mapEdge f b.1)).1) = b
  rw [forwardPart_mapEdge_forwardPart hQF hQ hg, mapEdge_leftInverse hQF hf hgf,
    forwardPart_forward]
def forwardPerm (hQF : ProjOnEdgesAndFaces.Statement)
    (hQ : LatticeQuotients.Statement) (hf : P.InducesMap r f) (hg : P.InducesMap r' g)
    (hfg : ∀ u, f (g u) = u) (hgf : ∀ u, g (f u) = u) : P.ForwardEdge ≃ P.ForwardEdge where
  toFun b := forwardPart (P.mapEdge f b.1)
  invFun b := forwardPart (P.mapEdge g b.1)
  left_inv := forwardPart_leftInverse hQF hQ hf hg hgf
  right_inv := forwardPart_leftInverse hQF hQ hg hf hfg
open Classical in
def signFactor (f : P.TorusSpace → P.TorusSpace) (b : P.ForwardEdge) :
    Matrices.ComplexMatrix2.specialUnitary → Matrices.ComplexMatrix2.specialUnitary :=
  if (P.mapEdge f b.1).IsForward then id else Inv.inv
theorem pullback_eq_signFactor (U : P.GaugeConfig) (b : P.ForwardEdge) :
    P.pullback f U b = signFactor f b (U (forwardPart (P.mapEdge f b.1))) := by
  change BoxTorus.edgeVariable U (P.mapEdge f b.1) = _
  by_cases h : (P.mapEdge f b.1).IsForward
  · rw [BoxTorus.edgeVariable, dif_pos h, signFactor, if_pos h, forwardPart, dif_pos h]
    rfl
  · rw [BoxTorus.edgeVariable, dif_neg h, signFactor, if_neg h, forwardPart, dif_neg h]
include hQF hQ hH in
theorem map_haarMeasure (hf : P.InducesMap r f) (hg : P.InducesMap r' g)
    (hfg : ∀ u, f (g u) = u) (hgf : ∀ u, g (f u) = u) :
    P.haarMeasure.map (P.pullback f) = P.haarMeasure := by
  have e : P.pullback f =
      fun u b => signFactor f b (u (forwardPerm hQF hQ hf hg hfg hgf b)) :=
    funext fun U => funext fun b => pullback_eq_signFactor U b
  rw [e]
  refine haarPi_map_reindex_inv hH (forwardPerm hQF hQ hf hg hfg hgf) (signFactor f) fun b => ?_
  unfold signFactor
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl
theorem continuous_edgeVariable (c : P.DirectedEdge) :
    Continuous fun U : P.GaugeConfig => BoxTorus.edgeVariable U c := by
  by_cases h : c.IsForward
  · simp only [BoxTorus.edgeVariable, dif_pos h]
    exact continuous_apply _
  · simp only [BoxTorus.edgeVariable, dif_neg h]
    exact (continuous_apply _).inv
theorem continuous_pullback (s : P.TorusSpace → P.TorusSpace) : Continuous (P.pullback s) :=
  continuous_pi fun _ => continuous_edgeVariable _
include hQF hQ hL hH in
theorem pullbackPreservesHaarAndAction (hf : P.InducesMap r f) (hg : P.InducesMap r' g)
    (hfg : ∀ u, f (g u) = u) (hgf : ∀ u, g (f u) = u) :
    P.PullbackPreservesHaarAndAction f := by
  have hfg' : f ∘ g = id := funext hfg
  have hgf' : g ∘ f = id := funext hgf
  refine ⟨⟨{ toFun := P.pullback f
             invFun := P.pullback g
             left_inv := fun U => ?_
             right_inv := fun U => ?_
             continuous_toFun := continuous_pullback f
             continuous_invFun := continuous_pullback g }, rfl⟩,
    ⟨(continuous_pullback f).measurable, map_haarMeasure hQF hQ hH hf hg hfg hgf⟩, fun U => ?_⟩
  · rw [pullback_comp hQF hQ hf hg, hfg', pullback_id]
  · rw [pullback_comp hQF hQ hg hf, hgf', pullback_id]
  · have hb : Function.Bijective (P.mapFace f) := Function.bijective_iff_has_inverse.mpr
      ⟨P.mapFace g, mapFace_leftInverse hQF hQ hL hf hgf,
        mapFace_leftInverse hQF hQ hL hg hfg⟩
    change ∑ᶠ p, BoxTorus.faceEnergy (P.pullback f U) p = ∑ᶠ p, BoxTorus.faceEnergy U p
    have hp : ∀ p, BoxTorus.faceEnergy (P.pullback f U) p =
        BoxTorus.faceEnergy U (P.mapFace f p) :=
      faceEnergy_pullback hQF hQ hL hf U
    simp only [hp]
    exact finsum_comp_equiv (Equiv.ofBijective _ hb)
end Measure
end OnQuotient
open OnQuotient
theorem stableProperties
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hA : ReflectionGridArithmetic.Statement) (hQF : ProjOnEdgesAndFaces.Statement)
    (hQ : LatticeQuotients.Statement)
    (hL : LatticeSymmetryAction.Statement)
    (hH : Matrices.ComplexMatrix2.HaarExpChartProperties) (P : PeriodSubgroup D)
    (r : D.LatticeSym) (hP : P.IsStableUnder r) :
    P.HasInverseQuotientMaps r ∧ P.RespectsLatticeStructure (P.quotientMap r) ∧
      (∀ r₂ : D.LatticeSym, P.IsStableUnder r₂ → P.QuotientMapsCompose r r₂) ∧
      P.PullbackCompatible r ∧ P.PullbackPreservesHaarAndAction (P.quotientMap r) := by
  obtain ⟨w, v, hm⟩ := exists_isSignedMotion hT hP
  have hC : D.LatticeSymGroupLaws := (hA D).2.1
  obtain ⟨i, hir, hri, -⟩ := (hC r r).2
  have hmi := hm.inv fun x => congrFun hri x
  have hf : P.InducesMap r (P.quotientMap r) := inducesMap_quotientMap hm.exists_inducesMap
  have hg : P.InducesMap i (P.quotientMap i) := inducesMap_quotientMap hmi.exists_inducesMap
  have hfg : ∀ u, P.quotientMap r (P.quotientMap i u) = u := fun u => by
    obtain ⟨x, rfl⟩ := proj_surjective P u
    rw [inducesMap_apply hg, inducesMap_apply hf]
    exact congrArg P.proj (congrFun hri x)
  have hgf : ∀ u, P.quotientMap i (P.quotientMap r u) = u := fun u => by
    obtain ⟨x, rfl⟩ := proj_surjective P u
    rw [inducesMap_apply hf, inducesMap_apply hg]
    exact congrArg P.proj (congrFun hir x)
  refine ⟨⟨hf, i, fun x => congrFun hir x, fun x => congrFun hri x, hg, funext hfg, funext hgf⟩,
    respectsLatticeStructure hQF hQ hL hm hf hg hfg hgf, fun r₂ h₂ => ?_,
    fun U => ⟨edgeVariable_pullback hQF hQ hf U, liftField_pullback hQF hQ hf U,
      faceEnergy_pullback hQF hQ hL hf U⟩,
    pullbackPreservesHaarAndAction hQF hQ hL hH hf hg hfg hgf⟩
  obtain ⟨w₂, v₂, hm₂⟩ := exists_isSignedMotion hT h₂
  have hf₂ : P.InducesMap r₂ (P.quotientMap r₂) := inducesMap_quotientMap hm₂.exists_inducesMap
  obtain ⟨c, hc, -⟩ := (hC r r₂).1
  refine ⟨⟨c, hc, ?_⟩, pullback_comp hQF hQ hf hf₂, fun F => ?_⟩
  · funext x
    change P.proj (c.toFun x) = P.quotientMap r (P.quotientMap r₂ (P.proj x))
    rw [hc, inducesMap_apply hf₂, inducesMap_apply hf]
    rfl
  · funext U
    exact congrArg F (pullback_comp hQF hQ hf hf₂ U)
theorem torusProj_surjective (D : ChessboardSetup) : Function.Surjective D.proj := fun u =>
  ⟨_, TestFunctions.torusProj_liftPoint (ℓ := PeriodicLattice.torusSide D.L D.m) u⟩
theorem exists_torusSymmetry
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (r : D.LatticeSym) :
    ∃ s : D.Torus → D.Torus, (∀ x, s (D.proj x) = D.proj (r.toFun x)) ∧
      Tower.IsDistancePreserving s ∧
      s '' (PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ) : Set D.Torus) =
        PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ) := by
  have h := (hT D.L (L_pos D) D.isAdmissible D.K).2.2.2.2.1 0
    (Nat.zero_le _) r.toFun r.preservesDist (by
      change r.toFun '' (InfiniteLattice.latticeSubgroup _ : Set AmbientSpace) =
        InfiniteLattice.latticeSubgroup _
      rw [meshAt_zero_eq]
      exact r.image_eq)
  obtain ⟨s, hs, si, sl⟩ := h.2.2 D.m D.m.pos
  have hd : PeriodicLattice.levelDepth (D.K : ℕ) 0 = ((D.K : ℕ) : ℤ) := by
    simp [PeriodicLattice.levelDepth]
  refine ⟨s, hs, si, ?_⟩
  have sl' : s '' (PeriodicLattice.sublattice D.L D.m (PeriodicLattice.levelDepth (D.K : ℕ) 0) :
      Set (PeriodicLattice.FourTorus D.L D.m)) =
        PeriodicLattice.sublattice D.L D.m (PeriodicLattice.levelDepth (D.K : ℕ) 0) :=
    sl
  rwa [hd] at sl'
theorem preservesPeriodicExpectation
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hA : ReflectionGridArithmetic.Statement)
    (hI : PeriodicLattice.WilsonMeasureIsometryInvariant)
    (r : D.LatticeSym) : D.PreservesPeriodicExpectation r := by
  obtain ⟨i, hir, hri, -⟩ := ((hA D).2.1 r r).2
  obtain ⟨s, hs, -, -⟩ := exists_torusSymmetry hT r
  obtain ⟨s', hs', si', sl'⟩ := exists_torusSymmetry hT i
  have hss' : ∀ u, s (s' u) = u := fun u => by
    obtain ⟨x, rfl⟩ := torusProj_surjective D u
    rw [hs', hs]
    exact congrArg D.proj (congrFun hri x)
  have hs's : ∀ u, s' (s u) = u := fun u => by
    obtain ⟨x, rfl⟩ := torusProj_surjective D u
    rw [hs, hs']
    exact congrArg D.proj (congrFun hir x)
  let σ : D.Torus ≃ D.Torus := ⟨s', s, hss', hs's⟩
  have hσ : PeriodicLattice.IsSublatticeIsometry ((D.K : ℕ) : ℤ) σ := ⟨si', sl'⟩
  have h1 : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  obtain ⟨hends, -, hmap⟩ := (hI D.L D.m D.K D.β h1 D.m.pos D.K.pos).2.2 σ hσ
  have hpull : D.pullbackField s = PeriodicLattice.transportGaugeField σ := by
    funext U b
    refine congrArg U ?_
    have e1 := hends b
    have e2 : ((D.imageLink s b).source : D.Torus) = s b.source ∧
        ((D.imageLink s b).target : D.Torus) = s b.target :=
      Classical.epsilon_spec (p := fun b' : D.PeriodicLink =>
        (b'.source : D.Torus) = s b.source ∧ (b'.target : D.Torus) = s b.target)
        ⟨PeriodicLattice.bondPreimage σ b, e1⟩
    exact PeriodicLattice.Bond.ext (Subtype.ext (e2.1.trans e1.1.symm))
      (Subtype.ext (e2.2.trans e1.2.symm))
  have hm : Measurable (PeriodicLattice.transportGaugeField σ :
      (D.PeriodicLink → Matrices.ComplexMatrix2) → D.PeriodicLink → Matrices.ComplexMatrix2) :=
    measurable_pi_lambda _ fun b => measurable_pi_apply _
  refine ⟨s, funext fun x => (hs x).symm, fun F hF => ?_⟩
  change ∫ U, F (D.pullbackField s U) ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β =
    ∫ U, F U ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β
  rw [hpull]
  conv_rhs => rw [← hmap]
  rw [integral_map hm.aemeasurable hF.1.aestronglyMeasurable]
theorem mem_periodSubgroup_iff (P : PeriodSubgroup D) (x : AmbientSpace) :
    x ∈ P.subgroup ↔ ∀ μ, x μ ∈ AddSubgroup.zmultiples (P.sideLengths μ) := by
  change x ∈ BoxTorus.periods P.sideLengths ↔ _
  simp [BoxTorus.periods, AddSubgroup.mem_pi]
theorem intSign_mul_mem_zmultiples {a z : ℝ} (s : ℤˣ) (hz : z ∈ AddSubgroup.zmultiples a) :
    ((s : ℤ) : ℝ) * z ∈ AddSubgroup.zmultiples a := by
  rcases Int.units_eq_one_or s with e | e
  · simpa [e] using hz
  · simpa [e] using neg_mem hz
theorem isStableUnder_of_diagonal
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (P : PeriodSubgroup D) (r : D.LatticeSym) (hd : IsCoordDiagonal (linearComponent r.toFun)) :
    P.IsStableUnder r := by
  obtain ⟨w, hw, v, hv⟩ := exists_affine_hyperoctahedral hT r
  have e : linearComponent r.toFun = (w : AmbientSpace →ₗ[ℝ] AmbientSpace) :=
    linearComponent_eq_of ⟨v, hv⟩
  obtain ⟨π, s, h⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).mp hw
  have hπ : ∀ μ, π μ = μ := fun μ => by
    obtain ⟨c, hc⟩ := hd (π μ)
    rw [e] at hc
    have h1 := congrFun hc μ
    change w (coordVec (π μ)) μ = _ at h1
    rw [h] at h1
    by_contra hne
    have hs : ((s μ : ℤ) : ℝ) ≠ 0 := by
      rcases Int.units_eq_one_or (s μ) with e | e <;> simp [e]
    simp [coordVec, Ne.symm hne, hs] at h1
  have hx : ∀ x μ, w x μ = ((s μ : ℤ) : ℝ) * x μ := fun x μ => by rw [h, hπ]
  change linearComponent r.toFun '' (P.subgroup : Set AmbientSpace) = P.subgroup
  rw [e]
  apply Subset.antisymm
  · rintro _ ⟨x, hxP, rfl⟩
    refine (mem_periodSubgroup_iff P _).mpr fun μ => ?_
    change w x μ ∈ _
    rw [hx]
    exact intSign_mul_mem_zmultiples _ ((mem_periodSubgroup_iff P x).mp hxP μ)
  · intro y hy
    refine ⟨w y, (mem_periodSubgroup_iff P _).mpr fun μ => ?_, funext fun μ => ?_⟩
    · rw [hx]
      exact intSign_mul_mem_zmultiples _ ((mem_periodSubgroup_iff P y).mp hy μ)
    · change w (w y) μ = y μ
      rw [hx, hx, ← mul_assoc]
      rcases Int.units_eq_one_or (s μ) with e | e <;> simp [e]
theorem hyperoctahedral_mem_cubicPeriod {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    (hw : w ∈ InfiniteLattice.hyperoctahedralLinearGroup)
    {x : AmbientSpace} (hx : x ∈ D.cubicPeriod.subgroup) : w x ∈ D.cubicPeriod.subgroup := by
  obtain ⟨π, s, h⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).mp hw
  refine (mem_periodSubgroup_iff _ _).mpr fun μ => ?_
  rw [h]
  have h1 := (mem_periodSubgroup_iff _ x).mp hx (π μ)
  rw [ChessboardSetup.sideLengths_cubicPeriod] at h1
  rw [ChessboardSetup.sideLengths_cubicPeriod]
  exact intSign_mul_mem_zmultiples _ h1
theorem cubicPeriod_isStableUnder
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (r : D.LatticeSym) : D.cubicPeriod.IsStableUnder r := by
  obtain ⟨w, hw, v, hv⟩ := exists_affine_hyperoctahedral hT r
  have e : linearComponent r.toFun = (w : AmbientSpace →ₗ[ℝ] AmbientSpace) :=
    linearComponent_eq_of ⟨v, hv⟩
  change linearComponent r.toFun '' (D.cubicPeriod.subgroup : Set AmbientSpace) =
    D.cubicPeriod.subgroup
  rw [e]
  apply Subset.antisymm
  · rintro _ ⟨x, hxP, rfl⟩
    exact hyperoctahedral_mem_cubicPeriod hw hxP
  · intro y hy
    refine ⟨w⁻¹ y, hyperoctahedral_mem_cubicPeriod (inv_mem hw) hy, ?_⟩
    change w (w.symm y) = y
    simp
theorem hyperoctahedral_mem_latticeSubgroup {a : ℝ} {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    (hw : w ∈ InfiniteLattice.hyperoctahedralLinearGroup) {x : AmbientSpace}
    (hx : x ∈ InfiniteLattice.latticeSubgroup a) : w x ∈ InfiniteLattice.latticeSubgroup a := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetryGroup.hyperoctahedral_mem_latticeSubgroup <;> assumption
theorem exists_latticeSym_lift
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (s : PeriodicLattice.TorusLatticeSymmetry D.L D.m (D.K : ℕ)) :
    ∃ r : D.LatticeSym, D.proj ∘ r.toFun = s.toFun ∘ D.proj := by
  have hd : PeriodicLattice.levelDepth (D.K : ℕ) 0 = ((D.K : ℕ) : ℤ) := by
    simp [PeriodicLattice.levelDepth]
  have h := (hT D.L (L_pos D) D.isAdmissible D.K).2.2.2.1 D.m D.m.pos 0
    (Nat.zero_le _) s.toFun s.dist_eq (by
      change s.toFun '' (PeriodicLattice.sublattice D.L D.m (PeriodicLattice.levelDepth (D.K : ℕ) 0) :
        Set (PeriodicLattice.FourTorus D.L D.m)) =
          PeriodicLattice.sublattice D.L D.m (PeriodicLattice.levelDepth (D.K : ℕ) 0)
      rw [hd]
      exact s.image_eq)
  obtain ⟨⟨w, hw, v, hvs, hx⟩, -⟩ := h
  rw [meshAt_zero_eq] at hvs
  refine ⟨⟨fun x => w x + v, fun x y => ?_, ?_⟩, funext fun x => (hx x).symm⟩
  · rw [add_sub_add_right_eq_sub, ← map_sub, euclidNormVec_hyperoctahedral hw]
  · apply Subset.antisymm
    · rintro _ ⟨x, hxs, rfl⟩
      exact add_mem (hyperoctahedral_mem_latticeSubgroup hw hxs) hvs
    · intro y hy
      refine ⟨w⁻¹ (y - v), hyperoctahedral_mem_latticeSubgroup (inv_mem hw) (sub_mem hy hvs), ?_⟩
      change w (w.symm (y - v)) + v = y
      simp
theorem quotientMaps (hA : ReflectionGridArithmetic.Statement)
    (hL : LatticeSymmetryAction.Statement)
    (hQ : LatticeQuotients.Statement) (hQF : ProjOnEdgesAndFaces.Statement)
    (hH : Matrices.ComplexMatrix2.HaarExpChartProperties)
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hI : PeriodicLattice.WilsonMeasureIsometryInvariant) : QuotientMapsStatement := fun _ =>
  ⟨stableProperties hT hA hQF hQ hL hH, fun r _ => preservesPeriodicExpectation hT hA hI r,
    isStableUnder_of_diagonal hT, cubicPeriod_isStableUnder hT, exists_latticeSym_lift hT⟩
end InducedQuotientMaps
end YangMills.Construction.ChessboardTori
end
