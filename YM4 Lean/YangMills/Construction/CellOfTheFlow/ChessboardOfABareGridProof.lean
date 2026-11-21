import YangMills.Construction.CellOfTheFlow.ChessboardOfABareGrid
import YangMills.Construction.ClusterExpansionOfAStep.IsometriesOfTheEnergy
import YangMills.Construction.FormsOnATorus.FieldsOfAGridOfCells
import YangMills.Construction.Lattice.ChessboardEstimateAtEveryGridDatum
import YangMills.Construction.Lattice.ChessboardValuesAsSeminormsOfAGridDatum
import YangMills.Construction.QuaternionicWilsonModel.TheQuaternionModelIsSUTwoWithWilsonsWeightProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.CellWindows
open BoxTorus
open PeriodicLattice (meshSize)
open TorusFields CubicGridFields WeightedResponses
open InfiniteLattice (AmbientSpace)
section ReflectionGroup
variable {d : Construction.CellGrid 13 0}
private def IsCoordinatewiseAffine (d : Construction.CellGrid 13 0) (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : Prop :=
  ∀ μ, (∃ t : ℤ, ∀ x : AmbientSpace, g x μ = x μ + 2 * d.cellLength * t) ∨
    ∃ t : ℤ, ∀ x : AmbientSpace, g x μ = -x μ + 2 * d.centre μ + 2 * d.cellLength * t
private theorem isCoordinatewiseAffine_of_mem {g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace} (hg : g ∈ d.reflectionGroup) :
    IsCoordinatewiseAffine d g := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨⟨ν, a⟩, rfl⟩ := hg
    intro μ
    by_cases h : μ = ν
    · subst h
      refine Or.inr ⟨a, fun x => ?_⟩
      simp only [Construction.CellGrid.coe_faceReflectEquiv, Construction.CellGrid.faceReflect, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, basisVector, Pi.single_eq_same]
      ring
    · refine Or.inl ⟨0, fun x => ?_⟩
      simp [Construction.CellGrid.coe_faceReflectEquiv, Construction.CellGrid.faceReflect, basisVector,
        Pi.single_eq_of_ne h]
  | one =>
    intro μ
    exact Or.inl ⟨0, fun x => by simp⟩
  | mul g h _ _ ihg ihh =>
    intro μ
    rcases ihg μ with ⟨t, ht⟩ | ⟨t, ht⟩ <;> rcases ihh μ with ⟨t', ht'⟩ | ⟨t', ht'⟩
    · refine Or.inl ⟨t + t', fun x => ?_⟩
      show g (h x) μ = _
      rw [ht, ht']
      push_cast
      ring
    · refine Or.inr ⟨t + t', fun x => ?_⟩
      show g (h x) μ = _
      rw [ht, ht']
      push_cast
      ring
    · refine Or.inr ⟨t - t', fun x => ?_⟩
      show g (h x) μ = _
      rw [ht, ht']
      push_cast
      ring
    · refine Or.inl ⟨t - t', fun x => ?_⟩
      show g (h x) μ = _
      rw [ht, ht']
      push_cast
      ring
  | inv g _ ih =>
    intro μ
    have hx : ∀ x : AmbientSpace, g (g⁻¹ x) = x := fun x => g.apply_symm_apply x
    rcases ih μ with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine Or.inl ⟨-t, fun x => ?_⟩
      have := ht (g⁻¹ x)
      rw [hx] at this
      push_cast
      linarith
    · refine Or.inr ⟨t, fun x => ?_⟩
      have := ht (g⁻¹ x)
      rw [hx] at this
      linarith
private structure IsCubicShape (d : Construction.CellGrid 13 0) (G : CellWindows.CellGrid) (M m : ℕ) : Prop where
  length : d.cellLength = G.side
  counts : ∀ μ, d.counts μ = M
  centre : ∀ μ, d.centre μ = (G.offset μ : ℝ) - 1 / 2
  m_eq : m = G.side * M
  side_pos : 0 < G.side
variable {G : CellWindows.CellGrid} {M m : ℕ}
private theorem IsCubicShape.sideLengths_eq (h : IsCubicShape d G M m) (μ : Fin 4) : d.sideLengths μ = (m : ℝ) := by
  show (d.counts μ : ℝ) * d.cellLength = _
  rw [h.counts, h.length, h.m_eq]
  push_cast
  ring
private theorem IsCubicShape.mem_cellCube (h : IsCubicShape d G M m) (κ : Fin 4 → ℤ) {y : AmbientSpace}
    (hy : ∀ μ, 0 ≤ y μ ∧ y μ ≤ G.side) :
    d.centre + (G.side : ℝ) • (fun μ => (κ μ : ℝ)) + y ∈ d.cellCube κ := by
  refine ⟨y, fun μ _ => ?_, ?_⟩
  · rw [h.length]
    exact hy μ
  · rw [h.length]
private theorem IsCubicShape.coord_bounds (h : IsCubicShape d G M m) {κ : Fin 4 → ℤ} {x : AmbientSpace}
    (hx : x ∈ d.cellCube κ) (μ : Fin 4) :
    d.centre μ + G.side * κ μ ≤ x μ ∧ x μ ≤ d.centre μ + G.side * κ μ + G.side := by
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 := hy μ (Set.mem_univ _)
  rw [h.length] at h1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h.length]
  constructor <;> linarith [h1.1, h1.2]
private def realAffine (g : TorusIsometry) (x : AmbientSpace) : AmbientSpace :=
  fun μ => (g.axisSign μ : ℝ) * x μ + (g.offset μ : ℝ)
private def intAffine (g : TorusIsometry) (z : Fin 4 → ℤ) : Fin 4 → ℤ := fun μ => g.axisSign μ * z μ + g.offset μ
private theorem reflectionTo_axisSign_of_even {κ κ' : Fin 4 → ℤ} {μ : Fin 4} (h : Even (κ' μ - κ μ)) :
    (G.reflectionTo κ κ').axisSign μ = 1 :=
  if_pos h
private theorem reflectionTo_offset_of_even {κ κ' : Fin 4 → ℤ} {μ : Fin 4} (h : Even (κ' μ - κ μ)) :
    (G.reflectionTo κ κ').offset μ = (G.side : ℤ) * (κ' μ - κ μ) :=
  if_pos h
private theorem reflectionTo_axisSign_of_not_even {κ κ' : Fin 4 → ℤ} {μ : Fin 4} (h : ¬ Even (κ' μ - κ μ)) :
    (G.reflectionTo κ κ').axisSign μ = -1 :=
  if_neg h
private theorem reflectionTo_offset_of_not_even {κ κ' : Fin 4 → ℤ} {μ : Fin 4} (h : ¬ Even (κ' μ - κ μ)) :
    (G.reflectionTo κ κ').offset μ = 2 * G.offset μ + (G.side : ℤ) * (κ μ + κ' μ) + (G.side : ℤ) - 1 :=
  if_neg h
private theorem IsCubicShape.apply_eq_realAffine (h : IsCubicShape d G M m) {g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace}
    (hg : g ∈ d.reflectionGroup) {κ κ' : Fin 4 → ℤ} (hc : ∀ x ∈ d.cellCube κ, g x ∈ d.cellCube κ') (x : AmbientSpace) :
    g x = realAffine (G.reflectionTo κ κ') x := by
  have hc0 : (0 : ℝ) < G.side := by exact_mod_cast h.side_pos
  have hx₀ : d.centre + (G.side : ℝ) • (fun μ => (κ μ : ℝ)) + 0 ∈ d.cellCube κ :=
    h.mem_cellCube κ fun μ => ⟨le_rfl, by simpa using hc0.le⟩
  have hx₁ : d.centre + (G.side : ℝ) • (fun μ => (κ μ : ℝ)) + (fun _ => (G.side : ℝ)) ∈ d.cellCube κ :=
    h.mem_cellCube κ fun μ => ⟨hc0.le, le_rfl⟩
  funext μ
  have a₀ := h.coord_bounds (hc _ hx₀) μ
  have a₁ := h.coord_bounds (hc _ hx₁) μ
  rcases isCoordinatewiseAffine_of_mem hg μ with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht] at a₀ a₁
    rw [h.length] at ht
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, h.length] at a₀ a₁
    have e1 : (κ' μ : ℝ) ≤ κ μ + 2 * t := by
      have : (G.side : ℝ) * κ' μ ≤ G.side * (κ μ + 2 * t) := by linarith [a₀.1]
      exact le_of_mul_le_mul_left this hc0
    have e2 : (κ μ : ℝ) + 2 * t ≤ κ' μ := by
      have : (G.side : ℝ) * (κ μ + 2 * t) ≤ G.side * κ' μ := by linarith [a₁.2]
      exact le_of_mul_le_mul_left this hc0
    have e3 : κ' μ = κ μ + 2 * t := by
      have : (κ' μ : ℝ) = ((κ μ + 2 * t : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    have hev : Even (κ' μ - κ μ) := ⟨t, by omega⟩
    show g x μ = (((G.reflectionTo κ κ').axisSign μ : ℤ) : ℝ) * x μ + (((G.reflectionTo κ κ').offset μ : ℤ) : ℝ)
    rw [ht, reflectionTo_axisSign_of_even hev, reflectionTo_offset_of_even hev, e3]
    push_cast
    ring
  · rw [ht] at a₀ a₁
    rw [h.length] at ht
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, h.length] at a₀ a₁
    have e1 : (κ' μ : ℝ) + κ μ + 1 ≤ 2 * t := by
      have : (G.side : ℝ) * (κ' μ + κ μ + 1) ≤ G.side * (2 * t) := by linarith [a₁.1]
      exact le_of_mul_le_mul_left this hc0
    have e2 : 2 * (t : ℝ) ≤ κ' μ + κ μ + 1 := by
      have : (G.side : ℝ) * (2 * t) ≤ G.side * (κ' μ + κ μ + 1) := by linarith [a₀.2]
      exact le_of_mul_le_mul_left this hc0
    have e3 : κ' μ + κ μ + 1 = 2 * t := by
      have : ((κ' μ + κ μ + 1 : ℤ) : ℝ) = ((2 * t : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    have hev : ¬ Even (κ' μ - κ μ) := by
      rw [Int.not_even_iff_odd]
      exact ⟨t - 1 - κ μ, by omega⟩
    have e4 : (2 : ℝ) * G.side * t = G.side * (κ' μ + κ μ + 1) := by
      have : ((κ' μ + κ μ + 1 : ℤ) : ℝ) = ((2 * t : ℤ) : ℝ) := by rw [e3]
      push_cast at this
      rw [this]
      ring
    show g x μ = (((G.reflectionTo κ κ').axisSign μ : ℤ) : ℝ) * x μ + (((G.reflectionTo κ κ').offset μ : ℤ) : ℝ)
    rw [ht, reflectionTo_axisSign_of_not_even hev, reflectionTo_offset_of_not_even hev, h.centre, e4]
    push_cast
    ring
end ReflectionGroup
section PeriodicSpace
variable {d : Construction.CellGrid 13 0} {G : CellWindows.CellGrid} {M m : ℕ}
private theorem realAffine_intCast (g : TorusIsometry) (z : Fin 4 → ℤ) :
    realAffine g (fun μ => (z μ : ℝ) * meshSize 13 0) = fun μ => ((intAffine g z μ : ℤ) : ℝ) * meshSize 13 0 := by
  funext μ
  simp only [realAffine, intAffine, meshSize_zero_eq_one, mul_one]
  push_cast
  ring
private theorem IsCubicShape.cellTransporter_spec (hG : GroupAndCells.AllHold) (h : IsCubicShape d G M m)
    (κ κ' : Fin 4 → ℤ) :
    d.cellTransporter (d.spaceCell κ) (d.spaceCell κ') ∈ d.inducedGroupMaps ∧
      ∀ w, d.cellTransporter (d.spaceCell κ) (d.spaceCell κ') (projection d.sideLengths w) =
        projection d.sideLengths (realAffine (G.reflectionTo κ κ') w) := by
  obtain ⟨hGOC, hInd, _, hST, _⟩ := hG 13 0 d
  have hcar : d.MapsCubeTo (d.cubeTransporter κ κ') κ κ' := (hGOC.2.1 κ κ').2.1
  obtain ⟨gbar, hind, _, _⟩ := hInd.1 _ (d.cubeTransporter κ κ').2
  have hform : ∀ x, ((d.cubeTransporter κ κ' : d.reflectionGroup) : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) x =
      realAffine (G.reflectionTo κ κ') x :=
    h.apply_eq_realAffine (d.cubeTransporter κ κ').2 fun x hx => by
      rw [← hcar]
      exact ⟨x, hx, rfl⟩
  have hcell : d.MapsCellTo gbar (d.spaceCell κ) (d.spaceCell κ') := by
    refine ⟨⟨_, (d.cubeTransporter κ κ').2, hind⟩, ?_⟩
    show gbar '' (projection d.sideLengths '' d.cellCube κ) = projection d.sideLengths '' d.cellCube κ'
    rw [Set.image_image, ← hcar, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    exact congrFun hind x
  have hc0 : d.spaceCell κ ∈ d.spaceCells := ⟨κ, rfl⟩
  have hck : d.spaceCell κ' ∈ d.spaceCells := ⟨κ', rfl⟩
  obtain ⟨hu, hspec⟩ := hST.2 _ hc0 _ hck
  have he : d.cellTransporter (d.spaceCell κ) (d.spaceCell κ') = gbar := hu.unique hspec hcell
  refine ⟨hspec.1, fun w => ?_⟩
  rw [he]
  have := congrFun hind w
  simp only [Function.comp_apply] at this
  rw [this, hform]
private theorem IsCubicShape.pointImage_pointOfCoords (hG : GroupAndCells.AllHold) (h : IsCubicShape d G M m)
    (κ κ' z : Fin 4 → ℤ) :
    (d.symmetryOfMap (d.cellTransporter (d.spaceCell κ) (d.spaceCell κ'))).pointImage (pointOfCoords d z) =
      pointOfCoords d (intAffine (G.reflectionTo κ κ') z) := by
  obtain ⟨_, hInd, _⟩ := hG 13 0 d
  obtain ⟨hmem, hform⟩ := h.cellTransporter_spec hG κ κ'
  refine Subtype.ext ?_
  show (d.symmetryOfMap (d.cellTransporter (d.spaceCell κ) (d.spaceCell κ'))).toFun _ = _
  rw [hInd.2.1 _ hmem]
  show d.cellTransporter (d.spaceCell κ) (d.spaceCell κ') (projection d.sideLengths _) = projection d.sideLengths _
  rw [hform, realAffine_intCast]
variable [NeZero m]
private theorem measurable_pullbackBy (g : TorusIsometry) : Measurable (pullbackBy (m := m) g) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun k => ?_
  unfold pullbackBy
  split_ifs
  · exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact continuous_inv.measurable.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))
private theorem ofTorusSite_mapSite (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (κ κ' : Fin 4 → ℤ) (x : TorusSite m) :
    ofTorusSite d ((G.reflectionTo κ κ').mapSite x) =
      pointOfCoords d (intAffine (G.reflectionTo κ κ') fun μ => ((x μ).cast : ℤ)) := by
  refine (pointOfCoords_eq_iff hd _ _).mpr fun μ => ?_
  have hp : (G.reflectionTo κ κ').axisPerm μ = μ := rfl
  simp only [TorusIsometry.mapSite, intAffine, ZMod.intCast_zmod_cast, hp]
  push_cast
  simp
private theorem IsCubicShape.pointImage_ofTorusSite (hG : GroupAndCells.AllHold) (h : IsCubicShape d G M m)
    (κ κ' : Fin 4 → ℤ) (x : TorusSite m) :
    (d.symmetryOfMap (d.cellTransporter (d.spaceCell κ) (d.spaceCell κ'))).pointImage (ofTorusSite d x) =
      ofTorusSite d ((G.reflectionTo κ κ').mapSite x) := by
  rw [ofTorusSite_mapSite h.sideLengths_eq]
  exact h.pointImage_pointOfCoords hG κ κ' _
private theorem IsCubicShape.pullback_configOfField (hG : GroupAndCells.AllHold) (hLat : GridLattice.Properties)
    (h : IsCubicShape d G M m) (h2 : 2 < m) (κ κ' : Fin 4 → ℤ) (W' : TorusField m) :
    (d.symmetryOfMap (d.cellTransporter (d.spaceCell κ) (d.spaceCell κ'))).pullback
        (configOfField h.sideLengths_eq h2 W') =
      configOfField h.sideLengths_eq h2 (pullbackBy (G.reflectionTo κ κ') W') := by
  obtain ⟨_, _, hCfg, hLinks, _⟩ := hLat 13 0 d
  have hd := h.sideLengths_eq
  funext b
  obtain ⟨⟨x, ν⟩, rfl⟩ := (forwardEdgeEquiv hd h2).surjective b
  have e : forwardEdgeEquiv hd h2 (x, ν) = forwardEdgeOf d (x, ν) := rfl
  rw [e, configOfField_forwardEdgeOf]
  set S := d.symmetryOfMap (d.cellTransporter (d.spaceCell κ) (d.spaceCell κ')) with hS
  set g := G.reflectionTo κ κ' with hg
  show edgeVariable (configOfField hd h2 W') (S.edgeImage (edgeFrom (ofTorusSite d x) ν)) = _
  obtain ⟨ht, hh⟩ := S.edgeImage_endpoints hLinks (edgeFrom (ofTorusSite d x) ν)
  have ht' : (S.edgeImage (edgeFrom (ofTorusSite d x) ν)).source = ofTorusSite d (g.mapSite x) :=
    ht.trans (h.pointImage_ofTorusSite hG κ κ' x)
  have hh' : (S.edgeImage (edgeFrom (ofTorusSite d x) ν)).target = ofTorusSite d (g.mapSite (x + unitStep m ν)) := by
    rw [hh]
    show S.pointImage (ofTorusSite d x + gridStep 13 0 d.sideLengths ν) = _
    rw [← ofTorusSite_add_unitStep hd]
    exact h.pointImage_ofTorusSite hG κ κ' _
  have hdir : g.axisPerm.symm ν = ν := rfl
  rcases g.axisSign_unit ν with hs | hs
  · have hadd : g.mapSite (x + unitStep m ν) = g.mapSite x + unitStep m ν := mapSite_add_unitStep_of_pos g x ν hs
    have heq : S.edgeImage (edgeFrom (ofTorusSite d x) ν) = edgeFrom (ofTorusSite d (g.mapSite x)) ν := by
      refine BoxTorus.DirectedEdge.ext ht' ?_
      rw [hh', hadd, ofTorusSite_add_unitStep hd]
      rfl
    rw [heq, edgeVariable_edgeFrom]
    simp only [pullbackBy, hdir, hs, if_true]
  · have hsub : g.mapSite (x + unitStep m ν) = g.mapSite x - unitStep m ν := mapSite_add_unitStep_of_neg g x ν hs
    have hne : g.axisSign ν ≠ 1 := by
      rw [hs]
      norm_num
    have heq : S.edgeImage (edgeFrom (ofTorusSite d x) ν) =
        (edgeFrom (ofTorusSite d (g.mapSite x - unitStep m ν)) ν).flip := by
      refine BoxTorus.DirectedEdge.ext ?_ ?_
      · rw [ht']
        show _ = ofTorusSite d (g.mapSite x - unitStep m ν) + gridStep 13 0 d.sideLengths ν
        rw [← ofTorusSite_add_unitStep hd, sub_add_cancel]
      · rw [hh', hsub]
        rfl
    rw [heq, hCfg.1, edgeVariable_edgeFrom]
    simp only [pullbackBy, hdir, if_neg hne, map_inv]
end PeriodicSpace
section CellObservables
variable {d : Construction.CellGrid 13 0} {G : CellWindows.CellGrid} {M m : ℕ}
private theorem IsCubicShape.mem_interior_spaceCell (hG : GroupAndCells.AllHold) (h : IsCubicShape d G M m)
    {κ z : Fin 4 → ℤ} (hz : ∀ μ, G.offset μ + G.side * κ μ ≤ z μ ∧ z μ < G.offset μ + G.side * κ μ + G.side) :
    ((pointOfCoords d z : d.GridPoint) : d.Space) ∈ interior (d.spaceCell κ) := by
  obtain ⟨_, hInd, _, _, _, hRefl, _⟩ := hG 13 0 d
  obtain ⟨θ, hθ, _, _⟩ := hInd.1 (d.faceReflectEquiv 0 0) (Subgroup.subset_closure ⟨(0, 0), rfl⟩)
  have hint := (hRefl 0 0 θ hθ).2.2.1 κ
  rw [hint]
  refine ⟨fun μ => (z μ : ℝ) * meshSize 13 0, ?_, rfl⟩
  refine mem_interior.mpr ⟨Set.pi Set.univ fun μ => Set.Ioo (d.centre μ + G.side * κ μ) (d.centre μ + G.side * κ μ + G.side),
    ?_, isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo, fun μ _ => ?_⟩
  · intro x hx
    have e : x = d.centre + (G.side : ℝ) • (fun μ => (κ μ : ℝ)) +
        (x - (d.centre + (G.side : ℝ) • (fun μ => (κ μ : ℝ)))) := by simp
    rw [e]
    refine h.mem_cellCube κ fun μ => ?_
    have := hx μ (Set.mem_univ _)
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · have h1 := hz μ
    have h2 : ((G.offset μ + G.side * κ μ : ℤ) : ℝ) ≤ z μ := by exact_mod_cast h1.1
    have h3 : ((z μ + 1 : ℤ) : ℝ) ≤ ((G.offset μ + G.side * κ μ + G.side : ℤ) : ℝ) := by exact_mod_cast h1.2
    push_cast at h2 h3
    show (z μ : ℝ) * meshSize 13 0 ∈ Set.Ioo (d.centre μ + G.side * κ μ) (d.centre μ + G.side * κ μ + G.side)
    rw [h.centre, meshSize_zero_eq_one, mul_one]
    constructor <;> linarith
variable [NeZero m]
private theorem IsCubicShape.ofTorusSite_mem_interior (hG : GroupAndCells.AllHold) (h : IsCubicShape d G M m)
    {κ : Fin 4 → ℤ} {x : TorusSite m} (hx : x ∈ G.cell m κ) :
    ((ofTorusSite d x : d.GridPoint) : d.Space) ∈ interior (d.spaceCell κ) := by
  classical
  unfold CellWindows.CellGrid.cell at hx
  obtain ⟨t, ht, rfl⟩ := (Finset.mem_filter.mp hx).2
  rw [ofTorusSite_siteOfInt h.sideLengths_eq]
  refine h.mem_interior_spaceCell hG fun μ => ?_
  have := ht μ
  constructor <;> omega
private theorem IsCubicShape.mem_cellObservables (hG : GroupAndCells.AllHold) (h : IsCubicShape d G M m) (h2 : 2 < m)
    {F : TorusField m → ℝ} (hFm : Measurable F) (hFb : ∃ C, ∀ W, |F W| ≤ C) {κ : Fin 4 → ℤ}
    (hread : DependsOnlyOn (G.cell m κ) F) (c : d.spaceCells) (hc : c.1 = d.spaceCell κ) :
    (fun U : d.GaugeConfig => ((F (fieldOfConfig h.sideLengths_eq h2 U) : ℝ) : ℂ)) ∈ d.cellObservables c := by
  classical
  have hd := h.sideLengths_eq
  obtain ⟨C, hC⟩ := hFb
  set E := d.edgesWithin (TopologicalSpace.Opens.interior c.1) with hE
  let extend : (↥(forwardPart E) → Conventions.StandingParameters.gaugeGroup) → d.GaugeConfig := fun w b =>
    if hb : b ∈ forwardPart E then w ⟨b, hb⟩ else 1
  have hextend : Measurable extend := by
    refine measurable_pi_iff.mpr fun b => ?_
    by_cases hb : b ∈ forwardPart E
    · simp only [extend, dif_pos hb]
      exact measurable_pi_apply _
    · simp only [extend, dif_neg hb]
      exact measurable_const
  refine ⟨fun w => ((F (fieldOfConfig hd h2 (extend w)) : ℝ) : ℂ), ?_, ⟨C, fun w => ?_⟩, fun U => ?_⟩
  · exact Complex.measurable_ofReal.comp (hFm.comp ((measurable_fieldOfConfig hd h2).comp hextend))
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact hC _
  · show ((F (fieldOfConfig hd h2 U) : ℝ) : ℂ) = ((F (fieldOfConfig hd h2 (extend fun b => U b.1)) : ℝ) : ℂ)
    congr 1
    refine hread _ _ fun b hb₁ hb₂ => ?_
    have hb : forwardEdgeEquiv hd h2 (b.1, b.2) ∈ forwardPart E := by
      refine Or.inl ⟨?_, ?_⟩
      · show ((ofTorusSite d b.1 : d.GridPoint) : d.Space) ∈ interior c.1
        rw [hc]
        exact h.ofTorusSite_mem_interior hG hb₁
      · show ((ofTorusSite d b.1 + gridStep 13 0 d.sideLengths b.2 : d.GridPoint) : d.Space) ∈ interior c.1
        rw [hc, ← ofTorusSite_add_unitStep hd]
        exact h.ofTorusSite_mem_interior hG hb₂
    simp only [fieldOfConfig, extend, dif_pos hb]
end CellObservables
section Comparison
variable {d : Construction.CellGrid 13 0} {G : CellWindows.CellGrid} {M m : ℕ}
private theorem IsCubicShape.div_side (h : IsCubicShape d G M m) : m / G.side = M := by
  rw [h.m_eq]
  exact Nat.mul_div_cancel_left _ h.side_pos
private theorem IsCubicShape.mem_indices (h : IsCubicShape d G M m) {κ : Fin 4 → ℤ} :
    κ ∈ G.indices m ↔ ∀ μ, 0 ≤ κ μ ∧ κ μ < (M : ℤ) := by
  simp only [CellWindows.CellGrid.indices, Fintype.mem_piFinset, Finset.mem_Ico, h.div_side]
private theorem IsCubicShape.card_indices (h : IsCubicShape d G M m) : (G.indices m).card = M ^ 4 := by
  simp [CellWindows.CellGrid.indices, Fintype.card_piFinset, h.div_side]
private def cellAt (d : Construction.CellGrid 13 0) (κ : Fin 4 → ℤ) : d.spaceCells := ⟨d.spaceCell κ, ⟨κ, rfl⟩⟩
private theorem IsCubicShape.spaceCell_eq_iff (hG : GroupAndCells.AllHold) (h : IsCubicShape d G M m)
    (a b : Fin 4 → ℤ) :
    d.spaceCell a = d.spaceCell b ↔ ∀ μ, (M : ℤ) ∣ b μ - a μ := by
  obtain ⟨_, _, hCells, _⟩ := hG 13 0 d
  rw [hCells.1]
  constructor
  · intro he μ
    have h1 := congrFun he μ
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
    rwa [h.counts] at h2
  · intro he
    funext μ
    refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ?_
    rw [h.counts]
    exact he μ
private theorem IsCubicShape.cellAt_injOn (hG : GroupAndCells.AllHold) (h : IsCubicShape d G M m)
    {κ κ' : Fin 4 → ℤ} (hκ : κ ∈ G.indices m) (hκ' : κ' ∈ G.indices m) (he : cellAt d κ = cellAt d κ') : κ = κ' := by
  have h1 := (h.spaceCell_eq_iff hG _ _).mp (congrArg Subtype.val he)
  funext μ
  have a1 := h.mem_indices.mp hκ μ
  have a2 := h.mem_indices.mp hκ' μ
  have h3 : κ' μ - κ μ = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd (h1 μ) ?_
    rw [abs_lt]
    constructor <;> omega
  omega
private theorem IsCubicShape.exists_cellAt_eq (hG : GroupAndCells.AllHold) (h : IsCubicShape d G M m) (hM0 : 0 < M)
    (c : d.spaceCells) : ∃ κ ∈ G.indices m, cellAt d κ = c := by
  obtain ⟨_, z, rfl⟩ := c
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM0.ne'
  refine ⟨fun μ => z μ % M, h.mem_indices.mpr fun μ => ⟨Int.emod_nonneg _ hMz, Int.emod_lt_of_pos _ (by exact_mod_cast hM0)⟩,
    Subtype.ext ?_⟩
  refine (h.spaceCell_eq_iff hG _ _).mpr fun μ => ?_
  exact Int.dvd_self_sub_emod
private def IsCubicShape.indicesEquiv (hG : GroupAndCells.AllHold) (h : IsCubicShape d G M m) (hM0 : 0 < M) :
    ↥(G.indices m) ≃ d.spaceCells :=
  Equiv.ofBijective (fun κ => cellAt d κ.1)
    ⟨fun a b he => Subtype.ext (h.cellAt_injOn hG a.2 b.2 he), fun c => by
      obtain ⟨κ, hκ, he⟩ := h.exists_cellAt_eq hG hM0 c
      exact ⟨⟨κ, hκ⟩, he⟩⟩
variable [NeZero m]
private theorem IsCubicShape.checkerboardCopy_configOfField (hG : GroupAndCells.AllHold)
    (hLat : GridLattice.Properties) (h : IsCubicShape d G M m) (h2 : 2 < m) {κ κ' : Fin 4 → ℤ}
    {c c' : d.spaceCells} (hc : c.1 = d.spaceCell κ) (hc' : c'.1 = d.spaceCell κ') (F₀ : d.cellObservables c)
    {F : TorusField m → ℝ} (hF₀ : ∀ U, F₀.1 U = ((F (fieldOfConfig h.sideLengths_eq h2 U) : ℝ) : ℂ))
    (W' : TorusField m) :
    d.checkerboardCopy c c' F₀ (configOfField h.sideLengths_eq h2 W') = ((cellCopy G κ κ' F W' : ℝ) : ℂ) := by
  have hd := h.sideLengths_eq
  have e := h.pullback_configOfField hG hLat h2 κ κ' W'
  have hval : (d.symmetryOfMap (d.cellTransporter c.1 c'.1)).actOnObservables F₀.1 (configOfField hd h2 W') =
      ((cellCopy G κ κ' F W' : ℝ) : ℂ) := by
    show F₀.1 ((d.symmetryOfMap (d.cellTransporter c.1 c'.1)).pullback (configOfField hd h2 W')) = _
    rw [hc, hc', e, hF₀, fieldOfConfig_configOfField]
    rfl
  unfold Construction.CellGrid.checkerboardCopy
  split_ifs
  · exact hval
  · show starRingEnd ℂ _ = _
    rw [hval, Complex.conj_ofReal]
private theorem IsCubicShape.copiesProductMean_eq (hG : GroupAndCells.AllHold) (hLat : GridLattice.Properties)
    (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm) (h : IsCubicShape d G M m) (h2 : 2 < m) (hM0 : 0 < M) (β : ℝ)
    {κ : Fin 4 → ℤ} {c : d.spaceCells} (hc : c.1 = d.spaceCell κ) (F₀ : d.cellObservables c)
    {F : TorusField m → ℝ} (hFm : Measurable F)
    (hF₀ : ∀ U, F₀.1 U = ((F (fieldOfConfig h.sideLengths_eq h2 U) : ℝ) : ℂ)) :
    d.copiesProductMean β c F₀ = ((copyProductMean G β κ (G.indices m) F : ℝ) : ℂ) := by
  classical
  have hd := h.sideLengths_eq
  have hprod : ∀ W', ∏ᶠ c' : d.spaceCells, d.checkerboardCopy c c' F₀ (configOfField hd h2 W') =
      ((∏ κ' ∈ G.indices m, cellCopy G κ κ' F W' : ℝ) : ℂ) := by
    intro W'
    rw [← finprod_comp_equiv (h.indicesEquiv hG hM0), finprod_eq_prod_of_fintype]
    push_cast
    rw [← Finset.prod_coe_sort (G.indices m) fun κ' => ((cellCopy G κ κ' F W' : ℝ) : ℂ)]
    exact Finset.prod_congr rfl fun κ' _ => h.checkerboardCopy_configOfField hG hLat h2 hc rfl F₀ hF₀ W'
  have hfun : (fun U => ∏ᶠ c' : d.spaceCells, d.checkerboardCopy c c' F₀ U) =
      fun U => ((∏ κ' ∈ G.indices m, cellCopy G κ κ' F (fieldOfConfig hd h2 U) : ℝ) : ℂ) := by
    funext U
    have := hprod (fieldOfConfig hd h2 U)
    rwa [configOfField_fieldOfConfig] at this
  have hcm : ∀ κ', Measurable (cellCopy G κ κ' F) := fun κ' => hFm.comp (measurable_pullbackBy _)
  have hm : Measurable fun U : d.GaugeConfig =>
      ((∏ κ' ∈ G.indices m, cellCopy G κ κ' F (fieldOfConfig hd h2 U) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (Finset.measurable_prod _ fun κ' _ => (hcm κ').comp (measurable_fieldOfConfig hd h2))
  unfold Construction.CellGrid.copiesProductMean
  rw [hfun, gibbsMean_eq hq hd h2 β hm]
  simp only [fieldOfConfig_configOfField]
  exact integral_ofReal
private theorem IsCubicShape.checkerboardNorm_eq (hG : GroupAndCells.AllHold) (hLat : GridLattice.Properties)
    (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm) (h : IsCubicShape d G M m) (h2 : 2 < m) (hM0 : 0 < M) (β : ℝ)
    {κ : Fin 4 → ℤ} {c : d.spaceCells} (hc : c.1 = d.spaceCell κ) (F₀ : d.cellObservables c)
    {F : TorusField m → ℝ} (hFm : Measurable F)
    (hF₀ : ∀ U, F₀.1 U = ((F (fieldOfConfig h.sideLengths_eq h2 U) : ℝ) : ℂ)) :
    d.checkerboardNorm β c F₀ = chessboardNorm G β κ F := by
  have hcount : (d.numCells : ℝ) = ((G.indices m).card : ℝ) := by
    have : d.numCells = (G.indices m).card := by
      rw [h.card_indices]
      show ∏ μ, d.counts μ = M ^ 4
      simp [h.counts]
    rw [this]
  unfold Construction.CellGrid.checkerboardNorm chessboardNorm
  rw [h.copiesProductMean_eq hG hLat hq h2 hM0 β hc F₀ hFm hF₀, Complex.ofReal_re, hcount]
private theorem IsCubicShape.chessboard_bounds (hEst : Construction.CellGrid.CheckerboardBoundAtAllGrids)
    (hSem : CheckerboardSeminorms.Statement) (hG : GroupAndCells.AllHold)
    (hLat : GridLattice.Properties) (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm)
    (h : IsCubicShape d G M m) (h2 : 2 < m) (hM0 : 0 < M) {β : ℝ} (hβ : 0 < β) :
    (∀ (κ : Fin 4 → ℤ) (F : TorusField m → ℝ), κ ∈ G.indices m → Measurable F → (∃ M, ∀ W, |F W| ≤ M) →
      DependsOnlyOn (G.cell m κ) F → 0 ≤ copyProductMean G β κ (G.indices m) F) ∧
    ∀ (A : Finset (Fin 4 → ℤ)) (F : (Fin 4 → ℤ) → TorusField m → ℝ), A ⊆ G.indices m →
      (∀ κ ∈ A, Measurable (F κ) ∧ (∃ M, ∀ W, |F κ W| ≤ M) ∧ (∀ W, 0 ≤ F κ W) ∧ DependsOnlyOn (G.cell m κ) (F κ)) →
      ∫ W, ∏ κ ∈ A, F κ W ∂(wilsonLaw β m) ≤ ∏ κ ∈ A, chessboardNorm G β κ (F κ) := by
  classical
  have hd := h.sideLengths_eq
  refine ⟨fun κ F _ hFm hFb hread => ?_, fun A F hA hF => ?_⟩
  · let c := cellAt d κ
    let F₀ : d.cellObservables c := ⟨_, h.mem_cellObservables hG h2 hFm hFb hread c rfl⟩
    have h0 := (hEst 13 0 d β hβ).1 c F₀
    rw [h.copiesProductMean_eq hG hLat hq h2 hM0 β (κ := κ) rfl F₀ hFm (fun U => rfl)] at h0
    exact Complex.zero_le_real.mp h0
  · let S : Set d.spaceCells := cellAt d '' (A : Set (Fin 4 → ℤ))
    let a : ↥A → ↥S := fun κ => ⟨cellAt d κ.1, κ.1, Finset.mem_coe.mpr κ.2, rfl⟩
    have hab : Function.Bijective a := by
      constructor
      · intro x y he
        exact Subtype.ext (h.cellAt_injOn hG (hA x.2) (hA y.2) (congrArg Subtype.val he))
      · rintro ⟨_, κ, hκ, rfl⟩
        exact ⟨⟨κ, Finset.mem_coe.mp hκ⟩, rfl⟩
    let ES : ↥A ≃ ↥S := Equiv.ofBijective a hab
    have hcell : ∀ c' : S, c'.1.1 = d.spaceCell (ES.symm c').1 := fun c' => by
      conv_lhs => rw [← ES.apply_symm_apply c']
      rfl
    let Gs : (c' : S) → d.cellObservables c'.1 := fun c' =>
      ⟨_, h.mem_cellObservables hG h2 (hF _ (ES.symm c').2).1 (hF _ (ES.symm c').2).2.1 (hF _ (ES.symm c').2).2.2.2
        c'.1 (hcell c')⟩
    have hGs : ∀ (κ : ↥A) U, (Gs (ES κ)).1 U = ((F κ.1 (fieldOfConfig hd h2 U) : ℝ) : ℂ) := fun κ U => by
      show ((F (ES.symm (ES κ)).1 (fieldOfConfig hd h2 U) : ℝ) : ℂ) = _
      rw [ES.symm_apply_apply]
    have hest := (hSem 13 0 d β hβ (cellAt d 0) (d.cellOne _) (d.cellOne _) 0).2.2.2 S Gs
    have hfun : (fun U => ∏ᶠ c' : S, (Gs c').1 U) = fun U => ((∏ κ ∈ A, F κ (fieldOfConfig hd h2 U) : ℝ) : ℂ) := by
      funext U
      rw [← finprod_comp_equiv ES, finprod_eq_prod_of_fintype]
      push_cast
      rw [← Finset.prod_coe_sort A fun κ => ((F κ (fieldOfConfig hd h2 U) : ℝ) : ℂ)]
      exact Finset.prod_congr rfl fun κ _ => hGs κ U
    have hval : ∏ᶠ c' : S, d.checkerboardNorm β c'.1 (Gs c') = ∏ κ ∈ A, chessboardNorm G β κ (F κ) := by
      rw [← finprod_comp_equiv ES, finprod_eq_prod_of_fintype,
        ← Finset.prod_coe_sort A fun κ => chessboardNorm G β κ (F κ)]
      exact Finset.prod_congr rfl fun κ _ =>
        h.checkerboardNorm_eq hG hLat hq h2 hM0 β (κ := κ.1) rfl (Gs (ES κ)) (hF _ κ.2).1 (hGs κ)
    rw [hfun, hval] at hest
    have hm : Measurable fun U : d.GaugeConfig => ((∏ κ ∈ A, F κ (fieldOfConfig hd h2 U) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp
        (Finset.measurable_prod _ fun κ hκ => (hF κ hκ).1.comp (measurable_fieldOfConfig hd h2))
    rw [gibbsMean_eq hq hd h2 β hm] at hest
    simp only [fieldOfConfig_configOfField] at hest
    have hi : ∫ W, ((∏ κ ∈ A, F κ W : ℝ) : ℂ) ∂(wilsonLaw β m) =
        ((∫ W, ∏ κ ∈ A, F κ W ∂(wilsonLaw β m) : ℝ) : ℂ) :=
      integral_ofReal
    rw [hi, Complex.norm_real, Real.norm_eq_abs] at hest
    exact (le_abs_self _).trans hest
end Comparison
section UnitSide
variable {m : ℕ} [NeZero m]
private theorem isProbabilityMeasure_wilsonLaw (β : ℝ) : IsProbabilityMeasure (wilsonLaw β m) := by apply _root_.YangMills.SharedProofs.p2076 <;> assumption
private theorem eq_of_dependsOnlyOn_of_side_eq_one (hm : 1 < m) {G : CellWindows.CellGrid} (hs : G.side = 1)
    {κ : Fin 4 → ℤ} {F : TorusField m → ℝ} (hr : DependsOnlyOn (G.cell m κ) F) (W W' : TorusField m) :
    F W = F W' := by
  classical
  refine hr W W' fun b h1 h2 => ?_
  exfalso
  have key : ∀ x ∈ G.cell m κ, x = siteOfInt fun i => G.offset i + (G.side : ℤ) * κ i := by
    intro x hx
    unfold CellWindows.CellGrid.cell at hx
    obtain ⟨t, ht, rfl⟩ := (Finset.mem_filter.mp hx).2
    have ht0 : t = 0 := by
      funext i
      have := ht i
      rw [hs] at this
      simp only [Pi.zero_apply]
      push_cast at this
      omega
    simp [ht0]
  have e : b.1 + unitStep m b.2 = b.1 := (key _ h2).trans (key _ h1).symm
  have e0 : unitStep m b.2 = 0 := by simpa using e
  haveI : Fact (1 < m) := ⟨hm⟩
  have := congrFun e0 b.2
  simp [unitStep] at this
private theorem chessboard_bounds_of_side_eq_one (hm : 1 < m) (hev : Even m) {G : CellWindows.CellGrid}
    (hs : G.side = 1) (β : ℝ) :
    (∀ (κ : Fin 4 → ℤ) (F : TorusField m → ℝ), κ ∈ G.indices m → Measurable F → (∃ M, ∀ W, |F W| ≤ M) →
      DependsOnlyOn (G.cell m κ) F → 0 ≤ copyProductMean G β κ (G.indices m) F) ∧
    ∀ (A : Finset (Fin 4 → ℤ)) (F : (Fin 4 → ℤ) → TorusField m → ℝ), A ⊆ G.indices m →
      (∀ κ ∈ A, Measurable (F κ) ∧ (∃ M, ∀ W, |F κ W| ≤ M) ∧ (∀ W, 0 ≤ F κ W) ∧ DependsOnlyOn (G.cell m κ) (F κ)) →
      ∫ W, ∏ κ ∈ A, F κ W ∂(wilsonLaw β m) ≤ ∏ κ ∈ A, chessboardNorm G β κ (F κ) := by
  haveI := isProbabilityMeasure_wilsonLaw (m := m) β
  have hcard : (G.indices m).card = m ^ 4 := by
    simp [CellWindows.CellGrid.indices, Fintype.card_piFinset, hs]
  have hN : (G.indices m).card ≠ 0 := by
    rw [hcard]
    exact pow_ne_zero _ (by omega)
  have hNe : Even (G.indices m).card := by
    rw [hcard]
    exact hev.pow_of_ne_zero (by norm_num)
  have meanc : ∀ (κ : Fin 4 → ℤ) (F : TorusField m → ℝ), DependsOnlyOn (G.cell m κ) F →
      copyProductMean G β κ (G.indices m) F = F (trivialField m) ^ (G.indices m).card := by
    intro κ F hr
    have hc : ∀ W, ∏ κ' ∈ G.indices m, cellCopy G κ κ' F W = F (trivialField m) ^ (G.indices m).card := fun W => by
      have hk : ∀ κ' ∈ G.indices m, cellCopy G κ κ' F W = F (trivialField m) := fun κ' _ =>
        eq_of_dependsOnlyOn_of_side_eq_one hm hs hr _ _
      rw [Finset.prod_congr rfl hk]
      simp
    unfold copyProductMean
    simp only [hc]
    simp
  refine ⟨fun κ F _ _ _ hr => ?_, fun A F _ hF => ?_⟩
  · rw [meanc _ _ hr]
    exact hNe.pow_nonneg _
  · have hc : ∀ W, ∏ κ ∈ A, F κ W = ∏ κ ∈ A, F κ (trivialField m) := fun W =>
      Finset.prod_congr rfl fun κ hκ => eq_of_dependsOnlyOn_of_side_eq_one hm hs (hF κ hκ).2.2.2 W _
    simp only [hc]
    simp only [integral_const, probReal_univ, one_smul]
    refine (Finset.prod_congr rfl fun κ hκ => ?_).le
    unfold chessboardNorm
    rw [meanc _ _ (hF κ hκ).2.2.2, one_div, Real.pow_rpow_inv_natCast ((hF κ hκ).2.2.1 _) hN]
end UnitSide
theorem chessboardEstimate_holds (hEst : Construction.CellGrid.CheckerboardBoundAtAllGrids)
    (hSem : CheckerboardSeminorms.Statement) (hG : GroupAndCells.AllHold)
    (hLat : GridLattice.Properties) (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm) :
    chessboardEstimateStatement := by
  intro β m _ G hβ hfit hodd
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨t, ht⟩ := hfit.two_mul_side_dvd
  have hc := hfit.side_pos
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp at ht
      omega
    · exact h
  by_cases h4 : 4 ≤ m
  · have hm' : m = G.side * (2 * t) := by
      rw [ht]
      ring
    have h4' : 4 ≤ G.side * (2 * t) := hm' ▸ h4
    have hoff : ∀ μ, (((G.offset μ + ((G.side : ℤ) - 1) / 2 : ℤ) : ℝ)) - (G.side : ℝ) / 2 = (G.offset μ : ℝ) - 1 / 2 := by
      intro μ
      obtain ⟨r, hr⟩ := hodd
      have e1 : ((G.side : ℤ) - 1) / 2 = r := by omega
      have e2 : (G.side : ℝ) = 2 * r + 1 := by exact_mod_cast hr
      rw [e1, e2]
      push_cast
      ring
    have hsh : IsCubicShape (cubicCellGrid G.side (2 * t) (fun i => G.offset i + ((G.side : ℤ) - 1) / 2) hodd
        (even_two_mul t) (by omega) h4') G (2 * t) m := ⟨rfl, fun _ => rfl, hoff, hm', hc⟩
    exact hsh.chessboard_bounds hEst hSem hG hLat hq (by omega) (by omega) hβ
  · have h1 : G.side ≤ G.side * t := Nat.le_mul_of_pos_right _ ht0
    have h2 : m = 2 * (G.side * t) := by
      rw [ht]
      ring
    have hs : G.side = 1 := by omega
    exact chessboard_bounds_of_side_eq_one (by omega) ⟨G.side * t, by omega⟩ hs β
end YangMills.Construction.CellWindows
end
