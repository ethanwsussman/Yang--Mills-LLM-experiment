import YangMills.Construction.FormsOnATorus.ChessboardOnTheFieldsOfATorus
import YangMills.Construction.FormsOnATorus.FieldsOfAGridOfCells
import YangMills.Construction.Lattice.ChessboardValuesAsSeminormsOfAGridDatum
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction
open BoxTorus
open PeriodicLattice (meshSize)
open InfiniteLattice (AmbientSpace)
open WeightedResponses TorusLumps CubicGridFields
namespace TorusFields
section Group
variable {d : CellGrid 13 0}
private def ActsAxiswise (d : CellGrid 13 0) (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : Prop :=
  ∀ μ, (∃ t : ℤ, ∀ x : AmbientSpace, g x μ = x μ + 2 * d.cellLength * t) ∨
    ∃ t : ℤ, ∀ x : AmbientSpace, g x μ = -x μ + 2 * d.centre μ + 2 * d.cellLength * t
private theorem actsAxiswise_of_mem {g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace} (hg : g ∈ d.reflectionGroup) :
    ActsAxiswise d g := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨⟨ν, a⟩, rfl⟩ := hg
    intro μ
    by_cases h : μ = ν
    · subst h
      refine Or.inr ⟨a, fun x => ?_⟩
      simp only [CellGrid.coe_faceReflectEquiv, CellGrid.faceReflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        basisVector, Pi.single_eq_same]
      ring
    · refine Or.inl ⟨0, fun x => ?_⟩
      simp [CellGrid.coe_faceReflectEquiv, CellGrid.faceReflect, basisVector, Pi.single_eq_of_ne h]
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
private structure CubicShape (d : CellGrid 13 0) (c M m : ℕ) (u : Fin 4 → ℤ) : Prop where
  length_eq : d.cellLength = c
  counts_eq : ∀ μ, d.counts μ = M
  centre_eq : ∀ μ, d.centre μ = (u μ : ℝ) - (c : ℝ) / 2
  size_eq : m = c * M
  length_pos : 0 < c
variable {c M m : ℕ} {u : Fin 4 → ℤ}
private theorem sideLengths_of_shape (h : CubicShape d c M m u) (μ : Fin 4) : d.sideLengths μ = (m : ℝ) := by
  show (d.counts μ : ℝ) * d.cellLength = _
  rw [h.counts_eq, h.length_eq, h.size_eq]
  push_cast
  ring
private theorem mem_cellCube_zero (h : CubicShape d c M m u) {y : AmbientSpace} (hy : ∀ μ, 0 ≤ y μ ∧ y μ ≤ c) :
    d.centre + y ∈ d.cellCube 0 := by
  refine ⟨y, fun μ _ => ?_, ?_⟩
  · rw [h.length_eq]
    exact hy μ
  · funext μ
    simp
private theorem coord_bounds_of_mem_cellCube (h : CubicShape d c M m u) {κ : Fin 4 → ℤ} {x : AmbientSpace}
    (hx : x ∈ d.cellCube κ) (μ : Fin 4) :
    d.centre μ + c * κ μ ≤ x μ ∧ x μ ≤ d.centre μ + c * κ μ + c := by
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 := hy μ (Set.mem_univ _)
  rw [h.length_eq] at h1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h.length_eq]
  constructor <;> linarith [h1.1, h1.2]
private def reflectReal (c : ℕ) (u κ : Fin 4 → ℤ) (x : AmbientSpace) : AmbientSpace := fun μ =>
  (((-1 : ℤ) ^ (κ μ).natAbs : ℤ) : ℝ) * x μ + ((u μ + c * κ μ - (-1) ^ (κ μ).natAbs * u μ : ℤ) : ℝ)
private theorem eq_reflectReal_of_maps (h : CubicShape d c M m u) {g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace}
    (hg : g ∈ d.reflectionGroup) {κ : Fin 4 → ℤ}
    (hc : ∀ x ∈ d.cellCube 0, g x ∈ d.cellCube κ) (x : AmbientSpace) : g x = reflectReal c u κ x := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast h.length_pos
  have hx₀ : d.centre ∈ d.cellCube 0 := by
    have := mem_cellCube_zero h (y := 0) fun μ => ⟨le_rfl, by simp⟩
    simpa using this
  have hx₁ : d.centre + (fun _ => (c : ℝ)) ∈ d.cellCube 0 := mem_cellCube_zero h fun μ => ⟨hc0.le, le_rfl⟩
  funext μ
  have a₀ := coord_bounds_of_mem_cellCube h (hc _ hx₀) μ
  have a₁ := coord_bounds_of_mem_cellCube h (hc _ hx₁) μ
  rcases actsAxiswise_of_mem hg μ with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht] at a₀ a₁
    rw [h.length_eq] at ht
    simp only [Pi.add_apply, h.length_eq] at a₀ a₁
    have e1 : (κ μ : ℝ) ≤ 2 * t := by
      have : (c : ℝ) * κ μ ≤ c * (2 * t) := by linarith [a₀.1]
      exact le_of_mul_le_mul_left this hc0
    have e2 : (2 * (t : ℝ)) ≤ κ μ := by
      have : (c : ℝ) * (2 * t) ≤ c * κ μ := by linarith [a₁.2]
      exact le_of_mul_le_mul_left this hc0
    have e3 : κ μ = 2 * t := by
      have : (κ μ : ℝ) = ((2 * t : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    have hs : ((-1 : ℤ) ^ (κ μ).natAbs : ℤ) = 1 := by
      rw [e3]
      exact Even.neg_one_pow (Int.natAbs_even.mpr (even_two_mul t))
    show g x μ = _
    rw [ht]
    simp only [reflectReal, hs]
    rw [e3]
    push_cast
    ring
  · rw [ht] at a₀ a₁
    rw [h.length_eq] at ht
    simp only [Pi.add_apply, h.length_eq] at a₀ a₁
    have e1 : (κ μ : ℝ) + 1 ≤ 2 * t := by
      have : (c : ℝ) * (κ μ + 1) ≤ c * (2 * t) := by linarith [a₁.1]
      exact le_of_mul_le_mul_left this hc0
    have e2 : (2 * (t : ℝ)) ≤ κ μ + 1 := by
      have : (c : ℝ) * (2 * t) ≤ c * (κ μ + 1) := by linarith [a₀.2]
      exact le_of_mul_le_mul_left this hc0
    have e3 : κ μ = 2 * t - 1 := by
      have : (κ μ : ℝ) = ((2 * t - 1 : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    have hodd : Odd (κ μ) := by
      rw [e3]
      exact ⟨t - 1, by ring⟩
    have hs : ((-1 : ℤ) ^ (κ μ).natAbs : ℤ) = -1 := Odd.neg_one_pow (Int.natAbs_odd.mpr hodd)
    show g x μ = _
    rw [ht]
    simp only [reflectReal, hs, h.centre_eq]
    rw [e3]
    push_cast
    ring
end Group
section Torus
variable {d : CellGrid 13 0} {c M m : ℕ} {u : Fin 4 → ℤ}
private def reflectInt (c : ℕ) (u κ z : Fin 4 → ℤ) : Fin 4 → ℤ := fun μ =>
  (-1) ^ (κ μ).natAbs * z μ + (u μ + c * κ μ - (-1) ^ (κ μ).natAbs * u μ)
private theorem reflectReal_intCast (c : ℕ) (u κ z : Fin 4 → ℤ) :
    reflectReal c u κ (fun μ => (z μ : ℝ) * meshSize 13 0) =
      fun μ => ((reflectInt c u κ z μ : ℤ) : ℝ) * meshSize 13 0 := by
  funext μ
  simp only [reflectReal, reflectInt, meshSize_zero_eq_one, mul_one]
  push_cast
  ring
private theorem cellTransporter_spec (hG : GroupAndCells.AllHold) (h : CubicShape d c M m u) (κ : Fin 4 → ℤ) :
    d.cellTransporter (d.spaceCell 0) (d.spaceCell κ) ∈ d.inducedGroupMaps ∧
      ∀ w, d.cellTransporter (d.spaceCell 0) (d.spaceCell κ) (projection d.sideLengths w) =
        projection d.sideLengths (reflectReal c u κ w) := by
  obtain ⟨hGOC, hInd, _, hST, _⟩ := hG 13 0 d
  have hcar : d.MapsCubeTo (d.cubeTransporter 0 κ) 0 κ := (hGOC.2.1 0 κ).2.1
  obtain ⟨gbar, hind, _, _⟩ := hInd.1 _ (d.cubeTransporter 0 κ).2
  have hform : ∀ x, ((d.cubeTransporter 0 κ : d.reflectionGroup) : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) x =
      reflectReal c u κ x :=
    eq_reflectReal_of_maps h (d.cubeTransporter 0 κ).2 fun x hx => by
      rw [← hcar]
      exact ⟨x, hx, rfl⟩
  have hcell : d.MapsCellTo gbar (d.spaceCell 0) (d.spaceCell κ) := by
    refine ⟨⟨_, (d.cubeTransporter 0 κ).2, hind⟩, ?_⟩
    show gbar '' (projection d.sideLengths '' d.cellCube 0) = projection d.sideLengths '' d.cellCube κ
    rw [Set.image_image, ← hcar, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    exact congrFun hind x
  have hc0 : d.spaceCell 0 ∈ d.spaceCells := ⟨0, rfl⟩
  have hck : d.spaceCell κ ∈ d.spaceCells := ⟨κ, rfl⟩
  obtain ⟨hu, hspec⟩ := hST.2 _ hc0 _ hck
  have he : d.cellTransporter (d.spaceCell 0) (d.spaceCell κ) = gbar := hu.unique hspec hcell
  refine ⟨hspec.1, fun w => ?_⟩
  rw [he]
  have := congrFun hind w
  simp only [Function.comp_apply] at this
  rw [this, hform]
private theorem pointImage_pointOfCoords (hG : GroupAndCells.AllHold) (h : CubicShape d c M m u) (κ z : Fin 4 → ℤ) :
    (d.symmetryOfMap (d.cellTransporter (d.spaceCell 0) (d.spaceCell κ))).pointImage (pointOfCoords d z) =
      pointOfCoords d (reflectInt c u κ z) := by
  obtain ⟨_, hInd, _⟩ := hG 13 0 d
  obtain ⟨hmem, hform⟩ := cellTransporter_spec hG h κ
  refine Subtype.ext ?_
  show (d.symmetryOfMap (d.cellTransporter (d.spaceCell 0) (d.spaceCell κ))).toFun _ = _
  rw [hInd.2.1 _ hmem]
  show d.cellTransporter (d.spaceCell 0) (d.spaceCell κ) (projection d.sideLengths _) = projection d.sideLengths _
  rw [hform, reflectReal_intCast]
private def pullbackField (g : TorusIsometry) (W' : TorusField m) : TorusField m := fun x k =>
  open Classical in
  if g.axisSign (g.axisPerm.symm k) = 1 then W' (g.mapSite x) (g.axisPerm.symm k)
  else (W' (g.mapSite x - unitStep m (g.axisPerm.symm k)) (g.axisPerm.symm k))⁻¹
private theorem transports_pullbackField (g : TorusIsometry) (W' : TorusField m) :
    g.Transports (pullbackField g W') W' := by
  intro x k
  simp only [pullbackField]
  split_ifs <;> rfl
private theorem measurable_pullbackField (g : TorusIsometry) : Measurable (pullbackField (m := m) g) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun k => ?_
  unfold pullbackField
  split_ifs
  · exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact continuous_inv.measurable.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))
private theorem ofTorusSite_mapSite (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (κ : Fin 4 → ℤ) (x : TorusSite m) :
    ofTorusSite d ((cellReflection c u κ).mapSite x) =
      pointOfCoords d (reflectInt c u κ fun μ => ((x μ).cast : ℤ)) := by
  refine (pointOfCoords_eq_iff hd _ _).mpr fun μ => ?_
  simp only [TorusIsometry.mapSite, cellReflection, reflectInt, ZMod.intCast_zmod_cast, Equiv.Perm.coe_one, id]
  push_cast
  simp
private theorem pointImage_ofTorusSite (hG : GroupAndCells.AllHold) (h : CubicShape d c M m u) (κ : Fin 4 → ℤ)
    (x : TorusSite m) :
    (d.symmetryOfMap (d.cellTransporter (d.spaceCell 0) (d.spaceCell κ))).pointImage (ofTorusSite d x) =
      ofTorusSite d ((cellReflection c u κ).mapSite x) := by
  rw [ofTorusSite_mapSite (sideLengths_of_shape h)]
  exact pointImage_pointOfCoords hG h κ _
variable [NeZero m]
private theorem pullback_configOfField (hG : GroupAndCells.AllHold) (hLat : GridLattice.Properties)
    (h : CubicShape d c M m u) (h2 : 2 < m) (κ : Fin 4 → ℤ) (W' : TorusField m) :
    (d.symmetryOfMap (d.cellTransporter (d.spaceCell 0) (d.spaceCell κ))).pullback
        (configOfField (sideLengths_of_shape h) h2 W') =
      configOfField (sideLengths_of_shape h) h2 (pullbackField (cellReflection c u κ) W') := by
  obtain ⟨_, _, hCfg, hLinks, _⟩ := hLat 13 0 d
  have hd := sideLengths_of_shape h
  funext b
  obtain ⟨⟨x, ν⟩, rfl⟩ := (forwardEdgeEquiv hd h2).surjective b
  have e : forwardEdgeEquiv hd h2 (x, ν) = forwardEdgeOf d (x, ν) := rfl
  rw [e, configOfField_forwardEdgeOf]
  set S := d.symmetryOfMap (d.cellTransporter (d.spaceCell 0) (d.spaceCell κ)) with hS
  set g := cellReflection c u κ with hg
  show edgeVariable (configOfField hd h2 W') (S.edgeImage (edgeFrom (ofTorusSite d x) ν)) = _
  obtain ⟨ht, hh⟩ := S.edgeImage_endpoints hLinks (edgeFrom (ofTorusSite d x) ν)
  have ht' : (S.edgeImage (edgeFrom (ofTorusSite d x) ν)).source = ofTorusSite d (g.mapSite x) :=
    ht.trans (pointImage_ofTorusSite hG h κ x)
  have hh' : (S.edgeImage (edgeFrom (ofTorusSite d x) ν)).target =
      ofTorusSite d (g.mapSite (x + unitStep m ν)) := by
    rw [hh]
    show S.pointImage (ofTorusSite d x + gridStep 13 0 d.sideLengths ν) = _
    rw [← ofTorusSite_add_unitStep hd]
    exact pointImage_ofTorusSite hG h κ _
  have hdir : g.axisPerm.symm ν = ν := rfl
  rcases g.axisSign_unit ν with hs | hs
  · have hadd : g.mapSite (x + unitStep m ν) = g.mapSite x + unitStep m ν :=
      mapSite_add_unitStep_of_pos g x ν hs
    have heq : S.edgeImage (edgeFrom (ofTorusSite d x) ν) = edgeFrom (ofTorusSite d (g.mapSite x)) ν := by
      refine DirectedEdge.ext ht' ?_
      rw [hh', hadd, ofTorusSite_add_unitStep hd]
      rfl
    rw [heq, edgeVariable_edgeFrom]
    simp only [pullbackField, hdir, hs, if_true]
  · have hsub : g.mapSite (x + unitStep m ν) = g.mapSite x - unitStep m ν :=
      mapSite_add_unitStep_of_neg g x ν hs
    have hne : g.axisSign ν ≠ 1 := by
      rw [hs]
      norm_num
    have heq : S.edgeImage (edgeFrom (ofTorusSite d x) ν) =
        (edgeFrom (ofTorusSite d (g.mapSite x - unitStep m ν)) ν).flip := by
      refine DirectedEdge.ext ?_ ?_
      · rw [ht']
        show _ = ofTorusSite d (g.mapSite x - unitStep m ν) + gridStep 13 0 d.sideLengths ν
        rw [← ofTorusSite_add_unitStep hd, sub_add_cancel]
      · rw [hh', hsub]
        rfl
    rw [heq, hCfg.1, edgeVariable_edgeFrom]
    simp only [pullbackField, hdir, if_neg hne, map_inv]
end Torus
section Cell
variable {d : CellGrid 13 0} {c M m : ℕ} {u : Fin 4 → ℤ}
private theorem mem_interior_cell_zero (hG : GroupAndCells.AllHold) (h : CubicShape d c M m u) (hc : Odd c)
    {z : Fin 4 → ℤ} (hz : ∀ μ, |z μ - u μ| ≤ (((c - 1) / 2 : ℕ) : ℤ)) :
    ((pointOfCoords d z : d.GridPoint) : d.Space) ∈ interior (d.spaceCell 0) := by
  obtain ⟨_, hInd, _, _, _, hRefl, _⟩ := hG 13 0 d
  obtain ⟨θ, hθ, _, _⟩ := hInd.1 (d.faceReflectEquiv 0 0) (Subgroup.subset_closure ⟨(0, 0), rfl⟩)
  have hint := (hRefl 0 0 θ hθ).2.2.1 0
  rw [hint]
  obtain ⟨r, hr⟩ := hc
  have hr' : (c - 1) / 2 = r := by omega
  refine ⟨fun μ => (z μ : ℝ) * meshSize 13 0, ?_, rfl⟩
  have hc0 : (0 : ℝ) < c := by exact_mod_cast h.length_pos
  refine mem_interior.mpr ⟨Set.pi Set.univ fun μ => Set.Ioo (d.centre μ) (d.centre μ + c), ?_,
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo, fun μ _ => ?_⟩
  · intro x hx
    have e : x = d.centre + (x - d.centre) := by simp
    rw [e]
    refine mem_cellCube_zero h fun μ => ?_
    have := hx μ (Set.mem_univ _)
    simp only [Pi.sub_apply]
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · have h1 := abs_le.mp (hz μ)
    rw [hr'] at h1
    have h2 : ((z μ - u μ : ℤ) : ℝ) ≤ r := by exact_mod_cast h1.2
    have h3 : -(r : ℝ) ≤ ((z μ - u μ : ℤ) : ℝ) := by exact_mod_cast h1.1
    push_cast at h2 h3
    have hcr : (c : ℝ) = 2 * r + 1 := by exact_mod_cast hr
    show (z μ : ℝ) * meshSize 13 0 ∈ Set.Ioo (d.centre μ) (d.centre μ + c)
    rw [h.centre_eq, meshSize_zero_eq_one, mul_one]
    constructor <;> linarith
variable [NeZero m]
private theorem mem_cellObservables (hG : GroupAndCells.AllHold) (h : CubicShape d c M m u) (h2 : 2 < m)
    (hc : Odd c) {G : TorusField m → ℝ} (hGm : Measurable G) (hG0 : ∀ W, 0 ≤ G W) (hG1 : ∀ W, G W ≤ 1)
    (hread : DependsOnlyOnBox u ((c - 1) / 2) G) (hc₀ : d.spaceCell 0 ∈ d.spaceCells) :
    (fun U : d.GaugeConfig => ((G (fieldOfConfig (sideLengths_of_shape h) h2 U) : ℝ) : ℂ)) ∈
      d.cellObservables ⟨_, hc₀⟩ := by
  classical
  have hd := sideLengths_of_shape h
  set E := d.edgesWithin (TopologicalSpace.Opens.interior (d.spaceCell 0)) with hE
  let ext : (↥(forwardPart E) → Conventions.StandingParameters.gaugeGroup) → d.GaugeConfig := fun w b =>
    if hb : b ∈ forwardPart E then w ⟨b, hb⟩ else 1
  have hext : Measurable ext := by
    refine measurable_pi_iff.mpr fun b => ?_
    by_cases hb : b ∈ forwardPart E
    · simp only [ext, dif_pos hb]
      exact measurable_pi_apply _
    · simp only [ext, dif_neg hb]
      exact measurable_const
  refine ⟨fun w => ((G (fieldOfConfig hd h2 (ext w)) : ℝ) : ℂ), ?_, ⟨1, fun w => ?_⟩, fun U => ?_⟩
  · exact Complex.measurable_ofReal.comp (hGm.comp ((measurable_fieldOfConfig hd h2).comp hext))
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hG0 _)]
    exact hG1 _
  · show ((G (fieldOfConfig hd h2 U) : ℝ) : ℂ) = ((G (fieldOfConfig hd h2 (ext fun b => U b.1)) : ℝ) : ℂ)
    congr 1
    refine hread _ _ fun t ht => ?_
    obtain ⟨t₁, ν⟩ := t
    simp only [bondFrom]
    have hb : forwardEdgeEquiv hd h2 ((siteOfInt u : TorusSite m) + siteOfInt t₁, ν) ∈ forwardPart E := by
      refine Or.inl ⟨?_, ?_⟩
      · show ((ofTorusSite d ((siteOfInt u : TorusSite m) + siteOfInt t₁) : d.GridPoint) : d.Space) ∈
          interior (d.spaceCell 0)
        have e : ((siteOfInt u : TorusSite m) + siteOfInt t₁) = siteOfInt (u + t₁) := by
          funext i
          simp [siteOfInt]
        rw [e, ofTorusSite_siteOfInt hd]
        refine mem_interior_cell_zero hG h hc fun μ => ?_
        have := ht.1 μ
        simpa using this
      · show ((ofTorusSite d ((siteOfInt u : TorusSite m) + siteOfInt t₁) + gridStep 13 0 d.sideLengths ν :
            d.GridPoint) : d.Space) ∈ interior (d.spaceCell 0)
        have e : ((siteOfInt u : TorusSite m) + siteOfInt t₁) = siteOfInt (u + t₁) := by
          funext i
          simp [siteOfInt]
        rw [e, ofTorusSite_siteOfInt hd, gridStep_eq_pointOfCoords, ← pointOfCoords_add]
        refine mem_interior_cell_zero hG h hc fun μ => ?_
        have := ht.2 μ
        have e2 : ((u + t₁ + Pi.single ν 1 : Fin 4 → ℤ)) μ - u μ = ((t₁ + Pi.single ν 1 : Fin 4 → ℤ)) μ := by
          simp only [Pi.add_apply]
          ring
        rw [e2]
        exact this
    simp only [fieldOfConfig, ext, dif_pos hb]
end Cell
section Main
variable {d : CellGrid 13 0} {c M m : ℕ} {u : Fin 4 → ℤ}
private def cellOfIndex (d : CellGrid 13 0) {M : ℕ} (k : Fin 4 → Fin M) : d.spaceCells :=
  ⟨d.spaceCell fun μ => ((k μ : ℕ) : ℤ), ⟨_, rfl⟩⟩
private theorem cellOfIndex_bijective (hG : GroupAndCells.AllHold) (h : CubicShape d c M m u) (hM0 : 0 < M) :
    Function.Bijective (cellOfIndex d : (Fin 4 → Fin M) → d.spaceCells) := by
  obtain ⟨_, _, hCells, _⟩ := hG 13 0 d
  have hclass : ∀ a b : Fin 4 → ℤ, d.spaceCell a = d.spaceCell b ↔ ∀ μ, (M : ℤ) ∣ b μ - a μ := by
    intro a b
    rw [hCells.1]
    constructor
    · intro he μ
      have h1 := congrFun he μ
      have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
      rwa [h.counts_eq] at h2
    · intro he
      funext μ
      refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ?_
      rw [h.counts_eq]
      exact he μ
  constructor
  · intro k k' he
    have h1 := (hclass _ _).mp (congrArg Subtype.val he)
    funext μ
    have h2 := h1 μ
    have h3 : (((k' μ : ℕ) : ℤ) - ((k μ : ℕ) : ℤ)) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd h2 ?_
      have a1 := (k μ).2
      have a2 := (k' μ).2
      rw [abs_lt]
      constructor <;> omega
    exact Fin.ext (by omega)
  · rintro ⟨_, z, rfl⟩
    have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM0.ne'
    refine ⟨fun μ => ⟨(z μ % M).toNat, ?_⟩, Subtype.ext ?_⟩
    · have h1 := Int.emod_nonneg (z μ) hMz
      have h2 := Int.emod_lt_of_pos (z μ) (by exact_mod_cast hM0 : (0 : ℤ) < M)
      omega
    · refine (hclass _ _).mpr fun μ => ?_
      have h1 := Int.emod_nonneg (z μ) hMz
      show (M : ℤ) ∣ z μ - (((z μ % M).toNat : ℕ) : ℤ)
      rw [Int.toNat_of_nonneg h1]
      exact Int.dvd_self_sub_emod
variable [NeZero m]
private theorem checkerboard_power_le (hSem : CheckerboardSeminorms.Statement) (hG : GroupAndCells.AllHold)
    (hLat : GridLattice.Properties) (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm)
    (h : CubicShape d c M m u) (h2 : 2 < m) (hc : Odd c) (hM0 : 0 < M) {β : ℝ} (hβ : 0 < β)
    {G : TorusField m → ℝ} {H : (Fin 4 → Fin M) → TorusField m → ℝ} (hGm : Measurable G)
    (hG0 : ∀ W, 0 ≤ G W) (hG1 : ∀ W, G W ≤ 1)
    (hread : DependsOnlyOnBox u ((c - 1) / 2) G) (hcopy : IsCellCopy c u G H) :
    (∫ W, G W ∂(wilsonLaw β m)) ^ (M ^ 4) ≤ ∫ W, ∏ k, H k W ∂(wilsonLaw β m) := by
  classical
  have hd := sideLengths_of_shape h
  have hc₀ : d.spaceCell 0 ∈ d.spaceCells := ⟨0, rfl⟩
  let c₀ : d.spaceCells := ⟨_, hc₀⟩
  let F₀ : d.cellObservables c₀ := ⟨_, mem_cellObservables hG h h2 hc hGm hG0 hG1 hread hc₀⟩
  have hF₀ : ∀ U, F₀.1 U = ((G (fieldOfConfig hd h2 U) : ℝ) : ℂ) := fun U => rfl
  have : IsProbabilityMeasure (wilsonLaw β m) := by
    constructor
    have hcont : Continuous fun W : TorusField m => Real.exp (-β * wilsonAction Finset.univ W) :=
      Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonAction _))
    have hI := hcont.integrable_of_hasCompactSupport (μ := fieldHaar m) (HasCompactSupport.of_compactSpace _)
    have hZ : 0 < ∫ W, Real.exp (-β * wilsonAction Finset.univ W) ∂(fieldHaar m) := integral_exp_pos hI
    unfold wilsonLaw
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hI.div_const _)
        (Filter.Eventually.of_forall fun W => div_nonneg (Real.exp_nonneg _) hZ.le),
      integral_div, div_self hZ.ne', ENNReal.ofReal_one]
  let Gs : (c' : ({c₀} : Set d.spaceCells)) → d.cellObservables c'.1 := fun c' =>
    (show c₀ = c'.1 from (Set.mem_singleton_iff.mp c'.2).symm) ▸ F₀
  have hest := (hSem 13 0 d β hβ c₀ F₀ F₀ 0).2.2.2 {c₀} Gs
  have hsing : ∀ f : ({c₀} : Set d.spaceCells) → ℂ, ∏ᶠ c', f c' = f ⟨c₀, rfl⟩ := fun f => finprod_unique f
  have hsingR : ∀ f : ({c₀} : Set d.spaceCells) → ℝ, ∏ᶠ c', f c' = f ⟨c₀, rfl⟩ := fun f => finprod_unique f
  simp only [hsing, hsingR] at hest
  have hE : d.gibbsMean β (fun U => F₀.1 U) = ((∫ W, G W ∂(wilsonLaw β m) : ℝ) : ℂ) := by
    have hm : Measurable fun U : d.GaugeConfig => F₀.1 U :=
      Complex.measurable_ofReal.comp (hGm.comp (measurable_fieldOfConfig hd h2))
    rw [gibbsMean_eq hq hd h2 β hm]
    simp only [hF₀, fieldOfConfig_configOfField]
    exact integral_ofReal
  have hGn : 0 ≤ ∫ W, G W ∂(wilsonLaw β m) := integral_nonneg hG0
  set N : ℕ := M ^ 4 with hN
  have hcount : (d.numCells : ℝ) = (N : ℝ) := by
    have : d.numCells = N := by
      show ∏ μ, d.counts μ = M ^ 4
      simp [h.counts_eq]
    rw [this]
  let g : (Fin 4 → Fin M) → TorusIsometry := fun k => cellReflection c u fun μ => ((k μ : ℕ) : ℤ)
  have hHk : ∀ k W', H k W' = G (pullbackField (g k) W') := fun k W' =>
    hcopy k _ _ (transports_pullbackField _ W')
  have hHm : ∀ k, Measurable (H k) := fun k => by
    have : H k = G ∘ pullbackField (g k) := funext (hHk k)
    rw [this]
    exact hGm.comp (measurable_pullbackField _)
  have hcopyEval : ∀ k W', d.checkerboardCopy c₀ (cellOfIndex d k) F₀ (configOfField hd h2 W') =
      ((H k W' : ℝ) : ℂ) := by
    intro k W'
    have e := pullback_configOfField hG hLat h h2 (fun μ => ((k μ : ℕ) : ℤ)) W'
    have hval : (d.symmetryOfMap (d.cellTransporter c₀.1 (cellOfIndex d k).1)).actOnObservables F₀.1
        (configOfField hd h2 W') = ((H k W' : ℝ) : ℂ) := by
      show F₀.1 ((d.symmetryOfMap (d.cellTransporter (d.spaceCell 0) (d.spaceCell _))).pullback
        (configOfField hd h2 W')) = _
      rw [e, hF₀, fieldOfConfig_configOfField, hHk k W']
    unfold CellGrid.checkerboardCopy
    split_ifs
    · exact hval
    · show starRingEnd ℂ _ = _
      rw [hval, Complex.conj_ofReal]
  let eq := Equiv.ofBijective _ (cellOfIndex_bijective hG h hM0)
  have hprod : ∀ W', ∏ᶠ c' : d.spaceCells, d.checkerboardCopy c₀ c' F₀ (configOfField hd h2 W') =
      ((∏ k, H k W' : ℝ) : ℂ) := by
    intro W'
    rw [← finprod_comp_equiv eq, finprod_eq_prod_of_fintype]
    push_cast
    exact Finset.prod_congr rfl fun k _ => hcopyEval k W'
  have hfun : (fun U => ∏ᶠ c' : d.spaceCells, d.checkerboardCopy c₀ c' F₀ U) =
      fun U => ((∏ k, H k (fieldOfConfig hd h2 U) : ℝ) : ℂ) := by
    funext U
    have := hprod (fieldOfConfig hd h2 U)
    rwa [configOfField_fieldOfConfig] at this
  have hQ : d.copiesProductMean β c₀ F₀ = ((∫ W, ∏ k, H k W ∂(wilsonLaw β m) : ℝ) : ℂ) := by
    unfold CellGrid.copiesProductMean
    rw [hfun]
    have hm : Measurable fun U : d.GaugeConfig => ((∏ k, H k (fieldOfConfig hd h2 U) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp
        (Finset.measurable_prod _ fun k _ => (hHm k).comp (measurable_fieldOfConfig hd h2))
    rw [gibbsMean_eq hq hd h2 β hm]
    simp only [fieldOfConfig_configOfField]
    exact integral_ofReal
  have hest' : ‖d.gibbsMean β (fun U => F₀.1 U)‖ ≤ d.checkerboardNorm β c₀ F₀ := hest
  rw [hE, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hGn] at hest'
  unfold CellGrid.checkerboardNorm at hest'
  rw [hQ, Complex.ofReal_re, hcount] at hest'
  have hQ0 : 0 ≤ ∫ W, ∏ k, H k W ∂(wilsonLaw β m) := integral_nonneg fun W =>
    Finset.prod_nonneg fun k _ => by
      rw [hHk k W]
      exact hG0 _
  have hN0 : N ≠ 0 := pow_ne_zero _ hM0.ne'
  have hpow := pow_le_pow_left₀ hGn hest' N
  rw [one_div, Real.rpow_inv_natCast_pow hQ0 hN0] at hpow
  exact hpow
end Main
theorem chessboardEstimate_holds (hSem : CheckerboardSeminorms.Statement)
    (hG : GroupAndCells.AllHold) (hLat : GridLattice.Properties)
    (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm) : ChessboardEstimate := by
  intro c M m _ hm hc hM hM0 h4 β hβ u G H hGm hG0 hG1 hread hcopy
  have h4' : 4 ≤ c * M := hm ▸ h4
  have hsh : CubicShape (cubicCellGrid c M u hc hM hM0 h4') c M m u :=
    ⟨rfl, fun _ => rfl, fun _ => rfl, hm, hc.pos⟩
  exact checkerboard_power_le hSem hG hLat hq hsh (by omega) hc hM0 hβ hGm hG0 hG1 hread hcopy
end TorusFields
end YangMills.Construction
end
