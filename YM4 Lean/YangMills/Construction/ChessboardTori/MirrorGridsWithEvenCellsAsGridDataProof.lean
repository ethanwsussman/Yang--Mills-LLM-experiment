import YangMills.Construction.ChessboardTori.MirrorGridsWithEvenCellsAsGridData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set MeasureTheory BoxTorus
namespace ChessboardTori.ReflectionGridAsCellGrid
variable {s s' : Fin 4 → ℝ} {L : ℕ} {κ : ℤ}
theorem spaceEquivOfSidesEq_rfl (x : BoxTorus.Space s) :
    spaceEquivOfSidesEq (rfl : s = s) x = x := by
  obtain ⟨w, rfl⟩ := projection_surjective s x
  rfl
theorem gridPointEquivOfSidesEq_rfl (x : BoxTorus.GridPoint L κ s) :
    gridPointEquivOfSidesEq (rfl : s = s) x = x :=
  Subtype.ext (spaceEquivOfSidesEq_rfl _)
theorem edgeEquivOfSidesEq_rfl (e : BoxTorus.DirectedEdge L κ s) :
    edgeEquivOfSidesEq (rfl : s = s) e = e :=
  BoxTorus.DirectedEdge.ext (gridPointEquivOfSidesEq_rfl _) (gridPointEquivOfSidesEq_rfl _)
theorem forwardEdgeEquivOfSidesEq_rfl (e : BoxTorus.ForwardEdge L κ s) :
    forwardEdgeEquivOfSidesEq (rfl : s = s) e = e :=
  Subtype.ext (edgeEquivOfSidesEq_rfl _)
theorem gaugeConfigOfSidesEq_rfl :
    gaugeConfigOfSidesEq (L := L) (κ := κ) (rfl : s = s) = id := by
  funext V e
  simp only [gaugeConfigOfSidesEq, Function.comp, id]
  congr 1
  rw [Equiv.symm_apply_eq, forwardEdgeEquivOfSidesEq_rfl]
theorem faceEquivOfSidesEq_rfl (f : BoxTorus.Face L κ s) :
    faceEquivOfSidesEq (rfl : s = s) f = f :=
  BoxTorus.Face.ext (gridPointEquivOfSidesEq_rfl _) rfl rfl
theorem isHomeomorph_spaceEquivOfSidesEq (h : s = s') :
    IsHomeomorph (spaceEquivOfSidesEq h) := by
  subst h
  have e : (spaceEquivOfSidesEq (rfl : s = s) : BoxTorus.Space s → BoxTorus.Space s) = id :=
    funext spaceEquivOfSidesEq_rfl
  rw [e]
  exact (Homeomorph.refl _).isHomeomorph
theorem image_gridSubgroup (h : s = s') :
    spaceEquivOfSidesEq h '' (gridSubgroup L κ s : Set (BoxTorus.Space s)) =
      (gridSubgroup L κ s' : Set (BoxTorus.Space s')) := by
  subst h
  ext x
  simp [spaceEquivOfSidesEq_rfl]
theorem torusDist_spaceEquivOfSidesEq (h : s = s') (x y : BoxTorus.Space s) :
    torusDist (spaceEquivOfSidesEq h x) (spaceEquivOfSidesEq h y) = torusDist x y := by
  subst h
  rw [spaceEquivOfSidesEq_rfl, spaceEquivOfSidesEq_rfl]
theorem edgeEquivOfSidesEq_flip (h : s = s') (e : BoxTorus.DirectedEdge L κ s) :
    edgeEquivOfSidesEq h e.flip = (edgeEquivOfSidesEq h e).flip := by
  subst h
  rw [edgeEquivOfSidesEq_rfl, edgeEquivOfSidesEq_rfl]
theorem isHomeomorph_gaugeConfigOfSidesEq (h : s = s') :
    IsHomeomorph (gaugeConfigOfSidesEq (L := L) (κ := κ) h) := by
  subst h
  rw [gaugeConfigOfSidesEq_rfl]
  exact (Homeomorph.refl _).isHomeomorph
theorem edgeVariable_gaugeConfigOfSidesEq (h : s = s') (V : BoxTorus.GaugeConfig L κ s)
    (e : BoxTorus.DirectedEdge L κ s) :
    edgeVariable (gaugeConfigOfSidesEq h V) (edgeEquivOfSidesEq h e) = edgeVariable V e := by
  subst h
  rw [gaugeConfigOfSidesEq_rfl, edgeEquivOfSidesEq_rfl]
  rfl
theorem map_haarConfigMeasure (h : s = s') :
    (haarConfigMeasure L κ s).map (gaugeConfigOfSidesEq h) = haarConfigMeasure L κ s' := by
  subst h
  rw [gaugeConfigOfSidesEq_rfl, Measure.map_id]
theorem vertexSet_faceEquivOfSidesEq (h : s = s') (f : BoxTorus.Face L κ s) :
    (faceEquivOfSidesEq h f).vertexSet = gridPointEquivOfSidesEq h '' f.vertexSet := by
  subst h
  rw [faceEquivOfSidesEq_rfl]
  ext x
  simp [gridPointEquivOfSidesEq_rfl]
theorem faceHolonomy_gaugeConfigOfSidesEq (h : s = s') (V : BoxTorus.GaugeConfig L κ s)
    (f : BoxTorus.Face L κ s) :
    faceHolonomy (gaugeConfigOfSidesEq h V) (faceEquivOfSidesEq h f) = faceHolonomy V f := by
  subst h
  rw [gaugeConfigOfSidesEq_rfl, faceEquivOfSidesEq_rfl]
  rfl
theorem faceEnergy_gaugeConfigOfSidesEq (h : s = s') (V : BoxTorus.GaugeConfig L κ s)
    (f : BoxTorus.Face L κ s) :
    faceEnergy (gaugeConfigOfSidesEq h V) (faceEquivOfSidesEq h f) = faceEnergy V f := by
  subst h
  rw [gaugeConfigOfSidesEq_rfl, faceEquivOfSidesEq_rfl]
  rfl
theorem wilsonAction_gaugeConfigOfSidesEq (h : s = s') (V : BoxTorus.GaugeConfig L κ s) :
    wilsonAction (gaugeConfigOfSidesEq h V) = wilsonAction V := by
  subst h
  rw [gaugeConfigOfSidesEq_rfl]
  rfl
theorem sideLengths_boxPeriods {D : ChessboardSetup} (g : ReflectionGrid D) (c : Fin 4 → ℤ)
    (hc : ∀ i, 2 ≤ c i) (i : Fin 4) :
    (g.boxPeriods c hc).sideLengths i = (c i : ℝ) * g.cellSide := by
  change ((c i * g.cellRatio : ℤ) : ℝ) * D.mesh = _
  rw [g.cellSide_eq]
  push_cast
  ring
theorem exists_isCellTriple {D : ChessboardSetup} (g : ReflectionGrid D) (c : Fin 4 → ℤ)
    (hc : ∀ i, 2 ≤ c i) (hev : ∀ i, Even (c i)) :
    ∃ d : CellGrid D.L ((D.K : ℕ) : ℤ), g.IsCellTriple c d := by
  have hcast : ∀ i, (((c i).toNat : ℕ) : ℤ) = c i := fun i =>
    Int.toNat_of_nonneg (by linarith [hc i])
  have hmesh : 0 < D.mesh := D.mesh_pos
  have hrat : (2 : ℝ) ≤ (g.cellRatio : ℝ) := by exact_mod_cast g.two_le_cellRatio
  have hlen : g.cellSide = (g.cellRatio : ℝ) * D.mesh := g.cellSide_eq
  have hpos : 0 < g.cellSide := by
    rw [hlen]
    exact mul_pos (by linarith) hmesh
  refine ⟨{ admissible := D.isAdmissible
            cellLength := g.cellSide
            cellLength_pos := hpos
            cellLength_div_meshSize := ⟨g.cellRatio, ?_⟩
            counts := fun i => (c i).toNat
            counts_pos := fun i => ?_
            counts_even := fun i => ?_
            four_meshSize_le := fun i => ?_
            centre := g.origin
            centre_mem := g.origin_mem }, rfl, hcast, rfl⟩
  · change g.cellSide / D.mesh = _
    rw [hlen]
    field_simp
  · have := hcast i
    have := hc i
    omega
  · refine (Int.even_coe_nat _).mp ?_
    rw [hcast]
    exact hev i
  · change 4 * D.mesh ≤ (((c i).toNat : ℕ) : ℝ) * g.cellSide
    have hre : (((c i).toNat : ℕ) : ℝ) = (c i : ℝ) := by exact_mod_cast hcast i
    have htwo : (2 : ℝ) ≤ (c i : ℝ) := by exact_mod_cast hc i
    rw [hre, hlen]
    have hfour : (4 : ℝ) ≤ (c i : ℝ) * (g.cellRatio : ℝ) := by nlinarith
    nlinarith
theorem statement_holds : ReflectionGridAsCellGrid.Statement := by
  intro D g c hc hev
  refine ⟨exists_isCellTriple g c hc hev, ?_⟩
  rintro d ⟨hlen, hcounts, -⟩
  have hsides : ∀ i, d.sideLengths i = (c i : ℝ) * g.cellSide := fun i => by
    have hre : ((d.counts i : ℕ) : ℝ) = (c i : ℝ) := by exact_mod_cast hcounts i
    change ((d.counts i : ℕ) : ℝ) * d.cellLength = _
    rw [hre, hlen]
  have h : d.sideLengths = (g.boxPeriods c hc).sideLengths :=
    funext fun i => (hsides i).trans (sideLengths_boxPeriods g c hc i).symm
  refine ⟨hsides, ?_, h, ?_, ?_, ?_, ?_⟩
  · rw [h]
    rfl
  · exact ⟨isHomeomorph_spaceEquivOfSidesEq h, fun x => rfl, image_gridSubgroup h,
      torusDist_spaceEquivOfSidesEq h⟩
  · exact ⟨isForward_edgeEquivOfSidesEq h, edgeEquivOfSidesEq_flip h⟩
  · exact ⟨isHomeomorph_gaugeConfigOfSidesEq h, edgeVariable_gaugeConfigOfSidesEq h,
      map_haarConfigMeasure h⟩
  · exact ⟨vertexSet_faceEquivOfSidesEq h, faceHolonomy_gaugeConfigOfSidesEq h,
      faceEnergy_gaugeConfigOfSidesEq h, wilsonAction_gaugeConfigOfSidesEq h⟩
end ChessboardTori.ReflectionGridAsCellGrid
end YangMills.Construction
end
