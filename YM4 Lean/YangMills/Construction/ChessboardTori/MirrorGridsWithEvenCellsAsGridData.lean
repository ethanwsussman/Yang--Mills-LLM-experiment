import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace BoxTorus
variable {ℓ ℓ' : Fin 4 → ℝ} {L : ℕ} {κ : ℤ}
def spaceEquivOfSidesEq (h : ℓ = ℓ') : Space ℓ ≃+ Space ℓ' :=
  AddEquiv.piCongrRight fun μ => QuotientAddGroup.quotientAddEquivOfEq (by rw [h])
theorem spaceEquivOfSidesEq_projection (h : ℓ = ℓ') (w : Fin 4 → ℝ) :
    spaceEquivOfSidesEq h (projection ℓ w) = projection ℓ' w := rfl
theorem spaceEquivOfSidesEq_mem_gridSubgroup (h : ℓ = ℓ') (x : Space ℓ) :
    spaceEquivOfSidesEq h x ∈ gridSubgroup L κ ℓ' ↔ x ∈ gridSubgroup L κ ℓ := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, (spaceEquivOfSidesEq h).injective ?_⟩
    rw [hm, spaceEquivOfSidesEq_projection]
  · rintro ⟨m, rfl⟩
    exact ⟨m, spaceEquivOfSidesEq_projection h _⟩
def gridPointEquivOfSidesEq (h : ℓ = ℓ') : GridPoint L κ ℓ ≃ GridPoint L κ ℓ' :=
  (spaceEquivOfSidesEq h).toEquiv.subtypeEquiv fun x => (spaceEquivOfSidesEq_mem_gridSubgroup h x).symm
theorem coe_gridPointEquivOfSidesEq (h : ℓ = ℓ') (x : GridPoint L κ ℓ) :
    (gridPointEquivOfSidesEq h x : Space ℓ') = spaceEquivOfSidesEq h (x : Space ℓ) := rfl
theorem isNeighbourStep_gridPointEquivOfSidesEq (h : ℓ = ℓ') (x y : GridPoint L κ ℓ) (ν : Fin 4)
    (σ : ℝ) :
    IsNeighbourStep (gridPointEquivOfSidesEq h x) (gridPointEquivOfSidesEq h y) ν σ ↔
      IsNeighbourStep x y ν σ := by
  have e : (spaceEquivOfSidesEq h
      (translate (x : Space ℓ) ((σ * PeriodicLattice.meshSize L κ) • basisVector ν))) =
      translate (gridPointEquivOfSidesEq h x : Space ℓ')
        ((σ * PeriodicLattice.meshSize L κ) • basisVector ν) := by
    rw [translate, map_add, spaceEquivOfSidesEq_projection]
    rfl
  unfold IsNeighbourStep
  rw [coe_gridPointEquivOfSidesEq h y, ← e, (spaceEquivOfSidesEq h).injective.eq_iff]
def edgeEquivOfSidesEq (h : ℓ = ℓ') : DirectedEdge L κ ℓ ≃ DirectedEdge L κ ℓ' where
  toFun b := ⟨gridPointEquivOfSidesEq h b.source, gridPointEquivOfSidesEq h b.target, by
    obtain ⟨ν, σ, hs⟩ := b.isNeighbour
    exact ⟨ν, σ, (isNeighbourStep_gridPointEquivOfSidesEq h _ _ ν σ).mpr hs⟩⟩
  invFun b := ⟨(gridPointEquivOfSidesEq h).symm b.source,
    (gridPointEquivOfSidesEq h).symm b.target, by
    obtain ⟨ν, σ, hs⟩ := b.isNeighbour
    refine ⟨ν, σ, (isNeighbourStep_gridPointEquivOfSidesEq h _ _ ν σ).mp ?_⟩
    simpa using hs⟩
  left_inv _ := DirectedEdge.ext ((gridPointEquivOfSidesEq h).symm_apply_apply _)
    ((gridPointEquivOfSidesEq h).symm_apply_apply _)
  right_inv _ := DirectedEdge.ext ((gridPointEquivOfSidesEq h).apply_symm_apply _)
    ((gridPointEquivOfSidesEq h).apply_symm_apply _)
theorem isForward_edgeEquivOfSidesEq (h : ℓ = ℓ') (b : DirectedEdge L κ ℓ) :
    (edgeEquivOfSidesEq h b).IsForward ↔ b.IsForward :=
  exists_congr fun ν => isNeighbourStep_gridPointEquivOfSidesEq h b.source b.target ν 1
def forwardEdgeEquivOfSidesEq (h : ℓ = ℓ') : ForwardEdge L κ ℓ ≃ ForwardEdge L κ ℓ' :=
  (edgeEquivOfSidesEq h).subtypeEquiv fun b => (isForward_edgeEquivOfSidesEq h b).symm
def gaugeConfigOfSidesEq (h : ℓ = ℓ') (U : GaugeConfig L κ ℓ) : GaugeConfig L κ ℓ' :=
  U ∘ (forwardEdgeEquivOfSidesEq h).symm
def faceEquivOfSidesEq (h : ℓ = ℓ') : Face L κ ℓ ≃ Face L κ ℓ' where
  toFun p := ⟨gridPointEquivOfSidesEq h p.corner, p.dir₁, p.dir₂, p.dir₁_lt_dir₂⟩
  invFun p := ⟨(gridPointEquivOfSidesEq h).symm p.corner, p.dir₁, p.dir₂, p.dir₁_lt_dir₂⟩
  left_inv _ := Face.ext ((gridPointEquivOfSidesEq h).symm_apply_apply _) rfl rfl
  right_inv _ := Face.ext ((gridPointEquivOfSidesEq h).apply_symm_apply _) rfl rfl
end BoxTorus
namespace ChessboardTori
open BoxTorus
def ReflectionGrid.IsCellTriple {D : ChessboardSetup} (g : ReflectionGrid D) (n : Fin 4 → ℤ)
    (d : CellGrid D.L ((D.K : ℕ) : ℤ)) : Prop :=
  d.cellLength = g.cellSide ∧ (∀ μ, (d.counts μ : ℤ) = n μ) ∧ d.centre = g.origin
namespace PeriodSubgroup
variable {D : ChessboardSetup} (P : PeriodSubgroup D) {d : CellGrid D.L ((D.K : ℕ) : ℤ)}
def SpaceAgrees (h : d.sideLengths = P.sideLengths) : Prop :=
  IsHomeomorph (spaceEquivOfSidesEq h) ∧
  (∀ x : Fin 4 → ℝ, spaceEquivOfSidesEq h (BoxTorus.projection d.sideLengths x) = P.proj x) ∧
  spaceEquivOfSidesEq h '' (BoxTorus.gridSubgroup D.L ((D.K : ℕ) : ℤ) d.sideLengths : Set d.Space) =
    (P.gridSubgroup : Set P.TorusSpace) ∧
  ∀ u v : d.Space,
    P.torusDist (spaceEquivOfSidesEq h u) (spaceEquivOfSidesEq h v) = BoxTorus.torusDist u v
def EdgesAgree (h : d.sideLengths = P.sideLengths) : Prop :=
  (∀ b : d.DirectedEdge, (edgeEquivOfSidesEq h b : P.DirectedEdge).IsForward ↔ b.IsForward) ∧
  ∀ b : d.DirectedEdge,
    edgeEquivOfSidesEq h b.flip = (edgeEquivOfSidesEq h b : P.DirectedEdge).flip
def GaugeConfigsAgree (h : d.sideLengths = P.sideLengths) : Prop :=
  IsHomeomorph (gaugeConfigOfSidesEq (L := D.L) (κ := ((D.K : ℕ) : ℤ)) h) ∧
  (∀ (U : d.GaugeConfig) (b : d.DirectedEdge),
    edgeVariable (gaugeConfigOfSidesEq h U : P.GaugeConfig) (edgeEquivOfSidesEq h b) =
      edgeVariable U b) ∧
  (haarConfigMeasure D.L ((D.K : ℕ) : ℤ) d.sideLengths).map (gaugeConfigOfSidesEq h) =
    P.haarMeasure
def FacesAgree (h : d.sideLengths = P.sideLengths) : Prop :=
  (∀ p : d.Face, (faceEquivOfSidesEq h p : P.Face).vertexSet =
    gridPointEquivOfSidesEq h '' p.vertexSet) ∧
  (∀ (U : d.GaugeConfig) (p : d.Face),
    faceHolonomy (gaugeConfigOfSidesEq h U : P.GaugeConfig)
      (faceEquivOfSidesEq h p) = faceHolonomy U p) ∧
  (∀ (U : d.GaugeConfig) (p : d.Face),
    P.faceEnergy (gaugeConfigOfSidesEq h U) (faceEquivOfSidesEq h p) =
      BoxTorus.faceEnergy U p) ∧
  ∀ U : d.GaugeConfig, P.wilsonAction (gaugeConfigOfSidesEq h U) = d.wilsonAction U
end PeriodSubgroup
def ReflectionGridAsCellGrid.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D) (n : Fin 4 → ℤ) (hn : ∀ μ, 2 ≤ n μ),
    (∀ μ, Even (n μ)) →
    (∃ d : CellGrid D.L ((D.K : ℕ) : ℤ), g.IsCellTriple n d) ∧
    ∀ d : CellGrid D.L ((D.K : ℕ) : ℤ), g.IsCellTriple n d →
      (∀ μ, d.sideLengths μ = (n μ : ℝ) * g.cellSide) ∧
      periods d.sideLengths = (g.boxPeriods n hn).subgroup ∧
      ∃ h : d.sideLengths = (g.boxPeriods n hn).sideLengths,
        (g.boxPeriods n hn).SpaceAgrees h ∧ (g.boxPeriods n hn).EdgesAgree h ∧
        (g.boxPeriods n hn).GaugeConfigsAgree h ∧
        (g.boxPeriods n hn).FacesAgree h
end ChessboardTori
end YangMills.Construction
end
