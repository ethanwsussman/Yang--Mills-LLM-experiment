import YangMills.Construction.Lattice.CellGridGibbsMeasure
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory
open PeriodicLattice (torusSide meshSize pointOnAxis)
namespace CellGrid
variable {L m : ℕ} {κ : ℤ} {d : CellGrid L κ}
def HasEqualSides (d : CellGrid L κ) (m : ℕ) : Prop := ∀ μ, d.sideLengths μ = torusSide L m
def spaceEquivTorus (h : d.HasEqualSides m) : d.Space ≃+ PeriodicLattice.FourTorus L m :=
  AddEquiv.piCongrRight fun μ =>
    QuotientAddGroup.quotientAddEquivOfEq (by rw [h μ])
theorem spaceEquivTorus_projection (h : d.HasEqualSides m) (w : Fin 4 → ℝ) :
    spaceEquivTorus h (BoxTorus.projection d.sideLengths w) =
      fun μ => (w μ : AddCircle (torusSide L m)) := rfl
theorem spaceEquivTorus_smul_basisVector (h : d.HasEqualSides m) (ν : Fin 4) (t : ℝ) :
    spaceEquivTorus h (BoxTorus.projection d.sideLengths (t • BoxTorus.basisVector ν)) =
      pointOnAxis L m ν t := by
  rw [spaceEquivTorus_projection]
  funext μ
  by_cases e : μ = ν
  · subst e
    simp [pointOnAxis, BoxTorus.basisVector]
  · simp [pointOnAxis, BoxTorus.basisVector, Pi.single_eq_of_ne e]
theorem spaceEquivTorus_mem_sublattice_iff (h : d.HasEqualSides m) (x : d.Space) :
    spaceEquivTorus h x ∈ PeriodicLattice.sublattice L m κ ↔
      x ∈ BoxTorus.gridSubgroup L κ d.sideLengths := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, (spaceEquivTorus h).injective ?_⟩
    rw [spaceEquivTorus_projection]
    exact funext hn
  · rintro ⟨n, rfl⟩
    exact ⟨n, fun μ => by rw [spaceEquivTorus_projection]⟩
def gridPointEquivSite (h : d.HasEqualSides m) : d.GridPoint ≃ PeriodicLattice.Site L m κ :=
  (spaceEquivTorus h).toEquiv.subtypeEquiv fun x => (spaceEquivTorus_mem_sublattice_iff h x).symm
theorem coe_gridPointEquivSite (h : d.HasEqualSides m) (x : d.GridPoint) :
    (gridPointEquivSite h x : PeriodicLattice.FourTorus L m) = spaceEquivTorus h (x : d.Space) :=
  rfl
theorem isNeighbourStep_iff (h : d.HasEqualSides m) (x x' : d.GridPoint) (ν : Fin 4) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    BoxTorus.IsNeighbourStep x x' ν σ ↔
      (gridPointEquivSite h x' : PeriodicLattice.FourTorus L m) =
        (gridPointEquivSite h x : PeriodicLattice.FourTorus L m) +
          pointOnAxis L m ν (σ * meshSize L κ) := by
  rw [coe_gridPointEquivSite, coe_gridPointEquivSite, ← spaceEquivTorus_smul_basisVector h,
    ← map_add, (spaceEquivTorus h).injective.eq_iff]
  exact ⟨fun e => e.2, fun e => ⟨hσ, e⟩⟩
theorem pointOnAxis_neg (ν : Fin 4) (t : ℝ) : pointOnAxis L m ν (-t) = -pointOnAxis L m ν t := by
  funext μ
  by_cases e : μ = ν
  · subst e
    simp [pointOnAxis]
  · simp [pointOnAxis, Pi.single_eq_of_ne e]
def bondOfEdge (h : d.HasEqualSides m) (b : d.DirectedEdge) : PeriodicLattice.Bond L m κ where
  source := gridPointEquivSite h b.source
  target := gridPointEquivSite h b.target
  isNeighbour := by
    obtain ⟨ν, σ, hs⟩ := b.isNeighbour
    have e := (isNeighbourStep_iff h _ _ ν hs.1).mp hs
    refine ⟨ν, ?_⟩
    rcases hs.1 with rfl | rfl
    · refine Or.inl (Subtype.ext ?_)
      rw [AddSubgroup.coe_sub, e, one_mul, add_sub_cancel_left]
      rfl
    · refine Or.inr (Subtype.ext ?_)
      rw [AddSubgroup.coe_sub, e, neg_one_mul, add_sub_cancel_left, pointOnAxis_neg]
      rfl
def edgeOfBond (h : d.HasEqualSides m) (b : PeriodicLattice.Bond L m κ) : d.DirectedEdge where
  source := (gridPointEquivSite h).symm b.source
  target := (gridPointEquivSite h).symm b.target
  isNeighbour := by
    obtain ⟨ν, e | e⟩ := b.isNeighbour
    · refine ⟨ν, 1, (isNeighbourStep_iff h _ _ ν (Or.inl rfl)).mpr ?_⟩
      have e' : (b.target : PeriodicLattice.FourTorus L m) =
          b.source + pointOnAxis L m ν (meshSize L κ) :=
        congrArg Subtype.val (sub_eq_iff_eq_add'.mp e)
      simpa [one_mul] using e'
    · refine ⟨ν, -1, (isNeighbourStep_iff h _ _ ν (Or.inr rfl)).mpr ?_⟩
      have e' : (b.target : PeriodicLattice.FourTorus L m) =
          b.source + -pointOnAxis L m ν (meshSize L κ) :=
        congrArg Subtype.val (sub_eq_iff_eq_add'.mp e)
      simpa [neg_one_mul, pointOnAxis_neg] using e'
def edgeEquivBond (h : d.HasEqualSides m) : d.DirectedEdge ≃ PeriodicLattice.Bond L m κ where
  toFun := bondOfEdge h
  invFun := edgeOfBond h
  left_inv _ := BoxTorus.DirectedEdge.ext ((gridPointEquivSite h).symm_apply_apply _)
    ((gridPointEquivSite h).symm_apply_apply _)
  right_inv _ := PeriodicLattice.Bond.ext ((gridPointEquivSite h).apply_symm_apply _)
    ((gridPointEquivSite h).apply_symm_apply _)
def toBondField (h : d.HasEqualSides m) (U : d.GaugeConfig) :
    PeriodicLattice.Bond L m κ → Matrices.ComplexMatrix2 :=
  fun b => (BoxTorus.edgeVariable U ((edgeEquivBond h).symm b) : Matrices.ComplexMatrix2)
def plaquetteOfFace (h : d.HasEqualSides m) (p : d.Face) : PeriodicLattice.Plaquette L m κ where
  origin := gridPointEquivSite h p.corner
  firstAxis := p.dir₁
  secondAxis := p.dir₂
  firstAxis_lt_secondAxis := p.dir₁_lt_dir₂
end CellGrid
namespace EqualSideGrids
open CellGrid
variable {L m : ℕ} {κ : ℤ} {d : CellGrid L κ}
def SameSpaceAndEdges (h : d.HasEqualSides m) : Prop :=
  IsHomeomorph (spaceEquivTorus h) ∧
  spaceEquivTorus h '' (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) =
    (PeriodicLattice.sublattice L m κ : Set (PeriodicLattice.FourTorus L m)) ∧
  (∀ b : d.DirectedEdge, b.IsForward ↔ (edgeEquivBond h b).IsPositivelyOriented) ∧
  ∀ b : d.DirectedEdge, edgeEquivBond h b.flip = (edgeEquivBond h b).opposite
def SameGaugeFields (h : d.HasEqualSides m) : Prop :=
  Set.BijOn (toBondField h) Set.univ (PeriodicLattice.compactGaugeFields L m κ) ∧
  (BoxTorus.haarConfigMeasure L κ d.sideLengths).map (toBondField h) =
    PeriodicLattice.productHaarMeasure L m κ
def SameActionAndGibbsMeasure {K : ℕ} {d : CellGrid L (K : ℤ)} (h : d.HasEqualSides m) (β : ℝ) :
    Prop :=
  (∀ (U : d.GaugeConfig) (p : d.Face),
    (BoxTorus.faceHolonomy U p : Matrices.ComplexMatrix2) =
        PeriodicLattice.plaquetteHolonomy (toBondField h U) (plaquetteOfFace h p) ∧
      BoxTorus.faceEnergy U p =
        PeriodicLattice.plaquetteCost (toBondField h U) (plaquetteOfFace h p)) ∧
  (∀ U : d.GaugeConfig, d.wilsonAction U = PeriodicLattice.wilsonAction (toBondField h U)) ∧
  d.normalizingIntegral β = PeriodicLattice.partitionFunction L m K β ∧
  (d.gibbsMeasure β).map (toBondField h) = PeriodicLattice.wilsonGibbsMeasure L m K β ∧
  ∀ F : (PeriodicLattice.Bond L m (K : ℤ) → Matrices.ComplexMatrix2) → ℂ, Measurable F →
    (∃ C : ℝ, ∀ U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ), ‖F U‖ ≤ C) →
    d.gibbsMean β (fun U => F (toBondField h U)) =
      PeriodicLattice.gibbsExpectation L m K β F
def Statement : Prop :=
  ∀ (s : Conventions.StandingParameters) (d : CellGrid s.L ((s.K : ℕ) : ℤ))
    (h : d.HasEqualSides (s.m : ℕ)) (β : ℝ), 0 < β →
    SameSpaceAndEdges h ∧ SameGaugeFields h ∧ SameActionAndGibbsMeasure h β
end EqualSideGrids
end YangMills.Construction
end
