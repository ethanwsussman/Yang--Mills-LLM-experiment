import YangMills.Construction.Lattice.ActionOfABareGaugeTransformation
import YangMills.Construction.Lattice.AmbientSpaceOfTheRealPairsOnADomain
import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSites
import YangMills.Construction.RunningCouplingSlope.IndicesInACellAreBounded
import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace CellIndexCount
open Tower
variable {L n k : ℕ}
private abbrev CellVertices (c : Vertex L n k k) : Type := ↥(PeriodicLattice.refinedBlock k c)
private theorem vertex_mem_cell (hcell : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} {v : Vertex L n k m} {c : Vertex L n k k}
    (hv : levelVertexCell v = c) : (v : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k c := by
  have hpos : 0 < L := by
    have := hL.2
    omega
  have h1 := (hcell L hL n k).2.2.1 (v.toSublattice (PeriodicLattice.levelDepth k 0))
  rw [PeriodicLattice.coe_toSublattice_finest hpos v] at h1
  rw [← hv]
  exact h1
private theorem card_vertexIndices_le (hcell : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {c : Vertex L n k k} [Finite (CellVertices c)] {m : ℕ} :
    Nat.card {p : Fin 3 × Vertex L n k m // levelVertexCell p.2 = c} ≤
      Nat.card (Fin 3 × CellVertices c) := by
  refine Nat.card_le_card_of_injective
    (fun p => (p.1.1, ⟨(p.1.2 : PeriodicLattice.FourTorus L n), vertex_mem_cell hcell hL p.2⟩)) ?_
  rintro ⟨⟨a, v⟩, hv⟩ ⟨⟨a', v'⟩, hv'⟩ e
  have e1 : a = a' := congrArg Prod.fst e
  have e2 : (v : PeriodicLattice.FourTorus L n) = v' := congrArg (fun t => (t.2 : PeriodicLattice.FourTorus L n)) e
  exact Subtype.ext (Prod.ext e1 (Subtype.ext e2))
private theorem card_edgeIndices_le (hcell : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {c : Vertex L n k k} [Finite (CellVertices c)] {m : ℕ} :
    Nat.card {p : Fin 3 × PositiveEdge L n k m // levelVertexCell p.2.1.source = c} ≤
      Nat.card (Fin 3 × Fin 4 × CellVertices c) := by
  refine Nat.card_le_card_of_injective
    (fun p => (p.1.1, Classical.choose p.1.2.2,
      ⟨(p.1.2.1.source : PeriodicLattice.FourTorus L n), vertex_mem_cell hcell hL p.2⟩)) ?_
  rintro ⟨⟨a, b⟩, hb0⟩ ⟨⟨a', b'⟩, hb0'⟩ e
  have e1 : a = a' := congrArg Prod.fst e
  have e2 : Classical.choose b.2 = Classical.choose b'.2 := congrArg (fun t => t.2.1) e
  have e3 : (b.1.source : PeriodicLattice.FourTorus L n) = b'.1.source :=
    congrArg (fun t => (t.2.2 : PeriodicLattice.FourTorus L n)) e
  have e4 : b.1.source = b'.1.source := Subtype.ext e3
  have hb := Classical.choose_spec b.2
  have hb' := Classical.choose_spec b'.2
  rw [← e2] at hb'
  have e5 : b.1.target = b'.1.target := by
    have := hb.trans hb'.symm
    rw [e4] at this
    exact sub_left_injective this
  exact Subtype.ext (Prod.ext e1 (Subtype.ext (PeriodicLattice.Bond.ext e4 e5)))
end CellIndexCount
open CellIndexCount Tower in
theorem indicesPerCellBounded_holds (hcell : NeighbouringFineVertexCells)
    (hblocks : Tower.BlockPathContourPivotStatement) :
    IndicesPerCellBounded := by
  intro L hL k hk
  refine ⟨((k + 1) * (12 * L ^ (4 * k)) : ℕ), by positivity, fun n hn c => ?_⟩
  have hcard : (PeriodicLattice.refinedBlock k c : Set (PeriodicLattice.FourTorus L n)).ncard = L ^ (4 * k) :=
    ((hblocks L hL k k k hk le_rfl le_rfl).1 n hn).1.ncard_eq c
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hfin : (PeriodicLattice.refinedBlock k c : Set (PeriodicLattice.FourTorus L n)).Finite :=
    Set.finite_of_ncard_pos (by
      rw [hcard]
      positivity)
  have : Finite (CellVertices c) := hfin
  have hP : Nat.card (CellVertices c) = L ^ (4 * k) := by
    rw [← hcard]
    exact Nat.card_coe_set_eq _
  have h1 : ∀ m, Nat.card {p : Fin 3 × Vertex L n k m // levelVertexCell p.2 = c} ≤
      12 * L ^ (4 * k) := fun m => by
    refine (card_vertexIndices_le hcell hL).trans ?_
    rw [Nat.card_prod, hP, Nat.card_eq_fintype_card, Fintype.card_fin]
    nlinarith [Nat.zero_le (L ^ (4 * k))]
  have h2 : ∀ m, Nat.card {p : Fin 3 × PositiveEdge L n k m // levelVertexCell p.2.1.source = c} ≤
      12 * L ^ (4 * k) := fun m => by
    refine (card_edgeIndices_le hcell hL).trans ?_
    rw [Nat.card_prod, Nat.card_prod, hP, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_fin, Fintype.card_fin]
    nlinarith [Nat.zero_le (L ^ (4 * k))]
  have hle : 12 * L ^ (4 * k) ≤ (k + 1) * (12 * L ^ (4 * k)) := by
    nlinarith [Nat.zero_le (k * (12 * L ^ (4 * k)))]
  have : NeZero L := ⟨by omega⟩
  have hedges : ∀ m, Finite (Edge L n k m) := fun m => PeriodicLattice.instFiniteBond _
  refine ⟨fun m _ => by exact_mod_cast (h1 m).trans hle, fun m _ => by exact_mod_cast (h2 m).trans hle,
    ?_⟩
  have hfe : ∀ m, Finite {p : Fin 3 × PositiveEdge L n k m // levelVertexCell p.2.1.source = c} :=
    fun m => by
      have := hedges m
      infer_instance
  let A := {p : Fin 3 × PositiveEdge L n k 0 // levelVertexCell p.2.1.source = c}
  let B := Σ i : Fin k, {p : Fin 3 × PositiveEdge L n k (i + 1) // levelVertexCell p.2.1.source = c}
  have hBf : ∀ i : Fin k, Finite {p : Fin 3 × PositiveEdge L n k (i + 1) //
      levelVertexCell p.2.1.source = c} := fun i => hfe _
  have hAf : Finite A := hfe 0
  have hinj : Function.Injective (fun q : {q : LevelFormIndex L n k //
      levelFormIndexCell q = c} => (match q with
        | ⟨.inl p, h⟩ => .inl ⟨p, h⟩
        | ⟨.inr ⟨i, p⟩, h⟩ => .inr ⟨i, ⟨p, h⟩⟩ : A ⊕ B)) := by
    rintro ⟨p | ⟨i, p⟩, h⟩ ⟨p' | ⟨i', p'⟩, h'⟩ e
    · have e1 : p = p' := congrArg Subtype.val (Sum.inl.inj e)
      subst e1
      rfl
    · simp at e
    · simp at e
    · obtain ⟨rfl, e2⟩ := Sigma.mk.inj_iff.1 (Sum.inr.inj e)
      have e4 : p = p' := congrArg Subtype.val (eq_of_heq e2)
      subst e4
      rfl
  have hcount : Nat.card {q : LevelFormIndex L n k // levelFormIndexCell q = c} ≤
      (k + 1) * (12 * L ^ (4 * k)) := by
    refine (Nat.card_le_card_of_injective _ hinj).trans ?_
    rw [Nat.card_sum, Nat.card_sigma]
    have hA : Nat.card A ≤ 12 * L ^ (4 * k) := h2 0
    have hS : ∑ i : Fin k, Nat.card {p : Fin 3 × PositiveEdge L n k (i + 1) //
        levelVertexCell p.2.1.source = c} ≤ k * (12 * L ^ (4 * k)) := by
      calc _ ≤ ∑ _i : Fin k, 12 * L ^ (4 * k) := Finset.sum_le_sum fun i _ => h2 _
        _ = k * (12 * L ^ (4 * k)) := by simp
    calc _ ≤ 12 * L ^ (4 * k) + k * (12 * L ^ (4 * k)) := add_le_add hA hS
      _ = (k + 1) * (12 * L ^ (4 * k)) := by ring
  exact_mod_cast hcount
end YangMills.Construction.RunningCouplingSlope
end
