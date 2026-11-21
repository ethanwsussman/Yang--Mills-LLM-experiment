import YangMills.Construction.Towers.LogarithmsSectorsAndTheDensity
import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensityDecayProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies.UnitLatticeIndexed
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.AbelianFieldDensity YangMills.Construction.Tower.LocalFamilies
open YangMills.Construction.OneLoopNotation
theorem meshAt_zero_zero (L : ℕ) : meshAt L 0 0 = 1 := by
  simp [meshAt]
theorem exists_vertex_eq_castVec (L : ℕ) (v : Fin 4 → ℤ) :
    ∃ x : FullSpace.Vertex L 0 0,
      (x : InfiniteLattice.AmbientSpace) = PeriodicOperators.castVec v :=
  ⟨⟨PeriodicOperators.castVec v, v, fun μ => by
    simp [PeriodicOperators.castVec, meshAt_zero_zero]⟩, rfl⟩
theorem vertex_eq_castVec (L : ℕ) (x : FullSpace.Vertex L 0 0) :
    ∃ v : Fin 4 → ℤ, (x : InfiniteLattice.AmbientSpace) = PeriodicOperators.castVec v := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.HessianExpDecay.vertex_eq_castVec <;> assumption
theorem fibre_bound_of_range {J : Type} (pos : J → InfiniteLattice.AmbientSpace) (m : ℕ)
    (h : ∀ j, {j' | pos j' = pos j}.Finite ∧ {j' | pos j' = pos j}.ncard ≤ m)
    (y : InfiniteLattice.AmbientSpace) : {j | pos j = y}.Finite ∧ {j | pos j = y}.ncard ≤ m := by
  by_cases hy : ∃ j, pos j = y
  · obtain ⟨j, rfl⟩ := hy
    exact h j
  · have hempty : {j | pos j = y} = ∅ :=
      Set.eq_empty_of_forall_notMem fun j hj => hy ⟨j, hj⟩
    rw [hempty]
    simp
theorem unitLatticeIndexedSpaces (hL2 : UnitLatticeL2Statement)
    (hTrace : AbelianFieldDensity.TraceIsBoundedLinear)
    (hDecay : RangeTwoResolventDecay)
    (hLog : AbelianFieldDensity.LogSectorsAndDensity) :
    UnitLatticeIndexedSpaces := by
  intro L hL z C hz hC
  obtain ⟨-, ⟨-, -, -, hVert, hVertCoords, hVertOps⟩,
    ⟨-, -, -, hEdge, hEdgeCoords, hEdgeOps⟩⟩ := hL2.2 L
  obtain ⟨hShift, hSector⟩ := hLog
  obtain ⟨hUniq, -, -, -, -, -, hVertInt, hEdgeInt, -⟩ := hSector L hL z hz
  obtain ⟨hVertDecay, hEdgeDecay⟩ := (hDecay z C hz hC).2 L
  have hInit : ∀ e : FullSpace.PositiveEdge (meshAt L 0 0),
      ∃ μ : Fin 4, FullSpace.forwardEdge e.1.initial μ = e := by
    intro e
    obtain ⟨⟨x, μ⟩, hp, -⟩ := hUniq e
    have hx : e.1.initial = x := by
      have := congrArg (fun c : FullSpace.PositiveEdge (meshAt L 0 0) => c.1.initial) hp
      exact this.symm
    exact ⟨μ, by rw [hx]; exact hp⟩
  have hVertLog := (hShift (IndexL2 (VertexIndex L)) (IndexL2 (VertexIndex L)) z hz).1
  have hEdgeLog := (hShift (IndexL2 (EdgeIndex L)) (IndexL2 (EdgeIndex L)) z hz).1
  refine ⟨⟨⟨?_, ?_⟩, hVertCoords, hVertOps, ?_, ?_, hVertLog, hVertInt,
    hVertDecay⟩, ⟨⟨?_, ?_⟩, hEdgeCoords, hEdgeOps, ?_, ?_, hEdgeLog,
    hEdgeInt, hEdgeDecay⟩, ⟨?_, ?_⟩⟩
  · exact fun j => vertex_eq_castVec L j.2
  · refine fibre_bound_of_range _ _ fun j => ?_
    have hj := hVert.1 j.2
    change {j' | vertexPos L j' = (j.2 : InfiniteLattice.AmbientSpace)}.Finite ∧
      {j' | vertexPos L j' = (j.2 : InfiniteLattice.AmbientSpace)}.ncard ≤ 3
    rw [hj.1]
    exact ⟨Set.finite_range _, hj.2.le⟩
  · intro v
    obtain ⟨x, hx⟩ := exists_vertex_eq_castVec L v
    rw [← hx]
    exact (hTrace L x).1.1
  · intro v
    obtain ⟨x, hx⟩ := exists_vertex_eq_castVec L v
    rw [← hx]
    exact (hTrace L x).1.2
  · exact fun j => vertex_eq_castVec L j.2.1.initial
  · refine fibre_bound_of_range _ _ fun j => ?_
    have hj := hEdge.1 j.2.1.initial
    change {j' | edgePos L j' = (j.2.1.initial : InfiniteLattice.AmbientSpace)}.Finite ∧
      {j' | edgePos L j' = (j.2.1.initial : InfiniteLattice.AmbientSpace)}.ncard ≤ 12
    rw [hj.1]
    exact ⟨Set.finite_range _, hj.2.le⟩
  · intro v
    obtain ⟨x, hx⟩ := exists_vertex_eq_castVec L v
    rw [← hx]
    exact (hTrace L x).2.1.1
  · intro v
    obtain ⟨x, hx⟩ := exists_vertex_eq_castVec L v
    rw [← hx]
    exact (hTrace L x).2.1.2
  · exact fun e => vertex_eq_castVec L e.1.initial
  · refine fibre_bound_of_range _ _ fun e => ?_
    have hSub : {c | positiveEdgeInitial (L := L) c = positiveEdgeInitial e} ⊆
        Set.range (fun μ : Fin 4 => FullSpace.forwardEdge e.1.initial μ) := by
      intro c hc
      have hce : c.1.initial = e.1.initial := Subtype.ext hc
      obtain ⟨μ, hμ⟩ := hInit c
      exact ⟨μ, by rw [← hce]; exact hμ⟩
    have hFin : (Set.range (fun μ : Fin 4 => FullSpace.forwardEdge e.1.initial μ)).Finite :=
      Set.finite_range _
    refine ⟨hFin.subset hSub, (Set.ncard_le_ncard hSub hFin).trans ?_⟩
    calc (Set.range (fun μ : Fin 4 => FullSpace.forwardEdge e.1.initial μ)).ncard
        ≤ (Set.univ : Set (Fin 4)).ncard := by
          rw [← Set.image_univ]
          exact Set.ncard_image_le Set.finite_univ
      _ = 4 := by simp [Set.ncard_univ]
end YangMills.Construction.Tower.LocalFamilies.UnitLatticeIndexed
end
