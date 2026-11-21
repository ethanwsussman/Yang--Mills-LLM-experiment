import YangMills.Construction.Towers.QuotientMapOnBonds
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.EdgeProjection
variable {L n k i : ℕ}
theorem projVertex_sub (x y : Tower.FullSpace.Vertex L k i) :
    Tower.FullSpace.projVertex L n k i (x - y) =
      Tower.FullSpace.projVertex L n k i x - Tower.FullSpace.projVertex L n k i y := by
  refine Subtype.ext (funext fun μ => ?_)
  simp [Tower.FullSpace.projVertex, TorusMetric.torusProj]
theorem projVertex_neg (x : Tower.FullSpace.Vertex L k i) :
    Tower.FullSpace.projVertex L n k i (-x) = -Tower.FullSpace.projVertex L n k i x := by
  refine Subtype.ext (funext fun μ => ?_)
  simp [Tower.FullSpace.projVertex, TorusMetric.torusProj]
theorem projVertex_axisStep (μ : Fin 4) :
    Tower.FullSpace.projVertex L n k i (InfiniteLattice.axisStep (Tower.meshAt L k i) μ) =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ := by
  refine Subtype.ext (funext fun ν => ?_)
  by_cases hνμ : ν = μ
  · subst hνμ
    simp [Tower.FullSpace.projVertex, TorusMetric.torusProj, InfiniteLattice.axisStep,
      PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Tower.meshSize_levelDepth]
  · simp [Tower.FullSpace.projVertex, TorusMetric.torusProj, InfiniteLattice.axisStep,
      PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hνμ]
theorem exists_edge_over (b : Tower.FullSpace.Edge L k i) :
    ∃ c : Tower.Edge L n k i,
      c.source = Tower.FullSpace.projVertex L n k i b.initial ∧
        c.target = Tower.FullSpace.projVertex L n k i b.terminal := by
  refine ⟨⟨Tower.FullSpace.projVertex L n k i b.initial,
    Tower.FullSpace.projVertex L n k i b.terminal, ?_⟩, rfl, rfl⟩
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · exact ⟨μ, Or.inl (by rw [← projVertex_sub, h, projVertex_axisStep])⟩
  · exact ⟨μ, Or.inr (by rw [← projVertex_sub, h, projVertex_neg, projVertex_axisStep])⟩
theorem projEdge_source (b : Tower.FullSpace.Edge L k i) :
    (Tower.FullSpace.projEdge L n k i b).source = Tower.FullSpace.projVertex L n k i b.initial :=
  (Classical.epsilon_spec (exists_edge_over b)).1
theorem projEdge_target (b : Tower.FullSpace.Edge L k i) :
    (Tower.FullSpace.projEdge L n k i b).target = Tower.FullSpace.projVertex L n k i b.terminal :=
  (Classical.epsilon_spec (exists_edge_over b)).2
theorem projEdge_opposite (b : Tower.FullSpace.Edge L k i) :
    (Tower.FullSpace.projEdge L n k i b).opposite = Tower.FullSpace.projEdge L n k i b.opposite :=
  PeriodicLattice.Bond.ext
    ((projEdge_target b).trans (projEdge_source b.opposite).symm)
    ((projEdge_source b).trans (projEdge_target b.opposite).symm)
theorem projEdge_isPositivelyOriented {b : Tower.FullSpace.Edge L k i}
    (hb : b.IsPositivelyOriented) :
    (Tower.FullSpace.projEdge L n k i b).IsPositivelyOriented := by
  obtain ⟨μ, h⟩ := hb
  refine ⟨μ, ?_⟩
  rw [projEdge_target, projEdge_source, ← projVertex_sub, h, projVertex_axisStep]
theorem projField_apply {ℬ : Set (Tower.FullSpace.Edge L k i)}
    {ℬ' : Set (Tower.Edge L n k i)} (hℬ : BijOn (Tower.FullSpace.projEdge L n k i) ℬ ℬ')
    (V : Tower.FullSpace.Edge L k i → Matrices.ComplexMatrix2) {b : Tower.FullSpace.Edge L k i}
    (hb : b ∈ ℬ) :
    Tower.FullSpace.projField L n k i ℬ V (Tower.FullSpace.projEdge L n k i b) = V b := by
  have h : ∃ b' ∈ ℬ, Tower.FullSpace.projEdge L n k i b' = Tower.FullSpace.projEdge L n k i b :=
    ⟨b, hb, rfl⟩
  have hc := h.choose_spec
  have he : h.choose = b := hℬ.injOn hc.1 hb hc.2
  unfold Tower.FullSpace.projField
  rw [dif_pos h, he]
theorem edgeProjectionProperties_holds : Tower.EdgeProjectionProperties := by
  intro L n k i _ _ _
  refine ⟨fun b => ⟨projEdge_source b, projEdge_target b, projEdge_isPositivelyOriented,
    projEdge_opposite b⟩, fun ℬ ℬ' hrev hℬ => ?_⟩
  have hclosed : PeriodicLattice.IsReversalClosed ℬ' := by
    intro c hc
    obtain ⟨b, hb, rfl⟩ := hℬ.surjOn hc
    rw [projEdge_opposite]
    exact hℬ.mapsTo (hrev b hb)
  refine ⟨hclosed, fun V hV => ⟨fun b hb => projField_apply hℬ V hb, ?_, ?_⟩⟩
  · intro c hc
    obtain ⟨b, hb, rfl⟩ := hℬ.surjOn hc
    rw [projField_apply hℬ V hb]
    exact hV.1 b hb
  · intro c hc
    obtain ⟨b, hb, rfl⟩ := hℬ.surjOn hc
    rw [projEdge_opposite, projField_apply hℬ V (hrev b hb), projField_apply hℬ V hb]
    exact hV.2 b hb
end YangMills.Construction.Tower.EdgeProjection
end
