import YangMills.Construction.Towers.TheDilationOfAWaveOfTheThirdColourProof
import YangMills.Construction.Towers.TheFormsOfBondsAsFieldsOnTheClasses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOperators
namespace EdgeFormQuotIndicator
open OneLoopLaw.FunctionalStiffness
variable {L m : ℕ}
theorem pauliZ_mem_traceless :
    Matrices.ComplexMatrix2.pauliFamily 2 ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.ThirdColourScaling.pauliFamily_two_mem_traceless <;> assumption
theorem pauliCoeff_pauliZ (a : Fin 3) :
    pauliCoeff a (Matrices.ComplexMatrix2.pauliFamily 2) = if a = 2 then 1 else 0 := by
  simp only [pauliCoeff, dif_pos pauliZ_mem_traceless]
  fin_cases a <;>
    simp [OneLoop.pauliCoordinateEquiv, Matrices.ComplexMatrix2.pauliFamily, OneLoop.pauliZ]
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem edge_orientation_xor (hXor : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (b : Edge L m 0 0) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
  have e : PeriodicLattice.levelDepth 1 1 = PeriodicLattice.levelDepth 0 0 := by
    simp [PeriodicLattice.levelDepth]
  have h₁ := hXor L m 1 hL hm one_pos 1 le_rfl
  unfold Edge PeriodicLattice.BondAtLevel at *
  rw [e] at h₁
  exact h₁ b
open Classical in
theorem liftedPauliForm_apply (q : EffectiveAction.IntBond) (c : PositiveEdge L m 0 0) :
    liftedPauliForm L m 2 q c.1 =
      if c = positiveImage L m q then Matrices.ComplexMatrix2.pauliFamily 2 else 0 := by
  simp only [liftedPauliForm, pauliEdgeForm, extendOddly, if_pos c.2, Subtype.ext_iff]
theorem liftedPauliForm_mem
    (hX : ∀ b : Edge L m 0 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (q : EffectiveAction.IntBond) : liftedPauliForm L m 2 q ∈ complexEdgeForms L m 0 0 := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · have e := liftedPauliForm_apply (L := L) (m := m) q ⟨b, hb⟩
    change liftedPauliForm L m 2 q b ∈ Matrices.ComplexMatrix2.traceless
    simp only at e
    rw [e]
    split_ifs
    · exact pauliZ_mem_traceless
    · exact Matrices.ComplexMatrix2.traceless.zero_mem
  · simp only [liftedPauliForm, pauliEdgeForm, extendOddly]
    rcases hX b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have e : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
      rw [if_neg h₂, if_pos h₁, e]
    · rw [if_pos h₁, if_neg h₂, neg_neg]
theorem projVertex_eq_projectSite (q : EffectiveAction.IntPoint) (x : FullSpace.Vertex L 0 0)
    (hx : ∀ μ, (x : InfiniteLattice.AmbientSpace) μ = (q μ : ℝ)) :
    FullSpace.projVertex L m 0 0 x = EffectiveAction.projectSite L m 0 0 q := by
  apply Subtype.ext
  funext μ
  have hs : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth 0 0) = 1 := by
    simp [PeriodicLattice.meshSize]
  change (((x : InfiniteLattice.AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) =
    (((q μ : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth 0 0) : ℝ) : AddCircle _)
  rw [hx μ, hs, mul_one]
theorem projVertex_add_axisStep (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    FullSpace.projVertex L m 0 0 (x + InfiniteLattice.axisStep (meshAt L 0 0) μ) =
      FullSpace.projVertex L m 0 0 x +
        PeriodicLattice.unitStep L m (PeriodicLattice.levelDepth 0 0) μ := by
  apply Subtype.ext
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp [FullSpace.projVertex, TorusMetric.torusProj, InfiniteLattice.axisStep,
      PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis]
    simp [PeriodicLattice.meshSize, meshAt]
  · simp [FullSpace.projVertex, TorusMetric.torusProj, InfiniteLattice.axisStep,
      PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hν]
theorem projPositiveEdge_forwardEdge (hB : LocalKernels.Periodisation.ProjEdgesCompatible L m 0 0)
    (q : EffectiveAction.IntBond) (x : FullSpace.Vertex L 0 0)
    (hx : ∀ μ, (x : InfiniteLattice.AmbientSpace) μ = (q.1 μ : ℝ)) :
    LocalKernels.projPositiveEdge L m 0 0 (FullSpace.forwardEdge x q.2) = positiveImage L m q := by
  apply Subtype.ext
  rw [hB.2.1]
  refine PeriodicLattice.Bond.ext ?_ ?_
  · rw [(hB.1 _).1]
    exact projVertex_eq_projectSite q.1 x hx
  · rw [(hB.1 _).2]
    change FullSpace.projVertex L m 0 0 (x + InfiniteLattice.axisStep (meshAt L 0 0) q.2) =
      EffectiveAction.projectSite L m 0 0 q.1 +
        PeriodicLattice.unitStep L m (PeriodicLattice.levelDepth 0 0) q.2
    rw [projVertex_add_axisStep, projVertex_eq_projectSite q.1 x hx]
theorem mkQuot_eq_iff (hC : LocalKernels.Periodisation.ProjCellsClassified L m 0 0) (a a' : Fin 3)
    (b b' : PeriodicOperators.PosEdge L 0 0) :
    (PeriodicOperators.colourEdges L 0 0).mkQuot (2 * L ^ m) (a, b) =
        (PeriodicOperators.colourEdges L 0 0).mkQuot (2 * L ^ m) (a', b') ↔
      a = a' ∧ LocalKernels.projPositiveEdge L m 0 0 b = LocalKernels.projPositiveEdge L m 0 0 b' := by
  have hc := (hC .edge).2
  constructor
  · intro h
    let g : (PeriodicOperators.colourEdges L 0 0).Carrier → Fin 3 × PositiveEdge L m 0 0 :=
      fun κ => (κ.1, LocalKernels.projPositiveEdge L m 0 0 κ.2)
    have hg : ∀ ι ι' : (PeriodicOperators.colourEdges L 0 0).Carrier,
        (∃ v : Fin 4 → ℤ, ι' = (PeriodicOperators.colourEdges L 0 0).translate ((2 * L ^ m) • v) ι) →
          g ι = g ι' := by
      rintro ι _ ⟨v, rfl⟩
      exact Prod.ext rfl ((hc ι.2 _).2 ⟨v, rfl⟩)
    have e := congrArg (Quot.lift g hg) h
    exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
  · rintro ⟨rfl, e⟩
    obtain ⟨v, hv⟩ := (hc b b').1 e
    refine Quot.sound ⟨v, ?_⟩
    exact Prod.ext rfl hv
end EdgeFormQuotIndicator
open EdgeFormQuotIndicator OneLoopLaw.FunctionalStiffness in
theorem edgeFormIsQuotIndicator_holds
    (hCells : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hXor : PeriodicLattice.LevelBondOrientationDichotomy) :
    EdgeFormIsQuotIndicator := by
  intro L hL m hm q x hx
  obtain ⟨hC, hB⟩ := (hCells L hL 0 m hm).1 0 le_rfl
  refine ⟨liftedPauliForm_mem (edge_orientation_xor hXor hL hm) q, ?_⟩
  have hs : ∀ κ : (remainderIndex L 0).Carrier,
      PeriodicOperators.UnitFieldTraces.quotIndicator (PeriodicOperators.colourEdges L 0 0)
          (2 * L ^ m) ((2 : Fin 3), FullSpace.forwardEdge x q.2)
          ((remainderIndex L 0).mkQuot (2 * L ^ m) κ) =
        remainderCoeffs (liftedPauliForm L m 2 q) κ := by
    rintro ⟨a, b⟩
    have e : remainderCoeffs (liftedPauliForm L m 2 q) (a, b) =
        pauliCoeff a (liftedPauliForm L m 2 q (LocalKernels.projPositiveEdge L m 0 0 b).1) := rfl
    rw [e, liftedPauliForm_apply, ← projPositiveEdge_forwardEdge hB q x hx]
    simp only [PeriodicOperators.UnitFieldTraces.quotIndicator]
    have hcl := mkQuot_eq_iff hC a 2 b (FullSpace.forwardEdge x q.2)
    by_cases hb : LocalKernels.projPositiveEdge L m 0 0 b =
        LocalKernels.projPositiveEdge L m 0 0 (FullSpace.forwardEdge x q.2)
    · rw [if_pos hb, pauliCoeff_pauliZ]
      by_cases ha : a = 2
      · rw [if_pos ha, if_pos (hcl.2 ⟨ha, hb⟩)]
      · rw [if_neg ha, if_neg fun h => ha (hcl.1 h).1]
    · rw [if_neg hb, pauliCoeff_zero, if_neg fun h => hb (hcl.1 h).2]
  have spec := Classical.epsilon_spec
    (p := fun f : (remainderIndex L 0).QuotMod (2 * L ^ m) → ℂ =>
      ∀ κ : (remainderIndex L 0).Carrier,
        f ((remainderIndex L 0).mkQuot (2 * L ^ m) κ) =
          remainderCoeffs (liftedPauliForm L m 2 q) κ) ⟨_, hs⟩
  funext c
  induction c using Quot.ind with
  | mk κ => exact (spec κ).trans (hs κ).symm
end YangMills.Construction.Tower.MassiveOperators
end
