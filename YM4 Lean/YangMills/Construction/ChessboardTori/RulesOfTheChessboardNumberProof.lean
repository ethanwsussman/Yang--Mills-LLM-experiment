import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.ChessboardTori.CopiesOfCellFunctions
import YangMills.Construction.ChessboardTori.GroupCoordinateByCoordinate
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
namespace ChessboardExpectationRules
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem isProbabilityMeasure_liftedMeasure (hCover : LatticeCovering.CoveringStatement)
    (D : ChessboardSetup) : IsProbabilityMeasure D.liftedMeasure :=
  (hCover ⟨D.toStandingParameters, D.β, D.beta_pos⟩).2.2.1.2.2.2.2.2
theorem cellSide_pos : 0 < g.cellSide := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.cellSide_pos <;> assumption
theorem cellsWithin_finite (hCells : CellsBlocksAndSigns.Statement)
    (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    {B S : Set InfiniteLattice.AmbientSpace}
    (hB : B ∈ g.blocks) (hS : S ∈ g.cellSet) : (g.cellsWithin B).Finite := by
  have hcount := (((hCells D g).2 hside).2 B hB).2 S hS
  have hcard := hcount.2.1
  have hpos : 0 < g.cellsAcross := by
    have hg := cellSide_pos g
    unfold ReflectionGrid.cellsAcross
    exact div_pos (by linarith) hg
  refine Set.finite_of_ncard_ne_zero fun h0 => ?_
  rw [h0] at hcard
  have : (0 : ℝ) < g.cellsAcross ^ 4 := by positivity
  simp at hcard
  linarith
theorem one_mem_cellObservables (S : Set InfiniteLattice.AmbientSpace) :
    (1 : D.GaugeField → ℂ) ∈ ReflectionGrid.cellObservables (D := D) S :=
  ⟨fun _ => 1, measurable_const, ⟨1, fun _ => by simp⟩, rfl⟩
theorem norm_le_supNorm {S : Set InfiniteLattice.AmbientSpace} {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) (U : D.GaugeField) :
    ‖F U‖ ≤ InfiniteLattice.observableSupNorm F := by
  obtain ⟨f, -, ⟨C, hC⟩, rfl⟩ := hF
  exact le_ciSup (f := fun U => ‖(f ∘ ReflectionGrid.restrictField S) U‖) ⟨C, by
    rintro _ ⟨U, rfl⟩
    exact hC _⟩ U
theorem norm_transportTo_le {S S' : Set InfiniteLattice.AmbientSpace} {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) (U : D.GaugeField) :
    ‖g.transportTo S S' F U‖ ≤ InfiniteLattice.observableSupNorm F := by
  have h := norm_le_supNorm hF
    ((g.toLatticeSym (g.mover S S')).pullbackField U)
  simp only [ReflectionGrid.transportTo, ReflectionGrid.transport, Conventions.signedConjFun,
    Conventions.signedConj]
  split_ifs
  · exact h
  · rw [Complex.norm_conj]
    exact h
end ChessboardExpectationRules
theorem ChessboardExpectationRules.holds (hCopies : CellFunctionCopies.Statement)
    (hGroup : ReflectionGroupCoordinates.Statement) (hCells : CellsBlocksAndSigns.Statement)
    (hCover : LatticeCovering.CoveringStatement) : ChessboardExpectationRules.Statement := by
  intro D g hside B hB S hS
  have := ChessboardExpectationRules.isProbabilityMeasure_liftedMeasure hCover D
  have hfin := ChessboardExpectationRules.cellsWithin_finite g hCells hside hB hS
  have hcarry : ∀ S' ∈ g.cellSet, ∃ r : g.reflectionGroup, r.1 '' S = S' := fun S' hS' =>
    ((hGroup D g).2.2.2.2.2.2.1 S hS S' hS').exists
  have hone := ChessboardExpectationRules.one_mem_cellObservables (D := D) S
  refine ⟨fun F hF => ⟨fun S' hS' => ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨r, hr⟩ := hcarry S' hS'
    congr 1
    funext U
    refine finprod_mem_congr rfl fun S'' hS'' => ?_
    rw [(hCopies D g S hS S' hS' S'' hS''.1 r hr F hF F hF 1).2.2.1]
  · have hconj : ∀ S'' ∈ g.cellsWithin B, g.transportTo S S'' (fun U' => starRingEnd ℂ (F U')) =
        fun U => starRingEnd ℂ (g.transportTo S S'' F U) := fun S'' hS'' => by
      obtain ⟨r, hr⟩ := hcarry S'' hS''.1
      exact (hCopies D g S hS S'' hS''.1 S'' hS''.1 r hr F hF F hF 1).2.2.2.1
    unfold ChessboardSetup.liftedExpectation
    rw [← integral_conj]
    congr 1
    funext U
    beta_reduce
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin,
      map_prod]
    refine Finset.prod_congr rfl fun S'' hS'' => ?_
    rw [hconj S'' (hfin.mem_toFinset.mp hS'')]
  · have hb : ∀ U, ‖∏ᶠ S'' ∈ g.cellsWithin B, g.transportTo S S'' F U‖ ≤
        InfiniteLattice.observableSupNorm F ^ (g.cellsWithin B).ncard := fun U => by
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin, norm_prod, Set.ncard_eq_toFinset_card _ hfin,
        ← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        fun _ _ => ChessboardExpectationRules.norm_transportTo_le g hF U
    have h := norm_integral_le_of_norm_le_const (μ := D.liftedMeasure)
      (Filter.Eventually.of_forall hb)
    simpa [ChessboardSetup.liftedExpectation] using h
  · have h1 : (fun U => ∏ᶠ S'' ∈ g.cellsWithin B, g.transportTo S S'' (fun _ => 1) U) =
        fun _ : D.GaugeField => (1 : ℂ) := by
      funext U
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
      refine Finset.prod_eq_one fun S'' hS'' => ?_
      have hm := (hfin.mem_toFinset.mp hS'').1
      obtain ⟨r, hr⟩ := hcarry S'' hm
      exact congrFun (hCopies D g S hS S'' hm S'' hm r hr 1 hone 1 hone 1).2.2.2.2.2.2.2 U
    rw [h1]
    simp [ChessboardSetup.liftedExpectation]
end YangMills.Construction.ChessboardTori
end
