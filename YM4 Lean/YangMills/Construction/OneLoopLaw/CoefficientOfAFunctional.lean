import YangMills.Construction.EffectiveAction.Coefficient
import YangMills.Construction.PeriodicOperators.TemperedFunctionals
import YangMills.Construction.Towers.DilationOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicOperators.Tempered
namespace OneLoopLaw.FunctionalStiffness
variable {L : ℕ}
theorem sublattice_levelDepth_self (L n j : ℕ) :
    PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth j j) =
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth 0 0) := by
  simp
def siteRescale (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) (m : ℕ) :
    PeriodicLattice.SiteAtLevel L m K j ≃+ Tower.Vertex L (m + (K - j)) 0 0 :=
  (Tower.scaleVertex hL hj j).trans
    (AddEquiv.addSubgroupCongr (sublattice_levelDepth_self L (m + (K - j)) j))
theorem siteRescale_unitStep (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) (m : ℕ) (μ : Fin 4) :
    siteRescale hL hj m (PeriodicLattice.unitStep L m (PeriodicLattice.levelDepth K j) μ) =
      PeriodicLattice.unitStep L (m + (K - j)) (PeriodicLattice.levelDepth 0 0) μ := by
  refine Subtype.ext ?_
  have hstep := congrArg Subtype.val (Tower.scaleVertex_unitStep (n := m) hL hj j μ)
  simpa [siteRescale, PeriodicLattice.unitStep, PeriodicLattice.meshSize] using hstep
def bondRescale (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) (m : ℕ) :
    PeriodicLattice.BondAtLevel L m K j ≃ UnitEdge L (m + (K - j)) :=
  Tower.edgeEquivOfVertexEquiv (siteRescale hL hj m) (siteRescale_unitStep hL hj m)
theorem siteRescale_projectSite (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) (m : ℕ)
    (p : EffectiveAction.IntPoint) :
    siteRescale hL hj m (EffectiveAction.projectSite L m K j p) =
      EffectiveAction.projectSite L (m + (K - j)) 0 0 p := by
  refine Subtype.ext ?_
  have hp := Tower.scaling_gridPoint (n := m) hL hj j p
  simpa [siteRescale, EffectiveAction.projectSite, PeriodicLattice.meshSize,
    Tower.coe_scaleVertex] using hp
theorem bondRescale_projectBond (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) (m : ℕ)
    (p : EffectiveAction.IntBond) :
    bondRescale hL hj m (EffectiveAction.projectBond L m K j p) =
      EffectiveAction.projectBond L (m + (K - j)) 0 0 p := by
  refine PeriodicLattice.Bond.ext ?_ ?_
  · exact siteRescale_projectSite hL hj m p.1
  · change siteRescale hL hj m (EffectiveAction.projectSite L m K j p.1 +
      PeriodicLattice.unitStep L m (PeriodicLattice.levelDepth K j) p.2) =
      EffectiveAction.projectSite L (m + (K - j)) 0 0 p.1 +
        PeriodicLattice.unitStep L (m + (K - j)) (PeriodicLattice.levelDepth 0 0) p.2
    rw [map_add, siteRescale_projectSite, siteRescale_unitStep]
def torusFamily (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) (F : FieldFamily L) :
    EffectiveAction.TorusFunctional L K j :=
  fun m U => F (m + (K - j)) (U ∘ (bondRescale hL hj m).symm)
def pauliLieBasis : Fin 3 → Matrices.ComplexMatrix2.LieElement :=
  Matrices.PowerExpCharts.pauliLie
theorem pauliLieBasis_toMatrix (a : Fin 3) :
    (pauliLieBasis a).toMatrix = Matrices.ComplexMatrix2.pauliFamily a := rfl
structure HasStiffnessConstant (hL : 0 < L) (F : FieldFamily L) (c : ℝ) : Prop where
  isFunctional : IsLatticeFunctional L F
  torus : ∀ K j : ℕ, 0 < K → ∀ hj : j ≤ K,
    EffectiveAction.IsTorusFunctional L K j (torusFamily hL hj F)
  stiffness : ∀ K j : ℕ, 0 < K → ∀ hj : j ≤ K,
    EffectiveAction.IsTorusStiffnessWith pauliLieBasis (torusFamily hL hj F) c
def stiffnessConstant (hL : 0 < L) (F : FieldFamily L) : ℝ :=
  Classical.epsilon (HasStiffnessConstant hL F)
open Classical in
def pauliEdgeForm (L n : ℕ) (a : Fin 3) (x : PositiveUnitEdge L n) :
    UnitEdge L n → Matrices.ComplexMatrix2 :=
  Tower.extendOddly (k := 0) (j := 0) fun b =>
    if b = x.1 then Matrices.ComplexMatrix2.pauliFamily a else 0
def positiveImage (L n : ℕ) (p : EffectiveAction.IntBond) : PositiveUnitEdge L n :=
  ⟨EffectiveAction.projectBond L n 0 0 p, p.2,
    by simp [EffectiveAction.projectBond, PeriodicLattice.Bond.forwardFrom]⟩
def liftedPauliForm (L n : ℕ) (a : Fin 3) (p : EffectiveAction.IntBond) :
    UnitEdge L n → Matrices.ComplexMatrix2 :=
  pauliEdgeForm L n a (positiveImage L n p)
end OneLoopLaw.FunctionalStiffness
end YangMills.Construction
end
