import YangMills.Construction.InfiniteLattice.CutoffLattice
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace CutoffLattice
open YangMills.Construction.InfiniteLattice
section Covering
variable (L m K : ℕ)
abbrev torusCover : AmbientSpace → PeriodicLattice.FourTorus L m :=
  TorusMetric.torusProj (PeriodicLattice.torusSide L m)
def addVec (u : PeriodicLattice.FourTorus L m) (v : AmbientSpace) : PeriodicLattice.FourTorus L m :=
  PeriodicLattice.shiftBy L m K K u v
def projectFace (p : ElementaryPlaquette (spacingAt L K)) : PeriodicLattice.Plaquette L m (K : ℤ) :=
  ⟨projectPoint L m (K : ℤ) p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
abbrev pullbackField (U : PeriodicLattice.Bond L m (K : ℤ) → Matrices.ComplexMatrix2) : FieldsAt L K :=
  liftField L m (K : ℤ) U
def periodizedMeasure (β : ℝ) : Measure (FieldsAt L K) :=
  (PeriodicLattice.wilsonGibbsMeasure L m K β).map (pullbackField L m K)
end Covering
section WeakConvergence
variable {X : Type*} [TopologicalSpace X]
def supNorm (F : C(X, ℝ)) : ℝ := ⨆ x, |F x|
theorem supNorm_eq_norm [CompactSpace X] (F : C(X, ℝ)) : supNorm F = ‖F‖ := by
  rw [ContinuousMap.norm_eq_iSup_norm]
  rfl
def integralAgainst {Y E : Type*} [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Measure Y) (F : Y → E) : E :=
  ∫ x, F x ∂ν
def WeaklyConvergent [MeasurableSpace X] [BorelSpace X] (ν : ℕ → Measure X) (ν' : Measure X) :
    Prop :=
  ∀ F : C(X, ℝ), Tendsto (fun i => integralAgainst (ν i) F) atTop (𝓝 (integralAgainst ν' F))
end WeakConvergence
end CutoffLattice
end YangMills.Construction
