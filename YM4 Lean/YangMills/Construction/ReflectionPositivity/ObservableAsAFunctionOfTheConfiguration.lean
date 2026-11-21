import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.ReflectionPositivity.TwoSidesOfAMirrorAndTheirAlgebras
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
namespace MirrorData
variable (D : MirrorData)
@[reducible] def fieldTopology : TopologicalSpace D.LatticeGaugeField :=
  .induced (D.linkValues {b : D.LatticeBond | b.IsPositivelyOriented}) inferInstance
def IsBoundedBorelField (F : D.LatticeGaugeField → ℝ) : Prop :=
  Measurable[@borel _ D.fieldTopology] F ∧ TestFunctions.IsBoundedFun F
def observableFn (f : D.Torus → ℝ) (U : D.LatticeGaugeField) : ℝ :=
  PeriodicLattice.smearedObservable f U.1
def ObservableContinuousBounded (f : D.Torus → ℝ) : Prop :=
  Continuous[D.fieldTopology, inferInstance] (D.observableFn f) ∧
    ∀ U : D.LatticeGaugeField, |D.observableFn f U| ≤
      2 * ∑ᶠ p : D.LatticePlaquette, |f p.barycenter|
def CenteredProductsBoundedBorel (n : ℕ) : Prop :=
  ∀ (f : Fin n → D.Torus → ℝ) (α : Fin n → ℝ),
    D.IsBoundedBorelField fun U =>
      ∏ i, (D.observableFn (f i) U - α i)
def ObservableLinear (f h : D.Torus → ℝ) (t : ℝ) : Prop :=
  D.observableFn (f + t • h) =
    D.observableFn f + t • D.observableFn h
end MirrorData
def ObservableFnFacts : Prop :=
  ∀ D : MirrorData, Finite D.LatticePlaquette ∧
    (∀ f : D.Torus → ℝ, D.ObservableContinuousBounded f) ∧
    (∀ f : D.Torus → ℝ, D.IsBoundedBorelField (D.observableFn f)) ∧
    (∀ n : ℕ, D.CenteredProductsBoundedBorel n) ∧
    ∀ (f h : D.Torus → ℝ) (t : ℝ), D.ObservableLinear f h t
end YangMills.Construction.ReflectionPositivity.AxisMirror
