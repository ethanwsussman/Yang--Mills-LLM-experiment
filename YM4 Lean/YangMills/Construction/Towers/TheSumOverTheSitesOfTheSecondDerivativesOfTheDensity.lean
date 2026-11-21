import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensity
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
def SecondDerivativeSiteSum : Prop :=
  ∀ z : ℝ, 0 < z → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (q q' : EffectiveAction.IntBond) (x x' : FullSpace.Vertex L 0 0),
      (∀ μ, (x : InfiniteLattice.AmbientSpace) μ = (q.1 μ : ℝ)) →
      (∀ μ, (x' : InfiniteLattice.AmbientSpace) μ = (q'.1 μ : ℝ)) →
      Tendsto (fun n => PeriodicOperators.Tempered.complexHessian (massiveFieldFamily L z) n
          (OneLoopLaw.FunctionalStiffness.liftedPauliForm L n 2 q)
          (OneLoopLaw.FunctionalStiffness.liftedPauliForm L n 2 q')) atTop
        (𝓝 (∑' y : FullSpace.Vertex L 0 0,
          secondDerivative z y (FullSpace.forwardEdge x q.2) (FullSpace.forwardEdge x' q'.2)))
end YangMills.Construction.Tower.AbelianFieldDensity
end
