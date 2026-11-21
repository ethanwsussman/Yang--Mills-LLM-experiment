import YangMills.Construction.InfiniteLattice.SpecificationDensitiesAndTheDensityDistanceAtOneSpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace FixedSpacing
def ConditionalDensityDependsOnRim.Statement : Prop :=
  ∀ (D : Setup) (W : LinkWindow D.mesh),
    (FactorsThroughFinite ((W.links : Set (Link D.mesh)) ∪ W.rim)
        (fun U => (D.localAction W U : ℂ)) ∧
      FactorsThroughFinite W.rim (fun U' => (D.localPartition W U' : ℂ)) ∧
      (∃ φ : W.Assignments × LinkVariables W.rim → ℝ, Continuous φ ∧
        ∀ (V : W.Assignments) (U' : D.Fields),
          D.conditionalDensity W V U' = φ (V, restrictField U' W.rim)) ∧
      (∀ (V : W.Assignments) (U' : D.Fields),
        Real.exp (-(2 * D.β * (W.faceCount : ℝ))) ≤ D.conditionalDensity W V U' ∧
          D.conditionalDensity W V U' ≤ Real.exp (2 * D.β * (W.faceCount : ℝ))) ∧
      ∀ U' : D.Fields, ∫ V, D.conditionalDensity W V U' ∂W.haarProd = 1) ∧
    (∀ U' : D.Fields,
      W.haarProd.withDensity (fun V => ENNReal.ofReal (D.conditionalDensity W V U')) =
        InfiniteLattice.wilsonSpecification D.β W.links U') ∧
    (∀ F ∈ finiteLinkFunctions D.mesh, D.conditionalKernel W F ∈ finiteLinkFunctions D.mesh) ∧
    ∀ (T : Set (Link D.mesh)) (F : D.Fields → ℂ), FactorsThroughFinite T F →
      FactorsThroughFinite (W.rim ∪ (T \ (W.links : Set (Link D.mesh)))) (D.conditionalKernel W F)
end FixedSpacing
end YangMills.Construction
