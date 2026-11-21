import YangMills.Construction.InfiniteLattice.SpecificationOnObservables
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def WindowSpecificationForms.Statement : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (β : ℝ), 0 < β → ∀ (W : LinkWindow a) (ξ : GaugeField a),
    (∫ V, Real.exp (-β * W.windowAction (W.glue ha V ξ)) ∂W.haarProd) =
        partitionFunction β W.links ξ ∧
      IsProbabilityMeasure (wilsonSpecification β W.links ξ) ∧
      ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        W.conditionalAverage ha β F ξ = W.wilsonKernel ha β F ξ ∧
          W.conditionalAverage ha β F ξ =
            ∫ V, F (W.glue ha V ξ) ∂wilsonSpecification β W.links ξ
end InfiniteLattice
end YangMills.Construction
