import YangMills.Construction.InfiniteLattice.BondFamiliesJoinsAndContinuousFunctionsOfFinitelyManyBonds
import YangMills.Construction.InfiniteLattice.SpecificationOnObservables
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction
open InfiniteLattice FieldsAtSpacing
namespace InfiniteLattice
variable {a : ℝ}
namespace LinkWindow
variable (W : LinkWindow a)
def numeratorIntegrand (ha : 0 < a) (β : ℝ) (F : GaugeField a → ℂ)
    (ξ : GaugeField a) (V : W.Assignments) : ℂ :=
  F (W.glue ha V ξ) * (Real.exp (-β * W.windowAction (W.glue ha V ξ)) : ℂ)
def denominatorIntegrand (ha : 0 < a) (β : ℝ) (ξ : GaugeField a)
    (V : W.Assignments) : ℝ :=
  Real.exp (-β * W.windowAction (W.glue ha V ξ))
def partitionDenominator (ha : 0 < a) (β : ℝ) (ξ : GaugeField a) : ℝ :=
  ∫ V, W.denominatorIntegrand ha β ξ V ∂W.haarProd
theorem conditionalAverage_eq_div (ha : 0 < a) (β : ℝ) (F : GaugeField a → ℂ)
    (ξ : GaugeField a) :
    W.conditionalAverage ha β F ξ =
      (∫ V, W.numeratorIntegrand ha β F ξ V ∂W.haarProd) /
        (W.partitionDenominator ha β ξ : ℂ) :=
  rfl
end LinkWindow
def denominatorLowerBound (β : ℝ) (n : ℕ) : ℝ := Real.exp (-2 * β * n)
namespace ConditionalAverageProperties
def claim : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (β : ℝ), 0 < β → ∀ (W : LinkWindow a) (F H : GaugeField a → ℂ),
    IsBoundedObservable F → IsBoundedObservable H →
    (W.faces.Finite ∧
      0 < denominatorLowerBound β W.faceCount ∧
      ∀ ξ : GaugeField a,
        Integrable (W.numeratorIntegrand ha β F ξ) W.haarProd ∧
        Integrable (W.denominatorIntegrand ha β ξ) W.haarProd ∧
        denominatorLowerBound β W.faceCount ≤ W.partitionDenominator ha β ξ ∧
        W.partitionDenominator ha β ξ ≤ 1) ∧
    (IsBoundedObservable (W.conditionalAverage ha β F) ∧
      IsBlindTo (W.links : Set (Link a)) (W.conditionalAverage ha β F)) ∧
    observableSupNorm (W.conditionalAverage ha β F) ≤ observableSupNorm F ∧
    (IsBlindTo (W.links : Set (Link a)) H →
      W.conditionalAverage ha β (H * F) = H * W.conditionalAverage ha β F) ∧
    (F ∈ continuousFiniteLinkFunctions a →
      W.conditionalAverage ha β F ∈ continuousFiniteLinkFunctions a) ∧
    (W.conditionalAverage ha β (F + H) =
        W.conditionalAverage ha β F + W.conditionalAverage ha β H ∧
      (∀ z : ℂ, W.conditionalAverage ha β (z • F) = z • W.conditionalAverage ha β F) ∧
      W.conditionalAverage ha β 1 = 1 ∧
      ∀ Fs : ℕ → GaugeField a → ℂ, (∀ n, IsBoundedObservable (Fs n)) →
        BddAbove (Set.range fun n => observableSupNorm (Fs n)) →
        (∀ U, Tendsto (fun n => Fs n U) atTop (𝓝 (F U))) →
        ∀ ξ, Tendsto (fun n => W.conditionalAverage ha β (Fs n) ξ) atTop
          (𝓝 (W.conditionalAverage ha β F ξ)))
end ConditionalAverageProperties
end InfiniteLattice
end YangMills.Construction
