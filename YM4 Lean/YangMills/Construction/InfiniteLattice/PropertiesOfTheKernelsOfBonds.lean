import YangMills.Construction.InfiniteLattice.KernelsOfFiniteSetsOfBonds
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace GibbsAtFixedSpacing
variable {a : ℝ}
def kernelNumerator (Λ : Finset (Link a)) (hΛ : HasNoOppositePairs (Λ : Set (Link a)))
    (W : GaugeField a → ℝ) (F : GaugeField a → ℂ) (U : GaugeField a) : ℂ :=
  ∫ V, F (overwriteLinks hΛ V U) * (Real.exp (-W (overwriteLinks hΛ V U)) : ℂ)
    ∂LinkVariables.haarMeasure (Λ : Set (Link a))
def kernelDenominator (Λ : Finset (Link a))
    (hΛ : HasNoOppositePairs (Λ : Set (Link a))) (W : GaugeField a → ℝ)
    (U : GaugeField a) : ℝ :=
  ∫ V, Real.exp (-W (overwriteLinks hΛ V U)) ∂LinkVariables.haarMeasure (Λ : Set (Link a))
theorem linkKernel_eq_div (Λ : Finset (Link a))
    (hΛ : HasNoOppositePairs (Λ : Set (Link a))) (W : GaugeField a → ℝ)
    (F : GaugeField a → ℂ) (U : GaugeField a) :
    linkKernel Λ hΛ W F U =
      kernelNumerator Λ hΛ W F U / (kernelDenominator Λ hΛ W U : ℂ) := rfl
def oscillation (D : GaugeField a → ℝ) : ℝ := (⨆ U, D U) - ⨅ U, D U
def IsPartialReversal (Λ' Λ : Finset (Link a)) : Prop :=
  ∃ R : Set (Link a), R ⊆ (Λ : Set (Link a)) ∧
    (Λ' : Set (Link a)) = ((Λ : Set (Link a)) \ R) ∪ Link.opposite '' R
def LinkKernelProperties : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ (Λ : Finset (Link a))
    (hΛ : HasNoOppositePairs (Λ : Set (Link a))) (W W' : GaugeField a → ℝ),
    IsRealLocalContinuous W → IsRealLocalContinuous W' →
    ((∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        (∀ U : GaugeField a,
          Integrable (fun V => F (overwriteLinks hΛ V U) * (Real.exp (-W (overwriteLinks hΛ V U)) : ℂ))
            (LinkVariables.haarMeasure (Λ : Set (Link a))) ∧
          Integrable (fun V => Real.exp (-W (overwriteLinks hΛ V U)))
            (LinkVariables.haarMeasure (Λ : Set (Link a)))) ∧
        IsBoundedObservable (kernelNumerator Λ hΛ W F) ∧
        IsBoundedObservable (fun U => (kernelDenominator Λ hΛ W U : ℂ)) ∧
        (∀ U : GaugeField a,
          Real.exp (-observableSupNorm fun U' => (W U' : ℂ)) ≤ kernelDenominator Λ hΛ W U) ∧
        IsBoundedObservable (linkKernel Λ hΛ W F) ∧
        IsIndependentOfLinks hΛ (linkKernel Λ hΛ W F) ∧
        ((∀ U : GaugeField a, 0 ≤ F U) → ∀ U : GaugeField a, 0 ≤ linkKernel Λ hΛ W F U) ∧
        observableSupNorm (linkKernel Λ hΛ W F) ≤ observableSupNorm F) ∧
      (∀ (c c' : ℂ) (F F' : GaugeField a → ℂ), IsBoundedObservable F → IsBoundedObservable F' →
        linkKernel Λ hΛ W (fun U => c * F U + c' * F' U) =
          fun U => c * linkKernel Λ hΛ W F U + c' * linkKernel Λ hΛ W F' U) ∧
      linkKernel Λ hΛ W (fun _ => 1) = fun _ => 1) ∧
    (∀ H F : GaugeField a → ℂ, IsBoundedObservable H → IsBoundedObservable F →
      IsIndependentOfLinks hΛ H →
      linkKernel Λ hΛ W (fun U => H U * F U) = fun U => H U * linkKernel Λ hΛ W F U) ∧
    ((∀ (S : Set (Link a)) (F : GaugeField a → ℂ), S ⊆ positiveLinkSet a →
        IsBoundedObservable F → DependsOnlyOnLinks S W → DependsOnlyOnLinks S F →
        DependsOnlyOnLinks S (linkKernel Λ hΛ W F)) ∧
      (∀ F : GaugeField a → ℂ, IsBoundedObservable F → Continuous F →
        Continuous (linkKernel Λ hΛ W F)) ∧
      ∀ F ∈ continuousLocal a, linkKernel Λ hΛ W F ∈ continuousLocal a) ∧
    (∀ ν : BorelProb a, ∃! μ : BorelProb a, ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      μ.integral F = ν.integral (linkKernel Λ hΛ W F)) ∧
    (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      observableSupNorm (fun U => linkKernel Λ hΛ W F U - linkKernel Λ hΛ W' F U) ≤
        observableSupNorm F * (Real.exp (oscillation fun U => W U - W' U) - 1)) ∧
    (IsIndependentOfLinks hΛ (fun U => W U - W' U) →
      ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        linkKernel Λ hΛ W F = linkKernel Λ hΛ W' F) ∧
    (∀ Λ' : Finset (Link a), IsPartialReversal Λ' Λ →
      ∃ hΛ' : HasNoOppositePairs (Λ' : Set (Link a)),
        (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
          linkKernel Λ' hΛ' W F = linkKernel Λ hΛ W F) ∧
        plaquettesTouching Λ' = plaquettesTouching Λ ∧
        ∀ β : ℝ, 0 < β → ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
          wilsonLinkKernel β Λ' hΛ' F = wilsonLinkKernel β Λ hΛ F)
end GibbsAtFixedSpacing
end YangMills.Construction
