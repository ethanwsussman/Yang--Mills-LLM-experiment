import YangMills.Construction.ClusterExpansionOfAStep.LabelsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open Classical in
def valuesOn {I : Type} {S : I → Type} (Γ : Finset I) (τ : ∀ i : Γ, S i) : ∀ i, WithNone (S i) :=
  fun i => if h : i ∈ Γ then Sum.inr (τ ⟨i, h⟩) else Sum.inl ()
def LintegralPiWithNone : Prop :=
  ∀ (I : Type) [Fintype I] (S : I → Type) [∀ i, MeasurableSpace (S i)] (ν : ∀ i, Measure (S i))
    [∀ i, SigmaFinite (ν i)] [∀ i, SigmaFinite (withNoneMeasure (ν i))]
    (f : (∀ i, WithNone (S i)) → ENNReal), Measurable f →
    ∫⁻ σ, f σ ∂Measure.pi (fun i => withNoneMeasure (ν i)) =
      ∑ Γ : Finset I, ∫⁻ τ, f (valuesOn Γ τ) ∂Measure.pi (fun i : Γ => ν i)
end YangMills.Construction.TorusLumps
end
