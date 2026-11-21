import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ProductMeasure
def glueParts {B I Q X : Type} {T : I → Type} (e : (Σ i, T i) ⊕ Q ≃ B) (c : ∀ i, T i → X) (r : Q → X) : B → X :=
  fun b => match e.symm b with
    | Sum.inl p => c p.1 p.2
    | Sum.inr u => r u
def LintegralPiPartitionStatement : Prop :=
  ∀ (B I Q X : Type) (T : I → Type) [Fintype B] [Fintype I] [Fintype Q] [∀ i, Fintype (T i)] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (e : (Σ i, T i) ⊕ Q ≃ B) (f : (B → X) → ENNReal), Measurable f →
    ∫⁻ w, f w ∂Measure.pi (fun _ : B => μ) =
      ∫⁻ c, ∫⁻ r, f (glueParts e c r) ∂Measure.pi (fun _ : Q => μ)
        ∂Measure.pi (fun i : I => Measure.pi fun _ : T i => μ)
end YangMills.Construction.ProductMeasure
end
