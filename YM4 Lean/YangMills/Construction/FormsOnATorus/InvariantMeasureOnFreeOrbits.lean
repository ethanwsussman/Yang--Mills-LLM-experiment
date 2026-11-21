import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.GroupActions
def FreeOrbitMeasureIsProduct : Prop :=
  ∀ (K X Z : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] (m : Measure X) [IsFiniteMeasure m]
    (act : K → X → X) (σ : Z → X),
    (∀ k l x, act k (act l x) = act (k * l) x) →
    (∀ k, MeasurePreserving (act k) m m) →
    MeasurableEmbedding (fun p : K × Z => act p.1 (σ p.2)) →
    ∃ ν : Measure Z, IsFiniteMeasure ν ∧ ∀ f : X → ENNReal, Measurable f →
      ∫⁻ x in Set.range (fun p : K × Z => act p.1 (σ p.2)), f x ∂m = ∫⁻ k, ∫⁻ z, f (act k (σ z)) ∂ν ∂μ
end YangMills.Construction.GroupActions
end
