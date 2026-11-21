import YangMills.Construction.ReflectionPositivity.WeightsFormAndSeriesOfASplitTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open NormalFamilies
def ReflectionSeriesMul : Prop :=
  ∀ (Λ : PeriodSublattice 1) (k : ℤ) (P : NormalLevelPair 1),
    Λ.HasReflectionSeries k P 1 1 ∧
    (∀ (K₁ K₂ : Λ.QuotientField → ℂ) (s₁ s₂ : ℝ),
      Λ.HasReflectionSeries k P K₁ s₁ → Λ.HasReflectionSeries k P K₂ s₂ →
        Λ.HasReflectionSeries k P (K₁ * K₂) (s₁ * s₂)) ∧
    ∀ (ι : Type) (t : Finset ι) (K : ι → Λ.QuotientField → ℂ) (s : ι → ℝ),
      (∀ i ∈ t, Λ.HasReflectionSeries k P (K i) (s i)) →
        Λ.HasReflectionSeries k P (∏ i ∈ t, K i) (∏ i ∈ t, s i)
end YangMills.Construction.InfiniteLattice
