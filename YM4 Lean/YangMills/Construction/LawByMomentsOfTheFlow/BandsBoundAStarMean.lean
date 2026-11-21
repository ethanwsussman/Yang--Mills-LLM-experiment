import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldOfCopies
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentMethod
def invariantCondExpBandBoundStatement : Prop :=
  ∀ (J : Type) (P : Measure (TranslateValues J)) [IsProbabilityMeasure P] (Y : TranslateValues J → ℝ)
    (e : ℕ → TranslateValues J → ℝ) (f : ℕ → ℕ → TranslateValues J → ℝ) (p : ℕ → ℕ) (b G : ℕ → ℝ) (Bd : ℝ),
    Integrable Y P → (∀ᵐ v ∂P, 0 ≤ Y v) →
    (∀ i, Integrable (e i) P ∧ ∀ᵐ v ∂P, e i v = 0 ∨ e i v = 1) →
    (∀ i M, Integrable (f i M) P ∧ ∀ᵐ v ∂P, 0 ≤ f i M v) →
    (∀ i, 2 ≤ p i) → (∀ i, 0 ≤ b i) → (∀ i, 0 ≤ G i) →
    (∀ i, ∀ᵐ v ∂P, invariantCondExp P (e i) v ≤ b i) → (∀ i M, ∀ᵐ v ∂P, invariantCondExp P (f i M) v ≤ G i) →
    Tendsto b atTop (𝓝 0) →
    (∀ I, ∑ i ∈ Finset.range I, G i ^ (1 / (p i : ℝ)) * b i ^ (1 - 1 / (p i : ℝ)) ≤ Bd) →
    (∀ I M : ℕ, ∀ᵐ v ∂P, min (Y v) (M : ℝ) * (1 - e I v) ≤
      ∑ i ∈ Finset.range I, f i (M ^ p i) v ^ (1 / (p i : ℝ)) * e i v) →
    ∀ᵐ v ∂P, invariantCondExp P Y v ≤ Bd
end YangMills.Construction.MomentMethod
end
