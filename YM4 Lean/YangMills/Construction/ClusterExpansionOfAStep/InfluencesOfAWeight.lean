import YangMills.Construction.ClusterExpansionOfAStep.LawOfAWeightOnSpins
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
namespace Dobrushin
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
def PairConstraint.AllCompatible (A : PairConstraint S) (i j : I) : Prop := ∀ s t, A.compatible i j s t
def PairConstraint.DoubleRatioBound (A : PairConstraint S) (G : (∀ i, S i) → ℝ) (i j : I) (f : ℝ) : Prop :=
  ∀ (σ σ' : ∀ i, S i) (s : S i), A.IsAdmissible (Function.update σ i s) →
    A.IsAdmissible (Function.update σ' i s) → (∀ k, k ≠ j → σ k = σ' k) →
    G (Function.update σ i s) * G (Function.update σ' i (A.vacant i)) ≤
      Real.exp f * (G (Function.update σ' i s) * G (Function.update σ i (A.vacant i)))
def ActivityInfluenceStatement : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (S : I → Type) [∀ i, MeasurableSpace (S i)] (A : PairConstraint S)
    (m : ∀ i, Measure (S i)) [∀ i, SigmaFinite (m i)] (G : (∀ i, S i) → ℝ) (z : I → ℝ)
    (hG : A.IsActivityBounded m G z), (∀ i, z i ≤ 1 / 2) →
    (∀ i j, i ≠ j → ∀ σ σ', A.IsAdmissible σ → A.IsAdmissible σ' → (∀ k, k ≠ j → σ k = σ' k) →
      ∀ B, MeasurableSet B →
        (A.singleSiteKernel m hG.measurable_weightDensity i σ).real B ≤
          (A.singleSiteKernel m hG.measurable_weightDensity i σ').real B + z i) ∧
    (∀ i j (f : ℝ), i ≠ j → A.AllCompatible i j → 0 ≤ f → A.DoubleRatioBound G i j f →
      ∀ σ σ', A.IsAdmissible σ → A.IsAdmissible σ' → (∀ k, k ≠ j → σ k = σ' k) →
      ∀ B, MeasurableSet B →
        (A.singleSiteKernel m hG.measurable_weightDensity i σ).real B ≤
          (A.singleSiteKernel m hG.measurable_weightDensity i σ').real B + 4 * z i * min 1 f) ∧
    ∀ (M : Finset I) (F : (∀ i, S i) → ℝ), Measurable F → (∀ σ, |F σ| ≤ 1) →
      (∀ σ, (∀ i ∈ M, σ i = A.vacant i) → F σ = 0) →
      |∫ σ, F σ ∂A.gibbsLaw m G| ≤ ∑ i ∈ M, z i
end Dobrushin
end YangMills.Construction
end
