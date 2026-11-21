import YangMills.Construction.ClusterExpansionOfAStep.LawOfAWeightOnSpins
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction
namespace LinearResponse
open Dobrushin
def TiltedGibbsComparison : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (S : I → Type) [∀ i, MeasurableSpace (S i)] (A : PairConstraint S)
    (m : ∀ i, Measure (S i)) [∀ i, SigmaFinite (m i)] (G Y : (∀ i, S i) → ℝ) (z z' : I → ℝ)
    (h : A.IsActivityBounded m G z) (_ : A.IsActivityBounded m (fun σ => G σ * Y σ) z') (c : I → I → ℝ) (b w : I → ℝ),
    (∀ σ, A.IsAdmissible σ → 0 < Y σ) → (∀ i, z i ≤ 1) → (∀ i j, 0 ≤ c i j) → (∀ i, 0 ≤ b i) → (∀ i, 0 < w i) →
    (∀ i j, i ≠ j → ∀ σ σ', A.IsAdmissible σ → A.IsAdmissible σ' → (∀ k, k ≠ j → σ k = σ' k) →
      ∀ B, MeasurableSet B →
        (A.singleSiteKernel m h.measurable_weightDensity i σ).real B ≤
          (A.singleSiteKernel m h.measurable_weightDensity i σ').real B + c i j / 2) →
    (∀ j, ∑ i, w i * c i j ≤ w j / 2) →
    (∀ i, 2 * (z i + z' i) ≤ b i ∨ ∃ e : ℝ, 0 ≤ e ∧ e ≤ 1 ∧ 8 * e * z i ≤ b i ∧
      ∀ σ (s : S i), A.IsAdmissible (Function.update σ i s) → s ≠ A.vacant i →
        |Y (Function.update σ i s) - Y (Function.update σ i (A.vacant i))| ≤
          e * Y (Function.update σ i (A.vacant i))) →
    ∃ a : I → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, w i * a i ≤ 2 * ∑ i, w i * b i ∧
      ∀ (F : (∀ i, S i) → ℝ) (o : I → ℝ), Measurable F → (∃ C, ∀ σ, |F σ| ≤ C) → A.OscillationBound F o →
        |∫ σ, F σ ∂A.gibbsLaw m G - ∫ σ, F σ ∂A.gibbsLaw m (fun σ => G σ * Y σ)| ≤ ∑ i, a i * o i
end LinearResponse
end YangMills.Construction
end
