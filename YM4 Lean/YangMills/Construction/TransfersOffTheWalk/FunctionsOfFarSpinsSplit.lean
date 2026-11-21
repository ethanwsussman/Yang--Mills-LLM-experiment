import YangMills.Construction.ClusterExpansionOfAStep.ComparisonOfTwoGases
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.Dobrushin
def vacateOutside {I : Type} [DecidableEq I] {S : I → Type} (A : PairConstraint S) (M : Finset I) (σ : ∀ i, S i) : ∀ i, S i :=
  fun i => if i ∈ M then σ i else A.vacant i
def polyMomentConstant (K : ℕ) : ℝ := 2 * (K.factorial : ℝ) * 2 ^ K
def decouplingConstant (K Q : ℕ) : ℝ :=
  2 * Q * polyMomentConstant K + 96 * (Q : ℝ) ^ 2 + Q * (2 * polyMomentConstant K) ^ Q
def LocalFunctionsDecoupleStatement : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (S : I → Type) [∀ i, MeasurableSpace (S i)] (A : PairConstraint S)
    (μ : ∀ i, Measure (S i)) [∀ i, SigmaFinite (μ i)] (G : (∀ i, S i) → ℝ) (z : I → ℝ)
    (hA : A.IsActivityBounded μ G z) (c : I → I → ℝ) (Q : ℕ) (k : Fin Q → ℕ) (M : Fin Q → Finset I) (w : Fin Q → I → ℝ)
    (f : Fin Q → (∀ i, S i) → ℝ) (U : Fin Q → ℝ) (N : (∀ i, S i) → ℝ) (ε δ t : ℝ),
    (∀ a, A.HasDobrushinColumns μ hA.measurable_weightDensity c (w a)) → (∀ a, ∀ i ∈ M a, 1 ≤ w a i) →
    (∀ a b, a ≠ b → ∑ i ∈ M b, w a i * z i ≤ δ) → (∀ a, Measurable (f a)) → Measurable N → (∀ σ, 0 ≤ N σ) →
    (∀ a, 0 ≤ U a) → 0 ≤ ε → 0 ≤ δ → 0 ≤ t → (∀ a σ, N (vacateOutside A (M a) σ) ≤ N σ) →
    (∀ a σ, A.IsAdmissible σ → |f a σ| ≤ U a * (1 + N σ) ^ k a) →
    (∀ a σ, A.IsAdmissible σ → |f a σ - f a (vacateOutside A (M a) σ)| ≤ ε * (U a * (1 + N σ) ^ k a)) →
    ∫⁻ σ, ENNReal.ofReal (Real.exp (N σ)) ∂A.gibbsLaw μ G ≤ 2 →
    |∫ σ, ∏ a, f a σ ∂A.gibbsLaw μ G - ∏ a, ∫ σ, f a σ ∂A.gibbsLaw μ G| ≤
      decouplingConstant (∑ a, k a) Q * (∏ a, U a) * (ε + Real.exp (-(t / 2)) + (1 + t) ^ (∑ a, k a) * δ)
end YangMills.Construction.Dobrushin
end
