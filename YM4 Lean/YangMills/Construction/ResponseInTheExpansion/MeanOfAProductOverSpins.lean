import YangMills.Construction.ClusterExpansionOfAStep.LawOfAWeightOnSpins
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
namespace Dobrushin
def PairConstraint.HasSmallExcess {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
    (A : PairConstraint S) (m : ∀ i, Measure (S i)) (G : (∀ i, S i) → ℝ) (g : ∀ i, S i → ℝ) (e : I → ℝ) : Prop :=
  ∀ i σ, A.IsAdmissible σ →
    ∫⁻ s in {A.vacant i}ᶜ, ENNReal.ofReal (g i s - 1) * A.weightDensity G (Function.update σ i s) ∂m i ≤
      ENNReal.ofReal (e i) * A.weightDensity G (Function.update σ i (A.vacant i))
def MeanOfProductStatement : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (S : I → Type) [∀ i, MeasurableSpace (S i)] (A : PairConstraint S)
    (m : ∀ i, Measure (S i)) [∀ i, SigmaFinite (m i)] (G : (∀ i, S i) → ℝ) (z : I → ℝ)
    (_ : A.IsActivityBounded m G z) (g : ∀ i, S i → ℝ) (e : I → ℝ),
    (∀ i, Measurable (g i)) → (∀ i s, 1 ≤ g i s) → (∀ i, g i (A.vacant i) = 1) → (∀ i, 0 ≤ e i) →
    A.HasSmallExcess m G g e →
    ∫⁻ σ, ∏ i, ENNReal.ofReal (g i (σ i)) ∂(A.gibbsLaw m G) ≤ ENNReal.ofReal (∏ i, (1 + e i))
end Dobrushin
end YangMills.Construction
end
