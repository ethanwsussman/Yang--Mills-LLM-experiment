import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldOfCopies
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentMethod
def jointLimitPropertiesStatement : Prop :=
  ∀ (T : TranslatedLaws) (J : Type) [Countable J] (X : J → T.Family) (P : Measure (TranslateValues J)), T.IsPreserving →
    (∀ j, TranslatedLaws.HasBoundedMoments (X j)) → IsJointLimitLaw T X P →
    MeasurePreserving (translateShift (J := J)) P P ∧
    (∀ (l : ℕ) (a : Fin l → J × ℕ), Integrable (fun v : TranslateValues J => ∏ c, v (a c)) P ∧
      Tendsto (fun i => ∫ ω, ∏ c, TranslatedLaws.translate (X (a c).1) (a c).2 i ω ∂(T.μ i)) atTop
        (𝓝 (∫ v, ∏ c, v (a c) ∂P))) ∧
    (∀ (l : ℕ) (a : Fin l → J × ℕ) (G : (Fin l → ℝ) → ℝ), Continuous G →
      (∀ᶠ i in atTop, ∀ ω, G (fun c => TranslatedLaws.translate (X (a c).1) (a c).2 i ω) = 0) →
      ∀ᵐ v ∂P, G (fun c => v (a c)) = 0) ∧
    (∀ j, Tendsto (fun M : ℕ => eLpNorm (fun v : TranslateValues J =>
        (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, k) - invariantCondExp P (evalAtZero j) v) 2 P) atTop (𝓝 0)) ∧
    (∀ j, Tendsto (fun k : ℕ => ∫ v, v (j, 0) * v (j, k) ∂P) atTop (𝓝 0) → invariantCondExp P (evalAtZero j) =ᵐ[P] 0) ∧
    ∀ (j : J) (b C₀ Cb : ℝ), 0 ≤ b → (∀ᵐ v ∂P, 0 ≤ v (j, 0) ∧ v (j, 0) ≤ Cb) →
      (∀ q : ℕ, 1 ≤ q → ∃ gap : ℕ, ∀ k : Fin q → ℕ, (∀ c e, c ≠ e → gap ≤ k c - k e ∨ gap ≤ k e - k c) →
        ∫ v, ∏ c, v (j, k c) ∂P ≤ C₀ * b ^ q) →
      ∀ᵐ v ∂P, invariantCondExp P (evalAtZero j) v ≤ b
end YangMills.Construction.MomentMethod
end
