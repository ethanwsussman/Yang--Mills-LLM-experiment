import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.LocalTermsOfAMeasureForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def PushforwardFieldProperties : Prop :=
  ∀ (κ ι : Type) [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] (j : κ → ι), Function.Injective j →
    (∀ ξ ζ : BondField κ, pushforwardField j (ξ + ζ) = pushforwardField j ξ + pushforwardField j ζ) ∧
    (∀ (v : ℝ) (ξ : BondField κ), pushforwardField j (v • ξ) = v • pushforwardField j ξ) ∧
    (∀ (k : κ) (e : BondVector), pushforwardField j (bondVariation k e) = bondVariation (j k) e) ∧
    (∀ (ξ : BondField κ) (k : κ), pushforwardField j ξ (j k) = ξ k) ∧
    (∀ (ξ : BondField κ) (b : ι), (∀ k, j k ≠ b) → pushforwardField j ξ b = 0) ∧
    Continuous (pushforwardField (ι := ι) j) ∧
    ∀ (n : WithTop ℕ∞) (f : BondField ι → ℝ) (ξ : BondField κ), ContDiffAt ℝ n f (pushforwardField j ξ) →
      ContDiffAt ℝ n (fun z => f (pushforwardField j z)) ξ ∧
      (1 ≤ n → ∀ u : BondField κ, fderiv ℝ (fun z => f (pushforwardField j z)) ξ u =
        fderiv ℝ f (pushforwardField j ξ) (pushforwardField j u)) ∧
      (2 ≤ n → ∀ u v : BondField κ, secondDerivAlong (fun z => f (pushforwardField j z)) ξ u v =
        secondDerivAlong f (pushforwardField j ξ) (pushforwardField j u) (pushforwardField j v)) ∧
      (3 ≤ n → ∀ u v z : BondField κ, thirdDerivAlong (fun z => f (pushforwardField j z)) ξ u v z =
        thirdDerivAlong f (pushforwardField j ξ) (pushforwardField j u) (pushforwardField j v) (pushforwardField j z))
end YangMills.Construction.ColdStepAtMirrorFrames
end
