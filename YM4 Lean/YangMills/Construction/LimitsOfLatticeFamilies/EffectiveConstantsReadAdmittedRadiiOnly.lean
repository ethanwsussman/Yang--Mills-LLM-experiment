import YangMills.Construction.LimitsOfLatticeFamilies.ReferenceRadiusPriceAndEffectiveConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
def EffConstReadsAdmissibleRadii : Prop :=
  (∀ (s : Conventions.StandingParameters) (M : {M : ℕ // IsBlockScale s M}) (Y : ModelSpace),
    refRadius s Y ∈ admissibleRadii s Y ∧ 1 ≤ costFactor M.1 Y ∧
    ∀ (C : SeparationBound) (n : ℕ), 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R →
      (flatRadius s Y R ∈ admissibleRadii s Y ∧ 0 ≤ effConst s Y M.1 C n d R ∧
        (R ∈ admissibleRadii s Y →
          effConst s Y M.1 C n d R = C.val n d (flatRadius s Y R)) ∧
        (R ∉ admissibleRadii s Y →
          effConst s Y M.1 C n d R =
            costFactor M.1 Y ^ n * C.val n d (flatRadius s Y R)) ∧
        (Y = euclidean →
          flatRadius s Y R = R ∧ effConst s Y M.1 C n d R = C.val n d R)) ∧
      ∀ r ∈ admissibleRadii s Y, ∀ Θ : ℝ, 1 ≤ Θ →
        flatRadiusOf s Y r R ∈ admissibleRadii s Y ∧
        0 ≤ effConstOf s Y r Θ C n d R ∧
        (R ∈ admissibleRadii s Y →
          effConstOf s Y r Θ C n d R = C.val n d (flatRadiusOf s Y r R)) ∧
        (R ∉ admissibleRadii s Y →
          effConstOf s Y r Θ C n d R =
            Θ ^ n * C.val n d (flatRadiusOf s Y r R)) ∧
        (Y = euclidean →
          flatRadiusOf s Y r R = R ∧ effConstOf s Y r Θ C n d R = C.val n d R)) ∧
  ∀ M : ℕ, costFactor M torus = 16 ^ 4 * (1 + 320 * Real.pi * M)
end YangMills.Construction.LatticeLimits
end
