import YangMills.Construction.LimitsOfLatticeFamilies.TranslationModulusInTheSharpNorm
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
def C1CompactSuppIsLipschitz : Prop :=
  (∀ (s : Conventions.StandingParameters) (Y : ModelSpace),
    (∀ f : c1CompactSupp s Y univ, gradSup f < ⊤ ∧
      (∀ x y, |f.1 x - f.1 y| ≤ (gradSup f).toReal * ModelSpace.dist s Y x y) ∧
      IsLipschitzReal s Y f.1 ∧
      lipNumber s Y f.1 ≤ (gradSup f).toReal) ∧
    ∀ A : Set (Y.Carrier s), c1CompactSupp s Y A ⊆ lipCompactSupp s Y A) ∧
  ∀ s : Conventions.StandingParameters,
    (∀ f : torus.Carrier s → ℝ, IsCompactIn s torus (supportIn s torus f)) ∧
    ∀ f : torus.Carrier s → ℝ, IsC1 s torus f → f ∈ c1CompactSupp s torus univ
end YangMills.Construction.LatticeLimits
end
