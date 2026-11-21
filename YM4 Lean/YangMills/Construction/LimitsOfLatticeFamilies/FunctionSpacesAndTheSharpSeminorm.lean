import YangMills.Construction.LimitsOfLatticeFamilies.TranslationModulusInTheSharpNorm
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LatticeLimits.SharpSeminorm
open ModelSpace
def Properties : Prop :=
  ∀ (s : Conventions.StandingParameters) (M : BlockScale s) (Y : ModelSpace),
    (∀ A : Set (Y.Carrier s),
      ∃ W : Submodule ℝ (Y.Carrier s → ℝ), (W : Set _) = lipCompactSupp s Y A) ∧
    (∀ A : Set (Y.Carrier s), ∃ W : Submodule ℝ (Y.Carrier s → ℝ), (W : Set _) = c1CompactSupp s Y A) ∧
    (∀ g ∈ lipCompactSupp s Y univ, TestFunctions.IsBoundedFun g ∧ IsLipschitzReal s Y g) ∧
    (∀ g ∈ lipCompactSupp s Y univ, 0 ≤ sharpNorm s M Y g) ∧
    (∀ (c : ℝ), ∀ g ∈ lipCompactSupp s Y univ, sharpNorm s M Y (c • g) = |c| * sharpNorm s M Y g) ∧
    ∀ g ∈ lipCompactSupp s Y univ, ∀ g' ∈ lipCompactSupp s Y univ,
      sharpNorm s M Y (g + g') ≤ sharpNorm s M Y g + sharpNorm s M Y g'
end YangMills.Construction.LatticeLimits.SharpSeminorm
end
