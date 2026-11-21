import YangMills.Construction.LimitsOfLatticeFamilies.IsometriesTranslationsAndEnlargedSupports
import YangMills.Construction.LimitsOfLatticeFamilies.TranslationModulusInTheSharpNorm
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits.CutoffAndSymmetry
open ModelSpace
variable (s : Conventions.StandingParameters) (M : BlockScale s) (Y : ModelSpace)
def CutoffBound : Prop :=
  ∀ (A : Set (Y.Carrier s)) (g χ : Y.Carrier s → ℝ), g ∈ c1CompactSupp s Y A →
    χ ∈ c1CompactSupp s Y univ → (∀ y, χ y ∈ Icc (0 : ℝ) 1) →
      (fun y => χ y * g y) ∈ c1CompactSupp s Y (A ∩ supportIn s Y χ) ∧
        sharpNorm s M Y (fun y => χ y * g y) ≤
          (1 + 40 * (M.1 : ℝ) * lipNumber s Y χ) * sharpNorm s M Y g
def IsometryInvariance : Prop :=
  ∀ r : SpaceIsometry s Y,
    (∃ r' : SpaceIsometry s Y, r'.toEquiv = r.toEquiv.symm) ∧
      (∀ g ∈ c1CompactSupp s Y univ,
        r.pushFun g ∈ c1CompactSupp s Y univ ∧
          supportIn s Y (r.pushFun g) = r.toEquiv '' supportIn s Y g) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ f ∈ sepTuples s Y n, r.pushTuple f ∈ sepTuples s Y n
variable {s Y}
def ModulusVanishesAtZero (f : c1CompactSupp s Y univ) : Prop :=
  (∀ δ : ℝ≥0, gradOscillation f δ ≤ 2 * gradSup f ∧ sharpTranslationModulus M f δ < ⊤) ∧
    Tendsto (sharpTranslationModulus M f) (𝓝 0) (𝓝 0)
def Assertions : Prop :=
  ∀ (s : Conventions.StandingParameters) (M : BlockScale s) (Y : ModelSpace),
    CutoffBound s M Y ∧ IsometryInvariance s Y ∧ ∀ f : c1CompactSupp s Y univ, ModulusVanishesAtZero M f
end YangMills.Construction.LatticeLimits.CutoffAndSymmetry
end
