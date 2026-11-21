import YangMills.Construction.Continuum.FlatFunctionsTensorsOfSubTuplesAndSmoothTuples
import YangMills.Construction.Continuum.PointsDerivativesDiagonalsAndTheGradientSupremum
import YangMills.Construction.Continuum.SchwartzFunctionsAndTheirTwoFamiliesOfSeminorms
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.Continuum.UnifiedTestSpace
def idxByArg (n : ℕ) :
    YangMills.Construction.ConfigGradients.Idx n ≃ YangMills.Construction.TestSpaces.MultiIdx4 n where
  toFun α i c := α (toLex (i, c))
  invFun β ι := β (ofLex ι).1 (ofLex ι).2
  left_inv _ := rfl
  right_inv _ := rfl
def GradientSignsAgree (n : ℕ) : Prop :=
  (∀ x : YangMills.Construction.ConfigGradients.Pt n,
    YangMills.Construction.ConfigGradients.ptNorm x = YangMills.Construction.TestSpaces.tupleNorm x) ∧
  YangMills.Construction.ConfigGradients.smoothFns n = {φ | ContDiff ℝ ∞ φ} ∧
  (∀ α : YangMills.Construction.ConfigGradients.Idx n,
    YangMills.Construction.TestSpaces.idxOrder (idxByArg n α) =
      YangMills.Construction.ConfigGradients.idxDegree α) ∧
  (∀ (α : YangMills.Construction.ConfigGradients.Idx n),
    ∀ φ ∈ YangMills.Construction.ConfigGradients.smoothFns n,
      YangMills.Construction.ConfigGradients.partialD α φ =
        YangMills.Construction.TestSpaces.multiDeriv (idxByArg n α) φ) ∧
  YangMills.Construction.ConfigGradients.diagLocus n = YangMills.Construction.TestSpaces.diagonalLocus n
def SchwartzSpacesAgree (n : ℕ) : Prop :=
  (∀ φ ∈ YangMills.Construction.ConfigGradients.smoothFns n,
    (φ ∈ YangMills.Construction.SchwartzSeminorms.schwartzSpace n ↔
      φ ∈ YangMills.Construction.TestSpaces.schwartzSet n)) ∧
  (∀ (φ : YangMills.Construction.SchwartzSeminorms.schwartzSpace n) (k : ℕ), 0 < k →
    YangMills.Construction.TestSpaces.weightedSeminorm k φ.1 =
      YangMills.Construction.SchwartzSeminorms.weightNorm k φ) ∧
  YangMills.Construction.FlatTensors.flatSchwartz n = YangMills.Construction.TestSpaces.flatSchwartzSet n
def SmoothTupleTensorsFlat (s : YangMills.Construction.Conventions.StandingParameters) (n : ℕ) : Prop :=
  YangMills.Construction.FlatTensors.smoothSepTuples s n =
    {f | f ∈ YangMills.Construction.AmbientPoints.separatedTuples s .euclidean n ∧
      YangMills.Construction.TestSpaces.HasSmoothComponents Set.univ f} ∧
  ∀ f ∈ YangMills.Construction.FlatTensors.smoothSepTuples s n,
    YangMills.Construction.FlatTensors.pointTensor (YangMills.Construction.FlatTensors.toComplexTuple f) ∈
      YangMills.Construction.FlatTensors.flatSchwartz n ∧
    ∀ x, YangMills.Construction.FlatTensors.pointTensor (YangMills.Construction.FlatTensors.toComplexTuple f) x =
      ((YangMills.Construction.FlatTensors.pointTensor (R := ℝ) f x : ℝ) : ℂ)
def DualCharacterizedBySeminorms (n : ℕ) : Prop :=
  ∀ S : YangMills.Construction.FlatTensors.flatSchwartz n → ℂ,
    YangMills.Construction.ConfigurationSpace.IsLinearOnFlatSchwartz S →
      (S ∈ YangMills.Construction.FlatTensors.flatSchwartzDual n ↔
        ∃ (k : ℕ) (c : ℝ), 0 < k ∧ 0 ≤ c ∧ ∀ φ : YangMills.Construction.FlatTensors.flatSchwartz n,
          ENNReal.ofReal ‖S φ‖ ≤
            ENNReal.ofReal c * YangMills.Construction.ConfigurationSpace.sobolevWeightNorm k φ.1)
def TestSpacesUnified : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (GradientSignsAgree n ∧ SchwartzSpacesAgree n) ∧
      (∀ s : YangMills.Construction.Conventions.StandingParameters, SmoothTupleTensorsFlat s n) ∧
      DualCharacterizedBySeminorms n
end YangMills.Construction.Continuum.UnifiedTestSpace
end
