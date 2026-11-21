import YangMills.Construction.LawInAState.DataOfTheLaw
import YangMills.Construction.LawInAState.FormsDominatedBySites
import YangMills.Construction.LawInAState.TheExponentsOfTheBox
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
def translateSiteBound (n : ℝ) : ℝ := (2 * n + 13) ^ 4
def formFamilyMass (C₂ G n : ℝ) : ℝ := (C₂ ^ 2 * G ^ 4 + C₂ * G ^ 2 + 1) * translateSiteBound n
def boxFlatness (C₂ x : ℝ) : ℝ := C₂ * (boxRadius x : ℝ) ^ (-(2 / 3) : ℝ) * BoxGaussian.boxScale x * Real.log x
def boxMeanCurlBound (C₂ x : ℝ) : ℝ := C₂ * (boxRadius x : ℝ) ^ 2 * BoxGaussian.boxScale x
def farSiteOverlap (T c n : ℝ) : ℝ := T * Real.exp (-(c / 4 * n))
def outsideBoxMass (T c x : ℝ) : ℝ := T * Real.exp (-(c / 4 * ((boxRadius x : ℝ) / 32 - 4)))
def farPairError (C₂ G T c n x : ℝ) : ℝ :=
  C₂ ^ 2 * translateSiteBound n ^ 2 * farSiteOverlap T c n ^ 2 +
    C₂ ^ 2 * farSiteOverlap T c n * translateSiteBound n * G ^ 2 +
    boxMeanCurlBound C₂ x ^ 2 * C₂ ^ 2 * G ^ 2 * translateSiteBound n ^ 2 * farSiteOverlap T c n
def nearTranslateRadius (n : ℝ) : ℕ := ⌈3 * n⌉₊ + 12
def nearPairShare (n x : ℝ) : ℝ :=
  (2 * (nearTranslateRadius n : ℝ) + 1) ^ 4 / (2 * (averagingRadius x : ℝ) + 1) ^ 4
def logWeightBound (C₂ x : ℝ) : ℝ := C₂ * (boxRadius x : ℝ) ^ 9 * x ^ (-(1 / 2) : ℝ) * Real.log x ^ 3
def weightExcess (C₂ x : ℝ) : ℝ := 8 * logWeightBound C₂ x + 8 * Real.exp (-((boxRadius x : ℝ) ^ 4))
def marksRemainder (C₂ c n x : ℝ) : ℝ :=
  C₂ * n ^ 4 * (boxRadius x : ℝ) ^ 8 * BoxGaussian.boxScale x ^ 3 + Real.exp (-(c * (boxRadius x : ℝ)))
def boxSizesStatement : Prop :=
  ∀ (C₂ c G T Λ Cm : ℝ) (R₀ : ℕ), 1 ≤ C₂ → 0 < c → 1 ≤ G → 0 ≤ T → 1 ≤ Λ → 0 ≤ Cm →
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x n : ℝ, x₀ ≤ x →
    2 ^ 12 * (TorusLumps.clusterRange x : ℝ) ≤ n → n ≤ 2 ^ 13 * Λ * (TorusLumps.clusterRange x : ℝ) →
      QuadraticConcentration.BoxSizes Cm x (C₂ / x) (formFamilyMass C₂ G n) (2 * boxFlatness C₂ x)
        (farPairError C₂ G T c n x) (nearPairShare n x) (weightExcess C₂ x) (marksRemainder C₂ c n x)
        (x ^ Cm) (x ^ (-(32 * (2 * Cm + 4)) : ℝ)) ∧
      R₀ ≤ boxRadius x ∧ 16 ≤ averagingRadius x ∧ 1 ≤ Real.log x ∧
      x ^ (-(32 * (2 * Cm + 4)) : ℝ) ≤ 1 / 2 ∧
      Real.exp (2 * logWeightBound C₂ x) ≤
        (1 + weightExcess C₂ x) * (1 - Real.exp (-((boxRadius x : ℝ) ^ 4))) ∧
      0 < 1 - Real.exp (-((boxRadius x : ℝ) ^ 4)) ∧
      C₂ * G ^ 2 * QuadraticConcentration.vectorMass C₂ G (translateSiteBound n) (outsideBoxMass T c x)
          (boxFlatness C₂ x) (boxMeanCurlBound C₂ x) ≤
        formFamilyMass C₂ G n * (2 * boxFlatness C₂ x) ^ 2 ∧
      QuadraticConcentration.vectorMass C₂ G (translateSiteBound n) (outsideBoxMass T c x)
          (boxFlatness C₂ x) (boxMeanCurlBound C₂ x) ≤
        formFamilyMass C₂ G n * (2 * boxFlatness C₂ x) ^ 2
end YangMills.Construction.StateLaws
end
