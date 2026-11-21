import YangMills.Construction.Continuum.GrowthConditionFromABoundOnSeparatedTuples
import YangMills.Construction.Continuum.TwoFormsOfTheGrowthCondition
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SeparatedPowerBound
open YangMills.Construction.TestSpaces hiding flatSchwartzSet weightedSeminorm
open YangMills.Construction.GrowthSequences YangMills.Construction.GrowthForms
open YangMills.Construction.SmoothSepR4
open YangMills.Construction.SeparatedBound
open YangMills.Construction.ConfigurationSpace (flatSchwartzSet sobolevWeightNorm)
def PowerSepBound (M : ℝ) (a : ℕ) (C k : ℝ) (S : CorrelationFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (d : ℝ), 0 < d → ∀ X : SepTupleOfCard n,
    SupportedSeparated 1 d X →
      |S n hn X| ≤ (C * max 1 (d ^ (-(a : ℤ)))) ^ n * (n.factorial : ℝ) ^ k * sharpNormProd M X
def powerBase (M : ℝ) (a : ℕ) (C : ℝ) : ℝ := 160 * M * extBaseMax ^ (1 + a) * C
structure PowerGrowthConsequences (M : ℝ) (a : ℕ) (C k : ℝ) (S : CorrelationFamily) : Prop where
  existsUnique_extension : ∀ (n : ℕ) (hn : 2 ≤ n), ∃! T, ExtendsToFlat (S n hn) T
  extension_bound : ∀ (n : ℕ) (hn : 2 ≤ n) (T : flatSchwartzSet n → ℂ),
    ExtendsToFlat (S n hn) T → ∀ φ : flatSchwartzSet n,
      ENNReal.ofReal ‖T φ‖ ≤
        ENNReal.ofReal (2 * extFactorAbs * powerBase M a C ^ n * (n.factorial : ℝ) ^ (19 + k)) *
          sobolevWeightNorm ((10 + a) * n) φ.1
  centred_bound : ∀ (n : ℕ), 2 ≤ n → ∀ d : ℝ, 0 < d → ∀ X : SepTupleOfCard n,
    SupportedSeparated 1 d X →
      |centredOfCumulants S ⟨n, X⟩| ≤
        (C * max 1 (d ^ (-(a : ℤ)))) ^ n * (n.factorial : ℝ) ^ (k + 1) * sharpNormProd M X
  existsUnique_centred_extension : ∀ (n : ℕ), 2 ≤ n →
    ∃! T, ExtendsToFlat (fun X : SepTupleOfCard n => centredOfCumulants S ⟨n, X⟩) T
  moment_geomBound : ∀ Q, IsMomentSequence S Q →
    GeomBound Q (10 + a) (2 * extFactorAbs) (powerBase M a C) (20 + k)
  isSchwingerFamily : ∀ Q, IsMomentSequence S Q →
    ∃ T, IsSchwingerFamily (centredOfCumulants S) T ∧ MatchesMembers Q T
  growthBound : ∀ ϰ : ℝ, 20 + k ≤ ϰ →
    YangMills.Construction.TestSpaces.GrowthBound (10 + a) (2 * extFactorAbs) (powerBase M a C) ϰ
      (centredOfCumulants S)
  growthWith : ∀ Q, IsMomentSequence S Q →
    GrowthWith Q (10 + a) (2 * extFactorAbs * max 1 (powerBase M a C))
      (20 + k + YangMills.Construction.Continuum.binaryLog (max 1 (powerBase M a C)))
def GrowthFromPowerSepBound : Prop :=
  ∀ (M : ℝ) (a : ℕ) (C k : ℝ) (S : CorrelationFamily), 1 ≤ M → 0 ≤ C → 0 ≤ k →
    (∀ (n : ℕ) (hn : 2 ≤ n), IsMultilinearOnSep (S n hn)) →
    IsSepFunctional (centredOfCumulants S) →
    PowerSepBound M a C k S →
    PowerGrowthConsequences M a C k S
end YangMills.Construction.SeparatedPowerBound
end
