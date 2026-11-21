import YangMills.Construction.Continuum.LinearCombinationsOfAdmissibleSequences
import YangMills.Construction.Continuum.TensorOfATupleAndTheSequenceOfACombination
import Mathlib
noncomputable section
namespace YangMills.Construction.ConfigSpace
namespace UpperCombination
variable {ι : Type} [Fintype ι]
def linComb (c : ι → ℂ) (X : ι → UpperFamily) : UpperCombination :=
  ∑ i, c i • ofFamily (X i)
def lengthPart (c : ι → ℂ) (X : ι → UpperFamily) (q : ℕ) : FnOrScalar q :=
  ofConfigFn fun x =>
    ∑ i : {i // familyLength (X i).toSeparatedFamily = q},
      c i * toConfigFn (familyTensor (X i).toSeparatedFamily) fun j => x (Fin.cast i.2 j)
end UpperCombination
def CombinationSequenceAdmissibleLinear : Prop :=
  (∀ (ι : Type) [Fintype ι] (c : ι → ℂ) (X : ι → UpperFamily),
    (∀ i, AllSmoothCompact (X i).2.1) →
      UpperCombination.HasSmoothFamilies (UpperCombination.linComb c X)) ∧
  (∀ F : UpperCombination, UpperCombination.HasSmoothFamilies F →
    (∀ (ι : Type) [Fintype ι] (c : ι → ℂ) (X : ι → UpperFamily),
      (∀ i, AllSmoothCompact (X i).2.1) → F = UpperCombination.linComb c X →
        ∀ q : ℕ, combinationSequence F q = UpperCombination.lengthPart c X q) ∧
    ∃ h : ∀ q : ℕ, combinationSequence F q ∈ flatOffPosTimeAt q,
      PosTimeSeq.IsFinitelySupported fun q => ⟨combinationSequence F q, h q⟩) ∧
  (∃ W : Submodule ℂ UpperCombination,
    (W : Set UpperCombination) = {F | UpperCombination.HasSmoothFamilies F}) ∧
  (∀ (a a' : ℂ) (F F' : UpperCombination), UpperCombination.HasSmoothFamilies F →
    UpperCombination.HasSmoothFamilies F' →
    ∀ q : ℕ, combinationSequence (a • F + a' • F') q =
      linCombAt a a' (combinationSequence F q) (combinationSequence F' q)) ∧
  UpperCombination.HasSmoothFamilies (UpperCombination.ofFamily UpperFamily.nil) ∧
  combinationSequence (UpperCombination.ofFamily UpperFamily.nil) 0 = (1 : ℂ) ∧
  ∀ q : ℕ, 1 ≤ q → combinationSequence (UpperCombination.ofFamily UpperFamily.nil) q = zeroOfDegree q
end YangMills.Construction.ConfigSpace
end
