import YangMills.Construction.Lattice.BlockAveraging
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open YangMills.Construction.Matrices
variable {L m K : ℕ} {i i' : ℤ}
def extendByOne (B : Set (Bond L m i)) (W : Bond L m i → ComplexMatrix2) :
    Bond L m i → ComplexMatrix2 :=
  open Classical in
  fun b => if b ∈ B then W b else 1
theorem extendByOne_mem_compactGaugeFields {B : Set (Bond L m i)}
    {W : Bond L m i → ComplexMatrix2}
    (hB : IsReversalClosed B) (hW : IsGaugeField compactGaugeGroup B W) :
    extendByOne B W ∈ compactGaugeFields L m i := by
  classical
  have hopp : ∀ b : Bond L m i, b.opposite.opposite = b := fun b => Bond.ext rfl rfl
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b ∈ B
    · simpa [extendByOne, hb] using hW.1 b hb
    · simp [extendByOne, hb]
  · by_cases hb : b ∈ B
    · simp [extendByOne, hb, hB b hb, hW.2 b hb]
    · have hb' : b.opposite ∉ B := fun h => hb (by simpa [hopp] using hB _ h)
      simp [extendByOne, hb, hb']
def blockAverageIter (ω : ℝ) (j n : ℕ) :
    (BondAtLevel L m K j → ComplexMatrix2) → BondAtLevel L m K (j + n) → ComplexMatrix2 :=
  iterateFromLevel (blockAverageStep ω) j n
def partialBlockAverage (ω : ℝ) {j : ℕ} (n : ℕ) (B : Set (BondAtLevel L m K j))
    (W : BondAtLevel L m K j → ComplexMatrix2) (c : BondAtLevel L m K (j + n)) :
    ComplexMatrix2 :=
  blockAverageIter ω j n (extendByOne B W) c
def IsSecondAveragingCase (ω : ℝ) (U : Bond L m i' → ComplexMatrix2) (c : Bond L m i) : Prop :=
  ¬IsRegularAveragingCase ω U c ∧
    ∀ x ∈ sitesInBlock i' c.source, ∀ σ σ', contourCrossingDefect U c x σ σ' ≠ -1
def IsThirdAveragingCase (ω : ℝ) (U : Bond L m i' → ComplexMatrix2) (c : Bond L m i) : Prop :=
  ¬IsRegularAveragingCase ω U c ∧ ¬IsSecondAveragingCase ω U c
end PeriodicLattice
end YangMills.Construction
