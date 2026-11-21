import YangMills.Construction.Cumulants.NumberOfBlocksAndImagesOfPartitions
import YangMills.Construction.Cumulants.PartitionsMomentsAndTheCentredFunctionalOfAFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TestSpaces
open SetPartition
variable {n : ℕ}
def CumulantRestrictFormula (σ : SepTuple → ℝ) (X : SepTupleOfCard n)
    (J : Finset (Fin n)) : Prop :=
  cumulant σ (sepRestrict X J) = ∑ ρ : Partitions J,
    (-1 : ℝ) ^ (blockCount ρ - 1) * ((blockCount ρ - 1).factorial : ℝ) *
      ∏ C ∈ ρ.parts, σ ⟨C.card, sepRestrict X C⟩
def CentredRestrictFormula (S : (p : ℕ) → 2 ≤ p → SepTupleOfCard p → ℝ)
    (X : SepTupleOfCard n) (J : Finset (Fin n)) : Prop :=
  centredOfCumulants S ⟨J.card, sepRestrict X J⟩ =
    ∑ ρ ∈ (atLeastTwoPartitions J).attach, ∏ C ∈ ρ.1.parts.attach,
      S C.1.card (two_le_card_of_mem_atLeastTwoPartitions ρ.2 C.2) (sepRestrict X C.1)
def signedPartitionSum {α : Type} [DecidableEq α] (E : Finset α) : ℝ :=
  ∑ ϖ : Partitions E, ∏ W ∈ ϖ.parts,
    (-1 : ℝ) ^ (W.card - 1) * ((W.card - 1).factorial : ℝ)
def MomentCumulantInversion (σ : SepTuple → ℝ) (X : SepTupleOfCard n) : Prop :=
  σ ⟨n, X⟩ = ∑ η : Partitions (Finset.univ : Finset (Fin n)),
    ∏ J ∈ η.parts, cumulant σ (sepRestrict X J)
def CumulantMultilinearInversion : Prop :=
  (∀ σ : SepTuple → ℝ, IsSepFunctional σ →
    ∀ S : (p : ℕ) → 2 ≤ p → SepTupleOfCard p → ℝ,
      (∀ n, 1 ≤ n → ∀ (X : SepTupleOfCard n) (J : Finset (Fin n)),
        (J.Nonempty → CumulantRestrictFormula σ X J) ∧
          CentredRestrictFormula S X J) ∧
      (∀ n, 1 ≤ n → IsMultilinearOnSep fun X : SepTupleOfCard n => cumulant σ X) ∧
      ((∀ p (hp : 2 ≤ p), IsMultilinearOnSep (S p hp)) → IsSepFunctional (centredOfCumulants S)) ∧
      IsSepFunctional (centredPart σ) ∧
      ∀ n, 1 ≤ n → ∀ X : SepTupleOfCard n, MomentCumulantInversion σ X) ∧
  ∀ (α : Type) [DecidableEq α] (E : Finset α),
    (E.card = 1 → signedPartitionSum E = 1) ∧ (2 ≤ E.card → signedPartitionSum E = 0)
end YangMills.Construction.TestSpaces
