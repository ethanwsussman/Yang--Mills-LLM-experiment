import YangMills.Construction.HoleBesideASecondHole.TermsOfAChainAtACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace CellTerms
open BlockAverages
def smallCellTermsStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ Ca : ℝ, 0 < Ca ∧ ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ δ : ℝ, 0 < δ →
    ∃ cL : ℝ, 0 < cL ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (r : ℝ) (V : F.GaugeField F.top), 0 < r → r ≤ cL → IsCold S F.top r V →
        ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ cL →
          ∀ (β : ℝ) (z : F.Cell), z ∈ S → 0 ≤ β →
            (∀ y ∈ BlockAverages.cellBall S z 5, unweightedLocalNorm S (referenceFieldChain S V) U y ≤ β) →
            chartCellTerms a S (referenceFieldChain S V) U V z ≤ Ca * (r + β) ^ 2
end CellTerms
end YangMills.Construction
end
