import YangMills.Construction.HoleBesideASecondHole.TermsOfAChainAtACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.CellTerms
open BlockAverages
def nonzeroAveragesStatement : Prop :=
  ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ δ : ℝ, 0 < δ → ∃ cL : ℝ, 0 < cL ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (r : ℝ) (V : F.GaugeField F.top), 0 < r → r ≤ cL → IsCold S F.top r V →
        ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ cL →
          ∀ C : Finset F.Cell, C ⊆ S → HasNonzeroAveragesOn C (referenceFieldChain S V) U
end YangMills.Construction.CellTerms
end
