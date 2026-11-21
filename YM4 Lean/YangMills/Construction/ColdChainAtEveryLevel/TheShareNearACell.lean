import YangMills.Construction.ColdChainAtEveryLevel.LocalRestrictionsOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def cellShareIsLocalStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ (c : ℝ) (Ck : ℕ → ℝ), 0 < c ∧ (∀ k, 0 ≤ Ck k) ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ (U : ChainChart F) (Y : F.Cell) (B : Finset (F.Site F.top × Fin 4)),
          (∀ b, b ∈ B ↔ b ∈ innerBonds S F.top ∧ (b.1 = Y ∨ b.1 + unitStep F.top b.2 = Y)) →
          (Y ∈ S → localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y ≤ c) →
            IsLocalRepresentation S (referenceFieldChain S V) Y B Ck U (localCellShare a S (referenceFieldChain S V) V Y) ∧
            |localCellShare a S (referenceFieldChain S V) V Y U fun _ _ => 0| ≤
              Ck 0 * (s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y) ^ 2 ∧
            ∀ (n : ℕ) (A : Fin n → ChainChart F) (e : Fin n → F.Site F.top → Fin 4 → imaginaryQuaternions), n = 1 →
              ‖localIteratedDeriv (localCellShare a S (referenceFieldChain S V) V Y) U A e‖ ≤
                Ck 1 * (s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y) *
                  ∏ l, localDirectionSize S (referenceFieldChain S V) B Y (A l) (e l)
end YangMills.Construction.BlockAverages
end
