import YangMills.Construction.ColdChainAtEveryLevel.LogarithmsOfTheCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
def levelCoordinateQuarticStatement : Prop :=
  ∃ (C : ℝ) (L0 : ℕ), 0 < C ∧ ∀ L : ℕ, Odd L → L0 ≤ L → ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c →
          ∀ j, j < F.top → ∀ z ∈ S,
            Real.sqrt (Real.sqrt (∑ b ∈ bondsOver S {z} j,
                ‖levelCoordinate (referenceFieldChain S V) U j b.1 b.2‖ ^ 4)) ≤
              C * localNorm S (referenceFieldChain S V) U (constOneWeights F) z
end BlockAverages
end YangMills.Construction
end
