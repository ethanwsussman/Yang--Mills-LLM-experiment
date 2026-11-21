import YangMills.Construction.ColdChainAtEveryLevel.LevelRecursionNearACell
import YangMills.Construction.ColdChainAtEveryLevel.LogarithmsOfTheCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
def bondAngleAndAverageNormStatement : Prop :=
  ∃ L0 : ℕ, ∀ L : ℕ, Odd L → L0 ≤ L → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ (U : ChainChart F) (j : ℕ) (b : F.Site (j + 1) × Fin 4), j < F.top → b ∈ innerBonds S (j + 1) →
          ∀ t : ℝ, 0 ≤ t → t ≤ c →
            BoundedOnAdjacentBlocks (fun x i => ‖levelCoordinate (referenceFieldChain S V) U j x i‖) b t →
            ‖bondAngle (referenceFieldChain S V) U j b -
                parallelAverage (referenceFieldChain S V j) (levelCoordinate (referenceFieldChain S V) U j) b‖ ≤
              C * (t ^ 2 + s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 * t) ∧
            0 ≤ 1 - ‖gaugedBondAverage (referenceFieldChain S V) U j b‖ ∧
            1 - ‖gaugedBondAverage (referenceFieldChain S V) U j b‖ ≤
              C * (t ^ 2 + s ^ 2 * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 4)
end BlockAverages
end YangMills.Construction
end
