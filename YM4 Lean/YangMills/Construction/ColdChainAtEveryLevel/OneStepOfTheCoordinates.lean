import YangMills.Construction.ColdChainAtEveryLevel.LevelRecursionNearACell
import YangMills.Construction.ColdChainAtEveryLevel.LogarithmsOfTheCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
def levelCoordinateStepStatement : Prop :=
  ∃ L0 : ℕ, ∀ L : ℕ, Odd L → L0 ≤ L → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ (U : ChainChart F) (j : ℕ) (b : F.Site (j + 1) × Fin 4), j + 1 < F.top →
          b ∈ innerBonds S (j + 1) →
          ∀ t : ℝ, 0 ≤ t → t ≤ c → ‖(U.coarse j b.1 b.2 : ℍ[ℝ])‖ ≤ c →
            BoundedOnAdjacentBlocks (fun x i => ‖levelCoordinate (referenceFieldChain S V) U j x i‖) b t →
            ‖levelCoordinate (referenceFieldChain S V) U (j + 1) b.1 b.2 -
                ((U.coarse j b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) -
                parallelAverage (referenceFieldChain S V j) (levelCoordinate (referenceFieldChain S V) U j) b‖ ≤
              C * (t ^ 2 + (s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 +
                ‖(U.coarse j b.1 b.2 : ℍ[ℝ])‖ +
                ‖((referenceDefect (referenceFieldChain S V) j b : UnitQuaternion) : ℍ[ℝ]) - 1‖) * t)
end BlockAverages
end YangMills.Construction
end
