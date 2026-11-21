import YangMills.Construction.ColdChainAtEveryLevel.CoordinatesAtTheLevels
import YangMills.Construction.ColdChainAtEveryLevel.PairsAtOffsets
import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open Offsets
def localNormSqOnBallsAcrossFramesStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (F F' : BlockFrame) (m : ℕ) (S : Finset F.Cell) (S' : Finset F'.Cell) (s : ℝ)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r ρ : ℕ),
    F'.blockSide = F.blockSide → F'.depth = F.depth → Odd F.blockSide → IsAdmissibleAmbient F →
    IsAdmissibleAmbient F' → 1024 ≤ m → IsOrthantRegular S m → IsOrthantRegular S' m → 0 < s → s ≤ c →
    IsCold S F.top s V → IsCold S' F'.top s V' → AgreeOnBall S V S' V' Y Y' r → ρ + 100 ≤ r →
    ∀ (A : ChainChart F) (A' : ChainChart F'), ChartsAgreeAtOffsets Y Y' ρ A A' →
      ∀ g : Fin 4 → ℤ, (∀ i, |g i| + 5 ≤ (ρ : ℤ)) →
        localNormSq S (cellBall S (Y + siteOfCoords F.top g) 4) (referenceFieldChain S V) A (constOneWeights F) =
          localNormSq S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) (referenceFieldChain S' V') A'
            (constOneWeights F')
end YangMills.Construction.BlockAverages
end
