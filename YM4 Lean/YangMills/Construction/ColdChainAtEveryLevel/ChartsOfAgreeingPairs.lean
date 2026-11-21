import YangMills.Construction.ColdChainAtEveryLevel.ComparedCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.CoordinatesAtTheLevels
import YangMills.Construction.ColdChainAtEveryLevel.TheChartIsLocal
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def agreeingChartsComparedStatement : Prop :=
  ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ (c : ℝ) (r₀ : ℕ) (Cm : ℕ → ℝ), 0 < c ∧ (∀ k, 0 ≤ Cm k) ∧
    ∀ (F F' : BlockFrame) (m : ℕ) (S : Finset F.Cell) (S' : Finset F'.Cell), F.blockSide = L →
      F'.blockSide = L → F'.depth = F.depth →
      IsAdmissibleAmbient F → IsAdmissibleAmbient F' → 1024 ≤ m → IsOrthantRegular S m →
      IsOrthantRegular S' m →
      ∀ (s : ℝ) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
        0 < s → s ≤ c →
        IsCold S F.top s V → IsCold S' F'.top s V' → r₀ ≤ r → AgreeOnBall S V S' V' Y Y' r →
        ∀ (U : ChainChart F) (U' : ChainChart F'),
          (∀ z ∈ S, localNorm S (referenceFieldChain S V) U (constOneWeights F) z ≤ c) →
          (∀ z ∈ S', localNorm S' (referenceFieldChain S' V') U' (constOneWeights F') z ≤ c) →
          ∀ b ∈ chordBonds S, enclosingCell b.1 = Y →
            (depthSiteAtSameOffset Y Y' b.1, b.2) ∈ chordBonds S' ∧
            AreComparedRepresentations S (referenceFieldChain S V) Y Y' (topBondsAt b) Cm U U'
              (bondChartCoord (referenceFieldChain S V) V b)
              (bondChartCoord (referenceFieldChain S' V') V' (depthSiteAtSameOffset Y Y' b.1, b.2))
end YangMills.Construction.BlockAverages
end
