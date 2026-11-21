import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ChainNoise
def translatedCopiesBoundStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (β : ℝ) (u n M : ℕ) [NeZero n] (g : ChessboardGrids.MirrorGrid),
    Odd ℓ.side → 2 ^ 16 ≤ ℓ.side → 0 < β → n = 2 * ℓ.side ^ M →
    ChessboardGrids.IsGridOfTorus g ℓ.side M → 2 * g.side ≤ n →
    ∀ (c₀ : Fin 4 → ℕ)
      (Φ : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n → ℝ),
      c₀ ∈ g.cellIndices n → ChainNoise.IsCellObservable ℓ g u n c₀ Φ →
      (g.atDepth ℓ.side u).chessboardNormAt β (WeightedResponses.fineSide ℓ.side u n) c₀
          (ChainNoise.noiseExpectation ℓ u n Φ) ^ ChessboardGrids.numCells n g.side ≤
        ChainNoise.pairExpectation ℓ β u n fun p => ∏ e ∈ g.evenTranslations n,
          Φ (ChainNoise.pairTranslate ℓ u n (fun i => 2 * (g.side : ℤ) * (e i : ℤ)) p) ^ 16
end YangMills.Construction.ChainNoise
end
