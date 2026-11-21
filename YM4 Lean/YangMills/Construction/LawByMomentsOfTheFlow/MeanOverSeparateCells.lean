import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def separateCellsExpectationStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (β : ℝ) (u n M : ℕ) [NeZero n] (g : ChessboardGrids.MirrorGrid),
    Odd ℓ.side → 2 ^ 16 ≤ ℓ.side → 0 < β → n = 2 * ℓ.side ^ M → 2 ≤ M + u →
    ChessboardGrids.IsGridOfTorus g ℓ.side M → ∀ {ι : Type} (I : Finset ι) (c : ι → Fin 4 → ℕ)
      (Φ : ι → TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n → ℝ),
      (∀ i ∈ I, c i ∈ g.cellIndices n) → Set.InjOn c I →
      (∀ i ∈ I, ChainNoise.IsCellObservable ℓ g u n (c i) (Φ i)) →
      ChainNoise.pairExpectation ℓ β u n (fun p => ∏ i ∈ I, Φ i p) ≤
        ∏ i ∈ I, (g.atDepth ℓ.side u).chessboardNormAt β (WeightedResponses.fineSide ℓ.side u n) (c i)
          (ChainNoise.noiseExpectation ℓ u n (Φ i))
end YangMills.Construction.MomentLaw
end
