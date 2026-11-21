import YangMills.Construction.ResponseInTheExpansion.MeansOfTheSmoothMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.FamilyNorms
namespace YangMills.Construction
namespace WeightedResponses
def ScoreRemainderDecayAt (P : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (i : Fin 4) (reversed : Bool), P.coupling ≤ x →
    (∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions),
      IsCubicTopTorus P.L t P.n₀ F → IsSmallCurvature (5 / 4 * P.σ) V → 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      ContDiffThreeAlongBonds ((coldHalfLawAt P x f).scoreRemainderAt (cellBond Y i reversed) 0) V ∧
      |bondDeriv ((coldHalfLawAt P x f).scoreRemainderAt (cellBond Y i reversed) 0) V c X| ≤
        P.Cs * Real.exp (-(2 ^ 8 * P.κ * bondSpan Y c))) ∧
    ∀ (F F' : BlockFrame) (Y : F.Cell) (Y' : F'.Cell) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
      (q k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
      IsCubicTopTorus P.L t P.n₀ F →
      IsCubicTopTorus P.L t P.n₀ F' → IsSmallCurvature (5 / 4 * P.σ) V → IsSmallCurvature (5 / 4 * P.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → k ≤ 2 → (∀ l, BondWithinRadius q (b l)) →
      AreUnitVectors X →
      |bondDeriv ((coldHalfLawAt P x f).scoreRemainderAt (cellBond Y i reversed) 0) V (bondsAt Y b) X -
          bondDeriv ((coldHalfLawAt P x f).scoreRemainderAt (cellBond Y' i reversed) 0) V' (bondsAt Y' b) X| ≤
        P.Cs * Real.exp (-(2 ^ 8 * P.κ * q))
def ScoreRemainderDecay : Prop := EventuallyInParameters ScoreRemainderDecayAt
end WeightedResponses
end YangMills.Construction
end
