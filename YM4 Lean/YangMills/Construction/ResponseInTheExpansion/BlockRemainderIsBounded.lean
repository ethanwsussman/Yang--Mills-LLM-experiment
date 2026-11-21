import YangMills.Construction.ResponseInTheExpansion.BlockRemainderAboveTheFrame
import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
def BlockSumDerivBoundAt (T : StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x e : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsAdmissibleAt T t x f F V → 0 < e → IsTorusRemainder T.L T.σ T.decayRate e (e / T.η₃) r →
    InClosedBallProduct T.ballRadius η → 1 ≤ k → k ≤ 3 → AreUnitVectors X →
    |bondDeriv ((coldHalfLawAt T x f).blockSum r Y η) V c X| ≤
      C * (e / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y c)
def BlockSumNearValueAt (T : StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x e : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell)
    (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsAdmissibleAt T t x f F V → IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → 0 < e →
    IsTorusRemainder T.L T.σ T.decayRate e (e / T.η₃) r → k ≤ 2 → AreUnitVectors X →
    |(coldHalfLawAt T x f).expectation V (fun η => bondDeriv ((coldHalfLawAt T x f).blockSum r Y η) V c X) -
        bondDeriv ((coldHalfLawAt T x f).blockSum r Y 0) V c X| ≤ C * (e / T.η₃) * x ^ (-(1 / 2) : ℝ)
def blockSumBoundStatement : Prop :=
  ∃ C : StepParameters → ℝ, (∀ T, 0 < C T) ∧
    EventuallyInParameters fun T => BlockSumDerivBoundAt T (C (parametersBeforeSide T)) ∧
      BlockSumNearValueAt T (C (parametersBeforeSide T))
end YangMills.Construction.WeightedResponses
end
