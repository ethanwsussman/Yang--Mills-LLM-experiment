import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import YangMills.Construction.ResponseInTheExpansion.FamiliesOnOneTorus
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfAMeanInTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.Interpolation YangMills.Construction.Estimates
variable {F : BlockFrame}
structure HasMixedDerivBounds (ρ κ C e e₃ : ℝ) (G : F.Site F.depth → AboveFrames F)
    (V : F.GaugeField F.top) : Prop where
  smooth : ∀ y, JointlyContDiffOnBalls ρ V (G y)
  deriv_one : ∀ (y : F.Site F.depth) (ζ : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F)))
    (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    (∀ b, ‖ζ b‖ ≤ ρ) → ‖u‖ = 1 → k ≤ 2 → AreUnitVectors X →
    |jointMixedDeriv (G y) ζ V ![b] ![u] c X| ≤ C * (if k = 2 then e₃ else e) *
      Real.exp (-(2 ^ 7 * κ * cellSetDiameter
        (insert (enclosingCell y) (chordBondCells ![b] ∪ topBondCells c))))
  deriv_two : ∀ (y : F.Site F.depth) (ζ : StepVariable (finiteCells F)) (b b' : ↥(chordBonds (finiteCells F)))
    (u u' : EuclideanSpace ℝ (Fin 3)), (∀ b, ‖ζ b‖ ≤ ρ) → ‖u‖ = 1 → ‖u'‖ = 1 →
    |jointMixedDeriv (G y) ζ V ![b, b'] ![u, u'] (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions)| ≤
      C * e * Real.exp (-(2 ^ 7 * κ * cellSetDiameter (insert (enclosingCell y) (chordBondCells ![b, b'] ∪
        topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)))))
def remainderExpansionAboveFramesAt (T : StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x e : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (r : F.Site F.depth → F.GaugeField F.depth → ℝ),
    T.coupling ≤ x → IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 < e →
    IsDecayingSiteFamily T.L T.σ T.decayRate e (e / T.η₃) r →
    HasMixedDerivBounds T.ballRadius T.κ C e (e / T.η₃) ((coldHalfLawAt T x f).liftedExpansion r) V
def remainderExpansionAboveFramesStatement : Prop :=
  ∃ C : StepParameters → ℝ, (∀ T, 0 < C T) ∧
    EventuallyInParameters fun T => remainderExpansionAboveFramesAt T (C (parametersBeforeSide T))
end YangMills.Construction.WeightedResponses
end
