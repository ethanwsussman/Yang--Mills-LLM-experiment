import YangMills.Construction.SummableBoundsOfTheFlow.ObservableOfTheFrameGap
import YangMills.Construction.SummableBoundsOfTheFlow.ThirdOrderWithTwoFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def gapObservableThirdOrderAt (T : StepParameters) (Cf : ℝ) : Prop :=
  ∀ N : ℕ, ∃ (CN : ℝ) (Cq : ℕ → ℝ), 0 < CN ∧ (∀ q, 0 ≤ Cq q) ∧
    ∀ (t : ℕ) (x s : ℝ) (φ : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell)
      (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions)
      (Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions),
      T.coupling ≤ x → 0 ≤ s → s ≤ 1 →
      FamilyNorms.IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ →
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → AreUnitVectors X →
      (∀ i, 4 * frameRadius x + 5 < F.extent i) →
      (∀ w X' : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X' (Th w X')) →
      ThirdOrderHypotheses Th s T.a T.chainParams.ρA T.ballRadius x T.κ
        (CN * (x ^ N)⁻¹ * (Cf * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x))))
        (CN * (x ^ N)⁻¹ * (Cf * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x))))
        (frameRadius x) T.p Cq V Y c X
        (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V)
        (blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y V)
def gapObservableThirdOrderStatement : Prop :=
  EventuallyInParameters fun T => gapObservableThirdOrderAt T T.Cs
end Interpolation
end YangMills.Construction
end
