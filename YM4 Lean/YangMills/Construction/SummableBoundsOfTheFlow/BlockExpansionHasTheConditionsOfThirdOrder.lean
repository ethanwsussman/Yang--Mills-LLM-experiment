import YangMills.Construction.SummableBoundsOfTheFlow.ThirdOrderWithTwoFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def blockExpansionThirdOrderAt (T : StepParameters) (Cq : ℕ → ℝ) : Prop :=
  ∀ (t : ℕ) (x s ε : ℝ) (φ h : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell)
    (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions)
    (Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 → 0 < ε →
    FamilyNorms.IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ →
    FamilyNorms.IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h →
    IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → AreUnitVectors X →
    (∀ w X' : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X' (Th w X')) →
    ThirdOrderHypotheses Th s T.a T.chainParams.ρA T.ballRadius x T.κ (T.Cs * ε * x ^ (-(1 / 2 : ℝ)))
      (T.Cs * ε * x ^ (-(1 / 2 : ℝ))) (frameRadius x) T.p Cq V Y c X
      (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V)
      (fun η => interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) h Y η V)
def blockExpansionThirdOrderStatement : Prop :=
  ∃ Cq : StepParameters → ℕ → ℝ, (∀ T q, 0 ≤ Cq T q) ∧
    EventuallyInParameters fun T =>
      blockExpansionThirdOrderAt T (Cq { T with n₀ := 0, CE := 0, coupling := 0 })
end Interpolation
end YangMills.Construction
end
