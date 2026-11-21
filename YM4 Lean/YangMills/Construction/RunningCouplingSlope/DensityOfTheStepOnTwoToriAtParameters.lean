import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
def StepDensityLocality : Prop :=
  ∃ c : RenormalizationStepParameters.ChainParameters → ℝ, (∀ p, 0 < c p) ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∃ C : ℝ, 0 < C ∧
    ∀ (t n n' : ℕ) [NeZero n] [NeZero n'], 64 ≤ n → 64 ≤ n' →
      ∀ (y : TorusFields.TorusSite n) (y' : TorusFields.TorusSite n')
        (W : TorusFields.TorusField n) (W' : TorusFields.TorusField n') (m : ℕ),
        2 * m + 2 < n → 2 * m + 2 < n' →
        TorusFields.IsCold T.threshold W → TorusFields.IsCold T.threshold W' →
        TorusLumps.FieldsAgreeNear W W' y y' m →
        ∀ (k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → BlockAverages.imaginaryQuaternions), k ≤ 2 →
          (∀ l, TorusFields.BondOffsetInBox m (b l)) →
          BlockAverages.AreUnitVectors X →
          |TorusFields.mixedDeriv (ReferenceDensity.stepDensityFamily T.coupling T.ρA T.lam T.side t n y) W
                (fun l => TorusLumps.bondFrom y (b l)) X -
              TorusFields.mixedDeriv (ReferenceDensity.stepDensityFamily T.coupling T.ρA T.lam T.side t n' y') W'
                (fun l => TorusLumps.bondFrom y' (b l)) X| ≤
            C * Real.exp (-(c T.toChainParameters * m))
end RunningCouplingSlope
end YangMills.Construction
end
