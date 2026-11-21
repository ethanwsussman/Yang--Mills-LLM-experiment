import YangMills.Construction.RunningCouplingSlope.OnePlainStepOnTheWhole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
def MeanStepShiftCovariant : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ δ : ℝ, 0 < δ ∧ ∀ k j : ℕ, j < k →
    ∀ n : Fin 4 → ℤ,
    ∀ V ∈ nearIdentityFields L k j δ,
      nextMeanIterate (Tower.FullSpace.pushField (PeriodicOperators.intShift n) V) =
          Tower.FullSpace.pushField (PeriodicOperators.intShift n) (nextMeanIterate V) ∧
      ∀ c : Tower.FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
        meanRadius (Tower.FullSpace.pushField (PeriodicOperators.intShift n) V)
            (Tower.FullSpace.edgeImage (PeriodicOperators.intShift n) c) =
          meanRadius V c ∧
        ∀ B ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k j),
          meanCovariantStep (Tower.FullSpace.pushField (PeriodicOperators.intShift n) V)
              (Tower.FullSpace.isometryOnTangent (PeriodicOperators.intShift n) V B)
              (Tower.FullSpace.edgeImage (PeriodicOperators.intShift n) c) =
            meanCovariantStep V B c
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
