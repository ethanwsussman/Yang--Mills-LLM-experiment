import YangMills.Construction.SystemOfAdmissibleConstants.AdmissibleSideLengths
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
open RenormalizationStepParameters TrajectoryData
namespace TrajectoryCouplingsGiveWindow
def Statement : Prop :=
  ∀ P : ∀ (T : ParameterAssignment) (y : ℝ), TrajectoryParameters T y → ℝ → Prop,
    SystemOfAdmissibleConstants.ForAllTrajectoryCouplings P →
      HoldsAtAdmissibleParameters fun T y => ∀ Bs : ℝ, 2 * T.B ≤ Bs → ForSmallCoupling fun g =>
        ∃ D : TrajectoryParameters T y, D.shift = Bs ∧ P T y D g
end TrajectoryCouplingsGiveWindow
end YangMills.Construction.TotalDensities
end
