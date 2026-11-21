import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Conventions.StandingParameters
def centeredBox (s : StandingParameters) : Set (Fin 4 → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ico (-(s.side / 2)) (s.side / 2)
def IsCenteredLift (s : StandingParameters) (y : s.Torus) (z : Fin 4 → ℝ) : Prop :=
  z ∈ s.centeredBox ∧ TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) z = y
def CenteredLiftUnique : Prop :=
  ∀ (s : StandingParameters) (y : s.Torus), ∃! z : Fin 4 → ℝ, s.IsCenteredLift y z
end Conventions.StandingParameters
end YangMills.Construction
end
