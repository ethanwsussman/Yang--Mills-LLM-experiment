import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusMetric
variable {S : ℝ}
def IsMinimalLift (z : Torus4 S) (v : Fin 4 → ℝ) : Prop :=
  torusProj S v = z ∧ euclidNormVec v = torusEuclidNorm z
def minimalLift (z : Torus4 S) : Fin 4 → ℝ := Classical.epsilon (IsMinimalLift z)
def MinimalLiftUnique : Prop :=
  ∀ (s : Conventions.StandingParameters) (z : s.Torus), torusEuclidNorm z < s.side / 2 →
    (∃! v : Fin 4 → ℝ, IsMinimalLift z v) ∧ IsMinimalLift z (minimalLift z) ∧
      ∀ w : Fin 4 → ℝ, torusProj (PeriodicLattice.torusSide s.L s.m) w = z → w ≠ minimalLift z →
        s.side - torusEuclidNorm z ≤ euclidNormVec w ∧ s.side / 2 < s.side - torusEuclidNorm z
end YangMills.Construction.TorusMetric
end
