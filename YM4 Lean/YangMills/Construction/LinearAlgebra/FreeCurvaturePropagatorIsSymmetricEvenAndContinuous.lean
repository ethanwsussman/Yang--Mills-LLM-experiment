import YangMills.Construction.Lattice.AxisBivectorBasis
import YangMills.Construction.LinearAlgebra.FreeCurvaturePropagator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Exterior
open YangMills.Construction.PeriodicLattice
def FreeCurvaturePropagatorSymmEvenContinuous : Prop :=
  (∀ x : Fin 4 → ℝ, x ≠ 0 → IsSelfAdjointMap (freeCurvaturePropagator x)) ∧
    (∀ x : Fin 4 → ℝ, x ≠ 0 → freeCurvaturePropagator (-x) = freeCurvaturePropagator x) ∧
      ∀ P Q : AxisPlane,
        ContinuousOn (fun x : Fin 4 → ℝ => bivectorMatrixEntry (freeCurvaturePropagator x) P Q) {x | x ≠ 0}
end YangMills.Construction.Exterior
end
