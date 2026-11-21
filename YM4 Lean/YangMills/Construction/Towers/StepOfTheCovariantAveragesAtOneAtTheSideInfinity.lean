import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower.FullSpace
def SmoothingStepAtOne : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k i : ℕ, i < k →
    (∀ A ∈ edgeFormSpace (meshAt L k i),
      complexSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) A =
        linearSmoothing (a := meshAt L k (i + 1)) L A ∧
      contourLogDrift (L := L) (k := k) (j := i) (fun _ => 1) A =
        cubeContourAverage (a := meshAt L k (i + 1)) L A ∧
      covariantSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) A =
        crossingSmoothing (a := meshAt L k (i + 1)) L A) ∧
    ∀ f ∈ vertexFunctionSpace (meshAt L k i),
      adjointCubeAverage (L := L) (k := k) (j := i) (fun _ => 1) f =
        vertexSmoothing (a := meshAt L k (i + 1)) L f
end Tower.FullSpace
end YangMills.Construction
end
