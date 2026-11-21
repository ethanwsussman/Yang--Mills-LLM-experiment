import YangMills.Construction.Towers.MultiplesOfTheKernelOfAnEvaluation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open PeriodicOperators (Represents swapKernel)
theorem ScalarMultipleKernels.statement_holds : ScalarMultipleKernels.Statement := by
  intro r r' m hom hk uniq z a a'
  have hmap : PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' (fun f => z • m f) =
      (z : ℂ) • PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m := by
    funext f
    exact hom z (m (r.ofCoeffs f))
  have hrep : Represents ((z : ℂ) • r.kernel r' m)
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' fun f => z • m f) := by
    rw [hmap]
    exact hk.smul_represents z
  have hspec : Represents (r.kernel r' fun f => z • m f)
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' fun f => z • m f) :=
    Classical.epsilon_spec (p := fun T => Represents T
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' fun f => z • m f)) ⟨_, hrep⟩
  have hker := uniq _ _ _ hspec hrep
  refine ⟨hker, ?_⟩
  rw [hker]
  funext x y
  simp only [meshTranspose, PeriodicOperators.wTranspose, meshWeight, swapKernel,
    Pi.smul_apply, smul_eq_mul]
  push_cast
  ring
end YangMills.Construction.Tower
end
