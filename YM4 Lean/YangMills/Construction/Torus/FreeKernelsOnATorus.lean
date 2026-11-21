import YangMills.Construction.Continuum.FreeRingKernelsAndTheFreeBoxKernel
import YangMills.Construction.Torus.IntegralOverTheTorus
import YangMills.Construction.Torus.LiftsOfBallsFunctionsAndTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice TestFunctions
namespace FreeRingKernels
variable {L m n : ℕ}
def IsTorusKernelFamily (f : Fin n → FourTorus L m → ℝ) : Prop :=
  (∀ j, IsBoundedBorel (f j)) ∧
    (Pairwise fun i j => Disjoint (metricSupport (f i)) (metricSupport (f j))) ∧
      SupportsInSomeBall f
open Classical in
def tupleLift (f : Fin n → FourTorus L m → ℝ) : Fin n → (Fin 4 → ℝ) → ℝ :=
  if H : ∃ g, IsTupleLift f g then H.choose else 0
theorem exists_isTupleLift {f : Fin n → FourTorus L m → ℝ} (hf : SupportsInSomeBall f) :
    ∃ g, IsTupleLift f g := by
  obtain ⟨z, r, hz⟩ := hf
  exact ⟨fun i => ballIndicatorLift (liftPoint z) r (f i), z, r, hz, liftPoint z,
    torusProj_liftPoint z, fun _ => rfl⟩
theorem isTupleLift_tupleLift {f : Fin n → FourTorus L m → ℝ}
    (hf : SupportsInSomeBall f) : IsTupleLift f (tupleLift f) := by
  have H := exists_isTupleLift hf
  rw [tupleLift, dif_pos H]
  exact H.choose_spec
def freeBoxKernelTorus (f : Fin 4 → FourTorus L m → ℝ) : ℝ :=
  freeBoxKernel (tupleLift f)
end FreeRingKernels
end YangMills.Construction
end
