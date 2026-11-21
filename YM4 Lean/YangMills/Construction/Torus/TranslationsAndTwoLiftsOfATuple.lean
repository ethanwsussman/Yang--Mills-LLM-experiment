import YangMills.Construction.Torus.FreeKernelsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tuples TestFunctions PeriodicLattice Conventions
namespace FreeRingKernels.TranslationInvariance
def KernelsTranslationInvariant : Prop :=
  (∀ (m : ℕ), 2 ≤ m → ∀ R : Set (Fin m → Fin m), IsRingOfTuples R →
    ∀ f : Fin m → (Fin 4 → ℝ) → ℝ, IsAdmissibleTestFamily f → ∀ v : Fin 4 → ℝ,
      freeRingKernel R (fun j y => f j (y - v)) = freeRingKernel R f) ∧
  (∀ f : Fin 4 → (Fin 4 → ℝ) → ℝ, IsAdmissibleTestFamily f → ∀ v : Fin 4 → ℝ,
    freeBoxKernel (fun j y => f j (y - v)) = freeBoxKernel f) ∧
  (∀ x : Fin 4 → Fin 4 → ℝ, Function.Injective x → ∀ v : Fin 4 → ℝ,
    freeBoxDensity (fun i => x i + v) = freeBoxDensity x)
def LiftsDifferByPeriod : Prop :=
  ∀ (s : StandingParameters) (m : ℕ), 1 ≤ m → ∀ (f : Fin m → s.Torus → ℝ) (z z' : s.Torus)
    (ρ ρ' : ℝ), SupportsInBall z ρ f → SupportsInBall z' ρ' f →
      ∀ c ∈ liftsOf z, ∀ c' ∈ liftsOf z', ∃ k : Fin 4 → ℤ, ∀ i,
        ballIndicatorLift c' ρ' (f i) =
          fun y => ballIndicatorLift c ρ (f i) (fun α => y α - s.side * (k α : ℝ))
def LiftKernelsIndependent : Prop :=
  (∀ (s : StandingParameters) (m : ℕ), 2 ≤ m → ∀ f : Fin m → s.Torus → ℝ,
    IsTorusKernelFamily f →
    (∀ g, IsTupleLift f g → IsAdmissibleTestFamily g) ∧
      ∀ g g', IsTupleLift f g → IsTupleLift f g' →
        ∀ R : Set (Fin m → Fin m), IsRingOfTuples R → freeRingKernel R g = freeRingKernel R g') ∧
  (∀ (s : StandingParameters) (f : Fin 4 → s.Torus → ℝ), IsTorusKernelFamily f →
    ∀ g g', IsTupleLift f g → IsTupleLift f g' → freeBoxKernel g = freeBoxKernel g')
def Statement : Prop :=
  KernelsTranslationInvariant ∧ LiftsDifferByPeriod ∧ LiftKernelsIndependent
end FreeRingKernels.TranslationInvariance
end YangMills.Construction
end
