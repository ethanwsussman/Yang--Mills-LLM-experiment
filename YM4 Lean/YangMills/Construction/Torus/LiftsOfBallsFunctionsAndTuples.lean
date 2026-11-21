import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.Lattice.ToriLatticesNormsAndFunctionsOfFinitelyManyVariables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TestFunctions
open TorusMetric
variable {L m n : ℕ} {E : Type*} [Zero E]
def IsAdmissibleRadius (L m : ℕ) (ρ : ℝ) : Prop := 0 < ρ ∧ ρ < PeriodicLattice.torusSide L m / 4
def IsClosedBallLift (z : PeriodicLattice.FourTorus L m) (ρ : ℝ) (B : Set (Fin 4 → ℝ)) : Prop :=
  IsAdmissibleRadius L m ρ ∧ ∃ c ∈ PeriodicLattice.liftsOf z, B = closedBallR4 c ρ
def ballIndicatorLift (c : Fin 4 → ℝ) (ρ : ℝ) (f : PeriodicLattice.FourTorus L m → E) :
    (Fin 4 → ℝ) → E :=
  (closedBallR4 c ρ).indicator (f ∘ torusProj (PeriodicLattice.torusSide L m))
def IsFunctionLift (z : PeriodicLattice.FourTorus L m) (ρ : ℝ) (c : Fin 4 → ℝ)
    (f : PeriodicLattice.FourTorus L m → E) (g : (Fin 4 → ℝ) → E) : Prop :=
  IsAdmissibleRadius L m ρ ∧ c ∈ PeriodicLattice.liftsOf z ∧
    PeriodicLattice.metricSupport f ⊆ closedBallTorus z ρ ∧ g = ballIndicatorLift c ρ f
def SupportsInBall (z : PeriodicLattice.FourTorus L m) (ρ : ℝ)
    (f : Fin n → PeriodicLattice.FourTorus L m → E) : Prop :=
  IsAdmissibleRadius L m ρ ∧ ∀ i, PeriodicLattice.metricSupport (f i) ⊆ closedBallTorus z ρ
def SupportsInSomeBall (f : Fin n → PeriodicLattice.FourTorus L m → E) : Prop :=
  ∃ (z : PeriodicLattice.FourTorus L m) (ρ : ℝ), SupportsInBall z ρ f
def IsTupleLift (f : Fin n → PeriodicLattice.FourTorus L m → E)
    (g : Fin n → (Fin 4 → ℝ) → E) : Prop :=
  ∃ (z : PeriodicLattice.FourTorus L m) (ρ : ℝ), SupportsInBall z ρ f ∧
    ∃ c ∈ PeriodicLattice.liftsOf z, ∀ i, g i = ballIndicatorLift c ρ (f i)
end TestFunctions
end YangMills.Construction
