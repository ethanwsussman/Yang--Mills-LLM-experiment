import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace RiemannSums
def periodLattice : AddSubgroup InfiniteLattice.AmbientSpace :=
  InfiniteLattice.latticeSubgroup (2 * Real.pi)
abbrev DualClasses (N : ℕ) : Type :=
  dualLattice N ⧸ periodLattice.addSubgroupOf (dualLattice N)
def HolomorphicNearStrip (w : ℝ) (f : (Fin 4 → ℂ) → ℂ) : Prop :=
  ∃ U : Set (Coordinates.ComplexCoordinates 4), imStrip w ⊆ U ∧
    Coordinates.ComplexCoordinates.IsHolomorphicIn U
      fun (z : Coordinates.ComplexCoordinates 4) (_ : Fin 1) => f z
def PeriodicOnStrip (w : ℝ) (f : (Fin 4 → ℂ) → ℂ) : Prop :=
  ∀ z ∈ imStrip w, ∀ q ∈ periodLattice, f (z + toComplexVec q) = f z
def BoundedOnStrip (w : ℝ) (f : (Fin 4 → ℂ) → ℂ) : Prop :=
  ∃ M : ℝ, ∀ z ∈ imStrip w, ‖f z‖ ≤ M
def classSum (N : ℕ) (f : (Fin 4 → ℂ) → ℂ) : ℂ :=
  ∑ᶠ q : DualClasses N, f (toComplexVec (Quotient.out q : dualLattice N))
def stripSup (w : ℝ) (f : (Fin 4 → ℂ) → ℂ) : ℝ :=
  ⨆ z : imStrip w, ‖f z‖
def Claim : Prop :=
  ∀ (N : ℕ) (w : ℝ) (f : (Fin 4 → ℂ) → ℂ), 0 < N → 0 < w →
    HolomorphicNearStrip w f → PeriodicOnStrip w f → BoundedOnStrip w f →
    ‖((N : ℂ) ^ 4)⁻¹ * classSum N f - torusAverage fun x => f (toComplexVec x)‖ ≤
        stripSup w f * ((1 + 2 * (Real.exp (w * N) - 1)⁻¹) ^ 4 - 1) ∧
      ∀ t ∈ imStrip w,
        (torusAverage fun x => f (toComplexVec x + t)) = torusAverage fun x => f (toComplexVec x)
end RiemannSums
end YangMills.Construction.PeriodicOperators
end
