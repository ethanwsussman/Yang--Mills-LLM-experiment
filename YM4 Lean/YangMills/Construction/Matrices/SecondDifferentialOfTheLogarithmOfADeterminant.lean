import YangMills.Construction.Lattice.DerivativeOfAHolomorphicMapAndOpenBalls
import Mathlib
open scoped Topology
noncomputable section
namespace YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv
variable {N n : ℕ}
def asLine (g : ComplexCoordinates N → ℂ) : ComplexCoordinates N → ComplexCoordinates 1 :=
  fun z _ => g z
def IsHolomorphicScalarIn (O : Set (ComplexCoordinates N)) (g : ComplexCoordinates N → ℂ) : Prop :=
  IsHolomorphicIn O (asLine g)
def scalarDeriv (g : ComplexCoordinates N → ℂ) (z v : ComplexCoordinates N) : ℂ :=
  fderiv ℝ (asLine g) z v 0
def scalarSecondDeriv (g : ComplexCoordinates N → ℂ) (z u v : ComplexCoordinates N) : ℂ :=
  secondDeriv (asLine g) z u v 0
def seriesLog (w : ℂ) : ℂ :=
  ∑' m : ℕ, (-1 : ℂ) ^ m * (w - 1) ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
def detNormalized (M : ComplexCoordinates N → Matrix (Fin n) (Fin n) ℂ)
    (z : ComplexCoordinates N) : ℂ :=
  Matrix.det ((M 0)⁻¹ * M z)
def logDetNormalized (M : ComplexCoordinates N → Matrix (Fin n) (Fin n) ℂ)
    (z : ComplexCoordinates N) : ℂ :=
  seriesLog (detNormalized M z)
def derivMatrix (M : ComplexCoordinates N → Matrix (Fin n) (Fin n) ℂ)
    (u : ComplexCoordinates N) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => scalarDeriv (fun z => M z i j) 0 u
def secondDerivMatrix (M : ComplexCoordinates N → Matrix (Fin n) (Fin n) ℂ)
    (u v : ComplexCoordinates N) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => scalarSecondDeriv (fun z => M z i j) 0 u v
def Claim : Prop :=
  (∀ (N n : ℕ) (O : Set (ComplexCoordinates N)) (M : ComplexCoordinates N → Matrix (Fin n) (Fin n) ℂ),
    IsOpen O → 0 ∈ O → (∀ i j, IsHolomorphicScalarIn O fun z => M z i j) → IsUnit (M 0) →
      (∃ W : Set (ComplexCoordinates N), IsOpen W ∧ 0 ∈ W ∧ W ⊆ O ∧
        (∀ z ∈ W, ‖detNormalized M z - 1‖ < 1) ∧
        IsHolomorphicScalarIn W (logDetNormalized M)) ∧
      ∀ u v : ComplexCoordinates N,
        scalarSecondDeriv (logDetNormalized M) 0 u v =
          Matrix.trace ((M 0)⁻¹ * secondDerivMatrix M u v) -
            Matrix.trace ((M 0)⁻¹ * derivMatrix M u * (M 0)⁻¹ *
              derivMatrix M v)) ∧
  ∀ (N : ℕ) (W : Set (ComplexCoordinates N)) (g : ComplexCoordinates N → ℂ),
    IsOpen W → 0 ∈ W → IsHolomorphicScalarIn W g → ∀ u v : ComplexCoordinates N,
      HasDerivAt (fun t : ℝ => g (t • u)) (scalarDeriv g 0 u) 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, DifferentiableAt ℝ (fun t' : ℝ => g (t • u + t' • v)) 0) ∧
      HasDerivAt (fun t : ℝ => deriv (fun t' : ℝ => g (t • u + t' • v)) 0)
        (scalarSecondDeriv g 0 u v) 0
end YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv
