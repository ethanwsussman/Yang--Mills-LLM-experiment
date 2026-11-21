import YangMills.Construction.FreeKernel.DiscreteTorusAsClassesOfVectors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.VectorClasses
open YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint YangMills.Construction.FourVector
def ExpWaveMultipliers : Prop :=
  ∀ (k : Fin 4 → ℝ) (μ : Fin 4),
    ShortDistanceTwoPoint.forwardDiff μ (ShortDistanceTwoPoint.expWave k) =
        (fun z => (Complex.exp (Complex.I * (k μ : ℂ)) - 1) * ShortDistanceTwoPoint.expWave k z) ∧
      ShortDistanceTwoPoint.backwardDiff μ (ShortDistanceTwoPoint.expWave k) =
        (fun z => -(Complex.exp (-(Complex.I * (k μ : ℂ))) - 1) *
          ShortDistanceTwoPoint.expWave k z) ∧
      ShortDistanceTwoPoint.discreteLaplacian (ShortDistanceTwoPoint.expWave k) =
        fun z => (ShortDistanceTwoPoint.laplacianSymbol k : ℂ) * ShortDistanceTwoPoint.expWave k z
def LaplacianSymbolModulusFormAndBounds : Prop :=
  (∀ k : Fin 4 → ℝ, ShortDistanceTwoPoint.laplacianSymbol k =
      ∑ μ, ‖Complex.exp (Complex.I * (k μ : ℂ)) - 1‖ ^ 2) ∧
    ∀ k : Fin 4 → ℝ, (∀ μ, k μ ∈ Set.Icc (-Real.pi) Real.pi) →
      4 / Real.pi ^ 2 * FourVector.euclidNorm k ^ 2 ≤ ShortDistanceTwoPoint.laplacianSymbol k ∧
        ShortDistanceTwoPoint.laplacianSymbol k ≤ FourVector.euclidNorm k ^ 2
def ExpWaveCharacters (n : ℕ) [NeZero n] : Prop :=
  (ShortDistanceTwoPoint.momentumSet n).ncard = n ^ 4 ∧
    (∀ k ∈ ShortDistanceTwoPoint.momentumSet n,
      IsClassFunction n (ShortDistanceTwoPoint.expWave k)) ∧
    (∀ k ∈ ShortDistanceTwoPoint.momentumSet n, ∀ k' ∈ ShortDistanceTwoPoint.momentumSet n,
      classSum n (ShortDistanceTwoPoint.expWave (k - k')) =
        (n : ℂ) ^ 4 * (FourVector.propIndicator (k = k') : ℂ)) ∧
    ∀ f g : (Fin 4 → ℤ) → ℂ, IsClassFunction n f → IsClassFunction n g →
      (∀ k ∈ ShortDistanceTwoPoint.momentumSet n,
        classSum n (fun z => f z * ShortDistanceTwoPoint.expWave (-k) z) =
          classSum n (fun z => g z * ShortDistanceTwoPoint.expWave (-k) z)) → f = g
def deltaAtZeroClass (n : ℕ) (z : Fin 4 → ℤ) : ℂ :=
  (FourVector.propIndicator
    (ShortDistanceTwoPoint.zmodClass n z = ShortDistanceTwoPoint.zmodClass n 0) : ℂ)
def DiscreteLaplacianOfGreen (n : ℕ) : Prop :=
  ShortDistanceTwoPoint.discreteLaplacian (greenOnVectors n) =
    fun z => deltaAtZeroClass n z - ((n : ℂ) ^ 4)⁻¹
def ContinuumGreenSecondPartials : Prop :=
  ∀ (ν ν' : Fin 4) (u : Fin 4 → ℝ), u ≠ 0 →
    LineDifferentiableAt ℝ ShortDistanceTwoPoint.continuumGreenFunction u
        (FourVector.unitVec ν') ∧
      LineDifferentiableAt ℝ
        (FourVector.coordPartialDeriv ν' ShortDistanceTwoPoint.continuumGreenFunction) u
        (FourVector.unitVec ν) ∧
      FourVector.coordPartialDeriv ν
          (FourVector.coordPartialDeriv ν' ShortDistanceTwoPoint.continuumGreenFunction) u =
        -(1 / (2 * Real.pi ^ 2 * FourVector.euclidNorm u ^ 4)) *
          (FourVector.kronecker ν ν' - 4 * u ν * u ν' / FourVector.euclidNorm u ^ 2)
def FourierFactsAndGreenIdentities.Statement : Prop :=
  ∀ (n : ℕ) [NeZero n], 2 ≤ n →
    ExpWaveMultipliers ∧ LaplacianSymbolModulusFormAndBounds ∧ ExpWaveCharacters n ∧
      DiscreteLaplacianOfGreen n ∧ ContinuumGreenSecondPartials
end YangMills.Construction.PeriodicLattice.VectorClasses
end
