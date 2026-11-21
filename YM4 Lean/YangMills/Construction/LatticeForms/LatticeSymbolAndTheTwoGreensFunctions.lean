import YangMills.Construction.LatticeForms.IndicatorCochainsKernelsAndPseudoInverses
import YangMills.Construction.LatticeForms.UnitDifferencesLatticeLaplacianAndTheTwoGreensFunctions
import YangMills.Construction.TestFunctions.LaplacianOfR4
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
open YangMills.Construction.TorusMetric
def torusEuclideanEquiv (n : ℕ) : (IntegerTorus n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (IntegerTorus n) :=
  (WithLp.linearEquiv 2 ℝ (IntegerTorus n → ℝ)).symm
theorem inner_torusEuclideanEquiv {n : ℕ} [NeZero n] (g g' : IntegerTorus n → ℝ) :
    inner ℝ (torusEuclideanEquiv n g) (torusEuclideanEquiv n g') = torusInner g g' := by
  simp [torusEuclideanEquiv, torusInner, PiLp.inner_apply, mul_comm]
def discreteLaplacianPinv (n : ℕ) [NeZero n] : (IntegerTorus n → ℝ) →ₗ[ℝ] IntegerTorus n → ℝ :=
  (torusEuclideanEquiv n).symm.conj
    (YangMills.Construction.LatticeForms.moorePenrose
      ((torusEuclideanEquiv n).conj (discreteLaplacianLinear ℝ)))
def ExpWavesAreEigenvectors (n : ℕ) : Prop :=
  (∀ k : Fin 4 → ℝ, discreteLaplacian (expWave k) = fun z => (laplacianSymbol k : ℂ) * expWave k z) ∧
    ∀ k ∈ momentumSet n, discreteLaplacian (expWaveOnTorus (n := n) k) =
      fun z => (laplacianSymbol k : ℂ) * expWaveOnTorus k z
def SymbolComparableToSquare : Prop :=
  ∀ k : Fin 4 → ℝ, (∀ μ, k μ ∈ Icc (-Real.pi) Real.pi) →
    4 / Real.pi ^ 2 * euclidNormVec k ^ 2 ≤ laplacianSymbol k ∧
      laplacianSymbol k ≤ euclidNormVec k ^ 2
def PinvKernelIsLatticeGreen (n : ℕ) [NeZero n] : Prop :=
  (∀ g g' : IntegerTorus n → ℝ,
      torusInner g (discreteLaplacian g') = torusInner (discreteLaplacian g) g') ∧
    (∀ g : IntegerTorus n → ℝ, 0 ≤ torusInner g (discreteLaplacian g)) ∧
    (∀ z : IntegerTorus n, (latticeGreenFunction n z).im = 0) ∧
    ∀ z z' : IntegerTorus n,
      (kernelOf (discreteLaplacianPinv n) z z' : ℂ) = latticeGreenFunction n (z - z')
def ContinuumGreenIsFundamentalSolution : Prop :=
  (∀ B : Set (Fin 4 → ℝ), MeasurableSet B → Bornology.IsBounded B →
      IntegrableOn continuumGreenFunction B) ∧
    ∀ φ : (Fin 4 → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ u, continuumGreenFunction u *
        (-YangMills.Construction.TestFunctions.laplacianR4 φ u) = φ 0
def ContinuumGreenSecondDerivatives : Prop :=
  ∀ u : Fin 4 → ℝ, u ≠ 0 → ∀ ν ν' : Fin 4,
    YangMills.Construction.TestFunctions.partialDerivR4 ν
        (YangMills.Construction.TestFunctions.partialDerivR4 ν' continuumGreenFunction) u =
      -(1 / (2 * Real.pi ^ 2 * euclidNormVec u ^ 4)) *
        ((if ν = ν' then 1 else 0) - 4 * u ν * u ν' / euclidNormVec u ^ 2)
def SymbolAndGreenFunctions : Prop :=
  ∀ (n : ℕ) [NeZero n], 2 ≤ n →
    ExpWavesAreEigenvectors n ∧
      SymbolComparableToSquare ∧
      PinvKernelIsLatticeGreen n ∧
      ContinuumGreenIsFundamentalSolution ∧
      ContinuumGreenSecondDerivatives
end YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
