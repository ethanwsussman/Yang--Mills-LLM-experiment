import YangMills.Construction.Matrices.NormAndTraceOfAComplexMatrix
import YangMills.Construction.Towers.ParametrixOfTheExpansionInTheFlux
import Mathlib
set_option autoImplicit false
open Filter Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (torusAverage toComplexVec)
noncomputable section
namespace YangMills.Construction.Tower.MagneticWeyl
open FluxExpansion in
def HalfLineTraceLimits : Prop :=
  ∀ (n : ℕ) [NeZero n] (z : ℝ), 0 < z → ∀ s₁ s₂ : AmbientSpace → Matrix (Fin n) (Fin n) ℂ,
    Continuous s₁ → Continuous s₂ →
    ContinuousOn (fun w : ℝ => torusAverage fun q =>
        Matrices.RectangularMatrix.diagSum (termZero n (z + w) q))
      (Ici 0) ∧
    ContinuousOn (fun w : ℝ => torusAverage fun q =>
        Matrices.RectangularMatrix.diagSum (termOne (z + w) s₁ q))
      (Ici 0) ∧
    ContinuousOn (fun w : ℝ => torusAverage fun q =>
        Matrices.RectangularMatrix.diagSum (termTwo (z + w) s₁ s₂ q))
      (Ici 0) ∧
    (∀ w φ : ℝ, 0 ≤ w →
      (torusAverage fun q => Matrices.RectangularMatrix.diagSum (approxInverse (z + w) φ s₁ s₂ q)) =
        (torusAverage fun q => Matrices.RectangularMatrix.diagSum (termZero n (z + w) q)) +
          (φ : ℂ) * (torusAverage fun q => Matrices.RectangularMatrix.diagSum (termOne (z + w) s₁ q)) +
          (φ : ℂ) ^ 2 * torusAverage fun q =>
            Matrices.RectangularMatrix.diagSum (termTwo (z + w) s₁ s₂ q)) ∧
    Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, ((n : ℂ) * (((1 + w)⁻¹ : ℝ) : ℂ) -
        torusAverage fun q => Matrices.RectangularMatrix.diagSum (termZero n (z + w) q))) atTop
      (nhds (torusAverage fun q => Matrices.RectangularMatrix.diagSum
        (Complex.log (baseSymbol q + z) • (1 : Matrix (Fin n) (Fin n) ℂ)))) ∧
    Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y,
        -(torusAverage fun q => Matrices.RectangularMatrix.diagSum (termOne (z + w) s₁ q))) atTop
      (nhds (torusAverage fun q => shiftedInverse z q * Matrices.RectangularMatrix.diagSum (s₁ q))) ∧
    Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y,
        -(torusAverage fun q => Matrices.RectangularMatrix.diagSum (termTwo (z + w) s₁ s₂ q))) atTop
      (nhds (torusAverage fun q =>
        -(1 / 2) * shiftedInverse z q ^ 2 * Matrices.RectangularMatrix.diagSum (s₁ q ^ 2) +
          shiftedInverse z q * Matrices.RectangularMatrix.diagSum (s₂ q) +
          (n : ℂ) / 24 * shiftedInverse z q ^ 2 * baseSymbolSecondDeriv 0 q * baseSymbolSecondDeriv 1 q))
end YangMills.Construction.Tower.MagneticWeyl
end
