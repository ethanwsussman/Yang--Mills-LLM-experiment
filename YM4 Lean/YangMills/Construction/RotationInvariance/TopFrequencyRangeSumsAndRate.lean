import YangMills.Construction.RotationInvariance.TopFrequencyOfTheHarmonics
import Mathlib
set_option autoImplicit false
open Complex (I)
open Filter Topology
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.MaxFrequencyFacts
def symmIcc (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
def MaxFrequencyLe {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) : Prop :=
  ∀ n : ℕ, (maxFrequency S d.angle n : ℝ) ≤ d.base.expo * (n : ℝ) / 4
def FiniteHarmonicSum (S : ConnFamily) (θ : RealPlane.openingAngles) {q : ℕ}
    (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → RealPlane.realLabels) : Prop :=
  (∀ ν : ℤ, maxFrequency S θ (q + 1) < ν.natAbs → angleHarmonic S θ y φ ν = 0) ∧
  (∀ t s : ℝ, angleFunction S θ y φ ((t : ℂ) + I * (s : ℂ)) =
    ∑ ν ∈ symmIcc (maxFrequency S θ (q + 1)),
      angleHarmonic S θ y φ ν * Complex.exp (4 * I * (ν : ℂ) * ((t : ℂ) + I * (s : ℂ)))) ∧
  ∀ s : ℝ, angleFunction S θ y φ (I * (s : ℂ)) =
    ∑ ν ∈ symmIcc (maxFrequency S θ (q + 1)),
      angleHarmonic S θ y φ ν * Complex.exp (-(4 * (ν : ℂ) * (s : ℂ)))
def MaxFrequencyAttained (S : ConnFamily) (θ : RealPlane.openingAngles) : Prop :=
  ∀ n : ℕ, 1 ≤ maxFrequency S θ n →
    2 ≤ n ∧ ∀ q : ℕ, n = q + 1 → ∃ y ∈ RealPlane.pencilSet θ (q + 1),
      ∃ φ : Fin (q + 1) → RealPlane.realLabels,
        angleHarmonic S θ y φ (-(maxFrequency S θ (q + 1) : ℤ)) ≠ 0
def ImagAngleAsymptotic (S : ConnFamily) (θ : RealPlane.openingAngles) {q : ℕ}
    (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → RealPlane.realLabels) : Prop :=
  Tendsto
    (fun s : ℝ => ((Real.exp (-(4 * (maxFrequency S θ (q + 1) : ℝ) * s)) : ℝ) : ℂ) *
      angleFunction S θ y φ (I * (s : ℂ)))
    atTop (𝓝 (angleHarmonic S θ y φ (-(maxFrequency S θ (q + 1) : ℤ))))
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S),
    MaxFrequencyLe d ∧
    (∀ (q : ℕ), 1 ≤ q → ∀ y ∈ RealPlane.pencilSet d.angle (q + 1),
      ∀ φ : Fin (q + 1) → RealPlane.realLabels,
        FiniteHarmonicSum S d.angle y φ ∧ ImagAngleAsymptotic S d.angle y φ) ∧
    MaxFrequencyAttained S d.angle
end YangMills.Construction.EuclideanFunctionals.MaxFrequencyFacts
end
