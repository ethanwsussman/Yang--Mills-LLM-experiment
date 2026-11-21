import YangMills.Construction.RotationInvariance.HarmonicsOfTheFunctionOfTheAngle
import Mathlib
set_option autoImplicit false
open Complex (I)
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals.PencilHarmonics
def harmonicBound {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) (q : ℕ) : ℝ :=
  d.base.expo * ((q + 1 : ℕ) : ℝ) / 4
def VanishAbove {m : SharpScale} {S : ConnFamily}
    (d : PlaneDataWithAperture m S) {q : ℕ}
    (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → realLabels) : Prop :=
  ∀ n : ℤ, harmonicBound d q < |(n : ℝ)| → angleHarmonic S d.angle y φ n = 0
def FiniteFourierExpansion {m : SharpScale} {S : ConnFamily}
    (d : PlaneDataWithAperture m S) {q : ℕ}
    (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → realLabels) : Prop :=
  ∀ t s : ℝ,
    angleFunction S d.angle y φ ((t : ℂ) + I * (s : ℂ)) =
      ∑ n ∈ Finset.Icc (-⌊harmonicBound d q⌋) ⌊harmonicBound d q⌋,
        angleHarmonic S d.angle y φ n *
          Complex.exp (4 * I * (n : ℂ) * ((t : ℂ) + I * (s : ℂ)))
def TranslationInvariantHarmonics (S : ConnFamily) (θ₀ : openingAngles) {q : ℕ}
    (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → realLabels) : Prop :=
  ∀ u : RealPlane,
    (fun i => y i + u) ∈ pencilSet θ₀ (q + 1) ∧
      ∀ n : ℤ, angleHarmonic S θ₀ (fun i => y i + u) φ n = angleHarmonic S θ₀ y φ n
def ConjSymmetricHarmonics (S : ConnFamily) (θ₀ : openingAngles) {q : ℕ}
    (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → realLabels) : Prop :=
  ∀ n : ℤ, angleHarmonic S θ₀ y φ (-n) = (starRingEnd ℂ) (angleHarmonic S θ₀ y φ n)
def HarmonicsOnHorizontalLines (S : ConnFamily) (θ₀ : openingAngles) {q : ℕ}
    (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → realLabels) : Prop :=
  (∀ s : ℝ, BddAbove (Set.range fun t : ℝ =>
    ‖angleFunction S θ₀ y φ ((t : ℂ) + I * (s : ℂ))‖)) ∧
  ∀ (n : ℤ) (s : ℝ),
    angleHarmonic S θ₀ y φ n =
        ((2 / Real.pi : ℝ) : ℂ) *
          ∫ t : ℝ in (0 : ℝ)..(Real.pi / 2),
            angleFunction S θ₀ y φ ((t : ℂ) + I * (s : ℂ)) *
              Complex.exp (-(4 * I * (n : ℂ) * ((t : ℂ) + I * (s : ℂ)))) ∧
      ‖angleHarmonic S θ₀ y φ n‖ ≤
        Real.exp (4 * (n : ℝ) * s) *
          ⨆ t : ℝ, ‖angleFunction S θ₀ y φ ((t : ℂ) + I * (s : ℂ))‖
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S) (q : ℕ), 1 ≤ q →
    ∀ y ∈ pencilSet d.angle (q + 1), ∀ φ : Fin (q + 1) → realLabels,
      VanishAbove d y φ ∧
      FiniteFourierExpansion d y φ ∧
      TranslationInvariantHarmonics S d.angle y φ ∧
      ConjSymmetricHarmonics S d.angle y φ ∧
      HarmonicsOnHorizontalLines S d.angle y φ
end EuclideanFunctionals.PencilHarmonics
end YangMills.Construction
end
