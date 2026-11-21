import YangMills.Construction.RotationInvariance.FunctionOnTheUnionOfTubes
import YangMills.Construction.RotationInvariance.TopFrequencyOfTheHarmonics
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
def HasHarmonicExpansion (S : ConnFamily) (θ : RealPlane.openingAngles) {q : ℕ}
    (φ : Fin (q + 1) → RealPlane.realLabels) (c : ℤ → (Fin (q + 1) → ℂ × ℂ) → ℂ) : Prop :=
  ∀ z ∈ ForwardTube.orderedTubeUnion q, ∀ s : ℝ,
    tubeUnionFunction S φ (ForwardTube.imagBoostTuple s z) =
      ∑ h ∈ Finset.Icc (-(maxFrequency S θ (q + 1) : ℤ)) (maxFrequency S θ (q + 1) : ℤ),
        c h z * Complex.exp (-(4 * (h : ℂ) * (s : ℂ)))
def harmonicFamily (S : ConnFamily) (θ : RealPlane.openingAngles) {q : ℕ}
    (φ : Fin (q + 1) → RealPlane.realLabels) : ℤ → (Fin (q + 1) → ℂ × ℂ) → ℂ :=
  Classical.epsilon (HasHarmonicExpansion S θ φ)
def tubeUnionHarmonic (S : ConnFamily) (θ : RealPlane.openingAngles) {q : ℕ}
    (φ : Fin (q + 1) → RealPlane.realLabels) (h : ℤ) (z : Fin (q + 1) → ℂ × ℂ) : ℂ :=
  if |h| ≤ (maxFrequency S θ (q + 1) : ℤ) then harmonicFamily S θ φ h z else 0
namespace TubeUnionHarmonics
variable {q : ℕ}
def UniqueExpansion (S : ConnFamily) (θ : RealPlane.openingAngles)
    (φ : Fin (q + 1) → RealPlane.realLabels) : Prop :=
  HasHarmonicExpansion S θ φ (harmonicFamily S θ φ) ∧
    (∀ c : ℤ → (Fin (q + 1) → ℂ × ℂ) → ℂ, HasHarmonicExpansion S θ φ c →
      ∀ h : ℤ, |h| ≤ (maxFrequency S θ (q + 1) : ℤ) →
        ∀ z ∈ ForwardTube.orderedTubeUnion q, c h z = harmonicFamily S θ φ h z) ∧
    ∀ h : ℤ, |h| ≤ (maxFrequency S θ (q + 1) : ℤ) →
      ForwardTube.HolomorphicOnTuples (ForwardTube.orderedTubeUnion q) (harmonicFamily S θ φ h)
def EqAngleHarmonicOnPencils (S : ConnFamily) (θ : RealPlane.openingAngles)
    (φ : Fin (q + 1) → RealPlane.realLabels) : Prop :=
  ∀ y ∈ RealPlane.pencilSet θ (q + 1), ∀ h : ℤ,
    tubeUnionHarmonic S θ φ h (ForwardTube.embedPlaneTuple y) = angleHarmonic S θ y φ h
def SymmetryAndMultilinearity (S : ConnFamily) (θ : RealPlane.openingAngles)
    (φ : Fin (q + 1) → RealPlane.realLabels) : Prop :=
  ∀ h : ℤ, ∀ z ∈ ForwardTube.orderedTubeUnion q,
    (∀ σ : Equiv.Perm (Fin (q + 1)),
      tubeUnionHarmonic S θ (RealPlane.permuteTuple σ φ) h (RealPlane.permuteTuple σ z) =
        tubeUnionHarmonic S θ φ h z) ∧
    (∀ u : ℂ × ℂ,
      tubeUnionHarmonic S θ φ h (ForwardTube.addConstTuple z u) =
        tubeUnionHarmonic S θ φ h z) ∧
    (∀ s : ℝ,
      tubeUnionHarmonic S θ φ h (ForwardTube.imagBoostTuple s z) =
        Complex.exp (-(4 * (h : ℂ) * (s : ℂ))) * tubeUnionHarmonic S θ φ h z) ∧
    RealPlane.IsMultilinearLabels fun ψ : Fin (q + 1) → RealPlane.realLabels =>
      tubeUnionHarmonic S θ ψ h z
def HarmonicSumEq (S : ConnFamily) (θ : RealPlane.openingAngles)
    (φ : Fin (q + 1) → RealPlane.realLabels) : Prop :=
  ∀ z ∈ ForwardTube.orderedTubeUnion q,
    ∑ h ∈ Finset.Icc (-(maxFrequency S θ (q + 1) : ℤ)) (maxFrequency S θ (q + 1) : ℤ),
      tubeUnionHarmonic S θ φ h z = tubeUnionFunction S φ z
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S) (q : ℕ), 1 ≤ q →
    ∀ φ : Fin (q + 1) → RealPlane.realLabels,
      UniqueExpansion S d.angle φ ∧
      EqAngleHarmonicOnPencils S d.angle φ ∧
      SymmetryAndMultilinearity S d.angle φ ∧
      HarmonicSumEq S d.angle φ
end TubeUnionHarmonics
end YangMills.Construction.EuclideanFunctionals
end
