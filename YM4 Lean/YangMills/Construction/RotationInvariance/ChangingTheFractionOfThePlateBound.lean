import YangMills.Construction.EuclideanFunctionals.TransportOfAReconstructionAndThePlateBoundInACoordinatePlane
import YangMills.Construction.RotationInvariance.ComplexTuplesAndPlaneData
import YangMills.Construction.RotationInvariance.TopFrequencyOfTheHarmonics
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.FractionChange
open YangMills.Construction.ForwardTube
variable {m : SharpScale} {S : ConnFamily}
def productConstantsAt (p c' : ℝ) (C : (RealPlane → ℝ) → ℝ) (φ : RealPlane → ℝ) : ℝ :=
  (1 - 4 * c') ^ (-p) * C φ
def BoundsInTimePlane (σ : EuclidFunctionalWithRecon m S) {p c : ℝ}
    (hp : 0 < p) (hc : c ∈ productBoundFractions) : Prop :=
  ProductBoundWithExponent σ hp hc ∧ ImagePlaneProductBound σ 1 hp hc
def IsProductPlaneData (σ : EuclidFunctionalWithRecon m S) (p : ℝ)
    (C : (RealPlane → ℝ) → ℝ) (c : ℝ) : Prop :=
  ∃ d : ProductPlaneData m S, d.fnl = σ ∧ d.exponent = p ∧ d.fraction = c ∧
    ∀ φ : realLabels, d.labelBound φ = C φ
def IsApertureSettingData (σ : EuclidFunctionalWithRecon m S) (p : ℝ)
    (C : (RealPlane → ℝ) → ℝ) (c' : ℝ) (φ₀ : openingAngles) : Prop :=
  ∃ d : PlaneDataWithAperture m S, d.base.sigma = σ ∧ d.base.expo = p ∧
    d.base.frac = c' ∧ d.angle = φ₀ ∧
    ∀ φ : realLabels, d.base.labelConst φ = productConstantsAt p c' C φ
def SameKernelsAndHarmonics (S₁ S₂ : ConnFamily) (φ₀ : openingAngles) : Prop :=
  (∀ q : ℕ, 1 ≤ q → ∀ φ : Fin (q + 1) → realLabels,
    (∀ v ∈ forwardTubePow q, planeKernel S₁ φ v = planeKernel S₂ φ v) ∧
    ∀ y ∈ pencilSet φ₀ (q + 1),
      angleFunction S₁ φ₀ y φ = angleFunction S₂ φ₀ y φ ∧
      ∀ ν : ℤ, angleHarmonic S₁ φ₀ y φ ν = angleHarmonic S₂ φ₀ y φ ν) ∧
  ∀ n : ℕ, maxFrequency S₁ φ₀ n = maxFrequency S₂ φ₀ n
def Holds : Prop :=
  (∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S) (p : ℝ)
      (C : (RealPlane → ℝ) → ℝ) (c : ℝ) (h : ProductBoundHolds σ p C c),
    (∀ c' ∈ productBoundFractions, ProductBoundHolds σ p (productConstantsAt p c' C) c') ∧
    (∀ (c' : ℝ) (hc' : c' ∈ productBoundFractions),
      BoundsInTimePlane σ h.pos_exponent hc') ∧
    (σ.ConeCondition →
      IsProductPlaneData σ p C c ∧
      ∀ (c' : ℝ) (hc' : c' ∈ productBoundFractions),
        (∀ φ₀ : openingAngles, IsApertureSettingData σ p C c' φ₀) ∧
        BoundsInTimePlane σ h.pos_exponent hc' ∧
        ProductBoundHolds σ p (productConstantsAt p c' C) c')) ∧
  ∀ (m : SharpScale) (S₁ S₂ : ConnFamily), ProductPlaneData m S₁ → ProductPlaneData m S₂ →
    centeredFnFree S₁ = centeredFnFree S₂ →
    ∀ φ₀ : openingAngles, SameKernelsAndHarmonics S₁ S₂ φ₀
end YangMills.Construction.EuclideanFunctionals.FractionChange
end
