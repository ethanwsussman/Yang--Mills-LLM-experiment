import YangMills.Construction.HilbertSpace.CommutingSemigroupGroupPairs
import YangMills.Construction.TwoPoints.PlaneKernelOfAForm
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace YangMills.Construction
namespace TwoPoints
def energyDecay (t : ℝ) (p : SpectralCalculus.SpectralPlane) : ℝ := Real.exp (-t * (p.1 : ℝ))
structure IsAveragedKernelSpectralMeasure
    (S : (InfiniteLattice.AmbientSpace → ℂ) → (InfiniteLattice.AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) (n : InfiniteLattice.AmbientSpace)
    (μ : Measure SpectralCalculus.SpectralPlane) : Prop where
  lintegral_decay_lt_top : ∀ t : ℝ≥0, 0 < t → ∫⁻ p, ENNReal.ofReal (energyDecay t p) ∂μ < ∞
  kernel_eq_integral : ∀ t : ℝ≥0, 0 < t → ∀ s : ℝ,
    transverseAveragedKernel S φ (planeCoords ((t : ℝ) • n + s • planePerp n)) =
      integralWrt μ (SpectralCalculus.spectralCharacter t s)
def averagedKernelSpectralMeasure
    (S : (InfiniteLattice.AmbientSpace → ℂ) → (InfiniteLattice.AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) (n : InfiniteLattice.AmbientSpace) :
    Measure SpectralCalculus.SpectralPlane :=
  Classical.epsilon (IsAveragedKernelSpectralMeasure S φ n)
def decayTransform
    (S : (InfiniteLattice.AmbientSpace → ℂ) → (InfiniteLattice.AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) (n : InfiniteLattice.AmbientSpace) (t : ℝ) : ℝ :=
  ∫ p, energyDecay t p ∂(averagedKernelSpectralMeasure S φ n)
def axisDecayTransform
    (S : (InfiniteLattice.AmbientSpace → ℂ) → (InfiniteLattice.AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) : ℝ → ℝ :=
  decayTransform S φ (PeriodicLattice.coordVec 3)
def diagDecayTransform
    (S : (InfiniteLattice.AmbientSpace → ℂ) → (InfiniteLattice.AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) : ℝ → ℝ :=
  decayTransform S φ diagNormalPlus
end TwoPoints
end YangMills.Construction
end
