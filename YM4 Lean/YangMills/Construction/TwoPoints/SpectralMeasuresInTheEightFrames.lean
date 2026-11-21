import YangMills.Construction.TwoPoints.OneFieldSpaceAtAMirror
import YangMills.Construction.TwoPoints.SpectralMeasuresOfThePlaneKernel
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace YangMills.Construction
namespace TwoPoints
open SpectralCalculus (SpectralPlane)
open InfiniteLattice (AmbientSpace)
open PeriodicLattice (coordVec)
def positiveHalfPlane (n : AmbientSpace) : Set (Fin 2 → ℝ) := {y | 0 < euclidDot (planeCoords n) y}
def doubleLaplace (n : AmbientSpace) (f : (Fin 2 → ℝ) → ℂ) (z : SpectralPlane) : ℂ :=
  TwoPoints.lebesgueIntegral fun t : ℝ => TwoPoints.lebesgueIntegral fun s : ℝ =>
    f (planeCoords (t • n + s • planePerp n)) *
      Complex.exp (((-t * (z.1 : ℝ) : ℝ) : ℂ) + Complex.I * ((s * z.2 : ℝ) : ℂ))
structure RepresentsDecay (B : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (ψ : (Fin 2 → ℝ) → ℂ)
    (n : AmbientSpace) (μ : Measure SpectralPlane) : Prop where
  isSpectral : IsAveragedKernelSpectralMeasure B ψ n μ
  transform_eq_integral : ∀ t : ℝ, 0 < t → decayTransform B ψ n t = ∫ z, energyDecay t z ∂μ
  transform_eq_kernel : ∀ t : ℝ, 0 < t →
    ((decayTransform B ψ n t : ℝ) : ℂ) = transverseAveragedKernel B ψ (planeCoords (t • n))
def RepresentsPlateNorm (B : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (ψ : (Fin 2 → ℝ) → ℂ)
    (n : AmbientSpace) (μ : Measure SpectralPlane) : Prop :=
  ∀ f ∈ cc1In (positiveHalfPlane n), ∀ hf : tensorPlate f ψ ∈ halfSpaceDomain n,
    ENNReal.ofReal (‖reflectedClass B n ⟨tensorPlate f ψ, hf⟩‖ ^ 2) =
      ∫⁻ z, ‖doubleLaplace n f z‖ₑ ^ 2 ∂μ
structure NormalSpectralData (B : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (ψ : (Fin 2 → ℝ) → ℂ)
    (n : AmbientSpace) : Prop where
  represents : RepresentsDecay B ψ n (averagedKernelSpectralMeasure B ψ n)
  transform_nonneg : ∀ t : ℝ, 0 < t → 0 ≤ decayTransform B ψ n t
  transform_antitoneOn : AntitoneOn (decayTransform B ψ n) (Ioi 0)
  transform_invariant : ∀ g ∈ dihedralInPlane, ∀ t : ℝ, 0 < t →
    decayTransform B ψ (g n) t = decayTransform B ψ n t
  plateNorm : RepresentsPlateNorm B ψ n (averagedKernelSpectralMeasure B ψ n)
  tendsto_total : Tendsto (fun t : ℝ => ENNReal.ofReal (decayTransform B ψ n t)) (𝓝[>] 0)
    (𝓝 (averagedKernelSpectralMeasure B ψ n univ))
  isFinite_weighted : IsFiniteMeasure ((averagedKernelSpectralMeasure B ψ n).withDensity
    fun z => ENNReal.ofReal (energyDecay 1 z))
  sigmaFinite : SigmaFinite (averagedKernelSpectralMeasure B ψ n)
def SpectralMeasuresAtAllNormals.Statement : Prop :=
  ∀ (c : FixedScale) (B : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (ψ : (Fin 2 → ℝ) → ℂ),
    IsDisjointForm B → IsAdmissibleForm c B → ψ ∈ transProfiles →
      (∀ n ∈ planeReflectionNormals, NormalSpectralData B ψ n) ∧
      (∀ t : ℝ, 0 < t →
        decayTransform B ψ (coordVec 3) t = axisDecayTransform B ψ t ∧
        decayTransform B ψ (-coordVec 3) t = axisDecayTransform B ψ t ∧
        decayTransform B ψ (coordVec 0) t = axisDecayTransform B ψ t ∧
        decayTransform B ψ (-coordVec 0) t = axisDecayTransform B ψ t) ∧
      ∀ t : ℝ, 0 < t →
        decayTransform B ψ diagNormalPlus t = diagDecayTransform B ψ t ∧
        decayTransform B ψ (-diagNormalPlus) t = diagDecayTransform B ψ t ∧
        decayTransform B ψ diagNormalMinus t = diagDecayTransform B ψ t ∧
        decayTransform B ψ (-diagNormalMinus) t = diagDecayTransform B ψ t
end TwoPoints
end YangMills.Construction
end
