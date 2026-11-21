import YangMills.Construction.TwoPoints.OneFieldSpaceAtAMirror
import YangMills.Construction.TwoPoints.PlaneKernelOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
structure IsRegularAveragedKernel (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) : Prop where
  integrable : ∀ y : Fin 2 → ℝ, y ≠ 0 → MeasureTheory.Integrable fun ζ : Fin 2 → ℝ =>
    ((ofCoords (formKernel S) y ζ : ℝ) : ℂ) * profileCorr φ φ ζ
  im_eq_zero : ∀ y : Fin 2 → ℝ, y ≠ 0 → (transverseAveragedKernel S φ y).im = 0
  continuousOn : ContinuousOn (transverseAveragedKernel S φ) {y | y ≠ 0}
  invariant : ∀ g ∈ dihedralInPlane, ∀ y : Fin 2 → ℝ, y ≠ 0 →
    transverseAveragedKernel S φ (planeCoords (g (embedPlane y))) = transverseAveragedKernel S φ y
def IsRestrictedFormKernel (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) : Prop :=
  ∀ f ∈ cc1Plane, ∀ g ∈ cc1Plane, Disjoint (tsupport f) (tsupport g) →
    restrictedForm S φ f g =
      lebesgueIntegral fun y' : Fin 2 → ℝ => lebesgueIntegral fun y : Fin 2 → ℝ =>
        f y * g y' * transverseAveragedKernel S φ (y' - y)
def normalFrameIntegral (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) (n : AmbientSpace) (f g : (Fin 2 → ℝ) → ℂ) (t s : ℝ) : ℂ :=
  lebesgueIntegral fun b₂ : ℝ => lebesgueIntegral fun a₂ : ℝ =>
    lebesgueIntegral fun b₁ : ℝ => lebesgueIntegral fun a₁ : ℝ =>
      conjFun f (planeCoords (a₁ • n + b₁ • planePerp n)) *
        g (planeCoords (a₂ • n + b₂ • planePerp n)) *
        transverseAveragedKernel S φ
          (planeCoords ((t + a₁ + a₂) • n + (s + b₂ - b₁) • planePerp n))
def SatisfiesNormalFrameFormula (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) (n : AmbientSpace) : Prop :=
  ∀ f ∈ cc1In {y : Fin 2 → ℝ | 0 < euclidDot (planeCoords n) y},
    ∀ g ∈ cc1In {y : Fin 2 → ℝ | 0 < euclidDot (planeCoords n) y},
      ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ,
        ∃ (hf : tensorPlate f φ ∈ halfSpaceDomain n)
          (hg : translateFun (t • n + s • planePerp n) (tensorPlate g φ) ∈ halfSpaceDomain n),
          reflectedForm S n ⟨_, hf⟩ ⟨_, hg⟩ = normalFrameIntegral S φ n f g t s
def AveragedKernelProperties.Statement : Prop :=
  ∀ (St : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ), IsDisjointForm S →
    IsAdmissibleForm St S →
    ∀ φ ∈ transProfiles,
      IsRegularAveragedKernel S φ ∧ IsRestrictedFormKernel S φ ∧
        ∀ n ∈ planeReflectionNormals, SatisfiesNormalFrameFormula S φ n
end YangMills.Construction.TwoPoints
end
