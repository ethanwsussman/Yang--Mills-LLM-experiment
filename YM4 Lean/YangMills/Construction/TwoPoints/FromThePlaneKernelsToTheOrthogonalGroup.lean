import YangMills.Construction.TwoPoints.RotationInvarianceOfThePlaneKernel
import YangMills.Construction.TwoPoints.ThirdPropertyAndFamiliesOfSpectralMeasures
import YangMills.Construction.TwoPoints.TransverseReflectionAndTheSixCoordinatePlanes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
def permConjRotation (w : Equiv.Perm AmbientSpace) (t : ℝ) (ξ : AmbientSpace) : AmbientSpace :=
  w (rotateInPlane t (w⁻¹ ξ))
def rotationInCoordPlane (i j : Fin 4) (t : ℝ) (x : AmbientSpace) : AmbientSpace :=
  Function.update (Function.update x i (Real.cos t * x i - Real.sin t * x j)) j
    (Real.sin t * x i + Real.cos t * x j)
def radialProfile (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (r : ℝ) : ℝ :=
  formKernel S (r • coordVec 3)
def IsRealAnalyticOnIoi (s : ℝ → ℝ) : Prop :=
  YangMills.Construction.Coordinates.ComplexCoordinates.IsRealAnalyticIn (N := 1) (N' := 1)
    (YangMills.Construction.Coordinates.ComplexCoordinates.realLocus 1 ∩ {z | 0 < (z 0).re})
    fun z _ => ((s (z 0).re : ℝ) : ℂ)
def HasRadialProfile (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (s : ℝ → ℝ) : Prop :=
  ∀ f ∈ compactC1Real, ∀ g ∈ compactC1Real, DisjointSupports f g →
    (S f g : ℂ) = lebesgueIntegral fun y : AmbientSpace => lebesgueIntegral fun x : AmbientSpace =>
      f x * g y * (s (euclidNorm (x - y)) : ℂ)
def PlaneKernelsToOrthogonalInvariance.Statement : Prop :=
  ∀ (L : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ),
    IsDisjointForm S → IsAdmissibleForm L S →
    (∀ φ ∈ transProfiles, IsRotationInvariantAveragedKernel S φ) →
    (∀ ξ : AmbientSpace, ξ ≠ 0 → ∀ t : ℝ,
      formKernel S (rotateInPlane t ξ) = formKernel S ξ) ∧
    (∀ i j : Fin 4, i ≠ j → ∀ w ∈ hyperoctahedralPerms, IsAxisPermutation w →
      w (coordVec 3) = coordVec i → w (coordVec 0) = coordVec j →
        ∀ t : ℝ, permConjRotation w t = rotationInCoordPlane i j t ∧
          ∀ ξ : AmbientSpace, ξ ≠ 0 →
            formKernel S (permConjRotation w t ξ) = formKernel S ξ) ∧
    (IsRealAnalyticOnIoi (radialProfile S) ∧
      ∀ ξ : AmbientSpace, ξ ≠ 0 → formKernel S ξ = radialProfile S (euclidNorm ξ)) ∧
    HasRadialProfile S (radialProfile S) ∧
    ∀ R : Matrix.orthogonalGroup (Fin 4) ℝ, ∀ f ∈ compactC1Real, ∀ g ∈ compactC1Real,
      DisjointSupports f g →
        S (rotateFun R f) (rotateFun R g) = S f g
end YangMills.Construction.TwoPoints
end
