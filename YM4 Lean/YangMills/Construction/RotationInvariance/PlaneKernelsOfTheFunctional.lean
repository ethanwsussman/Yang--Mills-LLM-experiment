import YangMills.Construction.Conventions.RealPowerAndLogarithm
import YangMills.Construction.ForwardTube.ShiftedTubesInLightConeCoordinates
import YangMills.Construction.RotationInvariance.OrderedTuplesOfFunctionsAndTheCosineOfAnAperture
import YangMills.Construction.RotationInvariance.RadialBumpsAtALengthAndTheirFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane Filter
namespace ForwardTube
def rotatedTubePow (θ : rightAngleMultiples) (q : ℕ) : Set (Fin q → ℂ × ℂ) :=
  Set.univ.pi fun _ => rotatedForwardTube θ
def unrotate (θ : rightAngleMultiples) {q : ℕ} (v : Fin q → ℂ × ℂ) :
    Fin q → ℂ × ℂ :=
  fun i => complexBoost ((-(θ : ℝ) : ℝ) : ℂ) (v i)
end ForwardTube
namespace EuclideanFunctionals
open ForwardTube
def centeredFnAtProducts (S : ConnFamily) {n : ℕ} (f : Fin n → RealPlane → ℂ)
    (ψ : Fin n → realLabels) : ℂ :=
  centeredFnFree S (complexTuple fun i => productFunction (f i) (ψ i))
def differenceIntegral {q : ℕ} (f : Fin (q + 1) → RealPlane → ℂ)
    (g : (Fin q → ℂ × ℂ) → ℂ) : ℂ :=
  profileIntegral f fun y => g (embedPlaneTuple (successiveDifferences y))
structure IsPlaneKernel (S : ConnFamily) {q : ℕ} (ψ : Fin (q + 1) → realLabels)
    (K : (Fin q → ℂ × ℂ) → ℂ) : Prop where
  holomorphic : HolomorphicOnTuples (forwardTubePow q) K
  integral_eq : ∀ f : Fin (q + 1) → RealPlane → ℂ, (∀ i, f i ∈ complexProfiles) →
    FunsTimeSeparated f → centeredFnAtProducts S f ψ = differenceIntegral f K
def planeKernel (S : ConnFamily) {q : ℕ} (ψ : Fin (q + 1) → realLabels) :
    (Fin q → ℂ × ℂ) → ℂ :=
  Classical.epsilon (IsPlaneKernel S ψ)
namespace PlaneKernelProps
variable {m : SharpScale} {S : ConnFamily}
def BoundedByMarginPow (d : PlaneDataWithAperture m S) {q : ℕ}
    (ψ : Fin (q + 1) → realLabels) : Prop :=
  ∀ v ∈ forwardTubePow q, ‖planeKernel S ψ v‖ ≤
    (∏ i, d.base.labelConst (ψ i)) *
      RealPower.rpowPos (tubeMargin v) (-(d.base.expo * ((q + 1 : ℕ) : ℝ)))
def RealOnRealLocus (S : ConnFamily) {q : ℕ} (ψ : Fin (q + 1) → realLabels) : Prop :=
  realLocus (forwardTubePow q) = embedPlaneTuple '' {y | ∀ i, y i ∈ RealPlane.openRightHalf} ∧
    ∀ v ∈ realLocus (forwardTubePow q), (planeKernel S ψ v).im = 0
def TendstoFromMollifiers (d : PlaneDataWithAperture m S) {q : ℕ}
    (ψ : Fin (q + 1) → realLabels) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ ρ : ℕ+ → RealPlane → ℝ, d.IsRadialMollifier ε ρ →
    ∀ C : Set (Fin q → ℂ × ℂ), IsCompact C → C ⊆ shiftedForwardTubePow q ε →
      TendstoUniformlyOn (d.mollifiedKernel ε ρ fun i => (ψ i : RealPlane → ℝ))
        (planeKernel S ψ) atTop C
def RotatedFrameRep (S : ConnFamily) {q : ℕ} (ψ : Fin (q + 1) → realLabels)
    (θ : rightAngleMultiples) : Prop :=
  (∀ v ∈ rotatedTubePow θ q, unrotate θ v ∈ forwardTubePow q) ∧
    HolomorphicOnTuples (rotatedTubePow θ q)
      (fun v => planeKernel S ψ (unrotate θ v)) ∧
    ∀ f : Fin (q + 1) → RealPlane → ℂ, (∀ i, f i ∈ complexProfiles) →
      FunsDirectionSeparated θ f →
      centeredFnAtProducts S f ψ =
        differenceIntegral f fun v => planeKernel S ψ (unrotate θ v)
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S) (q : ℕ), 1 ≤ q →
    ∀ ψ : Fin (q + 1) → realLabels,
      IsPlaneKernel S ψ (planeKernel S ψ) ∧
      (∀ K : (Fin q → ℂ × ℂ) → ℂ, IsPlaneKernel S ψ K →
        ∀ v ∈ forwardTubePow q, K v = planeKernel S ψ v) ∧
      BoundedByMarginPow d ψ ∧
      RealOnRealLocus S ψ ∧
      TendstoFromMollifiers d ψ ∧
      ∀ θ : rightAngleMultiples, RotatedFrameRep S ψ θ
end PlaneKernelProps
end EuclideanFunctionals
end YangMills.Construction
end
