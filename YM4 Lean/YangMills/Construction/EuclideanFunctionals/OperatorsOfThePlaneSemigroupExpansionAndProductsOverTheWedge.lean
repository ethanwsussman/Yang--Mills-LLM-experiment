import YangMills.Construction.EuclideanFunctionals.FormsOfTheOperatorsOverTheWedge
import YangMills.Construction.EuclideanFunctionals.SignsOfTheCalculusOfAProjectionValuedMeasure
import YangMills.Construction.RotationInvariance.ApertureTimeGapsAndComplexAnalysisInThePlane
import YangMills.Construction.RotationInvariance.DiscsMotionsAndComplexPositionsOfThePlane
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
namespace SpectralPoint
def expansionKernel (m n : ℕ) (u : ℂ × ℂ) (q : EPlanePoints) : ℂ :=
  (lightConePlus q : ℂ) ^ m * (lightConeMinus q : ℂ) ^ n * planeExpKernel u q
end SpectralPoint
namespace EuclidFunctionalWithRecon
open SpectralPoint
variable {s : SharpScale} {𝒞 : ConnFamily} (σ : EuclidFunctionalWithRecon s 𝒞)
def expansionOp (u : ℂ × ℂ) (m n : ℕ) : σ.space →L[ℂ] σ.space :=
  ((-1 : ℂ) ^ (m + n) / ((m.factorial : ℂ) * (n.factorial : ℂ))) •
    σ.wedgeOp fun q => expansionKernel m n u q.1
def tubeWord (φ : σ.space) :
    (r : ℕ) → (Fin (r + 1) → σ.space →L[ℂ] σ.space) → (Fin r → ℂ × ℂ) → σ.space
  | 0, B, _ => B 0 φ
  | r + 1, B, u =>
    B 0 (σ.wedgeIntegralOp (u 0) (tubeWord φ r (Fin.tail B) (Fin.tail u)))
end EuclidFunctionalWithRecon
namespace TubeSemigroup
open HilbertSpaceBasics (ofBounded)
open ResolvedOps (expComplex)
open SpectralPoint
open EuclidFunctionalWithRecon
variable {s : SharpScale} {𝒞 : ConnFamily} (σ : EuclidFunctionalWithRecon s 𝒞)
def BoundedAndSupported : Prop :=
  (∀ u ∈ ForwardTube.closedForwardTube, ∀ q ∈ wedge.1, ‖planeExpKernel u q‖ ≤ 1) ∧
  (∀ u ∈ ForwardTube.closedForwardTube, σ.tubeOp u = ofBounded (σ.wedgeIntegralOp u)) ∧
  σ.planeMeasure ⟨wedge.1ᶜ, wedge.2.compl⟩ = 0
def ContractionSemigroup : Prop :=
  σ.wedgeIntegralOp 0 = 1 ∧
  ∀ u ∈ ForwardTube.closedForwardTube, ∀ u' ∈ ForwardTube.closedForwardTube,
    u + u' ∈ ForwardTube.closedForwardTube ∧ ForwardTube.tubeStar u ∈ ForwardTube.closedForwardTube ∧
    ‖σ.wedgeIntegralOp u‖ ≤ 1 ∧
    σ.wedgeIntegralOp u * σ.wedgeIntegralOp u' = σ.wedgeIntegralOp (u + u') ∧
    star (σ.wedgeIntegralOp u) = σ.wedgeIntegralOp (ForwardTube.tubeStar u) ∧
    σ.wedgeIntegralOp u σ.recon.vac = σ.recon.vac
def StrongContinuity : Prop :=
  ∀ φ : σ.space, ContinuousOn (fun u => σ.wedgeIntegralOp u φ) ForwardTube.closedForwardTube
def TubeExpansion : Prop :=
  (∀ u ∈ ForwardTube.forwardTube,
    (∀ m n : ℕ, Continuous (expansionKernel m n u) ∧
      (∃ K : ℝ, ∀ q ∈ wedge.1, ‖expansionKernel m n u q‖ ≤ K) ∧
      ‖σ.expansionOp u m n‖ ≤
        ((ForwardTube.lightConePlus u).re ^ m)⁻¹ * ((ForwardTube.lightConeMinus u).re ^ n)⁻¹) ∧
    ∀ h : ℂ × ℂ, ‖ForwardTube.lightConePlus h‖ < (ForwardTube.lightConePlus u).re →
      ‖ForwardTube.lightConeMinus h‖ < (ForwardTube.lightConeMinus u).re →
      u + h ∈ ForwardTube.forwardTube ∧
      Summable (fun b : ℕ × ℕ =>
        ‖(ForwardTube.lightConePlus h ^ b.1 * ForwardTube.lightConeMinus h ^ b.2) •
          σ.expansionOp u b.1 b.2‖) ∧
      HasSum (fun b : ℕ × ℕ =>
        (ForwardTube.lightConePlus h ^ b.1 * ForwardTube.lightConeMinus h ^ b.2) •
          σ.expansionOp u b.1 b.2)
        (σ.wedgeIntegralOp (u + h))) ∧
  ForwardTube.HolomorphicVectorOnTuples {x : Fin 1 → ℂ × ℂ | x 0 ∈ ForwardTube.forwardTube}
    fun x => σ.wedgeIntegralOp (x 0)
def RealPoints : Prop :=
  ∀ y : RealPlane, 0 ≤ y 0 →
    σ.wedgeIntegralOp (ForwardTube.embedPlane y) =
      expComplex σ.recon.ham ((y 0 : ℝ) : ℂ) *
        spatialTranslOp σ.jointMeasure (y 1 • PeriodicLattice.coordVec 0) ∧
    ∀ G : finCombIn upperHalf,
      (planeShift y).actFree G.1 ∈ finCombIn upperHalf ∧
      σ.wedgeIntegralOp (ForwardTube.embedPlane y) (σ.recon.cls G) =
        readClass σ.recon.cls ((planeShift y).actFree G.1)
def WordBounds : Prop :=
  ∀ (r : ℕ) (B : Fin (r + 1) → σ.space →L[ℂ] σ.space) (φ : σ.space),
    (∀ u ∈ pi univ fun _ : Fin r => ForwardTube.closedForwardTube,
      ‖σ.tubeWord φ r B u‖ ≤ (∏ i, ‖B i‖) * ‖φ‖) ∧
    ContinuousOn (σ.tubeWord φ r B) (pi univ fun _ : Fin r => ForwardTube.closedForwardTube) ∧
    ForwardTube.HolomorphicVectorOnTuples (pi univ fun _ : Fin r => ForwardTube.forwardTube)
      (σ.tubeWord φ r B)
def Holds : Prop :=
  ∀ (s : SharpScale) (𝒞 : ConnFamily) (σ : EuclidFunctionalWithRecon s 𝒞),
    σ.ConeCondition →
      BoundedAndSupported σ ∧ ContractionSemigroup σ ∧ StrongContinuity σ ∧
      TubeExpansion σ ∧ RealPoints σ ∧ WordBounds σ
end TubeSemigroup
end YangMills.Construction.EuclideanFunctionals
