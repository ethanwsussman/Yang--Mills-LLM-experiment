import YangMills.Construction.EuclideanFunctionals.FirstFactsOnAReconstruction
import YangMills.Construction.EuclideanFunctionals.PlateBoundOfAFunctionalWithReconstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open BorelSpectral
open SpectralPoint (IsUnitVec3)
open RealPlane
variable {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
  {H' : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  (R' : OSReconstruction H' S)
def MapsClassesTo (V : σ.space →ₗ[ℂ] H') : Prop :=
  ∀ F : finCombIn upperHalf, V (σ.recon.cls F) = R'.cls F
def UniqueUnitaryEquiv : Prop :=
  ∃ (V : σ.space →ₗ[ℂ] H') (hV : OperatorTransport.IsUnitaryMap V),
    MapsClassesTo σ R' V ∧
    (∀ W : σ.space →ₗ[ℂ] H', OperatorTransport.IsUnitaryMap W →
      MapsClassesTo σ R' W → W = V) ∧
    OperatorTransport.conjOp hV σ.recon.ham = R'.ham ∧
    (∀ j, OperatorTransport.conjOp hV (σ.recon.mom j) = R'.mom j) ∧
    ∀ Δ : BorelSubsets SpectralPoint.EMPoints,
      ((hamMomMeasure R'.ham R'.mom Δ : H' →L[ℂ] H') : H' →ₗ[ℂ] H') =
        σ.jointMeasure.unitaryPushforward hV Δ
def SameSpectralNullSets : Prop :=
  (∀ Δ : BorelSubsets SpectralPoint.EMPoints,
    hamMomMeasure R'.ham R'.mom Δ = 0 ↔ σ.jointMeasure Δ = 0) ∧
  (∀ n : Fin 3 → ℝ, IsUnitVec3 n →
    ((σ.withRecon R').HamGeAbsDirMomentum n ↔
      σ.HamGeAbsDirMomentum n)) ∧
  ((σ.withRecon R').ConeCondition ↔ σ.ConeCondition)
def SameHeightNormsAndProductBound : Prop :=
  (∀ c : ℝ, 0 < c → ∀ F ∈ finCombIn {y | c < y 3},
    heightNorm (σ.withRecon R') c F = heightNorm σ c F ∧
    heightNorm σ c F =
      (osForm S (pullDown c F) (pullDown c F)).re ^ (1 / 2 : ℝ)) ∧
  ∀ {p c : ℝ} (hp : 0 < p) (hc : c ∈ productBoundFractions),
    (ProductBoundWithExponent σ hp hc ↔
      ProductBoundWithExponent (σ.withRecon R') hp hc) ∧
    ∀ φ ∈ realLabels, ∀ C : ℝ,
      ProductBoundWith σ hp hc φ C ↔ ProductBoundWith (σ.withRecon R') hp hc φ C
namespace ReconUnique
def statement : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S)
    (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (R' : OSReconstruction H' S),
    UniqueUnitaryEquiv σ R' ∧ SameSpectralNullSets σ R' ∧ SameHeightNormsAndProductBound σ R'
end ReconUnique
end YangMills.Construction.EuclideanFunctionals
