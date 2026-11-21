import YangMills.Construction.ComplexAnalysis.BanachValuedHolomorphy
import YangMills.Construction.EuclideanFunctionals.FirstFactsOnAReconstruction
import YangMills.Construction.EuclideanFunctionals.OperatorsOfTheForwardTubeOverTheWedge
import YangMills.Construction.EuclideanFunctionals.OperatorsOverThePyramid
import YangMills.Construction.EuclideanFunctionals.ScalarMeasuresOfTheJointSpectralMeasure
import YangMills.Construction.ForwardTube.ClosedTubeAndShiftedTuples
import Mathlib
set_option autoImplicit false
open ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
namespace SpectralPoint
def reflectConj (ζ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  Fin.snoc (α := fun _ => ℂ) (fun i => -conj (spatialComplex ζ i)) (conj (ζ 3))
def ofRealPoint (x : R4) : Fin 4 → ℂ := fun i => (x i : ℂ)
def planeEmbed (u : ℂ × ℂ) : Fin 4 → ℂ := ![u.2, 0, 0, u.1]
end SpectralPoint
namespace ConeSemigroup
open HilbertSpaceBasics (ofBounded)
open SpectralPoint
def statement : Prop :=
  ∀ {s : SharpScale} {𝒞 : ConnFamily} (σ : EuclidFunctionalWithRecon s 𝒞), σ.ConeCondition →
    (∀ ζ : Fin 4 → ℂ, 0 ≤ coneMargin ζ → ‖σ.coneOp ζ‖ ≤ 1) ∧
    (∀ ζ ζ' : Fin 4 → ℂ, 0 ≤ coneMargin ζ → 0 ≤ coneMargin ζ' →
      0 ≤ coneMargin (ζ + ζ') ∧ σ.coneOp ζ * σ.coneOp ζ' = σ.coneOp (ζ + ζ')) ∧
    (∀ ζ : Fin 4 → ℂ, 0 ≤ coneMargin ζ →
      coneMargin (reflectConj ζ) = coneMargin ζ ∧ 0 ≤ coneMargin (reflectConj ζ) ∧
        star (σ.coneOp ζ) = σ.coneOp (reflectConj ζ)) ∧
    (∀ ζ : Fin 4 → ℂ, 0 ≤ coneMargin ζ →
      σ.coneOp ζ σ.recon.vac = σ.recon.vac) ∧
    (∀ x : R4, 0 ≤ x 3 →
      coneMargin (ofRealPoint x) = x 3 ∧ 0 ≤ coneMargin (ofRealPoint x) ∧
        σ.coneOp (ofRealPoint x) =
          σ.heatSemigroup (x 3) * σ.spatialShiftOp (fun i => x i.castSucc) ∧
        ∀ G : finCombIn upperHalf,
          σ.coneOp (ofRealPoint x) (σ.recon.cls G) =
            readClass σ.recon.cls ((EuclidMotion.transl x).actFree G.1)) ∧
    IsClosed {ζ : Fin 4 → ℂ | 0 ≤ coneMargin ζ} ∧
    (∀ φ : σ.space,
      ContinuousOn (fun ζ => σ.coneOp ζ φ) {ζ : Fin 4 → ℂ | 0 ≤ coneMargin ζ}) ∧
    (∀ ζ₀ : Fin 4 → ℂ, 0 < coneMargin ζ₀ →
      ∃ T : PowerSeries.MultiIndex 4 → σ.space →L[ℂ] σ.space,
        (∀ γ, ‖T γ‖ ≤ (γ.order.factorial : ℝ) * (coneMargin ζ₀ ^ γ.order)⁻¹ / (γ.factorial : ℝ)) ∧
        ∀ h : Fin 4 → ℂ, ∑ i, ‖h i‖ < coneMargin ζ₀ →
          0 < coneMargin (ζ₀ + h) ∧
          Summable (fun γ => ‖PowerSeries.MultiIndex.monomial h γ • T γ‖) ∧
          HasSum (fun γ => PowerSeries.MultiIndex.monomial h γ • T γ) (σ.coneOp (ζ₀ + h))) ∧
    IsOpen {ζ : Fin 4 → ℂ | 0 < coneMargin ζ} ∧
    BanachValued.IsOperatorHolomorphicOn (n := 4) {ζ : Fin 4 → ℂ | 0 < coneMargin ζ}
      σ.coneOp ∧
    (∀ u : ℂ × ℂ,
      (0 ≤ coneMargin (planeEmbed u) ↔ u ∈ ForwardTube.closedForwardTube) ∧
      (u ∈ ForwardTube.closedForwardTube →
        σ.coneOp (planeEmbed u) =
            σ.jointMeasure.integralOpOn SpectralPoint.pyramid (fun q =>
              Complex.exp (-(u.1 * (SpectralPoint.energyOf q.1 : ℂ)) +
                Complex.I * u.2 * (SpectralPoint.momentumOf q.1 0 : ℂ))) ∧
          ofBounded (σ.coneOp (planeEmbed u)) = σ.tubeOp u))
end ConeSemigroup
end YangMills.Construction.EuclideanFunctionals
