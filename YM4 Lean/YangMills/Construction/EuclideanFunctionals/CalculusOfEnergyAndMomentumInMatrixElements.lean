import YangMills.Construction.EuclideanFunctionals.FirstFactsOnAReconstruction
import YangMills.Construction.EuclideanFunctionals.ScalarMeasuresOfTheJointSpectralMeasure
import YangMills.Construction.MeasureTheory.FourMeasureIntegral
import YangMills.Construction.SpectralMeasures.ProjectionValued
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open HilbertSpaceBasics (UnboundedOp)
open BorelSpectral
open ResolvedOps (StronglyCommute IsJointSpectralMeasure IsDiagonalized)
open SelfAdjointFunctions (expI)
namespace SpectralPoint
def negEnergyBorel : BorelSubsets EMPoints :=
  ⟨{p | energyOf p < 0}, measurableSet_lt measurable_energyOf measurable_const⟩
theorem dotR4_spatialEmbed (v q : Fin 3 → ℝ) : dotR4 (spatialEmbed v) q = dot3 v q := by
  simp [dotR4, spatialEmbed]
end SpectralPoint
namespace EuclidFunctionalWithRecon
open SpectralPoint
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
def hamAndMomenta : Fin 4 → UnboundedOp σ.space :=
  hamMomFamily σ.recon.ham σ.recon.mom
def JointMeasureOfHamMom (φ ψ : σ.space) : Prop :=
  (∀ k, IsDiagonalized (σ.hamAndMomenta k)) ∧
    (∀ k, OperatorTransport.IsSelfAdjointUnbounded (σ.hamAndMomenta k)) ∧
    (∀ j k, j ≠ k → StronglyCommute (σ.hamAndMomenta j) (σ.hamAndMomenta k)) ∧
    (∀ v : Fin 3 → ℝ, σ.spatialShiftOp v =
      expI (σ.recon.mom 0) (v 0) *
        expI (σ.recon.mom 1) (v 1) *
          expI (σ.recon.mom 2) (v 2)) ∧
    IsJointSpectralMeasure σ.hamAndMomenta σ.jointMeasure ∧
    σ.pairSpectralMeasure φ ψ = σ.jointMeasure.matrixCoeff φ ψ ∧
    ∃ h : Spectral.IsSpectralMeasure
        (fun Δ : Spectral.BorelSubset EMPoints => σ.jointMeasure Δ),
      ∀ Δ : Spectral.BorelSubset EMPoints,
        (Spectral.ProjValuedMeasure.mk _ h).form φ ψ Δ =
          σ.pairSpectralMeasure φ ψ Δ
def PairMeasurePolarization (φ ψ : σ.space) : Prop :=
  (∀ B : BorelSubsets EMPoints, σ.pairSpectralMeasure φ ψ B =
    (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4, (Complex.I ^ k)⁻¹ *
      (((σ.spectralMeasureAt (φ + Complex.I ^ k • ψ)).real B.1 : ℝ) : ℂ)) ∧
    (∀ k ∈ Finset.range 4, IsFiniteMeasure (σ.spectralMeasureAt (φ + Complex.I ^ k • ψ))) ∧
    (∀ g : EMPoints → ℂ, Measurable g → (∃ b : ℝ, ∀ p, ‖g p‖ ≤ b) →
      BorelComplexMeasures.integralOf (σ.pairSpectralMeasure φ ψ) g =
        (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4, (Complex.I ^ k)⁻¹ *
          ∫ p, g p ∂σ.spectralMeasureAt (φ + Complex.I ^ k • ψ)) ∧
    (∀ N : BorelSubsets EMPoints, σ.jointMeasure N = 0 →
      ∀ B : BorelSubsets EMPoints, B.1 ⊆ N.1 →
        σ.jointMeasure B = 0 ∧ σ.pairSpectralMeasure φ ψ B = 0) ∧
    σ.jointMeasure SpectralPoint.negEnergyBorel = 0
def HeatMatrixElements (φ ψ : σ.space) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ, 0 ≤ s → ∀ v : Fin 3 → ℝ,
    IsSelfAdjoint (σ.heatSemigroup t) ∧
      ‖σ.heatSemigroup t‖ ≤ 1 ∧
      σ.heatSemigroup t * σ.heatSemigroup s = σ.heatSemigroup (t + s) ∧
      σ.heatSemigroup t * σ.spatialShiftOp v =
        σ.spatialShiftOp v * σ.heatSemigroup t ∧
      ⟪φ, σ.heatSemigroup t (σ.spatialShiftOp v ψ)⟫_ℂ =
        BorelComplexMeasures.integralOf (σ.pairSpectralMeasure φ ψ)
          (zeroExtend SpectralPoint.nonnegEnergy.1
            (SpectralPoint.laplaceFourierKernel t (spatialEmbed v)))
end EuclidFunctionalWithRecon
def HamMomMatrixCalculus : Prop :=
  ∀ (c : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon c S)
    (φ ψ : σ.space),
    σ.JointMeasureOfHamMom φ ψ ∧ σ.PairMeasurePolarization φ ψ ∧
      σ.HeatMatrixElements φ ψ
end YangMills.Construction.EuclideanFunctionals
