import YangMills.Construction.ReflectionPositivity.EnergyMomentumMeasuresOfAPicture
import YangMills.Construction.ReflectionPositivity.FormOfTransferPowerOffZeroEnergy
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
open YangMills.Construction.HilbertSpace (SesqForm)
open YangMills.Construction.FormHilbert (IsPosSesqForm)
def ReflectionPair.powerOffGroundForm (p : ReflectionPair) (ν : unitPositiveClass) (μ : Fin 4)
    (n : ℕ) : SesqForm (p.Hilb ν μ) := fun ψ ψ' =>
  inner ℂ ψ ((p.transferOp ν μ ^ n * (1 - groundProjection μ p ν)) ψ')
namespace PowerOffGround
def groundSet (μ : Fin 4) : Set (EnergyMomentum.SpectralSpace μ) := {x | x.energy = 0}
def excitedSet (μ : Fin 4) : Set (EnergyMomentum.SpectralSpace μ) :=
  {x | 0 < x.energy ∧ x.energy < ⊤}
def AgreesWithPairForms (ν : unitPositiveClass) (μ : Fin 4) (n : ℕ) (hn : 1 ≤ n) : Prop :=
  (∀ ψ ψ' : ReflectionPair.site.Hilb ν μ,
    ReflectionPair.site.powerOffGroundForm ν μ n ψ ψ' = sitePowerForm ν μ n hn ψ ψ') ∧
  ∀ ψ ψ' : ReflectionPair.link.Hilb ν μ,
    ReflectionPair.link.powerOffGroundForm ν μ n ψ ψ' = linkPowerForm ν μ n hn ψ ψ'
variable (p : ReflectionPair) (ν : unitPositiveClass) (μ : Fin 4) (n : ℕ)
def GroundAndDiagonal : Prop :=
  (∀ (s t : ℂ) (ψ ψ' : p.Hilb ν μ),
    groundProjection μ p ν (s • ψ + t • ψ') =
      s • groundProjection μ p ν ψ + t • groundProjection μ p ν ψ') ∧
  ∀ ψ : p.Hilb ν μ,
    inner ℂ ψ (groundProjection μ p ν ψ) =
        (((p.spectralMeasure ν μ ψ).real (groundSet μ) : ℝ) : ℂ) ∧
      p.powerOffGroundForm ν μ n ψ ψ =
        ((∫ x, (excitedSet μ).indicator
            (fun y : EnergyMomentum.SpectralSpace μ => EnergyMomentum.expNegNatMulEnergy n y.energy) x
            ∂p.spectralMeasure ν μ ψ : ℝ) : ℂ)
def GroundSplits : Prop :=
  p.transferOp ν μ ^ n * groundProjection μ p ν = groundProjection μ p ν ∧
  p.transferOp ν μ ^ n = groundProjection μ p ν +
    p.transferOp ν μ ^ n * (1 - groundProjection μ p ν) ∧
  ∀ w : EnergyMomentum.orthLattice μ,
    groundProjection μ p ν * p.shiftMonomial ν μ (w : Fin 4 → ℤ) = groundProjection μ p ν
def IsPosConjSymmForm : Prop :=
  IsPosSesqForm (p.powerOffGroundForm ν μ n) ∧ (p.powerOffGroundForm ν μ n).IsConjSymm ∧
  ∀ ψ ψ' : p.Hilb ν μ,
    ‖p.powerOffGroundForm ν μ n ψ ψ'‖ ≤
        Real.sqrt (p.powerOffGroundForm ν μ n ψ ψ).re *
          Real.sqrt (p.powerOffGroundForm ν μ n ψ' ψ').re ∧
      (p.powerOffGroundForm ν μ n (ψ + ψ') (ψ + ψ')).re ≤
        2 * (p.powerOffGroundForm ν μ n ψ ψ).re + 2 * (p.powerOffGroundForm ν μ n ψ' ψ').re
def TransverseInvariance : Prop :=
  ∀ (w : EnergyMomentum.orthLattice μ) (ψ : p.Hilb ν μ),
    p.powerOffGroundForm ν μ n (p.shiftMonomial ν μ (w : Fin 4 → ℤ) ψ)
        (p.shiftMonomial ν μ (w : Fin 4 → ℤ) ψ) = p.powerOffGroundForm ν μ n ψ ψ
def Holds : Prop :=
  ∀ (ν : unitPositiveClass) (μ : Fin 4) (n : ℕ) (hn : 1 ≤ n),
    AgreesWithPairForms ν μ n hn ∧
    ∀ p : ReflectionPair,
      GroundAndDiagonal p ν μ n ∧ GroundSplits p ν μ n ∧
        IsPosConjSymmForm p ν μ n ∧ TransverseInvariance p ν μ n
end PowerOffGround
end YangMills.Construction.ReflectionPositivity.DirectionPictures
