import YangMills.Construction.ReflectionPositiveLimits.ReconstructionFromAContractionAtADenseSetOfTimes
import Mathlib
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace YangMills.Construction
namespace EnergyMomentum
def expNegTimeEnergy (t : ℝ≥0) (p : EnergyMomentumSpace) : ℂ :=
  Complex.exp ((-(t : ℝ) * (p.1 : ℝ) : ℝ) : ℂ)
def expCoordMomentum (i : Fin 3) (s : ℝ) (p : EnergyMomentumSpace) : ℂ :=
  Complex.exp (Complex.I * ((s * p.2 i : ℝ) : ℂ))
def expMomentumDot (y : Momentum3) (p : EnergyMomentumSpace) : ℂ :=
  Complex.exp (Complex.I * ((spatialDot y p.2 : ℝ) : ℂ))
def absMomentumCoord (i : Fin 3) (p : EnergyMomentumSpace) : ℂ :=
  ((|p.2 i| : ℝ) : ℂ)
def energyGeAbsMomentum : Set EnergyMomentumLine :=
  {p | |p.2| ≤ (p.1 : ℝ)}
end EnergyMomentum
namespace ReflectionPositivity.FunctionalReconstruction
open EnergyMomentum EuclideanSpectral
structure VacuumEnergyMomentumSystem (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  vacuumVec : H
  energy : H →ₗ.[ℂ] H
  momenta : Fin 3 → H →ₗ.[ℂ] H
structure ReconstructionData (σ : Tuple → ℝ) : Prop where
  reconstructionHypotheses : ReconstructionHypotheses σ
  contractsOnDenseTimes : ContractsOnDenseTimes σ
theorem ReconstructionData.reflectionPositive {σ : Tuple → ℝ} (hσ : ReconstructionData σ) :
    ReflectionPositiveAt timeZeroMirror σ :=
  hσ.reconstructionHypotheses.isReflectionPositive
section
variable (σ : Tuple → ℝ) (hσ : ReconstructionData σ)
def hamiltonianOp :
    ReconstructionSpace σ hσ.reflectionPositive →ₗ.[ℂ]
      ReconstructionSpace σ hσ.reflectionPositive :=
  ReflectionPositivity.hamiltonian σ hσ.reflectionPositive
def momentumOpOf (i : Fin 3) :
    ReconstructionSpace σ hσ.reflectionPositive →ₗ.[ℂ]
      ReconstructionSpace σ hσ.reflectionPositive :=
  ReflectionPositivity.momentumOp σ hσ.reflectionPositive i
def reconstruction :
    VacuumEnergyMomentumSystem (ReconstructionSpace σ hσ.reflectionPositive) where
  vacuumVec := ReflectionPositivity.vacuum σ hσ.reflectionPositive
  energy := hamiltonianOp σ hσ
  momenta := momentumOpOf σ hσ
def heatOperator (t : ℝ≥0) :
    ReconstructionSpace σ hσ.reflectionPositive →L[ℂ]
      ReconstructionSpace σ hσ.reflectionPositive :=
  (jointSpectralMeasure σ hσ.reflectionPositive).boundedCalculus (expNegTimeEnergy t)
def coordTranslationOperator (i : Fin 3) (s : ℝ) :
    ReconstructionSpace σ hσ.reflectionPositive →L[ℂ]
      ReconstructionSpace σ hσ.reflectionPositive :=
  (jointSpectralMeasure σ hσ.reflectionPositive).boundedCalculus (expCoordMomentum i s)
def translationOperator (y : Momentum3) :
    ReconstructionSpace σ hσ.reflectionPositive →L[ℂ]
      ReconstructionSpace σ hσ.reflectionPositive :=
  (jointSpectralMeasure σ hσ.reflectionPositive).boundedCalculus (expMomentumDot y)
def absMomentumOp (i : Fin 3) :
    ReconstructionSpace σ hσ.reflectionPositive →ₗ.[ℂ]
      ReconstructionSpace σ hσ.reflectionPositive :=
  (jointSpectralMeasure σ hσ.reflectionPositive).calculusOperator (absMomentumCoord i)
def jointSpectrum (i : Fin 3) : Set EnergyMomentumLine :=
  (axisSpectralMeasure σ hσ.reflectionPositive i).supp
def EnergyDominatesMomentum (i : Fin 3) : Prop :=
  jointSpectrum σ hσ i ⊆ energyGeAbsMomentum
structure IsProjOntoEnergyKernel
    (B : ReconstructionSpace σ hσ.reflectionPositive →L[ℂ]
      ReconstructionSpace σ hσ.reflectionPositive) : Prop where
  isOrthProjection : IsOrthProjection B
  fixedSet_eq : fixedSet B = pmapKernel (hamiltonianOp σ hσ)
def groundStateProjection :
    ReconstructionSpace σ hσ.reflectionPositive →L[ℂ]
      ReconstructionSpace σ hσ.reflectionPositive :=
  Classical.epsilon (IsProjOntoEnergyKernel σ hσ)
def IsInvariant (ψ : ReconstructionSpace σ hσ.reflectionPositive) : Prop :=
  (∀ t, transferSemigroup σ hσ.reflectionPositive t ψ = ψ) ∧
    ∀ v, spatialTranslationRep σ hσ.reflectionPositive v ψ = ψ
def IsErgodic : Prop :=
  ∀ ψ : ReconstructionSpace σ hσ.reflectionPositive, IsInvariant σ hσ ψ →
    ∃ c : ℂ, ψ = c • ReflectionPositivity.vacuum σ hσ.reflectionPositive
end
end ReflectionPositivity.FunctionalReconstruction
end YangMills.Construction
