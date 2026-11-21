import YangMills.Construction.ReflectionPositivity.MeasureOfTheSemigroupAndOneGroupOfTranslations
import YangMills.Construction.ReflectionPositivity.ReconstructedSystem
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity
namespace PairMeasureOperators
variable (σ : SeparatedTuples.TupleFunctional)
  (hσ : HilbertSpaceBasics.IsPosSemidef (TupleForm.reflectionForm σ))
def pairHamiltonian : SpectralTheory.UnboundedOperator (Reconstruction.PhysicalSpace σ hσ) :=
  ShiftSpectralMeasure.energyOp σ hσ 0
def pairMomentum (k : Fin 3) : SpectralTheory.UnboundedOperator (Reconstruction.PhysicalSpace σ hσ) :=
  ShiftSpectralMeasure.momentumOp σ hσ k
def energyMomentumPair (k : Fin 3) :
    Fin 2 → SpectralTheory.UnboundedOperator (Reconstruction.PhysicalSpace σ hσ) :=
  ![pairHamiltonian σ hσ, pairMomentum σ hσ k]
theorem isJointSpectralMeasure_energyMomentumPair (k : Fin 3)
    (hk : ShiftSpectralMeasure.energyOp σ hσ k = pairHamiltonian σ hσ) :
    SpectralTheory.IsJointSpectralMeasure (ShiftSpectralMeasure.shiftSpectralMeasure σ hσ k).extend
      (energyMomentumPair σ hσ k) := by
  intro j
  fin_cases j
  · exact hk.symm
  · rfl
def groundStateProjection :
    Reconstruction.PhysicalSpace σ hσ →L[ℂ] Reconstruction.PhysicalSpace σ hσ :=
  HilbertSpaceBasics.orthProjOnto (SpectralTheory.opKernel (pairHamiltonian σ hσ))
def pairJointSpectrum (k : Fin 3) : Set (Fin 2 → ℝ) :=
  (ShiftSpectralMeasure.shiftSpectralMeasure σ hσ k).extend.support
theorem isJointSpectrum_energyMomentumPair (k : Fin 3)
    (hk : ShiftSpectralMeasure.energyOp σ hσ k = pairHamiltonian σ hσ) :
    SpectralTheory.IsJointSpectrum (pairJointSpectrum σ hσ k) (energyMomentumPair σ hσ k) :=
  ⟨_, isJointSpectralMeasure_energyMomentumPair σ hσ k hk, rfl⟩
def HamiltonianDominatesMomentum (k : Fin 3) : Prop :=
  pairJointSpectrum σ hσ k ⊆ QuantumSystem.forwardCone
end PairMeasureOperators
end ReflectionPositivity
end YangMills.Construction
