import YangMills.Construction.ReflectionPositiveLimits.ExponentialsOfTheGenerators
import Mathlib
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.GeneratorExponentials
open EnergyMomentum ReflectionPositivity ReflectionPositivity.FunctionalReconstruction
  ReflectionPositivity.DenseTimeReconstruction
theorem laplaceFourierExp_zero_displacement (t : ℝ≥0) :
    laplaceFourierExp t 0 = expNegTimeEnergy t := by
  funext p
  simp [laplaceFourierExp, expNegTimeEnergy, spatialDot]
theorem laplaceFourierExp_zero_time (y : Momentum3) :
    laplaceFourierExp 0 y = expMomentumDot y := by
  funext p
  simp [laplaceFourierExp, expMomentumDot]
theorem spatialDot_smul_single (i : Fin 3) (s : ℝ) (q : Momentum3) :
    spatialDot (s • EuclideanSpace.single i (1 : ℝ)) q = s * q i := by
  simp [spatialDot, Finset.sum_ite_eq']
theorem expMomentumDot_smul_single (i : Fin 3) (s : ℝ) :
    expMomentumDot (s • EuclideanSpace.single i (1 : ℝ)) = expCoordMomentum i s := by
  funext p
  simp only [expMomentumDot, expCoordMomentum, spatialDot_smul_single]
theorem generatorExponentialsHold_of_reconstruction (hR : DenseTimeReconstructionHolds) :
    GeneratorExponentialsHold := by
  intro σ hσ
  obtain ⟨-, hall⟩ := hR
  obtain ⟨-, -, hc⟩ := hall σ hσ.reconstructionHypotheses
  obtain ⟨hT, hU, -, -, hJ⟩ := hc hσ.contractsOnDenseTimes
  have hU0 : spatialTranslationRep σ hσ.reflectionPositive 0 = 1 := by
    ext ψ
    apply (hU.isUnitary 0).bijective.1
    have h := congrArg (fun B => B ψ) (hU.add 0 0)
    simpa using h
  have hy : ∀ y, translationOperator σ hσ y =
      spatialTranslationRep σ hσ.reflectionPositive y := by
    intro y
    have h := hJ.isJointSpectralMeasure 0 y
    rw [hT.zero, one_mul, laplaceFourierExp_zero_time] at h
    exact h.symm
  refine ⟨fun t => ?_, hy, fun i s => ?_⟩
  · have h := hJ.isJointSpectralMeasure t 0
    rw [hU0, mul_one, laplaceFourierExp_zero_displacement] at h
    exact h.symm
  · rw [← hy]
    simp only [translationOperator, coordTranslationOperator, expMomentumDot_smul_single]
end YangMills.Construction.ReflectionPositivity.GeneratorExponentials
