import YangMills.Construction.ReflectionPositiveLimits.ZeroEnergyProjectionIsSpectral
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.GroundStateSpectral
open EnergyMomentum EnergyMomentum.Generators EnergyMomentum.JointSpectral EuclideanSpectral
  ReflectionPositivity ReflectionPositivity.FunctionalReconstruction
  ReflectionPositivity.DenseTimeReconstruction
theorem eq_of_fixedSet_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {A B : H →L[ℂ] H} (hA : IsOrthProjection A)
    (hB : IsOrthProjection B) (h : fixedSet A = fixedSet B) : A = B := by
  have fixA : ∀ ψ, B (A ψ) = A ψ := fun ψ => by
    have m : A ψ ∈ fixedSet A := congrArg (fun C : H →L[ℂ] H => C ψ) hA.idempotent
    rw [h] at m
    exact m
  have fixB : ∀ ψ, A (B ψ) = B ψ := fun ψ => by
    have m : B ψ ∈ fixedSet B := congrArg (fun C : H →L[ℂ] H => C ψ) hB.idempotent
    rw [← h] at m
    exact m
  ext ψ
  refine ext_inner_left ℂ fun χ => ?_
  calc ⟪χ, A ψ⟫_ℂ = ⟪χ, B (A ψ)⟫_ℂ := by rw [fixA]
    _ = ⟪B χ, A ψ⟫_ℂ := hB.selfAdjoint χ (A ψ)
    _ = ⟪A (B χ), ψ⟫_ℂ := hA.selfAdjoint (B χ) ψ
    _ = ⟪B χ, ψ⟫_ℂ := by rw [fixB]
    _ = ⟪χ, B ψ⟫_ℂ := (hB.selfAdjoint χ ψ).symm
theorem groundStateProjectionSpectral_of_reconstruction
    (hRec : DenseTimeReconstructionHolds) (hGen : GeneratorsTheorem)
    (hSpec : JointSpectralMeasureTheorem) : GroundStateProjectionSpectral := by
  intro σ hσ
  obtain ⟨-, -, hc⟩ := hRec.2 σ hσ.reconstructionHypotheses
  obtain ⟨hT, hU, -, -, hJ⟩ := hc hσ.contractsOnDenseTimes
  have hsg : IsContractionSemigroupWithUnitaryGroup (transferSemigroup σ hσ.reflectionPositive)
      (spatialTranslationRep σ hσ.reflectionPositive) :=
    { isSelfAdjoint := fun t => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun x y =>
        (hT.isSelfAdjoint t x y).symm
      norm_le_one := hT.isContraction
      semigroup_zero := hT.zero
      semigroup_add := hT.add
      isUnitary := fun y => ⟨(hU.isUnitary y).bijective, (hU.isUnitary y).norm_map⟩
      group_add := hU.add
      semigroup_mul_group := hU.commutes
      continuous_semigroup := hT.isStronglyContinuous
      continuous_group := hU.isStronglyContinuous }
  obtain ⟨-, -, -, hK, -⟩ := hGen _ _ _ hsg
  have hEq := (hSpec _ _ _ hsg).1.2.1 _ hJ.isJointSpectralMeasure
  have hE : IsProjOntoEnergyKernel σ hσ
      (jointSpectralMeasure σ hσ.reflectionPositive zeroEnergySet) := by
    refine ⟨?_, ?_⟩
    · rw [hEq]
      exact hK.isOrthProjection
    · have e := hK.fixedSet_eq
      unfold EnergyMomentum.Generators.hamiltonian at e
      rw [← hEq] at e
      exact e
  have hP : IsProjOntoEnergyKernel σ hσ (groundStateProjection σ hσ) :=
    Classical.epsilon_spec ⟨_, hE⟩
  exact ⟨hP, eq_of_fixedSet_eq hP.isOrthProjection hE.isOrthProjection
    (hP.fixedSet_eq.trans hE.fixedSet_eq.symm)⟩
end YangMills.Construction.ReflectionPositivity.GroundStateSpectral
