import YangMills.Construction.RunningCouplingSlope.CoordinatesOfTheStepsOfAChainForm
import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower BlockAverages ColdStepAtMirrorFrames TorusLumps
variable {L n k : ℕ}
def finalNoise : LevelForms L n (k + 1) →ₗ[ℝ] Tower.edgeFormSpace L n (k + 1) (k + 1) :=
  (LinearMap.proj (Fin.last k) : ((i : Fin (k + 1)) → Tower.edgeFormSpace L n (k + 1) (i + 1)) →ₗ[ℝ] _) ∘ₗ
    LinearMap.snd ℝ _ _
def SlotCoordsIsometry : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    LevelFormsEuclidean L n (k + 1) ∧ Tower.EdgeFormsEuclidean L n (k + 1) (k + 1) ∧
    ∃ (p : LevelForms L n (k + 1) →ₗ[ℝ] EuclideanSpace ℝ (ChainCoord L n (k + 1)))
      (s : EuclideanSpace ℝ (ChainCoord L n (k + 1)) →ₗ[ℝ] LevelForms L n (k + 1))
      (i : Tower.edgeFormSpace L n (k + 1) (k + 1) →ₗ[ℝ] LevelForms L n (k + 1)),
      (∀ ξ, WithLp.ofLp (p ξ) = slotCoords ξ) ∧
      (∀ ξ ξ', levelPairing (formValues ξ) (formValues ξ') =
        dotProduct (WithLp.ofLp (p ξ)) (WithLp.ofLp (p ξ')) +
          (Tower.edgeFormPairing ((finalNoise ξ : Tower.edgeFormSpace L n (k + 1) (k + 1)) : Tower.Edge L n (k + 1) (k + 1) → Matrices.ComplexMatrix2)
            ((finalNoise ξ' : Tower.edgeFormSpace L n (k + 1) (k + 1)) : Tower.Edge L n (k + 1) (k + 1) → Matrices.ComplexMatrix2)).re) ∧
      p ∘ₗ s = LinearMap.id ∧ finalNoise ∘ₗ s = 0 ∧ p ∘ₗ i = 0 ∧ finalNoise ∘ₗ i = LinearMap.id
end YangMills.Construction.RunningCouplingSlope
end
