import YangMills.Construction.EnergyMomentum.MomentumLineCoordinates
import YangMills.Construction.EnergyMomentum.SpectralMeasureOfVector
import YangMills.Construction.EuclideanSpectral.FunctionalCalculus
import Mathlib
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace YangMills.Construction.EnergyMomentum.JointSpectral
open YangMills.Construction.EnergyMomentum YangMills.Construction.EuclideanSpectral
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
def IsJointSpectralMeasure (T : ℝ≥0 → 𝓗 →L[ℂ] 𝓗) (U : Momentum3 → 𝓗 →L[ℂ] 𝓗)
    (P : SpectralMeasure EnergyMomentumSpace 𝓗) : Prop :=
  ∀ t y, T t * U y = P.boundedCalculus (laplaceFourierExp t y)
def jointSpectralMeasure (T : ℝ≥0 → 𝓗 →L[ℂ] 𝓗) (U : Momentum3 → 𝓗 →L[ℂ] 𝓗) :
    SpectralMeasure EnergyMomentumSpace 𝓗 :=
  haveI : Nonempty (SpectralMeasure EnergyMomentumSpace 𝓗) :=
    SpectralMeasure.nonempty_of_isEuclideanBorel isEuclideanBorel_energyMomentumSpace
  Classical.epsilon (IsJointSpectralMeasure T U)
def momentumMarginal (T : ℝ≥0 → 𝓗 →L[ℂ] 𝓗) (U : Momentum3 → 𝓗 →L[ℂ] 𝓗) (i : Fin 3) :
    SpectralMeasure EnergyMomentumLine 𝓗 :=
  (jointSpectralMeasure T U).pushforward isEuclideanBorel_energyMomentumLine
    (projMomentum i) (measurable_projMomentum i)
def IsMomentumMarginal (T : ℝ≥0 → 𝓗 →L[ℂ] 𝓗) (U : Momentum3 → 𝓗 →L[ℂ] 𝓗) (i : Fin 3)
    (Q : SpectralMeasure EnergyMomentumLine 𝓗) : Prop :=
  ∀ (t : ℝ≥0) (s : ℝ), T t * U (s • EuclideanSpace.single i (1 : ℝ)) =
    Q.boundedCalculus (laplaceFourierExpLine t s)
def JointSpectralMeasureTheorem : Prop :=
  ∀ (𝓚 : Type) [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚] [CompleteSpace 𝓚]
    (T : ℝ≥0 → 𝓚 →L[ℂ] 𝓚) (U : Momentum3 → 𝓚 →L[ℂ] 𝓚),
    IsContractionSemigroupWithUnitaryGroup T U →
    (IsJointSpectralMeasure T U (jointSpectralMeasure T U) ∧
      (∀ P : SpectralMeasure EnergyMomentumSpace 𝓚, IsJointSpectralMeasure T U P →
        P = jointSpectralMeasure T U) ∧
      ∀ v : 𝓚, (jointSpectralMeasure T U).diagMeasure v = spectralMeasure T U v) ∧
    (∀ t, opKernel (T t) = {0}) ∧
    ∀ i : Fin 3, IsMomentumMarginal T U i (momentumMarginal T U i) ∧
      ∀ Q : SpectralMeasure EnergyMomentumLine 𝓚, IsMomentumMarginal T U i Q →
        Q = momentumMarginal T U i
end YangMills.Construction.EnergyMomentum.JointSpectral
