import YangMills.Construction.SummableBoundsOfTheFlow.TheFinerExpansionReturns
import YangMills.Construction.SummableBoundsOfTheFlow.TiltOfTheImage
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FamilyNorms
open YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.ShareFamilies
def shareBound (T : RenormalizationStepParameters.ParameterAssignment) : ℝ := weightGrowthSup T.rt T.n₁ * maxOfFirstFour T.N
def stepPiecesAt (T : RenormalizationStepParameters.ParameterAssignment) (C₀ M y₀ : ℝ) : Prop :=
  ∀ y : ℝ, y₀ ≤ y → ∀ (t : ℕ) (x : ℝ) (D : TorusFunctional) (ε : ℝ) (h : LocalDensity), y ≤ x → 0 < ε →
    HasExpansion (T.stepParameters y) t x D →
    IsCurvatureFreeTilt (T.stepParameters y) t x D (FamilyNorms.ParameterAssignment.reference T t) h ε →
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → IsNormBoundedFamily (T.stepParameters y) T.E T.E₃
      (FamilyNorms.ParameterAssignment.reference T t + θ • h)) →
    ∃ c m e g : LocalDensity, StepImagePieces (T.stepParameters y) t x ε C₀ (shareBound T) M
      (FamilyNorms.ParameterAssignment.oneLoop T t) (FamilyNorms.ParameterAssignment.secondStep T t)
      (kernelImage (T.stepParameters y) x D) (FamilyNorms.ParameterAssignment.reference T (t + 1)) c m e g
      (levelShareFamily T.coupling T.side (t + 1))
def stepPiecesStatement : Prop :=
  ∃ Q : ColdStepAtMirrorFrames.StepParameters → Prop, ColdStepAtMirrorFrames.EventuallyInParameters Q ∧
    ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters → T.HoldsFrom Q →
      ∃ C₀ M y₀ : ℝ, 0 ≤ C₀ ∧ 0 ≤ shareBound T ∧ 0 ≤ M ∧
      (∀ t, |FamilyNorms.ParameterAssignment.secondStep T t| ≤ M) ∧
      (∀ y : ℝ, T.floorMin ≤ y → ∀ t, IsNormBoundedFamily (T.stepParameters y) (T.E / 2) (T.E₃ / 2)
        (FamilyNorms.ParameterAssignment.reference T t)) ∧
      stepPiecesAt T C₀ M y₀
end YangMills.Construction.FamilyNorms
end
