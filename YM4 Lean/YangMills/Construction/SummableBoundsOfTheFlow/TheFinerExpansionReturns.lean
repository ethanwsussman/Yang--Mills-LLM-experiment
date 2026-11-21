import YangMills.Construction.ClusterExpansionOfAStep.StepVariablesAtParameters
import YangMills.Construction.ClusterExpansionOfAStep.TheExpansionReturns
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasAnExpansion
import YangMills.Construction.SummableBoundsOfTheFlow.FinerExpansion
import YangMills.Construction.SummableBoundsOfTheFlow.ScaledVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusLumps RenormalizationStepParameters StepReturn ReferenceDensity ScaledVariables
namespace FamilyNorms
def TiltReturnsAt (q : TorusLumps.StepParameters) (f : ℕ → LocalDensity) (b d : ℕ → ℝ) (yp C₁ : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (D : TorusFunctional) (ε : ℝ) (h : LocalDensity), yp ≤ x → 0 < ε → HasExpansion q t x D →
    IsCurvatureFreeTilt q t x D (f t) h ε →
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → IsNormBoundedFamily q q.E q.E₃ (f t + θ • h)) →
    ∃ (x' : ℝ) (h' : LocalDensity), HasExpansion q (t + 1) x' (kernelImage q x D) ∧
      IsCurvatureFreeTilt q (t + 1) x' (kernelImage q x D) (f (t + 1)) h' (ε / 8 + C₁ * x ^ (-(3 / 4 : ℝ))) ∧
      |x' - (x - b t - d t / x)| ≤ C₁ * (x ^ (-(1 / 2 : ℝ)) * ε + x ^ (-(3 / 2 : ℝ)))
def RefinedExpansionReturnsAt (q : TorusLumps.StepParameters) (f : ℕ → LocalDensity) (b d : ℕ → ℝ)
    (yp Bh R : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (D : TorusFunctional), yp ≤ x → HasRefinedExpansion q Bh (f t) t x D →
    ∃ x' : ℝ, HasRefinedExpansion q Bh (f (t + 1)) (t + 1) x' (kernelImage q x D) ∧
      |x' - (x - b t - d t / x)| ≤ R * x ^ (-(5 / 4 : ℝ))
def WilsonHasRefinedExpansionAt (q : TorusLumps.StepParameters) (f : ℕ → LocalDensity) (yp Bh : ℝ) : Prop :=
  ∀ β : ℝ, yp ≤ β → HasRefinedExpansion q Bh (f 0) 0 β (wilsonWeight β)
def ParameterAssignment.reference (T : RenormalizationStepParameters.ParameterAssignment) : ℕ → LocalDensity :=
  referenceFamily T.coupling T.ρA T.lam T.side
def ParameterAssignment.oneLoop (T : RenormalizationStepParameters.ParameterAssignment) (t : ℕ) : ℝ :=
  oneLoopCoefficient T.coupling T.ρA T.lam T.side t
def ParameterAssignment.secondStep (T : RenormalizationStepParameters.ParameterAssignment) (t : ℕ) : ℝ :=
  secondStepCoefficient T.coupling T.ρA T.lam T.side t
structure RefinedExpansionHolds (T : RenormalizationStepParameters.ParameterAssignment) (y C₁ M : ℝ) : Prop where
  admissible : (T.stepParameters y).Admissible
  returns : ExpansionReturnsAt (T.stepParameters y)
  C₁_pos : 0 < C₁
  secondStep_le : ∀ t, |ParameterAssignment.secondStep T t| ≤ M
  tilt : TiltReturnsAt (T.stepParameters y) (ParameterAssignment.reference T) (ParameterAssignment.oneLoop T)
    (ParameterAssignment.secondStep T) y C₁
  refined : RefinedExpansionReturnsAt (T.stepParameters y) (ParameterAssignment.reference T)
    (ParameterAssignment.oneLoop T) (ParameterAssignment.secondStep T) y (2 * C₁) (C₁ * (2 * C₁ + 1))
  wilson : WilsonHasRefinedExpansionAt (T.stepParameters y) (ParameterAssignment.reference T) y (2 * C₁)
def RefinedExpansionReturns : Prop :=
  ∃ Q : ColdStepAtMirrorFrames.StepParameters → Prop, ColdStepAtMirrorFrames.EventuallyInParameters Q ∧
    ∃ (floorL : ℝ → ℕ) (ceilRt : ChainParameters → ℝ) (ceilσ : ChainParameters → ℝ → ℝ)
      (floorN : ChainParameters → ℝ → ℝ → ℕ) (floorCs : ChainParameters → ℝ → ℝ → ℝ) (C₀ : ℝ),
      (∀ D, 0 < ceilRt D) ∧ (∀ D r, 0 < ceilσ D r) ∧
      ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → floorL T.coupling ≤ T.side → T.rt ≤ ceilRt T.toChainParameters →
        T.threshold ≤ ceilσ T.toChainParameters T.rt → floorN T.toChainParameters T.rt T.threshold ≤ T.n₀ →
        floorCs T.toChainParameters T.rt T.threshold ≤ T.Cs → C₀ ≤ T.derivBound → T.HoldsFrom Q →
        ∃ y₀ C₁ M : ℝ, ∀ y : ℝ, y₀ ≤ y → RefinedExpansionHolds T y C₁ M
end FamilyNorms
end YangMills.Construction
end
