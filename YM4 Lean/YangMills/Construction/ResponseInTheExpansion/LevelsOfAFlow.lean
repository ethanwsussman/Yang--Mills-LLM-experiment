import YangMills.Construction.ClusterExpansionOfAStep.FlowOfTheExpansion
import YangMills.Construction.ResponseInTheExpansion.LevelsOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import YangMills.Construction.ResponseInTheExpansion.WilsonWeightHasTheExpansionOfTheResponse
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
def couplingsAlongFlow (ℓ : TorusLumps.StepParameters) (β : ℝ) (j : ℕ) : ℝ := (TorusLumps.couplingFlow ℓ β j).1
structure StageOnFlow (T : RenormalizationStepParameters.ParameterAssignment) (K : WeightedResponses.ResponseParameters) (y β : ℝ) (t : ℕ)
    (z : StageWithResponse (T.stepParameters y)) : Prop where
  depth_eq : z.1.depth = t
  coupling_eq : z.1.coupling = couplingsAlongFlow (T.stepParameters y) β t
  nextCoupling_eq : z.1.nextCoupling = couplingsAlongFlow (T.stepParameters y) β (t + 1)
  functional_eq : z.1.functional = (TorusLumps.couplingFlow (T.stepParameters y) β t).2
  params_eq : z.2.responseParams = K
  onFamily : WeightedResponses.OnStepParameters T y z.2
  isSymmetricWeight : z.1.toStepSetup.IsSymmetricWeight
  nextCoupling_eq_shifted : z.1.nextCoupling = z.1.toStepSetup.shiftedCoupling T.lam
  abs_coeff_sub_one_le : |z.2.coeff - 1| ≤ 1 / 4
def initialStage (T : RenormalizationStepParameters.ParameterAssignment) (y β : ℝ) (K : WeightedResponses.ResponseParameters)
    (f : TorusLumps.LocalDensity) (Λ : TorusLumps.LabelSpace)
    (Dq : (n : ℕ) → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (Φ : (n : ℕ) → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) → (Y → Λ.Ω) →
      Finset (TorusFields.TorusSite n) → ℝ)
    (φ : (n : ℕ) → TorusFields.TorusSite n → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) →
      (Y → Λ.Ω) → ℝ) : StageWithResponse (T.stepParameters y) :=
  ⟨{ depth := 0, coupling := β, nextCoupling := couplingsAlongFlow (T.stepParameters y) β 1,
     functional := TorusLumps.wilsonWeight β, density := f, labels := Λ, labelWeight := Dq, clusterFactor := Φ,
     siteDensity := φ, anchorRadius := T.ρA, barrierFn := T.cutoff },
   { responseParams := K, coeff := 1, score := fun _ => 0, cold := wilsonColdResponse (T.stepParameters y).side,
     hull := wilsonHullResponse (T.stepParameters y).side Λ.Ω, siteRemainder := fun _ _ _ => 0,
     totalRemainder := fun _ _ _ => 0 }⟩
structure IsInitialStage (T : RenormalizationStepParameters.ParameterAssignment) (y β : ℝ) (z : StageWithResponse (T.stepParameters y)) : Prop where
  isWilson : ∃ (K : WeightedResponses.ResponseParameters) (f : TorusLumps.LocalDensity) (Λ : TorusLumps.LabelSpace)
    (Dq : (n : ℕ) → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (Φ : (n : ℕ) → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) → (Y → Λ.Ω) →
      Finset (TorusFields.TorusSite n) → ℝ)
    (φ : (n : ℕ) → TorusFields.TorusSite n → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) →
      (Y → Λ.Ω) → ℝ),
    z = initialStage T y β K f Λ Dq Φ φ
  anchorRadius_eq : z.1.anchorRadius = T.ρA
  barrierFn_eq : z.1.barrierFn = T.cutoff
  depth_eq : z.1.depth = 0
  coupling_eq : z.1.coupling = β
  functional_eq : z.1.functional = TorusLumps.wilsonWeight β
  nextCoupling_eq : z.1.nextCoupling = couplingsAlongFlow (T.stepParameters y) β 1
  score_eq : ∀ w, z.2.score w = 0
  coeff_eq : z.2.coeff = 1
abbrev flowStages (T : RenormalizationStepParameters.ParameterAssignment) (y β : ℝ)
    (hL : ∀ c : WeightedResponses.ChainStage (T.stepParameters y), ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup)
    (z₀ : StageWithResponse (T.stepParameters y)) : ℕ → StageWithResponse (T.stepParameters y) :=
  stagesFrom hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀
def StagesOnFlowUpTo (T : RenormalizationStepParameters.ParameterAssignment) (K : WeightedResponses.ResponseParameters) (y β : ℝ)
    (hL : ∀ c : WeightedResponses.ChainStage (T.stepParameters y), ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup)
    (z₀ : StageWithResponse (T.stepParameters y)) (s : ℕ) : Prop :=
  ∀ t ≤ s, StageOnFlow T K y β t (flowStages T y β hL z₀ t)
end ResponseInTheExpansion
end YangMills.Construction
end
