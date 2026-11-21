import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.NumbersOfFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusLumps
namespace FamilyNorms
def HasBoundedLimitForm (L t : ℕ) (g : TopLevelFamily) (c : ℝ) : Prop :=
  ∃ q : BondBilinearForm,
    (∀ b b' X X', Filter.Tendsto (fun n => secondDerivAtUniform g L t n b b' X X') Filter.atTop
      (nhds (q b b' X X'))) ∧
    ∀ (X : imaginaryQuaternions) (μ ν : Fin 4) (A : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
      ‖X‖ = 1 → μ < ν → IsLinearPotential (constantPlaneCurvature X μ ν) A →
      ∃ v : ℝ, HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        q e.1 e.2 (A e.1) (A e.2)) v ∧ |v| ≤ c
def topFamilyNormStatement : Prop :=
  ∀ P : TorusLumps.StepParameters, P.Admissible →
    (∀ (t : ℕ) (s s' ε ε₃ : ℝ) (g : TopLevelFamily) (e : ℕ → ℕ → ℝ) (e' : ℕ → ℝ),
      P.threshold ≤ s → P.threshold ≤ s' →
      IsLocalDensity P.side t P.n₀ s g → DerivDecay P.side t P.n₀ s g e →
      IsLocalOnTori P.side t P.n₀ s' (centredFamily g) e' →
      (∀ k m, 1 ≤ k → k ≤ 3 → e k m ≤ (if k = 3 then ε₃ else ε) / P.weight m) →
      (∀ m, e' m ≤ ε / P.weight m) → IsNormBoundedFamily P ε ε₃ (densityOfTopFamily P.side t g)) ∧
    (∀ (t : ℕ) (g : TopLevelFamily) (c : ℝ), HasBoundedLimitForm P.side t g c →
      ∃ v, HasUnitPlaneValue (densityOfTopFamily P.side t g) v ∧ |v| ≤ c) ∧
    ∀ m : ℕ, Real.exp (-(P.rt / 2 ^ 9 * m)) ≤ weightGrowthSup P.rt P.n₁ / P.weight m
end FamilyNorms
end YangMills.Construction
end
