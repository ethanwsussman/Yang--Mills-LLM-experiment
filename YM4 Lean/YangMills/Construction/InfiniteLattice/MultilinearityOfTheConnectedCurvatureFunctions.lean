import YangMills.Construction.InfiniteLattice.TorusFunctionalsAndTuplesReadOnATorus
import YangMills.Construction.Lattice.LatticeAsAProbabilitySpace
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace TorusCumulants
namespace Multilinearity
open Cumulants LatticeProbability SeparatedFamilies
open Probability (IsBoundedRealRV)
def MixedCumulantRealLinear : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (k : Fin n)
    (Y : Fin n → Ω → ℝ) (Y₁ Y₂ : Ω → ℝ) (c₁ c₂ : ℝ),
    (∀ i, IsBoundedRealRV (Y i)) → IsBoundedRealRV Y₁ →
    IsBoundedRealRV Y₂ → (Y k = fun ω => c₁ * Y₁ ω + c₂ * Y₂ ω) →
    (mixedCumulant μ Y).im = 0 ∧
      mixedCumulant μ Y =
        (c₁ : ℂ) * mixedCumulant μ (Function.update Y k Y₁) +
          (c₂ : ℂ) * mixedCumulant μ (Function.update Y k Y₂)
def CumulantRealized (P : Conventions.StandingParameters) (β : ℝ) {n : ℕ}
    (f : Fin n → P.Torus → ℝ) : Prop :=
  IsProbabilityMeasure (gibbsMeasureOn P β) ∧
    (∀ i, IsBoundedRealRV (observableVector P f i)) ∧
    cumulantFunctional P.L P.m P.K β f = mixedCumulant (gibbsMeasureOn P β) (observableVector P f)
abbrev IsTorusLipschitz (P : Conventions.StandingParameters) (f : P.Torus → ℝ) : Prop :=
  TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus f
def LipschitzSubspace (P : Conventions.StandingParameters) : Prop :=
  (∃ V : Submodule ℝ (P.Torus → ℝ), (V : Set (P.Torus → ℝ)) = {f | IsTorusLipschitz P f}) ∧
    ∀ f : P.Torus → ℝ, IsTorusLipschitz P f → TestFunctions.IsBoundedFun f
def FunctionalRealLinear (P : Conventions.StandingParameters) (β : ℝ) (n : ℕ) : Prop :=
  ∀ f : Fin n → P.Torus → ℝ, (∀ i, IsTorusLipschitz P (f i)) →
    (cumulantFunctional P.L P.m P.K β f).im = 0 ∧
      ∀ (k : Fin n) (g₁ g₂ : P.Torus → ℝ) (c₁ c₂ : ℝ), IsTorusLipschitz P g₁ →
        IsTorusLipschitz P g₂ →
        cumulantFunctional P.L P.m P.K β (Function.update f k fun x => c₁ * g₁ x + c₂ * g₂ x) =
          (c₁ : ℂ) * cumulantFunctional P.L P.m P.K β (Function.update f k g₁) +
            (c₂ : ℂ) * cumulantFunctional P.L P.m P.K β (Function.update f k g₂)
structure IsAdmissibleRadius (L m : ℕ) (r : ℝ) : Prop where
  pos : 0 < r
  two_mul_add_two_le : 2 * r + 2 ≤ (L : ℝ) ^ m
def RadiusIndependent (P : Conventions.StandingParameters) (β : ℝ) (n : ℕ) : Prop :=
  ∀ F ∈ separatedLipschitzSet n, ∃ z : ℂ, ∀ r : ℝ, IsAdmissibleRadius P.L P.m r →
    (∀ i, tsupport (F i) ⊆ originBall (ENNReal.ofReal r)) →
      FitsOnTorus P.L P.m r F ∧ cumulantOfFamily P.L P.m P.K β F = z
def FamilyFunctionalRealAdditive (P : Conventions.StandingParameters) (β : ℝ) (n : ℕ)
    (r : ℝ) : Prop :=
  ∀ F ∈ separatedLipschitzSetIn n (ENNReal.ofReal r),
    (cumulantOfFamily P.L P.m P.K β F).im = 0 ∧
    (∀ (k : Fin n) (g : (Fin 4 → ℝ) → ℝ),
      Function.update F k g ∈ separatedLipschitzSetIn n (ENNReal.ofReal r) →
      Function.update F k (F k + g) ∈ separatedLipschitzSetIn n (ENNReal.ofReal r) →
      cumulantOfFamily P.L P.m P.K β (Function.update F k (F k + g)) =
        cumulantOfFamily P.L P.m P.K β F +
          cumulantOfFamily P.L P.m P.K β (Function.update F k g)) ∧
    (∀ (k : Fin n) (c : ℝ),
      Function.update F k (c • F k) ∈ separatedLipschitzSetIn n (ENNReal.ofReal r) →
      cumulantOfFamily P.L P.m P.K β (Function.update F k (c • F k)) =
        (c : ℂ) * cumulantOfFamily P.L P.m P.K β F) ∧
    ∀ k : Fin n, F k = 0 → cumulantOfFamily P.L P.m P.K β F = 0
def claim : Prop :=
  MixedCumulantRealLinear ∧
    ∀ (P : Conventions.StandingParameters) (β : ℝ) (n : ℕ), 0 < β → 1 ≤ n →
      (∀ f : Fin n → P.Torus → ℝ, BoundedComponents f → CumulantRealized P β f) ∧
      LipschitzSubspace P ∧
      FunctionalRealLinear P β n ∧
      RadiusIndependent P β n ∧
      ∀ r : ℝ, IsAdmissibleRadius P.L P.m r → FamilyFunctionalRealAdditive P β n r
end Multilinearity
end TorusCumulants
end YangMills.Construction
