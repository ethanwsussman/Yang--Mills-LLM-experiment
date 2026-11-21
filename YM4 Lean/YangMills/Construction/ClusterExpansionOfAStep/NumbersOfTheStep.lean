import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages
abbrev LatticeBond : Type := (Fin 4 → ℤ) × Fin 4
def offsetNorm (h : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (h i).natAbs
def bondPairDiam (c c' : LatticeBond) : ℕ :=
  max (max (offsetNorm c.1) (offsetNorm c'.1)) (offsetNorm (c.1 - c'.1))
def planeCurvature (X : imaginaryQuaternions) (μ ν : Fin 4) : Fin 4 → Fin 4 → imaginaryQuaternions :=
  fun α β => if α = μ ∧ β = ν then X else if α = ν ∧ β = μ then -X else 0
def quaternionI : imaginaryQuaternions := ⟨⟨0, 1, 0, 0⟩, rfl⟩
def unitPlaneCurvature : Fin 4 → Fin 4 → imaginaryQuaternions := planeCurvature quaternionI 0 1
def potentialNorm (c : LatticeBond) : ℝ := ‖linearPotential unitPlaneCurvature c‖
def expansionWeight (rt n₁ : ℝ) (m : ℕ) : ℝ :=
  max 1 (((m : ℝ) / n₁) ^ 16000) * Real.exp (rt / 2 ^ 10 * m)
def potentialDecaySum (rt : ℝ) : ℝ :=
  ∑' cc : LatticeBond × LatticeBond, potentialNorm cc.1 * potentialNorm cc.2 *
    Real.exp (-(rt / 2 ^ 6 * bondPairDiam cc.1 cc.2))
def potentialWeightSum (rt n₁ : ℝ) : ℝ :=
  2 * ∑' cc : LatticeBond × LatticeBond, potentialNorm cc.1 * potentialNorm cc.2 /
    expansionWeight rt n₁ (bondPairDiam cc.1 cc.2)
def weightGrowthSup (rt n₁ : ℝ) : ℝ :=
  ⨆ m : ℕ, expansionWeight rt n₁ m * Real.exp (-(2 * (rt / 2 ^ 10) * m))
def maxOfFirstFour (N : ℕ → ℝ) : ℝ := max (max (N 0) (N 1)) (max (N 2) (N 3))
def baseConstant (Cs rt : ℝ) : ℝ := Cs * potentialDecaySum rt + 1
def expansionConstant (Cs Na rt n₁ : ℝ) : ℝ :=
  weightGrowthSup rt n₁ * (2 * Cs + baseConstant Cs rt * Na) + baseConstant Cs rt
end YangMills.Construction.TorusLumps
end
