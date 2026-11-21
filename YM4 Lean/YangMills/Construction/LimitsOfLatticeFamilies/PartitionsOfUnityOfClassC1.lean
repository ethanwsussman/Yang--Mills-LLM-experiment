import YangMills.Construction.LimitsOfLatticeFamilies.CuttingDataOnTheTorus
import YangMills.Construction.LimitsOfLatticeFamilies.ReferenceRadiusPriceAndEffectiveConstants
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LatticeLimits.C1PartitionOfUnity
open ModelSpace
structure IsSmoothPartitionAtScale (s : Conventions.StandingParameters) (Y : ModelSpace) (a : ℝ)
    {I : Type*} (χ : I → c1CompactSupp s Y univ) : Prop where
  mem_Icc : ∀ i y, (χ i).1 y ∈ Icc (0 : ℝ) 1
  locallyFinite : ∀ K : Set (Y.Carrier s), IsCompactIn s Y K →
    {i | (K ∩ supportIn s Y (χ i).1).Nonempty}.Finite
  hasSum_one : ∀ y, HasSum (fun i => (χ i).1 y) 1
  support_subset_closedBall : ∀ i, ∃ x, supportIn s Y (χ i).1 ⊆ closedBall s Y x (2 * a)
  dist_le : ∀ i, ∀ y ∈ supportIn s Y (χ i).1, ∀ y' ∈ supportIn s Y (χ i).1,
    dist s Y y y' ≤ 4 * a
  lipNumber_le_gradSup : ∀ i,
    ENNReal.ofReal (TestFunctions.bestLipschitzConstant (dist s Y) (χ i).1) ≤
      ⨆ y, ENNReal.ofReal (TorusMetric.euclidNormVec (grad s Y (χ i).1 y))
  gradSup_le : ∀ i,
    ⨆ y, ENNReal.ofReal (TorusMetric.euclidNormVec (grad s Y (χ i).1 y)) ≤ ENNReal.ofReal (Real.pi / a)
def YieldsTorusPartitionData (s : Conventions.StandingParameters) (M : {M : ℕ // IsBlockScale s M}) (w : ℕ)
    [NeZero w] (a : ℝ) (χ : (Fin 4 → ZMod w) → c1CompactSupp s torus univ) : Prop :=
  (∀ r Θ : ℝ, r ∈ admissibleRadii s torus → 2 * a ≤ r → 1 ≤ Θ →
    (w : ℝ) ^ 4 * (1 + 40 * Real.pi * (M.1 : ℝ) * (w : ℝ) / s.side) ≤ Θ →
      IsTorusPartitionDatum s M.1 r (fun i => (χ i).1) Θ) ∧
  (w = 16 →
    IsTorusPartitionDatum s M.1 (refRadius s torus) (fun i => (χ i).1) (torusFactor M.1))
def Claim : Prop :=
  ∀ (s : Conventions.StandingParameters) (M : {M : ℕ // IsBlockScale s M}) (a : ℝ), 0 < a →
    (∃ χ : (Fin 4 → ℤ) → c1CompactSupp s euclidean univ, IsSmoothPartitionAtScale s euclidean a χ) ∧
    ∀ (w : ℕ) [NeZero w], 3 ≤ w → a = s.side / (w : ℝ) →
      ∃ χ : (Fin 4 → ZMod w) → c1CompactSupp s torus univ,
        IsSmoothPartitionAtScale s torus a χ ∧ YieldsTorusPartitionData s M w a χ
end YangMills.Construction.LatticeLimits.C1PartitionOfUnity
end
