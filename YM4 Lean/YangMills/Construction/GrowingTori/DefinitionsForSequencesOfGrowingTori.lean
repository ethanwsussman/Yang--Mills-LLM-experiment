import YangMills.Construction.Lattice.RemaindersOfTheFlowOfTheConstruction
import YangMills.Construction.Parameters.OrderOfChoice
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GrowingTori
def HighThresholdCeiling (T : ParameterChoice.DerivedConstants)
    (c : ParameterChoice.ChoiceUpToCoupling) : Prop :=
  c.γH ≤ (c.γ ^ (-2 : ℤ) + ParameterChoice.doubledFiniteCoefficient T c.L + 1) ^ (-(1 / 2) : ℝ)
theorem highThresholdCeiling_of_couplingConstraints {T : ParameterChoice.DerivedConstants}
    {N : ParameterChoice.ExternalConstants} {c : ParameterChoice.ChoiceUpToCoupling}
    (h : ParameterChoice.CouplingConstraints T N c) : HighThresholdCeiling T c :=
  h.γH_ceiling
structure ParameterConstraints (T : ParameterChoice.DerivedConstants)
    (c : ParameterChoice.FullChoice) : Prop where
  factor_admissible : Conventions.IsAdmissibleBlockingFactor c.L
  M_eq_pow : ∃ m' : ℕ, c.M = c.L ^ m'
  exponent_lowerBound : ParameterChoice.ExponentLowerBound (c.r : ℝ)
  c₂_nonneg : 0 ≤ T.c₂ c.L
  Cβ_nonneg : 0 ≤ T.Cβ c.toChoiceUpToRadii
  CPrime_pos : 0 < T.CPrime c.toChoiceUpToRadii
  γ_pos : 0 < c.γ
  γH_pos : 0 < c.γH
  γH_le_ceiling : HighThresholdCeiling T c.toChoiceUpToCoupling
  γJ_pos : 0 < c.γJ
  γJ_le_γH : c.γJ ≤ c.γH
  gap_lowerBound : ParameterChoice.GapLowerBound c.L (c.gapNumber : ℝ)
structure GrowthParameters where
  constants : ParameterChoice.DerivedConstants
  choice : ParameterChoice.FullChoice
  admissible : ParameterConstraints constants choice
  activityKind : PeriodicLattice.ActivityDomainKind
namespace GrowthParameters
variable (D : GrowthParameters)
abbrev L : ℕ := D.choice.L
abbrev upToCoupling : ParameterChoice.ChoiceUpToCoupling := D.choice.toChoiceUpToCoupling
abbrev width : ℝ := FlowConstants.widthSharp D.constants D.upToCoupling
abbrev remainders : InfiniteLattice.CutoffRemainders D.choice :=
  PeriodicLattice.CubesOfStep.constructionRemainders D.constants D.choice D.activityKind
abbrev window (K : ℕ) (g : ℝ) : Set ℝ :=
  FlowConstants.flowFirstPassageWindow D.constants D.choice K D.activityKind (D.remainders K) g
def standingParams (K m : ℕ+) : Conventions.StandingParameters :=
  ⟨D.L, D.admissible.factor_admissible, K, m⟩
theorem one_le_M : 1 ≤ D.choice.M := by
  obtain ⟨m', h⟩ := D.admissible.M_eq_pow
  have hL : 0 < D.choice.L := by
    have := D.admissible.factor_admissible.2
    omega
  rw [h]
  exact Nat.one_le_pow _ _ hL
theorem width_pos : 0 < D.width := by
  have hp : 0 < D.choice.γ ^ (D.choice.κ₀ - 8) := Real.rpow_pos_of_pos D.admissible.γ_pos _
  have hC := mul_pos D.admissible.CPrime_pos hp
  have hβ := D.admissible.Cβ_nonneg
  show 0 < FlowConstants.widthSharp D.constants D.upToCoupling
  unfold FlowConstants.widthSharp FlowConstants.flowError
  exact add_pos_of_nonneg_of_pos hβ hC
def IsReferenceCoupling (g : ℝ) : Prop := 0 < g ∧ g ≤ D.choice.γJ
end GrowthParameters
structure FirstPassagePoint (D : GrowthParameters) (g : ℝ) where
  K : ℕ+
  β : ℝ
  mem_window : β ∈ D.window K g
inductive Ambient (L : ℕ) where
  | euclidean
  | torus (ℓ : ℝ) (hℓ : ℓ ∈ PeriodicLattice.torusSides L)
namespace Ambient
variable {L : ℕ}
def Point : Ambient L → Type
  | euclidean => Fin 4 → ℝ
  | torus ℓ _ => TorusMetric.Torus4 ℓ
def separation : (E : Ambient L) → E.Point → E.Point → ℝ
  | euclidean => fun (u v : Fin 4 → ℝ) => TorusMetric.euclidNormVec (u - v)
  | torus ℓ _ => fun (u v : TorusMetric.Torus4 ℓ) => TorusMetric.torusEuclidNorm (u - v)
end Ambient
end YangMills.Construction.GrowingTori
end
