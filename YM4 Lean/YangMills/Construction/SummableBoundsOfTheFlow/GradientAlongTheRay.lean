import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongAList
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace IteratedDerivative
variable {ι B T : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
def variableDirection (T : Type) [NormedAddCommGroup T] (u : ι → B) : (ι → B) × T := (u, 0)
def parameterDirections (ι B : Type) [NormedAddCommGroup B] {T : Type} (l : List T) : List ((ι → B) × T) :=
  l.map fun u => (0, u)
def rayGradientSum (f : (ι → B) × T → ℝ) (Q : Finset ι) (p : (ι → B) × T) : ℝ :=
  ∑ b ∈ Q, ∫ v in (0 : ℝ)..1, fderiv ℝ f (v • p.1, p.2) (Pi.single b (p.1 b), 0)
structure RayGradientBounds (f : (ι → B) × T → ℝ) (Q : Finset ι) (η : ι → B) (tl : List T) (A : ι → ℝ)
    (D : ι → ι → ℝ) : Prop where
  value_le : |derivAlong (rayGradientSum f Q) (parameterDirections ι B tl) (η, 0)| ≤
    ∑ b ∈ Q, ‖η b‖ * (A b + ∑ b', ‖η b'‖ * D b b')
  deriv_le : ∀ (b₀ : ι) (e : B),
    |derivAlong (rayGradientSum f Q) (parameterDirections ι B tl ++ [variableDirection T (Pi.single b₀ e)]) (η, 0)| ≤
      ‖e‖ * (∑ b ∈ Q, ‖η b‖ * D b b₀ + if b₀ ∈ Q then A b₀ + ∑ b', ‖η b'‖ * D b₀ b' else 0)
def RayGradientSumSmoothAndBounded : Prop :=
  ∀ (ι B T : Type) [Fintype ι] [DecidableEq ι] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup T] [NormedSpace ℝ T] (f : (ι → B) × T → ℝ) (Q : Finset ι) (η : ι → B) (tl : List T),
    (∀ v ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ((tl.length + 3 : ℕ) : WithTop ℕ∞) f (v • η, 0)) →
    ContDiffAt ℝ ((tl.length + 2 : ℕ) : WithTop ℕ∞) (rayGradientSum f Q) (η, 0) ∧
    (∀ (A : ι → ℝ) (D : ι → ι → ℝ), (∀ b b', 0 ≤ D b b') →
      (∀ (b : ι) (e : B), |derivAlong f (parameterDirections ι B tl ++ [variableDirection T (Pi.single b e)]) (0, 0)| ≤
        ‖e‖ * A b) →
      (∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ (b b' : ι) (e e' : B),
        |derivAlong f (variableDirection T (Pi.single b' e') :: (parameterDirections ι B tl ++
          [variableDirection T (Pi.single b e)])) (v • η, 0)| ≤ ‖e‖ * ‖e'‖ * D b b') →
      RayGradientBounds f Q η tl A D) ∧
    (tl = [] → ∀ (D : ι → ι → ℝ) (H : ι → ι → ι → ℝ), (∀ b b', 0 ≤ D b b') → (∀ b b' b'', 0 ≤ H b b' b'') →
      (∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ (b b' : ι) (e e' : B),
        |derivAlong f [variableDirection T (Pi.single b' e'), variableDirection T (Pi.single b e)] (v • η, 0)| ≤
          ‖e‖ * ‖e'‖ * D b b') →
      (∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ (b b' b'' : ι) (e e' e'' : B),
        |derivAlong f [variableDirection T (Pi.single b'' e''), variableDirection T (Pi.single b' e'),
          variableDirection T (Pi.single b e)] (v • η, 0)| ≤ ‖e‖ * ‖e'‖ * ‖e''‖ * H b b' b'') →
      ∀ (b₁ b₂ : ι) (e₁ e₂ : B),
        |derivAlong (rayGradientSum f Q) [variableDirection T (Pi.single b₂ e₂), variableDirection T (Pi.single b₁ e₁)]
          (η, 0)| ≤ ‖e₁‖ * ‖e₂‖ * (∑ b ∈ Q, ‖η b‖ * H b b₁ b₂ +
            (if b₁ ∈ Q then D b₁ b₂ else 0) + if b₂ ∈ Q then D b₂ b₁ else 0))
end IteratedDerivative
end YangMills.Construction
end
