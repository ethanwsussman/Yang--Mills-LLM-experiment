import YangMills.Construction.ResponseInTheExpansion.ColdConditionsOfAResponse
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace WeightedResponses
structure LevelShareBounds (ℓ : TorusLumps.StepParameters) (t : ℕ) (Ca : ℝ) : Prop where
  isCurvatureFamily : TorusLumps.IsCurvatureFamily ℓ Ca (ShareFamilies.levelShareFamily ℓ.coupling ℓ.side (t + 1))
  hasForm : TorusLumps.HasCurvatureForm (ShareFamilies.levelShareFamily ℓ.coupling ℓ.side (t + 1)) 1
  sum_centered_eq : ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ V : TorusFields.TorusField n, TorusFields.IsCold ℓ.threshold V →
    ∑ z, TorusLumps.centered (ShareFamilies.levelShareFamily ℓ.coupling ℓ.side (t + 1)) n z V =
      TorusFields.actionAtLevel ℓ.coupling ℓ.side (t + 1) Finset.univ V
  share_trivial : ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ y : TorusFields.TorusSite n,
    StepCosts.levelShare ℓ.coupling ℓ.side (t + 1) Finset.univ y (TorusFields.trivialField n) = 0
def ColdBoundsFromHalfBounds : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (K : ResponseParameters) (t : ℕ) (x c b Ca : ℝ) (P : ColdResponse ℓ.side (t + 1))
    (G : TorusLumps.LocalDensity),
    ℓ.Admissible → 0 < K.η₃ → K.η₃ ≤ 1 → 0 ≤ K.Ka → 0 ≤ K.Kb → 0 < x → LevelShareBounds ℓ t Ca →
    HalfDensityBounds ℓ (K.Ka * x ^ (-(1 / 2) : ℝ)) K.η₃ (responseSubShare ℓ.coupling P c) →
    HalfDensityBounds ℓ (K.Kb * x⁻¹) K.η₃ G → IsTotalRemainder ℓ P c G → RemainderBounds ℓ K (t + 1) P →
    TorusLumps.HasCurvatureForm (responseSubShare ℓ.coupling P c) b → TorusLumps.HasCurvatureForm G b →
    |b| * Ca ≤ K.Ka * x ^ (-(1 / 2) : ℝ) / 2 → |b| * Ca ≤ K.Kb * x⁻¹ / 2 →
    ∃ Ra Rb : TorusLumps.LocalDensity, ColdResponseBounds ℓ K (t + 1) x (c + b) P Ra Rb
end WeightedResponses
end YangMills.Construction
end
