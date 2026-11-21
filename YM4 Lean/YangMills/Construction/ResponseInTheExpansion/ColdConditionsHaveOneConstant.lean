import YangMills.Construction.ResponseInTheExpansion.ConditionsFromHalfBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.TorusFields YangMills.Construction.ShareFamilies YangMills.Construction.BlockAverages
def UnitResponseInvariant (ℓ : StepParameters) {t : ℕ} (P : ColdResponse ℓ.side t) : Prop :=
  ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (g : TorusIsometry) (y : TorusSite n) (W W' : TorusField n), IsCold ℓ.threshold W →
    g.Transports W W' → P n (g.mapSite y) W' (constOneWeight _) = P n y W (constOneWeight _)
def ColdResponseCoeffUniqueStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ y : ℝ, T.floorMin ≤ y →
    ∀ (K : ResponseParameters) (t : ℕ) (x c c' Ca : ℝ) (P : ColdResponse (T.stepParameters y).side (t + 1))
      (Ra Rb Ra' Rb' : LocalDensity),
      0 < K.η₃ → K.η₃ ≤ 1 → 0 ≤ K.Kb → 0 < x → LevelShareBounds (T.stepParameters y) t Ca →
      SumInvariantUnderIsometries (T.stepParameters y)
        (levelShareFamily (T.stepParameters y).coupling (T.stepParameters y).side (t + 1)) →
      UnitResponseInvariant (T.stepParameters y) P →
      ColdResponseBounds (T.stepParameters y) K (t + 1) x c P Ra Rb →
      ColdResponseBounds (T.stepParameters y) K (t + 1) x c' P Ra' Rb' → c = c'
end YangMills.Construction.ResponseInTheExpansion
end
