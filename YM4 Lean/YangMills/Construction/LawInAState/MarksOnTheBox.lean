import YangMills.Construction.LawInAState.MarksOnABox
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
def boxResponsesQuadraticStatement : Prop :=
  StateLaws.HoldsForShapes fun Tb y Kr Xi vt => ∀ (C₁ : ℝ) (Cj xp : ℕ → ℝ), ∃ C cc d₀ : ℝ, 0 < cc ∧ 0 < d₀ ∧
    ∀ d : ℝ, 0 < d → d ≤ d₀ →
    ∀ (K : ℕ) (β : ℝ) (al : ℕ → ℝ) (T : WeightedResponses.StageTower (Tb.stepParameters y)),
      BoxResponses.IsStateChain Tb y Kr Xi d K β al T →
    ∀ (k m R : ℕ) (x : ℝ), k = StateLaws.separationLevel (Tb.stepParameters y) β K d →
      x = StateLaws.couplingAtSeparation (Tb.stepParameters y) β K d →
      R = StateLaws.boxRadius x → m = StateLaws.averagingRadius x →
    ∀ (f h : InfiniteLattice.AmbientSpace → ℝ), StateLaws.IsNormalizedTestPair d vt f h →
    ∀ (o : TorusFields.TorusSite (BoxResponses.boxSide (Tb.stepParameters y).side K k)),
      BoxMarks.IsLocalizedNear (Tb.stepParameters y).side K k m R o f →
      BoxMarks.IsLocalizedNear (Tb.stepParameters y).side K k m R o h →
    ∀ (c : BoxGaussian.BoxChart T k o R) (c₀ ε φ₀ : ℝ), BoxMarks.IsGoodChart T β K k c x C₁ c₀ ε φ₀ Cj xp →
      ∃ (κ κ' : (Fin 4 → ℤ) → TorusFields.TorusSite (BoxResponses.boxSide (Tb.stepParameters y).side K k) →
          TorusFields.TorusPlaquette (BoxResponses.boxSide (Tb.stepParameters y).side K k) →
          TorusFields.TorusPlaquette (BoxResponses.boxSide (Tb.stepParameters y).side K k) → ℝ)
          (κ₀ κ₀' : (Fin 4 → ℤ) → ℝ),
        BoxMarks.IsBoxKernelFamily T β al K k m c C cc
            (C * ((vt * StateLaws.lengthInSites (Tb.stepParameters y).side K k d)⁻¹ + Real.exp (-(cc * R))))
            (C * StateLaws.lengthInSites (Tb.stepParameters y).side K k d ^ 4 * (R : ℝ) ^ 8 *
              BoxGaussian.boxScale x ^ 3 + Real.exp (-(cc * R)))
            (fun v => StateLaws.translateBy (Tb.stepParameters y).side K k v f) κ κ₀ ∧
        BoxMarks.IsBoxKernelFamily T β al K k m c C cc
            (C * ((vt * StateLaws.lengthInSites (Tb.stepParameters y).side K k d)⁻¹ + Real.exp (-(cc * R))))
            (C * StateLaws.lengthInSites (Tb.stepParameters y).side K k d ^ 4 * (R : ℝ) ^ 8 *
              BoxGaussian.boxScale x ^ 3 + Real.exp (-(cc * R)))
            (fun v => StateLaws.translateBy (Tb.stepParameters y).side K k v h) κ' κ₀'
end YangMills.Construction.StateLaws
end
