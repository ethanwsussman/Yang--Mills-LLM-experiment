import YangMills.Construction.LawInAState.MarksOnABox
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
def IsWellLocalizedNear (L K k m R : ℕ) [NeZero L] (o : TorusFields.TorusSite (BoxResponses.boxSide L K k))
    (f : InfiniteLattice.AmbientSpace → ℝ) : Prop :=
  ∀ v ∈ StateLaws.shiftSet m, BoxMarks.weightSitesOf L K k (StateLaws.translateBy L K k v f) ⊆
    ResponseInTheExpansion.supBall o (3 * (R : ℝ) / 32)
def boxProductsStatement : Prop :=
  StateLaws.HoldsForShapes fun Tb y Kr Xi vt => ∀ (C₁ c₁ : ℝ) (Cj xp : ℕ → ℝ), 0 < c₁ → ∃ C d₀ : ℝ, 0 < d₀ ∧
    ∀ d : ℝ, 0 < d → d ≤ d₀ →
    ∀ (K : ℕ) (β : ℝ) (al : ℕ → ℝ) (T : WeightedResponses.StageTower (Tb.stepParameters y)),
      BoxResponses.IsStateChain Tb y Kr Xi d K β al T →
    ∀ (k m R : ℕ) (x : ℝ), k = StateLaws.separationLevel (Tb.stepParameters y) β K d →
      x = StateLaws.couplingAtSeparation (Tb.stepParameters y) β K d →
      R = StateLaws.boxRadius x → m = StateLaws.averagingRadius x →
      16 * R < BoxResponses.boxSide (Tb.stepParameters y).side K k →
    ∀ (f h : InfiniteLattice.AmbientSpace → ℝ), StateLaws.IsNormalizedTestPair d vt f h →
    ∀ (o : TorusFields.TorusSite (BoxResponses.boxSide (Tb.stepParameters y).side K k)),
      IsWellLocalizedNear (Tb.stepParameters y).side K k m R o f →
      IsWellLocalizedNear (Tb.stepParameters y).side K k m R o h →
    ∀ (c : BoxGaussian.BoxChart T k o R) (c₀ : ℝ),
      BoxMarks.IsGoodChart T β K k c x C₁ c₀ (C₁ * (R : ℝ) ^ 9 * x ^ (-(1 / 2) : ℝ) * Real.log x ^ 3)
        (C₁ * (R : ℝ) ^ (-(2 / 3) : ℝ) * BoxGaussian.boxScale x * Real.log x) Cj xp →
    ∀ (κ κ' : (Fin 4 → ℤ) → TorusFields.TorusSite (BoxResponses.boxSide (Tb.stepParameters y).side K k) →
        TorusFields.TorusPlaquette (BoxResponses.boxSide (Tb.stepParameters y).side K k) →
        TorusFields.TorusPlaquette (BoxResponses.boxSide (Tb.stepParameters y).side K k) → ℝ)
        (κ₀ κ₀' : (Fin 4 → ℤ) → ℝ),
      BoxMarks.IsBoxKernelFamily T β al K k m c C₁ c₁
          (C₁ * ((vt * StateLaws.lengthInSites (Tb.stepParameters y).side K k d)⁻¹ + Real.exp (-(c₁ * R))))
          (C₁ * StateLaws.lengthInSites (Tb.stepParameters y).side K k d ^ 4 * (R : ℝ) ^ 8 *
            BoxGaussian.boxScale x ^ 3 + Real.exp (-(c₁ * R)))
          (fun v => StateLaws.translateBy (Tb.stepParameters y).side K k v f) κ κ₀ →
      BoxMarks.IsBoxKernelFamily T β al K k m c C₁ c₁
          (C₁ * ((vt * StateLaws.lengthInSites (Tb.stepParameters y).side K k d)⁻¹ + Real.exp (-(c₁ * R))))
          (C₁ * StateLaws.lengthInSites (Tb.stepParameters y).side K k d ^ 4 * (R : ℝ) ^ 8 *
            BoxGaussian.boxScale x ^ 3 + Real.exp (-(c₁ * R)))
          (fun v => StateLaws.translateBy (Tb.stepParameters y).side K k v h) κ' κ₀' →
        eLpNorm (fun u => BoxResponses.shiftAveragedProduct T β al K k m
            (fun v => StateLaws.translateBy (Tb.stepParameters y).side K k v f)
            (fun v => StateLaws.translateBy (Tb.stepParameters y).side K k v h) u -
            BoxMarks.boxCoefficient (Tb.stepParameters y).coupling (Tb.stepParameters y).side k m o R x κ κ') 16
            (BoxResponses.stageLaw T β K k) ≤
          ENNReal.ofReal (C * x ^ (-(2 + 1 / 130) : ℝ)) ∧
        eLpNorm (BoxResponses.shiftAveragedResponse T β al K k m
            fun v => StateLaws.translateBy (Tb.stepParameters y).side K k v f) 16
            (BoxResponses.stageLaw T β K k) ≤
          ENNReal.ofReal (C * x ^ (-(1 + 1 / 130) : ℝ)) ∧
        eLpNorm (BoxResponses.shiftAveragedResponse T β al K k m
            fun v => StateLaws.translateBy (Tb.stepParameters y).side K k v h) 16
            (BoxResponses.stageLaw T β K k) ≤
          ENNReal.ofReal (C * x ^ (-(1 + 1 / 130) : ℝ))
end YangMills.Construction.StateLaws
end
