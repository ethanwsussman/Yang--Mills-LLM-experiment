import YangMills.Construction.LawInAState.MarksOnABox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BoxMarks
open TorusFields WeightedResponses StateLaws BoxResponses
open InfiniteLattice (AmbientSpace)
def IsDeepInBox (L K k m R : ℕ) [NeZero L] (r : ℝ) (o : TorusSite (boxSide L K k))
    (f : AmbientSpace → ℝ) : Prop :=
  ∀ v ∈ shiftSet m, weightSitesOf L K k (translateBy L K k v f) ⊆
    ResponseInTheExpansion.supBall o ((R : ℝ) / 8 - r)
def boxCoefficientStatement : Prop :=
  HoldsForShapes fun Tb y Kr Xi vt => ∀ C₁ c₁ : ℝ, 0 < c₁ → ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (K : ℕ) (β : ℝ) (α : ℕ → ℝ) (T : StageTower (Tb.stepParameters y)), IsStateChain Tb y Kr Xi δ K β α T →
    ∀ (k m R : ℕ) (x : ℝ), k = separationLevel (Tb.stepParameters y) β K δ →
    x = couplingAtSeparation (Tb.stepParameters y) β K δ →
    R = boxRadius x → m = averagingRadius x → ∀ (f g : AmbientSpace → ℝ), IsNormalizedTestPair δ vt f g →
    3 / 4 ≤ α k → ∀ (o : TorusSite (boxSide (Tb.stepParameters y).side K k)),
    IsDeepInBox (Tb.stepParameters y).side K k m R (lengthInSites (Tb.stepParameters y).side K k δ) o f →
    IsDeepInBox (Tb.stepParameters y).side K k m R (lengthInSites (Tb.stepParameters y).side K k δ) o g →
    ∀ κ κ' : (Fin 4 → ℤ) → TorusSite (boxSide (Tb.stepParameters y).side K k) →
        TorusPlaquette (boxSide (Tb.stepParameters y).side K k) →
        TorusPlaquette (boxSide (Tb.stepParameters y).side K k) → ℝ,
      (∀ v ∈ shiftSet m, IsWeightKernel (Tb.stepParameters y).side k (α k) C₁ c₁
        (C₁ * ((vt * lengthInSites (Tb.stepParameters y).side K k δ)⁻¹ + Real.exp (-(c₁ * R))))
        (unitTorusWeight (Tb.stepParameters y).side K k
          (translateBy (Tb.stepParameters y).side K k v f)) (κ v)) →
      (∀ v ∈ shiftSet m, IsWeightKernel (Tb.stepParameters y).side k (α k) C₁ c₁
        (C₁ * ((vt * lengthInSites (Tb.stepParameters y).side K k δ)⁻¹ + Real.exp (-(c₁ * R))))
        (unitTorusWeight (Tb.stepParameters y).side K k
          (translateBy (Tb.stepParameters y).side K k v g)) (κ' v)) →
      ∃ ε : ℝ, |ε| ≤ C * lengthInSites (Tb.stepParameters y).side K k δ ^ (-(1 / 2) : ℝ) +
          C * x ^ (-(1 / 130) : ℝ) ∧
        boxCoefficient (Tb.stepParameters y).coupling (Tb.stepParameters y).side k m o R x κ κ' =
          α k ^ 2 * (9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * TestFunctions.inverseEighthKernel f g * (1 + ε)
end YangMills.Construction.BoxMarks
end
