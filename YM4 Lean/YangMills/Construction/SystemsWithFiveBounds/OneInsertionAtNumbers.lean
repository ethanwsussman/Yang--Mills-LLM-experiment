import YangMills.Construction.SystemsWithFiveBounds.BoundsAtNumbers
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open TestFunctions (IsLipschitzFor euclidDistR4 closedBallR4 sharpNormR4)
open InfiniteLattice (AmbientSpace localObsAbove reflectionSeminorm timeConj)
open ChessboardTori (GridCell)
open ReflectionsAndOneInsertion (complexSmeared)
def SingleInsertionWithConstants : Prop :=
  ∀ (F : StatedSideFamily) (N : BoundConstants), BoundsHoldAt F N →
    ∀ (D : ChessboardTori.ChessboardSetup), D.L = F.L → F.IsFirstPassage D.K D.β →
    ∀ (c : GridCell D) (h : AmbientSpace → ℝ), IsLipschitzFor euclidDistR4 h →
      tsupport h ⊆ closedBallR4 c.centre (N.insertionRadiusRatio * c.side) → c.side ≤ 1 →
      InfiniteLattice.IsBoundedObservable (complexSmeared D h) ∧
      ∀ ρ ∈ F.stateSet D.L D.K D.β, ∀ ν ∈ F.stateSet D.L D.K D.β,
      ∀ P ∈ localObsAbove c.baseTime, ∀ Q ∈ localObsAbove c.baseTime,
        ‖∫ U, timeConj c.baseTime Q U *
            (complexSmeared D h U - ∫ V, complexSmeared D h V ∂ν) *
            (c.timeShift 1).actOn P U ∂ρ‖ ≤
          N.insertionConst * c.side ^ (-N.insertionExponent) * sharpNormR4 F.M h *
            reflectionSeminorm ρ c.baseTime Q * reflectionSeminorm ρ c.baseTime P
end YangMills.Construction.SystemsWithFiveBounds
end
