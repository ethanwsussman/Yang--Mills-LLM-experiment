import YangMills.Construction.RotationInvariance.SelectionAtALabelledConfigurationMappedToItselfByARotation
import Mathlib
set_option autoImplicit false
open Complex (I)
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals.RotationFixedSelection
theorem holds_of_distinctHarmonics (hHarm : DistinctHarmonics.Holds) : Holds := by
  intro m S d n hn c hc t u σ hRot hLab h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  obtain ⟨-, -, hPerm, hTransl, hRotInv, -, -, -, -⟩ :=
    hHarm m S d (k + 1) (by omega) h c.labelVec
  have hTranslInj : ∀ (y : Fin (k + 2) → RealPlane) (v : RealPlane),
      y ∈ injectivePointTuples (k + 2) → translateTuple y v ∈ injectivePointTuples (k + 2) := by
    intro y v hy i j hij
    exact hy (add_right_cancel hij)
  have hPermInj : permuteTuple σ c.points ∈ injectivePointTuples (k + 2) := by
    intro i j hij
    exact σ.injective (hc hij)
  have hImg : translateTuple
      (mapPoints (rotate t) (translateTuple c.points (-u))) u =
        permuteTuple σ c.points := by
    funext i
    have hi := hRot i
    rw [sub_eq_add_neg, add_comm] at hi
    exact hi
  have hRotInj :
      mapPoints (rotate t) (translateTuple c.points (-u)) ∈
        injectivePointTuples (k + 2) := by
    have hBack := hTranslInj _ (-u) hPermInj
    rw [← hImg] at hBack
    have hCancel : translateTuple (translateTuple
        (mapPoints (rotate t) (translateTuple c.points (-u))) u) (-u) =
          mapPoints (rotate t) (translateTuple c.points (-u)) := by
      funext i
      exact add_neg_cancel_right _ _
    rwa [hCancel] at hBack
  have hLabFixed : permuteTuple σ c.labelVec = c.labelVec := funext hLab
  have hAdjointFineSiteAverage := hPerm σ c.points hc
  rw [hLabFixed, ← hImg, hTransl u _ hRotInj,
    hRotInv _ (hTranslInj _ _ hc) t, hTransl (-u) _ hc] at hAdjointFineSiteAverage
  show (1 - Complex.exp (4 * I * (h : ℂ) * (t : ℂ))) *
    distinctHarmonic S d.angle c.labelVec h c.points = 0
  rw [sub_mul, one_mul, hAdjointFineSiteAverage, sub_self]
end EuclideanFunctionals.RotationFixedSelection
end YangMills.Construction
