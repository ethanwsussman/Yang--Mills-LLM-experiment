import YangMills.Construction.TorusOrFourSpace.CompactnessAndLiftsOfClosedBallsAndOriginBallsProof
import YangMills.Construction.TorusOrFourSpace.EffectiveConstantHoldsOnATorus
import YangMills.Construction.TorusOrFourSpace.FromBallsOfOneRadiusToAllSeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
namespace TorusEffectiveBound
private theorem params_side_pos (P : Params) : 0 < P.side := by apply _root_.YangMills.SharedProofs.p25685 <;> assumption
theorem claim_holds (hB : BallsToSeparated.TorusBoundFromBallsOfOneRadius) : Claim := by
  intro P θ Θ C n hn d hd F hF hbd
  have hs := params_side_pos P
  have hA : allowedRadii P torus = Set.Ioo 0 (P.side / 4) := rfl
  have hr : 0 < ballRadius P θ torus := mul_pos θ.val_mem.1 hs
  have hc : 0 ≤ C.val n d (ballRadius P θ torus) := C.nonneg n hn d _ hd hr
  have hm := hB P θ Θ n hn d _ hd hc F hF hbd
  have he : ∀ R ∈ Set.Ici (P.side / 4), effConst Θ torus C n d R =
      thetaNumber Θ torus ^ n * C.val n d (ballRadius P θ torus) := by
    intro R hR
    have hout : R ∉ allowedRadii P torus := by
      rw [hA]
      exact fun h => absurd h.2 (not_lt.mpr hR)
    unfold effConst
    rw [if_neg hout]
  refine ⟨fun R => ⟨fun hR => ⟨?_, ?_⟩, fun hR => ?_⟩, fun R hR => ⟨he R hR, fun h hh => ?_⟩⟩
  · have hR' : P.side / 4 ≤ R := hR
    linarith
  · rw [hA]
    exact fun h => absurd h.2 (not_lt.mpr hR)
  · rw [hA] at hR
    by_contra hlt
    exact hR.2 ⟨hR.1, not_le.mp hlt⟩
  · rw [he R hR]
    exact hm h hh
end TorusEffectiveBound
end YangMills.Construction.PeriodicSpace
