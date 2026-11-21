import YangMills.Construction.TorusOrFourSpace.CuttingAtAnyRadiusOnATorus
import YangMills.Construction.TorusOrFourSpace.EffectiveConstantsAtEveryRadius
import YangMills.Construction.TorusOrFourSpace.FromBallsOfOneRadiusToAllSeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.BallsToSeparated
open Kind
theorem torusBoundFromBallsOfOneRadius_holds (hcut : Kind.CutAtRadius.TorusCutAtAnyRadius) :
    TorusBoundFromBallsOfOneRadius := by
  intro D θ P n hn d c hd hc Ψ hΨ hbound h hh
  have hr := ballRadius_mem_allowedRadii D θ torus
  have hlt : ballRadius D θ torus < D.side / 4 := hr.2
  have hfam : Kind.CutAtRadius.IsCuttingFamily D (ballRadius D θ torus) P.bump :=
    { mem_unitInterval := P.subordinate.mem_unitInterval
      sum_eq_one := P.subordinate.sum_eq_one
      support_subset_ball := fun a => (bump_support_subset_ball P a).choose_spec.2 }
  obtain ⟨-, -, hnext⟩ := (hcut D (ballRadius D θ torus) hr.1).2 P.Idx P.bump hfam
  obtain ⟨htuples, hbounds⟩ := hnext n hn d hd
  exact hbounds c hc Ψ hΨ (fun g hg => hbound g ((htuples hlt g.1).1 hg).2) h hh
end YangMills.Construction.PeriodicSpace.BallsToSeparated
