import YangMills.Construction.TorusOrFourSpace.ClosedBallsAndCompactSetsInBalls
import YangMills.Construction.TorusOrFourSpace.CompactnessAndLiftsOfClosedBallsAndOriginBalls
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
theorem closedBallsCompactAndCover_holds
    (hBallFacts : BallCompactnessAndTorusLifts) :
    ClosedBallsCompactAndCover := by
  intro D
  obtain ⟨hCpt, -, -, hLifts, -, hOrig, hExh, -⟩ := hBallFacts D
  refine ⟨hCpt, ⟨hLifts, fun ρ hρ _ => hOrig ρ hρ⟩, hExh, ?_⟩
  intro E S R _ hR hD
  rcases S.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
  · exact ⟨closedBallAbout D E (origin D E) R, ⟨hR, origin D E, rfl⟩, Set.empty_subset _⟩
  · refine ⟨closedBallAbout D E w R, ⟨hR, w, rfl⟩, fun y hy => ?_⟩
    have hBound : ENNReal.ofReal (quotDist D E y w) ≤ setDiam D E S :=
      le_iSup₂_of_le y hy (le_iSup₂_of_le w hw le_rfl)
    exact (ENNReal.ofReal_le_ofReal_iff hR.le).1 (hBound.trans hD)
end YangMills.Construction.PeriodicSpace
