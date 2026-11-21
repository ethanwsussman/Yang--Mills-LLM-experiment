import YangMills.Construction.Towers.AveragesAreContractions
import YangMills.Construction.Towers.CrossingAverageOnASide
import YangMills.Construction.Towers.CrossingAverageOnTheWhole
import YangMills.Construction.Towers.ScaledQOnASide
import YangMills.Construction.Towers.ScaledQOnTheWhole
import YangMills.Construction.Towers.ScaledROnASide
import YangMills.Construction.Towers.ScaledROnTheWhole
import YangMills.Construction.Towers.SiteAverageOnASide
import YangMills.Construction.Towers.SiteAverageOnTheWhole
import YangMills.Construction.Towers.SumsOverThePointsOfThePlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
theorem SmoothingContraction.claim_of_bounds
    (hCrossFull : Tower.CrossingSmoothingBound.NormBound)
    (hVertexFull : Tower.FullVertexSmoothing.Claim)
    (hQFull : Tower.RescaledQFullSpace.OpNormLeExp)
    (hRFull : Tower.WholeLatticeR.ConjugateBound)
    (hCross : Tower.CrossingSmoothingContraction.normAtMostOne)
    (hVertex : Tower.SideVertexSmoothing.Claim)
    (hQ : Tower.RescaledQFiniteSide.OpNormLeOne)
    (hR : Tower.RescaledRFiniteSide.OpNormLeOne)
    (hWaves : Tower.PlaneWaveSums.Claim) : Tower.SmoothingContraction.Claim := by
  intro L hL k hk
  have w0 : ∀ a : ℝ, Real.exp (2 * TorusMetric.l1NormVec 0 * a) = 1 := by
    intro a; simp [TorusMetric.l1NormVec]
  have w1 : ∀ a : ℝ, Real.exp (TorusMetric.l1NormVec 0 * a) = 1 := by
    intro a; simp [TorusMetric.l1NormVec]
  have w2 : Real.exp (2 * TorusMetric.l1NormVec 0) = 1 := by simp [TorusMetric.l1NormVec]
  have w3 : Real.exp (TorusMetric.l1NormVec 0) = 1 := by simp [TorusMetric.l1NormVec]
  refine ⟨⟨?_, fun θ => ⟨fun i hi => ⟨hCrossFull L hL k i hi θ, hVertexFull L hL k i hi θ⟩,
    hQFull L hL k hk θ, hRFull L hL k hk θ⟩⟩,
    fun n hn => ⟨fun _ _ _ _ _ _ _ => rfl, fun i hi => ⟨?_, ?_⟩, ?_, ?_⟩, hWaves L hL k hk⟩
  · intro i i' j j' _ _ T
    funext ι' ι
    simp [PeriodicOperators.expConj, PeriodicOperators.bilinDot,
      PeriodicOperators.toComplexVec]
  · rw [w0]; exact hCross L hL n k i hn hi
  · rw [w1]; exact hVertex L hL n k i hn hi
  · rw [w2]; exact hQ L hL n k hn hk
  · rw [w3]; exact hR L hL n k hn hk
end YangMills.Construction.Tower
end
