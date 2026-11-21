import YangMills.Construction.ResponseInTheExpansion.DensityOfASettingIsLive
import YangMills.Construction.ResponseInTheExpansion.ResponseReadsItsSite
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
theorem chartResponse_dependsOnlyOnSite (hLive : WeightedResponses.ChartDensitySupportedOnLiveStates) :
    ResponseInTheExpansion.chartResponseDependsOnlyOnSite := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ K => ?_⟩
  obtain ⟨y₀, hy₀⟩ := hLive T hT
  refine ⟨max y₀ T.floorMin, fun y hy R A _ hAt n _ s hn hs z h h' hr => ?_⟩
  obtain ⟨a₁, a₂⟩ := max_le_iff.mp hy
  have hR := hAt.onFamily
  have hbd := hAt.admissible.bounds
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hside : TorusLumps.IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hnL : R.params.n₀ ≤ n * R.params.side := le_trans hn (Nat.le_mul_of_pos_right _ hLpos)
  have hσ : 0 < R.params.threshold := by
    rw [hR.params_eq]
    exact hT.σ_pos
  have hcold : TorusFields.IsCold R.params.threshold (TorusFields.trivialField (n * R.params.side)) := by
    intro x μ ν _
    simpa [TorusFields.curvature, TorusFields.holonomy, TorusFields.trivialField] using hσ
  have hP := hbd.cold_reads (n * R.params.side) hnL z (TorusFields.trivialField _) hcold h h' hr
  unfold WeightedResponses.chartResponse StepSettings.weightedMean
  congr 1
  refine integral_congr_ae (ae_of_all _ fun η => ?_)
  by_cases hd : WeightedResponses.chartDensity s η = 0
  · simp only [hd, mul_zero]
  · have hl := hy₀ y a₁ R hR n s hn hs η hd
    have hQ := hbd.hull_reads (n * R.params.side) hside z (s.field η) s.support s.labelling hl h h' hr
    simp only [WeightedResponses.centeredHullResponse, hQ, hP]
end YangMills.Construction.ResponseInTheExpansion
end
