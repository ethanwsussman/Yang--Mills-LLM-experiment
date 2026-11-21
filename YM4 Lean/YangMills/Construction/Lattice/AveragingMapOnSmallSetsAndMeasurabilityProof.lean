import YangMills.Construction.Averaging.AveragingMapRealAnalyticAtSmallRadii
import YangMills.Construction.Averaging.EverySmallRadiusServes
import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSet
import YangMills.Construction.Lattice.AveragingMapIsABorelMap
import YangMills.Construction.Lattice.AveragingMapOnSmallSetsAndMeasurability
import YangMills.Construction.Lattice.ThreeAveragingCaseSetsAreBorel
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.PeriodicLattice
theorem blockAverageSmallSetAndMeasurable_holds
    (hRadius : Averaging.SmallRadius.EverySmallRadiusSuffices)
    (hAnalytic : Averaging.BlockAverageRealAnalyticOnSmallFields)
    (hBorel : CaseSetsMeasurableStatement)
    (hCont : BlockAverageContinuousOnEachCaseSet)
    (hMap : BlockAverageIsBorelMap) :
    BlockAverageSmallSetAndMeasurable := by
  intro s k hk
  have hω : Averaging.smoothingRadius s.L ∈ Ioc (0 : ℝ) (averagingRadiusCap s.L) :=
    Averaging.isSmoothingRadius_smoothingRadius s.isAdmissible.1 s.isAdmissible.2
  refine ⟨fun c hc => ⟨⟨fun U hU => ?_, fun _ => hAnalytic s _ hω k hk c hc _⟩, hBorel s k hk c hc,
    hCont s k hk c hc⟩, hMap s k hk⟩
  have hC := hRadius s _ hω k hk c
  exact ⟨hU.2, fun x hx => (hC.contourMean_spec U hU c.source (Or.inl rfl) x hx).1,
    fun x hx => (hC.contourMean_spec U hU c.target (Or.inr rfl) x hx).1,
    fun x hx => (hC.crossingDefect_near hc U hU x hx).2.trans (by norm_num)⟩
end YangMills.Construction.PeriodicLattice
