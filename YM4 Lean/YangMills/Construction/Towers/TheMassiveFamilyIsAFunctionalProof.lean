import YangMills.Construction.Towers.TheMassiveFamilyIsAFunctional
import YangMills.Construction.Towers.TheMassiveFunctionalIsGaugeInvariant
import YangMills.Construction.Towers.TheMassiveFunctionalIsInvariantUnderIsometries
import YangMills.Construction.Towers.TheMassiveFunctionalIsRealAnalyticNearOne
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveStiffnessFunctions
theorem fieldFamilyIsFunctional_holds (hg : MassiveFunctionals.GaugeInvariance.Claim)
    (hi : MassiveLogDet.IsometryInvariance) (ha : MassiveLogDet.AnalyticNearIdentity) :
    FieldFamilyIsFunctional := by
  intro L hL z hz
  obtain ⟨s₀, hs₀, hlarge⟩ := ha L hL z hz
  refine ⟨s₀, hs₀, fun s hs hle m hm hside => ?_⟩
  refine
    { analytic := hlarge s hs hle m hm hside
      map_identity := ?_
      locallyGauge := ?_
      globalGauge := ?_
      symmetry := ?_ }
  · exact sub_self _
  · refine ⟨Set.univ, Filter.Eventually.of_forall fun _ => trivial, ?_⟩
    exact eventually_nhdsWithin_of_forall fun U hU v hv _ => hg L hL z hz m hm U hU v hv
  · refine eventually_nhdsWithin_of_forall fun U hU g hgr => ?_
    exact hg L hL z hz m hm U hU _ fun _ => hgr
  · exact eventually_nhdsWithin_of_forall fun U hU σ hσ hμ => hi L hL z hz m hm U hU σ hσ hμ
end YangMills.Construction.Tower.MassiveStiffnessFunctions
end
