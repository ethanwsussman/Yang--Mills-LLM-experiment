import YangMills.Construction.QuaternionicWilsonModel.TheTorusStatesHaveAMemberProof
import YangMills.Construction.TheStatementsProvedTogether.FromFarSpinsMoveAVariableAtOneLevelProof
import YangMills.Construction.QuaternionicWilsonModel.TheTopOfTheTrajectoryWithTheFlow
import YangMills.Construction.TotalDensitiesGiveASystem.TheTopOfTheTrajectory
import YangMills.Construction.WindowOfTheParameters.CoefficientAsAMixedMomentProof
import Mathlib

namespace YangMills.Construction.BackwardReduction

/-- The flow-bound conclusion already contains the exact exported trajectory
conclusion.  Its witnesses can be reused, avoiding a second parameter-selection
and small-coupling-interval construction. -/
theorem trajectoryTop_of_topWithFlowBound
    (h : TopAux.TopWithFlowBound.Statement) :
    TotalDensities.TrajectoryTopStatement := by
  obtain ⟨J, Lstar, hJ, hL⟩ := h
  refine ⟨J, Lstar, hJ, fun L hodd hge => ?_⟩
  obtain ⟨ℓ, Bs, c₅, γ, Nw, CT, _, _, _, _, _, hside, hdepth,
    hunit, hBs, hc₅, hγ, hCT, hNw, _, _, _, _, _, hcoupling⟩ := hL L hodd hge
  exact ⟨ℓ, Bs, c₅, γ, Nw, CT, hside, hdepth, hunit, hBs, hc₅,
    hγ, hCT, hNw, fun g hg => (hcoupling g hg).1⟩

end YangMills.Construction.BackwardReduction

namespace YangMills.Construction.TheStatementsProvedTogether
theorem top_with_flow_bound :
    YangMills.Construction.TopAux.TopWithFlowBound.Statement :=
  YangMills.Construction.TopAux.TopWithFlowBound.holds
    YangMills.Construction.TheStatementsProvedTogether.step_parameters_exist
    YangMills.Construction.TheStatementsProvedTogether.flow_passes
    YangMills.Construction.TheStatementsProvedTogether.pairs_tied_to_wilson_measure
    YangMills.Construction.TheStatementsProvedTogether.total_density_subseq_limit_exists
    YangMills.Construction.TheStatementsProvedTogether.exists_coupling_constants
    YangMills.Construction.TheStatementsProvedTogether.firstPassagePath_data
    YangMills.Construction.TheStatementsProvedTogether.expansionFlow_eq_totalFlow
theorem totalDensity_trajectory_top : YangMills.Construction.TotalDensities.TrajectoryTopStatement :=
  BackwardReduction.trajectoryTop_of_topWithFlowBound top_with_flow_bound
theorem top_limits_real_ne_zero :
    YangMills.Construction.QuaternionicWilsonModel.TopLimitsRealNonzero.MainStatement :=
  YangMills.Construction.QuaternionicWilsonModel.TopLimitsRealNonzero.mainStatement_holds
    YangMills.Construction.TheStatementsProvedTogether.totalDensity_trajectory_top
    YangMills.Construction.TheStatementsProvedTogether.testClasses_nonempty_all_scales
    YangMills.Construction.TheStatementsProvedTogether.torus_lipschitz_tuple_props
    YangMills.Construction.TheStatementsProvedTogether.torusCumulant_multilinear
    YangMills.Construction.TheStatementsProvedTogether.test_pair_transport_lift_dilation
theorem quaternion_model_eq_wilson_SU2 :
    YangMills.Construction.QuaternionModel.quaternionModelIsWilsonSU2Statement :=
  YangMills.Construction.QuaternionModel.quaternionModelIsWilsonSU2
    YangMills.Construction.TheStatementsProvedTogether.unit_quaternion_haar_trace_norm
    YangMills.Construction.TheStatementsProvedTogether.wilson_measure_torus
    YangMills.Construction.TheStatementsProvedTogether.torus_ursell_eq_weighted_curvature
    YangMills.Construction.TheStatementsProvedTogether.bottomChainLaw_eq_wilsonGibbs
theorem slope_eq_mixed_moment :
    YangMills.Construction.SlopeCoefficient.SlopeIsMixedMoment :=
  YangMills.Construction.SlopeCoefficient.slopeIsMixedMoment
theorem flow_reads_mixed_moment :
    YangMills.Construction.TopAux.flowReadsMixedMomentStatement :=
  YangMills.Construction.TopAux.flowReadsMixedMomentStatement_holds
    YangMills.Construction.TheStatementsProvedTogether.slope_eq_mixed_moment
theorem model_seams : YangMills.Construction.ModelSeams.seamsStatement :=
  YangMills.Construction.ModelSeamsProof.seamsStatement_holds
    YangMills.Construction.TheStatementsProvedTogether.weighted_response_chain_isProbabilityMeasure
    YangMills.Construction.TheStatementsProvedTogether.bottomChainLaw_eq_wilsonGibbs
    YangMills.Construction.TheStatementsProvedTogether.minimal_action_unit_coefficient
    YangMills.Construction.TheStatementsProvedTogether.step_parameters_exist
    YangMills.Construction.TheStatementsProvedTogether.slope_eq_mixed_moment
theorem torus_limits_eq_infinite_volume_limits :
    YangMills.Construction.InfiniteLattice.TorusLimitsAreInfiniteVolumeLimits :=
  YangMills.Construction.InfiniteLattice.TorusLimitCharacterization.torusLimitsAreInfiniteVolumeLimits_holds
theorem torusStates_nonempty :
    YangMills.Construction.QuaternionicWilsonModel.TorusLimitSetNonempty.NonemptyStatement :=
  YangMills.Construction.QuaternionicWilsonModel.TorusLimitSetNonempty.nonemptyStatement_holds
    YangMills.Construction.TheStatementsProvedTogether.torus_limit_sets_nonempty
    YangMills.Construction.TheStatementsProvedTogether.torus_limits_eq_infinite_volume_limits
end YangMills.Construction.TheStatementsProvedTogether
