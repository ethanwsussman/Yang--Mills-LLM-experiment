import YangMills.Construction.ComplexAnalysis.DominatedIntegralHolomorphicProof
import YangMills.Construction.PeriodicOperators.NormsOfJetsAndAffineFamiliesOfInvertibleJetsProof
import YangMills.Construction.PeriodicOperators.PeriodicOperatorsOfFiniteRangeAsLocalOperatorFunctionsProof
import YangMills.Construction.TheStatementsProvedTogether.FromJacobiFormulaForTheDeterminantProof
import YangMills.Construction.Towers.BondsOnWhichTheAveragesDependProof
import YangMills.Construction.Towers.ComponentsOfTheJetAlongHolomorphicAmplitudesProof
import YangMills.Construction.Towers.CovariantAveragesAtAPeriodicExtensionDescendProof
import YangMills.Construction.Towers.CovariantDifferenceAtAPeriodicExtensionDescendsProof
import YangMills.Construction.Towers.CovariantDifferenceIsLocalWithACounterpartProof
import YangMills.Construction.Towers.CovariantDifferenceOfAFieldIsLocalWithEntireKernelsProof
import YangMills.Construction.Towers.DifferencesGiveTheTwoOperatorsAtOneOnTheUnitLatticeProof
import YangMills.Construction.Towers.EntireCoordinatesAreClosedProof
import YangMills.Construction.Towers.EntriesOfTheConfigurationOfAFieldProof
import YangMills.Construction.Towers.EntriesOfTheHessianCurvatureKernelProof
import YangMills.Construction.Towers.ExtensionByZeroOfSiteFunctionsDescendsProof
import YangMills.Construction.Towers.FourKernelsOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.HalfPlaquetteTraceKernelOfAFieldIsLocalProof
import YangMills.Construction.Towers.InversesOfJetsWithHolomorphicComponentsProof
import YangMills.Construction.Towers.IterateDifferentialIsLocalWithACounterpartProof
import YangMills.Construction.Towers.KernelOfAMapWithFinitelyManyEvaluationsProof
import YangMills.Construction.Towers.LocalLinearMapsWithAPeriodicCounterpartProof
import YangMills.Construction.Towers.PeriodicExtensionsAndPeriodisationProof
import YangMills.Construction.Towers.SecondOrderKernelAtAPeriodicExtensionDescendsProof
import YangMills.Construction.Towers.SecondOrderTermOfAPeriodicExtensionProof
import YangMills.Construction.Towers.SecondOrderTermsAtAPeriodicExtensionProof
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheScaledPictureAndTheirJetsProof
import YangMills.Construction.Towers.TheTwoOperatorsAsFunctionsOfTheFieldProof
import YangMills.Construction.Towers.TheTwoOperatorsAtOneOnATorusProof
import YangMills.Construction.Towers.ThreeOperatorsOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.TraceNumberOfJetsWithHolomorphicComponentsProof
import YangMills.Construction.Towers.TranslatedConfigurationOfAFieldProof
import YangMills.Construction.Towers.TransportDefectKernelOfAFieldIsLocalProof
import YangMills.Construction.Towers.TransposesOfDifferencesAtScalarFunctionsProof
import YangMills.Construction.Towers.TransposesOfTheDifferencesAtAPointOfTheUnitLatticeProof
import Mathlib
namespace YangMills.Construction.TheStatementsProvedTogether
theorem covariant_difference_local :
    YangMills.Construction.LocalKernels.CovDiffLocality.CovDiffIsLocal :=
  YangMills.Construction.LocalKernels.CovDiffLocality.covDiffIsLocal_holds
    periodicExtension_cells_and_classes bond_or_reverse_positive_exclusive
theorem iterate_derivative_local :
    YangMills.Construction.LocalKernels.IterDerivLocality.IterDerivIsLocal :=
  YangMills.Construction.LocalKernels.IterDerivLocality.iterDerivIsLocal_holds
    average_deriv_local_with_counterpart complexIterate_deriv_chainRule
    full_space_complex_iterate_chain iterated_means_of_periodic_lift
    cellFunction_periodicExtension_properties
theorem local_linear_map_periodize :
    YangMills.Construction.LocalKernels.Periodisation.LocalLinearMapsPeriodize :=
  YangMills.Construction.LocalKernels.Periodisation.PeriodicCounterpart.localLinearMapsPeriodize
    torus_and_space_lattice_properties pauli_matrix_relations
    periodicExtension_cells_and_classes local_kernel_linearMap_matrix
    quotient_map_bonds_properties descending_kernels_closed_add_mul_transpose
theorem periodicExtension_covariantMean_descend :
    YangMills.Construction.LocalKernels.PeriodicLiftDescent.CovariantMeansDescend :=
  YangMills.Construction.LocalKernels.PeriodicLiftDescent.covariantMeansDescend_holds
    local_linear_map_periodize cellFunction_periodicExtension_properties
    iterated_means_of_periodic_lift covariant_difference_local
    smallIterates_mem_complexGaugeGroup adjoint_blockAverage_isLocal_periodic
    contour_log_drift_local average_deriv_local_with_counterpart
    iterate_derivative_local
theorem covariant_difference_periodic_extension_descends :
    YangMills.Construction.LocalKernels.CovDiffAtLift.Claim :=
  YangMills.Construction.LocalKernels.CovDiffAtLift.holds
    local_linear_map_periodize covariant_difference_local
theorem extend_by_zero_descends :
    YangMills.Construction.LocalKernels.ZeroExtensionOfVertexFunctions.Claim := by apply _root_.YangMills.Construction.LocalKernels.VertexZeroExtension.claim_holds <;> assumption
theorem hessian_descends_at_lifts :
    YangMills.Construction.LocalKernels.HessianAtLifts.HessianDescendsAtLifts :=
  YangMills.Construction.LocalKernels.HessianAtLifts.hessianDescendsAtLifts_holds
    periodic_local_bilinear_kernels local_linear_map_periodize
    periodicExtension_cells_and_classes action_hessian_kernel
    plaquette_term_derivatives plaquettes_containing_edge
    torus_and_space_lattice_properties periodic_lift_is_gauge_field
theorem average_support_bonds :
    YangMills.Construction.Tower.SupportOfMeans.SupportOfMeansHolds :=
  YangMills.Construction.Tower.SupportOfMeans.supportOfMeans_holds
    expChart_holomorphic periodicLattice_bond_endpoints_orientation
    doubleBlock_polydiscs block_average_near_identity
    complex_average_depends_on_double_block leftChart_configurations
    double_block_bonds_paths_averages tower_sublattices_symmetries_scalings
    tower_blocks_paths_contours_pivots levelwise_complex_means
theorem quadratic_term_local :
    YangMills.Construction.LocalKernels.QuadraticTermIsLocal :=
  YangMills.Construction.LocalKernels.QuadraticLocality.quadraticTermIsLocal_of
    covariant_average_eq_derivative average_support_bonds tower_blocks_paths_contours_pivots
theorem lift_quadratic_term :
    YangMills.Construction.LocalKernels.QuadraticTermOfLift :=
  YangMills.Construction.LocalKernels.LiftQuadraticTerm.quadraticTermOfLift_holds
    covariant_average_eq_derivative iterated_means_of_periodic_lift
    blockAverages_mem_polydisc tower_iterated_means_polydisc
    finiteEdgeSet_configuration_product quotient_map_bonds_properties
    bond_or_reverse_positive_exclusive matrix2_exp_log_estimates
theorem quadratic_terms_at_periodic_lift :
    YangMills.Construction.LocalKernels.QuadraticTermsFormedAtLift :=
  YangMills.Construction.LocalKernels.QuadraticTermsAtLift.quadraticTermsFormedAtLift_holds
    covariant_average_eq_derivative iterated_means_of_periodic_lift
    average_support_bonds tower_blocks_paths_contours_pivots
theorem quadratic_kernel_periodic_extension_descends :
    YangMills.Construction.LocalKernels.QuadraticKernelAtExtensionDescends :=
  YangMills.Construction.LocalKernels.KernelDescent.quadraticKernelAtExtensionDescends_holds
    periodic_local_bilinear_kernels periodicExtension_cells_and_classes
    iterated_means_of_periodic_lift quadratic_terms_at_periodic_lift
    quadratic_term_local lift_quadratic_term pauli_matrix_relations
    bond_or_reverse_positive_exclusive
theorem periodisation_periodic_extension :
    YangMills.Construction.LocalKernels.Periodisation.PeriodisationHolds :=
  YangMills.Construction.LocalKernels.Periodisation.periodisationHolds_of_parts
    periodicExtension_cells_and_classes descending_kernels_closed_add_mul_transpose
    local_kernel_linearMap_matrix pair_bracket_transpose periodic_local_bilinear_kernels
    covariant_difference_periodic_extension_descends commutator_periodic_lift_descends
    hessian_descends_at_lifts iterated_means_of_periodic_lift
    quadratic_terms_at_periodic_lift periodicExtension_covariantMean_descend
    extend_by_zero_descends quadratic_kernel_periodic_extension_descends
theorem holomorphicJets_closed_add_mul_transpose :
    YangMills.Construction.Tower.FullSpace.JetClosure.JetOpsClosed :=
  YangMills.Construction.Tower.FullSpace.JetClosure.jetOpsClosed_holds
    local_operator_function_jets jetProduct_arguments_and_equal_jets
    holomorphic_power_series_and_limits
theorem scaled_blockAverages_local :
    YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.MeansAreLocal :=
  YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.meansAreLocal_holds
    tower_three_map_kernels covariant_averaging_properties
    tower_blocks_paths_contours_pivots tower_translation_isometry_properties
    infiniteLattice_over_torus holomorphic_power_series_and_limits
theorem jet_components_holomorphic_amplitudes :
    YangMills.Construction.Tower.FullSpace.JetAlongAmplitudes.JetComponentsHolomorphicAlongAmplitudes :=
  YangMills.Construction.Tower.FullSpace.JetAlongAmplitudes.jetComponentsHolomorphicAlongAmplitudes_holds
    tower_indexSets_properties local_operator_function_jets
    local_operator_function_kernels periodic_symbol_calculus
    periodic_operator_strip_symbols holomorphic_iff_differentiable
theorem local_kernel_entire_criterion :
    YangMills.Construction.Tower.FullSpace.EntireLocalCriterion.Criterion :=
  YangMills.Construction.Tower.FullSpace.EntireLocal.entireLocalCriterion_holds
    tower_indexSets_properties periodicOperator_covariant_finiteRange
theorem wilson_action_hessian_parts :
    YangMills.Construction.Tower.CurvatureHessianFacts.Claim :=
  YangMills.Construction.Tower.CurvatureHessianFacts.claim_holds
    quadraticForm_symmetricKernel plaquettes_containing_edge
theorem hessian_curvature_kernel_entries :
    YangMills.Construction.Tower.FullSpace.CurvatureKernelEntries :=
  YangMills.Construction.Tower.FullSpace.CurvatureEntries.curvatureKernelEntries_holds
    wilson_action_hessian_parts quadraticForm_symmetricKernel
theorem gauge_field_of_form_entries :
    YangMills.Construction.Tower.FullSpace.GaugeFieldOfFormEntries := by apply _root_.YangMills.Construction.Tower.FullSpace.gaugeFieldOfFormEntries_holds <;> assumption
theorem entire_dependence_closed :
    YangMills.Construction.Tower.FullSpace.EntireDependenceClosed := by apply _root_.YangMills.Construction.Tower.FullSpace.entireDependence_closed <;> assumption
theorem shifted_field_gauge_comm :
    YangMills.Construction.Tower.FullSpace.ShiftedFieldGauge.ShiftCommutes := by apply _root_.YangMills.Construction.Tower.FullSpace.ShiftedFieldGauge.shiftCommutes_holds <;> assumption
theorem curvatureHessianKernel_isLocal :
    YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.CurvatureKernelIsLocal :=
  YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.curvatureKernelIsLocal_of
    local_kernel_entire_criterion gauge_field_of_form_entries shifted_field_gauge_comm
    hessian_curvature_kernel_entries entire_dependence_closed plaquettes_containing_edge
theorem fullSpace_kernel_finiteSupportMap :
    YangMills.Construction.Tower.FullSpace.FiniteSupportKernel.KernelOfFiniteSupportMap := by apply _root_.YangMills.Construction.Tower.FullSpace.FiniteSupportKernel.kernelOfFiniteSupportMap_holds <;> assumption
theorem holonomy_defect_kernel_local :
    YangMills.Construction.Tower.FullSpace.HolonomyDefectLocality.KernelIsLocal :=
  YangMills.Construction.Tower.FullSpace.HolonomyDefectLocality.kernelIsLocal
    local_kernel_entire_criterion gauge_field_of_form_entries shifted_field_gauge_comm
    fullSpace_kernel_finiteSupportMap entire_dependence_closed
theorem rescaled_differenceKernel_local :
    YangMills.Construction.Tower.FullSpace.RescaledDifferenceLocality.RescaledDifferenceKernelIsLocal :=
  YangMills.Construction.Tower.FullSpace.RescaledDifferenceLocality.rescaledDifferenceKernelIsLocal_of
    local_kernel_entire_criterion gauge_field_of_form_entries shifted_field_gauge_comm
    fullSpace_kernel_finiteSupportMap entire_dependence_closed
theorem halfPlaquette_traceKernel_local :
    YangMills.Construction.Tower.FullSpace.HalfFaceTraceLocality.HalfFaceTraceKernelIsLocal :=
  YangMills.Construction.Tower.FullSpace.HalfFaceTraceLocality.halfFaceTraceKernelIsLocal_holds
    local_kernel_entire_criterion gauge_field_of_form_entries shifted_field_gauge_comm
    fullSpace_kernel_finiteSupportMap entire_dependence_closed
theorem scaledKernels_local :
    YangMills.Construction.Tower.FullSpace.ScaledKernelsLocal.FourKernelsLocal :=
  YangMills.Construction.Tower.FullSpace.ScaledKernelsLocal.fourKernelsLocal_holds
    rescaled_differenceKernel_local holonomy_defect_kernel_local
    halfPlaquette_traceKernel_local curvatureHessianKernel_isLocal
theorem jet_inverse_holomorphic :
    YangMills.Construction.Tower.FullSpace.InvertibleJetInverseHolomorphic :=
  YangMills.Construction.Tower.FullSpace.InverseJetHolomorphy.invertibleJetInverseHolomorphic_holds
    holomorphicJets_closed_add_mul_transpose periodic_operator_jets_constant_part local_operator_function_jets
    periodic_operator_determinants_holomorphic periodic_operator_strip_symbols
theorem finiteRange_periodicOperator_as_localOpFun :
    YangMills.Construction.PeriodicOperators.ConstantOpFun.Claim :=
  YangMills.Construction.PeriodicOperators.ConstantOpFun.claim_holds
    periodicOperator_covariant_finiteRange local_operator_function_parameter_independent
    local_operator_function_jets periodic_operator_strip_symbols
    periodic_symbol_calculus periodic_jet_calculus
theorem wilson_action_hessian_decomposition :
    YangMills.Construction.Tower.WilsonHessian.DecompositionHolds :=
  YangMills.Construction.Tower.WilsonHessianProof.decomposition_holds
    plaquette_term_derivatives action_hessian_kernel plaquettes_containing_edge
    wilson_action_hessian_parts matrix2_exp_log_estimates
theorem full_space_three_operators_local :
    YangMills.Construction.Tower.FullSpace.ThreeLocalOperators.LocalEntireOperators :=
  YangMills.Construction.Tower.FullSpace.ThreeLocalOperators.localEntireOperators
    scaledKernels_local wilson_action_hessian_decomposition local_operator_function_jets
    finiteRange_periodicOperator_as_localOpFun free_operators_periodic
    periodicOperator_covariant_finiteRange tower_indexSets_properties
theorem dominated_integral_holomorphic_deriv :
    YangMills.Construction.ComplexAnalysis.DominatedIntegralHolomorphicAndDeriv := by apply _root_.YangMills.Construction.ComplexAnalysis.dominatedIntegralHolomorphicAndDeriv <;> assumption
theorem box_integral_holomorphic_in_parameter :
    YangMills.Construction.ComplexAnalysis.BoxIntegralHolomorphicInParameter :=
  YangMills.Construction.ComplexAnalysis.ParameterBox.boxIntegralHolomorphicInParameter_of_dominated
    dominated_integral_holomorphic_deriv
theorem jet_trace_holomorphic :
    YangMills.Construction.Tower.FullSpace.JetTraceHolomorphy.Claim :=
  YangMills.Construction.Tower.FullSpace.JetTraceHolomorphy.claim_holds
    box_integral_holomorphic_in_parameter norm_periodicHom
theorem scaled_operatorFunctions_properties :
    YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions.ScaledOperatorFunctionsClaim :=
  YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions.claim_of_parts
    scaledKernels_local full_space_three_operators_local scaled_blockAverages_local
    jet_components_holomorphic_amplitudes holomorphicJets_closed_add_mul_transpose
    jet_inverse_holomorphic jet_trace_holomorphic
    tower_indexSets_properties matrix2_exp_log_estimates
theorem jet_norms_and_affine_invertible_jets :
    YangMills.Construction.PeriodicOperators.JetNormsAffine.Claim :=
  YangMills.Construction.PeriodicOperators.JetNormsAffine.claim_holds
    periodic_jet_calculus local_operator_function_jets
    jetProduct_arguments_and_equal_jets periodic_quadruple_algebra
    quotient_matrix_norms_traces
theorem massiveJets_properties :
    YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.MassJetsClaim :=
  YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.massJetsClaim_holds
    free_operator_strip_constants_admissible plane_wave_calculus
    scaled_operatorFunctions_properties local_operator_function_jets periodic_jet_calculus
    periodic_quadruple_algebra jetProduct_arguments_and_equal_jets jet_norms_and_affine_invertible_jets
    periodic_quotient_transpose_norm_bound norm_periodicHom
theorem covariant_difference_kernel_local_entire :
    YangMills.Construction.Tower.CovDiffKernelLocalEntire :=
  YangMills.Construction.Tower.CovDiffKernelProof.covDiffKernelLocalEntire_holds
theorem field_kernel_real_of_real_field :
    YangMills.Construction.Tower.RealFieldKernels.Statement :=
  YangMills.Construction.Tower.RealFieldKernels.holds hessian_symm_det_pos
theorem two_operator_kernels_product :
    YangMills.Construction.Tower.TwoOperatorKernelProducts.Statement :=
  YangMills.Construction.Tower.TwoOperatorKernelProducts.statement_of_transposes
    covariant_difference_transpose
theorem field_hessian_local_entire_kernel :
    YangMills.Construction.Tower.FieldHessian.Claim :=
  YangMills.Construction.Tower.FieldHessian.claim_holds
    action_hessian_kernel action_deriv_finite_plaquette_set plaquettes_bonds_finite
    left_chart_isometry_preserves_pairing_hessian tower_translation_isometry_properties
    matrix2_exp_log_estimates complex_matrix_two_norm_exp_log
theorem two_operators_as_field_functions :
    YangMills.Construction.Tower.TwoOperatorsAsFieldFunctions :=
  YangMills.Construction.Tower.FieldFunctionsProof.twoOperatorsAsFieldFunctions
    two_operator_kernels_product covariant_difference_kernel_local_entire
    field_hessian_local_entire_kernel field_kernel_real_of_real_field local_operator_function_jets
    covariant_difference_transpose tower_indexSets_properties
    holomorphic_power_series_and_limits matrix2_exp_log_estimates
    complex_matrix_two_norm_exp_log
theorem torus_twoOperators_at_identity :
    YangMills.Construction.Tower.TwoOperatorsAtIdentityTorusClaim :=
  YangMills.Construction.Tower.IdentityOperatorsTorus.twoOperatorsAtIdentityTorusClaim_holds
    hessian_symm_det_pos covariant_difference_transpose action_hessian_kernel
    plaquette_term_derivatives plaquette_sum_pairings
theorem unit_lattice_coboundaries_at_one :
    YangMills.Construction.Tower.CoboundariesAtIdentity :=
  YangMills.Construction.Tower.IdentityOperators.coboundariesAtIdentity_holds
    left_chart_properties plaquette_term_derivatives action_hessian_kernel
    covariant_difference_transpose row_finite_kernel_products pauli_matrix_relations
theorem scalar_difference_adjoint :
    YangMills.Construction.Tower.ScalarDifferenceAdjoints := by apply _root_.YangMills.Construction.Tower.DifferenceAdjoints.scalarDifferenceAdjoints_holds <;> assumption
theorem latticeDifference_adjoint_formulas :
    YangMills.Construction.Tower.UnitLatticeAdjoints.AdjointFormulas :=
  YangMills.Construction.Tower.UnitLatticeAdjoints.adjointFormulas_holds
    scalar_difference_adjoint covariant_difference_transpose
end YangMills.Construction.TheStatementsProvedTogether
