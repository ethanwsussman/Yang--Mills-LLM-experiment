import YangMills.Construction.Averaging.MeanOfTheConstantFamilyProof
import YangMills.Construction.Lattice.AveragingMapOnSmallSetsAndMeasurabilityProof
import YangMills.Construction.Lattice.DoubleBlockStraightPathCorridorAndPivotBondProof
import YangMills.Construction.Lattice.FirstDerivativeOfTheAverageLogarithmProof
import YangMills.Construction.Lattice.FirstDerivativeOfTheContourVariablesProof
import YangMills.Construction.Lattice.GaugeCovarianceOfTheIteratesOfTheSchemesProof
import YangMills.Construction.Lattice.GaugeCovarianceOfTheOneStepObjectsProof
import YangMills.Construction.Lattice.HolonomyCommutingEqualStepsProof
import YangMills.Construction.Lattice.IteratesOfTheTwoSchemesProof
import YangMills.Construction.Lattice.LevelBondOrientationDichotomyProof
import YangMills.Construction.Lattice.MeanLinearAverageIsTheAbsorbedAverageProof
import YangMills.Construction.Lattice.OneStepCovarianceAndDomainsProof
import YangMills.Construction.Lattice.OneStepObjectsNearSmallPlaquettesProof
import YangMills.Construction.Lattice.PolydiscOfTheOneStepObjectsExistsProof
import YangMills.Construction.Lattice.PositiveOneOfABondAndItsReverseProof
import YangMills.Construction.Lattice.PropertiesOfTheTwoSchemesProof
import YangMills.Construction.Lattice.SchemeAverageDependsOnTheDoubleBlockAloneProof
import YangMills.Construction.Lattice.SchemeIterateReadsTheBareDoubleBlockProof
import YangMills.Construction.Lattice.SecondOrderBoundOfTheAverageLogarithmProof
import YangMills.Construction.Lattice.SpreadOfAContourFamilyProof
import YangMills.Construction.Lattice.ThreeAveragingCaseSetsAreBorelProof
import YangMills.Construction.Lattice.ToolboxMeanLinearAverageIsTheAbsorbedAverageProof
import YangMills.Construction.Lattice.TwoSidedCovarianceOfTheTwoSchemesProof
import YangMills.Construction.Lattice.ValuesOfTheTwoSchemesProof
import YangMills.Construction.Matrices.ConjugationDeterminantProof
import YangMills.Construction.Matrices.ElementaryMatrixBoundsProof
import YangMills.Construction.Matrices.ExpLogSeriesConvergenceProof
import YangMills.Construction.Matrices.ExponentialChartsOfPowersOfGProof
import YangMills.Construction.Matrices.OperatorNormAbsoluteSeriesProof
import YangMills.Construction.TheStatementsProvedTogether.FromPowerSeriesAndLimitsOfHolomorphicMapsProof
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChartProof
import YangMills.Construction.Towers.RealAnalyticMapsOfConfigurationsAreDifferentiableProof
import YangMills.Construction.Towers.ReverseOfAStraightPathAtTheSideInfinityProof
import YangMills.Construction.Towers.TrivialConfigurationAtAStepProof
import YangMills.Construction.Towers.ValuesOfTheAveragesNearTheTrivialConfigurationProof
import Mathlib
namespace YangMills.Construction.TheStatementsProvedTogether
theorem averaging_domains_open_holomorphic :
    YangMills.Construction.PeriodicLattice.AveragingDomainsOpenAndHolomorphic :=
  YangMills.Construction.PeriodicLattice.AveragingDomains.openAndHolomorphic torus_block_paths
    complex_log_mean_small_families holomorphic_at_unimodular_arguments matrix2_exp_log_estimates
theorem scheme_finest_base_sites :
    YangMills.Construction.PeriodicLattice.SchemeFinestBaseSites := by apply _root_.YangMills.Construction.PeriodicLattice.schemeFinestBaseSites_holds <;> assumption
theorem matrix2_norm_exp_log_conj :
    YangMills.Construction.Matrices.ComplexMatrix2.NormExpLogConjugation := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.normExpLogConjugation_holds <;> assumption
theorem cornered_scheme_gauge_law_and_conj :
    YangMills.Construction.PeriodicLattice.CorneredSchemeGaugeLawAndConjugation :=
  YangMills.Construction.PeriodicLattice.corneredSchemeGaugeLawAndConjugation
    matrix2_norm_exp_log_conj torus_block_paths
theorem periodicLattice_schemes_gaugeCovariant :
    YangMills.Construction.PeriodicLattice.GaugeCovarianceStatement :=
  YangMills.Construction.PeriodicLattice.schemesGaugeCovariant_of_statements
    matrix2_norm_exp_log_conj cornered_scheme_gauge_law_and_conj complex_log_mean_small_families
    torus_block_paths
theorem one_step_average_depends_on_double_block :
    YangMills.Construction.PeriodicLattice.OneStepAverageIsLocal :=
  YangMills.Construction.PeriodicLattice.oneStepAverageIsLocal_holds torus_block_paths
theorem iterated_block_average_gauge_covariant :
    YangMills.Construction.PeriodicLattice.IteratedAverageGaugeCovariance :=
  YangMills.Construction.PeriodicLattice.iteratedAverage_gaugeCovariant
    periodicLattice_schemes_gaugeCovariant one_step_average_depends_on_double_block
theorem iterated_block_average_locality :
    YangMills.Construction.PeriodicLattice.IteratedAverageLocality :=
  YangMills.Construction.PeriodicLattice.iteratedAverageLocality_of_coordinates
    torus_lattice_coordinate_description one_step_average_depends_on_double_block
theorem iterated_average_gauge_local :
    YangMills.Construction.PeriodicLattice.IteratedAverageGaugeLocality :=
  YangMills.Construction.PeriodicLattice.iteratedAverageGaugeLocality_proof
    scheme_finest_base_sites torus_lattice_coordinate_description
    iterated_block_average_gauge_covariant iterated_block_average_locality
theorem averaging_schemes_gauge_covariant :
    YangMills.Construction.PeriodicLattice.SchemesGaugeCovariant :=
  YangMills.Construction.PeriodicLattice.schemesGaugeCovariant_twoSided
    periodicLattice_schemes_gaugeCovariant matrix2_norm_exp_log_conj cornered_scheme_gauge_law_and_conj
    torus_block_paths
theorem scheme_values_mem_gaugeGroup :
    YangMills.Construction.PeriodicLattice.SchemeValuesInGaugeGroup :=
  YangMills.Construction.PeriodicLattice.SchemeValuesInGaugeGroup.holds torus_block_paths
    complex_log_mean_small_families matrix2_exp_log_estimates unitary_two_log_spec
theorem torus_averaging_scheme_props :
    YangMills.Construction.PeriodicLattice.AveragingSchemeProperties :=
  YangMills.Construction.PeriodicLattice.averagingSchemeProperties_holds torus_block_paths
    meanScheme_average_eq_complex_blockAverage averaging_domains_open_holomorphic
    scheme_values_mem_gaugeGroup centred_scheme_small_curvature averaging_schemes_gauge_covariant
    iterated_average_gauge_local
theorem block_average_near_trivial_field :
    YangMills.Construction.Tower.SmoothingNearTrivialField :=
  YangMills.Construction.Tower.SmoothingNearTrivialProof.smoothingNearTrivialField
    torus_averaging_scheme_props unitary_log_conj_properties
    torus_and_space_lattice_properties finiteEdgeSet_configuration_product
theorem blockAverage_caseSets_measurable :
    YangMills.Construction.PeriodicLattice.CaseSetsMeasurableStatement :=
  YangMills.Construction.PeriodicLattice.CaseSetsMeasurable.caseSetsMeasurable_of_everySmallRadiusSuffices
    averaging_smallRadius_suffices
theorem block_average_continuousOn_case_sets :
    YangMills.Construction.PeriodicLattice.BlockAverageContinuousOnEachCaseSet :=
  YangMills.Construction.PeriodicLattice.BlockAverageContinuity.blockAverageContinuousOnEachCaseSet_holds
    averaging_smallRadius_suffices unitary_two_log_spec
theorem bond_orientation_reverse :
    YangMills.Construction.PeriodicLattice.PositiveOrientationOfBondAndOpposite :=
  YangMills.Construction.PeriodicLattice.positiveOrientationOfBondAndOpposite_holds
    periodicLattice_bond_endpoints_orientation double_block_bonds_paths_averages
theorem measurable_block_average :
    YangMills.Construction.PeriodicLattice.BlockAverageIsBorelMap :=
  YangMills.Construction.PeriodicLattice.BlockAverageBorel.blockAverage_isBorelMap
    blockAverage_caseSets_measurable block_average_continuousOn_case_sets unitary_two_log_spec
    matrix2_exp_log_estimates bond_orientation_reverse double_block_bonds_paths_averages
theorem block_average_analyticOn_small_fields :
    YangMills.Construction.Averaging.BlockAverageRealAnalyticOnSmallFields :=
  YangMills.Construction.Averaging.SmallFieldAnalyticity.blockAverageRealAnalyticOnSmallFields_holds
    averaging_smallRadius_suffices double_block_contours holomorphic_power_series_and_limits
    entrywise_holomorphic_restriction matrix2_exp_log_estimates
theorem block_average_small_set_measurable :
    YangMills.Construction.PeriodicLattice.BlockAverageSmallSetAndMeasurable :=
  YangMills.Construction.PeriodicLattice.blockAverageSmallSetAndMeasurable_holds
    averaging_smallRadius_suffices block_average_analyticOn_small_fields blockAverage_caseSets_measurable
    block_average_continuousOn_case_sets measurable_block_average
theorem holonomy_gauge_covariant :
    YangMills.Construction.PeriodicLattice.GaugeCovarianceOfHolonomy := by apply _root_.YangMills.Construction.PeriodicLattice.gaugeCovarianceOfHolonomy_holds <;> assumption
theorem matrix2_mean_covariance :
    YangMills.Construction.Matrices.ComplexMatrix2.LogMeanCovariance :=
  YangMills.Construction.Matrices.ComplexMatrix2.logMeanCovariance_holds complexMatrixTwo_opNorm_conj
theorem blockAverage_local_and_gauge_covariant :
    YangMills.Construction.PeriodicLattice.BlockAverageLocalityAndCovariance :=
  YangMills.Construction.PeriodicLattice.blockAverageLocalityAndCovariance_holds
    torus_block_partition_properties torus_block_paths holonomy_gauge_covariant
    matrix2_mean_covariance complexMatrixTwo_opNorm_conj unitary_log_conj_properties
    matrix2_exp_log_estimates complex_log_mean_small_families
theorem specialUnitary_two_angle_bounds :
    YangMills.Construction.Matrices.ComplexMatrix2.SpecialUnitaryAngleBounds :=
  YangMills.Construction.Matrices.ComplexMatrix2.RotationAngle.specialUnitaryAngleBounds_holds
    unitary_log_conj_properties complexMatrixTwo_opNorm_conj matrix2_exp_log_estimates
theorem path_rearrangement_le :
    YangMills.Construction.PeriodicLattice.PathRearrangementBound :=
  YangMills.Construction.PeriodicLattice.PathRearrangementProof.pathRearrangementBound_holds
    specialUnitary_two_angle_bounds
theorem holonomy_commute_equal_steps :
    YangMills.Construction.PeriodicLattice.HolonomyCommutesWithEqualSteps :=
  YangMills.Construction.PeriodicLattice.EqualStepFlows.holonomyCommutesWithEqualSteps
    path_rearrangement_le
theorem contour_family_spread_bound :
    YangMills.Construction.PeriodicLattice.ContourFamilySpread :=
  YangMills.Construction.PeriodicLattice.ContourSpread.contourFamilySpread_holds
    torus_block_partition_properties complexMatrixTwo_opNorm_conj path_rearrangement_le
    specialUnitary_two_angle_bounds
theorem radii_lt_explicit_bound :
    YangMills.Construction.Averaging.ExplicitRadii.Holds :=
  YangMills.Construction.Averaging.ExplicitRadiiProof.holds complex_log_mean_small_families
    averaging_smallRadius_suffices contour_family_spread_bound double_block_contours
    torus_block_paths holonomy_commute_equal_steps block_average_analyticOn_small_fields
theorem smoothing_analytic_covariant_on_sides :
    YangMills.Construction.Tower.SmoothingAnalyticCovariantOnSides :=
  YangMills.Construction.Tower.smoothingAnalyticCovariantOnSides_holds
    holomorphic_at_unimodular_arguments torus_and_space_lattice_properties
    block_average_near_trivial_field radii_lt_explicit_bound
    block_average_small_set_measurable blockAverage_local_and_gauge_covariant
theorem mean_identity_family_eq_one :
    YangMills.Construction.Averaging.IdentityFamilyMeanIsOne :=
  YangMills.Construction.Averaging.identityFamilyMeanIsOne_of_expLogEstimates matrix2_exp_log_estimates
theorem trivialField_isConfiguration :
    YangMills.Construction.Tower.TrivialFieldAtStep :=
  YangMills.Construction.Tower.TrivialFieldProof.trivialFieldAtStep_holds mean_identity_family_eq_one
theorem matrix_two_conj_det :
    YangMills.Construction.Matrices.ComplexMatrix2.ConjugationDeterminant := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.conjugationDeterminant_holds <;> assumption
theorem pauli_matrix_relations :
    YangMills.Construction.OneLoop.PauliMatrixRelations :=
  YangMills.Construction.OneLoop.pauliMatrixRelations_of_conjugationDeterminant
    matrix_two_conj_det
theorem exp_charts_of_powers :
    YangMills.Construction.Matrices.PowerExpCharts.ExpChartsStatement :=
  YangMills.Construction.Matrices.PowerExpCharts.expChartsStatement_holds exp_log_numeric_bounds
    unitary_log_conj_properties matrix2_exp_log_estimates holomorphic_power_series_and_limits
    pauli_matrix_relations expChart_holomorphic
theorem analyticOn_configurations_differentiable :
    YangMills.Construction.Tower.AnalyticMapDifferentiableStatement :=
  YangMills.Construction.Tower.AnalyticMapDifferentiable.statement_of_charts exp_charts_of_powers
    finiteEdgeSet_configuration_product
theorem leftChart_configurations :
    YangMills.Construction.Tower.LeftChartFields.Claim :=
  YangMills.Construction.Tower.LeftChartFields.claim_holds unitary_log_conj_properties
    matrix2_exp_log_estimates exp_charts_of_powers holomorphic_power_series_and_limits
    torus_and_space_lattice_properties
theorem axial_path_reverse :
    YangMills.Construction.PeriodicLattice.AxialPathReversal := by apply _root_.YangMills.Construction.PeriodicLattice.axialPathReversal_holds <;> assumption
theorem axisPath_reverse :
    YangMills.Construction.Tower.FullSpace.AxisPathReversal.statement := by apply _root_.YangMills.Construction.Tower.FullSpace.AxisPathReversal.holds <;> assumption
theorem axis_path_reverse :
    YangMills.Construction.Tower.AxisPathReversal.MainStatement :=
  YangMills.Construction.Tower.AxisPathReversal.mainStatement_holds tower_block_structure
    axial_path_reverse axisPath_reverse
theorem centred_linear_average_eq_absorbed_average :
    YangMills.Construction.PeriodicLattice.CentredLinearAverageEqScaled :=
  YangMills.Construction.PeriodicLattice.centredLinearAverageEqScaled_holds torus_block_paths
theorem centred_scheme_linear_average_eq :
    YangMills.Construction.PeriodicLattice.CentredSchemeLinearAverageEq :=
  YangMills.Construction.PeriodicLattice.centredSchemeLinearAverageEq_of_scaled
    centred_linear_average_eq_absorbed_average
theorem contour_holonomy_first_deriv :
    YangMills.Construction.PeriodicLattice.ContourHolonomyDerivative.Statement :=
  YangMills.Construction.PeriodicLattice.ContourHolonomyDerivative.statement_holds
    complex_log_mean_small_families matrix2_exp_log_estimates
theorem hasDerivAt_block_average_log_zero :
    YangMills.Construction.PeriodicLattice.HasDerivBlockAverageLogAtZero :=
  YangMills.Construction.PeriodicLattice.BlockAverageLogDeriv.hasDerivBlockAverageLogAtZero
    contour_holonomy_first_deriv mean_identity_family_eq_one torus_block_partition_properties
    matrix2_exp_log_estimates
theorem trivialGaugeField_blockAverages :
    YangMills.Construction.PeriodicLattice.TrivialFieldAverages.Statement :=
  YangMills.Construction.PeriodicLattice.TrivialFieldAverages.trivialGaugeField_averages
    mean_identity_family_eq_one
theorem complex_matrix_two_elementary_inequalities :
    YangMills.Construction.Matrices.ComplexMatrix2.ElementaryInequalitiesStatement :=
  YangMills.Construction.Matrices.ComplexMatrix2.ElementaryBounds.elementaryInequalities
    matrix2_norm_exp_log_conj matrix2_exp_log_estimates holomorphic_power_series_and_limits
    specialUnitary_two_angle_bounds
theorem matrix2_elementary_inequalities :
    YangMills.Construction.Matrices.ComplexMatrix2.RestatedElementaryInequalitiesStatement := by apply _root_.YangMills.Construction.TheStatementsProvedTogether.complex_matrix_two_elementary_inequalities <;> assumption
theorem complex_average_depends_on_double_block :
    YangMills.Construction.PeriodicLattice.ComplexAverageIsLocal :=
  YangMills.Construction.PeriodicLattice.complexAverageIsLocal_of_blockPaths torus_block_paths
theorem centred_average_eq_on_small_fields :
    YangMills.Construction.PeriodicLattice.CentredAverageAgreesOnSmallFields :=
  YangMills.Construction.PeriodicLattice.centredAverageAgreesOnSmallFields radii_lt_explicit_bound
    complex_average_depends_on_double_block meanScheme_average_eq_complex_blockAverage torus_block_paths
theorem double_block_from_lowest_corner :
    YangMills.Construction.PeriodicLattice.DoubleBlockFromLowestCorner :=
  YangMills.Construction.PeriodicLattice.doubleBlockFromLowestCorner_holds
    torus_lattice_coordinate_description corner_box_of_sites_properties
theorem comb_gauge_on_box :
    YangMills.Construction.PeriodicLattice.CombTransportOnBox.Statement :=
  YangMills.Construction.PeriodicLattice.CombGaugeOnBox.holds path_rearrangement_le
    specialUnitary_two_angle_bounds complexMatrixTwo_opNorm_conj holonomy_gauge_covariant
    unitary_two_log_spec
theorem norm_exp_gauge_transport :
    YangMills.Construction.PeriodicLattice.NormExpAndGaugeTransport :=
  YangMills.Construction.PeriodicLattice.normExpAndGaugeTransport_holds matrix2_exp_log_estimates
theorem singleScale_gaugeCovariance :
    YangMills.Construction.PeriodicLattice.StepObjectsGaugeCovariance :=
  YangMills.Construction.PeriodicLattice.StepObjectsCovarianceProof.stepObjectsGaugeCovariance_holds
    periodicLattice_schemes_gaugeCovariant norm_exp_gauge_transport torus_block_paths
theorem one_step_near_small_plaquette_curvature :
    YangMills.Construction.PeriodicLattice.StepObjectsNearSmallCurvature :=
  YangMills.Construction.PeriodicLattice.stepObjectsNearSmallCurvature_holds
    singleScale_gaugeCovariance comb_gauge_on_box torus_block_paths
    double_block_from_lowest_corner complexMatrixTwo_opNorm_conj
    holomorphic_power_series_and_limits expChart_holomorphic
theorem real_bond_field_step :
    YangMills.Construction.PeriodicLattice.RealBondFieldStepStatement :=
  YangMills.Construction.PeriodicLattice.realBondFieldStep_holds one_step_near_small_plaquette_curvature
    scheme_values_mem_gaugeGroup centred_average_eq_on_small_fields matrix2_exp_log_estimates
    unitary_two_log_spec
theorem blockSpin_firstOrder_quantities :
    YangMills.Construction.PeriodicLattice.StepQuantitiesFirstOrder :=
  YangMills.Construction.PeriodicLattice.stepQuantitiesFirstOrder_proof
    one_step_near_small_plaquette_curvature torus_block_paths one_step_average_depends_on_double_block
    holomorphic_power_series_and_limits matrix2_elementary_inequalities
theorem double_block_corridor_pivot_bond :
    YangMills.Construction.PeriodicLattice.DoubleBlockGeometryClaim :=
  YangMills.Construction.PeriodicLattice.doubleBlockGeometryClaim_holds
    torus_lattice_coordinate_description refinedLattice_blockCoordinates
theorem matrix_two_opNorm_summable_series :
    YangMills.Construction.Matrices.ComplexMatrix2.OperatorNormSeriesProperties := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.operatorNormSeriesProperties_holds <;> assumption
theorem matrix_exp_log_series_summable :
    YangMills.Construction.Matrices.ComplexMatrix2.ExpLogSeriesConvergence :=
  YangMills.Construction.Matrices.ComplexMatrix2.expLogSeriesConvergence_holds
    matrix_two_opNorm_summable_series
theorem bond_or_reverse_positive_exclusive :
    YangMills.Construction.PeriodicLattice.LevelBondOrientationDichotomy := by apply _root_.YangMills.Construction.PeriodicLattice.levelBondOrientationDichotomy_holds <;> assumption
theorem card_sites_plaquettes :
    YangMills.Construction.PeriodicLattice.SiteAndPlaquetteCounts := by apply _root_.YangMills.Construction.PeriodicLattice.Counting.siteAndPlaquetteCounts_holds <;> assumption
theorem elementary_block_gauge_facts :
    YangMills.Construction.PeriodicLattice.ElementaryStepFacts :=
  YangMills.Construction.PeriodicLattice.elementaryStepFacts_holds unitary_two_log_spec
    matrix2_exp_log_estimates matrix_exp_log_series_summable complexMatrixTwo_opNorm_conj
    torus_block_partition_properties double_block_corridor_pivot_bond bond_or_reverse_positive_exclusive
    card_sites_plaquettes
theorem latticeObjects_near_one_uniform :
    YangMills.Construction.PeriodicLattice.SchemeObjectsNearOneUniformly :=
  YangMills.Construction.PeriodicLattice.schemeObjectsNearOneUniformly_holds torus_block_paths
    complex_log_mean_small_families matrix2_exp_log_estimates
theorem exists_polydisc_radius_blocking :
    YangMills.Construction.PeriodicLattice.OneStepPolydiscRadiusExists :=
  YangMills.Construction.PeriodicLattice.oneStepPolydiscRadiusExists_holds
    latticeObjects_near_one_uniform matrix2_exp_log_estimates bond_or_reverse_positive_exclusive
    elementary_block_gauge_facts
theorem holomorphic_bounded_step_quantities :
    YangMills.Construction.PeriodicLattice.HolomorphyOfBoundedStepQuantities :=
  YangMills.Construction.PeriodicLattice.HolomorphyOfBoundedStepQuantities.holds
    holomorphic_power_series_and_limits averaging_domains_open_holomorphic
theorem exists_polydisc_radius_one_step :
    YangMills.Construction.PeriodicLattice.ExistsOneStepPolydiscRadius :=
  YangMills.Construction.PeriodicLattice.existsOneStepPolydiscRadius_holds
    exists_polydisc_radius_blocking holomorphic_bounded_step_quantities
theorem step_objects_chart_invariant :
    YangMills.Construction.PeriodicLattice.StepObjectsChartInvariant :=
  YangMills.Construction.PeriodicLattice.ChartInvariance.stepObjectsChartInvariant_of
    torus_standardPartition_cube_geometry double_block_contours
theorem one_scale_covariance_domains :
    YangMills.Construction.PeriodicLattice.stepCovarianceDomainsStatement :=
  YangMills.Construction.PeriodicLattice.stepCovarianceDomainsStatement_proof
    singleScale_gaugeCovariance exists_polydisc_radius_one_step
    step_objects_chart_invariant one_step_near_small_plaquette_curvature
    blockSpin_firstOrder_quantities real_bond_field_step
theorem block_average_log_second_order_bound :
    YangMills.Construction.PeriodicLattice.BlockAverageLogSecondOrderBound :=
  YangMills.Construction.PeriodicLattice.blockAverageLog_secondOrderBound
    one_scale_covariance_domains hasDerivAt_block_average_log_zero trivialGaugeField_blockAverages
    holomorphic_power_series_and_limits matrix2_elementary_inequalities matrix2_exp_log_estimates
theorem single_lattice_step_bounds :
    YangMills.Construction.PeriodicLattice.SingleStepBounds :=
  YangMills.Construction.PeriodicLattice.SingleStepEstimate.singleStepBounds
    specialUnitary_two_angle_bounds complexMatrixTwo_opNorm_conj torus_block_paths
    path_rearrangement_le scheme_values_mem_gaugeGroup centred_scheme_small_curvature
    contour_family_spread_bound
theorem coarse_plaquette_comb_gauge :
    YangMills.Construction.PeriodicLattice.CoarsePlaquetteCombGauge :=
  YangMills.Construction.PeriodicLattice.coarsePlaquetteCombGauge_holds comb_gauge_on_box
    single_lattice_step_bounds periodicLattice_schemes_gaugeCovariant corner_box_of_sites_properties
    one_step_average_depends_on_double_block one_scale_covariance_domains
end YangMills.Construction.TheStatementsProvedTogether
