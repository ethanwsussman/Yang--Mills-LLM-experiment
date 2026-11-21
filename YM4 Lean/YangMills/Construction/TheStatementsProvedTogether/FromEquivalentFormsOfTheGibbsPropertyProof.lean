import YangMills.Construction.Analysis.CyclicTraceProductBoundsOfHolder
import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGridsProof
import YangMills.Construction.ChessboardTori.AssertionsOfTheTransferPictureProof
import YangMills.Construction.ChessboardTori.CellFunctionsReadOnASlabProof
import YangMills.Construction.ChessboardTori.ChessboardBoundOfAFamilyProof
import YangMills.Construction.ChessboardTori.ChessboardEstimateProof
import YangMills.Construction.ChessboardTori.DistanceToFacePlanesAndOpenCellsProof
import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGridProof
import YangMills.Construction.ChessboardTori.ExpansionOfTheCrossingKernelProof
import YangMills.Construction.ChessboardTori.ExpectationOnTheSideGroupProof
import YangMills.Construction.ChessboardTori.GroupCoordinateByCoordinateProof
import YangMills.Construction.ChessboardTori.GroupOnTheTorusAsAQuotientProof
import YangMills.Construction.ChessboardTori.InducedIsometriesOfTheTorusProof
import YangMills.Construction.ChessboardTori.LinksAndPlaquettesUnderLatticeIsometriesProof
import YangMills.Construction.ChessboardTori.NumberOfThePeriodisedSourceProof
import YangMills.Construction.ChessboardTori.QuotientMapOnLinksAndPlaquettesProof
import YangMills.Construction.ChessboardTori.QuotientsOfTheLatticeProof
import YangMills.Construction.ChessboardTori.ReflectionBoundInOneDirectionProof
import YangMills.Construction.ChessboardTori.ReflectionsAndTranslationsOfSlabsProof
import YangMills.Construction.ChessboardTori.RulesOfTheChessboardNumberProof
import YangMills.Construction.ChessboardTori.SitesOffTheFacePlanesProof
import YangMills.Construction.ChessboardTori.TermsOfThePeriodisedSourceProof
import YangMills.Construction.ChessboardTori.ThreeEvaluationRulesProof
import YangMills.Construction.ChessboardTori.TraceFormulaProof
import YangMills.Construction.ChessboardTori.WilsonWeightAsASlabIntegralProof
import YangMills.Construction.Cumulants.GeneratingFunctionOfATupleAndItsLogarithmProof
import YangMills.Construction.InfiniteLattice.AllMirrorsOfPeriodicGibbsStatesProof
import YangMills.Construction.InfiniteLattice.EquivalentFormsOfTheGibbsPropertyProof
import YangMills.Construction.InfiniteLattice.MetricForTheWeakTopologyOfRealTestsProof
import YangMills.Construction.InfiniteLattice.MovesOfBondsSupportsAndPlaquettesProof
import YangMills.Construction.InfiniteLattice.PeriodisationAndThreeIdentitiesOfTheCoveringProof
import YangMills.Construction.InfiniteLattice.StatesAtFixedSpacingProof
import YangMills.Construction.InfiniteLattice.TorusLimitsArePeriodicGibbsStatesProof
import YangMills.Construction.InfiniteLattice.TransportOfLipschitzFunctionsAtAPositiveMarginProofForm
import YangMills.Construction.InfiniteLattice.WeakLimitPointsOfTheFamilyAreLimitsAlongSequencesProof
import YangMills.Construction.InfiniteLattice.WeaklyConvergentSubsequencesOfStatesProof
import YangMills.Construction.Lattice.CellGridPropertiesProofs
import YangMills.Construction.Lattice.ConnectedFunctionsAreAFiniteSumOverPlaquettesProof
import YangMills.Construction.Lattice.CubesBlocksDistancesAndTracesProof
import YangMills.Construction.Lattice.GridDataOfEqualSidesProof
import YangMills.Construction.Lattice.LatticeIntegralIsEntireAndPositiveProof
import YangMills.Construction.Lattice.StandardPartitionsAndLevelUnitsProof
import YangMills.Construction.Lattice.WilsonMeasureIsometriesAndCumulantsAreFormedProof
import YangMills.Construction.MirrorGridsOfEverySide.ActionOnTheCellAlgebrasAtEveryMirrorGridProof
import YangMills.Construction.MirrorGridsOfEverySide.ActionOnTheCellAlgebrasOfTheTorusAtEveryMirrorGridProof
import YangMills.Construction.MirrorGridsOfEverySide.CellsOnTheTorusAtEveryMirrorGridProof
import YangMills.Construction.MirrorGridsOfEverySide.CentresAreSitesAtEveryMirrorGridProof
import YangMills.Construction.MirrorGridsOfEverySide.CoarserGridOnSpaceAtEveryMirrorGridProof
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsAtEveryMirrorGridProof
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsOfTheTorusAtEveryMirrorGridProof
import YangMills.Construction.MirrorGridsOfEverySide.SideIsAnOddMultipleOfTheSpacingAtEveryMirrorGridProof
import YangMills.Construction.ReflectionPositivity.BondsAndPlaquettesAreNotDegenerateProof
import YangMills.Construction.ReflectionPositivity.CovarianceOfTheCurvatureDensityProof
import YangMills.Construction.ReflectionPositivity.FactsOfTheCoveringMapProof
import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsInTheCoarseCaseProof
import YangMills.Construction.SystemOfAdmissibleConstants.SizeOfAnObservableOnABallProof
import YangMills.Construction.TheStatementsProvedTogether.FromComponentFunctionsOfTheProjectionsProof
import Mathlib
namespace YangMills.Construction.TheStatementsProvedTogether
theorem gibbs_tfae :
    YangMills.Construction.InfiniteLattice.GibbsEquivalences.GibbsEquivalenceStatement :=
  YangMills.Construction.InfiniteLattice.GibbsEquivalences.gibbsEquivalenceStatement_proof
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.gibbsSpecification_props_everyMesh
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.equilibrium_class_eq_gibbs_states
    YangMills.Construction.TheStatementsProvedTogether.infiniteLattice_configurationSpace
    YangMills.Construction.TheStatementsProvedTogether.countable_product_of_group_copies
theorem torus_limits_periodic_gibbs :
    YangMills.Construction.InfiniteLattice.TorusLimitsSubsetPeriodicGibbs :=
  YangMills.Construction.InfiniteLattice.PeriodicGibbsOfTorusLimits.torusLimitsSubsetPeriodicGibbs_holds
    YangMills.Construction.TheStatementsProvedTogether.states_ext_of_continuous_local
    YangMills.Construction.TheStatementsProvedTogether.periodicLift_in_window
    gibbs_tfae
theorem periodic_gibbs_reflection_symmetries :
    YangMills.Construction.InfiniteLattice.PeriodicGibbsSymmetries.Statement :=
  YangMills.Construction.InfiniteLattice.PeriodicGibbsSymmetries.statement_holds
    YangMills.Construction.TheStatementsProvedTogether.periodic_gibbs_states_at_spacing
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.infinite_lattice_basic_structure
theorem periodicLift_clusterPt_seq_limit :
    YangMills.Construction.InfiniteLattice.PeriodicLiftAtCutoff.ClusterPointsAreSequentialLimits :=
  YangMills.Construction.InfiniteLattice.PeriodicLiftAtCutoff.SequentialLimits.clusterPointsAreSequentialLimits_of
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.compact_configuration_and_measure_spaces
    YangMills.Construction.TheStatementsProvedTogether.torus_state_periodic_measure
theorem exists_weakly_convergent_subseq_of_states :
    YangMills.Construction.InfiniteLattice.PeriodicExtensions.EveryStateSequenceHasWeaklyConvergentSubsequence.Statement :=
  YangMills.Construction.InfiniteLattice.PeriodicExtensions.EveryStateSequenceHasWeaklyConvergentSubsequence.holds
    YangMills.Construction.TheStatementsProvedTogether.infinite_lattice_gauge_field_space
theorem periodic_extension_weak_metric :
    YangMills.Construction.InfiniteLattice.PeriodicExtensions.WeakMetricStatement :=
  YangMills.Construction.InfiniteLattice.PeriodicExtensions.weakMetricStatement_holds
    exists_weakly_convergent_subseq_of_states
    YangMills.Construction.TheStatementsProvedTogether.infinite_lattice_gauge_field_space
theorem torus_limit_sets_nonempty :
    YangMills.Construction.InfiniteLattice.TorusLimitSetsNonempty :=
  YangMills.Construction.InfiniteLattice.torusLimitSetsNonempty_holds
    YangMills.Construction.TheStatementsProvedTogether.infinite_lattice_gauge_field_space
    YangMills.Construction.TheStatementsProvedTogether.torus_state_periodic_measure
theorem axis_mirror_projection_facts :
    YangMills.Construction.ReflectionPositivity.AxisMirror.ProjectionFacts :=
  YangMills.Construction.ReflectionPositivity.AxisMirror.ProjectionFacts.holds
theorem lipschitz_periodization :
    YangMills.Construction.LipschitzPeriodization.Statement :=
  YangMills.Construction.LipschitzPeriodization.statement_of_projectionFacts
    axis_mirror_projection_facts
theorem smeared_observable_bound :
    YangMills.Construction.AdmissibleConstants.SmearedObservableBound :=
  YangMills.Construction.AdmissibleConstants.smearedObservableBound_holds
theorem wilsonGibbsMeasure_isometry_invariant :
    YangMills.Construction.PeriodicLattice.WilsonMeasureIsometryInvariant :=
  YangMills.Construction.PeriodicLattice.IsometryInvariance.wilsonGibbsMeasure_isometry_invariant
theorem laplace_transform_and_log_of_tuple :
    YangMills.Construction.RandomTuple.TupleLaplaceLog.LaplaceAndLogTheorem :=
  YangMills.Construction.RandomTuple.TupleLaplaceLog.laplaceAndLogTheorem_holds
    YangMills.Construction.TheStatementsProvedTogether.joint_mgf_and_log
    YangMills.Construction.TheStatementsProvedTogether.holomorphic_contDiff_several_variables
theorem wilsonMeasure_isometries_cumulants_wellDefined :
    YangMills.Construction.PeriodicLattice.WilsonCumulantWellPosedness.statement :=
  YangMills.Construction.PeriodicLattice.WilsonCumulantWellPosedness.statement_holds
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.wilsonWeight_gauge_invariant
    wilsonGibbsMeasure_isometry_invariant
    laplace_transform_and_log_of_tuple
theorem centred_moment_le_coarse :
    YangMills.Construction.SeparatedMoments.CoarseCaseMomentBound :=
  YangMills.Construction.SeparatedMoments.coarseCaseMomentBound_of_smearedBound
    smeared_observable_bound
    wilsonMeasure_isometries_cumulants_wellDefined
theorem partition_function_entire_pos :
    YangMills.Construction.PartitionFunctionAnalyticity.Statement :=
  YangMills.Construction.PartitionFunctionAnalyticity.statement_proof
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.gauge_field_space_product
theorem connected_function_finite_sum_plaquettes :
    YangMills.Construction.ConnectedFunctionExpansion.Statement :=
  YangMills.Construction.ConnectedFunctionExpansion.statement_holds
    partition_function_entire_pos
    YangMills.Construction.TheStatementsProvedTogether.holomorphic_principalLog_calculus
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.gauge_field_space_product
    YangMills.Construction.TheStatementsProvedTogether.holomorphic_contDiff_several_variables
theorem periodization_covering_identities :
    YangMills.Construction.PeriodizationIdentities.Statement :=
  YangMills.Construction.PeriodizationIdentities.statement_holds
    YangMills.Construction.TheStatementsProvedTogether.cutoff_cover_periodic_lift
    YangMills.Construction.TheStatementsProvedTogether.functions_of_link_subsets
    connected_function_finite_sum_plaquettes
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.gauge_field_space_product
theorem grid_lattice_properties :
    YangMills.Construction.GridLattice.Properties :=
  YangMills.Construction.GridLattice.properties
theorem equalSideGrid_props :
    YangMills.Construction.EqualSideGrids.Statement :=
  YangMills.Construction.EqualSideGrids.statement_holds
    grid_lattice_properties
theorem reflection_grid_arithmetic :
    YangMills.Construction.ChessboardTori.ReflectionGridArithmetic.Statement :=
  YangMills.Construction.ChessboardTori.ReflectionGridArithmetic.holds
    equalSideGrid_props
theorem reflection_group_coordinatewise :
    YangMills.Construction.ChessboardTori.ReflectionGroupCoordinates.Statement :=
  YangMills.Construction.ChessboardTori.ReflectionGroupCoordinatesProof.statement_holds
theorem chessboard_cellFunction_copies :
    YangMills.Construction.ChessboardTori.CellFunctionCopies.Statement :=
  YangMills.Construction.ChessboardTori.CellFunctionCopies.statement_holds
    reflection_group_coordinatewise
theorem chessboard_torus_wall_dist_open_cells :
    YangMills.Construction.ChessboardTori.WallDistanceAndOpenCells.Statement :=
  YangMills.Construction.ChessboardTori.wallDistanceAndOpenCells_holds
theorem chessboard_covering_grid_cells :
    YangMills.Construction.ChessboardTori.ProjOnGridCells.Statement :=
  YangMills.Construction.ChessboardTori.ProjOnGridCells.statement_holds
    chessboard_torus_wall_dist_open_cells
    reflection_grid_arithmetic
theorem isometries_transport_links_supports_plaquettes :
    YangMills.Construction.GibbsAtFixedSpacing.SymmetriesTransportLinksSupportsAndPlaquettes :=
  YangMills.Construction.GibbsAtFixedSpacing.symmetriesTransportLinksSupportsAndPlaquettes_holds
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.infiniteLattice_field_isometry_properties
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.plaquette_energy_indep_basepoint_orientation
theorem chessboard_links_plaquettes_isometry :
    YangMills.Construction.ChessboardTori.LatticeSymmetryAction.Statement :=
  YangMills.Construction.ChessboardTori.LatticeSymmetryAction.statement_holds
    isometries_transport_links_supports_plaquettes
theorem chessboard_exp_observable :
    YangMills.Construction.ChessboardTori.ExponentialObservableRules.Statement :=
  YangMills.Construction.ChessboardTori.ExponentialObservableRules.holds
    chessboard_links_plaquettes_isometry
theorem chessboard_torus_induced_isometries :
    YangMills.Construction.ChessboardTori.TorusInducedSymmetries.Statement :=
  YangMills.Construction.ChessboardTori.TorusInducedSymmetries.statement_proof
    reflection_group_coordinatewise
    reflection_grid_arithmetic
theorem chessboard_sites_off_facePlanes :
    YangMills.Construction.ChessboardTori.PointsOffWalls.Statement :=
  YangMills.Construction.ChessboardTori.PointsOffWalls.statement_holds
theorem torus_reflection_group_quotient :
    YangMills.Construction.ChessboardTori.TorusReflectionGroup.Statement :=
  YangMills.Construction.ChessboardTori.TorusReflectionGroup.holds
    reflection_grid_arithmetic
    reflection_group_coordinatewise
    chessboard_torus_induced_isometries
    chessboard_sites_off_facePlanes
theorem chessboard_grid_basic :
    YangMills.Construction.ChessboardTori.GridBasicProperties.Statement :=
  YangMills.Construction.ChessboardTori.GridBasicProperties.proof
    chessboard_sites_off_facePlanes
    chessboard_links_plaquettes_isometry
    chessboard_exp_observable
    reflection_group_coordinatewise
    chessboard_cellFunction_copies
    chessboard_torus_wall_dist_open_cells
    chessboard_torus_induced_isometries
    torus_reflection_group_quotient
    chessboard_covering_grid_cells
theorem chessboard_cells_blocks_parity :
    YangMills.Construction.ChessboardTori.CellsBlocksAndSigns.Statement :=
  YangMills.Construction.ChessboardTori.CellsBlocksAndSigns.statement_holds
    chessboard_grid_basic
    reflection_grid_arithmetic
theorem standard_partitions_level_scaling :
    YangMills.Construction.PeriodicLattice.StandardPartitionsInUnits :=
  YangMills.Construction.PeriodicLattice.standardPartitionsInUnits_holds
theorem cube_block_distance_trace_facts :
    YangMills.Construction.PeriodicLattice.CubeGeometry.ElementaryLatticeFacts :=
  YangMills.Construction.PeriodicLattice.CubeGeometry.elementaryLatticeFacts_holds
    YangMills.Construction.TheStatementsProvedTogether.torus_block_partition_properties
    standard_partitions_level_scaling
    YangMills.Construction.TheStatementsProvedTogether.torus_lattice_coordinate_description
    YangMills.Construction.TheStatementsProvedTogether.unitary_two_log_spec
theorem chessboard_lifting_rules :
    YangMills.Construction.ChessboardTori.LiftingRules.Statement :=
  YangMills.Construction.ChessboardTori.LiftingRules.holds
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.torus_covering_lifts_and_descended_maps
    YangMills.Construction.TheStatementsProvedTogether.card_sites_plaquettes
    cube_block_distance_trace_facts
    chessboard_grid_basic
theorem chessboard_block_invariance :
    YangMills.Construction.ChessboardTori.ChessboardBlockInvariance.Statement :=
  YangMills.Construction.ChessboardTori.ChessboardBlockInvariance.chessboardBlockInvariance_holds
    reflection_grid_arithmetic
    chessboard_cells_blocks_parity
    chessboard_lifting_rules
    chessboard_grid_basic
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.wilsonWeight_gauge_invariant
theorem chessboard_torus_transfer_properties :
    YangMills.Construction.ChessboardTori.TransferAssertions.Statement :=
  YangMills.Construction.ChessboardTori.TransferAssertions.holds
    YangMills.Construction.TheStatementsProvedTogether.haar_expChart_properties
theorem crossingKernel_expansion :
    YangMills.Construction.ChessboardTori.KernelExpansion.Statement :=
  YangMills.Construction.ChessboardTori.KernelExpansion.statement_holds
theorem squareSummable_trace_mul_cyclic :
    YangMills.Construction.SquareSummable.CyclicTraceProductBounds :=
  YangMills.Construction.SquareSummable.CyclicTraceProducts.cyclicTraceProductBounds_holds
theorem chessboard_cyclic_trace :
    YangMills.Construction.ChessboardTori.CyclicTraceFormula.Statement :=
  YangMills.Construction.ChessboardTori.CyclicTraceFormula.statement_holds
    crossingKernel_expansion
    chessboard_torus_transfer_properties
    squareSummable_trace_mul_cyclic
theorem chessboard_lattice_quotients :
    YangMills.Construction.ChessboardTori.LatticeQuotients.Statement :=
  YangMills.Construction.ChessboardTori.LatticeQuotients.statement_holds
theorem chessboard_quotient_edges_faces :
    YangMills.Construction.ChessboardTori.ProjOnEdgesAndFaces.Statement :=
  YangMills.Construction.ChessboardTori.ProjOnEdgesAndFaces.holds
    chessboard_lattice_quotients
theorem cellFunction_slab_restriction :
    YangMills.Construction.ChessboardTori.SlabRestrictionOfCellFunctions.Statement :=
  YangMills.Construction.ChessboardTori.SlabRestrictionOfCellFunctions.statement_holds
    chessboard_quotient_edges_faces
    chessboard_torus_transfer_properties
theorem chessboard_torus_quotient_maps :
    YangMills.Construction.ChessboardTori.QuotientMapsStatement :=
  YangMills.Construction.ChessboardTori.InducedQuotientMaps.quotientMaps
    reflection_grid_arithmetic
    chessboard_links_plaquettes_isometry
    chessboard_lattice_quotients
    chessboard_quotient_edges_faces
    YangMills.Construction.TheStatementsProvedTogether.haar_expChart_properties
    YangMills.Construction.TheStatementsProvedTogether.tower_sublattices_symmetries_scalings
    wilsonGibbsMeasure_isometry_invariant
theorem chessboard_slab_symmetries :
    YangMills.Construction.ChessboardTori.SlabSymmetries.Statement :=
  YangMills.Construction.ChessboardTori.SlabSymmetries.proof
    chessboard_torus_quotient_maps
    chessboard_torus_transfer_properties
    chessboard_quotient_edges_faces
theorem chessboard_layer_carrying_elements :
    YangMills.Construction.ChessboardTori.LayerCarryingElements.Statement :=
  YangMills.Construction.ChessboardTori.LayerCarryingElements.holds
    reflection_grid_arithmetic
    reflection_group_coordinatewise
    chessboard_torus_quotient_maps
    chessboard_quotient_edges_faces
    chessboard_slab_symmetries
theorem chessboard_period_group_expectation :
    YangMills.Construction.ChessboardTori.PeriodExpectation.Statement :=
  YangMills.Construction.ChessboardTori.PeriodExpectation.holds
    chessboard_quotient_edges_faces
    reflection_grid_arithmetic
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.wilsonWeight_gauge_invariant
theorem wilson_weight_slab_decomposition :
    YangMills.Construction.ChessboardTori.SlabDecompositionOfWilsonWeight.Statement :=
  YangMills.Construction.ChessboardTori.SlabDecompositionOfWilsonWeight.statement_of_transferAssertions
    chessboard_torus_transfer_properties
theorem chessboard_one_axis_reflection_bound :
    YangMills.Construction.ChessboardTori.OneAxisReflectionBound.Statement :=
  YangMills.Construction.ChessboardTori.OneAxisReflectionBound.statement_holds
    reflection_grid_arithmetic
    chessboard_grid_basic
    chessboard_torus_transfer_properties
    chessboard_slab_symmetries
    chessboard_cyclic_trace
    chessboard_period_group_expectation
    wilson_weight_slab_decomposition
    cellFunction_slab_restriction
    chessboard_layer_carrying_elements
theorem family_chessboard_bound :
    YangMills.Construction.ChessboardTori.FamilyChessboardBound.Statement :=
  YangMills.Construction.ChessboardTori.FamilyChessboardBound.proof
    chessboard_one_axis_reflection_bound
    chessboard_grid_basic
theorem chessboard_expectation_rules :
    YangMills.Construction.ChessboardTori.ChessboardExpectationRules.Statement :=
  YangMills.Construction.ChessboardTori.ChessboardExpectationRules.holds
    chessboard_cellFunction_copies
    reflection_group_coordinatewise
    chessboard_cells_blocks_parity
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.torusLattice_covering
theorem periodized_source_terms :
    YangMills.Construction.ChessboardTori.PeriodizedSourceTerms.Statement :=
  YangMills.Construction.ChessboardTori.PeriodizedSourceTerms.statement_holds
    chessboard_torus_wall_dist_open_cells
    reflection_group_coordinatewise
theorem chessboard_periodizedSource_expectation :
    YangMills.Construction.ChessboardTori.PeriodizedSourceExpectation.Statement :=
  YangMills.Construction.ChessboardTori.PeriodizedSourceExpectation.proof
    chessboard_grid_basic
    periodized_source_terms
    chessboard_cells_blocks_parity
    chessboard_lifting_rules
theorem chessboard_estimate :
    YangMills.Construction.ChessboardTori.ChessboardInequality.Statement :=
  YangMills.Construction.ChessboardTori.ChessboardInequality.holds
    reflection_grid_arithmetic
    family_chessboard_bound
    chessboard_block_invariance
    chessboard_expectation_rules
    periodized_source_terms
    chessboard_periodizedSource_expectation
theorem chessboard_torus_reduction :
    YangMills.Construction.ChessboardTori.TorusReduction.Statement :=
  YangMills.Construction.ChessboardTori.TorusReduction.proof
    reflection_grid_arithmetic
    chessboard_cells_blocks_parity
    chessboard_lifting_rules
    chessboard_grid_basic
    chessboard_estimate
    YangMills.Construction.TheStatementsProvedTogether.card_sites_plaquettes
theorem chessboard_seminorms_torus :
    YangMills.Construction.ChessboardTori.TorusChessboardSeminorms.Statement :=
  YangMills.Construction.ChessboardTori.TorusChessboardSeminorms.proof
    chessboard_torus_reduction
    chessboard_cells_blocks_parity
    chessboard_grid_basic
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.wilsonWeight_gauge_invariant
theorem chessboard_estimate_reflection_grid :
    YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.Statement :=
  YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.proof
    chessboard_torus_reduction
    chessboard_seminorms_torus
    chessboard_torus_quotient_maps
    chessboard_grid_basic
    reflection_grid_arithmetic
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.wilsonWeight_gauge_invariant
theorem bonds_plaquettes_nondegenerate :
    YangMills.Construction.ReflectionPositivity.PlaquetteNondegeneracy.NondegeneracyStatement :=
  YangMills.Construction.ReflectionPositivity.PlaquetteNondegeneracy.nondegeneracy
    YangMills.Construction.TheStatementsProvedTogether.elementary_square_corners
theorem curvatureDensity_symmetry_covariant :
    YangMills.Construction.ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.SymmetryCovariance :=
  YangMills.Construction.ReflectionPositivity.CutoffMirrors.CurvatureDensityCovariance.symmetryCovariance
    bonds_plaquettes_nondegenerate
    wilsonGibbsMeasure_isometry_invariant
    _root_.YangMills.Construction.TheStatementsProvedTogether.LatticeSymmetries.wilsonWeight_gauge_invariant
    YangMills.Construction.TheStatementsProvedTogether.metric_torus_test_function_facts
    YangMills.Construction.TheStatementsProvedTogether.tower_sublattices_symmetries_scalings
theorem reflection_grid_acts_on_cell_algebra :
    YangMills.Construction.MirrorGridsAllSides.AllGridsActOnCellObservables :=
  YangMills.Construction.MirrorGridsAllSides.allGridsActOnCellObservables_holds
theorem mirror_grid_torus_cells :
    YangMills.Construction.MirrorGridsAllSides.AllGridsTorusCellStructure :=
  YangMills.Construction.MirrorGridsAllSides.allGridsTorusCellStructure_holds
    reflection_grid_arithmetic
    chessboard_covering_grid_cells
    chessboard_cells_blocks_parity
theorem reflectionGroup_acts_on_cells :
    YangMills.Construction.MirrorGridsAllSides.AllGridsReflectionGroupActsOnCells :=
  YangMills.Construction.MirrorGridsAllSides.allGridsReflectionGroupActsOnCells_holds
    reflection_group_coordinatewise
    chessboard_cells_blocks_parity
theorem mirror_group_acts_torus_cells :
    YangMills.Construction.MirrorGridsAllSides.AllGridsTorusGroupActsOnCells :=
  YangMills.Construction.MirrorGridsAllSides.allGridsTorusGroupActsOnCells
    chessboard_torus_induced_isometries
    torus_reflection_group_quotient
    reflection_group_coordinatewise
    chessboard_cells_blocks_parity
theorem reflection_grid_action_cell_observables :
    YangMills.Construction.MirrorGridsAllSides.AllGridsTorusActOnCellObservables :=
  YangMills.Construction.MirrorGridsAllSides.allGridsTorusActOnCellObservables_holds
    chessboard_lifting_rules
    reflectionGroup_acts_on_cells
    mirror_grid_torus_cells
    mirror_group_acts_torus_cells
theorem side_odd_multiple_spacing_mirror_grid :
    YangMills.Construction.MirrorGridsAllSides.CellSideOddMultipleEveryGrid :=
  YangMills.Construction.MirrorGridsAllSides.cellSideOddMultipleEveryGrid_holds
theorem mirror_grid_cell_centres_mem_lattice :
    YangMills.Construction.MirrorGridsAllSides.AllGridsCellCentresInLattice :=
  YangMills.Construction.MirrorGridsAllSides.allGridsCellCentresInLattice_holds
    side_odd_multiple_spacing_mirror_grid
theorem reflection_grid_coarsening :
    YangMills.Construction.MirrorGridsAllSides.AllGridsCoarseningOnSpace :=
  YangMills.Construction.MirrorGridsAllSides.allGridsCoarseningOnSpace_holds
end YangMills.Construction.TheStatementsProvedTogether
