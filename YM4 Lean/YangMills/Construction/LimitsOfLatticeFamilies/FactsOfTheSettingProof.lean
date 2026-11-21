import YangMills.Construction.LimitsOfLatticeFamilies.ClassC1AndTheGradientThroughTheLift
import YangMills.Construction.LimitsOfLatticeFamilies.ClosedBallsAndTheTorusAreCompact
import YangMills.Construction.LimitsOfLatticeFamilies.CompactlySupportedClassC1FunctionsAreLipschitz
import YangMills.Construction.LimitsOfLatticeFamilies.DifferencesOfTranslatesAreSmall
import YangMills.Construction.LimitsOfLatticeFamilies.EffectiveConstantsReadAdmittedRadiiOnly
import YangMills.Construction.LimitsOfLatticeFamilies.FactsOfTheSetting
import YangMills.Construction.LimitsOfLatticeFamilies.FunctionSpacesAndTheSharpSeminorm
import YangMills.Construction.LimitsOfLatticeFamilies.LengthOfAPointGivesAnInvariantDistance
import YangMills.Construction.LimitsOfLatticeFamilies.MembersOfHierarchiesOnSeparatedTuples
import YangMills.Construction.LimitsOfLatticeFamilies.OneProductAndEntriesZero
import YangMills.Construction.LimitsOfLatticeFamilies.ProductsPermutationsSubTuplesAndCentredTerms
import YangMills.Construction.LimitsOfLatticeFamilies.ProjectionKernelsAndShortestLifts
import YangMills.Construction.LimitsOfLatticeFamilies.SeparatedTensorsLieInFiniteBalls
import YangMills.Construction.LimitsOfLatticeFamilies.SeparationOfASeparatedTupleIsPositive
import YangMills.Construction.LimitsOfLatticeFamilies.TranslationsActOnFunctionsAsIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeLimits.SettingFactsHold
theorem eventuallyIn_finite_conj :
    ModelSpace.SettingFacts.EventuallyInFiniteConj := by
  intro J _ k P hP
  have hP' : ∀ i, ∃ j₀, ∀ j ∈ J, j₀ ≤ j → P i j := hP
  choose t ht using hP'
  exact ⟨Finset.univ.sup t, fun j hj hle i =>
    ht i j hj ((Finset.le_sup (Finset.mem_univ i)).trans hle)⟩
theorem of_claims
    (hLift : C1ViaLift.Claim)
    (hCompact : CompactBallsAndTorus.Claim)
    (hLipschitz : C1CompactSuppIsLipschitz)
    (hRadii : EffConstReadsAdmissibleRadii)
    (hNorm : InvariantDistFromNorm.Claim)
    (hSep : SepTupleMembers.Claim)
    (hCommon : CommonProductAndZeroComponent)
    (hClosed : TupleClassesClosed.Claim)
    (hProj : ProjKernelAndMinimalLifts.Claim)
    (hMinSep : MinSeparationPos)
    (hBall : SepTensorsInFiniteBalls.Claim)
    (hShiftDiff : ShiftDifferenceBounds)
    (hShift : ShiftIsIsometry)
    (hSharp : SharpSeminorm.Properties) :
    SettingFactsHold.statement := fun s M Y =>
  { dist_invariant := hNorm s Y
    closedBall_compact := ((hCompact s).1 Y).1
    torus_compact := (hCompact s).2
    compact_bounded := ((hCompact s).1 Y).2
    eventually_conj := eventuallyIn_finite_conj
    commonProduct := hCommon s Y
    minSeparation_pos := hMinSep s Y
    effConst_admissible := hRadii.1 s M Y
    torusFactor_eq := hRadii.2
    sepTensors_bounded := hBall s Y
    shift_isometric := hShift s M Y
    shift_diff := hShiftDiff s M Y
    proj_kernels := (hProj s).1
    proj_lifts := (hProj s).2 Y
    isC1_iff := hLift s Y
    c1_lipschitz := hLipschitz.1 s Y
    torus_support := hLipschitz.2 s
    submodules := hSharp s M Y
    product_closed := (hClosed s Y).1
    centred_defined := (hClosed s Y).2
    hierarchy_sepTuples := hSep s Y }
end YangMills.Construction.LatticeLimits.SettingFactsHold
end
