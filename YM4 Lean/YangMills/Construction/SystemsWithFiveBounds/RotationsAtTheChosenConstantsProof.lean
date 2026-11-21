import YangMills.Construction.Continuum.RulesOfTheOrthogonalActionProof
import YangMills.Construction.Continuum.OnePointFunctionIsImmaterialForTheInvariance
import YangMills.Construction.Continuum.TheRecursionOfTheConnectedFunctionsIsTriangular
import YangMills.Construction.InfiniteLattice.SeparationAndAdmissibilityOfTuplesOfFourSpace
import YangMills.Construction.LimitTheorem.MeasureOfTheTranslationsOnOneCompletion
import YangMills.Construction.LimitTheorem.RotationInvarianceOfACentredLimit
import YangMills.Construction.LimitTheorem.ComponentFieldData
import YangMills.Construction.SystemsWithFiveBounds.BoundOnOneInsertedFieldAtNumbers
import YangMills.Construction.SystemsWithFiveBounds.ConditionsAtFixedConstantsProof
import YangMills.Construction.SystemsWithFiveBounds.ConditionsOfALimitAtConstantsProof
import YangMills.Construction.SystemsWithFiveBounds.InsertionBoundOfALimitAtNumbers
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
section
open MeasureTheory Filter InfiniteLattice
open scoped Topology ComplexOrder Matrix
noncomputable section
namespace WindowLimits
open LatticeConventions (NormalHyperplane)
open LimitConventions (ApproxTriple)
open ReflectionPositivity.ApproximatingSequences (LatticeApproximation)
open FirstPassageSeqs (originPlaquette)
open LimitTheorem (evalOnMap)
open SeparatedTuples (TupleFunctional SepTuple)
section StatesApproximating
variable {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (Q : CutoffCouplingSequence L)
variable {Q} {ρ ν : ∀ j, Measure (Q.Fields j)} {hρ : ∀ j, ρ j ∈ Q.gibbsStates j}
private theorem convergesTo_latticeApprox (A : StatesApproximation Q ρ ν hρ) {σ : TupleFunctional}
    (hσ : Q.HasLimit ρ ν σ) : ApproxTriple.ConvergesTo (Q.latticeApprox ρ ν hρ) σ := by apply _root_.YangMills.SharedProofs.p60486 <;> assumption
include hL in
private theorem latticeApprox_isBounded (hB : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (A : StatesApproximation Q ρ ν hρ) {σ : TupleFunctional} (hσ : Q.HasLimit ρ ν σ) :
    LatticeApproximation.IsBoundedForSomeM (unitAxisMirrorData hL) (Q.latticeApprox ρ ν hρ) :=
  (hB.1 (unitAxisMirrorData hL) (Q.latticeApprox ρ ν hρ) fun X => ⟨σ X, convergesTo_latticeApprox A hσ X⟩).2
end StatesApproximating
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace WindowLimits
open BoundsOnEverySide TestFunctions
open LimitTheorem
open LimitConventions (cubicMotionGroup)
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
private theorem sharpNormR4_nonneg (M : ℝ) (f : (Fin 4 → ℝ) → ℝ) : 0 ≤ sharpNormR4 M f := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.sharpNormR4_nonneg <;> assumption
section Growth
open TestSpaces
private theorem growthBound_of_testSpaceGrowth
    (hN : Continuum.TwoPresentations.PresentationsAgree)
    {C : ConditionConstants} {σ : TupleFunctional} (hf : IsSepFunctional (evalOnMap σ))
    (hg : TestSpaces.GrowthBound C.kE C.cE C.CE C.κ (evalOnMap σ)) :
    LimitTheorem.GrowthBound C σ := by apply _root_.YangMills.SharedProofs.p40086 <;> assumption
end Growth
section Regularity
variable    {σ : TupleFunctional}
private theorem isRegular_of_testSpaceRegular {σ : TupleFunctional}
    (h : TestSpaces.IsRegular (evalOnMap σ)) : LimitTheorem.IsRegular σ := by apply _root_.YangMills.SharedProofs.p39455 <;> assumption
private theorem isRegular_of_testSpaceGrowth (hD : TestSpaces.OffDiagonal.OffDiagonalFacts) {σ : TupleFunctional}
    (hf : TestSpaces.IsSepFunctional (evalOnMap σ)) {k : ℕ} {c C κ : ℝ}
    (hg : TestSpaces.GrowthBound k c C κ (evalOnMap σ)) : LimitTheorem.IsRegular σ := by
  obtain ⟨-, -, -, -, U, hU, -⟩ := hg
  exact isRegular_of_testSpaceRegular ((hD 1 one_pos).2.2.1 (evalOnMap σ) U hf hU).1
end Regularity
end WindowLimits
end
end
section
open Set
noncomputable section
namespace SystemsWithFiveBounds
open SeparatedTuples (SepTuple)
open LimitTheorem (ExistentialConstants)
namespace BoundConstants
variable (N : BoundConstants)
variable {N}
private theorem cumulantBound_pos (h : N.Admissible) (n : ℕ) (d : ℝ) {R : ℝ} (hR : 0 < R) :
    0 < N.cumulantBound n d R := by apply _root_.YangMills.SharedProofs.p39650 <;> assumption
private theorem cumulantBound_antitone (h : N.Admissible) (n : ℕ) {d d' R : ℝ} (hd : 0 < d)
    (hle : d ≤ d') (hR : 0 < R) : N.cumulantBound n d' R ≤ N.cumulantBound n d R := by apply _root_.YangMills.SharedProofs.p25134 <;> assumption
end BoundConstants
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily)
open Probability (IsBoundedRealRV)
open LimitTheorem (evalOnMap)
open WindowLimits
open TestFunctions
open SeparatedTuples (TupleFunctional)
section Moments
variable {F : StatedSideFamily} {N : BoundConstants} (B : BoundsHoldAt F N) {K : ℕ+} {β : ℝ}
  {ρ ν : Measure (GaugeField (PeriodicLattice.meshSize F.L ((K : ℕ) : ℤ)))}
include B in
private theorem abs_centredMoment_le (hLeo : Cumulants.MomentCumulantFormula.Claim)
    (hM : SmearedObservablesWellDefined)
    (hD : F.IsFirstPassage K β) (hρs : ρ ∈ F.stateSet F.L K β) (hνs : ν ∈ F.stateSet F.L K β)
    {n : ℕ} (f : Fin n → AmbientSpace → ℝ)
    (hf : ∀ i, f i ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)))
    {d R : ℝ} (hd : 0 < d) (hR : 0 < R) (hb : ∀ i, ∃ x, tsupport (f i) ⊆ closedBallR4 x R)
    (hs : HasSeparatedSupportsR4 f d) :
    |∫ U, ∏ i, (smearedEnergy (f i) U - ∫ V, smearedEnergy (f i) V ∂ν) ∂ρ| ≤
      momentWeight N n d R * ∏ i, sharpNormR4 F.M (f i) := by apply _root_.YangMills.SharedProofs.p95142 <;> assumption
end Moments
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily GibbsStateSequence unitMassBumps)
open WindowLimits
open TestFunctions
open LimitTheorem
open SystemsWithFiveBounds.GibbsLimitInheritance (unitIntegralTestFunctions)
open LimitConventions (cubicMotionGroup)
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
section WindowLimit
variable {F : StatedSideFamily} {N : BoundConstants} (Q : WindowStates F) {σ : TupleFunctional}
private theorem tendsto_cutoff_coe : Tendsto (fun j => ((Q.K j : ℕ+) : ℕ)) atTop atTop := by apply _root_.YangMills.SharedProofs.p107289 <;> assumption
end WindowLimit
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily)
open WindowLimits
open LimitTheorem
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
section WindowLimit
variable {F : StatedSideFamily} {N : BoundConstants} (Q : WindowStates F) {σ : TupleFunctional}
private theorem abs_limitValue_le (hLeo : Cumulants.MomentCumulantFormula.Claim)
    (hM : SmearedObservablesWellDefined) (B : BoundsHoldAt F N)
    (hσ : Q.HasLimit σ) {n : ℕ} (X : SepTupleOfCard n) {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (hb : ∀ i, ∃ x, tsupport (X.1 i) ⊆ TestFunctions.closedBallR4 x R)
    (hs : TestFunctions.HasSeparatedSupportsR4 X.1 d) :
    |evalOnMap σ ⟨n, X⟩| ≤ momentWeight N n d R * ∏ i, TestFunctions.sharpNormR4 F.M (X.1 i) := by
  refine le_of_tendsto (hσ ⟨n, X⟩).abs (Eventually.of_forall fun j => ?_)
  exact abs_centredMoment_le B hLeo hM (Q.isFirstPassage j) (Q.ρ_state j) (Q.ν_state j) X.1 X.2.1 hd hR hb hs
end WindowLimit
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace WindowLimits
open BoundsOnEverySide
open LimitTheorem
open SeparatedTuples (TupleFunctional SepTuple RealValued)
open TestSpaces (SepTupleOfCard)
open TorusMetric (euclidNormVec)
open TestFunctions (closedBallR4 setDistR4 sharpNormR4 HasSeparatedSupportsR4)
private theorem setDistR4_comm (S T : Set (Fin 4 → ℝ)) : setDistR4 S T = setDistR4 T S := by apply _root_.YangMills.SharedProofs.p12154 <;> assumption
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology ENNReal
noncomputable section
namespace WindowLimits
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
open TupleLists (ofList toList)
open Probability (IsBoundedRealRV)
open BoundsOnEverySide TestFunctions
open LimitTheorem
section Reindexing
private theorem tendsto_succPNat_atTop : Tendsto Nat.succPNat atTop atTop := by apply _root_.YangMills.SharedProofs.p14344 <;> assumption
end Reindexing
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace WindowLimits
open BoundsOnEverySide TestFunctions
open LimitTheorem
open SeparatedTuples (TupleFunctional SepTuple DecompositionData)
open TestSpaces (SepTupleOfCard)
open TupleLists (ofList toList)
open TorusMetric (euclidNormVec)
private theorem tupleFunctional_ext {σ τ : TupleFunctional} (h : ∀ Y, σ Y = τ Y) : σ = τ := by apply _root_.YangMills.SharedProofs.p5793 <;> assumption
private theorem evalOnMap_ofList (τ : TupleFunctional) (W : SepTuple) : evalOnMap τ (ofList W) = τ W := by apply _root_.YangMills.SharedProofs.p25328 <;> assumption
section Centred
variable      {S : CumulantFamily}
private theorem evalOnMap_centredOf (S : CumulantFamily) (X : TestSpaces.SepTuple) :
    evalOnMap (centredOf S) X = TestSpaces.centredOfCumulants S X := by apply _root_.YangMills.SharedProofs.p13412 <;> assumption
end Centred
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily)
open SeparatedTuples (TupleFunctional SepTuple DecompositionData)
open TestSpaces (SepTupleOfCard)
open TupleLists (ofList toList)
open TorusMetric (euclidNormVec)
open WindowLimits
open LimitTheorem
open WindowLimits
open TestFunctions
open LimitTheorem
private structure Inputs : Prop where
  observables : SmearedObservablesWellDefined
  momentCumulant : Cumulants.MomentCumulantFormula.Claim
  bounded : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded
  complements : ReflectionPositivity.ReconstructionComplements.ComplementsTheorem
  tupleFacts : SeparatedTuples.BasicFacts.MainFacts
  inheritance : GibbsLimitInheritance.InheritanceTheorem
  presentations : Continuum.TwoPresentations.PresentationsAgree
  offDiagonal : TestSpaces.OffDiagonal.OffDiagonalFacts
  determination : CanonicalDecompositionUniqueness.DecompositionDeterminations
  limit : WindowLimitConditions
  decomposition : CanonicalDecompositionConditions
section WindowLimit
variable {F : StatedSideFamily} {N : BoundConstants} (P : Inputs) (B : BoundsHoldAt F N) (Q : WindowStates F) {σ : TupleFunctional}
include P in
private theorem isSepFunctional_of_limit (hσ : Q.HasLimit σ) : TestSpaces.IsSepFunctional (evalOnMap σ) :=
  (P.limit.limit_conditions Q hσ).isSepFunctional
include P in
private theorem limitSymmetries_of_limit (hσ : Q.HasLimit σ) : LimitSymmetries σ :=
  (P.limit.limit_conditions Q hσ).symmetries
include P in
private theorem reconstructionProperties_of_limit (hσ : Q.HasLimit σ) : ReconstructionProperties σ :=
  (P.limit.limit_conditions Q hσ).reconstruction
include P B in
private theorem testSpaceGrowth_of_limit (hσ : Q.HasLimit σ) :
    TestSpaces.GrowthBound (growthOrder N)
      (1 + 2 * SeparatedBound.extFactorAbs)
      (growthConst F.M N (unitBallBound F.M N)) (20 + N.factorialExponent) (evalOnMap σ) :=
  P.decomposition.growth_bound B Q hσ
include P B in
private theorem isRegular_of_limit (hσ : Q.HasLimit σ) : LimitTheorem.IsRegular σ :=
  isRegular_of_testSpaceGrowth P.offDiagonal (isSepFunctional_of_limit P Q hσ) (testSpaceGrowth_of_limit P B Q hσ)
include P B in
private theorem growthBound_of_limit (hσ : Q.HasLimit σ) (cl r : SepTuple → SepTuple → ℝ) (E : LawConstants) :
    LimitTheorem.GrowthBound ((existentialConstantsAt F.M N (unitBallBound F.M N) cl r).toConditionConstants E) σ :=
  growthBound_of_testSpaceGrowth P.presentations (isSepFunctional_of_limit P Q hσ)
    (testSpaceGrowth_of_limit P B Q hσ)
include P B in
private theorem clustering_of_extremal (hσ : Q.HasLimit σ) (hpure : ∀ j, Q.ρ j ∈ cutoffExtremalSet F.L (Q.K j) (Q.β j))
    (X Y : SepTuple) (v : Fin 4 → ℝ) (hv : clusteringRadiusOf X Y ≤ euclidNormVec v) :
    SepTuple.Composable X (SeparatedTuples.push (SeparatedTuples.translate v) Y) ∧
      |σ (SepTuple.juxt X (SeparatedTuples.push (SeparatedTuples.translate v) Y)) - σ X * σ Y| ≤
        clusteringConstOf F.M N X Y * (euclidNormVec v ^ 2)⁻¹ :=
  P.decomposition.cluster_law B Q hσ hpure X Y v hv
end WindowLimit
section Decomposition
variable {F : StatedSideFamily} {N : BoundConstants} (P : Inputs) (B : BoundsHoldAt F N) {Q : WindowStates F} {S : CumulantFamily}
include P B in
private theorem exists_windowStates_of_component (hρν : Q.ρ = Q.ν) (hvol : ∀ j, IsInfiniteVolumeLimit F.L (Q.K j) (Q.β j) (Q.ν j)) (hσ : Q.HasLimit (centredOf S))
    {A' : DecompositionData} (hA : A'.IsCanonical (centredOf S)) (ξ : A'.space) :
    ∃ Q' : WindowStates F, Q'.HasLimit (A'.comp ξ) ∧
      ∀ j, Q'.ρ j ∈ cutoffExtremalSet F.L (Q'.K j) (Q'.β j) :=
  P.decomposition.exists_states_of_component B hρν hvol hσ hA ξ
end Decomposition
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open WindowLimits
open BoundsOnEverySide TestFunctions
open LimitTheorem
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
section WindowLimit
variable {F : StatedSideFamily} {N : BoundConstants} (P : Inputs) (Q : WindowStates F) {σ : TupleFunctional}
  {ϑ : ℝ}
private theorem states_obeyTwoPointLaw (hT : TwoPointLawAt F N ϑ) (K : ExistentialConstants) :
    GibbsLimitInheritance.StatesObeyTwoPointLaw ϑ (K.toConditionConstants (lawConstantsOf N)) Q.ρ := by apply _root_.YangMills.SharedProofs.p41393 <;> assumption
include P in
private theorem twoPointLaw_of_limit (hT : TwoPointLawAt F N ϑ) (hσ : Q.HasLimit σ) (K : ExistentialConstants) :
    TwoPointLawHoldsAt ϑ (K.toConditionConstants (lawConstantsOf N)) σ := by
  obtain ⟨-, -, -, -, hlaw⟩ := P.inheritance.1 F.L F.admissible F.M ϑ Q.K Q.ρ Q.ν σ
    (fun j => (Q.ρ_mem j).1.1) hσ
  exact hlaw _ (states_obeyTwoPointLaw Q hT K)
end WindowLimit
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology ENNReal NNReal InnerProductSpace
noncomputable section
namespace WindowLimits
open TestSpaces (SepTupleOfCard)
open HilbertSpaceBasics (IsPosSemidef IsOrthProjOnto orthProjOnto ofBounded)
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass vacuum timeShift spaceShift embedSpatial
  timeBasisVec posTupleVec)
open ReflectionPositivity.PairMeasureOperators (pairHamiltonian groundStateProjection)
open ReflectionPositivity.ContractionFunctionals (IsAdmissible)
open TupleLists (ofList toList)
open TorusMetric (euclidNormVec)
open BoundsOnEverySide
open LimitTheorem
open SeparatedTuples hiding conjugation
open ReflectionPositivity.TupleForm
open SpectralTheory
open CanonicalDecompositionUniqueness
section Auxiliary
private theorem hasReconstruction_of_properties {σ : TupleFunctional} (hl : ReconstructionProperties σ)
    (p : IsPosSemidef (reflectionForm σ)) : HasReconstruction σ p := by
  obtain ⟨-, -, q, hq, -⟩ := hl
  exact hq
private theorem exists_rigidMotion_hyperoctahedral (w : TorusTransport.hyperoctahedral) :
    ∃ r : Motions.RigidMotion, IsHyperoctahedralMotion r ∧ r.toFun = w.1 := by apply _root_.YangMills.SharedProofs.p35926 <;> assumption
end Auxiliary
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology ENNReal NNReal InnerProductSpace
noncomputable section
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily)
open TestSpaces (SepTupleOfCard)
open HilbertSpaceBasics (IsPosSemidef IsOrthProjOnto orthProjOnto ofBounded)
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass vacuum timeShift spaceShift embedSpatial
  timeBasisVec posTupleVec)
open ReflectionPositivity.PairMeasureOperators (pairHamiltonian groundStateProjection)
open ReflectionPositivity.ContractionFunctionals (IsAdmissible)
open TupleLists (ofList toList)
open TorusMetric (euclidNormVec)
open WindowLimits
open BoundsOnEverySide TestFunctions
open LimitTheorem
open WindowLimits
open LimitTheorem
open SeparatedTuples hiding conjugation
open ReflectionPositivity.TupleForm
open SpectralTheory
open CanonicalDecompositionUniqueness
private structure IdentificationInputs : Prop where
  identifications : CutoffRepresentatives.IdentificationsHold
section WindowLimit
variable {F : StatedSideFamily} {N : BoundConstants} (P : Inputs) (P' : IdentificationInputs) (B : BoundsHoldAt F N)
  (Q : WindowStates F) {σ : TupleFunctional}
include P B in
private theorem componentSymmetries_of_limit (hσ : Q.HasLimit σ) : _root_.YangMills.Construction.LimitTheorem.ComponentSymmetries σ := by
  have s := limitSymmetries_of_limit P Q hσ
  refine ⟨fun v => ?_, fun w' => ?_, fun M _ => s.reflectionPositive M, fun M _ => s.reflectionPositive M,
    s.isPermInvariant, isRegular_of_limit P B Q hσ⟩
  · have h := s.motion_invariant (LimitTheorem.shiftMotion v) ⟨1, fun x => by simp [LimitTheorem.shiftMotion]⟩
    have e : (LimitTheorem.shiftMotion v).toFun = SeparatedTuples.translate v := by
      funext x
      simp [Motions.RigidMotion.toFun, LimitTheorem.shiftMotion, SeparatedTuples.translate]
    rw [LimitTheorem.IsMotionInvariant, e] at h
    exact h
  · obtain ⟨r, hr, e⟩ := exists_rigidMotion_hyperoctahedral w'
    have h := s.motion_invariant r hr
    rw [LimitTheorem.IsMotionInvariant, e] at h
    exact h
end WindowLimit
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology InnerProductSpace
noncomputable section
namespace WindowLimits
open TestSpaces (SepTupleOfCard)
open HilbertSpaceBasics (IsPosSemidef)
open LimitTheorem
open SeparatedTuples hiding conjugation
open ReflectionPositivity.TupleForm
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass vacuum posTupleVec)
open TwoPoints.TestPlates
open TestFunctions (separatedPairsR4)
private theorem centredOfCumulants_two (S : CumulantFamily) (X : SepTupleOfCard 2) :
    TestSpaces.centredOfCumulants S ⟨2, X⟩ = S 2 le_rfl X := by apply _root_.YangMills.SharedProofs.p31970 <;> assumption
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace WindowLimits
open BoundsOnEverySide
open LimitTheorem
open SeparatedTuples hiding conjugation
open ReflectionPositivity.TupleForm
open TestSpaces (SepTupleOfCard)
open TupleLists (ofList toList)
open HilbertSpaceBasics (IsPosSemidef)
section WindowLimit
variable     
    {σ : TupleFunctional}
private def cumulantFamilyOf (σ : TupleFunctional) : CumulantFamily := fun _ _ X => connectedFn σ X
private theorem isDisjointlySupported_of_pair {f h : RealValued} (hm : [f, h] ∈ PairFunctions.sepPairs) :
    IsDisjointlySupported [f, h] :=
  (R4TupleForms.isDisjointlySupported_iff_mem_separatedAll EuclideanFunctionals.defaultMirrorData _).2
    (ReflectionPositivity.AxisMirror.Ambient.separatedN_subset_separatedAll _ _ 2 hm)
private theorem pair_of_isDisjointlySupported {f h : RealValued} (hs : IsDisjointlySupported [f, h]) :
    [f, h] ∈ PairFunctions.sepPairs := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1
    ((R4TupleForms.isDisjointlySupported_iff_mem_separatedAll EuclideanFunctionals.defaultMirrorData _).1 hs)
  exact ⟨rfl, hn.2⟩
private theorem isDisjointlySupported_swap {f h : RealValued} (hs : IsDisjointlySupported [f, h]) :
    IsDisjointlySupported [h, f] := by
  have d : Disjoint (tsupport f) (tsupport h) := by simpa using hs.2
  refine ⟨fun g hg => hs.1 g ?_, by simpa using d.symm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
  exact hg.symm
private theorem isBilinearOnPairs_of (hcomb : SeparatedTuples.BasicFacts.SeparatedOfLinearCombinationInOneEntry)
    {S : EuclideanFunctionals.ConnFamily} {τ : TupleFunctional} (hm : τ.IsEntrywiseLinear)
    (hv : ∀ (Y : PairFunctions.sepPairs) (Z : SepTuple), Z.1 = Y.1 → S.fn 2 le_rfl Y = τ Z) :
    PairFunctions.IsBilinearOnPairs (S.fn 2 le_rfl) := by
  intro b b' f f' h h₁ h₂
  have s₁ := isDisjointlySupported_of_pair h₁
  have s₂ := isDisjointlySupported_of_pair h₂
  have s₃ : IsDisjointlySupported [b • f + b' • f', h] := hcomb [] [h] f f' b b' s₁ s₂
  have t₁ := isDisjointlySupported_swap s₁
  have t₂ := isDisjointlySupported_swap s₂
  have t₃ := isDisjointlySupported_swap s₃
  have v : ∀ {g k : RealValued} (hs : IsDisjointlySupported [g, k]),
      PairFunctions.evalPair (S.fn 2 le_rfl) g k = τ ⟨[g, k], hs⟩ := fun hs =>
    (PairFunctions.evalPair_of_mem _ (pair_of_isDisjointlySupported hs)).trans (hv _ ⟨_, hs⟩ rfl)
  refine ⟨?_, ?_⟩
  · have e := hm [] [h] f f' b b' ⟨_, s₁⟩ ⟨_, s₂⟩ ⟨_, s₃⟩ rfl rfl rfl
    exact (v s₃).trans (e.trans (by rw [v s₁, v s₂]))
  · have e := hm [h] [] f f' b b' ⟨_, t₁⟩ ⟨_, t₂⟩ ⟨_, t₃⟩ rfl rfl rfl
    exact (v t₃).trans (e.trans (by rw [v t₁, v t₂]))
private def HasReflectedUpperBound (σ : TupleFunctional) : Prop :=
  ∀ S : EuclideanFunctionals.ConnFamily,
    (∀ (n : ℕ) (hn : 2 ≤ n) (X : SepTupleOfCard n),
      S.fn n hn (TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData n X) = connectedFn σ X) →
    ∃ (d₀ : ℝ) (u : ℝ → ℝ), TwoPoints.ReflectedUpperBound
      (PairFunctions.realPartForm (S.fn 2 le_rfl)) d₀ u
private theorem map_two_eq_centredOf {S : EuclideanFunctionals.ConnFamily}
    (hS : ∀ (n : ℕ) (hn : 2 ≤ n) (X : SepTupleOfCard n),
      S.fn n hn (TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData n X) = connectedFn σ X)
    (Y : PairFunctions.sepPairs) (Z : SepTuple) (e : Z.1 = Y.1) :
    S.fn 2 le_rfl Y = centredOf (cumulantFamilyOf σ) Z := by
  let X₂ := (TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData 2).symm Y
  have e₁ : TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData 2 X₂ = Y := Equiv.apply_symm_apply _ _
  have e₂ : toList ⟨2, X₂⟩ = Z := Subtype.ext ((congrArg Subtype.val e₁).trans e.symm)
  have e₃ : centredOf (cumulantFamilyOf σ) Z = connectedFn σ X₂ := by
    rw [← e₂]
    show evalOnMap (centredOf (cumulantFamilyOf σ)) ⟨2, X₂⟩ = _
    rw [evalOnMap_centredOf, centredOfCumulants_two]
    rfl
  rw [e₃, ← hS 2 le_rfl X₂, e₁]
private theorem onFunction_ofOrthogonalMatrix {α : Type*} (Rm : Matrix.orthogonalGroup (Fin 4) ℝ)
    (f : EuclideanFunctionals.R4 → α) :
    (EuclideanFunctionals.EuclidMotion.ofOrthogonalMatrix Rm).actFn f = TwoPoints.rotateFun Rm f := by
  funext x
  have hy : EuclideanFunctionals.EuclidMotion.ofOrthogonalMatrix Rm
      (((Rm⁻¹ : Matrix.orthogonalGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ).mulVec x) = x := by
    rw [EuclideanFunctionals.EuclidMotion.ofOrthogonalMatrix_apply, Matrix.mulVec_mulVec]
    have h1 : Rm.1 * ((Rm⁻¹ : Matrix.orthogonalGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) = 1 :=
      congrArg Subtype.val (mul_inv_cancel Rm)
    rw [h1, Matrix.one_mulVec]
  have h := EuclideanFunctionals.EuclidMotion.inv_apply_apply (EuclideanFunctionals.EuclidMotion.ofOrthogonalMatrix Rm)
    (((Rm⁻¹ : Matrix.orthogonalGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ).mulVec x)
  rw [hy] at h
  show f ((EuclideanFunctionals.EuclidMotion.ofOrthogonalMatrix Rm)⁻¹ x) = _
  rw [h]
  rfl
abbrev _root_.YangMills.SharedProofs.p36578 := @onFunction_ofOrthogonalMatrix
private theorem isEuclidIsometry_matMap (Qm : Orthogonal.orthogonalGroupFour) :
    IsEuclidIsometry (OrthogonalAction.matMap Qm) := by apply _root_.YangMills.Construction.OrthogonalAction.Laws.euclidDistR4_matMap <;> assumption
private theorem push_matMap_val (hF : SeparatedTuples.BasicFacts.IsometryActionOnTuples) (Qm : Orthogonal.orthogonalGroupFour)
    (X : SepTuple) : (push (OrthogonalAction.matMap Qm) X).1 =
      (EuclideanFunctionals.EuclidMotion.ofOrthogonalMatrix Qm).actList X.1 := by
  have hs := (hF _ (isEuclidIsometry_matMap Qm) X X).1
  have e : (push (OrthogonalAction.matMap Qm) X).1 = pushList (OrthogonalAction.matMap Qm) X.1 := by
    unfold push
    rw [dif_pos hs]
  rw [e]
  refine List.map_congr_left fun f _ => ?_
  rw [onFunction_ofOrthogonalMatrix]
  funext x
  have hinj : Function.Injective (OrthogonalAction.matMap Qm) := fun a b hab => by
    have h1 : ((Qm⁻¹ : Matrix.orthogonalGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) * Qm.1 = 1 :=
      congrArg Subtype.val (inv_mul_cancel Qm)
    have := congrArg (((Qm⁻¹ : Matrix.orthogonalGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ).mulVec) hab
    simpa [OrthogonalAction.matMap, Matrix.mulVec_mulVec, h1] using this
  have hy : OrthogonalAction.matMap Qm
      (((Qm⁻¹ : Matrix.orthogonalGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ).mulVec x) = x := by
    have h1 : Qm.1 * ((Qm⁻¹ : Matrix.orthogonalGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) = 1 :=
      congrArg Subtype.val (mul_inv_cancel Qm)
    simp [OrthogonalAction.matMap, Matrix.mulVec_mulVec, h1]
  show f (Function.invFun (OrthogonalAction.matMap Qm) x) = _
  conv_lhs => rw [← hy]
  rw [Function.leftInverse_invFun hinj]
  rfl
private theorem orthogonalMap_eq_matMap (Rm : Orthogonal.orthogonalGroupFour) :
    orthogonalMap Rm = OrthogonalAction.matMap Rm := by
  funext x
  simp [orthogonalMap, ofOrthogonal, Motions.RigidMotion.toFun, OrthogonalAction.matMap]
end WindowLimit
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open TestSpaces (SepTupleOfCard)
open TupleLists (ofList toList)
open HilbertSpaceBasics (IsPosSemidef)
open WindowLimits
open BoundsOnEverySide
open LimitTheorem
open SeparatedTuples hiding conjugation
open ReflectionPositivity.TupleForm
private structure RotationInputs : Prop where
  recursion : TestSpaces.CumulantRecursionTriangular
  centredRotation : FirstPassageSeqs.CenteredLimitRotation.Claim
  insertion : InsertionBoundsOfLimitWithConstants
  onePoint : OrthogonalAction.OnePointIrrelevance
  cone : RotationsAndCone.RotationsAndConeStatement
  translations : TranslationMeasureFromReconstruction
  os : ComponentConditions.OSFromConditionsStatement
  field : ExistsInsertionBoundOfFieldOperatorBound
section WindowLimit
variable {F : StatedSideFamily} {N : BoundConstants} (P : Inputs) (P' : IdentificationInputs) (R : RotationInputs)
  (B : BoundsHoldAt F N) (Q : WindowStates F) {σ : TupleFunctional}
private def WindowStates.selfCentred : WindowStates F :=
  { Q with ν := Q.ρ, ν_mem := Q.ρ_mem, ν_state := Q.ρ_state }
include R in
private theorem insertionBounds_of_limit (B : BoundsHoldAt F N) (hσ : Q.HasLimit σ) :
    InsertionBounds F.L F.M N σ := by
  let s : Conventions.StandingParameters := (unitAxisMirrorData F.admissible).toStandingParameters
  let K : ℕ → ℕ := fun j => (Q.K j.succPNat : ℕ)
  let β : ℕ → ℝ := fun j => Q.β j.succPNat
  let ρ : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ))) := fun j => Q.ρ j.succPNat
  let ν : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ))) := fun j => Q.ν j.succPNat
  let σm : R4TupleForms.FinTuple s → ℝ := fun X => σ (R4TupleForms.finTupleEquiv s X)
  have hcut : Tendsto K atTop atTop := (tendsto_cutoff_coe Q).comp tendsto_succPNat_atTop
  have hlim : IsPeriodicStateLimit K β ρ ν σm := by
    refine ⟨fun j => (Q.K j.succPNat).pos, ⟨hcut, fun j => Q.ρ_mem _, fun j => Q.ν_mem _⟩, fun X => ?_⟩
    have h := (hσ (Continuum.SeparatedFourTuples.sepTupleEquiv s X)).comp tendsto_succPNat_atTop
    exact h
  obtain ⟨hS, -, -, -, ⟨hf, hb⟩, -⟩ := R.insertion F N B s K β ρ ν σm rfl hlim
    (fun j hj => Q.isFirstPassage j.succPNat) (fun j hj => Q.ρ_state j.succPNat)
    (fun j hj => Q.ν_state j.succPNat)
  have e : R4TupleForms.toTupleFunctional σm hf = σ := tupleFunctional_ext fun Y =>
    congrArg σ ((R4TupleForms.finTupleEquiv s).apply_symm_apply Y)
  rw [e] at hb
  exact hb
include P R in
private theorem exists_connFamily (hσ : Q.HasLimit σ) :
    ∃ S : EuclideanFunctionals.ConnFamily, ∀ (n : ℕ) (hn : 2 ≤ n) (X : SepTupleOfCard n),
      S.fn n hn (TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData n X) = connectedFn σ X := by
  have hs := isSepFunctional_of_limit P Q hσ
  have hex := (R.recursion.2.2.2 (evalOnMap σ) hs).1
  obtain ⟨S, hS⟩ : ∃ S : EuclideanFunctionals.ConnFamily, ∀ (n : ℕ) (hn : 2 ≤ n)
      (X : TestSpaces.SepTupleOfCard n),
      S.fn n hn (TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData n X) =
        TestSpaces.cumulantRec (evalOnMap σ) n X := by
    refine ⟨⟨fun n _ Y => TestSpaces.cumulantRec (evalOnMap σ) n
      ((TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData n).symm Y), fun n hn => ?_⟩, fun n hn X => ?_⟩
    · exact ((R.recursion.2.2.1.1 n (by omega) _ (standingParamsOfFamily F)
        (TestSpaces.cumulantRec (evalOnMap σ) n)).1).1 (hex n (by omega)).2.2.2
    · show TestSpaces.cumulantRec (evalOnMap σ) n
        ((TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData n).symm
          (TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData n X)) = _
      rw [Equiv.symm_apply_apply]
  exact ⟨S, fun n hn X => (hS n hn X).trans ((hex n (by omega)).2.1 X)⟩
include P P' R in
private theorem connFamily_orthogonalInvariant (B : BoundsHoldAt F N) (hσ : Q.HasLimit σ) (hU : HasReflectedUpperBound σ)
    {S : EuclideanFunctionals.ConnFamily}
    (hS : ∀ (n : ℕ) (hn : 2 ≤ n) (X : SepTupleOfCard n),
      S.fn n hn (TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData n X) = connectedFn σ X) :
    EuclideanFunctionals.TwoPointRotationCriterion.OrthogonalInvariantConnected S := by
  have hL := F.admissible
  obtain ⟨hA, -⟩ := P.inheritance.1 F.L F.admissible F.M 0 Q.K Q.ρ Q.ν σ (fun j => (Q.ρ_mem j).1.1) hσ
  obtain ⟨-, h2, -⟩ := P'.identifications F.L hL Q.K Q.ρ (fun j => (Q.ρ_mem j).1.1) (cumulantFamilyOf σ)
  have hσc : Q.selfCentred.HasLimit (centredOf (cumulantFamilyOf σ)) :=
    h2.1 fun n hn X => hA.2 n hn X
  have A₀ := P.limit.approximation Q.selfCentred
  have hb := latticeApprox_isBounded hL P.bounded A₀ hσc
  have hl := convergesTo_latticeApprox A₀ hσc
  have hτ : (centredOf (cumulantFamilyOf σ)).toFun =
      FirstPassageSeqs.onSepTuples (EuclideanFunctionals.centeredFn S) := by
    funext X
    have e₁ := (R.recursion.2.1.1 S).1 (ofList X).1 (ofList X).2
    have e₂ : TestSpaces.connFamilyOnTuples S = cumulantFamilyOf σ := by
      funext m hm Y
      exact hS m hm Y
    rw [e₂] at e₁
    have e₃ : TestSpaces.centredOfConnFamily S ⟨(ofList X).1, (ofList X).2⟩ =
        FirstPassageSeqs.onSepTuples (EuclideanFunctionals.centeredFn S) X := by
      unfold TestSpaces.centredOfConnFamily FirstPassageSeqs.onSepTuples
      exact congrArg (EuclideanFunctionals.centeredFn S) (Subtype.ext (List.ofFn_get X.1))
    exact e₁.symm.trans e₃
  let c : EuclideanFunctionals.SharpScale := ⟨F.M, F.one_le_M⟩
  have hsup : ∀ f : EuclideanFunctionals.R4 → ℝ, tsupport f = EuclideanFunctionals.supp f := fun f =>
    (SeparationR4.closedSupport_euclidean_eq_tsupport EuclideanFunctionals.defaultMirrorData f).symm
  have hper := (P.limit.limit_conditions Q hσ).perBall _ B (unitBallBound F.M N) (clusteringConstOf F.M N) clusteringRadiusOf
    ⟨0, fun _ => 0⟩
  have hloc : EuclideanFunctionals.HasClusterBounds S c (fun n d R => N.cumulantBound n d R) := by
    intro n hn Rr d hR hd f hf hball hsep
    let Y := (TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData n).symm ⟨List.ofFn f, hf⟩
    have e₁ : TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData n Y = ⟨List.ofFn f, hf⟩ :=
      Equiv.apply_symm_apply _ _
    have eY : Y.1 = f := List.ofFn_injective (congrArg Subtype.val e₁)
    have h₁ := (hper n hn Rr hR d hd Y (fun i => ?_) (fun i l hil => ?_)).1
    · rw [← e₁, hS n hn Y]
      have e₂ : ∏ i, c.sharpNorm (f i) = ∏ i, TestFunctions.sharpNormR4 F.M (Y.1 i) := by
        rw [eY]
        rfl
      rw [e₂]
      exact h₁
    · rw [eY, hsup]
      exact hball i
    · rw [eY, hsup, hsup]
      exact hsep hil
  have hN := B.admissible_constants
  have hprem : FirstPassageSeqs.CenteredLimitRotation.TwoPointHypotheses S
      (fun n d R => N.cumulantBound n d R) :=
    ⟨isBilinearOnPairs_of P.tupleFacts.2.1 (limitSymmetries_of_limit P Q.selfCentred hσc).isEntrywiseLinear (map_two_eq_centredOf hS),
      fun d R _ hR => (BoundConstants.cumulantBound_pos hN 2 d hR).le,
      fun d d' R hd hle hR => BoundConstants.cumulantBound_antitone hN 2 hd hle hR, hU S hS⟩
  have hslab := (insertionBounds_of_limit R Q.selfCentred B hσc).freeSlab
  exact (R.centredRotation (unitAxisMirrorData hL) _ S _ hτ hb A₀.isReflPos (hτ ▸ hl) c _ hloc hprem
    (centredOf (cumulantFamilyOf σ)) (fieldExponent N)
    (freeSlabConst F.L F.M N) Insertion.ballRadiusRatio
    (by unfold fieldExponent; linarith [hN.insertionExponent_nonneg]) (by norm_num [Insertion.ballRadiusRatio])
    (by norm_num [Insertion.ballRadiusRatio]) (fun X => congrFun hτ X)
    (fun η hη h₁ y hy k hk hks F F' => hslab η hη h₁ y hy k hk hks F F')).1
include P P' R in
private theorem isInvariant_matMap_of_limit (B : BoundsHoldAt F N) (hσ : Q.HasLimit σ) (hU : HasReflectedUpperBound σ)
    (Qm : Orthogonal.orthogonalGroupFour) : σ.IsInvariant (OrthogonalAction.matMap Qm) := by
  obtain ⟨S, hS⟩ := exists_connFamily P R Q hσ
  have hV := connFamily_orthogonalInvariant P P' R Q B hσ hU hS
  have hs := isSepFunctional_of_limit P Q hσ
  have hex := (R.recursion.2.2.2 (evalOnMap σ) hs).1
  have hrec : ∀ T : SepTuple, 1 ≤ T.1.length →
      OrthogonalAction.cumulantAt σ T = connectedFn σ (ofList T).2 := fun T hT => (hex _ hT).2.1 _
  have hval : ∀ (T : SepTuple) (n : ℕ) (hn : 2 ≤ n), T.1.length = n →
      connectedFn σ (ofList T).2 = ReflectionPositivity.AxisMirror.Ambient.evalOrZero (S.fn n hn) T.1 := by
    rintro T _ hn rfl
    have hm : T.1 ∈ EuclideanFunctionals.sepN T.1.length := by
      have h := (TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData T.1.length (ofList T).2).2
      have e : (TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData T.1.length (ofList T).2).1 = T.1 :=
        List.ofFn_get T.1
      rwa [e] at h
    have e : TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData T.1.length (ofList T).2 = ⟨T.1, hm⟩ :=
      Subtype.ext (List.ofFn_get T.1)
    have e₄ : ReflectionPositivity.AxisMirror.Ambient.evalOrZero (S.fn _ hn) T.1 = S.fn _ hn ⟨T.1, hm⟩ := by
      unfold ReflectionPositivity.AxisMirror.Ambient.evalOrZero
      exact dif_pos hm
    exact (hS _ hn (ofList T).2).symm.trans ((congrArg (S.fn _ hn) e).trans e₄.symm)
  obtain ⟨c, hc⟩ := (P.limit.limit_conditions Q hσ).onePoint_eq
  refine (R.onePoint σ Qm).2 ⟨c, fun f hf => ?_⟩ fun X hX => ?_
  · have hf' : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) := ⟨hf.1, hf.2, Set.subset_univ _⟩
    have eT : OrthogonalAction.singletonTuple f hf = toList ⟨1, TestSpaces.singletonSepTuple f hf'⟩ :=
      Subtype.ext (by simp [OrthogonalAction.singletonTuple, toList, TestSpaces.singletonSepTuple])
    have e₀ : connectedFn σ (ofList (OrthogonalAction.singletonTuple f hf)).2 =
        connectedFn σ (TestSpaces.singletonSepTuple f hf') := by
      rw [eT]
      exact congrArg (fun Y : TestSpaces.SepTuple => connectedFn σ Y.2) (TupleLists.ofList_toList _)
    have e₁ : σ (OrthogonalAction.singletonTuple f hf) = evalOnMap σ ⟨1, TestSpaces.singletonSepTuple f hf'⟩ :=
      congrArg σ eT
    refine ⟨?_, ?_⟩
    · rw [hrec _ (by simp [OrthogonalAction.singletonTuple]), e₀, e₁]
      exact TestSpaces.cumulant_single _ _
    · rw [e₁]
      exact hc _
  · have hmem : X.1 ∈ EuclideanFunctionals.sepN X.1.length := by
      have h := (TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData X.1.length (ofList X).2).2
      have e : (TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData X.1.length (ofList X).2).1 = X.1 :=
        List.ofFn_get X.1
      rwa [e] at h
    have e₁ := push_matMap_val P.tupleFacts.1 Qm X
    have hlen : (push (OrthogonalAction.matMap Qm) X).1.length = X.1.length := by
      rw [e₁]
      simp [EuclideanFunctionals.EuclidMotion.actList]
    have hn : 2 ≤ X.1.length := hX
    rw [hrec _ (by omega), hrec _ (by omega), hval _ _ hn hlen, hval _ _ hn rfl, e₁]
    exact hV _ hn Qm _ hmem
include P P' R in
private theorem isO4InvariantFunctional_of_limit (B : BoundsHoldAt F N) (hσ : Q.HasLimit σ)
    (hU : HasReflectedUpperBound σ) : IsO4InvariantFunctional σ := fun Rm => by
  rw [orthogonalMap_eq_matMap]
  exact isInvariant_matMap_of_limit P P' R Q B hσ hU Rm
include P P' R in
private theorem forwardCone_of_limit (B : BoundsHoldAt F N) (hσ : Q.HasLimit σ) (hU : HasReflectedUpperBound σ) :
    ∃ h : IsPosSemidef (reflectionForm σ), JointSpectrumInForwardCone σ ∧ HasSpatialRotationRep σ ∧
      ReflectionPositivity.ReconstructionComplements.SupportClaim σ h ∧
      ReflectionPositivity.ReconstructionComplements.jointMeasure σ h
        ⟨RotationsAndCone.spacelikeRegion,
          RotationsAndCone.isOpen_spacelikeRegion.measurableSet⟩ = 0 := by
  have hL := F.admissible
  have A₀ := P.limit.approximation Q
  have hl := convergesTo_latticeApprox A₀ hσ
  have hb := latticeApprox_isBounded hL P.bounded A₀ hσ
  obtain ⟨h, hMe, hOp, hCa, hMa, -⟩ := P.complements.2 (unitAxisMirrorData hL) _ σ hb A₀.isReflPos hl
  have s := limitSymmetries_of_limit P Q hσ
  have hlist := reconstructionProperties_of_limit P Q hσ
  have hfour : Continuum.RotationModulus.RotationHypotheses F.M σ
      (fun k d R => |momentWeight N k d R|) := by
    refine ⟨s.isEntrywiseLinear, s.isPermInvariant, s.reflectionPositive _, fun _ _ _ _ _ _ => abs_nonneg _,
      fun k _ d R hd hR X hk hball hsep => ?_, fun Rm => isInvariant_matMap_of_limit P P' R Q B hσ hU _⟩
    subst hk
    have hs : TestFunctions.HasSeparatedSupportsR4 (ofList X).2.1 d := by
      refine ⟨hd, fun i l hil => ?_⟩
      rcases lt_or_gt_of_ne hil with hlt | hlt
      · exact List.pairwise_iff_get.1 hsep i l hlt
      · rw [setDistR4_comm]
        exact List.pairwise_iff_get.1 hsep l i hlt
    have hv := abs_limitValue_le Q P.momentCumulant P.observables B hσ (ofList X).2 hd hR
      (fun i => hball _ (List.get_mem _ _)) hs
    have e₁ : ∏ i, TestFunctions.sharpNormR4 F.M ((ofList X).2.1 i) =
        (X.1.map (TestFunctions.sharpNormR4 F.M)).prod := Fin.prod_univ_fun_getElem _ _
    have e₂ : evalOnMap σ ⟨(ofList X).1, (ofList X).2⟩ = σ X := evalOnMap_ofList σ X
    rw [e₁, e₂] at hv
    refine hv.trans (mul_le_mul_of_nonneg_right (le_abs_self _) ?_)
    rw [← e₁]
    exact Finset.prod_nonneg fun _ _ => sharpNormR4_nonneg _ _
  have hR := hasReconstruction_of_properties hlist h
  obtain ⟨h₁, h₂, h₃⟩ := R.cone _ σ _ h ⟨F.one_le_M, hfour, hR, hMe, hOp, hMa⟩
  exact ⟨h, h₁, h₂, hCa, h₃⟩
include P P' R in
private theorem componentOS_of_extremal (B : BoundsHoldAt F N) (hσ : Q.HasLimit σ)
    (hpure : ∀ j, Q.ρ j ∈ cutoffExtremalSet F.L (Q.K j) (Q.β j)) (hU : HasReflectedUpperBound σ)
    (E : LawConstants) (hc₁ : 0 ≤ ((existentialConstants F.M N).toConditionConstants E).cE)
    (hc₂ : 0 ≤ ((existentialConstants F.M N).toConditionConstants E).CE) :
    (∀ T, HasSchwingerSequence σ T → SatisfiesAxiomLists ((existentialConstants F.M N).toConditionConstants E) T) ∧
      ComponentFieldData σ := by
  obtain ⟨h, -, -, hCa, hz⟩ := forwardCone_of_limit P P' R Q B hσ hU
  have hf := isSepFunctional_of_limit P Q hσ
  have hlist := reconstructionProperties_of_limit P Q hσ
  obtain ⟨hpos, hmeas⟩ := R.translations σ h hf (hasReconstruction_of_properties hlist h) hCa hz
  have hsym := componentSymmetries_of_limit P B Q hσ
  have hrot := isO4InvariantFunctional_of_limit P P' R Q B hσ hU
  have hcluster : ComponentConditions.ClustersAtInfinity σ := fun X Y =>
    ⟨clusteringConstOf F.M N X Y, clusteringRadiusOf X Y, fun v hv =>
      clustering_of_extremal P B Q hσ hpure X Y v hv⟩
  have hgrowth : GrowthBound ((existentialConstants F.M N).toConditionConstants E) σ :=
    growthBound_of_limit P B Q hσ _ _ E
  exact ⟨R.os _ σ hc₁ hc₂ h hf hsym.shift_invariant hrot hsym.permInvariant hgrowth hcluster,
    _, hc₁, hc₂, h, hf, hsym.shift_invariant, hrot, hsym.permInvariant, hgrowth, hpos, hmeas,
    R.field F.L F.M N σ B.admissible_constants hpos (insertionBounds_of_limit R Q B hσ).fieldOperator,
    hcluster⟩
end WindowLimit
private structure RotationConditionsWithConstants (M : ℝ) (N : BoundConstants) (S : CumulantFamily) : Prop where
  o4Invariant : IsO4Invariant S
  permute : ∀ A' : DecompositionData, A'.IsCanonical (centredOf S) →
    NonLatticeRotationsPermute A'
  componentsInvariant : ∀ A' : DecompositionData, A'.IsCanonical (centredOf S) →
    ∀ ξ, IsO4InvariantFunctional (A'.comp ξ)
  jointSpectrum : ∀ A' : DecompositionData, A'.IsCanonical (centredOf S) →
    ∀ ξ, JointSpectrumInForwardCone (A'.comp ξ)
  spatialRotations : ∀ A' : DecompositionData, A'.IsCanonical (centredOf S) →
    ∀ ξ, HasSpatialRotationRep (A'.comp ξ)
  componentOS : ∀ E, ∀ A' : DecompositionData, A'.IsCanonical (centredOf S) →
    ∀ ξ, (∀ T, HasSchwingerSequence (A'.comp ξ) T →
      SatisfiesAxiomLists ((existentialConstants M N).toConditionConstants E) T) ∧ ComponentFieldData (A'.comp ξ)
section CentredLimit
variable {F : StatedSideFamily} {N : BoundConstants} (P : Inputs) (P' : IdentificationInputs) (R : RotationInputs)
  (B : BoundsHoldAt F N) {Q : WindowStates F} {S : CumulantFamily}
include P P' R B in
private theorem rotationPropertiesWithConstants_of (hS : CutoffRepresentatives.CentredSymmetriesAndCumulants S)
    (hρν : Q.ρ = Q.ν) (hvol : ∀ j, IsInfiniteVolumeLimit F.L (Q.K j) (Q.β j) (Q.ν j)) (hσ : Q.HasLimit (centredOf S))
    (hU : ∀ (Q' : WindowStates F) (τ : TupleFunctional), Q'.HasLimit τ → HasReflectedUpperBound τ)
    (hc₁ : 0 ≤ (existentialConstants F.M N).cE) (hc₂ : 0 ≤ (existentialConstants F.M N).CE) :
    RotationConditionsWithConstants F.M N S := by
  have hcomp := fun (A' : DecompositionData) (hA : A'.IsCanonical (centredOf S)) ξ =>
    exists_windowStates_of_component P B hρν hvol hσ hA ξ
  have hrot := isO4InvariantFunctional_of_limit P P' R Q B hσ (hU Q _ hσ)
  refine ⟨fun Rm => (hS.2.1 (ofOrthogonal Rm)).1 (hrot Rm), fun A' hA Rm _ => ?_, fun A' hA ξ => ?_,
    fun A' hA ξ => ?_, fun A' hA ξ => ?_, fun E A' hA ξ => ?_⟩
  · have hi : IsEuclidIsometry (orthogonalMap Rm) := by
      rw [orthogonalMap_eq_matMap]
      exact isEuclidIsometry_matMap Rm
    obtain ⟨-, k, hk, -, hom, hm⟩ := (P.determination (centredOf S)).2.2.1 A' hA (orthogonalMap Rm) hi (hrot Rm)
    exact ⟨hom.homeomorph k, hm, fun ξ => hk ξ⟩
  · obtain ⟨Q', hl, -⟩ := hcomp A' hA ξ
    exact isO4InvariantFunctional_of_limit P P' R Q' B hl (hU Q' _ hl)
  · obtain ⟨Q', hl, -⟩ := hcomp A' hA ξ
    obtain ⟨-, h₁, -, -, -⟩ := forwardCone_of_limit P P' R Q' B hl (hU Q' _ hl)
    exact h₁
  · obtain ⟨Q', hl, -⟩ := hcomp A' hA ξ
    obtain ⟨-, -, h₂, -, -⟩ := forwardCone_of_limit P P' R Q' B hl (hU Q' _ hl)
    exact h₂
  · obtain ⟨Q', hl, hp⟩ := hcomp A' hA ξ
    exact componentOS_of_extremal P P' R Q' B hl hp (hU Q' _ hl) E hc₁ hc₂
end CentredLimit
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily)
open WindowLimits
open LimitTheorem
open SeparatedTuples hiding conjugation
section SideFamilySequences
variable {F : StatedSideFamily}
private def windowStatesOfSequence (Q : ApproximatingSequence F) : WindowStates F where
  K := Q.cutoff
  tendsto_K := tendsto_atTop.2 fun b => (tendsto_atTop.1 Q.tendsto_cutoff (b : ℕ)).mono fun _ hj =>
    PNat.coe_le_coe _ _ |>.1 hj
  β := Q.coupling
  isFirstPassage := Q.isDatum
  ρ := Q.state
  ν := Q.state
  ρ_mem := Q.mem_gibbs
  ν_mem := Q.mem_gibbs
  ρ_state j := F.volumeLimits_mem _ _ (Q.isDatum j) _ (Q.isLimit j)
  ν_state j := F.volumeLimits_mem _ _ (Q.isDatum j) _ (Q.isLimit j)
variable (P' : IdentificationInputs)
include P' in
private theorem hasLimit_of_sequence {Q : ApproximatingSequence F} {S : CumulantFamily} (hQ : Q.Defines S) :
    CutoffRepresentatives.CentredSymmetriesAndCumulants S ∧
      (windowStatesOfSequence Q).HasLimit (centredOf S) := by
  obtain ⟨-, h2, h3⟩ := P'.identifications F.L F.admissible Q.cutoff Q.state (fun j => (Q.mem_gibbs j).1.1) S
  exact ⟨h3, h2.1 hQ⟩
end SideFamilySequences
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily)
open TestSpaces (SepTupleOfCard)
open WindowLimits
open LimitTheorem
open SeparatedTuples hiding conjugation
open TestFunctions (separatedPairsR4 inverseEighthKernel)
private theorem twoPointFactor_pos : 0 < twoPointFactor := by
  unfold twoPointFactor
  have := Real.pi_pos
  positivity
private def reflectedBound (d : ℝ) : ℝ :=
  3 / 2 * (4 / 3) ^ 4 * (twoPointFactor * TestPairs.kernelUpperConst) / Real.log (1 / d) ^ 2
private theorem reflectedBound_pos {d : ℝ} (hd : 0 < d) (h1 : d < 1) : 0 < reflectedBound d := by
  have hl : 0 < Real.log (1 / d) := Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hd).2 h1)
  have hc : 0 < TestPairs.kernelUpperConst := by
    unfold TestPairs.kernelUpperConst
    have := Real.pi_pos
    positivity
  have := twoPointFactor_pos
  unfold reflectedBound
  positivity
private theorem tendsto_reflectedBound : Tendsto reflectedBound (𝓝[>] 0) (𝓝 0) := by
  have h₁ : Tendsto (fun d : ℝ => |Real.log d|) (𝓝[>] 0) atTop :=
    tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h₂ : Tendsto (fun d : ℝ => |Real.log d| ^ 2) (𝓝[>] 0) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp h₁
  refine (h₂.const_div_atTop (3 / 2 * (4 / 3) ^ 4 * (twoPointFactor * TestPairs.kernelUpperConst))).congr fun d => ?_
  simp [reflectedBound, one_div, Real.log_inv, sq_abs]
private theorem hasReflectedUpperBound_of_law (hG : TestPairs.GeometryAndKernelBounds) (P : Inputs)
    (hSmaller : TwoPoints.SmallerShape.Statement) {F : StatedSideFamily} {N : BoundConstants} {ϑ : ℝ}
    (hN : N.Admissible) (hT : TwoPointLawAt F N ϑ) (hϑ : ϑ ∈ Ioc (0 : ℝ) 1)
    (hshape : ϑ ≤ TwoPoints.Shapes.shapeConst) (Q : WindowStates F) {τ : TupleFunctional}
    (hτ : Q.HasLimit τ) : HasReflectedUpperBound τ := by
  intro S hS
  have hd₀ := hN.lawScale_mem
  have hlaw := twoPointLaw_of_limit P Q hT hτ (existentialConstants 1 N)
  refine ⟨N.lawScale, reflectedBound, ⟨hd₀.1, fun d hd => reflectedBound_pos hd.1 (hd.2.trans_lt hd₀.2),
    tendsto_reflectedBound, ?_⟩⟩
  rintro ϖ hϖ hle h ⟨⟨⟨p₁, p₂⟩, hp, h₁, h₂⟩, hm₁, hh, hsup⟩
  simp only at h₁ h₂
  subst h₂
  have hd : 0 < 5 / 2 * ϖ := by positivity
  have hd1 : 5 / 2 * ϖ < 1 := hle.trans_lt hd₀.2
  have hcls : (p₁, p₂) ∈ separatedPairsR4 (5 / 2 * ϖ) ϑ := (hSmaller ϑ hϑ.1 hshape).1 _ hd hp
  have cre : ∀ p : AmbientSpace → ℝ, TwoPoints.ofRealFun p ∈ TwoPoints.compactC1Real → ContDiff ℝ 1 p := fun p hq => by
    have e : p = fun x => (TwoPoints.ofRealFun p x).re := by
      funext x
      simp [TwoPoints.ofRealFun]
    rw [e]
    exact Complex.reCLM.contDiff.comp hq.1.1
  have hc₁ := cre p₁ (h₁ ▸ hm₁)
  have hc₂ := cre p₂ hh
  obtain ⟨X, hX, η, hv, -, hup⟩ := hlaw _ ⟨hd, hle⟩ p₁ p₂ hcls hc₁ hc₂
  let Y := TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData 2 X
  have hY : Y.1 = [p₁, p₂] := by
    show List.ofFn X.1 = _
    rw [hX]
    simp [List.ofFn_succ]
  have hmem : [p₁, p₂] ∈ PairFunctions.sepPairs := hY ▸ Y.2
  have eY : Y = ⟨[p₁, p₂], hmem⟩ := Subtype.ext hY
  have eform : PairFunctions.realPartForm (S.fn 2 le_rfl) (TwoPoints.reflectFun (PeriodicLattice.coordVec 3)
      (TwoPoints.ofRealFun p₂)) (TwoPoints.ofRealFun p₂) = connectedFn τ X := by
    rw [← h₁]
    refine (PairFunctions.realPartForm_ofRealFun _ p₁ p₂).trans ?_
    refine (PairFunctions.evalPair_of_mem _ hmem).trans ?_
    exact (congrArg (S.fn 2 le_rfl) eY.symm).trans (hS 2 le_rfl X)
  rw [eform, hv]
  have hp' := hcls
  simp only [separatedPairsR4, TestFunctions.separatedPairs, Set.mem_ofPred_eq] at hp'
  obtain ⟨x₁, x₂, b₁, b₂, s₁, s₂⟩ := hp'
  have hcent : TestFunctions.IsCentrePairR4 (5 / 2 * ϖ) ϑ x₁ x₂ (p₁, p₂) :=
    ⟨⟨b₁.2.2.2.1, b₁.2.2.2.2.1, b₁.2.2.2.2.2⟩, ⟨b₂.2.2.2.1, b₂.2.2.2.2.1, b₂.2.2.2.2.2⟩, s₁, s₂⟩
  obtain ⟨-, -, -, -, hchain⟩ := (hG.1 _ _ ⟨hd, hϑ⟩ x₁ x₂ p₁ p₂ hcls hcent).1
  have hK₀ : 0 ≤ inverseEighthKernel p₁ p₂ := by
    have hs₁ : 0 ≤ TestFunctions.uniformNorm p₁ := Real.iSup_nonneg fun _ => norm_nonneg _
    have hs₂ : 0 ≤ TestFunctions.uniformNorm p₂ := Real.iSup_nonneg fun _ => norm_nonneg _
    have hf : 0 ≤ TestPairs.kernelLowerConst * ϑ ^ 2 * TestFunctions.uniformNorm p₁ *
        TestFunctions.uniformNorm p₂ := by
      unfold TestPairs.kernelLowerConst
      have := hϑ.1
      positivity
    exact hf.trans (hchain.1.trans hchain.2.1)
  have hK₁ := hchain.2.2.1.trans hchain.2.2.2
  have e₁ : TestFunctions.uniformNorm (TwoPoints.ofRealFun p₁) = TestFunctions.uniformNorm p₁ := by
    simp [TestFunctions.uniformNorm, TwoPoints.ofRealFun]
  have e₂ : TestFunctions.uniformNorm (TwoPoints.ofRealFun p₂) = TestFunctions.uniformNorm p₂ := by
    simp [TestFunctions.uniformNorm, TwoPoints.ofRealFun]
  have e₃ : TestFunctions.uniformNorm p₁ = TestFunctions.uniformNorm p₂ := by
    rw [← e₁, ← e₂, h₁]
    exact hsup
  rw [e₂]
  rw [e₃] at hK₁
  have hη := hN.lawError_mem _ ⟨hd, hle⟩
  have hl : 0 < Real.log (1 / (5 / 2 * ϖ)) ^ 2 := by
    have : 0 < Real.log (1 / (5 / 2 * ϖ)) := Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hd).2 hd1)
    positivity
  have hup' : 1 + η ≤ 3 / 2 * (4 / 3) ^ 4 := by
    refine hup.trans ?_
    have h₃ : (1 + N.lawError (5 / 2 * ϖ)) ^ 4 ≤ (4 / 3 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by linarith [hη.1]) (by linarith [hη.2]) 4
    show 3 / 2 * (1 + N.lawError (5 / 2 * ϖ)) ^ 4 ≤ _
    linarith
  have hlf := twoPointFactor_pos
  have ha : 0 ≤ twoPointFactor * inverseEighthKernel p₁ p₂ / Real.log (1 / (5 / 2 * ϖ)) ^ 2 := by positivity
  calc twoPointFactor * inverseEighthKernel p₁ p₂ / Real.log (1 / (5 / 2 * ϖ)) ^ 2 * (1 + η)
      ≤ twoPointFactor * inverseEighthKernel p₁ p₂ / Real.log (1 / (5 / 2 * ϖ)) ^ 2 * (3 / 2 * (4 / 3) ^ 4) :=
        mul_le_mul_of_nonneg_left hup' ha
    _ ≤ twoPointFactor * (TestPairs.kernelUpperConst * TestFunctions.uniformNorm p₂ * TestFunctions.uniformNorm p₂) /
          Real.log (1 / (5 / 2 * ϖ)) ^ 2 * (3 / 2 * (4 / 3) ^ 4) := by
        refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hK₁ hlf.le) hl.le
    _ = reflectedBound (5 / 2 * ϖ) * TestFunctions.uniformNorm p₂ * TestFunctions.uniformNorm p₂ := by
        unfold reflectedBound
        ring
private theorem componentOSAt_of {K : ExistentialConstants} {E : LawConstants} {σ : TupleFunctional}
    (h : (∀ T, HasSchwingerSequence σ T → SatisfiesAxiomLists (K.toConditionConstants E) T) ∧
      ComponentFieldData σ) : ComponentOSAt K σ := by
  refine ⟨fun T hT => ?_, h.2⟩
  obtain ⟨⟨g, i, rp, sy, cl, re⟩, gr⟩ := h.1 T hT
  exact ⟨⟨g, i, rp, sy, cl, re⟩, gr⟩
private theorem rotationPropertiesAt_existentialConstants (hG : TestPairs.GeometryAndKernelBounds) (P : Inputs)
    (P' : IdentificationInputs) (R : RotationInputs) (hSmaller : TwoPoints.SmallerShape.Statement) (M : ℝ)
    (N : BoundConstants) (hK : (existentialConstants M N).SideConditions) :
    RotationConditionsAt M N (existentialConstants M N) := by
  rintro F rfl B ϑ hϑ hshape hT Q S hQ
  obtain ⟨h3, hσ⟩ := hasLimit_of_sequence P' hQ
  have cl := rotationPropertiesWithConstants_of P P' R B h3 rfl Q.isLimit hσ
    (fun Q' _ hl => hasReflectedUpperBound_of_law hG P hSmaller B.admissible_constants hT hϑ hshape Q' hl)
    hK.cE_pos.le hK.CE_pos.le
  exact ⟨cl.o4Invariant, cl.permute, cl.componentsInvariant, cl.jointSpectrum, cl.spatialRotations,
    fun A' hA ξ => componentOSAt_of (cl.componentOS ⟨0, fun _ => 0⟩ A' hA ξ)⟩
end SystemsWithFiveBounds
end
end
noncomputable section
namespace SystemsWithFiveBounds
theorem rotationPropertiesAtExistentialConstants_of_inputs
    (h1 : SystemsWithFiveBounds.WindowLimitProperties)
    (h2 : SystemsWithFiveBounds.CanonicalDecompositionOfLimits)
    (h3 : PeriodicGibbsLimits.ObservablesAndMomentsDefined.Statement)
    (h4 : Cumulants.MomentCumulantFormula.Claim)
    (h5 : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (h6 : ReflectionPositivity.ReconstructionComplements.ComplementsTheorem)
    (h7 : SeparatedTuples.BasicFacts.MainFacts)
    (h8 : SystemsWithFiveBounds.GibbsLimitInheritance.InheritanceTheorem)
    (h9 : Continuum.TwoPresentations.PresentationsAgree)
    (h10 : TestSpaces.OffDiagonal.OffDiagonalFacts)
    (h11 : CanonicalDecompositionUniqueness.DecompositionDeterminations)
    (h12 : LimitTheorem.CutoffRepresentatives.IdentificationsHold)
    (h13 : TestSpaces.CumulantRecursionTriangular)
    (h14 : FirstPassageSeqs.CenteredLimitRotation.Claim)
    (h15 : SystemsWithFiveBounds.InsertionBoundsOfLimitWithConstants)
    (h16 : OrthogonalAction.OnePointIrrelevance)
    (h17 : LimitTheorem.RotationsAndCone.RotationsAndConeStatement)
    (h18 : LimitTheorem.TranslationMeasureFromReconstruction)
    (h19 : LimitTheorem.ComponentConditions.OSFromConditionsStatement)
    (h20 : SystemsWithFiveBounds.ExistsInsertionBoundOfFieldOperatorBound)
    (h21 : TestPairs.GeometryAndKernelBounds)
    (h22 : TwoPoints.SmallerShape.Statement) :
    RotationConditionsAtExistentialConstants :=
  have P : Inputs := { observables := smearedObservablesWellDefined_of h3, momentCumulant := h4, bounded := h5, complements := h6, tupleFacts := h7, inheritance := h8, presentations := h9, offDiagonal := h10, determination := h11, limit := h1, decomposition := h2 }
  have P' : IdentificationInputs := { identifications := h12 }
  have R : RotationInputs := { recursion := h13, centredRotation := h14, insertion := h15, onePoint := h16, cone := h17, translations := h18, os := h19, field := h20 }
  fun M N hK => rotationPropertiesAt_existentialConstants h21 P P' R h22 M N hK
end SystemsWithFiveBounds
end
end YangMills.Construction
