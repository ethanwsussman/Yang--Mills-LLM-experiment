import YangMills.Construction.Continuum.TheRecursionOfTheConnectedFunctionsIsTriangularProof
import YangMills.Construction.QuaternionicWilsonModel.WhatTheTopGivesAtEveryCouplingProof
import YangMills.Construction.Continuum.DistributionsOffTheDiagonalsAndTranslationsInSpace
import YangMills.Construction.Continuum.OneSpaceOfTestFunctionsFlatTensorsAndTheDual
import YangMills.Construction.Continuum.PointsFunctionsFlatnessAndNormsInTheTwoPresentations
import YangMills.Construction.Continuum.RulesOfTheOrthogonalActionProof
import YangMills.Construction.LawThroughTheLevels.PairOfTheClassIsOfTestFunctions
import YangMills.Construction.LimitTheorem.FromOneCanonicalDecompositionToEvery
import YangMills.Construction.ReflectionPositivity.ContractionOfTheLimitOfALatticeApproximationProof
import YangMills.Construction.ReflectionPositivity.HamiltonianBoundsTheMomentaInTheLimit
import YangMills.Construction.SpectralTheory.GeneratorsOfUnitaryGroupsAndSemigroups
import YangMills.Construction.SystemsWithFiveBounds.CanonicalDecompositionAlongStatesProof
import YangMills.Construction.SystemsWithFiveBounds.ConditionsAtFixedConstants
import YangMills.Construction.TwoPoints.ElementaryFactsOfMirrorsAndPlatesProof
import YangMills.Construction.TwoPoints.EverySmallerShapeServes
import YangMills.Construction.TwoPoints.PartsOfATestPlate
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
section OfTheStates
variable {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (Q : CutoffCouplingSequence L)
variable {Q} {ρ ν : ∀ j, Measure (Q.Fields j)} {hρ : ∀ j, ρ j ∈ Q.gibbsStates j}
private theorem integral_representative_eq_pairedValue (A : StatesApproximation Q ρ ν hρ) (j : ℕ+)
    (X : SepTuple) :
    ∫ U, (Q.latticeApprox ρ ν hρ).latticeProduct (𝕜 := ℝ) j X.1 U ∂ρ j =
      Q.pairedValue ρ ν j (TupleLists.ofList X) := by
  unfold CutoffCouplingSequence.pairedValue
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  show (X.1.map fun f => LatticeApproximation.smearedField (Q.latticeApprox ρ ν hρ) j f U).prod =
    ∏ i : Fin X.1.length, (smearedEnergy (X.1.get i) U - ∫ V, smearedEnergy (X.1.get i) V ∂ν j)
  rw [← Fin.prod_univ_fun_getElem]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hmem : X.1.get i ∈ X.1 := List.get_mem _ _
  obtain ⟨h₁, h₂⟩ := X.2.1 _ hmem
  have hc : Continuous (X.1.get i) := ContDiff.continuous (n := 1) h₁
  exact A.smearedField_eq j _ ⟨hc.measurable, h₂.exists_bound_of_continuous hc, h₂⟩ U
private theorem convergesTo_latticeApprox (A : StatesApproximation Q ρ ν hρ) {σ : TupleFunctional}
    (hσ : Q.HasLimit ρ ν σ) : ApproxTriple.ConvergesTo (Q.latticeApprox ρ ν hρ) σ := by
  intro X
  have hX := hσ (TupleLists.ofList X)
  have e : evalOnMap σ (TupleLists.ofList X) = σ X := by
    unfold evalOnMap
    rw [TupleLists.toList_ofList]
  rw [e] at hX
  exact hX.congr fun j => (integral_representative_eq_pairedValue A j X).symm
abbrev _root_.YangMills.SharedProofs.p60486 := @convergesTo_latticeApprox
include hL in
private theorem isBoundedForSomeM_latticeApprox
    (hB : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (A : StatesApproximation Q ρ ν hρ) {σ : TupleFunctional} (hσ : Q.HasLimit ρ ν σ) :
    LatticeApproximation.IsBoundedForSomeM (unitAxisMirrorData hL) (Q.latticeApprox ρ ν hρ) :=
  (hB.1 (unitAxisMirrorData hL) (Q.latticeApprox ρ ν hρ) fun X => ⟨σ X, convergesTo_latticeApprox A hσ X⟩).2
end OfTheStates
end WindowLimits
end
end
section
noncomputable section
open Filter MeasureTheory Topology
open scoped ComplexOrder ENNReal InnerProductSpace NNReal
namespace WindowLimits
section Separability
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass posTupleVec)
open SeparatedTuples ReflectionPositivity.TupleForm HilbertSpaceBasics
variable (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
private theorem reflectionForm_posTupleVec (X Y : supportedIn TimeAxis.upperHalfSpace) :
    reflectionForm σ (posTupleVec X) (posTupleVec Y) =
      (σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) Y.1) : ℂ) := by
  simp only [reflectionForm, reflectConj, posTupleVec, conjugation_basisVec, pushSpan, linearExtend_basisVec,
    formalMul_basisVec, TupleFunctional.spanExtension]
abbrev _root_.YangMills.SharedProofs.p11521 := @reflectionForm_posTupleVec
private theorem inner_posClass (F G : PositiveSpan) :
    ⟪posClass σ h F, posClass σ h G⟫_ℂ = reflectionForm σ F G :=
  UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := FormSpace (reflectionForm σ) h) F G
end Separability
section SeparabilityOfTheSpace
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass posTupleVec)
open TestFunctions TorusMetric
open SeparatedTuples ReflectionPositivity.TupleForm HilbertSpaceBasics
open TimeAxis (timeReflection upperHalfSpace)
open InfiniteLattice (AmbientSpace)
private theorem timeReflection_involutive : Function.Involutive timeReflection := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitContraction.timeReflection_involutive <;> assumption
private theorem invMap_timeReflection : SeparatedTuples.invMap timeReflection = timeReflection := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.invMap_timeReflection <;> assumption
private theorem continuous_timeReflection : Continuous timeReflection := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.continuous_timeReflection <;> assumption
private def timeReflectionHomeomorph : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toFun := timeReflection
  invFun := timeReflection
  left_inv := timeReflection_involutive
  right_inv := timeReflection_involutive
  continuous_toFun := continuous_timeReflection
  continuous_invFun := continuous_timeReflection
private theorem tsupport_comp_timeReflection (f : RealValued) :
    tsupport (f ∘ timeReflection) = timeReflection ⁻¹' tsupport f :=
  tsupport_comp_eq_preimage f timeReflectionHomeomorph
private theorem contDiff_timeReflection : ContDiff ℝ 1 timeReflection := by apply _root_.YangMills.Construction.OrthogonalAction.Laws.contDiff_timeReflection <;> assumption
private theorem isDisjointlySupported_pushList_timeReflection (X : SepTuple) :
    IsDisjointlySupported (pushList timeReflection X.1) := by
  simp only [pushList, invMap_timeReflection]
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    have h := X.2.1 f hf
    exact ⟨ContDiff.comp h.1 contDiff_timeReflection, h.2.comp_homeomorph timeReflectionHomeomorph⟩
  · refine List.pairwise_map.2 (X.2.2.imp fun {f h} hd => ?_)
    rw [tsupport_comp_timeReflection, tsupport_comp_timeReflection]
    exact hd.preimage _
private theorem push_timeReflection_val (X : SepTuple) :
    (push timeReflection X).1 = X.1.map fun f => f ∘ timeReflection := by
  unfold push
  rw [dif_pos (isDisjointlySupported_pushList_timeReflection X)]
  simp [pushList, invMap_timeReflection]
private theorem composable_push_timeReflection {X Y : SepTuple} (hX : X ∈ supportedIn upperHalfSpace)
    (hY : Y ∈ supportedIn upperHalfSpace) : SepTuple.Composable (push timeReflection X) Y := by apply _root_.YangMills.Construction.OrthogonalAction.Laws.composable_timeReflection <;> assumption
private theorem juxt_push_timeReflection_val {A B : SepTuple} {k : ℕ} (a b : Fin k → RealValued)
    (hA : A.1 = List.ofFn a) (hB : B.1 = List.ofFn b) (hA' : A ∈ supportedIn upperHalfSpace)
    (hB' : B ∈ supportedIn upperHalfSpace) :
    (SepTuple.juxt (push timeReflection A) B).1 =
      List.ofFn (Fin.append (fun i => a i ∘ timeReflection) b) := by
  rw [SepTuple.juxt_val (composable_push_timeReflection hA' hB'), push_timeReflection_val, hA, hB,
    List.ofFn_fin_append, List.map_ofFn]
  rfl
abbrev _root_.YangMills.SharedProofs.p44178 := @juxt_push_timeReflection_val
end SeparabilityOfTheSpace
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
section Growth
open TestSpaces
private theorem mem_flatSchwartzSet_of_offDiagonal {n : ℕ} {φ : PointTuple n → ℂ}
    (h : φ ∈ ConfigSpace.schwartzFlatOffDiagonal n) : φ ∈ flatSchwartzSet n := by
  rw [SchwartzAxioms.flatSchwartzSet_eq]
  exact h
abbrev _root_.YangMills.SharedProofs.p12297 := @mem_flatSchwartzSet_of_offDiagonal
private def flatSequenceOf (U : (p : ℕ) → flatSchwartzSet p → ℂ) :
    ConfigSpace.FlatSequence
  | 0, c => c.1
  | m + 1, φ => U (m + 1) ⟨φ.1, mem_flatSchwartzSet_of_offDiagonal φ.2⟩
private theorem norm_le_of_ofReal_le
    (hN : Continuum.TwoPresentations.PresentationsAgree) {n k : ℕ} {c : ℝ} {z : ℂ}
    (φ : ConfigSpace.SchwartzFn n) (hc : 0 ≤ c)
    (h : ENNReal.ofReal ‖z‖ ≤ ENNReal.ofReal c * weightedSeminorm k φ.1) :
    ‖z‖ ≤ c * ConfigSpace.bracketNorm k φ := by
  have e : ENNReal.ofReal (ConfigSpace.bracketNorm k φ) = weightedSeminorm k φ.1 :=
    (hN n).2.2.2.2.2.2.2.2.2.2.2.2.2.2 k φ
  rw [← e, ← ENNReal.ofReal_mul hc] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc ENNReal.toReal_nonneg)).1 h
abbrev _root_.YangMills.SharedProofs.p4988 := @norm_le_of_ofReal_le
private theorem isSepFamilyFunctional_evalOnConfig {σ : TupleFunctional}
    (hf : IsSepFunctional (evalOnMap σ)) :
    ConfigSpace.IsSepFamilyFunctional (evalOnConfig σ) := by
  refine ⟨?_, fun n hn i b b' X X' X'' h₁ h₂ h₃ => ?_⟩
  · have e : ofConfigTuple ConfigSpace.nilSepFamily = sepTupleNil :=
      sepTuple_ext _ _ rfl fun k => k.elim0
    rw [evalOnConfig, e]
    exact hf.1
  · exact hf.2 n hn i b b' (ofConfigTuple ⟨n, X⟩).2 (ofConfigTuple ⟨n, X'⟩).2
      (ofConfigTuple ⟨n, X''⟩).2 h₁ h₂ h₃
abbrev _root_.YangMills.SharedProofs.p14370 := @isSepFamilyFunctional_evalOnConfig
private theorem hasSchwingerSequence_flatSequenceOf
    (hN : Continuum.TwoPresentations.PresentationsAgree) {σ : TupleFunctional}
    {U : (p : ℕ) → flatSchwartzSet p → ℂ}
    (hf : IsSepFunctional (evalOnMap σ))
    (hU : TestSpaces.IsSchwingerFamily (evalOnMap σ) U) :
    LimitTheorem.HasSchwingerSequence σ (flatSequenceOf U) := by
  refine ⟨isSepFamilyFunctional_evalOnConfig hf, fun _ => rfl, fun m => ⟨⟨?_, ?_⟩, fun X hX h => ?_⟩⟩
  · intro a b φ ψ χ e
    exact (hU.1 (m + 1) (by omega)).1 a b _ _ _ e
  · obtain ⟨k, c, hk, hc, hb⟩ := (hU.1 (m + 1) (by omega)).2.1
    exact ⟨k, c, hk, hc, fun φ =>
      norm_le_of_ofReal_le hN (ConfigSpace.toSchwartzFn φ) hc
        (hb ⟨φ.1, mem_flatSchwartzSet_of_offDiagonal φ.2⟩)⟩
  · have hs : HasSmoothComponents Set.univ X.1 := fun i => by
      obtain ⟨-, h₁, h₂, h₃⟩ := ConfigSpace.mem_realSmoothCompactIn_iff.1 (hX i)
      exact ⟨h₁, h₂, h₃⟩
    have et : ConfigSpace.tensorRealFamily X.1 = TestSpaces.tensorProdComplex X.1 := by
      funext x
      simp [ConfigSpace.tensorRealFamily, ConfigSpace.tensorFamily,
        TestSpaces.tensorProdComplex, TestSpaces.tensorProd]
    have hY : X.1 ∈ disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) (m + 1) :=
      (ofConfigTuple ⟨m + 1, X⟩).2.2
    have hv := (hU.1 (m + 1) (by omega)).2.2 ⟨X.1, hY⟩ hs (et ▸ mem_flatSchwartzSet_of_offDiagonal h)
    refine Eq.trans ?_ hv
    exact congrArg (U (m + 1)) (Subtype.ext et)
private theorem growthBound_of_testSpaceGrowth
    (hN : Continuum.TwoPresentations.PresentationsAgree)
    {C : ConditionConstants} {σ : TupleFunctional} (hf : IsSepFunctional (evalOnMap σ))
    (hg : TestSpaces.GrowthBound C.kE C.cE C.CE C.κ (evalOnMap σ)) :
    LimitTheorem.GrowthBound C σ := by
  obtain ⟨-, hc, hC, hκ, U, hU, hUb⟩ := hg
  refine ⟨flatSequenceOf U, hasSchwingerSequence_flatSequenceOf hN hf hU, fun m φ => ?_⟩
  have hcoef : 0 ≤ C.cE * C.CE ^ (m + 1) * ((m + 1).factorial : ℝ) ^ C.κ := by positivity
  exact norm_le_of_ofReal_le hN (ConfigSpace.toSchwartzFn φ) hcoef
    (hUb (m + 1) (by omega) ⟨φ.1, mem_flatSchwartzSet_of_offDiagonal φ.2⟩)
abbrev _root_.YangMills.SharedProofs.p40086 := @growthBound_of_testSpaceGrowth
end Growth
section ALimit
variable    {σ : TupleFunctional}
private theorem isRegular_of_testSpaceRegular {σ : TupleFunctional}
    (h : TestSpaces.IsRegular (evalOnMap σ)) : LimitTheorem.IsRegular σ := by
  intro n hn
  obtain ⟨u, hu₁, hu₂⟩ := h.2 n hn
  have key : ∀ V' : Set (TestSpaces.PointTuple n), TestSpaces.distinctLocus n = V' →
      ∃ u : TestFn V' → ℂ, IsDistribution V' u ∧
        ∀ X : SepTupleOfCard n, TestSpaces.HasSmoothComponents Set.univ X.1 →
          ∃ h : TestSpaces.tensorProdComplex X.1 ∈ TestSpaces.smoothCompactSupp V',
            u ⟨_, h⟩ = ((evalOnMap σ ⟨n, X⟩ : ℝ) : ℂ) := by
    rintro _ rfl
    exact ⟨u, hu₁, hu₂⟩
  exact key _ (compl_compl _).symm
abbrev _root_.YangMills.SharedProofs.p39455 := @isRegular_of_testSpaceRegular
private theorem isRegular_of_growthBound (hD : TestSpaces.OffDiagonal.OffDiagonalFacts)
    {σ : TupleFunctional}
    (hf : TestSpaces.IsSepFunctional (evalOnMap σ)) {k : ℕ} {c C κ : ℝ}
    (hg : TestSpaces.GrowthBound k c C κ (evalOnMap σ)) : LimitTheorem.IsRegular σ := by
  obtain ⟨-, -, -, -, U, hU, -⟩ := hg
  exact isRegular_of_testSpaceRegular ((hD 1 one_pos).2.2.1 (evalOnMap σ) U hf hU).1
end ALimit
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace WindowLimits
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
open BoundsOnEverySide TestFunctions
open LimitTheorem
private theorem cumulant_eq_restrictToTestTuples (s₀ : Conventions.StandingParameters)
    (σ : TestSpaces.SepTuple → ℝ) (n : ℕ) (hn : 2 ≤ n) (X : SepTupleOfCard n) :
    TestSpaces.cumulant σ X =
      LimitGrowthFromCutoffBound.restrictToTestTuples (connectedFamilyOf s₀ σ) n hn X := rfl
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily)
open WindowLimits
open TestFunctions
open LimitTheorem
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
section ALimit
variable {F : StatedSideFamily} {N : BoundConstants} (Q : WindowStates F) {σ : TupleFunctional}
private theorem tendsToFamily_of_hasLimit
    (hInh : GibbsLimitInheritance.InheritanceTheorem) (hσ : Q.HasLimit σ) :
    BoundsOnEverySide.GibbsStateSequence.TendsToFamily Q.toGibbsStateSequence
      (connectedFamilyOf (standingParamsOfFamily F) (evalOnMap σ)) := by
  obtain ⟨hA, -⟩ := (hInh.1 F.L F.admissible F.M 0 Q.K Q.ρ Q.ν σ (fun j => (Q.ρ_mem j).1.1) hσ)
  intro n hn f
  exact hA.2 n hn ⟨f.1, (AmbientPoints.mem_separatedTuples_r4_iff f.1).1 f.2⟩
end ALimit
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace WindowLimits
open SeparatedTuples (TupleFunctional SepTuple DecompositionData)
open TestSpaces (SepTupleOfCard)
open TupleLists (ofList toList)
open CanonicalDecomposition (DecompositionTriple)
open TorusMetric (euclidNormVec)
open BoundsOnEverySide TestFunctions
open LimitTheorem
private theorem evalOnMap_ofList (τ : TupleFunctional) (W : SepTuple) : evalOnMap τ (ofList W) = τ W := by apply _root_.YangMills.SharedProofs.p25328 <;> assumption
private theorem isPermutationInvariant_evalOnMap {τ : TupleFunctional} (h : τ.IsPermInvariant) :
    WightmanReconstruction.IsPermutationInvariant (evalOnMap τ) := by apply _root_.YangMills.SharedProofs.p108250 <;> assumption
section Canonical
variable      {S : CumulantFamily}
private theorem evalOnMap_centredOf (S : CumulantFamily) (X : TestSpaces.SepTuple) :
    evalOnMap (centredOf S) X = TestSpaces.centredOfCumulants S X := by apply _root_.YangMills.SharedProofs.p13412 <;> assumption
private theorem tendsto_const_mul_inv_sq_atInfinity (c : ℝ) :
    Tendsto (fun v : Fin 4 → ℝ => c * (euclidNormVec v ^ 2)⁻¹) SeparatedTuples.atInfinity (𝓝 0) := by
  have h₁ : Tendsto euclidNormVec SeparatedTuples.atInfinity atTop := tendsto_comap
  have h₂ := (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp h₁)).const_mul c
  simpa using h₂
end Canonical
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
open CanonicalDecomposition (DecompositionTriple)
open TorusMetric (euclidNormVec)
open WindowLimits
open TestFunctions
open LimitTheorem
open WindowLimits
open TestFunctions
open LimitTheorem
private structure PrimaryInputs : Prop where
  bounded : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded
  reconstruction : ReflectionPositivity.LimitReconstruction.LimitReconstructionTheorem
  cone : ReflectionPositivity.LimitMomentumBound.MomentumBoundTheorem
  inherit : GibbsLimitInheritance.InheritanceTheorem
  moments : ClusterMoments.IteratedLimitIsMoment
  presentations : Continuum.TwoPresentations.PresentationsAgree
  offDiagonal : TestSpaces.OffDiagonal.OffDiagonalFacts
  determines : CanonicalDecompositionUniqueness.DecompositionDeterminations
  transfer : LimitTheorem.DecompositionTransfer.TransferStatement
  generators : GeneratorsAndFlows.GeneratorFlowTheorem
  windowConditions : WindowLimitConditions
  decompositionConditions : CanonicalDecompositionConditions
section ALimit
variable {F : StatedSideFamily} {N : BoundConstants} (P : PrimaryInputs) (B : BoundsHoldAt F N)
  (Q : WindowStates F) {σ : TupleFunctional}
include P in
private theorem isSepFunctional_of_hasLimit (hσ : Q.HasLimit σ) :
    TestSpaces.IsSepFunctional (evalOnMap σ) :=
  (P.windowConditions.limit_conditions Q hσ).isSepFunctional
include P in
private theorem limitSymmetries_of_hasLimit (hσ : Q.HasLimit σ) : LimitSymmetries σ :=
  (P.windowConditions.limit_conditions Q hσ).symmetries
include P in
private theorem reconstructionProperties_of_hasLimit (hσ : Q.HasLimit σ) : ReconstructionProperties σ :=
  (P.windowConditions.limit_conditions Q hσ).reconstruction
include P B in
private theorem testSpaceGrowth_of_hasLimit (hσ : Q.HasLimit σ) :
    TestSpaces.GrowthBound (growthOrder N)
      (1 + 2 * SeparatedBound.extFactorAbs)
      (growthConst F.M N (unitBallBound F.M N)) (20 + N.factorialExponent) (evalOnMap σ) :=
  P.decompositionConditions.growth_bound B Q hσ
include P B in
private theorem isRegular_of_hasLimit (hσ : Q.HasLimit σ) : LimitTheorem.IsRegular σ :=
  isRegular_of_growthBound P.offDiagonal (isSepFunctional_of_hasLimit P Q hσ)
    (testSpaceGrowth_of_hasLimit P B Q hσ)
include P B in
private theorem growthBound_of_hasLimit (hσ : Q.HasLimit σ) (cl r : SepTuple → SepTuple → ℝ)
    (E : LawConstants) :
    LimitTheorem.GrowthBound
      ((existentialConstantsAt F.M N (unitBallBound F.M N) cl r).toConditionConstants E) σ :=
  growthBound_of_testSpaceGrowth P.presentations (isSepFunctional_of_hasLimit P Q hσ)
    (testSpaceGrowth_of_hasLimit P B Q hσ)
include P B in
private theorem clusters_of_extremal (hσ : Q.HasLimit σ)
    (hpure : ∀ j, Q.ρ j ∈ cutoffExtremalSet F.L (Q.K j) (Q.β j))
    (X Y : SepTuple) (v : Fin 4 → ℝ) (hv : clusteringRadiusOf X Y ≤ euclidNormVec v) :
    SepTuple.Composable X (SeparatedTuples.push (SeparatedTuples.translate v) Y) ∧
      |σ (SepTuple.juxt X (SeparatedTuples.push (SeparatedTuples.translate v) Y)) - σ X * σ Y| ≤
        clusteringConstOf F.M N X Y * (euclidNormVec v ^ 2)⁻¹ :=
  P.decompositionConditions.cluster_law B Q hσ hpure X Y v hv
end ALimit
section Canonical
variable {F : StatedSideFamily} {N : BoundConstants} (P : PrimaryInputs) (B : BoundsHoldAt F N)
  {Q : WindowStates F} {S : CumulantFamily}
include P B in
private theorem exists_canonicalDecomposition (hρν : Q.ρ = Q.ν)
    (hvol : ∀ j, IsInfiniteVolumeLimit F.L (Q.K j) (Q.β j) (Q.ν j)) (hσ : Q.HasLimit (centredOf S)) :
    ∃ Bt : DecompositionData, Bt.IsCanonical (centredOf S) ∧
      ∀ ξ, ∃ Q' : WindowStates F, Q'.HasLimit (Bt.comp ξ) ∧
        ∀ j, Q'.ρ j ∈ cutoffExtremalSet F.L (Q'.K j) (Q'.β j) :=
  P.decompositionConditions.exists_canonical_decomposition B hρν hvol hσ
include P B in
private theorem exists_states_of_component (hρν : Q.ρ = Q.ν)
    (hvol : ∀ j, IsInfiniteVolumeLimit F.L (Q.K j) (Q.β j) (Q.ν j)) (hσ : Q.HasLimit (centredOf S))
    {A' : DecompositionData} (hA : A'.IsCanonical (centredOf S)) (ξ : A'.space) :
    ∃ Q' : WindowStates F, Q'.HasLimit (A'.comp ξ) ∧
      ∀ j, Q'.ρ j ∈ cutoffExtremalSet F.L (Q'.K j) (Q'.β j) :=
  P.decompositionConditions.exists_states_of_component B hρν hvol hσ hA ξ
end Canonical
end SystemsWithFiveBounds
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace WindowLimits
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
open BoundsOnEverySide TestFunctions
open LimitTheorem
private theorem disjoint_of_setDistR4_pos {A B : Set AmbientSpace} {d : ℝ} (hd : 0 < d)
    (h : ENNReal.ofReal d ≤ setDistR4 A B) : Disjoint A B := by apply _root_.YangMills.Construction.NonGaussianLimits.disjoint_of_le_setDistR4 <;> assumption
private theorem pair_mem_disjointSupportTuples (hP : Scales.SeparatedPairsAreTestFunctionsStatement)
    {d ϑ : ℝ} (hd : 0 < d) {f g : AmbientSpace → ℝ} (hp : (f, g) ∈ separatedPairsR4 d ϑ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    ![f, g] ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) 2 := by
  obtain ⟨hf', hg'⟩ := hP d ϑ f g hd.le hp
  have hp' := hp
  simp only [separatedPairsR4, separatedPairs, Set.mem_ofPred_eq] at hp'
  obtain ⟨-, -, -, -, s, -⟩ := hp'
  have hdis := disjoint_of_setDistR4_pos hd s
  refine ⟨fun i => ?_, fun i i' hii => ?_⟩
  · fin_cases i
    · exact ⟨hf, hf'.2, Set.subset_univ _⟩
    · exact ⟨hg, hg'.2, Set.subset_univ _⟩
  · fin_cases i <;> fin_cases i'
    · exact absurd rfl hii
    · exact hdis
    · exact hdis.symm
    · exact absurd rfl hii
abbrev _root_.YangMills.SharedProofs.p22880 := @pair_mem_disjointSupportTuples
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology
noncomputable section
namespace SystemsWithFiveBounds
open SeparatedTuples (TupleFunctional SepTuple)
open TestSpaces (SepTupleOfCard)
open WindowLimits
open BoundsOnEverySide TestFunctions
open LimitTheorem
private theorem lawConstantsOf_sideConditions {N : BoundConstants}
    (h : N.Admissible) : (lawConstantsOf N).SideConditions :=
  ⟨h.lawScale_mem, h.lawError_monotoneOn, h.lawError_mem, h.lawError_tendsto⟩
section ALimit
variable {F : StatedSideFamily} {N : BoundConstants} (P : PrimaryInputs) (Q : WindowStates F)
  {σ : TupleFunctional} {ϑ : ℝ}
private theorem statesObeyTwoPointLaw_of (hT : TwoPointLawAt F N ϑ) (K : ExistentialConstants) :
    GibbsLimitInheritance.StatesObeyTwoPointLaw ϑ (K.toConditionConstants (lawConstantsOf N)) Q.ρ := by
  intro d hd f h hp hf hh
  have hK := tendsto_atTop.1 Q.tendsto_K (⟨N.cutoffThreshold d + 1, Nat.succ_pos _⟩ : ℕ+)
  filter_upwards [hK] with j hj
  have hj' : N.cutoffThreshold d ≤ (Q.K j : ℕ) := by
    have : N.cutoffThreshold d + 1 ≤ (Q.K j : ℕ) := hj
    omega
  obtain ⟨t, ht, η, hv, h₁, h₂⟩ :=
    hT d hd (Q.K j) (Q.β j) (Q.isFirstPassage j) hj' (Q.ρ j) (Q.ρ_state j) f h hp hf hh
  refine ⟨1 + η, ?_, h₁, h₂⟩
  rw [ht, hv]
  rfl
abbrev _root_.YangMills.SharedProofs.p41393 := @statesObeyTwoPointLaw_of
include P in
private theorem twoPointLaw_of_hasLimit (hT : TwoPointLawAt F N ϑ) (hσ : Q.HasLimit σ)
    (K : ExistentialConstants) :
    TwoPointLawHoldsAt ϑ (K.toConditionConstants (lawConstantsOf N)) σ := by
  obtain ⟨-, -, -, -, hlaw⟩ := P.inherit.1 F.L F.admissible F.M ϑ Q.K Q.ρ Q.ν σ
    (fun j => (Q.ρ_mem j).1.1) hσ
  exact hlaw _ (statesObeyTwoPointLaw_of Q hT K)
end ALimit
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
open TupleLists (ofList toList)
open TorusMetric (euclidNormVec)
open BoundsOnEverySide
open LimitTheorem
open SeparatedTuples hiding conjugation
open ReflectionPositivity.TupleForm
open SpectralTheory
open CanonicalDecompositionUniqueness
private theorem hamiltonianGeMomentum_of_pairMeasure
    (hM : ReflectionPositivity.ShiftSpectralMeasure.ShiftSpectralMeasureTheorem) {σ : TupleFunctional}
    (hH : ReflectionPositivity.ContractionFunctionals.IsAdmissible σ)
    (h : IsPosSemidef (reflectionForm σ)) (i : Fin 3)
    (hb : ReflectionPositivity.PairMeasureOperators.HamiltonianDominatesMomentum σ h i) :
    HamiltonianGeMomentum σ h i := by
  obtain ⟨h', -, he⟩ := hM σ hH
  exact ⟨_, ReflectionPositivity.PairMeasureOperators.isJointSpectrum_energyMomentumPair σ h i (he i 0), hb⟩
section Projections
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
private theorem eq_of_isOrthProjOnto {P Q : ℋ →L[ℂ] ℋ} {M : Set ℋ} (hP : IsOrthProjOnto P M)
    (hQ : IsOrthProjOnto Q M) : P = Q := by
  obtain ⟨⟨sP, iP⟩, rP⟩ := hP
  obtain ⟨⟨sQ, iQ⟩, rQ⟩ := hQ
  have h₁ : P * Q = Q := by
    ext ψ
    obtain ⟨χ, hχ⟩ : Q ψ ∈ Set.range P := by rw [rP, ← rQ]; exact ⟨ψ, rfl⟩
    show P (Q ψ) = Q ψ
    rw [← hχ]
    exact congrArg (fun A : ℋ →L[ℂ] ℋ => A χ) iP.symm
  have h₂ : Q * P = P := by
    ext ψ
    obtain ⟨χ, hχ⟩ : P ψ ∈ Set.range Q := by rw [rQ, ← rP]; exact ⟨ψ, rfl⟩
    show Q (P ψ) = P ψ
    rw [← hχ]
    exact congrArg (fun A : ℋ →L[ℂ] ℋ => A χ) iQ.symm
  calc P = Q * P := h₂.symm
    _ = star Q * star P := by rw [← sP, ← sQ]
    _ = star (P * Q) := (star_mul P Q).symm
    _ = star Q := by rw [h₁]
    _ = Q := sQ.symm
private theorem orthProj_kernel_of_contractionFlow (hGen : GeneratorsAndFlows.GeneratorFlowTheorem)
    (A : UnboundedOperator ℋ) (F : ProjectionMeasure 1 ℋ) (hA : HasSpectralResolution A F)
    (hc : F.IsConcentratedOn nonnegReals) (T : ℝ≥0 → ℋ →L[ℂ] ℋ)
    (hT : ∀ t, ofBounded (T t) = F.expNegMulOp t) :
    IsOrthProjOnto (orthProjOnto (opKernel A)) (opKernel A) ∧
      TendstoStrongly atTop T (orthProjOnto (opKernel A)) := by
  have hS : F.ContractionFlowFacts := (hGen ℋ).1 F |>.2.1 hc
  have hA' : A = F.coordinateOp 0 := hA
  have hinj : ∀ B B' : ℋ →L[ℂ] ℋ, ofBounded B = ofBounded B' → B = B' := by
    intro B B' h
    ext ψ
    exact (unboundedOperator_eq_iff _ _).1 h |>.2 ⟨ψ, Submodule.mem_top⟩ ⟨ψ, Submodule.mem_top⟩ rfl
  have hST : ∀ t, F.contractionFlow t = T t :=
    fun t => hinj _ _ ((hS.expNegMulOp_eq t).symm.trans (hT t).symm)
  have hproj : IsOrthProjOnto (F zeroPoint) (opKernel A) :=
    ⟨⟨(F.isStarProjection _).isSelfAdjoint.star_eq.symm, (F.isStarProjection _).isIdempotentElem.eq.symm⟩, by
      rw [hA', hS.kernel_eq_range_atom]⟩
  have hP : orthProjOnto (opKernel A) = F zeroPoint :=
    eq_of_isOrthProjOnto (Classical.epsilon_spec (p := fun Q => IsOrthProjOnto Q (opKernel A)) ⟨_, hproj⟩) hproj
  rw [hP]
  refine ⟨hproj, ?_⟩
  have hconv := hS.tendsto_atom
  simpa only [funext hST] using hconv
end Projections
section Plateau
variable {σ : TupleFunctional} (h : IsPosSemidef (reflectionForm σ))
private theorem dense_range_posClass : Dense (Set.range (posClass σ h)) :=
  UniformSpace.Completion.denseRange_coe (α := HilbertSpaceBasics.FormSpace (reflectionForm σ) h)
private theorem isPlateauSpace_of_reconstruction (hGen : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hR : HasReconstruction σ h) :
    IsPlateauSpace σ (posClass σ h) (LimitTheorem.hamiltonianKernel σ h) (groundStateProjection σ h) := by
  obtain ⟨-, hS, hT, hM⟩ := hR
  obtain ⟨-, -, -, -, -, ⟨F, hF, hc, hFT⟩, -, hΩ⟩ := hS
  obtain ⟨⟨⟨sQ, iQ⟩, rQ⟩, hconv⟩ :=
    orthProj_kernel_of_contractionFlow hGen (pairHamiltonian σ h) F hF hc (timeShift σ h) hFT
  have hQ : groundStateProjection σ h = orthProjOnto (opKernel (pairHamiltonian σ h)) := rfl
  rw [← hQ] at sQ iQ rQ hconv
  set Q := groundStateProjection σ h with hQdef
  have hK : (LimitTheorem.hamiltonianKernel σ h : Set (PhysicalSpace σ h)) = Set.range Q := by
    have e : opKernel (pairHamiltonian σ h) =
        ((LinearMap.range (Q : PhysicalSpace σ h →ₗ[ℂ] PhysicalSpace σ h) :
        Submodule ℂ (PhysicalSpace σ h)) : Set (PhysicalSpace σ h)) := by
      rw [← rQ]; rfl
    have e' : Submodule.span ℂ (opKernel (pairHamiltonian σ h)) =
        LinearMap.range (Q : PhysicalSpace σ h →ₗ[ℂ] PhysicalSpace σ h) := by
      rw [e]; exact Submodule.span_eq _
    unfold LimitTheorem.hamiltonianKernel
    rw [e']
    rfl
  have hfix : ∀ ψ ∈ Set.range Q, Q ψ = ψ := by
    rintro _ ⟨χ, rfl⟩
    exact congrArg (fun A : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h => A χ) iQ.symm
  refine ⟨dense_range_posClass h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK]
    have : Set.range Q = {ψ | Q ψ = ψ} := Set.Subset.antisymm hfix fun ψ hψ => ⟨ψ, hψ⟩
    rw [this]
    exact isClosed_eq Q.continuous continuous_id
  · intro ψ
    show Q ψ ∈ (LimitTheorem.hamiltonianKernel σ h : Set _)
    rw [hK]; exact ⟨ψ, rfl⟩
  · intro ψ hψ
    have : ψ ∈ (LimitTheorem.hamiltonianKernel σ h : Set _) := hψ
    rw [hK] at this
    exact hfix ψ this
  · intro φ ψ
    have : star Q = Q := sQ.symm
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, this]
  · exact Submodule.subset_span ⟨hΩ.1, hΩ.2⟩
  · intro G G'
    have hU0 : spaceShift σ h 0 = 1 := hT.2.2.2.1.map_zero
    have hv0 : embedSpatial (0 : Fin 3 → ℝ) = 0 := by
      funext i
      fin_cases i <;> simp [embedSpatial]
    have ht := (hconv (posClass σ h G')).comp tendsto_real_toNNReal_atTop
    have hi : Tendsto (fun t : ℝ => ⟪posClass σ h G, timeShift σ h t.toNNReal (posClass σ h G')⟫_ℂ) atTop
        (𝓝 ⟪posClass σ h G, Q (posClass σ h G')⟫_ℂ) := Filter.Tendsto.inner tendsto_const_nhds ht
    refine hi.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht0
    have := hM G G' t.toNNReal 0
    rw [hU0, hv0, add_zero, Real.coe_toNNReal t ht0] at this
    exact this
end Plateau
section Misc
private theorem euclidNormVec_smul_timeBasisVec {t : ℝ} (ht : 0 ≤ t) :
    TorusMetric.euclidNormVec (t • timeBasisVec) = t := by
  simp [TorusMetric.euclidNormVec, timeBasisVec, PeriodicLattice.coordVec, TimeAxis.timeIdx,
    Fin.sum_univ_four, Real.sqrt_sq ht]
private theorem coordNegation_eq_timeReflection :
    ⇑(TorusTransport.coordNegation 3).1 = TimeAxis.timeReflection := by
  rw [TorusTransport.coe_coordNegation]
  funext x
  exact TorusTransport.timeReflect_apply x
private theorem hasReconstruction_of_properties {σ : TupleFunctional} (hl : ReconstructionProperties σ)
    (p : IsPosSemidef (reflectionForm σ)) : HasReconstruction σ p := by
  obtain ⟨-, -, q, hq, -⟩ := hl
  exact hq
private theorem groundStatesAsL2_of_canonical (hGen : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hC : CanonicalDecompositionUniqueness.DecompositionDeterminations) {σ : TupleFunctional}
    {B : DecompositionData} (hB : B.IsCanonical σ) (hinv : ComponentsInvariantAndClustering B)
    (hl : ReconstructionProperties σ) : GroundStatesAsL2 σ B := by
  intro p
  obtain ⟨-, U, hU, -, hΩ, hcard⟩ := (hC σ).2.2.2 B hB hinv (PhysicalSpace σ p) (posClass σ p)
    (LimitTheorem.hamiltonianKernel σ p) (groundStateProjection σ p)
    (isPlateauSpace_of_reconstruction p hGen (hasReconstruction_of_properties hl p))
  exact ⟨U, hU, hΩ, hcard⟩
private theorem isomorphic_of_uniquelyIsomorphic {A B : DecompositionData} (h : IsUniquelyIsomorphic A B) :
    A.Isomorphic B := by
  obtain ⟨f, hf, -, hh, hm⟩ := h
  exact ⟨hh.homeomorph f, hm, hf⟩
private theorem permutesComponents_of_uniquelyIsomorphic {B : DecompositionData}
    {r : AmbientSpace → AmbientSpace}
    (h : IsUniquelyIsomorphic (transportedDecomposition B r) B) : PermutesComponents B r := by
  obtain ⟨f, hf, -, hh, hm⟩ := h
  exact ⟨hh.homeomorph f, hm, hf⟩
private theorem isEuclidIsometry_hyperoctahedral (w : TorusTransport.hyperoctahedral) :
    IsEuclidIsometry w.1 := by apply _root_.YangMills.Construction.ConditionDefaults.isEuclidIsometry_hyperoctahedral <;> assumption
private theorem exists_hyperoctahedralMotion (w : TorusTransport.hyperoctahedral) :
    ∃ r : Motions.RigidMotion, IsHyperoctahedralMotion r ∧ r.toFun = w.1 := by
  obtain ⟨M, hM, v, hw⟩ := TimeAxisSymbols.isEuclideanMotion_hyperoctahedral w
  have hv : v = 0 := by
    have h₀ : w.1 0 = M.mulVec 0 + v := congrFun hw 0
    have h₁ : w.1 0 = 0 := (TorusTransport.hyperoctahedralLinear w).map_zero
    rw [h₁, Matrix.mulVec_zero, zero_add] at h₀
    exact h₀.symm
  subst hv
  have hx : ∀ x, w.1 x = M.mulVec x := fun x => by
    have : w.1 x = M.mulVec x + 0 := congrFun hw x
    rwa [add_zero] at this
  refine ⟨⟨M, hM, 0⟩, ⟨w, fun x => (hx x).symm⟩, ?_⟩
  funext x
  simp [Motions.RigidMotion.toFun, hx]
abbrev _root_.YangMills.SharedProofs.p35926 := @exists_hyperoctahedralMotion
end Misc
private theorem componentsInvariantAndClustering_of {Bt : DecompositionData} {r c : SepTuple → SepTuple → ℝ}
    (hs : ∀ ξ, _root_.YangMills.Construction.LimitTheorem.ComponentSymmetries (Bt.comp ξ))
    (hc : ∀ ξ (X Y : SepTuple) (v : Fin 4 → ℝ), r X Y ≤ euclidNormVec v →
      |Bt.comp ξ (SepTuple.juxt X (push (translate v) Y)) - Bt.comp ξ X * Bt.comp ξ Y| ≤
        c X Y * (euclidNormVec v ^ 2)⁻¹) :
    ComponentsInvariantAndClustering Bt := by
  refine ⟨fun ξ v => (hs ξ).shift_invariant v, fun ξ => ?_, ?_⟩
  · have := (hs ξ).hyperoctahedral_invariant (TorusTransport.coordNegation 3)
    rwa [coordNegation_eq_timeReflection] at this
  · intro X _ Y _ ε hε
    refine ⟨max (max (r X Y) 1) (|c X Y| / ε), fun t ht ξ => ?_⟩
    have h1 : 1 ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
    have h0 : 0 ≤ t := by linarith
    have hr : r X Y ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
    have hq : |c X Y| / ε ≤ t := (le_max_right _ _).trans ht
    have hv := euclidNormVec_smul_timeBasisVec h0
    have := hc ξ X Y (t • timeBasisVec) (by rw [hv]; exact hr)
    rw [hv] at this
    refine this.trans ?_
    have ht2 : 0 < t ^ 2 := by positivity
    calc c X Y * (t ^ 2)⁻¹ ≤ |c X Y| * (t ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (inv_nonneg.2 ht2.le)
      _ ≤ ε := by
          rw [← div_eq_mul_inv, div_le_iff₀ ht2]
          have h₁ : |c X Y| ≤ t * ε := (div_le_iff₀ hε).1 hq
          have h₂ : t ≤ t ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left h₂ hε.le]
private theorem opKernel_eq_hamiltonianKernel {σ : TupleFunctional} (h : IsPosSemidef (reflectionForm σ))
    (hGen : GeneratorsAndFlows.GeneratorFlowTheorem) (hR : HasReconstruction σ h) :
    opKernel (pairHamiltonian σ h) = (LimitTheorem.hamiltonianKernel σ h : Set (PhysicalSpace σ h)) := by
  obtain ⟨-, hS, hT, hM⟩ := hR
  obtain ⟨-, -, -, -, -, ⟨F, hF, hc, hFT⟩, -, hΩ⟩ := hS
  obtain ⟨⟨⟨sQ, iQ⟩, rQ⟩, hconv⟩ :=
    orthProj_kernel_of_contractionFlow hGen (pairHamiltonian σ h) F hF hc (timeShift σ h) hFT
  have hQ : groundStateProjection σ h = orthProjOnto (opKernel (pairHamiltonian σ h)) := rfl
  rw [← hQ] at sQ iQ rQ hconv
  set Q := groundStateProjection σ h with hQdef
  have e : opKernel (pairHamiltonian σ h) =
      ((LinearMap.range (Q : PhysicalSpace σ h →ₗ[ℂ] PhysicalSpace σ h) :
      Submodule ℂ (PhysicalSpace σ h)) : Set (PhysicalSpace σ h)) := by
    rw [← rQ]; rfl
  have e' : Submodule.span ℂ (opKernel (pairHamiltonian σ h)) =
      LinearMap.range (Q : PhysicalSpace σ h →ₗ[ℂ] PhysicalSpace σ h) := by
    rw [e]; exact Submodule.span_eq _
  unfold LimitTheorem.hamiltonianKernel
  rw [e']
  exact e
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
open TupleLists (ofList toList)
open TorusMetric (euclidNormVec)
open WindowLimits
open LimitTheorem
open SeparatedTuples hiding conjugation
open ReflectionPositivity.TupleForm
open SpectralTheory
open CanonicalDecompositionUniqueness
private structure SecondaryInputs : Prop where
  semigroup : ReflectionPositivity.ShiftSpectralMeasure.ShiftSpectralMeasureTheorem
  ident : LimitTheorem.CutoffRepresentatives.IdentificationsHold
  limitGrowth : LimitGrowthAtConstants
  pair : Scales.SeparatedPairsAreTestFunctionsStatement
section ALimit
variable {F : StatedSideFamily} {N : BoundConstants} (P : PrimaryInputs) (P' : SecondaryInputs)
  (B : BoundsHoldAt F N) (Q : WindowStates F) {σ : TupleFunctional}
include P P' in
private theorem hamiltonianGeMomentum_of_hasLimit (hσ : Q.HasLimit σ) (p : IsPosSemidef (reflectionForm σ))
    (i : Fin 3) : HamiltonianGeMomentum σ p i := by
  have A₀ := P.windowConditions.approximation Q
  have hl := convergesTo_latticeApprox A₀ hσ
  have hb := isBoundedForSomeM_latticeApprox F.admissible P.bounded A₀ hσ
  obtain ⟨hH, -⟩ := P.reconstruction (unitAxisMirrorData F.admissible) _ σ hb A₀.isReflPos hl
  obtain ⟨_, _, _, _, _, _, _, hcone⟩ := P.cone.1 (unitAxisMirrorData F.admissible) _ σ hb
    A₀.isReflPos hl
  exact hamiltonianGeMomentum_of_pairMeasure P'.semigroup hH p i (hcone i).2.1
include P B in
private theorem componentSymmetries_of_hasLimit (hσ : Q.HasLimit σ) : _root_.YangMills.Construction.LimitTheorem.ComponentSymmetries σ := by
  have s := limitSymmetries_of_hasLimit P Q hσ
  refine ⟨fun v => ?_, fun w' => ?_, fun M _ => s.reflectionPositive M, fun M _ => s.reflectionPositive M,
    s.isPermInvariant, isRegular_of_hasLimit P B Q hσ⟩
  · have h := s.motion_invariant (LimitTheorem.shiftMotion v)
      ⟨1, fun x => by simp [LimitTheorem.shiftMotion]⟩
    have e : (LimitTheorem.shiftMotion v).toFun = SeparatedTuples.translate v := by
      funext x
      simp [Motions.RigidMotion.toFun, LimitTheorem.shiftMotion, SeparatedTuples.translate]
    rw [LimitTheorem.IsMotionInvariant, e] at h
    exact h
  · obtain ⟨r, hr, e⟩ := exists_hyperoctahedralMotion w'
    have h := s.motion_invariant r hr
    rw [LimitTheorem.IsMotionInvariant, e] at h
    exact h
private abbrev diracDecomposition (σ : TupleFunctional) : DecompositionData :=
  DecompositionData.mk (space := Unit) (law := Measure.dirac ()) (comp := fun _ => σ)
include P B in
private theorem isCanonical_diracDecomposition (hσ : Q.HasLimit σ)
    (hpure : ∀ j, Q.ρ j ∈ cutoffExtremalSet F.L (Q.K j) (Q.β j)) :
    (diracDecomposition σ).IsCanonical σ := by
  have hs := limitSymmetries_of_hasLimit P Q hσ
  have hfac : ClusterMoments.ClusterFactorises (fun _ : Unit => evalOnMap σ) := by
    intro Y Z
    refine ⟨fun v => clusteringConstOf F.M N Y Z * (euclidNormVec v ^ 2)⁻¹,
      tendsto_const_mul_inv_sq_atInfinity _, ?_⟩
    have hfar : ∀ᶠ v in SeparatedTuples.atInfinity, clusteringRadiusOf Y Z ≤ euclidNormVec v :=
      (tendsto_comap (f := euclidNormVec) (x := atTop)).eventually (eventually_ge_atTop _)
    filter_upwards [hfar] with v hv _
    rw [evalOnMap_ofList, evalOnMap_ofList, evalOnMap_ofList]
    exact (clusters_of_extremal P B Q hσ hpure Y Z v hv).2
  have hM := fun X Y => P.moments Unit (Measure.dirac ()) (fun _ => evalOnMap σ) (evalOnMap σ)
    (fun _ => continuous_const) (fun _ => isPermutationInvariant_evalOnMap hs.isPermInvariant)
    (fun X => by simp) hfac X Y
  have efun : (fun W => evalOnMap σ (ofList W)) = ⇑σ := funext (evalOnMap_ofList σ)
  have e₂ : ∀ Y : List SepTuple, (Y.map ofList).map toList = Y := fun Y => by
    simp [List.map_map, Function.comp_def, TupleLists.toList_ofList]
  refine ⟨inferInstanceAs (CompactSpace Unit), inferInstanceAs (TopologicalSpace.MetrizableSpace Unit),
    inferInstanceAs (IsProbabilityMeasure (Measure.dirac ())), ?_, fun _ => hs.isPermInvariant,
    fun _ => hs.isEntrywiseLinear, fun X => (continuous_const : Continuous fun _ : Unit => σ X),
    fun a b _ => Subsingleton.elim (α := Unit) a b, ?_, ?_⟩
  · refine Set.eq_univ_of_forall fun x hx => ?_
    obtain ⟨O, ⟨-, h0⟩, hxO⟩ := hx
    have h1 : (Measure.dirac () : Measure Unit) O = 1 := Measure.dirac_apply_of_mem hxO
    exact one_ne_zero (h1.symm.trans h0)
  · intro X Y k hk vs hvs
    have hadm : CanonicalDecomposition.IsAdmissibleShifts (ofList X) (Y.map ofList) (k + 1) vs := by
      show vs ∈ iterLimitDomain (toList (ofList X)) ((Y.map ofList).map toList) Set.univ (k + 1)
      rw [TupleLists.toList_ofList, e₂]
      exact hvs
    obtain ⟨-, c, hc⟩ := (hM (ofList X) (Y.map ofList)).1 k (by simpa using hk) vs hadm
    refine ⟨c, ?_⟩
    unfold CanonicalDecomposition.partialLimit at hc
    rw [TupleLists.toList_ofList, e₂, efun] at hc
    rw [atInfinityWithin_univ]
    exact hc
  · intro X Y
    have h := (hM (ofList X) (Y.map ofList)).2
    have e₃ : ((Y.map ofList).map fun Z => evalOnMap σ Z) = Y.map fun Z => σ Z := by
      simp [List.map_map, Function.comp_def, evalOnMap_ofList]
    rw [integral_dirac, evalOnMap_ofList, e₃] at h
    show ∫ _, σ X * (Y.map fun Z => σ Z).prod ∂Measure.dirac () = iteratedLimitAtInfinity σ X Y Set.univ
    rw [integral_dirac, h]
    unfold CanonicalDecomposition.iterLimit CanonicalDecomposition.partialLimit
    rw [TupleLists.toList_ofList, e₂, efun, List.length_map]
    rfl
include P B in
private theorem opKernel_eq_span_vacuum_of_extremal (hσ : Q.HasLimit σ)
    (hpure : ∀ j, Q.ρ j ∈ cutoffExtremalSet F.L (Q.K j) (Q.β j))
    (p : IsPosSemidef (reflectionForm σ)) :
    opKernel (pairHamiltonian σ p) = (ℂ ∙ vacuum σ p : Submodule ℂ (PhysicalSpace σ p)) := by
  have hl := reconstructionProperties_of_hasLimit P Q hσ
  have hR := hasReconstruction_of_properties hl p
  have hsp := isPlateauSpace_of_reconstruction p P.generators hR
  have hcan := isCanonical_diracDecomposition P B Q hσ hpure
  have hinv : ComponentsInvariantAndClustering (diracDecomposition σ) :=
    componentsInvariantAndClustering_of (r := clusteringRadiusOf) (c := clusteringConstOf F.M N)
      (fun _ => componentSymmetries_of_hasLimit P B Q hσ)
      (fun _ X Y v hv => (clusters_of_extremal P B Q hσ hpure X Y v hv).2)
  obtain ⟨-, U, -, -, -, hcard⟩ :=
    (P.determines σ).2.2.2 _ hcan hinv (PhysicalSpace σ p) (posClass σ p) _ _ hsp
  have hcard' : Cardinal.toENat (Module.rank ℂ (LimitTheorem.hamiltonianKernel σ p)) = 1 := by
    rw [← hcard]
    show ENat.card Unit = 1
    simp
  have hrank : Module.rank ℂ (LimitTheorem.hamiltonianKernel σ p) = 1 := Cardinal.toENat_eq_one.1 hcard'
  have hfin : Module.finrank ℂ (LimitTheorem.hamiltonianKernel σ p) = 1 :=
    Module.finrank_eq_of_rank_eq (by simpa using hrank)
  let Ω : LimitTheorem.hamiltonianKernel σ p := ⟨vacuum σ p, hsp.vacuum_mem⟩
  have hΩ : Ω ≠ 0 := fun h0 => by
    have e : vacuum σ p = 0 := congrArg Subtype.val h0
    have hn : ‖vacuum σ p‖ = 1 := hR.1.2.1
    rw [e, norm_zero] at hn
    exact zero_ne_one hn
  have hall := (finrank_eq_one_iff_of_nonzero' Ω hΩ).1 hfin
  have hK : LimitTheorem.hamiltonianKernel σ p = (ℂ ∙ vacuum σ p : Submodule ℂ (PhysicalSpace σ p)) := by
    refine le_antisymm (fun x hx => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hsp.vacuum_mem)
    obtain ⟨c, hc⟩ := hall ⟨x, hx⟩
    exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩
  rw [opKernel_eq_hamiltonianKernel p P.generators hR, hK]
include P P' B in
private theorem componentReconstruction_of_extremal (hσ : Q.HasLimit σ)
    (hpure : ∀ j, Q.ρ j ∈ cutoffExtremalSet F.L (Q.K j) (Q.β j)) : _root_.YangMills.Construction.LimitTheorem.ComponentReconstruction σ :=
  ⟨reconstructionProperties_of_hasLimit P Q hσ, opKernel_eq_span_vacuum_of_extremal P B Q hσ hpure,
    hamiltonianGeMomentum_of_hasLimit P P' Q hσ⟩
end ALimit
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
    TestSpaces.centredOfCumulants S ⟨2, X⟩ = S 2 le_rfl X := by apply _root_.YangMills.Construction.TestSpaces.RecursionTriangular.centredOfCumulants_pair <;> assumption
abbrev _root_.YangMills.SharedProofs.p31970 := @centredOfCumulants_two
private theorem two_le_rank_physicalSpace {σ : TupleFunctional} (p : IsPosSemidef (reflectionForm σ))
    (hR : HasReconstruction σ p)
    (X : supportedIn TimeAxis.upperHalfSpace) (h0 : σ X.1 = 0)
    (hpos : 0 < σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) X.1)) :
    2 ≤ Module.rank ℂ (PhysicalSpace σ p) := by
  obtain ⟨⟨-, hn, hX⟩, -⟩ := hR
  set u := posClass σ p (posTupleVec X) with hu
  have huΩ : ⟪u, vacuum σ p⟫_ℂ = 0 := by
    rw [hu, (hX X).1, h0]
    simp
  have huu : ⟪u, u⟫_ℂ = ((σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) X.1) : ℝ) : ℂ) := by
    rw [hu, inner_posClass, reflectionForm_posTupleVec]
  have hu0 : ⟪u, u⟫_ℂ ≠ 0 := by
    rw [huu]
    exact_mod_cast hpos.ne'
  have hΩ0 : vacuum σ p ≠ 0 := fun e => by
    rw [e, norm_zero] at hn
    exact zero_ne_one hn
  have hli : LinearIndependent ℂ ![vacuum σ p, u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e₁ := congrArg (fun y => ⟪u, y⟫_ℂ) hst
    simp only [inner_add_right, inner_smul_right, huΩ, inner_zero_right, mul_zero, zero_add] at e₁
    have ht : t = 0 := (mul_eq_zero.1 e₁).resolve_right hu0
    subst ht
    simp only [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right hΩ0, rfl⟩
  have h := hli.cardinal_le_rank
  simpa using h
private theorem reflectAcross_coordVec_eq_timeReflection :
    TwoPoints.reflectAcross (PeriodicLattice.coordVec 3) = TimeAxis.timeReflection := by apply _root_.YangMills.Construction.TwoPoints.ReflectionsPlaneFacts.reflectAcross_coordVec_three <;> assumption
private theorem exists_reflected_pair (hPl : TestPlatePieces.Statement) {ϖ : ℝ} (hϖ : 0 < ϖ)
    (hϖ4 : ϖ ≤ 4) :
    ∃ f : AmbientSpace → ℝ,
      (f ∘ TimeAxis.timeReflection, f) ∈ separatedPairsR4 (5 / 2 * ϖ) TwoPoints.Shapes.shapeConst ∧
      ContDiff ℝ 1 f ∧ ContDiff ℝ 1 (f ∘ TimeAxis.timeReflection) ∧
      tsupport f ⊆ TimeAxis.upperHalfSpace := by
  let b : ContDiffBump (0 : Fin 2 → ℝ) := ⟨1, 2, one_pos, by norm_num⟩
  let φ : (Fin 2 → ℝ) → ℂ := fun ζ => ((b ζ : ℝ) : ℂ)
  have hφs : tsupport φ ⊆ tsupport b := closure_mono fun ζ hζ hb => hζ (by simp [φ, hb])
  have hbt : tsupport b ⊆ Metric.closedBall 0 2 := by
    rw [b.tsupport_eq]
  have hφ : φ ∈ TwoPoints.transProfiles :=
    ⟨⟨Complex.ofRealCLM.contDiff.comp b.contDiff, b.hasCompactSupport.isCompact.of_isClosed_subset
      (isClosed_tsupport _) hφs, Set.subset_univ _⟩, fun ζ => by simp [φ]⟩
  have hset : PlateHypotheses φ 4 ϖ 1 := by
    refine ⟨hφ, ⟨0, by simp [φ, b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))]⟩,
      by norm_num, fun ζ hζ => ?_, hϖ, hϖ4, ⟨le_rfl, by norm_num⟩⟩
    have h₁ : ‖ζ‖ ≤ 2 := by simpa using hbt (hφs hζ)
    have hc : ∀ i, ζ i ^ 2 ≤ 4 := fun i => by
      have : |ζ i| ≤ 2 := (norm_le_pi_norm ζ i).trans h₁
      nlinarith [abs_nonneg (ζ i), sq_abs (ζ i)]
    show TwoPoints.euclidNorm ζ ≤ 4
    refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
    rw [Fin.sum_univ_two]
    nlinarith [hc 0, hc 1]
  obtain ⟨hcover, -, -, hdec, hmirror⟩ := hPl φ 4 ϖ 1 hset
  obtain ⟨ι, hι⟩ : (supportCells ϖ φ).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : ∀ ι, cellBump ϖ ι 0 = 0 := fun ι => by
      have hn : ι ∉ supportCells ϖ φ := by simp [hne]
      have hz : localizedProfile ϖ φ ι 0 = 0 := by
        by_contra h
        exact hn ⟨0, h⟩
      have hb0 : φ 0 = 1 := by
        simp [φ, b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))]
      simpa [localizedProfile, hb0] using hz
    have hs := hcover.1 0
    simp only [h0] at hs
    exact zero_ne_one (hasSum_zero.unique hs)
  obtain ⟨⟨⟨p₁, p₂⟩, hp, h₁, h₂⟩, hm, hh, -⟩ := (hmirror ι hι).1
  have hpart := ((hdec.2.2 ι hι).1)
  simp only at hp h₁ h₂
  set h := upperCellPlate ϖ 1 φ ι with hdef
  have hreal : ∀ x, p₂ x = (h x).re := fun x => by
    rw [← h₂]
    simp [TwoPoints.ofRealFun]
  have hc₂ : ContDiff ℝ 1 p₂ := by
    have : p₂ = fun x => (h x).re := funext hreal
    rw [this]
    exact Complex.reCLM.contDiff.comp hh.1.1
  have hp₁ : p₁ = p₂ ∘ TimeAxis.timeReflection := by
    funext x
    have e := congrFun h₁ x
    rw [← h₂, TwoPoints.reflectFun, reflectAcross_coordVec_eq_timeReflection] at e
    exact Complex.ofReal_injective e
  have hsup : tsupport p₂ ⊆ tsupport h := closure_mono fun x hx hz => hx (by
    rw [hreal, show h x = 0 from hz]
    simp)
  refine ⟨p₂, hp₁ ▸ hp, hc₂, ?_, fun x hx => ?_⟩
  · exact hc₂.comp (by
      refine contDiff_pi.2 fun μ => ?_
      fin_cases μ <;> simp [TimeAxis.timeReflection] <;> fun_prop)
  · have h₃ := hpart.2.2 (hsup hx)
    show TimeAxis.timeComponent x > 0
    have : TimeAxis.timeComponent x = x 3 := rfl
    rw [this]
    linarith [h₃.1]
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology ENNReal
noncomputable section
namespace WindowLimits
open TestSpaces (SepTupleOfCard)
open HilbertSpaceBasics (IsPosSemidef)
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass vacuum posTupleVec timeShift)
open ReflectionPositivity.PairMeasureOperators (pairHamiltonian groundStateProjection)
open TupleLists (ofList toList)
open TorusMetric (euclidNormVec)
open BoundsOnEverySide
open LimitTheorem
open SeparatedTuples hiding conjugation
open ReflectionPositivity.TupleForm
private theorem existsUnique_distribution_offDiagonal {n : ℕ} {Φ : SepTupleOfCard n → ℝ}
    (h : ∃! u : TestSpaces.TestFnOn (TestSpaces.distinctLocus n) → ℂ,
      TestSpaces.IsDistribOn u ∧ ∀ X : SepTupleOfCard n, TestSpaces.HasSmoothComponents Set.univ X.1 →
        ∃ h : TestSpaces.tensorProdComplex X.1 ∈ TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus n),
          u ⟨_, h⟩ = ((Φ X : ℝ) : ℂ)) :
    ∃! u, IsDistribution (offDiagonal n) u ∧ AgreesOnTensors Φ u := by
  have key : ∀ V' : Set (TestSpaces.PointTuple n), TestSpaces.distinctLocus n = V' →
      ∃! u : TestFn V' → ℂ, IsDistribution V' u ∧
        ∀ X : SepTupleOfCard n, TestSpaces.HasSmoothComponents Set.univ X.1 →
          ∃ h : TestSpaces.tensorProdComplex X.1 ∈ TestSpaces.smoothCompactSupp V',
            u ⟨_, h⟩ = ((Φ X : ℝ) : ℂ) := by
    rintro _ rfl
    exact h
  exact key _ (compl_compl _).symm
abbrev _root_.YangMills.SharedProofs.p64229 := @existsUnique_distribution_offDiagonal
section TheLimit
section Assembly
private theorem exists_unit_integral_tuple : ∃ X : SepTupleOfCard 1, ∫ x, X.1 0 x = 1 := by
  let b : ContDiffBump (0 : Fin 4 → ℝ) := ⟨1, 2, one_pos, by norm_num⟩
  have hstar : b.normed volume ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) :=
    ⟨b.contDiff_normed, b.hasCompactSupport_normed, Set.subset_univ _⟩
  exact ⟨TestSpaces.singletonSepTuple _ hstar, b.integral_normed⟩
end Assembly
end TheLimit
end WindowLimits
end
end
section
open MeasureTheory Filter InfiniteLattice Set
open scoped Topology ENNReal
noncomputable section
namespace SystemsWithFiveBounds
open WindowLimits
open BoundsOnEverySide (SideFamily)
open LimitTheorem
open SeparatedTuples hiding conjugation
open ReflectionPositivity.TupleForm
open TestSpaces (SepTupleOfCard)
open HilbertSpaceBasics (IsPosSemidef)
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass vacuum posTupleVec timeShift)
open ReflectionPositivity.PairMeasureOperators (pairHamiltonian groundStateProjection)
open TupleLists (ofList toList)
open TorusMetric (euclidNormVec)
section TheLimit
variable {F : StatedSideFamily} {N : BoundConstants} (P : PrimaryInputs) (P' : SecondaryInputs)
  (B : BoundsHoldAt F N) {Q : WindowStates F} {S : CumulantFamily}
include P B in
private theorem testSpaceRegular_of_hasLimit {σ : TupleFunctional} (Q : WindowStates F) (hσ : Q.HasLimit σ) :
    TestSpaces.IsRegular (evalOnMap σ) := by
  obtain ⟨-, -, -, -, U, hU, -⟩ := testSpaceGrowth_of_hasLimit P B Q hσ
  exact ((P.offDiagonal 1 one_pos).2.2.1 (evalOnMap σ) U (isSepFunctional_of_hasLimit P Q hσ) hU).1
include P P' B in
private theorem hasDistributions_of_hasLimit (hOne : Continuum.UnifiedTestSpace.TestSpacesUnified)
    (hTwo : ConfigurationSpace.SmoothSubspaces)
    (hS : LimitTheorem.CutoffRepresentatives.CentredSymmetriesAndCumulants S)
    (hσ : Q.HasLimit (centredOf S)) : HasDistributions S := by
  have hf := isSepFunctional_of_hasLimit P Q hσ
  have hreg := testSpaceRegular_of_hasLimit P B Q hσ
  refine ⟨hf, isRegular_of_testSpaceRegular hreg, fun n hn => ?_⟩
  have hcon := (P'.limitGrowth F N B (standingParamsOfFamily F)
    (connectedFamilyOf (standingParamsOfFamily F) (evalOnMap (centredOf S)))
    Q.toGibbsStateSequence Q.isFirstPassage Q.ρ_state (tendsToFamily_of_hasLimit Q P.inherit hσ)).consequences
  obtain ⟨T, hT, -⟩ := hcon.existsUnique_extension n hn
  have hnpos : 0 < n := by omega
  obtain ⟨-, hres, -, -, -⟩ := P.offDiagonal n hnpos
  obtain ⟨⟨-, -, hs2, hs3⟩, -, -⟩ := hOne n hnpos
  have hin : ∀ φ : TestSpaces.flatSchwartzSet n, φ.1 ∈ FlatTensors.flatSchwartz n :=
    fun φ => hs3.symm ▸ φ.2
  let T' : TestSpaces.flatSchwartzSet n → ℂ := fun φ => T ⟨φ.1, hin φ⟩
  have hsm : ∀ (a : ℂ) (φ : TestSpaces.flatSchwartzSet n),
      a • φ.1 ∈ FlatTensors.flatSchwartz n := fun a φ => by
    have h : φ.1 ∈ ConfigurationSpace.flatSchwartzSet n := hin φ
    show a • φ.1 ∈ ConfigurationSpace.flatSchwartzSet n
    rw [ConfigurationSpace.flatSchwartzSet_eq_rapidDecaySet_inter] at h ⊢
    obtain ⟨-, ⟨-, -, -, hA⟩, -, -, -, hB⟩ := hTwo n hnpos
    exact ⟨hA a _ h.1, hB a _ h.2⟩
  have hlin : TestSpaces.IsCLinearOnFlat T' := fun a b φ ψ χ e => by
    obtain ⟨ha, hm⟩ := hT.1.1
    have e₁ := ha ⟨_, hsm a φ⟩ ⟨_, hsm b ψ⟩ ⟨χ.1, hin χ⟩ e
    have e₂ := hm a ⟨φ.1, hin φ⟩ ⟨_, hsm a φ⟩ rfl
    have e₃ := hm b ⟨ψ.1, hin ψ⟩ ⟨_, hsm b ψ⟩ rfl
    show T ⟨χ.1, hin χ⟩ = a * T ⟨φ.1, hin φ⟩ + b * T ⟨ψ.1, hin ψ⟩
    rw [e₁, e₂, e₃]
  set c : ℝ := 2 * SeparatedBound.extFactorAbs *
      SeparatedPowerBound.powerBase F.M N.sepExponent (powerConst N) ^ n *
      (n.factorial : ℝ) ^ ((19 : ℝ) + N.factorialExponent) with hc
  have hb : ∀ φ : TestSpaces.flatSchwartzSet n, ENNReal.ofReal ‖T' φ‖ ≤
      ENNReal.ofReal |c| * TestSpaces.weightedSeminorm ((10 + N.sepExponent) * n) φ.1 := fun φ => by
    have h := hcon.extension_bound n hn T hT ⟨φ.1, hin φ⟩
    have hk : 0 < (10 + N.sepExponent) * n := Nat.mul_pos (by omega) hnpos
    have e : TestSpaces.weightedSeminorm ((10 + N.sepExponent) * n) φ.1 =
        ConfigurationSpace.sobolevWeightNorm ((10 + N.sepExponent) * n) φ.1 :=
      hs2 ⟨φ.1, (hin φ).1⟩ _ hk
    rw [e]
    exact h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_abs_self _)) _)
  obtain ⟨hsub, hdist⟩ :=
    hres T' ((10 + N.sepExponent) * n) |c| hlin (Nat.mul_pos (by omega) hnpos) (abs_nonneg _) hb
  have hvalue : ∀ X : SepTupleOfCard n, TestSpaces.HasSmoothComponents Set.univ X.1 →
      ∃ h : TestSpaces.tensorProdComplex X.1 ∈ TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus n),
        TestSpaces.OffDiagonal.restrictToCompactSupp hsub T' ⟨_, h⟩ = ((S n hn X : ℝ) : ℂ) := by
    intro X hX
    obtain ⟨u, -, hu⟩ := hreg.2 n hnpos
    obtain ⟨h, -⟩ := hu X hX
    refine ⟨h, ?_⟩
    have et : ConfigurationSpace.ofRealFun (TestSpaces.tensorProd X.1) =
        TestSpaces.tensorProdComplex X.1 := by
      funext x
      simp [ConfigurationSpace.ofRealFun, TestSpaces.tensorProdComplex, TestSpaces.tensorProd]
    have hflat : ConfigurationSpace.ofRealFun (TestSpaces.tensorProd X.1) ∈
        ConfigurationSpace.flatSchwartzSet n := by
      rw [et]
      exact hin ⟨_, hsub h⟩
    have e := hT.2 X.1 ⟨X.2, hX⟩ hflat
    have e₂ : LimitGrowthFromCutoffBound.restrictToTestTuples
        (connectedFamilyOf (standingParamsOfFamily F) (evalOnMap (centredOf S))) n hn X = S n hn X :=
      (cumulant_eq_restrictToTestTuples (standingParamsOfFamily F) _ n hn X).symm.trans (hS.2.2.2 n hn X)
    have e₃ : TestSpaces.OffDiagonal.restrictToCompactSupp hsub T' ⟨_, h⟩ = T ⟨_, hflat⟩ :=
      congrArg T (Subtype.ext et.symm)
    rw [e₃]
    exact e.trans (congrArg (fun t : ℝ => (t : ℂ)) e₂)
  refine existsUnique_distribution_offDiagonal
    ⟨TestSpaces.OffDiagonal.restrictToCompactSupp hsub T', ⟨hdist, hvalue⟩, ?_⟩
  rintro u ⟨hu, hv⟩
  refine (P.offDiagonal n hnpos).1 u _ hu hdist fun X hX h => ?_
  obtain ⟨h₁, e₁⟩ := hv X hX
  obtain ⟨h₂, e₂⟩ := hvalue X hX
  exact e₁.trans e₂.symm
private abbrev existentialConditionConstants (M : ℝ) (N : BoundConstants) (E : LawConstants) :
    ConditionConstants :=
  (existentialConstants M N).toConditionConstants E
private structure ConditionsAtConstants (M : ℝ) (N : BoundConstants) (S : CumulantFamily) : Prop where
  symmetries : _root_.YangMills.Construction.LimitTheorem.LatticeSymmetries S
  coordinateMirrors : IsReflectionPositiveAxial (centredOf S)
  distributions : HasDistributions S
  perBall : ∀ E, PerBallBoundsAt M (existentialConditionConstants M N E) (centredOf S)
  growth : ∀ E, GrowthBound (existentialConditionConstants M N E) (centredOf S)
  reconstruction : ReconstructionProperties (centredOf S)
  connected_eq : HasCumulants (centredOf S) S
  diagonalMirrors : IsReflectionPositiveDiagonal (centredOf S)
  bounds : ∀ (h : IsPosSemidef (reflectionForm (centredOf S))) (i : Fin 3),
    HamiltonianGeMomentum (centredOf S) h i
  decomposition : _root_.YangMills.Construction.LimitTheorem.DecompositionProperties (centredOf S)
  componentSymmetries : ∀ A' : DecompositionData, A'.IsCanonical (centredOf S) →
    ∀ ξ, _root_.YangMills.Construction.LimitTheorem.ComponentSymmetries (A'.comp ξ)
  componentOnePoint : ∀ A' : DecompositionData, A'.IsCanonical (centredOf S) →
    ∃ c : A'.space → ℝ, Continuous c ∧ ∫ ξ, c ξ ∂A'.law = 0 ∧
      ∀ (ξ : A'.space) (X : SepTupleOfCard 1), connectedFn (A'.comp ξ) X = c ξ * ∫ x, X.1 0 x
  componentPerBall : ∀ A' : DecompositionData, A'.IsCanonical (centredOf S) →
    ∀ ξ E, PerBallBoundsAt M (existentialConditionConstants M N E) (A'.comp ξ)
  componentGrowth : ∀ A' : DecompositionData, A'.IsCanonical (centredOf S) →
    ∀ ξ E, GrowthBound (existentialConditionConstants M N E) (A'.comp ξ)
  componentReconstruction : ∀ A' : DecompositionData, A'.IsCanonical (centredOf S) →
    ∀ ξ, _root_.YangMills.Construction.LimitTheorem.ComponentReconstruction (A'.comp ξ)
  componentClusters : ∀ A' : DecompositionData, A'.IsCanonical (centredOf S) →
    ∀ ξ (X Y : SepTuple) (v : Fin 4 → ℝ), clusteringRadiusOf X Y ≤ euclidNormVec v →
      SepTuple.Composable X (push (translate v) Y) ∧
        |A'.comp ξ (SepTuple.juxt X (push (translate v) Y)) - A'.comp ξ X * A'.comp ξ Y| ≤
          clusteringConstOf M N X Y * (euclidNormVec v ^ 2)⁻¹
section Assembly
variable {ϑ : ℝ}
include P B in
private theorem onePointConstants_of (hS : LimitTheorem.CutoffRepresentatives.CentredSymmetriesAndCumulants S)
    (hρν : Q.ρ = Q.ν) (hvol : ∀ j, IsInfiniteVolumeLimit F.L (Q.K j) (Q.β j) (Q.ν j))
    (hσ : Q.HasLimit (centredOf S))
    {A' : DecompositionData} (hA : A'.IsCanonical (centredOf S)) :
    ∃ c : A'.space → ℝ, Continuous c ∧ ∫ ξ, c ξ ∂A'.law = 0 ∧
      ∀ (ξ : A'.space) (X : SepTupleOfCard 1), connectedFn (A'.comp ξ) X = c ξ * ∫ x, X.1 0 x := by
  have hcomp := fun ξ => exists_states_of_component P B hρν hvol hσ hA ξ
  obtain ⟨Xs, hXs⟩ := exists_unit_integral_tuple
  let X₀ : SepTuple := toList ⟨1, Xs⟩
  refine ⟨fun ξ => A'.comp ξ X₀, hA.continuous_comp X₀, ?_, fun ξ X => ?_⟩
  · have h := hA.integral_comp_prod X₀ []
    have e₀ : connectedFn (centredOf S) Xs = evalOnMap (centredOf S) ⟨1, Xs⟩ :=
      TestSpaces.cumulant_single _ Xs
    have e₁ : (centredOf S) X₀ = 0 := by
      have := hS.2.2.1 Xs
      rw [e₀] at this
      exact this
    simp only [List.map_nil, List.prod_nil, mul_one] at h
    rw [h]
    show SeparatedTuples.iterLimitValue (centredOf S) X₀ [] Set.univ 0 [] = 0
    simpa [SeparatedTuples.iterLimitValue, SeparatedTuples.shiftedJuxt] using e₁
  · obtain ⟨Q', hl, -⟩ := hcomp ξ
    obtain ⟨c, hc⟩ := (P.windowConditions.limit_conditions Q' hl).onePoint_eq
    have e₁ : connectedFn (A'.comp ξ) X = evalOnMap (A'.comp ξ) ⟨1, X⟩ :=
      TestSpaces.cumulant_single _ X
    have e₂ : A'.comp ξ X₀ = c := by
      have := hc Xs
      rw [hXs, mul_one] at this
      exact this
    show connectedFn (A'.comp ξ) X = A'.comp ξ X₀ * ∫ x, X.1 0 x
    rw [e₁, hc X, e₂]
include P B in
private theorem decompositionProperties_of (hρν : Q.ρ = Q.ν)
    (hvol : ∀ j, IsInfiniteVolumeLimit F.L (Q.K j) (Q.β j) (Q.ν j)) (hσ : Q.HasLimit (centredOf S)) :
    _root_.YangMills.Construction.LimitTheorem.DecompositionProperties (centredOf S) := by
  obtain ⟨Bt, hB, hcomp⟩ := exists_canonicalDecomposition P B hρν hvol hσ
  have hs : ∀ ξ, _root_.YangMills.Construction.LimitTheorem.ComponentSymmetries (Bt.comp ξ) := fun ξ => by
    obtain ⟨Q', hl, -⟩ := hcomp ξ
    exact componentSymmetries_of_hasLimit P B Q' hl
  have hinv : CanonicalDecompositionUniqueness.ComponentsInvariantAndClustering Bt :=
    componentsInvariantAndClustering_of (r := clusteringRadiusOf) (c := clusteringConstOf F.M N) hs
      fun ξ X Y v hv => by
        obtain ⟨Q', hl, hp⟩ := hcomp ξ
        exact (clusters_of_extremal P B Q' hl hp X Y v hv).2
  have hl := reconstructionProperties_of_hasLimit P Q hσ
  have hsS := componentSymmetries_of_hasLimit P B Q hσ
  have hG : LimitTheorem.DecompositionTransfer.HasDecompositionConditions (centredOf S) Bt :=
    ⟨hB, fun A₁ hA₁ => isomorphic_of_uniquelyIsomorphic ((P.determines _).1 A₁ _ hA₁ hB),
      groundStatesAsL2_of_canonical P.generators P.determines hB hinv hl,
      fun r hr hi => permutesComponents_of_uniquelyIsomorphic ((P.determines _).2.2.1 _ hB r hr hi).2⟩
  refine ⟨⟨_, hB⟩, fun A₁ B₁ hA₁ hB₁ => ?_, fun A₁ hA₁ => ?_, fun A₁ hA₁ => ?_,
    fun A₁ hA₁ => ⟨fun v => ?_, fun w' => ?_⟩⟩
  · exact isomorphic_of_uniquelyIsomorphic ((P.determines _).1 A₁ B₁ hA₁ hB₁)
  · exact (P.transfer _ _ A₁ hG hA₁).2.1.1
  · exact (P.transfer _ _ A₁ hG hA₁).2.2.2
  · exact (P.transfer _ _ A₁ hG hA₁).2.2.1 _ (isEuclidIsometry_translate v) (hsS.shift_invariant v)
  · exact (P.transfer _ _ A₁ hG hA₁).2.2.1 _ (isEuclidIsometry_hyperoctahedral w')
      (hsS.hyperoctahedral_invariant w')
include P P' in
private theorem two_le_rank_of_hasLimit (hPl : TwoPoints.TestPlates.TestPlatePieces.Statement)
    (hSm : TwoPoints.SmallerShape.Statement)
    (hS : LimitTheorem.CutoffRepresentatives.CentredSymmetriesAndCumulants S)
    (hσ : Q.HasLimit (centredOf S)) {E : LawConstants} (hE : E.SideConditions)
    (hϑ : ϑ ∈ Ioc (0 : ℝ) 1) (hshape : ϑ ≤ TwoPoints.Shapes.shapeConst)
    (hpos : ∀ d ∈ Ioc (0 : ℝ) E.d₀, ∀ X : SepTupleOfCard 2,
      (X.1 0, X.1 1) ∈ TestFunctions.separatedPairsR4 d ϑ → 0 < S 2 le_rfl X)
    (p : IsPosSemidef (reflectionForm (centredOf S))) :
    2 ≤ Module.rank ℂ (PhysicalSpace (centredOf S) p) := by
  have hd₀ := hE.d₀_mem
  have hϖ : 0 < 2 / 5 * E.d₀ := by linarith [hd₀.1]
  have hϖ4 : 2 / 5 * E.d₀ ≤ 4 := by linarith [hd₀.2]
  obtain ⟨f, hpair, hc, hcθ, hsupp⟩ := exists_reflected_pair hPl hϖ hϖ4
  have e : 5 / 2 * (2 / 5 * E.d₀) = E.d₀ := by ring
  rw [e] at hpair
  have hcls : (f ∘ TimeAxis.timeReflection, f) ∈ TestFunctions.separatedPairsR4 E.d₀ ϑ :=
    (hSm ϑ hϑ.1 hshape).1 E.d₀ hd₀.1 hpair
  let X₂ : SepTupleOfCard 2 :=
    ⟨![f ∘ TimeAxis.timeReflection, f], pair_mem_disjointSupportTuples P'.pair hd₀.1 hcls hcθ hc⟩
  have h2 := hpos E.d₀ ⟨hd₀.1, le_rfl⟩ X₂ hcls
  have hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) := X₂.2.1 1
  let X₁ : SepTuple := toList ⟨1, TestSpaces.singletonSepTuple f hf⟩
  have hX₁ : X₁.1 = List.ofFn (fun _ : Fin 1 => f) := rfl
  have hmem : X₁ ∈ supportedIn TimeAxis.upperHalfSpace := fun g hg => by
    rw [hX₁] at hg
    simp at hg
    rw [hg]
    exact hsupp
  have h0 : (centredOf S) X₁ = 0 := by
    have e₀ : connectedFn (centredOf S) (TestSpaces.singletonSepTuple f hf) =
        evalOnMap (centredOf S) ⟨1, TestSpaces.singletonSepTuple f hf⟩ :=
      TestSpaces.cumulant_single _ _
    have := hS.2.2.1 (TestSpaces.singletonSepTuple f hf)
    rw [e₀] at this
    exact this
  have hprod : (centredOf S) (SepTuple.juxt (push TimeAxis.timeReflection X₁) X₁) = S 2 le_rfl X₂ := by
    have e₁ := juxt_push_timeReflection_val (fun _ => f) (fun _ => f) hX₁ hX₁ hmem hmem
    have e₂ : SepTuple.juxt (push TimeAxis.timeReflection X₁) X₁ = toList ⟨2, X₂⟩ :=
      Subtype.ext (e₁.trans (by
        show _ = List.ofFn ![f ∘ TimeAxis.timeReflection, f]
        simp [List.ofFn_succ, Fin.append, Fin.addCases]))
    rw [e₂]
    show evalOnMap (centredOf S) ⟨2, X₂⟩ = _
    rw [evalOnMap_centredOf, centredOfCumulants_two]
  exact two_le_rank_physicalSpace p
    (hasReconstruction_of_properties (reconstructionProperties_of_hasLimit P Q hσ) p)
    ⟨X₁, hmem⟩ h0 (hprod ▸ h2)
include P P' B in
private theorem conditionsAtConstants_of (hOne : Continuum.UnifiedTestSpace.TestSpacesUnified)
    (hTwo : ConfigurationSpace.SmoothSubspaces)
    (hS : LimitTheorem.CutoffRepresentatives.CentredSymmetriesAndCumulants S)
    (hρν : Q.ρ = Q.ν) (hvol : ∀ j, IsInfiniteVolumeLimit F.L (Q.K j) (Q.β j) (Q.ν j))
    (hσ : Q.HasLimit (centredOf S)) : ConditionsAtConstants F.M N S := by
  have hs := limitSymmetries_of_hasLimit P Q hσ
  have hcomp := fun (A' : DecompositionData) (hA : A'.IsCanonical (centredOf S)) ξ =>
    exists_states_of_component P B hρν hvol hσ hA ξ
  refine ⟨⟨fun v => (hS.2.1 _).1
      (hs.motion_invariant _ ⟨1, fun x => by simp [LimitTheorem.shiftMotion]⟩),
      fun r h _ => (hS.2.1 r).1 (hs.motion_invariant r h), hS.1.1 hs.isPermInvariant, hs.motion_invariant,
      hs.isPermInvariant⟩,
    fun M _ => hs.reflectionPositive M, hasDistributions_of_hasLimit P P' B hOne hTwo hS hσ,
    fun E => (P.windowConditions.limit_conditions Q hσ).perBall _ B _ _ _ E,
    fun E => growthBound_of_hasLimit P B Q hσ _ _ E,
    reconstructionProperties_of_hasLimit P Q hσ, hS.2.2.2, fun M _ => hs.reflectionPositive M,
    hamiltonianGeMomentum_of_hasLimit P P' Q hσ,
    decompositionProperties_of P B hρν hvol hσ, fun A' hA ξ => ?_,
    fun A' hA => onePointConstants_of P B hS hρν hvol hσ hA,
    fun A' hA ξ E => ?_, fun A' hA ξ E => ?_, fun A' hA ξ => ?_, fun A' hA ξ X Y v hv => ?_⟩
  · obtain ⟨Q', hl, -⟩ := hcomp A' hA ξ
    exact componentSymmetries_of_hasLimit P B Q' hl
  · obtain ⟨Q', hl, -⟩ := hcomp A' hA ξ
    exact (P.windowConditions.limit_conditions Q' hl).perBall _ B _ _ _ E
  · obtain ⟨Q', hl, -⟩ := hcomp A' hA ξ
    exact growthBound_of_hasLimit P B Q' hl _ _ E
  · obtain ⟨Q', hl, hp⟩ := hcomp A' hA ξ
    exact componentReconstruction_of_extremal P P' B Q' hl hp
  · obtain ⟨Q', hl, hp⟩ := hcomp A' hA ξ
    exact clusters_of_extremal P B Q' hl hp X Y v hv
include P P' B in
private theorem lawConditions_of (hPl : TwoPoints.TestPlates.TestPlatePieces.Statement)
    (hSm : TwoPoints.SmallerShape.Statement)
    (hS : LimitTheorem.CutoffRepresentatives.CentredSymmetriesAndCumulants S)
    (hρν : Q.ρ = Q.ν) (hvol : ∀ j, IsInfiniteVolumeLimit F.L (Q.K j) (Q.β j) (Q.ν j))
    (hσ : Q.HasLimit (centredOf S)) {E : LawConstants}
    (hE : E.SideConditions) (hϑ : ϑ ∈ Ioc (0 : ℝ) 1)
    (hshape : ϑ ≤ TwoPoints.Shapes.shapeConst)
    (hlaw : ∀ {τ : TupleFunctional} (Q' : WindowStates F), Q'.HasLimit τ →
      TwoPointLawHoldsAt ϑ (existentialConditionConstants F.M N E) τ) :
    TwoPointLawHoldsAt ϑ (existentialConditionConstants F.M N E) (centredOf S) ∧
      (∀ d ∈ Ioc (0 : ℝ) E.d₀, ∀ X : SepTupleOfCard 2,
        (X.1 0, X.1 1) ∈ TestFunctions.separatedPairsR4 d ϑ → 0 < S 2 le_rfl X) ∧
      (∀ h : IsPosSemidef (reflectionForm (centredOf S)),
        2 ≤ Module.rank ℂ (PhysicalSpace (centredOf S) h)) ∧
      ∀ A' : DecompositionData, A'.IsCanonical (centredOf S) →
        ∀ ξ, TwoPointLawHoldsAt ϑ (existentialConditionConstants F.M N E) (A'.comp ξ) := by
  have hpos : ∀ d ∈ Ioc (0 : ℝ) E.d₀, ∀ X : SepTupleOfCard 2,
      (X.1 0, X.1 1) ∈ TestFunctions.separatedPairsR4 d ϑ → 0 < S 2 le_rfl X := by
    intro d hd X hX
    have hp := P.inherit.2.2 ϑ (existentialConditionConstants F.M N E) (centredOf S) hϑ hE.d₀_mem.2
      hE.ηBar_mem (hlaw Q hσ)
    obtain ⟨X', hX', hq⟩ := hp d hd (X.1 0) (X.1 1) hX (X.2.1 0).1 (X.2.1 1).1
    have e : X' = X := Subtype.ext (hX'.trans (by ext i; fin_cases i <;> rfl))
    subst e
    rw [← hS.2.2.2 2 le_rfl]
    exact hq
  refine ⟨hlaw Q hσ, hpos, two_le_rank_of_hasLimit P P' hPl hSm hS hσ hE hϑ hshape hpos, fun A' hA ξ => ?_⟩
  obtain ⟨Q', hl, -⟩ := exists_states_of_component P B hρν hvol hσ hA ξ
  exact hlaw Q' hl
end Assembly
end TheLimit
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
open ReflectionPositivity.TupleForm
open WindowLimits
open LimitTheorem
open SeparatedTuples hiding conjugation
section AtAFamily
variable {F : StatedSideFamily}
private def windowStatesOf (Q : ApproximatingSequence F) : WindowStates F where
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
variable (P' : SecondaryInputs)
include P' in
private theorem hasLimit_of_defines {Q : ApproximatingSequence F} {S : CumulantFamily} (hQ : Q.Defines S) :
    LimitTheorem.CutoffRepresentatives.CentredSymmetriesAndCumulants S ∧
      (windowStatesOf Q).HasLimit (centredOf S) := by
  obtain ⟨-, h2, h3⟩ := P'.ident F.L F.admissible Q.cutoff Q.state (fun j => (Q.mem_gibbs j).1.1) S
  exact ⟨h3, h2.1 hQ⟩
end AtAFamily
private structure FinalInputs : Prop where
  one : Continuum.UnifiedTestSpace.TestSpacesUnified
  two : ConfigurationSpace.SmoothSubspaces
  plates : TwoPoints.TestPlates.TestPlatePieces.Statement
  smaller : TwoPoints.SmallerShape.Statement
variable (P : PrimaryInputs) (P' : SecondaryInputs) (P'' : FinalInputs) (M : ℝ) (N : BoundConstants)
include P P' P'' in
private theorem baseBoundsAt_existentialConstants : BaseConditionsAt M N (existentialConstants M N) := by
  rintro F rfl B Q S hQ
  obtain ⟨h3, hσ⟩ := hasLimit_of_defines P' hQ
  have cl := conditionsAtConstants_of P P' B P''.one P''.two h3 rfl Q.isLimit hσ
  exact ⟨cl.symmetries, cl.coordinateMirrors, cl.distributions, cl.perBall _, cl.growth _, cl.reconstruction,
    cl.connected_eq, cl.diagonalMirrors, cl.bounds, cl.decomposition, cl.componentSymmetries,
    cl.componentOnePoint, fun A hA ξ => cl.componentPerBall A hA ξ _,
    fun A hA ξ => cl.componentGrowth A hA ξ _, cl.componentReconstruction, cl.componentClusters⟩
include P P' P'' in
private theorem lawConditionsAt_existentialConstants : LawConditionsAt M N (existentialConstants M N) := by
  rintro F rfl B ϑ hϑ hshape hT Q S hQ
  obtain ⟨h3, hσ⟩ := hasLimit_of_defines P' hQ
  obtain ⟨h₁, h₂, h₃, h₄⟩ := lawConditions_of P P' B P''.plates P''.smaller h3 rfl Q.isLimit hσ
    (lawConstantsOf_sideConditions B.admissible_constants) hϑ hshape
    (fun Q' hl => twoPointLaw_of_hasLimit P Q' hT hl _)
  exact ⟨h₁, h₂, h₃, h₄⟩
end SystemsWithFiveBounds
end
end
noncomputable section
namespace SystemsWithFiveBounds
theorem baseAndLawBoundsAtExistentialConstants_of
    (h1 : SystemsWithFiveBounds.WindowLimitProperties)
    (h2 : SystemsWithFiveBounds.CanonicalDecompositionOfLimits)
    (h3 : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (h4 : ReflectionPositivity.LimitReconstruction.LimitReconstructionTheorem)
    (h5 : ReflectionPositivity.LimitMomentumBound.MomentumBoundTheorem)
    (h6 : SystemsWithFiveBounds.GibbsLimitInheritance.InheritanceTheorem)
    (h7 : ClusterMoments.IteratedLimitIsMoment)
    (h8 : Continuum.TwoPresentations.PresentationsAgree)
    (h9 : TestSpaces.OffDiagonal.OffDiagonalFacts)
    (h10 : CanonicalDecompositionUniqueness.DecompositionDeterminations)
    (h11 : LimitTheorem.DecompositionTransfer.TransferStatement)
    (h12 : GeneratorsAndFlows.GeneratorFlowTheorem)
    (h13 : ReflectionPositivity.ShiftSpectralMeasure.ShiftSpectralMeasureTheorem)
    (h14 : LimitTheorem.CutoffRepresentatives.IdentificationsHold)
    (h15 : SystemsWithFiveBounds.LimitGrowthAtConstants)
    (h16 : Scales.SeparatedPairsAreTestFunctionsStatement)
    (h17 : Continuum.UnifiedTestSpace.TestSpacesUnified)
    (h18 : ConfigurationSpace.SmoothSubspaces)
    (h19 : TwoPoints.TestPlates.TestPlatePieces.Statement)
    (h20 : TwoPoints.SmallerShape.Statement) :
    BaseAndLawConditionsAtExistentialConstants :=
  have P : PrimaryInputs :=
    { bounded := h3, reconstruction := h4, cone := h5, inherit := h6, moments := h7,
      presentations := h8, offDiagonal := h9, determines := h10, transfer := h11, generators := h12,
      windowConditions := h1, decompositionConditions := h2 }
  have P' : SecondaryInputs := { semigroup := h13, ident := h14, limitGrowth := h15, pair := h16 }
  have P'' : FinalInputs := { one := h17, two := h18, plates := h19, smaller := h20 }
  fun M N => ⟨baseBoundsAt_existentialConstants P P' P'' M N, lawConditionsAt_existentialConstants P P' P'' M N⟩
end SystemsWithFiveBounds
end
end YangMills.Construction
