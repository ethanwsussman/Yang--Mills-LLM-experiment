import YangMills.Construction.Continuum.TwoPresentationsOfTheSpaceOfAFamilyOfConnectedFunctions
import YangMills.Construction.GrowingTori.SetsOfConvergenceOfASequenceWithGrowingTori
import YangMills.Construction.GrowingTori.ThreeWaysOfSpeakingOfHierarchiesOnFourSpace
import YangMills.Construction.TorusOrFourSpace.MembersOfALimitOnFourSpaceAsDistributions
import Mathlib
set_option autoImplicit false
open Set
open scoped NNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits
open PeriodicSpace TorusTransport.TestFunctionOrders
open ReflectionSpaces (finiteUpperSequences)
open TimeAxisSymbols (spaceTimePoint timeAxisStabilizer timeAxisVec)
open PeriodicSpace.Kind.EuclideanLimitDistributions (HasMemberValues)
open PositiveFormReconstruction
open FormsOperators (IsHilbertCompletion HasCountableDenseSet formRadical formOnQuotient)
open Sequences (PNatIndexSet)
variable {D : Setup}
structure IsAdmissibleAlongSeq (S : ToriSequence D) (n : ℕ) (d R C : ℝ) : Prop where
  nonneg : 0 ≤ C
  bound : ∀ j, 16 * (n : ℝ) * (1 + R) ≤ S.side j →
    ∀ f ∈ AmbientPoints.sepLipTuples (D.params.toGrowth.standingParams (S.K j) (S.m j)) .torus n,
      AmbientPoints.SupportsInBalls R f → ENNReal.ofReal d ≤ AmbientPoints.supportGap f →
      ‖SchwingerFunctions.connectedSchwinger D.L (S.m j) (S.K j) (S.β j) f‖ ≤
        C * ∏ i, D.params.sharpNormTorus (f i)
def HasBallwiseBoundAlong (S : ToriSequence D) (C : BoundFamily) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → IsAdmissibleAlongSeq S n d R (C.val n d R)
def EventuallyObeys (S : ToriSequence D) (C : BoundFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : 0 < R) (j₀ : ℕ+), S.IsSideIndex n R j₀ →
    ∀ j, j₀ ≤ j → ∀ (d : ℝ) (hd : 0 < d) (f : Fin n → RealFn),
      f ∈ lipTuples n hn d R hd hR → S.Defined f j →
        ‖S.connected j f‖ ≤ C.val n d R * ∏ i, TestFunctions.sharpNormR4 (D.M : ℝ) (f i)
abbrev IsMemberDistrib (Ξ : D.LimitHierarchy) (n : ℕ+) (hn : 2 ≤ (n : ℕ))
    (T : Kind.Tuple.testFns D.euclidParams Kind.euclidean
      (Kind.pairwiseDistinct D.euclidParams Kind.euclidean n) → ℂ) : Prop :=
  HasMemberValues Ξ hn T
def MembersAreDistribs (Ξ : D.LimitHierarchy) : Prop :=
  ∀ (n : ℕ+) (hn : 2 ≤ (n : ℕ)),
    (∃! T, IsMemberDistrib Ξ n hn T) ∧
    ∀ T, IsMemberDistrib Ξ n hn T →
      Kind.Tuple.IsDistribOfOrderLE (5 * (n : ℕ) + 1) T ∧
      ∀ (U : Set (Kind.euclidean.Tuple D.euclidParams n))
        (hU : U ⊆ Kind.pairwiseDistinct D.euclidParams Kind.euclidean n),
        Kind.Tuple.IsOpenT D.euclidParams Kind.euclidean U →
          Kind.Tuple.HasOrderLEOn hU (5 * (n : ℕ) + 1) T
def IsPauliCoordinate {n : ℕ+} (v : ReflectionSpaces.Euclidean.Distribution
      (Continuum.BlockProducts.configSpace (n : ℕ)))
    (T : Kind.Tuple.testFns D.euclidParams Kind.euclidean
      (Kind.pairwiseDistinct D.euclidParams Kind.euclidean n) → ℂ) : Prop :=
  ∀ (G : Kind.euclidean.Tuple D.euclidParams n → ℂ)
    (hG : G ∈ Kind.Tuple.testFns D.euclidParams Kind.euclidean
      (Kind.pairwiseDistinct D.euclidParams Kind.euclidean n))
    (hG' : (fun x => G (Continuum.BlockProducts.pointAt x)) ∈
      ReflectionSpaces.Euclidean.testFunctionSpace
        (Continuum.BlockProducts.configSpace (n : ℕ))),
    v.form ⟨_, hG'⟩ = T ⟨G, hG⟩
def IsMemberFamily (Ξ : D.LimitHierarchy) (u : Continuum.BlockProducts.DistribFamily) : Prop :=
  ∀ (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (T), IsMemberDistrib Ξ n hn T → IsPauliCoordinate (u n hn) T
structure ExistenceAndBounds (S : ToriSequence D) (C : BoundFamily)
    (J : PNatIndexSet) (Ξ : D.LimitHierarchy) : Prop where
  isLimitHierarchy : S.IsLimitHierarchy J Ξ
  terms_defined : ∀ (n : ℕ), 2 ≤ n → ∀ (f : D.sepDomain n) (ρ : ℝ), 0 < ρ →
    SuppsWithin f.1 (ballOrigin ρ) → ∀ j, 2 * ρ + 2 ≤ (D.L : ℝ) ^ (S.m j : ℕ) → S.Defined f.1 j
  mem_boundedEuclidHierarchies : Ξ ∈ boundedEuclidHierarchies D.euclidParams C
  equicontinuous : HierarchyEquicontinuous Ξ C
  bound_of_admissible : ∀ (n : ℕ) (hn : 2 ≤ n) (d R : ℝ) (hd : 0 < d) (hR : 0 < R) (C' : ℝ),
    IsAdmissibleAlongSeq S n d R C' →
    ∀ f : D.sepDomain n, f.1 ∈ lipTuples n hn d R hd hR →
      |Ξ.func n hn f| ≤ C' * ∏ i, TestFunctions.sharpNormR4 (D.M : ℝ) (f.1 i)
  membersAreDistribs : MembersAreDistribs Ξ
  exists_memberFamily : ∃ u, IsMemberFamily Ξ u
structure Symmetries (C : BoundFamily) (Ξ : D.LimitHierarchy) : Prop where
  shift_invariant : ∀ (n : ℕ) (hn : 2 ≤ n) (f : D.sepDomain n) (a : Fin 4 → ℝ),
    Ξ.evalSigma ⟨n, GrowingTori.shiftFamily a f.1⟩ = Ξ.func n hn f
  hyperoctahedral_invariant : ∀ (n : ℕ) (hn : 2 ≤ n) (f : D.sepDomain n)
    (w : TorusTransport.hyperoctahedral),
    Ξ.evalSigma ⟨n, GrowingTori.hyperoctahedralActFamily w f.1⟩ = Ξ.func n hn f
  perm_invariant : ∀ (n : ℕ) (hn : 2 ≤ n) (f : D.sepDomain n) (σ : Equiv.Perm (Fin n)),
    Ξ.evalSigma ⟨n, fun i => f.1 (σ i)⟩ = Ξ.func n hn f
  distribs_invariant : ∀ (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (T), IsMemberDistrib Ξ n hn T →
    (∀ σ : Equiv.Perm (Fin (n : ℕ)), Kind.InvariantUnder (D := D.euclidParams) (E := Kind.euclidean)
      (fun x i => x (σ i)) T) ∧
    ∀ s : TorusPeriodization.euclideanMotions, Kind.InvariantUnder (D := D.euclidParams)
      (E := Kind.euclidean) (fun (x : Fin (n : ℕ) → Fin 4 → ℝ) i => s.1 (x i)) T
  shiftEstimate : ∀ (n : ℕ) (hn : 2 ≤ n), SatisfiesShiftEstimate D C Ξ hn
def reflectionPairing (Ξ : D.LimitHierarchy) (F F' : finiteUpperSequences D.euclidParams) : ℂ :=
  reflectionForm Ξ 3 0 F.1 F'.1
namespace LatticeLevel
variable (S : ToriSequence D)
abbrev momentDataAt (j : ℕ+) : CentredTensorMoments.MomentData :=
  D.momentSetup (S.K j) (S.m j) (S.β j) (S.β_pos j)
def seqPolynomial (j : ℕ+) (F : TestFamily) : (momentDataAt S j).BondField → ℂ :=
  fun U => ∑ᶠ q : ℕ, D.centredPolynomial (S.K j) (S.m j) (S.β j) (S.β_pos j) (F q) U
abbrev ReflectionIsSymmetryAt (j : ℕ+) : Prop :=
  (momentDataAt S j).ReflectionIsSymmetry 3 (S.spacing j / 2)
def reflectedPairingAt (j : ℕ+) (h : ReflectionIsSymmetryAt S j) (F F' : TestFamily) : ℂ :=
  S.expectation j fun U =>
    conj ((momentDataAt S j).compPullback h.toSymmetry (seqPolynomial S j F) U) *
      seqPolynomial S j F' U
end LatticeLevel
structure OSPositivity (S : ToriSequence D) (J : PNatIndexSet)
    (Ξ : D.LimitHierarchy) : Prop where
  moments_tendsto : ∀ (q : ℕ) (F : OrderedTestFun q),
    F ∈ sepTensorSubmodule D.euclidParams Set.univ q →
    DiagonalLimits.TendsToWhereDefined J (fun _ => True)
      (fun j _ => S.tensorMoment j F) (momentExtensionAt Ξ ⟨q, F⟩)
  form_eq_limit : ∀ F F' : finiteUpperSequences D.euclidParams,
    DiagonalLimits.TendsToWhereDefined J (LatticeLevel.ReflectionIsSymmetryAt S)
      (fun j h => LatticeLevel.reflectedPairingAt S j h F.1 F'.1) (reflectionPairing Ξ F F')
  holdsAtMirrors : ∀ u, IsMemberFamily Ξ u → ∀ (μ : Fin 4) (c : ℝ), ReflectionPositiveAt Ξ u μ c
def timeTranslateSeq (t : ℝ≥0) (F : TestFamily) : TestFamily :=
  ReflectionSpaces.composeFamily (fun _ x i => x i - (t : ℝ) • timeAxisVec) F
def spaceTranslateSeq (a : Fin 3 → ℝ) (F : TestFamily) : TestFamily :=
  ReflectionSpaces.composeFamily (fun _ x i => x i - spaceTimePoint a 0) F
structure IsReconstructionData (Ξ : D.LimitHierarchy)
    (V : PreHilbertData (finiteUpperSequences D.euclidParams)) : Prop where
  form_eq : V.form = reflectionPairing Ξ
  unitVec_eq : V.unitVec = OSSpaces.vacuumSequence D.euclidParams
  semigroupMap_eq : ∀ t F, (V.semigroupMap t F).1 = timeTranslateSeq t F.1
  translationMap_eq : ∀ a F, (V.translationMap a F).1 = spaceTranslateSeq a.ofLp F.1
  rotationMap_eq : ∀ w F, (V.rotationMap w F).1 = SymbolSequences.rotateFamily w F.1
def OSReconstruction (Ξ : D.LimitHierarchy) : Prop :=
  ∃ (V : PreHilbertData (finiteUpperSequences D.euclidParams)) (hV : V.IsAdmissible),
    IsReconstructionData Ξ V ∧
    QuotientInnerProduct V hV.hermitian.toIsSesquilinear ∧
    SemigroupMapsContract V hV.hermitian.toIsSesquilinear ∧
    (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ι : (finiteUpperSequences D.euclidParams ⧸
        formRadical V.form hV.hermitian.toIsSesquilinear) →ₗ[ℂ] H),
      IsHilbertCompletion (formOnQuotient V.form hV.hermitian.toIsSesquilinear) ι) ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ι : (finiteUpperSequences D.euclidParams ⧸
        formRadical V.form hV.hermitian.toIsSesquilinear) →ₗ[ℂ] H),
      IsHilbertCompletion (formOnQuotient V.form hV.hermitian.toIsSesquilinear) ι →
      HasCountableDenseSet H ∧ ‖vacuum V hV.hermitian.toIsSesquilinear ι‖ = 1 ∧
      TransferSemigroupCondition V hV.hermitian.toIsSesquilinear ι ∧
      TranslationCondition V hV.hermitian.toIsSesquilinear ι ∧
      RotationUnitarity V hV.hermitian.toIsSesquilinear ι
structure LimitRequirements (S : ToriSequence D) (C : BoundFamily) (J : PNatIndexSet)
    (Ξ : D.LimitHierarchy) : Prop where
  existenceAndBounds : ExistenceAndBounds S C J Ξ
  symmetries : Symmetries C Ξ
  osPositivity : OSPositivity S J Ξ
  reconstruction : OSReconstruction Ξ
def Holds : Prop :=
  ∀ (D : Setup) (S : ToriSequence D) (C : BoundFamily), HasBallwiseBoundAlong S C →
    EventuallyObeys S C ∧
    (∀ B : BoundedFamily, ∃ J, S.IsConvergenceSetWith C B J) ∧
    ∀ (J : PNatIndexSet) (Ξ : D.LimitHierarchy), S.IsConvergenceSet C J → S.IsLimitHierarchy J Ξ →
      LimitRequirements S C J Ξ
end YangMills.Construction.ToriLimits.GrowingVolumeLimits
end
