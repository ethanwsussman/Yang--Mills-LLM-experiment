import YangMills.Construction.Continuum.DistributionsOnPowersOfFourSpaceReadInCoordinates
import YangMills.Construction.Continuum.ElementaryFactsOnDistributions
import YangMills.Construction.GrowingTori.CalculusOfTheCentredLatticePolynomials
import YangMills.Construction.GrowingTori.InducedIsometriesNestedLatticesAndTheMirrorsOfATorus
import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes
import YangMills.Construction.GrowingTori.MultilinearityOnADomainThatIsNotLinear
import YangMills.Construction.GrowingTori.RadiiCentredMomentsAndConnectedFunctions
import YangMills.Construction.GrowingTori.SubFamiliesNeighbourhoodsAndTheSeparation
import YangMills.Construction.GrowingTori.TransportThroughABallToTheTorusOfAnExponent
import YangMills.Construction.HilbertSpaces.ReconstructionFromAPositiveForm
import YangMills.Construction.TorusOrFourSpace.CentredMomentsOfBoundedForms
import YangMills.Construction.TorusOrFourSpace.CountableFamilyOfACountableChoice
import YangMills.Construction.TorusOrFourSpace.DistinctPointsAndProductsOfAdmissibleFamilies
import YangMills.Construction.TorusOrFourSpace.EquicontinuityCompactnessAndExtractionOfSubsequences
import YangMills.Construction.TorusOrFourSpace.FamiliesOfDenseSetsAndMembersOfTheFamily
import YangMills.Construction.TorusOrFourSpace.TensorsOfSeparatedTuplesSpanADenseSubspace
import Mathlib
set_option autoImplicit false
open Set
open scoped NNReal ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps
open PeriodicSpace TorusTransport.TestFunctionOrders
open ReflectionSpaces (finiteUpperSequences)
structure CitedFacts : Prop where
  cumulants : MomentsAndConnected.Statement
  transport : ExponentTorusPeriodization.Statement
  multilinear : NonlinearDomain.Statement
  collars : SubfamiliesAndGaps.Statement
  extension : TensorExtension.Holds
  polynomials : LatticePolynomialCalculus.Holds
  nesting : GrowingTori.LatticeMotions.motions_lattices_mirrors
  elementary : DistributionBasics.ElementaryFacts
  product : Continuum.TensorProduct.TensorProductExistsUnique
  functionals : CentredTensorMoments.TorusFunctionals.Statement
  moments : PeriodicSpace.Kind.CentredMoments.Statement
  density : PeriodicSpace.DenseTensorSpan.DensityStatement
  distributions : PeriodicSpace.Kind.EuclideanLimitDistributions.LimitMembersAreDistributions
  symbols : TimeAxisSymbols.MomentFunctionals.Statement
  reconstruction : PositiveFormReconstruction.ReconstructionStatement
  compactness : PeriodicSpace.EquicontinuityCompactness.Statement
  translations : EuclideanSymmetryFacts.Statement
  countableFamily : PeriodicSpace.CountableChoiceFamilyFacts
variable {D : Setup}
abbrev pnatIndices : Sequences.PNatIndexSet := C1FormSeqKinds.allPNat
def radiusSeq (S : ToriSequence D) : pnatIndices.carrier → ℝ≥0∞ :=
  fun j => ENNReal.ofReal (S.radius j.1)
def IsPartialHierarchySeqOf (S : ToriSequence D) (C : BoundFamily)
    (Ψ : Kind.BoundedPartialHierarchySeq D.euclidParams .euclidean pnatIndices (radiusSeq S) C) :
    Prop :=
  ∀ (j : pnatIndices.carrier) (n : ℕ) (hn : 2 ≤ n)
    (f : Kind.sepLipTuplesWithin D.euclidParams .euclidean n
      (Kind.centredBall D.euclidParams .euclidean (radiusSeq S j))),
    ((Ψ.func j n hn f : ℝ) : ℂ) = S.connected j.1 f.1
structure CentredMomentsConverge (S : ToriSequence D) (J : Sequences.PNatIndexSet)
    (Ξ : D.LimitHierarchy) : Prop where
  atFixed : ∀ (q : ℕ) (h : D.sepDomain q),
    DiagonalLimits.TendsToWhereDefined J
      (fun j => h.1 ∈ sepLipTuplesInBall q (S.radius j) (S.radius_pos j))
      (fun j _ => S.centred j h.1) ((Ξ.partitionMoment h : ℝ) : ℂ)
  atMoving : ∀ (q : ℕ), 1 ≤ q → ∀ (d R : ℝ), 0 < d → 0 < R →
    ∀ A : Fin q → Set (Fin 4 → ℝ),
    Kind.SetsInBallsSeparated D.euclidParams .euclidean d R A →
    ∀ (h : D.sepDomain q) (H : ℕ+ → Fin q → RealFn),
      h.1 ∈ Kind.productSet D.euclidParams .euclidean
        (fun l => Kind.c1SupportedIn D.euclidParams .euclidean (A l)) →
      (∀ j, H j ∈ Kind.productSet D.euclidParams .euclidean
        (fun l => Kind.c1SupportedIn D.euclidParams .euclidean (A l))) →
      (∀ l, ∀ ε : ℝ, 0 < ε → DiagonalLimits.EventuallyAlong J fun j =>
        (Kind.sharpNormQ D.euclidParams .euclidean (H j l - h.1 l)).toReal < ε) →
      DiagonalLimits.TendsToWhereDefined J
        (fun j => H j ∈ sepLipTuplesInBall q (S.radius j) (S.radius_pos j))
        (fun j _ => S.centred j (H j)) ((Ξ.partitionMoment h : ℝ) : ℂ)
abbrev symbolSetup (D : Setup) : TorusTransport.TransportData := D.transportData 1 1
abbrev symbolMoments (Ξ : D.LimitHierarchy) : TimeAxisSymbols.SpaceTimeSymbol (symbolSetup D) → ℝ :=
  SymbolSequences.momentOnSymbol Ξ
def momentBoundNN (C : BoundFamily) (k : ℕ+) (d R : ℝ) : ℝ≥0 :=
  Real.toNNReal (momentBoundSum C k d R)
def ReflectionPositive (Ξ : D.LimitHierarchy) : Prop :=
  ∀ F : finiteUpperSequences D.euclidParams, IsNonnegComplex (reflectionPairing Ξ F F)
def MemberDistribsInvariant (Ξ : D.LimitHierarchy) : Prop :=
  ∀ (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (T), IsMemberDistrib Ξ n hn T →
    (∀ σ : Equiv.Perm (Fin (n : ℕ)), Kind.InvariantUnder (D := D.euclidParams)
      (E := Kind.euclidean) (fun x i => x (σ i)) T) ∧
    ∀ s : Kind.euclidean.Pt D.euclidParams → Kind.euclidean.Pt D.euclidParams,
      Kind.IsIsometry D.euclidParams Kind.euclidean s →
      (∀ (φ : Kind.sepC1Tuples D.euclidParams Kind.euclidean (n : ℕ))
          (h : Kind.compEach φ.1 s ∈ Kind.sepC1Tuples D.euclidParams Kind.euclidean (n : ℕ)),
        Ξ.func (n : ℕ) hn ⟨_, h⟩ = Ξ.func (n : ℕ) hn φ) →
      Kind.InvariantUnder (D := D.euclidParams) (E := Kind.euclidean)
        (fun x i => s (x i)) T
structure MomentLinearExtension (Ξ : D.LimitHierarchy) : Prop where
  at_zero : ∀ c : OrderedTestFun 0, momentExtensionAt Ξ ⟨0, c⟩ = c
  at_tensor : ∀ (q : ℕ) (X : D.sepDomain (q + 1)),
    momentExtensionAt Ξ ⟨q + 1, TensorExtension.realTensor D.euclidParams X.1⟩ =
      ((Ξ.partitionMoment X : ℝ) : ℂ)
  is_linear : ∀ (q : ℕ) (F G : OrderedTestFun q) (a b : ℂ),
    F ∈ sepTensorSubmodule D.euclidParams Set.univ q →
    G ∈ sepTensorSubmodule D.euclidParams Set.univ q →
    momentExtensionAt Ξ ⟨q, a • F + b • G⟩ =
      a * momentExtensionAt Ξ ⟨q, F⟩ + b * momentExtensionAt Ξ ⟨q, G⟩
structure SymbolPairingMatches (Ξ : D.LimitHierarchy) : Prop where
  surjective : Function.Surjective
    (SymbolSequences.spanSequence (D := symbolSetup D) D.euclidParams)
  pairing_eq : ∀ X Y : TimeAxisSymbols.PosSymbolSpan (symbolSetup D),
    reflectionPairing Ξ (SymbolSequences.spanSequence D.euclidParams X)
        (SymbolSequences.spanSequence D.euclidParams Y) =
      TimeAxisSymbols.osForm (symbolMoments Ξ) X Y
namespace ExistencePart
section
open AmbientPoints in
theorem mem_sepLipTuples_of_mem_lipTuplesTorus (D : Setup) (K : ℕ+)
    (m : ℕ+) {n : ℕ} (hn : 2 ≤ n) {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (hRm : R < (D.L : ℝ) ^ (m : ℕ) / 2)
    {g : Fin n → PeriodicLattice.FourTorus D.L m → ℝ}
    (hg : g ∈ lipTuplesTorus (ExponentTorusPeriodization.gluingSetup D m) m n hn d R
      hd hR hRm) :
    g ∈ sepLipTuples (D.params.toGrowth.standingParams K m) .torus n ∧
      SupportsInBalls (s := D.params.toGrowth.standingParams K m) (E := .torus) R g ∧
      ENNReal.ofReal d ≤ AmbientPoints.supportGap (s := D.params.toGrowth.standingParams K m)
        (E := .torus) g := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hs : ∀ i, (SourcesAndGluing.Ambient.torus m).supp
      (ExponentTorusPeriodization.gluingSetup D m) (g i) =
      @tsupport (Pt (D.params.toGrowth.standingParams K m) .torus) ℝ _ _ (g i) := fun i =>
    (AmbientPoints.closure_eq_closureWrt
      (X := Pt (D.params.toGrowth.standingParams K m) .torus) {u | g i u ≠ 0}).symm
  have hcompact : CompactSpace (Pt (D.params.toGrowth.standingParams K m) .torus) := by
    have : Fact (0 < PeriodicLattice.torusSide (D.params.toGrowth.standingParams K m).L
        (D.params.toGrowth.standingParams K m).m) := ⟨by
      have hL : 0 < (D.params.toGrowth.standingParams K m).L := by
        have := (D.params.toGrowth.standingParams K m).isAdmissible.2
        omega
      simp only [PeriodicLattice.torusSide]
      positivity⟩
    exact (homeomorphTorus _).symm.compactSpace
  have hsep : ∀ i k, i ≠ k → ENNReal.ofReal d ≤
      AmbientPoints.setDist (D.params.toGrowth.standingParams K m) .torus
        (@tsupport (Pt (D.params.toGrowth.standingParams K m) .torus) ℝ _ _ (g i))
        (@tsupport (Pt (D.params.toGrowth.standingParams K m) .torus) ℝ _ _ (g k)) := by
    intro i k hik
    rw [← hs, ← hs]
    exact h3 i k hik
  refine ⟨⟨fun i => h1 i, fun i => isClosed_closure.isCompact, fun i k hik => ?_⟩, fun i => ?_, ?_⟩
  · refine Set.disjoint_left.2 fun x hi hk => ?_
    have h := hsep i k hik
    have h0 : AmbientPoints.setDist (D.params.toGrowth.standingParams K m) .torus
        (@tsupport (Pt (D.params.toGrowth.standingParams K m) .torus) ℝ _ _ (g i))
        (@tsupport (Pt (D.params.toGrowth.standingParams K m) .torus) ℝ _ _ (g k)) ≤ 0 := by
      refine (iInf₂_le x hi).trans ((iInf₂_le x hk).trans ?_)
      simp [pointDist_self]
    have : ENNReal.ofReal d ≤ 0 := h.trans h0
    simp only [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
    linarith
  · obtain ⟨x, hx⟩ := h2 i
    refine ⟨x, ?_⟩
    rw [← hs]
    exact hx
  · exact le_iInf fun i => le_iInf fun k => le_iInf fun hik => hsep i k hik
theorem radius_lt_half_pow_of_torusSide_ge {L : ℕ} {m : ℕ} {n : ℕ} (hn : 2 ≤ n) {R : ℝ}
    (hR : 0 < R) (h : 16 * (n : ℝ) * (1 + R) ≤ PeriodicLattice.torusSide L m) :
    R < (L : ℝ) ^ m / 2 := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : 16 * 2 * (1 + R) ≤ 16 * (n : ℝ) * (1 + R) := by nlinarith
  have h4 : PeriodicLattice.torusSide L m = 2 * (L : ℝ) ^ m := rfl
  rw [h4] at h
  nlinarith
variable (S : ToriSequence D)
theorem norm_connected_le_of_admissible (h : CitedFacts) {n : ℕ} (hn : 2 ≤ n) {d R c : ℝ}
    (hd : 0 < d) (hR : 0 < R)
    (hc : IsAdmissibleAlongSeq S n d R c) {j : ℕ+}
    (hs : 16 * (n : ℝ) * (1 + R) ≤ S.side j) {f : Fin n → RealFn}
    (hf : f ∈ lipTuples n hn d R hd hR) (hg : S.Defined f j) :
    ‖S.connected j f‖ ≤ c * ∏ i, TestFunctions.sharpNormR4 (D.M : ℝ) (f i) := by
  have hρ := S.radius_pos j
  have hg' : f ∈ sepLipTuplesInBall n (S.radius j) hρ := by
    rw [sepLipTuplesInBall_eq_lipTuplesInBall D.L (by omega) _ hρ]
    exact hg
  obtain ⟨hsepF, hsupp⟩ := hg'
  have hRm := radius_lt_half_pow_of_torusSide_ge hn hR hs
  obtain ⟨-, hFun, hTup⟩ := (h.transport D (S.m j)).2 (S.radius j) hρ le_rfl
  obtain ⟨-, -, -, -, -, hclass⟩ := hTup n hn f hsepF hsupp
  have hmem := hclass d R hd hR hRm hf
  obtain ⟨hg1, hg2, hg3⟩ :=
    mem_sepLipTuples_of_mem_lipTuplesTorus D (S.K j) (S.m j) hn hd hR hRm hmem
  have hb := hc.bound j hs _ hg1 hg2 hg3
  have hnorm : ∀ i, D.params.sharpNormTorus
      (SchwingerFunctions.periodizeAll D.L (S.m j) f i) =
      TestFunctions.sharpNormR4 (D.M : ℝ) (f i) := by
    intro i
    exact ((hFun ℝ).2.1 (f i) ⟨hsepF.2.1 i, hsupp i⟩ (fun _ => rfl) (hsepF.1 i)).2.2.2.2
  refine le_trans hb (le_of_eq ?_)
  congr 1
  exact Finset.prod_congr rfl fun i _ => hnorm i
theorem eventuallyObeys_of_ballwise (h : CitedFacts) (C : BoundFamily)
    (hC : HasBallwiseBoundAlong S C) : EventuallyObeys S C := by
  intro n hn R hR j₀ hj₀ j hj d hd f hf hg
  exact norm_connected_le_of_admissible S h hn hd hR (hC n hn d R hd hR) (hj₀ j hj) hf hg
theorem exists_lt_radiusFn (h : CitedFacts) (ρ : ℝ) : ∃ jρ : ℤ, ∀ j : pnatIndices.carrier,
    jρ ≤ (((j.1 : ℕ+) : ℕ) : ℤ) → ρ < S.radius j.1 := by
  obtain ⟨-, hlim, -⟩ := (h.cumulants D S).1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim.eventually_gt_atTop ρ)
  refine ⟨((N : ℕ) : ℤ), fun j hj => hN j.1 ?_⟩
  exact_mod_cast hj
theorem mem_sepLipTuplesWithin_centredBall_iff (h : CitedFacts) {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ}
    (hρ : 0 < ρ) (f : Fin n → RealFn) :
    f ∈ Kind.sepLipTuplesWithin D.euclidParams .euclidean n
        (Kind.centredBall D.euclidParams .euclidean (ENNReal.ofReal ρ)) ↔
      f ∈ GrowingTori.lipTuplesInBall D.L n ρ := by
  have hM := h.multilinear (symbolSetup D)
  obtain ⟨-, -, -, -, -, -, -, -, hY⟩ := hM
  obtain ⟨-, -, hcl, -, -, -⟩ := hY D.euclidParams rfl
  have h1 := hcl (.ball ρ hρ) n hn
  have h2 := sepLipTuplesInBall_eq_lipTuplesInBall D.L hn ρ hρ
  have h3 : (TestTupleClass.ball ρ hρ).members (symbolSetup D).toStandingParameters n =
      sepLipTuplesInBall n ρ hρ := rfl
  have h4 : (TestTupleClass.ball ρ hρ).periodicClass D.euclidParams n =
      Kind.sepLipTuplesWithin D.euclidParams .euclidean n
        (Kind.centredBall D.euclidParams .euclidean (ENNReal.ofReal ρ)) := rfl
  have h5 : Kind.sepLipTuplesWithin D.euclidParams .euclidean n
        (Kind.centredBall D.euclidParams .euclidean (ENNReal.ofReal ρ)) =
      GrowingTori.lipTuplesInBall D.L n ρ := by
    rw [← h4, ← h1, h3, h2]
  rw [h5]
  exact Iff.rfl
theorem exists_partialHierarchySeq (h : CitedFacts) (C : BoundFamily)
    (hC : HasBallwiseBoundAlong S C) : ∃ Ψ, IsPartialHierarchySeqOf S C Ψ := by
  obtain ⟨-, -, -, -, -, hPH⟩ := h.cumulants D S
  choose Φ hΦ hΦc using hPH
  let W : ExplicitPartialHierarchySeq D.L pnatIndices (fun j => S.radius j.1) :=
    ⟨fun ρ _ => exists_lt_radiusFn S h ρ, fun j => Φ j.1⟩
  obtain ⟨-, -, -, -, -, -, -, -, hY⟩ := h.multilinear (symbolSetup D)
  obtain ⟨-, -, -, -, -, hSeq⟩ := hY D.euclidParams rfl
  obtain ⟨e, he⟩ := hSeq pnatIndices (fun j => S.radius j.1)
  obtain ⟨hagree, hfrom, -, -⟩ := he (e.symm W)
  have hW : e (e.symm W) = W := e.apply_symm_apply W
  rw [hW] at hagree
  have hfrom' : ∀ (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : 0 < R),
      (e.symm W).BoundedFrom C n hn R (((S.firstIndex n R : ℕ+) : ℕ) : ℤ) := by
    intro n hn R hR
    refine (hfrom C n hn R hR _).2 ?_
    rw [hW]
    intro j hj d hd f hf
    have hj' : S.firstIndex n R ≤ j.1 := by
      have : ((S.firstIndex n R : ℕ+) : ℕ) ≤ ((j.1 : ℕ+) : ℕ) := by exact_mod_cast hj
      exact this
    have hb := norm_connected_le_of_admissible S h hn hd hR (hC n hn d R hd hR)
      (S.isSideIndex_firstIndex n R j.1 hj') hf f.2
    have hval := hΦ j.1 n hn f
    have hval' : |(W.term j).phi n hn f| = ‖S.connected j.1 f.1‖ := by
      have h1 : ((W.term j).phi n hn f : ℂ) = S.connected j.1 f.1 := hval
      rw [← h1, Complex.norm_real, Real.norm_eq_abs]
    rw [hval']
    exact hb
  refine ⟨{ toPartialHierarchySeq := e.symm W
            threshold := fun n _ R _ => (((S.firstIndex n R : ℕ+) : ℕ) : ℤ)
            boundedFrom := fun n hn R hR => hfrom' n hn R hR }, ?_⟩
  intro j n hn f
  have hf : f.1 ∈ GrowingTori.lipTuplesInBall D.L n (S.radius j.1) :=
    (mem_sepLipTuplesWithin_centredBall_iff h (by omega) (S.radius_pos j.1) f.1).1 f.2
  have h1 := hagree j n hn f.1 f.2 hf
  have h2 := hΦ j.1 n hn ⟨f.1, hf⟩
  have h3 : (e.symm W).func j n hn f = (Φ j.1).phi n hn ⟨f.1, hf⟩ := h1
  show (((e.symm W).func j n hn f : ℝ) : ℂ) = _
  rw [h3]
  exact h2
end
structure LimitCitedFacts : Prop where
  families : PeriodicSpace.DenseFamilies.Claim
  covers : PeriodicSpace.TorusBallCoversAndPartitionsOfUnity
  evalOnSigma : CoordinateRepresentation.DistributionsReadInCoordinates
  distinct : Kind.AdmissibleProductFacts
section
variable (S : ToriSequence D)
def pnatIndex (j : ℕ+) : pnatIndices.carrier := ⟨j, Set.mem_univ j⟩
theorem mem_lipTuplesInBall_of_sepC1 {n : ℕ} (hn : 1 ≤ n)
    {f : Fin n → RealFn}
    (hf : f ∈ Kind.sepC1Tuples D.euclidParams .euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    (hs : SuppsWithin f (ballOrigin ρ)) : f ∈ GrowingTori.lipTuplesInBall D.L n ρ := by
  rw [← sepLipTuplesInBall_eq_lipTuplesInBall D.L hn ρ hρ]
  obtain ⟨h1, h2, h3⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff f).1 hf
  exact ⟨⟨fun i => lipschitzR4_of_contDiff (h1 i) (h2 i), h2, h3⟩, hs⟩
theorem suppsWithin_of_mem_sepC1TuplesInBall {n : ℕ} {f : Fin n → RealFn}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hf : f ∈ Kind.sepC1TuplesInBall D.euclidParams .euclidean n (ENNReal.ofReal ρ)) :
    SuppsWithin f (ballOrigin ρ) := by
  intro i
  have h := hf.2 i
  rw [← BallTuples.ballR4_eq_centredBall D.euclidParams hρ.le,
    BallTuples.supportQ_euclidean] at h
  exact h
theorem tendstoIn_of_tendsToOnSepAlong (h : CitedFacts) (C : BoundFamily)
    {Ψ : Kind.BoundedPartialHierarchySeq D.euclidParams .euclidean pnatIndices (radiusSeq S) C}
    (hΨ : IsPartialHierarchySeqOf S C Ψ) {J : Sequences.PNatIndexSet}
    {hJ : J.carrier ⊆ pnatIndices.carrier} {Ξ : D.LimitHierarchy}
    (hconv : Ψ.toPartialHierarchySeq.TendsToOnSepAlong J hJ Ξ) :
    S.IsLimitHierarchy J Ξ := by
  intro n hn f ε hε
  obtain ⟨j', hj'⟩ := hconv n hn f ε hε
  refine ⟨j', fun j hjJ hle => ?_⟩
  obtain ⟨⟨hj0, hdef⟩, hlt⟩ := hj' j hjJ hle
  have hg : f.1 ∈ GrowingTori.lipTuplesInBall D.L n (S.radius j) :=
    mem_lipTuplesInBall_of_sepC1 (by omega) f.2 (S.radius_pos j)
      (suppsWithin_of_mem_sepC1TuplesInBall (S.radius_pos j) hdef)
  have hY := (mem_sepLipTuplesWithin_centredBall_iff h (by omega) (S.radius_pos j) f.1).2 hg
  refine ⟨hg, ?_⟩
  have hval := Ψ.toPartialHierarchySeq.evalAt_of_mem ⟨j, hj0⟩ hn ⟨f.1, hY⟩
  have hc := hΨ ⟨j, hj0⟩ n hn ⟨f.1, hY⟩
  show ‖S.connected j f.1 - _‖ < ε
  rw [← hc, ← Complex.ofReal_sub, Complex.norm_real]
  rw [← hval]
  exact hlt
theorem exists_isConvergenceSetWith (h : CitedFacts) (hL : LimitCitedFacts) (C : BoundFamily)
    (hC : HasBallwiseBoundAlong S C) (B : BoundedFamily) :
    ∃ J, S.IsConvergenceSetWith C B J := by
  obtain ⟨Ψ, hΨ⟩ := exists_partialHierarchySeq S h C hC
  obtain ⟨F⟩ := (hL.families D.euclidParams .euclidean).1.2
  let θ : PeriodicSpace.RadiusRatio := ⟨1 / 8, by norm_num⟩
  have hr : 0 < PeriodicSpace.Kind.ballRadius D.euclidParams θ
      PeriodicSpace.Kind.torus :=
    mul_pos (by norm_num [θ]) (PeriodicSpace.Kind.side_pos _)
  have hP : Nonempty (PeriodicSpace.Kind.TorusPartitionChoice D.euclidParams θ) := by
    obtain ⟨⟨J, hJ, x, hx⟩, hχ, -⟩ := hL.covers D.euclidParams _ hr
    obtain ⟨A, _, -, χ, hχ'⟩ := hχ J hJ x hx
    exact ⟨{ numBalls := J, center := x, cover := hx, Idx := A, bump := χ,
             subordinate := hχ' }⟩
  obtain ⟨P⟩ := hP
  have hE := (h.compactness D.euclidParams .euclidean θ P F C).2.2.2.1
  have := B.countable
  obtain ⟨⟨J, hJ, Ξ, w, ⟨hw, hconv⟩, hΞ, hest, -⟩, -⟩ :=
    hE pnatIndices (radiusSeq S) Ψ B.Idx B.start B.seq B.bounded
  have hlim := tendstoIn_of_tendsToOnSepAlong S h C hΨ hconv
  exact ⟨J, { limit_exists := fun n hn f => ⟨_, hlim n hn f⟩
              limit_hierarchy := ⟨Ξ, hlim, hΞ, hest⟩
              seq_tendsto := fun ι => ⟨w ι, hw ι⟩ }⟩
def restrictAlong {C : BoundFamily}
    (Ψ : Kind.BoundedPartialHierarchySeq D.euclidParams .euclidean pnatIndices (radiusSeq S) C)
    (J : Sequences.PNatIndexSet) :
    Kind.BoundedPartialHierarchySeq D.euclidParams .euclidean J
      (fun j => radiusSeq S (pnatIndex j.1)) C where
  radii := ⟨fun j => Ψ.radii.pos _, fun r hr => by
      obtain ⟨j', hj'⟩ := Ψ.radii.eventually_gt r hr
      exact ⟨j', fun j _ hle _ => hj' j (Set.mem_univ j) hle (Set.mem_univ j)⟩,
    fun h => by cases h⟩
  func j := Ψ.func (pnatIndex j.1)
  multilinear j := Ψ.multilinear _
  symmetric j := Ψ.symmetric _
  threshold := Ψ.threshold
  boundedFrom n hn R hR j hj := Ψ.boundedFrom n hn R hR (pnatIndex j.1) hj
theorem restrictAlong_converges (h : CitedFacts) {C : BoundFamily}
    {Ψ : Kind.BoundedPartialHierarchySeq D.euclidParams .euclidean pnatIndices (radiusSeq S) C}
    (hΨ : IsPartialHierarchySeqOf S C Ψ) {J : Sequences.PNatIndexSet} {Ξ : D.LimitHierarchy}
    (hΞ : S.IsLimitHierarchy J Ξ) :
    (restrictAlong S Ψ J).toPartialHierarchySeq.ConvergesOnSepTuples Ξ := by
  intro n hn f ε hε
  obtain ⟨j', hj'⟩ := hΞ n hn f ε hε
  refine ⟨j', fun j hj => ?_⟩
  obtain ⟨hg, hlt⟩ := hj' j.1 j.2 hj
  have hY := (mem_sepLipTuplesWithin_centredBall_iff h (by omega) (S.radius_pos j.1) f.1).2 hg
  refine ⟨hY, ?_⟩
  have hc : ((Ψ.func (pnatIndex j.1) n hn ⟨f.1, hY⟩ : ℝ) : ℂ) = S.connected j.1 f.1 :=
    hΨ (pnatIndex j.1) n hn ⟨f.1, hY⟩
  have hlt' : ‖((Ψ.func (pnatIndex j.1) n hn ⟨f.1, hY⟩ : ℝ) : ℂ) -
      ((Ξ.func n hn f : ℝ) : ℂ)‖ < ε := by
    rw [hc]
    exact hlt
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hlt'
  exact hlt'.le
theorem limit_member_facts (h : CitedFacts) (C : BoundFamily) (hC : HasBallwiseBoundAlong S C)
    {J : Sequences.PNatIndexSet} {Ξ : D.LimitHierarchy} (hΞ : S.IsLimitHierarchy J Ξ) (n : ℕ+)
    (hn : 2 ≤ (n : ℕ)) :
    (∃! T, Kind.EuclideanLimitDistributions.HasMemberValues Ξ hn T) ∧
      ∀ T, Kind.EuclideanLimitDistributions.HasMemberValues Ξ hn T →
        Kind.Tuple.IsDistribOfOrderLE (5 * (n : ℕ) + 1) T ∧
        (∀ (Ω' : Set (Kind.euclidean.Tuple D.euclidParams n))
            (h : Ω' ⊆ Kind.pairwiseDistinct D.euclidParams Kind.euclidean n),
          Kind.Tuple.IsOpenT D.euclidParams Kind.euclidean Ω' →
            Kind.Tuple.HasOrderLEOn h (5 * (n : ℕ) + 1) T) ∧
        (∀ σ : Equiv.Perm (Fin (n : ℕ)), Kind.InvariantUnder (D := D.euclidParams)
          (E := Kind.euclidean) (fun x i => x (σ i)) T) ∧
        ∀ s : Kind.euclidean.Pt D.euclidParams → Kind.euclidean.Pt D.euclidParams,
          Kind.IsIsometry D.euclidParams Kind.euclidean s →
          (∀ (φ : Kind.sepC1Tuples D.euclidParams Kind.euclidean (n : ℕ))
              (h : Kind.compEach φ.1 s ∈
                Kind.sepC1Tuples D.euclidParams Kind.euclidean (n : ℕ)),
            Ξ.func (n : ℕ) hn ⟨_, h⟩ = Ξ.func (n : ℕ) hn φ) →
          Kind.InvariantUnder (D := D.euclidParams) (E := Kind.euclidean)
            (fun x i => s (x i)) T := by
  obtain ⟨Ψ, hΨ⟩ := exists_partialHierarchySeq S h C hC
  exact h.distributions D.euclidParams C J _ (restrictAlong S Ψ J) Ξ
    (restrictAlong_converges S h hΨ hΞ) n hn
theorem memberDistribsInvariant_of_tendstoIn (h : CitedFacts) (C : BoundFamily)
    (hC : HasBallwiseBoundAlong S C) {J : Sequences.PNatIndexSet} {Ξ : D.LimitHierarchy}
    (hΞ : S.IsLimitHierarchy J Ξ) : MemberDistribsInvariant Ξ := by
  intro n hn T hT
  obtain ⟨-, -, hp, hs⟩ := (limit_member_facts S h C hC hΞ n hn).2 T hT
  exact ⟨hp, hs⟩
theorem proj_euclidean_eq_pointAt (Y : PeriodicSpace.Params) {p : ℕ+}
    (x : ReflectionSpaces.Euclidean.Coord (4 * (p : ℕ))) :
    Kind.Tuple.proj Y .euclidean x =
      Continuum.BlockProducts.pointAt x := by
  funext i μ
  show x _ = x _
  congr 1
  apply Fin.ext
  simp [Continuum.BlockProducts.pointCoordEquiv, finProdFinEquiv]
  omega
theorem exists_isCoordinateRepresentation (hL : LimitCitedFacts) (n : ℕ+)
    (T : Kind.Tuple.testFns D.euclidParams Kind.euclidean
      (Kind.pairwiseDistinct D.euclidParams Kind.euclidean n) → ℂ)
    (hT : Kind.Tuple.IsDistrib T) :
    ∃ v : ReflectionSpaces.Euclidean.Distribution
      (Continuum.BlockProducts.configSpace (n : ℕ)), IsPauliCoordinate v T := by
  have hW : CoordinateRepresentation.IsCoordinateImageOfSet
      (Kind.pairwiseDistinct D.euclidParams Kind.euclidean n)
      (Continuum.BlockProducts.configSpace (n : ℕ)) := by
    refine Set.ext fun x => ?_
    have hq := proj_euclidean_eq_pointAt D.euclidParams (p := n) x
    show Continuum.BlockProducts.pointAt x ∈
        TestFunctions.injectiveTuples (Fin 4 → ℝ) (n : ℕ) ↔
      Kind.Tuple.proj D.euclidParams .euclidean x ∈
        Kind.pairwiseDistinct D.euclidParams Kind.euclidean n
    rw [hq]
    exact Iff.rfl
  obtain ⟨V, ⟨-, hV⟩, -⟩ := (hL.evalOnSigma D.euclidParams n _ _
    (hL.distinct D.euclidParams .euclidean n).1 hW).2.2 T hT
  refine ⟨V, fun G hG hG' => hV ⟨G, hG⟩ ⟨_, hG'⟩ ?_⟩
  funext x
  show G _ = G _
  rw [proj_euclidean_eq_pointAt]
theorem exists_isMemberFamily (hL : LimitCitedFacts) {Ξ : D.LimitHierarchy}
    (hM : MembersAreDistribs Ξ) : ∃ u, IsMemberFamily Ξ u := by
  have key : ∀ (n : ℕ+) (hn : 2 ≤ (n : ℕ)), ∃ v : ReflectionSpaces.Euclidean.Distribution
      (Continuum.BlockProducts.configSpace (n : ℕ)),
      ∀ T, IsMemberDistrib Ξ n hn T → IsPauliCoordinate v T := by
    intro n hn
    obtain ⟨⟨T₀, hT₀, hu⟩, -⟩ := hM n hn
    obtain ⟨v, hv⟩ := exists_isCoordinateRepresentation hL n T₀ hT₀.1
    exact ⟨v, fun T hT => by rwa [hu T hT]⟩
  choose v hv using key
  exact ⟨fun n hn => v ⟨n, by omega⟩ hn, fun n hn T hT => hv n hn T hT⟩
theorem abs_func_le_of_admissible (h : CitedFacts) {J : Sequences.PNatIndexSet}
    {Ξ : D.LimitHierarchy} (hΞ : S.IsLimitHierarchy J Ξ) (n : ℕ) (hn : 2 ≤ n) (d R : ℝ)
    (hd : 0 < d) (hR : 0 < R) (C' : ℝ) (hC' : IsAdmissibleAlongSeq S n d R C')
    (f : D.sepDomain n) (hf : f.1 ∈ lipTuples n hn d R hd hR) :
    |Ξ.func n hn f| ≤ C' * ∏ i, TestFunctions.sharpNormR4 (D.M : ℝ) (f.1 i) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨j', hj'⟩ := hΞ n hn f ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (S.side_tendsto.eventually_ge_atTop (16 * (n : ℝ) * (1 + R)))
  obtain ⟨j, hjJ, hjl⟩ := J.infinite.exists_gt (max N ⟨j'.toNat + 1, by omega⟩)
  have hjN : N ≤ j := (le_max_left _ _).trans hjl.le
  have hjM : (⟨j'.toNat + 1, by omega⟩ : ℕ+) ≤ j := (le_max_right _ _).trans hjl.le
  have hjM' : j'.toNat + 1 ≤ (j : ℕ) := hjM
  obtain ⟨hg, hlt⟩ := hj' j hjJ (by omega)
  have hb := norm_connected_le_of_admissible S h hn hd hR hC' (hN j hjN) hf hg
  have hsub := norm_sub_norm_le ((Ξ.func n hn f : ℝ) : ℂ) (S.connected j f.1)
  rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs] at hsub
  linarith
theorem membersAreDistribs_of_tendstoIn (h : CitedFacts) (C : BoundFamily)
    (hC : HasBallwiseBoundAlong S C) {J : Sequences.PNatIndexSet} {Ξ : D.LimitHierarchy}
    (hΞ : S.IsLimitHierarchy J Ξ) : MembersAreDistribs Ξ := by
  intro n hn
  obtain ⟨h1, h2⟩ := limit_member_facts S h C hC hΞ n hn
  refine ⟨h1, fun T hT => ?_⟩
  obtain ⟨h3, h4, -, -⟩ := h2 T hT
  exact ⟨h3, h4⟩
theorem existenceAndBounds_of_tendstoIn (h : CitedFacts) (hL : LimitCitedFacts) (C : BoundFamily)
    (hC : HasBallwiseBoundAlong S C) {J : Sequences.PNatIndexSet} {Ξ : D.LimitHierarchy}
    (hJ : S.IsConvergenceSet C J) (hΞ : S.IsLimitHierarchy J Ξ) :
    ExistenceAndBounds S C J Ξ := by
  obtain ⟨Ξ', h1, h2, h3⟩ := hJ.limit_hierarchy
  obtain rfl := h1.unique hΞ
  have hM := membersAreDistribs_of_tendstoIn S h C hC hΞ
  refine
    { isLimitHierarchy := hΞ
      terms_defined := ?_
      mem_boundedEuclidHierarchies := h2
      equicontinuous := h3
      bound_of_admissible := abs_func_le_of_admissible S h hΞ
      membersAreDistribs := hM
      exists_memberFamily := exists_isMemberFamily hL hM }
  intro n hn f ρ hρ hs j hle
  obtain ⟨-, -, hiff⟩ := (h.cumulants D S).1
  have hρj := (hiff j ρ hρ).1 hle
  refine mem_lipTuplesInBall_of_sepC1 (by omega) f.2 (S.radius_pos j) fun i x hx => ?_
  exact lt_of_lt_of_le (hs i hx) hρj
end
end ExistencePart
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps
end
