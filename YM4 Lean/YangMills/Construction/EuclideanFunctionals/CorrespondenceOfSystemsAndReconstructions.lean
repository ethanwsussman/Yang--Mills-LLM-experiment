import YangMills.Construction.EuclideanFunctionals.OperatorsOfTheClosedForwardTube
import YangMills.Construction.EuclideanFunctionals.OperatorsOfTheForwardTubeOverTheWedge
import YangMills.Construction.EuclideanFunctionals.PlateBoundOfASymmetricEuclideanFunctional
import YangMills.Construction.EuclideanFunctionals.TransportOfAReconstructionAndThePlateBoundInACoordinatePlane
import YangMills.Construction.ForwardTube.ClosedTubeAndShiftedTuples
import YangMills.Construction.SpectralTheory.PreliminarySettingsDefs
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.DefinitionComparison
open YangMills.Construction.SettingsComparison (IsSameMeasure euclideanToCoords totalOp)
def lowerEnvelope (C : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (d R : ℝ) : ℝ :=
  sInf ((fun d' => max (C n d' R) 0) '' Set.Ioc 0 d)
def LowerEnvelopeIsAdmissible (m : SharpScale) (S : ConnFamily) : Prop :=
  (∀ (C C' : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (d R : ℝ), 2 ≤ n → 0 < R → 0 < d →
      (∀ d' ∈ Set.Ioc 0 d, C n d' R = C' n d' R) → lowerEnvelope C n d R = lowerEnvelope C' n d R) ∧
    ∀ C : ℕ → ℝ → ℝ → ℝ, HasClusterBounds S m C →
      HasClusterBounds S m (lowerEnvelope C) ∧
      (∀ (n : ℕ) (d R : ℝ), 2 ≤ n → 0 < R → 0 < d → 0 ≤ lowerEnvelope C n d R) ∧
      ∀ (n : ℕ) (d₁ d₂ R : ℝ), 2 ≤ n → 0 < R → 0 < d₁ → d₁ ≤ d₂ →
        lowerEnvelope C n d₂ R ≤ lowerEnvelope C n d₁ R
def PropertiesAgree (m : SharpScale) (S : ConnFamily) : Prop :=
  (ConnectedSymmetric S ↔ IsSymmMultilinReal S) ∧
    (ConnectedInvariant S ↔ IsLatticeInvariant S) ∧
    (OSPositive S ↔ IsOSPositive S) ∧
    LowerEnvelopeIsAdmissible m S
section Passages
variable {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] {S : ConnFamily}
structure Corresponds (R : OSReconstruction ℋ S) (sys : OSData ℋ S) : Prop where
  cls_eq : ∀ F : FreeSep, readClass R.cls F = classOrZero sys.cls F
  isJointSpectralMeasure : ResolvedOps.IsJointSpectralMeasure
    (hamMomFamily R.ham R.mom) (hamMomMeasure R.ham R.mom)
  measure_eq : IsSameMeasure (hamMomMeasure R.ham R.mom) sys.pvm
  rotOp_eq : ∀ w, R.rotOp w = sys.rotOp w
  vac_eq : R.vac = sys.vac
  ham_eq : R.ham =
    ⟨sys.pvm.fnDomain energyFn, hamiltonianOp sys.pvm⟩
  mom_eq : ∀ j, R.mom j =
    ⟨sys.pvm.fnDomain (fun p => (momCoord j p : ℂ)),
      momentumOp sys.pvm j⟩
  exp_eq : ∀ t : ℝ, 0 ≤ t →
    ⇑(ResolvedOps.expComplex R.ham (t : ℂ)) = ⇑(semigroupOp sys.pvm t)
  spatial_eq : ∀ v ∈ spatialVecs,
    ⇑(spatialTranslOp (hamMomMeasure R.ham R.mom) v) =
      ⇑(spatialShiftOp sys.pvm v)
variable (ℋ S) in
def PassagesInverse : Prop :=
  (∀ (R : OSReconstruction ℋ S) (sys sys' : OSData ℋ S),
    Corresponds R sys → Corresponds R sys' → sys = sys') ∧
  ∀ (R R' : OSReconstruction ℋ S) (sys : OSData ℋ S),
    Corresponds R sys → Corresponds R' sys → R = R'
end Passages
section Forms
variable {m : SharpScale} {S : ConnFamily}
structure OSDataOf (σ : EuclidFunctionalWithRecon m S) where
  isSymmMultilinReal : IsSymmMultilinReal S
  isLatticeInvariant : IsLatticeInvariant S
  isOSPositive : IsOSPositive S
  osData : OSData σ.space S
  corresponds : Corresponds σ.recon osData
abbrev OSDataOf.toSymm {σ : EuclidFunctionalWithRecon m S}
    (s : OSDataOf σ) : SymmEuclidFunctional m S where
  isSymmMultilinReal := s.isSymmMultilinReal
  isLatticeInvariant := s.isLatticeInvariant
  isOSPositive := s.isOSPositive
  clusterConst := σ.clusterConst
  hasClusterBounds := σ.cluster
  space := σ.space
  osData := s.osData
structure ReconOf (τ : SymmEuclidFunctional m S) where
  symm : ConnectedSymmetric S
  invariant : ConnectedInvariant S
  positive : OSPositive S
  recon : OSReconstruction τ.space S
  corresponds : Corresponds recon τ.osData
abbrev ReconOf.toRecon {τ : SymmEuclidFunctional m S}
    (r : ReconOf τ) : EuclidFunctionalWithRecon m S where
  symm := r.symm
  invariant := r.invariant
  positive := r.positive
  clusterConst := τ.clusterConst
  cluster := τ.hasClusterBounds
  space := τ.space
  recon := r.recon
end Forms
section Numbers
variable {m : SharpScale} {S : ConnFamily}
def SymmProductBoundWith (τ : SymmEuclidFunctional m S) {p c : ℝ} (_hp : 0 < p)
    (_hc : c ∈ stripFractionRange) (φ : RealPlane → ℝ) (C : ℝ) : Prop :=
  ∀ (η : ℝ) (hη : η ∈ gapWidthRange),
    ∀ α ∈ complexProfiles, tsupport α ⊆ {y : RealPlane | |y 0| < c * η} →
    ∀ F F' : freeSpanIn {x | η / 4 < x 3},
      ‖stripInsertion S F.1 (productFunction α φ) F'.1‖ ≤
        C * η ^ (-p) * profileL1Norm α *
          loweredNorm τ (quarter_pos_of_mem_gapWidthRange hη) F *
          loweredNorm τ (quarter_pos_of_mem_gapWidthRange hη) F'
theorem hasProductBound_iff (τ : SymmEuclidFunctional m S) {p c : ℝ} (hp : 0 < p)
    (hc : c ∈ stripFractionRange) :
    HasProductBound τ hp hc ↔ ∀ φ ∈ realLabels, ∃ C : ℝ, SymmProductBoundWith τ hp hc φ C :=
  Iff.rfl
def SymmRotatedProductBoundWith (τ : SymmEuclidFunctional m S) (w : hyperoctahedral)
    {p c : ℝ} (_hp : 0 < p) (_hc : c ∈ stripFractionRange) (φ : RealPlane → ℝ) (C : ℝ) : Prop :=
  ∀ (η : ℝ) (hη : η ∈ gapWidthRange),
    ∀ α ∈ complexProfiles, tsupport α ⊆ {y : RealPlane | |y 0| < c * η} →
    ∀ F F' : freeSpanIn {x | η / 4 < x 3},
      ‖rotatedInsertion S w F.1 (productFunction α φ) F'.1‖ ≤
        C * η ^ (-p) * profileL1Norm α *
          rotatedLoweredNorm τ w (quarter_pos_of_mem_gapWidthRange hη) F *
          rotatedLoweredNorm τ w (quarter_pos_of_mem_gapWidthRange hη) F'
theorem hasProductBoundInRotatedPlane_iff (τ : SymmEuclidFunctional m S)
    (w : hyperoctahedral) {p c : ℝ} (hp : 0 < p) (hc : c ∈ stripFractionRange) :
    HasProductBoundInRotatedPlane τ w hp hc ↔
      ∀ φ ∈ realLabels, ∃ C : ℝ, SymmRotatedProductBoundWith τ w hp hc φ C :=
  Iff.rfl
end Numbers
section Objects
variable {m : SharpScale} {S : ConnFamily} {σ : EuclidFunctionalWithRecon m S}
  (s : OSDataOf σ)
def MeasuresAgree : Prop :=
  s.toSymm.clusterConst = σ.clusterConst ∧
    IsSameMeasure σ.jointMeasure s.toSymm.jointSpecMeasure ∧
    ∀ B : EuclideanSpectral.BorelSubset 4,
      s.toSymm.SupportsJointSpec B ↔
        σ.jointMeasure.IsCarriedBy (euclideanToCoords B)
def ConeConditionsAgree : Prop :=
  (∀ j : Fin 3, σ.HamGeAbsMomentum j ↔ s.toSymm.EnergyBoundsMom j) ∧
    (σ.ConeCondition ↔ s.toSymm.LightConeBound) ∧
    euclideanToCoords momentumPyramid = SpectralPoint.pyramid
def InsertionsAgree : Prop :=
  ∀ (c : ℝ) (F A : FreeSep) (h : R4 → ℂ) (hc : IsStripHeight c F h A),
    pullDown c F = lowerBy hc.pos ⟨F, hc.left_mem⟩ ∧
      heightNorm σ c F = loweredNorm s.toSymm hc.pos ⟨F, hc.left_mem⟩ ∧
      insertion S F h A = stripInsertion S F h A
def ProductBoundsAgree : Prop :=
  ∀ (p c : ℝ) (hp : 0 < p) (hc : c ∈ productBoundFractions),
    c ∈ stripFractionRange ∧
      (ProductBoundWithExponent σ hp hc ↔
        HasProductBound s.toSymm hp (productBoundFractions_subset_stripFractionRange hc)) ∧
      ∀ φ ∈ realLabels, ∀ C : ℝ, ProductBoundWith σ hp hc φ C ↔
        SymmProductBoundWith s.toSymm hp (productBoundFractions_subset_stripFractionRange hc) φ C
def PicturesAgree : Prop :=
  ∀ w : hyperoctahedral,
    mappedUpperSpan w = finCombIn (movedHalfSpace w) ∧
      (normalPicture s.toSymm w).refl =
        (w : EuclidMotion) * timeFlip * (w : EuclidMotion)⁻¹ ∧
      (∀ A : freeSpanIn (movedHalfSpace w),
        movedClass s.toSymm w A = mappedReconClass σ w A.1) ∧
      (∀ (c : ℝ) (F A : FreeSep) (h : R4 → ℂ), IsStripHeight c F h A →
        mappedInsertionForm S w ((w : EuclidMotion).actFree F) ((w : EuclidMotion).actFn h)
            ((w : EuclidMotion).actFree A) =
          rotatedInsertion S w F h A) ∧
      ∀ (p c : ℝ) (hp : 0 < p) (hc : c ∈ productBoundFractions),
        (ImagePlaneProductBound σ w hp hc ↔
          HasProductBoundInRotatedPlane s.toSymm w hp
            (productBoundFractions_subset_stripFractionRange hc)) ∧
        ∀ φ ∈ realLabels, ∀ C : ℝ, ImagePlaneProductBoundWith σ w hp hc φ C ↔
          SymmRotatedProductBoundWith s.toSymm w hp
            (productBoundFractions_subset_stripFractionRange hc) φ C
def TubeOperatorsAgree : Prop :=
  σ.ConeCondition → ∀ v ∈ ForwardTube.closedForwardTube,
    σ.tubeOp v = totalOp (s.toSymm.tubeOp v)
def ObjectsAgree : Prop :=
  MeasuresAgree s ∧ ConeConditionsAgree s ∧ InsertionsAgree s ∧ ProductBoundsAgree s ∧
    PicturesAgree s ∧ TubeOperatorsAgree s
end Objects
end YangMills.Construction.EuclideanFunctionals.DefinitionComparison
