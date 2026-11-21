import YangMills.Construction.Lattice.DirichletOperatorsOfASeparatedSequence
import YangMills.Construction.SeparatedSequences.TwoSequencesOfOneClass
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction
namespace SeparatedSequences
namespace BaseParameters
variable (D : BaseParameters) {T : ℕ} (hT : T ≤ D.t) (Ω : ℕ → Set D.Torus)
abbrev truncScales : SeparatedSequences.ScaleData :=
  ⟨D.K, T, T, D.blockExp, hT.trans D.t_le_K, hT.trans D.t_le_K⟩
def truncLayerSites (n : ℕ) : Set (D.LatticeSite n) :=
  SeparatedSequences.layerLatticeSites (D.truncScales hT) Ω n
def truncLayerPoints : Set D.Torus := SeparatedSequences.layerPoints (D.truncScales hT) Ω
abbrev TruncCoarseSpace : Type := ↥(D.truncLayerPoints hT Ω) → ℝ
instance finite_truncLayerPoints : Finite ↥(D.truncLayerPoints hT Ω) :=
  Set.Finite.to_subtype (Set.Finite.biUnion (Set.finite_Iic _) fun _ _ =>
    (Set.toFinite _).image _)
def truncCoarseInner (u v : D.TruncCoarseSpace hT Ω) : ℝ :=
  ∑ n ∈ Finset.range (T + 1), D.levelMeshRatio n ^ dimension *
    ∑ᶠ y : ↥(D.truncLayerSites hT Ω n),
      SeparatedClasses.extendZero _ u (y.1 : D.Torus) *
        SeparatedClasses.extendZero _ v (y.1 : D.Torus)
theorem exists_truncLevelSite (y : ↥(D.truncLayerPoints hT Ω)) :
    ∃ p : Σ n : ℕ, D.LatticeSite n,
      p.1 ≤ T ∧ p.2 ∈ D.truncLayerSites hT Ω p.1 ∧ (p.2 : D.Torus) = y := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨n, hn, z, hz, rfl⟩ := mem_iUnion₂.mp hy
  exact ⟨⟨n, z⟩, hn, hz, rfl⟩
def truncLevelSite (y : ↥(D.truncLayerPoints hT Ω)) : Σ n : ℕ, D.LatticeSite n :=
  (D.exists_truncLevelSite hT Ω y).choose
def truncBlockAverage : ↥(zeroFormsOn D.K (Ω 0)) →ₗ[ℝ] D.TruncCoarseSpace hT Ω where
  toFun f y := D.blockAverageZero (D.truncLevelSite hT Ω y).1 f.1 (D.truncLevelSite hT Ω y).2
  map_add' f g := by
    funext y
    simp
  map_smul' c f := by
    funext y
    simp
def truncWeightMul : D.TruncCoarseSpace hT Ω →ₗ[ℝ] D.TruncCoarseSpace hT Ω where
  toFun u y := D.levelWeight (D.truncLevelSite hT Ω y).1 *
    (D.levelMeshRatio (D.truncLevelSite hT Ω y).1 ^ 2)⁻¹ * u y
  map_add' u v := by
    funext y
    simp only [Pi.add_apply]
    ring
  map_smul' c u := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def truncBlockAverageAdjoint : D.TruncCoarseSpace hT Ω →ₗ[ℝ] ↥(zeroFormsOn D.K (Ω 0)) :=
  FiniteDimReal.adjointFor (D.restrictedZeroInner Ω) (D.truncCoarseInner hT Ω)
    (D.truncBlockAverage hT Ω)
def truncZeroGreen : Module.End ℝ ↥(zeroFormsOn D.K (Ω 0)) :=
  Ring.inverse (dirichletLaplacian D.K D.t (Ω 0) +
    D.truncBlockAverageAdjoint hT Ω ∘ₗ D.truncWeightMul hT Ω ∘ₗ
      D.truncBlockAverage hT Ω)
end BaseParameters
end SeparatedSequences
namespace SeparatedClasses
def LevelFamilyAgrees {α : ℕ → Type} (t T : ℕ) (F G : ∀ n, Set (α n)) : Prop :=
  (∀ n ≤ T, F n = G n) ∧ ∀ n, T < n → n ≤ t → F n = ∅
namespace ClassData
variable (C : ClassData) (Ω : ℕ → Set C.Point)
theorem lastNonempty_le : C.lastNonempty Ω ≤ C.t :=
  csSup_le' fun _ h => h.1
variable {C} {T : ℕ} (hT : T ≤ C.t)
abbrev truncScales : SeparatedSequences.ScaleData :=
  ⟨C.K, T, T, C.blockExp, hT.trans C.t_le_cutoff, hT.trans C.t_le_cutoff⟩
abbrev truncMember (n : ℕ) : Set C.Point := SeparatedSequences.truncatedMember (truncScales hT) Ω n
abbrev truncLayer (n : ℕ) : Set C.Point := SeparatedSequences.layerSet (truncScales hT) Ω n
abbrev truncLayerSites (n : ℕ) : Set (C.LatticeSite n) :=
  SeparatedSequences.layerLatticeSites (truncScales hT) Ω n
def truncApexes : Set (Σ n : ℕ, C.LatticeSite n) :=
  {y | y.1 ≤ T ∧ y.2 ∈ truncLayerSites Ω hT y.1}
def truncChainLength (Γ : List LiftedSegment) : ℝ :=
  ∑ n ∈ Finset.Icc 1 T, (C.coarseMesh n)⁻¹ *
      C.toLevelUnits (pathLengthIn (torusSide C.L C.m) Γ (truncLayer Ω hT n)) +
    (C.coarseMesh 0)⁻¹ *
      C.toLevelUnits (pathLengthIn (torusSide C.L C.m) Γ (truncMember Ω hT 1)ᶜ)
def truncChainDist (y y' : C.Point) : ENNReal :=
  ⨅ Γ ∈ {Γ : List LiftedSegment | IsTreeGraph (torusSide C.L C.m) Γ ∧
      y ∈ segmentsSupport (torusSide C.L C.m) Γ ∧ y' ∈ segmentsSupport (torusSide C.L C.m) Γ},
    ENNReal.ofReal (truncChainLength Ω hT Γ)
def truncSiteLayerSup (γ : ℝ) (f : C.SiteFn) : ℝ :=
  sSup {r | ∃ n ≤ T, ∃ x : C.BareSite, (x : C.Point) ∈ truncLayer Ω hT n ∧
    r = C.coarseMesh n ^ (-γ) * |f x|}
def truncBondLayerSup (γ : ℝ) (f : C.BondFn) : ℝ :=
  sSup {r | ∃ n ≤ T, ∃ b : C.BareBond, (decidingSite Ω b : C.Point) ∈ truncLayer Ω hT n ∧
    r = C.coarseMesh n ^ (-γ) * |f b|}
def truncLayerBonds (j : ℕ) : Set (C.LatticeBond j) :=
  {c | (c.source ∈ truncLayerSites Ω hT j ∨ c.target ∈ truncLayerSites Ω hT j) ∧
    c ∉ (bondsMeeting (truncMember Ω hT (j + 1)) : Set (C.LatticeBond j))}
def truncatedBondSetAt (φ : BondFrame) : (j : ℕ) → Set (C.PosLatticeBond j)
  | 0 => {c | c ∈ C.frameSet Ω φ ∧
      c.1 ∉ (bondsMeeting (truncMember Ω hT 1) : Set (C.LatticeBond 0))}
  | j + 1 => {c | c.1 ∈ truncLayerBonds Ω hT (j + 1)}
def truncatedBondSet (φ : BondFrame) : Set (Σ j : ℕ, C.PosLatticeBond j) :=
  {c | c.1 ≤ T ∧ c.2 ∈ truncatedBondSetAt Ω hT φ c.1}
structure AgreesWithTruncation : Prop where
  member_eq : ∀ n, C.memberAt Ω n = truncMember Ω hT n
  layer_eq : LevelFamilyAgrees (α := fun _ => C.Point) C.t T (C.layerAt Ω) (truncLayer Ω hT)
  determiningBonds_eq : LevelFamilyAgrees C.t T (determiningBondsAt C.cutoff C.t Ω)
    (determiningBondsAt C.cutoff T Ω)
  determiningBondSet_eq : determiningBondSet C.cutoff C.t Ω =
    determiningBondSet C.cutoff T Ω
  activeBondsAt_eq : LevelFamilyAgrees C.t T (activeBondsAt C.cutoff C.t Ω)
    (activeBondsAt C.cutoff T Ω)
  activeBonds_eq : C.activeBonds Ω = activeBondSet C.cutoff T Ω
  layerSites_eq : LevelFamilyAgrees C.t T (C.layerSitesAt Ω) (truncLayerSites Ω hT)
  layerPts_eq : C.layerPts Ω = SeparatedSequences.layerPoints (truncScales hT) Ω
  apexes_eq : {y : Σ n : ℕ, C.LatticeSite n | y.1 ≤ C.t ∧ y.2 ∈ C.layerSitesAt Ω y.1} =
    truncApexes Ω hT
  chainLength_eq : ∀ Γ, C.chainLength Ω Γ = truncChainLength Ω hT Γ
  chainDist_eq : ∀ y y', C.chainDist Ω y y' = truncChainDist Ω hT y y'
  zeroGreen_eq : (C.baseParamsAt 1 one_pos).zeroGreen Ω =
    (C.baseParamsAt 1 one_pos).truncZeroGreen hT Ω
  siteLayerSup_eq : ∀ γ f, C.siteLayerSup Ω γ f = truncSiteLayerSup Ω hT γ f
  bondLayerSup_eq : ∀ γ f, C.bondLayerSup Ω γ f = truncBondLayerSup Ω hT γ f
  layerBonds_eq : LevelFamilyAgrees C.t T (C.layerBonds Ω) (truncLayerBonds Ω hT)
  expansionSetAt_eq : ∀ φ, LevelFamilyAgrees C.t T (C.expansionSetAt Ω φ) (truncatedBondSetAt Ω hT φ)
  expansionSet_eq : ∀ φ, C.expansionSet Ω φ = truncatedBondSet Ω hT φ
end ClassData
def AgreesUpToLastNonempty : Prop :=
  ∀ (C : ClassData) (Ω : ℕ → Set C.Point), Ω ∈ C.separatedClass →
    ClassData.AgreesWithTruncation Ω (C.lastNonempty_le Ω)
end SeparatedClasses
end YangMills.Construction
end
