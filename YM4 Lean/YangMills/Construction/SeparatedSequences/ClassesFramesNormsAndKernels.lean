import YangMills.Construction.Conventions.LeveledParameters
import YangMills.Construction.Dirichlet.RegionSequenceOperators
import YangMills.Construction.Lattice.DirichletDifferenceOperators
import YangMills.Construction.Lattice.InwardBondsAndSetsInForce
import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators TorusMetric
namespace SeparatedClasses
def translateBond {L m : ℕ} {j : ℤ} (v : PeriodicLattice.Site L m j)
    (b : PeriodicLattice.PositivelyOrientedBond L m j) :
    PeriodicLattice.PositivelyOrientedBond L m j :=
  ⟨⟨b.1.source + v, b.1.target + v, by
      obtain ⟨μ, h⟩ := b.1.isNeighbour
      exact ⟨μ, by simpa only [add_sub_add_right_eq_sub] using h⟩⟩, by
    obtain ⟨μ, h⟩ := b.2
    exact ⟨μ, by simpa only [add_sub_add_right_eq_sub] using h⟩⟩
open Classical in
def extendZero {ι : Type} (Y : Set ι) (f : Y → ℝ) : ι → ℝ :=
  fun i => if h : i ∈ Y then f ⟨i, h⟩ else 0
def IsCountingKernel {ι κ : Type} (T : (ι → ℝ) → κ → ℝ) (k : κ → ι → ℝ) : Prop :=
  ∀ f x, T f x = ∑ᶠ x', k x x' * f x'
def countingKernel {ι κ : Type} (T : (ι → ℝ) → κ → ℝ) : κ → ι → ℝ :=
  Classical.epsilon (IsCountingKernel T)
structure ClassData extends Conventions.LeveledParameters where
  blockExp : ℕ
  gapExp : ℕ
  L_le_pow_gapExp : L ≤ L ^ gapExp
namespace ClassData
variable (C : ClassData)
abbrev cutoff : ℕ := C.K
def blockSize : ℕ := C.L ^ C.blockExp
def gapSize : ℕ := C.L ^ C.gapExp
abbrev scales : SeparatedSequences.ScaleData :=
  ⟨C.K, C.t, C.t, C.blockExp, C.t_le_cutoff, C.t_le_cutoff⟩
abbrev Point : Type := PeriodicLattice.FourTorus C.L C.m
abbrev LatticeSite (n : ℕ) : Type := PeriodicLattice.SiteAtLevel C.L C.m C.cutoff n
abbrev LatticeBond (n : ℕ) : Type := PeriodicLattice.BondAtLevel C.L C.m C.cutoff n
abbrev PosLatticeBond (n : ℕ) : Type :=
  PeriodicLattice.PositivelyOrientedBond C.L C.m (PeriodicLattice.levelDepth C.cutoff n)
abbrev BareSite : Type := PeriodicLattice.DirichletOperators.BareSite C.L C.m C.cutoff
abbrev BareBond : Type := PeriodicLattice.DirichletOperators.BareBond C.L C.m C.cutoff
abbrev SiteFn : Type := PeriodicLattice.DirichletOperators.ZeroForms C.L C.m C.cutoff
abbrev BondFn : Type := PeriodicLattice.DirichletOperators.OneForms C.L C.m C.cutoff
def separatedClass : Set (ℕ → Set C.Point) :=
  {Ω | (Ω 0).Nonempty ∧
    SeparatedSequences.IsSeparatedSequence C.scales (C.gapSize : ℝ) Ω ∧
    ∀ n, C.t < n → Ω n = ∅}
def lastNonempty (Ω : ℕ → Set C.Point) : ℕ := sSup {n | n ≤ C.t ∧ (Ω n).Nonempty}
variable (Ω : ℕ → Set C.Point)
abbrev memberAt (n : ℕ) : Set C.Point := SeparatedSequences.truncatedMember C.scales Ω n
abbrev layerAt (n : ℕ) : Set C.Point := SeparatedSequences.layerSet C.scales Ω n
abbrev activeBonds : Set (Σ n : ℕ, C.LatticeBond n) :=
  PeriodicLattice.activeBondSet C.cutoff C.t Ω
abbrev layerSitesAt (n : ℕ) : Set (C.LatticeSite n) :=
  SeparatedSequences.layerLatticeSites C.scales Ω n
abbrev layerPts : Set C.Point := SeparatedSequences.layerPoints C.scales Ω
abbrev chainLength (Γ : List TorusMetric.LiftedSegment) : ℝ :=
  SeparatedSequences.layerWeightedLength C.scales Ω Γ
abbrev chainDist (y y' : C.Point) : ENNReal :=
  SeparatedSequences.layerWeightedDist C.scales Ω y y'
def Apex : Type := {y : Σ n : ℕ, C.LatticeSite n // y.1 ≤ C.t ∧ y.2 ∈ C.layerSitesAt Ω y.1}
abbrev frameSet (φ : PeriodicLattice.DirichletOperators.BondFrame) : Set C.BareBond :=
  PeriodicLattice.DirichletOperators.framedBonds C.cutoff (Ω 0) φ
abbrev forms (φ : PeriodicLattice.DirichletOperators.BondFrame) : Submodule ℝ C.BondFn :=
  PeriodicLattice.DirichletOperators.oneFormsOn C.cutoff (Ω 0) φ
variable {C}
abbrev sitesWithin (X : Set C.Point) : Set C.BareSite := PeriodicLattice.sitesIn X
abbrev bondsWithin (X : Set C.Point) : Set (C.LatticeBond 0) := PeriodicLattice.bondsMeeting X
def SiteSupportedOn (X : Set C.Point) (f : C.SiteFn) : Prop := ∀ x, x ∉ sitesWithin X → f x = 0
def BondSupportedOn (X : Set C.Point) (f : C.BondFn) : Prop :=
  ∀ b : C.BareBond, b.1 ∉ bondsWithin X → f b = 0
namespace Apex
variable {Ω}
def level (y : C.Apex Ω) : ℕ := y.1.1
def site (y : C.Apex Ω) : C.LatticeSite y.level := y.1.2
def point (y : C.Apex Ω) : C.Point := (y.site : C.Point)
def mesh (y : C.Apex Ω) : ℝ := C.coarseMesh y.level
def block (y : C.Apex Ω) : Set C.Point := SeparatedSequences.siteBlock C.scales y.site
def doubledBlock (y : C.Apex Ω) : Set C.Point :=
  SeparatedSequences.doubledSiteBlock C.scales y.site
end Apex
open Classical in
def anchorSite (b : C.BareBond) : C.BareSite :=
  if (b.1.source : C.Point) ∉ Ω 0 ∧ (b.1.target : C.Point) ∈ Ω 0 then b.1.target else b.1.source
def BondAnchoredIn (X : Set C.Point) (b : C.BareBond) : Prop := (anchorSite Ω b : C.Point) ∈ X
def AnchorSupportedIn (X : Set C.Point) (f : C.BondFn) : Prop :=
  ∀ b, ¬BondAnchoredIn Ω X b → f b = 0
open Classical in
def decidingSite (b : C.BareBond) : C.BareSite :=
  if (b.1.source : C.Point) ∉ Ω 0 then b.1.target else b.1.source
variable (C)
abbrev fineStep (μ : Fin 4) : C.BareSite :=
  PeriodicLattice.unitStep C.L C.m (PeriodicLattice.levelDepth C.cutoff 0) μ
def siteBwd (μ : Fin 4) (f : C.SiteFn) : C.SiteFn :=
  fun x => -C.finestMesh⁻¹ * (f x - f (x - C.fineStep μ))
abbrev siteGrad (f : C.SiteFn) : C.BondFn := PeriodicLattice.DirichletOperators.grad C.t f
def siteDiv (g : C.BondFn) : C.SiteFn :=
  fun x => ∑ μ, C.siteBwd μ (PeriodicLattice.DirichletOperators.axisComponent g μ) x
def siteLap (f : C.SiteFn) : C.SiteFn := C.siteDiv (C.siteGrad f)
def bondFwd (ν : Fin 4) (A : C.BondFn) : C.BondFn :=
  fun b => C.finestMesh⁻¹ * (A (translateBond (C.fineStep ν) b) - A b)
def bondBwd (ν : Fin 4) (A : C.BondFn) : C.BondFn :=
  fun b => -C.finestMesh⁻¹ * (A b - A (translateBond (-C.fineStep ν) b))
def bondLap (A : C.BondFn) : C.BondFn :=
  fun b => ∑ ν, C.bondBwd ν (C.bondFwd ν A) b
abbrev Tensors (r : ℕ) : Type := (Fin r → Fin 4) → C.BondFn
def gradOne (A : C.BondFn) : C.Tensors 1 := fun ν => C.bondFwd (ν 0) A
def gradTwo (J : C.Tensors 1) : C.Tensors 2 :=
  fun ν => C.bondFwd (ν 0) (J fun _ => ν 1)
def bondInner (A A' : C.BondFn) : ℝ := PeriodicLattice.DirichletOperators.latticeInner C.L C.t A A'
def tensorInner {r : ℕ} (J J' : C.Tensors r) : ℝ := ∑ ν, C.bondInner (J ν) (J' ν)
def divOne (φ : PeriodicLattice.DirichletOperators.BondFrame) (J : C.Tensors 1) : C.BondFn :=
  RegionSequence.adjointValue (C.forms Ω φ : Set C.BondFn) C.bondInner C.tensorInner
    C.gradOne J
def divTwo (φ : PeriodicLattice.DirichletOperators.BondFrame) (J : C.Tensors 2) : C.BondFn :=
  RegionSequence.adjointValue (C.forms Ω φ : Set C.BondFn) C.bondInner C.tensorInner
    (fun A => C.gradTwo (C.gradOne A)) J
variable {C}
def siteMulBond (φ : C.SiteFn) (f : C.BondFn) : C.BondFn :=
  fun b => φ b.1.source * f b
def composeDiv {X : Type}
    (G : ↥(PeriodicLattice.DirichletOperators.zeroFormsOn C.cutoff (Ω 0)) → X)
    (g : C.BondFn) : X :=
  G ⟨PeriodicLattice.DirichletOperators.siteProjection C.cutoff (Ω 0) (C.siteDiv g),
    LinearMap.mem_range_self _ _⟩
variable (C)
def lOneDist (x x' : C.Point) : ℝ := C.toLevelUnits (TorusMetric.torusL1Norm (x - x'))
def siteSupNorm (f : C.SiteFn) : ℝ := ⨆ x, |f x|
def bondSupNorm (f : C.BondFn) : ℝ := ⨆ b, |f b|
def tensorSupNorm {r : ℕ} (J : C.Tensors r) : ℝ := ⨆ ν, C.bondSupNorm (J ν)
def bondL2 (f : C.BondFn) : ℝ := √(C.bondInner f f)
def tensorL2 {r : ℕ} (J : C.Tensors r) : ℝ := √(C.tensorInner J J)
def siteHolder (α : ℝ) (f : C.SiteFn) : ℝ :=
  sSup {r | ∃ x x' : C.BareSite, 0 < C.lOneDist x x' ∧ C.lOneDist x x' ≤ 1 ∧
    r = C.lOneDist x x' ^ (-α) * |f x' - f x|}
def bondHolder (α : ℝ) (f : C.BondFn) : ℝ :=
  sSup {r | ∃ b b' : C.BareBond, b.1.target - b.1.source = b'.1.target - b'.1.source ∧
    0 < C.lOneDist b.1.source b'.1.source ∧ C.lOneDist b.1.source b'.1.source ≤ 1 ∧
    r = C.lOneDist b.1.source b'.1.source ^ (-α) * |f b' - f b|}
def tensorHolder {r : ℕ} (α : ℝ) (J : C.Tensors r) : ℝ := ⨆ ν, C.bondHolder α (J ν)
def siteScaledHolder (α lam : ℝ) (f : C.SiteFn) : ℝ :=
  sSup {r | ∃ x x' : C.BareSite, 0 < C.lOneDist x x' ∧ C.lOneDist x x' ≤ lam ∧
    r = (lam / C.lOneDist x x') ^ α * |f x' - f x|}
def bondScaledHolder (α lam : ℝ) (f : C.BondFn) : ℝ :=
  sSup {r | ∃ b b' : C.BareBond, b.1.target - b.1.source = b'.1.target - b'.1.source ∧
    0 < C.lOneDist b.1.source b'.1.source ∧ C.lOneDist b.1.source b'.1.source ≤ lam ∧
    r = (lam / C.lOneDist b.1.source b'.1.source) ^ α * |f b' - f b|}
def tensorScaledHolder {r : ℕ} (α lam : ℝ) (J : C.Tensors r) : ℝ :=
  ⨆ ν, C.bondScaledHolder α lam (J ν)
def siteLayerSup (γ : ℝ) (f : C.SiteFn) : ℝ :=
  sSup {r | ∃ n ≤ C.t, ∃ x : C.BareSite, (x : C.Point) ∈ C.layerAt Ω n ∧
    r = C.coarseMesh n ^ (-γ) * |f x|}
def bondLayerSup (γ : ℝ) (f : C.BondFn) : ℝ :=
  sSup {r | ∃ n ≤ C.t, ∃ b : C.BareBond, (decidingSite Ω b : C.Point) ∈ C.layerAt Ω n ∧
    r = C.coarseMesh n ^ (-γ) * |f b|}
def layerBonds (j : ℕ) : Set (C.LatticeBond j) :=
  {c | (c.source ∈ C.layerSitesAt Ω j ∨ c.target ∈ C.layerSitesAt Ω j) ∧
    c ∉ (PeriodicLattice.bondsMeeting (C.memberAt Ω (j + 1)) : Set (C.LatticeBond j))}
def expansionSetAt (φ : PeriodicLattice.DirichletOperators.BondFrame) :
    (j : ℕ) → Set (C.PosLatticeBond j)
  | 0 => {c | c ∈ C.frameSet Ω φ ∧
      c.1 ∉ (PeriodicLattice.bondsMeeting (C.memberAt Ω 1) : Set (C.LatticeBond 0))}
  | j + 1 => {c | c.1 ∈ C.layerBonds Ω (j + 1)}
def expansionSet (φ : PeriodicLattice.DirichletOperators.BondFrame) :
    Set (Σ j : ℕ, C.PosLatticeBond j) :=
  {c | c.1 ≤ C.t ∧ c.2 ∈ C.expansionSetAt Ω φ c.1}
def expansionMesh (c : Σ j : ℕ, C.PosLatticeBond j) : ℝ := C.coarseMesh c.1
def expansionSource (c : Σ j : ℕ, C.PosLatticeBond j) : C.LatticeSite c.1 := c.2.1.source
open Classical in
def rowAnchor (c : Σ j : ℕ, C.PosLatticeBond j) : C.LatticeSite c.1 :=
  if (c.2.1.source : C.Point) ∈ Ω c.1 then c.2.1.source else c.2.1.target
end ClassData
end SeparatedClasses
end YangMills.Construction
end
