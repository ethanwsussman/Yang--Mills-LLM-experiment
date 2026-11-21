import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedSequences
namespace BaseParameters
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus) (φ : BondFrame)
def IsBlockCentreOf (x : D.Torus) (p : Σ n : ℕ, D.LatticeSite n) : Prop :=
  p.1 ≤ D.t ∧ p.2 ∈ D.layerSites Ω p.1 ∧ x ∈ fineBlock (D := D) p.2
instance nonempty_sigma_latticeSite : Nonempty (Σ n : ℕ, D.LatticeSite n) := ⟨⟨0, 0⟩⟩
def blockCentre (x : D.Torus) : Σ n : ℕ, D.LatticeSite n :=
  Classical.epsilon (D.IsBlockCentreOf Ω x)
def blockLevel (x : D.Torus) : ℕ := (D.blockCentre Ω x).1
def IsExteriorSite {n : ℕ} (y : D.LatticeSite n) : Prop :=
  (y : D.Torus) ∉ D.memberAt Ω n ∧
    ∃ e : BondAtLevel D.L D.m D.K n, (e.source : D.Torus) ∈ D.memberAt Ω n ∧ e.target = y
def averagingSegment (n : ℕ) (x : BareSite D.L D.m D.K) (μ : Fin 4) :
    List (BareOrientedBond D.L D.m D.K) :=
  forwardAxisPath x μ (D.L ^ n)
variable {D} in
def bondCorridorOf {n : ℕ} (c : D.LevelBond n) : Set (BareBond D.L D.m D.K) :=
  {e | e.1.target - e.1.source = unitStep D.L D.m (levelDepth D.K 0) (bondAxis c) ∧
    (e.1.source : D.Torus) ∈ fineBlock (D := D) c.1.source ∧
    (e.1.target : D.Torus) ∈ fineBlock (D := D) c.1.target}
def secondMemberCollar (r : ℕ) : Set (BareSite D.L D.m D.K) :=
  {x | ∃ x₀ : BareSite D.L D.m D.K, (x₀ : D.Torus) ∈ D.memberAt Ω 1 ∧
    ∃ γ : List (BareOrientedBond D.L D.m D.K), γ.length ≤ r ∧ IsBondPathFromTo γ x₀ x}
def MemberSitesInCubes : Prop :=
  ∀ n ≤ D.t, ∀ k ≤ n, ∀ x : D.LatticeSite k,
    ((x : D.Torus) ∈ D.memberAt Ω n ↔
      ∃ y : D.LatticeSite n, (y : D.Torus) ∈ D.memberAt Ω n ∧ (x : D.Torus) ∈ cube (D := D) y) ∧
    ∀ y : D.LatticeSite n, (y : D.Torus) ∉ D.memberAt Ω n → (x : D.Torus) ∈ cube (D := D) y →
      (x : D.Torus) ∉ D.memberAt Ω n
def FineSitesPartitionIntoBlocks : Prop :=
  (∀ x : BareSite D.L D.m D.K,
      x ∈ sitesOfRegion D.K (Ω 0) ↔ ∃ p, D.IsBlockCentreOf Ω (x : D.Torus) p) ∧
    (∀ (x : BareSite D.L D.m D.K) (p q : Σ n : ℕ, D.LatticeSite n),
      D.IsBlockCentreOf Ω (x : D.Torus) p → D.IsBlockCentreOf Ω (x : D.Torus) q → p = q) ∧
    ∀ x : BareSite D.L D.m D.K, x ∈ sitesOfRegion D.K (Ω 0) →
      D.IsBlockCentreOf Ω (x : D.Torus) (D.blockCentre Ω (x : D.Torus))
def ExteriorBlocksInLowerLayer : Prop :=
  ∀ n, n + 1 ≤ D.t → ∀ y : D.LatticeSite (n + 1), D.IsExteriorSite Ω y →
    cube (D := D) y ⊆ D.memberAt Ω n ∧
    (∀ z : D.LatticeSite n, (z : D.Torus) ∈ coarseBlock (D := D) y → z ∈ D.layerSites Ω n) ∧
    (∃ z : D.LatticeSite n, (z : D.Torus) = y ∧ z ∈ D.layerSites Ω n) ∧
    fineBlock (D := D) y =
      ⋃ z : {z : D.LatticeSite n // (z : D.Torus) ∈ coarseBlock (D := D) y},
        fineBlock (D := D) z.1 ∧
    Pairwise fun z z' : {z : D.LatticeSite n // (z : D.Torus) ∈ coarseBlock (D := D) y} =>
      Disjoint (fineBlock (D := D) z.1) (fineBlock (D := D) z'.1)
def LayerBondKinds : Prop :=
  (∀ n, 1 ≤ n → n ≤ D.t → ∀ c ∈ D.layerBondSet Ω φ n,
      (D.IsInnerBond Ω c ∨ D.IsOutgoingBond Ω c) ∧
        ∀ y, D.IsOuterEndpoint Ω c y → D.IsExteriorSite Ω y) ∧
    (∀ c ∈ D.layerBondSet Ω φ 0,
      D.IsInnerBond Ω c ∨ (φ = BondFrame.star ∧ c ∈ frontierBonds D.K (Ω 0))) ∧
    ∀ n ≤ D.t, ∀ c : D.LevelBond n, D.IsInnerBond Ω c → c ∈ D.layerBondSet Ω φ n
def AverageSupports : Prop :=
  ∀ n ≤ D.t, ∀ c : D.LevelBond n,
    (∀ x : BareSite D.L D.m D.K, (x : D.Torus) ∈ fineBlock (D := D) c.1.source →
      ∀ e ∈ D.averagingSegment n x (bondAxis c),
        e.target - e.source = unitStep D.L D.m (levelDepth D.K 0) (bondAxis c) ∧
        (e.source : D.Torus) ∈ fineBlock (D := D) c.1.source ∪ fineBlock (D := D) c.1.target ∧
        (e.target : D.Torus) ∈ fineBlock (D := D) c.1.source ∪ fineBlock (D := D) c.1.target) ∧
    (c ∈ D.layerBondSet Ω φ n → 1 ≤ n →
      fineBlock (D := D) c.1.source ∪ fineBlock (D := D) c.1.target ⊆ D.memberAt Ω (n - 1) ∧
      Disjoint (fineBlock (D := D) c.1.source ∪ fineBlock (D := D) c.1.target)
        (D.memberAt Ω (n + 1)) ∧
      ∀ x : BareSite D.L D.m D.K, (x : D.Torus) ∈ fineBlock (D := D) c.1.source →
        ∀ e ∈ D.averagingSegment n x (bondAxis c),
          ∃ f ∈ interiorBonds D.K (Ω 0), f.1 = e) ∧
    (bondCorridorOf c).ncard = D.L ^ (n * (dimension - 1)) ∧
    ∀ e ∈ bondCorridorOf c,
      {x : BareSite D.L D.m D.K | (x : D.Torus) ∈ fineBlock (D := D) c.1.source ∧
        e.1 ∈ D.averagingSegment n x (bondAxis c)}.ncard = D.L ^ n ∧
      ∀ c' : D.LevelBond n, c' ≠ c →
        ∀ x : BareSite D.L D.m D.K, (x : D.Torus) ∈ fineBlock (D := D) c'.1.source →
          e.1 ∉ D.averagingSegment n x (bondAxis c')
def NeighbourLevelsClose : Prop :=
  ∀ e : BareOrientedBond D.L D.m D.K, e.source ∈ sitesOfRegion D.K (Ω 0) →
    e.target ∈ sitesOfRegion D.K (Ω 0) →
      D.blockLevel Ω (e.source : D.Torus) ≤ D.blockLevel Ω (e.target : D.Torus) + 1 ∧
      D.blockLevel Ω (e.target : D.Torus) ≤ D.blockLevel Ω (e.source : D.Torus) + 1
def SecondMemberCollarProperties : Prop :=
  D.secondMemberCollar Ω 3 ⊆ sitesOfRegion D.K (Ω 0) ∧
    D.secondMemberCollar Ω 2 ∩ frontierSites D.K (Ω 0) = ∅ ∧
    frontierSites D.K (Ω 0) ⊆ D.layerSites Ω 0 ∧
    ∀ e : BareBond D.L D.m D.K,
      (e.1.source ∈ D.secondMemberCollar Ω 2 ∨ e.1.target ∈ D.secondMemberCollar Ω 2) →
        e ∈ interiorBonds D.K (Ω 0)
end BaseParameters
def SequenceGeometry : Prop :=
  ∀ (D : SequenceDatum) (φ : BondFrame),
    D.MemberSitesInCubes D.region ∧
    D.FineSitesPartitionIntoBlocks D.region ∧
    D.ExteriorBlocksInLowerLayer D.region ∧
    D.LayerBondKinds D.region φ ∧
    D.AverageSupports D.region φ ∧
    D.NeighbourLevelsClose D.region ∧
    D.SecondMemberCollarProperties D.region
end SeparatedSequences
end YangMills.Construction
end
