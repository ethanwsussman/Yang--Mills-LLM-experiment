import YangMills.Construction.SeparatedSequences.SiteSumThresholds
import YangMills.Construction.SeparatedSequences.SupDistanceInLevelUnits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators TorusMetric
namespace SeparatedClasses.ApexSumsAndMeetingBlocks
variable (C : ClassData) (Ω : ℕ → Set C.Point)
def ChainDistGrowsWithLevel : Prop :=
  ∀ y y' : C.Apex Ω,
    ENNReal.ofReal ((C.gapSize : ℝ) * (C.blockSize : ℝ) *
        max (|(y.level : ℝ) - (y'.level : ℝ)| - 1) 0) ≤
      C.chainDist Ω y.point y'.point
def MeshRatioBound (a : ℝ) : Prop :=
  ∀ s : ℝ, 0 ≤ s →
    s * Real.log (C.L : ℝ) ≤ a * ((C.gapSize : ℝ) * (C.blockSize : ℝ)) →
    ∀ y y' : C.Apex Ω,
      max (y.mesh / y'.mesh) (y'.mesh / y.mesh) ^ s ≤
        (C.L : ℝ) ^ s * Real.exp (a * (C.chainDist Ω y.point y'.point).toReal)
def ExpSumOverApexesBounded (a : ℝ) : Prop :=
  SeparatedSequences.siteSumThreshold 4 C.L a ≤ (C.gapSize : ℝ) * (C.blockSize : ℝ) →
    ∀ y : C.Apex Ω,
      ∑ᶠ y'' : C.Apex Ω, Real.exp (-a * (C.chainDist Ω y.point y''.point).toReal) ≤
        SeparatedSequences.siteSumMajorant 4 C.L a
def MeetingBlocksAdjacent : Prop :=
  ∀ y y' : C.Apex Ω, (y.block ∩ y'.block).Nonempty →
    |(y.level : ℝ) - (y'.level : ℝ)| ≤ 1 ∧ C.chainDist Ω y.point y'.point ≤ 4
def MeetingBlocksCount : Prop :=
  ∀ y : C.Apex Ω, {z : C.Apex Ω | (z.block ∩ y.block).Nonempty}.encard ≤ ((C.L + 2) ^ 4 : ℕ)
def NearSitesInMeetingBlocks : Prop :=
  ∀ x x' : C.BareSite, (x : C.Point) ∈ Ω 0 → (x' : C.Point) ∈ Ω 0 →
    C.supDist x x' ≤ C.finestMesh →
    ∃ z z' : C.Apex Ω, (x : C.Point) ∈ z.block ∧ (x' : C.Point) ∈ z'.block ∧
      (z.block = z'.block ∨ (z.block ∩ z'.block).Nonempty)
def BondAnchorNearBlock : Prop :=
  ∀ (y : C.Apex Ω) (b : C.BareBond), b.1 ∈ ClassData.bondsWithin y.block →
    (ClassData.anchorSite Ω b : C.Point) ∈ y.block ∨
      ∃ z : C.Apex Ω, (ClassData.anchorSite Ω b : C.Point) ∈ z.block ∧ (z.block ∩ y.block).Nonempty
def SitesNearApexInBase : Prop :=
  ∀ (y : C.Apex Ω) (x : C.BareSite),
    (1 ≤ y.level → C.supDist x y.point ≤ 2 * y.mesh → (x : C.Point) ∈ Ω 0) ∧
      (C.supDist x y.point < y.mesh → (x : C.Point) ∈ Ω 0)
def ApexesOfNearSites : Prop :=
  ∀ (y z : C.Apex Ω) (x : C.BareSite), (x : C.Point) ∈ Ω 0 →
    C.supDist x y.point ≤ 2 * y.mesh → (x : C.Point) ∈ z.block →
    (C.L : ℝ)⁻¹ * y.mesh ≤ z.mesh ∧ z.mesh ≤ (C.L : ℝ) * y.mesh ∧
      C.chainDist Ω y.point z.point ≤ ENNReal.ofReal (4 * (2 * (C.L : ℝ) + 1))
def ChainDistDominatesLOne : Prop :=
  ∀ p p' : C.Point,
    ENNReal.ofReal ((C.coarseMesh (C.lastNonempty Ω))⁻¹ * C.lOneDist p p') ≤
      C.chainDist Ω p p'
def ExpansionEndpointsClose : Prop :=
  ∀ (φ : BondFrame), ∀ c ∈ C.expansionSet Ω φ,
    C.chainDist Ω (c.2.1.source : C.Point) (c.2.1.target : C.Point) ≤
      ENNReal.ofReal (((C.L : ℝ) + 1) / 2)
def Statement : Prop :=
  ∀ (C : ClassData), C.L ≤ C.blockSize → ∀ Ω ∈ C.separatedClass,
    ChainDistGrowsWithLevel C Ω ∧
      (∀ a : ℝ, 0 < a → MeshRatioBound C Ω a ∧ ExpSumOverApexesBounded C Ω a) ∧
      MeetingBlocksAdjacent C Ω ∧ MeetingBlocksCount C Ω ∧ NearSitesInMeetingBlocks C Ω ∧
      BondAnchorNearBlock C Ω ∧ SitesNearApexInBase C Ω ∧
      ApexesOfNearSites C Ω ∧ ChainDistDominatesLOne C Ω ∧ ExpansionEndpointsClose C Ω
end SeparatedClasses.ApexSumsAndMeetingBlocks
end YangMills.Construction
end
