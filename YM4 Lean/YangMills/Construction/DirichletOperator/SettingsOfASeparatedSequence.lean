import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.RegionSequence.PastLastLevel
import YangMills.Construction.RegionSequence.SeparatedNestedRegions
import YangMills.Construction.Weighted.SeparatedRegions
import YangMills.Construction.Weighted.SeparatedSums
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace RegionSequence
def segmentToLifted (σ : Torus.TorusSegment 4) : TorusMetric.LiftedSegment :=
  ⟨σ.start, σ.start + σ.direction⟩
namespace NestedRegions
variable (𝒮 : NestedRegions)
def IsCubePartition (𝒞 : Set (Set 𝒮.Point)) : Prop :=
  ⋃₀ 𝒞 = univ ∧ 𝒞.Pairwise fun Q Q' => Disjoint (interior Q) (interior Q')
structure CubeGridFits (M : ℕ) : Prop where
  isCubePartition : ∀ n ≤ 𝒮.s, 𝒮.IsCubePartition (𝒮.cubeGrid M n)
  even_count : ∀ n ≤ 𝒮.s, ∃ N : ℕ, Even N ∧ 0 < N ∧
    𝒮.side = (N : ℝ) * ((M : ℝ) * 𝒮.scale n) ∧ (𝒮.cubeGrid M n).ncard = N ^ 4
  isCubeUnionAt : ∀ n ≤ 𝒮.s, ∀ Q ∈ 𝒮.cubeGrid M n, 𝒮.IsCubeUnionAt n Q
  eq_sUnion_lower : ∀ n < 𝒮.s, ∀ Q ∈ 𝒮.cubeGrid M (n + 1),
    ∃ 𝒞 ⊆ 𝒮.cubeGrid M n, Q = ⋃₀ 𝒞
structure IsTorusData (M R₁ : ℕ) : Prop where
  fourDimOdd : Blocking.FourDimOddFactor 4 𝒮.L
  blockNumber_power : ∃ k : ℕ, M = 𝒮.L ^ k
  le_blockNumber : 𝒮.L ≤ M
  gapNumber_power : ∃ k : ℕ, R₁ = 𝒮.L ^ k
  le_gapNumber : 𝒮.L ≤ R₁
  side_eq : ∃ k : ℕ, 0 < k ∧
    𝒮.side = 2 * k * ((M : ℝ) * ((𝒮.L : ℝ) ^ 𝒮.s * 𝒮.ξ))
variable {𝒮} in
def IsTorusData.toTorusData {M R₁ : ℕ} (h : 𝒮.IsTorusData M R₁) : Weighted.TorusData where
  L := 𝒮.L
  blocking := h.fourDimOdd
  blockNumber := M
  blockNumber_power := h.blockNumber_power
  le_blockNumber := h.le_blockNumber
  gapNumber := R₁
  gapNumber_power := h.gapNumber_power
  le_gapNumber := h.le_gapNumber
  bareSpacing := 𝒮.ξ
  bareSpacing_pos := 𝒮.ξ_pos
  top := 𝒮.s
  side := 𝒮.side
  side_multiple := h.side_eq
variable {𝒮} in
structure AgreesWithTorusData {M R₁ : ℕ} {h : 𝒮.IsTorusData M R₁}
    (B : Weighted.SeparatedChain h.toTorusData) : Prop where
  shell_torus : ∀ n, 𝒮.shellOf n = Torus.shell 𝒮.Ω n
  shell_data : ∀ n, 𝒮.shellOf n = B.layer n
  centres_torus : ∀ n, 𝒮.centresAt n = Torus.shellSites 𝒮.L 𝒮.ξ 𝒮.Ω n
  centres_data : ∀ n, 𝒮.centresAt n = B.layerSites n
  allCentres_torus : 𝒮.allCentres = Torus.unionShellSites 𝒮.L 𝒮.ξ 𝒮.s 𝒮.Ω
  allCentres_data : 𝒮.allCentres = B.allSites
  scale_torus : ∀ y ∈ 𝒮.allCentres, 𝒮.levelScale y = Torus.shellSpacing 𝒮.L 𝒮.ξ 𝒮.Ω y
  scale_data : ∀ y ∈ 𝒮.allCentres, 𝒮.levelScale y = B.siteScale y
  cell_torus : ∀ y ∈ 𝒮.allCentres, 𝒮.cellOf y = Torus.siteCube 𝒮.L 𝒮.ξ 𝒮.Ω y
  cell_data : ∀ y ∈ 𝒮.allCentres, 𝒮.cellOf y = B.siteCube y
  length_torus : ∀ Γ : List (Torus.TorusSegment 4),
    𝒮.chainWeight Γ = Torus.chainWeightedLength 𝒮.L 𝒮.ξ 𝒮.s 𝒮.Ω Γ
  length_data : ∀ Γ : List (Torus.TorusSegment 4),
    𝒮.chainWeight Γ = B.weightedLength (Γ.map segmentToLifted)
  dist_torus : ∀ y y' : 𝒮.Point,
    𝒮.weightedDist y y' = Torus.chainWeightedDist 𝒮.L 𝒮.ξ 𝒮.s 𝒮.Ω y y'
  dist_data : ∀ y y' : 𝒮.Point, 𝒮.weightedDist y y' = B.weightedDistance y y'
structure EndsAt (s' : ℕ) : Prop where
  le_s : s' ≤ 𝒮.s
  side_mem : ∃ k : ℤ, 𝒮.side = (k : ℝ) * (2 * Torus.scaleSpacing 𝒮.L 𝒮.ξ s')
  Ω_eq_empty_of_lt : ∀ n, s' < n → 𝒮.Ω n = ∅
variable {𝒮} in
def EndsAt.truncate {s' : ℕ} (h : 𝒮.EndsAt s') : NestedRegions :=
  { 𝒮 with
    s := s'
    side_mem_zmultiples := h.side_mem
    Ω_succ_subset := fun n hn => 𝒮.Ω_succ_subset n (hn.trans_le h.le_s)
    isCubeUnion_Ω := fun n hn => 𝒮.isCubeUnion_Ω n (hn.trans h.le_s)
    Ω_eq_empty := h.Ω_eq_empty_of_lt }
variable {𝒮} in
def EqOnCentres {s' : ℕ} (h : 𝒮.EndsAt s') (ω : 𝒮.Coarse) (ω' : h.truncate.Coarse) : Prop :=
  ∀ (y : 𝒮.Point) (hy : y ∈ 𝒮.allCentres) (hy' : y ∈ h.truncate.allCentres), ω ⟨y, hy⟩ = ω' ⟨y, hy'⟩
variable {𝒮} in
structure TruncationAgrees {s' : ℕ} (h : 𝒮.EndsAt s') : Prop where
  shellOf_eq : ∀ n, 𝒮.shellOf n = h.truncate.shellOf n
  centresAt_eq : ∀ n, 𝒮.centresAt n = h.truncate.centresAt n
  allCentres_eq : 𝒮.allCentres = h.truncate.allCentres
  cellOf_eq : ∀ y, 𝒮.cellOf y = h.truncate.cellOf y
  coarseBonds_eq : ∀ n, 𝒮.coarseBonds n = h.truncate.coarseBonds n
  siteFns_eq : 𝒮.siteFns = h.truncate.siteFns
  oneForms_eq : 𝒮.oneForms = h.truncate.oneForms
  coarseInner_eq : ∀ (ω₁ ω₂ : 𝒮.Coarse) (ω₁' ω₂' : h.truncate.Coarse),
    EqOnCentres h ω₁ ω₁' → EqOnCentres h ω₂ ω₂' →
      coarseInner ω₁ ω₂ = coarseInner (𝒮 := h.truncate) ω₁' ω₂'
  dirichletLap_eq : ∀ f : 𝒮.FineSite → ℝ,
    dirichletLap f = dirichletLap (𝒮 := h.truncate) f
  dDir_eq : ∀ f : 𝒮.FineSite → ℝ, dDir f = dDir (𝒮 := h.truncate) f
  dDirAdj_eq : ∀ A : 𝒮.FineBond → ℝ,
    dDirAdj A = dDirAdj (𝒮 := h.truncate) A
  curlSqDir_eq : ∀ A : 𝒮.FineBond → ℝ,
    curlSqDir A = curlSqDir (𝒮 := h.truncate) A
  blockAvg_eq : ∀ f : 𝒮.FineSite → ℝ,
    EqOnCentres h (blockAvg f) (blockAvg (𝒮 := h.truncate) f)
  blockAvgAdj_eq : ∀ (ω : 𝒮.Coarse) (ω' : h.truncate.Coarse),
    EqOnCentres h ω ω' → blockAvgAdj ω = blockAvgAdj (𝒮 := h.truncate) ω'
  bondAvg_eq : ∀ (n : ℕ) (A : 𝒮.FineBond → ℝ) (c : 𝒮.BondAt n),
    bondAvg n A c = bondAvg (𝒮 := h.truncate) n A c
  weightMul_eq : ∀ (ω : 𝒮.Coarse) (ω' : h.truncate.Coarse),
    EqOnCentres h ω ω' →
      EqOnCentres h (weightMul ω) (weightMul (𝒮 := h.truncate) ω')
  gaugeLap_eq : ∀ f : 𝒮.FineSite → ℝ, gaugeLap f = gaugeLap (𝒮 := h.truncate) f
  gaugeGreenOp_eq : ∀ f : 𝒮.FineSite → ℝ, gaugeGreenOp f = gaugeGreenOp (𝒮 := h.truncate) f
  avgKernel_eq : 𝒮.avgKernel = h.truncate.avgKernel
  rangeProj_eq : ∀ f : 𝒮.FineSite → ℝ,
    rangeProj f = rangeProj (𝒮 := h.truncate) f
  complProj_eq : ∀ f : 𝒮.FineSite → ℝ,
    complProj f = complProj (𝒮 := h.truncate) f
  avgOp_eq : ∀ A : 𝒮.FineBond → ℝ,
    avgOp A = avgOp (𝒮 := h.truncate) A
  baseOp_eq : ∀ A : 𝒮.FineBond → ℝ, baseOp A = baseOp (𝒮 := h.truncate) A
  longOp_eq : ∀ A : 𝒮.FineBond → ℝ,
    longOp A = longOp (𝒮 := h.truncate) A
  baseGreen_eq : ∀ A : 𝒮.FineBond → ℝ, baseGreen A = baseGreen (𝒮 := h.truncate) A
  weightedDist_eq : ∀ y y' : 𝒮.Point, 𝒮.weightedDist y y' = h.truncate.weightedDist y y'
end NestedRegions
end RegionSequence
namespace Propagator.SeparatedRegionChain
open RegionSequence
variable (P : SeparatedRegionChain)
structure IsRegionChain : Prop where
  side_mem : ∃ k : ℤ, P.sideInUnits = (k : ℝ) * (2 * Torus.scaleSpacing P.L P.baseMesh P.level)
  isCubeUnion : ∀ n ≤ P.level, Torus.IsCubeUnion (Torus.scaleSpacing P.L P.baseMesh n) (P.regionInUnits n)
theorem baseMesh_pos : 0 < P.baseMesh := zpow_pos P.L_pos _
variable {P} in
def IsRegionChain.toNestedRegions (h : P.IsRegionChain)
    (𝔟 : Set (Dirichlet.LatticeBond 4 P.sideInUnits P.baseMesh))
    (inner_subset : ∀ b : Dirichlet.LatticeBond 4 P.sideInUnits P.baseMesh,
      (b.source : Torus.PeriodicTorus 4 P.sideInUnits) ∈ P.regionInUnits 0 →
      (b.target : Torus.PeriodicTorus 4 P.sideInUnits) ∈ P.regionInUnits 0 → b ∈ 𝔟)
    (subset_star : ∀ b ∈ 𝔟, (b.source : Torus.PeriodicTorus 4 P.sideInUnits) ∈ P.regionInUnits 0 ∨
      (b.target : Torus.PeriodicTorus 4 P.sideInUnits) ∈ P.regionInUnits 0) : NestedRegions where
  L := P.L
  odd_L := P.isAdmissible.1
  thirteen_le_L := P.isAdmissible.2
  ξ := P.baseMesh
  ξ_pos := P.baseMesh_pos
  side := P.sideInUnits
  side_pos := P.sideInUnits_pos
  s := P.level
  side_mem_zmultiples := h.side_mem
  Ω := P.regionInUnits
  Ω_succ_subset := fun n hn => image_mono (P.separated.2 n hn).1
  isCubeUnion_Ω := h.isCubeUnion
  Ω_eq_empty := fun n hn => by simp [regionInUnits, P.empty_past n hn]
  bonds := 𝔟
  mem_bonds_of_mem := inner_subset
  mem_of_mem_bonds := subset_star
end Propagator.SeparatedRegionChain
namespace RegionSequence
def SettingsCoherent : Prop :=
  (∀ (𝒮 : NestedRegions) (M R₁ : ℕ), Torus.IsPowerGe 𝒮.L M → Torus.IsPowerGe 𝒮.L R₁ →
      (∃ k : ℤ, 𝒮.side = (k : ℝ) * (2 * ((M : ℝ) * 𝒮.scale 𝒮.s))) →
      𝒮.CubeGridFits M) ∧
    (∀ (𝒮 : NestedRegions) (M R₁ : ℕ), 𝒮.IsGapSeparated M R₁ → (𝒮.Ω 0).Nonempty →
      Torus.IsSeparatedChain 𝒮.L 𝒮.ξ M R₁ 𝒮.s 𝒮.Ω ∧
      ∃ (h : 𝒮.IsTorusData M R₁) (B : Weighted.SeparatedChain h.toTorusData),
        B.stage = 𝒮.Ω ∧ NestedRegions.AgreesWithTorusData B) ∧
    (∀ P : Propagator.SeparatedRegionChain, P.L ≤ P.blockCount →
      ∃ h : P.IsRegionChain,
        ∀ (𝔟 : Set (Dirichlet.LatticeBond 4 P.sideInUnits P.baseMesh))
          (inner_subset : ∀ b : Dirichlet.LatticeBond 4 P.sideInUnits P.baseMesh,
            (b.source : Torus.PeriodicTorus 4 P.sideInUnits) ∈ P.regionInUnits 0 →
              (b.target : Torus.PeriodicTorus 4 P.sideInUnits) ∈ P.regionInUnits 0 → b ∈ 𝔟)
          (subset_star : ∀ b ∈ 𝔟, (b.source : Torus.PeriodicTorus 4 P.sideInUnits) ∈ P.regionInUnits 0 ∨
            (b.target : Torus.PeriodicTorus 4 P.sideInUnits) ∈ P.regionInUnits 0),
          (h.toNestedRegions 𝔟 inner_subset subset_star).IsLevelUnitChain P.K P.m P.blockCount
              P.gapSize ∧
            ∃ e : (h.toNestedRegions 𝔟 inner_subset subset_star).EndsAt
                (Torus.lastNonemptyIndex P.regionInUnits),
              e.truncate.IsGapSeparated P.blockCount P.gapSize ∧
              NestedRegions.TruncationAgrees e ∧
              ∀ y y' : PeriodicLattice.FourTorus P.L P.m,
                ENNReal.ofReal (e.truncate.weightedDist (P.toUnits y) (P.toUnits y')) =
                  P.layerDist y y') ∧
    (∀ (𝒮 : NestedRegions) (K m M R₁ : ℕ), 𝒮.L ≤ M → 𝒮.IsLevelUnitChain K m M R₁ →
      ∃ e : 𝒮.EndsAt (Torus.lastNonemptyIndex 𝒮.Ω), e.truncate.IsGapSeparated M R₁ ∧
        NestedRegions.TruncationAgrees e) ∧
    (∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
      AntitoneOn (Weighted.separatedSumConst 4 L) (Ioi 0) ∧
        AntitoneOn (Weighted.separatedSumRadius 4 L) (Ioi 0))
end RegionSequence
end YangMills.Construction
end
