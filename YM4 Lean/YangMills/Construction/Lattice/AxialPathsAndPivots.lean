import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BlocksAndCorridors
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K k : ℕ}
def IsBondEndpointPair {j : ℤ} (x y : Site L m j) : Prop :=
  ∃ b : Bond L m j, b.source = x ∧ b.target = y
def bondWithEnds {j : ℤ} (x y : Site L m j) : Bond L m j :=
  Classical.epsilon fun b => b.source = x ∧ b.target = y
def axialPathSite (c : BondAtLevel L m K (k + 1)) (μ : Fin 4) (ε : ℤ) (s : ℕ) :
    SiteAtLevel L m K k :=
  c.source.toSublattice (levelDepth K k) + ((s : ℤ) * ε) • unitStep L m (levelDepth K k) μ
def axialPathStepBond (c : BondAtLevel L m K (k + 1)) (μ : Fin 4) (ε : ℤ) (s : ℕ) :
    BondAtLevel L m K k :=
  bondWithEnds (axialPathSite c μ ε s) (axialPathSite c μ ε (s + 1))
def axialPathBonds (c : BondAtLevel L m K (k + 1)) (μ : Fin 4) (ε : ℤ) :
    List (BondAtLevel L m K k) :=
  (List.range L).map (axialPathStepBond c μ ε)
def JoinsEndBlocks (c : BondAtLevel L m K (k + 1)) (b : BondAtLevel L m K k) : Prop :=
  ((b.source : FourTorus L m) ∈ unitBlock c.source ∧ (b.target : FourTorus L m) ∈ unitBlock c.target) ∨
    ((b.source : FourTorus L m) ∈ unitBlock c.target ∧ (b.target : FourTorus L m) ∈ unitBlock c.source)
def bondSegment (c : BondAtLevel L m K (k + 1)) (μ : Fin 4) (ε : ℤ) : Set (FourTorus L m) :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ t ≤ L ∧
    p = (c.source : FourTorus L m) + pointOnAxis L m μ (t * ε * meshSize L (levelDepth K k))}
def MeshSizesInLevelUnits (L m K k : ℕ) : Prop :=
  toLevelUnits L K k (meshSize L (levelDepth K k)) = 1 ∧
  toLevelUnits L K k (meshSize L (levelDepth K (k + 1))) = L ∧
  toLevelUnits L K k (torusSide L m) = 2 * (L : ℝ) ^ (m + K - k)
structure AxialPathAndPivot (c : BondAtLevel L m K (k + 1)) (μ : Fin 4) (ε : ℤ) : Prop where
  isPositivelyOriented_iff : c.IsPositivelyOriented ↔ ε = 1
  site_zero : axialPathSite c μ ε 0 = c.source.toSublattice (levelDepth K k)
  site_last : axialPathSite c μ ε L = c.target.toSublattice (levelDepth K k)
  site_injOn : InjOn (axialPathSite c μ ε) (Iic L)
  consecutive_isBond : ∀ s : ℕ, s < L →
    IsBondEndpointPair (axialPathSite c μ ε s) (axialPathSite c μ ε (s + 1))
  stepBond_injOn : InjOn (axialPathStepBond c μ ε) (Iio L)
  isBondPath : IsBondPathFromTo (axialPathBonds c μ ε)
    (c.source.toSublattice (levelDepth K k)) (c.target.toSublattice (levelDepth K k))
  eq_of_length_eq : ∀ Γ : List (BondAtLevel L m K k), Γ.length = L →
    IsBondPathFromTo Γ (c.source.toSublattice (levelDepth K k)) (c.target.toSublattice (levelDepth K k)) →
      Γ = axialPathBonds c μ ε
  axialPath_eq : axialPath (c.source.toSublattice (levelDepth K k)) (c.target.toSublattice (levelDepth K k)) =
    axialPathBonds c μ ε
  unitBlock_inter_eq_empty : unitBlock c.source ∩ unitBlock c.target = ∅
  site_mem_source_block : ∀ s : ℕ, s ≤ (L - 1) / 2 →
    (axialPathSite c μ ε s : FourTorus L m) ∈ unitBlock c.source
  site_mem_target_block : ∀ s : ℕ, (L + 1) / 2 ≤ s → s ≤ L →
    (axialPathSite c μ ε s : FourTorus L m) ∈ unitBlock c.target
  stepBond_within_source_block : ∀ s : ℕ, s < (L - 1) / 2 →
    ((axialPathStepBond c μ ε s).source : FourTorus L m) ∈ unitBlock c.source ∧
      ((axialPathStepBond c μ ε s).target : FourTorus L m) ∈ unitBlock c.source
  stepBond_within_target_block : ∀ s : ℕ, (L - 1) / 2 < s → s < L →
    ((axialPathStepBond c μ ε s).source : FourTorus L m) ∈ unitBlock c.target ∧
      ((axialPathStepBond c μ ε s).target : FourTorus L m) ∈ unitBlock c.target
  middle_stepBond_mem : ((axialPathStepBond c μ ε ((L - 1) / 2)).source : FourTorus L m) ∈ unitBlock c.source ∧
    ((axialPathStepBond c μ ε ((L - 1) / 2)).target : FourTorus L m) ∈ unitBlock c.target
  stepBond_mem_bondCorridor_iff : ∀ s : ℕ, (s < L ∧ axialPathStepBond c μ ε s ∈
    (bondCorridor c : Set (BondAtLevel L m K k))) ↔ s = (L - 1) / 2
  joinsEndBlocks_iff : ∀ s : ℕ,
    (s < L ∧ JoinsEndBlocks c (axialPathStepBond c μ ε s)) ↔ s = (L - 1) / 2
  pivot_eq : (pivot c : BondAtLevel L m K k) = axialPathStepBond c μ ε ((L - 1) / 2)
  pivot_source : (pivot c : BondAtLevel L m K k).source =
    c.source.toSublattice (levelDepth K k) + ((((L - 1) / 2 : ℕ) : ℤ) * ε) • unitStep L m (levelDepth K k) μ
  pivot_target : (pivot c : BondAtLevel L m K k).target =
    c.source.toSublattice (levelDepth K k) + ((((L + 1) / 2 : ℕ) : ℤ) * ε) • unitStep L m (levelDepth K k) μ
  pivot_source_mem : ((pivot c : BondAtLevel L m K k).source : FourTorus L m) ∈ unitBlock c.source
  pivot_target_mem : ((pivot c : BondAtLevel L m K k).target : FourTorus L m) ∈ unitBlock c.target
  pivot_opposite : (pivot c.opposite : BondAtLevel L m K k) =
    (pivot c : BondAtLevel L m K k).opposite
  pivot_isPositivelyOriented_iff : (pivot c : BondAtLevel L m K k).IsPositivelyOriented ↔ c.IsPositivelyOriented
  pivot_source_mem_iff : ∀ Θ : Set (SiteAtLevel L m K (k + 1)),
    ((pivot c : BondAtLevel L m K k).source : FourTorus L m) ∈ refinedBlockUnion 1 Θ ↔ c.source ∈ Θ
  pivot_target_mem_iff : ∀ Θ : Set (SiteAtLevel L m K (k + 1)),
    ((pivot c : BondAtLevel L m K k).target : FourTorus L m) ∈ refinedBlockUnion 1 Θ ↔ c.target ∈ Θ
  pivot_endpoint_mem_iff : ∀ Θ : Set (SiteAtLevel L m K (k + 1)),
    (((pivot c : BondAtLevel L m K k).source : FourTorus L m) ∈ refinedBlockUnion 1 Θ ∨
      ((pivot c : BondAtLevel L m K k).target : FourTorus L m) ∈ refinedBlockUnion 1 Θ) ↔
        (c.source ∈ Θ ∨ c.target ∈ Θ)
  eq_of_pivot_eq : ∀ c' : BondAtLevel L m K (k + 1),
    (pivot c' : BondAtLevel L m K k) = pivot c → c' = c
  source_ne_target : c.source ≠ c.target
  bondSegment_inter_sublattice : bondSegment c μ ε ∩ (sublattice L m (levelDepth K (k + 1)) : Set (FourTorus L m)) =
    {(c.source : FourTorus L m), (c.target : FourTorus L m)}
  translated_pivot_isBond : ∀ ν : Fin 4, ν ≠ μ →
    IsBondEndpointPair ((pivot c : BondAtLevel L m K k).source + unitStep L m (levelDepth K k) ν)
      ((pivot c : BondAtLevel L m K k).target + unitStep L m (levelDepth K k) ν)
  translated_pivot_mem_bondCorridor : ∀ ν : Fin 4, ν ≠ μ →
    bondWithEnds ((pivot c : BondAtLevel L m K k).source + unitStep L m (levelDepth K k) ν)
      ((pivot c : BondAtLevel L m K k).target + unitStep L m (levelDepth K k) ν) ∈
        (bondCorridor c : Set (BondAtLevel L m K k))
  translated_pivot_ne_stepBond : ∀ ν : Fin 4, ν ≠ μ → ∀ s : ℕ, s < L →
    bondWithEnds ((pivot c : BondAtLevel L m K k).source + unitStep L m (levelDepth K k) ν)
      ((pivot c : BondAtLevel L m K k).target + unitStep L m (levelDepth K k) ν) ≠
        axialPathStepBond c μ ε s
def AxialPathCorridorAndPivotStatement : Prop :=
  ∀ (s : Conventions.StandingParameters) (k : ℕ), k < (s.K : ℕ) →
    MeshSizesInLevelUnits s.L s.m s.K k ∧
    ∀ c : BondAtLevel s.L s.m s.K (k + 1),
      (∃! q : Fin 4 × ℤ, IsAxialDisplacement (c.source.toSublattice (levelDepth s.K k))
        (c.target.toSublattice (levelDepth s.K k)) q.1 q.2) ∧
      ∃ (μ : Fin 4) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
        IsAxialDisplacement (c.source.toSublattice (levelDepth s.K k))
          (c.target.toSublattice (levelDepth s.K k)) μ (ε * (s.L : ℤ)) ∧
        AxialPathAndPivot c μ ε
end YangMills.Construction.PeriodicLattice
