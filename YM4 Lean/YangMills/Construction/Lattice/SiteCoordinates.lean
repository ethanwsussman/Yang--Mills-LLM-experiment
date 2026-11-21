import YangMills.Construction.Lattice.BlocksAndCorridors
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def halfPeriod (L m : ℕ) (j : ℤ) : ℕ := L ^ ((m : ℤ) + j).toNat
def offsetSite {L m : ℕ} {j : ℤ} (y : Site L m j) (n : Fin 4 → ℤ) : Site L m j :=
  y + ∑ μ, n μ • unitStep L m j μ
def axisLine {L m : ℕ} {j : ℤ} (y : Site L m j) (μ : Fin 4) : Set (Site L m j) :=
  {x | ∃ t : ℤ, x = y + t • unitStep L m j μ}
def IsMinimalResidue (M t : ℤ) : Prop := ∀ s : ℤ, s ≡ t [ZMOD M] → |t| ≤ |s|
def blockOffsets (L n : ℕ) : Set (Fin 4 → ℤ) := {p | ∀ μ, 2 * |p μ| ≤ (L : ℤ) ^ n - 1}
def refinedOffsetSite {L m : ℕ} {j : ℤ} (n : ℕ) (y : Site L m j) (p : Fin 4 → ℤ) :
    Site L m (j + n) :=
  offsetSite (y.toSublattice (j + n)) p
def SublatticeCoordinates (L m : ℕ) (j : ℤ) : Prop :=
  torusSide L m / meshSize L j = ((2 * halfPeriod L m j : ℕ) : ℝ) ∧
  0 < 2 * halfPeriod L m j ∧
  (∀ j' : ℤ, j ≤ j' → sublattice L m j ≤ sublattice L m j') ∧
  (∀ y x : Site L m j, ∃ n : Fin 4 → ℤ, x = offsetSite y n) ∧
  (∀ (y : Site L m j) (n n' : Fin 4 → ℤ), offsetSite y n = offsetSite y n' ↔
    ∀ μ, n μ ≡ n' μ [ZMOD (2 * halfPeriod L m j : ℕ)]) ∧
  (∀ (y : Site L m j) (μ : Fin 4), (axisLine y μ).ncard = 2 * halfPeriod L m j) ∧
  (∀ t : ℤ, |t| < (halfPeriod L m j : ℤ) →
    IsMinimalResidue (2 * halfPeriod L m j : ℕ) t ∧
      ∀ s : ℤ, s ≡ t [ZMOD (2 * halfPeriod L m j : ℕ)] →
        IsMinimalResidue (2 * halfPeriod L m j : ℕ) s → s = t) ∧
  (∀ (y : Site L m j) (n : Fin 4 → ℤ),
    (∀ μ, IsMinimalResidue (2 * halfPeriod L m j : ℕ) (n μ)) →
      TorusMetric.torusSupNorm ((offsetSite y n : FourTorus L m) - (y : FourTorus L m)) =
          meshSize L j * TorusMetric.supNormVec (fun μ => (n μ : ℝ)) ∧
      TorusMetric.torusL1Norm ((offsetSite y n : FourTorus L m) - (y : FourTorus L m)) =
          meshSize L j * TorusMetric.l1NormVec (fun μ => (n μ : ℝ)))
def LevelUnitCoordinates (L m K k : ℕ) : Prop :=
  toLevelUnits L K k (torusSide L m) = 2 * (L : ℝ) ^ (m + K - k) ∧
  (∀ (y : SiteAtLevel L m K k) (μ : Fin 4), (axisLine y μ).ncard = 2 * L ^ (m + K - k)) ∧
  (∀ i : ℕ, i ≤ K → ∀ b : BondAtLevel L m K i,
    toLevelUnits L K k |b.orientedLength| = (L : ℝ) ^ ((i : ℤ) - (k : ℤ))) ∧
  (∀ i : ℕ, k ≤ i → i ≤ K → sublattice L m (levelDepth K i) ≤ sublattice L m (levelDepth K k)) ∧
  (k < K → ∀ (c : BondAtLevel L m K (k + 1)) (μ : Fin 4),
    c.target - c.source = unitStep L m (levelDepth K (k + 1)) μ →
      c.target.toSublattice (levelDepth K k) =
        c.source.toSublattice (levelDepth K k) + (L : ℤ) • unitStep L m (levelDepth K k) μ)
def RefinedBlockCoordinates (L m : ℕ) (j : ℤ) (n : ℕ) : Prop :=
  ∀ y : Site L m j,
    (y : FourTorus L m) ∈ sublattice L m (j + n) ∧
    refinedBlock n y = (fun p => (refinedOffsetSite n y p : FourTorus L m)) '' blockOffsets L n ∧
    InjOn (refinedOffsetSite n y) (blockOffsets L n) ∧
    (refinedBlock n y).ncard = L ^ (4 * n) ∧
    refinedBlock 0 y = {(y : FourTorus L m)}
def RefinedBlockNesting (L m K k i j : ℕ) : Prop :=
  ∀ y : SiteAtLevel L m K k,
    refinedBlock i y =
      ⋃ x ∈ (sitesIn (refinedBlock (i - j) y) :
          Set (Site L m (levelDepth K k + ((i - j : ℕ) : ℤ)))),
        refinedBlock j x ∧
    (sitesIn (refinedBlock (i - j) y) :
        Set (Site L m (levelDepth K k + ((i - j : ℕ) : ℤ)))).PairwiseDisjoint (refinedBlock j)
def CoordinateDescription : Prop :=
  ∀ L m : ℕ, Odd L → 13 ≤ L → 0 < m →
    (∀ j : ℤ, -(m : ℤ) ≤ j → SublatticeCoordinates L m j) ∧
    (∀ K k : ℕ, 0 < K → k ≤ K → LevelUnitCoordinates L m K k) ∧
    (∀ (j : ℤ) (n : ℕ), -(m : ℤ) ≤ j → RefinedBlockCoordinates L m j n) ∧
    (∀ K k i j : ℕ, 0 < K → j ≤ i → i ≤ k → k ≤ K → RefinedBlockNesting L m K k i j)
end PeriodicLattice
end YangMills.Construction
