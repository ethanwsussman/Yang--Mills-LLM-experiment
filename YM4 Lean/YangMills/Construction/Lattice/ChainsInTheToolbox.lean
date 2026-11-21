import YangMills.Construction.Lattice.AveragesOnUnionsOfBlocks
import YangMills.Construction.Lattice.SmallPlaquetteThresholdInTheToolbox
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m K : ℕ}
def DescendingBondChain : (k : ℕ) → BondAtLevel L m K k → Type
  | 0, _ => PUnit
  | k + 1, c => Σ x : ↥(sitesInBlock (levelDepth K k) c.source),
      Σ e : {e : BondAtLevel L m K k // e ∈ crossingPath c x.1}, DescendingBondChain k e.1
def descendingChainEnd : (k : ℕ) → (c : BondAtLevel L m K k) → DescendingBondChain k c →
    BondAtLevel L m K 0
  | 0, c, _ => c
  | k + 1, _, t => descendingChainEnd k t.2.1.1 t.2.2
def descendingChainTransport (s : AveragingScheme) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (k : ℕ) → (c : BondAtLevel L m K k) → DescendingBondChain k c → ComplexMatrix2
  | 0, _, _ => 1
  | k + 1, c, t =>
      contourHolonomy s (iteratedAverage s k U) c.source t.1.1 *
        pathHolonomy (iteratedAverage s k U) (axialPath t.1.1 t.2.1.1.source) *
        descendingChainTransport s U k t.2.1.1 t.2.2
def enclosingSiteAt (j : ℕ) (x : SiteAtLevel L m K 0) : SiteAtLevel L m K j :=
  Classical.epsilon fun z : SiteAtLevel L m K j => x ∈ blockSitesBelow 0 ({z} : Set _)
def nestedBlockTransport (s : AveragingScheme) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (k : ℕ) → SiteAtLevel L m K k → SiteAtLevel L m K 0 → ComplexMatrix2
  | 0, _, _ => 1
  | 1, y, x => contourHolonomy s (iteratedAverage s 0 U) y x
  | n + 2, y, x =>
      contourHolonomy s (iteratedAverage s (n + 1) U) y (enclosingSiteAt (n + 1) x) *
        nestedBlockTransport s U (n + 1) (enclosingSiteAt (n + 1) x) x
structure SmallCurvatureOnBlocks {k : ℕ} (Z : Set (SiteAtLevel L m K k)) (α₀ : ℝ)
    (U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop where
  gaugeField : IsGaugeFieldWithin (blockSitesBelow 0 Z) U
  plaquettes : ∀ p : PlaquetteAtLevel L m K 0, p.LiesIn (blockSitesBelow 0 Z) →
    ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) ≤ α₀ * finestMeshInLevelUnits L k ^ 2
def IsChainTransportConstant (L : ℕ) (κ : ℝ) : Prop :=
  ∀ m K k : ℕ, 0 < m → 1 ≤ k → k ≤ K → ∀ (s : AveragingScheme) (α₀ : ℝ), 0 < α₀ →
    α₀ ≤ smallPlaquetteThreshold L → ∀ U : BondAtLevel L m K 0 → ComplexMatrix2,
    (∀ c : BondAtLevel L m K k, c.IsPositivelyOriented → SmallCurvatureOnBlocks (bondEnds c) α₀ U →
      ∀ (t : DescendingBondChain k c) (Γ : List (BondAtLevel L m K 0)),
        IsBondPathFromTo Γ (finestBaseSite s K k c.source) (descendingChainEnd k c t).source →
        Γ.length ≤ 16 * L ^ k →
        (∀ e ∈ Γ, e.LiesIn (blockSitesBelow 0 (bondEnds c))) →
          ComplexMatrix2.operatorNorm (descendingChainTransport s U k c t - pathHolonomy U Γ) ≤
            κ * α₀) ∧
    (∀ y : SiteAtLevel L m K k, SmallCurvatureOnBlocks ({y} : Set _) α₀ U →
      ∀ x ∈ blockSitesBelow 0 ({y} : Set (SiteAtLevel L m K k)),
      ∀ Γ : List (BondAtLevel L m K 0), IsBondPathFromTo Γ (finestBaseSite s K k y) x →
        Γ.length ≤ 16 * L ^ k →
        (∀ e ∈ Γ, e.LiesIn (blockSitesBelow 0 ({y} : Set (SiteAtLevel L m K k)))) →
          ComplexMatrix2.operatorNorm (nestedBlockTransport s U k y x - pathHolonomy U Γ) ≤
            κ * α₀)
def chainTransportConstant (L : ℕ) : ℝ := Classical.epsilon (IsChainTransportConstant L)
end YangMills.Construction.PeriodicLattice
