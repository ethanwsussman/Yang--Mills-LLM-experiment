import YangMills.Construction.Lattice.AveragesAndPropagatorsAtAConfiguration
import YangMills.Construction.Lattice.GaugeFunctionalOfOrderK
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def DescendingChain : (k : ℕ) → BondAtLevel L m K k → Type
  | 0, _ => PUnit
  | k + 1, c => Σ x : ↥(sitesInBlock (levelDepth K k) c.source),
      Σ e : {e : BondAtLevel L m K k // e ∈ crossingPath c x.1}, DescendingChain k e.1
def chainBottom : (k : ℕ) → (c : BondAtLevel L m K k) → DescendingChain k c → BondAtLevel L m K 0
  | 0, c, _ => c
  | k + 1, _, t => chainBottom k t.2.1.1 t.2.2
def chainHolonomy (s : AveragingScheme) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    (k : ℕ) → (c : BondAtLevel L m K k) → DescendingChain k c → Matrices.ComplexMatrix2
  | 0, _, _ => 1
  | k + 1, c, t =>
      (contourHolonomy s (iteratedAverage s k U) c.source t.1.1 *
        pathHolonomy (iteratedAverage s k U) (axialPath t.1.1 t.2.1.1.source)) *
      chainHolonomy s U k t.2.1.1 t.2.2
def schemeBlockTransport (s : AveragingScheme) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (k : ℕ) (y : SiteAtLevel L m K k) (x : SiteAtLevel L m K 0) : Matrices.ComplexMatrix2 :=
  match s with
  | .centred => ancestorTransport U x k
  | .cornered => blockTransport U k y x
def IsChainHolonomyConstant (L : ℕ) (κ : ℝ) : Prop :=
  ∀ (m K k : ℕ) (α₀ : ℝ) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) (s : AveragingScheme),
    0 < m → IsPropagatorSetting k α₀ U →
    (∀ (c : PositiveBondAtLevel L m K k) (t : DescendingChain k c.1) (γ : List (BondAtLevel L m K 0)),
      IsBondPathFromTo γ (finestBaseSite s K k c.1.source) (chainBottom k c.1 t).source →
      γ.length ≤ 16 * L ^ k → (∀ e ∈ γ, e.LiesIn (sitesInBondBlockPair 0 c.1)) →
        Matrices.ComplexMatrix2.operatorNorm (chainHolonomy s U k c.1 t - pathHolonomy U γ) ≤ κ * α₀) ∧
    ∀ (y : SiteAtLevel L m K k) (x : SiteAtLevel L m K 0) (γ : List (BondAtLevel L m K 0)),
      x ∈ blockSitesAtLevel 0 y → IsBondPathFromTo γ (finestBaseSite s K k y) x →
      γ.length ≤ 16 * L ^ k → (∀ e ∈ γ, e.LiesIn (blockSitesAtLevel 0 y)) →
        Matrices.ComplexMatrix2.operatorNorm (schemeBlockTransport s U k y x - pathHolonomy U γ) ≤
          κ * α₀
def chainHolonomyConstant (L : ℕ) : ℝ := Classical.epsilon (IsChainHolonomyConstant L)
end YangMills.Construction.PeriodicLattice
