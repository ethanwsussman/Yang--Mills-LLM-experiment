import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.ObjectsAtASiteOnTheBlock
import YangMills.Construction.Lattice.OneStepSchemes
import YangMills.Construction.Lattice.SiteBoxes
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K i : ℕ}
structure BlockBondContainment (y : SiteAtLevel L m K (i + 1)) (c : BondAtLevel L m K (i + 1)) :
    Prop where
  unitBlock_subset : unitBlock y ⊆ bondDoubleBlock c
  bonds_subset : (coarseSiteBlockBonds y).bonds ⊆ (bondsInDoubleBlock c : Set (BondAtLevel L m K i))
  bonds_eq : (bondsInDoubleBlock c : Set (BondAtLevel L m K i)) =
    (bondsWithin (sitesIn (bondDoubleBlock c) : Set (SiteAtLevel L m K i))).bonds
  far_endpoint : ∀ z : SiteAtLevel L m K (i + 1),
    (c.source = y ∧ c.target = z) ∨ (c.target = y ∧ c.source = z) →
    (z : FourTorus L m) ∈ sublattice L m (levelDepth K i) ∧ (z : FourTorus L m) ∉ unitBlock y
structure UnitBlockPaths (y : SiteAtLevel L m K (i + 1)) : Prop where
  center_mem : (y : FourTorus L m) ∈ unitBlock y
  endpoints_mem : ∀ b ∈ (coarseSiteBlockBonds y).bonds,
    b.source ∈ coarseSiteBlock y ∧ b.target ∈ coarseSiteBlock y
  xor_oriented : ∀ b : BondAtLevel L m K i,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  exists_oriented_bond : ∃ c : BondAtLevel L m K (i + 1),
    c.IsPositivelyOriented ∧ (c.source = y ∨ c.target = y)
  oriented_bond : ∀ c : BondAtLevel L m K (i + 1), c.IsPositivelyOriented →
    (c.source = y ∨ c.target = y) → BlockBondContainment y c
  comb_defined : ∀ x ∈ coarseSiteBlock y, ∃ P : Set (SiteAtLevel L m K i),
    IsSiteBox (levelDepth K i) P ∧ schemeBaseSite .cornered (levelDepth K i) y ∈ P ∧ x ∈ P
  comb_subset : ∀ x ∈ coarseSiteBlock y,
    ∀ b ∈ coordinateComb (schemeBaseSite .cornered (levelDepth K i) y) x,
    b ∈ (coarseSiteBlockBonds y).bonds
  contour_subset : ∀ x ∈ coarseSiteBlock y, ∀ Γ ∈ contourSet y x, ∀ b ∈ Γ,
    b ∈ (coarseSiteBlockBonds y).bonds
structure ExpLogGaugeGroupFacts : Prop where
  matExp_mem_complex : ∀ A ∈ ComplexMatrix2.traceless,
    ComplexMatrix2.matExp (Complex.I • A) ∈ complexGaugeGroup
  matExp_mem_compact : ∀ A ∈ ComplexMatrix2.hermitianTraceless,
    ComplexMatrix2.matExp (Complex.I • A) ∈ compactGaugeGroup
  logSeries_mem : ∀ X ∈ complexGaugeGroup, ComplexMatrix2.operatorNorm (X - 1) < 1 →
    Complex.I⁻¹ • ComplexMatrix2.logSeries X ∈ ComplexMatrix2.traceless ∧
      (X ∈ compactGaugeGroup →
        Complex.I⁻¹ • ComplexMatrix2.logSeries X ∈ ComplexMatrix2.hermitianTraceless ∧
        X ∈ ComplexMatrix2.unitaryLogDomain ∧
        ComplexMatrix2.logSeries X = ComplexMatrix2.unitaryLog X)
def IsExpTwistedFieldOnBlock (y : SiteAtLevel L m K (i + 1))
    (W₀ a W : BondAtLevel L m K i → ComplexMatrix2) : Prop :=
  IsGaugeField complexGaugeGroup (coarseSiteBlockBonds y).bonds W ∧
    ∀ b ∈ (coarseSiteBlockBonds y).bonds, b.IsPositivelyOriented →
      W b = ComplexMatrix2.matExp (Complex.I • a b) * W₀ b
def UniqueExpTwistedFieldOnBlock (y : SiteAtLevel L m K (i + 1))
    (W₀ a : BondAtLevel L m K i → ComplexMatrix2) : Prop :=
  IsReversalClosed (coarseSiteBlockBonds y).bonds ∧
    (∃ W, IsExpTwistedFieldOnBlock y W₀ a W) ∧
    ∀ W W', IsExpTwistedFieldOnBlock y W₀ a W →
      IsExpTwistedFieldOnBlock y W₀ a W' → ∀ b ∈ (coarseSiteBlockBonds y).bonds, W b = W' b
def ConjugatedExpMemGaugeGroups : Prop :=
  (∀ V ∈ complexGaugeGroup, ∀ Vl ∈ complexGaugeGroup, ∀ Vr ∈ complexGaugeGroup,
    ∀ A ∈ ComplexMatrix2.traceless,
    Vl * ComplexMatrix2.matExp (Complex.I • A) * V * Vr⁻¹ * V⁻¹ ∈ complexGaugeGroup) ∧
  ∀ V ∈ compactGaugeGroup, ∀ Vl ∈ compactGaugeGroup, ∀ Vr ∈ compactGaugeGroup,
    ∀ A ∈ ComplexMatrix2.hermitianTraceless,
    Vl * ComplexMatrix2.matExp (Complex.I • A) * V * Vr⁻¹ * V⁻¹ ∈ compactGaugeGroup
def UnitBlockPathsAndLogarithm : Prop :=
  (∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    ∀ m K i : ℕ, 0 < m → i < K →
    ∀ y : SiteAtLevel L m K (i + 1), UnitBlockPaths y) ∧
  ExpLogGaugeGroupFacts ∧
  (∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    ∀ m K i : ℕ, 0 < m → i < K →
    ∀ (y : SiteAtLevel L m K (i + 1)) (ℬ₀ 𝒜 : Set (BondAtLevel L m K i))
      (W₀ a : BondAtLevel L m K i → ComplexMatrix2),
      IsGaugeFieldNearBlock y ℬ₀ W₀ → IsLieFieldNearBlock y 𝒜 a →
      UniqueExpTwistedFieldOnBlock y W₀ a) ∧
  ConjugatedExpMemGaugeGroups
end YangMills.Construction.PeriodicLattice
end
