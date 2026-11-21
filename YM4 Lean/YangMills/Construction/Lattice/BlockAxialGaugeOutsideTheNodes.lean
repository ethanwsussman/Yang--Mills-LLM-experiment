import YangMills.Construction.Lattice.AxialGauges
import YangMills.Construction.Lattice.TowersAndMinimalConfigurations
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def OffNodeAxialData (K k i : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j)) (P'' : Set (SiteAtLevel L m K (i + 1))) : Prop :=
  i < k ∧ k ≤ K ∧ IsDeterminingChain K k Ω ∧ B ⊆ determiningBondSet K k Ω ∧
    ∀ y ∈ P'', (y : FourTorus L m) ∈ Ω 0
def IsLinkDatum {K : ℕ} (B : Set (Σ j : ℕ, BondAtLevel L m K j))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) : Prop :=
  ∀ q ∈ B, V q.1 q.2 ∈ compactGaugeGroup ∧
    ((⟨q.1, q.2.opposite⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ B → V q.1 q.2.opposite = (V q.1 q.2)⁻¹)
def IsEndpointOf {K : ℕ} (B : Set (Σ j : ℕ, BondAtLevel L m K j)) (x : FourTorus L m) : Prop :=
  ∃ q ∈ B, (q.2.source : FourTorus L m) = x ∨ (q.2.target : FourTorus L m) = x
def endpointSitesAt {K : ℕ} (B : Set (Σ j : ℕ, BondAtLevel L m K j)) (i : ℕ) :
    Set (SiteAtLevel L m K i) :=
  {x | IsEndpointOf B (x : FourTorus L m)}
def linkConstraintSet (ω : ℝ) {K : ℕ} (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j)) (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {U | U ∈ gaugeFieldsInside K (Ω 0) ∧
    ∀ q ∈ B, averagingOnDeterminingSet ω K (Ω 0) U q.1 q.2 = V q.1 q.2}
def endpointFixingGaugeGroup {K : ℕ} (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j)) : Set (SiteAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {u | (∀ x ∈ (sitesIn (Ω 0) : Set (SiteAtLevel L m K 0)), u x ∈ compactGaugeGroup) ∧
    (∀ x ∉ (sitesIn (Ω 0) : Set (SiteAtLevel L m K 0)), u x = 1) ∧
    ∀ x : SiteAtLevel L m K 0, IsEndpointOf B (x : FourTorus L m) → u x = 1}
def endpointFixingOrbit {K : ℕ} (Ω : ℕ → Set (FourTorus L m)) (B : Set (Σ j : ℕ, BondAtLevel L m K j))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {W | ∃ u ∈ endpointFixingGaugeGroup Ω B,
    W = extendByOne (bondsInside (Ω 0)) (gaugeTransform u U)}
def IsConstrainedCritical (ω : ℝ) {K : ℕ} (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j)) (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  U ∈ linkConstraintSet ω Ω B V ∧
    ∀ (δ : ℝ) (c : ℝ → BondAtLevel L m K 0 → Matrices.ComplexMatrix2), 0 < δ →
      (∀ t ∈ Ioo (-δ) δ, c t ∈ linkConstraintSet ω Ω B V) →
      (∀ b r s, DifferentiableOn ℝ (fun t => c t b r s) (Ioo (-δ) δ)) → c 0 = U →
      deriv (fun t => actionInside K (Ω 0) (c t)) 0 = 0
def regularConstrainedCriticalSet (ω ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j)) (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {U | IsConstrainedCritical ω Ω B V U ∧ IsRegularField ε K k Ω U}
def HasUniqueCriticalOrbit (ω ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j)) (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) : Prop :=
  ∃ U ∈ regularConstrainedCriticalSet ω ε K k Ω B V,
    regularConstrainedCriticalSet ω ε K k Ω B V = endpointFixingOrbit Ω B U
def ContourTrivialOffEndpoints {K : ℕ} {i : ℕ} (B : Set (Σ j : ℕ, BondAtLevel L m K j))
    (P'' : Set (SiteAtLevel L m K (i + 1))) (W : BondAtLevel L m K i → Matrices.ComplexMatrix2) : Prop :=
  ∀ y ∈ P'', ∀ x ∈ sitesInBlock (levelDepth K i) y, (x : FourTorus L m) ≠ y →
    ¬ IsEndpointOf B (x : FourTorus L m) → meanContourHolonomy W y x = 1
def AveragingDefinedOnBlocks {K : ℕ} {i : ℕ} (X : Set (FourTorus L m))
    (P'' : Set (SiteAtLevel L m K (i + 1))) : Prop :=
  ∀ b ∈ (blockBonds (levelDepth K i) P'' : Set (BondAtLevel L m K i)),
    refinedBlock i b.source ⊆ X ∧ refinedBlock i b.target ⊆ X
def IsLevelBlockAxialOffEndpoints (ω : ℝ) (K k i : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j)) (P'' : Set (SiteAtLevel L m K (i + 1)))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  OffNodeAxialData K k i Ω B P'' ∧ U ∈ gaugeFieldsInside K (Ω 0) ∧
    AveragingDefinedOnBlocks (Ω 0) P'' ∧
    (∀ y ∈ P'', ∀ x ∈ sitesInBlock (levelDepth K i) y,
      HasContourMean (averagingOnDeterminingSet ω K (Ω 0) U i) y x) ∧
    ContourTrivialOffEndpoints B P'' (averagingOnDeterminingSet ω K (Ω 0) U i)
def IsBlockAxialOrbitRepresentative (ω ε : ℝ) (K k i : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j)) (P'' : Set (SiteAtLevel L m K (i + 1)))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  IsLinkDatum B V ∧ HasUniqueCriticalOrbit ω ε K k Ω B V ∧
    U ∈ regularConstrainedCriticalSet ω ε K k Ω B V ∧
    IsLevelBlockAxialOffEndpoints ω K k i Ω B P'' U
end PeriodicLattice
end YangMills.Construction
end
