import YangMills.Construction.Lattice.AveragesOfAConfigurationOnARegion
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import YangMills.Construction.Lattice.MinimalConfigurationsAtComplexData
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def IsChainFromIndex (K k : ℕ) (i : ℤ) (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  -(m : ℤ) ≤ i ∧ 1 ≤ k ∧ k ≤ K ∧ IsDeterminingChain K k Ω ∧
    ∀ q ≤ k, ∃ c : ℤ, i ≤ c ∧ c ≤ levelDepth K q ∧ IsPartitionRegion c (Ω q)
theorem IsChainFromIndex.index_le_levelDepth {K k : ℕ} {i : ℤ} {Ω : ℕ → Set (FourTorus L m)}
    (h : IsChainFromIndex K k i Ω) : i ≤ levelDepth K k := by
  obtain ⟨c, hic, hcd, -⟩ := h.2.2.2.2 k le_rfl
  exact hic.trans hcd
def AndAveragesFormed {K n : ℕ} (Ω₀ : Set (FourTorus L m)) (C : Set (BondAtLevel L m K n))
    (P : Prop) : Prop :=
  (∀ c ∈ C, IsAverageFormedOnRegion Ω₀ c) ∧ P
def AveragesFormedOn {K : ℕ} (Ω₀ : Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j)) : Prop :=
  ∀ q ∈ B, IsAverageFormedOnRegion Ω₀ q.2
def formedLinkConstraintSet (ω : ℝ) {K : ℕ} (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {U | AveragesFormedOn (Ω 0) B ∧ U ∈ linkConstraintSet ω Ω B V}
def IsFormedConstrainedCritical (ω : ℝ) {K : ℕ} (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  U ∈ formedLinkConstraintSet ω Ω B V ∧
    ∀ (δ : ℝ) (c : ℝ → BondAtLevel L m K 0 → Matrices.ComplexMatrix2), 0 < δ →
      (∀ t ∈ Ioo (-δ) δ, c t ∈ formedLinkConstraintSet ω Ω B V) →
      (∀ b r s, DifferentiableOn ℝ (fun t => c t b r s) (Ioo (-δ) δ)) → c 0 = U →
      deriv (fun t => actionInside K (Ω 0) (c t)) 0 = 0
def formedRegularCriticalSet (ω ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {U | IsFormedConstrainedCritical ω Ω B V U ∧ IsRegularField ε K k Ω U}
def HasFormedMinimalOrbit (ω ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) : Prop :=
  ∃ U ∈ formedRegularCriticalSet ω ε K k Ω B V,
    formedRegularCriticalSet ω ε K k Ω B V = endpointFixingOrbit Ω B U
def imageChain (σ : FourTorus L m ≃ FourTorus L m) (Ω : ℕ → Set (FourTorus L m)) :
    ℕ → Set (FourTorus L m) :=
  fun q => σ '' Ω q
def bondSetImage (σ : FourTorus L m ≃ FourTorus L m) {K : ℕ}
    (B : Set (Σ j : ℕ, BondAtLevel L m K j)) : Set (Σ j : ℕ, BondAtLevel L m K j) :=
  (fun q => (⟨q.1, bondImage σ q.2⟩ : Σ j : ℕ, BondAtLevel L m K j)) '' B
def datumImage (σ : FourTorus L m ≃ FourTorus L m) {K : ℕ}
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2 :=
  fun q => transportGaugeField σ (V q)
def IsChainTriple (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (n : ℕ)
    (z : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ k ∧ n < j ∧ ∃ t ∈ annulusSites K k Ω j,
    (z : FourTorus L m) ∈ refinedBlock (j - n - 1) t ∧ x ∈ sitesInBlock (levelDepth K n) z
def memberFamilies {K : ℕ} (B : Set (Σ j : ℕ, BondAtLevel L m K j)) :
    Submodule ℂ (PositiveBondIn B → Matrices.ComplexMatrix2) :=
  Submodule.pi univ fun _ => Matrices.ComplexMatrix2.traceless
theorem mem_complexFamilyBall_iff {K : ℕ} {B : Set (Σ j : ℕ, BondAtLevel L m K j)} {ρ : ℝ}
    {A : PositiveBondIn B → Matrices.ComplexMatrix2} :
    A ∈ complexFamilyBall B ρ ↔
      A ∈ memberFamilies B ∧ Matrices.GroupLieProduct.supNorm A < ρ := by
  simp [complexFamilyBall, memberFamilies, Matrices.GroupLieProduct.supBall,
    Matrices.GroupLieProduct.tracelessPi, Matrices.ComplexMatrix2.complexifiedProduct,
    Matrices.ComplexMatrix2.FactorKind.complexified, Submodule.mem_pi]
def twistedFamily (σ : FourTorus L m ≃ FourTorus L m) {K : ℕ}
    {B : Set (Σ j : ℕ, BondAtLevel L m K j)}
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (A : PositiveBondIn B → Matrices.ComplexMatrix2) :
    PositiveBondIn (bondSetImage σ B) → Matrices.ComplexMatrix2 :=
  fun p => twistedFormValue σ (V₀ p.1.1) (familyAtLevel A p.1.1) p.1.2
end PeriodicLattice
end YangMills.Construction
