import YangMills.Construction.Lattice.AnalyticityDomains
import YangMills.Construction.Lattice.ScaleLabels
import YangMills.Construction.Lattice.StoredBondFieldSystems
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator Topology ENNReal
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K : ℕ}
def IsAnalyticOnPairSet (𝒰 : Set (FieldCurrentPair L m K)) (f : FieldCurrentPair L m K → ℂ) : Prop :=
  ∃ _ : Fintype (BondAtLevel L m K 0), ∀ P ∈ 𝒰, ∃ F : FieldCurrentPair L m K → ℂ,
    AnalyticAt ℂ F P ∧ ∀ᶠ Q in 𝓝[𝒰] P, f Q = F Q
def DependsOnlyOnRestrictionTo (X : Set (FourTorus L m)) (𝒰 : Set (FieldCurrentPair L m K))
    (f : FieldCurrentPair L m K → ℂ) : Prop :=
  ∀ P ∈ 𝒰, ∀ Q ∈ 𝒰,
    (∀ b ∈ (bondsMeeting X : Set (BondAtLevel L m K 0)), P.1 b = Q.1 b ∧ P.2 b = Q.2 b) →
    f P = f Q
def IsComplexGaugeInvariantAt (X : Set (FourTorus L m)) (𝒰 : Set (FieldCurrentPair L m K))
    (f : FieldCurrentPair L m K → ℂ) : Prop :=
  ∀ u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2, (∀ y, u y ∈ complexGaugeGroup) → ∀ P ∈ 𝒰,
    f (pairGaugeTransform X u P) = f P
def IsLocalActivityFunction (X : Set (FourTorus L m)) (𝒰 : Set (FieldCurrentPair L m K))
    (f : FieldCurrentPair L m K → ℂ) : Prop :=
  IsAnalyticOnPairSet 𝒰 f ∧ DependsOnlyOnRestrictionTo X 𝒰 f ∧ IsComplexGaugeInvariantAt X 𝒰 f
def pairSetSupremum (𝒰 : Set (FieldCurrentPair L m K)) (f : FieldCurrentPair L m K → ℂ) : ℝ≥0∞ :=
  ⨆ P ∈ 𝒰, ENNReal.ofReal ‖f P‖
abbrev LocalActivities (L m K : ℕ) : Type := Set (FourTorus L m) → FieldCurrentPair L m K → ℂ
abbrev RootedLocalActivities (L m K j : ℕ) : Type :=
  Set (FourTorus L m) → SiteAtLevel L m K j → FieldCurrentPair L m K → ℂ
inductive ActivityDomainKind : Type
  | singleScale
  | hereditary
namespace AnalyticityConstants
variable (N : AnalyticityConstants) (C : Fin 2 → ℝ) (q : ℕ) (x : ℕ → ℝ)
def activityDomain (s : ActivityDomainKind) (K j : ℕ) (X : Set (FourTorus L m)) :
    Set (FieldCurrentPair L m K) :=
  match s with
  | .singleScale =>
      N.singleScaleDomainEqualRadii K j X (Thresholds.couplingRadius C q x 0 j)
        (Thresholds.couplingRadius C q x 1 j)
  | .hereditary =>
      N.hereditaryDomain K j X (Thresholds.couplingRadius C q x 0 j)
        (Thresholds.couplingRadius C q x 1 j) (Thresholds.couplingRadius C q x 0 j)
def IsAdmissibleDomainSet (K j : ℕ) (𝒳 : Set (Set (FourTorus L m))) : Prop :=
  1 ≤ j ∧ j ≤ K ∧ 𝒳 ⊆ connectedRegions L m (coarseCubeIndex K N.cubeExp j)
def IsLocalActivityFamily (s : ActivityDomainKind) (K j : ℕ) (𝒳 : Set (Set (FourTorus L m)))
    (E : LocalActivities L m K) : Prop :=
  N.IsAdmissibleDomainSet K j 𝒳 ∧
    ∀ X ∈ 𝒳, IsLocalActivityFunction X (N.activityDomain C q x s K j X) (E X)
def IsRootedActivityFamily (s : ActivityDomainKind) (K j : ℕ) (𝒳 : Set (Set (FourTorus L m)))
    (E : RootedLocalActivities L m K j) : Prop :=
  N.IsAdmissibleDomainSet K j 𝒳 ∧
    ∀ X ∈ 𝒳, ∀ z ∈ (sitesIn X : Set (SiteAtLevel L m K j)),
      IsLocalActivityFunction X (N.activityDomain C q x s K j X) (E X z)
def decayNorm (s : ActivityDomainKind) (K j : ℕ) (κ : ℝ) (𝒳 : Set (Set (FourTorus L m)))
    (E : LocalActivities L m K) : ℝ≥0∞ :=
  ⨆ X ∈ 𝒳, ENNReal.ofReal (Real.exp (κ * linearExtent K N.cubeExp j X)) *
    pairSetSupremum (N.activityDomain C q x s K j X) (E X)
def rootedDecayNorm (s : ActivityDomainKind) (K j : ℕ) (κ : ℝ) (𝒳 : Set (Set (FourTorus L m)))
    (E : RootedLocalActivities L m K j) : ℝ≥0∞ :=
  ⨆ X ∈ 𝒳, ⨆ z ∈ (sitesIn X : Set (SiteAtLevel L m K j)),
    ENNReal.ofReal (Real.exp (κ * linearExtent K N.cubeExp j X)) *
      pairSetSupremum (N.activityDomain C q x s K j X) (E X z)
def rootedBoundedClass (s : ActivityDomainKind) (K j : ℕ) (κ E₀ : ℝ)
    (𝒳 : Set (Set (FourTorus L m))) : Set (RootedLocalActivities L m K j) :=
  {E | 0 < κ ∧ 0 ≤ E₀ ∧ N.IsRootedActivityFamily C q x s K j 𝒳 E ∧
    N.rootedDecayNorm C q x s K j κ 𝒳 E ≤ ENNReal.ofReal E₀}
def couplingClass (s : ActivityDomainKind) (K j : ℕ) (κ κ₀ : ℝ) (𝒳 : Set (Set (FourTorus L m))) :
    Set (LocalActivities L m K) :=
  {E | 0 < κ ∧ 0 < x j ∧ N.IsLocalActivityFamily C q x s K j 𝒳 E ∧
    N.decayNorm C q x s K j κ 𝒳 E ≤ ENNReal.ofReal (Thresholds.couplingAt x j ^ κ₀)}
variable {j : ℕ} {c : ℕ → ℕ}
def boundaryRegions (S : ScaleLabel L m K N.cubeExp c j) (hj : 1 ≤ j) : Set (Set (FourTorus L m)) :=
  {X | X ∈ connectedRegions L m (coarseCubeIndex K N.cubeExp j) ∧ (X ∩ S.domainSeq j).Nonempty ∧
    (X ∩ addCubeLayer (coarseCubeIndex K N.cubeExp j) (S.largeField ⟨j, hj, le_rfl⟩)).Nonempty}
def markedSetsWithin (S : ScaleLabel L m K N.cubeExp c j) (X : Set (FourTorus L m)) :
    ScaleIndex j → Set (FourTorus L m) :=
  fun i => (S.atScale i).markedSet ∩ X
abbrev BoundaryActivities (𝔅 : StoredBonds L m K j) : Type :=
  (X : Set (FourTorus L m)) → (ScaleIndex j → Set (FourTorus L m)) → 𝔅.FieldsNear X →
    FieldCurrentPair L m K → ℂ
variable (S : ScaleLabel L m K N.cubeExp c j) (hj : 1 ≤ j) (𝔅 : StoredBonds L m K j)
  (Φ : Set 𝔅.FieldSystem)
structure IsBoundaryActivityFamily (B : BoundaryActivities 𝔅) : Prop where
  stable : 𝔅.IsConjugationStable Φ
  analytic : ∀ X ∈ N.boundaryRegions S hj, ∀ φ ∈ 𝔅.restrictSetNear X Φ,
    IsAnalyticOnPairSet (N.layeredDomain C q x K j S.domainSeq X) (B X (N.markedSetsWithin S X) φ)
  local_ : ∀ X ∈ N.boundaryRegions S hj, ∀ φ ∈ 𝔅.restrictSetNear X Φ,
    DependsOnlyOnRestrictionTo X (N.layeredDomain C q x K j S.domainSeq X)
      (B X (N.markedSetsWithin S X) φ)
  invariant : ∀ X ∈ N.boundaryRegions S hj, ∀ φ ∈ 𝔅.restrictSetNear X Φ,
    ∀ u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2.specialUnitary,
    ∀ P ∈ N.layeredDomain C q x K j S.domainSeq X,
      B X (N.markedSetsWithin S X) (𝔅.conjugateNear X u φ)
          (pairGaugeTransform X (fun y => (u y : Matrices.ComplexMatrix2)) P) =
        B X (N.markedSetsWithin S X) φ P
end AnalyticityConstants
end PeriodicLattice
end YangMills.Construction
