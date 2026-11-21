import YangMills.Construction.Lattice.PositionDependentCouplings
import YangMills.Construction.Lattice.WeightedWilsonActions
import YangMills.Construction.PolymerActivities.LocalisedActivitiesAndTheirNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K : ℕ}
def configurationPair (j : ℕ) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    FieldCurrentPair L m K :=
  (U, yangMillsCurrent (finestMeshInLevelUnits L j) U)
def restrictPairTo (X : Set (FourTorus L m)) (P : FieldCurrentPair L m K) :
    FieldCurrentPair L m K :=
  (extendByOne (bondsMeeting X) P.1, (bondsMeeting X : Set (BondAtLevel L m K 0)).indicator P.2)
namespace ScaleLabel
variable {n k j : ℕ} {c : ℕ → ℕ}
def restrictScale (S : ScaleLabel L m K n c k) (h : j ≤ k) : ScaleLabel L m K n c j where
  atScale i := S.atScale ⟨i, i.2.1, i.2.2.trans h⟩
  level_le := h.trans S.level_le
  domain_isUnion i := S.domain_isUnion ⟨i, i.2.1, i.2.2.trans h⟩
  smallFieldRegion_isUnion i := S.smallFieldRegion_isUnion ⟨i, i.2.1, i.2.2.trans h⟩
  smallFieldRegion_subset_domain i := S.smallFieldRegion_subset_domain ⟨i, i.2.1, i.2.2.trans h⟩
  succ_domain_subset i i' e :=
    S.succ_domain_subset ⟨i, i.2.1, i.2.2.trans h⟩ ⟨i', i'.2.1, i'.2.2.trans h⟩ e
  markedSet_subset i := S.markedSet_subset ⟨i, i.2.1, i.2.2.trans h⟩
  markedSet_empty_or_union i := S.markedSet_empty_or_union ⟨i, i.2.1, i.2.2.trans h⟩
def smallFieldSeq (S : ScaleLabel L m K n c k) (j : ℕ) : Set (FourTorus L m) :=
  open Classical in
  if h : j ∈ Set.Icc 1 k then (S.atScale ⟨j, h⟩).smallFieldRegion else univ
end ScaleLabel
namespace StoredBonds
variable {k j : ℕ}
def restrictLevel (𝔅 : StoredBonds L m K k) (h : j ≤ k) : StoredBonds L m K j where
  sets i := 𝔅.sets (Fin.castLE h i)
  positivelyOriented i := 𝔅.positivelyOriented (Fin.castLE h i)
def restrictLevelSystem (𝔅 : StoredBonds L m K k) (h : j ≤ k) (𝔣 : 𝔅.FieldSystem) :
    (𝔅.restrictLevel h).FieldSystem :=
  fun i b => 𝔣 (Fin.castLE h i) b
end StoredBonds
def regularPolymerDomains (K n j : ℕ) (Λ : Set (FourTorus L m)) : Set (Set (FourTorus L m)) :=
  {X | X ∈ connectedRegions L m (coarseCubeIndex K n j) ∧ X ⊆ Λ}
def remainderPolymerDomains (K n v j : ℕ) (Λ : Set (FourTorus L m)) :
    Set (Set (FourTorus L m)) :=
  {X | X ∈ connectedRegions L m (coarseCubeIndex K n j) ∧ X ⊆ smoothedRegionInterior K n v j Λ ∧
    IsScaledCubeUnion K j (n + v) X}
def regularActivitySum (K n v j : ℕ) (Λ : Set (FourTorus L m)) (E : RootedLocalActivities L m K j)
    (P : FieldCurrentPair L m K) : ℂ :=
  ∑ᶠ z ∈ (sitesIn (smoothedRegionInterior K n v j Λ) : Set (SiteAtLevel L m K j)),
    ∑ᶠ X ∈ {X ∈ regularPolymerDomains K n j Λ | (z : FourTorus L m) ∈ X}, E X z (restrictPairTo X P)
def remainderActivitySum (K n v j : ℕ) (Λ : Set (FourTorus L m)) (R : LocalActivities L m K)
    (P : FieldCurrentPair L m K) : ℂ :=
  ∑ᶠ X ∈ remainderPolymerDomains K n v j Λ, R X (restrictPairTo X P)
namespace AnalyticityConstants
variable (N : AnalyticityConstants) {c : ℕ → ℕ}
def boundaryActivitySum {j : ℕ} (S : ScaleLabel L m K N.cubeExp c j) (hj : 1 ≤ j)
    (𝔅 : StoredBonds L m K j) (B : BoundaryActivities 𝔅) (𝔣 : 𝔅.FieldSystem)
    (P : FieldCurrentPair L m K) : ℂ :=
  ∑ᶠ X ∈ N.boundaryRegions S hj,
    B X (N.markedSetsWithin S X) (𝔅.restrictNear X 𝔣) (restrictPairTo X P)
variable {k : ℕ}
structure EffectiveActionData (L m K : ℕ) {k : ℕ} (𝔅 : StoredBonds L m K k) where
  regularActs : (j : ℕ) → RootedLocalActivities L m K j
  remainderActs : ℕ → LocalActivities L m K
  boundaryActs : (j : ScaleIndex k) → BoundaryActivities (𝔅.restrictLevel j.2.2)
  vacuumEnergy : ℂ
variable (β : ℝ) (b : ℕ → ℝ) (v : ℕ → ℕ) (S : ScaleLabel L m K N.cubeExp c k)
  {𝔅 : StoredBonds L m K k} (D : EffectiveActionData L m K 𝔅)
def regularPart (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : ℂ :=
  ∑ j ∈ Finset.Icc 1 k,
    (regularActivitySum K N.cubeExp (v j) j (S.smallFieldSeq j) (D.regularActs j)
        (configurationPair j U) -
      regularActivitySum K N.cubeExp (v j) j (S.smallFieldSeq j) (D.regularActs j)
        (configurationPair j trivialGaugeField) -
      (b j : ℂ) * variableCouplingEnergy
        (smoothedRegionProfile K N.cubeExp (v j) j (S.smallFieldSeq j)) U)
def remainderPart (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : ℂ :=
  ∑ j ∈ Finset.Icc 1 k,
    (remainderActivitySum K N.cubeExp (v j) j (S.smallFieldSeq j) (D.remainderActs j)
        (configurationPair j U) -
      remainderActivitySum K N.cubeExp (v j) j (S.smallFieldSeq j) (D.remainderActs j)
        (configurationPair j trivialGaugeField))
def boundaryPart (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) (𝔣 : 𝔅.FieldSystem) : ℂ :=
  ∑ j : ScaleIndex k,
    N.boundaryActivitySum (S.restrictScale j.2.2) j.2.1 (𝔅.restrictLevel j.2.2) (D.boundaryActs j)
      (𝔅.restrictLevelSystem j.2.2 𝔣) (configurationPair j U)
def effectiveAction (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) (𝔣 : 𝔅.FieldSystem) : ℂ :=
  -variableCouplingEnergy
      (localInverseCoupling K N.cubeExp β b v S.smallFieldSeq k) U +
    N.regularPart b v S D U + N.remainderPart v S D U + N.boundaryPart S D U 𝔣 - D.vacuumEnergy
variable (C : Fin 2 → ℝ) (q : ℕ) (x : ℕ → ℝ)
structure ActionDataInClasses (s : ActivityDomainKind) (κ E₀ κ' κ₀ : ℝ)
    (Φ : (j : ScaleIndex k) → Set (𝔅.restrictLevel j.2.2).FieldSystem) : Prop where
  regular_mem : ∀ j : ScaleIndex k, D.regularActs j ∈ N.rootedBoundedClass C q x s K j κ E₀
    (regularPolymerDomains K N.cubeExp j (S.smallFieldSeq j))
  remainder_mem : ∀ j : ScaleIndex k, D.remainderActs j ∈ N.couplingClass C q x s K j κ' κ₀
    (remainderPolymerDomains K N.cubeExp (v j) j (S.smallFieldSeq j))
  boundary_isFamily : ∀ j : ScaleIndex k, N.IsBoundaryActivityFamily C q x (S.restrictScale j.2.2) j.2.1
    (𝔅.restrictLevel j.2.2) (Φ j) (D.boundaryActs j)
end AnalyticityConstants
end PeriodicLattice
end YangMills.Construction
