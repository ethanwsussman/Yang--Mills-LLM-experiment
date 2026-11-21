import YangMills.Construction.Lattice.LiftingIsConsistentWithTheAveragesProof
import YangMills.Construction.Lattice.BondOrientationDichotomy
import YangMills.Construction.Lattice.BoundaryOfTheImageOfAPlaquette
import YangMills.Construction.Lattice.CovarianceOfComplexAveragingOfDeterminingSetsProof
import YangMills.Construction.Lattice.CovarianceOfGaugeFixingUnderIsometries
import YangMills.Construction.Lattice.CovarianceOfMinimalOrbitsUnderIsometriesProof
import YangMills.Construction.Lattice.IsometryCovarianceOfRegularSetsAndAxialRepresentatives
import YangMills.Construction.Lattice.MeanSchemeIsTheAveragingMapOnSmallConfigurationsProof
import YangMills.Construction.Towers.IsometryCovarianceOfTheCovariantAveragesOnTheWholeLatticeProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice.RegularSetsAxialGaugeCovariance
variable {L m K : ℕ} {j : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
section LinkImages
theorem bondPreimage_bondImage (hS : PreservesCells σ j) (b : Bond L m j) :
    bondPreimage σ (bondImage σ b) = b := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexDeterminingAveragingCovariance.bondPreimage_bondImage <;> assumption
theorem transport_bondImage (hS : PreservesCells σ j) (U : Bond L m j → ComplexMatrix2)
    (b : Bond L m j) : transportGaugeField σ U (bondImage σ b) = U b :=
  congrArg U (bondPreimage_bondImage hS b)
theorem transport_bondImage_opposite (hS : PreservesCells σ j) (U : Bond L m j → ComplexMatrix2)
    (b : Bond L m j) : transportGaugeField σ U (bondImage σ b).opposite = U b.opposite := by
  rw [← hS.2.2.2.2.1 b]
  exact transport_bondImage hS U b.opposite
theorem bondImage_symm_bondImage (hS : PreservesCells σ j) (b : Bond L m j) :
    bondImage σ.symm (bondImage σ b) = b :=
  bondPreimage_bondImage hS b
theorem transport_symm_transport (hS : PreservesCells σ j) (U : Bond L m j → ComplexMatrix2) :
    transportGaugeField σ.symm (transportGaugeField σ U) = U := by
  funext b
  exact transport_bondImage hS U b
theorem isGaugeField_image (hS : PreservesCells σ j)
    {E : Set (Bond L m j)} {W : Bond L m j → ComplexMatrix2} {𝒢 : Set ComplexMatrix2}
    (h : IsGaugeField 𝒢 E W) :
    IsGaugeField 𝒢 (bondImage σ '' E) (transportGaugeField σ W) := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    rw [transport_bondImage hS]
    exact h₁ b hb
  · rintro _ ⟨b, hb, rfl⟩
    rw [transport_bondImage_opposite hS, transport_bondImage hS]
    exact h₂ b hb
theorem bondImage_mem_bondsInside_iff (hS : PreservesCells σ j) (X : Set (FourTorus L m))
    (b : Bond L m j) :
    bondImage σ b ∈ (bondsInside (σ '' X) : Set (Bond L m j)) ↔
      b ∈ (bondsInside X : Set (Bond L m j)) := by
  rw [(hS.2.2.2.2.2.2 X).2.2]
  exact hS.2.2.1.1.mem_set_image
theorem extendByOne_transport (hS : PreservesCells σ j) (X : Set (FourTorus L m))
    (U : Bond L m j → ComplexMatrix2) :
    extendByOne (bondsInside (σ '' X)) (transportGaugeField σ U) =
      transportGaugeField σ (extendByOne (bondsInside X) U) := by
  classical
  funext b
  obtain ⟨c, rfl⟩ := hS.2.2.1.2 b
  rw [transport_bondImage hS]
  by_cases hc : c ∈ (bondsInside X : Set (Bond L m j))
  · simp [extendByOne, hc, bondImage_mem_bondsInside_iff hS X c, transport_bondImage hS]
  · simp [extendByOne, hc, bondImage_mem_bondsInside_iff hS X c]
end LinkImages
section FinestFields
variable {ω : ℝ} {i : ℤ}
theorem transport_mem_gaugeFieldsInside (hS : PreservesCells σ (levelDepth K 0))
    {X : Set (FourTorus L m)} {U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : U ∈ gaugeFieldsInside K X) :
    transportGaugeField σ U ∈ gaugeFieldsInside K (σ '' X) := by
  refine ⟨?_, fun b hb => ?_⟩
  · rw [(hS.2.2.2.2.2.2 X).2.2]
    exact isGaugeField_image hS hU.1
  · obtain ⟨c, rfl⟩ := hS.2.2.1.2 b
    rw [transport_bondImage hS]
    exact hU.2 c fun hc => hb ((bondImage_mem_bondsInside_iff hS X c).2 hc)
theorem blockField_transport (hS : PreservesCells σ (levelDepth K 0))
    (hF : BlockFieldEquivariant K i σ) {n : ℕ} (hn : n ≤ K) (hi : i ≤ levelDepth K n)
    {X : Set (FourTorus L m)} {U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup (bondsInside X) U) :
    blockFieldAtLevel (Averaging.smoothingRadius L) n
        (extendByOne (bondsInside (σ '' X)) (transportGaugeField σ U)) =
      transportGaugeField σ
        (blockFieldAtLevel (K := K) (Averaging.smoothingRadius L) n (extendByOne (bondsInside X) U)) := by
  rw [extendByOne_transport hS]
  exact hF n hn hi _ (extendByOne_mem_compactGaugeFields
    (fun _ h => ⟨h.2, h.1⟩) hU)
end FinestFields
section ConstrainedSets
structure IsometryActsUpTo (i : ℤ) (K k : ℕ) (σ : FourTorus L m ≃ FourTorus L m) : Prop where
  le_top : k ≤ K
  le_depth : ∀ q ≤ k, i ≤ levelDepth K q
  cells : ∀ j : ℤ, i ≤ j → PreservesCells σ j
  cells_symm : ∀ j : ℤ, i ≤ j → PreservesCells σ.symm j
  blockFields : BlockFieldEquivariant K i σ
  blockFields_symm : BlockFieldEquivariant K i σ.symm
theorem IsometryActsUpTo.symm {i : ℤ} {k : ℕ} (c : IsometryActsUpTo i K k σ) :
    IsometryActsUpTo i K k σ.symm :=
  ⟨c.le_top, c.le_depth, c.cells_symm, c.cells, c.blockFields_symm, c.blockFields⟩
theorem IsometryActsUpTo.atFinest {i : ℤ} {k : ℕ} (c : IsometryActsUpTo i K k σ) :
    PreservesCells σ (levelDepth K 0) :=
  c.cells _ (c.le_depth 0 (Nat.zero_le k))
structure ImageData (k : ℕ) (σ : FourTorus L m ≃ FourTorus L m) (Ω Ω' : ℕ → Set (FourTorus L m))
    (B B' : Set (Σ j : ℕ, BondAtLevel L m K j))
    (V V' : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) : Prop where
  region_zero : Ω' 0 = σ '' Ω 0
  bonds_eq : B' = bondSetImage σ B
  level_le : ∀ q ∈ B, q.1 ≤ k
  values_eq : ∀ q ∈ B, V' q.1 (bondImage σ q.2) = V q.1 q.2
variable {i : ℤ} {k : ℕ} {Ω Ω' : ℕ → Set (FourTorus L m)}
  {B B' : Set (Σ j : ℕ, BondAtLevel L m K j)} {V V' : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2}
theorem ImageData.symm (c : IsometryActsUpTo i K k σ) (r : ImageData k σ Ω Ω' B B' V V') :
    ImageData k σ.symm Ω' Ω B' B V' V := by
  have hback : ∀ q ∈ B, (⟨q.1, bondImage σ.symm (bondImage σ q.2)⟩ :
      Σ j : ℕ, BondAtLevel L m K j) = q := fun q hq => by
    rw [bondImage_symm_bondImage (c.cells _ (c.le_depth _ (r.level_le q hq)))]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [r.region_zero]
    exact (Equiv.symm_image_image σ _).symm
  · rw [r.bonds_eq, bondSetImage, bondSetImage, image_image]
    ext q
    constructor
    · intro hq
      exact ⟨q, hq, hback q hq⟩
    · rintro ⟨q', hq', rfl⟩
      show (⟨q'.1, bondImage σ.symm (bondImage σ q'.2)⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ B
      rw [hback q' hq']
      exact hq'
  · intro q hq
    rw [r.bonds_eq] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact r.level_le q' hq'
  · intro q hq
    rw [r.bonds_eq] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    show V q'.1 (bondImage σ.symm (bondImage σ q'.2)) = V' q'.1 (bondImage σ q'.2)
    rw [bondImage_symm_bondImage (c.cells _ (c.le_depth _ (r.level_le q' hq'))), r.values_eq q' hq']
theorem transport_mem_linkConstraintSet (c : IsometryActsUpTo i K k σ)
    (r : ImageData k σ Ω Ω' B B' V V')
    {U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : U ∈ linkConstraintSet (Averaging.smoothingRadius L) Ω B V) :
    transportGaugeField σ U ∈ linkConstraintSet (Averaging.smoothingRadius L) Ω' B' V' := by
  refine ⟨?_, ?_⟩
  · rw [r.region_zero]
    exact transport_mem_gaugeFieldsInside c.atFinest hU.1
  · intro q' hq'
    rw [r.bonds_eq] at hq'
    obtain ⟨q, hq, rfl⟩ := hq'
    have hk := r.level_le q hq
    have hS := c.cells _ (c.le_depth _ hk)
    show averagingOnDeterminingSet (Averaging.smoothingRadius L) K (Ω' 0) (transportGaugeField σ U) q.1
        (bondImage σ q.2) = V' q.1 (bondImage σ q.2)
    rw [r.values_eq q hq, r.region_zero, ← hU.2 q hq]
    unfold averagingOnDeterminingSet
    rw [blockField_transport c.atFinest c.blockFields (hk.trans c.le_top) (c.le_depth _ hk) hU.1.1]
    exact transport_bondImage hS _ _
theorem isConstrainedCritical_transport (c : IsometryActsUpTo i K k σ)
    (r : ImageData k σ Ω Ω' B B' V V')
    (hA : ∀ W : BondAtLevel L m K 0 → ComplexMatrix2,
      IsGaugeField compactGaugeGroup (bondsInside (Ω 0)) W →
      actionInside K (Ω' 0) (transportGaugeField σ W) = actionInside K (Ω 0) W)
    {U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : IsConstrainedCritical (Averaging.smoothingRadius L) Ω B V U) :
    IsConstrainedCritical (Averaging.smoothingRadius L) Ω' B' V' (transportGaugeField σ U) := by
  refine ⟨transport_mem_linkConstraintSet c r hU.1, fun δ f hδ hf hd h0 => ?_⟩
  have hS₀ := c.atFinest
  have hS₀' := c.symm.atFinest
  let g : ℝ → BondAtLevel L m K 0 → ComplexMatrix2 := fun t => transportGaugeField σ.symm (f t)
  have hg : ∀ t ∈ Ioo (-δ) δ, g t ∈ linkConstraintSet (Averaging.smoothingRadius L) Ω B V :=
    fun t ht => transport_mem_linkConstraintSet c.symm (r.symm c) (hf t ht)
  have hg0 : g 0 = U := by
    show transportGaugeField σ.symm (f 0) = U
    rw [h0]
    exact transport_symm_transport hS₀ U
  have hder := hU.2 δ g hδ hg (fun b r s => hd _ r s) hg0
  have heq : (fun t => actionInside K (Ω' 0) (f t)) =ᶠ[nhds 0]
      fun t => actionInside K (Ω 0) (g t) := by
    filter_upwards [Ioo_mem_nhds (by linarith : -δ < 0) hδ] with t ht
    have hfg : f t = transportGaugeField σ (g t) := (transport_symm_transport hS₀' (f t)).symm
    rw [hfg]
    exact hA _ (hg t ht).1.1
  rw [heq.deriv_eq]
  exact hder
theorem actionInside_symm_transport (c : IsometryActsUpTo i K k σ)
    (r : ImageData k σ Ω Ω' B B' V V')
    (hA : ∀ W : BondAtLevel L m K 0 → ComplexMatrix2,
      IsGaugeField compactGaugeGroup (bondsInside (Ω 0)) W →
      actionInside K (Ω' 0) (transportGaugeField σ W) = actionInside K (Ω 0) W)
    (W : BondAtLevel L m K 0 → ComplexMatrix2)
    (hW : IsGaugeField compactGaugeGroup (bondsInside (Ω' 0)) W) :
    actionInside K (Ω 0) (transportGaugeField σ.symm W) = actionInside K (Ω' 0) W := by
  have hS₀' := c.symm.atFinest
  have hcfg : IsGaugeField compactGaugeGroup (bondsInside (Ω 0)) (transportGaugeField σ.symm W) := by
    have h := isGaugeField_image hS₀' hW
    rw [← (hS₀'.2.2.2.2.2.2 _).2.2, (r.symm c).region_zero.symm] at h
    exact h
  have h := hA _ hcfg
  rw [show transportGaugeField σ (transportGaugeField σ.symm W) = W from
    transport_symm_transport hS₀' W] at h
  exact h.symm
theorem regularConstrainedCriticalSet_image {ε : ℝ} (c : IsometryActsUpTo i K k σ)
    (r : ImageData k σ Ω Ω' B B' V V')
    (hA : ∀ W : BondAtLevel L m K 0 → ComplexMatrix2,
      IsGaugeField compactGaugeGroup (bondsInside (Ω 0)) W →
      actionInside K (Ω' 0) (transportGaugeField σ W) = actionInside K (Ω 0) W)
    (hreg : ∀ U ∈ gaugeFieldsInside K (Ω 0),
      (IsRegularField ε K k Ω' (transportGaugeField σ U) ↔ IsRegularField ε K k Ω U)) :
    regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω' B' V' =
      transportGaugeField σ ''
        regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω B V := by
  have hS₀' := c.symm.atFinest
  ext W
  constructor
  · rintro ⟨hc, hW⟩
    have hU := isConstrainedCritical_transport c.symm (r.symm c)
      (actionInside_symm_transport c r hA) hc
    have hWU : transportGaugeField σ (transportGaugeField σ.symm W) = W :=
      transport_symm_transport hS₀' W
    refine ⟨_, ⟨hU, (hreg _ hU.1.1).1 ?_⟩, hWU⟩
    rw [hWU]
    exact hW
  · rintro ⟨U, ⟨hc, hU⟩, rfl⟩
    exact ⟨isConstrainedCritical_transport c r hA hc, (hreg U hc.1.1).2 hU⟩
theorem extendByOne_gaugeTransform_transport (hS : PreservesCells σ (levelDepth K 0))
    (hGa : ∀ (ℬ : Set (BondAtLevel L m K 0)) (U : BondAtLevel L m K 0 → ComplexMatrix2)
      (u : SiteAtLevel L m K 0 → ComplexMatrix2), IsReversalClosed ℬ →
      IsGaugeField compactGaugeGroup ℬ U →
      IsGaugeMap compactGaugeGroup u → ∀ b ∈ bondImage σ '' ℬ,
        transportGaugeField σ (gaugeTransform u U) b =
          gaugeTransform (transportSiteFunction σ u) (transportGaugeField σ U) b)
    {X : Set (FourTorus L m)} {U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : U ∈ gaugeFieldsInside K X)
    {u : SiteAtLevel L m K 0 → ComplexMatrix2} (hu : IsGaugeMap compactGaugeGroup u) :
    extendByOne (bondsInside (σ '' X))
        (gaugeTransform (transportSiteFunction σ u) (transportGaugeField σ U)) =
      transportGaugeField σ (extendByOne (bondsInside X) (gaugeTransform u U)) := by
  classical
  rw [← extendByOne_transport hS]
  funext b
  by_cases hb : b ∈ (bondsInside (σ '' X) : Set (BondAtLevel L m K 0))
  · simp only [extendByOne, hb, if_true]
    refine (hGa (bondsInside X) U u (fun _ h => ⟨h.2, h.1⟩) hU.1 hu b ?_).symm
    rw [← (hS.2.2.2.2.2.2 X).2.2]
    exact hb
  · simp only [extendByOne, hb, if_false]
theorem isGaugeMap_of_mem {u : SiteAtLevel L m K 0 → ComplexMatrix2}
    (hu : u ∈ endpointFixingGaugeGroup Ω B) :
    IsGaugeMap compactGaugeGroup u := by
  intro x
  by_cases hx : x ∈ (sitesIn (Ω 0) : Set (SiteAtLevel L m K 0))
  · exact hu.1 x hx
  · rw [hu.2.1 x hx]
    exact ComplexMatrix2.specialUnitary.one_mem
theorem endpointFixingOrbit_transport (hS : PreservesCells σ (levelDepth K 0))
    (hGa : ∀ (ℬ : Set (BondAtLevel L m K 0)) (U : BondAtLevel L m K 0 → ComplexMatrix2)
      (u : SiteAtLevel L m K 0 → ComplexMatrix2), IsReversalClosed ℬ →
      IsGaugeField compactGaugeGroup ℬ U →
      IsGaugeMap compactGaugeGroup u → ∀ b ∈ bondImage σ '' ℬ,
        transportGaugeField σ (gaugeTransform u U) b =
          gaugeTransform (transportSiteFunction σ u) (transportGaugeField σ U) b)
    (hres : endpointFixingGaugeGroup Ω' B' =
      transportSiteFunction σ '' endpointFixingGaugeGroup Ω B) (h0 : Ω' 0 = σ '' Ω 0)
    {U : BondAtLevel L m K 0 → ComplexMatrix2} (hU : U ∈ gaugeFieldsInside K (Ω 0)) :
    endpointFixingOrbit Ω' B' (transportGaugeField σ U) =
      transportGaugeField σ '' endpointFixingOrbit Ω B U := by
  ext W
  constructor
  · rintro ⟨u', hu', rfl⟩
    rw [hres] at hu'
    obtain ⟨u, hu, rfl⟩ := hu'
    refine ⟨_, ⟨u, hu, rfl⟩, ?_⟩
    rw [h0]
    exact (_root_.YangMills.Construction.PeriodicLattice.RegularSetsAxialGaugeCovariance.extendByOne_gaugeTransform_transport hS hGa hU (isGaugeMap_of_mem hu)).symm
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨transportSiteFunction σ u, ?_, ?_⟩
    · rw [hres]
      exact mem_image_of_mem _ hu
    · rw [h0]
      exact (_root_.YangMills.Construction.PeriodicLattice.RegularSetsAxialGaugeCovariance.extendByOne_gaugeTransform_transport hS hGa hU (isGaugeMap_of_mem hu)).symm
theorem hasUniqueCriticalOrbit_transport_iff {ε : ℝ} (hS : PreservesCells σ (levelDepth K 0))
    (hcrit : regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω' B' V' =
      transportGaugeField σ ''
        regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω B V)
    (horb : ∀ U ∈ gaugeFieldsInside K (Ω 0),
      endpointFixingOrbit Ω' B' (transportGaugeField σ U) =
        transportGaugeField σ '' endpointFixingOrbit Ω B U) :
    HasUniqueCriticalOrbit (Averaging.smoothingRadius L) ε K k Ω' B' V' ↔
      HasUniqueCriticalOrbit (Averaging.smoothingRadius L) ε K k Ω B V := by
  have hinj : Function.Injective (transportGaugeField σ :
      (BondAtLevel L m K 0 → ComplexMatrix2) → BondAtLevel L m K 0 → ComplexMatrix2) :=
    Function.LeftInverse.injective (g := transportGaugeField σ.symm) (transport_symm_transport hS)
  constructor
  · rintro ⟨U', hU', hE⟩
    rw [hcrit] at hU'
    obtain ⟨U, hU, rfl⟩ := hU'
    refine ⟨U, hU, ?_⟩
    rw [hcrit, horb U hU.1.1.1] at hE
    exact image_injective.2 hinj hE
  · rintro ⟨U, hU, hE⟩
    refine ⟨transportGaugeField σ U, ?_, ?_⟩
    · rw [hcrit]
      exact mem_image_of_mem _ hU
    · rw [hcrit, horb U hU.1.1.1, hE]
end ConstrainedSets
section Facts
structure IsometryFacts (i : ℤ) (K : ℕ) (σ : FourTorus L m ≃ FourTorus L m) : Prop where
  cells : ∀ j : ℤ, i ≤ j → PreservesCells σ j
  cells_symm : ∀ j : ℤ, i ≤ j → PreservesCells σ.symm j
  blockFields : BlockFieldEquivariant K i σ
  blockFields_symm : BlockFieldEquivariant K i σ.symm
  regionBlockFields : RegionBlockFieldEquivariant K i σ
  actionInside : ∀ (i' : ℤ) (Ω₀ : Set (FourTorus L m)) (U : BondAtLevel L m K 0 → ComplexMatrix2),
    i ≤ levelDepth K 0 → i ≤ i' → IsPartitionRegion i' Ω₀ →
      IsGaugeField compactGaugeGroup (bondsInside Ω₀) U →
      actionInside K (σ '' Ω₀) (transportGaugeField σ U) = actionInside K Ω₀ U
  gaugeTransform : i ≤ levelDepth K 0 → ∀ (ℬ : Set (BondAtLevel L m K 0))
    (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (u : SiteAtLevel L m K 0 → ComplexMatrix2), IsReversalClosed ℬ →
    IsGaugeField compactGaugeGroup ℬ U →
    IsGaugeMap compactGaugeGroup u → ∀ b ∈ bondImage σ '' ℬ,
      transportGaugeField σ (gaugeTransform u U) b =
        gaugeTransform (transportSiteFunction σ u) (transportGaugeField σ U) b
  constraintSets : ∀ ε : ℝ, 0 < ε → ∀ (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2),
    IsDeterminingChainFrom K k i Ω → IsActiveLinkDatum K k Ω V →
      ConstraintSetsTransport σ ε K k Ω V ∧
      ∀ U ∈ gaugeFieldsInside K (Ω 0), FieldTransports σ ε K k Ω V U
  chainObjects : PreservesChainObjects i σ
  determiningSets : PreservesDeterminingSets i σ
  blocks : ∀ j : ℤ, i ≤ j → IsometryInvariance.MapsBlocks σ j
  axialGauge : ∀ k : ℕ, k < K → i ≤ levelDepth K (k + 1) →
    ∀ (P'' : Set (SiteAtLevel L m K (k + 1))) (W : BondAtLevel L m K k → ComplexMatrix2),
      IsBlockAxialGauge K k (sitePointImage σ P'') (transportGaugeField σ W) ↔
        IsBlockAxialGauge K k P'' W
  orientation : ∀ j : ℤ, -(m : ℤ) < j → ∀ b : Bond L m j,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  m_pos : 0 < m
  plaquetteNorm : ∀ j : ℤ, i ≤ j → ∀ (ℬ : Set (Bond L m j)) (U : Bond L m j → ComplexMatrix2),
    IsReversalClosed ℬ → IsGaugeField compactGaugeGroup ℬ U → ∀ p : Plaquette L m j,
      (∀ b ∈ p.boundaryBonds, b ∈ ℬ) →
      ComplexMatrix2.operatorNorm (plaquetteHolonomy (transportGaugeField σ.symm U)
        (plaquetteImage σ.symm p) - 1) = ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1)
  plaquetteBoundary : ∀ j : ℤ, i ≤ j → ∀ p : Plaquette L m j,
    (∀ b ∈ (plaquetteImage σ.symm p).boundaryBonds, ∃ c ∈ p.boundaryBonds,
      b = bondImage σ.symm c ∨ b = (bondImage σ.symm c).opposite) ∧
    ∀ c ∈ p.boundaryBonds, ∃ b ∈ (plaquetteImage σ.symm p).boundaryBonds,
      b = bondImage σ.symm c ∨ b = (bondImage σ.symm c).opposite
  averageStep : BlockAverageStepEquivariant K i σ
  bondObjects : ∀ k : ℕ, k < K → i ≤ levelDepth K (k + 1) →
    IsometryInvariance.MapsBondObjects σ K k
  doubleBlockLocal : ∀ k : ℕ, k < K → ∀ (c : BondAtLevel L m K (k + 1))
    (U U' : BondAtLevel L m K k → ComplexMatrix2),
    (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), U b = U' b) →
      blockAverage (Averaging.smoothingRadius L) U c = blockAverage (Averaging.smoothingRadius L) U' c
  averageStep_mapsTo : ∀ k : ℕ, k < K → MapsTo (blockAverageStep (L := L) (m := m) (K := K)
    (Averaging.smoothingRadius L) k) (gaugeFieldsAtLevel L m K k) (gaugeFieldsAtLevel L m K (k + 1))
variable {i : ℤ} {k : ℕ} {Ω : ℕ → Set (FourTorus L m)}
theorem IsometryFacts.actsUpTo (t : IsometryFacts i K σ) (h : IsDeterminingChainFrom K k i Ω) :
    IsometryActsUpTo i K k σ :=
  ⟨h.1, fun q hq => by
    obtain ⟨a, ha, ha', -⟩ := h.2.2 q hq
    exact ha.trans ha', t.cells, t.cells_symm, t.blockFields, t.blockFields_symm⟩
theorem isLinkDatum_one (B : Set (Σ j : ℕ, BondAtLevel L m K j)) :
    IsLinkDatum B (fun _ _ => (1 : ComplexMatrix2)) :=
  fun _ _ => ⟨ComplexMatrix2.specialUnitary.one_mem, fun _ => by simp⟩
theorem isRegularField_transport_iff (t : IsometryFacts i K σ) (h : IsDeterminingChainFrom K k i Ω)
    {ε : ℝ} (hε : 0 < ε) {U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : U ∈ gaugeFieldsInside K (Ω 0)) :
    IsRegularField ε K k (imageChain σ Ω) (transportGaugeField σ U) ↔ IsRegularField ε K k Ω U :=
  ((t.constraintSets ε hε k Ω _ h (isLinkDatum_one _)).2 U hU).1
theorem activeBondSet_imageChain (t : IsometryFacts i K σ) (h : IsDeterminingChainFrom K k i Ω) :
    activeBondSet K k (imageChain σ Ω) = bondSetImage σ (activeBondSet K k Ω) :=
  (t.chainObjects K k Ω (imageChain σ Ω) (t.actsUpTo h).le_depth
    fun _ _ => rfl).2.2.2.2.2.2.2.1
theorem imageData_activeBondSet (t : IsometryFacts i K σ) (h : IsDeterminingChainFrom K k i Ω)
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) :
    ImageData k σ Ω (imageChain σ Ω) (activeBondSet K k Ω) (activeBondSet K k (imageChain σ Ω)) V
      (datumImage σ V) :=
  ⟨rfl, activeBondSet_imageChain t h, fun _ hq => hq.1.1, fun q hq =>
    transport_bondImage ((t.actsUpTo h).cells _ ((t.actsUpTo h).le_depth _ hq.1.1)) (V q.1) q.2⟩
theorem activeBondSet_transport (t : IsometryFacts i K σ) (h : IsDeterminingChainFrom K k i Ω)
    {ε : ℝ} (hε : 0 < ε) {V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2}
    (hV : IsLinkDatum (activeBondSet K k Ω) V) :
    regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k (imageChain σ Ω)
        (activeBondSet K k (imageChain σ Ω)) (datumImage σ V) =
      transportGaugeField σ ''
        regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω (activeBondSet K k Ω) V ∧
    (HasUniqueCriticalOrbit (Averaging.smoothingRadius L) ε K k (imageChain σ Ω)
        (activeBondSet K k (imageChain σ Ω)) (datumImage σ V) ↔
      HasUniqueCriticalOrbit (Averaging.smoothingRadius L) ε K k Ω (activeBondSet K k Ω) V) := by
  have c := t.actsUpTo h
  obtain ⟨a, ha, ha', hreg⟩ := h.2.2 0 (Nat.zero_le k)
  have hd₀ := c.le_depth 0 (Nat.zero_le k)
  have hcrit := regularConstrainedCriticalSet_image (ε := ε) c (imageData_activeBondSet t h V)
    (fun W hW => t.actionInside a (Ω 0) W hd₀ ha hreg hW)
    (fun U hU => isRegularField_transport_iff t h hε hU)
  have hres := ((t.constraintSets ε hε k Ω V h hV).1).2.2.1
  exact ⟨hcrit, hasUniqueCriticalOrbit_transport_iff c.atFinest hcrit
    fun U hU => endpointFixingOrbit_transport c.atFinest (t.gaugeTransform hd₀) hres rfl hU⟩
end Facts
section OrbitsAndFields
variable {i : ℤ}
theorem preservesOrbitFunctions (t : IsometryFacts i K σ) : PreservesOrbitFunctions K i σ := by
  intro ε k Ω V hε hdet hV
  obtain ⟨hcrit, hiff⟩ := activeBondSet_transport t hdet hε hV
  refine ⟨hiff.symm, fun hM E Φ hΦ U' hU' U hU => ?_⟩
  obtain ⟨U₀, hU₀, hE⟩ := hiff.2 hM
  have key : ∀ W ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k
      (imageChain σ Ω) (activeBondSet K k (imageChain σ Ω)) (datumImage σ V), Φ W = Φ U₀ := by
    intro W hW
    rw [hE] at hW
    exact hΦ U₀ hU₀ W hW
  have h₁ : transportGaugeField σ U ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L)
      ε K k (imageChain σ Ω) (activeBondSet K k (imageChain σ Ω)) (datumImage σ V) := by
    rw [hcrit]
    exact mem_image_of_mem _ hU
  rw [key _ hU', key _ h₁]
theorem preservesRegularFields (t : IsometryFacts i K σ) : PreservesRegularFields K i σ := by
  intro α₀ e r k Ω hα hdet _
  have c := t.actsUpTo hdet
  have hS₀' := c.symm.atFinest
  ext W
  constructor
  · rintro ⟨hin, hr⟩
    have hWU : transportGaugeField σ (transportGaugeField σ.symm W) = W :=
      transport_symm_transport hS₀' W
    have hin' : transportGaugeField σ.symm W ∈ gaugeFieldsInside K (Ω 0) := by
      have h := transport_mem_gaugeFieldsInside hS₀' hin
      rwa [show σ.symm '' imageChain σ Ω 0 = Ω 0 from Equiv.symm_image_image σ _] at h
    refine ⟨_, ⟨hin', (isRegularField_transport_iff t hdet hα hin').1 ?_⟩, hWU⟩
    rw [hWU]
    exact hr
  · rintro ⟨U, ⟨hin, hr⟩, rfl⟩
    exact ⟨transport_mem_gaugeFieldsInside c.atFinest hin,
      (isRegularField_transport_iff t hdet hα hin).2 hr⟩
theorem isLinkDatum_datumImage {k : ℕ} {Ω : ℕ → Set (FourTorus L m)} (t : IsometryFacts i K σ)
    (h : IsDeterminingChainFrom K k i Ω) {V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2}
    (hV : IsLinkDatum (activeBondSet K k Ω) V) :
    IsLinkDatum (activeBondSet K k (imageChain σ Ω)) (datumImage σ V) := by
  have c := t.actsUpTo h
  rw [activeBondSet_imageChain t h]
  rintro _ ⟨q, hq, rfl⟩
  have hS := c.cells _ (c.le_depth _ hq.1.1)
  have hv : datumImage σ V q.1 (bondImage σ q.2) = V q.1 q.2 := transport_bondImage hS (V q.1) q.2
  have hr : datumImage σ V q.1 (bondImage σ q.2).opposite = V q.1 q.2.opposite :=
    transport_bondImage_opposite hS (V q.1) q.2
  refine ⟨?_, fun hq' => ?_⟩
  · show datumImage σ V q.1 (bondImage σ q.2) ∈ compactGaugeGroup
    rw [hv]
    exact (hV q hq).1
  · show datumImage σ V q.1 (bondImage σ q.2).opposite =
      (datumImage σ V q.1 (bondImage σ q.2))⁻¹
    rw [hv, hr]
    refine (hV q hq).2 ?_
    obtain ⟨q', hq'', he⟩ := hq'
    have hS' := c.cells _ (c.le_depth _ hq''.1.1)
    obtain ⟨n, b⟩ := q'
    obtain ⟨n', b'⟩ := q
    simp only [Sigma.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    have he' := eq_of_heq he
    rw [← hS.2.2.2.2.1 b'] at he'
    have : b = b'.opposite := hS.2.2.1.1 he'
    subst this
    exact hq''
theorem preservesAxialGaugeRepresentatives (t : IsometryFacts i K σ) :
    PreservesAxialGaugeRepresentatives K i σ := by
  intro ε k Ω V Y hε hF hset
  have hdet : IsDeterminingChainFrom K (k + 1) i Ω :=
    ⟨hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2⟩
  have c := t.actsUpTo hdet
  have hk₁ := c.le_depth (k + 1) le_rfl
  have hk₀ := c.le_depth k (Nat.le_succ k)
  have hkK : k < K := hset.succ_le
  obtain ⟨hcrit, hiff⟩ := activeBondSet_transport t hdet hε hset.linkDatum
  have hSk := t.cells _ hk₀
  have hS₁ := t.cells _ hk₁
  have hObj := t.chainObjects K (k + 1) Ω (imageChain σ Ω) c.le_depth fun _ _ => rfl
  have hnode : ∀ x, IsEndpointOf (activeBondSet K (k + 1) (imageChain σ Ω)) (σ x) ↔
      IsEndpointOf (activeBondSet K (k + 1) Ω) x := hObj.2.2.2.2.2.2.2.2.2.1
  have hblk := t.blocks _ hk₁ 1
  have hbimg : ∀ x, σ x ∈ refinedBlockUnion 1 (siteSetImage σ Y) ↔ x ∈ refinedBlockUnion 1 Y := by
    intro x
    simp only [refinedBlockUnion, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨y', ⟨y, hy, hyy⟩, hx⟩
      have e : y' = sitePreimage σ.symm y := Subtype.ext (hyy.trans (hS₁.1 y).symm)
      subst e
      rw [← hblk y] at hx
      obtain ⟨x₀, hx₀, he⟩ := hx
      obtain rfl := σ.injective he
      exact ⟨y, hy, hx₀⟩
    · rintro ⟨y, hy, hx⟩
      refine ⟨siteImage σ y, ⟨y, hy, hS₁.1 y⟩, ?_⟩
      show σ x ∈ refinedBlock 1 (sitePreimage σ.symm y)
      rw [← hblk y]
      exact mem_image_of_mem σ hx
  have hAvg : ∀ U ∈ gaugeFieldsInside K (Ω 0),
      regionBlockField k (imageChain σ Ω 0) (transportGaugeField σ U) =
        transportGaugeField σ (regionBlockField k (Ω 0) U) := fun U hU =>
    blockField_transport c.atFinest t.blockFields hkK.le hk₀ hU.1
  have hax : ∀ W : BondAtLevel L m K k → ComplexMatrix2,
      IsBlockAxialGauge K k (siteSetImage σ Y) (transportGaugeField σ W) ↔
        IsBlockAxialGauge K k Y W := fun W => t.axialGauge k hkK hk₁ Y W
  have helem : transportGaugeField σ '' axialGaugeRepresentatives ε K k Ω V Y =
      axialGaugeRepresentatives ε K k (imageChain σ Ω) (datumImage σ V)
        (siteSetImage σ Y) := by
    ext W
    constructor
    · rintro ⟨U, ⟨hU, hg⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · show transportGaugeField σ U ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L)
          ε K (k + 1) (imageChain σ Ω) (activeBondSet K (k + 1) (imageChain σ Ω))
          (datumImage σ V)
        rw [hcrit]
        exact mem_image_of_mem _ hU
      · rw [hAvg U hU.1.1.1]
        exact (hax _).2 hg
    · rintro ⟨hW, hg⟩
      have hW' : W ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K (k + 1)
          (imageChain σ Ω) (activeBondSet K (k + 1) (imageChain σ Ω))
          (datumImage σ V) := hW
      rw [hcrit] at hW'
      obtain ⟨U, hU, rfl⟩ := hW'
      rw [hAvg U hU.1.1.1] at hg
      exact ⟨U, ⟨hU, (hax _).1 hg⟩, rfl⟩
  refine ⟨⟨hset.succ_le, (t.determiningSets K (k + 1) Ω hdet).1.2.1,
    isLinkDatum_datumImage t hdet hset.linkDatum, hiff.2 hset.uniqueOrbit, ?_, ?_⟩, helem, ?_⟩
  · rintro y' ⟨y, hy, hyy⟩
    rw [show imageChain σ Ω (k + 1) = σ '' Ω (k + 1) from rfl, (hS₁.2.2.2.2.2.2 _).1]
    refine ⟨y, hset.subset_sites hy, Subtype.ext ?_⟩
    rw [hS₁.1 y, hyy]
  · intro x hx hne
    obtain ⟨x₀, rfl⟩ := σ.surjective x
    rw [hnode]
    refine hset.no_endpoints x₀ ((hbimg x₀).1 hx) fun y hy e => ?_
    exact hne (siteImage σ y) ⟨y, hy, hS₁.1 y⟩ (by rw [hS₁.1 y, e])
  · intro hnodes W hW U' hU' c' hc' hform
    rw [← helem] at hU'
    obtain ⟨U, hU, rfl⟩ := hU'
    obtain ⟨b, rfl⟩ := hSk.2.2.1.2 c'
    have hin := hU.1.1.1.1
    obtain ⟨a, ha, ha', hreg⟩ := hdet.2.2 0 (Nat.zero_le _)
    have hform' : IsAverageFormedOnRegion (Ω 0) b :=
      ((t.regionBlockFields k hkK.le hk₀ a ha ha' (Ω 0) hreg U hin.1 b).1).1 hform
    have hsite : ∀ x : SiteAtLevel L m K k,
        siteImage σ x ∈ blockAndEndpointSites (activeBondSet K (k + 1) (imageChain σ Ω))
          (siteSetImage σ Y) →
        x ∈ blockAndEndpointSites (activeBondSet K (k + 1) Ω) Y := by
      rintro x (h | h)
      · left
        have h' : ((siteImage σ x : SiteAtLevel L m K k) : FourTorus L m) ∈
            refinedBlockUnion 1 (siteSetImage σ Y) := h
        rw [hSk.1 x] at h'
        exact (hbimg _).1 h'
      · right
        have h' : IsEndpointOf (activeBondSet K (k + 1) (imageChain σ Ω))
            ((siteImage σ x : SiteAtLevel L m K k) : FourTorus L m) := h
        rw [hSk.1 x] at h'
        exact (hnode _).1 h'
    have hb : b ∈ blockAndEndpointBonds (activeBondSet K (k + 1) Ω) Y := by
      refine ⟨hsite _ ?_, hsite _ ?_⟩
      · rw [← (hSk.2.2.2.1 b).1]
        exact hc'.1
      · rw [← (hSk.2.2.2.1 b).2]
        exact hc'.2
    rw [hAvg U hin, transport_bondImage hSk, transport_bondImage hSk]
    exact hW U hU b hb hform'
end OrbitsAndFields
section FamilyBall
theorem bond_opposite_opposite {b : Bond L m j} : b.opposite.opposite = b := Bond.ext rfl rfl
theorem isUnit_det_of_mem {X : ComplexMatrix2} (h : X ∈ compactGaugeGroup) : IsUnit X.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem inv_mem_unitaryGroup_of_mem {X : ComplexMatrix2} (h : X ∈ compactGaugeGroup) :
    X⁻¹ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by apply _root_.YangMills.Construction.PeriodicLattice.MinimalOrbitsUnderIsometries.inv_mem_unitaryGroup <;> assumption
theorem conj_mem_traceless {g X : ComplexMatrix2} (hg : IsUnit g.det)
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy g X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.FullSpace.IsometryEquivariance.conjugateBy_mem_traceless_of_isUnit <;> assumption
def positiveOrientation (b : Bond L m j) : Bond L m j :=
  open Classical in if b.IsPositivelyOriented then b else b.opposite
theorem positiveOrientation_of_pos {b : Bond L m j} (h : b.IsPositivelyOriented) :
    positiveOrientation b = b := if_pos h
theorem positiveOrientation_of_not {b : Bond L m j} (h : ¬b.IsPositivelyOriented) :
    positiveOrientation b = b.opposite := if_neg h
theorem positiveOrientation_isPositive {b : Bond L m j}
    (hX : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    (positiveOrientation b).IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.LiftAveragesProof.positivelyOriented_isPositivelyOriented <;> assumption
theorem not_isPositive_opposite {b : Bond L m j}
    (hX : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by
  rcases hX with ⟨-, h₂⟩ | ⟨-, h₂⟩
  · exact h₂
  · exact absurd h h₂
theorem positiveOrientation_bondImage_preimage (hS : PreservesCells σ j)
    (hS' : PreservesCells σ.symm j)
    (hX : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {b' : Bond L m j} (hb' : b'.IsPositivelyOriented) :
    positiveOrientation (bondImage σ (positiveOrientation (bondPreimage σ b'))) = b' := by
  have hb : bondImage σ (bondPreimage σ b') = b' := bondPreimage_bondImage hS' b'
  by_cases h : (bondPreimage σ b').IsPositivelyOriented
  · rw [positiveOrientation_of_pos h, hb, positiveOrientation_of_pos hb']
  · rw [positiveOrientation_of_not h, hS.2.2.2.2.1, hb,
      positiveOrientation_of_not (not_isPositive_opposite (hX b') hb'), bond_opposite_opposite]
def LevelIsCarried (σ : FourTorus L m ≃ FourTorus L m) (K n : ℕ) : Prop :=
  PreservesCells σ (levelDepth K n) ∧
    PreservesCells σ.symm (levelDepth K n) ∧
    ∀ b : BondAtLevel L m K n, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
theorem complexFamilyBall_bondSetImage (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    {S : Set (Σ n : ℕ, BondAtLevel L m K n)} {ρ : ℝ}
    {V₀ : ∀ n : ℕ, BondAtLevel L m K n → ComplexMatrix2}
    (hrev : ∀ q ∈ S, (⟨q.1, q.2.opposite⟩ : Σ n : ℕ, BondAtLevel L m K n) ∈ S)
    (hlev : ∀ q ∈ S, LevelIsCarried σ K q.1) (hV : ∀ q ∈ S, V₀ q.1 q.2 ∈ compactGaugeGroup) :
    complexFamilyBall (bondSetImage σ S) ρ =
      twistedFamily (B := S) σ V₀ '' complexFamilyBall S ρ := by
  classical
  have hpull : ∀ q' ∈ bondSetImage σ S,
      (⟨q'.1, bondPreimage σ q'.2⟩ : Σ n : ℕ, BondAtLevel L m K n) ∈ S ∧
        LevelIsCarried σ K q'.1 := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨?_, hlev q hq⟩
    show (⟨q.1, bondPreimage σ (bondImage σ q.2)⟩ : Σ n : ℕ, BondAtLevel L m K n) ∈ S
    rw [bondPreimage_bondImage (hlev q hq).1]
    exact hq
  have horient : ∀ q ∈ S,
      (⟨q.1, positiveOrientation q.2⟩ : Σ n : ℕ, BondAtLevel L m K n) ∈ S := by
    intro q hq
    by_cases h : q.2.IsPositivelyOriented
    · rw [positiveOrientation_of_pos h]
      exact hq
    · rw [positiveOrientation_of_not h]
      exact hrev q hq
  have himage : ∀ q ∈ S, (⟨q.1, positiveOrientation (bondImage σ q.2)⟩ :
      Σ n : ℕ, BondAtLevel L m K n) ∈ bondSetImage σ S := by
    intro q hq
    by_cases h : (bondImage σ q.2).IsPositivelyOriented
    · rw [positiveOrientation_of_pos h]
      exact ⟨q, hq, rfl⟩
    · rw [positiveOrientation_of_not h, ← (hlev q hq).1.2.2.2.2.1]
      exact ⟨_, hrev q hq, rfl⟩
  let e : PositiveBondIn (bondSetImage σ S) → PositiveBondIn S := fun p =>
    ⟨⟨p.1.1, positiveOrientation (bondPreimage σ p.1.2)⟩, horient _ (hpull _ p.2.1).1,
      positiveOrientation_isPositive ((hpull _ p.2.1).2.2.2 _)⟩
  let f : PositiveBondIn S → PositiveBondIn (bondSetImage σ S) := fun p =>
    ⟨⟨p.1.1, positiveOrientation (bondImage σ p.1.2)⟩, himage _ p.2.1,
      positiveOrientation_isPositive ((hlev _ p.2.1).2.2 _)⟩
  have hef : ∀ p, f (e p) = p := by
    rintro ⟨⟨n, b'⟩, hb⟩
    have h := (hpull _ hb.1).2
    exact Subtype.ext (congrArg (Sigma.mk n)
      (positiveOrientation_bondImage_preimage h.1 h.2.1 h.2.2 hb.2))
  have hfe : ∀ p, e (f p) = p := by
    rintro ⟨⟨n, b⟩, hb⟩
    have h := hlev _ hb.1
    exact Subtype.ext (congrArg (Sigma.mk n)
      (positiveOrientation_bondImage_preimage (σ := σ.symm) h.2.1 h.1 h.2.2 hb.2))
  let E : PositiveBondIn (bondSetImage σ S) ≃ PositiveBondIn S := ⟨e, f, hef, hfe⟩
  let g : PositiveBondIn (bondSetImage σ S) → ComplexMatrix2 := fun p =>
    V₀ p.1.1 (bondPreimage σ p.1.2).opposite
  have hg : ∀ p, ¬(bondPreimage σ p.1.2).IsPositivelyOriented → g p ∈ compactGaugeGroup :=
    fun p _ => hV _ (hrev _ (hpull _ p.2.1).1)
  let M : PositiveBondIn (bondSetImage σ S) → ComplexMatrix2 → ComplexMatrix2 := fun p X =>
    if (bondPreimage σ p.1.2).IsPositivelyOriented then X
    else -ComplexMatrix2.conjugateBy (g p)⁻¹ X
  let N : PositiveBondIn (bondSetImage σ S) → ComplexMatrix2 → ComplexMatrix2 := fun p X =>
    if (bondPreimage σ p.1.2).IsPositivelyOriented then X
    else -ComplexMatrix2.conjugateBy (g p) X
  have hfam : ∀ (A : PositiveBondIn S → ComplexMatrix2) (q : PositiveBondIn S),
      familyAtLevel A q.1.1 q.1.2 = A q := fun A q => dif_pos q.2
  have hT : ∀ A p, twistedFamily (B := S) σ V₀ A p = M p (A (e p)) := by
    intro A p
    show twistedFormValue σ (V₀ p.1.1) (familyAtLevel A p.1.1) p.1.2 = _
    unfold twistedFormValue
    by_cases h : (bondPreimage σ p.1.2).IsPositivelyOriented
    · simp only [M, if_pos h]
      rw [← hfam A (e p)]
      show familyAtLevel A p.1.1 (bondPreimage σ p.1.2) =
        familyAtLevel A p.1.1 (positiveOrientation (bondPreimage σ p.1.2))
      rw [positiveOrientation_of_pos h]
    · simp only [M, if_neg h]
      rw [← hfam A (e p)]
      show -ComplexMatrix2.conjugateBy (g p)⁻¹
          (familyAtLevel A p.1.1 (bondPreimage σ p.1.2).opposite) =
        -ComplexMatrix2.conjugateBy (g p)⁻¹
          (familyAtLevel A p.1.1 (positiveOrientation (bondPreimage σ p.1.2)))
      rw [positiveOrientation_of_not h]
  have hMnorm : ∀ p X, ComplexMatrix2.operatorNorm (M p X) = ComplexMatrix2.operatorNorm X := by
    intro p X
    by_cases h : (bondPreimage σ p.1.2).IsPositivelyOriented
    · simp only [M, if_pos h]
    · simp only [M, if_neg h]
      have := hN.2.1 X (g p)⁻¹ (inv_mem_unitaryGroup_of_mem (hg p h))
      rw [← this]
      simp only [ComplexMatrix2.operatorNorm, ComplexMatrix2.conjugateBy]
      exact norm_neg _
  have hMsl : ∀ p X, X ∈ ComplexMatrix2.traceless → M p X ∈ ComplexMatrix2.traceless := by
    intro p X hX
    by_cases h : (bondPreimage σ p.1.2).IsPositivelyOriented
    · simpa only [M, if_pos h] using hX
    · simp only [M, if_neg h]
      have hd : IsUnit ((g p)⁻¹).det := by
        rw [Matrix.det_nonsing_inv]
        exact (isUnit_det_of_mem (hg p h)).ringInverse
      exact ComplexMatrix2.traceless.neg_mem (conj_mem_traceless hd hX)
  have hNsl : ∀ p X, X ∈ ComplexMatrix2.traceless → N p X ∈ ComplexMatrix2.traceless := by
    intro p X hX
    by_cases h : (bondPreimage σ p.1.2).IsPositivelyOriented
    · simpa only [N, if_pos h] using hX
    · simp only [N, if_neg h]
      exact ComplexMatrix2.traceless.neg_mem (conj_mem_traceless (isUnit_det_of_mem (hg p h)) hX)
  have hMN : ∀ p X, M p (N p X) = X := by
    intro p X
    by_cases h : (bondPreimage σ p.1.2).IsPositivelyOriented
    · simp only [M, N, if_pos h]
    · simp only [M, N, if_neg h]
      have hd := isUnit_det_of_mem (hg p h)
      have h₁ : (g p)⁻¹ * g p = 1 := Matrix.nonsing_inv_mul _ hd
      have h₂ : ((g p)⁻¹)⁻¹ = g p := Matrix.nonsing_inv_nonsing_inv _ hd
      simp only [ComplexMatrix2.conjugateBy, h₂, mul_neg, neg_mul, neg_neg]
      calc (g p)⁻¹ * (g p * X * (g p)⁻¹) * g p
          = ((g p)⁻¹ * g p) * X * ((g p)⁻¹ * g p) := by simp only [mul_assoc]
        _ = X := by rw [h₁, one_mul, mul_one]
  have hnorm : ∀ A, GroupLieProduct.supNorm (twistedFamily (B := S) σ V₀ A) =
      GroupLieProduct.supNorm A := by
    intro A
    unfold GroupLieProduct.supNorm
    exact Equiv.iSup_congr E fun p => by rw [hT, hMnorm]; rfl
  have hmem : ∀ {T : Set (Σ n : ℕ, BondAtLevel L m K n)} {A : PositiveBondIn T → ComplexMatrix2},
      A ∈ memberFamilies T ↔ ∀ s, A s ∈ ComplexMatrix2.traceless := by
    intro T A
    simp [memberFamilies, Submodule.mem_pi]
  ext A'
  constructor
  · intro hA'
    obtain ⟨h₁, h₂⟩ := mem_complexFamilyBall_iff.1 hA'
    let A : PositiveBondIn S → ComplexMatrix2 := fun p => N (f p) (A' (f p))
    have hTA : twistedFamily (B := S) σ V₀ A = A' := by
      funext p
      rw [hT]
      show M p (N (f (e p)) (A' (f (e p)))) = A' p
      rw [hef, hMN]
    refine ⟨A, mem_complexFamilyBall_iff.2 ⟨hmem.2 fun p => hNsl _ _ (hmem.1 h₁ _), ?_⟩, hTA⟩
    rw [← hnorm A, hTA]
    exact h₂
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨h₁, h₂⟩ := mem_complexFamilyBall_iff.1 hA
    refine mem_complexFamilyBall_iff.2 ⟨hmem.2 fun p => ?_, by rw [hnorm]; exact h₂⟩
    rw [hT]
    exact hMsl _ _ (hmem.1 h₁ _)
theorem opposite_mem_activeBondsAt {k n : ℕ} {Ω : ℕ → Set (FourTorus L m)}
    {b : BondAtLevel L m K n}
    (hb : b ∈ activeBondsAt K k Ω n) : b.opposite ∈ activeBondsAt K k Ω n :=
  ⟨⟨Or.symm hb.1.1, ⟨hb.1.2.2, hb.1.2.1⟩⟩, fun h =>
    hb.2 ⟨h.1, ⟨Or.symm h.2.1.1, ⟨h.2.1.2.2, h.2.1.2.1⟩⟩, Or.symm h.2.2⟩⟩
theorem opposite_mem_activeBondSet {k : ℕ} {Ω : ℕ → Set (FourTorus L m)}
    {q : Σ n : ℕ, BondAtLevel L m K n}
    (hq : q ∈ activeBondSet K k Ω) :
    (⟨q.1, q.2.opposite⟩ : Σ n : ℕ, BondAtLevel L m K n) ∈ activeBondSet K k Ω := by
  have hb : q.2 ∈ activeBondsAt K k Ω q.1 := ⟨hq.1.2, hq.2⟩
  have h := opposite_mem_activeBondsAt hb
  exact ⟨⟨hq.1.1, h.1⟩, h.2⟩
theorem preservesFamilyBall {i : ℤ} (t : IsometryFacts i K σ)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation) :
    PreservesFamilyBall K i σ := by
  intro ε εBar rB e r k Ω V₀ hε hεB hrB hdet _ hV₀ _
  have c := t.actsUpTo hdet
  refine complexFamilyBall_bondSetImage hN (fun q hq => opposite_mem_activeBondSet hq)
    (fun q hq => ?_) (fun q hq => ?_)
  · have hk := hq.1.1
    have hd : -(m : ℤ) < levelDepth K q.1 := by
      have h₁ := c.le_top
      have h₂ := t.m_pos
      simp only [levelDepth]
      omega
    exact ⟨c.cells _ (c.le_depth _ hk), c.cells_symm _ (c.le_depth _ hk), t.orientation _ hd⟩
  · exact (hV₀.1 q.1 hq.1.1).1 q.2 ⟨hq.1.2, hq.2⟩
end FamilyBall
section RegularData
variable {i : ℤ}
theorem mem_iff_of_bondImage (hS : PreservesCells σ j) {E E' : Set (Bond L m j)}
    (hE : E' = bondImage σ '' E) (hcl : IsReversalClosed E) {c b' : Bond L m j}
    (h : c = bondImage σ.symm b' ∨ c = (bondImage σ.symm b').opposite) : c ∈ E ↔ b' ∈ E' := by
  obtain ⟨d, rfl⟩ := hS.2.2.1.2 b'
  rw [bondImage_symm_bondImage hS] at h
  rw [hE, hS.2.2.1.1.mem_set_image]
  rcases h with rfl | rfl
  · rfl
  · refine ⟨fun h => ?_, hcl _⟩
    have h' := hcl _ h
    rwa [bond_opposite_opposite] at h'
theorem exists_compact_gluing {E : Set (Bond L m j)} (hE : IsReversalClosed E)
    {A M : Bond L m j → ComplexMatrix2} (hA : IsGaugeField compactGaugeGroup E A)
    (hM : IsGaugeField compactGaugeGroup univ M) :
    ∃ R : Bond L m j → ComplexMatrix2, IsGaugeField compactGaugeGroup univ R ∧
      (∀ b ∈ E, R b = A b) ∧ ∀ b ∉ E, R b = M b := by
  classical
  refine ⟨fun b => if b ∈ E then A b else M b, ⟨fun b _ => ?_, fun b _ => ?_⟩,
    fun b hb => if_pos hb, fun b hb => if_neg hb⟩
  · by_cases hb : b ∈ E
    · simpa only [if_pos hb] using hA.1 b hb
    · simpa only [if_neg hb] using hM.1 b (mem_univ b)
  · by_cases hb : b ∈ E
    · simp only [if_pos hb, if_pos (hE b hb)]
      exact hA.2 b hb
    · have hb' : b.opposite ∉ E := fun h => hb (by simpa only [bond_opposite_opposite] using hE _ h)
      simp only [if_neg hb, if_neg hb']
      exact hM.2 b (mem_univ b)
theorem plaquetteHolonomy_congr {U U' : Bond L m j → ComplexMatrix2} {p : Plaquette L m j}
    (h : ∀ b ∈ p.boundaryBonds, U b = U' b) : plaquetteHolonomy U p = plaquetteHolonomy U' p := by apply _root_.YangMills.Construction.PeriodicLattice.CentredAverageSmallFields.plaquetteHolonomy_congr <;> assumption
theorem datumImage_mem_regular {k : ℕ} {Ω : ℕ → Set (FourTorus L m)} (t : IsometryFacts i K σ)
    (hdet : IsDeterminingChainFrom K k i Ω) {εBar : ℝ}
    {V : ∀ n : ℕ, BondAtLevel L m K n → ComplexMatrix2}
    (hV : V ∈ activeRegularRealFields εBar K k Ω) :
    datumImage σ V ∈ activeRegularRealFields εBar K k (imageChain σ Ω) := by
  have c := t.actsUpTo hdet
  have hΓ : ∀ q ≤ k, activeBondsAt K k (imageChain σ Ω) q =
      bondImage σ '' activeBondsAt K k Ω q :=
    (t.chainObjects K k Ω _ c.le_depth fun _ _ => rfl).2.2.2.2.2.2.2.2.1
  have hcl : ∀ q, IsReversalClosed (activeBondsAt K k Ω q) :=
    fun q _ h => opposite_mem_activeBondsAt h
  have hcl' : ∀ q, IsReversalClosed (activeBondsAt K k (imageChain σ Ω) q) :=
    fun q _ h => opposite_mem_activeBondsAt h
  obtain ⟨h₁, h₂, h₃⟩ := hV
  have hcfg : ∀ q ≤ k, IsGaugeField compactGaugeGroup (activeBondsAt K k (imageChain σ Ω) q)
      (datumImage σ V q) := by
    intro q hq
    rw [hΓ q hq]
    exact isGaugeField_image (c.cells _ (c.le_depth q hq)) (h₁ q hq)
  refine ⟨hcfg, ?_, ?_⟩
  · intro p' hex hall
    have hd₀ := c.le_depth 0 (Nat.zero_le k)
    have hS₀ := c.cells _ hd₀
    have hE := hΓ 0 (Nat.zero_le k)
    obtain ⟨hb₁, hb₂⟩ := t.plaquetteBoundary _ hd₀ p'
    have e₁ : ∃ b ∈ (plaquetteImage σ.symm p').boundaryBonds, b ∈ activeBondsAt K k Ω 0 := by
      obtain ⟨b', hb', hin⟩ := hex
      obtain ⟨b, hb, he⟩ := hb₂ b' hb'
      exact ⟨b, hb, (mem_iff_of_bondImage hS₀ hE (hcl 0) he).2 hin⟩
    have e₂ : ∀ b ∈ (plaquetteImage σ.symm p').boundaryBonds, b ∈ activeBondsAt K k Ω 0 := by
      intro b hb
      obtain ⟨b', hb', he⟩ := hb₁ b hb
      exact (mem_iff_of_bondImage hS₀ hE (hcl 0) he).2 (hall b' hb')
    have hn := t.plaquetteNorm _ hd₀ _ _ (hcl' 0) (hcfg 0 (Nat.zero_le k)) p' hall
    rw [show transportGaugeField σ.symm (datumImage σ V 0) = V 0 from
      transport_symm_transport hS₀ (V 0)] at hn
    rw [← hn]
    exact h₂ _ e₁ e₂
  · intro q hq p' hex hall
    have hd₁ := c.le_depth (q + 1) hq
    have hdq := c.le_depth q hq.le
    have hS₁ := c.cells _ hd₁
    have hSq := c.cells _ hdq
    have hqK : q < K := lt_of_lt_of_le hq c.le_top
    have hE₁ := hΓ (q + 1) hq
    obtain ⟨hb₁, hb₂⟩ := t.plaquetteBoundary _ hd₁ p'
    have hI : (bondsInside (imageChain σ Ω q \ imageChain σ Ω (q + 1)) :
        Set (BondAtLevel L m K (q + 1))) =
        bondImage σ '' (bondsInside (Ω q \ Ω (q + 1)) : Set (BondAtLevel L m K (q + 1))) := by
      rw [show imageChain σ Ω q \ imageChain σ Ω (q + 1) = σ '' (Ω q \ Ω (q + 1)) from
        (image_sdiff σ.injective _ _).symm]
      exact (hS₁.2.2.2.2.2.2 _).2.2
    have hclI : IsReversalClosed
        (bondsInside (Ω q \ Ω (q + 1)) : Set (BondAtLevel L m K (q + 1))) :=
      fun _ h => ⟨h.2, h.1⟩
    have e₁ : ∃ b ∈ (plaquetteImage σ.symm p').boundaryBonds,
        b ∈ activeBondsAt K k Ω (q + 1) := by
      obtain ⟨b', hb', hin⟩ := hex
      obtain ⟨b, hb, he⟩ := hb₂ b' hb'
      exact ⟨b, hb, (mem_iff_of_bondImage hS₁ hE₁ (hcl _) he).2 hin⟩
    have e₂ : ∀ b ∈ (plaquetteImage σ.symm p').boundaryBonds, b ∈ activeBondsAt K k Ω (q + 1) ∨
        b ∈ (bondsInside (Ω q \ Ω (q + 1)) : Set (BondAtLevel L m K (q + 1))) := by
      intro b hb
      obtain ⟨b', hb', he⟩ := hb₁ b hb
      rcases hall b' hb' with h | h
      · exact Or.inl ((mem_iff_of_bondImage hS₁ hE₁ (hcl _) he).2 h)
      · exact Or.inr ((mem_iff_of_bondImage hS₁ hI hclI he).2 h)
    obtain ⟨H₁, H₂⟩ := h₃ q hq _ e₁ e₂
    have hAv : ∀ b : BondAtLevel L m K (q + 1), HasBlockAverageAt K q (activeBondsAt K k Ω) b →
        HasBlockAverageAt K q (activeBondsAt K k (imageChain σ Ω)) (bondImage σ b) := by
      intro b hb c' hc'
      rw [hΓ q hq.le]
      have hmem : c' ∈ (bondsInside (σ '' bondDoubleBlock b) : Set (BondAtLevel L m K q)) := by
        rw [(t.bondObjects q hqK hd₁ b).1]
        exact hc'
      rw [(hSq.2.2.2.2.2.2 _).2.2] at hmem
      obtain ⟨d, hd, rfl⟩ := hmem
      exact mem_image_of_mem _ (hb hd)
    have hAvRev : ∀ b : BondAtLevel L m K (q + 1),
        HasBlockAverageAt K q (activeBondsAt K k Ω) b.opposite →
        HasBlockAverageAt K q (activeBondsAt K k Ω) b := by
      intro b hb x hx
      have e : bondDoubleBlock b.opposite = bondDoubleBlock b := union_comm _ _
      refine hb ?_
      show x ∈ (bondsInside (bondDoubleBlock b.opposite) : Set (BondAtLevel L m K q))
      rw [e]
      exact hx
    have hFirst : ∀ d : BondAtLevel L m K (q + 1), bondImage σ d ∈ p'.boundaryBonds →
        bondImage σ d ∉ activeBondsAt K k (imageChain σ Ω) (q + 1) →
        HasBlockAverageAt K q (activeBondsAt K k Ω) d := by
      intro d hd hn
      obtain ⟨b, hb, he⟩ := hb₂ _ hd
      have hnot : b ∉ activeBondsAt K k Ω (q + 1) :=
        fun h => hn ((mem_iff_of_bondImage hS₁ hE₁ (hcl _) he).1 h)
      have hav := H₁ b hb hnot
      rw [bondImage_symm_bondImage hS₁] at he
      rcases he with rfl | rfl
      · exact hav
      · exact hAvRev _ hav
    have hW₀ := extendByOne_mem_compactGaugeFields (hcl q) (h₁ q hq.le)
    have hMr := t.averageStep_mapsTo q hqK hW₀
    obtain ⟨R, hR, hRin, hRout⟩ := exists_compact_gluing (hcl (q + 1)) (h₁ (q + 1) hq) hMr
    have hW₀on : ∀ b ∈ activeBondsAt K k Ω q,
        extendByOne (activeBondsAt K k Ω q) (V q) b = V q b := fun b hb => by
      classical
      exact if_pos hb
    have hRp : ∀ b ∈ (plaquetteImage σ.symm p').boundaryBonds,
        levelMixedField (Averaging.smoothingRadius L) K q (activeBondsAt K k Ω) V b = R b := by
      classical
      intro b hb
      by_cases hbΓ : b ∈ activeBondsAt K k Ω (q + 1)
      · rw [hRin b hbΓ]
        exact if_pos hbΓ
      · rw [hRout b hbΓ]
        refine (if_neg hbΓ).trans ?_
        exact t.doubleBlockLocal q hqK b _ _ fun x hx => (hW₀on x (H₁ b hb hbΓ hx)).symm
    have hRp' : ∀ b' ∈ p'.boundaryBonds,
        levelMixedField (Averaging.smoothingRadius L) K q (activeBondsAt K k (imageChain σ Ω))
          (datumImage σ V) b' = transportGaugeField σ R b' := by
      classical
      intro b' hb'
      obtain ⟨d, rfl⟩ := hS₁.2.2.1.2 b'
      rw [transport_bondImage hS₁]
      have hmem : bondImage σ d ∈ activeBondsAt K k (imageChain σ Ω) (q + 1) ↔
          d ∈ activeBondsAt K k Ω (q + 1) := by
        rw [hE₁]
        exact hS₁.2.2.1.1.mem_set_image
      by_cases hd : d ∈ activeBondsAt K k Ω (q + 1)
      · rw [hRin d hd]
        refine (if_pos (hmem.2 hd)).trans ?_
        exact transport_bondImage hS₁ (V (q + 1)) d
      · rw [hRout d hd]
        have hn := mt hmem.1 hd
        refine (if_neg hn).trans ?_
        have hav := hAv d (hFirst d hb' hn)
        have e₃ : blockAverage (Averaging.smoothingRadius L) (datumImage σ V q) (bondImage σ d) =
            blockAverage (Averaging.smoothingRadius L) (transportGaugeField σ
              (extendByOne (activeBondsAt K k Ω q) (V q))) (bondImage σ d) := by
          refine t.doubleBlockLocal q hqK _ _ _ fun x hx => ?_
          have hx' := hav hx
          rw [hΓ q hq.le] at hx'
          obtain ⟨y, hy, rfl⟩ := hx'
          rw [transport_bondImage hSq, hW₀on y hy]
          exact transport_bondImage hSq (V q) y
        have e₄ := congrFun ((t.averageStep q hqK hd₁).2 _ hW₀).2 (bondImage σ d)
        rw [transport_bondImage hS₁] at e₄
        exact e₃.trans e₄
    refine ⟨fun b' hb' hn => ?_, ?_⟩
    · obtain ⟨d, rfl⟩ := hS₁.2.2.1.2 b'
      exact hAv d (hFirst d hb' hn)
    · have hcfgR : IsGaugeField compactGaugeGroup univ (transportGaugeField σ R) := by
        have h := isGaugeField_image hS₁ hR
        rwa [image_univ, hS₁.2.2.1.2.range_eq] at h
      have hn := t.plaquetteNorm _ hd₁ univ _ (fun _ _ => mem_univ _) hcfgR p'
        (fun _ _ => mem_univ _)
      rw [transport_symm_transport hS₁] at hn
      rw [plaquetteHolonomy_congr hRp', ← hn, ← plaquetteHolonomy_congr hRp]
      exact H₂
theorem preservesRegularData (t : IsometryFacts i K σ) (t' : IsometryFacts i K σ.symm) :
    PreservesRegularData K i σ := by
  intro εBar e r k Ω hε hdet _
  have c := t.actsUpTo hdet
  refine ⟨fun V hV => datumImage_mem_regular t hdet hV, fun V' hV' => ?_⟩
  have h := datumImage_mem_regular t' (t.determiningSets K k Ω hdet).1 hV'
  have hseq : imageChain σ.symm (imageChain σ Ω) = Ω :=
    funext fun q => Equiv.symm_image_image σ _
  rw [hseq] at h
  exact ⟨_, h, fun n hn => transport_symm_transport (c.cells_symm _ (c.le_depth n hn)) (V' n)⟩
end RegularData
section Conclusion
variable {i : ℤ}
theorem isometryFacts
    (hAvg : AveragingMapsEquivariant)
    (hMin : IsometryCovarianceOfMinimalOrbits)
    (hGf : GaugeFixingCovarianceStatement)
    (hHol : IsometryCovariance.Statement)
    (hTow : IsometriesPreserveTowersAndStepCubes)
    (hOb : IsometryPreservesChainObjects)
    (hSB : IsometriesPreserveCells)
    (hBl : IsometryInvariance.InvariantUnderIsometries)
    (hBorel : BlockAverageIsBorelMap)
    (hReads : BlockAverageDependsOnDoubleBlock)
    (hXor : BondOrientationDichotomy)
    (hBdy : PlaquetteImageBoundary)
    (hstd : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K)
    (hi : -(m : ℤ) ≤ i)
    (hσ : σ ∈ latticeIsometries L m i) (hσ' : σ.symm ∈ latticeIsometries L m i) :
    IsometryFacts i K σ := by
  obtain ⟨ε₀, hH⟩ := hHol
  have hA := hAvg L m hstd hm i hi σ hσ K
  have hA' := hAvg L m hstd hm i hi σ.symm hσ' K
  have hGσ := hGf L m i hstd hm hi σ hσ
  refine ⟨fun j hj => hSB L m i j σ hstd hm hi hσ hj,
    fun j hj => hSB L m i j σ.symm hstd hm hi hσ' hj, hA.2.1, hA'.2.1, hA.2.2.2.2.2.1,
    fun i' Ω₀ U hd hi' hr hc => (hH L m hstd hm i hi σ hσ).2 K i' Ω₀ U hd hi' hr hc,
    fun hd ℬ U u h₁ h₂ h₃ => hGσ.1 _ hd ℬ U u h₁ h₂ h₃,
    fun ε hε k Ω V hd hV => ?_, hOb L m i σ hstd hm hi hσ,
    (hTow.1 L m i σ hstd hm hi hσ).2.1,
    fun j hj => ((hBl L m hstd hm i hi σ hσ).1 j hj).1,
    fun k hk hd P W => ((hGσ.2.2 K k hk hd).2.1 P W),
    fun j hj b => hXor L m hstd hm j hj b, hm,
    fun j hj ℬ U hcl hU p hp =>
      ((((hH L m hstd hm i hi σ.symm hσ').1 j hj).1 ℬ U hcl hU).2 p hp).2.2.2,
    fun j hj p => hBdy L m i j σ.symm hstd hm hi hσ' hj p, hA.1,
    fun k hk hd => (hBl L m hstd hm i hi σ hσ).2.1 K k hk hd,
    fun k hk c U U' h => hReads L m K k hstd hm hk _ c U U' h,
    fun k hk => ?_⟩
  · have h := (hMin L m K i σ ε hstd hm hi hσ hε).1 k Ω V hd hV
    exact ⟨h.1, h.2.1⟩
  · have h : BlockAverageBorel L m K (Averaging.smoothingRadius L) k :=
      hBorel ⟨L, hstd, ⟨K, hK⟩, ⟨m, hm⟩⟩ k hk
    exact h.choose
theorem regularSetsAndAxialGauge_covariant
    (hAvg : AveragingMapsEquivariant)
    (hMin : IsometryCovarianceOfMinimalOrbits)
    (hGf : GaugeFixingCovarianceStatement)
    (hHol : IsometryCovariance.Statement)
    (hTow : IsometriesPreserveTowersAndStepCubes)
    (hG : LatticeIsometryGroupActionStatement)
    (hOb : IsometryPreservesChainObjects)
    (hSB : IsometriesPreserveCells)
    (hBl : IsometryInvariance.InvariantUnderIsometries)
    (hBorel : BlockAverageIsBorelMap)
    (hReads : BlockAverageDependsOnDoubleBlock)
    (hXor : BondOrientationDichotomy)
    (hBdy : PlaquetteImageBoundary)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation) :
    IsometryCovariantRegularSetsAndAxialGauge := by
  intro L m K hstd hm hK i σ hi hσ
  have hσ' : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨H, hH⟩ := (hG L m i hstd hm hi).1.1
    have h₁ : σ ∈ H := by
      exact show σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) from by rw [hH]; exact hσ
    have h₂ : σ⁻¹ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := H.inv_mem h₁
    rw [hH] at h₂
    exact h₂
  have t := isometryFacts hAvg hMin hGf hHol hTow hOb hSB hBl hBorel hReads hXor hBdy
    hstd hm hK hi hσ hσ'
  have t' : IsometryFacts i K σ.symm :=
    isometryFacts hAvg hMin hGf hHol hTow hOb hSB hBl hBorel hReads hXor hBdy
      hstd hm hK hi hσ' hσ
  exact ⟨preservesOrbitFunctions t, preservesRegularFields t, preservesRegularData t t',
    preservesFamilyBall t hN, preservesAxialGaugeRepresentatives t⟩
end Conclusion
end PeriodicLattice.RegularSetsAxialGaugeCovariance
end YangMills.Construction
