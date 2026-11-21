import YangMills.Construction.Lattice.LiftingIsConsistentWithTheAveragesProof
import YangMills.Construction.Lattice.ConstraintSetsAndAxialGaugeAtComplexConfigurationsUnderIsometries
import YangMills.Construction.Lattice.CovarianceOfComplexAveragesProof
import YangMills.Construction.Lattice.IsometryCovarianceOfTowersAndCubesOfAStep
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
namespace ComplexConstraintIsometry
variable {L m : ℕ}
section Bonds
variable {j : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
theorem bondImage_source (h : MapsCellsAndCubes σ j) (b : Bond L m j) :
    ((bondImage σ b).source : FourTorus L m) = σ b.source := (h.2.2.2.1 b).1
theorem bondImage_target (h : MapsCellsAndCubes σ j) (b : Bond L m j) :
    ((bondImage σ b).target : FourTorus L m) = σ b.target := (h.2.2.2.1 b).2
theorem bondPreimage_bondImage (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    bondPreimage σ (bondImage σ b) = b := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.bondPreimage_bondImage <;> assumption
theorem bondImage_bondPreimage (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    bondImage σ (bondPreimage σ b) = b := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexAveragesCommuteWithIsometries.bondImage_bondPreimage <;> assumption
theorem bondImage_opposite (h : MapsCellsAndCubes σ j) (b : Bond L m j) :
    bondImage σ b.opposite = (bondImage σ b).opposite := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.bondImage_opposite <;> assumption
theorem transportGaugeField_bondImage (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (U : Bond L m j → ComplexMatrix2) (b : Bond L m j) :
    transportGaugeField σ U (bondImage σ b) = U b := by
  simp only [transportGaugeField, bondPreimage_bondImage h h']
theorem coe_sitePreimage_symm (h : MapsCellsAndCubes σ j) (y : Site L m j) :
    ((sitePreimage σ.symm y : Site L m j) : FourTorus L m) = σ y := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.coe_sitePreimage_of_maps <;> assumption
theorem coe_sitePreimage (h : MapsCellsAndCubes σ.symm j) (y : Site L m j) :
    ((sitePreimage σ y : Site L m j) : FourTorus L m) = σ.symm y :=
  coe_sitePreimage_symm (σ := σ.symm) h y
theorem bondImage_source_eq (h : MapsCellsAndCubes σ j) (b : Bond L m j) :
    (bondImage σ b).source = sitePreimage σ.symm b.source :=
  Subtype.ext (by rw [bondImage_source h, coe_sitePreimage_symm h])
theorem bondImage_target_eq (h : MapsCellsAndCubes σ j) (b : Bond L m j) :
    (bondImage σ b).target = sitePreimage σ.symm b.target :=
  Subtype.ext (by rw [bondImage_target h, coe_sitePreimage_symm h])
theorem bondImage_mem_bondsInside_image (h : MapsCellsAndCubes σ j) (X : Set (FourTorus L m))
    (b : Bond L m j) : bondImage σ b ∈ (bondsInside (σ '' X) : Set (Bond L m j)) ↔
      b ∈ (bondsInside X : Set (Bond L m j)) := by
  simp only [bondsInside, mem_ofPred_eq, bondImage_source h, bondImage_target h,
    σ.injective.mem_set_image]
theorem image_bondsInside (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (X : Set (FourTorus L m)) :
    bondImage σ '' (bondsInside X : Set (Bond L m j)) = bondsInside (σ '' X) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.image_bondsInside <;> assumption
theorem isGaugeField_transport_iff (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (G : Set ComplexMatrix2) (B : Set (Bond L m j))
    (V : Bond L m j → ComplexMatrix2) :
    IsGaugeField G (bondImage σ '' B) (transportGaugeField σ V) ↔ IsGaugeField G B V := by
  constructor
  · rintro ⟨hg, hr⟩
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · have := hg _ (mem_image_of_mem _ hb)
      rwa [transportGaugeField_bondImage h h'] at this
    · have := hr _ (mem_image_of_mem _ hb)
      rwa [← bondImage_opposite h, transportGaugeField_bondImage h h',
        transportGaugeField_bondImage h h'] at this
  · rintro ⟨hg, hr⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      rw [transportGaugeField_bondImage h h']
      exact hg b hb
    · rintro _ ⟨b, hb, rfl⟩
      rw [← bondImage_opposite h, transportGaugeField_bondImage h h',
        transportGaugeField_bondImage h h']
      exact hr b hb
theorem extendByOne_congr {B : Set (Bond L m j)} {W W' : Bond L m j → ComplexMatrix2}
    (h : ∀ b ∈ B, W b = W' b) : extendByOne B W = extendByOne B W' := by apply _root_.YangMills.Construction.PeriodicLattice.LiftAveragesProof.extendByOne_congr <;> assumption
end Bonds
theorem transport_mem_complexInteriorFields {K : ℕ} {σ : FourTorus L m ≃ FourTorus L m}
    (h : MapsCellsAndCubes σ (levelDepth K 0))
    (h' : MapsCellsAndCubes σ.symm (levelDepth K 0)) {X : Set (FourTorus L m)}
    {W : BondAtLevel L m K 0 → ComplexMatrix2} (hW : W ∈ complexInteriorFields K X) :
    transportGaugeField σ W ∈ complexInteriorFields K (σ '' X) := by
  obtain ⟨hc, h1⟩ := hW
  refine ⟨?_, fun b hb => ?_⟩
  · rw [← image_bondsInside h h']
    exact (isGaugeField_transport_iff h h' _ _ _).2 hc
  · refine h1 _ fun hb' => hb ?_
    have := (bondImage_mem_bondsInside_image h X _).2 hb'
    rwa [bondImage_bondPreimage h h'] at this
section Bridge
variable {K : ℕ}
theorem complexAverageIsDefined_succ (B : Set (BondAtLevel L m K 0))
    (U : BondAtLevel L m K 0 → ComplexMatrix2) (n : ℕ) (c : BondAtLevel L m K (n + 1)) :
    ComplexAverageIsDefined K B U (n + 1) c ↔
      ∀ c' : BondAtLevel L m K (n + 1), (c' = c ∨ c' = c.opposite) → c'.IsPositivelyOriented →
        (∀ b ∈ (bondsInDoubleBlock c' : Set (BondAtLevel L m K n)),
          ComplexAverageIsDefined K B U n b) ∧
        complexBlockFieldAtLevel n U ∈ complexAveragingDomainNearOne c' := by
  rw [ComplexAverageIsDefined]
theorem complexIterateDefinedAt_succ (B : Set (BondAtLevel L m K 0))
    (W : BondAtLevel L m K 0 → ComplexMatrix2) (n : ℕ) (c : BondAtLevel L m K (n + 1)) :
    ComplexIterateDefinedAt B W (n + 1) c ↔
      (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) ⊆ (complexIteratePartial B W n).support ∧
        onSetElseOne (bondsInDoubleBlock c) (complexIteratePartial B W n).field ∈
          complexAveragingDomainNearOne c.positivelyOriented :=
  Iff.rfl
theorem complexIterate_succ (B : Set (BondAtLevel L m K 0))
    (W : BondAtLevel L m K 0 → ComplexMatrix2) (n : ℕ) (c : BondAtLevel L m K (n + 1)) :
    complexIterate B W (n + 1) c =
      complexBlockAverage (onSetElseOne (bondsInDoubleBlock c)
        (complexIteratePartial B W n).field) c :=
  rfl
theorem complexBlockFieldAtLevel_succ (U : BondAtLevel L m K 0 → ComplexMatrix2) (n : ℕ)
    (c : BondAtLevel L m K (n + 1)) :
    complexBlockFieldAtLevel (n + 1) U c = complexBlockAverage (complexBlockFieldAtLevel n U) c :=
  rfl
theorem complexAverageIsDefined_iff_iterateDefined (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hpos : PositiveOrientationOfBondAndOpposite)
    (hread : ComplexAverageIsLocal)
    (B : Set (BondAtLevel L m K 0)) (W : BondAtLevel L m K 0 → ComplexMatrix2) :
    ∀ (n : ℕ), n ≤ K → ∀ c : BondAtLevel L m K n,
      (ComplexAverageIsDefined K B (extendByOne B W) n c ↔
        ComplexIterateDefinedAt B W n c) ∧
      (ComplexIterateDefinedAt B W n c →
        complexBlockFieldAtLevel n (extendByOne B W) c = complexIterate B W n c)
  | 0, _, c => by
    refine ⟨by rw [ComplexAverageIsDefined]; exact Iff.rfl, fun hc => ?_⟩
    have hc' : c ∈ B := hc
    change extendByOne B W c = W c
    simp only [extendByOne, if_pos hc']
  | n + 1, hn, c => by
    have hnK : n < K := hn
    have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) hnK
    have ih := complexAverageIsDefined_iff_iterateDefined hL hm hpos hread B W n hnK.le
    obtain ⟨-, hxor, hp, hor, -, -, hP⟩ := hpos L m K hL hm hK n hnK c
    have reads := hread L m K n hL.1 hL.2 hm hnK
    have agree : (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
          ComplexIterateDefinedAt B W n b) →
        ∀ b ∈ (bondsInDoubleBlock c.positivelyOriented : Set (BondAtLevel L m K n)),
          complexBlockFieldAtLevel n (extendByOne B W) b =
            onSetElseOne (bondsInDoubleBlock c) (complexIteratePartial B W n).field b := by
      intro hf b hb
      rw [hP] at hb
      simp only [onSetElseOne, if_pos hb]
      exact (ih b).2 (hf b hb)
    have unique : ∀ c' : BondAtLevel L m K (n + 1), (c' = c ∨ c' = c.opposite) →
        c'.IsPositivelyOriented → c' = c.positivelyOriented := by
      rintro c' (rfl | rfl) hc'
      · simp only [Bond.positivelyOriented, if_pos hc']
      · have hnot : ¬c.IsPositivelyOriented := by
          rcases hxor with ⟨-, hb⟩ | ⟨-, hb⟩
          · exact absurd hc' hb
          · exact hb
        simp only [Bond.positivelyOriented, if_neg hnot]
    refine ⟨⟨fun hd => ?_, fun hf => ?_⟩, fun hf => ?_⟩
    · obtain ⟨hb, hdom⟩ := (complexAverageIsDefined_succ _ _ _ _).1 hd _ hor hp
      rw [hP] at hb
      have hform : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
          ComplexIterateDefinedAt B W n b := fun b hb' => (ih b).1.1 (hb b hb')
      exact (complexIterateDefinedAt_succ _ _ _ _).2
        ⟨fun b hb' => hform b hb', ((reads _ hp).mem_domain_iff _ _ (agree hform)).1 hdom⟩
    · obtain ⟨hs, hdom⟩ := (complexIterateDefinedAt_succ _ _ _ _).1 hf
      have hform : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
          ComplexIterateDefinedAt B W n b := fun b hb' => hs hb'
      refine (complexAverageIsDefined_succ _ _ _ _).2 fun c' hc' hpc' => ?_
      rw [unique c' hc' hpc']
      refine ⟨fun b hb => (ih b).1.2 (hform b (hP ▸ hb)), ?_⟩
      exact ((reads _ hp).mem_domain_iff _ _ (agree hform)).2 hdom
    · obtain ⟨hs, -⟩ := (complexIterateDefinedAt_succ _ _ _ _).1 hf
      have hform : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
          ComplexIterateDefinedAt B W n b := fun b hb' => hs hb'
      have hag := agree hform
      rw [complexBlockFieldAtLevel_succ, complexIterate_succ]
      by_cases hc : c.IsPositivelyOriented
      · have e : c.positivelyOriented = c := if_pos hc
        rw [e] at hag
        simp only [complexBlockAverage, if_pos hc]
        exact (reads c hc).average_eq _ _ hag
      · have e : c.positivelyOriented = c.opposite := if_neg hc
        rw [e] at hag hp
        simp only [complexBlockAverage, if_neg hc]
        rw [(reads c.opposite hp).average_eq _ _ hag]
theorem complexIterateDefinedAt_congr (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hpos : PositiveOrientationOfBondAndOpposite)
    (hread : ComplexAverageIsLocal)
    {B : Set (BondAtLevel L m K 0)} {W W' : BondAtLevel L m K 0 → ComplexMatrix2}
    (h : ∀ b ∈ B, W b = W' b) {n : ℕ} (hn : n ≤ K) (c : BondAtLevel L m K n)
    (hf : ComplexIterateDefinedAt B W n c) : ComplexIterateDefinedAt B W' n c := by
  have h₁ := ((complexAverageIsDefined_iff_iterateDefined hL hm hpos hread B W n hn c).1).2 hf
  rw [extendByOne_congr h] at h₁
  exact ((complexAverageIsDefined_iff_iterateDefined hL hm hpos hread B W' n hn c).1).1 h₁
end Bridge
section Constraint
variable {i : ℤ} {σ : FourTorus L m ≃ FourTorus L m} {K k : ℕ} {Ω : ℕ → Set (FourTorus L m)}
structure TransportHypotheses (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) (K k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) : Prop where
  blockingFactor : Conventions.IsAdmissibleBlockingFactor L
  m_pos : 0 < m
  orientation : PositiveOrientationOfBondAndOpposite
  locality : ComplexAverageIsLocal
  averages : PreservesComplexBlockAverages σ i
  maps : ∀ j : ℤ, i ≤ j → MapsCellsAndCubes σ j
  mapsInv : ∀ j : ℤ, i ≤ j → MapsCellsAndCubes σ.symm j
  activeBondSet_imageChain : activeBondSet K k (imageChain σ Ω) = bondSetImage σ (activeBondSet K k Ω)
  chain : IsChainFromIndex K k i Ω
namespace TransportHypotheses
variable (S : TransportHypotheses i σ K k Ω)
include S
theorem level_le {q : Σ j : ℕ, BondAtLevel L m K j} (hq : q ∈ activeBondSet K k Ω) : q.1 ≤ K :=
  hq.1.1.trans S.chain.2.2.1
theorem index_le_levelDepth {q : Σ j : ℕ, BondAtLevel L m K j} (hq : q ∈ activeBondSet K k Ω) :
    i ≤ levelDepth K q.1 := by
  have h₁ := S.chain.index_le_levelDepth
  have h₂ : q.1 ≤ k := hq.1.1
  have h₃ : levelDepth K k ≤ levelDepth K q.1 := by
    simp only [levelDepth]
    omega
  exact h₁.trans h₃
theorem index_le_levelDepth_zero : i ≤ levelDepth K 0 := by
  have h₁ := S.chain.index_le_levelDepth
  have h₃ : levelDepth K k ≤ levelDepth K 0 := by
    simp only [levelDepth]
    omega
  exact h₁.trans h₃
theorem maps_zero : MapsCellsAndCubes σ (levelDepth K 0) := S.maps _ S.index_le_levelDepth_zero
theorem mapsInv_zero : MapsCellsAndCubes σ.symm (levelDepth K 0) :=
  S.mapsInv _ S.index_le_levelDepth_zero
theorem image_bondsInside_zero :
    bondImage σ '' (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) =
      bondsInside (imageChain σ Ω 0) :=
  image_bondsInside S.maps_zero S.mapsInv_zero (Ω 0)
theorem holomorphicEquation {q : Σ j : ℕ, BondAtLevel L m K j} (hq : q ∈ activeBondSet K k Ω) :
    IsHolomorphicEquation σ
      (complexGaugeFields (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)))
      (bondsInside (Ω 0) : Set (BondAtLevel L m K 0))
      {U ∈ complexGaugeFields (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) |
        ComplexIterateDefinedAt (bondsInside (imageChain σ Ω 0))
          (transportGaugeField σ U) q.1 (bondImage σ q.2)}
      {U ∈ complexGaugeFields (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) |
        ComplexIterateDefinedAt (bondsInside (Ω 0)) U q.1 q.2}
      (fun U => complexIterate (bondsInside (imageChain σ Ω 0))
        (transportGaugeField σ U) q.1 (bondImage σ q.2))
      (fun U => transportGaugeField σ (complexIterate (bondsInside (Ω 0)) U q.1)
        (bondImage σ q.2)) := by
  have h := (S.averages K).2 q.1 (S.level_le hq) (S.index_le_levelDepth hq)
    (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) (fun _ hb => ⟨hb.2, hb.1⟩) q.2
  rw [S.image_bondsInside_zero] at h
  exact h
theorem hasComplexBlockDatum_iff (W : BondAtLevel L m K 0 → ComplexMatrix2) :
    HasComplexBlockDatum K k Ω (Ω 0) W ↔
      ∀ q ∈ activeBondSet K k Ω, ComplexIterateDefinedAt (bondsInside (Ω 0)) W q.1 q.2 :=
  forall₂_congr fun q hq =>
    (complexAverageIsDefined_iff_iterateDefined S.blockingFactor S.m_pos S.orientation S.locality
      _ W q.1 (S.level_le hq) q.2).1
theorem hasComplexBlockDatum_imageChain_iff (Y : BondAtLevel L m K 0 → ComplexMatrix2) :
    HasComplexBlockDatum K k (imageChain σ Ω) (imageChain σ Ω 0) Y ↔
      ∀ q ∈ activeBondSet K k Ω, ComplexIterateDefinedAt (bondsInside (imageChain σ Ω 0)) Y q.1
        (bondImage σ q.2) := by
  unfold HasComplexBlockDatum
  rw [S.activeBondSet_imageChain, bondSetImage, forall_mem_image]
  exact forall₂_congr fun q hq =>
    (complexAverageIsDefined_iff_iterateDefined S.blockingFactor S.m_pos S.orientation S.locality
      _ Y q.1 (S.level_le hq) _).1
omit S in
theorem mem_complexGaugeFields_of_interior {W : BondAtLevel L m K 0 → ComplexMatrix2}
    (hW : W ∈ complexInteriorFields K (Ω 0)) :
    W ∈ complexGaugeFields (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) :=
  hW.1
theorem complexBlockDatum_bondImage {W : BondAtLevel L m K 0 → ComplexMatrix2}
    (hW : W ∈ complexInteriorFields K (Ω 0)) {q : Σ j : ℕ, BondAtLevel L m K j}
    (hq : q ∈ activeBondSet K k Ω)
    (h₂ : ComplexIterateDefinedAt (bondsInside (Ω 0)) W q.1 q.2)
    (h₁ : ComplexIterateDefinedAt (bondsInside (imageChain σ Ω 0))
      (transportGaugeField σ W) q.1 (bondImage σ q.2)) :
    complexBlockDatum K (imageChain σ Ω 0) (transportGaugeField σ W) q.1
        (bondImage σ q.2) =
      complexBlockDatum K (Ω 0) W q.1 q.2 := by
  have hP := mem_complexGaugeFields_of_interior hW
  have e := (S.holomorphicEquation hq).2.2.1 W ⟨⟨hP, h₁⟩, ⟨hP, h₂⟩⟩
  have e' : complexIterate (bondsInside (imageChain σ Ω 0))
      (transportGaugeField σ W) q.1 (bondImage σ q.2) =
      complexIterate (bondsInside (Ω 0)) W q.1 q.2 := by
    refine e.trans ?_
    exact transportGaugeField_bondImage (S.maps _ (S.index_le_levelDepth hq))
      (S.mapsInv _ (S.index_le_levelDepth hq)) _ _
  unfold complexBlockDatum
  rw [(complexAverageIsDefined_iff_iterateDefined S.blockingFactor S.m_pos S.orientation S.locality
      _ W q.1 (S.level_le hq) q.2).2 h₂,
    (complexAverageIsDefined_iff_iterateDefined S.blockingFactor S.m_pos S.orientation S.locality
      _ _ q.1 (S.level_le hq) _).2 h₁]
  exact e'
theorem mem_complexConstraintSet_iff (X : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2)
    {W : BondAtLevel L m K 0 → ComplexMatrix2} (hW : W ∈ complexInteriorFields K (Ω 0))
    (hd : HasComplexBlockDatum K k Ω (Ω 0) W)
    (hd' : HasComplexBlockDatum K k (imageChain σ Ω) (imageChain σ Ω 0)
      (transportGaugeField σ W)) :
    W ∈ complexConstraintSet K k Ω X ↔
      transportGaugeField σ W ∈ complexConstraintSet K k (imageChain σ Ω) (datumImage σ X) := by
  have core : ∀ q ∈ activeBondSet K k Ω,
      complexBlockDatum K (imageChain σ Ω 0) (transportGaugeField σ W) q.1
        (bondImage σ q.2) = complexBlockDatum K (Ω 0) W q.1 q.2 := fun q hq =>
    S.complexBlockDatum_bondImage hW hq ((S.hasComplexBlockDatum_iff W).1 hd q hq)
      ((S.hasComplexBlockDatum_imageChain_iff _).1 hd' q hq)
  have image : ∀ q ∈ activeBondSet K k Ω,
      datumImage σ X q.1 (bondImage σ q.2) = X q.1 q.2 := fun q hq =>
    transportGaugeField_bondImage (S.maps _ (S.index_le_levelDepth hq))
      (S.mapsInv _ (S.index_le_levelDepth hq)) _ _
  constructor
  · rintro ⟨-, -, he⟩
    refine ⟨transport_mem_complexInteriorFields S.maps_zero S.mapsInv_zero hW, hd', fun q' hq' => ?_⟩
    rw [S.activeBondSet_imageChain] at hq'
    obtain ⟨q, hq, rfl⟩ := hq'
    exact (core q hq).trans ((he q hq).trans (image q hq).symm)
  · rintro ⟨-, -, he⟩
    refine ⟨hW, hd, fun q hq => ?_⟩
    have hq' : (⟨q.1, bondImage σ q.2⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈
        activeBondSet K k (imageChain σ Ω) := by
      rw [S.activeBondSet_imageChain]
      exact mem_image_of_mem _ hq
    exact (core q hq).symm.trans ((he _ hq').trans (image q hq))
theorem exists_isOpen_iterateDefined {q : Σ j : ℕ, BondAtLevel L m K j}
    (hq : q ∈ activeBondSet K k Ω) :
    ∃ T : Set (BondAtLevel L m K 0 → ComplexMatrix2), IsOpen T ∧
      ∀ W ∈ complexInteriorFields K (Ω 0), (W ∈ T ↔
        ComplexIterateDefinedAt (bondsInside (imageChain σ Ω 0))
            (transportGaugeField σ W) q.1 (bondImage σ q.2) ∧
          ComplexIterateDefinedAt (bondsInside (Ω 0)) W q.1 q.2) := by
  obtain ⟨-, -, ⟨O, hO, hOe⟩, -⟩ := (S.holomorphicEquation hq).1
  have hcont : Continuous (restrictToBonds (bondsInside (Ω 0) : Set (BondAtLevel L m K 0))) := by
    unfold restrictToBonds
    exact continuous_pi fun b => continuous_apply _
  refine ⟨_, hO.preimage hcont, fun W hW => ?_⟩
  have hP := mem_complexGaugeFields_of_interior hW
  constructor
  · intro hWO
    have hmem : restrictToBonds (bondsInside (Ω 0)) W ∈ O ∩
        restrictToBonds (bondsInside (Ω 0)) ''
          complexGaugeFields (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) :=
      ⟨hWO, mem_image_of_mem _ hP⟩
    rw [← hOe] at hmem
    obtain ⟨W', ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩, e⟩ := hmem
    have agree : ∀ b ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)), W' b = W b :=
      fun b hb => congrFun e ⟨b, hb⟩
    have agree' : ∀ b ∈ (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0)),
        transportGaugeField σ W' b = transportGaugeField σ W b := by
      rw [← S.image_bondsInside_zero]
      rintro _ ⟨b, hb, rfl⟩
      rw [transportGaugeField_bondImage S.maps_zero S.mapsInv_zero,
        transportGaugeField_bondImage S.maps_zero S.mapsInv_zero]
      exact agree b hb
    exact ⟨complexIterateDefinedAt_congr S.blockingFactor S.m_pos S.orientation S.locality agree'
        (S.level_le hq) _ h₁,
      complexIterateDefinedAt_congr S.blockingFactor S.m_pos S.orientation S.locality agree
        (S.level_le hq) _ h₂⟩
  · rintro ⟨h₁, h₂⟩
    have hmem : restrictToBonds (bondsInside (Ω 0)) W ∈
        restrictToBonds (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) ''
          ({U ∈ complexGaugeFields (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) |
              ComplexIterateDefinedAt (bondsInside (imageChain σ Ω 0))
                (transportGaugeField σ U) q.1 (bondImage σ q.2)} ∩
            {U ∈ complexGaugeFields (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) |
              ComplexIterateDefinedAt (bondsInside (Ω 0)) U q.1 q.2}) :=
      mem_image_of_mem _ ⟨⟨hP, h₁⟩, ⟨hP, h₂⟩⟩
    rw [hOe] at hmem
    exact hmem.1
theorem isRelativelyOpen_datumDefined :
    ComplexMatrix2.IsRelativelyOpen (complexInteriorFields K (Ω 0))
      {W | W ∈ complexInteriorFields K (Ω 0) ∧ HasComplexBlockDatum K k Ω (Ω 0) W ∧
        HasComplexBlockDatum K k (imageChain σ Ω) (imageChain σ Ω 0)
          (transportGaugeField σ W)} := by
  have hfin : ∀ j : ℤ, Finite (Bond L m j) := fun j =>
    have := SeparatedSequences.BaseParameters.site_finite (L := L)
      (by have := S.blockingFactor.2; omega) m j
    Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) fun b b' h =>
      Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hT := fun (q : Σ j : ℕ, BondAtLevel L m K j) (hq : q ∈ activeBondSet K k Ω) =>
    S.exists_isOpen_iterateDefined hq
  choose! T hTo hT using hT
  refine ⟨⋂ (n : Fin (k + 1)) (c : BondAtLevel L m K n)
      (_ : (⟨n, c⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k Ω), T ⟨n, c⟩, ?_, ?_⟩
  · have := hfin
    exact isOpen_iInter_of_finite fun n =>
      haveI := hfin (levelDepth K n)
      isOpen_iInter_of_finite fun c => isOpen_iInter_of_finite fun h => hTo _ h
  · ext W
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨hW, hd, hd'⟩
      refine ⟨fun n c h => ?_, hW⟩
      exact (hT _ h W hW).2 ⟨(S.hasComplexBlockDatum_imageChain_iff _).1 hd' _ h,
        (S.hasComplexBlockDatum_iff W).1 hd _ h⟩
    · rintro ⟨hmem, hW⟩
      have hall : ∀ q ∈ activeBondSet K k Ω, W ∈ T q := fun q hq => by
        obtain ⟨n, c⟩ := q
        have hn : n < k + 1 := Nat.lt_succ_of_le hq.1.1
        exact hmem ⟨n, hn⟩ c hq
      exact ⟨hW, (S.hasComplexBlockDatum_iff W).2 fun q hq => ((hT q hq W hW).1 (hall q hq)).2,
        (S.hasComplexBlockDatum_imageChain_iff _).2 fun q hq => ((hT q hq W hW).1 (hall q hq)).1⟩
theorem hasComplexBlockDatum_iff_transport (ht : IsTorusTranslation σ)
    {W : BondAtLevel L m K 0 → ComplexMatrix2}
    (hP : W ∈ complexGaugeFields (bondsInside (Ω 0) : Set (BondAtLevel L m K 0))) :
    HasComplexBlockDatum K k Ω (Ω 0) W ↔
      HasComplexBlockDatum K k (imageChain σ Ω) (imageChain σ Ω 0)
        (transportGaugeField σ W) := by
  rw [S.hasComplexBlockDatum_iff, S.hasComplexBlockDatum_imageChain_iff]
  refine forall₂_congr fun q hq => ?_
  have e := (S.holomorphicEquation hq).2.2.2 ht
  constructor
  · intro h
    have : W ∈ {U ∈ complexGaugeFields (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) |
        ComplexIterateDefinedAt (bondsInside (imageChain σ Ω 0))
          (transportGaugeField σ U) q.1 (bondImage σ q.2)} := by
      rw [e]
      exact ⟨hP, h⟩
    exact this.2
  · intro h
    have : W ∈ {U ∈ complexGaugeFields (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) |
        ComplexIterateDefinedAt (bondsInside (Ω 0)) U q.1 q.2} := by
      rw [← e]
      exact ⟨hP, h⟩
    exact this.2
theorem image_complexConstraintSet (ht : IsTorusTranslation σ)
    (X : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) :
    transportGaugeField σ '' complexConstraintSet K k Ω X =
      complexConstraintSet K k (imageChain σ Ω) (datumImage σ X) := by
  ext W'
  constructor
  · rintro ⟨W, hW, rfl⟩
    have hd' := (S.hasComplexBlockDatum_iff_transport ht
      (mem_complexGaugeFields_of_interior hW.1)).1 hW.2.1
    exact (S.mem_complexConstraintSet_iff X hW.1 hW.2.1 hd').1 hW
  · intro hW'
    have hback : transportGaugeField σ (transportGaugeField σ.symm W') = W' := by
      funext b
      change W' (bondImage σ (bondPreimage σ b)) = W' b
      rw [bondImage_bondPreimage S.maps_zero S.mapsInv_zero]
    have hW : transportGaugeField σ.symm W' ∈ complexInteriorFields K (Ω 0) := by
      have h := transport_mem_complexInteriorFields (σ := σ.symm) S.mapsInv_zero S.maps_zero hW'.1
      rwa [imageChain, Equiv.symm_image_image] at h
    have hd' : HasComplexBlockDatum K k (imageChain σ Ω) (imageChain σ Ω 0)
        (transportGaugeField σ (transportGaugeField σ.symm W')) := by
      rw [hback]
      exact hW'.2.1
    have hd := (S.hasComplexBlockDatum_iff_transport ht
      (mem_complexGaugeFields_of_interior hW)).2 hd'
    refine ⟨_, (S.mem_complexConstraintSet_iff X hW hd hd').2 ?_, hback⟩
    rw [hback]
    exact hW'
end TransportHypotheses
end Constraint
section Axial
variable {i : ℤ} {σ : FourTorus L m ≃ FourTorus L m} {K k : ℕ}
theorem sitePreimage_mem_sitesInBlock_iff {j j₁ : ℤ} (h : MapsCellsAndCubes σ j)
    (hb : IsometryInvariance.MapsBlocks σ j₁) (y : Site L m j₁) (x : Site L m j) :
    sitePreimage σ.symm x ∈ sitesInBlock j (sitePreimage σ.symm y) ↔ x ∈ sitesInBlock j y := by
  change ((sitePreimage σ.symm x : Site L m j) : FourTorus L m) ∈
      refinedBlock 1 (sitePreimage σ.symm y) ↔ (x : FourTorus L m) ∈ refinedBlock 1 y
  rw [coe_sitePreimage_symm h, ← hb 1 y, σ.injective.mem_set_image]
theorem blockBonds_image {j j₁ : ℤ} (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j)
    (hb : IsometryInvariance.MapsBlocks σ j₁) (P : Set (Site L m j₁)) :
    blockBonds j (sitePreimage σ.symm '' P) = bondImage σ '' blockBonds j P := by
  ext b'
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, ht, hh⟩
    have e := bondImage_bondPreimage h h' b'
    rw [← e, bondImage_source_eq h] at ht
    rw [← e, bondImage_target_eq h] at hh
    exact ⟨bondPreimage σ b', ⟨y, hy, (sitePreimage_mem_sitesInBlock_iff h hb y _).1 ht,
      (sitePreimage_mem_sitesInBlock_iff h hb y _).1 hh⟩, e⟩
  · rintro ⟨b, ⟨y, hy, ht, hh⟩, rfl⟩
    refine ⟨_, mem_image_of_mem _ hy, ?_, ?_⟩
    · rw [bondImage_source_eq h]
      exact (sitePreimage_mem_sitesInBlock_iff h hb y _).2 ht
    · rw [bondImage_target_eq h]
      exact (sitePreimage_mem_sitesInBlock_iff h hb y _).2 hh
theorem isComplexBlockAxialGauge_transport_iff (hC : PreservesComplexContourMeans σ i)
    (h₁ : MapsCellsAndCubes σ (levelDepth K (k + 1)))
    (h : MapsCellsAndCubes σ (levelDepth K k))
    (h' : MapsCellsAndCubes σ.symm (levelDepth K k))
    (hb : IsometryInvariance.MapsBlocks σ (levelDepth K (k + 1)))
    (hk : k < K) (hi : i ≤ levelDepth K (k + 1)) (P : Set (SiteAtLevel L m K (k + 1)))
    (V : BondAtLevel L m K k → ComplexMatrix2) :
    IsComplexBlockAxialGauge K k (sitePreimage σ.symm '' P) (transportGaugeField σ V) ↔
      IsComplexBlockAxialGauge K k P V := by
  have transfer : ∀ y ∈ P, ∀ x ∈ sitesInBlock (levelDepth K k) y,
      IsGaugeField complexGaugeGroup (blockBonds (levelDepth K k) P) V →
      (ComplexMatrix2.familyDiameter (contourHolonomies (transportGaugeField σ V)
          (sitePreimage σ.symm y) (sitePreimage σ.symm x)) =
        ComplexMatrix2.familyDiameter (contourHolonomies V y x)) ∧
      (ComplexMatrix2.familyDiameter (contourHolonomies V y x) < Averaging.centreOfMassDiameter →
        complexMeanContourHolonomy (transportGaugeField σ V) (sitePreimage σ.symm y)
          (sitePreimage σ.symm x) = complexMeanContourHolonomy V y x) := by
    intro y hy x hx hc
    have hU : V ∈ complexGaugeFields (bondsInside (unitBlock y) : Set (BondAtLevel L m K k)) :=
      ⟨fun b hb' => hc.1 b ⟨y, hy, hb'.1, hb'.2⟩, fun b hb' => hc.2 b ⟨y, hy, hb'.1, hb'.2⟩⟩
    obtain ⟨e, hid⟩ := hC K k hk hi y x hx
    refine ⟨e V hU, fun hd => ?_⟩
    exact hid.2.2.1 V ⟨⟨hU, by rw [e V hU]; exact hd⟩, ⟨hU, hd⟩⟩
  have hne : ∀ (y : SiteAtLevel L m K (k + 1)) (x : SiteAtLevel L m K k),
      ((sitePreimage σ.symm x : SiteAtLevel L m K k) : FourTorus L m) ≠
        (sitePreimage σ.symm y : SiteAtLevel L m K (k + 1)) ↔ (x : FourTorus L m) ≠ y := by
    intro y x
    rw [coe_sitePreimage_symm h, coe_sitePreimage_symm h₁]
    exact σ.injective.ne_iff
  unfold IsComplexBlockAxialGauge
  rw [blockBonds_image h h' hb, isGaugeField_transport_iff h h']
  constructor
  · rintro ⟨hk', hc, hv⟩
    refine ⟨hk', hc, fun y hy x hx => ?_⟩
    obtain ⟨e, ev⟩ := transfer y hy x hx hc
    obtain ⟨hd, hn⟩ := hv _ (mem_image_of_mem _ hy) _
      ((sitePreimage_mem_sitesInBlock_iff h hb y x).2 hx)
    rw [e] at hd
    exact ⟨hd, fun hxy => by rw [← ev hd]; exact hn ((hne y x).2 hxy)⟩
  · rintro ⟨hk', hc, hv⟩
    refine ⟨hk', hc, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ x₂ hx₂
    have hsite : sitePreimage σ.symm (sitePreimage σ x₂) = x₂ :=
      Subtype.ext (by rw [coe_sitePreimage_symm h, coe_sitePreimage h', Equiv.apply_symm_apply])
    rw [← hsite] at hx₂ ⊢
    have hx := (sitePreimage_mem_sitesInBlock_iff h hb y _).1 hx₂
    obtain ⟨e, ev⟩ := transfer y hy _ hx hc
    obtain ⟨hd, hn⟩ := hv y hy _ hx
    refine ⟨by rw [e]; exact hd, fun hxy => ?_⟩
    rw [ev hd]
    exact hn ((hne y _).1 hxy)
end Axial
end ComplexConstraintIsometry
open ComplexConstraintIsometry in
theorem isometriesPreserveComplexConstraintSetsAndAxialGauge_of_covariance
    (hav : ComplexAveragesCommuteWithIsometries.Statement)
    (hcon : ComplexContourHolonomyCovariance)
    (hiso : LatticeIsometryGroupActionStatement)
    (hblk : IsometryInvariance.InvariantUnderIsometries)
    (hsets : IsometriesPreserveTowersAndStepCubes)
    (hpos : PositiveOrientationOfBondAndOpposite)
    (hread : ComplexAverageIsLocal) :
    IsometriesPreserveComplexConstraintSetsAndAxialGauge := by
  intro L m hL hm i hi σ hσ
  have hgroup := hiso L m i hL hm hi
  obtain ⟨⟨H, hH⟩, -⟩ := hgroup.1
  have hσ' : σ.symm ∈ latticeIsometries L m i := by
    have hs : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
    rw [← hH]
    exact H.inv_mem hs
  have hc : ∀ j : ℤ, i ≤ j → MapsCellsAndCubes σ j := fun j hj =>
    (hgroup.2.2.2.2 σ hσ j hj).1
  have hc' : ∀ j : ℤ, i ≤ j → MapsCellsAndCubes σ.symm j := fun j hj =>
    (hgroup.2.2.2.2 σ.symm hσ' j hj).1
  have hA := hav L m i σ hL hm hi hσ
  have hC := hcon L m i σ hL hm hi hσ
  have hforce := (hsets.1 L m i σ hL hm hi hσ).2.2.1
  refine ⟨fun K k Ω hΩ => ?_, fun K k hk hi' P V => ?_⟩
  · have S : TransportHypotheses i σ K k Ω := ⟨hL, hm, hpos, hread, hA, hc, hc',
      (hforce K k Ω ⟨hΩ.2.2.1, hΩ.2.2.2.1, hΩ.2.2.2.2⟩).2.1, hΩ⟩
    exact ⟨S.isRelativelyOpen_datumDefined,
      fun X _ W hW hd hd' => S.mem_complexConstraintSet_iff X hW hd hd',
      fun ht X _ => S.image_complexConstraintSet ht X⟩
  · have hi₀ : i ≤ levelDepth K k := hi'.trans (by simp only [levelDepth]; omega)
    exact isComplexBlockAxialGauge_transport_iff hC (hc _ hi') (hc _ hi₀) (hc' _ hi₀)
      ((hblk L m hL hm i hi σ hσ).1 _ hi').1 hk hi' P V
end PeriodicLattice
end YangMills.Construction
