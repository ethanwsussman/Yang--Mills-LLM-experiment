import YangMills.Construction.Lattice.CovarianceAndBorelMeasurabilityOfTheAveragedContours
import YangMills.Construction.Lattice.CovarianceOfGaugeFixingUnderIsometries
import YangMills.Construction.Lattice.CovarianceOfTheAveragingMapsProof
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.GaugeFixingCovariance
variable {L m : ℕ}
structure IsometryTransport (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop where
  endpoints : ∀ j : ℤ, i ≤ j → ∀ b : Bond L m j,
    ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
      ((bondImage σ b).target : FourTorus L m) = σ b.target
  sites : ∀ j : ℤ, i ≤ j → ∀ y : Site L m j,
    ((sitePreimage σ.symm y : Site L m j) : FourTorus L m) = σ y
  blocks : ∀ j : ℤ, i ≤ j → IsometryInvariance.MapsBlocks σ j
theorem isometryTransport_of_mem (hG : LatticeIsometryGroupActionStatement)
    (hB : IsometryInvariance.InvariantUnderIsometries)
    (hs : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i) {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : σ ∈ latticeIsometries L m i) : IsometryTransport σ i := by
  have hC := fun j (hj : i ≤ j) => ((hG L m i hs hm hi).2.2.2.2 σ hσ j hj).1
  refine ⟨fun j hj => (hC j hj).2.2.2.1, fun j hj y => ?_,
    fun j hj => ((hB L m hs hm i hi σ hσ).1 j hj).1⟩
  have hex : ∃ x : Site L m j, (x : FourTorus L m) = σ.symm.symm y := by
    have hmem : σ y ∈ σ '' (sublattice L m j : Set (FourTorus L m)) := ⟨y, y.2, rfl⟩
    rw [(hC j hj).1] at hmem
    exact ⟨⟨σ y, hmem⟩, rfl⟩
  exact Classical.epsilon_spec hex
theorem symm_mem_latticeIsometries (hG : LatticeIsometryGroupActionStatement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) :
    σ.symm ∈ latticeIsometries L m i := by apply _root_.YangMills.Construction.PeriodicLattice.EquivarianceProof.symm_mem_latticeIsometries <;> assumption
theorem coe_toSublattice (hL : 0 < L) {j j' : ℤ} (h : j ≤ j') (x : Site L m j) :
    ((x.toSublattice j' : Site L m j') : FourTorus L m) = x := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
section Bonds
variable {σ : FourTorus L m ≃ FourTorus L m} {i j : ℤ}
theorem bondPreimage_source (h' : IsometryTransport σ.symm i) (hj : i ≤ j) (b : Bond L m j) :
    ((bondPreimage σ b).source : FourTorus L m) = σ.symm b.source :=
  (h'.endpoints j hj b).1
theorem bondPreimage_target (h' : IsometryTransport σ.symm i) (hj : i ≤ j) (b : Bond L m j) :
    ((bondPreimage σ b).target : FourTorus L m) = σ.symm b.target :=
  (h'.endpoints j hj b).2
theorem coe_sitePreimage (h' : IsometryTransport σ.symm i) (hj : i ≤ j) (y : Site L m j) :
    ((sitePreimage σ y : Site L m j) : FourTorus L m) = σ.symm y :=
  h'.sites j hj y
theorem sitePreimage_symm_sitePreimage (h : IsometryTransport σ i)
    (h' : IsometryTransport σ.symm i) (hj : i ≤ j)
    (y : Site L m j) : sitePreimage σ.symm (sitePreimage σ y) = y :=
  Subtype.ext (by rw [h.sites j hj, coe_sitePreimage h' hj, Equiv.apply_symm_apply])
theorem bondImage_bondPreimage (h : IsometryTransport σ i) (h' : IsometryTransport σ.symm i)
    (hj : i ≤ j) (b : Bond L m j) : bondImage σ (bondPreimage σ b) = b :=
  Bond.ext
    (Subtype.ext (by
      rw [(h.endpoints j hj _).1, bondPreimage_source h' hj, Equiv.apply_symm_apply]))
    (Subtype.ext (by
      rw [(h.endpoints j hj _).2, bondPreimage_target h' hj, Equiv.apply_symm_apply]))
theorem bondPreimage_opposite (h' : IsometryTransport σ.symm i) (hj : i ≤ j) (b : Bond L m j) :
    bondPreimage σ b.opposite = (bondPreimage σ b).opposite :=
  Bond.ext (Subtype.ext (by
      show ((bondPreimage σ b.opposite).source : FourTorus L m) =
        ((bondPreimage σ b).target : FourTorus L m)
      rw [bondPreimage_source h' hj, bondPreimage_target h' hj]; rfl))
    (Subtype.ext (by
      show ((bondPreimage σ b.opposite).target : FourTorus L m) =
        ((bondPreimage σ b).source : FourTorus L m)
      rw [bondPreimage_target h' hj, bondPreimage_source h' hj]; rfl))
theorem transportGaugeField_mem_compactGaugeFields (h' : IsometryTransport σ.symm i)
    (hj : i ≤ j) {U : Bond L m j → Matrices.ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j) :
    transportGaugeField σ U ∈ compactGaugeFields L m j :=
  ⟨fun _ _ => hU.1 _ (mem_univ _), fun b _ => by
    show U (bondPreimage σ b.opposite) = (U (bondPreimage σ b))⁻¹
    rw [bondPreimage_opposite h' hj]
    exact hU.2 _ (mem_univ _)⟩
theorem transportGaugeField_gaugeTransform (h' : IsometryTransport σ.symm i) (hj : i ≤ j)
    (u : Site L m j → Matrices.ComplexMatrix2)
    (U : Bond L m j → Matrices.ComplexMatrix2) (b : Bond L m j) :
    transportGaugeField σ (gaugeTransform u U) b =
      gaugeTransform (transportSiteFunction σ u) (transportGaugeField σ U) b := by
  have e₁ : (bondPreimage σ b).source = sitePreimage σ b.source :=
    Subtype.ext (by rw [bondPreimage_source h' hj, coe_sitePreimage h' hj])
  have e₂ : (bondPreimage σ b).target = sitePreimage σ b.target :=
    Subtype.ext (by rw [bondPreimage_target h' hj, coe_sitePreimage h' hj])
  simp only [transportGaugeField, gaugeTransform, transportSiteFunction, e₁, e₂]
theorem datumImage_gaugeTransformDatum (hL : 0 < L) {K q : ℕ} (h' : IsometryTransport σ.symm i)
    (hq : i ≤ levelDepth K q) (v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) (c : BondAtLevel L m K q) :
    datumImage σ (gaugeTransformDatum v V) q c =
      gaugeTransformDatum (transportSiteFunction σ v) (datumImage σ V) q c := by
  have hle : levelDepth K q ≤ levelDepth K 0 := by simp [levelDepth]
  have h0 : i ≤ levelDepth K 0 := hq.trans hle
  have e₁ : (bondPreimage σ c).source.toSublattice (levelDepth K 0) =
      sitePreimage σ (c.source.toSublattice (levelDepth K 0)) :=
    Subtype.ext (by
      rw [coe_toSublattice hL hle, coe_sitePreimage h' h0, coe_toSublattice hL hle,
        bondPreimage_source h' hq])
  have e₂ : (bondPreimage σ c).target.toSublattice (levelDepth K 0) =
      sitePreimage σ (c.target.toSublattice (levelDepth K 0)) :=
    Subtype.ext (by
      rw [coe_toSublattice hL hle, coe_sitePreimage h' h0, coe_toSublattice hL hle,
        bondPreimage_target h' hq])
  show gaugeTransformDatum v V q (bondPreimage σ c) = _
  rw [gaugeTransformDatum_apply, gaugeTransformDatum_apply, e₁, e₂]
  rfl
end Bonds
section Sites
variable {σ : FourTorus L m ≃ FourTorus L m} {i : ℤ}
theorem siteSetImage_eq_image {j : ℤ} (h : IsometryTransport σ i) (hj : i ≤ j)
    (P : Set (Site L m j)) :
    sitePointImage σ P = sitePreimage σ.symm '' P := by
  ext x
  constructor
  · rintro ⟨y, hy, e⟩
    exact ⟨y, hy, Subtype.ext (by rw [h.sites j hj, e])⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, h.sites j hj y⟩
theorem sitePreimage_symm_injective {j : ℤ} (h : IsometryTransport σ i) (hj : i ≤ j) :
    Function.Injective (sitePreimage σ.symm : Site L m j → Site L m j) := fun x y e =>
  Subtype.ext (σ.injective (by rw [← h.sites j hj, ← h.sites j hj, e]))
theorem sitePreimage_symm_mem_sitesInBlock_iff {j j' : ℤ} (h : IsometryTransport σ i)
    (hj : i ≤ j) (hj' : i ≤ j') (y : Site L m j) (x : Site L m j') :
    sitePreimage σ.symm x ∈ sitesInBlock j' (sitePreimage σ.symm y) ↔ x ∈ sitesInBlock j' y := by
  show ((sitePreimage σ.symm x : Site L m j') : FourTorus L m) ∈
      refinedBlock 1 (sitePreimage σ.symm y) ↔ (x : FourTorus L m) ∈ refinedBlock 1 y
  rw [← h.blocks j hj 1 y, h.sites j' hj' x]
  exact σ.injective.mem_set_image
theorem sitesInBlock_sitePreimage_symm {j j' : ℤ} (h : IsometryTransport σ i)
    (h' : IsometryTransport σ.symm i) (hj : i ≤ j) (hj' : i ≤ j') (y : Site L m j) :
    sitesInBlock j' (sitePreimage σ.symm y) = sitePreimage σ.symm '' sitesInBlock j' y := by
  ext x
  constructor
  · intro hx
    refine ⟨sitePreimage σ x, ?_, sitePreimage_symm_sitePreimage h h' hj' x⟩
    rw [← sitePreimage_symm_mem_sitesInBlock_iff h hj hj', sitePreimage_symm_sitePreimage h h' hj']
    exact hx
  · rintro ⟨z, hz, rfl⟩
    exact (sitePreimage_symm_mem_sitesInBlock_iff h hj hj' y z).2 hz
theorem blockSitesExceptCenter_sitePreimage_symm {K k : ℕ} (h : IsometryTransport σ i)
    (h' : IsometryTransport σ.symm i)
    (hk : i ≤ levelDepth K (k + 1)) (hk' : i ≤ levelDepth K k) (y : SiteAtLevel L m K (k + 1)) :
    blockSitesExceptCenter K k (sitePreimage σ.symm y) =
      sitePreimage σ.symm '' blockSitesExceptCenter K k y := by
  have hne : ∀ z : SiteAtLevel L m K k,
      ((sitePreimage σ.symm z : SiteAtLevel L m K k) : FourTorus L m) ≠
          (sitePreimage σ.symm y : SiteAtLevel L m K (k + 1)) ↔
        (z : FourTorus L m) ≠ y := fun z => by
    rw [h.sites _ hk', h.sites _ hk]
    exact σ.injective.ne_iff
  ext x
  constructor
  · rintro ⟨hx, hxy⟩
    rw [sitesInBlock_sitePreimage_symm h h' hk hk'] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨z, ⟨hz, (hne z).1 hxy⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hzy⟩, rfl⟩
    exact ⟨(sitePreimage_symm_mem_sitesInBlock_iff h hk hk' y z).2 hz, (hne z).2 hzy⟩
end Sites
theorem meanContour_transport (hH : IsometryCovariance.Statement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) {j j' : ℤ}
    (hjj : j' = j + 1) (hj : i ≤ j) (ℬ : Set (Bond L m j'))
    (U : Bond L m j' → Matrices.ComplexMatrix2) (y : Site L m j)
    (x : Site L m j') (hx : x ∈ sitesInBlock j' y) (hcl : IsReversalClosed ℬ)
    (hU : IsGaugeField compactGaugeGroup ℬ U) (hΓ : ∀ Γ ∈ contourSet y x, ∀ b ∈ Γ, b ∈ ℬ) :
    (HasContourMean (transportGaugeField σ U) (sitePreimage σ.symm y)
        (sitePreimage σ.symm x) ↔ HasContourMean U y x) ∧
      (HasContourMean U y x →
        meanContourHolonomy (transportGaugeField σ U) (sitePreimage σ.symm y)
          (sitePreimage σ.symm x) = meanContourHolonomy U y x) := by
  subst hjj
  obtain ⟨ε, hε⟩ := hH
  exact ((hε L m hs hm i hi σ hσ).1 j hj).2.2.2 y x ℬ U hx hcl hU hΓ |>.2
theorem levelDepth_eq_succ_add_one (K k : ℕ) : levelDepth K k = levelDepth K (k + 1) + 1 := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.levelDepth_eq_succ_add_one <;> assumption
theorem axialGauge_transport (hH : IsometryCovariance.Statement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i)
    (h : IsometryTransport σ i) (h' : IsometryTransport σ.symm i) {K k : ℕ}
    (hk : i ≤ levelDepth K (k + 1)) (A₀ : ℝ) (𝔭₀ : ℕ) (x : ℕ → ℝ)
    (P'' : Set (SiteAtLevel L m K (k + 1))) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (hV : V ∈ gaugeFieldsAtLevel L m K k) :
    (HasOffCenterContours K k (sitePointImage σ P'') (transportGaugeField σ V) ↔
        HasOffCenterContours K k P'' V) ∧
      axialGaugeFactor A₀ 𝔭₀ x K k (transportGaugeField σ V) (sitePointImage σ P'') =
        axialGaugeFactor A₀ 𝔭₀ x K k V P'' ∧
      (HasOffCenterContours K k P'' V →
        axialGaugeFunction K k (sitePointImage σ P'') (transportGaugeField σ V) =
          axialGaugeFunction K k P'' V) := by
  have hk' : i ≤ levelDepth K k := by rw [levelDepth_eq_succ_add_one]; omega
  have key := fun (y : SiteAtLevel L m K (k + 1)) (z : SiteAtLevel L m K k)
      (hz : z ∈ sitesInBlock (levelDepth K k) y) =>
    meanContour_transport hH hs hm hi hσ (levelDepth_eq_succ_add_one K k) hk univ V y z hz
      (fun _ _ => mem_univ _) hV (fun _ _ _ _ => mem_univ _)
  have hP := siteSetImage_eq_image h hk P''
  have hoff := fun y => blockSitesExceptCenter_sitePreimage_symm (K := K) (k := k) h h' hk hk' y
  have hinj := sitePreimage_symm_injective (L := L) (m := m) h hk
  have hinj' := sitePreimage_symm_injective (L := L) (m := m) h hk'
  have hiff : HasOffCenterContours K k (sitePointImage σ P'') (transportGaugeField σ V) ↔
      HasOffCenterContours K k P'' V := by
    rw [hP]
    constructor
    · intro hc y hy z hz
      exact (key y z hz.1).1.1 (hc _ ⟨y, hy, rfl⟩ _ (by rw [hoff]; exact ⟨z, hz, rfl⟩))
    · rintro hc _ ⟨y, hy, rfl⟩ z' hz'
      rw [hoff] at hz'
      obtain ⟨z, hz, rfl⟩ := hz'
      exact (key y z hz.1).1.2 (hc y hy z hz)
  refine ⟨hiff, ?_, fun hc => ?_⟩
  · simp only [axialGaugeFactor]
    by_cases hc : HasOffCenterContours K k P'' V
    · rw [if_pos (hiff.2 hc), if_pos hc, hP, finprod_mem_image hinj.injOn]
      refine finprod_mem_congr rfl fun y hy => ?_
      rw [hoff, finprod_mem_image hinj'.injOn]
      refine finprod_mem_congr rfl fun z hz => ?_
      rw [(key y z hz.1).2 (hc y hy z hz)]
    · rw [if_neg (fun e => hc (hiff.1 e)), if_neg hc]
  · simp only [axialGaugeFunction]
    rw [hP, finsum_mem_image hinj.injOn]
    refine finsum_mem_congr rfl fun y hy => ?_
    rw [hoff, finsum_mem_image hinj'.injOn]
    refine finsum_mem_congr rfl fun z hz => ?_
    rw [(key y z hz.1).2 (hc y hy z hz)]
theorem isBlockAxialGauge_transport (hH : IsometryCovariance.Statement)
    (hC : MeanContourCovarianceStatement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i)
    (h : IsometryTransport σ i) (h' : IsometryTransport σ.symm i) {K k : ℕ} (hkK : k < K)
    (hk : i ≤ levelDepth K (k + 1)) (P'' : Set (SiteAtLevel L m K (k + 1)))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (hA : IsBlockAxialGauge K k P'' V) :
    IsBlockAxialGauge K k (sitePointImage σ P'') (transportGaugeField σ V) := by
  have hk' : i ≤ levelDepth K k := by rw [levelDepth_eq_succ_add_one]; omega
  obtain ⟨⟨-, hconf, hdef⟩, hone⟩ := hA
  have hcl : IsReversalClosed (blockBonds (levelDepth K k) P'') := by
    rintro b ⟨y, hy, hb⟩
    exact ⟨y, hy, hb.2, hb.1⟩
  have key : ∀ y ∈ P'', ∀ z ∈ sitesInBlock (levelDepth K k) y, _ := fun y hy z hz =>
    meanContour_transport hH hs hm hi hσ (levelDepth_eq_succ_add_one K k) hk
      (blockBonds (levelDepth K k) P'') V y z hz hcl
      hconf (fun Γ hΓ b hb => ⟨y, hy, (hC L m K hs.1 hs.2 hm k hkK y z hz).1 Γ hΓ b hb⟩)
  have hP := siteSetImage_eq_image h hk P''
  obtain ⟨ε, hε⟩ := hH
  have hconf' : IsGaugeField compactGaugeGroup (bondImage σ '' blockBonds (levelDepth K k) P'')
      (transportGaugeField σ V) :=
    (((hε L m hs hm i hi σ hσ).1 _ hk').1 _ V hcl hconf).1.2.1
  have hsub : blockBonds (levelDepth K k) (sitePointImage σ P'') ⊆
      bondImage σ '' blockBonds (levelDepth K k) P'' := by
    rintro b ⟨y', hy', hb⟩
    rw [hP] at hy'
    obtain ⟨y, hy, rfl⟩ := hy'
    refine ⟨bondPreimage σ b, ⟨y, hy, ?_, ?_⟩, bondImage_bondPreimage h h' hk' b⟩
    · have e : (bondPreimage σ b).source = sitePreimage σ b.source :=
        Subtype.ext (by rw [bondPreimage_source h' hk', coe_sitePreimage h' hk'])
      rw [e, ← sitePreimage_symm_mem_sitesInBlock_iff h hk hk',
        sitePreimage_symm_sitePreimage h h' hk']
      exact hb.1
    · have e : (bondPreimage σ b).target = sitePreimage σ b.target :=
        Subtype.ext (by rw [bondPreimage_target h' hk', coe_sitePreimage h' hk'])
      rw [e, ← sitePreimage_symm_mem_sitesInBlock_iff h hk hk',
        sitePreimage_symm_sitePreimage h h' hk']
      exact hb.2
  refine ⟨⟨hkK, ⟨fun b hb => hconf'.1 b (hsub hb), fun b hb => hconf'.2 b (hsub hb)⟩, ?_⟩, ?_⟩
  · intro y' hy' x' hx'
    rw [hP] at hy'
    obtain ⟨y, hy, rfl⟩ := hy'
    rw [sitesInBlock_sitePreimage_symm h h' hk hk'] at hx'
    obtain ⟨z, hz, rfl⟩ := hx'
    exact (key y hy z hz).1.2 (hdef y hy z hz)
  · intro y' hy' x' hx' hne
    rw [hP] at hy'
    obtain ⟨y, hy, rfl⟩ := hy'
    rw [sitesInBlock_sitePreimage_symm h h' hk hk'] at hx'
    obtain ⟨z, hz, rfl⟩ := hx'
    rw [(key y hy z hz).2 (hdef y hy z hz)]
    refine hone y hy z hz fun e => hne ?_
    rw [h.sites _ hk', h.sites _ hk, e]
theorem isClosed_compactGaugeFields (L m : ℕ) (j : ℤ) : IsClosed (compactGaugeFields L m j) := by apply _root_.YangMills.Construction.PeriodicLattice.isClosed_compactGaugeFields <;> assumption
theorem rgMap_transportMeasure (hA : AveragingMapsEquivariant)
    (hW : BlockAverageIsBorelMap)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i)
    (h' : IsometryTransport σ.symm i) {K k : ℕ} (hkK : k < K)
    (hk : i ≤ levelDepth K (k + 1)) (ν : Measure (BondAtLevel L m K k → Matrices.ComplexMatrix2))
    (hν : IsFiniteGaugeMeasure k ν) :
    rgMap (K := K) k (transportMeasure σ ν) = transportMeasure σ (rgMap k ν) := by
  classical
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hk' : i ≤ levelDepth K k := by rw [levelDepth_eq_succ_add_one]; omega
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) hkK
  obtain ⟨hmaps, hborel⟩ : BlockAverageBorel L m K (Averaging.smoothingRadius L) k :=
    hW ⟨L, hs, ⟨K, hK⟩, ⟨m, hm⟩⟩ k hkK
  have hSm : MeasurableSet (gaugeFieldsAtLevel L m K k) :=
    (isClosed_compactGaugeFields L m _).measurableSet
  have hf : Measurable (hmaps.restrict _ _ _) := by
    have e₁ := BorelSpace.measurable_eq (α := ↥(gaugeFieldsAtLevel L m K k))
    have e₂ := BorelSpace.measurable_eq (α := ↥(gaugeFieldsAtLevel L m K (k + 1)))
    unfold Kernels.IsBorelMeasurable at hborel
    rw [← e₁, ← e₂] at hborel
    exact hborel
  set g : (BondAtLevel L m K k → Matrices.ComplexMatrix2) →
      BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2 :=
    fun U => if hU : U ∈ gaugeFieldsAtLevel L m K k then
      ((hmaps.restrict _ _ _ ⟨U, hU⟩ : gaugeFieldsAtLevel L m K (k + 1)) :
        BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2)
      else (fun _ => 1) with hgdef
  have hg : Measurable g :=
    Measurable.dite (measurable_subtype_coe.comp hf) measurable_const hSm
  have hgS : ∀ U ∈ gaugeFieldsAtLevel L m K k,
      g U = blockAverageStep (Averaging.smoothingRadius L) k U := by
    intro U hU
    simp only [hgdef, dif_pos hU]
    rfl
  have hT : Measurable (transportGaugeField σ :
      (BondAtLevel L m K k → Matrices.ComplexMatrix2) →
        BondAtLevel L m K k → Matrices.ComplexMatrix2) :=
    measurable_pi_lambda _ fun b => measurable_pi_apply _
  have hT' : Measurable (transportGaugeField σ :
      (BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2) →
        BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2) :=
    measurable_pi_lambda _ fun b => measurable_pi_apply _
  have hae : ∀ᵐ U ∂ν, U ∈ gaugeFieldsAtLevel L m K k := mem_ae_iff.2 hν.2
  have hae' : ∀ᵐ U ∂(ν.map (transportGaugeField σ)),
      U ∈ gaugeFieldsAtLevel L m K k := by
    refine (ae_map_iff hT.aemeasurable (p := fun U => U ∈ gaugeFieldsAtLevel L m K k) hSm).2 ?_
    exact hae.mono fun U hU => transportGaugeField_mem_compactGaugeFields h' hk' hU
  have hcomm := ((hA L m hs hm i hi σ hσ K).1 k hkK hk).2
  simp only [rgMap, transportMeasure]
  calc (ν.map (transportGaugeField σ)).map (blockAverageStep (Averaging.smoothingRadius L) k)
      = (ν.map (transportGaugeField σ)).map g :=
        Measure.map_congr (hae'.mono fun U hU => (hgS U hU).symm)
    _ = ν.map (g ∘ transportGaugeField σ) := Measure.map_map hg hT
    _ = ν.map (transportGaugeField σ ∘ g) := Measure.map_congr (hae.mono fun U hU => by
        show g (transportGaugeField σ U) = transportGaugeField σ (g U)
        rw [hgS _ (transportGaugeField_mem_compactGaugeFields h' hk' hU), hgS U hU]
        exact (hcomm U hU).2)
    _ = (ν.map g).map (transportGaugeField σ) := (Measure.map_map hT' hg).symm
    _ = (ν.map (blockAverageStep (Averaging.smoothingRadius L) k)).map (transportGaugeField σ) := by
        rw [Measure.map_congr (hae.mono fun U hU => hgS U hU)]
theorem gaugeFixingCovariance (hG : LatticeIsometryGroupActionStatement)
    (hB : IsometryInvariance.InvariantUnderIsometries)
    (hH : IsometryCovariance.Statement)
    (hA : AveragingMapsEquivariant)
    (hW : BlockAverageIsBorelMap)
    (hC : MeanContourCovarianceStatement) :
    GaugeFixingCovarianceStatement := by
  intro L m i hs hm hi σ hσ
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hs.2
  have h := isometryTransport_of_mem hG hB hs hm hi hσ
  have hσ' := symm_mem_latticeIsometries hG hs hm hi hσ
  have h' := isometryTransport_of_mem hG hB hs hm hi hσ'
  refine ⟨fun j hj ℬ U u _ _ _ b _ => transportGaugeField_gaugeTransform h' hj u U b, ?_, ?_⟩
  · rintro K k Ω - - hreg V v - - _ ⟨⟨a, b⟩, hb, rfl⟩
    obtain ⟨c, hc, hc', -⟩ := hreg a hb.1
    exact datumImage_gaugeTransformDatum hL h' (hc.trans hc') v V _
  · intro K k hkK hk
    have hk' : i ≤ levelDepth K k := by rw [levelDepth_eq_succ_add_one]; omega
    refine ⟨fun A₀ 𝔭₀ x P'' V hV => axialGauge_transport hH hs hm hi hσ h h' hk A₀ 𝔭₀ x P'' V hV,
      fun P'' V => ⟨fun hax => ?_, isBlockAxialGauge_transport hH hC hs hm hi hσ h h' hkK hk P'' V⟩,
      fun ν hν => rgMap_transportMeasure hA hW hs hm hi hσ h' hkK hk ν hν⟩
    have := isBlockAxialGauge_transport hH hC hs hm hi hσ' h' h hkK hk (sitePointImage σ P'')
      (transportGaugeField σ V) hax
    have e₁ : sitePointImage σ.symm (sitePointImage σ P'') = P'' := by
      rw [siteSetImage_eq_image h hk, siteSetImage_eq_image h' hk, image_image]
      simp only [Equiv.symm_symm]
      conv_rhs => rw [← image_id P'']
      exact image_congr fun y _ => sitePreimage_symm_sitePreimage h' h hk y
    have e₂ : transportGaugeField σ.symm (transportGaugeField σ V) = V := by
      funext b
      show V (bondPreimage σ (bondPreimage σ.symm b)) = V b
      exact congrArg V (bondImage_bondPreimage h' h hk' b)
    rwa [e₁, e₂] at this
end YangMills.Construction.PeriodicLattice.GaugeFixingCovariance
