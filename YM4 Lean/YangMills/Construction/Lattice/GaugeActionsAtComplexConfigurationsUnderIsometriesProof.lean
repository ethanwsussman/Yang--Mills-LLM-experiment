import YangMills.Construction.Lattice.ActionOfABareGaugeTransformation
import YangMills.Construction.Lattice.ConstraintSetsAndAxialGaugeAtComplexConfigurationsUnderIsometriesProof
import YangMills.Construction.Lattice.GaugeActionsAtComplexConfigurationsUnderIsometries
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ComplexGaugeCovarianceUnderIsometries
open YangMills.Construction.Matrices
variable {L m : ℕ} {j : ℤ}
theorem analyticAt_apply_coord {ι : Type} [Fintype ι] (a : ι) (w : ι → ComplexMatrix2) :
    AnalyticAt ℂ (fun w : ι → ComplexMatrix2 => w a) w :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ComplexMatrix2) a).analyticAt w
theorem isHolomorphicInFieldAndGauge_of_conj {S : Type} [Finite S] {B : Set (Bond L m j)}
    [Finite ↥B] {f : (Bond L m j → ComplexMatrix2) → (S → ComplexMatrix2) → ComplexMatrix2}
    {b : Bond L m j} (hb : b ∈ B) (s t : S)
    (hf : ∀ U ∈ complexGaugeFields B, ∀ u : S → ComplexMatrix2, (∀ x, u x ∈ complexGaugeGroup) →
      f U u = u s * U b * (u t)⁻¹) :
    IsHolomorphicInFieldAndGauge B f := by
  let _ : Fintype ↥B := Fintype.ofFinite _
  let _ : Fintype S := Fintype.ofFinite _
  refine ⟨inferInstance, inferInstance, fun U _ u hu => ?_⟩
  refine ⟨fun w => w (Sum.inr s) * w (Sum.inl ⟨b, hb⟩) * (w (Sum.inr t))⁻¹, ?_, ?_⟩
  · have hdet : (fieldGaugePoint B U u (Sum.inr t)).det ≠ 0 := by
      have h : (u t).det = 1 := hu t
      show (u t).det ≠ 0
      rw [h]
      exact one_ne_zero
    have hinv : AnalyticAt ℂ (fun w : ↥B ⊕ S → ComplexMatrix2 => (w (Sum.inr t))⁻¹)
        (fieldGaugePoint B U u) :=
      AnalyticAt.comp (g := fun Y : ComplexMatrix2 => Y⁻¹)
        (f := fun w : ↥B ⊕ S → ComplexMatrix2 => w (Sum.inr t))
        (analyticAt_inv_of_det_ne_zero hdet) (analyticAt_apply_coord _ _)
    exact ((analyticAt_apply_coord _ _).mul (analyticAt_apply_coord _ _)).mul hinv
  · refine Eventually.of_forall fun w U' hU' u' hu' hw => ?_
    rw [hf U' hU' u' hu', ← hw]
    rfl
section Transport
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem coe_sitePreimage (h : MapsCellsAndCubes σ.symm j) (y : Site L m j) :
    ((sitePreimage σ y : Site L m j) : FourTorus L m) = σ.symm y := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexConstraintIsometry.coe_sitePreimage <;> assumption
theorem bondPreimage_bondImage (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    bondPreimage σ (bondImage σ b) = b := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.bondPreimage_bondImage <;> assumption
theorem sitePreimage_source_bondImage (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    sitePreimage σ (bondImage σ b).source = b.source :=
  Subtype.ext (by rw [coe_sitePreimage h', (h.2.2.2.1 b).1, Equiv.symm_apply_apply])
theorem sitePreimage_target_bondImage (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    sitePreimage σ (bondImage σ b).target = b.target :=
  Subtype.ext (by rw [coe_sitePreimage h', (h.2.2.2.1 b).2, Equiv.symm_apply_apply])
theorem complexGaugeTransformCovariant_of_maps (hL : 0 < L) (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) :
    ComplexGaugeTransformCovariant σ j := by
  intro B b hb
  have hS : Finite (Site L m j) := SeparatedSequences.BaseParameters.site_finite hL m j
  have hB : Finite (Bond L m j) :=
    Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) fun b b' hbb =>
      Bond.ext (congrArg Prod.fst hbb) (congrArg Prod.snd hbb)
  have hleft : ∀ (U : Bond L m j → ComplexMatrix2) (u : Site L m j → ComplexMatrix2),
      transportGaugeField σ (gaugeTransform u U) (bondImage σ b) =
        u b.source * U b * (u b.target)⁻¹ := by
    intro U u
    show gaugeTransform u U (bondPreimage σ (bondImage σ b)) = _
    rw [bondPreimage_bondImage h h']
    rfl
  have hright : ∀ (U : Bond L m j → ComplexMatrix2) (u : Site L m j → ComplexMatrix2),
      gaugeTransform (transportSiteFunction σ u) (transportGaugeField σ U) (bondImage σ b) =
        u b.source * U b * (u b.target)⁻¹ := by
    intro U u
    show u (sitePreimage σ (bondImage σ b).source) * U (bondPreimage σ (bondImage σ b)) *
      (u (sitePreimage σ (bondImage σ b).target))⁻¹ = _
    rw [bondPreimage_bondImage h h', sitePreimage_source_bondImage h h',
      sitePreimage_target_bondImage h h']
  refine ⟨isHolomorphicInFieldAndGauge_of_conj hb b.source b.target fun U _ u _ => hleft U u,
    isHolomorphicInFieldAndGauge_of_conj hb b.source b.target fun U _ u _ => hright U u,
    fun U _ u _ => (hleft U u).trans (hright U u).symm⟩
end Transport
section ComplexData
variable {K k : ℕ} {σ : FourTorus L m ≃ FourTorus L m}
theorem sitePreimage_finest_source {n : ℕ} (hL : 0 < L)
    (h : MapsCellsAndCubes σ (levelDepth K n))
    (h₀' : MapsCellsAndCubes σ.symm (levelDepth K 0)) (b : BondAtLevel L m K n) :
    sitePreimage σ ((bondImage σ b).source.toSublattice (levelDepth K 0)) =
      b.source.toSublattice (levelDepth K 0) :=
  Subtype.ext (by
    rw [coe_sitePreimage h₀', coe_toSublattice_finest hL, coe_toSublattice_finest hL,
      (h.2.2.2.1 b).1, Equiv.symm_apply_apply])
theorem sitePreimage_finest_target {n : ℕ} (hL : 0 < L)
    (h : MapsCellsAndCubes σ (levelDepth K n))
    (h₀' : MapsCellsAndCubes σ.symm (levelDepth K 0)) (b : BondAtLevel L m K n) :
    sitePreimage σ ((bondImage σ b).target.toSublattice (levelDepth K 0)) =
      b.target.toSublattice (levelDepth K 0) :=
  Subtype.ext (by
    rw [coe_sitePreimage h₀', coe_toSublattice_finest hL, coe_toSublattice_finest hL,
      (h.2.2.2.1 b).2, Equiv.symm_apply_apply])
theorem complexDatumGaugeCovariant_of_maps {Ω : ℕ → Set (FourTorus L m)} (hL : 0 < L)
    (h : ∀ n ≤ k, MapsCellsAndCubes σ (levelDepth K n))
    (h' : ∀ n ≤ k, MapsCellsAndCubes σ.symm (levelDepth K n)) :
    ComplexDatumGaugeCovariant σ K k Ω := by
  rintro ⟨n, b⟩ hq
  have hnk : n ≤ k := hq.1.1
  have hb : b ∈ activeBondsAt K k Ω n := ⟨hq.1.2, hq.2⟩
  have hn := h n hnk
  have hn' := h' n hnk
  have h₀' := h' 0 (Nat.zero_le k)
  have hS : Finite (SiteAtLevel L m K 0) := SeparatedSequences.BaseParameters.site_finite hL m _
  have hB : Finite (BondAtLevel L m K n) := by
    have : Finite (SiteAtLevel L m K n) := SeparatedSequences.BaseParameters.site_finite hL m _
    exact Finite.of_injective (fun b : BondAtLevel L m K n => (b.source, b.target))
      fun b b' hbb => Bond.ext (congrArg Prod.fst hbb) (congrArg Prod.snd hbb)
  have hleft : ∀ (Y : BondAtLevel L m K n → ComplexMatrix2)
      (v : SiteAtLevel L m K 0 → ComplexMatrix2),
      transportGaugeField σ (gaugeTransform (restrictGaugeMap n v) Y) (bondImage σ b) =
        v (b.source.toSublattice (levelDepth K 0)) * Y b *
          (v (b.target.toSublattice (levelDepth K 0)))⁻¹ := by
    intro Y v
    show gaugeTransform (restrictGaugeMap n v) Y (bondPreimage σ (bondImage σ b)) = _
    rw [bondPreimage_bondImage hn hn']
    rfl
  have hright : ∀ (Y : BondAtLevel L m K n → ComplexMatrix2)
      (v : SiteAtLevel L m K 0 → ComplexMatrix2),
      gaugeTransform (restrictGaugeMap n (transportSiteFunction σ v)) (transportGaugeField σ Y)
          (bondImage σ b) =
        v (b.source.toSublattice (levelDepth K 0)) * Y b *
          (v (b.target.toSublattice (levelDepth K 0)))⁻¹ := by
    intro Y v
    show v (sitePreimage σ ((bondImage σ b).source.toSublattice (levelDepth K 0))) *
        Y (bondPreimage σ (bondImage σ b)) *
        (v (sitePreimage σ ((bondImage σ b).target.toSublattice (levelDepth K 0))))⁻¹ = _
    rw [bondPreimage_bondImage hn hn', sitePreimage_finest_source hL hn h₀',
      sitePreimage_finest_target hL hn h₀']
  refine ⟨isHolomorphicInFieldAndGauge_of_conj hb _ _ fun Y _ v _ => hleft Y v,
    isHolomorphicInFieldAndGauge_of_conj hb _ _ fun Y _ v _ => hright Y v, fun X _ v _ => ?_⟩
  exact (hleft (X n) v).trans (hright (X n) v).symm
theorem complexStabilizerCovariant_of_maps {Ω : ℕ → Set (FourTorus L m)}
    (h₀ : MapsCellsAndCubes σ (levelDepth K 0))
    (h₀' : MapsCellsAndCubes σ.symm (levelDepth K 0))
    (hnode : ∀ x, IsEndpointOf (activeBondSet K k (imageChain σ Ω)) (σ x) ↔
      IsEndpointOf (activeBondSet K k Ω) x) :
    ComplexStabilizerCovariant σ K k Ω := by
  have hcoe : ∀ x : SiteAtLevel L m K 0,
      ((sitePreimage σ x : SiteAtLevel L m K 0) : FourTorus L m) = σ.symm x :=
    coe_sitePreimage h₀'
  have hcoe' : ∀ x : SiteAtLevel L m K 0,
      ((sitePreimage σ.symm x : SiteAtLevel L m K 0) : FourTorus L m) = σ x :=
    coe_sitePreimage (σ := σ.symm) h₀
  have hpi : ∀ x : SiteAtLevel L m K 0, sitePreimage σ (sitePreimage σ.symm x) = x := fun x =>
    Subtype.ext (by rw [hcoe, hcoe', Equiv.symm_apply_apply])
  have hip : ∀ x : SiteAtLevel L m K 0, sitePreimage σ.symm (sitePreimage σ x) = x := fun x =>
    Subtype.ext (by rw [hcoe', hcoe, Equiv.apply_symm_apply])
  have hsite : ∀ x : SiteAtLevel L m K 0,
      x ∈ (sitesIn (imageChain σ Ω 0) : Set (SiteAtLevel L m K 0)) ↔
        sitePreimage σ x ∈ (sitesIn (Ω 0) : Set (SiteAtLevel L m K 0)) := by
    intro x
    show (x : FourTorus L m) ∈ σ '' Ω 0 ↔
      ((sitePreimage σ x : SiteAtLevel L m K 0) : FourTorus L m) ∈ Ω 0
    rw [hcoe]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [← hyx, Equiv.symm_apply_apply]
      exact hy
    · intro hx
      exact ⟨_, hx, Equiv.apply_symm_apply σ _⟩
  have hnd : ∀ x : SiteAtLevel L m K 0,
      IsEndpointOf (activeBondSet K k (imageChain σ Ω)) (x : FourTorus L m) ↔
        IsEndpointOf (activeBondSet K k Ω)
          ((sitePreimage σ x : SiteAtLevel L m K 0) : FourTorus L m) := by
    intro x
    have := hnode (σ.symm x)
    rw [Equiv.apply_symm_apply] at this
    rw [hcoe]
    exact this
  apply Subset.antisymm
  · rintro w ⟨w₁, w₂, w₃⟩
    refine ⟨fun x => w (sitePreimage σ.symm x), ?_, ?_⟩
    · rw [complexStabilizerGroup, mem_ofPred_eq]
      refine ⟨fun x hx => w₁ _ ((hsite _).2 ?_), fun x hx => w₂ _ fun hh => hx ?_,
        fun x hx => w₃ _ ((hnd _).2 ?_)⟩
      · rw [hpi]
        exact hx
      · have := (hsite _).1 hh
        rwa [hpi] at this
      · rw [hpi]
        exact hx
    · funext x
      show w (sitePreimage σ.symm (sitePreimage σ x)) = w x
      rw [hip]
  · rintro _ ⟨u, ⟨u₁, u₂, u₃⟩, rfl⟩
    rw [complexStabilizerGroup, mem_ofPred_eq]
    exact ⟨fun x hx => u₁ _ ((hsite x).1 hx), fun x hx => u₂ _ fun hh => hx ((hsite x).2 hh),
      fun x hx => u₃ _ ((hnd x).1 hx)⟩
end ComplexData
theorem statement_holds (h₁ : LatticeIsometryGroupActionStatement)
    (h₂ : IsometriesPreserveTowersAndStepCubes) :
    ComplexGaugeCovarianceUnderIsometries.Statement := by
  intro L m hL hm i hi σ hσ
  have hpos : 0 < L := by
    have := hL.2
    omega
  have hg := h₁ L m i hL hm hi
  have hσ' : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨⟨H, hH⟩, -⟩ := hg.1
    have t : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
    have t' := H.inv_mem t
    rw [← hH]
    exact t'
  have hcar : ∀ j : ℤ, i ≤ j → MapsCellsAndCubes σ j :=
    fun j hj => (hg.2.2.2.2 σ hσ j hj).1
  have hcar' : ∀ j : ℤ, i ≤ j → MapsCellsAndCubes σ.symm j :=
    fun j hj => (hg.2.2.2.2 σ.symm hσ' j hj).1
  refine ⟨fun j hj => complexGaugeTransformCovariant_of_maps hpos (hcar j hj) (hcar' j hj),
    fun K k Ω hΩ => ?_⟩
  have hidx : i ≤ levelDepth K k := hΩ.index_le_levelDepth
  have hlev : ∀ n ≤ k, i ≤ levelDepth K n := fun n hn => by
    have : (n : ℤ) ≤ k := by exact_mod_cast hn
    simp only [levelDepth] at hidx ⊢
    omega
  have hAt : IsDeterminingChainFrom K k i Ω := ⟨hΩ.2.2.1, hΩ.2.2.2.1, hΩ.2.2.2.2⟩
  have hset := (h₂.1 L m i σ hL hm hi hσ).2.2.1 K k Ω hAt
  exact ⟨complexDatumGaugeCovariant_of_maps hpos (fun n hn => hcar _ (hlev n hn))
      (fun n hn => hcar' _ (hlev n hn)),
    complexStabilizerCovariant_of_maps (hcar _ (hlev 0 (Nat.zero_le k)))
      (hcar' _ (hlev 0 (Nat.zero_le k))) hset.2.2.2.1⟩
end YangMills.Construction.PeriodicLattice.ComplexGaugeCovarianceUnderIsometries
