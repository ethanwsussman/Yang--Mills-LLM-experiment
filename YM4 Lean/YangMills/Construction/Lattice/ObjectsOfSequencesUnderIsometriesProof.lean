import YangMills.Construction.Lattice.CovarianceOfMinimalOrbitsUnderIsometriesProof
import YangMills.Construction.Lattice.SitesBondsAndPlaquettesOfSetsUnderIsometriesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace ChainObjectsUnderIsometry
variable {L m : ℕ} {j : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
theorem eq_image_of_forall_mem_iff {α : Type*} {f : α → α} (hf : Function.Surjective f)
    {A B : Set α} (h : ∀ b, f b ∈ A ↔ b ∈ B) : A = f '' B := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCells.eq_image_of_surjective_of_mem_iff <;> assumption
theorem coe_source_bondImage (hσ : PreservesCells σ j) (b : Bond L m j) :
    ((bondImage σ b).source : FourTorus L m) = σ b.source := by apply _root_.YangMills.Construction.PeriodicLattice.MinimalOrbitsUnderIsometries.coe_source_bondImage <;> assumption
theorem coe_target_bondImage (hσ : PreservesCells σ j) (b : Bond L m j) :
    ((bondImage σ b).target : FourTorus L m) = σ b.target := by apply _root_.YangMills.Construction.PeriodicLattice.MinimalOrbitsUnderIsometries.coe_target_bondImage <;> assumption
theorem siteImage_mem_sitesIn_iff (hσ : PreservesCells σ j) {X Y : Set (FourTorus L m)}
    (hXY : ∀ x, σ x ∈ Y ↔ x ∈ X) (y : Site L m j) :
    siteImage σ y ∈ (sitesIn Y : Set (Site L m j)) ↔ y ∈ (sitesIn X : Set (Site L m j)) := by
  change ((siteImage σ y : Site L m j) : FourTorus L m) ∈ Y ↔ (y : FourTorus L m) ∈ X
  rw [hσ.1 y]
  exact hXY y
theorem bondImage_mem_bondsMeeting_iff (hσ : PreservesCells σ j) {X Y : Set (FourTorus L m)}
    (hXY : ∀ x, σ x ∈ Y ↔ x ∈ X) (b : Bond L m j) :
    bondImage σ b ∈ (bondsMeeting Y : Set (Bond L m j)) ↔
      b ∈ (bondsMeeting X : Set (Bond L m j)) := by
  change ((bondImage σ b).source : FourTorus L m) ∈ Y ∨
      ((bondImage σ b).target : FourTorus L m) ∈ Y ↔
    (b.source : FourTorus L m) ∈ X ∨ (b.target : FourTorus L m) ∈ X
  rw [coe_source_bondImage hσ, coe_target_bondImage hσ, hXY, hXY]
theorem bondImage_mem_bondsInside_iff (hσ : PreservesCells σ j) {X Y : Set (FourTorus L m)}
    (hXY : ∀ x, σ x ∈ Y ↔ x ∈ X) (b : Bond L m j) :
    bondImage σ b ∈ (bondsInside Y : Set (Bond L m j)) ↔
      b ∈ (bondsInside X : Set (Bond L m j)) := by
  change ((bondImage σ b).source : FourTorus L m) ∈ Y ∧
      ((bondImage σ b).target : FourTorus L m) ∈ Y ↔
    (b.source : FourTorus L m) ∈ X ∧ (b.target : FourTorus L m) ∈ X
  rw [coe_source_bondImage hσ, coe_target_bondImage hσ, hXY, hXY]
section Chains
variable {K k : ℕ} {Ω Ω' : ℕ → Set (FourTorus L m)}
theorem apply_mem_iff (hΩ : ∀ q ≤ k, Ω' q = σ '' Ω q) {q : ℕ} (hq : q ≤ k) (x : FourTorus L m) :
    σ x ∈ Ω' q ↔ x ∈ Ω q := by
  rw [hΩ q hq]
  exact σ.injective.mem_set_image
theorem siteImage_mem_annulusSites_iff (H : ∀ q ≤ k, PreservesCells σ (levelDepth K q))
    (hΩ : ∀ q ≤ k, Ω' q = σ '' Ω q) {q : ℕ} (hq : q ≤ k) (y : SiteAtLevel L m K q) :
    siteImage σ y ∈ annulusSites K k Ω' q ↔ y ∈ annulusSites K k Ω q := by
  unfold annulusSites
  split_ifs with hlt
  · refine siteImage_mem_sitesIn_iff (H q hq) (fun x => ?_) y
    rw [mem_sdiff, mem_sdiff, apply_mem_iff hΩ hq, apply_mem_iff hΩ (Nat.succ_le_of_lt hlt)]
  · exact siteImage_mem_sitesIn_iff (H q hq) (apply_mem_iff hΩ le_rfl) y
theorem bondImage_mem_determiningBondsAt_iff (H : ∀ q ≤ k, PreservesCells σ (levelDepth K q))
    (hΩ : ∀ q ≤ k, Ω' q = σ '' Ω q) {q : ℕ} (hq : q ≤ k) (b : BondAtLevel L m K q) :
    bondImage σ b ∈ determiningBondsAt K k Ω' q ↔ b ∈ determiningBondsAt K k Ω q := by
  have hends := (H q hq).2.2.2.1 b
  change ((bondImage σ b).source ∈ annulusSites K k Ω' q ∨
      (bondImage σ b).target ∈ annulusSites K k Ω' q) ∧
      bondImage σ b ∈ (bondsInside (Ω' 0) : Set (BondAtLevel L m K q)) ↔
    (b.source ∈ annulusSites K k Ω q ∨ b.target ∈ annulusSites K k Ω q) ∧
      b ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K q))
  rw [hends.1, hends.2, siteImage_mem_annulusSites_iff H hΩ hq,
    siteImage_mem_annulusSites_iff H hΩ hq,
    bondImage_mem_bondsInside_iff (H q hq) (apply_mem_iff hΩ (Nat.zero_le k))]
theorem mem_determiningBondSet_iff (H : ∀ q ≤ k, PreservesCells σ (levelDepth K q))
    (hΩ : ∀ q ≤ k, Ω' q = σ '' Ω q) (q : ℕ) (b : BondAtLevel L m K q) :
    (⟨q, bondImage σ b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ determiningBondSet K k Ω' ↔
      (⟨q, b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ determiningBondSet K k Ω :=
  and_congr_right fun hq => bondImage_mem_determiningBondsAt_iff H hΩ hq b
theorem mem_inwardPointingBonds_iff (H : ∀ q ≤ k, PreservesCells σ (levelDepth K q))
    (hΩ : ∀ q ≤ k, Ω' q = σ '' Ω q) (q : ℕ) (b : BondAtLevel L m K q) :
    (⟨q, bondImage σ b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ inwardPointingBonds K k Ω' ↔
      (⟨q, b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ inwardPointingBonds K k Ω :=
  and_congr_right fun hlt =>
    and_congr (bondImage_mem_determiningBondsAt_iff H hΩ hlt.le b)
      (bondImage_mem_bondsMeeting_iff (H q hlt.le) (apply_mem_iff hΩ (Nat.succ_le_of_lt hlt)) b)
theorem mk_bondImage_mem_bondSetImage_iff (H : ∀ q ≤ k, PreservesCells σ (levelDepth K q))
    {q : ℕ} (hq : q ≤ k) (B : Set (Σ j : ℕ, BondAtLevel L m K j)) (b : BondAtLevel L m K q) :
    (⟨q, bondImage σ b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ bondSetImage σ B ↔
      (⟨q, b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ B := by
  constructor
  · rintro ⟨⟨q', c⟩, hc, he⟩
    obtain ⟨rfl, he'⟩ := Sigma.mk.inj_iff.1 he
    rwa [← (H q' hq).2.2.1.1 (eq_of_heq he')]
  · exact fun hb => ⟨⟨q, b⟩, hb, rfl⟩
theorem eq_bondSetImage (H : ∀ q ≤ k, PreservesCells σ (levelDepth K q))
    {A B : Set (Σ j : ℕ, BondAtLevel L m K j)} (hA : ∀ q ∈ A, q.1 ≤ k)
    (h : ∀ (q : ℕ) (b : BondAtLevel L m K q),
      (⟨q, bondImage σ b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ A ↔
        (⟨q, b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ B) :
    A = bondSetImage σ B := by
  ext ⟨q, c⟩
  constructor
  · intro hc
    obtain ⟨b, rfl⟩ := (H q (hA _ hc)).2.2.1.2 c
    exact ⟨⟨q, b⟩, (h q b).1 hc, rfl⟩
  · rintro ⟨⟨q', b⟩, hb, he⟩
    obtain ⟨rfl, he'⟩ := Sigma.mk.inj_iff.1 he
    rw [← eq_of_heq he']
    exact (h q' b).2 hb
theorem isEndpointOf_bondSetImage_iff (H : ∀ q ≤ k, PreservesCells σ (levelDepth K q))
    {B : Set (Σ j : ℕ, BondAtLevel L m K j)} (hB : ∀ q ∈ B, q.1 ≤ k) (x : FourTorus L m) :
    IsEndpointOf (bondSetImage σ B) (σ x) ↔ IsEndpointOf B x := by
  constructor
  · rintro ⟨_, ⟨⟨q, b⟩, hb, rfl⟩, hx⟩
    refine ⟨⟨q, b⟩, hb, ?_⟩
    have hq := H q (hB _ hb)
    rcases hx with hx | hx
    · exact Or.inl (σ.injective ((coe_source_bondImage hq b).symm.trans hx))
    · exact Or.inr (σ.injective ((coe_target_bondImage hq b).symm.trans hx))
  · rintro ⟨⟨q, b⟩, hb, hx⟩
    refine ⟨_, ⟨⟨q, b⟩, hb, rfl⟩, ?_⟩
    have hq := H q (hB _ hb)
    rcases hx with hx | hx
    · exact Or.inl ((coe_source_bondImage hq b).trans (congrArg σ hx))
    · exact Or.inr ((coe_target_bondImage hq b).trans (congrArg σ hx))
theorem localScale_image (hΩ : ∀ q ≤ k, Ω' q = σ '' Ω q) (C : Set (FourTorus L m)) :
    localScale L k Ω' (σ '' C) = localScale L k Ω C := by
  have hs : {q | q ≤ k ∧ (σ '' C ∩ Ω' q).Nonempty} = {q | q ≤ k ∧ (C ∩ Ω q).Nonempty} := by
    ext q
    refine and_congr_right fun hq => ?_
    rw [hΩ q hq, ← image_inter σ.injective, image_nonempty]
  unfold localScale
  rw [hs]
end Chains
end ChainObjectsUnderIsometry
open ChainObjectsUnderIsometry in
theorem isometryPreservesChainObjects_holds (hS : IsometriesPreserveCells) :
    IsometryPreservesChainObjects := by
  intro L m i σ hL hm hi hσ K k Ω Ω' hdepth hΩ
  have H : ∀ q ≤ k, PreservesCells σ (levelDepth K q) :=
    fun q hq => hS L m i _ σ hL hm hi hσ (hdepth q hq)
  have H0 := H 0 (Nat.zero_le k)
  have hdet : ∀ q ∈ determiningBondSet K k Ω, q.1 ≤ k := fun q hq => hq.1
  have hactive : ∀ q ∈ activeBondSet K k Ω, q.1 ≤ k := fun q hq => hq.1.1
  have hset : determiningBondSet K k Ω' = bondSetImage σ (determiningBondSet K k Ω) :=
    eq_bondSetImage H (fun q hq => hq.1) (mem_determiningBondSet_iff H hΩ)
  have himage : activeBondSet K k Ω' = bondSetImage σ (activeBondSet K k Ω) :=
    eq_bondSetImage H (fun q hq => hq.1.1) fun q b =>
      and_congr (mem_determiningBondSet_iff H hΩ q b)
        (not_congr (mem_inwardPointingBonds_iff H hΩ q b))
  refine ⟨hset, ?_, ?_, ?_, ?_, ?_, ?_, himage, ?_, ?_, ?_⟩
  · exact fun q hq => eq_image_of_forall_mem_iff (H q hq).2.2.1.2
      (bondImage_mem_determiningBondsAt_iff H hΩ hq)
  · exact fun q hq => eq_image_of_forall_mem_iff (H q hq).2.1.2
      (siteImage_mem_annulusSites_iff H hΩ hq)
  · intro x
    have hn := isEndpointOf_bondSetImage_iff H hdet x
    rw [← hset] at hn
    exact and_congr (apply_mem_iff hΩ (Nat.zero_le k) x) hn
  · intro b
    rw [coe_source_bondImage H0, coe_target_bondImage H0, ← image_pair, localScale_image hΩ]
  · intro p
    rw [H0.2.2.2.2.2.1 p, localScale_image hΩ]
  · exact eq_bondSetImage H (fun q hq => hq.1.le) (mem_inwardPointingBonds_iff H hΩ)
  · exact fun q hq => eq_image_of_forall_mem_iff (H q hq).2.2.1.2 fun b =>
      and_congr (bondImage_mem_determiningBondsAt_iff H hΩ hq b)
        (not_congr (mem_inwardPointingBonds_iff H hΩ q b))
  · intro x
    rw [himage]
    exact isEndpointOf_bondSetImage_iff H hactive x
  · intro F hF
    have hdiff : determiningBondSetDiff K k Ω' (bondSetImage σ F) =
        bondSetImage σ (determiningBondSetDiff K k Ω F) := by
      refine eq_bondSetImage H (fun q hq => hq.1.1) fun q b => ?_
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(mem_determiningBondSet_iff H hΩ q b).1 h₁,
          fun h => h₂ ((mk_bondImage_mem_bondSetImage_iff H h₁.1 F b).2 h)⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨(mem_determiningBondSet_iff H hΩ q b).2 h₁,
          fun h => h₂ ((mk_bondImage_mem_bondSetImage_iff H h₁.1 F b).1 h)⟩
    refine ⟨⟨?_, ?_⟩, hdiff, ?_, ?_⟩
    · rintro _ ⟨⟨q, b⟩, hb, rfl⟩
      exact (mem_inwardPointingBonds_iff H hΩ q b).2 (hF.1 hb)
    · rintro _ ⟨⟨q, b⟩, hb, rfl⟩
      have hr : bondImage σ b.opposite = (bondImage σ b).opposite :=
        (H q (hF.1 hb).1.le).2.2.2.2.1 b
      exact ⟨⟨q, b.opposite⟩, hF.2 _ hb, congrArg (Sigma.mk q) hr⟩
    · exact fun q hq => eq_image_of_forall_mem_iff (H q hq).2.2.1.2 fun b =>
        and_congr (bondImage_mem_determiningBondsAt_iff H hΩ hq b)
          (not_congr (mk_bondImage_mem_bondSetImage_iff H hq F b))
    · intro x
      rw [hdiff]
      exact isEndpointOf_bondSetImage_iff H (fun q hq => hq.1.1) x
end YangMills.Construction.PeriodicLattice
