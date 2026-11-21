import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroupProof
import YangMills.Construction.Lattice.AverageOfTheLiftOfOrder
import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Lattice.LiftOfOrderIsAConfiguration
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace OrderLiftAverage
variable {L m K : ℕ}
private theorem unitBlock_eq_blockAtLevel {j : ℕ} (y : SiteAtLevel L m K (j + 1)) :
    unitBlock y = blockAtLevel j y := by
  show refinedBlock 1 y = refinedBlock (j + 1 - j) y
  rw [Nat.add_sub_cancel_left]
private theorem twoBlockFieldValues_one {j j' : ℤ} (c : Bond L m j) (b : Bond L m j') :
    twoBlockFieldValues j' c 1 b = 1 := by
  unfold twoBlockFieldValues
  split_ifs <;> simp
private theorem one_mem_complexGaugeGroup : (1 : Matrices.ComplexMatrix2) ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.ComplexMeanMembership.one_mem_gaugeGroup <;> assumption
end OrderLiftAverage
open OrderLiftAverage in
theorem orderLiftAverageStep_holds
    (hCases : OrderLiftCases)
    (hField : OrderLiftIsGaugeField)
    (hCentres : CoarseCentreProperties)
    (hDouble : DoubleBlockStructure.Statement)
    (hPair : TwoBlockFieldMeanProperties) :
    OrderLiftAverageStep := by
  intro L m K hL hm j k hjk hkK 𝒞 hrev V hV
  have hK : 0 < K := by omega
  have hjK : j < K := by omega
  have hjk' : j + 1 ≤ k := hjk
  obtain ⟨-, hUniq, hNotOver, hTwo⟩ := (hCases L m K hL hm hK).1 j k hjk.le hkK
  obtain ⟨-, hUniq₁, hNotOver₁, hTwo₁⟩ := (hCases L m K hL hm hK).1 (j + 1) k hjk' hkK
  obtain ⟨-, ⟨-, -, hGauge, -⟩, -⟩ := hField L m K hL hm hK j k hjk.le hkK 𝒞 hrev V hV
  obtain ⟨-, ⟨-, -, hGauge₁, hReal₁⟩, -⟩ := hField L m K hL hm hK (j + 1) k hjk' hkK 𝒞 hrev V hV
  have hNest : ∀ (y : SiteAtLevel L m K k) (s : SiteAtLevel L m K (j + 1)),
      (s : FourTorus L m) ∈ blockAtLevel (j + 1) y → unitBlock s ⊆ blockAtLevel j y := by
    intro y s hs
    obtain ⟨-, hblock, -, -, -, -⟩ := hCentres L m K hL hm hK (j + 1) k hjk' hkK
    obtain ⟨-, -, -, hcomp, -, -⟩ := hCentres L m K hL hm hK j k hjk.le hkK
    rw [(hblock y).1] at hs
    obtain ⟨x, hx, hxy⟩ := hs
    obtain rfl : x = s := Subtype.ext hx
    have hsub := (hcomp (j + 1) (Nat.le_succ j) hjk').2 x
    rw [hxy] at hsub
    rw [unitBlock_eq_blockAtLevel]
    exact hsub
  have hAll : ∀ c₁ : BondAtLevel L m K (j + 1),
      IsInsideSomeBlock k c₁ ∨ ∃ c : BondAtLevel L m K k, CoversBond c c₁ := by
    intro c₁
    have hu := ((hField L m K hL hm hK (j + 1) k hjk' hkK univ (fun _ _ => mem_univ _)
      (fun _ => 1) ⟨fun _ _ => one_mem_complexGaugeGroup, fun _ _ => by simp⟩).2.2 rfl).1
    have hc : c₁ ∈ bondsInsideOrOverCoarse (j + 1) (univ : Set (BondAtLevel L m K k)) := by
      rw [hu]; exact mem_univ c₁
    rcases hc with h | ⟨c, -, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, h⟩
  have hOverValues : ∀ (𝒞' : Set (BondAtLevel L m K k)) (V' : BondAtLevel L m K k → Matrices.ComplexMatrix2),
      IsReversalClosed 𝒞' → IsGaugeField complexGaugeGroup 𝒞' V' →
      ∀ (c₁ : BondAtLevel L m K (j + 1)), ∀ c ∈ 𝒞', CoversBond c c₁ →
        (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j)) ⊆ bondsInsideOrOverCoarse j 𝒞' ∧
        ∀ b ∈ (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j)),
          orderLift j V' b = twoBlockFieldValues (levelDepth K j) c₁ (V' c) b := by
    intro 𝒞' V' hrev' hV' c₁ c hc hover
    have hS := hNest c.source c₁.source hover.1
    have hT := hNest c.target c₁.target hover.2
    have hdisj := (hDouble L m K j hL hm hjK c₁).1.1
    have hne : ∀ z : FourTorus L m, z ∈ unitBlock c₁.source → z ∈ unitBlock c₁.target → False := by
      intro z h1 h2
      have hz : z ∈ unitBlock c₁.source ∩ unitBlock c₁.target := ⟨h1, h2⟩
      rw [hdisj] at hz
      exact hz
    have hv := hTwo 𝒞' V' hrev' hV'
    have hcls : ∀ b ∈ (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j)),
        b ∈ bondsInsideOrOverCoarse j 𝒞' ∧
          orderLift j V' b = twoBlockFieldValues (levelDepth K j) c₁ (V' c) b := by
      intro b hb
      obtain ⟨hs, ht⟩ := hb
      rcases hs with hs | hs <;> rcases ht with ht | ht
      · have hin : IsInsideSomeBlock k b := ⟨c.source, hS hs, hS ht⟩
        have hmem : b ∈ bondsInsideOrOverCoarse j 𝒞' := Or.inl hin
        obtain ⟨-, -, -, h1, -, -⟩ := hv b hmem
        refine ⟨hmem, ?_⟩
        have hp : b ∈ (bondsInside (unitBlock c₁.source) : Set (BondAtLevel L m K j)) ∨
            b ∈ (bondsInside (unitBlock c₁.target) : Set (BondAtLevel L m K j)) := Or.inl ⟨hs, ht⟩
        rw [h1 hin]
        unfold twoBlockFieldValues
        rw [if_pos hp]
      · have hover' : CoversBond c b := ⟨hS hs, hT ht⟩
        have hmem : b ∈ bondsInsideOrOverCoarse j 𝒞' := Or.inr ⟨c, hc, hover'⟩
        obtain ⟨-, -, -, -, h2, -⟩ := hv b hmem
        refine ⟨hmem, ?_⟩
        have hn : ¬(b ∈ (bondsInside (unitBlock c₁.source) : Set (BondAtLevel L m K j)) ∨
            b ∈ (bondsInside (unitBlock c₁.target) : Set (BondAtLevel L m K j))) := by
          rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact hne _ h ht
          · exact hne _ hs h
        have hp : b ∈ (bondCorridor c₁ : Set (BondAtLevel L m K j)) := ⟨hs, ht⟩
        rw [h2 c hc hover']
        unfold twoBlockFieldValues
        rw [if_neg hn, if_pos hp]
      · have hover' : CoversBond c.opposite b := ⟨hT hs, hS ht⟩
        have hmem : b ∈ bondsInsideOrOverCoarse j 𝒞' := Or.inr ⟨c.opposite, hrev' c hc, hover'⟩
        obtain ⟨-, -, -, -, h2, -⟩ := hv b hmem
        refine ⟨hmem, ?_⟩
        have hn : ¬(b ∈ (bondsInside (unitBlock c₁.source) : Set (BondAtLevel L m K j)) ∨
            b ∈ (bondsInside (unitBlock c₁.target) : Set (BondAtLevel L m K j))) := by
          rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact hne _ h hs
          · exact hne _ ht h
        have hn' : b ∉ (bondCorridor c₁ : Set (BondAtLevel L m K j)) := fun h => hne _ h.1 hs
        have hp : b.opposite ∈ (bondCorridor c₁ : Set (BondAtLevel L m K j)) := ⟨ht, hs⟩
        rw [h2 c.opposite (hrev' c hc) hover', hV'.2 c hc]
        unfold twoBlockFieldValues
        rw [if_neg hn, if_neg hn', if_pos hp]
      · have hin : IsInsideSomeBlock k b := ⟨c.target, hT hs, hT ht⟩
        have hmem : b ∈ bondsInsideOrOverCoarse j 𝒞' := Or.inl hin
        obtain ⟨-, -, -, h1, -, -⟩ := hv b hmem
        refine ⟨hmem, ?_⟩
        have hp : b ∈ (bondsInside (unitBlock c₁.source) : Set (BondAtLevel L m K j)) ∨
            b ∈ (bondsInside (unitBlock c₁.target) : Set (BondAtLevel L m K j)) := Or.inr ⟨hs, ht⟩
        rw [h1 hin]
        unfold twoBlockFieldValues
        rw [if_pos hp]
    exact ⟨fun b hb => (hcls b hb).1, fun b hb => (hcls b hb).2⟩
  have hInsideValues : ∀ (c₁ : BondAtLevel L m K (j + 1)) (y : SiteAtLevel L m K k),
      IsInsideBlockAt (j + 1) y c₁ →
        (∀ b ∈ (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j)), IsInsideBlockAt j y b) ∧
        (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j)) ⊆ bondsInsideOrOverCoarse j 𝒞 ∧
        ∀ b ∈ (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j)),
          orderLift j V b = twoBlockFieldValues (levelDepth K j) c₁ 1 b := by
    intro c₁ y hy
    have hS := hNest y c₁.source hy.1
    have hT := hNest y c₁.target hy.2
    have hin : ∀ b ∈ (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j)), IsInsideBlockAt j y b := by
      intro b hb
      obtain ⟨hs, ht⟩ := hb
      refine ⟨?_, ?_⟩
      · rcases hs with hs | hs
        · exact hS hs
        · exact hT hs
      · rcases ht with ht | ht
        · exact hS ht
        · exact hT ht
    have hsub : (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j)) ⊆ bondsInsideOrOverCoarse j 𝒞 :=
      fun b hb => Or.inl ⟨y, hin b hb⟩
    refine ⟨hin, hsub, fun b hb => ?_⟩
    obtain ⟨-, -, -, h1, -, -⟩ := hTwo 𝒞 V hrev hV b (hsub hb)
    rw [h1 ⟨y, hin b hb⟩, twoBlockFieldValues_one]
  have hMissing : ∀ (c₁ : BondAtLevel L m K (j + 1)) (c : BondAtLevel L m K k), c ∉ 𝒞 →
      CoversBond c c₁ →
        c₁ ∉ bondsInsideOrOverCoarse (j + 1) 𝒞 ∧
        (bondCorridor c₁ : Set (BondAtLevel L m K j)).Nonempty ∧
        (∀ b ∈ (bondCorridor c₁ : Set (BondAtLevel L m K j)), b ∉ bondsInsideOrOverCoarse j 𝒞) ∧
        ¬(bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j)) ⊆ bondsInsideOrOverCoarse j 𝒞 := by
    intro c₁ c hc hover
    have hS := hNest c.source c₁.source hover.1
    have hT := hNest c.target c₁.target hover.2
    have hnon : (bondCorridor c₁ : Set (BondAtLevel L m K j)).Nonempty :=
      (hDouble L m K j hL hm hjK c₁).2.2.1.2
    have hcor : ∀ b ∈ (bondCorridor c₁ : Set (BondAtLevel L m K j)), b ∉ bondsInsideOrOverCoarse j 𝒞 := by
      intro b hb
      have hob : CoversBond c b := ⟨hS hb.1, hT hb.2⟩
      rintro (hin | ⟨c', hc', ho'⟩)
      · exact hNotOver b hin c hob
      · exact hc (hUniq b c' c ho' hob ▸ hc')
    refine ⟨?_, hnon, hcor, ?_⟩
    · rintro (hin | ⟨c', hc', ho'⟩)
      · exact hNotOver₁ c₁ hin c hover
      · exact hc (hUniq₁ c₁ c' c ho' hover ▸ hc')
    · intro hsub
      obtain ⟨b, hb⟩ := hnon
      exact hcor b hb (hsub ⟨Or.inl hb.1, Or.inr hb.2⟩)
  have hStep : ∀ c₁ ∈ bondsInsideOrOverCoarse (j + 1) 𝒞,
      (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j)) ⊆ bondsInsideOrOverCoarse j 𝒞 ∧
      ∀ b ∈ (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j)),
        orderLift j V b = twoBlockFieldValues (levelDepth K j) c₁ (orderLift (j + 1) V c₁) b := by
    intro c₁ hmem
    obtain ⟨-, -, -, h1, h2, -⟩ := hTwo₁ 𝒞 V hrev hV c₁ hmem
    rcases hmem with ⟨y, hy⟩ | ⟨c, hc, ho⟩
    · rw [h1 ⟨y, hy⟩]
      exact (hInsideValues c₁ y hy).2
    · rw [h2 c hc ho]
      exact hOverValues 𝒞 V hrev hV c₁ c hc ho
  have hExt : ∀ c₁ ∈ bondsInsideOrOverCoarse (j + 1) 𝒞,
      onSetElseOne (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j)) (orderLift j V) =
        onSetElseOne (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j))
          (twoBlockFieldValues (levelDepth K j) c₁ (orderLift (j + 1) V c₁)) := by
    intro c₁ hc
    funext b
    by_cases hb : b ∈ (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j))
    · simp only [onSetElseOne, if_pos hb]
      exact (hStep c₁ hc).2 b hb
    · simp only [onSetElseOne, if_neg hb]
  have hBack : ∀ c₁ : BondAtLevel L m K (j + 1),
      (bondsInDoubleBlock c₁ : Set (BondAtLevel L m K j)) ⊆ bondsInsideOrOverCoarse j 𝒞 →
      c₁ ∈ bondsInsideOrOverCoarse (j + 1) 𝒞 := by
    intro c₁ hsub
    rcases hAll c₁ with hin | ⟨c, ho⟩
    · exact Or.inl hin
    · by_cases hc : c ∈ 𝒞
      · exact Or.inr ⟨c, hc, ho⟩
      · exact absurd hsub (hMissing c₁ c hc ho).2.2.2
  refine ⟨hGauge, fun c₁ => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rcases hAll c₁ with hin | ⟨c, ho⟩
    · exact Or.inl ⟨hin, fun ⟨c, _, ho⟩ => hNotOver₁ c₁ hin c ho,
        fun ⟨c, _, ho⟩ => hNotOver₁ c₁ hin c ho⟩
    · have hni : ¬IsInsideSomeBlock k c₁ := fun hin => hNotOver₁ c₁ hin c ho
      by_cases hc : c ∈ 𝒞
      · refine Or.inr (Or.inl ⟨hni, ⟨c, hc, ho⟩, ?_⟩)
        rintro ⟨c', hc', ho'⟩
        exact hc' (hUniq₁ c₁ c c' ho ho' ▸ hc)
      · refine Or.inr (Or.inr ⟨hni, ?_, ⟨c, hc, ho⟩⟩)
        rintro ⟨c', hc', ho'⟩
        exact hc (hUniq₁ c₁ c' c ho' ho ▸ hc')
  · intro y hy
    obtain ⟨h1, h2, h3⟩ := hInsideValues c₁ y hy
    exact ⟨Or.inl ⟨y, hy⟩, h1, h2, h3⟩
  · intro c hc ho
    have hS := hNest c.source c₁.source ho.1
    have hT := hNest c.target c₁.target ho.2
    obtain ⟨hsub, hval⟩ := hOverValues 𝒞 V hrev hV c₁ c hc ho
    refine ⟨Or.inr ⟨c, hc, ho⟩, fun b hb => ⟨hS hb.1, hS hb.2⟩, fun b hb => ⟨hT hb.1, hT hb.2⟩,
      fun b hb => ⟨⟨hS hb.1, hT hb.2⟩, ⟨hT hb.2, hS hb.1⟩⟩, hsub, hval, ?_⟩
    intro 𝒞' V' hrev' hV' hc' hVc _ b hb
    rw [(hOverValues 𝒞' V' hrev' hV' c₁ c hc' ho).2 b hb, hval b hb, hVc]
  · exact fun c hc ho => hMissing c₁ c hc ho
  · refine ⟨?_, fun c₁ hc => ?_⟩
    · ext c₁
      constructor
      · rintro ⟨hsub, -⟩
        exact hBack c₁ hsub
      · intro hc
        have hTB := hPair L hL m K j hm hjK c₁ _ (hGauge₁.1 c₁ hc)
        refine ⟨(hStep c₁ hc).1, ?_⟩
        show onSetElseOne _ (orderLift j V) ∈ _
        rw [hExt c₁ hc]
        exact hTB.2.2.2.2.1.1
    · have hTB := hPair L hL m K j hm hjK c₁ _ (hGauge₁.1 c₁ hc)
      show complexBlockAverage (onSetElseOne _ (orderLift j V)) c₁ = _
      rw [hExt c₁ hc]
      exact hTB.2.2.2.2.1.2.2
  · intro hVr
    refine ⟨?_, fun c₁ hc => ?_⟩
    · ext c₁
      exact ⟨fun hsub => hBack c₁ hsub, fun hc => (hStep c₁ hc).1⟩
    · have hTB := hPair L hL m K j hm hjK c₁ _ (hGauge₁.1 c₁ hc)
      have hR := hTB.2.2.2.2.2 ((hReal₁ hVr).1 c₁ hc)
      refine ⟨?_, ?_⟩
      · show blockAverage _ (onSetElseOne _ (orderLift j V)) c₁ = _
        rw [hExt c₁ hc]
        exact hR.2.2.2
      · show blockAverageCase _ (onSetElseOne _ (orderLift j V)) c₁.positivelyOriented = _
        rw [hExt c₁ hc]
        exact hR.2.1
end YangMills.Construction.PeriodicLattice
