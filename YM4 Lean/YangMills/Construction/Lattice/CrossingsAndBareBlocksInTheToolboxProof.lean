import YangMills.Construction.Lattice.BlocksBoxesAndPathsProof
import YangMills.Construction.Lattice.CombGaugeRoundACoarsePlaquetteProof
import YangMills.Construction.Lattice.CrossingsAndBareBlocksInTheToolbox
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CrossingsProof
variable {L m K : ℕ} {j : ℤ}
private theorem succ_smul_unitStep (x : Site L m j) (μ : Fin 4) (i : ℕ) :
    x + unitStep L m j μ + (i : ℤ) • unitStep L m j μ = x + ((i + 1 : ℕ) : ℤ) • unitStep L m j μ := by
  push_cast
  rw [add_zsmul, one_zsmul]
  abel
private theorem forwardFlow_add (x : Site L m j) (μ : Fin 4) (a b : ℕ) :
    forwardAxisPath x μ (a + b) =
      forwardAxisPath x μ a ++ forwardAxisPath (x + (a : ℤ) • unitStep L m j μ) μ b := by
  induction a generalizing x with
  | zero => simp [forwardAxisPath]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [forwardAxisPath, List.cons_append]
    rw [ih, succ_smul_unitStep]
private theorem mem_forwardFlow {x : Site L m j} {μ : Fin 4} {a : ℕ} {b : Bond L m j}
    (hb : b ∈ forwardAxisPath x μ a) :
    ∃ i : ℕ, i < a ∧ b = Bond.forwardFrom (x + (i : ℤ) • unitStep L m j μ) μ := by
  induction a generalizing x with
  | zero => simp [forwardAxisPath] at hb
  | succ a ih =>
    simp only [forwardAxisPath, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := ih hb
      exact ⟨i + 1, by omega, by rw [succ_smul_unitStep]⟩
private theorem nodup_forwardFlow (x : Site L m j) (μ : Fin 4) (a : ℕ)
    (h : ∀ i i' : ℕ, i < a → i' < a →
      x + (i : ℤ) • unitStep L m j μ = x + (i' : ℤ) • unitStep L m j μ → i = i') :
    (forwardAxisPath x μ a).Nodup := by
  induction a generalizing x with
  | zero => simp [forwardAxisPath]
  | succ a ih =>
    simp only [forwardAxisPath, List.nodup_cons]
    refine ⟨fun hmem => ?_, ih _ fun i i' hi hi' he => ?_⟩
    · obtain ⟨i, hi, hb⟩ := mem_forwardFlow hmem
      have ht : x = x + unitStep L m j μ + (i : ℤ) • unitStep L m j μ := congrArg Bond.source hb
      rw [succ_smul_unitStep] at ht
      have := h 0 (i + 1) (by omega) (by omega) (by simpa using ht)
      omega
    · rw [succ_smul_unitStep, succ_smul_unitStep] at he
      have := h (i + 1) (i' + 1) (by omega) (by omega) he
      omega
private theorem isBondPathFromTo_forwardFlow (x : Site L m j) (μ : Fin 4) (a : ℕ) :
    IsBondPathFromTo (forwardAxisPath x μ a) x (x + (a : ℤ) • unitStep L m j μ) := by apply _root_.YangMills.SharedProofs.p2140 <;> assumption
private theorem offsetSite_single (x : Site L m j) (ν : Fin 4) (n : ℤ) :
    offsetSite x (Pi.single ν n) = x + n • unitStep L m j ν := by apply _root_.YangMills.Construction.PeriodicLattice.DoubleBlockCorner.offsetSite_single <;> assumption
private theorem smul_unitStep_injective (hLat : SublatticeCoordinates L m j) {M : ℕ}
    (hM : (m : ℤ) + j = M) (x : Site L m j) (μ : Fin 4) {i i' : ℕ}
    (hi : (i : ℤ) < (L : ℤ) ^ M) (hi' : (i' : ℤ) < (L : ℤ) ^ M)
    (h : x + (i : ℤ) • unitStep L m j μ = x + (i' : ℤ) • unitStep L m j μ) : i = i' := by
  have he : offsetSite x (Pi.single μ (i : ℤ)) =
      offsetSite x (Pi.single μ (i' : ℤ)) := by
    rw [offsetSite_single, offsetSite_single, h]
  have hd := Int.modEq_iff_dvd.1 ((hLat.2.2.2.2.1 x _ _).1 he μ)
  have hcast : ((2 * halfPeriod L m j : ℕ) : ℤ) = 2 * (L : ℤ) ^ M := by
    simp [halfPeriod, hM]
  rw [hcast] at hd
  simp only [Pi.single_eq_same] at hd
  have hlt : |(i' : ℤ) - i| < 2 * (L : ℤ) ^ M := by
    rw [abs_lt]
    constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  omega
private theorem axialPath_eq_forwardFlow (hLat : SublatticeCoordinates L m j) {M : ℕ}
    (hM : (m : ℤ) + j = M) (x : Site L m j) (μ : Fin 4) (a : ℕ)
    (ha : (a : ℤ) < (L : ℤ) ^ M) :
    axialPath x (x + (a : ℤ) • unitStep L m j μ) = forwardAxisPath x μ a := by
  have hcast : ((2 * halfPeriod L m j : ℕ) : ℤ) = 2 * (L : ℤ) ^ M := by
    simp [halfPeriod, hM]
  have hdisp : IsAxialDisplacement x (x + (a : ℤ) • unitStep L m j μ) μ (a : ℤ) := by
    refine ⟨by simp, ?_⟩
    rw [hM, zpow_natCast, abs_of_nonneg (by omega)]
    exact_mod_cast ha
  have hex : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x (x + (a : ℤ) • unitStep L m j μ) q.1 q.2 :=
    ⟨(μ, (a : ℤ)), hdisp⟩
  unfold axialPath
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have key : (hex.choose.1 = μ ∧ hex.choose.2 = (a : ℤ)) ∨ (a = 0 ∧ hex.choose.2 = 0) := by
    generalize hex.choose = r at h1 h2
    obtain ⟨ν, n⟩ := r
    simp only at h1 h2 ⊢
    have he : offsetSite x (Pi.single ν n) =
        offsetSite x (Pi.single μ (a : ℤ)) := by
      rw [offsetSite_single, offsetSite_single, ← h1]
      abel
    have hc := (hLat.2.2.2.2.1 x _ _).1 he
    have hn : |n| < (L : ℤ) ^ M := by
      rw [hM, zpow_natCast] at h2
      exact_mod_cast h2
    have hn' := abs_lt.1 hn
    by_cases hνμ : ν = μ
    · subst hνμ
      left
      have hd := Int.modEq_iff_dvd.1 (hc ν)
      rw [hcast] at hd
      simp only [Pi.single_eq_same] at hd
      have hlt : |(a : ℤ) - n| < 2 * (L : ℤ) ^ M := by
        rw [abs_lt]
        constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd hd hlt
      exact ⟨rfl, by omega⟩
    · right
      have hd := Int.modEq_iff_dvd.1 (hc μ)
      have hd' := Int.modEq_iff_dvd.1 (hc ν)
      rw [hcast] at hd hd'
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hνμ),
        Pi.single_eq_of_ne hνμ] at hd hd'
      have hlt : |(a : ℤ) - 0| < 2 * (L : ℤ) ^ M := by
        rw [abs_lt]
        constructor <;> omega
      have hlt' : |(0 : ℤ) - n| < 2 * (L : ℤ) ^ M := by
        rw [abs_lt]
        constructor <;> omega
      have e1 := Int.eq_zero_of_abs_lt_dvd hd hlt
      have e2 := Int.eq_zero_of_abs_lt_dvd hd' hlt'
      exact ⟨by omega, by omega⟩
  rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · rw [k1, k2]
    unfold flowAlong
    rw [if_pos (by omega)]
    simp
  · rw [k2]
    subst k1
    simp [flowAlong, forwardAxisPath]
private theorem coordCount_sitesFromCorner_le (z : Site L m j) (N : Fin 4 → ℤ) (μ : Fin 4) (B : ℕ)
    (hN : N μ ≤ (B : ℤ)) : coordCount μ (sitesFromCorner z N) ≤ (B : ℕ∞) := by apply _root_.YangMills.Construction.PeriodicLattice.CoarsePlaquetteGauge.coordCount_sitesFromCorner_le <;> assumption
private theorem sitesIn_sitesAsTorusPoints (P : Set (Site L m j)) :
    (sitesIn (sitesAsTorusPoints P) : Set (Site L m j)) = P := by apply _root_.YangMills.Construction.PeriodicLattice.DoubleBlockCorner.sitesIn_siteImage <;> assumption
private theorem refinedBlock_congr {a b : ℤ} (h : a = b) (r : ℕ) (w : Site L m a)
    (w' : Site L m b) (hw : (w : FourTorus L m) = w') : refinedBlock r w = refinedBlock r w' := by
  subst h
  rw [Subtype.ext hw]
private theorem blockCard_and_prefixes (hP : BlockPaths.Statement)
    (hU : CoordinateDescription) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) : BlockCardAndCrossingPrefixes L m K := by
  intro n hn c hc
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨hy, hb⟩ := hP L m K hL.1 hL.2 hm n hn
  obtain ⟨⟨hco, hcard, -⟩, -, -⟩ := hy c.source
  obtain ⟨-, -, -, hSP, -⟩ := hb c μ hμ
  have hLat : SublatticeCoordinates L m (levelDepth K n) :=
    (hU L m hL.1 hL.2 hm).1 (levelDepth K n) (by simp only [levelDepth]; omega)
  have hM : (m : ℤ) + levelDepth K n = ((m + K - n : ℕ) : ℤ) := by
    simp only [levelDepth]
    omega
  have hLM : (L : ℤ) ≤ (L : ℤ) ^ (m + K - n) := by
    have hpos : (1 : ℤ) ≤ L := by have := hL.2; omega
    exact le_self_pow₀ hpos (by omega)
  refine ⟨?_, fun x hx => ?_⟩
  · have himg : Subtype.val '' (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)) =
        unitBlock c.source := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hp
        have hp' := hp
        rw [← hco.2] at hp'
        obtain ⟨q, -, rfl⟩ := hp'
        exact ⟨_, hp, rfl⟩
    rw [Nat.card_coe_set_eq, ← hcard, ← himg, ncard_image_of_injective _ Subtype.val_injective]
  · have hcr : crossingPath c x = forwardAxisPath x μ L := (hSP.1 x hx).2.1
    rw [hcr]
    refine ⟨nodup_forwardFlow x μ L fun i i' hi hi' he =>
      smul_unitStep_injective hLat hM x μ (by omega) (by omega) he, fun b hb' => ?_⟩
    obtain ⟨i, hi, rfl⟩ := mem_forwardFlow hb'
    obtain ⟨r, rfl⟩ : ∃ r, L = i + (r + 1) := ⟨L - i - 1, by omega⟩
    refine ⟨forwardAxisPath x μ i, forwardAxisPath (x + (i : ℤ) • unitStep _ m _ μ + unitStep _ m _ μ) μ r,
      ?_, ?_, ?_⟩
    · rw [forwardFlow_add]
      rfl
    · exact axialPath_eq_forwardFlow hLat hM x μ i (by omega)
    · exact isBondPathFromTo_forwardFlow x μ i
private theorem bareBlocks_siteBoxes (hC : CornerBoxProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) : BareBlocksAreSiteBoxes L m K := by
  intro k hk1 hkK
  obtain ⟨hbox, hcorner⟩ := hC L m K hL hm (by omega) 0 (Nat.zero_le _)
  have hBS := hcorner k (Nat.zero_le _) hkK
  have hLk : (1 : ℤ) ≤ (L : ℤ) ^ k := by
    have hpos : (1 : ℤ) ≤ L := by have := hL.2; omega
    exact one_le_pow₀ hpos
  refine ⟨fun y => ?_, fun c hc => ?_⟩
  · obtain ⟨hset, hcount⟩ := (hBS y).1
    have hP : blockSitesBelow 0 ({y} : Set (SiteAtLevel L m K k)) =
        sitesFromCorner (blockCorner (j' := levelDepth K 0) ((L : ℤ) ^ k) y)
          (uniformCounts ((L : ℤ) ^ k)) := by
      have : blockUnionAtLevel 0 ({y} : Set (SiteAtLevel L m K k)) = refinedBlock k y := by
        simp [refinedBlockUnion]
      rw [blockSitesBelow, this]
      erw [hset]
      exact sitesIn_sitesAsTorusPoints _
    rw [hP]
    refine ⟨(hbox _ _ fun μ => ⟨hLk, ?_⟩).1, fun μ => ?_⟩
    · have := hcount.1 μ
      have h2 := hcount.2
      simp only [Nat.sub_zero] at this h2 ⊢
      show (L : ℤ) ^ k < _
      omega
    · refine coordCount_sitesFromCorner_le _ _ μ _ ?_
      simp [uniformCounts]
  · obtain ⟨μ, hμ⟩ := hc
    obtain ⟨hset, hcount⟩ := (hBS c.source).2.1 μ
    have hh : (Bond.forwardFrom c.source μ).target = c.target := by
      show c.source + unitStep L m _ μ = c.target
      rw [← hμ]
      abel
    have ht : (Bond.forwardFrom c.source μ).source = c.source := rfl
    rw [hh, ht] at hset
    have hP : blockSitesBelow 0 (bondEnds c) =
        sitesFromCorner (blockCorner (j' := levelDepth K 0) ((L : ℤ) ^ k) c.source)
          (doubledCounts ((L : ℤ) ^ k) μ) := by
      have : blockUnionAtLevel 0 (bondEnds c) =
          refinedBlock k c.source ∪ refinedBlock k c.target := by
        simp [refinedBlockUnion, bondEnds]
      rw [blockSitesBelow, this]
      erw [hset]
      exact sitesIn_sitesAsTorusPoints _
    rw [hP]
    have hlow : ∀ ν, 1 ≤ doubledCounts ((L : ℤ) ^ k) μ ν := by
      intro ν
      by_cases h : ν = μ
      · subst h
        simp only [doubledCounts, Function.update_self]
        omega
      · simpa [doubledCounts, Function.update_of_ne h, uniformCounts] using hLk
    refine ⟨(hbox _ _ fun ν => ⟨hlow ν, ?_⟩).1, fun ν => ?_⟩
    · have := hcount.1 ν
      have h2 := hcount.2
      simp only [Nat.sub_zero] at this h2 ⊢
      omega
    · refine coordCount_sitesFromCorner_le _ _ ν _ ?_
      have := hcount.1 ν
      simp only [Nat.sub_zero] at this
      push_cast
      exact this
private theorem bareSite_uniqueSubblock (hB : BlocksBoxesPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) : BareSiteUniqueSubblock L m K := by
  intro j hj z x hx
  have hD : Averaging.OneStep.Parameters 4 2 L K m Matrices.ComplexMatrix2.specialUnitary :=
    ⟨rfl, rfl, rfl, hL.1, hL.2, by omega, hm⟩
  obtain ⟨-, -, hik, hbb, -, -, -⟩ := hB L K m hD
  have hmem : ∀ (k : ℕ) (y : SiteAtLevel L m K k) (w : SiteAtLevel L m K 0),
      w ∈ blockSitesBelow 0 ({y} : Set (SiteAtLevel L m K k)) ↔
        (w : FourTorus L m) ∈ refinedBlock k y := by
    intro k y w
    simp [blockSitesBelow, sitesIn, refinedBlockUnion]
  have hx' := (hmem _ z x).1 hx
  rw [(hbb (j + 1) j (j + 1) (by omega) le_rfl (by omega) z).1] at hx'
  simp only [mem_iUnion] at hx'
  obtain ⟨w, hw, hxw⟩ := hx'
  have e : levelDepth K (j + 1) + ((j + 1 - j : ℕ) : ℤ) = levelDepth K j := by
    rw [Nat.add_sub_cancel_left]
    show (K : ℤ) - ((j + 1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = (K : ℤ) - (j : ℤ)
    push_cast
    ring
  have hwl : (w : FourTorus L m) ∈ sublattice L m (levelDepth K j) := e ▸ w.2
  have hbl : refinedBlock j w = refinedBlock j (⟨w, hwl⟩ : SiteAtLevel L m K j) :=
    refinedBlock_congr e j w _ rfl
  have hw' : (w : FourTorus L m) ∈ unitBlock z := by
    have hbo : refinedBlock (j + 1 - j) z = unitBlock z := by rw [Nat.add_sub_cancel_left]
    have : (w : FourTorus L m) ∈ refinedBlock (j + 1 - j) z := hw
    rwa [hbo] at this
  rw [hbl] at hxw
  refine ⟨⟨w, hwl⟩, hw', (hmem _ _ x).2 hxw, fun z'' hz'' => ?_⟩
  exact (hik j j le_rfl (by omega)).2.2.1.1.elim_set (mem_univ _) (mem_univ _) x
    ((hmem _ z'' x).1 hz'') hxw
theorem crossingsAndBareBlocks_of_blockStructure (hB : BlocksBoxesPaths.Statement)
    (hP : BlockPaths.Statement) (hC : CornerBoxProperties) (hU : CoordinateDescription) :
    CrossingsAndBareBlocks.Statement :=
  fun _ hL _ _ hm => ⟨blockCard_and_prefixes hP hU hL hm, bareBlocks_siteBoxes hC hL hm,
    bareSite_uniqueSubblock hB hL hm⟩
end YangMills.Construction.PeriodicLattice.CrossingsProof
