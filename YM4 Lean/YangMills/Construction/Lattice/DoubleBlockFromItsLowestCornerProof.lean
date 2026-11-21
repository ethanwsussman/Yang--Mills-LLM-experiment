import YangMills.Construction.Lattice.DoubleBlockFromItsLowestCorner
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.DoubleBlockCorner
variable {L m : ℕ} {j : ℤ}
theorem offsetSite_offsetSite (z : Site L m j) (p t : Fin 4 → ℤ) :
    offsetSite (offsetSite z p) t = offsetSite z (p + t) := by
  simp only [offsetSite, Pi.add_apply, add_smul, Finset.sum_add_distrib, add_assoc]
theorem offsetSite_single (z : Site L m j) (ν : Fin 4) (a : ℤ) :
    offsetSite z (Pi.single ν a) = z + a • unitStep L m j ν := by
  unfold offsetSite
  congr 1
  rw [Finset.sum_eq_single ν]
  · simp
  · intro μ _ hμ
    simp [Pi.single_eq_of_ne hμ]
  · simp
theorem blockCorner_eq_schemeBaseSite (y : Site L m j) (j' : ℤ) :
    (blockCorner (j' := j') (L : ℤ) y : Site L m j') = schemeBaseSite .cornered j' y := by
  simp only [blockCorner, schemeBaseSite, centreToFaceSteps, offsetSite, neg_smul,
    Finset.sum_neg_distrib, Finset.smul_sum, sub_eq_add_neg]
theorem sitesIn_siteImage (P : Set (Site L m j)) : sitesIn (sitesAsTorusPoints P) = P := by
  ext x
  simp only [sitesIn, sitesAsTorusPoints, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]
  · exact fun hx => ⟨x, hx, rfl⟩
theorem sitesFromCorner_eq_image (z : Site L m j) (N : Fin 4 → ℤ) :
    sitesFromCorner z N = offsetSite z '' {t | ∀ μ, 0 ≤ t μ ∧ t μ < N μ} := by
  ext x
  simp only [sitesFromCorner, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
theorem mem_cornerQuadruples_iff (μ : Fin 4) (r : Fin 4 → ℤ) :
    r ∈ cornerQuadruples L μ ↔
      ∀ ν, 0 ≤ r ν ∧ r ν < doubledCounts (L : ℤ) μ ν := by
  have hb : ∀ ν, uniformCounts (L : ℤ) ν = (L : ℤ) := fun _ => rfl
  simp only [cornerQuadruples, mem_ofPred_eq, doubledCounts]
  constructor
  · rintro ⟨h0, h1, h2⟩ ν
    by_cases h : ν = μ
    · subst h
      simp only [Function.update_self]
      omega
    · simp only [Function.update_of_ne h, hb]
      have := h2 ν h
      omega
  · intro h
    refine ⟨(h μ).1, ?_, fun ν hν => ⟨(h ν).1, ?_⟩⟩
    · have := (h μ).2
      simp only [Function.update_self] at this
      omega
    · have := (h ν).2
      simp only [Function.update_of_ne hν, hb] at this
      omega
theorem eq_of_modEq_of_abs_sub_lt {M a b : ℤ} (h : a ≡ b [ZMOD M]) (hab : |a - b| < M) :
    a = b := by
  have hd : M ∣ a - b := (Int.modEq_iff_dvd.mp h.symm)
  have := Int.eq_zero_of_abs_lt_dvd hd hab
  omega
theorem eq_of_offsetSite_eq (z : Site L m j) {M B : ℤ}
    (hCong : ∀ p q : Fin 4 → ℤ, offsetSite z p = offsetSite z q ↔
      ∀ μ, p μ ≡ q μ [ZMOD M])
    (hB : B < M) {s t : Fin 4 → ℤ} (hd : ∀ ν, |s ν - t ν| ≤ B)
    (h : offsetSite z s = offsetSite z t) : s = t :=
  funext fun ν => eq_of_modEq_of_abs_sub_lt ((hCong s t).mp h ν) (lt_of_le_of_lt (hd ν) hB)
theorem offsetSite_add_single (z : Site L m j) (r : Fin 4 → ℤ) (ν : Fin 4) (a : ℤ) :
    offsetSite z (r + Pi.single ν a) = offsetSite z r + a • unitStep L m j ν := by
  rw [← offsetSite_offsetSite, offsetSite_single]
theorem abs_sub_add_single_le {B : ℤ} {r r' : Fin 4 → ℤ} (hd : ∀ ν, |r' ν - r ν| + 1 ≤ B)
    (ν : Fin 4) {a : ℤ} (ha : |a| ≤ 1) (κ : Fin 4) :
    |r' κ - (r + Pi.single ν a : Fin 4 → ℤ) κ| ≤ B := by
  have b3 : |(Pi.single ν a : Fin 4 → ℤ) κ| ≤ 1 := by
    by_cases h : κ = ν
    · subst h
      simpa using ha
    · simp [Pi.single_eq_of_ne h]
  have b1 := hd κ
  simp only [Pi.add_apply]
  rw [abs_le] at b3
  rw [abs_le]
  have := le_abs_self (r' κ - r κ)
  have := neg_abs_le (r' κ - r κ)
  omega
theorem exists_bond_iff_differByUnitVector (z : Site L m j) {M B : ℤ}
    (hCong : ∀ p q : Fin 4 → ℤ, offsetSite z p = offsetSite z q ↔
      ∀ μ, p μ ≡ q μ [ZMOD M])
    (hB : B < M) {r r' : Fin 4 → ℤ} (hd : ∀ ν, |r' ν - r ν| + 1 ≤ B) :
    (∃ b : Bond L m j, b.source = offsetSite z r ∧ b.target = offsetSite z r') ↔
      DifferByUnitVector r r' := by
  constructor
  · rintro ⟨b, ht, hh⟩
    obtain ⟨ν, h | h⟩ := b.isNeighbour
    · refine ⟨ν, Or.inl ?_⟩
      have hs : offsetSite z r' = offsetSite z (r + Pi.single ν 1) := by
        rw [offsetSite_add_single, one_smul, ← h, ← ht, ← hh]
        abel
      have := eq_of_offsetSite_eq z hCong hB (abs_sub_add_single_le hd ν (by simp)) hs
      rw [this]
      abel
    · refine ⟨ν, Or.inr ?_⟩
      have hs : offsetSite z r' = offsetSite z (r + Pi.single ν (-1)) := by
        rw [offsetSite_add_single, neg_smul, one_smul, ← neg_eq_iff_eq_neg.mpr h, ← ht, ← hh]
        abel
      have := eq_of_offsetSite_eq z hCong hB (abs_sub_add_single_le hd ν (by simp)) hs
      rw [this, Pi.single_neg]
      abel
  · rintro ⟨ν, h | h⟩
    · have hr'e : r' = r + Pi.single ν 1 := by rw [← h]; abel
      refine ⟨⟨offsetSite z r, offsetSite z r', ν, Or.inl ?_⟩, rfl, rfl⟩
      rw [hr'e, offsetSite_add_single, one_smul]
      abel
    · have hr'e : r' = r + Pi.single ν (-1) := by
        rw [Pi.single_neg, ← h]
        abel
      refine ⟨⟨offsetSite z r, offsetSite z r', ν, Or.inr ?_⟩, rfl, rfl⟩
      rw [hr'e, offsetSite_add_single, neg_smul, one_smul]
      abel
theorem bounds_of_mem_cornerQuadruples {μ : Fin 4} {r : Fin 4 → ℤ}
    (hr : r ∈ cornerQuadruples L μ) (ν : Fin 4) :
    0 ≤ r ν ∧ r ν ≤ 2 * (L : ℤ) - 1 := by
  obtain ⟨h0, h1, h2⟩ := (show 0 ≤ r μ ∧ r μ ≤ 2 * (L : ℤ) - 1 ∧
    ∀ ν, ν ≠ μ → 0 ≤ r ν ∧ r ν ≤ (L : ℤ) - 1 from hr)
  by_cases h : ν = μ
  · subst h
    exact ⟨h0, h1⟩
  · have := h2 ν h
    omega
theorem lowerHalf_eq (μ : Fin 4) :
    {t : Fin 4 → ℤ | ∀ ν, 0 ≤ t ν ∧ t ν < uniformCounts (L : ℤ) ν} =
      {r | r ∈ cornerQuadruples L μ ∧ r μ ≤ (L : ℤ) - 1} := by
  have hb : ∀ ν, uniformCounts (L : ℤ) ν = (L : ℤ) := fun _ => rfl
  ext r
  simp only [mem_ofPred_eq, hb, cornerQuadruples]
  constructor
  · intro h
    refine ⟨⟨(h μ).1, ?_, fun ν _ => ⟨(h ν).1, ?_⟩⟩, ?_⟩
    · have := (h μ).2
      omega
    · have := (h ν).2
      omega
    · have := (h μ).2
      omega
  · rintro ⟨⟨h0, -, h2⟩, h3⟩ ν
    by_cases h : ν = μ
    · subst h
      exact ⟨h0, by omega⟩
    · have := h2 ν h
      omega
theorem upperHalf_eq (o : Site L m j) (μ : Fin 4) :
    offsetSite (offsetSite o (Pi.single μ (L : ℤ))) ''
        {t : Fin 4 → ℤ | ∀ ν, 0 ≤ t ν ∧ t ν < uniformCounts (L : ℤ) ν} =
      offsetSite o '' {r | r ∈ cornerQuadruples L μ ∧ (L : ℤ) ≤ r μ} := by
  have hb : ∀ ν, uniformCounts (L : ℤ) ν = (L : ℤ) := fun _ => rfl
  ext x
  simp only [mem_image, mem_ofPred_eq, hb, cornerQuadruples]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Pi.single μ (L : ℤ) + t, ⟨⟨?_, ?_, fun ν hν => ?_⟩, ?_⟩,
      ?_⟩
    · have := ht μ
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    · have := ht μ
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    · have := ht ν
      simp only [Pi.add_apply, Pi.single_eq_of_ne hν]
      omega
    · have := ht μ
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    · exact (offsetSite_offsetSite o _ t).symm
  · rintro ⟨r, ⟨⟨h0, h1', h2⟩, h3⟩, rfl⟩
    refine ⟨r - Pi.single μ (L : ℤ), fun ν => ?_, by
      rw [offsetSite_offsetSite, add_sub_cancel]⟩
    by_cases h : ν = μ
    · subst h
      simp only [Pi.sub_apply, Pi.single_eq_same]
      omega
    · have := h2 ν h
      simp only [Pi.sub_apply, Pi.single_eq_of_ne h]
      omega
theorem cornerCoordinates_of_boxes {K n : ℕ} (c : BondAtLevel L m K (n + 1)) (μ : Fin 4) {M : ℤ}
    (hT : unitBlock c.source = sitesAsTorusPoints (sitesFromCorner
      (schemeBaseSite .cornered (levelDepth K n) c.source : SiteAtLevel L m K n)
        (uniformCounts (L : ℤ))))
    (hH : unitBlock c.target = sitesAsTorusPoints (sitesFromCorner
      (offsetSite (schemeBaseSite .cornered (levelDepth K n) c.source : SiteAtLevel L m K n)
        (Pi.single μ (L : ℤ))) (uniformCounts (L : ℤ))))
    (hD : bondDoubleBlock c = sitesAsTorusPoints (sitesFromCorner
      (schemeBaseSite .cornered (levelDepth K n) c.source : SiteAtLevel L m K n)
        (doubledCounts (L : ℤ) μ)))
    (hCong : ∀ p q : Fin 4 → ℤ,
      offsetSite (schemeBaseSite .cornered (levelDepth K n) c.source : SiteAtLevel L m K n) p =
        offsetSite (schemeBaseSite .cornered (levelDepth K n) c.source : SiteAtLevel L m K n) q ↔
      ∀ μ, p μ ≡ q μ [ZMOD M])
    (hB : 2 * (L : ℤ) < M) : DoubleBlockCornerCoordinates c μ := by
  have hDouble : (sitesIn (bondDoubleBlock c) : Set (SiteAtLevel L m K n)) =
      offsetSite (schemeBaseSite .cornered (levelDepth K n) c.source : SiteAtLevel L m K n) ''
        cornerQuadruples L μ := by
    rw [hD, sitesIn_siteImage, sitesFromCorner_eq_image]
    congr 1
    ext r
    exact (mem_cornerQuadruples_iff μ r).symm
  refine ⟨hDouble, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hDouble] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    refine ⟨r, ⟨hr, rfl⟩, fun r' hr' => ?_⟩
    refine eq_of_offsetSite_eq _ hCong hB (fun ν => ?_) hr'.2.symm
    have := bounds_of_mem_cornerQuadruples hr ν
    have := bounds_of_mem_cornerQuadruples hr'.1 ν
    rw [abs_le]
    omega
  · rw [hT, sitesIn_siteImage, sitesFromCorner_eq_image, lowerHalf_eq μ]
  · rw [hH, sitesIn_siteImage, sitesFromCorner_eq_image, upperHalf_eq]
  · intro r hr r' hr'
    refine exists_bond_iff_differByUnitVector _ hCong hB fun ν => ?_
    have b1 := bounds_of_mem_cornerQuadruples hr ν
    have b2 := bounds_of_mem_cornerQuadruples hr' ν
    have : |r' ν - r ν| ≤ 2 * (L : ℤ) - 1 := by
      rw [abs_le]
      omega
    omega
end YangMills.Construction.PeriodicLattice.DoubleBlockCorner
namespace YangMills.Construction.PeriodicLattice
open DoubleBlockCorner in
theorem doubleBlockFromLowestCorner_holds (hU : CoordinateDescription)
    (hB : CornerBoxProperties) : DoubleBlockFromLowestCorner := by
  intro L m K hL hm n hn c μ hc
  obtain ⟨hodd, h13⟩ := hL
  have hK : 0 < K := by omega
  have hLat := hU L m hodd h13 hm
  have hBox := hB L m K ⟨hodd, h13⟩ hm hK n hn.le
  have hbl : BlocksAreCornerBoxes L m K n (n + 1) := hBox.2 (n + 1) (by omega) hn
  have h1 : n + 1 - n = 1 := by omega
  obtain ⟨⟨hT, -⟩, hD, -⟩ := hbl c.source
  obtain ⟨⟨hH, -⟩, -, -⟩ := hbl c.target
  obtain ⟨hUn, -⟩ := hD μ
  rw [h1, pow_one] at hT hH hUn
  have hhead : (Bond.forwardFrom c.source μ).target = c.target := by
    show c.source + unitStep L m (levelDepth K (n + 1)) μ = c.target
    rw [← hc]
    abel
  have htail : (Bond.forwardFrom c.source μ).source = c.source := rfl
  rw [hhead, htail] at hUn
  rw [blockCorner_eq_schemeBaseSite] at hT hH hUn
  have hbase : schemeBaseSite .cornered (levelDepth K n) c.target =
      offsetSite (schemeBaseSite .cornered (levelDepth K n) c.source : SiteAtLevel L m K n)
        (Pi.single μ (L : ℤ)) := by
    have hinl := (hLat.2.1 K n hK hn.le).2.2.2.2 hn c μ hc
    rw [offsetSite_single]
    simp only [schemeBaseSite]
    rw [hinl]
    abel
  rw [hbase] at hH
  have he2 : 2 ≤ m + K - n := by omega
  have hLz : (13 : ℤ) ≤ (L : ℤ) := by exact_mod_cast h13
  have hpow : (L : ℤ) ^ 2 ≤ (L : ℤ) ^ (m + K - n) := pow_le_pow_right₀ (by omega) he2
  have hbig : 13 * (L : ℤ) ≤ (L : ℤ) ^ (m + K - n) := by nlinarith
  have hcount : halfPeriod L m (levelDepth K n) = L ^ (m + K - n) := by
    have : ((m : ℤ) + levelDepth K n).toNat = m + K - n := by
      simp only [levelDepth]
      omega
    rw [halfPeriod, this]
  have hj : -(m : ℤ) ≤ levelDepth K n := by
    simp only [levelDepth]
    omega
  have hCong := (hLat.1 (levelDepth K n) hj).2.2.2.2.1
    (schemeBaseSite .cornered (levelDepth K n) c.source : SiteAtLevel L m K n)
  have hB2 : 2 * (L : ℤ) < ((2 * halfPeriod L m (levelDepth K n) : ℕ) : ℤ) := by
    rw [hcount]
    push_cast
    omega
  have hN : ∀ ν, 1 ≤ doubledCounts (L : ℤ) μ ν ∧
      doubledCounts (L : ℤ) μ ν < (L : ℤ) ^ (m + K - n) := by
    intro ν
    by_cases h : ν = μ
    · subst h
      simp only [doubledCounts, Function.update_self]
      omega
    · have hb : uniformCounts (L : ℤ) ν = (L : ℤ) := rfl
      simp only [doubledCounts, Function.update_of_ne h, hb]
      omega
  obtain ⟨hbox, halong⟩ := hBox.1 _ (doubledCounts (L : ℤ) μ) hN
  have hUn' : bondDoubleBlock c = sitesAsTorusPoints (sitesFromCorner
      (schemeBaseSite .cornered (levelDepth K n) c.source : SiteAtLevel L m K n)
        (doubledCounts (L : ℤ) μ)) := hUn
  have hCorner : (sitesIn (bondDoubleBlock c) : Set (SiteAtLevel L m K n)) =
      sitesFromCorner (schemeBaseSite .cornered (levelDepth K n) c.source)
        (doubledCounts (L : ℤ) μ) := by
    rw [hUn', sitesIn_siteImage]
  refine ⟨cornerCoordinates_of_boxes c μ hT hH hUn' hCong hB2, ?_, ?_⟩
  · rw [hCorner]
    exact hbox
  · rw [hCorner]
    exact halong
end YangMills.Construction.PeriodicLattice
