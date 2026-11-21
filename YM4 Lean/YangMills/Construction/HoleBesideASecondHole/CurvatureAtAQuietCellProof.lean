import YangMills.Construction.HoleBesideASecondHole.CoercivityOfTheChain
import YangMills.Construction.HoleBesideASecondHole.CurvatureAtAQuietCell
import YangMills.Construction.HoleBesideASecondHole.LinesAndStripsOfALatticeField
import YangMills.Construction.HoleBesideASecondHole.MeansAtACoreBondProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.HoleSavings
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.BlockSites YangMills.Construction.LatticeGauge
namespace QuietCell
variable {F : BlockFrame}
theorem sum_sum_le_mul_of_multiplicity_le {α β : Type} [DecidableEq α] [DecidableEq β] (P : Finset β)
    (Q : β → Finset α) (R : Finset α)
    (w : α → ℝ) (hw : ∀ u ∈ R, 0 ≤ w u) (hQ : ∀ p ∈ P, Q p ⊆ R)
    (hc : ∀ u ∈ R, (P.filter fun p => u ∈ Q p).card ≤ 24) :
    ∑ p ∈ P, ∑ u ∈ Q p, w u ≤ 24 * ∑ u ∈ R, w u := by
  have h1 : ∀ p ∈ P, ∑ u ∈ Q p, w u = ∑ u ∈ R, if u ∈ Q p then w u else 0 := by
    intro p hp
    rw [← Finset.sum_filter]
    congr 1
    ext u
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hQ p hp h, h⟩, fun h => h.2⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun u hu => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h2 : (((P.filter fun p => u ∈ Q p).card : ℕ) : ℝ) ≤ 24 := by exact_mod_cast hc u hu
  exact mul_le_mul_of_nonneg_right h2 (hw u hu)
theorem card_plaquettes_with_corner_le {j : ℕ} (P : Finset (F.Site j × Fin 4 × Fin 4))
    (hP : ∀ p ∈ P, p.2.1 < p.2.2) (x : F.Site j) :
    (P.filter fun p => x ∈ plaquetteCorners p).card ≤ 24 := by
  classical
  let T : Finset ((Fin 4 × Fin 4) × Bool × Bool) :=
    (Finset.univ.filter fun m : Fin 4 × Fin 4 => m.1 < m.2) ×ˢ Finset.univ
  have hT : T.card = 24 := by decide
  let f : (Fin 4 × Fin 4) × Bool × Bool → F.Site j × Fin 4 × Fin 4 := fun u =>
    (x - (if u.2.1 then unitStep j u.1.1 else 0) - (if u.2.2 then unitStep j u.1.2 else 0), u.1.1, u.1.2)
  have hsub : (P.filter fun p => x ∈ plaquetteCorners p) ⊆ T.image f := by
    intro p hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_filter.mp hp
    obtain ⟨z, μ, ν⟩ := p
    have hlt : μ < ν := hP _ hp₁
    have hmem : ∀ b b' : Bool, z = x - (if b then unitStep j μ else 0) - (if b' then unitStep j ν else 0) →
        (z, μ, ν) ∈ T.image f := fun b b' he => Finset.mem_image.mpr
      ⟨((μ, ν), b, b'), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, Finset.mem_univ _⟩, by
        simp only [f]
        rw [← he]⟩
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hp₂
    rcases hp₂ with h | h | h | h
    · exact hmem false false (by simp [h])
    · exact hmem true false (by simp [h])
    · exact hmem false true (by simp [h])
    · exact hmem true true (by simp [h]; abel)
  calc _ ≤ (T.image f).card := Finset.card_le_card hsub
    _ ≤ T.card := Finset.card_image_le
    _ = 24 := hT
theorem eq_of_mem_sitesBelow_of_mem_sitesBelow (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (i : ℕ)
    (hi : i ≤ F.depth) {x x' : F.Site F.depth}
    {z : F.Site i} (h : z ∈ sitesBelow i x) (h' : z ∈ sitesBelow i x') : x = x' := by
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp h
  obtain ⟨o', ho', e⟩ := Finset.mem_image.mp h'
  have hM : Odd (F.blockSide ^ (F.depth - i)) := hodd.pow
  obtain ⟨k, hk⟩ := hM
  have hMz : ((F.blockSide ^ (F.depth - i) : ℕ) : ℤ) = 2 * k + 1 := by rw [hk]; push_cast; ring
  have hMz' : (F.blockSide : ℤ) ^ (F.depth - i) = 2 * k + 1 := by
    rw [← hMz]
    push_cast
    rfl
  have hh : (((F.blockSide ^ (F.depth - i) : ℕ) : ℤ) - 1) / 2 = k := by omega
  have hd := _root_.YangMills.Construction.BlockSites.siteOfCoords_eq_iff.mp e
  funext l
  have hl := hd l
  have hper : (F.period i l : ℤ) = (F.blockSide : ℤ) ^ (F.depth - i) * F.period F.depth l := by
    have : F.period i l = F.blockSide ^ (F.depth - i) * F.period F.depth l := by
      simp only [BlockFrame.period]
      have e1 : F.top - i = (F.depth - i) + (F.top - F.depth) := by
        simp only [BlockFrame.top]
        omega
      rw [e1, pow_add]
      ring
    rw [this]
    push_cast
    rfl
  have hi1 := Fintype.mem_piFinset.mp ho l
  have hi2 := Fintype.mem_piFinset.mp ho' l
  have hi3 := Finset.mem_Icc.mp hi1
  have hi4 := Finset.mem_Icc.mp hi2
  have hn : F.top - i = (F.depth - i) + 1 := by simp only [BlockFrame.top]; omega
  rw [hper, hMz'] at hl
  rw [hh] at hi3 hi4
  have h1 : ((2 * (k : ℤ) + 1)) ∣ o l - o' l := by
    have h2 : (2 * (k : ℤ) + 1) ∣ (2 * (k : ℤ) + 1) * siteCoords x l + o l -
        ((2 * (k : ℤ) + 1) * siteCoords x' l + o' l) :=
      (Dvd.intro _ rfl).trans hl
    have h3 : (2 * (k : ℤ) + 1) * siteCoords x l + o l - ((2 * (k : ℤ) + 1) * siteCoords x' l + o' l) =
        (2 * (k : ℤ) + 1) * (siteCoords x l - siteCoords x' l) + (o l - o' l) := by ring
    rw [h3] at h2
    exact (Int.dvd_add_right (Dvd.intro _ rfl)).mp h2
  have h4 : o l - o' l = 0 := Int.eq_zero_of_abs_lt_dvd h1 (by
    rw [abs_lt]
    constructor <;> omega)
  have h5 : (F.period F.depth l : ℤ) ∣ siteCoords x l - siteCoords x' l := by
    have h6 : (2 * (k : ℤ) + 1) * siteCoords x l + o l - ((2 * (k : ℤ) + 1) * siteCoords x' l + o' l) =
        (2 * (k : ℤ) + 1) * (siteCoords x l - siteCoords x' l) := by
      have : o l = o' l := by omega
      rw [this]
      ring
    rw [h6] at hl
    exact (mul_dvd_mul_iff_left (by omega)).mp hl
  have h7 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr h5
  rwa [intCast_siteCoords, intCast_siteCoords, eq_comm] at h7
theorem mem_sitesBelow_of_mem_sitesBelow (hodd : Odd F.blockSide) (i : ℕ) (hi : i ≤ F.depth)
    {x : F.Site F.depth} {z : F.Site i} {v : F.Cell}
    (hz : z ∈ sitesBelow i x) (hx : x ∈ sitesBelow F.depth v) : z ∈ sitesBelow i v := by
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨p, hp, hxe⟩ := mem_sitesBelow_iff.mp hx
  obtain ⟨k, hk⟩ := (hodd.pow : Odd (F.blockSide ^ (F.depth - i)))
  obtain ⟨m, hm⟩ := hodd
  have hn : F.top - i = (F.depth - i) + 1 := by simp only [BlockFrame.top]; omega
  have hMz : ((F.blockSide ^ (F.depth - i) : ℕ) : ℤ) = 2 * k + 1 := by rw [hk]; push_cast; ring
  have hLz : (F.blockSide : ℤ) = 2 * m + 1 := by rw [hm]; push_cast; ring
  have hpow : (F.blockSide : ℤ) ^ (F.depth - i) = 2 * k + 1 := by
    rw [← hMz]
    push_cast
    rfl
  have hh : (((F.blockSide ^ (F.depth - i) : ℕ) : ℤ) - 1) / 2 = k := by omega
  have hper : ∀ l, (F.period i l : ℤ) = (F.blockSide : ℤ) ^ (F.depth - i) * F.period F.depth l := by
    intro l
    have : F.period i l = F.blockSide ^ (F.depth - i) * F.period F.depth l := by
      simp only [BlockFrame.period]
      have e1 : F.top - i = (F.depth - i) + (F.top - F.depth) := by
        simp only [BlockFrame.top]
        omega
      rw [e1, pow_add]
      ring
    rw [this]
    push_cast
    rfl
  refine Finset.mem_image.mpr ⟨fun l => (F.blockSide : ℤ) ^ (F.depth - i) * p l + o l,
    Fintype.mem_piFinset.mpr fun l => ?_, ?_⟩
  · have h1 := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp ho l)
    have h2 := hp l
    have hM2 : (((F.blockSide ^ (F.top - i) : ℕ) : ℤ) - 1) / 2 = (2 * (k : ℤ) + 1) * m + k := by
      have : ((F.blockSide ^ (F.top - i) : ℕ) : ℤ) = (2 * (k : ℤ) + 1) * (2 * m + 1) := by
        rw [hn, pow_succ]
        push_cast
        rw [← hLz]
        have := hpow
        rw [this]
      rw [this]
      have : (2 * (k : ℤ) + 1) * (2 * m + 1) - 1 = 2 * ((2 * (k : ℤ) + 1) * m + k) := by ring
      rw [this]
      omega
    have hhm : ((F.blockSide : ℤ) - 1) / 2 = m := by omega
    rw [hhm, abs_le] at h2
    rw [hh] at h1
    rw [hM2, hpow]
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩ <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  · refine _root_.YangMills.Construction.BlockSites.siteOfCoords_eq_iff.mpr fun l => ?_
    have h1 := _root_.YangMills.Construction.BlockSites.siteOfCoords_eq_iff.mp ((_root_.YangMills.Construction.BlockSites.siteOfCoords_siteCoords x).trans hxe) l
    rw [hper l]
    have e : (F.blockSide : ℤ) ^ (F.depth - i) * siteCoords x l + o l -
        ((F.blockSide : ℤ) ^ (F.top - i) * siteCoords v l + ((F.blockSide : ℤ) ^ (F.depth - i) * p l + o l)) =
        -((F.blockSide : ℤ) ^ (F.depth - i) * ((F.blockSide : ℤ) * siteCoords v l + p l - siteCoords x l)) := by
      rw [hn, pow_succ]
      ring
    rw [e]
    exact (dvd_neg).mpr (mul_dvd_mul_left _ h1)
theorem quaternion_re_le_norm (q : ℍ[ℝ]) : q.re ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.quaternion_re_le_norm <;> assumption
theorem plaquetteEnergy_nonneg {U : F.GaugeField 0} (p : F.Site 0 × Fin 4 × Fin 4) :
    0 ≤ plaquetteEnergy U p := by apply _root_.YangMills.Construction.LumpContours.CutAction.plaquetteEnergy_nonneg <;> assumption
theorem sub_re_mul_unit_nonneg {q : ℍ[ℝ]} (g : UnitQuaternion) : 0 ≤ ‖q‖ - (q * (g : ℍ[ℝ])).re := by
  have h := quaternion_re_le_norm (q * (g : ℍ[ℝ]))
  rw [norm_mul, _root_.YangMills.Construction.LatticeGauge.norm_coe_unitQuaternion, mul_one] at h
  linarith
theorem blockFit_nonneg {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    0 ≤ blockFit X X' c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
theorem contourFit_nonneg (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth)
    (W : F.GaugeField F.depth) (V : F.GaugeField F.top) (c : F.Cell × Fin 4) : 0 ≤ contourFit J₀ h b W V c :=
  sub_re_mul_unit_nonneg _
theorem card_plaquettes_over_site_le (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (P : Finset (F.Site F.depth × Fin 4 × Fin 4))
    (hP : ∀ p ∈ P, p.2.1 < p.2.2) (i : ℕ) (hi : i ≤ F.depth) (z : F.Site i) :
    (P.filter fun p => z ∈ cutBelow i (plaquetteCorners p)).card ≤ 24 := by
  classical
  by_cases hne : (P.filter fun p => z ∈ cutBelow i (plaquetteCorners p)).Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    obtain ⟨x₀, -, hz₀⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hp₀).2
    refine (Finset.card_le_card ?_).trans (card_plaquettes_with_corner_le P hP x₀)
    intro p hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_filter.mp hp
    obtain ⟨x, hx, hz⟩ := Finset.mem_biUnion.mp h₂
    rw [eq_of_mem_sitesBelow_of_mem_sitesBelow hodd hs i hi hz hz₀] at hx
    exact Finset.mem_filter.mpr ⟨h₁, hx⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp
theorem fst_mem_of_mem_cutPlaquettes {j : ℕ} {X : Finset (F.Site j)} {p : F.Site j × Fin 4 × Fin 4}
    (h : p ∈ cutPlaquettes X) : p.1 ∈ X := (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1
theorem fst_mem_of_mem_cutBonds {j : ℕ} {X : Finset (F.Site j)} {c : F.Site j × Fin 4} (h : c ∈ cutBonds X) :
    c.1 ∈ X := (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1
theorem cutBelow_subset_cutBelow {i j : ℕ} {X Y : Finset (F.Site j)} (h : X ⊆ Y) :
    cutBelow i X ⊆ cutBelow i Y :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h
theorem mem_cutPlaquettes_of_subset {j : ℕ} {X Y : Finset (F.Site j)} (h : X ⊆ Y) {p : F.Site j × Fin 4 × Fin 4}
    (hp : p ∈ cutPlaquettes X) : p ∈ cutPlaquettes Y := by apply _root_.YangMills.Construction.CoreBondMeans.cutPlaquettes_mono <;> assumption
theorem mem_cutBonds_of_subset {j : ℕ} {X Y : Finset (F.Site j)} (h : X ⊆ Y) {c : F.Site j × Fin 4}
    (hc : c ∈ cutBonds X) : c ∈ cutBonds Y := by apply _root_.YangMills.Construction.CoreBondMeans.cutBonds_mono <;> assumption
theorem sum_cutChainEnergy_le {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀)
    (hodd : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (ha : 0 ≤ a) (B₁ B₃ : Finset F.Cell) (hB : B₁ ⊆ B₃)
    (P : Finset (F.Site F.depth × Fin 4 × Fin 4))
    (hP : ∀ p ∈ P, p.2.1 < p.2.2 ∧ plaquetteCorners p ⊆ D.chainSites ∩ cutBelow F.depth B₁) :
    ∑ p ∈ P, cutChainEnergy a F.depth (plaquetteCorners p) D.chain ≤ 24 * D.energyOver B₃ := by
  classical
  have hlow : ∀ p ∈ P, plaquetteCorners p ⊆ D.chainSites := fun p hp x hx =>
    (Finset.mem_inter.mp ((hP p hp).2 hx)).1
  have hblk : ∀ (i : ℕ), i ≤ F.depth → ∀ p ∈ P, ∀ z ∈ cutBelow i (plaquetteCorners p), z ∈ cutBelow i B₃ := by
    intro i hi p hp z hz
    obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp ((hP p hp).2 hx)).2
    exact Finset.mem_biUnion.mpr ⟨v, hB hv, mem_sitesBelow_of_mem_sitesBelow hodd i hi hzx hxv⟩
  have hPord : ∀ p ∈ P, p.2.1 < p.2.2 := fun p hp => (hP p hp).1
  set R₀ := (cutPlaquettes (cutBelow 0 D.chainSites)).filter
    fun q => ∃ x ∈ plaquetteCorners q, x ∈ cutBelow 0 B₃ with hR₀
  have h₀ := sum_sum_le_mul_of_multiplicity_le P (fun p => cutPlaquettes (cutBelow 0 (plaquetteCorners p))) R₀
    (plaquetteEnergy (D.chain 0))
    (fun u _ => plaquetteEnergy_nonneg u)
    (fun p hp q hq => Finset.mem_filter.mpr ⟨mem_cutPlaquettes_of_subset (cutBelow_subset_cutBelow (hlow p hp)) hq,
      q.1, by simp [plaquetteCorners], hblk 0 (Nat.zero_le _) p hp _ (fst_mem_of_mem_cutPlaquettes hq)⟩)
    (fun u _ => (Finset.card_le_card (fun p hp => by
      obtain ⟨h₁, h₂⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨h₁, fst_mem_of_mem_cutPlaquettes h₂⟩)).trans
      (card_plaquettes_over_site_le hodd hs P hPord 0 (Nat.zero_le _) u.1))
  have h₁ : ∀ i ∈ Finset.range F.depth, ∑ p ∈ P, ∑ c ∈ cutBonds (cutBelow (i + 1) (plaquetteCorners p)),
      blockFit (D.chain i) (D.chain (i + 1)) c ≤
      24 * ∑ c ∈ cutBonds (cutBelow (i + 1) D.chainSites),
        (if c.1 ∈ cutBelow (i + 1) B₃ ∨ c.1 + unitStep (i + 1) c.2 ∈ cutBelow (i + 1) B₃
          then blockFit (D.chain i) (D.chain (i + 1)) c else 0) := by
    intro i hi
    have hi' : i + 1 ≤ F.depth := Finset.mem_range.mp hi
    rw [← Finset.sum_filter]
    exact sum_sum_le_mul_of_multiplicity_le P _ _ (blockFit (D.chain i) (D.chain (i + 1)))
      (fun u _ => blockFit_nonneg _ _ u)
      (fun p hp c hc => Finset.mem_filter.mpr ⟨mem_cutBonds_of_subset (cutBelow_subset_cutBelow (hlow p hp)) hc,
        Or.inl (hblk (i + 1) hi' p hp _ (fst_mem_of_mem_cutBonds hc))⟩)
      (fun u _ => (Finset.card_le_card (fun p hp => by
        obtain ⟨h₁, h₂⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨h₁, fst_mem_of_mem_cutBonds h₂⟩)).trans
        (card_plaquettes_over_site_le hodd hs P hPord (i + 1) hi' u.1))
  have htop : 0 ≤ a * ∑ c ∈ cutBonds D.cells,
      (if c.1 ∈ B₃ ∨ c.1 + unitStep F.top c.2 ∈ B₃ then D.topBondFit c else 0) :=
    mul_nonneg ha (Finset.sum_nonneg fun c _ => by
      split_ifs
      · exact contourFit_nonneg _ _ _ _ _ _
      · exact le_rfl)
  have e₀ : ∑ p ∈ cutPlaquettes (cutBelow 0 D.chainSites),
      (if ∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 B₃ then plaquetteEnergy (D.chain 0) p else 0) =
      ∑ q ∈ R₀, plaquetteEnergy (D.chain 0) q := by
    rw [hR₀, Finset.sum_filter]
  have e₁ : ∑ p ∈ P, cutChainEnergy a F.depth (plaquetteCorners p) D.chain =
      ∑ p ∈ P, ∑ q ∈ cutPlaquettes (cutBelow 0 (plaquetteCorners p)), plaquetteEnergy (D.chain 0) q +
      a * ∑ i ∈ Finset.range F.depth, ∑ p ∈ P, ∑ c ∈ cutBonds (cutBelow (i + 1) (plaquetteCorners p)),
        blockFit (D.chain i) (D.chain (i + 1)) c := by
    simp only [cutChainEnergy, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [e₁, HoleData.energyOver, e₀]
  have h₂ := Finset.sum_le_sum h₁
  have h₃ : a * ∑ i ∈ Finset.range F.depth, ∑ p ∈ P, ∑ c ∈ cutBonds (cutBelow (i + 1) (plaquetteCorners p)),
      blockFit (D.chain i) (D.chain (i + 1)) c ≤
      a * ∑ i ∈ Finset.range F.depth, 24 * ∑ c ∈ cutBonds (cutBelow (i + 1) D.chainSites),
        (if c.1 ∈ cutBelow (i + 1) B₃ ∨ c.1 + unitStep (i + 1) c.2 ∈ cutBelow (i + 1) B₃
          then blockFit (D.chain i) (D.chain (i + 1)) c else 0) := mul_le_mul_of_nonneg_left h₂ ha
  rw [← Finset.mul_sum] at h₃
  linarith
end QuietCell
open QuietCell in
theorem quietCellCurvature (hco : ChainCoercivity) : quietCellCurvatureStatement := by
  classical
  obtain ⟨cK, hcK, -, L₀, hco⟩ := hco
  refine ⟨24 / cK, by positivity, L₀, fun a C s θ J₀ L g F D ha hC hs hodd hL₀ hFL hcub hsmall y hy hsp => ?_⟩
  subst hFL
  have hside : ∀ i, 0 < F.extent i := fun i => by
    have h1 := hcub.1 i
    have h2 := hcub.2
    omega
  have amb : IsAdmissibleAmbient F := Or.inr fun i => by
    have h1 := hcub.1 i
    have h2 := hcub.2
    omega
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hE : D.energyOver (cellBall y 3) < C * s ^ 2 := by
    by_contra hge
    exact hsp (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy, not_lt.mp hge⟩))
  have hB : cellBall y 1 ⊆ cellBall y 3 := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := mem_cellBall_iff.mp hv
    refine mem_cellBall_iff.mpr ⟨c, fun i => ?_, rfl⟩
    have := hc i
    push_cast at this ⊢
    linarith
  set P := cutPlaquettes (D.chainSites ∩ cutBelow F.depth (cellBall y 1)) with hPdef
  have hP : ∀ p ∈ P, p.2.1 < p.2.2 ∧ plaquetteCorners p ⊆ D.chainSites ∩ cutBelow F.depth (cellBall y 1) :=
    fun p hp => (Finset.mem_filter.mp hp).2
  have hcoer := fun p =>
    (hco a F.blockSide ha hodd hL₀ F rfl amb F.depth (by simp [BlockFrame.top])).1 p D.chain
  have hle : ∀ p ∈ P, plaquetteDefect D.fineField p ^ 2 ≤
      cutChainEnergy a F.depth (plaquetteCorners p) D.chain / cK := by
    intro p hp
    have h1 := hcoer p (hP p hp).1
    rw [D.chain_top] at h1
    have h2 := sum_cutChainEnergy_le D hodd hside ha0 _ _ hB {p} (fun q hq => by
      rw [Finset.mem_singleton.mp hq]
      exact hP p hp)
    rw [Finset.sum_singleton] at h2
    have h3 : min (plaquetteDefect D.fineField p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) <
        (F.blockSide : ℝ) ^ (-4 : ℤ) := by
      have h4 : min (plaquetteDefect D.fineField p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) * cK <
          24 * (C * s ^ 2) := by linarith
      have h5 : min (plaquetteDefect D.fineField p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) < 24 / cK * C * s ^ 2 := by
        rw [show 24 / cK * C * s ^ 2 = (24 * (C * s ^ 2)) / cK by ring]
        exact (lt_div_iff₀ hcK).mpr h4
      linarith
    have h6 : min (plaquetteDefect D.fineField p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) =
        plaquetteDefect D.fineField p ^ 2 := by
      rcases min_choice (plaquetteDefect D.fineField p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) with h | h
      · exact h
      · rw [h] at h3
        exact absurd h3 (lt_irrefl _)
    rw [h6] at h1
    rw [le_div_iff₀ hcK]
    linarith
  have hsum := sum_cutChainEnergy_le D hodd hside ha0 _ _ hB P hP
  calc ∑ p ∈ P, plaquetteDefect D.fineField p ^ 2 ≤
        ∑ p ∈ P, cutChainEnergy a F.depth (plaquetteCorners p) D.chain / cK := Finset.sum_le_sum hle
    _ = (∑ p ∈ P, cutChainEnergy a F.depth (plaquetteCorners p) D.chain) / cK := by rw [Finset.sum_div]
    _ ≤ (24 * D.energyOver (cellBall y 3)) / cK := by gcongr
    _ ≤ (24 * (C * s ^ 2)) / cK := by gcongr
    _ = 24 / cK * C * s ^ 2 := by ring
end YangMills.Construction.HoleSavings
end
