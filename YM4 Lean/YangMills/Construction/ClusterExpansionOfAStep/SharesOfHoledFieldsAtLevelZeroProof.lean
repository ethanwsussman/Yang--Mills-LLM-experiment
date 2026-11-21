import YangMills.Construction.ClusterExpansionOfAStep.SetsEqualInBoxes
import YangMills.Construction.ClusterExpansionOfAStep.SharesOfHoledFieldsAtLevelZero
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open scoped Quaternion
open BlockAverages LumpContours TorusFields TorusLumps StepCosts
namespace HoledShares
theorem natAbs_le_of_abs_le {a : ℤ} {m : ℕ} (h : |a| ≤ (m : ℤ)) : a.natAbs ≤ m := by apply _root_.YangMills.Construction.CongruentBoxes.natAbs_le_of_abs_le_natCast <;> assumption
theorem abs_le_of_natAbs_le {a : ℤ} {m : ℕ} (h : a.natAbs ≤ m) : |a| ≤ (m : ℤ) := by apply _root_.YangMills.Construction.CongruentBoxes.abs_le_natCast_of_natAbs_le <;> assumption
variable {ℓ : StepParameters} {n n' : ℕ} [NeZero n] [NeZero n']
theorem holonomy_eq_of_fieldsAgreeNear {U : TorusField n} {U' : TorusField n'} {x : TorusSite n}
    {x' : TorusSite n'} {m : ℕ}
    (hagree : FieldsAgreeNear U U' x x' m) (b : Fin 4 → ℤ) (μ ν : Fin 4)
    (h : ∀ d ∈ plaquetteOffsets μ ν, OffsetInBox m (b + d)) :
    holonomy U (x + siteOfInt b) μ ν = holonomy U' (x' + siteOfInt b) μ ν := by
  have d0 := h 0 (by simp [plaquetteOffsets])
  have d1 := h (Pi.single μ 1) (by simp [plaquetteOffsets])
  have d2 := h (Pi.single ν 1) (by simp [plaquetteOffsets])
  have d3 := h (Pi.single μ 1 + Pi.single ν 1) (by simp [plaquetteOffsets])
  rw [add_zero] at d0
  have hlink : ∀ (c : Fin 4 → ℤ) (i : Fin 4), OffsetInBox m c → OffsetInBox m (c + Pi.single i 1) →
      U (x + siteOfInt c) i = U' (x' + siteOfInt c) i := fun c i h1 h2 => hagree (c, i) ⟨h1, h2⟩
  have a3 : b + (Pi.single μ 1 + Pi.single ν 1) = (b + Pi.single μ 1) + Pi.single ν 1 := by
    rw [add_assoc]
  have a4 : b + (Pi.single μ 1 + Pi.single ν 1) = (b + Pi.single ν 1) + Pi.single μ 1 := by
    rw [add_assoc, add_comm (Pi.single μ 1)]
  have e1 := hlink b μ d0 d1
  have e2 := hlink (b + Pi.single μ 1) ν d1 (a3 ▸ d3)
  have e3 := hlink (b + Pi.single ν 1) μ d2 (a4 ▸ d3)
  have e4 := hlink b ν d0 d2
  unfold holonomy
  simp only [unitStep_eq_siteOfInt]
  rw [add_siteOfInt_add, add_siteOfInt_add] at e2 e3
  rw [e1, e2, e3, e4]
theorem mem_thickening_of_fieldsAgreeNear (hadm : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (hLn' : ℓ.side ∣ n') {U : TorusField n} {U' : TorusField n'}
    {x : TorusSite n} {x' : TorusSite n'} {m : ℕ} (hm : 2 ^ 16 ≤ m) (hn : 2 * m + 2 < n)
    (hagree : FieldsAgreeNear U U' x x' m) (hblock : SameBlockPosition ℓ x x') (h : Fin 4 → ℤ)
    (hbox : OffsetInBox (m - 2 ^ 16) h)
    (hz : x + siteOfInt h ∈ thickening lumpRange (torusHotSites ℓ U)) :
    x' + siteOfInt h ∈ thickening lumpRange (torusHotSites ℓ U') := by
  classical
  obtain ⟨u, hu, hd⟩ := (Finset.mem_filter.mp hz).2
  obtain ⟨e, he, heb⟩ := exists_offset_of_supDist (x + siteOfInt h) u
  obtain ⟨l, hl, hul⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨w, μ, ν, hlt, hhot, z, hzc, rfl⟩ := (mem_torusHotLumps_iff ℓ hadm hLn U l).mp hl
  have hcorner : lumpCorner ℓ u = lumpCorner ℓ z := (Finset.mem_filter.mp hul).2
  have hclose := supDist_lt_of_lumpCorner_eq hadm hLn hcorner.symm
  obtain ⟨e₁, he₁, he₁b⟩ := exists_offset_of_supDist u z
  obtain ⟨d, hdm, hzd⟩ := (mem_plaquetteVertices_iff_offset w z μ ν).mp hzc
  have hew : ∀ i, |e i| ≤ (lumpRange : ℤ) := fun i => abs_le_of_natAbs_le ((heb i).trans hd)
  have he₁w : ∀ i, |e₁ i| ≤ 2 ^ 15 := fun i => by
    have h1 := he₁b i
    have h2 : (e₁ i).natAbs ≤ 2 ^ 15 := by omega
    exact_mod_cast abs_le_of_natAbs_le h2
  set a : Fin 4 → ℤ := h + e with ha
  have hua : u = x + siteOfInt a := by rw [he, add_assoc, ← siteOfInt_add]
  have hza : z = x + siteOfInt (a + e₁) := by
    rw [add_siteOfInt_add, ← hua]
    exact he₁
  set b : Fin 4 → ℤ := a + e₁ - d with hbd
  have hwb : w = x + siteOfInt b := by
    have h1 : x + siteOfInt b + siteOfInt d = w + siteOfInt d := by
      rw [← add_siteOfInt_add, hbd, sub_add_cancel, ← hza, hzd]
    exact (add_right_cancel h1).symm
  have hmz : ((m - 2 ^ 16 : ℕ) : ℤ) + 2 ^ 16 = m := by
    have : m - 2 ^ 16 + 2 ^ 16 = m := Nat.sub_add_cancel hm
    exact_mod_cast this
  have hin : ∀ d' ∈ plaquetteOffsets μ ν, OffsetInBox m (b + d') := by
    intro d' hd' i
    have h1 := hbox i
    have h2 := hew i
    have h3 := he₁w i
    have h4 := abs_le_two_of_mem_plaquetteOffsets hdm i
    have h5 := abs_le_two_of_mem_plaquetteOffsets hd' i
    simp only [hbd, ha, Pi.add_apply, Pi.sub_apply]
    rw [abs_le] at h1 h2 h3 h4 h5 ⊢
    norm_num [lumpRange] at h2
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]
  have hhol := holonomy_eq_of_fieldsAgreeNear hagree b μ ν hin
  have hhot' : ℓ.threshold ≤ curvature U' (x' + siteOfInt b) μ ν := by
    have : curvature U' (x' + siteOfInt b) μ ν = curvature U w μ ν := by
      unfold curvature
      rw [hwb, hhol]
    rw [this]
    exact hhot
  have hzc' : x' + siteOfInt (a + e₁) ∈ plaquetteVertices (x' + siteOfInt b) μ ν := by
    refine (mem_plaquetteVertices_iff_offset _ _ μ ν).mpr ⟨d, hdm, ?_⟩
    rw [← add_siteOfInt_add, hbd, sub_add_cancel]
  have hl' : torusLumpOf ℓ (x' + siteOfInt (a + e₁)) ∈ torusHotLumps ℓ U' :=
    (mem_torusHotLumps_iff ℓ hadm hLn' U' _).mpr ⟨_, μ, ν, hlt, hhot', _, hzc', rfl⟩
  have hbig : 2 ^ 17 < n := by omega
  have hk : lumpCorner ℓ (x + siteOfInt a) = lumpCorner ℓ (x + siteOfInt (a + e₁)) := by
    rw [← hua, ← hza]
    exact hcorner
  have hk' := lumpCorner_eq_of_sameBlockPosition hadm hLn hLn' hbig hblock a e₁ he₁w hk
  have hu' : x' + siteOfInt a ∈ torusHotSites ℓ U' :=
    Finset.mem_biUnion.mpr ⟨_, hl', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, hu', ?_⟩
  have : x' + siteOfInt a = x' + siteOfInt h + siteOfInt e := by rw [ha, add_siteOfInt_add]
  rw [this]
  exact supDist_add_siteOfInt_le _ _ _ fun i => natAbs_le_of_abs_le (hew i)
@[irreducible] def nearbyPlaquetteOffsets : Finset ((Fin 4 → ℤ) × Fin 4 × Fin 4) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-2 : ℤ) 2) ×ˢ Finset.univ
def offsetPlaquette (x : TorusSite n) (q : (Fin 4 → ℤ) × Fin 4 × Fin 4) : TorusPlaquette n :=
  (x + siteOfInt q.1, q.2.1, q.2.2)
theorem mem_nearbyPlaquetteOffsets {q : (Fin 4 → ℤ) × Fin 4 × Fin 4} :
    q ∈ nearbyPlaquetteOffsets ↔ ∀ i, |q.1 i| ≤ 2 := by
  unfold nearbyPlaquetteOffsets
  rw [Finset.mem_product]
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_univ, and_true, abs_le]
theorem siteOfInt_eq_zero_iff (hbig : 4 < n) {a : Fin 4 → ℤ} (ha : ∀ i, |a i| ≤ 4) :
    (siteOfInt a : TorusSite n) = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext i
    have h1 : ((a i : ℤ) : ZMod n) = 0 := congrFun h i
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    refine Int.eq_zero_of_abs_lt_dvd h1 ?_
    have := ha i
    omega
  · rintro rfl
    exact siteOfInt_zero_offset
theorem offsetPlaquette_injOn (hbig : 4 < n) (x : TorusSite n) {q q' : (Fin 4 → ℤ) × Fin 4 × Fin 4}
    (hq : q ∈ nearbyPlaquetteOffsets) (hq' : q' ∈ nearbyPlaquetteOffsets)
    (h : offsetPlaquette x q = offsetPlaquette x q') : q = q' := by
  obtain ⟨e, μ, ν⟩ := q
  obtain ⟨e', μ', ν'⟩ := q'
  simp only [offsetPlaquette, Prod.mk.injEq] at h
  obtain ⟨h1, rfl, rfl⟩ := h
  have h2 : (siteOfInt (e - e') : TorusSite n) = 0 := by
    funext i
    have := congrFun (add_left_cancel h1) i
    simp only [siteOfInt, Pi.sub_apply, Pi.zero_apply] at this ⊢
    push_cast
    rw [this, sub_self]
  have h3 : ∀ i, |(e - e') i| ≤ 4 := by
    intro i
    have a1 := mem_nearbyPlaquetteOffsets.mp hq i
    have a2 := mem_nearbyPlaquetteOffsets.mp hq' i
    simp only [Pi.sub_apply]
    simp only at a1 a2
    rw [abs_le] at a1 a2 ⊢
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have h4 := (siteOfInt_eq_zero_iff hbig h3).mp h2
  have : e = e' := sub_eq_zero.mp h4
  rw [this]
theorem plaquetteVertices_eq_map (w : TorusSite n) (μ ν : Fin 4) :
    plaquetteVertices w μ ν = (plaquetteOffsets μ ν).map fun d => w + siteOfInt d := by
  simp [plaquetteVertices, plaquetteOffsets, siteOfInt_zero_offset, siteOfInt_add,
    unitStep_eq_siteOfInt, add_assoc]
theorem levelShare_zero_eq_sum (hbig : 4 < n) (a : ℝ) (L : ℕ) (S : Finset (TorusSite n))
    (x : TorusSite n) (W : TorusField n) :
    levelShare a L 0 S x W = ∑ q ∈ nearbyPlaquetteOffsets, open Classical in
      if offsetPlaquette x q ∈ plaquettesIn S then
      ((((plaquetteVertices (offsetPlaquette x q).1 (offsetPlaquette x q).2.1
          (offsetPlaquette x q).2.2).count x : ℕ) : ℝ) / 4 *
        plaquetteEnergy W (offsetPlaquette x q).1 (offsetPlaquette x q).2.1
          (offsetPlaquette x q).2.2) else 0 := by
  classical
  simp only [levelShare]
  rw [← Finset.sum_filter, ← Finset.sum_image
    (s := nearbyPlaquetteOffsets.filter fun q => offsetPlaquette x q ∈ plaquettesIn S)
    (g := offsetPlaquette x) (f := fun p : TorusPlaquette n =>
      (((plaquetteVertices p.1 p.2.1 p.2.2).count x : ℕ) : ℝ) / 4 * plaquetteEnergy W p.1 p.2.1 p.2.2)
    (fun q hq q' hq' h => offsetPlaquette_injOn hbig x (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).1
      (Finset.mem_filter.mp (Finset.mem_coe.mp hq')).1 h)]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hq).2
  · intro p hp hnot
    have hc : (plaquetteVertices p.1 p.2.1 p.2.2).count x = 0 := by
      rw [List.count_eq_zero]
      intro hx
      obtain ⟨d, hd, hxd⟩ := (mem_plaquetteVertices_iff_offset _ _ _ _).mp hx
      apply hnot
      refine Finset.mem_image.mpr ⟨(-d, p.2.1, p.2.2), Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · refine mem_nearbyPlaquetteOffsets.mpr fun i => ?_
        have := abs_le_two_of_mem_plaquetteOffsets hd i
        simpa using this
      · have : offsetPlaquette x (-d, p.2.1, p.2.2) = p := by
          simp only [offsetPlaquette]
          have h1 : x + siteOfInt (-d) = p.1 := by
            rw [hxd, add_assoc, ← siteOfInt_add, add_neg_cancel, siteOfInt_zero_offset, add_zero]
          rw [h1]
        rw [this]
        exact hp
      · simp only [offsetPlaquette]
        have h1 : x + siteOfInt (-d) = p.1 := by
          rw [hxd, add_assoc, ← siteOfInt_add, add_neg_cancel, siteOfInt_zero_offset, add_zero]
        rw [h1]
    rw [hc]
    simp
theorem count_plaquetteVertices_eq (hbig : 4 < n) (hbig' : 4 < n') (x : TorusSite n)
    (x' : TorusSite n') {e : Fin 4 → ℤ} (he : ∀ i, |e i| ≤ 2) (μ ν : Fin 4) :
    (plaquetteVertices (x + siteOfInt e) μ ν).count x =
      (plaquetteVertices (x' + siteOfInt e) μ ν).count x' := by
  have key : ∀ (N : ℕ) [NeZero N], 4 < N → ∀ (z : TorusSite N) (d : Fin 4 → ℤ),
      d ∈ plaquetteOffsets μ ν → (z + siteOfInt e + siteOfInt d = z ↔ e + d = 0) := by
    intro N _ hN z d hd
    have h1 : ∀ i, |(e + d) i| ≤ 4 := by
      intro i
      have a1 := he i
      have a2 := abs_le_two_of_mem_plaquetteOffsets hd i
      simp only [Pi.add_apply]
      rw [abs_le] at a1 a2 ⊢
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    rw [← siteOfInt_eq_zero_iff hN h1, add_assoc, ← siteOfInt_add]
    exact add_eq_left
  rw [plaquetteVertices_eq_map, plaquetteVertices_eq_map, List.count, List.count, List.countP_map,
    List.countP_map]
  refine List.countP_congr fun d hd => ?_
  simp only [Function.comp_apply, beq_iff_eq]
  rw [key n hbig x d hd, key n' hbig' x' d hd]
theorem levelZeroShareIsLocal : LevelZeroShareIsLocal := by
  classical
  intro ℓ hadm n n' _ _ U U' x x' m hLn hLn' hm hn hn' hagree hblock
  have hm16 : 2 ^ 16 ≤ m := by omega
  have hbig : 4 < n := by omega
  have hbig' : 4 < n' := by omega
  have hblock' : SameBlockPosition ℓ x' x := by
    intro i
    have := hblock i
    have h2 : (ℓ.side : ℤ) ∣ (((x i).cast : ℤ) - ((x' i).cast : ℤ)) := Int.dvd_of_emod_eq_zero this
    have h3 : (ℓ.side : ℤ) ∣ (((x' i).cast : ℤ) - ((x i).cast : ℤ)) := by
      have := dvd_neg.mpr h2
      simpa using this
    exact Int.emod_eq_zero_of_dvd h3
  have hreg : ∀ h : Fin 4 → ℤ, OffsetInBox (m - 2 ^ 16) h →
      (x + siteOfInt h ∈ (Finset.univ \ thickening lumpRange (torusHotSites ℓ U) :
          Finset (TorusSite n)) ↔
        x' + siteOfInt h ∈ (Finset.univ \ thickening lumpRange (torusHotSites ℓ U') :
          Finset (TorusSite n'))) := by
    intro h hh
    rw [Finset.mem_sdiff, Finset.mem_sdiff]
    simp only [Finset.mem_univ, true_and, not_iff_not]
    exact ⟨mem_thickening_of_fieldsAgreeNear hadm hLn hLn' hm16 hn hagree hblock h hh,
      mem_thickening_of_fieldsAgreeNear hadm hLn' hLn hm16 hn'
        (fun b hbb => (hagree b hbb).symm) hblock' h hh⟩
  have hsmall : ∀ (e d : Fin 4 → ℤ) (μ ν : Fin 4), (∀ i, |e i| ≤ 2) → d ∈ plaquetteOffsets μ ν →
      ∀ r : ℕ, 4 ≤ r → OffsetInBox r (e + d) := by
    intro e d μ ν he hd r hr i
    have a1 := he i
    have a2 := abs_le_two_of_mem_plaquetteOffsets hd i
    have hr' : (4 : ℤ) ≤ r := by exact_mod_cast hr
    simp only [Pi.add_apply]
    rw [abs_le] at a1 a2 ⊢
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  rw [levelShare_zero_eq_sum hbig, levelShare_zero_eq_sum hbig']
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨e, μ, ν⟩ := q
  have he : ∀ i, |e i| ≤ 2 := mem_nearbyPlaquetteOffsets.mp hq
  have hmem : offsetPlaquette x (e, μ, ν) ∈
        plaquettesIn (Finset.univ \ thickening lumpRange (torusHotSites ℓ U)) ↔
      offsetPlaquette x' (e, μ, ν) ∈
        plaquettesIn (Finset.univ \ thickening lumpRange (torusHotSites ℓ U')) := by
    simp only [offsetPlaquette, mem_plaquettesIn_iff_forall_vertex]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h z hz
      obtain ⟨d, hd, rfl⟩ := (mem_plaquetteVertices_iff_offset _ _ _ _).mp hz
      have h1 := h (x + siteOfInt e + siteOfInt d)
        ((mem_plaquetteVertices_iff_offset _ _ _ _).mpr ⟨d, hd, rfl⟩)
      rw [← add_siteOfInt_add] at h1 ⊢
      exact (hreg _ (hsmall e d μ ν he hd _ (by omega))).mp h1
    · intro h z hz
      obtain ⟨d, hd, rfl⟩ := (mem_plaquetteVertices_iff_offset _ _ _ _).mp hz
      have h1 := h (x' + siteOfInt e + siteOfInt d)
        ((mem_plaquetteVertices_iff_offset _ _ _ _).mpr ⟨d, hd, rfl⟩)
      rw [← add_siteOfInt_add] at h1 ⊢
      exact (hreg _ (hsmall e d μ ν he hd _ (by omega))).mpr h1
  by_cases h : offsetPlaquette x (e, μ, ν) ∈
      plaquettesIn (Finset.univ \ thickening lumpRange (torusHotSites ℓ U))
  · rw [if_pos h, if_pos (hmem.mp h)]
    simp only [offsetPlaquette]
    rw [count_plaquetteVertices_eq hbig hbig' x x' he μ ν]
    have hp := holonomy_eq_of_fieldsAgreeNear hagree e μ ν fun d hd => hsmall e d μ ν he hd m (by omega)
    unfold TorusFields.plaquetteEnergy
    rw [hp]
  · rw [if_neg h, if_neg fun h' => h (hmem.mpr h')]
end HoledShares
end YangMills.Construction
end
