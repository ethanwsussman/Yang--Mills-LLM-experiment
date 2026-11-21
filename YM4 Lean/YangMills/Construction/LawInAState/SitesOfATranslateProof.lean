import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.LawInAState.ASiteNearThePairProof
import YangMills.Construction.LawInAState.SitesOfATranslate
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
namespace TranslateSites
variable {L : ℕ} [NeZero L]
private theorem fineBlock_mem_form (hodd : Odd L) : (t n : ℕ) → [NeZero n] → (y : TorusFields.TorusSite n) →
    (c : TorusFields.TorusSite (WeightedResponses.fineSide L t n)) →
    c ∈ WeightedResponses.fineBlock L t n y → ∃ e : Fin 4 → ℤ, (∀ i, 2 * |e i| ≤ (L : ℤ) ^ t - 1) ∧
      c = TorusFields.siteOfInt fun i => (L : ℤ) ^ t * ((y i).cast : ℤ) + e i
  | 0, n, _, y, c, hc => by
    have hcy : c = y := Finset.mem_singleton.mp hc
    refine ⟨0, by simp, ?_⟩
    rw [hcy]
    funext i
    simp only [TorusFields.siteOfInt, pow_zero, one_mul, Pi.zero_apply, add_zero]
    exact (ZMod.intCast_zmod_cast (y i)).symm
  | t + 1, n, _, Y, c, hc => by
    obtain ⟨z, hz, hcz⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨e, he, hce⟩ := fineBlock_mem_form hodd t (n * L) z c hcz
    have hzY : TorusLumps.parentBlock L z = Y := by simpa [TorusLumps.sitesInBlocks] using hz
    obtain ⟨o, ho, hzo⟩ := BlockOffsets.exists_fineSite_of_parentBlock hodd Y z hzY
    have hoi := (BlockOffsets.mem_centredCube_iff o).1 ho
    have hL1 : (1 : ℤ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hQ : (0 : ℤ) < (L : ℤ) ^ t := by positivity
    refine ⟨fun i => (L : ℤ) ^ t * o i + e i, fun i => ?_, ?_⟩
    · obtain ⟨H, hH⟩ := hodd
      have hLH : ((L : ℤ) - 1) / 2 = (H : ℤ) := by subst hH; push_cast; omega
      have hLe : (L : ℤ) = 2 * H + 1 := by subst hH; push_cast; ring
      have h1 := hoi i
      rw [hLH] at h1
      have h2 : |o i| ≤ H := abs_le.mpr h1
      have h3 : |(L : ℤ) ^ t * o i + e i| ≤ (L : ℤ) ^ t * H + |e i| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        rw [abs_mul, abs_of_pos hQ]
        exact mul_le_mul_of_nonneg_left h2 hQ.le
      have h4 := he i
      have hq : (L : ℤ) ^ t * L = (L : ℤ) ^ t * (2 * H + 1) := by rw [← hLe]
      show 2 * |(L : ℤ) ^ t * o i + e i| ≤ (L : ℤ) ^ (t + 1) - 1
      rw [pow_succ]
      linarith [h3, h4, hq]
    · rw [hce]
      funext i
      simp only [TorusFields.siteOfInt]
      have hNL : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
      have hzi : z i = (((L : ℤ) * (((Y i).cast : ℤ) + 0) + o i : ℤ) : ZMod (n * L)) := by
        rw [hzo]
        rfl
      set a : ℤ := (L : ℤ) * (((Y i).cast : ℤ) + 0) + o i with ha
      have hk : ((z i).cast : ℤ) = a + ((n * L : ℕ) : ℤ) * (-(a / ((n * L : ℕ) : ℤ))) := by
        rw [hzi, ZMod.coe_intCast, Int.emod_def]
        ring
      have hM : ((((n * L : ℕ) : ℤ) * (L : ℤ) ^ t : ℤ) : ZMod (WeightedResponses.fineSide L t (n * L))) = 0 := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨1, ?_⟩
        rw [WeightedResponses.fineSide_eq]
        push_cast
        ring
      have hring : (L : ℤ) ^ t * ((z i).cast : ℤ) + e i =
          ((L : ℤ) ^ (t + 1) * ((Y i).cast : ℤ) + ((L : ℤ) ^ t * o i + e i)) +
            (((n * L : ℕ) : ℤ) * (L : ℤ) ^ t) * (-(a / ((n * L : ℕ) : ℤ))) := by
        rw [hk, ha]
        ring
      rw [hring, Int.cast_add, Int.cast_mul _ (-(a / ((n * L : ℕ) : ℤ))), hM, zero_mul, add_zero]
      rfl
private theorem plaquetteVertex_form {m : ℕ} (x : TorusFields.TorusSite m) (μ ν : Fin 4) {c : TorusFields.TorusSite m}
    (hc : c ∈ TorusFields.plaquetteVertices x μ ν) :
    ∃ w : Fin 4 → ℤ, (∀ i, 0 ≤ w i ∧ w i ≤ 2) ∧ c = x + TorusFields.siteOfInt w := by apply _root_.YangMills.SharedProofs.p59526 <;> assumption
private theorem barycenter_position_bound {A Λ ρ Y e δ ε u t z v c o : ℝ} (hA : 1 ≤ A) (hΛ : 0 < Λ)
    (he : 2 * |e| ≤ A - 1) (hδ : |ε - 2 * δ| ≤ 4) (ho : |Λ * c - o| ≤ 1)
    (hb : |(2 * (A * Y + e - δ + 2 * Λ * A * u) + ε + 4 * Λ * A * t) / (2 * (A * Λ)) + 2 * z -
        v * (A / (A * Λ)) - c| ≤ ρ) :
    |Y + 2 * Λ * (u + t + z) - v - o| ≤ Λ * ρ + 3 := by
  set E : ℝ := (2 * e + (ε - 2 * δ)) / (2 * A) with hE
  have hexp : Λ * ((2 * (A * Y + e - δ + 2 * Λ * A * u) + ε + 4 * Λ * A * t) / (2 * (A * Λ)) + 2 * z -
      v * (A / (A * Λ)) - c) = Y + 2 * Λ * (u + t + z) - v - Λ * c + E := by
    rw [hE]
    field_simp
    ring
  have hEb : |E| ≤ 2 := by
    rw [hE, abs_div, abs_of_pos (by positivity : 0 < 2 * A), div_le_iff₀ (by positivity)]
    have h1 : |2 * e + (ε - 2 * δ)| ≤ 2 * |e| + |ε - 2 * δ| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hL : |Y + 2 * Λ * (u + t + z) - v - Λ * c + E| ≤ Λ * ρ := by
    rw [← hexp, abs_mul, abs_of_pos hΛ]
    exact mul_le_mul_of_nonneg_left hb hΛ.le
  have hsplit : Y + 2 * Λ * (u + t + z) - v - o =
      (Y + 2 * Λ * (u + t + z) - v - Λ * c + E) + (Λ * c - o) - E := by ring
  rw [hsplit]
  have h1 := abs_sub (Y + 2 * Λ * (u + t + z) - v - Λ * c + E + (Λ * c - o)) E
  have h2 := abs_add_le (Y + 2 * Λ * (u + t + z) - v - Λ * c + E) (Λ * c - o)
  linarith
private theorem coord_offset_bound (hodd : Odd L) {K k : ℕ} (hk : k ≤ K) {c : InfiniteLattice.AmbientSpace} {ρ : ℝ}
    {g : InfiniteLattice.AmbientSpace → ℝ}
    (hg : ∀ x ∈ tsupport g, ∀ i, |x i - c i| ≤ ρ) {v : Fin 4 → ℤ}
    {y : TorusFields.TorusSite (BoxResponses.boxSide L K k)}
    (hy : y ∈ BoxMarks.weightSitesOf L K k (translateBy L K k v g)) (i : Fin 4) :
    ∃ W : ℤ, (W : ZMod (BoxResponses.boxSide L K k)) =
        y i - ((⌊(L : ℝ) ^ (K - k) * c i⌋ + v i : ℤ) : ZMod (BoxResponses.boxSide L K k)) ∧
      |(W : ℝ)| ≤ (L : ℝ) ^ (K - k) * ρ + 3 := by
  classical
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨p, ⟨hlt, c', hc', hblk⟩, hw⟩ : ∃ p, WeightedResponses.IsPlaquetteAt L k y p ∧
      BoxResponses.unitTorusWeight L K k (translateBy L K k v g) p ≠ 0 := by
    simpa [BoxMarks.weightSitesOf, ResponseInTheExpansion.weightSupportSites] using hy
  obtain ⟨z, hz⟩ : ∃ z : Fin 4 → ℤ, translateBy L K k v g
      (fun j => ((WeightedResponses.doubledBarycentre p j).val : ℝ) / (2 * (L : ℝ) ^ K) + 2 * (z j : ℝ)) ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hw (finsum_eq_zero_of_forall_eq_zero hno)
  have hmem := subset_tsupport g (Function.mem_support.mpr hz)
  have hb := hg _ hmem i
  simp only [Pi.sub_apply] at hb
  obtain ⟨e, he, hce⟩ := fineBlock_mem_form hodd k (BoxResponses.boxSide L K k) y c' hblk
  obtain ⟨w, hw2, hcw⟩ := plaquetteVertex_form p.1 p.2.1 p.2.2 hc'
  have hMeq : ((WeightedResponses.fineSide L k (BoxResponses.boxSide L K k) : ℕ) : ℤ) =
      2 * (L : ℤ) ^ (K - k) * (L : ℤ) ^ k := by
    rw [WeightedResponses.fineSide_eq, BoxResponses.boxSide]
    push_cast
    ring
  set Y : ℤ := ((y i).cast : ℤ) with hY
  set X : ℤ := (L : ℤ) ^ k * Y + e i - w i with hX
  have hcong : (((p.1 i).val : ℤ) : ZMod (WeightedResponses.fineSide L k (BoxResponses.boxSide L K k))) =
      (X : ZMod _) := by
    have h1 : c' i = p.1 i + (w i : ZMod _) := by
      rw [hcw]
      rfl
    have h2 : c' i = (((L : ℤ) ^ k * Y + e i : ℤ) : ZMod _) := by
      rw [hce]
      rfl
    have h3 : p.1 i = (X : ZMod _) := by
      rw [hX, Int.cast_sub, ← h2, h1]
      ring
    rw [h3.symm]
    simp
  obtain ⟨u, hu⟩ : ∃ u : ℤ, ((p.1 i).val : ℤ) =
      X + ((WeightedResponses.fineSide L k (BoxResponses.boxSide L K k) : ℕ) : ℤ) * u := by
    obtain ⟨u, hu⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcong.symm
    exact ⟨u, by linarith⟩
  set ε : ℕ := (if i = p.2.1 then 1 else 0) + (if i = p.2.2 then 1 else 0) with hε
  have hε2 : ε ≤ 2 := by
    rw [hε]
    split_ifs <;> simp
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (((WeightedResponses.doubledBarycentre p i).val : ℕ) : ℤ) =
      2 * ((p.1 i).val : ℤ) + ε + 2 * ((WeightedResponses.fineSide L k (BoxResponses.boxSide L K k) : ℕ) : ℤ) * t := by
    have h1 : WeightedResponses.doubledBarycentre p i = ((2 * (p.1 i).val + ε : ℕ) : ZMod _) := by
      simp only [WeightedResponses.doubledBarycentre, hε]
      congr 1
      ring
    refine ⟨-(((2 * (p.1 i).val + ε : ℕ) : ℤ) /
      ((2 * WeightedResponses.fineSide L k (BoxResponses.boxSide L K k) : ℕ) : ℤ)), ?_⟩
    rw [h1, ZMod.val_natCast]
    have h2 := Int.emod_add_mul_ediv ((2 * (p.1 i).val + ε : ℕ) : ℤ)
      ((2 * WeightedResponses.fineSide L k (BoxResponses.boxSide L K k) : ℕ) : ℤ)
    push_cast at h2 ⊢
    linarith
  set A : ℝ := (L : ℝ) ^ k with hA
  set Λ : ℝ := (L : ℝ) ^ (K - k) with hΛ
  have hA1 : 1 ≤ A := one_le_pow₀ hL1
  have hΛ0 : 0 < Λ := by positivity
  have hAΛ : (L : ℝ) ^ K = A * Λ := by
    rw [hA, hΛ, ← pow_add, Nat.add_sub_cancel' hk]
  have hD : (((WeightedResponses.doubledBarycentre p i).val : ℕ) : ℝ) =
      2 * (A * (Y : ℝ) + (e i : ℝ) - (w i : ℝ) + 2 * Λ * A * (u : ℝ)) + (ε : ℝ) + 4 * Λ * A * (t : ℝ) := by
    have h1 : ((((WeightedResponses.doubledBarycentre p i).val : ℕ) : ℤ) : ℝ) = _ :=
      congrArg (fun q : ℤ => (q : ℝ)) ht
    rw [hu, hMeq, hX] at h1
    push_cast at h1
    rw [h1, hA, hΛ]
    ring
  have hbig := barycenter_position_bound (A := A) (Λ := Λ) (ρ := ρ) (Y := Y) (e := e i) (δ := w i) (ε := ε)
    (u := u) (t := t) (z := z i) (v := v i) (c := c i) (o := (⌊Λ * c i⌋ : ℤ)) hA1 hΛ0 ?_ ?_ ?_ ?_
  · refine ⟨Y + 2 * (L : ℤ) ^ (K - k) * (u + t + z i) - v i - ⌊Λ * c i⌋, ?_, ?_⟩
    · have hN : ((2 * (L : ℤ) ^ (K - k) : ℤ) : ZMod (BoxResponses.boxSide L K k)) = 0 := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨1, ?_⟩
        simp [BoxResponses.boxSide]
      rw [Int.cast_sub, Int.cast_sub, Int.cast_add, Int.cast_mul _ (u + t + z i), hN, zero_mul, add_zero, hY]
      simp
      ring
    · push_cast
      simpa [hΛ] using hbig
  · have h1 := he i
    have h2 : (2 * |e i| : ℤ) ≤ (L : ℤ) ^ k - 1 := h1
    have h3 : ((2 * |e i| : ℤ) : ℝ) ≤ (((L : ℤ) ^ k - 1 : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    simpa [hA] using h3
  · have h1 : (0 : ℝ) ≤ (w i : ℝ) := by exact_mod_cast (hw2 i).1
    have h2 : (w i : ℝ) ≤ 2 := by exact_mod_cast (hw2 i).2
    have h3 : (ε : ℝ) ≤ 2 := by exact_mod_cast hε2
    have h4 : (0 : ℝ) ≤ (ε : ℝ) := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith
  · have h1 := Int.floor_le (Λ * c i)
    have h2 := Int.lt_floor_add_one (Λ * c i)
    rw [abs_le]
    constructor <;> linarith
  · have hq : (((WeightedResponses.doubledBarycentre p i).val : ℕ) : ℝ) / (2 * (L : ℝ) ^ K) + 2 * (z i : ℝ) -
        latticeShift L K k v i - c i =
        (2 * (A * (Y : ℝ) + (e i : ℝ) - (w i : ℝ) + 2 * Λ * A * (u : ℝ)) + (ε : ℝ) + 4 * Λ * A * (t : ℝ)) /
          (2 * (A * Λ)) + 2 * (z i : ℝ) - (v i : ℝ) * (A / (A * Λ)) - c i := by
      rw [hD, hAΛ]
      simp only [latticeShift]
      rw [hAΛ]
    rw [← hq]
    exact hb
private theorem abs_apply_le_euclidNormVec (y : Fin 4 → ℝ) (i : Fin 4) : |y i| ≤ TorusMetric.euclidNormVec y := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
end TranslateSites
open TranslateSites in
theorem translateSitesStatement_holds : translateSitesStatement := by
  intro L K k _ hodd hk d c f hd hf
  refine ⟨fun i => ((⌊(L : ℝ) ^ (K - k) * c i⌋ : ℤ) : ZMod (BoxResponses.boxSide L K k)), fun v y hy => ?_⟩
  have hg : ∀ x ∈ tsupport f, ∀ i, |x i - c i| ≤ d := by
    intro x hx i
    have h1 : TorusMetric.euclidNormVec (x - c) ≤ d := hf hx
    exact (abs_apply_le_euclidNormVec (x - c) i).trans h1
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hr : (0 : ℝ) ≤ lengthInSites L K k d + 4 := by unfold lengthInSites; positivity
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  refine le_trans (Nat.cast_le.mpr (?_ : TorusFields.supDist y _ ≤ ⌊lengthInSites L K k d + 4⌋₊)) (Nat.floor_le hr)
  refine Finset.sup_le fun i _ => Nat.le_floor ?_
  obtain ⟨W, hW, hWb⟩ := coord_offset_bound hodd hk hg hy i
  set a : ZMod (BoxResponses.boxSide L K k) := y i - (((fun i => ((⌊(L : ℝ) ^ (K - k) * c i⌋ : ℤ) :
      ZMod (BoxResponses.boxSide L K k))) : TorusFields.TorusSite (BoxResponses.boxSide L K k)) +
      TorusFields.siteOfInt v : TorusFields.TorusSite (BoxResponses.boxSide L K k)) i with ha
  have hWa : (W : ZMod (BoxResponses.boxSide L K k)) = a := by
    rw [hW, ha]
    simp [TorusFields.siteOfInt]
  have h1 : a.valMinAbs.natAbs ≤ W.natAbs :=
    ZMod.natAbs_min_of_le_div_two _ _ _ (by rw [hWa]; exact ZMod.coe_valMinAbs a) (ZMod.natAbs_valMinAbs_le a)
  have h2 : ((a.valMinAbs.natAbs : ℕ) : ℝ) ≤ (W.natAbs : ℝ) := by exact_mod_cast h1
  have h3 : (W.natAbs : ℝ) = |(W : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h4 : lengthInSites L K k d = (L : ℝ) ^ (K - k) * d := by simp [lengthInSites, mul_comm]
  rw [h4]
  linarith
end YangMills.Construction.StateLaws
end
