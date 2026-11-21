import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.LawInAState.MomentsOfTheCentredResponsesProof
import YangMills.Construction.LawInAState.PlaquettesAtASite
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open TorusFields WeightedResponses TorusLumps BlockOffsets BoxResponses ResponseInTheExpansion
open InfiniteLattice (AmbientSpace)
namespace PlaquetteWeightAtSite
variable {L : ℕ} [NeZero L]
private theorem fineBlock_mem_eq_siteOfInt (hodd : Odd L) : (t n : ℕ) → [NeZero n] → (y : TorusSite n) →
    (c : TorusSite (fineSide L t n)) →
    c ∈ fineBlock L t n y → ∃ e : Fin 4 → ℤ, (∀ i, 2 * |e i| ≤ (L : ℤ) ^ t - 1) ∧
      c = siteOfInt fun i => (L : ℤ) ^ t * ((y i).cast : ℤ) + e i
  | 0, n, _, y, c, hc => by
    have hcy : c = y := Finset.mem_singleton.mp hc
    refine ⟨0, by simp, ?_⟩
    rw [hcy]
    funext i
    simp only [siteOfInt, pow_zero, one_mul, Pi.zero_apply, add_zero]
    exact (ZMod.intCast_zmod_cast (y i)).symm
  | t + 1, n, _, Y, c, hc => by
    obtain ⟨z, hz, hcz⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨e, he, hce⟩ := fineBlock_mem_eq_siteOfInt hodd t (n * L) z c hcz
    have hzY : parentBlock L z = Y := by simpa [sitesInBlocks] using hz
    obtain ⟨o, ho, hzo⟩ := exists_fineSite_of_parentBlock hodd Y z hzY
    have hoi := (mem_centredCube_iff o).1 ho
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
      simp only [siteOfInt]
      haveI hNL : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
      have hzi : z i = (((L : ℤ) * (((Y i).cast : ℤ) + 0) + o i : ℤ) : ZMod (n * L)) := by
        rw [hzo]
        rfl
      set a : ℤ := (L : ℤ) * (((Y i).cast : ℤ) + 0) + o i with ha
      have hk : ((z i).cast : ℤ) = a + ((n * L : ℕ) : ℤ) * (-(a / ((n * L : ℕ) : ℤ))) := by
        rw [hzi, ZMod.coe_intCast, Int.emod_def]
        ring
      have hM : ((((n * L : ℕ) : ℤ) * (L : ℤ) ^ t : ℤ) : ZMod (fineSide L t (n * L))) = 0 := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨1, ?_⟩
        rw [fineSide_eq]
        push_cast
        ring
      have hring : (L : ℤ) ^ t * ((z i).cast : ℤ) + e i =
          ((L : ℤ) ^ (t + 1) * ((Y i).cast : ℤ) + ((L : ℤ) ^ t * o i + e i)) +
            (((n * L : ℕ) : ℤ) * (L : ℤ) ^ t) * (-(a / ((n * L : ℕ) : ℤ))) := by
        rw [hk, ha]
        ring
      rw [hring, Int.cast_add, Int.cast_mul _ (-(a / ((n * L : ℕ) : ℤ))), hM, zero_mul, add_zero]
      rfl
private def dirCount (μ ν i : Fin 4) : ℤ := (if i = μ then 1 else 0) + (if i = ν then 1 else 0)
private theorem plaquetteVertex_eq_add_siteOfInt {m : ℕ} (x : TorusSite m) (μ ν : Fin 4) (hlt : μ < ν)
    (c : TorusSite m) (hc : c ∈ plaquetteVertices x μ ν) :
    ∃ ε : Fin 4 → ℤ, (∀ i, |dirCount μ ν i - 2 * ε i| ≤ 1) ∧ c = x + siteOfInt ε := by
  have hne : μ ≠ ν := ne_of_lt hlt
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · refine ⟨0, fun i => ?_, ?_⟩
    · by_cases h1 : i = μ <;> by_cases h2 : i = ν <;> simp [dirCount, h1, h2, hne, hne.symm]
    · funext i
      simp [siteOfInt]
  · refine ⟨Pi.single μ 1, fun i => ?_, ?_⟩
    · by_cases h1 : i = μ <;> by_cases h2 : i = ν <;> simp [dirCount, h1, h2, hne, hne.symm, Pi.single_apply]
    · rw [unitStep_eq_siteOfInt]
  · refine ⟨Pi.single ν 1, fun i => ?_, ?_⟩
    · by_cases h1 : i = μ <;> by_cases h2 : i = ν <;> simp [dirCount, h1, h2, hne, hne.symm, Pi.single_apply]
    · rw [unitStep_eq_siteOfInt]
  · refine ⟨Pi.single μ 1 + Pi.single ν 1, fun i => ?_, ?_⟩
    · by_cases h1 : i = μ <;> by_cases h2 : i = ν <;> simp [dirCount, h1, h2, hne, hne.symm, Pi.single_apply]
    · rw [unitStep_eq_siteOfInt, unitStep_eq_siteOfInt, siteOfInt_add, add_assoc]
abbrev _root_.YangMills.DeltaSharedProofs.p500648 := @plaquetteVertex_eq_add_siteOfInt
private theorem doubledBarycentre_eq_siteOfInt {m : ℕ} [NeZero m] (p : TorusPlaquette m) (v : Fin 4 → ℤ)
    (hv : p.1 = siteOfInt v) :
    doubledBarycentre p = siteOfInt fun i => 2 * v i + dirCount p.2.1 p.2.2 i := by
  funext i
  have hval : ((p.1 i).val : ℤ) = v i % (m : ℤ) := by
    rw [hv]
    exact ZMod.val_intCast (v i)
  simp only [doubledBarycentre, siteOfInt]
  rw [← Int.cast_natCast, ZMod.intCast_eq_intCast_iff_dvd_sub]
  push_cast
  rw [hval]
  refine ⟨v i / (m : ℤ), ?_⟩
  have := Int.emod_add_mul_ediv (v i) (m : ℤ)
  simp only [dirCount]
  linarith
abbrev _root_.YangMills.DeltaSharedProofs.p501694 := @doubledBarycentre_eq_siteOfInt
theorem periodizeUnitTorus_add_two_mul (f : AmbientSpace → ℝ) (x : AmbientSpace) (w : Fin 4 → ℤ) :
    periodizeUnitTorus f (fun i => x i + 2 * (w i : ℝ)) = periodizeUnitTorus f x := by apply _root_.YangMills.SharedProofs.p63249 <;> assumption
end PlaquetteWeightAtSite
open PlaquetteWeightAtSite in
theorem plaquetteWeightAtSite : plaquetteWeightAtSiteStatement := by
  intro L _ hodd K k hk f y u hu p hp
  obtain ⟨hlt, c, hc, hcy⟩ := hp
  obtain ⟨e, he, hce⟩ := fineBlock_mem_eq_siteOfInt hodd k (boxSide L K k) y c hcy
  obtain ⟨ε, hε, hcε⟩ := plaquetteVertex_eq_add_siteOfInt p.1 p.2.1 p.2.2 hlt c hc
  have hMe : ((fineSide L k (boxSide L K k) : ℕ) : ℤ) = 2 * (L : ℤ) ^ K := by
    rw [fineSide_eq]
    simp only [boxSide]
    push_cast
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  set A : Fin 4 → ℤ := fun i => (L : ℤ) ^ k * ((y i).cast : ℤ) with hA
  have hx : p.1 = siteOfInt fun i => A i + e i - ε i := by
    funext i
    have h1 := congrFun hce i
    have h2 := congrFun hcε i
    simp only [siteOfInt, Pi.add_apply] at h1 h2 ⊢
    have h3 : p.1 i = c i - ((ε i : ℤ) : ZMod (fineSide L k (boxSide L K k))) := eq_sub_of_add_eq h2.symm
    rw [h3, h1, ← Int.cast_sub]
  haveI : NeZero (2 * (fineSide L k (boxSide L K k))) := ⟨mul_ne_zero two_ne_zero (NeZero.ne _)⟩
  have hd := doubledBarycentre_eq_siteOfInt p _ hx
  set a : ℝ := (L : ℝ) ^ k / (L : ℝ) ^ K with ha
  have hLp : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hlift : ∀ i, ∃ t : ℤ, (((y i).cast : ℤ)) = u i + ((boxSide L K k : ℕ) : ℤ) * t := by
    intro i
    have h1 : (((u i : ℤ) : ZMod (boxSide L K k))) = (((y i).cast : ℤ) : ZMod (boxSide L K k)) := by
      rw [hu i, ZMod.intCast_zmod_cast]
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
    obtain ⟨t, ht⟩ := h2
    exact ⟨t, by linarith⟩
  choose t ht using hlift
  have hval : ∀ i, ∃ q : ℤ, (((doubledBarycentre p i).val : ℕ) : ℤ) =
      (2 * (A i + e i - ε i) + dirCount p.2.1 p.2.2 i) + 2 * (((fineSide L k (boxSide L K k)) : ℕ) : ℤ) * q := by
    intro i
    rw [hd]
    simp only [siteOfInt]
    set w : ℤ := 2 * (A i + e i - ε i) + dirCount p.2.1 p.2.2 i with hw
    have := ZMod.val_intCast (n := 2 * (fineSide L k (boxSide L K k))) w
    refine ⟨-(w / ((2 * (fineSide L k (boxSide L K k)) : ℕ) : ℤ)), ?_⟩
    rw [this, Int.emod_def]
    push_cast
    ring
  choose q hq using hval
  refine ⟨fun i => (2 * (e i : ℝ) + ((dirCount p.2.1 p.2.2 i : ℝ) - 2 * (ε i : ℝ))) / (2 * (L : ℝ) ^ K), fun i => ?_, ?_⟩
  · have b1 : (2 * |(e i : ℝ)|) ≤ (L : ℝ) ^ k - 1 := by exact_mod_cast he i
    have b2 : |(dirCount p.2.1 p.2.2 i : ℝ) - 2 * (ε i : ℝ)| ≤ 1 := by exact_mod_cast hε i
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * (L : ℝ) ^ K)]
    have b3 : |2 * (e i : ℝ) + ((dirCount p.2.1 p.2.2 i : ℝ) - 2 * (ε i : ℝ))| ≤ (L : ℝ) ^ k := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two]
      linarith
    rw [div_le_iff₀ (by positivity)]
    have : a / 2 * (2 * (L : ℝ) ^ K) = (L : ℝ) ^ k := by
      rw [ha]; field_simp
    rw [this]
    exact b3
  · have key : (fun i => (((doubledBarycentre p i).val : ℕ) : ℝ) / (2 * (L : ℝ) ^ K)) =
        fun i => ((u i : ℝ) * a + (2 * (e i : ℝ) + ((dirCount p.2.1 p.2.2 i : ℝ) - 2 * (ε i : ℝ))) / (2 * (L : ℝ) ^ K)) +
          2 * (((t i + q i : ℤ)) : ℝ) := by
      funext i
      have hMr : (((fineSide L k (boxSide L K k)) : ℕ) : ℝ) = 2 * (L : ℝ) ^ K := by exact_mod_cast hMe
      have hsr : (L : ℝ) ^ k * ((boxSide L K k : ℕ) : ℝ) = 2 * (L : ℝ) ^ K := by
        have : (((fineSide L k (boxSide L K k)) : ℕ) : ℝ) = ((boxSide L K k : ℕ) : ℝ) * (L : ℝ) ^ k := by
          rw [fineSide_eq]; push_cast; ring
        rw [← hMr, this]; ring
      have h1 : (((doubledBarycentre p i).val : ℕ) : ℝ) =
          2 * ((L : ℝ) ^ k * (u i + ((boxSide L K k : ℕ) : ℝ) * t i) + e i - ε i) + dirCount p.2.1 p.2.2 i +
            2 * (((fineSide L k (boxSide L K k)) : ℕ) : ℝ) * q i := by
        have := hq i
        rw [hA] at this
        simp only at this
        rw [ht i] at this
        exact_mod_cast this
      have h2 : (((doubledBarycentre p i).val : ℕ) : ℝ) = 2 * (L : ℝ) ^ k * u i + 4 * (L : ℝ) ^ K * t i + 2 * e i - 2 * ε i +
          dirCount p.2.1 p.2.2 i + 4 * (L : ℝ) ^ K * q i := by
        rw [h1, hMr]
        linear_combination (2 * (t i : ℝ)) * hsr
      rw [h2, ha]
      push_cast
      field_simp
      ring
    show periodizeUnitTorus f _ = _
    have := periodizeUnitTorus_add_two_mul f
      (fun i => (u i : ℝ) * a + (2 * (e i : ℝ) + ((dirCount p.2.1 p.2.2 i : ℝ) - 2 * (ε i : ℝ))) / (2 * (L : ℝ) ^ K))
      (fun i => t i + q i)
    rw [← this, ← key]
end YangMills.Construction.StateLaws
end
