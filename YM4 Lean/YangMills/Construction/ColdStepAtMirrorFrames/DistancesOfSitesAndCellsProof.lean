import YangMills.Construction.ColdChainAtEveryLevel.WeightsUpTheLevels
import YangMills.Construction.ColdStepAtMirrorFrames.BlocksCoverTheLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.DistancesOfSitesAndCells
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames.SiteCellDistance
theorem valMinAbs_intCast_natAbs_le {n : ℕ} (z : ℤ) : ((z : ZMod n).valMinAbs).natAbs ≤ z.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
variable {F : BlockFrame}
theorem enclosingCell_refineSite_add (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (y : F.Cell)
    (o : Fin 4 → ℤ) :
    enclosingCell (refineSite y + siteOfCoords F.depth o) =
      y + siteOfCoords F.top (fun i => (o i + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ)) := by
  have hLpos : (0 : ℤ) < (F.blockSide : ℤ) := by exact_mod_cast hL.pos
  have hsub : F.top - F.depth = 1 := by simp [BlockFrame.top]
  funext i
  have hper1 : F.period F.top i = F.extent i := by simp [BlockFrame.period]
  have hper0 : F.period F.depth i = F.period F.top i * F.blockSide := by
    simp [BlockFrame.period, hsub]
  have hne1 : NeZero (F.period F.top i) := ⟨by rw [hper1]; exact (hs i).ne'⟩
  have hne0 : NeZero (F.period F.depth i) :=
    ⟨by rw [hper0]; exact Nat.mul_ne_zero hne1.out (by exact_mod_cast hLpos.ne')⟩
  set c : ℤ := siteCoords y i with hc
  set P : ℤ := (F.period F.top i : ℤ) with hP
  set q : ℤ := ((F.blockSide : ℤ) * c + o i) / (P * (F.blockSide : ℤ)) with hq
  have hcoord : siteCoords (refineSite y + siteOfCoords F.depth o) i =
      (F.blockSide : ℤ) * c + o i - P * (F.blockSide : ℤ) * q := by
    have e1 : (refineSite y + siteOfCoords F.depth o : F.Site F.depth) i =
        (((F.blockSide : ℤ) * c + o i : ℤ) : ZMod (F.period F.depth i)) := by
      simp [refineSite, siteOfCoords, hc, siteCoords]
    have e2 := Int.emod_add_mul_ediv ((F.blockSide : ℤ) * c + o i) ((F.period F.depth i : ℕ) : ℤ)
    have e3 : ((F.period F.depth i : ℕ) : ℤ) = P * (F.blockSide : ℤ) := by
      rw [hper0, hP]
      push_cast
      ring
    simp only [siteCoords]
    rw [e1, ZMod.coe_intCast]
    rw [e3] at e2 ⊢
    linear_combination e2
  simp only [enclosingCell, siteOfCoords, hsub, pow_one, Pi.add_apply]
  rw [hcoord]
  have e4 : (F.blockSide : ℤ) * c + o i - P * (F.blockSide : ℤ) * q + ((F.blockSide : ℤ) - 1) / 2 =
      (o i + ((F.blockSide : ℤ) - 1) / 2) + (F.blockSide : ℤ) * (c - P * q) := by ring
  rw [e4, Int.add_mul_ediv_left _ _ hLpos.ne']
  push_cast
  have e5 : ((P : ℤ) : ZMod (F.period F.top i)) = 0 := by
    simp [hP]
  have e6 : ((c : ℤ) : ZMod (F.period F.top i)) = y i := by
    simp only [hc, siteCoords]
    exact ZMod.intCast_zmod_cast (y i)
  rw [e5, e6]
  ring
theorem half_blockSide_div_eq_zero (hL : Odd F.blockSide) :
    (0 + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ) = 0 := by
  obtain ⟨m, hm⟩ := hL
  have h1 : ((F.blockSide : ℤ) - 1) / 2 = m := by
    rw [hm]
    push_cast
    omega
  rw [h1, hm]
  push_cast
  rw [zero_add]
  exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
theorem siteOfCoords_zero (j : ℕ) : (siteOfCoords j (fun _ => (0 : ℤ)) : F.Site j) = 0 := by
  funext i
  simp [siteOfCoords]
theorem enclosingCell_refineSite (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (y : F.Cell) :
    enclosingCell (refineSite y) = y := by
  have h := enclosingCell_refineSite_add hL hs y (fun _ => 0)
  rw [siteOfCoords_zero, add_zero] at h
  rw [h]
  simp only [half_blockSide_div_eq_zero hL]
  rw [siteOfCoords_zero, add_zero]
theorem exists_offset_of_site (hB : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (x : F.Site F.depth) :
    ∃ (h : Fin 4 → ℤ), (∀ i, 2 * |h i| + 1 ≤ (F.blockSide : ℤ)) ∧
      x = refineSite (enclosingCell x) + siteOfCoords F.depth h := by
  have hsub : F.top - F.depth = 1 := by simp [BlockFrame.top]
  obtain ⟨m, hm⟩ := hL
  have hm' : (F.blockSide : ℤ) = 2 * m + 1 := by exact_mod_cast hm
  have hk : ((F.blockSide : ℤ) - 1) / 2 = m := by
    rw [hm']
    omega
  have hmem := hB F ⟨m, hm⟩ hs x
  unfold sitesOfCells at hmem
  obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.1 hmem
  obtain ⟨h, hh, hx⟩ := Finset.mem_image.1 hz
  rw [hsub, pow_one] at hh
  have hcent : cellCentre F.depth z = refineSite z := by
    unfold cellCentre refineSite
    rw [hsub, pow_one]
  rw [hcent] at hx
  have hhb : ∀ i, |h i| ≤ m := by
    intro i
    have := Fintype.mem_piFinset.1 hh i
    rw [Finset.mem_Icc, hk] at this
    exact abs_le.2 this
  have hcx : enclosingCell x = z := by
    rw [← hx, enclosingCell_refineSite_add ⟨m, hm⟩ hs]
    have : (fun i => (h i + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ)) = fun _ => (0 : ℤ) := by
      funext i
      rw [hk]
      have := abs_le.1 (hhb i)
      exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
    rw [this, siteOfCoords_zero, add_zero]
  refine ⟨h, fun i => ?_, ?_⟩
  · have := hhb i
    omega
  · rw [hcx, hx]
theorem siteSupDist_le_blockSide_mul (hB : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (x x' : F.Site F.depth) :
    (siteSupDist x x' : ℝ) ≤
      (F.blockSide : ℝ) * ((siteSupDist (enclosingCell x) (enclosingCell x') : ℝ) + 1) := by
  obtain ⟨h, hh, hx⟩ := exists_offset_of_site hB hL hs x
  obtain ⟨h', hh', hx'⟩ := exists_offset_of_site hB hL hs x'
  set z := enclosingCell x with hz
  set z' := enclosingCell x' with hz'
  set d : ℕ := siteSupDist z z' with hd
  have hsub : F.top - F.depth = 1 := by simp [BlockFrame.top]
  have hb : siteSupDist x x' ≤ F.blockSide * d + F.blockSide := by
    unfold siteSupDist
    refine Finset.sup_le fun i _ => ?_
    set o : ℤ := (z i - z' i).valMinAbs with ho
    have hod : o.natAbs ≤ d := Finset.le_sup (f := fun i => ((z i - z' i).valMinAbs).natAbs) (Finset.mem_univ i)
    have hper1 : F.period F.top i = F.extent i := by simp [BlockFrame.period]
    have hper0 : F.period F.depth i = F.period F.top i * F.blockSide := by
      simp [BlockFrame.period, hsub]
    have hne1 : NeZero (F.period F.top i) := ⟨by rw [hper1]; exact (hs i).ne'⟩
    have hcz : ((siteCoords z i - siteCoords z' i - o : ℤ) : ZMod (F.period F.top i)) = 0 := by
      have e1 : ((siteCoords z i : ℤ) : ZMod (F.period F.top i)) = z i := ZMod.intCast_zmod_cast (z i)
      have e2 : ((siteCoords z' i : ℤ) : ZMod (F.period F.top i)) = z' i :=
        ZMod.intCast_zmod_cast (z' i)
      have e3 : ((o : ℤ) : ZMod (F.period F.top i)) = z i - z' i := ZMod.coe_valMinAbs _
      push_cast
      rw [e1, e2, e3]
      ring
    obtain ⟨u, hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hcz
    have hval : x i - x' i =
        (((F.blockSide : ℤ) * o + (h i - h' i) : ℤ) : ZMod (F.period F.depth i)) := by
      have e1 : x i = (((F.blockSide : ℤ) * siteCoords z i + h i : ℤ) : ZMod (F.period F.depth i)) := by
        conv_lhs => rw [hx]
        simp [refineSite, siteOfCoords]
      have e2 : x' i =
          (((F.blockSide : ℤ) * siteCoords z' i + h' i : ℤ) : ZMod (F.period F.depth i)) := by
        conv_lhs => rw [hx']
        simp [refineSite, siteOfCoords]
      rw [e1, e2, ← Int.cast_sub]
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      refine ⟨-u, ?_⟩
      rw [hper0]
      push_cast
      linear_combination (-(F.blockSide : ℤ)) * hu
    rw [hval]
    refine (valMinAbs_intCast_natAbs_le _).trans ?_
    have hlin := Int.natAbs_add_le ((F.blockSide : ℤ) * o) (h i - h' i)
    have hmul : ((F.blockSide : ℤ) * o).natAbs = F.blockSide * o.natAbs := by
      rw [Int.natAbs_mul]
      simp
    have h1 := hh i
    have h2 := hh' i
    have hdiff : (h i - h' i).natAbs ≤ F.blockSide := by
      have : |h i - h' i| ≤ |h i| + |h' i| := abs_sub _ _
      have h3 : (((h i - h' i).natAbs : ℕ) : ℤ) ≤ (F.blockSide : ℤ) := by
        rw [← Int.abs_eq_natAbs]
        omega
      exact_mod_cast h3
    have hod2 : F.blockSide * o.natAbs ≤ F.blockSide * d := Nat.mul_le_mul_left _ hod
    omega
  have hbr : (siteSupDist x x' : ℝ) ≤ (F.blockSide : ℝ) * (d : ℝ) + F.blockSide := by
    exact_mod_cast hb
  calc (siteSupDist x x' : ℝ) ≤ (F.blockSide : ℝ) * (d : ℝ) + F.blockSide := hbr
    _ = _ := by ring
theorem supDistCellComparison_holds (hB : BlocksCoverLowerLevel) : SupDistCellComparison := by
  have h1 : ∀ (F : BlockFrame) (j : ℕ) (y z u : F.Site j), siteSupDist y y = 0 ∧
      siteSupDist y z = siteSupDist z y ∧ siteSupDist y u ≤ siteSupDist y z + siteSupDist z u := by
    intro F j y z u
    refine ⟨by simp [siteSupDist], ?_, ?_⟩
    · unfold siteSupDist
      congr 1
      funext i
      rw [← neg_sub (y i) (z i), ZMod.natAbs_valMinAbs_neg]
    · unfold siteSupDist
      refine Finset.sup_le fun i _ => ?_
      have e : y i - u i = (y i - z i) + (z i - u i) := by ring
      rw [e]
      refine (ZMod.natAbs_valMinAbs_add_le _ _).trans
        ((Int.natAbs_add_le _ _).trans (add_le_add ?_ ?_))
      · exact Finset.le_sup (f := fun i => ((y i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
      · exact Finset.le_sup (f := fun i => ((z i - u i).valMinAbs).natAbs) (Finset.mem_univ i)
  have h2 : ∀ (F : BlockFrame) (j : ℕ) (y : F.Site j) (o : Fin 4 → ℤ) (M : ℕ),
      (∀ i, (o i).natAbs ≤ M) → siteSupDist y (y + siteOfCoords j o) ≤ M := by
    intro F j y o M ho
    unfold siteSupDist
    refine Finset.sup_le fun i _ => ?_
    have e : y i - (y + siteOfCoords j o : F.Site j) i = -((o i : ℤ) : ZMod (F.period j i)) := by
      simp [siteOfCoords]
    rw [e, ZMod.natAbs_valMinAbs_neg]
    exact (valMinAbs_intCast_natAbs_le _).trans (ho i)
  refine ⟨h1, h2, fun F hL hs => ⟨fun x x' => ?_,
    fun x x' => siteSupDist_le_blockSide_mul hB hL hs x x', enclosingCell_refineSite hL hs⟩⟩
  have hLpos : (0 : ℤ) < (F.blockSide : ℤ) := by exact_mod_cast hL.pos
  have hsub : F.top - F.depth = 1 := by simp [BlockFrame.top]
  obtain ⟨m, hm⟩ := hL
  have hm' : (F.blockSide : ℤ) = 2 * m + 1 := by exact_mod_cast hm
  have hk : ((F.blockSide : ℤ) - 1) / 2 = m := by
    rw [hm']
    omega
  have hmem := hB F ⟨m, hm⟩ hs x
  unfold sitesOfCells at hmem
  obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.1 hmem
  obtain ⟨h, hh, hx⟩ := Finset.mem_image.1 hz
  rw [hsub, pow_one] at hh
  have hcent : cellCentre F.depth z = refineSite z := by
    unfold cellCentre refineSite
    rw [hsub, pow_one]
  rw [hcent] at hx
  have hhb : ∀ i, 0 ≤ h i + m ∧ h i + m < (F.blockSide : ℤ) := by
    intro i
    have := Fintype.mem_piFinset.1 hh i
    rw [Finset.mem_Icc, hk] at this
    omega
  set D : ℕ := siteSupDist x x' with hD
  set o : Fin 4 → ℤ := fun i => (x' i - x i).valMinAbs with ho
  have hoD : ∀ i, (o i).natAbs ≤ D := by
    intro i
    have e : (o i).natAbs = ((x i - x' i).valMinAbs).natAbs := by
      simp only [ho]
      rw [← neg_sub (x i) (x' i), ZMod.natAbs_valMinAbs_neg]
    rw [e]
    exact Finset.le_sup (f := fun i => ((x i - x' i).valMinAbs).natAbs) (Finset.mem_univ i)
  have hx' : x' = refineSite z + siteOfCoords F.depth (fun i => h i + o i) := by
    funext i
    have e : (siteOfCoords F.depth (fun i => h i + o i) : F.Site F.depth) i =
        (siteOfCoords F.depth h : F.Site F.depth) i + ((o i : ℤ) : ZMod (F.period F.depth i)) := by
      simp [siteOfCoords]
    have e2 : ((o i : ℤ) : ZMod (F.period F.depth i)) = x' i - x i := ZMod.coe_valMinAbs _
    rw [Pi.add_apply, e, e2, ← add_assoc, ← Pi.add_apply, hx]
    ring
  have hcx : enclosingCell x = z := by
    rw [← hx, enclosingCell_refineSite_add ⟨m, hm⟩ hs]
    have : (fun i => (h i + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ)) = fun _ => (0 : ℤ) := by
      funext i
      rw [hk]
      exact Int.ediv_eq_zero_of_lt (hhb i).1 (hhb i).2
    rw [this, siteOfCoords_zero, add_zero]
  have hcx' : enclosingCell x' =
      z + siteOfCoords F.top (fun i => (h i + o i + m) / (F.blockSide : ℤ)) := by
    rw [hx', enclosingCell_refineSite_add ⟨m, hm⟩ hs, hk]
  set q₀ : ℕ := D / F.blockSide with hq₀
  have hDq : (D : ℤ) < ((q₀ : ℤ) + 1) * (F.blockSide : ℤ) := by
    have := Nat.lt_mul_div_succ D (Nat.pos_of_ne_zero (by omega : F.blockSide ≠ 0))
    have h3 : D < F.blockSide * (q₀ + 1) := this
    linarith
  have hu : ∀ i, ((h i + o i + m) / (F.blockSide : ℤ)).natAbs ≤ q₀ + 1 := by
    intro i
    set a : ℤ := h i + o i + m with ha
    set u : ℤ := a / (F.blockSide : ℤ) with hu'
    have h5 : u * (F.blockSide : ℤ) ≤ a := Int.ediv_mul_le a hLpos.ne'
    have h6 : a < (u + 1) * (F.blockSide : ℤ) := Int.lt_ediv_add_one_mul_self a hLpos
    have h7 : |o i| ≤ (D : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hoD i
    have h8 := abs_le.1 h7
    have h9 := hhb i
    have up : u < (q₀ : ℤ) + 2 := by
      by_contra hc
      have hc' : (q₀ : ℤ) + 2 ≤ u := not_lt.1 hc
      nlinarith
    have dn : -((q₀ : ℤ) + 2) < u := by
      by_contra hc
      have hc' : u ≤ -((q₀ : ℤ) + 2) := not_lt.1 hc
      nlinarith
    omega
  have hd : siteSupDist (enclosingCell x) (enclosingCell x') ≤ q₀ + 1 := by
    rw [hcx, hcx']
    exact h2 F F.top z _ _ hu
  have hdr : (siteSupDist (enclosingCell x) (enclosingCell x') : ℝ) - 1 ≤ q₀ := by
    have : (siteSupDist (enclosingCell x) (enclosingCell x') : ℝ) ≤ q₀ + 1 := by exact_mod_cast hd
    linarith
  have hq : (F.blockSide : ℝ) * q₀ ≤ D := by
    have : F.blockSide * q₀ ≤ D := Nat.mul_div_le D F.blockSide
    exact_mod_cast this
  have hLr : (0 : ℝ) ≤ F.blockSide := Nat.cast_nonneg _
  calc (F.blockSide : ℝ) * ((siteSupDist (enclosingCell x) (enclosingCell x') : ℝ) - 1)
        ≤ F.blockSide * q₀ := mul_le_mul_of_nonneg_left hdr hLr
    _ ≤ D := hq
end YangMills.Construction.ColdStepAtMirrorFrames.SiteCellDistance
end
