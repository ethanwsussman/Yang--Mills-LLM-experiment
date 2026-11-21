import YangMills.Construction.ColdChainAtEveryLevel.BareDistanceOfCells
import YangMills.Construction.ColdChainAtEveryLevel.CellSecondDifference
import YangMills.Construction.ColdChainAtEveryLevel.CutsOfCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.GaugeDifferenceNearACell
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMapAgainstTheCurl
import YangMills.Construction.ColdChainAtEveryLevel.RealPointsOfAComplexFamily
import YangMills.Construction.ColdChainAtEveryLevel.TopAverageOfAnyChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace GaugeDiffNearCell
open CoordinateSeminorms CoordinateCutoffs CellDistances
variable {F : BlockFrame}
theorem cellBondNorm_four_one_eq (S : Finset F.Cell) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (z : F.Cell) :
    cellBondNorm 4 S (fun _ => 1) f z = Real.sqrt (Real.sqrt (∑ b ∈ bondsOver S {z} 0, ‖f b.1 b.2‖ ^ 4)) := by
  unfold cellBondNorm
  have hnn : 0 ≤ ∑ b ∈ bondsOver S {z} 0, ‖f b.1 b.2‖ ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
  have hpow : ∀ b : F.Site 0 × Fin 4, (1 * ‖f b.1 b.2‖) ^ (4 : ℝ) = ‖f b.1 b.2‖ ^ 4 := fun b => by
    rw [one_mul]
    exact_mod_cast Real.rpow_natCast _ 4
  simp only [hpow]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hnn]
  norm_num
theorem cellPlaquetteNorm_two_one_eq (S : Finset F.Cell) (g : F.Site 0 × Fin 4 × Fin 4 → ℍ[ℝ]) (z : F.Cell) :
    cellPlaquetteNorm 2 S (fun _ => 1) g z = Real.sqrt (∑ q ∈ plaquettesOver S {z} 0, ‖g q‖ ^ 2) := by
  unfold cellPlaquetteNorm
  have hpow : ∀ q : F.Site 0 × Fin 4 × Fin 4, (1 * ‖g q‖) ^ (2 : ℝ) = ‖g q‖ ^ 2 := fun b => by
    rw [one_mul]
    exact_mod_cast Real.rpow_natCast _ 2
  simp only [hpow]
  rw [Real.sqrt_eq_rpow]
theorem sqrt_sum_add_sum_le_localNorm_sq (S : Finset F.Cell) (R : F.FieldChain)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (z : F.Cell) (hz : z ∈ S) :
    Real.sqrt (∑ b ∈ bondsOver S {z} 0, ‖(u b.1 b.2 : ℍ[ℝ])‖ ^ 4) +
      ∑ q ∈ plaquettesOver S {z} 0, ‖linearizedCurl (R 0) u q‖ ^ 2 ≤
      localNorm S R (baseOnlyChart u) (constOneWeights F) z ^ 2 := by
  have hmono := localNormSq_mono_cells S (B := {z}) (B' := cellBall S z 3)
    (fun y hy => by
      rw [Finset.mem_singleton] at hy
      subst hy
      exact mem_cellBall_self hz) R (baseOnlyChart u) (constOneWeights F)
  unfold localNorm
  rw [Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _)]
  refine le_trans ?_ hmono
  unfold localNormSq
  simp only [constOneWeights, one_mul, baseOnlyChart]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
theorem bondFourthRoot_le_localNorm (S : Finset F.Cell) (R : F.FieldChain)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (z : F.Cell) (hz : z ∈ S) :
    Real.sqrt (Real.sqrt (∑ b ∈ bondsOver S {z} 0, ‖(u b.1 b.2 : ℍ[ℝ])‖ ^ 4)) ≤
      localNorm S R (baseOnlyChart u) (constOneWeights F) z := by
  have hsq := sqrt_sum_add_sum_le_localNorm_sq S R u z hz
  have hcurl : 0 ≤ ∑ q ∈ plaquettesOver S {z} 0, ‖linearizedCurl (R 0) u q‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  exact Real.sqrt_le_iff.2 ⟨ComplexFamilies.localNorm_nonneg _ _ _ _ _, by linarith⟩
theorem sqrt_curl_le_localNorm (S : Finset F.Cell) (R : F.FieldChain)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (z : F.Cell) (hz : z ∈ S) :
    Real.sqrt (∑ q ∈ plaquettesOver S {z} 0, ‖linearizedCurl (R 0) u q‖ ^ 2) ≤
      localNorm S R (baseOnlyChart u) (constOneWeights F) z := by
  have hsq := sqrt_sum_add_sum_le_localNorm_sq S R u z hz
  have hroot := Real.sqrt_nonneg (∑ b ∈ bondsOver S {z} 0, ‖(u b.1 b.2 : ℍ[ℝ])‖ ^ 4)
  exact Real.sqrt_le_iff.2 ⟨ComplexFamilies.localNorm_nonneg _ _ _ _ _, by linarith⟩
theorem sum_sq_le_localNorm_sq (hodd : Odd F.blockSide) (hamb : IsAdmissibleAmbient F) (S : Finset F.Cell)
    (R : F.FieldChain) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (z : F.Cell) (hz : z ∈ S) :
    ∑ b ∈ bondsOver S {z} 0, ‖(u b.1 b.2 : ℍ[ℝ])‖ ^ 2 ≤
      18 * ((F.blockSide : ℝ) ^ F.top) ^ 2 * localNorm S R (baseOnlyChart u) (constOneWeights F) z ^ 2 := by
  classical
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hLpos : (0 : ℝ) < (F.blockSide : ℝ) := by exact_mod_cast hodd.pos
  set D := cellBall S z 1 with hD
  have hcardD : (D.card : ℝ) ≤ 81 := by
    have hle := PatchLocality.card_le_of_cellSupDist_le z 1 D (fun y hy => by
      have hmem := (Finset.mem_filter.1 hy).2
      rw [CoordinateSeminorms.cellSupDist_comm]
      exact hmem)
    have hnat : D.card ≤ 81 := hle.trans (le_of_eq (by norm_num))
    exact_mod_cast hnat
  have hsub : bondsOver S {z} 0 ⊆ innerBonds D 0 := fun b hb =>
    BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hamb hodd S z (Nat.zero_le _) hb
  have hcard : ((bondsOver S {z} 0).card : ℝ) ≤ 324 * N ^ 4 := by
    have hprod : innerBonds D 0 ⊆ sitesOfCells D 0 ×ˢ (Finset.univ : Finset (Fin 4)) := Finset.filter_subset _ _
    have hc := Finset.card_le_card (hsub.trans hprod)
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hc
    have hsites := BlockLines.card_sitesOfCells_le hodd D 0
    have hsitesR : ((sitesOfCells D 0).card : ℝ) ≤ D.card * N ^ 4 := by
      have : ((sitesOfCells D 0).card : ℝ) ≤ ((D.card * (F.blockSide ^ (F.top - 0)) ^ 4 : ℕ) : ℝ) := by
        exact_mod_cast hsites
      simpa [hN] using this
    have hbonds : ((bondsOver S {z} 0).card : ℝ) ≤ (sitesOfCells D 0).card * 4 := by exact_mod_cast hc
    have hD81 : (D.card : ℝ) * N ^ 4 ≤ 81 * N ^ 4 := mul_le_mul_of_nonneg_right hcardD (by positivity)
    nlinarith
  set X : ℝ := ∑ b ∈ bondsOver S {z} 0, ‖(u b.1 b.2 : ℍ[ℝ])‖ ^ 4 with hX
  set T : ℝ := ∑ b ∈ bondsOver S {z} 0, ‖(u b.1 b.2 : ℍ[ℝ])‖ ^ 2 with hT
  have hXnn : 0 ≤ X := Finset.sum_nonneg fun _ _ => by positivity
  have hTsq : T ^ 2 ≤ (18 * N ^ 2) ^ 2 * X := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := bondsOver S {z} 0) (f := fun b => ‖(u b.1 b.2 : ℍ[ℝ])‖ ^ 2)
    have hsum : ∑ b ∈ bondsOver S {z} 0, (‖(u b.1 b.2 : ℍ[ℝ])‖ ^ 2) ^ 2 = X :=
      Finset.sum_congr rfl fun b _ => by ring
    rw [hsum] at hcs
    calc T ^ 2 ≤ ((bondsOver S {z} 0).card : ℝ) * X := hcs
      _ ≤ (324 * N ^ 4) * X := mul_le_mul_of_nonneg_right hcard hXnn
      _ = (18 * N ^ 2) ^ 2 * X := by ring
  have hTle : T ≤ 18 * N ^ 2 * Real.sqrt X := by
    have hroot := Real.le_sqrt_of_sq_le hTsq
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at hroot
  have hq := sqrt_sum_add_sum_le_localNorm_sq S R u z hz
  have hcurl : 0 ≤ ∑ q ∈ plaquettesOver S {z} 0, ‖linearizedCurl (R 0) u q‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hXle : Real.sqrt X ≤ localNorm S R (baseOnlyChart u) (constOneWeights F) z ^ 2 := by linarith
  exact hTle.trans (mul_le_mul_of_nonneg_left hXle (by positivity))
theorem fourNorm_sub_le {β : Type} (s : Finset β) (f g h : β → ℍ[ℝ]) (e : ∀ b, f b = g b - h b) :
    Real.sqrt (Real.sqrt (∑ b ∈ s, ‖f b‖ ^ 4)) ≤
      Real.sqrt (Real.sqrt (∑ b ∈ s, ‖g b‖ ^ 4)) + Real.sqrt (Real.sqrt (∑ b ∈ s, ‖h b‖ ^ 4)) :=
  sqrt_sqrt_sum_pow_four_le_add s (fun b => ‖f b‖) (fun b => ‖g b‖) (fun b => ‖h b‖) (fun _ _ => norm_nonneg _)
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) fun b _ => by
      simp only [e b]
      exact norm_sub_le _ _
theorem mem_cellBall_self_of_mem {S : Finset F.Cell} {z : F.Cell} (hz : z ∈ S) : z ∈ cellBall S z 22 := by
  refine Finset.mem_filter.2 ⟨hz, ?_⟩
  rw [CoordinateSeminorms.cellSupDist_self]
  omega
theorem scaleRadius_eq_of_far (hodd : Odd F.blockSide) (hamb : IsAdmissibleAmbient F) {S : Finset F.Cell}
    {z₀ z : F.Cell} (hz : cellSupDist z₀ z ≤ 22) {b : F.Site 0 × Fin 4} (hb : b ∈ bondsOver S {z} 0) :
    scaleRadius F 0 (cellCentre 0 (z₀ + siteOfCoords F.top (Pi.single 0 30))) b.1 = (F.blockSide : ℝ) ^ F.top := by
  set Pc : F.Cell := z₀ + siteOfCoords F.top (Pi.single 0 30) with hPc
  have hcell : enclosingCell b.1 = z := by
    have := (mem_bondsOver.1 hb).2
    simpa using this
  have hfar : 30 ≤ cellSupDist z₀ Pc := by
    have hsup := Finset.le_sup (f := fun i => ((z₀ i - Pc i).valMinAbs).natAbs) (Finset.mem_univ (0 : Fin 4))
    have hdiff : z₀ 0 - Pc 0 = (((-30 : ℤ)) : ZMod (F.period F.top 0)) := by
      simp [hPc, siteOfCoords]
    have hper : F.period F.top 0 = 0 ∨ 2 * |(-30 : ℤ)| < F.period F.top 0 := by
      have hs : F.period F.top 0 = F.extent 0 := by simp [BlockFrame.period]
      rw [hs]
      rcases hamb with h | h
      · exact Or.inl (h 0)
      · right
        have := h 0
        norm_num
        omega
    have hval : (((-30 : ℤ) : ZMod (F.period F.top 0))).valMinAbs = -30 := valMinAbs_intCast_of_small hper
    have habs : ((z₀ 0 - Pc 0).valMinAbs).natAbs = 30 := by
      rw [hdiff, hval]
      rfl
    have hle : ((z₀ 0 - Pc 0).valMinAbs).natAbs ≤ cellSupDist z₀ Pc := hsup
    omega
  have htri := CoordinateSeminorms.cellSupDist_triangle z₀ z Pc
  have hzP : 8 ≤ cellSupDist z Pc := by omega
  have hbase := cellSupDist_mul_le_baseDistance_add hodd b.1 Pc
  rw [hcell] at hbase
  have hNpos : (0 : ℤ) < (F.blockSide : ℤ) ^ F.top := by
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
    positivity
  have hmul : (8 : ℤ) * (F.blockSide : ℤ) ^ F.top ≤ (cellSupDist z Pc : ℤ) * (F.blockSide : ℤ) ^ F.top :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hzP) hNpos.le
  have hint : (F.blockSide : ℤ) ^ F.top ≤ (baseDistance b.1 (cellCentre 0 Pc) : ℤ) := by linarith
  have hreal : (F.blockSide : ℝ) ^ F.top ≤ (baseDistance b.1 (cellCentre 0 Pc) : ℝ) := by exact_mod_cast hint
  unfold scaleRadius
  refine min_eq_left (hreal.trans (le_max_right _ _))
end GaugeDiffNearCell
open GaugeDiffNearCell CoordinateSeminorms CoordinateCutoffs in
set_option maxHeartbeats 1000000 in
theorem gaugeMapDifferenceNearCellStatement_of (hG : gaugeMapCurlBoundStatement)
    (hTop : linearPartLocalBoundStatement) : gaugeMapDifferenceNearCellStatement := by
  obtain ⟨c, C, L1, hc, hC, hG'⟩ := hG
  obtain ⟨C₅, hC₅, hTop'⟩ := hTop
  refine ⟨min c 1, C * (1 + 2 * C₅) + 6 * C + 1, max L1 5, lt_min hc one_pos, by positivity, ?_⟩
  intro F m S hodd hL hamb hm hreg s V hs hsle hcold u z₀ hz₀
  have hL1 : L1 ≤ F.blockSide := le_trans (le_max_left _ _) hL
  have hL5 : 5 ≤ F.blockSide := le_trans (le_max_right _ _) hL
  have hsc : s ≤ c := hsle.trans (min_le_left _ _)
  have hs1 : s ≤ 1 := hsle.trans (min_le_right _ _)
  set p : F.Site 0 := cellCentre 0 (z₀ + siteOfCoords F.top (Pi.single 0 30)) with hp
  have hmain := (hG' F m S hodd hL1 hamb hm hreg s V hs hsc hcold u).1 (fun _ => 0) 0 0 p (by norm_num) (by norm_num)
    (by simp) z₀ hz₀
  have hw1 : ∀ j, classWeight F (fun _ => 0) 0 p j = fun _ => 1 := by
    intro j
    funext x
    rw [CoordinateCutoffs.classWeight_zero]
    simp
  rw [hw1 0, hw1 F.top] at hmain
  set near : F.Cell → ℝ := fun z => localNorm S (referenceFieldChain S V) (baseOnlyChart u) (constOneWeights F) z
    with hnear
  have hnear0 : ∀ z, 0 ≤ near z := fun z => ComplexFamilies.localNorm_nonneg _ _ _ _ _
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hNpos : 0 < N := by positivity
  have hT1 : ∀ z ∈ cellBall S z₀ 22,
      cellPlaquetteNorm 2 S (fun _ => 1) (linearizedCurl (referenceFieldChain S V 0) u) z +
      cellTopNorm S (fun _ => 1) (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) z ≤
        (1 + 2 * C₅) * near z := by
    intro z hz
    have hzS : z ∈ S := (Finset.mem_filter.1 hz).1
    rw [cellPlaquetteNorm_two_one_eq]
    have hcurl := sqrt_curl_le_localNorm S (referenceFieldChain S V) u z hzS
    have htop : cellTopNorm S (fun _ => 1) (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) z ≤
        2 * C₅ * near z := by
      unfold cellTopNorm
      refine Real.sqrt_le_iff.2 ⟨by have := hnear0 z; positivity, ?_⟩
      have hpt : ∀ c' ∈ bondsOver S {z} F.top,
          (1 * ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top c'.1 c'.2‖) ^ 2 ≤
            (C₅ * near z) ^ 2 := by
        intro c' hc'
        obtain ⟨hin, hcellc⟩ := mem_bondsOver.1 hc'
        have hbd := hTop' F S (referenceFieldChain S V) hodd hL5 hamb (baseOnlyChart u) c' hin
        have hcz : enclosingCell c'.1 = z := by simpa using hcellc
        rw [hcz] at hbd
        rw [one_mul]
        exact pow_le_pow_left₀ (norm_nonneg _) hbd 2
      refine (Finset.sum_le_sum hpt).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc4 : ((bondsOver S {z} F.top).card : ℝ) ≤ 4 := by exact_mod_cast card_bondsOver_singleton_top_le rfl
      nlinarith
    have hsplit : (1 + 2 * C₅) * near z = near z + 2 * C₅ * near z := by ring
    rw [hsplit]
    exact add_le_add hcurl htop
  have hT2 : ∀ z ∈ cellBall S z₀ 22, cellBondNorm 4 S (fun _ => 1) (fun x i => u x i) z +
      cellBondNorm 2 S (fun x => 1 / scaleRadius F 0 p x) (fun x i => u x i) z ≤ 6 * near z := by
    intro z hz
    obtain ⟨hzS, hzd⟩ := Finset.mem_filter.1 hz
    rw [cellBondNorm_four_one_eq]
    have hfour := bondFourthRoot_le_localNorm S (referenceFieldChain S V) u z hzS
    have htwo : cellBondNorm 2 S (fun x => 1 / scaleRadius F 0 p x) (fun x i => u x i) z ≤ 5 * near z := by
      unfold cellBondNorm
      have hterm : ∀ b ∈ bondsOver S {z} 0,
          (1 / scaleRadius F 0 p b.1 * ‖(u b.1 b.2 : ℍ[ℝ])‖) ^ (2 : ℝ) = ‖(u b.1 b.2 : ℍ[ℝ])‖ ^ 2 / N ^ 2 := by
        intro b hb
        rw [scaleRadius_eq_of_far hodd hamb hzd hb]
        have : (1 / N * ‖(u b.1 b.2 : ℍ[ℝ])‖) ^ (2 : ℝ) = (1 / N * ‖(u b.1 b.2 : ℍ[ℝ])‖) ^ 2 := by
          exact_mod_cast Real.rpow_natCast _ 2
        rw [this]
        field_simp
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
      have hsum := sum_sq_le_localNorm_sq hodd hamb S (referenceFieldChain S V) u z hzS
      have hdiv : (∑ b ∈ bondsOver S {z} 0, ‖(u b.1 b.2 : ℍ[ℝ])‖ ^ 2) / N ^ 2 ≤ (5 * near z) ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have h18 : 18 * N ^ 2 * near z ^ 2 ≤ (5 * near z) ^ 2 * N ^ 2 := by
          have : (5 * near z) ^ 2 * N ^ 2 = 25 * N ^ 2 * near z ^ 2 := by ring
          rw [this]
          have : 0 ≤ N ^ 2 * near z ^ 2 := by positivity
          nlinarith
        exact hsum.trans h18
      rw [show (1 / 2 : ℝ) = (1 / 2 : ℝ) from rfl, ← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_iff.2 ⟨by have := hnear0 z; positivity, hdiv⟩
    have hsplit : 6 * near z = near z + 5 * near z := by ring
    rw [hsplit]
    exact add_le_add hfour htwo
  set Sn : ℝ := ∑ z ∈ cellBall S z₀ 22, near z with hSn
  have hSnn : 0 ≤ Sn := Finset.sum_nonneg fun z _ => hnear0 z
  have hA : ∑ z ∈ cellBall S z₀ 22,
      (cellPlaquetteNorm 2 S (fun _ => 1) (linearizedCurl (referenceFieldChain S V 0) u) z +
      cellTopNorm S (fun _ => 1) (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) z) ≤
        (1 + 2 * C₅) * Sn := by
    rw [hSn, Finset.mul_sum]
    exact Finset.sum_le_sum hT1
  have hB : ∑ z ∈ cellBall S z₀ 22, (cellBondNorm 4 S (fun _ => 1) (fun x i => u x i) z +
      cellBondNorm 2 S (fun x => 1 / scaleRadius F 0 p x) (fun x i => u x i) z) ≤ 6 * Sn := by
    rw [hSn, Finset.mul_sum]
    exact Finset.sum_le_sum hT2
  have hbond2 : 0 ≤ cellBondNorm 2 S (fun x => 1 / scaleRadius F 0 p x) (formPlusGaugeDiff S V u) z₀ := by
    unfold cellBondNorm
    exact Real.rpow_nonneg (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (mul_nonneg (by
      have : 0 ≤ scaleRadius F 0 p b.1 := by
        unfold scaleRadius
        refine le_min (by positivity) (le_max_of_le_left (by positivity))
      positivity) (norm_nonneg _)) _) _
  have hmain' : cellBondNorm 4 S (fun _ => 1) (formPlusGaugeDiff S V u) z₀ ≤
      C * ((1 + 2 * C₅) * Sn) + C * s * (6 * Sn) := by
    have hsum : cellBondNorm 4 S (fun _ => 1) (formPlusGaugeDiff S V u) z₀ +
        cellBondNorm 2 S (fun x => 1 / scaleRadius F 0 p x) (formPlusGaugeDiff S V u) z₀ ≤
        C * ∑ z ∈ cellBall S z₀ 22,
          (cellPlaquetteNorm 2 S (fun _ => 1) (linearizedCurl (referenceFieldChain S V 0) u) z +
          cellTopNorm S (fun _ => 1) (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) z) +
        C * s * ∑ z ∈ cellBall S z₀ 22, (cellBondNorm 4 S (fun _ => 1) (fun x i => u x i) z +
          cellBondNorm 2 S (fun x => 1 / scaleRadius F 0 p x) (fun x i => u x i) z) := hmain
    have hCA := mul_le_mul_of_nonneg_left hA hC.le
    have hCB := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ C * s)
    linarith
  rw [cellBondNorm_four_one_eq] at hmain'
  have hDga := fourNorm_sub_le (bondsOver S {z₀} 0)
    (fun b => covariantDiff (referenceFieldChain S V 0)
      (GaugeMap.gaugeMap S V (referenceFieldChain S V 0) fun x i => u x i) b.1 b.2)
    (fun b => formPlusGaugeDiff S V u b.1 b.2) (fun b => (u b.1 b.2 : ℍ[ℝ])) (fun b => by
      simp only [formPlusGaugeDiff]
      abel)
  have hu0 : Real.sqrt (Real.sqrt (∑ b ∈ bondsOver S {z₀} 0, ‖(u b.1 b.2 : ℍ[ℝ])‖ ^ 4)) ≤ Sn := by
    refine (bondFourthRoot_le_localNorm S (referenceFieldChain S V) u z₀ hz₀).trans ?_
    exact Finset.single_le_sum (f := near) (fun z _ => hnear0 z) (mem_cellBall_self_of_mem hz₀)
  refine hDga.trans ?_
  have hs6 : C * s * (6 * Sn) ≤ 6 * C * Sn := by
    have : s * Sn ≤ 1 * Sn := mul_le_mul_of_nonneg_right hs1 hSnn
    nlinarith
  have hexp : (C * (1 + 2 * C₅) + 6 * C + 1) * Sn = C * ((1 + 2 * C₅) * Sn) + 6 * C * Sn + Sn := by ring
  rw [hexp]
  linarith
end YangMills.Construction.BlockAverages
end
