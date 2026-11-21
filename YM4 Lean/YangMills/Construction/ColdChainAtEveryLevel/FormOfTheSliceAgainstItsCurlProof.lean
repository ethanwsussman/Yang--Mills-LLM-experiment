import YangMills.Construction.ColdChainAtEveryLevel.FormOfTheSliceAgainstItsCurl
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMapAgainstTheCurl
import YangMills.Construction.HoleBesideASecondHole.CellsPutBackProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
namespace SliceFormCurl
theorem sum_sq_sum_nbhd_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (nbhd : ι → Finset ι) (M : ℝ) (hM : 0 ≤ M)
    (hsub : ∀ z, nbhd z ⊆ S) (hrow : ∀ z ∈ S, ((nbhd z).card : ℝ) ≤ M)
    (hcol : ∀ y ∈ S, ((S.filter fun z => y ∈ nbhd z).card : ℝ) ≤ M) (f : ι → ℝ) :
    ∑ z ∈ S, (∑ y ∈ nbhd z, f y) ^ 2 ≤ M ^ 2 * ∑ y ∈ S, f y ^ 2 := by
  have hswap : ∑ z ∈ S, ∑ y ∈ nbhd z, f y ^ 2 =
      ∑ y ∈ S, ∑ _z ∈ S.filter (fun z => y ∈ nbhd z), f y ^ 2 := by
    apply Finset.sum_comm'
    intro z y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, hy⟩
      exact ⟨⟨hz, hy⟩, hsub z hy⟩
    · rintro ⟨⟨hz, hy⟩, _⟩
      exact ⟨hz, hy⟩
  calc ∑ z ∈ S, (∑ y ∈ nbhd z, f y) ^ 2
      ≤ ∑ z ∈ S, M * ∑ y ∈ nbhd z, f y ^ 2 := by
        refine Finset.sum_le_sum fun z hz => sq_sum_le_card_mul_sum_sq.trans ?_
        exact mul_le_mul_of_nonneg_right (hrow z hz) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = M * ∑ y ∈ S, ∑ _z ∈ S.filter (fun z => y ∈ nbhd z), f y ^ 2 := by
        rw [← Finset.mul_sum, hswap]
    _ = M * ∑ y ∈ S, ((S.filter fun z => y ∈ nbhd z).card : ℝ) * f y ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ M * ∑ y ∈ S, M * f y ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y hy => ?_) hM
        exact mul_le_mul_of_nonneg_right (hcol y hy) (sq_nonneg _)
    _ = M ^ 2 * ∑ y ∈ S, f y ^ 2 := by
        rw [← Finset.mul_sum]; ring
theorem sqrt_sum_sq_add_le_of_absorb {ι : Type*} [DecidableEq ι] (S : Finset ι) (nbhd : ι → Finset ι)
    (M C s : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hs0 : 0 ≤ s) (hs : 2 * C * M * s ≤ 1) (hsub : ∀ z, nbhd z ⊆ S) (hrow : ∀ z ∈ S, ((nbhd z).card : ℝ) ≤ M)
    (hcol : ∀ y ∈ S, ((S.filter fun z => y ∈ nbhd z).card : ℝ) ≤ M) (A B P T : ι → ℝ) (hA : ∀ z, 0 ≤ A z)
    (hB : ∀ z, 0 ≤ B z)
    (h : ∀ z ∈ S, A z + B z ≤ C * ∑ y ∈ nbhd z, (P y + T y) + C * s * ∑ y ∈ nbhd z, (A y + B y)) :
    Real.sqrt (∑ z ∈ S, A z ^ 2) + Real.sqrt (∑ z ∈ S, B z ^ 2) ≤
      6 * C * M * (Real.sqrt (∑ z ∈ S, P z ^ 2) + Real.sqrt (∑ z ∈ S, T z ^ 2)) := by
  have h1 := sum_sq_sum_nbhd_le S nbhd M hM hsub hrow hcol (fun y => P y + T y)
  have h2 := sum_sq_sum_nbhd_le S nbhd M hM hsub hrow hcol (fun y => A y + B y)
  set SX : ℝ := ∑ z ∈ S, (A z + B z) ^ 2 with hSX
  set SY : ℝ := ∑ z ∈ S, (P z + T z) ^ 2 with hSY
  set SP : ℝ := ∑ z ∈ S, P z ^ 2 with hSP
  set ST : ℝ := ∑ z ∈ S, T z ^ 2 with hST
  have hSX0 : 0 ≤ SX := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSP0 : 0 ≤ SP := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hST0 : 0 ≤ ST := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : ∀ z ∈ S, (A z + B z) ^ 2 ≤ 2 * C ^ 2 * (∑ y ∈ nbhd z, (P y + T y)) ^ 2 +
      2 * (C * s) ^ 2 * (∑ y ∈ nbhd z, (A y + B y)) ^ 2 := by
    intro z hz
    have hx : 0 ≤ A z + B z := add_nonneg (hA z) (hB z)
    have hb := h z hz
    set a := ∑ y ∈ nbhd z, (P y + T y)
    set b := ∑ y ∈ nbhd z, (A y + B y)
    calc (A z + B z) ^ 2 ≤ (C * a + C * s * b) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ ≤ 2 * C ^ 2 * a ^ 2 + 2 * (C * s) ^ 2 * b ^ 2 := by
        nlinarith [sq_nonneg (C * a - C * s * b)]
  have h4 : SX ≤ 2 * C ^ 2 * (M ^ 2 * SY) + 2 * (C * s) ^ 2 * (M ^ 2 * SX) := by
    calc SX ≤ ∑ z ∈ S, (2 * C ^ 2 * (∑ y ∈ nbhd z, (P y + T y)) ^ 2 +
          2 * (C * s) ^ 2 * (∑ y ∈ nbhd z, (A y + B y)) ^ 2) := Finset.sum_le_sum h3
      _ = 2 * C ^ 2 * ∑ z ∈ S, (∑ y ∈ nbhd z, (P y + T y)) ^ 2 +
          2 * (C * s) ^ 2 * ∑ z ∈ S, (∑ y ∈ nbhd z, (A y + B y)) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by
        have e1 : 0 ≤ 2 * C ^ 2 := by positivity
        have e2 : 0 ≤ 2 * (C * s) ^ 2 := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left h1 e1) (mul_le_mul_of_nonneg_left h2 e2)
  have h5 : (C * M * s) ^ 2 ≤ 1 / 4 := by
    have e0 : 0 ≤ C * M * s := by positivity
    nlinarith
  have h6 : SX ≤ 4 * C ^ 2 * M ^ 2 * SY := by
    have e : 2 * (C * s) ^ 2 * (M ^ 2 * SX) ≤ 1 / 2 * SX := by
      have : 2 * (C * s) ^ 2 * (M ^ 2 * SX) = 2 * (C * M * s) ^ 2 * SX := by ring
      rw [this]
      nlinarith
    nlinarith
  have h7 : SY ≤ 2 * SP + 2 * ST := by
    rw [hSY, hSP, hST, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun z _ => by nlinarith [sq_nonneg (P z - T z)]
  set a := Real.sqrt SP with ha
  set b := Real.sqrt ST with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = SP := Real.sq_sqrt hSP0
  have hb2 : b ^ 2 = ST := Real.sq_sqrt hST0
  have h8 : SX ≤ (3 * C * M * (a + b)) ^ 2 := by
    have e1 : 0 ≤ C ^ 2 * M ^ 2 := by positivity
    have e2 : SX ≤ 8 * (C ^ 2 * M ^ 2) * (a ^ 2 + b ^ 2) := by
      rw [ha2, hb2]
      have : 4 * C ^ 2 * M ^ 2 * SY ≤ 4 * C ^ 2 * M ^ 2 * (2 * SP + 2 * ST) :=
        mul_le_mul_of_nonneg_left h7 (by positivity)
      nlinarith
    have e3 : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by nlinarith [mul_nonneg ha0 hb0]
    have e4 : (3 * C * M * (a + b)) ^ 2 = 9 * (C ^ 2 * M ^ 2) * (a + b) ^ 2 := by ring
    rw [e4]
    nlinarith [mul_le_mul_of_nonneg_left e3 e1, mul_nonneg e1 (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  have h9 : Real.sqrt SX ≤ 3 * C * M * (a + b) :=
    Real.sqrt_le_iff.2 ⟨by positivity, h8⟩
  have hA2 : Real.sqrt (∑ z ∈ S, A z ^ 2) ≤ Real.sqrt SX := by
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun z _ => ?_)
    exact pow_le_pow_left₀ (hA z) (le_add_of_nonneg_right (hB z)) 2
  have hB2 : Real.sqrt (∑ z ∈ S, B z ^ 2) ≤ Real.sqrt SX := by
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun z _ => ?_)
    exact pow_le_pow_left₀ (hB z) (le_add_of_nonneg_left (hA z)) 2
  nlinarith
theorem cellBondNorm_four_sq (S : Finset F.Cell) (w : F.Site 0 → ℝ) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (z : F.Cell) :
    cellBondNorm 4 S w f z ^ 2 = Real.sqrt (∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ 4) := by
  unfold cellBondNorm
  have e : ∀ t : ℝ, t ^ (4 : ℝ) = t ^ 4 := fun t => Real.rpow_ofNat t 4
  simp only [e]
  have hA : 0 ≤ ∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ 4 :=
    Finset.sum_nonneg fun _ _ => by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hA]
  norm_num
theorem cellBondNorm_two_sq (S : Finset F.Cell) (w : F.Site 0 → ℝ) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (z : F.Cell) :
    cellBondNorm 2 S w f z ^ 2 = ∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ 2 := by
  unfold cellBondNorm
  have e : ∀ t : ℝ, t ^ (2 : ℝ) = t ^ 2 := fun t => Real.rpow_ofNat t 2
  simp only [e]
  have hA : 0 ≤ ∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hA]
theorem cellPlaquetteNorm_two_sq (S : Finset F.Cell) (w : F.Site 0 → ℝ) (g : F.Site 0 × Fin 4 × Fin 4 → ℍ[ℝ])
    (z : F.Cell) :
    cellPlaquetteNorm 2 S w g z ^ 2 = ∑ p ∈ plaquettesOver S {z} 0, (w p.1 * ‖g p‖) ^ 2 := by
  unfold cellPlaquetteNorm
  have e : ∀ t : ℝ, t ^ (2 : ℝ) = t ^ 2 := fun t => Real.rpow_ofNat t 2
  simp only [e]
  have hA : 0 ≤ ∑ p ∈ plaquettesOver S {z} 0, (w p.1 * ‖g p‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hA]
theorem sum_bondsOver_singleton (S : Finset F.Cell) (j : ℕ) (g : F.Site j × Fin 4 → ℝ) :
    ∑ z ∈ S, ∑ b ∈ bondsOver S {z} j, g b = ∑ b ∈ bondsOver S S j, g b := by
  classical
  have e : ∀ z ∈ S, bondsOver S {z} j = (bondsOver S S j).filter fun b => enclosingCell b.1 = z := by
    intro z hz
    ext b
    simp only [bondsOver, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2 ▸ hz⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
  rw [Finset.sum_congr rfl fun z hz => by rw [e z hz]]
  exact Finset.sum_fiberwise_of_maps_to (fun b hb => (Finset.mem_filter.1 hb).2) g
theorem sum_plaquettesOver_singleton (S : Finset F.Cell) (j : ℕ) (g : F.Site j × Fin 4 × Fin 4 → ℝ) :
    ∑ z ∈ S, ∑ p ∈ plaquettesOver S {z} j, g p = ∑ p ∈ plaquettesOver S S j, g p := by
  classical
  have e : ∀ z ∈ S, plaquettesOver S {z} j =
      (plaquettesOver S S j).filter fun p => enclosingCell p.1 = z := by
    intro z hz
    ext p
    simp only [plaquettesOver, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2 ▸ hz⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
  rw [Finset.sum_congr rfl fun z hz => by rw [e z hz]]
  exact Finset.sum_fiberwise_of_maps_to (fun p hp => (Finset.mem_filter.1 hp).2) g
theorem bondsOver_self (hL : Odd F.blockSide) (S : Finset F.Cell) : bondsOver S S 0 = innerBonds S 0 := by
  classical
  ext b
  simp only [bondsOver, Finset.mem_filter, and_iff_left_iff_imp]
  intro hb
  have h1 := (Finset.mem_filter.1 hb).1
  exact BlockLines.enclosingCell_mem hL (Finset.mem_product.1 h1).1
theorem card_cellBall_le (S : Finset F.Cell) (z : F.Cell) (r : ℕ) : (cellBall S z r).card ≤ (2 * r + 1) ^ 4 := by apply _root_.YangMills.Construction.Reinsertion.card_cellBall_le <;> assumption
theorem card_cellBall_twentyTwo_le (S : Finset F.Cell) (z : F.Cell) : (cellBall S z 22).card ≤ 45 ^ 4 :=
  card_cellBall_le S z 22
theorem formPlusGaugeDiff_of_inGaugeSlice {S : Finset F.Cell} {V : F.GaugeField F.top}
    {u : F.Site 0 → Fin 4 → imaginaryQuaternions}
    (hu : GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) u) {b : F.Site 0 × Fin 4}
    (hb : b ∈ innerBonds S 0) :
    formPlusGaugeDiff S V u b.1 b.2 = (u b.1 b.2 : ℍ[ℝ]) := by
  have h := Finset.mem_filter.1 hb
  have h1 : b.1 ∈ sitesOfCells S 0 := (Finset.mem_product.1 h.1).1
  have h2 : b.1 + unitStep 0 b.2 ∈ sitesOfCells S 0 := h.2
  unfold formPlusGaugeDiff covariantDiff
  rw [hu _ h1, hu _ h2]
  simp [adjointAction]
theorem cellBondNorm_formPlusGaugeDiff_of_inGaugeSlice {S : Finset F.Cell} {V : F.GaugeField F.top}
    {u : F.Site 0 → Fin 4 → imaginaryQuaternions}
    (hu : GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) u) (q : ℝ) (w : F.Site 0 → ℝ) (z : F.Cell) :
    cellBondNorm q S w (formPlusGaugeDiff S V u) z = cellBondNorm q S w (fun x i => (u x i : ℍ[ℝ])) z := by
  unfold cellBondNorm
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [formPlusGaugeDiff_of_inGaugeSlice hu (Finset.mem_filter.1 hb).1]
end SliceFormCurl
open SliceFormCurl in
theorem sliceFormCurlBound_of_gaugeMapCurlBound (hG : gaugeMapCurlBoundStatement) :
    sliceFormCurlBoundStatement := by
  obtain ⟨c, C, L1, hc, hC, H⟩ := hG
  have hM : (0 : ℝ) < 45 ^ 4 := by norm_num
  refine ⟨min c (1 / (2 * C * 45 ^ 4)), 6 * C * 45 ^ 4, L1, lt_min hc (by positivity), by positivity, ?_⟩
  intro F m S hodd hL1 hamb hm hreg s V hs hsc hcold φ θ del p hθ hdel hφ u hu
  have key := (H F m S hodd hL1 hamb hm hreg s V hs (hsc.trans (min_le_left _ _)) hcold u).1
    φ θ del p hθ hdel hφ
  have hs2 : 2 * C * 45 ^ 4 * s ≤ 1 := by
    have h := hsc.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  classical
  have hrad : ∀ x : F.Site 0, 0 ≤ scaleRadius F 0 p x := fun x =>
    le_min (by positivity) (le_max_of_le_left (by positivity))
  have hw : ∀ x : F.Site 0, 0 ≤ classWeight F φ θ p 0 x := fun x =>
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (div_nonneg (hrad x) (by positivity)) _)
  have hw' : ∀ x : F.Site 0, 0 ≤ classWeight F φ θ p 0 x / scaleRadius F 0 p x := fun x =>
    div_nonneg (hw x) (hrad x)
  have hnorm : ∀ (q : ℝ) (w : F.Site 0 → ℝ), (∀ x, 0 ≤ w x) → ∀ (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (z : F.Cell),
      0 ≤ cellBondNorm q S w f z := fun q w hw f z =>
    Real.rpow_nonneg (Finset.sum_nonneg fun b _ =>
      Real.rpow_nonneg (mul_nonneg (hw _) (norm_nonneg _)) _) _
  have hAB := sqrt_sum_sq_add_le_of_absorb S (fun z => cellBall S z 22) (45 ^ 4) C s hM.le hC.le hs.le hs2
    (fun z => BlockLines.cellBall_subset S z 22)
    (fun z _ => by exact_mod_cast card_cellBall_twentyTwo_le S z)
    (fun y _ => by
      have hsubset : (S.filter fun z => y ∈ cellBall S z 22) ⊆ cellBall S y 22 := by
        intro z hz
        obtain ⟨hzS, hy⟩ := Finset.mem_filter.1 hz
        have hd := (Finset.mem_filter.1 hy).2
        exact Finset.mem_filter.2 ⟨hzS, by rw [BlockLines.cellSupDist_comm]; exact hd⟩
      exact_mod_cast (Finset.card_le_card hsubset).trans (card_cellBall_twentyTwo_le S y))
    (fun z => cellBondNorm 4 S (classWeight F φ θ p 0) (fun x i => (u x i : ℍ[ℝ])) z)
    (fun z => cellBondNorm 2 S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
      (fun x i => (u x i : ℍ[ℝ])) z)
    (fun z => cellPlaquetteNorm 2 S (classWeight F φ θ p 0) (linearizedCurl (referenceFieldChain S V 0) u) z)
    (fun z => cellTopNorm S (classWeight F φ θ p F.top)
      (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) z)
    (fun z => hnorm _ _ hw _ z) (fun z => hnorm _ _ hw' _ z)
    (fun z hz => by
      have h := key z hz
      rw [cellBondNorm_formPlusGaugeDiff_of_inGaugeSlice hu,
        cellBondNorm_formPlusGaugeDiff_of_inGaugeSlice hu] at h
      exact h)
  have e1 : cellwiseL4Norm S (classWeight F φ θ p 0) (fun x i => (u x i : ℍ[ℝ])) =
      Real.sqrt (∑ z ∈ S, cellBondNorm 4 S (classWeight F φ θ p 0) (fun x i => (u x i : ℍ[ℝ])) z ^ 2) := by
    unfold cellwiseL4Norm
    simp only [cellBondNorm_four_sq]
  have e2 : weightedBondL2Norm S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
      (fun x i => (u x i : ℍ[ℝ])) =
      Real.sqrt (∑ z ∈ S, cellBondNorm 2 S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
        (fun x i => (u x i : ℍ[ℝ])) z ^ 2) := by
    unfold weightedBondL2Norm
    simp only [cellBondNorm_two_sq]
    rw [sum_bondsOver_singleton, bondsOver_self hodd]
  have e3 : ∑ z ∈ S, cellPlaquetteNorm 2 S (classWeight F φ θ p 0)
      (linearizedCurl (referenceFieldChain S V 0) u) z ^ 2 =
      ∑ q ∈ plaquettesOver S S 0,
        (classWeight F φ θ p 0 q.1 * ‖linearizedCurl (referenceFieldChain S V 0) u q‖) ^ 2 := by
    simp only [cellPlaquetteNorm_two_sq]
    rw [sum_plaquettesOver_singleton]
  have e4 : ∑ z ∈ S, cellTopNorm S (classWeight F φ θ p F.top)
      (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) z ^ 2 ≤
      ∑ b ∈ innerBonds S F.top, (classWeight F φ θ p F.top b.1 *
        ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top b.1 b.2‖) ^ 2 := by
    calc ∑ z ∈ S, cellTopNorm S (classWeight F φ θ p F.top)
          (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) z ^ 2
        = ∑ z ∈ S, ∑ b ∈ bondsOver S {z} F.top, (classWeight F φ θ p F.top b.1 *
            ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top b.1 b.2‖) ^ 2 := by
          refine Finset.sum_congr rfl fun z _ => ?_
          unfold cellTopNorm
          exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = ∑ b ∈ bondsOver S S F.top, (classWeight F φ θ p F.top b.1 *
            ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top b.1 b.2‖) ^ 2 :=
          sum_bondsOver_singleton S F.top _
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => sq_nonneg _
  rw [e1, e2]
  refine hAB.trans (mul_le_mul_of_nonneg_left (add_le_add (le_of_eq ?_) (Real.sqrt_le_sqrt e4)) (by positivity))
  rw [e3]
end YangMills.Construction.BlockAverages
end
