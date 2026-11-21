import YangMills.Construction.ColdChainAtEveryLevel.AveragesAndLocalSizesOfALevelProof
import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdChainAtEveryLevel.GaugeDirectionsOfARegularChain
import Mathlib
import YangMills.Construction.ColdChainAtEveryLevel.CoordinatesOfEveryLevel
import YangMills.Construction.ColdChainAtEveryLevel.FactsOfTheLogarithm
set_option autoImplicit false

noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
def compositeMeanStatement : Prop :=
  ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 8 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c →
          ∀ (ξ : F.Site 0 → imaginaryQuaternions), ∀ y ∈ S,
            ‖adjointAction (GaugeMap.frameChange S V y (cellCentre 0 y))⁻¹
                (gaugeGeneratorAtLevel (referenceFieldChain S V) U ξ F.top y) -
                GaugeMap.frameCellMean S V y (fun x => ξ x)‖ ≤
              C * (s + supWeightedNorm S δ (referenceFieldChain S V) U) *
                (cellSiteNorm 4 S (fun _ => 1) (fun x => ξ x) y / (GaugeMap.cellSideLength F : ℝ))
end BlockAverages
end YangMills.Construction
end

noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace GeneratorMeans
open LatticePaths GaugeMap LatticeFractionalIntegration
section Blocks
def blockSite (L : ℕ) (v h : Lattice4) : Lattice4 := fun i => (L : ℤ) * v i + h i
theorem exists_half_of_odd {L : ℕ} (hL : Odd L) :
    ∃ l : ℤ, (L : ℤ) = 2 * l + 1 ∧ ((L : ℤ) - 1) / 2 = l ∧ 0 ≤ l := by
  obtain ⟨l, rfl⟩ := hL
  exact ⟨l, by push_cast; ring, by push_cast; omega, by positivity⟩
theorem half_natCast_mul {L M : ℕ} (hL : Odd L) (hM : Odd M) :
    (((L * M : ℕ) : ℤ) - 1) / 2 = (L : ℤ) * (((M : ℤ) - 1) / 2) + ((L : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.half_mul_odd <;> assumption
theorem blockSite_mem_centredCube {L M : ℕ} (hL : Odd L) (hM : Odd M) {v h : Lattice4}
    (hv : v ∈ centredCube M) (hh : h ∈ centredCube L) :
    blockSite L v h ∈ centredCube (L * M) := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.mul_add_mem_centredCube <;> assumption
theorem sum_blockSite {E : Type} [AddCommMonoid E] {L M : ℕ} (hL : Odd L) (hM : Odd M) (f : Lattice4 → E) :
    ∑ v ∈ centredCube M, ∑ h ∈ centredCube L, f (blockSite L v h) = ∑ w ∈ centredCube (L * M), f w := by
  obtain ⟨l, e1, e2, l0⟩ := exists_half_of_odd hL
  have hLpos : (0 : ℤ) < (L : ℤ) := by omega
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => blockSite L p.1 p.2)
    (fun w => (fun i => (w i + l) / (L : ℤ), fun i => (w i + l) % (L : ℤ) - l)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨v, h⟩ hp
    obtain ⟨hv, hh⟩ := Finset.mem_product.1 hp
    exact blockSite_mem_centredCube hL hM hv hh
  · intro w hw
    rw [mem_centredCube_iff] at hw
    rw [Finset.mem_product]
    constructor
    · rw [mem_centredCube_iff]
      intro i
      have h1 := hw i
      rw [half_natCast_mul hL hM, e2] at h1
      set m := ((M : ℤ) - 1) / 2
      constructor
      · have : -m * (L : ℤ) ≤ w i + l := by nlinarith [h1.1]
        have := Int.le_ediv_of_mul_le hLpos this
        simpa using this
      · have : w i + l < (m + 1) * (L : ℤ) := by nlinarith [h1.2]
        have := Int.ediv_lt_of_lt_mul hLpos this
        show (w i + l) / (L : ℤ) ≤ m
        omega
    · rw [mem_centredCube_iff]
      intro i
      have h3 := Int.emod_nonneg (w i + l) hLpos.ne'
      have h4 := Int.emod_lt_of_pos (w i + l) hLpos
      rw [e2]
      show -l ≤ (w i + l) % (L : ℤ) - l ∧ (w i + l) % (L : ℤ) - l ≤ l
      constructor <;> omega
  · rintro ⟨v, h⟩ hp
    have hh : h ∈ centredCube L := (Finset.mem_product.1 hp).2
    rw [mem_centredCube_iff] at hh
    have key : ∀ i, (blockSite L v h i + l) / (L : ℤ) = v i ∧ (blockSite L v h i + l) % (L : ℤ) = h i + l := by
      intro i
      have h1 := hh i
      rw [e2] at h1
      have a : blockSite L v h i + l = (h i + l) + (L : ℤ) * v i := by
        simp only [blockSite]
        ring
      have b0 : 0 ≤ h i + l := by omega
      have b1 : h i + l < (L : ℤ) := by omega
      rw [a]
      constructor
      · rw [Int.add_mul_ediv_left _ _ hLpos.ne', Int.ediv_eq_zero_of_lt b0 b1, zero_add]
      · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt b0 b1]
    refine Prod.ext ?_ ?_
    · funext i
      exact (key i).1
    · funext i
      show (blockSite L v h i + l) % (L : ℤ) - l = h i
      rw [(key i).2]
      ring
  · intro w _
    funext i
    show (L : ℤ) * ((w i + l) / (L : ℤ)) + ((w i + l) % (L : ℤ) - l) = w i
    have := Int.mul_ediv_add_emod (w i + l) (L : ℤ)
    linarith
  · rintro ⟨v, h⟩ _
    rfl
def blockAverage {E : Type} [AddCommGroup E] [Module ℝ E] (L : ℕ) (f : Lattice4 → E) (v : Lattice4) : E :=
  (1 / (L : ℝ) ^ 4) • ∑ h ∈ centredCube L, f (blockSite L v h)
theorem card_centredCube_real {L : ℕ} (hL : Odd L) : ((centredCube L).card : ℝ) = (L : ℝ) ^ 4 := by
  rw [card_centredCube hL]
  push_cast
  rfl
theorem blockAverage_nonneg {L : ℕ} {a : Lattice4 → ℝ} (ha : ∀ w, 0 ≤ a w) (v : Lattice4) :
    0 ≤ blockAverage L a v := by
  simp only [blockAverage, smul_eq_mul]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => ha _)
theorem norm_blockAverage_le {L : ℕ} (f : Lattice4 → ℍ[ℝ]) (v : Lattice4) :
    ‖blockAverage L f v‖ ≤ blockAverage L (fun w => ‖f w‖) v := by
  simp only [blockAverage, smul_eq_mul, norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
theorem blockAverage_add {L : ℕ} (a b : Lattice4 → ℝ) (v : Lattice4) :
    blockAverage L (fun w => a w + b w) v = blockAverage L a v + blockAverage L b v := by
  simp only [blockAverage, smul_eq_mul, Finset.sum_add_distrib, mul_add]
theorem blockAverage_mono {L : ℕ} {a b : Lattice4 → ℝ} (h : ∀ w, a w ≤ b w) (v : Lattice4) :
    blockAverage L a v ≤ blockAverage L b v := by
  simp only [blockAverage, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ => h _) (by positivity)
theorem blockAverage_sub {L : ℕ} (f g : Lattice4 → ℍ[ℝ]) (v : Lattice4) :
    blockAverage L (fun w => f w - g w) v = blockAverage L f v - blockAverage L g v := by
  simp only [blockAverage, Finset.sum_sub_distrib, smul_sub]
theorem pow_blockAverage_le {L : ℕ} (hL : Odd L) {a : Lattice4 → ℝ} (ha : ∀ w, 0 ≤ a w) (p : ℕ) (v : Lattice4) :
    blockAverage L a v ^ p ≤ blockAverage L (fun w => a w ^ p) v := by
  have hpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL.pos
  have := Real.pow_arith_mean_le_arith_mean_pow (centredCube L) (fun _ => 1 / (L : ℝ) ^ 4)
    (fun h => a (blockSite L v h)) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul, card_centredCube_real hL]; field_simp) (fun _ _ => ha _) p
  simpa [blockAverage, Finset.mul_sum] using this
theorem sum_pow_blockAverage_le {L M : ℕ} (hL : Odd L) (hM : Odd M) {a : Lattice4 → ℝ} (ha : ∀ w, 0 ≤ a w)
    (p : ℕ) :
    ∑ v ∈ centredCube M, blockAverage L a v ^ p ≤ (1 / (L : ℝ) ^ 4) * ∑ w ∈ centredCube (L * M), a w ^ p := by
  rw [← sum_blockSite hL hM, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  simpa [blockAverage] using pow_blockAverage_le hL ha p v
end Blocks
section Recursion
variable {L n : ℕ}
def iteratedBlockAverage (L : ℕ) (f : Lattice4 → ℍ[ℝ]) : ℕ → Lattice4 → ℍ[ℝ]
  | 0 => f
  | k + 1 => blockAverage L (iteratedBlockAverage L f k)
theorem blockSite_blockSite (L K : ℕ) (v h w : Lattice4) :
    blockSite K (blockSite L v h) w = blockSite (K * L) v (blockSite K h w) := by
  funext i
  simp only [blockSite]
  push_cast
  ring
theorem iteratedBlockAverage_eq (hL : Odd L) (f : Lattice4 → ℍ[ℝ]) (k : ℕ) (v : Lattice4) :
    iteratedBlockAverage L f k v =
      (1 / ((L : ℝ) ^ k) ^ 4) • ∑ w ∈ centredCube (L ^ k), f (blockSite (L ^ k) v w) := by
  induction k generalizing v with
  | zero =>
    have h1 : centredCube (L ^ 0) = {(0 : Lattice4)} := by
      ext h
      rw [mem_centredCube_iff, Finset.mem_singleton]
      constructor
      · intro hh
        funext i
        have := hh i
        simp at this
        simpa using le_antisymm this.2 this.1
      · rintro rfl i
        simp
    rw [h1, Finset.sum_singleton]
    have : blockSite (L ^ 0) v 0 = v := by
      funext i
      simp [blockSite]
    rw [this]
    simp [iteratedBlockAverage]
  | succ k ih =>
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL.pos
    have hk : Odd (L ^ k) := hL.pow
    show blockAverage L (iteratedBlockAverage L f k) v = _
    simp only [blockAverage]
    simp only [ih]
    rw [← Finset.smul_sum, smul_smul]
    have e : ∑ h ∈ centredCube L, ∑ w ∈ centredCube (L ^ k), f (blockSite (L ^ k) (blockSite L v h) w) =
        ∑ u ∈ centredCube (L ^ (k + 1)), f (blockSite (L ^ (k + 1)) v u) := by
      have := sum_blockSite (E := ℍ[ℝ]) hk hL (fun u => f (blockSite (L ^ (k + 1)) v u))
      rw [show L ^ k * L = L ^ (k + 1) from (pow_succ L k).symm] at this
      rw [← this]
      refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun w _ => ?_
      rw [blockSite_blockSite, pow_succ]
    rw [e]
    congr 1
    field_simp
    ring
theorem odd_pow (hL : Odd L) (k : ℕ) : Odd (L ^ k) := hL.pow
theorem mul_pow_sub_succ {j : ℕ} (hj : j < n) : L * L ^ (n - (j + 1)) = L ^ (n - j) := by
  rw [← pow_succ']
  congr 1
  omega
theorem sum_sq_mul_sq_le {s : Finset Lattice4} {a b : Lattice4 → ℝ} :
    ∑ v ∈ s, a v ^ 2 * b v ^ 2 ≤
      Real.sqrt (∑ v ∈ s, a v ^ 4) * Real.sqrt (∑ v ∈ s, b v ^ 4) := by
  have := Real.sum_mul_le_sqrt_mul_sqrt s (fun v => a v ^ 2) (fun v => b v ^ 2)
  have e1 : ∀ c : Lattice4 → ℝ, ∑ v ∈ s, (c v ^ 2) ^ 2 = ∑ v ∈ s, c v ^ 4 := fun c =>
    Finset.sum_congr rfl fun v _ => by ring
  simpa only [e1] using this
theorem norm_sub_average_le_of_steps (hL : Odd L) (hL5 : 5 ≤ L) (Φ : ℕ → Lattice4 → ℍ[ℝ]) (G : ℕ → Lattice4 → ℝ)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hG0 : ∀ j v, 0 ≤ G j v)
    (hstep : ∀ j, j < n → ∀ v ∈ centredCube (L ^ (n - (j + 1))),
      ‖Φ (j + 1) v - blockAverage L (Φ j) v‖ ≤ G j v * blockAverage L (fun w => ‖Φ j w‖) v)
    (hG : ∀ j, j < n → ∑ v ∈ centredCube (L ^ (n - (j + 1))), G j v ^ 4 ≤ g ^ 4) :
    ‖Φ n 0 - (1 / ((L : ℝ) ^ n) ^ 4) • ∑ w ∈ centredCube (L ^ n), Φ 0 w‖ ≤
      2 * g * (1 / (L : ℝ) ^ n) * Real.sqrt (Real.sqrt (∑ w ∈ centredCube (L ^ n), ‖Φ 0 w‖ ^ 4)) := by
  have hLr : (5 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL5
  set r : ℝ := 1 / (L : ℝ) with hr
  have hr0 : 0 < r := by positivity
  have hr5 : r ≤ 1 / 5 := by
    rw [hr]
    exact one_div_le_one_div_of_le (by norm_num) hLr
  have hr4 : 1 / (L : ℝ) ^ 4 = r ^ 4 := by
    rw [hr]
    field_simp
  set P := iteratedBlockAverage L (Φ 0) with hP
  set Q : ℕ → ℝ := fun j => ∑ v ∈ centredCube (L ^ (n - j)), ‖P j v‖ ^ 4 with hQ
  set E : ℕ → ℝ := fun j => ∑ v ∈ centredCube (L ^ (n - j)), ‖Φ j v - P j v‖ ^ 2 with hE
  have hQs : ∀ j, j < n → Q (j + 1) ≤ r ^ 4 * Q j := by
    intro j hj
    have h1 : Q (j + 1) ≤ ∑ v ∈ centredCube (L ^ (n - (j + 1))), blockAverage L (fun w => ‖P j w‖) v ^ 4 := by
      refine Finset.sum_le_sum fun v _ => ?_
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_blockAverage_le _ _) 4
    have h2 := sum_pow_blockAverage_le hL (odd_pow hL (n - (j + 1))) (a := fun w => ‖P j w‖)
      (fun _ => norm_nonneg _) 4
    rw [mul_pow_sub_succ hj, hr4] at h2
    exact h1.trans h2
  have hQj : ∀ j, j ≤ n → Q j ≤ r ^ (4 * j) * Q 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      simp
    | succ j ih =>
      intro hj
      have h1 := hQs j (by omega)
      have h2 := ih (by omega)
      calc Q (j + 1) ≤ r ^ 4 * Q j := h1
        _ ≤ r ^ 4 * (r ^ (4 * j) * Q 0) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
  set A : ℝ := Real.sqrt (Q 0) with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hEs : ∀ j, j < n → E (j + 1) ≤ 8 * r ^ 4 * E j + 2 * g ^ 2 * (r ^ 2 * (r ^ (2 * j) * A)) := by
    intro j hj
    set M := L ^ (n - (j + 1)) with hM
    have hMo : Odd M := odd_pow hL _
    set be : Lattice4 → ℝ := blockAverage L (fun w => ‖Φ j w - P j w‖) with hbe
    set bp : Lattice4 → ℝ := blockAverage L (fun w => ‖P j w‖) with hbp
    have hbe0 : ∀ v, 0 ≤ be v := blockAverage_nonneg fun _ => norm_nonneg _
    have hGle : ∀ v ∈ centredCube M, G j v ≤ 1 := by
      intro v hv
      have h1 : G j v ^ 4 ≤ g ^ 4 :=
        (Finset.single_le_sum (f := fun v => G j v ^ 4) (fun _ _ => by positivity) hv).trans (hG j hj)
      have h2 : G j v ≤ g := le_of_pow_le_pow_left₀ (by norm_num) hg0 h1
      linarith
    have hpt : ∀ v ∈ centredCube M,
        ‖Φ (j + 1) v - P (j + 1) v‖ ^ 2 ≤ 8 * be v ^ 2 + 2 * (G j v ^ 2 * bp v ^ 2) := by
      intro v hv
      have e1 : Φ (j + 1) v - P (j + 1) v =
          (Φ (j + 1) v - blockAverage L (Φ j) v) + blockAverage L (fun w => Φ j w - P j w) v := by
        rw [blockAverage_sub]
        show _ = _ + (_ - blockAverage L (iteratedBlockAverage L (Φ 0) j) v)
        show Φ (j + 1) v - blockAverage L (iteratedBlockAverage L (Φ 0) j) v = _
        abel
      have e2 : ‖blockAverage L (fun w => Φ j w - P j w) v‖ ≤ be v := norm_blockAverage_le _ _
      have e3 : blockAverage L (fun w => ‖Φ j w‖) v ≤ bp v + be v := by
        rw [hbe, hbp, ← blockAverage_add]
        refine blockAverage_mono (fun w => ?_) v
        have := norm_add_le (P j w) (Φ j w - P j w)
        rwa [add_sub_cancel] at this
      have e4 := hstep j hj v hv
      have hG1 := hGle v hv
      have hG0' := hG0 j v
      have e5 : ‖Φ (j + 1) v - P (j + 1) v‖ ≤ 2 * be v + G j v * bp v := by
        rw [e1]
        refine (norm_add_le _ _).trans ?_
        have : G j v * blockAverage L (fun w => ‖Φ j w‖) v ≤ G j v * (bp v + be v) :=
          mul_le_mul_of_nonneg_left e3 hG0'
        have h6 : G j v * be v ≤ be v := by nlinarith [hbe0 v]
        nlinarith
      have h7 : (2 * be v + G j v * bp v) ^ 2 ≤ 8 * be v ^ 2 + 2 * (G j v ^ 2 * bp v ^ 2) := by
        nlinarith [sq_nonneg (2 * be v - G j v * bp v)]
      exact (pow_le_pow_left₀ (norm_nonneg _) e5 2).trans h7
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    have hb2 := sum_pow_blockAverage_le hL hMo (a := fun w => ‖Φ j w - P j w‖) (fun _ => norm_nonneg _) 2
    have hb4 := sum_pow_blockAverage_le hL hMo (a := fun w => ‖P j w‖) (fun _ => norm_nonneg _) 4
    rw [hM, mul_pow_sub_succ hj, hr4] at hb2 hb4
    have hc := sum_sq_mul_sq_le (s := centredCube M) (a := G j) (b := bp)
    have hs1 : Real.sqrt (∑ v ∈ centredCube M, G j v ^ 4) ≤ g ^ 2 := by
      refine (Real.sqrt_le_sqrt (hG j hj)).trans ?_
      rw [show g ^ 4 = (g ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have hs2 : Real.sqrt (∑ v ∈ centredCube M, bp v ^ 4) ≤ r ^ 2 * (r ^ (2 * j) * A) := by
      have h1 : ∑ v ∈ centredCube M, bp v ^ 4 ≤ r ^ 4 * (r ^ (4 * j) * Q 0) :=
        hb4.trans (mul_le_mul_of_nonneg_left (hQj j hj.le) (by positivity))
      refine (Real.sqrt_le_sqrt h1).trans ?_
      rw [show r ^ 4 * (r ^ (4 * j) * Q 0) = (r ^ 2 * r ^ (2 * j)) ^ 2 * Q 0 by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), hA, mul_assoc]
    have hfin : ∑ v ∈ centredCube M, G j v ^ 2 * bp v ^ 2 ≤ g ^ 2 * (r ^ 2 * (r ^ (2 * j) * A)) :=
      hc.trans (mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (by positivity))
    calc E (j + 1) ≤ 8 * ∑ v ∈ centredCube M, be v ^ 2 + 2 * ∑ v ∈ centredCube M, G j v ^ 2 * bp v ^ 2 := hsum
      _ ≤ 8 * (r ^ 4 * E j) + 2 * (g ^ 2 * (r ^ 2 * (r ^ (2 * j) * A))) := by
          have : ∑ v ∈ centredCube M, be v ^ 2 ≤ r ^ 4 * E j := hb2
          linarith
      _ = _ := by ring
  have hE : ∀ j, j ≤ n → E j ≤ 4 * g ^ 2 * (r ^ (2 * j) * A) := by
    intro j
    induction j with
    | zero =>
      intro _
      have : E 0 = 0 := by
        refine Finset.sum_eq_zero fun v _ => ?_
        simp [hP, iteratedBlockAverage]
      rw [this]
      positivity
    | succ j ih =>
      intro hj
      have h1 := hEs j (by omega)
      have h2 := ih (by omega)
      have h3 : 32 * r ^ 2 ≤ 2 := by nlinarith
      calc E (j + 1) ≤ 8 * r ^ 4 * (4 * g ^ 2 * (r ^ (2 * j) * A)) +
            2 * g ^ 2 * (r ^ 2 * (r ^ (2 * j) * A)) := by
            have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 8 * r ^ 4 by positivity)
            linarith
        _ = (32 * r ^ 2 + 2) * (r ^ 2 * (g ^ 2 * (r ^ (2 * j) * A))) := by ring
        _ ≤ 4 * (r ^ 2 * (g ^ 2 * (r ^ (2 * j) * A))) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring
  have h0 : (0 : Lattice4) ∈ centredCube (L ^ (n - n)) := by
    rw [mem_centredCube_iff]
    intro i
    simp
  have hn := hE n le_rfl
  have hsingle : ‖Φ n 0 - P n 0‖ ^ 2 ≤ E n :=
    Finset.single_le_sum (f := fun v => ‖Φ n v - P n v‖ ^ 2) (fun _ _ => by positivity) h0
  have hPn : P n 0 = (1 / ((L : ℝ) ^ n) ^ 4) • ∑ w ∈ centredCube (L ^ n), Φ 0 w := by
    rw [hP, iteratedBlockAverage_eq hL]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    congr 1
    funext i
    simp [blockSite]
  rw [← hPn]
  have hfin : ‖Φ n 0 - P n 0‖ ^ 2 ≤ (2 * g * r ^ n * Real.sqrt A) ^ 2 := by
    refine (hsingle.trans hn).trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hA0]
    ring
  have hres := abs_le_of_sq_le_sq' hfin (by positivity)
  have e : (1 / (L : ℝ) ^ n) = r ^ n := by
    rw [hr, one_div_pow]
  have hQ0' : Q 0 = ∑ w ∈ centredCube (L ^ n), ‖Φ 0 w‖ ^ 4 := by
    simp [hQ, hP, iteratedBlockAverage]
  rw [e, ← hQ0', ← hA]
  exact hres.2
end Recursion
section OneStep
theorem coe_inv_mul_coe (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_inv_mul_coe <;> assumption
theorem adjointAction_mul (a b : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction (a * b) w = adjointAction a (adjointAction b w) := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_mul <;> assumption
theorem adjointAction_inv_cancel (g : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction g (adjointAction g⁻¹ w) = w := by
  rw [← adjointAction_mul, mul_inv_cancel]
  simp [adjointAction]
theorem adjointAction_sum {ι : Type} (g : UnitQuaternion) (T : Finset ι) (f : ι → ℍ[ℝ]) :
    adjointAction g (∑ i ∈ T, f i) = ∑ i ∈ T, adjointAction g (f i) := by
  simp only [adjointAction, Finset.mul_sum, Finset.sum_mul]
theorem adjointAction_smul (g : UnitQuaternion) (c : ℝ) (w : ℍ[ℝ]) :
    adjointAction g (c • w) = c • adjointAction g w := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem norm_adjointAction_sub_self_le (g : UnitQuaternion) (w : ℍ[ℝ]) :
    ‖adjointAction g w - w‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ * ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction_sub_le <;> assumption
theorem norm_transportedAverage_sub_le {ι : Type} (T : Finset ι) {w δ : ℝ} (hw : 0 ≤ w)
    (hT : w * (T.card : ℝ) = 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (A B : ι → UnitQuaternion) (v : ι → ℍ[ℝ])
    (hv : ∀ i ∈ T, (v i).re = 0)
    (ha : ∀ i ∈ T, ‖((A i * (B i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ δ) :
    ‖‖w • ∑ i ∈ T, ((A i * (B i)⁻¹ : UnitQuaternion) : ℍ[ℝ])‖⁻¹ •
        pureComponent ((((polarUnit (w • ∑ i ∈ T, ((A i * (B i)⁻¹ : UnitQuaternion) : ℍ[ℝ])))⁻¹ :
            UnitQuaternion) : ℍ[ℝ]) *
          (w • ∑ i ∈ T, (A i : ℍ[ℝ]) * v i * (((B i)⁻¹ : UnitQuaternion) : ℍ[ℝ]))) -
      w • ∑ i ∈ T, adjointAction (B i) (v i)‖ ≤ 12 * δ * (w * ∑ i ∈ T, ‖v i‖) := by
  set μ : ℍ[ℝ] := w • ∑ i ∈ T, ((A i * (B i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hμdef
  set m : ℍ[ℝ] := w • ∑ i ∈ T, adjointAction (B i) (v i) with hm
  set S : ℝ := w * ∑ i ∈ T, ‖v i‖ with hS
  have hμ : ‖μ - 1‖ ≤ δ := by
    have e : μ - 1 = w • ∑ i ∈ T, (((A i * (B i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) := by
      rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hT,
        one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
    calc w * ‖∑ i ∈ T, (((A i * (B i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1)‖ ≤ w * ∑ _i ∈ T, δ :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum ha)) hw
      _ = δ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, hT, one_mul]
  set r : ℝ := ‖μ‖ with hr
  have hr1 : |r - 1| ≤ δ := by
    have := abs_norm_sub_norm_le μ 1
    rw [norm_one] at this
    exact this.trans hμ
  have hrlo : 1 / 2 ≤ r := by
    have := (abs_le.1 hr1).1
    linarith
  have hrpos : 0 < r := by linarith
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [hr, h, norm_zero] at hrlo
    linarith
  have hrinv : r⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hrpos (by norm_num)]
    linarith
  have hrinv0 : 0 ≤ r⁻¹ := by positivity
  have hrinv1 : |r⁻¹ - 1| ≤ 2 * δ := by
    have e : r⁻¹ - 1 = r⁻¹ * (1 - r) := by
      field_simp
    rw [e, abs_mul, abs_of_nonneg hrinv0, abs_sub_comm]
    exact mul_le_mul hrinv hr1 (abs_nonneg _) (by norm_num)
  set k : UnitQuaternion := polarUnit μ with hk
  have hkc : (k : ℍ[ℝ]) = r⁻¹ • μ := coe_polarUnit hμ0
  have hk1 : ‖(k : ℍ[ℝ]) - 1‖ ≤ 4 * δ := by
    have e : (k : ℍ[ℝ]) - 1 = r⁻¹ • (μ - 1) + (r⁻¹ - 1) • (1 : ℍ[ℝ]) := by
      rw [hkc, smul_sub, sub_smul, one_smul]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hrinv0]
    have := mul_le_mul hrinv hμ (norm_nonneg _) (by norm_num)
    linarith
  have hkinv : ‖((k⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * δ := by
    rw [norm_coe_inv_sub_one]
    exact hk1
  have hmul : ∀ i, (A i : ℍ[ℝ]) * v i * (((B i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      ((A i * (B i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * adjointAction (B i) (v i) := by
    intro i
    calc (A i : ℍ[ℝ]) * v i * (((B i)⁻¹ : UnitQuaternion) : ℍ[ℝ])
        = (A i : ℍ[ℝ]) * ((((B i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (B i : ℍ[ℝ])) * v i *
            (((B i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
          rw [coe_inv_mul_coe, mul_one]
      _ = _ := by
          simp only [adjointAction, Submonoid.coe_mul, mul_assoc]
  set err : ℍ[ℝ] := w • ∑ i ∈ T,
    ((((k⁻¹ * (A i * (B i)⁻¹) : UnitQuaternion) : ℍ[ℝ]) - 1) * adjointAction (B i) (v i)) with herr
  have hinner : ((k⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
      (w • ∑ i ∈ T, (A i : ℍ[ℝ]) * v i * (((B i)⁻¹ : UnitQuaternion) : ℍ[ℝ])) = m + err := by
    rw [hm, herr, ← smul_add, ← Finset.sum_add_distrib, mul_smul_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e0 : ((k⁻¹ * (A i * (B i)⁻¹) : UnitQuaternion) : ℍ[ℝ]) =
        ((k⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((A i * (B i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := rfl
    rw [hmul i, sub_mul, one_mul, add_sub_cancel, e0, mul_assoc]
  have hmpure : pureComponent m = m := by
    rw [hm, pureComponent_smul, pureComponent_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    exact pureComponent_of_re_eq_zero (re_adjointAction _ (hv i hi))
  have hnorm : ∀ i, ‖adjointAction (B i) (v i)‖ = ‖v i‖ := fun i => norm_adjointAction _ _
  have hmS : ‖m‖ ≤ S := by
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) hw
    exact Finset.sum_congr rfl fun i _ => hnorm i
  have herrS : ‖err‖ ≤ 5 * δ * S := by
    rw [herr, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
    have h1 : ‖∑ i ∈ T, ((((k⁻¹ * (A i * (B i)⁻¹) : UnitQuaternion) : ℍ[ℝ]) - 1) *
          adjointAction (B i) (v i))‖ ≤ ∑ i ∈ T, 5 * δ * ‖v i‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      rw [norm_mul, hnorm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := norm_coe_mul_sub_one_le k⁻¹ (A i * (B i)⁻¹)
      have h2 := ha i hi
      linarith
    rw [← Finset.mul_sum] at h1
    calc w * _ ≤ w * (5 * δ * ∑ i ∈ T, ‖v i‖) := mul_le_mul_of_nonneg_left h1 hw
      _ = _ := by rw [hS]; ring
  rw [hinner, pureComponent_add, hmpure]
  have e : r⁻¹ • (m + pureComponent err) - m = (r⁻¹ - 1) • m + r⁻¹ • pureComponent err := by
    rw [smul_add, sub_smul, one_smul]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul (r⁻¹ - 1) m, norm_smul r⁻¹ (pureComponent err), Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hrinv0]
  have h1 : |r⁻¹ - 1| * ‖m‖ ≤ 2 * δ * S := mul_le_mul hrinv1 hmS (norm_nonneg _) (by positivity)
  have h2 : r⁻¹ * ‖pureComponent err‖ ≤ 2 * (5 * δ * S) :=
    mul_le_mul hrinv ((norm_pureComponent_le _).trans herrS) (norm_nonneg _) (by norm_num)
  linarith
end OneStep
section Frames
variable {F : BlockFrame}
theorem refineSite_cellCentre (j : ℕ) (hj : j + 1 ≤ F.top) (z : F.Cell) :
    refineSite (cellCentre (j + 1) z) = cellCentre j z := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.refineSite_cellCentre <;> assumption
def cellSite (y : F.Cell) (j : ℕ) (v : Lattice4) : F.Site j := cellCentre j y + siteOfCoords j v
theorem refineSite_cellSite_add {j : ℕ} (hj : j + 1 ≤ F.top) (y : F.Cell) (v h : Lattice4) :
    refineSite (cellSite y (j + 1) v) + siteOfCoords j h = cellSite y j (blockSite F.blockSide v h) := by
  simp only [cellSite]
  rw [refineSite_add j hj, refineSite_cellCentre j hj, add_assoc, ← siteOfCoords_add]
  rfl
theorem enclosingCell_cellSite (hL : Odd F.blockSide) {j : ℕ} (z : F.Cell) {h : Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) : enclosingCell (cellSite z j h) = z := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_cellCentre_add <;> assumption
theorem cellSite_mem {S : Finset F.Cell} {y : F.Cell} (hy : y ∈ S) {j : ℕ} {v : Lattice4}
    (hv : v ∈ centredCube (F.blockSide ^ (F.top - j))) : cellSite y j v ∈ sitesOfCells S j :=
  mem_sitesOfCells.2 ⟨y, hy, v, hv, rfl⟩
theorem cellSite_injective (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide) (y : F.Cell) (j : ℕ)
    {a b : Lattice4} (ha : a ∈ centredCube (F.blockSide ^ (F.top - j)))
    (hb : b ∈ centredCube (F.blockSide ^ (F.top - j))) (h : cellSite y j a = cellSite y j b) :
    a = b := by
  have h1 : (siteOfCoords j a : F.Site j) = siteOfCoords j b := add_left_cancel h
  funext i
  have h2 : ((a i : ℤ) : ZMod (F.period j i)) = ((b i : ℤ) : ZMod (F.period j i)) := congrFun h1 i
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h2
  have a1 := ((mem_centredCube_iff _ a).1 ha) i
  have b1 := ((mem_centredCube_iff _ b).1 hb) i
  have hMpos : (0 : ℤ) < ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) := by
    have := hL.pos
    positivity
  rcases hamb with h0 | h0
  · have : F.period j i = 0 := by simp [BlockFrame.period, h0 i]
    rw [this] at hd
    have := zero_dvd_iff.1 (by simpa using hd)
    omega
  · have hs := h0 i
    have hper : ((F.period j i : ℕ) : ℤ) = (F.extent i : ℤ) * ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) := by
      simp [BlockFrame.period]
    have hbig : ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) * 64 ≤ ((F.period j i : ℕ) : ℤ) := by
      rw [hper]
      nlinarith
    have hz := Int.eq_zero_of_abs_lt_dvd hd (by
      rw [abs_lt]
      constructor <;> omega)
    omega
theorem stepDisplacement_eq (j : ℕ) (st : PathStep) :
    stepDisplacement (F := F) j st = siteOfCoords j (FlatPairing.stepDisplacement st) := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords <;> assumption
theorem pathHolonomy_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j) (x0 : F.Site j)
    (l : List PathStep) :
    ∀ u : Lattice4, pathHolonomy (gaugeTransform γ X) (x0 + siteOfCoords j u) l =
      γ (x0 + siteOfCoords j u) * pathHolonomy X (x0 + siteOfCoords j u) l *
        (γ (x0 + siteOfCoords j (endpoint u l)))⁻¹ := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.pathHolonomy_gaugeTransform <;> assumption
theorem norm_linkValue_ratio_le {j : ℕ} {X R : F.GaugeField j} {D : Set (F.Site j)} {ε : ℝ}
    (hb : ∀ x i, x ∈ D → x + unitStep j i ∈ D → ‖((X x i * (R x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    {x : F.Site j} {st : PathStep} (hx : x ∈ D) (hy : x + stepDisplacement j st ∈ D) :
    ‖((linkValue X x st * (linkValue R x st)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε := by
  rcases st with ⟨i, b⟩
  cases b
  · simp only [linkValue, Bool.false_eq_true, if_false]
    have e : x + stepDisplacement j (i, false) = x - unitStep j i := by
      simp [stepDisplacement, sub_eq_add_neg]
    rw [e] at hy
    have h1 := hb _ i hy (by rw [sub_add_cancel]; exact hx)
    set A := X (x - unitStep j i) i
    set B := R (x - unitStep j i) i
    have e2 : A⁻¹ * (B⁻¹)⁻¹ = A⁻¹ * (A * B⁻¹)⁻¹ * (A⁻¹)⁻¹ := by group
    rw [e2, norm_coe_conj_sub_one, norm_coe_inv_sub_one]
    exact h1
  · simp only [linkValue, if_true]
    have e : x + stepDisplacement j (i, true) = x + unitStep j i := by simp [stepDisplacement]
    rw [e] at hy
    exact hb _ i hx hy
theorem norm_pathHolonomy_ratio_le {j : ℕ} {X R : F.GaugeField j} {D : Set (F.Site j)} {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ x i, x ∈ D → x + unitStep j i ∈ D → ‖((X x i * (R x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (x0 : F.Site j) :
    ∀ (l : List PathStep) (v : Lattice4), AllAlong (fun v => x0 + siteOfCoords j v ∈ D) v l →
      ‖((pathHolonomy X (x0 + siteOfCoords j v) l * (pathHolonomy R (x0 + siteOfCoords j v) l)⁻¹ :
          UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * ε := by
  intro l
  induction l with
  | nil =>
    intro v _
    simp [pathHolonomy]
  | cons st r ih =>
    intro v hp
    have hnext : x0 + siteOfCoords j v + stepDisplacement j st =
        x0 + siteOfCoords j (v + FlatPairing.stepDisplacement st) := by
      rw [stepDisplacement_eq, add_assoc, ← siteOfCoords_add]
    have hv : x0 + siteOfCoords j v ∈ D := hp.1
    have hw : x0 + siteOfCoords j v + stepDisplacement j st ∈ D := by
      rw [hnext]
      exact allAlong_head hp.2
    have h1 := norm_linkValue_ratio_le hb hv hw
    have h2 := ih _ hp.2
    simp only [pathHolonomy]
    rw [hnext]
    set a := linkValue X (x0 + siteOfCoords j v) st
    set b := linkValue R (x0 + siteOfCoords j v) st
    set P := pathHolonomy X (x0 + siteOfCoords j (v + FlatPairing.stepDisplacement st)) r
    set Q := pathHolonomy R (x0 + siteOfCoords j (v + FlatPairing.stepDisplacement st)) r
    have e : a * P * (b * Q)⁻¹ = (a * b⁻¹) * (b * (P * Q⁻¹) * b⁻¹) := by group
    rw [e]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    rw [norm_coe_conj_sub_one]
    simp only [List.length_cons]
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    linarith
theorem pathHolonomy_one {j : ℕ} (l : List PathStep) (x : F.Site j) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) x l = 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathHolonomy_one <;> assumption
theorem norm_pathHolonomy_sub_one_le {j : ℕ} {Y : F.GaugeField j} {D : Set (F.Site j)} {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ x i, x ∈ D → x + unitStep j i ∈ D → ‖((Y x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε) (x0 : F.Site j)
    (l : List PathStep) (v : Lattice4) (hp : AllAlong (fun v => x0 + siteOfCoords j v ∈ D) v l) :
    ‖((pathHolonomy Y (x0 + siteOfCoords j v) l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * ε := by
  have := norm_pathHolonomy_ratio_le (X := Y) (R := fun _ _ => (1 : UnitQuaternion)) hε
    (fun x i h1 h2 => by simpa using hb x i h1 h2) x0 l v hp
  simpa [pathHolonomy_one] using this
theorem length_axisPath_le {h : Lattice4} (π : Equiv.Perm (Fin 4)) (hh : h ∈ centredCube F.blockSide)
    (hL : 1 ≤ F.blockSide) : (axisPath h π).length ≤ 5 * F.blockSide := by
  have hlen : ∀ μ, (h μ).natAbs ≤ (F.blockSide - 1) / 2 := by
    intro μ
    have h1 := ((mem_centredCube_iff F.blockSide h).1 hh) μ
    omega
  have h0 := hlen (π 0)
  have h1 := hlen (π 1)
  have h2 := hlen (π 2)
  have h3 := hlen (π 3)
  have hl := length_axisPath h π
  omega
theorem mem_centredCube_of_betweenOrigin {L : ℕ} {h v : Lattice4} (hh : h ∈ centredCube L) (hL : 1 ≤ L)
    (hv : BetweenOrigin h v) : v ∈ centredCube L := by
  rw [mem_centredCube_iff]
  intro μ
  have h1 := ((mem_centredCube_iff L h).1 hh) μ
  have h2 := hv μ
  have hk : (0 : ℤ) ≤ ((L : ℤ) - 1) / 2 := by omega
  have a1 : min 0 (h μ) ≥ -(((L : ℤ) - 1) / 2) := le_min (by omega) h1.1
  have a2 : max 0 (h μ) ≤ ((L : ℤ) - 1) / 2 := max_le hk h1.2
  constructor <;> omega
def blockSites (y : F.Cell) (j : ℕ) (v : Lattice4) : Set (F.Site j) :=
  {x | ∃ h ∈ centredCube F.blockSide, x = cellSite y j (blockSite F.blockSide v h)}
def framedGenerator (S : Finset F.Cell) (V : F.GaugeField F.top) (U : ChainChart F)
    (ξ : F.Site 0 → imaginaryQuaternions) (y : F.Cell) (j : ℕ) (v : Lattice4) : ℍ[ℝ] :=
  adjointAction (frameChange S V y (baseSite (cellSite y j v)))⁻¹
    (gaugeGeneratorAtLevel (referenceFieldChain S V) U ξ j (cellSite y j v))
theorem re_gaugeGeneratorAtLevel (R : F.FieldChain) (U : ChainChart F) (ξ : F.Site 0 → imaginaryQuaternions)
    (j : ℕ) (x : F.Site j) : (gaugeGeneratorAtLevel R U ξ j x).re = 0 := by
  cases j with
  | zero => exact (ξ x).2
  | succ j =>
    simp only [gaugeGeneratorAtLevel]
    simp [re_pureComponent]
theorem blockAverage_eq_pairs {E : Type} [AddCommGroup E] [Module ℝ E] {L : ℕ} (hL : 0 < L)
    (f : Lattice4 → E) (v : Lattice4) :
    blockAverage L f v = (1 / (24 * (L : ℝ) ^ 4)) •
      ∑ p ∈ centredCube L ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4))), f (blockSite L v p.1) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Finset.smul_sum, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, blockAverage]
  congr 1
  rw [show Nat.factorial 4 = 24 from rfl]
  push_cast
  field_simp
theorem norm_framedGenerator_step_le (hodd : Odd F.blockSide) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (U : ChainChart F) (ξ : F.Site 0 → imaginaryQuaternions) (y : F.Cell) {j : ℕ} (hj : j < F.top)
    (v : Lattice4) {ε κ : ℝ} (hε : 0 ≤ ε) (hκ : 0 ≤ κ)
    (hsmall : 5 * (F.blockSide : ℝ) * ε ≤ 1 / 2)
    (hX : ∀ x i, x ∈ blockSites y j v → x + unitStep j i ∈ blockSites y j v →
      ‖((chartField (referenceFieldChain S V) U j x i * (referenceFieldChain S V j x i)⁻¹ : UnitQuaternion) :
        ℍ[ℝ]) - 1‖ ≤ ε)
    (hY : ∀ x i, x ∈ blockSites y j v → x + unitStep j i ∈ blockSites y j v →
      ‖((referenceInPatchFrame S V y j x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ κ) :
    ‖framedGenerator S V U ξ y (j + 1) v - blockAverage F.blockSide (framedGenerator S V U ξ y j) v‖ ≤
      (12 * (5 * (F.blockSide : ℝ) * ε) + 2 * (5 * (F.blockSide : ℝ) * κ)) *
        blockAverage F.blockSide (fun w => ‖framedGenerator S V U ξ y j w‖) v := by
  classical
  have hLpos : 0 < F.blockSide := hodd.pos
  set R := referenceFieldChain S V with hR
  set X := chartField R U j with hXdef
  set y' := cellSite y (j + 1) v with hy'
  set x0 := refineSite y' with hx0
  have hsite : ∀ h, x0 + siteOfCoords j h = cellSite y j (blockSite F.blockSide v h) := fun h =>
    refineSite_cellSite_add hj y v h
  set T : Finset (Lattice4 × Equiv.Perm (Fin 4)) := centredCube F.blockSide ×ˢ Finset.univ with hT
  set w : ℝ := 1 / (24 * (F.blockSide : ℝ) ^ 4) with hw
  have hw0 : 0 ≤ w := by positivity
  have hcard : w * (T.card : ℝ) = 1 := by
    rw [hT, Finset.card_product, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    push_cast
    rw [card_centredCube_real hodd, show ((Nat.factorial 4 : ℕ) : ℝ) = 24 by norm_num [Nat.factorial], hw]
    field_simp
  set A : Lattice4 × Equiv.Perm (Fin 4) → UnitQuaternion := fun p => pathHolonomy X x0 (axisPath p.1 p.2) with hA
  set B : Lattice4 × Equiv.Perm (Fin 4) → UnitQuaternion := fun p => pathHolonomy (R j) x0 (axisPath p.1 p.2)
    with hB
  set vv : Lattice4 × Equiv.Perm (Fin 4) → ℍ[ℝ] := fun p => gaugeGeneratorAtLevel R U ξ j (x0 + siteOfCoords j p.1)
    with hvv
  have hbase : x0 + siteOfCoords j (0 : Lattice4) = x0 := by rw [siteOfCoords_zero, add_zero]
  have hpath : ∀ p ∈ T, AllAlong (fun u => x0 + siteOfCoords j u ∈ blockSites y j v) 0 (axisPath p.1 p.2) := by
    intro p hp
    have hh : p.1 ∈ centredCube F.blockSide := (Finset.mem_product.1 hp).1
    refine allAlong_mono (fun u hu => ?_) (axisPath_spec p.1 p.2).1
    exact ⟨u, mem_centredCube_of_betweenOrigin hh hLpos hu, hsite u⟩
  have hlen : ∀ p ∈ T, ((axisPath p.1 p.2).length : ℝ) ≤ 5 * (F.blockSide : ℝ) := by
    intro p hp
    have hh : p.1 ∈ centredCube F.blockSide := (Finset.mem_product.1 hp).1
    exact_mod_cast length_axisPath_le p.2 hh hLpos
  have ha : ∀ p ∈ T, ‖((A p * (B p)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 5 * (F.blockSide : ℝ) * ε := by
    intro p hp
    have h1 := norm_pathHolonomy_ratio_le hε hX x0 _ 0 (hpath p hp)
    rw [hbase] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (hlen p hp) hε)
  have hT' : ∀ p ∈ T,
      ‖((pathHolonomy (referenceInPatchFrame S V y j) x0 (axisPath p.1 p.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        5 * (F.blockSide : ℝ) * κ := by
    intro p hp
    have h1 := norm_pathHolonomy_sub_one_le hκ hY x0 _ 0 (hpath p hp)
    rw [hbase] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (hlen p hp) hκ)
  have key := norm_transportedAverage_sub_le T hw0 hcard (by positivity) hsmall A B vv
    (fun p _ => re_gaugeGeneratorAtLevel _ _ _ _ _) ha
  have e1 : relativePathAverage X (R j) y' = w • ∑ p ∈ T, ((A p * (B p)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    simp only [relativePathAverage]
    rw [hT, Finset.sum_product]
  have e2 : ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy X (refineSite y') (axisPath h π) : UnitQuaternion) : ℍ[ℝ]) *
          gaugeGeneratorAtLevel R U ξ j (refineSite y' + siteOfCoords j h) *
          (((pathHolonomy (R j) (refineSite y') (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      ∑ p ∈ T, (A p : ℍ[ℝ]) * vv p * (((B p)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    rw [hT, Finset.sum_product]
  have egen : gaugeGeneratorAtLevel R U ξ (j + 1) y' =
      ‖w • ∑ p ∈ T, ((A p * (B p)⁻¹ : UnitQuaternion) : ℍ[ℝ])‖⁻¹ •
        pureComponent ((((polarUnit (w • ∑ p ∈ T, ((A p * (B p)⁻¹ : UnitQuaternion) : ℍ[ℝ])))⁻¹ :
            UnitQuaternion) : ℍ[ℝ]) *
          (w • ∑ p ∈ T, (A p : ℍ[ℝ]) * vv p * (((B p)⁻¹ : UnitQuaternion) : ℍ[ℝ]))) := by
    rw [← e1, ← e2]
    rfl
  rw [← egen] at key
  set f0 := frameChange S V y (baseSite y') with hf0
  set Ph : Lattice4 × Equiv.Perm (Fin 4) → ℍ[ℝ] := fun p => framedGenerator S V U ξ y j (blockSite F.blockSide v p.1)
    with hPh
  have hnorm : ∀ p, ‖vv p‖ = ‖Ph p‖ := by
    intro p
    simp only [hvv, hPh, framedGenerator, norm_adjointAction, hsite]
    rfl
  have hturn : ∀ p ∈ T, ‖adjointAction f0⁻¹ (adjointAction (B p) (vv p)) - Ph p‖ ≤
      2 * (5 * (F.blockSide : ℝ) * κ) * ‖Ph p‖ := by
    intro p hp
    set l := axisPath p.1 p.2 with hl
    have hend : endpoint 0 l = p.1 := (axisPath_spec p.1 p.2).2
    have hg := pathHolonomy_gaugeTransform (fun x : F.Site j => (frameChange S V y (baseSite x))⁻¹) (R j) x0 l 0
    rw [hbase, hend, hsite p.1, inv_inv] at hg
    have htb : baseSite x0 = baseSite y' := baseSite_refineSite j hj y'
    rw [htb] at hg
    have hc : adjointAction f0⁻¹ (adjointAction (B p) (vv p)) =
        adjointAction (pathHolonomy (referenceInPatchFrame S V y j) x0 l) (Ph p) := by
      have e3 : pathHolonomy (referenceInPatchFrame S V y j) x0 l =
          f0⁻¹ * B p * frameChange S V y (baseSite (cellSite y j (blockSite F.blockSide v p.1))) := hg
      rw [e3]
      simp only [hPh, framedGenerator]
      rw [adjointAction_mul, adjointAction_inv_cancel, adjointAction_mul]
      simp only [hvv, hsite]
      rfl
    rw [hc]
    refine (norm_adjointAction_sub_self_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hT' p hp) (by norm_num)) (norm_nonneg _)
  have hgy : framedGenerator S V U ξ y (j + 1) v = adjointAction f0⁻¹ (gaugeGeneratorAtLevel R U ξ (j + 1) y') := rfl
  rw [hgy, blockAverage_eq_pairs hLpos, blockAverage_eq_pairs hLpos]
  set S0 : ℝ := w * ∑ p ∈ T, ‖Ph p‖ with hS0
  have hsplit : adjointAction f0⁻¹ (gaugeGeneratorAtLevel R U ξ (j + 1) y') - w • ∑ p ∈ T, Ph p =
      adjointAction f0⁻¹ (gaugeGeneratorAtLevel R U ξ (j + 1) y' - w • ∑ p ∈ T, adjointAction (B p) (vv p)) +
        w • ∑ p ∈ T, (adjointAction f0⁻¹ (adjointAction (B p) (vv p)) - Ph p) := by
    rw [adjointAction_sub, adjointAction_smul, adjointAction_sum, Finset.sum_sub_distrib, smul_sub]
    abel
  have hS1 : w * ∑ p ∈ T, ‖vv p‖ = S0 := by
    rw [hS0]
    congr 1
    exact Finset.sum_congr rfl fun p _ => hnorm p
  rw [hS1] at key
  have hsec : ‖w • ∑ p ∈ T, (adjointAction f0⁻¹ (adjointAction (B p) (vv p)) - Ph p)‖ ≤
      2 * (5 * (F.blockSide : ℝ) * κ) * S0 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0]
    calc w * ‖∑ p ∈ T, (adjointAction f0⁻¹ (adjointAction (B p) (vv p)) - Ph p)‖
        ≤ w * ∑ p ∈ T, 2 * (5 * (F.blockSide : ℝ) * κ) * ‖Ph p‖ :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hturn)) hw0
      _ = _ := by
          rw [← Finset.mul_sum, hS0]
          ring
  show ‖adjointAction f0⁻¹ (gaugeGeneratorAtLevel R U ξ (j + 1) y') - w • ∑ p ∈ T, Ph p‖ ≤
    (12 * (5 * (F.blockSide : ℝ) * ε) + 2 * (5 * (F.blockSide : ℝ) * κ)) * (w • ∑ p ∈ T, ‖Ph p‖)
  rw [hsplit, smul_eq_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_adjointAction, add_mul]
  linarith
end Frames
section Sizes
variable {F : BlockFrame}
theorem le_sqrt_sqrt_of_pow_four_le {a b : ℝ} (h : a ^ 4 ≤ b) : a ≤ Real.sqrt (Real.sqrt b) := by
  refine Real.le_sqrt_of_sq_le (Real.le_sqrt_of_sq_le ?_)
  calc (a ^ 2) ^ 2 = a ^ 4 := by ring
    _ ≤ b := h
theorem sqrt_sqrt_pow_four {b : ℝ} (hb : 0 ≤ b) : Real.sqrt (Real.sqrt b) ^ 4 = b := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sqrt_sqrt_pow_four <;> assumption
theorem add_pow_four_le_eight_mul {a b : ℝ} : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  have h1 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have h2 : (a ^ 2 + b ^ 2) ^ 2 ≤ 2 * (a ^ 4 + b ^ 4) := by nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  calc (a + b) ^ 4 = ((a + b) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (a ^ 2 + b ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    _ = 4 * (a ^ 2 + b ^ 2) ^ 2 := by ring
    _ ≤ 4 * (2 * (a ^ 4 + b ^ 4)) := by linarith
    _ = _ := by ring
def bondNorm (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (y : F.Cell) (j : ℕ) (u : Lattice4)
    (i : Fin 4) : ℝ := by
  classical exact
    if (cellSite y j u, i) ∈ bondsOver S {y} j then ‖levelCoordinate R U j (cellSite y j u) i‖ else 0
def blockDeviation (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (y : F.Cell) (j : ℕ)
    (v : Lattice4) : ℝ :=
  Real.sqrt (Real.sqrt (∑ h ∈ centredCube F.blockSide, ∑ i : Fin 4,
    bondNorm S R U y j (blockSite F.blockSide v h) i ^ 4))
theorem blockDeviation_nonneg (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (y : F.Cell) (j : ℕ)
    (v : Lattice4) : 0 ≤ blockDeviation S R U y j v := Real.sqrt_nonneg _
theorem blockDeviation_pow_four (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (y : F.Cell) (j : ℕ)
    (v : Lattice4) :
    blockDeviation S R U y j v ^ 4 =
      ∑ h ∈ centredCube F.blockSide, ∑ i : Fin 4, bondNorm S R U y j (blockSite F.blockSide v h) i ^ 4 :=
  sqrt_sqrt_pow_four (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
theorem blockSite_mem_levelCube {j : ℕ} (hj : j < F.top) {v h : Lattice4} (hodd : Odd F.blockSide)
    (hv : v ∈ centredCube (F.blockSide ^ (F.top - (j + 1)))) (hh : h ∈ centredCube F.blockSide) :
    blockSite F.blockSide v h ∈ centredCube (F.blockSide ^ (F.top - j)) := by
  have := blockSite_mem_centredCube hodd (hodd.pow (n := F.top - (j + 1))) hv hh
  rwa [mul_pow_sub_succ hj] at this
theorem exists_bond_of_mem_blockSites (hodd : Odd F.blockSide) {S : Finset F.Cell} {y : F.Cell} (hy : y ∈ S)
    {j : ℕ} (hj : j < F.top) {v : Lattice4} (hv : v ∈ centredCube (F.blockSide ^ (F.top - (j + 1))))
    {x : F.Site j} {i : Fin 4} (hx : x ∈ blockSites y j v) (hx' : x + unitStep j i ∈ blockSites y j v) :
    ∃ u ∈ centredCube (F.blockSide ^ (F.top - j)), ∃ h ∈ centredCube F.blockSide,
      u = blockSite F.blockSide v h ∧ x = cellSite y j u ∧
      (cellSite y j u, i) ∈ bondsOver S {y} j ∧ (x, i) ∈ innerBonds S j := by
  classical
  obtain ⟨h, hh, rfl⟩ := hx
  obtain ⟨h', hh', e'⟩ := hx'
  have hu := blockSite_mem_levelCube hj hodd hv hh
  have hu' := blockSite_mem_levelCube hj hodd hv hh'
  have hb : (cellSite y j (blockSite F.blockSide v h), i) ∈ innerBonds S j := by
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨cellSite_mem hy hu, Finset.mem_univ _⟩, ?_⟩
    show cellSite y j (blockSite F.blockSide v h) + unitStep j i ∈ sitesOfCells S j
    rw [e']
    exact cellSite_mem hy hu'
  refine ⟨_, hu, h, hh, rfl, rfl, ?_, hb⟩
  unfold bondsOver
  refine Finset.mem_filter.2 ⟨hb, ?_⟩
  rw [Finset.mem_singleton]
  exact enclosingCell_cellSite hodd y hu
theorem sum_bondNorm_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (S : Finset F.Cell)
    (R : F.FieldChain) (U : ChainChart F) (y : F.Cell) (j : ℕ) :
    ∑ u ∈ centredCube (F.blockSide ^ (F.top - j)), ∑ i : Fin 4, bondNorm S R U y j u i ^ 4 ≤
      ∑ b ∈ bondsOver S {y} j, ‖levelCoordinate R U j b.1 b.2‖ ^ 4 := by
  classical
  rw [← Finset.sum_product']
  set T := centredCube (F.blockSide ^ (F.top - j)) ×ˢ (Finset.univ : Finset (Fin 4)) with hT
  set φ : Lattice4 × Fin 4 → F.Site j × Fin 4 := fun p => (cellSite y j p.1, p.2) with hφ
  set T' := T.filter fun p => φ p ∈ bondsOver S {y} j with hT'
  have h1 : ∑ p ∈ T, bondNorm S R U y j p.1 p.2 ^ 4 =
      ∑ p ∈ T', ‖levelCoordinate R U j (φ p).1 (φ p).2‖ ^ 4 := by
    rw [hT', Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold bondNorm
    split_ifs with h <;> simp_all
  have hinj : Set.InjOn φ (T' : Set (Lattice4 × Fin 4)) := by
    intro p hp q hq hpq
    have hp' := (Finset.mem_product.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).1).1
    have hq' := (Finset.mem_product.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).1).1
    have e1 : cellSite y j p.1 = cellSite y j q.1 := congrArg Prod.fst hpq
    have e2 : (φ p).2 = (φ q).2 := congrArg Prod.snd hpq
    exact Prod.ext (cellSite_injective hamb hodd y j hp' hq' e1) e2
  rw [h1, ← Finset.sum_image (f := fun b : F.Site j × Fin 4 => ‖levelCoordinate R U j b.1 b.2‖ ^ 4) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  intro b hb
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hb
  exact (Finset.mem_filter.1 hp).2
theorem sum_blockDeviation_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (S : Finset F.Cell)
    (R : F.FieldChain) (U : ChainChart F) (y : F.Cell) {j : ℕ} (hj : j < F.top) :
    ∑ v ∈ centredCube (F.blockSide ^ (F.top - (j + 1))), blockDeviation S R U y j v ^ 4 ≤
      ∑ b ∈ bondsOver S {y} j, ‖levelCoordinate R U j b.1 b.2‖ ^ 4 := by
  refine le_trans (le_of_eq ?_) (sum_bondNorm_le hamb hodd S R U y j)
  simp only [blockDeviation_pow_four]
  have := sum_blockSite (E := ℝ) hodd (hodd.pow (n := F.top - (j + 1)))
    (fun u => ∑ i : Fin 4, bondNorm S R U y j u i ^ 4)
  rwa [mul_pow_sub_succ hj] at this
theorem norm_ratio_le_blockDeviation (hodd : Odd F.blockSide) {S : Finset F.Cell} {y : F.Cell} (hy : y ∈ S)
    (R : F.FieldChain) (U : ChainChart F) {j : ℕ} (hj : j < F.top) {v : Lattice4}
    (hv : v ∈ centredCube (F.blockSide ^ (F.top - (j + 1))))
    {x : F.Site j} {i : Fin 4} (hx : x ∈ blockSites y j v) (hx' : x + unitStep j i ∈ blockSites y j v) :
    ‖((chartField R U j x i * (R j x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ blockDeviation S R U y j v := by
  classical
  obtain ⟨u, _, h, hh, rfl, rfl, hb, _⟩ := exists_bond_of_mem_blockSites hodd hy hj hv hx hx'
  have h1 : bondNorm S R U y j (blockSite F.blockSide v h) i =
      ‖levelCoordinate R U j (cellSite y j (blockSite F.blockSide v h)) i‖ := by
    unfold bondNorm
    rw [if_pos hb]
  have h2 : ‖((chartField R U j (cellSite y j (blockSite F.blockSide v h)) i *
        (R j (cellSite y j (blockSite F.blockSide v h)) i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      bondNorm S R U y j (blockSite F.blockSide v h) i := by
    rw [h1]
    exact norm_coe_sub_one_le_norm_unitQuaternionLog _
  refine h2.trans (le_sqrt_sqrt_of_pow_four_le ?_)
  calc bondNorm S R U y j (blockSite F.blockSide v h) i ^ 4 ≤
        ∑ i' : Fin 4, bondNorm S R U y j (blockSite F.blockSide v h) i' ^ 4 :=
        Finset.single_le_sum (f := fun i' => bondNorm S R U y j (blockSite F.blockSide v h) i' ^ 4)
          (fun _ _ => by positivity) (Finset.mem_univ i)
    _ ≤ ∑ h' ∈ centredCube F.blockSide, ∑ i' : Fin 4, bondNorm S R U y j (blockSite F.blockSide v h') i' ^ 4 :=
        Finset.single_le_sum
          (f := fun h' => ∑ i' : Fin 4, bondNorm S R U y j (blockSite F.blockSide v h') i' ^ 4)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hh
theorem cellSideLength_eq (F : BlockFrame) : cellSideLength F = ((F.blockSide ^ F.top : ℕ) : ℤ) := by
  unfold cellSideLength
  push_cast
  rfl
theorem cellSupDist_self (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem mem_patchDomain_of_cell {S : Finset F.Cell} {y : F.Cell} (hy : y ∈ S) (hL : 0 < F.blockSide)
    {x : Lattice4} (hx : ∀ i, 0 ≤ x i ∧ x i < cellSideLength F) : x ∈ patchDomain S y := by
  classical
  have hN : 0 < cellSideLength F := cellSideLength_pos hL
  unfold patchDomain
  refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, 0, ?_, fun i => (hx i).1⟩
  · have := hx i
    rw [Finset.mem_Icc]
    constructor <;> nlinarith [this.1, this.2]
  · unfold patchCorners
    refine Finset.mem_image.2 ⟨y, ?_, ?_⟩
    · unfold cellBall
      exact Finset.mem_filter.2 ⟨hy, by rw [cellSupDist_self]; norm_num⟩
    · funext i
      simp [cellDisplacement]
theorem baseSite_mem_patch (hodd : Odd F.blockSide) {S : Finset F.Cell} {y : F.Cell} (hy : y ∈ S)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) {j : ℕ} (hj : j ≤ F.top) {u : Lattice4}
    (hu : u ∈ centredCube (F.blockSide ^ (F.top - j))) :
    baseSite (cellSite y j u) ∈ (patchDomain S y).image (patchSite S y) := by
  classical
  have hLpos := hodd.pos
  set w : Lattice4 := blockSite (F.blockSide ^ j) u 0 with hw
  have h0 : (0 : Lattice4) ∈ centredCube (F.blockSide ^ j) := by
    rw [mem_centredCube_iff]
    intro i
    have : (0 : ℤ) ≤ (((F.blockSide ^ j : ℕ) : ℤ) - 1) / 2 := by
      have : 0 < F.blockSide ^ j := by positivity
      omega
    simpa using this
  have hwc : w ∈ centredCube (F.blockSide ^ F.top) := by
    have := blockSite_mem_centredCube (hodd.pow (n := j)) (hodd.pow (n := F.top - j)) hu h0
    rwa [← pow_add, Nat.add_sub_cancel' hj] at this
  obtain ⟨m, m1, m2, m0⟩ := exists_half_of_odd (hodd.pow (n := F.top))
  have hN : cellSideLength F = 2 * m + 1 := by rw [cellSideLength_eq]; exact m1
  have hh : (cellSideLength F - 1) / 2 = m := by rw [hN]; omega
  have hb : baseSite (cellSite y j u) = cellCentre 0 y + siteOfCoords 0 w := by
    simp only [cellSite]
    rw [baseSite_add j hj, baseSite_cellCentre j hj]
    congr 1
    congr 1
    funext i
    simp [hw, blockSite]
  rw [hb]
  refine Finset.mem_image.2 ⟨fun i => closedOrthant S y i * w i + m, mem_patchDomain_of_cell hy hLpos fun i => ?_, ?_⟩
  · have h1 := ((mem_centredCube_iff _ w).1 hwc) i
    rw [m2] at h1
    rw [hN]
    rcases he i with h | h <;> rw [h] <;> constructor <;> omega
  · simp only [patchSite]
    rw [hh]
    congr 1
    congr 1
    funext i
    rcases he i with h | h <;> rw [h] <;> ring
end Sizes
section Final
variable {F : BlockFrame}
theorem baseSite_level_zero (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem gaugeGeneratorAtLevel_zero (R : F.FieldChain) (U : ChainChart F) (ξ : F.Site 0 → imaginaryQuaternions)
    (x : F.Site 0) : gaugeGeneratorAtLevel R U ξ 0 x = (ξ x : ℍ[ℝ]) := rfl
theorem localNorm_nonneg (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights)
    (z : F.Cell) : 0 ≤ localNorm S R U w z := Real.sqrt_nonneg _
theorem frameCellMean_eq (hodd : Odd F.blockSide) {S : Finset F.Cell} {y : F.Cell} (V : F.GaugeField F.top)
    (U : ChainChart F) (ξ : F.Site 0 → imaginaryQuaternions)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) :
    frameCellMean S V y (fun x => ξ x) =
      (1 / ((F.blockSide : ℝ) ^ F.top) ^ 4) • ∑ w ∈ centredCube (F.blockSide ^ F.top),
        framedGenerator S V U ξ y 0 w := by
  obtain ⟨m, m1, m2, m0⟩ := exists_half_of_odd (hodd.pow (n := F.top))
  have hN : cellSideLength F = 2 * m + 1 := by rw [cellSideLength_eq]; exact m1
  have hh : (cellSideLength F - 1) / 2 = m := by rw [hN]; omega
  have hcast : (cellSideLength F : ℝ) = (F.blockSide : ℝ) ^ F.top := by
    unfold cellSideLength
    push_cast
    rfl
  have hsum : ∑ x ∈ cellOffsets F,
        adjointAction (frameChange S V y (patchSite S y x))⁻¹ (ξ (patchSite S y x) : ℍ[ℝ]) =
      ∑ w ∈ centredCube (F.blockSide ^ F.top), framedGenerator S V U ξ y 0 w := by
    refine Finset.sum_nbij' (fun (x : Lattice4) (k : Fin 4) => closedOrthant S y k * (x k - m))
      (fun (w : Lattice4) (k : Fin 4) => closedOrthant S y k * w k + m) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [mem_centredCube_iff]
      intro k
      have h1 := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hx k)
      rw [hN] at h1
      rw [m2]
      rcases he k with h | h <;> rw [h] <;> constructor <;> omega
    · intro w hw
      have h1 := ((mem_centredCube_iff _ w).1 hw)
      refine Fintype.mem_piFinset.2 fun k => ?_
      have h2 := h1 k
      rw [m2] at h2
      rw [Finset.mem_Ico, hN]
      rcases he k with h | h <;> rw [h] <;> constructor <;> omega
    · intro x _
      funext k
      rcases he k with h | h <;> simp only [h] <;> ring
    · intro w _
      funext k
      rcases he k with h | h <;> simp only [h] <;> ring
    · intro x _
      have e : patchSite S y x = cellSite y 0 (fun k => closedOrthant S y k * (x k - m)) := by
        simp only [patchSite, cellSite, hh]
      simp only [framedGenerator]
      rw [baseSite_level_zero, ← e, gaugeGeneratorAtLevel_zero]
  unfold frameCellMean
  rw [hcast, hsum]
theorem sqrt_sqrt_sum_le_cellSiteNorm (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {y : F.Cell} (hy : y ∈ S)
    (V : F.GaugeField F.top) (U : ChainChart F) (ξ : F.Site 0 → imaginaryQuaternions) :
    Real.sqrt (Real.sqrt (∑ w ∈ centredCube (F.blockSide ^ F.top), ‖framedGenerator S V U ξ y 0 w‖ ^ 4)) ≤
      cellSiteNorm 4 S (fun _ => 1) (fun x => ξ x) y := by
  classical
  have key : ∀ P : Finset (F.Site 0), (∀ w ∈ centredCube (F.blockSide ^ F.top), cellSite y 0 w ∈ P) →
      Real.sqrt (Real.sqrt (∑ w ∈ centredCube (F.blockSide ^ F.top), ‖framedGenerator S V U ξ y 0 w‖ ^ 4)) ≤
        (∑ x ∈ P, ((1 : ℝ) * ‖(ξ x : ℍ[ℝ])‖) ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) := by
    intro P hP
    have h1 : ∑ w ∈ centredCube (F.blockSide ^ F.top), ‖framedGenerator S V U ξ y 0 w‖ ^ 4 ≤
        ∑ x ∈ P, ‖(ξ x : ℍ[ℝ])‖ ^ 4 := by
      have e : ∀ w, ‖framedGenerator S V U ξ y 0 w‖ = ‖(ξ (cellSite y 0 w) : ℍ[ℝ])‖ := fun w =>
        norm_adjointAction _ _
      simp only [e]
      have hinj : Set.InjOn (cellSite (F := F) y 0) (centredCube (F.blockSide ^ F.top) : Set Lattice4) := by
        intro a ha b hb hab
        exact cellSite_injective hamb hodd y 0 (by simpa using ha) (by simpa using hb) hab
      rw [← Finset.sum_image (f := fun x => ‖(ξ x : ℍ[ℝ])‖ ^ 4) hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
      exact hP w hw
    have h2 : ∀ x ∈ P, ((1 : ℝ) * ‖(ξ x : ℍ[ℝ])‖) ^ (4 : ℝ) = ‖(ξ x : ℍ[ℝ])‖ ^ 4 := by
      intro x _
      rw [one_mul, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [Finset.sum_congr rfl h2]
    have hB : 0 ≤ ∑ x ∈ P, ‖(ξ x : ℍ[ℝ])‖ ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
    refine (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h1)).trans (le_of_eq ?_)
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hB]
    norm_num
  unfold cellSiteNorm
  refine key _ fun w hw => Finset.mem_filter.2 ⟨cellSite_mem hy (by simpa using hw), ?_⟩
  exact enclosingCell_cellSite hodd y (by simpa using hw)
theorem weightedNorm_decayWeights_le (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) {del : ℝ}
    (hdel : 0 < del) (y0 : F.Cell) :
    weightedNorm S R U (decayWeights F del 0 0 y0) ≤ weightedNorm S R U (constOneWeights F) := by
  have hw : ∀ z : F.Cell, localNorm S R U (decayWeights F del 0 0 y0) z ≤ localNorm S R U (constOneWeights F) z := by
    intro z
    unfold localNorm
    refine Real.sqrt_le_sqrt ?_
    unfold localNormSq
    have hle : ∀ (j : ℕ) (x : F.Site j), 0 ≤ decayWeights F del 0 0 y0 j x ∧
        decayWeights F del 0 0 y0 j x ≤ 1 := by
      intro j x
      have e : decayWeights F del 0 0 y0 j x = Real.exp (-del * cellSupDist (enclosingCell x) y0) := by
        simp [decayWeights]
      rw [e]
      refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 ?_⟩
      nlinarith
    have hterm : ∀ (j : ℕ) (x : F.Site j) (t : ℝ) (k : ℕ), 0 ≤ t →
        (decayWeights F del 0 0 y0 j x * t) ^ k ≤ (constOneWeights F j x * t) ^ k := by
      intro j x t k ht
      refine pow_le_pow_left₀ (mul_nonneg (hle j x).1 ht) ?_ k
      have := mul_le_mul_of_nonneg_right (hle j x).2 ht
      simpa [constOneWeights] using this
    refine add_le_add (add_le_add
      (Real.sqrt_le_sqrt (Finset.sum_le_sum fun b _ => hterm _ _ _ _ (norm_nonneg _)))
      (Finset.sum_le_sum fun b _ => hterm _ _ _ _ (norm_nonneg _))) ?_
    exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun b _ => hterm _ _ _ _ (norm_nonneg _)
  unfold weightedNorm
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun z _ => ?_)
  exact pow_le_pow_left₀ (localNorm_nonneg _ _ _ _ _) (hw z) 2
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem localNorm_le_supWeightedNorm (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) {del : ℝ}
    (hdel : 0 < del) {z : F.Cell} (hz : z ∈ S) :
    localNorm S R U (constOneWeights F) z ≤ Real.exp (3 * del) * supWeightedNorm S del R U := by
  classical
  have hdec : ∀ (j : ℕ) (x : F.Site j),
      decayWeights F del 0 0 z j x = Real.exp (-del * cellSupDist (enclosingCell x) z) := by
    intro j x
    simp [decayWeights]
  have hK : ∀ (j : ℕ) (x : F.Site j), enclosingCell x ∈ cellBall S z 3 →
      (1 : ℝ) ≤ Real.exp (3 * del) * decayWeights F del 0 0 z j x := by
    intro j x hx
    rw [hdec, ← Real.exp_add]
    have hd : cellSupDist (enclosingCell x) z ≤ 3 := by
      rw [cellSupDist_comm]
      unfold cellBall at hx
      exact (Finset.mem_filter.1 hx).2
    have hd' : (cellSupDist (enclosingCell x) z : ℝ) ≤ 3 := by exact_mod_cast hd
    exact Real.one_le_exp (by nlinarith)
  set w := decayWeights F del 0 0 z with hw
  set Kc := Real.exp (3 * del) with hKc
  have hKc0 : 0 < Kc := Real.exp_pos _
  have hterm : ∀ (j : ℕ) (x : F.Site j) (t : ℝ) (k : ℕ), 0 ≤ t → enclosingCell x ∈ cellBall S z 3 →
      (constOneWeights F j x * t) ^ k ≤ Kc ^ k * (w j x * t) ^ k := by
    intro j x t k ht hx
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by simpa [constOneWeights] using ht) ?_ k
    have := mul_le_mul_of_nonneg_right (hK j x hx) ht
    simpa [constOneWeights, mul_assoc] using this
  have hsq : localNormSq S (cellBall S z 3) R U (constOneWeights F) ≤
      Kc ^ 2 * localNormSq S (cellBall S z 3) R U w := by
    unfold localNormSq
    have cb : ∀ {B : Finset F.Cell} {j : ℕ} {b : F.Site j × Fin 4}, b ∈ bondsOver S B j →
        enclosingCell b.1 ∈ B := by
      intro B j b hb
      unfold bondsOver at hb
      exact (Finset.mem_filter.1 hb).2
    have cp : ∀ {B : Finset F.Cell} {p : F.Site 0 × Fin 4 × Fin 4}, p ∈ plaquettesOver S B 0 →
        enclosingCell p.1 ∈ B := by
      intro B p hp
      unfold plaquettesOver at hp
      exact (Finset.mem_filter.1 hp).2
    have h1 : Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (constOneWeights F 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) ≤
        Kc ^ 2 * Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) := by
      have hs : ∑ b ∈ bondsOver S (cellBall S z 3) 0, (constOneWeights F 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤
          (Kc ^ 2) ^ 2 * ∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun b hb => ?_
        have := hterm 0 b.1 _ 4 (norm_nonneg (U.fine b.1 b.2)) (cb hb)
        calc _ ≤ _ := this
          _ = _ := by ring
      calc _ ≤ Real.sqrt ((Kc ^ 2) ^ 2 *
            ∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) :=
            Real.sqrt_le_sqrt hs
        _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have h2 : ∑ p ∈ plaquettesOver S (cellBall S z 3) 0,
          (constOneWeights F 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 ≤
        Kc ^ 2 * ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun p hp => hterm 0 p.1 _ 2 (norm_nonneg _) (cp hp)
    have h3 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
          (constOneWeights F (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤
        Kc ^ 2 * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
          (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun c hc => hterm (j + 1) c.1 _ 2 (norm_nonneg _) (cb hc)
    rw [mul_add, mul_add]
    linarith
  have h1 : localNorm S R U (constOneWeights F) z ≤ Kc * localNorm S R U w z := by
    unfold localNorm
    calc _ ≤ Real.sqrt (Kc ^ 2 * localNormSq S (cellBall S z 3) R U w) := Real.sqrt_le_sqrt hsq
      _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hKc0.le]
  have h2 : localNorm S R U w z ≤ weightedNorm S R U w := by
    unfold weightedNorm
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    exact Finset.single_le_sum (f := fun y => localNorm S R U w y ^ 2) (fun _ _ => sq_nonneg _) hz
  have h3 : weightedNorm S R U w ≤ supWeightedNorm S del R U := by
    unfold supWeightedNorm
    refine le_ciSup (f := fun y0 : F.Cell => weightedNorm S R U (decayWeights F del 0 0 y0)) ?_ z
    exact ⟨weightedNorm S R U (constOneWeights F), by
      rintro _ ⟨y0, rfl⟩
      exact weightedNorm_decayWeights_le S R U hdel y0⟩
  exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans h3) hKc0.le)
theorem sum_stepBound_pow_four_le {M : ℕ} (hM : Odd M) {Lr ls : ℝ} (hLr : 0 ≤ Lr) (hls : 0 ≤ ls)
    (hs : Lr * ls * (M : ℝ) = 1) (bs : Lattice4 → ℝ) {B a : ℝ} (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hsum : ∑ v ∈ centredCube M, bs v ^ 4 ≤ B ^ 4) :
    ∑ v ∈ centredCube M, (12 * (5 * Lr * bs v) + 2 * (5 * Lr * (a * ls))) ^ 4 ≤ (120 * Lr * B + 20 * a) ^ 4 := by
  set b : ℝ := 10 * Lr * (a * ls) with hb
  have h1 : ∑ v ∈ centredCube M, (12 * (5 * Lr * bs v) + 2 * (5 * Lr * (a * ls))) ^ 4 ≤
      ∑ v ∈ centredCube M, 8 * ((60 * Lr) ^ 4 * bs v ^ 4 + b ^ 4) := by
    refine Finset.sum_le_sum fun v _ => ?_
    have e : 12 * (5 * Lr * bs v) + 2 * (5 * Lr * (a * ls)) = 60 * Lr * bs v + b := by
      rw [hb]
      ring
    rw [e, ← mul_pow]
    exact add_pow_four_le_eight_mul
  have h2 : ∑ v ∈ centredCube M, 8 * ((60 * Lr) ^ 4 * bs v ^ 4 + b ^ 4) =
      8 * ((60 * Lr) ^ 4 * ∑ v ∈ centredCube M, bs v ^ 4 + ((M : ℝ) * b) ^ 4) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      card_centredCube_real hM, mul_pow (M : ℝ) b]
  have h3 : (M : ℝ) * b = 10 * a := by
    rw [hb]
    calc (M : ℝ) * (10 * Lr * (a * ls)) = 10 * a * (Lr * ls * (M : ℝ)) := by ring
      _ = _ := by rw [hs, mul_one]
  set a1 : ℝ := 60 * Lr * B with ha1
  set a2 : ℝ := 10 * a with ha2
  have ha10 : 0 ≤ a1 := by positivity
  have ha20 : 0 ≤ a2 := by positivity
  have hgeq : 120 * Lr * B + 20 * a = 2 * (a1 + a2) := by
    rw [ha1, ha2]
    ring
  have h5 : (60 * Lr) ^ 4 * ∑ v ∈ centredCube M, bs v ^ 4 ≤ a1 ^ 4 := by
    calc _ ≤ (60 * Lr) ^ 4 * B ^ 4 := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by rw [ha1, mul_pow (60 * Lr)]
  have h6 : a1 ^ 4 + a2 ^ 4 ≤ (a1 + a2) ^ 4 := by
    have p1 := mul_nonneg (pow_nonneg ha10 3) ha20
    have p2 := mul_nonneg (pow_nonneg ha10 2) (pow_nonneg ha20 2)
    have p3 := mul_nonneg ha10 (pow_nonneg ha20 3)
    nlinarith
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ 8 * (a1 ^ 4 + a2 ^ 4) := by
        rw [h3]
        linarith
    _ ≤ (120 * Lr * B + 20 * a) ^ 4 := by
        rw [hgeq, mul_pow]
        have : 0 ≤ a1 ^ 4 + a2 ^ 4 := by positivity
        nlinarith
theorem norm_framedGenerator_step_le_of_bounds (hodd : Odd F.blockSide) {S : Finset F.Cell}
    {V : F.GaugeField F.top} {U : ChainChart F} {ξ : F.Site 0 → imaginaryQuaternions} {y : F.Cell} (hy : y ∈ S)
    (hsign : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1)
    {j : ℕ} (hj : j < F.top) {v : Lattice4} (hv : v ∈ centredCube (F.blockSide ^ (F.top - (j + 1)))) {κ : ℝ}
    (hκ : 0 ≤ κ)
    (hsmall : 5 * (F.blockSide : ℝ) * blockDeviation S (referenceFieldChain S V) U y j v ≤ 1 / 2)
    (hbond : ∀ b ∈ innerBonds S j, baseSite b.1 ∈ (patchDomain S y).image (patchSite S y) →
      baseSite (b.1 + unitStep j b.2) ∈ (patchDomain S y).image (patchSite S y) →
      unitDeviation (referenceInPatchFrame S V y j b.1 b.2) ≤ κ) :
    ‖framedGenerator S V U ξ y (j + 1) v - blockAverage F.blockSide (framedGenerator S V U ξ y j) v‖ ≤
      (12 * (5 * (F.blockSide : ℝ) * blockDeviation S (referenceFieldChain S V) U y j v) +
          2 * (5 * (F.blockSide : ℝ) * κ)) *
        blockAverage F.blockSide (fun w => ‖framedGenerator S V U ξ y j w‖) v := by
  refine norm_framedGenerator_step_le hodd S V U ξ y hj v (blockDeviation_nonneg _ _ _ _ _ _) hκ hsmall
    (fun x i hx hx' => norm_ratio_le_blockDeviation hodd hy _ U hj hv hx hx') (fun x i hx hx' => ?_)
  obtain ⟨u, hu, h, hh, _, ex, _, hb⟩ := exists_bond_of_mem_blockSites hodd hy hj hv hx hx'
  obtain ⟨h', hh', ex'⟩ := hx'
  have p1 : baseSite x ∈ (patchDomain S y).image (patchSite S y) := by
    rw [ex]
    exact baseSite_mem_patch hodd hy hsign hj.le hu
  have p2 : baseSite (x + unitStep j i) ∈ (patchDomain S y).image (patchSite S y) := by
    rw [ex']
    exact baseSite_mem_patch hodd hy hsign hj.le (blockSite_mem_levelCube hj hodd hv hh')
  exact hbond (x, i) hb p1 p2
theorem blockSide_mul_levelScale (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top) :
    (F.blockSide : ℝ) * levelScale F j * ((F.blockSide ^ (F.top - (j + 1)) : ℕ) : ℝ) = 1 := by
  have hL : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hodd.pos.ne'
  have e1 : F.top - j = (F.top - (j + 1)) + 1 := by omega
  unfold levelScale
  rw [e1, pow_succ]
  push_cast
  rw [one_div, inv_pow]
  field_simp
theorem norm_framedGenerator_top_sub_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hL5 : 5 ≤ F.blockSide) {S : Finset F.Cell} {V : F.GaugeField F.top}
    {U : ChainChart F} (ξ : F.Site 0 → imaginaryQuaternions) {y : F.Cell} (hy : y ∈ S)
    (hsign : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) {g T : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgT : g ≤ T) (G : ℕ → Lattice4 → ℝ) (hG0 : ∀ j v, 0 ≤ G j v)
    (hstep : ∀ j, j < F.top → ∀ v ∈ centredCube (F.blockSide ^ (F.top - (j + 1))),
      ‖framedGenerator S V U ξ y (j + 1) v - blockAverage F.blockSide (framedGenerator S V U ξ y j) v‖ ≤
        G j v * blockAverage F.blockSide (fun w => ‖framedGenerator S V U ξ y j w‖) v)
    (hG : ∀ j, j < F.top → ∑ v ∈ centredCube (F.blockSide ^ (F.top - (j + 1))), G j v ^ 4 ≤ g ^ 4) :
    ‖adjointAction (frameChange S V y (cellCentre 0 y))⁻¹
          (gaugeGeneratorAtLevel (referenceFieldChain S V) U ξ F.top y) -
        frameCellMean S V y (fun x => ξ x)‖ ≤
      2 * T * (cellSiteNorm 4 S (fun _ => 1) (fun x => ξ x) y / (cellSideLength F : ℝ)) := by
  have main := norm_sub_average_le_of_steps hodd hL5 (framedGenerator S V U ξ y) G hg0 hg1 hG0 hstep hG
  have hat : cellSite y F.top (0 : Lattice4) = y := by
    simp only [cellSite]
    rw [cellCentre_top, siteOfCoords_zero, add_zero]
  have htb : baseSite y = cellCentre 0 y := by
    have := baseSite_cellCentre (F := F) F.top le_rfl y
    rwa [cellCentre_top] at this
  have htop : framedGenerator S V U ξ y F.top 0 =
      adjointAction (frameChange S V y (cellCentre 0 y))⁻¹
        (gaugeGeneratorAtLevel (referenceFieldChain S V) U ξ F.top y) := by
    unfold framedGenerator
    rw [hat, htb]
  rw [← htop, frameCellMean_eq hodd V U ξ hsign]
  refine main.trans ?_
  have hsite := sqrt_sqrt_sum_le_cellSiteNorm hamb hodd hy V U ξ
  have hcast : (cellSideLength F : ℝ) = (F.blockSide : ℝ) ^ F.top := by
    unfold cellSideLength
    push_cast
    rfl
  rw [hcast]
  have hp : 0 ≤ 1 / (F.blockSide : ℝ) ^ F.top := by positivity
  have hq := Real.sqrt_nonneg
    (Real.sqrt (∑ w ∈ centredCube (F.blockSide ^ F.top), ‖framedGenerator S V U ξ y 0 w‖ ^ 4))
  have hT0 : 0 ≤ T := hg0.trans hgT
  calc 2 * g * (1 / (F.blockSide : ℝ) ^ F.top) *
        Real.sqrt (Real.sqrt (∑ w ∈ centredCube (F.blockSide ^ F.top), ‖framedGenerator S V U ξ y 0 w‖ ^ 4))
      ≤ 2 * T * (1 / (F.blockSide : ℝ) ^ F.top) * cellSiteNorm 4 S (fun _ => 1) (fun x => ξ x) y := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hp) hsite hq ?_
        positivity
    _ = _ := by ring
end Final
end GeneratorMeans
open GeneratorMeans LatticePaths GaugeMap LatticeFractionalIntegration in
theorem compositeMeanStatement_holds (hC : levelCoordinateQuarticStatement)
    (hB : referenceBoundsStatement) : compositeMeanStatement := by
  obtain ⟨C₁, L0, hC₁, hco⟩ := hC
  obtain ⟨C₂, c₂, L1, hC₂, hc₂, hbd⟩ := hB
  refine ⟨max (max L0 L1) 5, fun L hodd hL del hdel hdel8 => ?_⟩
  have hL0 : L0 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL1 : L1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL5 : 5 ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨c₁, hc₁, hco'⟩ := hco L hodd hL0 del hdel
  have hLr : (5 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL5
  have hLr0 : (0 : ℝ) < (L : ℝ) := by linarith
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = Real.exp (3 * del) := ⟨_, rfl⟩
  have he0 : 0 < e := he ▸ Real.exp_pos _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 120 * (L : ℝ) * C₁ * e + 20 * C₂ := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (min c₁ c₂) (1 / (2 * K)) := ⟨_, rfl⟩
  have hcpos : 0 < c := by
    rw [hcdef]
    exact lt_min (lt_min hc₁ hc₂) (by positivity)
  have hsc1 : c ≤ c₁ := by rw [hcdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hsc2 : c ≤ c₂ := by rw [hcdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hsc3 : c ≤ 1 / (2 * K) := by rw [hcdef]; exact min_le_right _ _
  refine ⟨c, 2 * K, hcpos, by positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold U hU ξ y hy
  subst hFL
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = supWeightedNorm S del (referenceFieldChain S V) U := ⟨_, rfl⟩
  obtain ⟨β, hβd⟩ : ∃ β : ℝ, β = localNorm S (referenceFieldChain S V) U (constOneWeights F) y := ⟨_, rfl⟩
  rw [← hN] at hU ⊢
  have hβ0 : 0 ≤ β := hβd ▸ localNorm_nonneg _ _ _ _ _
  have hβ : β ≤ e * N := by
    rw [hβd, hN, he]
    exact localNorm_le_supWeightedNorm S _ U hdel hy
  have hN0 : 0 ≤ N := nonneg_of_mul_nonneg_right (hβ0.trans hβ) he0
  have hlog : ∀ j, j < F.top → ∑ b ∈ bondsOver S {y} j,
      ‖levelCoordinate (referenceFieldChain S V) U j b.1 b.2‖ ^ 4 ≤ (C₁ * β) ^ 4 := by
    intro j hj
    have h1 := hco' F m S rfl hamb hm hreg s V hs (hsc.trans hsc1) hcold U
      (by rw [← hN]; exact hU.trans hsc1) j hj y hy
    rw [← hβd] at h1
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 4
    rwa [sqrt_sqrt_pow_four (Finset.sum_nonneg fun _ _ => by positivity)] at h2
  have hbond := (hbd F m S hodd hL1 hamb hm hreg s V hs (hsc.trans hsc2) hcold).1
  have hsign := (closedOrthant_spec hreg (by omega : 32 ≤ m) y).1
  have hB0 : 0 ≤ C₁ * β := by positivity
  have ha0 : 0 ≤ C₂ * s := by positivity
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = 120 * (F.blockSide : ℝ) * (C₁ * β) + 20 * (C₂ * s) := ⟨_, rfl⟩
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  have hgK : g ≤ K * (s + N) := by
    have h1 : 120 * (F.blockSide : ℝ) * C₁ * β ≤ 120 * (F.blockSide : ℝ) * C₁ * (e * N) :=
      mul_le_mul_of_nonneg_left hβ (by positivity)
    have h2 : 0 ≤ 120 * (F.blockSide : ℝ) * C₁ * e * s := by positivity
    have h3 : 0 ≤ 20 * C₂ * N := by positivity
    rw [hK, hg]
    nlinarith
  have hg1 : g ≤ 1 := by
    have h1 : s + N ≤ 1 / K := by
      have a1 := hsc.trans hsc3
      have a2 := hU.trans hsc3
      have e2 : 1 / (2 * K) + 1 / (2 * K) = 1 / K := by
        field_simp
        norm_num
      linarith
    calc g ≤ K * (s + N) := hgK
      _ ≤ K * (1 / K) := mul_le_mul_of_nonneg_left h1 hK0.le
      _ = 1 := by field_simp
  have hls0 : ∀ j, 0 ≤ levelScale F j := fun j => by
    unfold levelScale
    positivity
  have hbs : ∀ j, j < F.top → ∑ v ∈ centredCube (F.blockSide ^ (F.top - (j + 1))),
      blockDeviation S (referenceFieldChain S V) U y j v ^ 4 ≤ (C₁ * β) ^ 4 :=
    fun j hj => (sum_blockDeviation_le hamb hodd S _ U y hj).trans (hlog j hj)
  have res := norm_framedGenerator_top_sub_le hamb hodd hL5 (V := V) (U := U) ξ hy hsign hg0 hg1 hgK
    (fun j v => 12 * (5 * (F.blockSide : ℝ) * blockDeviation S (referenceFieldChain S V) U y j v) +
      2 * (5 * (F.blockSide : ℝ) * ((C₂ * s) * levelScale F j)))
    (fun j v => by
      have := blockDeviation_nonneg S (referenceFieldChain S V) U y j v
      have := hls0 j
      positivity)
    (fun j hj v hv => by
      refine norm_framedGenerator_step_le_of_bounds hodd hy hsign hj hv (mul_nonneg ha0 (hls0 j)) ?_
        (fun b hb p1 p2 => hbond j hj y hy b hb p1 p2)
      have hbs1 : blockDeviation S (referenceFieldChain S V) U y j v ≤ C₁ * β := by
        have h1 : blockDeviation S (referenceFieldChain S V) U y j v ^ 4 ≤ (C₁ * β) ^ 4 :=
          (Finset.single_le_sum (f := fun v => blockDeviation S (referenceFieldChain S V) U y j v ^ 4)
            (fun _ _ => by positivity) hv).trans (hbs j hj)
        exact le_of_pow_le_pow_left₀ (by norm_num) hB0 h1
      have h1 : 5 * (F.blockSide : ℝ) * blockDeviation S (referenceFieldChain S V) U y j v ≤
          5 * (F.blockSide : ℝ) * (C₁ * β) :=
        mul_le_mul_of_nonneg_left hbs1 (by positivity)
      have h3 : 0 ≤ (F.blockSide : ℝ) * (C₁ * β) := by positivity
      rw [hg] at hg1
      nlinarith)
    (fun j hj => by
      have := sum_stepBound_pow_four_le (hodd.pow (n := F.top - (j + 1))) (Nat.cast_nonneg F.blockSide) (hls0 j)
        (blockSide_mul_levelScale hodd hj)
        (fun v => blockDeviation S (referenceFieldChain S V) U y j v) hB0 ha0 (hbs j hj)
      rw [hg]
      exact this)
  calc _ ≤ _ := res
    _ = _ := by ring
end YangMills.Construction.BlockAverages
end
