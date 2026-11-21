import YangMills.Construction.HoleBesideASecondHole.ExcitedCellsPay
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.HoleSavings
open BlockAverages LumpContours
namespace ExcitedCells
variable {F : BlockFrame}
theorem period_eq_pow_mul {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (k : Fin 4) :
    F.period i k = F.blockSide ^ (j - i) * F.period j k := by
  simp only [BlockFrame.period]
  have : F.top - i = (F.top - j) + (j - i) := by omega
  rw [this, pow_add]
  ring
theorem siteCoords_cast {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by
  simp [siteCoords]
theorem siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) : siteOfCoords j (siteCoords x) = x := by
  funext k
  exact siteCoords_cast x k
theorem mem_centredCube_iff {M : ℕ} {o : Fin 4 → ℤ} :
    o ∈ centredCube M ↔ ∀ m, |o m| ≤ ((M : ℤ) - 1) / 2 := by
  simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
theorem odd_blockSide_pow (hL : Odd F.blockSide) (e : ℕ) : Odd (F.blockSide ^ e) := hL.pow
theorem pow_mul_intCast_eq {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (k : Fin 4) {a b : ℤ}
    (h : (a : ZMod (F.period j k)) = b) :
    (((F.blockSide : ℤ) ^ (j - i) * a : ℤ) : ZMod (F.period i k)) =
      (((F.blockSide : ℤ) ^ (j - i) * b : ℤ) : ZMod (F.period i k)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h ⊢
  rw [period_eq_pow_mul hij hj k]
  push_cast
  rw [← mul_sub]
  exact mul_dvd_mul_left _ h
theorem abs_mul_add_le_half {A B : ℕ} (hA : Odd A) (hB : Odd B) {h h' : ℤ} (h1 : |h| ≤ ((B : ℤ) - 1) / 2)
    (h2 : |h'| ≤ ((A : ℤ) - 1) / 2) : |(A : ℤ) * h + h'| ≤ (((A * B : ℕ) : ℤ) - 1) / 2 := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  have e1 : (((2 * b + 1 : ℕ) : ℤ) - 1) / 2 = b := by
    push_cast
    omega
  have e2 : (((2 * a + 1 : ℕ) : ℤ) - 1) / 2 = a := by
    push_cast
    omega
  have e3 : ((((2 * a + 1) * (2 * b + 1) : ℕ) : ℤ) - 1) / 2 = 2 * a * b + a + b := by
    push_cast
    have : (2 * (a : ℤ) + 1) * (2 * b + 1) - 1 = 2 * (2 * a * b + a + b) := by ring
    rw [this]
    omega
  rw [e1] at h1
  rw [e2] at h2
  rw [e3]
  have h1' := abs_le.1 h1
  have h2' := abs_le.1 h2
  rw [abs_le]
  push_cast
  constructor <;> nlinarith
theorem sitesBelow_trans {i j m : ℕ} (hij : i ≤ j) (hjm : j ≤ m) (hm : m ≤ F.top) (hL : Odd F.blockSide)
    (x : F.Site m) {w : F.Site j} (hw : w ∈ sitesBelow j x) {z : F.Site i} (hz : z ∈ sitesBelow i w) :
    z ∈ sitesBelow i x := by
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hw
  obtain ⟨h', hh', rfl⟩ := Finset.mem_image.1 hz
  have hh1 := mem_centredCube_iff.1 hh
  have hh2 := mem_centredCube_iff.1 hh'
  refine Finset.mem_image.2 ⟨fun k => (F.blockSide : ℤ) ^ (j - i) * h k + h' k, ?_, ?_⟩
  · refine mem_centredCube_iff.2 fun k => ?_
    have e : m - i = (j - i) + (m - j) := by omega
    rw [e, pow_add]
    have := abs_mul_add_le_half (odd_blockSide_pow hL (j - i)) (odd_blockSide_pow hL (m - j)) (hh1 k) (hh2 k)
    simpa using this
  · funext k
    simp only [siteOfCoords]
    have h1 : ((siteCoords (siteOfCoords (F := F) j fun k => (F.blockSide : ℤ) ^ (m - j) * siteCoords x k + h k) k : ℤ) :
        ZMod (F.period j k)) = (((F.blockSide : ℤ) ^ (m - j) * siteCoords x k + h k : ℤ) : ZMod (F.period j k)) := by
      rw [siteCoords_cast]
      rfl
    have h2 := pow_mul_intCast_eq hij (hjm.trans hm) k h1
    have e : (F.blockSide : ℤ) ^ (m - i) = (F.blockSide : ℤ) ^ (j - i) * (F.blockSide : ℤ) ^ (m - j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [Int.cast_add (R := ZMod (F.period i k)) _ (h' k), h2, e]
    push_cast
    ring
theorem self_mem_sitesBelow {j : ℕ} (hL : Odd F.blockSide) (x : F.Site j) : x ∈ sitesBelow j x := by
  refine Finset.mem_image.2 ⟨0, ?_, ?_⟩
  · refine mem_centredCube_iff.2 fun k => ?_
    simp
  · have e : (fun k => (F.blockSide : ℤ) ^ (j - j) * siteCoords x k + (0 : Fin 4 → ℤ) k) = siteCoords x := by
      funext k
      simp
    show siteOfCoords j (fun k => (F.blockSide : ℤ) ^ (j - j) * siteCoords x k + (0 : Fin 4 → ℤ) k) = x
    rw [e]
    exact siteOfCoords_siteCoords x
theorem sum_sum_le_mul_sum {A B : Type} (Ps : Finset A) (Q : Finset B) (Qp : A → Finset B) (G : B → ℝ)
    (hG : ∀ q, 0 ≤ G q) (K : ℕ) (hsub : ∀ p ∈ Ps, Qp p ⊆ Q)
    (hmul : ∀ q ∈ Q, ∀ [DecidablePred fun p => q ∈ Qp p], ((Ps.filter fun p => q ∈ Qp p).card) ≤ K) :
    ∑ p ∈ Ps, ∑ q ∈ Qp p, G q ≤ K * ∑ q ∈ Q, G q := by
  classical
  calc ∑ p ∈ Ps, ∑ q ∈ Qp p, G q
      = ∑ p ∈ Ps, ∑ q ∈ Q, (if q ∈ Qp p then G q else 0) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (hsub p hp)]
    _ = ∑ q ∈ Q, ∑ p ∈ Ps, (if q ∈ Qp p then G q else 0) := Finset.sum_comm
    _ ≤ ∑ q ∈ Q, (K : ℝ) * G q := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmul q hq) (hG q)
    _ = _ := (Finset.mul_sum _ _ _).symm
theorem eq_of_mem_sitesBelow {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (hL : Odd F.blockSide) {x : F.Site i}
    {y y' : F.Site j} (h1 : x ∈ sitesBelow i y) (h2 : x ∈ sitesBelow i y') : y = y' := by
  obtain ⟨h, hh, e1⟩ := Finset.mem_image.1 h1
  obtain ⟨h', hh', e2⟩ := Finset.mem_image.1 h2
  have a1 := mem_centredCube_iff.1 hh
  have a2 := mem_centredCube_iff.1 hh'
  obtain ⟨q, hq⟩ := odd_blockSide_pow hL (j - i)
  set B := F.blockSide ^ (j - i) with hB
  have hBc : (F.blockSide : ℤ) ^ (j - i) = (B : ℤ) := by rw [hB]; push_cast; rfl
  have hhalf : ((B : ℤ) - 1) / 2 = q := by
    rw [hq]
    push_cast
    omega
  rw [hhalf] at a1 a2
  funext k
  have ek := congrFun (e1.trans e2.symm) k
  simp only [siteOfCoords, hBc] at ek
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_eq_pow_mul hij hj k] at ek
  push_cast at ek
  rw [hBc] at ek
  have hd : (B : ℤ) ∣ h' k - h k := by
    have h3 : (B : ℤ) ∣ (B : ℤ) * siteCoords y' k + h' k - ((B : ℤ) * siteCoords y k + h k) :=
      dvd_trans (Dvd.intro _ rfl) ek
    have h4 : (B : ℤ) * siteCoords y' k + h' k - ((B : ℤ) * siteCoords y k + h k) =
        (B : ℤ) * (siteCoords y' k - siteCoords y k) + (h' k - h k) := by ring
    rw [h4] at h3
    exact (dvd_add_right (Dvd.intro _ rfl)).1 h3
  have hz : h' k - h k = 0 := by
    have b1 := abs_le.1 (a1 k)
    have b2 := abs_le.1 (a2 k)
    refine Int.eq_zero_of_abs_lt_dvd hd ?_
    rw [abs_lt]
    constructor <;> omega
  have h4 : (B : ℤ) * siteCoords y' k + h' k - ((B : ℤ) * siteCoords y k + h k) =
      (B : ℤ) * (siteCoords y' k - siteCoords y k) := by
    have : h' k = h k := by omega
    rw [this]
    ring
  rw [h4] at ek
  have hB0 : (B : ℤ) ≠ 0 := by omega
  have h5 := (mul_dvd_mul_iff_left hB0).1 ek
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, siteCoords_cast, siteCoords_cast] at h5
  exact h5
theorem card_centredCube (M : ℕ) (hM : Odd M) : ((centredCube M).card : ℝ) = (M : ℝ) ^ 4 := by
  have h : ∀ i : Fin 4, (Finset.Icc (-(((M : ℤ) - 1) / 2)) (((M : ℤ) - 1) / 2)).card = M := by
    intro i
    rw [Int.card_Icc]
    obtain ⟨k, rfl⟩ := hM
    push_cast
    omega
  calc ((centredCube M).card : ℝ) = ((∏ i : Fin 4,
        (Finset.Icc (-(((M : ℤ) - 1) / 2)) (((M : ℤ) - 1) / 2)).card : ℕ) : ℝ) := by
        rw [centredCube, Fintype.card_piFinset]
    _ = ((∏ _i : Fin 4, M : ℕ) : ℝ) := by rw [Finset.prod_congr rfl fun i _ => h i]
    _ = _ := by simp
theorem quaternion_re_le_norm (q : ℍ[ℝ]) : q.re ≤ ‖q‖ := by
  have h : q.re ^ 2 ≤ ‖q‖ ^ 2 := by
    rw [sq ‖q‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
  exact (abs_le_of_sq_le_sq' h (norm_nonneg q)).2
theorem norm_eq_one_of_mem_unitary {q : ℍ[ℝ]} (hq : q ∈ unitary ℍ[ℝ]) : ‖q‖ = 1 := by
  have : q * star q = 1 := (Unitary.mem_iff.1 hq).2
  have h2 : ‖q‖ * ‖star q‖ = 1 := by
    rw [← norm_mul, this, norm_one]
  rw [Quaternion.norm_star] at h2
  nlinarith [norm_nonneg q]
theorem blockFit_nonneg {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    0 ≤ blockFit X X' c := by
  unfold blockFit
  have h := quaternion_re_le_norm (contourAverage X c * ((X' c.1 c.2)⁻¹ : UnitQuaternion))
  rw [norm_mul, norm_eq_one_of_mem_unitary ((X' c.1 c.2)⁻¹ : UnitQuaternion).2, mul_one] at h
  linarith
theorem plaquetteEnergy_nonneg (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    0 ≤ plaquetteEnergy U p := by
  unfold plaquetteEnergy
  have := quaternion_re_le_norm ((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ])
  rw [norm_eq_one_of_mem_unitary (plaquetteHolonomy U p).2] at this
  linarith
theorem sum_weight_le_energy_gap {A : Type} (Ex : Finset F.Cell) (I I₁ : Finset A) (val : A → ℝ)
    (hval : ∀ e, 0 ≤ val e) (hsub : I₁ ⊆ I) (touch : F.Cell → A → Prop) (w : F.Cell → A → ℝ)
    (hw : ∀ y e, touch y e → w y e ≤ val e) (hw0 : ∀ y e, ¬ touch y e → w y e ≤ 0)
    (hoff : ∀ y ∈ Ex, ∀ e ∈ I₁, ¬ touch y e)
    (hcount : ∀ e ∈ I, ∀ [DecidablePred fun y => touch y e], (Ex.filter fun y => touch y e).card ≤ 10000) :
    ∑ y ∈ Ex, ∑ e ∈ I, w y e ≤ (10000 : ℝ) * (∑ e ∈ I, val e - ∑ e ∈ I₁, val e) := by
  classical
  have h1 : ∑ e ∈ I, val e - ∑ e ∈ I₁, val e = ∑ e ∈ I \ I₁, val e := by
    rw [← Finset.sum_sdiff hsub]
    ring
  rw [h1]
  have h2 : ∀ y ∈ Ex, ∑ e ∈ I, w y e ≤ ∑ e ∈ I.filter (touch y), val e := by
    intro y _
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun e _ => ?_
    by_cases h : touch y e
    · rw [if_pos h]
      exact hw y e h
    · rw [if_neg h]
      exact hw0 y e h
  refine (Finset.sum_le_sum h2).trans ?_
  have := sum_sum_le_mul_sum Ex (I \ I₁) (fun y => I.filter (touch y)) val hval 10000 ?_ ?_
  · exact_mod_cast this
  · intro y hy e he
    have he' := Finset.mem_filter.1 he
    exact Finset.mem_sdiff.2 ⟨he'.1, fun h => hoff y hy e h he'.2⟩
  · intro e he _
    have := hcount e (Finset.mem_sdiff.1 he).1
    refine le_trans (Finset.card_le_card ?_) this
    intro y hy
    have hy' := Finset.mem_filter.1 hy
    exact Finset.mem_filter.2 ⟨hy'.1, (Finset.mem_filter.1 hy'.2).2⟩
theorem mem_cellBall_comm (y y' : F.Cell) (r : ℕ) (h : y' ∈ cellBall y r) : y ∈ cellBall y' r := by
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.1 h
  refine Finset.mem_image.2 ⟨fun i => - o i, ?_, ?_⟩
  · refine mem_centredCube_iff.2 fun k => ?_
    have := mem_centredCube_iff.1 ho k
    simpa using this
  · funext k
    simp [siteOfCoords]
theorem card_cellBall_three_le (y : F.Cell) : (cellBall y 3).card ≤ 2401 := by
  unfold cellBall
  refine Finset.card_image_le.trans ?_
  have h := card_centredCube (2 * 3 + 1) ⟨3, by norm_num⟩
  have : (centredCube (2 * 3 + 1)).card = 2401 := by
    have h2 : ((centredCube (2 * 3 + 1)).card : ℝ) = ((2401 : ℕ) : ℝ) := by
      rw [h]
      norm_num
    exact_mod_cast h2
  omega
theorem card_filter_sees_le {i : ℕ} (hi : i ≤ F.top) (hL : Odd F.blockSide) (Ex : Finset F.Cell)
    (A : Finset (F.Site i)) (hA : A.card ≤ 4) (sees : F.Cell → Prop) [DecidablePred sees]
    (h : ∀ y, sees y → ∃ x ∈ A, x ∈ cutBelow i (cellBall y 3)) :
    (Ex.filter sees).card ≤ 10000 := by
  classical
  let cellFn : F.Site i → F.Cell := fun x => if hx : ∃ c, x ∈ sitesBelow i c then hx.choose else 0
  have hsub : Ex.filter sees ⊆ A.biUnion fun x => cellBall (cellFn x) 3 := by
    intro y hy
    obtain ⟨x, hxA, hx⟩ := h y (Finset.mem_filter.1 hy).2
    refine Finset.mem_biUnion.2 ⟨x, hxA, ?_⟩
    simp only [cutBelow, Finset.mem_biUnion] at hx
    obtain ⟨y', hy', hxy⟩ := hx
    have hex : ∃ c, x ∈ sitesBelow i c := ⟨y', hxy⟩
    have e : cellFn x = y' := by
      simp only [cellFn, dif_pos hex]
      exact eq_of_mem_sitesBelow hi le_rfl hL hex.choose_spec hxy
    rw [e]
    exact mem_cellBall_comm _ _ _ hy'
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have h2 : ∑ x ∈ A, (cellBall (cellFn x) 3).card ≤ ∑ _x ∈ A, 2401 :=
    Finset.sum_le_sum fun x _ => card_cellBall_three_le _
  rw [Finset.sum_const, smul_eq_mul] at h2
  nlinarith
theorem cellSupDist_le_three (hs : ∀ i, 0 < F.extent i) {y y' : F.Cell} (h : y' ∈ cellBall y 3) :
    cellSupDist y' y ≤ 3 := by
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.1 h
  unfold cellSupDist
  refine Finset.sup_le fun k _ => ?_
  have hp : 0 < F.period F.top k := by simpa [BlockFrame.period] using hs k
  haveI : NeZero (F.period F.top k) := ⟨hp.ne'⟩
  have ho' := mem_centredCube_iff.1 ho k
  have e : (y + siteOfCoords F.top o : F.Cell) k - y k = ((o k : ℤ) : ZMod (F.period F.top k)) := by
    simp [siteOfCoords]
  rw [e]
  have h1 : (((o k : ℤ) : ZMod (F.period F.top k)).valMinAbs).natAbs ≤ (o k).natAbs := by
    refine ZMod.natAbs_min_of_le_div_two _ _ _ (by simp) (ZMod.natAbs_valMinAbs_le _)
  have h2 : (o k).natAbs ≤ 3 := by
    have h3 : |o k| ≤ 3 := by
      have : (((2 * 3 + 1 : ℕ) : ℤ) - 1) / 2 = 3 := by norm_num
      rwa [this] at ho'
    have := abs_le.1 h3
    omega
  omega
theorem cutPlaquettes_mono {l : ℕ} {Z Z' : Finset (F.Site l)} (h : Z ⊆ Z') :
    cutPlaquettes Z ⊆ cutPlaquettes Z' := by
  intro p hp
  simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp ⊢
  exact ⟨h hp.1, hp.2.1, hp.2.2.trans h⟩
theorem cutBonds_mono {l : ℕ} {Z Z' : Finset (F.Site l)} (h : Z ⊆ Z') : cutBonds Z ⊆ cutBonds Z' := by
  intro c hc
  simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc ⊢
  exact ⟨h hc.1, h hc.2⟩
theorem cutBelow_mono {m : ℕ} (i : ℕ) {Z Z' : Finset (F.Site m)} (h : Z ⊆ Z') :
    cutBelow i Z ⊆ cutBelow i Z' := Finset.biUnion_subset_biUnion_of_subset_left _ h
theorem contourFit_nonneg (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth)
    (W : F.GaugeField F.depth) (V : F.GaugeField F.top) (c : F.Cell × Fin 4) : 0 ≤ contourFit J₀ h b W V c := by
  unfold contourFit
  have h1 := quaternion_re_le_norm (contourMean J₀ h b W c * ((V c.1 c.2)⁻¹ : UnitQuaternion))
  rw [norm_mul, norm_eq_one_of_mem_unitary ((V c.1 c.2)⁻¹ : UnitQuaternion).2, mul_one] at h1
  linarith
attribute [local irreducible] cellBall
theorem not_mem_cutBelow_kept_of_ball {i : ℕ} (hi : i ≤ F.depth) (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {S₁ : Finset F.Cell} {Q₁ : Finset (F.Site F.depth)} (hQ : Q₁ ⊆ cutBelow F.depth S₁) {y : F.Cell}
    (hy : ∀ y₁ ∈ S₁, 10 < cellSupDist y₁ y) {x : F.Site i} (hx : x ∈ cutBelow i Q₁)
    (hb : x ∈ cutBelow i (cellBall y 3)) : False := by
  simp only [cutBelow, Finset.mem_biUnion] at hx hb
  obtain ⟨w, hw, hxw⟩ := hx
  obtain ⟨y', hy', hxy⟩ := hb
  have hw' := hQ hw
  simp only [cutBelow, Finset.mem_biUnion] at hw'
  obtain ⟨y₁, hy₁, hwy⟩ := hw'
  have hnt : F.depth ≤ F.top := by show F.depth ≤ F.depth + 1; omega
  have h1 := sitesBelow_trans hi hnt le_rfl hL y₁ hwy hxw
  have h2 := eq_of_mem_sitesBelow (hi.trans hnt) le_rfl hL h1 hxy
  rw [h2] at hy₁
  have := hy y' hy₁
  have := cellSupDist_le_three hs hy'
  omega
end ExcitedCells
attribute [local irreducible] cellBall
set_option maxHeartbeats 800000 in
theorem excitedCellsPay : excitedCellsPayStatement := by
  classical
  intro F L g a s θ C J₀ D S₁ ha hFL hL hT hsub hdist
  subst hFL
  have hs : ∀ i, 0 < F.extent i := by
    intro i
    have := hT.2
    rw [hT.1 i]
    omega
  have hnt : F.depth ≤ F.top := by show F.depth ≤ F.depth + 1; omega
  set Ex := D.excitedCells C with hEx
  set Q := D.chainSites with hQ
  set Q₁ := Q ∩ cutBelow F.depth S₁ with hQ₁
  have hQ₁Q : Q₁ ⊆ Q := Finset.inter_subset_left
  have hQ₁S : Q₁ ⊆ cutBelow F.depth S₁ := Finset.inter_subset_right
  have hspot : ∀ y ∈ Ex, ∀ y₁ ∈ S₁, 10 < cellSupDist y₁ y :=
    fun y hy y₁ hy₁ => hdist y₁ hy₁ y (Finset.mem_union_left _ hy)
  have p0 := ExcitedCells.sum_weight_le_energy_gap Ex (cutPlaquettes (cutBelow 0 Q))
    (cutPlaquettes (cutBelow 0 Q₁))
    (plaquetteEnergy (D.chain 0)) (ExcitedCells.plaquetteEnergy_nonneg _)
    (ExcitedCells.cutPlaquettes_mono (ExcitedCells.cutBelow_mono 0 hQ₁Q))
    (fun y p => ∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 (cellBall y 3))
    (fun y p => if ∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 (cellBall y 3) then plaquetteEnergy (D.chain 0) p else 0)
    (fun y p h => by rw [if_pos h]) (fun y p h => by rw [if_neg h])
    (fun y hy p hp h => by
      obtain ⟨x, hx, hxb⟩ := h
      have h1 := (Finset.mem_filter.1 hp).2.2 hx
      exact ExcitedCells.not_mem_cutBelow_kept_of_ball (Nat.zero_le _) hL hs hQ₁S (hspot y hy) h1 hxb)
    (fun p _ _ => ExcitedCells.card_filter_sees_le (Nat.zero_le _) hL Ex (plaquetteCorners p)
      Finset.card_le_four _ fun y h => h)
  have p1 : ∀ i ∈ Finset.range F.depth, ∑ y ∈ Ex, ∑ c ∈ cutBonds (cutBelow (i + 1) Q),
      (if c.1 ∈ cutBelow (i + 1) (cellBall y 3) ∨ c.1 + unitStep (i + 1) c.2 ∈ cutBelow (i + 1) (cellBall y 3)
        then blockFit (D.chain i) (D.chain (i + 1)) c else 0) ≤
      (10000 : ℝ) * (∑ c ∈ cutBonds (cutBelow (i + 1) Q), blockFit (D.chain i) (D.chain (i + 1)) c -
        ∑ c ∈ cutBonds (cutBelow (i + 1) Q₁), blockFit (D.chain i) (D.chain (i + 1)) c) := by
    intro i hi
    have hi' : i + 1 ≤ F.depth := Finset.mem_range.1 hi
    refine ExcitedCells.sum_weight_le_energy_gap Ex _ _ _ (ExcitedCells.blockFit_nonneg _ _)
      (ExcitedCells.cutBonds_mono (ExcitedCells.cutBelow_mono (i + 1) hQ₁Q))
      (fun y c => c.1 ∈ cutBelow (i + 1) (cellBall y 3) ∨
        c.1 + unitStep (i + 1) c.2 ∈ cutBelow (i + 1) (cellBall y 3))
      _ (fun y c h => by rw [if_pos h]) (fun y c h => by rw [if_neg h]) ?_ ?_
    · intro y hy c hc h
      have hc' := Finset.mem_filter.1 hc
      rcases h with h | h
      · exact ExcitedCells.not_mem_cutBelow_kept_of_ball hi' hL hs hQ₁S (hspot y hy)
          (Finset.mem_product.1 hc'.1).1 h
      · exact ExcitedCells.not_mem_cutBelow_kept_of_ball hi' hL hs hQ₁S (hspot y hy) hc'.2 h
    · intro c _ _
      refine ExcitedCells.card_filter_sees_le (hi'.trans hnt) hL Ex {c.1, c.1 + unitStep (i + 1) c.2}
        (Finset.card_le_two.trans (by norm_num)) _ fun y h => ?_
      rcases h with h | h
      · exact ⟨c.1, by simp, h⟩
      · exact ⟨c.1 + unitStep (i + 1) c.2, by simp, h⟩
  have p2 := ExcitedCells.sum_weight_le_energy_gap Ex (cutBonds D.cells) (cutBonds S₁) D.topBondFit
    (fun c => ExcitedCells.contourFit_nonneg _ _ _ _ _ c) (ExcitedCells.cutBonds_mono hsub)
    (fun y c => c.1 ∈ cellBall y 3 ∨ c.1 + unitStep F.top c.2 ∈ cellBall y 3)
    (fun y c => if c.1 ∈ cellBall y 3 ∨ c.1 + unitStep F.top c.2 ∈ cellBall y 3 then D.topBondFit c else 0)
    (fun y c h => by rw [if_pos h]) (fun y c h => by rw [if_neg h])
    (fun y hy c hc h => by
      have hc' := Finset.mem_filter.1 hc
      have hy3 := hspot y hy
      rcases h with h | h
      · have := hy3 _ (Finset.mem_product.1 hc'.1).1
        have := ExcitedCells.cellSupDist_le_three hs h
        omega
      · have := hy3 _ hc'.2
        have := ExcitedCells.cellSupDist_le_three hs h
        omega)
    (fun c _ _ => ExcitedCells.card_filter_sees_le le_rfl hL Ex {c.1, c.1 + unitStep F.top c.2}
      (Finset.card_le_two.trans (by norm_num)) _ fun y h => by
        have hself : ∀ x ∈ cellBall y 3, x ∈ cutBelow F.top (cellBall y 3) := fun x hx => by
          simp only [cutBelow, Finset.mem_biUnion]
          exact ⟨x, hx, ExcitedCells.self_mem_sitesBelow hL x⟩
        rcases h with h | h
        · exact ⟨c.1, by simp, hself _ h⟩
        · exact ⟨c.1 + unitStep F.top c.2, by simp, hself _ h⟩)
  have hover : ∀ y ∈ Ex, C * s ^ 2 ≤ D.energyOver (cellBall y 3) := fun y hy => (Finset.mem_filter.1 hy).2
  have h1 := Finset.sum_le_sum hover
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have hsum : ∑ y ∈ Ex, D.energyOver (cellBall y 3) ≤ 10 ^ 4 * (D.totalEnergy - D.energyOn S₁) := by
    have e1 : D.totalEnergy = cutChainEnergy a F.depth Q D.chain + a * ∑ c ∈ cutBonds D.cells, D.topBondFit c := by
      have e0 : D.chainSites ∩ cutBelow F.depth D.cells = D.chainSites :=
        Finset.inter_eq_left.2 Finset.sdiff_subset
      unfold HoleData.totalEnergy HoleData.energyOn
      rw [e0]
    have e2 : D.energyOn S₁ = cutChainEnergy a F.depth Q₁ D.chain + a * ∑ c ∈ cutBonds S₁, D.topBondFit c := rfl
    rw [e1, e2]
    unfold cutChainEnergy
    have q1 := Finset.sum_le_sum p1
    rw [← Finset.mul_sum, Finset.sum_sub_distrib] at q1
    have q2 := mul_le_mul_of_nonneg_left q1 ha
    have e3 : ∑ y ∈ Ex, D.energyOver (cellBall y 3) =
        ∑ y ∈ Ex, ∑ p ∈ cutPlaquettes (cutBelow 0 Q),
          (if ∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 (cellBall y 3) then plaquetteEnergy (D.chain 0) p else 0) +
        a * ∑ i ∈ Finset.range F.depth, ∑ y ∈ Ex, ∑ c ∈ cutBonds (cutBelow (i + 1) Q),
          (if c.1 ∈ cutBelow (i + 1) (cellBall y 3) ∨ c.1 + unitStep (i + 1) c.2 ∈ cutBelow (i + 1) (cellBall y 3)
            then blockFit (D.chain i) (D.chain (i + 1)) c else 0) +
        a * ∑ y ∈ Ex, ∑ c ∈ cutBonds D.cells,
          (if c.1 ∈ cellBall y 3 ∨ c.1 + unitStep F.top c.2 ∈ cellBall y 3 then D.topBondFit c else 0) := by
      rw [Finset.sum_comm (s := Finset.range F.depth), Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      unfold HoleData.energyOver
      congr
    rw [e3]
    have q3 := mul_le_mul_of_nonneg_left p2 ha
    set P0 := ∑ p ∈ cutPlaquettes (cutBelow 0 Q), plaquetteEnergy (D.chain 0) p
    set P1 := ∑ p ∈ cutPlaquettes (cutBelow 0 Q₁), plaquetteEnergy (D.chain 0) p
    set B0 := ∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) Q), blockFit (D.chain i) (D.chain (i + 1)) c
    set B1 := ∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) Q₁), blockFit (D.chain i) (D.chain (i + 1)) c
    set T0 := ∑ c ∈ cutBonds D.cells, D.topBondFit c
    set T1 := ∑ c ∈ cutBonds S₁, D.topBondFit c
    have e5 : (10 : ℝ) ^ 4 * (P0 + a * B0 + a * T0 - (P1 + a * B1 + a * T1)) =
        10000 * (P0 - P1) + a * (10000 * (B0 - B1)) + a * (10000 * (T0 - T1)) := by ring
    rw [e5]
    exact add_le_add (add_le_add p0 q2) q3
  have e4 : (Ex.card : ℝ) * (C * s ^ 2) = C * s ^ 2 * Ex.card := by ring
  rw [e4] at h1
  exact h1.trans hsum
end YangMills.Construction.HoleSavings
end
