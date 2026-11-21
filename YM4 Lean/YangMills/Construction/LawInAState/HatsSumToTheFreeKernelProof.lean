import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystemProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernel
import YangMills.Construction.LawInAState.PlaquettesAtASite
import YangMills.Construction.ResponseInTheExpansion.MeansOfAWeight
import YangMills.Construction.ResponseInTheExpansion.WeightsNearTheirMeans
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
open TorusFields WeightedResponses TorusMetric BoxResponses ReflectionKernel
open InfiniteLattice (AmbientSpace)
namespace BlockMeanKernelProof
private def cellIndex (a : ℝ) (x : AmbientSpace) : Fin 4 → ℤ := fun i => ⌊x i / a + 1 / 2⌋
private theorem cellIndex_near {a : ℝ} (ha : 0 < a) (x : AmbientSpace) (i : Fin 4) :
    |x i - (cellIndex a x i : ℝ) * a| ≤ a / 2 := by
  have h1 := Int.floor_le (x i / a + 1 / 2)
  have h2 := Int.lt_floor_add_one (x i / a + 1 / 2)
  simp only [cellIndex]
  set u := ⌊x i / a + 1 / 2⌋
  have e : x i = (x i / a) * a := by field_simp
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith
private def nearestLift {N : ℕ} (e : Fin 4 → ℤ) (y : TorusSite N) : Fin 4 → ℤ :=
  fun i => e i + (y i - ((e i : ℤ) : ZMod N)).valMinAbs
private theorem nearestLift_cast {N : ℕ} [NeZero N] (e : Fin 4 → ℤ) (y : TorusSite N) (i : Fin 4) :
    ((nearestLift e y i : ℤ) : ZMod N) = y i := by
  simp [nearestLift, ZMod.coe_valMinAbs]
private theorem nearestLift_near {N : ℕ} [NeZero N] (e : Fin 4 → ℤ) (y : TorusSite N) (i : Fin 4) :
    2 * |nearestLift e y i - e i| ≤ (N : ℤ) := by
  have h := ZMod.natAbs_valMinAbs_le (y i - ((e i : ℤ) : ZMod N))
  simp only [nearestLift, add_sub_cancel_left]
  have h2 : (((y i - ((e i : ℤ) : ZMod N)).valMinAbs).natAbs : ℤ) ≤ ((N / 2 : ℕ) : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at h2
  omega
private theorem valMinAbs_intCast_of_small {N : ℕ} [NeZero N] (w : ℤ) (h : 2 * |w| < (N : ℤ)) :
    ((w : ZMod N)).valMinAbs = w := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  have := abs_lt.mp (show |w| < |w| + 1 by omega)
  constructor
  · have := neg_abs_le w
    omega
  · have := le_abs_self w
    omega
abbrev _root_.YangMills.SharedProofs.p9640 := @valMinAbs_intCast_of_small
private theorem nearestLift_intCast {N : ℕ} [NeZero N] (e u : Fin 4 → ℤ) (h : ∀ i, 2 * |u i - e i| < (N : ℤ)) :
    nearestLift e (fun i => ((u i : ℤ) : ZMod N)) = u := by
  funext i
  simp only [nearestLift]
  rw [← Int.cast_sub, valMinAbs_intCast_of_small _ (h i)]
  ring
private theorem minimalSiteDiff_intCast {N : ℕ} [NeZero N] (u u' : Fin 4 → ℤ)
    (h : ∀ i, 2 * |u i - u' i| < (N : ℤ)) :
    minimalSiteDiff (fun i => ((u i : ℤ) : ZMod N)) (fun i => ((u' i : ℤ) : ZMod N)) = u - u' := by
  funext i
  simp only [minimalSiteDiff, Pi.sub_apply]
  rw [← Int.cast_sub, valMinAbs_intCast_of_small _ (h i)]
variable {L : ℕ} [NeZero L]
private theorem blockMean_near_const (hM : BlockMeanIsLinearAndLocal) (hW : WeightsCloseToBlockMeans) (hodd : Odd L)
    (t n : ℕ) [NeZero n] (y : TorusSite n) (w : PlaquetteWeight (fineSide L t n)) (c₀ δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ p, IsPlaquetteAt L t y p → |w p - c₀| ≤ δ) : |blockMean L t n y w - c₀| ≤ δ := by
  classical
  obtain ⟨h1, hlin, hread⟩ := hM L hodd t n y
  set h' : PlaquetteWeight (fineSide L t n) := fun p => if IsPlaquetteAt L t y p then w p - c₀ else 0 with hh'
  have e1 : blockMean L t n y h' = blockMean L t n y w - c₀ := by
    have := hlin 1 (-c₀) w (constOneWeight _)
    rw [h1] at this
    have e2 : blockMean L t n y h' = blockMean L t n y (fun p => 1 * w p + (-c₀) * constOneWeight _ p) := by
      refine hread _ _ fun p hp => ?_
      simp only [hh', if_pos hp, constOneWeight]
      ring
    rw [e2, this]
    ring
  rw [← e1]
  refine ((hW L hodd t n y).1 h').trans ?_
  refine Real.iSup_le (fun p => ?_) hδ
  simp only [hh']
  split_ifs with hp
  · exact h p.1 hp
  · simpa using hδ
abbrev _root_.YangMills.SharedProofs.p64490 := @blockMean_near_const
private theorem blockMean_eq_zero (hM : BlockMeanIsLinearAndLocal) (hW : WeightsCloseToBlockMeans) (hodd : Odd L)
    (t n : ℕ) [NeZero n] (y : TorusSite n) (w : PlaquetteWeight (fineSide L t n))
    (h : ∀ p, IsPlaquetteAt L t y p → w p = 0) :
    blockMean L t n y w = 0 := by
  have := blockMean_near_const hM hW hodd t n y w 0 0 le_rfl fun p hp => by simp [h p hp]
  simpa using this
private theorem periodize_eq_self {f : AmbientSpace → ℝ} {c z : AmbientSpace} {d : ℝ}
    (hf : ∀ x, f x ≠ 0 → ∀ i, |x i - c i| ≤ 6 * d)
    (hd : d ≤ 1 / 100) (hz : ∀ i, |z i - c i| ≤ 3 / 2) : periodizeUnitTorus f z = f z := by
  unfold periodizeUnitTorus
  rw [finsum_eq_single _ (0 : Fin 4 → ℤ)]
  · simp
  · intro ζ hζ
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hζ
    have h1 := hf _ hne i
    have h2 := abs_le.mp h1
    have h3 := abs_le.mp (hz i)
    have hi' : ζ i ≠ 0 := by simpa using hi
    have h4 : (1 : ℝ) ≤ |(ζ i : ℝ)| := by
      have : (1 : ℤ) ≤ |ζ i| := Int.one_le_abs hi'
      exact_mod_cast this
    rcases le_abs'.mp h4 with h5 | h5
    · linarith [h2.1, h2.2, h3.1, h3.2]
    · linarith [h2.1, h2.2, h3.1, h3.2]
private theorem boxSide_mul_spacing {K k : ℕ} (hk : k ≤ K) :
    ((boxSide L K k : ℕ) : ℝ) * ((L : ℝ) ^ k / (L : ℝ) ^ K) = 2 := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h1 : (L : ℝ) ^ (K - k) * (L : ℝ) ^ k = (L : ℝ) ^ K := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  simp only [boxSide]
  push_cast
  field_simp
  linarith
abbrev _root_.YangMills.SharedProofs.p9522 := @boxSide_mul_spacing
private theorem nearestLift_scaled {N : ℕ} [NeZero N] {a : ℝ} (ha : 0 < a) (hN : (N : ℝ) * a = 2)
    (e : Fin 4 → ℤ) (y : TorusSite N)
    (i : Fin 4) : |(nearestLift e y i : ℝ) * a - (e i : ℝ) * a| ≤ 1 := by
  have h := nearestLift_near e y i
  have h2 : 2 * |(nearestLift e y i : ℝ) - (e i : ℝ)| ≤ (N : ℝ) := by exact_mod_cast h
  rw [← sub_mul, abs_mul, abs_of_pos ha]
  nlinarith
private theorem plaquette_weight_value (hP : plaquetteWeightAtSiteStatement) (hodd : Odd L) {K k : ℕ} (hk : k ≤ K)
    {f : AmbientSpace → ℝ} {c : AmbientSpace} {d a : ℝ} (ha : a = (L : ℝ) ^ k / (L : ℝ) ^ K) (ha0 : 0 < a)
    (hf : ∀ x, f x ≠ 0 → ∀ i, |x i - c i| ≤ 6 * d)
    (hd : d ≤ 1 / 100) (ha1 : a ≤ 1 / 4) (y : TorusSite (boxSide L K k))
    (p : TorusPlaquette (fineSide L k (boxSide L K k)))
    (hp : IsPlaquetteAt L k y p) :
    ∃ θ : AmbientSpace, (∀ i, |θ i| ≤ a / 2) ∧
      unitTorusWeight L K k f p = f fun i => (nearestLift (cellIndex a c) y i : ℝ) * a + θ i := by
  obtain ⟨θ, hθ, hv⟩ := hP L hodd K k hk f y (nearestLift (cellIndex a c) y) (nearestLift_cast _ y) p hp
  rw [← ha] at hθ hv
  refine ⟨θ, hθ, ?_⟩
  rw [hv]
  refine periodize_eq_self hf hd fun i => ?_
  have hN := boxSide_mul_spacing (L := L) hk
  rw [← ha] at hN
  have h1 := nearestLift_scaled ha0 hN (cellIndex a c) y i
  have h2 := cellIndex_near ha0 c i
  have h3 := hθ i
  have b1 := abs_le.mp h1
  have b2 := abs_le.mp h2
  have b3 := abs_le.mp h3
  rw [abs_le]
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2]
private theorem blockMean_near_value (hM : BlockMeanIsLinearAndLocal) (hW : WeightsCloseToBlockMeans)
    (hP : plaquetteWeightAtSiteStatement) (hodd : Odd L) {K k : ℕ} (hk : k ≤ K) {f : AmbientSpace → ℝ}
    {c : AmbientSpace} {d a Λ : ℝ} (ha : a = (L : ℝ) ^ k / (L : ℝ) ^ K) (ha0 : 0 < a) (hΛ : 0 ≤ Λ)
    (hf : ∀ x, f x ≠ 0 → ∀ i, |x i - c i| ≤ 6 * d)
    (hl : ∀ (x x' : AmbientSpace) (t : ℝ), (∀ i, |x i - x' i| ≤ t) → |f x - f x'| ≤ Λ * t)
    (hd : d ≤ 1 / 100) (ha1 : a ≤ 1 / 4) (y : TorusSite (boxSide L K k)) :
    |blockMean L k (boxSide L K k) y (unitTorusWeight L K k f) -
      f fun i => (nearestLift (cellIndex a c) y i : ℝ) * a| ≤ Λ * a := by
  refine blockMean_near_const hM hW hodd k _ y _ _ _ (by positivity) fun p hp => ?_
  obtain ⟨θ, hθ, hv⟩ := plaquette_weight_value hP hodd hk ha ha0 hf hd ha1 y p hp
  rw [hv]
  have := hl (fun i => (nearestLift (cellIndex a c) y i : ℝ) * a + θ i)
    (fun i => (nearestLift (cellIndex a c) y i : ℝ) * a) a
    fun i => by
      have := hθ i
      simp only [add_sub_cancel_left]
      linarith
  exact this
private theorem exists_of_blockMean_ne_zero (hM : BlockMeanIsLinearAndLocal) (hW : WeightsCloseToBlockMeans)
    (hP : plaquetteWeightAtSiteStatement) (hodd : Odd L) {K k : ℕ} (hk : k ≤ K) {f : AmbientSpace → ℝ}
    {c : AmbientSpace} {d a : ℝ} (ha : a = (L : ℝ) ^ k / (L : ℝ) ^ K) (ha0 : 0 < a)
    (hf : ∀ x, f x ≠ 0 → ∀ i, |x i - c i| ≤ 6 * d)
    (hd : d ≤ 1 / 100) (ha1 : a ≤ 1 / 4) (y : TorusSite (boxSide L K k))
    (hne : blockMean L k (boxSide L K k) y (unitTorusWeight L K k f) ≠ 0) :
    ∃ x : AmbientSpace, f x ≠ 0 ∧ ∀ i, |(nearestLift (cellIndex a c) y i : ℝ) * a - x i| ≤ a / 2 := by
  by_contra hno
  push_neg at hno
  refine hne (blockMean_eq_zero hM hW hodd k _ y _ fun p hp => ?_)
  obtain ⟨θ, hθ, hv⟩ := plaquette_weight_value hP hodd hk ha ha0 hf hd ha1 y p hp
  rw [hv]
  by_contra hx
  obtain ⟨i, hi⟩ := hno _ hx
  have := hθ i
  simp only [sub_add_cancel_left, abs_neg] at hi
  linarith
private def cellSet (a : ℝ) (u : Fin 4 → ℤ) : Set AmbientSpace := {x | cellIndex a x = u}
private theorem cellSet_eq {a : ℝ} (ha : 0 < a) (u : Fin 4 → ℤ) :
    cellSet a u = Set.pi Set.univ fun i => Set.Ico (((u i : ℝ) - 1 / 2) * a) (((u i : ℝ) + 1 / 2) * a) := by
  ext x
  simp only [cellSet, Set.mem_setOf_eq, funext_iff, cellIndex, Int.floor_eq_iff, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ico]
  refine forall_congr' fun i => ?_
  have e : x i = (x i / a) * a := by field_simp
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor
    · have : ((u i : ℝ) - 1 / 2) ≤ x i / a := by rw [le_div_iff₀ ha]; exact h1
      linarith
    · have : x i / a < (u i : ℝ) + 1 / 2 := by rw [div_lt_iff₀ ha]; exact h2
      linarith
private theorem measurableSet_cellSet {a : ℝ} (ha : 0 < a) (u : Fin 4 → ℤ) : MeasurableSet (cellSet a u) := by
  rw [cellSet_eq ha]
  exact MeasurableSet.univ_pi fun i => measurableSet_Ico
private theorem volume_cellSet {a : ℝ} (ha : 0 < a) (u : Fin 4 → ℤ) :
    volume (cellSet a u) = ENNReal.ofReal (a ^ 4) := by
  rw [cellSet_eq ha, Real.volume_pi_Ico]
  have : ∀ i : Fin 4, ENNReal.ofReal (((u i : ℝ) + 1 / 2) * a - ((u i : ℝ) - 1 / 2) * a) = ENNReal.ofReal a := by
    intro i
    congr 1
    ring
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow ha.le]
private theorem indicator_term_integral {a : ℝ} (ha : 0 < a) (u u' : Fin 4 → ℤ) (t : ℝ) :
    Integrable (fun z : AmbientSpace × AmbientSpace =>
      if u = cellIndex a z.1 ∧ u' = cellIndex a z.2 then t else 0) ∧
    ∫ z : AmbientSpace × AmbientSpace, (if u = cellIndex a z.1 ∧ u' = cellIndex a z.2 then t else 0) =
      t * a ^ 8 := by
  have hS : (fun z : AmbientSpace × AmbientSpace => if u = cellIndex a z.1 ∧ u' = cellIndex a z.2 then t else 0) =
      (cellSet a u ×ˢ cellSet a u').indicator fun _ => t := by
    funext z
    simp only [Set.indicator, Set.mem_prod, cellSet, Set.mem_setOf_eq, eq_comm]
  have hm : MeasurableSet (cellSet a u ×ˢ cellSet a u') :=
    (measurableSet_cellSet ha u).prod (measurableSet_cellSet ha u')
  have hv : volume (cellSet a u ×ˢ cellSet a u') = ENNReal.ofReal (a ^ 8) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, volume_cellSet ha, volume_cellSet ha,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hS]
  constructor
  · refine (integrable_indicator_iff hm).mpr (integrableOn_const ?_)
    rw [hv]; exact ENNReal.ofReal_ne_top
  · rw [integral_indicator_const _ hm]
    simp only [Measure.real, hv, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
private theorem kernel_term_compare {F₁ F₂ A B e e' a Λ d : ℝ} (hF₁ : |F₁| ≤ 1) (hF₂ : |F₂| ≤ 1)
    (hA : |A - F₁| ≤ 2 * (Λ * a)) (hB : |B - F₂| ≤ 2 * (Λ * a)) (hΛa : Λ * a ≤ 1) (hd : 0 < d) (ha : 0 ≤ a)
    (hΛ : 0 ≤ Λ) (he : d / 2 ≤ e) (he' : d / 2 ≤ e') (hee : |e - e'| ≤ 2 * a) :
    |F₁ * F₂ * (e ^ 8)⁻¹ - A * B * (e' ^ 8)⁻¹| ≤ 8 * (Λ * a) * (2 / d) ^ 8 + 144 * a * (2 / d) ^ 9 := by
  set m := 2 / d with hm
  have hm0 : 0 < m := by positivity
  have he0 : 0 < e := by linarith
  have he0' : 0 < e' := by linarith
  set b := e⁻¹ with hb
  set b' := e'⁻¹ with hb'
  have hbm : b ≤ m := by
    rw [hb, hm, inv_le_comm₀ he0 (by positivity)]
    simpa using he
  have hbm' : b' ≤ m := by
    rw [hb', hm, inv_le_comm₀ he0' (by positivity)]
    simpa using he'
  have hb0 : 0 < b := inv_pos.mpr he0
  have hb0' : 0 < b' := inv_pos.mpr he0'
  have hbb : |b - b'| ≤ 2 * a * m ^ 2 := by
    have e1 : b - b' = (e' - e) * (b * b') := by
      rw [hb, hb']; field_simp
    rw [e1, abs_mul, abs_sub_comm, abs_of_pos (by positivity : 0 < b * b')]
    have : b * b' ≤ m ^ 2 := by rw [sq]; exact mul_le_mul hbm hbm' hb0'.le hm0.le
    exact mul_le_mul hee this (by positivity) (by positivity)
  have h8 : |b ^ 8 - b' ^ 8| ≤ 16 * a * m ^ 9 := by
    have h := abs_pow_sub_pow_le b b' 8
    have hmax : max |b| |b'| ≤ m := by
      rw [abs_of_pos hb0, abs_of_pos hb0']
      exact max_le hbm hbm'
    have h7 : max |b| |b'| ^ (8 - 1) ≤ m ^ 7 := pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax 7
    calc _ ≤ |b - b'| * (8 : ℕ) * max |b| |b'| ^ (8 - 1) := h
      _ ≤ (2 * a * m ^ 2) * (8 : ℕ) * m ^ 7 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hbb (by positivity)) h7 (by positivity) (by positivity)
      _ = _ := by push_cast; ring
  have hb8 : b ^ 8 ≤ m ^ 8 := pow_le_pow_left₀ hb0.le hbm 8
  have hA3 : |A| ≤ 3 := by
    have := abs_le.mp hA
    have := abs_le.mp hF₁
    rw [abs_le]; constructor <;> linarith [abs_le.mp hA, abs_le.mp hF₁]
  have hB3 : |B| ≤ 3 := by
    rw [abs_le]; constructor <;> linarith [abs_le.mp hB, abs_le.mp hF₂]
  have hFF : |F₁ * F₂ - A * B| ≤ 8 * (Λ * a) := by
    have e1 : F₁ * F₂ - A * B = -((A - F₁) * F₂) - A * (B - F₂) := by ring
    have k1 : |(A - F₁) * F₂| ≤ 2 * (Λ * a) * 1 := by
      rw [abs_mul]; exact mul_le_mul hA hF₂ (abs_nonneg _) (by positivity)
    have k2 : |A * (B - F₂)| ≤ 3 * (2 * (Λ * a)) := by
      rw [abs_mul]; exact mul_le_mul hA3 hB (abs_nonneg _) (by norm_num)
    rw [e1]
    have := abs_sub (-((A - F₁) * F₂)) (A * (B - F₂))
    rw [abs_neg] at this
    linarith
  have hAB : |A * B| ≤ 9 := by
    rw [abs_mul]; nlinarith [abs_nonneg A, abs_nonneg B]
  rw [← inv_pow, ← inv_pow, ← hb, ← hb']
  have e2 : F₁ * F₂ * b ^ 8 - A * B * b' ^ 8 = (F₁ * F₂ - A * B) * b ^ 8 + A * B * (b ^ 8 - b' ^ 8) := by ring
  rw [e2]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by positivity : 0 < b ^ 8)]
    exact mul_le_mul hFF hb8 (by positivity) (by positivity)
  · rw [abs_mul]
    calc _ ≤ 9 * (16 * a * m ^ 9) := mul_le_mul hAB h8 (abs_nonneg _) (by norm_num)
      _ = _ := by ring
private theorem euclidNormVec_add_le (u v : AmbientSpace) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
abbrev _root_.YangMills.SharedProofs.p2091 := @euclidNormVec_add_le
private theorem euclidNormVec_le {v : AmbientSpace} {s : ℝ} (hs : 0 ≤ s) (h : ∀ i, |v i| ≤ s) :
    euclidNormVec v ≤ 2 * s := by apply _root_.YangMills.Construction.ConfigSpace.ModeCost.sqrt_sum_sq_le_two_mul <;> assumption
abbrev _root_.YangMills.SharedProofs.p16936 := @euclidNormVec_le
private theorem abs_euclidNormVec_sub_le (u v : AmbientSpace) :
    |euclidNormVec u - euclidNormVec v| ≤ euclidNormVec (u - v) := by
  have h1 := euclidNormVec_add_le (u - v) v
  have h2 := euclidNormVec_add_le (v - u) u
  rw [sub_add_cancel] at h1 h2
  have e : euclidNormVec (v - u) = euclidNormVec (u - v) := by
    simp only [euclidNormVec, Pi.sub_apply]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e] at h2
  rw [abs_le]
  constructor <;> linarith
abbrev _root_.YangMills.DeltaSharedProofs.p501537 := @abs_euclidNormVec_sub_le
private theorem continuous_of_coord_lipschitz {f : AmbientSpace → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hl : ∀ (x x' : AmbientSpace) (t : ℝ), (∀ i, |x i - x' i| ≤ t) → |f x - f x'| ≤ Λ * t) : Continuous f := by
  refine (LipschitzWith.of_dist_le_mul (K := Λ.toNNReal) fun x x' => ?_).continuous
  rw [Real.dist_eq, Real.coe_toNNReal _ hΛ]
  exact hl x x' _ fun i => by
    have := dist_le_pi_dist x x' i
    rwa [Real.dist_eq] at this
private theorem closedBoxPair_measure (c : AmbientSpace) (r η : ℝ) (hr : 0 ≤ r) :
    MeasurableSet ((Set.pi Set.univ fun i => Set.Icc (c i - r) (c i + r)) ×ˢ
      (Set.pi Set.univ fun i => Set.Icc (c i - r) (c i + r)) : Set (AmbientSpace × AmbientSpace)) ∧
    volume ((Set.pi Set.univ fun i => Set.Icc (c i - r) (c i + r)) ×ˢ
      (Set.pi Set.univ fun i => Set.Icc (c i - r) (c i + r)) : Set (AmbientSpace × AmbientSpace)) =
      ENNReal.ofReal ((2 * r) ^ 8) := by
  have hm : MeasurableSet (Set.pi Set.univ fun i => Set.Icc (c i - r) (c i + r) : Set AmbientSpace) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  refine ⟨hm.prod hm, ?_⟩
  have hv : volume (Set.pi Set.univ fun i => Set.Icc (c i - r) (c i + r) : Set AmbientSpace) =
      ENNReal.ofReal ((2 * r) ^ 4) := by
    rw [show (Set.pi Set.univ fun i => Set.Icc (c i - r) (c i + r) : Set AmbientSpace) =
      Set.Icc (fun i => c i - r) (fun i => c i + r) from (Set.pi_univ_Icc _ _), Real.volume_Icc_pi]
    have : ∀ i : Fin 4, ENNReal.ofReal (c i + r - (c i - r)) = ENNReal.ofReal (2 * r) := fun i => by
      congr 1
      ring
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.ofReal_pow (by positivity)]
  rw [Measure.volume_eq_prod, Measure.prod_prod, hv, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring
private def meanAt (L K k : ℕ) [NeZero L] (f : AmbientSpace → ℝ) (y : TorusSite (boxSide L K k)) : ℝ :=
  blockMean L k (boxSide L K k) y (unitTorusWeight L K k f)
private def cellTerm (L K k : ℕ) [NeZero L] (a : ℝ) (f h : AmbientSpace → ℝ) (y w : TorusSite (boxSide L K k)) : ℝ :=
  meanAt L K k f y * meanAt L K k h w * (normSq (fun i => (minimalSiteDiff y w i : ℝ)) ^ 4)⁻¹ * (a ^ 8)⁻¹
private def stepKernel (L K k : ℕ) [NeZero L] (a : ℝ) (e : Fin 4 → ℤ) (f h : AmbientSpace → ℝ)
    (z : AmbientSpace × AmbientSpace) : ℝ :=
  ∑ y : TorusSite (boxSide L K k), ∑ w : TorusSite (boxSide L K k),
    if nearestLift e y = cellIndex a z.1 ∧ nearestLift e w = cellIndex a z.2 then cellTerm L K k a f h y w else 0
private def pairKernel (f h : AmbientSpace → ℝ) (z : AmbientSpace × AmbientSpace) : ℝ :=
  f z.1 * h z.2 * (euclidNormVec (z.1 - z.2) ^ 8)⁻¹
private theorem inverseEighthKernel_eq_integral (f h : AmbientSpace → ℝ) :
    TestFunctions.inverseEighthKernel f h = ∫ z, pairKernel f h z := by
  unfold TestFunctions.inverseEighthKernel pairKernel
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [zpow_neg]
private theorem stepKernel_integral {a : ℝ} (ha : 0 < a) (e : Fin 4 → ℤ) (K k : ℕ) (f h : AmbientSpace → ℝ) :
    Integrable (stepKernel L K k a e f h) ∧ ∫ z, stepKernel L K k a e f h z = blockMeanKernelSum L K k f h := by
  have hint : ∀ y w : TorusSite (boxSide L K k), Integrable fun z : AmbientSpace × AmbientSpace =>
      if nearestLift e y = cellIndex a z.1 ∧ nearestLift e w = cellIndex a z.2 then cellTerm L K k a f h y w else 0 :=
    fun y w => (indicator_term_integral ha _ _ _).1
  constructor
  · exact integrable_finset_sum _ fun y _ => integrable_finset_sum _ fun w _ => hint y w
  · unfold stepKernel blockMeanKernelSum
    rw [integral_finset_sum _ fun y _ => integrable_finset_sum _ fun w _ => hint y w]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [integral_finset_sum _ fun w _ => hint y w]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [(indicator_term_integral ha _ _ _).2]
    simp only [cellTerm, meanAt]
    field_simp
section Estimates
variable {K k : ℕ} {c : AmbientSpace} {d Λ a : ℝ} {f h : AmbientSpace → ℝ}
private theorem cellIndex_close (hk : k ≤ K) (hd1 : d ≤ 1 / 100) (ha : a = (L : ℝ) ^ k / (L : ℝ) ^ K) (ha0 : 0 < a)
    (ha1 : a ≤ 1 / 4) (x x' : AmbientSpace) (hx : ∀ i, |x i - x' i| ≤ 14 * d) (i : Fin 4) :
    2 * |cellIndex a x i - cellIndex a x' i| < ((boxSide L K k : ℕ) : ℤ) := by
  have hN := boxSide_mul_spacing (L := L) hk
  rw [← ha] at hN
  have b1 := abs_le.mp (cellIndex_near ha0 x i)
  have b2 := abs_le.mp (cellIndex_near ha0 x' i)
  have b3 := abs_le.mp (hx i)
  have h1 : |(cellIndex a x i : ℝ) - (cellIndex a x' i : ℝ)| * a < 1 := by
    rw [← abs_of_pos ha0, ← abs_mul, abs_of_pos ha0, sub_mul, abs_lt]
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2]
  have h2 : 2 * |(cellIndex a x i : ℝ) - (cellIndex a x' i : ℝ)| < ((boxSide L K k : ℕ) : ℝ) := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  exact_mod_cast h2
private def pairBox (c : AmbientSpace) (d : ℝ) : Set (AmbientSpace × AmbientSpace) :=
  (Set.pi Set.univ fun i => Set.Icc (c i - 7 * d) (c i + 7 * d)) ×ˢ
    (Set.pi Set.univ fun i => Set.Icc (c i - 7 * d) (c i + 7 * d))
private theorem mem_pairBox {z : AmbientSpace × AmbientSpace} :
    z ∈ pairBox c d ↔ (∀ i, |z.1 i - c i| ≤ 7 * d) ∧ ∀ i, |z.2 i - c i| ≤ 7 * d := by
  simp only [pairBox, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => ⟨by linarith [(h1 i).1], by linarith [(h1 i).2]⟩,
      fun i => ⟨by linarith [(h2 i).1], by linarith [(h2 i).2]⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => ⟨by linarith [(h1 i).1], by linarith [(h1 i).2]⟩,
      fun i => ⟨by linarith [(h2 i).1], by linarith [(h2 i).2]⟩⟩
private theorem pairKernel_outside (hM : BlockMeanIsLinearAndLocal) (hW : WeightsCloseToBlockMeans)
    (hP : plaquetteWeightAtSiteStatement) (hodd : Odd L) (hk : k ≤ K) (hp : IsLocalizedLipschitzPair c d Λ f h)
    (hd : 0 < d) (hd1 : d ≤ 1 / 100) (ha : a = (L : ℝ) ^ k / (L : ℝ) ^ K) (ha0 : 0 < a) (ha64 : 64 * a ≤ d)
    (z : AmbientSpace × AmbientSpace) (hz : z ∉ pairBox c d) :
    pairKernel f h z = 0 ∧ stepKernel L K k a (cellIndex a c) f h z = 0 := by
  have ha1 : a ≤ 1 / 4 := by linarith
  constructor
  · by_contra hne
    simp only [pairKernel, mul_ne_zero_iff] at hne
    obtain ⟨⟨h1, h2⟩, -⟩ := hne
    refine hz (mem_pairBox.mpr ⟨fun i => ?_, fun i => ?_⟩)
    · exact (hp.f_localized _ h1 i).trans (by linarith)
    · exact (hp.h_localized _ h2 i).trans (by linarith)
  · refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun w _ => ?_
    split_ifs with hc
    · by_contra hne
      simp only [cellTerm, mul_ne_zero_iff] at hne
      obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := hne
      obtain ⟨x₀, hx₀, hx₀'⟩ := exists_of_blockMean_ne_zero hM hW hP hodd hk ha ha0 hp.f_localized hd1 ha1 y h1
      obtain ⟨x₁, hx₁, hx₁'⟩ := exists_of_blockMean_ne_zero hM hW hP hodd hk ha ha0 hp.h_localized hd1 ha1 w h2
      refine hz (mem_pairBox.mpr ⟨fun i => ?_, fun i => ?_⟩)
      · have b1 := abs_le.mp (cellIndex_near ha0 z.1 i)
        have b2 := abs_le.mp (hx₀' i)
        have b3 := abs_le.mp (hp.f_localized _ hx₀ i)
        rw [hc.1] at b2
        rw [abs_le]
        constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2]
      · have b1 := abs_le.mp (cellIndex_near ha0 z.2 i)
        have b2 := abs_le.mp (hx₁' i)
        have b3 := abs_le.mp (hp.h_localized _ hx₁ i)
        rw [hc.2] at b2
        rw [abs_le]
        constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2]
    · rfl
private theorem pairKernel_inside (hM : BlockMeanIsLinearAndLocal) (hW : WeightsCloseToBlockMeans)
    (hP : plaquetteWeightAtSiteStatement) (hodd : Odd L) (hk : k ≤ K) (hp : IsLocalizedLipschitzPair c d Λ f h)
    (hd : 0 < d) (hΛ : 0 ≤ Λ) (hd1 : d ≤ 1 / 100) (ha : a = (L : ℝ) ^ k / (L : ℝ) ^ K) (ha0 : 0 < a)
    (ha64 : 64 * a ≤ d) (hΛa : Λ * a ≤ 1) (z : AmbientSpace × AmbientSpace) (hz : z ∈ pairBox c d) :
    |pairKernel f h z - stepKernel L K k a (cellIndex a c) f h z| ≤
      8 * (Λ * a) * (2 / d) ^ 8 + 144 * a * (2 / d) ^ 9 := by
  have ha1 : a ≤ 1 / 4 := by linarith
  obtain ⟨hz1, hz2⟩ := mem_pairBox.mp hz
  obtain ⟨x, x'⟩ := z
  simp only at hz1 hz2
  set e := cellIndex a c with he
  set u := cellIndex a x with hu
  set u' := cellIndex a x' with hu'
  have hue : ∀ i, 2 * |u i - e i| < ((boxSide L K k : ℕ) : ℤ) := fun i =>
    cellIndex_close hk hd1 ha ha0 ha1 x c (fun i => (hz1 i).trans (by linarith)) i
  have hue' : ∀ i, 2 * |u' i - e i| < ((boxSide L K k : ℕ) : ℤ) := fun i =>
    cellIndex_close hk hd1 ha ha0 ha1 x' c (fun i => (hz2 i).trans (by linarith)) i
  have huu : ∀ i, 2 * |u i - u' i| < ((boxSide L K k : ℕ) : ℤ) := fun i =>
    cellIndex_close hk hd1 ha ha0 ha1 x x' (fun i => by
      have b1 := abs_le.mp (hz1 i)
      have b2 := abs_le.mp (hz2 i)
      rw [abs_le]
      constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]) i
  set y₀ : TorusSite (boxSide L K k) := fun i => ((u i : ℤ) : ZMod (boxSide L K k)) with hy₀
  set w₀ : TorusSite (boxSide L K k) := fun i => ((u' i : ℤ) : ZMod (boxSide L K k)) with hw₀
  have hly : nearestLift e y₀ = u := nearestLift_intCast e u hue
  have hlw : nearestLift e w₀ = u' := nearestLift_intCast e u' hue'
  have hcast : ∀ y : TorusSite (boxSide L K k), nearestLift e y = u → y = y₀ := fun y hy => by
    funext i
    rw [hy₀]
    simp only
    rw [← hy, nearestLift_cast]
  have hcast' : ∀ y : TorusSite (boxSide L K k), nearestLift e y = u' → y = w₀ := fun y hy => by
    funext i
    rw [hw₀]
    simp only
    rw [← hy, nearestLift_cast]
  have hG : stepKernel L K k a e f h (x, x') = cellTerm L K k a f h y₀ w₀ := by
    unfold stepKernel
    simp only
    rw [Finset.sum_eq_single y₀, Finset.sum_eq_single w₀]
    · rw [if_pos ⟨hly, hlw⟩]
    · intro w _ hw
      rw [if_neg fun hc => hw (hcast' w hc.2)]
    · simp
    · intro y _ hy
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [if_neg fun hc => hy (hcast y hc.1)]
    · simp
  rw [hG]
  have hpos : 0 ≤ 8 * (Λ * a) * (2 / d) ^ 8 + 144 * a * (2 / d) ^ 9 := by positivity
  by_cases hsep : (f x ≠ 0 ∧ h x' ≠ 0) ∨ (meanAt L K k f y₀ ≠ 0 ∧ meanAt L K k h w₀ ≠ 0)
  · obtain ⟨x₀, x₁, hf₀, hh₁, hx₀, hx₁⟩ : ∃ x₀ x₁ : AmbientSpace, f x₀ ≠ 0 ∧ h x₁ ≠ 0 ∧
        (∀ i, |x i - x₀ i| ≤ a) ∧ ∀ i, |x' i - x₁ i| ≤ a := by
      rcases hsep with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨x, x', h1, h2, fun i => by simpa using ha0.le, fun i => by simpa using ha0.le⟩
      · obtain ⟨x₀, hx₀, hx₀'⟩ := exists_of_blockMean_ne_zero hM hW hP hodd hk ha ha0 hp.f_localized hd1 ha1 y₀ h1
        obtain ⟨x₁, hx₁, hx₁'⟩ := exists_of_blockMean_ne_zero hM hW hP hodd hk ha ha0 hp.h_localized hd1 ha1 w₀ h2
        refine ⟨x₀, x₁, hx₀, hx₁, fun i => ?_, fun i => ?_⟩
        · have b1 := abs_le.mp (cellIndex_near ha0 x i)
          have b2 := abs_le.mp (hx₀' i)
          rw [← he, hly] at b2
          rw [abs_le]
          constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
        · have b1 := abs_le.mp (cellIndex_near ha0 x' i)
          have b2 := abs_le.mp (hx₁' i)
          rw [← he, hlw] at b2
          rw [abs_le]
          constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
    have hsepd := hp.separated x₀ x₁ hf₀ hh₁
    set v : AmbientSpace := fun i => ((u i - u' i : ℤ) : ℝ) * a with hv
    have d1 : |euclidNormVec (x - x') - euclidNormVec (x₀ - x₁)| ≤ 4 * a := by
      refine (abs_euclidNormVec_sub_le _ _).trans ?_
      have := euclidNormVec_le (v := (x - x') - (x₀ - x₁)) (s := 2 * a) (by positivity) fun i => by
        have b1 := abs_le.mp (hx₀ i)
        have b2 := abs_le.mp (hx₁ i)
        simp only [Pi.sub_apply]
        rw [abs_le]
        constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
      linarith
    have d2 : |euclidNormVec (x - x') - euclidNormVec v| ≤ 2 * a := by
      refine (abs_euclidNormVec_sub_le _ _).trans ?_
      refine euclidNormVec_le (by positivity) fun i => ?_
      have b1 := abs_le.mp (cellIndex_near ha0 x i)
      have b2 := abs_le.mp (cellIndex_near ha0 x' i)
      simp only [Pi.sub_apply, hv]
      push_cast
      rw [abs_le]
      constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2]
    have e1 : d / 2 ≤ euclidNormVec (x - x') := by
      have := (abs_le.mp d1).1
      linarith
    have e2 : d / 2 ≤ euclidNormVec v := by
      have := (abs_le.mp d1).1
      have := (abs_le.mp d2).2
      linarith
    have hA : |meanAt L K k f y₀ - f x| ≤ 2 * (Λ * a) := by
      have k1 := blockMean_near_value hM hW hP hodd hk ha ha0 hΛ hp.f_localized hp.f_lipschitz hd1 ha1 y₀
      rw [← he, hly] at k1
      have k2 := hp.f_lipschitz (fun i => (u i : ℝ) * a) x (a / 2) fun i => by
        rw [abs_sub_comm]
        exact cellIndex_near ha0 x i
      have k3 := abs_sub_le (meanAt L K k f y₀) (f fun i => (u i : ℝ) * a) (f x)
      simp only [meanAt] at k3 ⊢
      nlinarith
    have hB : |meanAt L K k h w₀ - h x'| ≤ 2 * (Λ * a) := by
      have k1 := blockMean_near_value hM hW hP hodd hk ha ha0 hΛ hp.h_localized hp.h_lipschitz hd1 ha1 w₀
      rw [← he, hlw] at k1
      have k2 := hp.h_lipschitz (fun i => (u' i : ℝ) * a) x' (a / 2) fun i => by
        rw [abs_sub_comm]
        exact cellIndex_near ha0 x' i
      have k3 := abs_sub_le (meanAt L K k h w₀) (h fun i => (u' i : ℝ) * a) (h x')
      simp only [meanAt] at k3 ⊢
      nlinarith
    have hterm : cellTerm L K k a f h y₀ w₀ =
        meanAt L K k f y₀ * meanAt L K k h w₀ * (euclidNormVec v ^ 8)⁻¹ := by
      have hD : minimalSiteDiff y₀ w₀ = u - u' := minimalSiteDiff_intCast u u' huu
      have hs : euclidNormVec v ^ 2 = a ^ 2 * normSq (fun i => (minimalSiteDiff y₀ w₀ i : ℝ)) := by
        rw [euclidNormVec, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), hD]
        simp only [normSq, hv, Finset.mul_sum, Pi.sub_apply]
        exact Finset.sum_congr rfl fun i _ => by ring
      have h8 : euclidNormVec v ^ 8 = a ^ 8 * normSq (fun i => (minimalSiteDiff y₀ w₀ i : ℝ)) ^ 4 := by
        calc euclidNormVec v ^ 8 = (euclidNormVec v ^ 2) ^ 4 := by ring
          _ = _ := by rw [hs]; ring
      rw [h8, mul_inv]
      simp only [cellTerm]
      ring
    rw [hterm]
    exact kernel_term_compare (hp.abs_f_le x) (hp.abs_h_le x') hA hB hΛa hd ha0.le hΛ e1 e2 d2
  · push_neg at hsep
    have h0 : pairKernel f h (x, x') = 0 := by
      simp only [pairKernel]
      by_cases h1 : f x = 0
      · simp [h1]
      · simp [hsep.1 h1]
    have h00 : cellTerm L K k a f h y₀ w₀ = 0 := by
      simp only [cellTerm]
      by_cases h1 : meanAt L K k f y₀ = 0
      · simp [h1]
      · simp [hsep.2 h1]
    rw [h0, h00]
    simpa using hpos
end Estimates
end BlockMeanKernelProof
open BlockMeanKernelProof in
theorem blockMeanSumApproxKernel_of (hM : BlockMeanIsLinearAndLocal) (hW : WeightsCloseToBlockMeans)
    (hP : plaquetteWeightAtSiteStatement) : blockMeanSumApproxKernelStatement := by
  refine ⟨73728 * 14 ^ 8, by positivity, ?_⟩
  intro L _ hodd K k hk c d Λ f h hp hd hΛ hd1 ha64 hΛa
  have hLp : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (L : ℝ) ^ k / (L : ℝ) ^ K := ⟨_, rfl⟩
  rw [← ha] at ha64 hΛa ⊢
  have ha0 : 0 < a := by rw [ha]; positivity
  set η : ℝ := 8 * (Λ * a) * (2 / d) ^ 8 + 144 * a * (2 / d) ^ 9 with hη
  obtain ⟨hGi, hGv⟩ := stepKernel_integral (L := L) ha0 (cellIndex a c) K k f h
  set G := stepKernel L K k a (cellIndex a c) f h with hG
  set g : AmbientSpace × AmbientSpace → ℝ := (pairBox c d).indicator fun _ => η with hg
  obtain ⟨hBm, hBv⟩ := closedBoxPair_measure c (7 * d) η (by positivity)
  have hBm' : MeasurableSet (pairBox c d) := hBm
  have hBv' : volume (pairBox c d) = ENNReal.ofReal ((2 * (7 * d)) ^ 8) := hBv
  have hgi : Integrable g := by
    refine (integrable_indicator_iff hBm').mpr (integrableOn_const ?_)
    rw [hBv']; exact ENNReal.ofReal_ne_top
  have hpt : ∀ z, ‖pairKernel f h z - G z‖ ≤ g z := by
    intro z
    rw [Real.norm_eq_abs]
    by_cases hz : z ∈ pairBox c d
    · rw [hg, Set.indicator_of_mem hz]
      exact pairKernel_inside hM hW hP hodd hk hp hd hΛ hd1 ha ha0 ha64 hΛa z hz
    · obtain ⟨h1, h2⟩ := pairKernel_outside hM hW hP hodd hk hp hd hd1 ha ha0 ha64 z hz
      rw [hg, Set.indicator_of_notMem hz, h1, hG, h2]
      simp
  have hfm : Measurable f := (continuous_of_coord_lipschitz hΛ hp.f_lipschitz).measurable
  have hhm : Measurable h := (continuous_of_coord_lipschitz hΛ hp.h_lipschitz).measurable
  have hEm : Measurable fun z : AmbientSpace × AmbientSpace => (euclidNormVec (z.1 - z.2) ^ 8)⁻¹ := by
    have hc : Continuous fun z : AmbientSpace × AmbientSpace => euclidNormVec (z.1 - z.2) := by
      unfold euclidNormVec
      fun_prop
    exact (hc.measurable.pow_const 8).inv
  have hKm : Measurable (pairKernel f h) :=
    ((hfm.comp measurable_fst).mul (hhm.comp measurable_snd)).mul hEm
  have hKi : Integrable (pairKernel f h) := by
    refine Integrable.mono' (hGi.norm.add hgi) hKm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    have h1 := hpt z
    rw [Real.norm_eq_abs] at h1 ⊢
    have h2 := abs_sub_abs_le_abs_sub (pairKernel f h z) (G z)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    linarith
  have hint : ∫ z, (pairKernel f h z - G z) = (∫ z, pairKernel f h z) - ∫ z, G z := integral_sub hKi hGi
  have hnorm := norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hpt)
  rw [hint, Real.norm_eq_abs] at hnorm
  have hgv : ∫ z, g z = η * (2 * (7 * d)) ^ 8 := by
    rw [hg, integral_indicator_const _ hBm']
    simp only [Measure.real, hBv', smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [hgv] at hnorm
  rw [← hGv, inverseEighthKernel_eq_integral, abs_sub_comm]
  refine hnorm.trans ?_
  rw [hη]
  have e1 : (8 * (Λ * a) * (2 / d) ^ 8 + 144 * a * (2 / d) ^ 9) * (2 * (7 * d)) ^ 8 =
      14 ^ 8 * (2048 * (Λ * a) + 73728 * (a / d)) := by
    field_simp
    ring
  rw [e1]
  have q2 : 0 ≤ Λ * a := by positivity
  have : (2048 * (Λ * a) + 73728 * (a / d)) ≤ 73728 * (Λ * a + a / d) := by nlinarith
  calc _ ≤ (14 : ℝ) ^ 8 * (73728 * (Λ * a + a / d)) := mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring
end YangMills.Construction.StateLaws
end
