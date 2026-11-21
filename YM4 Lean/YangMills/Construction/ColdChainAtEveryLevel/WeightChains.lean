import YangMills.Construction.ColdChainAtEveryLevel.SeminormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace WeightedAverages
open BlockAverages BlockLines LatticePaths LatticeFractionalIntegration
variable {F : BlockFrame}
theorem sum_pow_le_of_pos_weights {ι : Type} (s : Finset ι) (a w : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hw : ∀ i ∈ s, 0 < w i) (p : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ s, a i) ^ p ≤ (∑ i ∈ s, w i) ^ (p - 1) * ∑ i ∈ s, a i ^ p * ((w i)⁻¹) ^ (p - 1) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rw [Finset.sum_empty, zero_pow (by omega)]
    simp
  set T := ∑ i ∈ s, w i with hT
  have hTpos : 0 < T := Finset.sum_pos hw hs
  have h1 := Real.pow_arith_mean_le_arith_mean_pow s (fun i => w i / T) (fun i => a i / w i)
    (fun i hi => (div_pos (hw i hi) hTpos).le) (by
      rw [← Finset.sum_div, ← hT]
      exact div_self hTpos.ne') (fun i hi => div_nonneg (ha i hi) (hw i hi).le) p
  have e1 : ∑ i ∈ s, w i / T * (a i / w i) = (∑ i ∈ s, a i) / T := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := (hw i hi).ne'
    field_simp
  have e2 : ∑ i ∈ s, w i / T * (a i / w i) ^ p = (∑ i ∈ s, a i ^ p * ((w i)⁻¹) ^ (p - 1)) / T := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne := (hw i hi).ne'
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [div_pow, inv_pow, pow_succ (w i) q]
    field_simp
  rw [e1, e2, div_pow] at h1
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [div_le_div_iff₀ (by positivity) hTpos] at h1
  have h2 : T ^ (q + 1) = T ^ q * T := pow_succ T q
  rw [h2] at h1
  have h3 : (∑ i ∈ s, a i) ^ (q + 1) * T ≤ (T ^ q * ∑ i ∈ s, a i ^ (q + 1) * ((w i)⁻¹) ^ q) * T := by
    calc _ ≤ (∑ i ∈ s, a i ^ (q + 1) * ((w i)⁻¹) ^ q) * (T ^ q * T) := h1
      _ = _ := by ring
  exact le_of_mul_le_mul_right h3 hTpos
def levelMean {l : ℕ} (G : F.Site l → Fin 4 → ℝ) (y : F.Site (l + 1)) (d : Fin 4) : ℝ :=
  (1 / (F.blockSide : ℝ)) * lineBlockAverage G (y, d)
def meanChain (i : ℕ) (base : (l : ℕ) → F.Site l → Fin 4 → ℝ) : (l : ℕ) → F.Site l → Fin 4 → ℝ
  | 0 => base 0
  | l + 1 => if l + 1 ≤ i then base (l + 1) else levelMean (meanChain i base l)
theorem lineBlockAverage_pos (hodd : Odd F.blockSide) {l : ℕ} {G : F.Site l → Fin 4 → ℝ}
    (hG : ∀ x d, 0 < G x d) (c : F.Site (l + 1) × Fin 4) : 0 < lineBlockAverage G c := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hne : (centredCube F.blockSide).Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_centredCube_iff]
    intro i
    have := hodd.pos
    simp only [Pi.zero_apply]
    omega
  have hr : (Finset.range F.blockSide).Nonempty := Finset.nonempty_range_iff.2 hodd.pos.ne'
  unfold lineBlockAverage
  refine mul_pos (by positivity) (Finset.sum_pos (fun h _ => Finset.sum_pos (fun r _ => hG _ _) hr) hne)
theorem meanChain_pos (hodd : Odd F.blockSide) (i : ℕ) {base : (l : ℕ) → F.Site l → Fin 4 → ℝ}
    (hb : ∀ l x d, 0 < base l x d) (l : ℕ) : ∀ (x : F.Site l) (d : Fin 4), 0 < meanChain i base l x d := by
  induction l with
  | zero => exact fun x d => hb 0 x d
  | succ l ih =>
    intro x d
    have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
    simp only [meanChain]
    split_ifs
    · exact hb _ _ _
    · exact mul_pos (by positivity) (lineBlockAverage_pos hodd (fun x d => ih x d) _)
theorem sum_lineBond_sum_le {B : Finset F.Cell} {l : ℕ} (hl : l < F.top) (hodd : Odd F.blockSide)
    (Y : Finset (F.Site (l + 1) × Fin 4)) (hY : Y ⊆ innerBonds B (l + 1)) (g : F.Site l × Fin 4 → ℝ)
    (hg : ∀ b, 0 ≤ g b) :
    ∑ c ∈ Y, ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, g (lineBond c h r) ≤
      F.blockSide * ∑ b ∈ innerBonds B l, g b := by
  have e : ∑ c ∈ Y, ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, g (lineBond c h r) =
      ∑ r ∈ Finset.range F.blockSide, ∑ c ∈ Y, ∑ h ∈ centredCube F.blockSide, g (lineBond c h r) := by
    calc _ = ∑ c ∈ Y, ∑ r ∈ Finset.range F.blockSide, ∑ h ∈ centredCube F.blockSide, g (lineBond c h r) :=
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [e]
  refine (Finset.sum_le_card_nsmul _ _ _ fun r hr =>
    sum_lineBond_le hl hodd Y hY g hg r (Finset.mem_range.1 hr)).trans ?_
  simp
theorem lineBlockAverage_weighted_pow_le {B : Finset F.Cell} {l : ℕ} (hl : l < F.top) (hodd : Odd F.blockSide)
    (Y : Finset (F.Site (l + 1) × Fin 4)) (hY : Y ⊆ innerBonds B (l + 1)) {G f : F.Site l → Fin 4 → ℝ}
    (hG : ∀ x d, 0 < G x d) (hf : ∀ x d, 0 ≤ f x d) (p : ℕ) (hp : 1 ≤ p) :
    ∑ c ∈ Y, lineBlockAverage f c ^ p * ((levelMean G c.1 c.2)⁻¹) ^ (p - 1) ≤
      ((F.blockSide : ℝ) ^ p / (F.blockSide : ℝ) ^ 4) *
        ∑ b ∈ innerBonds B l, f b.1 b.2 ^ p * ((G b.1 b.2)⁻¹) ^ (p - 1) := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  set s : Finset (Lattice4 × ℕ) := centredCube F.blockSide ×ˢ Finset.range F.blockSide with hs
  set g : F.Site l × Fin 4 → ℝ := fun b => f b.1 b.2 ^ p * ((G b.1 b.2)⁻¹) ^ (p - 1) with hgd
  have hg : ∀ b, 0 ≤ g b := fun b => mul_nonneg (pow_nonneg (hf _ _) _)
    (pow_nonneg (inv_nonneg.2 (hG _ _).le) _)
  have hone : ∀ c : F.Site (l + 1) × Fin 4, lineBlockAverage f c ^ p * ((levelMean G c.1 c.2)⁻¹) ^ (p - 1) ≤
      ((F.blockSide : ℝ) ^ p / (F.blockSide : ℝ) ^ 5) *
        ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, g (lineBond c h r) := by
    intro c
    set fs : Lattice4 × ℕ → ℝ := fun q => f (lineBond c q.1 q.2).1 (lineBond c q.1 q.2).2 with hfs
    set Gs : Lattice4 × ℕ → ℝ := fun q => G (lineBond c q.1 q.2).1 (lineBond c q.1 q.2).2 with hGs
    have hr := sum_pow_le_of_pos_weights s fs Gs (fun q _ => hf _ _) (fun q _ => hG _ _) p hp
    have ef : lineBlockAverage f c = (1 / (F.blockSide : ℝ) ^ 4) * ∑ q ∈ s, fs q := by
      rw [hs, Finset.sum_product]
      rfl
    have eG : levelMean G c.1 c.2 = (1 / (F.blockSide : ℝ) ^ 5) * ∑ q ∈ s, Gs q := by
      have : lineBlockAverage G (c.1, c.2) = (1 / (F.blockSide : ℝ) ^ 4) * ∑ q ∈ s, Gs q := by
        rw [hs, Finset.sum_product]
        rfl
      rw [levelMean, this, ← mul_assoc]
      congr 1
      field_simp
    have es : ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, g (lineBond c h r) =
        ∑ q ∈ s, fs q ^ p * ((Gs q)⁻¹) ^ (p - 1) := by
      rw [hs, Finset.sum_product]
    have hTpos : 0 < ∑ q ∈ s, Gs q := by
      have hne : s.Nonempty := by
        refine Finset.Nonempty.product ?_ (Finset.nonempty_range_iff.2 hodd.pos.ne')
        refine ⟨0, ?_⟩
        rw [mem_centredCube_iff]
        intro i
        have := hodd.pos
        simp only [Pi.zero_apply]
        omega
      exact Finset.sum_pos (fun q _ => hG _ _) hne
    rw [ef, eG, es, mul_pow]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hr ⊢
    set T := ∑ q ∈ s, Gs q with hT
    set A := ∑ q ∈ s, fs q with hA
    set E := ∑ q' ∈ s, fs q' ^ (q + 1) * ((Gs q')⁻¹) ^ q with hE
    have e1 : ((1 / (F.blockSide : ℝ) ^ 5 * T)⁻¹) ^ q = ((F.blockSide : ℝ) ^ 5) ^ q * (T⁻¹) ^ q := by
      rw [mul_inv, one_div, inv_inv, mul_pow]
    rw [e1]
    calc (1 / (F.blockSide : ℝ) ^ 4) ^ (q + 1) * A ^ (q + 1) * (((F.blockSide : ℝ) ^ 5) ^ q * (T⁻¹) ^ q)
        ≤ (1 / (F.blockSide : ℝ) ^ 4) ^ (q + 1) * (T ^ q * E) * (((F.blockSide : ℝ) ^ 5) ^ q * (T⁻¹) ^ q) := by
          gcongr
      _ = (F.blockSide : ℝ) ^ (q + 1) / (F.blockSide : ℝ) ^ 5 * E := by
          have hTq : T ^ q * (T⁻¹) ^ q = 1 := by
            rw [← mul_pow, mul_inv_cancel₀ hTpos.ne', one_pow]
          have e2 : (1 / (F.blockSide : ℝ) ^ 4) ^ (q + 1) * ((F.blockSide : ℝ) ^ 5) ^ q =
              (F.blockSide : ℝ) ^ (q + 1) / (F.blockSide : ℝ) ^ 5 := by
            rw [div_pow, one_pow, ← pow_mul, ← pow_mul, div_mul_eq_mul_div, one_mul,
              div_eq_div_iff (pow_ne_zero _ hL.ne') (pow_ne_zero _ hL.ne'), ← pow_add, ← pow_add]
            congr 1
            ring
          calc _ = ((1 / (F.blockSide : ℝ) ^ 4) ^ (q + 1) * ((F.blockSide : ℝ) ^ 5) ^ q) *
                (T ^ q * (T⁻¹) ^ q) * E := by ring
            _ = _ := by rw [e2, hTq, mul_one]
  refine (Finset.sum_le_sum fun c _ => hone c).trans ?_
  rw [← Finset.mul_sum]
  have h3 := sum_lineBond_sum_le hl hodd Y hY g hg
  calc _ ≤ (F.blockSide : ℝ) ^ p / (F.blockSide : ℝ) ^ 5 * (F.blockSide * ∑ b ∈ innerBonds B l, g b) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by
        field_simp
namespace Chains
theorem natAbs_valMinAbs_intCast_le (n : ℕ) (d : ℤ) : ((d : ZMod n).valMinAbs).natAbs ≤ d.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
theorem natAbs_valMinAbs_add_le (n : ℕ) (a b : ZMod n) :
    (a + b).valMinAbs.natAbs ≤ a.valMinAbs.natAbs + b.valMinAbs.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_add_le_add <;> assumption
theorem siteOfCoords_add_coords {j : ℕ} (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j a + siteOfCoords j b = siteOfCoords j fun i => a i + b i := by apply _root_.YangMills.Construction.BlockLines.siteOfCoords_add_fun <;> assumption
theorem baseSite_siteOfCoords {j : ℕ} (hj : j ≤ F.top) (t : Fin 4 → ℤ) :
    baseSite (siteOfCoords (F := F) j t) = siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ j * t i) := by
  funext i
  change (((F.blockSide : ℤ) ^ j * siteCoords (siteOfCoords (F := F) j t) i : ℤ) : ZMod (F.period 0 i)) =
    (((F.blockSide : ℤ) ^ j * t i : ℤ) : ZMod (F.period 0 i))
  rw [siteCoords_siteOfCoords]
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 ?_
  have hp : (F.period 0 i : ℤ) = (F.blockSide : ℤ) ^ j * (F.period j i : ℤ) := by
    rw [period_eq, period_eq, Nat.sub_zero]
    have : F.top = j + (F.top - j) := by omega
    conv_lhs => rw [this, pow_add]
    ring
  rw [hp]
  refine ⟨t i / (F.period j i : ℤ), ?_⟩
  have := Int.emod_add_mul_ediv (t i) (F.period j i : ℤ)
  linear_combination (-(F.blockSide : ℤ) ^ j) * this
theorem baseSite_refineSite_add {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (g : Fin 4 → ℤ) :
    baseSite (refineSite y + siteOfCoords j g) =
      baseSite y + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ j * g i) := by
  have e : refineSite y + siteOfCoords j g =
      siteOfCoords j (fun l => (F.blockSide : ℤ) * siteCoords y l + g l) := by
    simp only [refineSite]
    rw [siteOfCoords_add_coords]
  rw [e, baseSite_siteOfCoords hj.le]
  simp only [baseSite]
  rw [siteOfCoords_add_coords]
  congr 1
  funext i
  rw [pow_succ]
  ring
theorem baseDistance_refineSite_add {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (g : Fin 4 → ℤ) (G : ℕ)
    (hG : ∀ i, (g i).natAbs ≤ G) (p : F.Site 0) :
    baseDistance (refineSite y + siteOfCoords j g) p ≤ baseDistance y p + F.blockSide ^ j * G ∧
      baseDistance y p ≤ baseDistance (refineSite y + siteOfCoords j g) p + F.blockSide ^ j * G := by
  have hcast : ∀ i, (((F.blockSide : ℤ) ^ j * g i).natAbs) ≤ F.blockSide ^ j * G := by
    intro i
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (hG i)
  have hcast' : ∀ i, ((-((F.blockSide : ℤ) ^ j * g i)).natAbs) ≤ F.blockSide ^ j * G := by
    intro i
    rw [Int.natAbs_neg]
    exact hcast i
  have hx : ∀ i, (baseSite (refineSite y + siteOfCoords j g) - p : F.Site 0) i =
      (baseSite y - p : F.Site 0) i + ((((F.blockSide : ℤ) ^ j * g i : ℤ)) : ZMod (F.period 0 i)) := by
    intro i
    rw [baseSite_refineSite_add hj]
    simp only [Pi.sub_apply, Pi.add_apply, siteOfCoords]
    ring
  constructor
  · apply Finset.sup_le
    intro i _
    rw [hx]
    refine le_trans (natAbs_valMinAbs_add_le _ _ _) ?_
    have h1 : (((baseSite y - p : F.Site 0) i).valMinAbs).natAbs ≤ baseDistance y p :=
      Finset.le_sup (f := fun i => (((baseSite y - p : F.Site 0) i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h2 := le_trans (natAbs_valMinAbs_intCast_le (F.period 0 i) ((F.blockSide : ℤ) ^ j * g i)) (hcast i)
    omega
  · apply Finset.sup_le
    intro i _
    have hy : (baseSite y - p : F.Site 0) i = (baseSite (refineSite y + siteOfCoords j g) - p : F.Site 0) i +
        (((-((F.blockSide : ℤ) ^ j * g i) : ℤ)) : ZMod (F.period 0 i)) := by
      rw [hx]
      push_cast
      ring
    rw [hy]
    refine le_trans (natAbs_valMinAbs_add_le _ _ _) ?_
    have h1 : (((baseSite (refineSite y + siteOfCoords j g) - p : F.Site 0) i).valMinAbs).natAbs ≤
        baseDistance (refineSite y + siteOfCoords j g) p :=
      Finset.le_sup (f := fun i => (((baseSite (refineSite y + siteOfCoords j g) - p : F.Site 0) i).valMinAbs).natAbs)
        (Finset.mem_univ i)
    have h2 := le_trans (natAbs_valMinAbs_intCast_le (F.period 0 i) (-((F.blockSide : ℤ) ^ j * g i))) (hcast' i)
    omega
theorem scaleRadius_pos (hL : 0 < F.blockSide) (j : ℕ) (p : F.Site 0) (x : F.Site j) :
    0 < scaleRadius F j p x := by apply _root_.YangMills.Construction.CoordinateSeminorms.scaleRadius_pos <;> assumption
theorem period_zero_eq {l : ℕ} (hl : l ≤ F.top) (i : Fin 4) :
    (F.period 0 i : ℤ) = (F.blockSide : ℤ) ^ l * (F.period l i : ℤ) := by
  rw [period_eq, period_eq, Nat.sub_zero]
  have : F.top = l + (F.top - l) := by omega
  conv_lhs => rw [this, pow_add]
  ring
theorem natAbs_le_baseDistance {l : ℕ} (x : F.Site l) (p : F.Site 0) (i : Fin 4) :
    (((baseSite x - p : F.Site 0) i).valMinAbs).natAbs ≤ baseDistance x p :=
  Finset.le_sup (f := fun i => (((baseSite x - p : F.Site 0) i).valMinAbs).natAbs) (Finset.mem_univ i)
theorem card_le_of_baseDistance_le {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide) (X : Finset (F.Site l))
    (p : F.Site 0) (r : ℕ) (hX : ∀ x ∈ X, baseDistance x p ≤ r) :
    X.card ≤ (2 * r / F.blockSide ^ l + 1) ^ 4 := by
  classical
  have hR : (0 : ℤ) < (F.blockSide : ℤ) ^ l := by
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hL
    positivity
  set R₀ : ℤ := (F.blockSide : ℤ) ^ l with hR₀
  set T : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (0 : ℤ) (2 * (r : ℤ) / R₀) with hT
  have hTc : T.card = (2 * r / F.blockSide ^ l + 1) ^ 4 := by
    simp only [hT, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
  rw [← hTc]
  set vm : F.Site l → Fin 4 → ℤ := fun x i => ((baseSite x - p : F.Site 0) i).valMinAbs with hvm
  have hbd : ∀ x ∈ X, ∀ i, -(r : ℤ) ≤ vm x i ∧ vm x i ≤ r := by
    intro x hx i
    have h1 := natAbs_le_baseDistance x p i
    have h2 := hX x hx
    simp only [hvm]
    omega
  apply Finset.card_le_card_of_injOn (fun x i => (vm x i + r) / R₀)
  · intro x hx
    refine Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun i => ?_)
    obtain ⟨h1, h2⟩ := hbd x (Finset.mem_coe.1 hx) i
    rw [Finset.mem_Icc]
    exact ⟨Int.ediv_nonneg (by omega) hR.le, Int.ediv_le_ediv hR (by omega)⟩
  · intro x hx x' hx' e
    funext i
    have he := congrFun e i
    simp only at he
    obtain ⟨h1, h2⟩ := hbd x (Finset.mem_coe.1 hx) i
    obtain ⟨h1', h2'⟩ := hbd x' (Finset.mem_coe.1 hx') i
    set A := vm x i with hA
    set A' := vm x' i with hA'
    have hcA : ((A : ℤ) : ZMod (F.period 0 i)) = (baseSite x - p : F.Site 0) i := ZMod.coe_valMinAbs _
    have hcA' : ((A' : ℤ) : ZMod (F.period 0 i)) = (baseSite x' - p : F.Site 0) i := ZMod.coe_valMinAbs _
    set a := siteCoords x i with ha
    set a' := siteCoords x' i with ha'
    have hxb : (baseSite x : F.Site 0) i = ((R₀ * a : ℤ) : ZMod (F.period 0 i)) := rfl
    have hxb' : (baseSite x' : F.Site 0) i = ((R₀ * a' : ℤ) : ZMod (F.period 0 i)) := rfl
    have hdiff : ((A - A' : ℤ) : ZMod (F.period 0 i)) = ((R₀ * (a - a') : ℤ) : ZMod (F.period 0 i)) := by
      rw [Int.cast_sub, hcA, hcA', Pi.sub_apply, Pi.sub_apply, hxb, hxb', sub_sub_sub_cancel_right,
        ← Int.cast_sub, mul_sub]
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hdiff
    rw [period_zero_eq hl i] at hq
    have hdvd : R₀ ∣ A - A' := by
      refine ⟨(a - a') - (F.period l i : ℤ) * q, ?_⟩
      linear_combination (-1 : ℤ) * hq
    have hmod1 := Int.emod_add_mul_ediv (A + r) R₀
    have hmod2 := Int.emod_add_mul_ediv (A' + r) R₀
    rw [he] at hmod1
    have hb1 := Int.emod_nonneg (A + r) hR.ne'
    have hb2 := Int.emod_lt_of_pos (A + r) hR
    have hb3 := Int.emod_nonneg (A' + r) hR.ne'
    have hb4 := Int.emod_lt_of_pos (A' + r) hR
    have habs : |A - A'| < R₀ := by
      rw [abs_lt]
      constructor <;> linarith
    have hz := Int.eq_zero_of_abs_lt_dvd hdvd habs
    have hAA : A = A' := by omega
    have hsame : (baseSite x : F.Site 0) i = baseSite x' i := by
      have h3 : (baseSite x - p : F.Site 0) i = (baseSite x' - p : F.Site 0) i := by
        rw [← hcA, ← hcA', hAA]
      simpa using h3
    have hcast : ((R₀ * a : ℤ) : ZMod (F.period 0 i)) = ((R₀ * a' : ℤ) : ZMod (F.period 0 i)) := by
      rw [← hxb, ← hxb', hsame]
    obtain ⟨q2, hq2⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hcast
    rw [period_zero_eq hl i] at hq2
    have hq3 : a' - a = (F.period l i : ℤ) * q2 := by
      apply mul_left_cancel₀ hR.ne'
      linear_combination hq2
    have hxc := (ZMod.intCast_eq_intCast_iff_dvd_sub a a' (F.period l i)).2 ⟨q2, hq3⟩
    have hx1 : ((a : ℤ) : ZMod (F.period l i)) = x i := ZMod.intCast_zmod_cast (x i)
    have hx2 : ((a' : ℤ) : ZMod (F.period l i)) = x' i := ZMod.intCast_zmod_cast (x' i)
    rw [← hx1, ← hx2, hxc]
theorem pow_le_scaleRadius {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide) (p : F.Site 0) (x : F.Site l) :
    (F.blockSide : ℝ) ^ l ≤ scaleRadius F l p x := by
  have h1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  simp only [scaleRadius]
  exact le_min (pow_le_pow_right₀ h1 hl) (le_max_left _ _)
theorem card_scaleRadius_lt {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide) (X : Finset (F.Site l))
    (p : F.Site 0) (m : ℕ) (hm : 2 ^ m * F.blockSide ^ l ≤ F.blockSide ^ F.top) :
    ((X.filter fun x => scaleRadius F l p x < ((2 ^ m * F.blockSide ^ l : ℕ) : ℝ)).card : ℝ) ≤ 81 * 16 ^ m := by
  classical
  have hcount := card_le_of_baseDistance_le hl hL
    (X.filter fun x => scaleRadius F l p x < ((2 ^ m * F.blockSide ^ l : ℕ) : ℝ)) p
    (2 ^ m * F.blockSide ^ l) (by
      intro x hx
      have h1 := (Finset.mem_filter.1 hx).2
      simp only [scaleRadius] at h1
      have hN : ((2 ^ m * F.blockSide ^ l : ℕ) : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := by exact_mod_cast hm
      rcases min_lt_iff.1 h1 with h2 | h2
      · linarith
      · have h3 : ((baseDistance x p : ℕ) : ℝ) < ((2 ^ m * F.blockSide ^ l : ℕ) : ℝ) :=
          lt_of_le_of_lt (le_max_right _ _) h2
        have h4 : baseDistance x p < 2 ^ m * F.blockSide ^ l := by exact_mod_cast h3
        exact h4.le)
  have hpos : 0 < F.blockSide ^ l := by positivity
  have e : 2 * (2 ^ m * F.blockSide ^ l) / F.blockSide ^ l = 2 * 2 ^ m := by
    rw [← mul_assoc]
    exact Nat.mul_div_cancel _ hpos
  rw [e] at hcount
  have h5 : (2 * 2 ^ m + 1) ^ 4 ≤ 81 * 16 ^ m := by
    have h6 : 2 * 2 ^ m + 1 ≤ 3 * 2 ^ m := by
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    calc (2 * 2 ^ m + 1) ^ 4 ≤ (3 * 2 ^ m) ^ 4 := Nat.pow_le_pow_left h6 4
      _ = 81 * 16 ^ m := by
          rw [mul_pow, ← pow_mul, mul_comm m 4, pow_mul]
          norm_num
  have h7 := le_trans hcount h5
  exact_mod_cast h7
theorem levelMean_le (hodd : Odd F.blockSide) {l : ℕ} {g : F.Site l → Fin 4 → ℝ} {y : F.Site (l + 1)}
    {d : Fin 4} {b : ℝ}
    (h : ∀ h ∈ centredCube F.blockSide, ∀ r ∈ Finset.range F.blockSide,
      g (lineBond (y, d) h r).1 (lineBond (y, d) h r).2 ≤ b) :
    levelMean g y d ≤ b := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have h1 : ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
      g (lineBond (y, d) h r).1 (lineBond (y, d) h r).2 ≤
      ∑ h ∈ centredCube F.blockSide, (F.blockSide : ℝ) * b := by
    refine Finset.sum_le_sum fun h' hh => ?_
    refine (Finset.sum_le_card_nsmul _ _ b (h h' hh)).trans ?_
    simp
  rw [Finset.sum_const, LatticePaths.card_centredCube hodd, nsmul_eq_mul] at h1
  have e : lineBlockAverage g (y, d) = 1 / (F.blockSide : ℝ) ^ 4 *
      ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        g (lineBond (y, d) h r).1 (lineBond (y, d) h r).2 := rfl
  rw [levelMean, e]
  calc _ ≤ 1 / (F.blockSide : ℝ) * (1 / (F.blockSide : ℝ) ^ 4 *
        (((F.blockSide ^ 4 : ℕ) : ℝ) * ((F.blockSide : ℝ) * b))) := by gcongr
    _ = b := by
        push_cast
        field_simp
theorem meanChain_of_le (i : ℕ) (base : (l : ℕ) → F.Site l → Fin 4 → ℝ) {l : ℕ} (h : l ≤ i) :
    meanChain i base l = base l := by
  cases l with
  | zero => rfl
  | succ l => simp [meanChain, h]
theorem meanChain_succ (i : ℕ) (base : (l : ℕ) → F.Site l → Fin 4 → ℝ) {l : ℕ} (h : i ≤ l) :
    meanChain i base (l + 1) = levelMean (meanChain i base l) := by
  have : ¬ l + 1 ≤ i := by omega
  simp [meanChain, this]
theorem baseDistance_lineBond {l : ℕ} (hl : l < F.top) (c : F.Site (l + 1) × Fin 4) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) {r : ℕ} (hr : r ∈ Finset.range F.blockSide) (p : F.Site 0) :
    ((baseDistance (lineBond c h r).1 p : ℕ) : ℝ) ≤ baseDistance c.1 p + 2 * (F.blockSide : ℝ) ^ (l + 1) ∧
      ((baseDistance c.1 p : ℕ) : ℝ) ≤
        baseDistance (lineBond c h r).1 p + 2 * (F.blockSide : ℝ) ^ (l + 1) := by
  have hr' := Finset.mem_range.1 hr
  have hb : ∀ i, ((h + (r : ℤ) • basisVector c.2) i).natAbs ≤ 2 * F.blockSide := by
    intro i
    have h1 := (mem_centredCube_iff F.blockSide h).1 hh i
    have h2 : |((r : ℤ) • basisVector c.2) i| ≤ F.blockSide := by
      by_cases hi : i = c.2
      · subst hi
        simp [basisVector]
        omega
      · simp [basisVector, hi]
    simp only [Pi.add_apply] at h2 ⊢
    have := abs_le.1 h2
    omega
  obtain ⟨a, b⟩ := baseDistance_refineSite_add hl c.1 (h + (r : ℤ) • basisVector c.2) (2 * F.blockSide) hb p
  rw [← lineBond_fst c h r] at a b
  have e : ((F.blockSide ^ l * (2 * F.blockSide) : ℕ) : ℝ) = 2 * (F.blockSide : ℝ) ^ (l + 1) := by
    push_cast
    ring
  have a' : ((baseDistance (lineBond c h r).1 p : ℕ) : ℝ) ≤
      ((baseDistance c.1 p + F.blockSide ^ l * (2 * F.blockSide) : ℕ) : ℝ) := by exact_mod_cast a
  have b' : ((baseDistance c.1 p : ℕ) : ℝ) ≤
      ((baseDistance (lineBond c h r).1 p + F.blockSide ^ l * (2 * F.blockSide) : ℕ) : ℝ) := by
    exact_mod_cast b
  rw [Nat.cast_add, e] at a' b'
  exact ⟨a', b'⟩
def radiusPower (p : F.Site 0) (κ : ℝ) : (l : ℕ) → F.Site l → Fin 4 → ℝ :=
  fun l x _ => scaleRadius F l p x ^ κ
theorem meanChain_radiusPower_le_of_nonneg (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) (p : F.Site 0)
    {κ : ℝ} (hκ : 0 ≤ κ) (i l : ℕ) (hil : i ≤ l) (hl : l ≤ F.top) : ∀ (x : F.Site l) (d : Fin 4),
      meanChain i (radiusPower p κ) l x d ≤
        (min ((F.blockSide : ℝ) ^ F.top) ((baseDistance x p : ℝ) + 4 * (F.blockSide : ℝ) ^ l)) ^ κ := by
  have hL2 : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast h2
  induction l, hil using Nat.le_induction with
  | base =>
    intro x d
    rw [meanChain_of_le i _ le_rfl]
    have h1 : scaleRadius F i p x ≤
        min ((F.blockSide : ℝ) ^ F.top) ((baseDistance x p : ℝ) + 4 * (F.blockSide : ℝ) ^ i) := by
      simp only [scaleRadius]
      refine min_le_min le_rfl (max_le ?_ ?_)
      · have : (0 : ℝ) ≤ baseDistance x p := by positivity
        have : (0 : ℝ) < (F.blockSide : ℝ) ^ i := by positivity
        linarith
      · have : (0 : ℝ) < (F.blockSide : ℝ) ^ i := by positivity
        linarith
    exact Real.rpow_le_rpow (scaleRadius_pos hodd.pos _ _ _).le h1 hκ
  | succ l hil ih =>
    intro y d
    rw [meanChain_succ i _ hil]
    refine levelMean_le hodd fun h hh r hr => ?_
    refine (ih (by omega) _ _).trans ?_
    have hd := (baseDistance_lineBond (by omega) (y, d) hh hr p).1
    have hnn : (0 : ℝ) ≤ min ((F.blockSide : ℝ) ^ F.top)
        ((baseDistance (lineBond (y, d) h r).1 p : ℝ) + 4 * (F.blockSide : ℝ) ^ l) :=
      le_min (by positivity) (by positivity)
    refine Real.rpow_le_rpow hnn (min_le_min le_rfl ?_) hκ
    have e : (F.blockSide : ℝ) ^ (l + 1) = (F.blockSide : ℝ) ^ l * F.blockSide := pow_succ _ _
    have h5 : (0 : ℝ) < (F.blockSide : ℝ) ^ l := by positivity
    have h6 : 2 * (F.blockSide : ℝ) ^ l ≤ (F.blockSide : ℝ) ^ (l + 1) := by
      rw [e]
      nlinarith
    simp only at hd
    linarith
theorem meanChain_radiusPower_le_of_nonpos (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) (p : F.Site 0)
    {κ : ℝ} (hκ : κ ≤ 0) (i l : ℕ) (hil : i ≤ l) (hl : l ≤ F.top) (hin : i ≤ F.top) :
    ∀ (x : F.Site l) (d : Fin 4),
      meanChain i (radiusPower p κ) l x d ≤
        (min ((F.blockSide : ℝ) ^ F.top)
          (max ((F.blockSide : ℝ) ^ i) ((baseDistance x p : ℝ) - 4 * (F.blockSide : ℝ) ^ l))) ^ κ := by
  have hL2 : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast h2
  have hpos : ∀ r : ℝ, 0 < min ((F.blockSide : ℝ) ^ F.top) (max ((F.blockSide : ℝ) ^ i) r) := fun r =>
    lt_min (by positivity) (lt_max_of_lt_left (by positivity))
  induction l, hil using Nat.le_induction with
  | base =>
    intro x d
    rw [meanChain_of_le i _ le_rfl]
    refine Real.rpow_le_rpow_of_nonpos (hpos _) ?_ hκ
    simp only [scaleRadius]
    refine min_le_min le_rfl (max_le_max le_rfl ?_)
    have : (0 : ℝ) < (F.blockSide : ℝ) ^ i := by positivity
    linarith
  | succ l hil ih =>
    intro y d
    rw [meanChain_succ i _ hil]
    refine levelMean_le hodd fun h hh r hr => ?_
    refine (ih (by omega) _ _).trans ?_
    refine Real.rpow_le_rpow_of_nonpos (hpos _) (min_le_min le_rfl (max_le_max le_rfl ?_)) hκ
    have hd := (baseDistance_lineBond (by omega) (y, d) hh hr p).2
    have e : (F.blockSide : ℝ) ^ (l + 1) = (F.blockSide : ℝ) ^ l * F.blockSide := pow_succ _ _
    have h5 : (0 : ℝ) < (F.blockSide : ℝ) ^ l := by positivity
    have h6 : 2 * (F.blockSide : ℝ) ^ l ≤ (F.blockSide : ℝ) ^ (l + 1) := by
      rw [e]
      nlinarith
    simp only at hd
    linarith
end Chains
namespace Chains
theorem levelMean_mono (hodd : Odd F.blockSide) {l : ℕ} {f g : F.Site l → Fin 4 → ℝ} (h : ∀ x d, f x d ≤ g x d)
    (y : F.Site (l + 1)) (d : Fin 4) : levelMean f y d ≤ levelMean g y d := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  unfold levelMean lineBlockAverage
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => h _ _
theorem levelMean_const (hodd : Odd F.blockSide) {l : ℕ} (a : ℝ) (y : F.Site (l + 1)) (d : Fin 4) :
    levelMean (fun (_ : F.Site l) (_ : Fin 4) => a) y d = a := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  simp only [levelMean, lineBlockAverage, Finset.sum_const, Finset.card_range,
    LatticePaths.card_centredCube hodd, nsmul_eq_mul]
  push_cast
  field_simp
theorem levelMean_add {l : ℕ} (f g : F.Site l → Fin 4 → ℝ) (y : F.Site (l + 1)) (d : Fin 4) :
    levelMean (fun x e => f x e + g x e) y d = levelMean f y d + levelMean g y d := by
  simp only [levelMean, lineBlockAverage, Finset.sum_add_distrib, mul_add]
theorem levelMean_smul {l : ℕ} (a : ℝ) (f : F.Site l → Fin 4 → ℝ) (y : F.Site (l + 1)) (d : Fin 4) :
    levelMean (fun x e => a * f x e) y d = a * levelMean f y d := by
  simp only [levelMean, lineBlockAverage, ← Finset.mul_sum]
  ring
theorem levelMean_sum {ι : Type} (hodd : Odd F.blockSide) {l : ℕ} (s : Finset ι) (α : ι → ℝ)
    (g : ι → F.Site l → Fin 4 → ℝ) (y : F.Site (l + 1)) (d : Fin 4) :
    levelMean (fun x e => ∑ t ∈ s, α t * g t x e) y d = ∑ t ∈ s, α t * levelMean (g t) y d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using levelMean_const hodd 0 y d
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [levelMean_add, levelMean_smul, ih]
theorem meanChain_le_sum {ι : Type} (hodd : Odd F.blockSide) (i : ℕ) (base : (l : ℕ) → F.Site l → Fin 4 → ℝ)
    (a₀ : ℝ) (s : Finset ι) (α : ι → ℝ) (bs : ι → (l : ℕ) → F.Site l → Fin 4 → ℝ)
    (h : ∀ x d, base i x d ≤ a₀ + ∑ t ∈ s, α t * bs t i x d) (l : ℕ) (hil : i ≤ l) :
    ∀ x d, meanChain i base l x d ≤ a₀ + ∑ t ∈ s, α t * meanChain i (bs t) l x d := by
  induction l, hil using Nat.le_induction with
  | base =>
    intro x d
    rw [meanChain_of_le i _ le_rfl]
    simp only [meanChain_of_le i _ le_rfl]
    exact h x d
  | succ l hil ih =>
    intro y d
    rw [meanChain_succ i _ hil]
    simp only [meanChain_succ i _ hil]
    refine (levelMean_mono hodd ih y d).trans (le_of_eq ?_)
    rw [levelMean_add, levelMean_const hodd, levelMean_sum hodd]
theorem meanChain_nonneg (hodd : Odd F.blockSide) (i : ℕ) {base : (l : ℕ) → F.Site l → Fin 4 → ℝ}
    (hb : ∀ l x d, 0 ≤ base l x d) (l : ℕ) : ∀ (x : F.Site l) (d : Fin 4), 0 ≤ meanChain i base l x d := by
  induction l with
  | zero => exact fun x d => hb 0 x d
  | succ l ih =>
    intro x d
    have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
    simp only [meanChain]
    split_ifs
    · exact hb _ _ _
    · refine mul_nonneg (by positivity) (mul_nonneg (by positivity) ?_)
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ih _ _
theorem sum_meanChain_le (hodd : Odd F.blockSide) (D : Finset F.Cell) (i : ℕ)
    {ψ : (l : ℕ) → F.Site l → Fin 4 → ℝ} (hψ : ∀ l x d, 0 ≤ ψ l x d) (l : ℕ) (hil : i ≤ l) (hl : l ≤ F.top) :
    ∑ b ∈ innerBonds D l, meanChain i ψ l b.1 b.2 ≤
      (1 / (F.blockSide : ℝ) ^ 4) ^ (l - i) * ∑ b ∈ innerBonds D i, ψ i b.1 b.2 := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  induction l, hil using Nat.le_induction with
  | base =>
    simp only [meanChain_of_le i _ le_rfl, Nat.sub_self, pow_zero, one_mul]
    exact le_rfl
  | succ l hil ih =>
    have h1 := ih (by omega)
    have h2 := sum_lineBond_sum_le (B := D) (l := l) (by omega) hodd (innerBonds D (l + 1)) subset_rfl
      (fun b => meanChain i ψ l b.1 b.2) (fun b => meanChain_nonneg hodd i hψ l _ _)
    have e : ∑ b ∈ innerBonds D (l + 1), meanChain i ψ (l + 1) b.1 b.2 =
        1 / (F.blockSide : ℝ) ^ 5 * ∑ c ∈ innerBonds D (l + 1), ∑ h ∈ centredCube F.blockSide,
          ∑ r ∈ Finset.range F.blockSide, meanChain i ψ l (lineBond c h r).1 (lineBond c h r).2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [meanChain_succ i _ hil, levelMean]
      have : lineBlockAverage (meanChain i ψ l) (c.1, c.2) = 1 / (F.blockSide : ℝ) ^ 4 *
          ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
            meanChain i ψ l (lineBond c h r).1 (lineBond c h r).2 := rfl
      rw [this, ← mul_assoc]
      congr 1
      field_simp
    rw [e]
    have e2 : l + 1 - i = (l - i) + 1 := by omega
    rw [e2, pow_succ]
    calc _ ≤ 1 / (F.blockSide : ℝ) ^ 5 * ((F.blockSide : ℝ) * ∑ b ∈ innerBonds D l, meanChain i ψ l b.1 b.2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 / (F.blockSide : ℝ) ^ 4) * ∑ b ∈ innerBonds D l, meanChain i ψ l b.1 b.2 := by
          field_simp
      _ ≤ (1 / (F.blockSide : ℝ) ^ 4) *
            ((1 / (F.blockSide : ℝ) ^ 4) ^ (l - i) * ∑ b ∈ innerBonds D i, ψ i b.1 b.2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
def radiusBelow (p : F.Site 0) (i t : ℕ) : (l : ℕ) → F.Site l → Fin 4 → ℝ :=
  fun l x _ => if scaleRadius F l p x < ((2 ^ (t + 1) * F.blockSide ^ i : ℕ) : ℝ) then 1 else 0
theorem radiusBelow_nonneg (p : F.Site 0) (i t l : ℕ) (x : F.Site l) (d : Fin 4) :
    0 ≤ radiusBelow p i t l x d := by
  unfold radiusBelow
  split_ifs <;> norm_num
theorem sum_radiusBelow_le (hodd : Odd F.blockSide) (D : Finset F.Cell) (p : F.Site 0) (i t : ℕ) (hi : i ≤ F.top)
    (hm : 2 ^ (t + 1) * F.blockSide ^ i ≤ F.blockSide ^ F.top) :
    ∑ b ∈ innerBonds D i, radiusBelow p i t i b.1 b.2 ≤ 4 * (81 * 16 ^ (t + 1)) := by
  classical
  set X := sitesOfCells D i with hX
  have h1 := card_scaleRadius_lt hi hodd.pos X p (t + 1) hm
  have h2 : ∑ b ∈ innerBonds D i, radiusBelow p i t i b.1 b.2 ≤
      ∑ b ∈ X ×ˢ (Finset.univ : Finset (Fin 4)), radiusBelow p i t i b.1 b.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun b _ _ =>
      radiusBelow_nonneg _ _ _ _ _ _
  refine h2.trans ?_
  rw [Finset.sum_product]
  simp only [radiusBelow]
  rw [Finset.sum_comm]
  simp only [Finset.sum_boole, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast at h1 ⊢
  linarith
theorem sum_range_pow_le_pow {r : ℝ} (hr : 2 ≤ r) (T : ℕ) : ∑ t ∈ Finset.range T, r ^ t ≤ r ^ T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : 0 ≤ r ^ T := by positivity
    nlinarith
end Chains
namespace Chains
theorem rpow_two_pow_mul {A : ℝ} (hA : 0 < A) (κ : ℝ) (t : ℕ) :
    ((2 : ℝ) ^ t * A) ^ κ = ((2 : ℝ) ^ κ) ^ t * A ^ κ := by
  rw [Real.mul_rpow (by positivity) hA.le]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
    mul_comm]
theorem meanChain_radiusPower_le_dyadic (hodd : Odd F.blockSide) (p : F.Site 0) {κ : ℝ} (hκ : κ ≤ 0)
    (hκ3 : -3 ≤ κ) (i l : ℕ) (hil : i ≤ l) (hl : l ≤ F.top) (D : Finset F.Cell) {c : F.Site l × Fin 4}
    (hc : c ∈ innerBonds D l) :
    meanChain i (radiusPower p κ) l c.1 c.2 ≤
      5185 * ((2 : ℝ) ^ (Nat.log 2 (F.blockSide ^ (l - i))) * (F.blockSide : ℝ) ^ i) ^ κ := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  set M : ℕ := F.blockSide ^ (l - i) with hM
  have hMpos : 0 < M := by
    have := hodd.pos
    positivity
  set T := Nat.log 2 M with hT
  have h2T : 2 ^ T ≤ M := Nat.pow_log_le_self 2 hMpos.ne'
  set A : ℝ := (F.blockSide : ℝ) ^ i with hA
  have hApos : 0 < A := by positivity
  have hin : i ≤ F.top := hil.trans hl
  have hLn : M * F.blockSide ^ i = F.blockSide ^ l := by
    rw [hM, ← pow_add]
    congr 1
    omega
  have hLl : F.blockSide ^ l ≤ F.blockSide ^ F.top := Nat.pow_le_pow_right hodd.pos hl
  have hbase : ∀ (x : F.Site i) (d : Fin 4), radiusPower p κ i x d ≤ ((2 : ℝ) ^ T * A) ^ κ +
      ∑ t ∈ Finset.range T, ((2 : ℝ) ^ t * A) ^ κ * radiusBelow p i t i x d := by
    intro x d
    set ρ := scaleRadius F i p x with hρ
    have hρA : A ≤ ρ := pow_le_scaleRadius hin hodd.pos p x
    have hterm : ∀ t ∈ Finset.range T, 0 ≤ ((2 : ℝ) ^ t * A) ^ κ * radiusBelow p i t i x d := fun t _ =>
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (radiusBelow_nonneg _ _ _ _ _ _)
    by_cases hbig : (2 : ℝ) ^ T * A ≤ ρ
    · have h1 : ρ ^ κ ≤ ((2 : ℝ) ^ T * A) ^ κ := Real.rpow_le_rpow_of_nonpos (by positivity) hbig hκ
      have h2 := Finset.sum_nonneg hterm
      show ρ ^ κ ≤ _
      linarith
    · push Not at hbig
      have hex : ∃ t, ρ < (2 : ℝ) ^ (t + 1) * A := by
        rcases Nat.eq_zero_or_pos T with h0 | h0
        · rw [h0] at hbig
          simp at hbig
          linarith
        · exact ⟨T - 1, by rwa [Nat.sub_add_cancel h0]⟩
      classical
      set t := Nat.find hex with ht
      have ht1 : ρ < (2 : ℝ) ^ (t + 1) * A := Nat.find_spec hex
      have htT : t < T := by
        by_contra hcon
        push Not at hcon
        have : T ≤ t := hcon
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · have hT0 : T = 0 := by omega
          rw [hT0] at hbig
          simp at hbig
          linarith
        · have hmin := Nat.find_min hex (m := t - 1) (by omega)
          rw [Nat.sub_add_cancel h0] at hmin
          push Not at hmin
          have hp : (2 : ℝ) ^ T ≤ (2 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) hcon
          nlinarith
      have ht2 : (2 : ℝ) ^ t * A ≤ ρ := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · rw [h0]
          simpa using hρA
        · have hmin := Nat.find_min hex (m := t - 1) (by omega)
          rw [Nat.sub_add_cancel h0] at hmin
          push Not at hmin
          exact hmin
      have h1 : ρ ^ κ ≤ ((2 : ℝ) ^ t * A) ^ κ := Real.rpow_le_rpow_of_nonpos (by positivity) ht2 hκ
      have hind : radiusBelow p i t i x d = 1 := by
        simp only [radiusBelow]
        rw [if_pos]
        push_cast
        exact ht1
      have h2 := Finset.single_le_sum hterm (Finset.mem_range.2 htT)
      simp only [hind, mul_one] at h2
      have h3 : (0 : ℝ) ≤ ((2 : ℝ) ^ T * A) ^ κ := Real.rpow_nonneg (by positivity) _
      show ρ ^ κ ≤ _
      linarith
  have hchain := meanChain_le_sum hodd i (radiusPower p κ) (((2 : ℝ) ^ T * A) ^ κ) (Finset.range T)
    (fun t => ((2 : ℝ) ^ t * A) ^ κ) (fun t => radiusBelow p i t) hbase l hil c.1 c.2
  refine hchain.trans ?_
  set b : ℝ := (2 : ℝ) ^ κ with hb
  have hbpos : 0 < b := by positivity
  have hb8 : 1 / 8 ≤ b := by
    have : (2 : ℝ) ^ (-3 : ℝ) ≤ b := Real.rpow_le_rpow_of_exponent_le (by norm_num) hκ3
    have e : (2 : ℝ) ^ (-3 : ℝ) = 1 / 8 := by
      rw [Real.rpow_neg (by norm_num)]
      norm_num
    rw [e] at this
    exact this
  have hMR : ((M : ℝ)) = (F.blockSide : ℝ) ^ (l - i) := by
    rw [hM]
    push_cast
    rfl
  have hterm : ∀ t ∈ Finset.range T, meanChain i (radiusBelow p i t) l c.1 c.2 ≤
      (1 / (M : ℝ) ^ 4) * (5184 * 16 ^ t) := by
    intro t ht
    have htT : t + 1 ≤ T := Finset.mem_range.1 ht
    have hm : 2 ^ (t + 1) * F.blockSide ^ i ≤ F.blockSide ^ F.top := by
      calc 2 ^ (t + 1) * F.blockSide ^ i ≤ 2 ^ T * F.blockSide ^ i :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) htT)
        _ ≤ M * F.blockSide ^ i := Nat.mul_le_mul_right _ h2T
        _ = F.blockSide ^ l := hLn
        _ ≤ _ := hLl
    have h1 := sum_radiusBelow_le hodd D p i t hin hm
    have hnn : ∀ l' x d, 0 ≤ radiusBelow p i t l' x d := fun l' x d => radiusBelow_nonneg _ _ _ _ _ _
    have h2 := sum_meanChain_le hodd D i hnn l hil hl
    have h3 : meanChain i (radiusBelow p i t) l c.1 c.2 ≤
        ∑ b ∈ innerBonds D l, meanChain i (radiusBelow p i t) l b.1 b.2 :=
      Finset.single_le_sum (f := fun b : F.Site l × Fin 4 => meanChain i (radiusBelow p i t) l b.1 b.2)
        (fun b _ => meanChain_nonneg hodd i hnn l _ _) hc
    refine h3.trans (h2.trans ?_)
    have e : (1 / (F.blockSide : ℝ) ^ 4) ^ (l - i) = 1 / (M : ℝ) ^ 4 := by
      rw [hMR, div_pow, one_pow, ← pow_mul, ← pow_mul, mul_comm]
    rw [e]
    refine mul_le_mul_of_nonneg_left (h1.trans (le_of_eq ?_)) (by positivity)
    rw [pow_succ]
    ring
  have hsum : ∑ t ∈ Finset.range T, ((2 : ℝ) ^ t * A) ^ κ * meanChain i (radiusBelow p i t) l c.1 c.2 ≤
      5184 * ((2 : ℝ) ^ T * A) ^ κ := by
    have h1 : ∑ t ∈ Finset.range T, ((2 : ℝ) ^ t * A) ^ κ * meanChain i (radiusBelow p i t) l c.1 c.2 ≤
        ∑ t ∈ Finset.range T, (A ^ κ * (1 / (M : ℝ) ^ 4) * 5184) * (16 * b) ^ t := by
      refine Finset.sum_le_sum fun t ht => ?_
      have h2 := hterm t ht
      have h3 : (0 : ℝ) ≤ ((2 : ℝ) ^ t * A) ^ κ := Real.rpow_nonneg (by positivity) _
      calc _ ≤ ((2 : ℝ) ^ t * A) ^ κ * ((1 / (M : ℝ) ^ 4) * (5184 * 16 ^ t)) :=
            mul_le_mul_of_nonneg_left h2 h3
        _ = _ := by
            rw [rpow_two_pow_mul hApos, mul_pow]
            ring
    refine h1.trans ?_
    rw [← Finset.mul_sum]
    have h4 := sum_range_pow_le_pow (r := 16 * b) (by linarith) T
    have h5 : (0 : ℝ) ≤ A ^ κ * (1 / (M : ℝ) ^ 4) * 5184 := by positivity
    refine (mul_le_mul_of_nonneg_left h4 h5).trans ?_
    have h6 : (16 * b) ^ T ≤ (M : ℝ) ^ 4 * b ^ T := by
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h7 : ((2 ^ T : ℕ) : ℝ) ≤ M := by exact_mod_cast h2T
      have h8 : (16 : ℝ) ^ T = (((2 ^ T : ℕ) : ℝ)) ^ 4 := by
        push_cast
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [h8]
      exact pow_le_pow_left₀ (by positivity) h7 4
    calc _ ≤ A ^ κ * (1 / (M : ℝ) ^ 4) * 5184 * ((M : ℝ) ^ 4 * b ^ T) :=
          mul_le_mul_of_nonneg_left h6 h5
      _ = 5184 * (b ^ T * A ^ κ) := by
          field_simp
      _ = _ := by rw [rpow_two_pow_mul hApos]
  linarith
end Chains
namespace Chains
theorem one_div_sixteen_rpow_le {κ : ℝ} (h0 : κ ≤ 0) (h1 : -(1 / 4) ≤ κ) : (1 / 16 : ℝ) ^ κ ≤ 2 := by
  have h2 : (1 / 16 : ℝ) ^ κ ≤ (1 / 16 : ℝ) ^ (-(1 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) h1
  linarith
theorem one_div_two_rpow_le {κ : ℝ} (h0 : κ ≤ 0) (h1 : -(1 / 4) ≤ κ) : (1 / 2 : ℝ) ^ κ ≤ 2 := by
  have h2 : (1 / 2 : ℝ) ^ κ ≤ (1 / 2 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
  linarith
theorem meanChain_radiusPower_le_scaleRadius (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) (p : F.Site 0)
    {κ : ℝ} (hκ : |κ| ≤ 1 / 4) (i l : ℕ) (hil : i ≤ l) (hl : l ≤ F.top) (D : Finset F.Cell)
    {c : F.Site l × Fin 4} (hc : c ∈ innerBonds D l) :
    meanChain i (radiusPower p κ) l c.1 c.2 ≤ 20000 * scaleRadius F l p c.1 ^ κ := by
  have hκ1 := abs_le.1 hκ
  set ρ := scaleRadius F l p c.1 with hρ
  have hρpos : 0 < ρ := scaleRadius_pos hodd.pos _ _ _
  have hρκ : 0 ≤ ρ ^ κ := Real.rpow_nonneg hρpos.le _
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  set B : ℝ := (F.blockSide : ℝ) ^ l with hB
  have hBpos : 0 < B := by positivity
  set d : ℝ := ((baseDistance c.1 p : ℕ) : ℝ) with hd
  have hρdef : ρ = min N (max B d) := rfl
  rcases le_total 0 κ with hpos | hneg
  · have h1 := meanChain_radiusPower_le_of_nonneg hodd h2 p hpos i l hil hl c.1 c.2
    refine h1.trans ?_
    rw [← hN, ← hB, ← hd]
    set m := min N (d + 4 * B) with hm
    have hm0 : 0 ≤ m := le_min (by positivity) (by positivity)
    have hm5 : m ≤ 5 * ρ := by
      rw [hρdef]
      rcases le_total N (max B d) with h | h
      · rw [min_eq_left h]
        have : m ≤ N := min_le_left _ _
        linarith
      · rw [min_eq_right h]
        have : m ≤ d + 4 * B := min_le_right _ _
        have h3 := le_max_left B d
        have h4 := le_max_right B d
        linarith
    have h3 : m ^ κ ≤ (5 * ρ) ^ κ := Real.rpow_le_rpow hm0 hm5 hpos
    rw [Real.mul_rpow (by norm_num) hρpos.le] at h3
    have h4 : (5 : ℝ) ^ κ ≤ 5 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := 5) (by norm_num) (by linarith : κ ≤ 1)
      simpa using this
    nlinarith
  · rcases le_or_gt (8 * B) d with hfar | hnear
    · have h1 := meanChain_radiusPower_le_of_nonpos hodd h2 p hneg i l hil hl (hil.trans hl) c.1 c.2
      refine h1.trans ?_
      rw [← hN, ← hB, ← hd]
      set A : ℝ := (F.blockSide : ℝ) ^ i with hA
      have hApos : 0 < A := by positivity
      set m := min N (max A (d - 4 * B)) with hm
      have hm2 : (1 / 2) * ρ ≤ m := by
        have hNpos : 0 < N := by positivity
        refine le_min ?_ ?_
        · have : ρ ≤ N := min_le_left _ _
          linarith
        · have h3 : ρ ≤ max B d := min_le_right _ _
          have h4 : max B d = d := max_eq_right (by linarith)
          have h5 := le_max_right A (d - 4 * B)
          rw [h4] at h3
          linarith
      have h3 : m ^ κ ≤ ((1 / 2) * ρ) ^ κ := Real.rpow_le_rpow_of_nonpos (by positivity) hm2 hneg
      rw [Real.mul_rpow (by norm_num) hρpos.le] at h3
      have h4 := one_div_two_rpow_le hneg (by linarith)
      nlinarith
    · have h1 := meanChain_radiusPower_le_dyadic hodd p hneg (by linarith) i l hil hl D hc
      refine h1.trans ?_
      set A : ℝ := (F.blockSide : ℝ) ^ i with hA
      have hApos : 0 < A := by positivity
      set M : ℕ := F.blockSide ^ (l - i) with hM
      set T := Nat.log 2 M with hT
      set Y : ℝ := (2 : ℝ) ^ T * A with hY
      have hMlt : M < 2 ^ (T + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
      have hMR : (M : ℝ) < 2 ^ (T + 1) := by exact_mod_cast hMlt
      have hBM : B = (M : ℝ) * A := by
        rw [hB, hA, hM]
        push_cast
        rw [← pow_add]
        congr 1
        omega
      have hB2 : B ≤ 2 * Y := by
        rw [hBM, hY, pow_succ] at *
        nlinarith
      have hρ16 : (1 / 16) * ρ ≤ Y := by
        have h3 : ρ ≤ max B d := min_le_right _ _
        have h4 : max B d ≤ 8 * B := max_le (by linarith) hnear.le
        linarith
      have h3 : Y ^ κ ≤ ((1 / 16) * ρ) ^ κ := Real.rpow_le_rpow_of_nonpos (by positivity) hρ16 hneg
      rw [Real.mul_rpow (by norm_num) hρpos.le] at h3
      have h4 := one_div_sixteen_rpow_le hneg (by linarith)
      nlinarith
end Chains
open Chains in
theorem sum_weighted_pow_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) (D : Finset F.Cell) (p : F.Site 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (P : ℕ) (hP : P = 2 ∨ P = 4) (i l : ℕ) (hil : i ≤ l) (hl : l ≤ F.top)
    (f : (m : ℕ) → F.Site m → Fin 4 → ℝ) (hf : ∀ m x d, 0 ≤ f m x d)
    (hrec : ∀ m, i ≤ m → m < l → ∀ c ∈ innerBonds D (m + 1), f (m + 1) c.1 c.2 ≤ lineBlockAverage (f m) c) :
    ∑ c ∈ innerBonds D l, (scaleRadius F l p c.1 ^ (-θ) * f l c.1 c.2) ^ P ≤
      (20000 : ℝ) ^ (P - 1) * ((F.blockSide : ℝ) ^ P / (F.blockSide : ℝ) ^ 4) ^ (l - i) *
        ∑ b ∈ innerBonds D i, (scaleRadius F i p b.1 ^ (-θ) * f i b.1 b.2) ^ P := by
  have hP1 : 1 ≤ P := by rcases hP with h | h <;> omega
  set κ : ℝ := θ * P / (P - 1 : ℝ) with hκd
  have hP1R : ((P : ℝ) - 1) ≠ 0 := by
    rcases hP with h | h <;> subst h <;> norm_num
  have hκ : |κ| ≤ 1 / 4 := by
    rw [hκd, abs_div, abs_mul]
    rcases hP with h | h <;> subst h
    · norm_num
      linarith
    · norm_num
      rw [div_le_iff₀ (by norm_num)]
      linarith
  have hκθ : κ * ((P - 1 : ℕ) : ℝ) = θ * P := by
    rw [hκd, Nat.cast_sub hP1]
    push_cast
    field_simp
  set G := meanChain i (radiusPower p κ) with hG
  have hbase : ∀ l' (x : F.Site l') (d : Fin 4), 0 < radiusPower p κ l' x d := fun l' x d =>
    Real.rpow_pos_of_pos (scaleRadius_pos hodd.pos _ _ _) _
  have hGpos : ∀ l' x d, 0 < G l' x d := fun l' => meanChain_pos hodd i hbase l'
  set Nrm : (m : ℕ) → ℝ := fun m =>
    ∑ b ∈ innerBonds D m, f m b.1 b.2 ^ P * ((G m b.1 b.2)⁻¹) ^ (P - 1) with hNrm
  have hstep : ∀ m, i ≤ m → m < l →
      Nrm (m + 1) ≤ ((F.blockSide : ℝ) ^ P / (F.blockSide : ℝ) ^ 4) * Nrm m := by
    intro m him hml
    have h1 := lineBlockAverage_weighted_pow_le (B := D) (l := m) (by omega) hodd (innerBonds D (m + 1))
      subset_rfl (G := G m) (f := f m) (hGpos m) (hf m) P hP1
    refine le_trans ?_ h1
    refine Finset.sum_le_sum fun c hc => ?_
    have e : G (m + 1) c.1 c.2 = levelMean (G m) c.1 c.2 := by
      rw [hG, meanChain_succ i _ him]
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (inv_nonneg.2 ?_) _)
    · exact pow_le_pow_left₀ (hf _ _ _) (hrec m him hml c hc) P
    · rw [← e]
      exact (hGpos _ _ _).le
  have hiter : ∀ m, i ≤ m → m ≤ l →
      Nrm m ≤ ((F.blockSide : ℝ) ^ P / (F.blockSide : ℝ) ^ 4) ^ (m - i) * Nrm i := by
    intro m him
    induction m, him using Nat.le_induction with
    | base => intro _; simp
    | succ m him ih =>
      intro hml
      have h1 := hstep m him (by omega)
      have h2' := ih (by omega)
      have e : m + 1 - i = (m - i) + 1 := by omega
      rw [e, pow_succ]
      have h3 : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ P / (F.blockSide : ℝ) ^ 4 := by positivity
      calc Nrm (m + 1) ≤ ((F.blockSide : ℝ) ^ P / (F.blockSide : ℝ) ^ 4) * Nrm m := h1
        _ ≤ ((F.blockSide : ℝ) ^ P / (F.blockSide : ℝ) ^ 4) *
              (((F.blockSide : ℝ) ^ P / (F.blockSide : ℝ) ^ 4) ^ (m - i) * Nrm i) :=
            mul_le_mul_of_nonneg_left h2' h3
        _ = _ := by ring
  have hbot : Nrm i = ∑ b ∈ innerBonds D i, (scaleRadius F i p b.1 ^ (-θ) * f i b.1 b.2) ^ P := by
    refine Finset.sum_congr rfl fun b _ => ?_
    have hρ := scaleRadius_pos (F := F) hodd.pos i p b.1
    have e : G i b.1 b.2 = scaleRadius F i p b.1 ^ κ := by
      rw [hG, meanChain_of_le i _ le_rfl]
      rfl
    rw [e, mul_pow, ← Real.rpow_neg hρ.le, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hρ.le, ← Real.rpow_mul hρ.le, mul_comm]
    congr 2
    rw [neg_mul, hκθ, neg_mul]
  have htop : ∑ c ∈ innerBonds D l, (scaleRadius F l p c.1 ^ (-θ) * f l c.1 c.2) ^ P ≤
      (20000 : ℝ) ^ (P - 1) * Nrm l := by
    rw [hNrm, Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hρ := scaleRadius_pos (F := F) hodd.pos l p c.1
    have hcmp := meanChain_radiusPower_le_scaleRadius hodd h2 p hκ i l hil hl D hc
    have hGc := hGpos l c.1 c.2
    have e1 : (scaleRadius F l p c.1 ^ (-θ)) ^ P = ((scaleRadius F l p c.1 ^ κ)⁻¹) ^ (P - 1) := by
      rw [← Real.rpow_neg hρ.le, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le,
        ← Real.rpow_mul hρ.le]
      congr 1
      rw [neg_mul, neg_mul, hκθ]
    have h3 : (scaleRadius F l p c.1 ^ κ)⁻¹ ≤ 20000 * (G l c.1 c.2)⁻¹ := by
      have hpk : 0 < scaleRadius F l p c.1 ^ κ := Real.rpow_pos_of_pos hρ _
      rw [inv_le_comm₀ hpk (by positivity), mul_inv, inv_inv]
      rw [inv_mul_le_iff₀ (by norm_num)]
      exact hcmp
    have h4 : ((scaleRadius F l p c.1 ^ κ)⁻¹) ^ (P - 1) ≤ (20000 * (G l c.1 c.2)⁻¹) ^ (P - 1) :=
      pow_le_pow_left₀ (inv_nonneg.2 (Real.rpow_nonneg hρ.le _)) h3 _
    rw [mul_pow, e1, mul_comm]
    calc f l c.1 c.2 ^ P * ((scaleRadius F l p c.1 ^ κ)⁻¹) ^ (P - 1)
        ≤ f l c.1 c.2 ^ P * (20000 * (G l c.1 c.2)⁻¹) ^ (P - 1) :=
          mul_le_mul_of_nonneg_left h4 (pow_nonneg (hf _ _ _) _)
      _ = _ := by
          rw [mul_pow]
          ring
  refine htop.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← hbot]
  exact hiter l hil le_rfl
end WeightedAverages
end YangMills.Construction
end
