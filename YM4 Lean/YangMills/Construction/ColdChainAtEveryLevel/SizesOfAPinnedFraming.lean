import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfASplitCriticalPointProof
import YangMills.Construction.ColdChainAtEveryLevel.SizesOnARegion
import YangMills.Construction.ColdChainAtEveryLevel.VariationsOfTheFramings
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.VariationRates
variable {F : BlockFrame} {S : Finset F.Cell} {j : ℕ}
theorem distFromOne_one : _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (1 : UnitQuaternion) = 0 := by simp [_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne]
theorem distFromOne_inv_mul_eq (x r : UnitQuaternion) : _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (x⁻¹ * r) = _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (x * r⁻¹) := by
  have e : x⁻¹ * r = x⁻¹ * (r * x⁻¹) * (x⁻¹)⁻¹ := by group
  rw [e, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_conj]
  have e2 : r * x⁻¹ = (x * r⁻¹)⁻¹ := by group
  rw [e2, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_inv]
theorem distFromOne_pathHolonomy_div_le (X R : F.GaugeField j) (x : F.Site j) (l : List PathStep) :
    _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (pathHolonomy X x l * (pathHolonomy R x l)⁻¹) ≤
      bondSum (fun x i => _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (X x i * (R x i)⁻¹)) x l := by
  induction l generalizing x with
  | nil => simp [pathHolonomy, bondSum, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_one]
  | cons st r ih =>
    simp only [pathHolonomy, bondSum]
    set Vx := linkValue X x st
    set Vr := linkValue R x st
    set Hx := pathHolonomy X (x + stepDisplacement j st) r
    set Hr := pathHolonomy R (x + stepDisplacement j st) r
    have e : Vx * Hx * (Vr * Hr)⁻¹ = (Vx * Vr⁻¹) * (Vr * (Hx * Hr⁻¹) * Vr⁻¹) := by group
    rw [e]
    refine (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_mul_le _ _).trans (add_le_add ?_ ?_)
    · rcases st with ⟨i, b⟩
      cases b
      · simp only [Vx, Vr, linkValue, Bool.false_eq_true, if_false, inv_inv]
        exact le_of_eq (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_inv_mul_eq _ _)
      · simp only [Vx, Vr, linkValue, if_true]
        exact le_rfl
    · rw [_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_conj]
      exact ih _
theorem distFromOne_polarUnit_le (q : ℍ[ℝ]) : _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (polarUnit q) ≤ 2 * ‖q - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.normSubOne_polarUnit_le <;> assumption
def offsetOrderPairs (L : ℕ) : Finset ((Fin 4 → ℤ) × Equiv.Perm (Fin 4)) := centredCube L ×ˢ Finset.univ
def maxAxisPathLength (L : ℕ) : ℕ := (offsetOrderPairs L).sup fun q => (axisPath q.1 q.2).length
theorem sum_offsetOrderPairs_weight (hodd : Odd F.blockSide) :
    ∑ _q ∈ offsetOrderPairs F.blockSide, (1 / (24 * (F.blockSide : ℝ) ^ 4)) = 1 := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  unfold offsetOrderPairs
  rw [Finset.sum_const, Finset.card_product, LatticePaths.card_centredCube hodd, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]
  have : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [nsmul_eq_mul]
  push_cast
  rw [this]
  field_simp
theorem norm_relativePathAverage_sub_one_le (hodd : Odd F.blockSide) (X R : F.GaugeField j) (y : F.Site (j + 1)) :
    ‖relativePathAverage X R y - 1‖ ≤ ∑ q ∈ offsetOrderPairs F.blockSide, (1 / (24 * (F.blockSide : ℝ) ^ 4)) *
      bondSum (fun x i => _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (X x i * (R x i)⁻¹)) (refineSite y) (axisPath q.1 q.2) := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hw : (0 : ℝ) ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) := by positivity
  have e : relativePathAverage X R y - 1 = ∑ q ∈ offsetOrderPairs F.blockSide, (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
      (((pathHolonomy X (refineSite y) (axisPath q.1 q.2) * (pathHolonomy R (refineSite y) (axisPath q.1 q.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) := by
    have e0 : relativePathAverage X R y = ∑ q ∈ offsetOrderPairs F.blockSide, (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
        ((pathHolonomy X (refineSite y) (axisPath q.1 q.2) * (pathHolonomy R (refineSite y) (axisPath q.1 q.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      unfold relativePathAverage offsetOrderPairs
      rw [Finset.sum_product, Finset.smul_sum]
      simp only [Finset.smul_sum]
    have e1 : ∑ _q ∈ offsetOrderPairs F.blockSide, (1 / (24 * (F.blockSide : ℝ) ^ 4)) • (1 : ℍ[ℝ]) = 1 := by
      rw [← Finset.sum_smul, sum_offsetOrderPairs_weight hodd, one_smul]
    rw [e0]
    conv_lhs => rw [← e1]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => (smul_sub _ _ _).symm
  rw [e]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_pathHolonomy_div_le X R _ _) hw
theorem add_pow_four_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by apply _root_.YangMills.Construction.BlockAverages.SplitCriticalPointBounds.add_pow_four_le <;> assumption
theorem sum_bondSum_pow_four_le {α : Type} (Ys : Finset α) (g : F.Site j → Fin 4 → ℝ) (hg : ∀ x i, 0 ≤ g x i)
    (B : Finset (F.Site j × Fin 4)) (l : List PathStep) (f : α → F.Site j) (hf : Set.InjOn f Ys)
    (hB : ∀ a ∈ Ys, ∀ b, LiesOnPath b (f a) l → b ∈ B) :
    ∑ a ∈ Ys, bondSum g (f a) l ^ 4 ≤ 16 ^ l.length * ∑ b ∈ B, g b.1 b.2 ^ 4 := by
  classical
  have hG : 0 ≤ ∑ b ∈ B, g b.1 b.2 ^ 4 := Finset.sum_nonneg fun b _ => by positivity
  induction l generalizing f with
  | nil =>
    simp only [bondSum, List.length_nil, pow_zero, one_mul]
    simpa using hG
  | cons st r ih =>
    have h1 := ih (fun a => f a + stepDisplacement j st) (fun a ha a' ha' e => hf ha ha' (add_right_cancel e))
      (fun a ha b hb => hB a ha b (Or.inr hb))
    set b₀ : α → F.Site j × Fin 4 := fun a =>
      if st.2 then (f a, st.1) else (f a - unitStep j st.1, st.1) with hb₀
    have hv : ∀ a, (if st.2 then g (f a) st.1 else g (f a - unitStep j st.1) st.1) = g (b₀ a).1 (b₀ a).2 := by
      intro a
      simp only [hb₀]
      split_ifs <;> rfl
    have hinj : Set.InjOn b₀ Ys := by
      intro a ha a' ha' e
      apply hf ha ha'
      simp only [hb₀] at e
      split_ifs at e
      · exact congrArg Prod.fst e
      · exact sub_left_injective (congrArg Prod.fst e)
    have hin : ∀ a ∈ Ys, b₀ a ∈ B := by
      intro a ha
      refine hB a ha _ (Or.inl ?_)
      simp only [hb₀]
      split_ifs <;> rfl
    have h2 : ∑ a ∈ Ys, g (b₀ a).1 (b₀ a).2 ^ 4 ≤ ∑ b ∈ B, g b.1 b.2 ^ 4 :=
      EvaluationSums.sum_comp_le_of_injOn Ys B b₀ hinj hin (fun b => g b.1 b.2 ^ 4) fun b => by have := hg b.1 b.2; positivity
    simp only [bondSum, hv, List.length_cons]
    have h3 : ∀ a ∈ Ys, (g (b₀ a).1 (b₀ a).2 + bondSum g (f a + stepDisplacement j st) r) ^ 4 ≤
        8 * (g (b₀ a).1 (b₀ a).2 ^ 4 + bondSum g (f a + stepDisplacement j st) r ^ 4) :=
      fun a _ => add_pow_four_le (hg _ _) (bondSum_nonneg hg _ _)
    refine (Finset.sum_le_sum h3).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, pow_succ]
    have h4 : (1 : ℝ) ≤ 16 ^ r.length := one_le_pow₀ (by norm_num)
    nlinarith
theorem sum_balancingGauge_pow_four_le (hodd : Odd F.blockSide) (hinj : Function.Injective (refineSite (F := F) (j := j))) (X R : F.GaugeField j)
    (Ys : Finset (F.Site (j + 1))) (B : Finset (F.Site j × Fin 4))
    (hB : ∀ y ∈ Ys, ∀ q ∈ offsetOrderPairs F.blockSide, ∀ b, LiesOnPath b (refineSite y) (axisPath q.1 q.2) → b ∈ B) :
    ∑ y ∈ Ys, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (balancingGauge X R y) ^ 4 ≤
      16 * 16 ^ maxAxisPathLength F.blockSide * ∑ b ∈ B, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (X b.1 b.2 * (R b.1 b.2)⁻¹) ^ 4 := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  set w : ℝ := 1 / (24 * (F.blockSide : ℝ) ^ 4) with hw
  have hw0 : 0 ≤ w := by positivity
  set g : F.Site j → Fin 4 → ℝ := fun x i => _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (X x i * (R x i)⁻¹) with hg
  have hg0 : ∀ x i, 0 ≤ g x i := fun _ _ => _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg _
  set G := ∑ b ∈ B, g b.1 b.2 ^ 4 with hG
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun b _ => by have := hg0 b.1 b.2; positivity
  have h1 : ∀ y ∈ Ys, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (balancingGauge X R y) ^ 4 ≤
      16 * ∑ q ∈ offsetOrderPairs F.blockSide, w * bondSum g (refineSite y) (axisPath q.1 q.2) ^ 4 := by
    intro y _
    have h2 : _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (balancingGauge X R y) ≤
        2 * ∑ q ∈ offsetOrderPairs F.blockSide, w * bondSum g (refineSite y) (axisPath q.1 q.2) := by
      unfold balancingGauge
      rw [_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_inv]
      refine (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_polarUnit_le _).trans ?_
      exact mul_le_mul_of_nonneg_left (norm_relativePathAverage_sub_one_le hodd X R y) (by norm_num)
    have h3 := Real.pow_arith_mean_le_arith_mean_pow (offsetOrderPairs F.blockSide) (fun _ => w)
      (fun q => bondSum g (refineSite y) (axisPath q.1 q.2)) (fun _ _ => hw0) (sum_offsetOrderPairs_weight hodd)
      (fun q _ => bondSum_nonneg hg0 _ _) 4
    have h4 := pow_le_pow_left₀ (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg _) h2 4
    rw [mul_pow] at h4
    norm_num at h4
    nlinarith
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h5 : ∀ q ∈ offsetOrderPairs F.blockSide, ∑ y ∈ Ys, w * bondSum g (refineSite y) (axisPath q.1 q.2) ^ 4 ≤ w * (16 ^ maxAxisPathLength F.blockSide * G) := by
    intro q hq
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hw0
    refine (sum_bondSum_pow_four_le Ys g hg0 B _ refineSite hinj.injOn fun y hy b hb => hB y hy q hq b hb).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hG0
    refine pow_le_pow_right₀ (by norm_num) ?_
    exact Finset.le_sup (f := fun q : (Fin 4 → ℤ) × Equiv.Perm (Fin 4) => (axisPath q.1 q.2).length) hq
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum h5) (by norm_num)).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, sum_offsetOrderPairs_weight hodd]
  ring
theorem mem_bondsOnRegion_of_liesOnPath (hodd : Odd F.blockSide) {R : Finset F.Cell} (hRS : R ⊆ S) (hj : j < F.top) {y : F.Site (j + 1)}
    (hy : y ∈ sitesOfCells R (j + 1)) {q : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)} (hq : q ∈ offsetOrderPairs F.blockSide)
    {b : F.Site j × Fin 4} (hb : LiesOnPath b (refineSite y) (axisPath q.1 q.2)) : b ∈ bondsOnRegion S R j := by
  classical
  set v := enclosingCell y with hv
  have hvR : v ∈ R := (baseSite_eq_cellCentre_add hodd (j := j + 1) hj hy).1
  have hy1 : y ∈ sitesOfCells {v} (j + 1) := mem_sitesOfCells_of_enclosingCell_mem hodd hy (by simp [hv])
  have hp := ChartCoordinates.allAlong_axisPath hodd (j := j) hj hy1 (Finset.mem_product.1 hq).1 q.2
  have hb' : LiesOnPath b (refineSite y + siteOfCoords j (0 : LatticeFractionalIntegration.Lattice4)) (axisPath q.1 q.2) := by
    rwa [ChartCoordinates.add_siteOfCoords_zero]
  obtain ⟨u, h1, h2, e⟩ := exists_offset_of_liesOnPath (refineSite y) hp hb'
  have e2 : b.1 + unitStep j b.2 = refineSite y + siteOfCoords j (u + LatticeFractionalIntegration.basisVector b.2) := by
    rw [e, unitStep_eq, siteOfCoords_add, add_assoc]
  have m1 : b.1 ∈ sitesOfCells {v} j := by rw [e]; exact h1
  have m2 : b.1 + unitStep j b.2 ∈ sitesOfCells {v} j := by rw [e2]; exact h2
  have hsub : ({v} : Finset F.Cell) ⊆ S := by simpa using hRS hvR
  refine Finset.mem_filter.2 ⟨?_, ?_, ?_⟩
  · exact ChartCoordinates.mem_innerBonds (mem_sitesOfCells_mono hsub m1) (mem_sitesOfCells_mono hsub m2)
  · rw [enclosingCell_of_mem_sitesOfCells_singleton hodd m1]; exact hvR
  · rw [enclosingCell_of_mem_sitesOfCells_singleton hodd m2]; exact hvR
def defectConstant (L : ℕ) : ℝ := 8 * 17 ^ 4 + 128 * 16 ^ maxAxisPathLength L + 1
theorem one_le_defectConstant (L : ℕ) : 1 ≤ defectConstant L := by
  unfold defectConstant
  have : (0 : ℝ) ≤ 128 * 16 ^ maxAxisPathLength L := by positivity
  linarith
theorem baseSite_mem_patchBaseSites (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {z : F.Cell}
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {R : Finset F.Cell} (hR : ∀ y ∈ R, y ∈ S ∧ cellSupDist z y ≤ 10) {x : F.Site j} (hj : j ≤ F.top)
    (hx : x ∈ sitesOfCells S j) (hc : enclosingCell x ∈ R) : baseSite x ∈ patchBaseSites S z := by
  obtain ⟨-, h, hh, e⟩ := baseSite_eq_cellCentre_add hodd hj hx
  rw [e]
  exact PatchLocality.mem_patchBaseSites_of_cellSupDist_le hamb hodd he (hR _ hc).1 (hR _ hc).2 hh
theorem quarticBound_slotDefect (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hinj : ∀ j, j < F.top → Function.Injective (refineSite (F := F) (j := j)))
    {z : F.Cell} (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {a C : ℝ} (hC : 0 ≤ C)
    {W : F.FieldChain} {kW : F.SiteGauge}
    {X : F.FieldChain} {k Γ : F.SiteGauge} (hpin : IsPinnedGauge a C S z W kW X k Γ) {R : Finset F.Cell}
    (hR : ∀ y ∈ R, y ∈ S ∧ cellSupDist z y ≤ 10) (hcard : R.card ≤ 17 ^ 4) :
    QuarticBound S R (defectConstant F.blockSide * (C * √(relativeEnergy a S z W kW X k Γ)))
      (fun u => _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (slotDefect W kW X k Γ u)) := by
  classical
  obtain ⟨-, hlink, hbond, hturn⟩ := hpin
  set r := C * √(relativeEnergy a S z W kW X k Γ) with hr
  have hr0 : 0 ≤ r := mul_nonneg hC (Real.sqrt_nonneg _)
  have hRS : R ⊆ S := fun y hy => (hR y hy).1
  have hc1 := one_le_defectConstant F.blockSide
  have hQ : ∀ x : ℝ, x ≤ defectConstant F.blockSide * r ^ 4 → x ≤ (defectConstant F.blockSide * r) ^ 4 := by
    intro x hx
    refine hx.trans ?_
    rw [mul_pow (defectConstant F.blockSide) r 4]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr0 4)
    calc defectConstant F.blockSide = defectConstant F.blockSide ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hc1 (by norm_num)
  intro j hj
  have hG : ∑ b ∈ bondsOnRegion S R j, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (relativeDefect W X Γ j b.1 b.2) ^ 4 ≤ r ^ 4 := by
    refine le_trans ?_ (hbond j hj)
    have e1 : ∑ b ∈ bondsOnRegion S R j, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (relativeDefect W X Γ j b.1 b.2) ^ 4 =
        ∑ b ∈ bondsOnRegion S R j, (if baseSite b.1 ∈ patchBaseSites S z ∧ baseSite (b.1 + unitStep j b.2) ∈ patchBaseSites S z then
          ‖((gaugedChainFields X Γ j b.1 b.2 * (W j b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 else 0) := by
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb' := Finset.mem_filter.1 hb
      obtain ⟨m1, m2⟩ := ChartCoordinates.innerBonds_ends hb'.1
      rw [if_pos ⟨baseSite_mem_patchBaseSites hamb hodd he hR hj.le m1 hb'.2.1,
        baseSite_mem_patchBaseSites hamb hodd he hR hj.le m2 hb'.2.2⟩]
      rfl
    rw [e1]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun b _ _ => ?_
    split_ifs
    · positivity
    · exact le_rfl
  have hbal := sum_balancingGauge_pow_four_le hodd (hinj j hj) (gaugedChainFields X Γ j) (W j) (sitesOfCells R (j + 1))
    (bondsOnRegion S R j) (fun y hy q hq b hb => mem_bondsOnRegion_of_liesOnPath hodd hRS hj hy hq hb)
  have hbal' : ∑ y ∈ sitesOfCells R (j + 1), _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (balancingGauge (gaugedChainFields X Γ j) (W j) y) ^ 4 ≤
      16 * 16 ^ maxAxisPathLength F.blockSide * r ^ 4 :=
    hbal.trans (mul_le_mul_of_nonneg_left hG (by positivity))
  have hr4 : 0 ≤ r ^ 4 := by positivity
  have h16 : (0 : ℝ) ≤ 16 ^ maxAxisPathLength F.blockSide := by positivity
  refine ⟨hQ _ ?_, hQ _ ?_⟩
  · refine (show _ ≤ r ^ 4 from hG).trans ?_
    nlinarith
  · by_cases hjn : j + 1 < F.top
    · have e1 : ∀ y ∈ sitesOfCells R (j + 1), _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (slotDefect W kW X k Γ (slotOfLink j y)) =
          _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (balancingGauge (gaugedChainFields X Γ j) (W j) y) := by
        intro y hy
        have hcell := (baseSite_eq_cellCentre_add hodd (j := j + 1) hj hy).1
        have hyS := mem_sitesOfCells_mono hRS hy
        have h1 := hlink j hjn y (baseSite_mem_patchBaseSites hamb hodd he hR (j := j + 1) hj hyS hcell)
        show _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugedLink k Γ j y * (kW (j + 1) y)⁻¹) = _
        rw [h1]
        unfold balancedLinkAgainst
        exact _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_conj _ _
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun y hy => ?_)) (hbal'.trans ?_)
      · show _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (slotDefect W kW X k Γ (slotOfLink j y)) ^ 4 =
          _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (balancingGauge (gaugedChainFields X Γ j) (W j) y) ^ 4
        rw [e1 y hy]
      · unfold defectConstant
        nlinarith
    · have hn : F.top = F.depth + 1 := rfl
      obtain rfl : j = F.depth := by omega
      have e1 : ∀ y ∈ sitesOfCells R F.top, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (slotDefect W kW X k Γ (slotOfLink F.depth y)) ^ 4 ≤
          8 * (r ^ 4 + _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (balancingGauge (gaugedChainFields X Γ F.depth) (W F.depth) y) ^ 4) := by
        intro y hy
        have hcell := (baseSite_eq_cellCentre_add hodd (j := F.top) le_rfl hy).1
        have hyS := mem_sitesOfCells_mono hRS hy
        have h1 := hturn y (baseSite_mem_patchBaseSites hamb hodd he hR (j := F.top) le_rfl hyS hcell)
        have e2 : slotDefect W kW X k Γ (slotOfLink F.depth y) = (topCorrection W kW X k Γ y)⁻¹ *
            (kW F.top y * balancingGauge (gaugedChainFields X Γ F.depth) (W F.depth) y * (kW F.top y)⁻¹) := by
          show gaugedLink k Γ F.depth y * (kW (F.depth + 1) y)⁻¹ = _
          unfold topCorrection balancedLinkAgainst
          group
        have h2 : _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (slotDefect W kW X k Γ (slotOfLink F.depth y)) ≤ r +
            _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (balancingGauge (gaugedChainFields X Γ F.depth) (W F.depth) y) := by
          rw [e2]
          refine (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_mul_le _ _).trans ?_
          rw [_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_inv, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_conj]
          exact add_le_add h1 le_rfl
        exact (pow_le_pow_left₀ (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg _) h2 4).trans (add_pow_four_le hr0 (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg _))
      refine (Finset.sum_le_sum e1).trans ?_
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have hcs := card_sitesOfCells_le hodd R F.top
      have hcr : (R.card : ℝ) ≤ 17 ^ 4 := by exact_mod_cast hcard
      simp only [Nat.sub_self, pow_zero, one_pow, mul_one] at hcs
      have h3 : ((sitesOfCells R F.top).card : ℝ) * r ^ 4 ≤ 17 ^ 4 * r ^ 4 :=
        mul_le_mul_of_nonneg_right (hcs.trans hcr) hr4
      unfold defectConstant
      nlinarith
end YangMills.Construction.BlockAverages.VariationRates
end
