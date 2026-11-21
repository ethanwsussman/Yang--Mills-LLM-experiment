import YangMills.Construction.ColdChainAtEveryLevel.SizesOfAPinnedFraming
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.VariationRates
variable {F : BlockFrame} {S : Finset F.Cell} {j : ℕ}
theorem quarticBound_add {R : Finset F.Cell} {Q Q' : ℝ} (hQ : 0 ≤ Q) (hQ' : 0 ≤ Q') {e e' : VariationSlot F → ℝ}
    (he : ∀ u, 0 ≤ e u) (he' : ∀ u, 0 ≤ e' u) (h : QuarticBound S R Q e) (h' : QuarticBound S R Q' e') :
    QuarticBound S R (2 * (Q + Q')) (fun u => e u + e' u) := by
  have key : ∀ {ι : Type} (s : Finset ι) (a b : ι → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
      ∑ i ∈ s, a i ^ 4 ≤ Q ^ 4 → ∑ i ∈ s, b i ^ 4 ≤ Q' ^ 4 → ∑ i ∈ s, (a i + b i) ^ 4 ≤ (2 * (Q + Q')) ^ 4 := by
    intro ι s a b ha hb h1 h2
    have h3 : ∑ i ∈ s, (a i + b i) ^ 4 ≤ 8 * (∑ i ∈ s, a i ^ 4 + ∑ i ∈ s, b i ^ 4) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => add_pow_four_le (ha i) (hb i)
    have h4 : Q ^ 4 + Q' ^ 4 ≤ (Q + Q') ^ 4 := by
      have := mul_nonneg hQ hQ'
      nlinarith [pow_nonneg hQ 3, pow_nonneg hQ' 3, pow_nonneg hQ 2, pow_nonneg hQ' 2,
        mul_nonneg (pow_nonneg hQ 3) hQ', mul_nonneg hQ (pow_nonneg hQ' 3),
        mul_nonneg (pow_nonneg hQ 2) (pow_nonneg hQ' 2)]
    have h5 : (0 : ℝ) ≤ (Q + Q') ^ 4 := by positivity
    nlinarith
  intro j hj
  exact ⟨key _ _ _ (fun _ => he _) (fun _ => he' _) (h j hj).1 (h' j hj).1,
    key _ _ _ (fun _ => he _) (fun _ => he' _) (h j hj).2 (h' j hj).2⟩
theorem quarticBound_const_mul {R : Finset F.Cell} {Q c : ℝ} (hc : 0 ≤ c) {e : VariationSlot F → ℝ}
    (h : QuarticBound S R Q e) : QuarticBound S R (c * Q) (fun u => c * e u) := by
  intro j hj
  simp only [mul_pow, ← Finset.mul_sum]
  exact ⟨mul_le_mul_of_nonneg_left (h j hj).1 (by positivity), mul_le_mul_of_nonneg_left (h j hj).2 (by positivity)⟩
theorem scaledQuarticBound_mono {R : Finset F.Cell} {P : ℝ} {f f' : VariationSlot F → ℝ} (h0 : ∀ u, 0 ≤ f' u)
    (hle : ∀ u, f' u ≤ f u) (h : ScaledQuarticBound S R P f) : ScaledQuarticBound S R P f' := by
  intro j hj
  have hs : 0 ≤ EvaluationSums.levelScale F j ^ 4 := by have := EvaluationSums.levelScale_nonneg F j; positivity
  refine ⟨le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) hs) (h j hj).1,
    le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) hs) (h j hj).2⟩
  · exact pow_le_pow_left₀ (h0 _) (hle _) 4
  · exact pow_le_pow_left₀ (h0 _) (hle _) 4
def scaledBondWeight (c : ℝ) (f : VariationSlot F → ℝ) : VariationSlot F → ℝ
  | Sum.inl b => c * EvaluationSums.levelScale F b.1 * f (Sum.inl b)
  | Sum.inr _ => 0
theorem scaledBondWeight_nonneg {c : ℝ} (hc : 0 ≤ c) {f : VariationSlot F → ℝ} (hf : ∀ u, 0 ≤ f u)
    (u : VariationSlot F) : 0 ≤ scaledBondWeight c f u := by
  rcases u with b | d
  · exact mul_nonneg (mul_nonneg hc (EvaluationSums.levelScale_nonneg F _)) (hf _)
  · exact le_rfl
theorem quarticBound_scaledBondWeight {R : Finset F.Cell} {P c : ℝ} (hc : 0 ≤ c) (hP : 0 ≤ P)
    {f : VariationSlot F → ℝ} (h : ScaledQuarticBound S R P f) :
    QuarticBound S R (c * P) (scaledBondWeight c f) := by
  intro j hj
  constructor
  · have e : ∀ b : F.Site j × Fin 4, scaledBondWeight c f (slotOfBond j b.1 b.2) ^ 4 =
        c ^ 4 * (EvaluationSums.levelScale F j ^ 4 * f (slotOfBond j b.1 b.2) ^ 4) := by
      intro b
      show (c * EvaluationSums.levelScale F j * f (slotOfBond j b.1 b.2)) ^ 4 = _
      ring
    simp only [e, ← Finset.mul_sum]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (h j hj).1 (by positivity)
  · have e : ∀ y : F.Site (j + 1), scaledBondWeight c f (slotOfLink j y) ^ 4 = 0 := by
      intro y
      show (0 : ℝ) ^ 4 = 0
      norm_num
    simp only [e, Finset.sum_const_zero]
    positivity
theorem sum_sitesOfCells_le (hodd : Odd F.blockSide) (R : Finset F.Cell) (j : ℕ) (f : F.Site j → ℝ)
    (hf : ∀ x, 0 ≤ f x) {A : ℝ} (h : ∀ y ∈ R, ∑ x ∈ sitesOfCells {y} j, f x ≤ A) :
    ∑ x ∈ sitesOfCells R j, f x ≤ R.card * A := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := sitesOfCells R j) (t := R) (g := fun x => enclosingCell x)
    (fun x hx => by
      obtain ⟨y, hy, a, ha, e⟩ := mem_sitesOfCells.1 hx
      have : enclosingCell x = y := by rw [e]; exact LocalPartition.enclosingCell_cellCentre_add hodd y a ha
      rw [this]; exact hy)]
  have h1 : ∀ y ∈ R, ∑ x ∈ sitesOfCells R j with enclosingCell x = y, f x ≤ A := by
    intro y hy
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => hf x) (h y hy)
    intro x hx
    have hx' := Finset.mem_filter.1 hx
    exact mem_sitesOfCells_of_enclosingCell_mem hodd hx'.1 (by simp [hx'.2])
  refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
  simp
theorem sum_bondsOnRegion_ends_le (hodd : Odd F.blockSide) (R : Finset F.Cell) (j : ℕ) (f : F.Site j → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ b ∈ bondsOnRegion S R j, f b.1 ≤ 4 * ∑ x ∈ sitesOfCells R j, f x ∧
      ∑ b ∈ bondsOnRegion S R j, f (b.1 + unitStep j b.2) ≤ 4 * ∑ x ∈ sitesOfCells R j, f x := by
  classical
  have hmem : ∀ b ∈ bondsOnRegion S R j, b.1 ∈ sitesOfCells R j ∧ b.1 + unitStep j b.2 ∈ sitesOfCells R j := by
    intro b hb
    have hb' := Finset.mem_filter.1 hb
    obtain ⟨m1, m2⟩ := ChartCoordinates.innerBonds_ends hb'.1
    exact ⟨mem_sitesOfCells_of_enclosingCell_mem hodd m1 hb'.2.1,
      mem_sitesOfCells_of_enclosingCell_mem hodd m2 hb'.2.2⟩
  constructor
  · rw [← Finset.sum_fiberwise (bondsOnRegion S R j) (fun b => b.2)]
    have h1 : ∀ i : Fin 4, ∑ b ∈ bondsOnRegion S R j with b.2 = i, f b.1 ≤ ∑ x ∈ sitesOfCells R j, f x := by
      intro i
      refine EvaluationSums.sum_comp_le_of_injOn ((bondsOnRegion S R j).filter fun b => b.2 = i) (sitesOfCells R j)
        (fun b => b.1) ?_ (fun b hb => (hmem b (Finset.mem_filter.1 hb).1).1) f hf
      intro b hb b' hb' e
      exact Prod.ext e (by rw [(Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2, (Finset.mem_filter.1 (Finset.mem_coe.1 hb')).2])
    refine (Finset.sum_le_sum fun i _ => h1 i).trans (le_of_eq ?_)
    simp
  · rw [← Finset.sum_fiberwise (bondsOnRegion S R j) (fun b => b.2)]
    have h1 : ∀ i : Fin 4, ∑ b ∈ bondsOnRegion S R j with b.2 = i, f (b.1 + unitStep j b.2) ≤
        ∑ x ∈ sitesOfCells R j, f x := by
      intro i
      have e0 : ∑ b ∈ bondsOnRegion S R j with b.2 = i, f (b.1 + unitStep j b.2) =
          ∑ b ∈ bondsOnRegion S R j with b.2 = i, f ((fun b : F.Site j × Fin 4 => b.1 + unitStep j b.2) b) := rfl
      rw [e0]
      refine EvaluationSums.sum_comp_le_of_injOn ((bondsOnRegion S R j).filter fun b => b.2 = i) (sitesOfCells R j)
        (fun b : F.Site j × Fin 4 => b.1 + unitStep j b.2) ?_
        (fun b hb => (hmem b (Finset.mem_filter.1 hb).1).2) f hf
      intro b hb b' hb' e
      have a1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
      have a2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hb')).2
      simp only [a1, a2] at e
      exact Prod.ext (add_right_cancel e) (by rw [a1, a2])
    refine (Finset.sum_le_sum fun i _ => h1 i).trans (le_of_eq ?_)
    simp
section Change
variable (W : F.FieldChain) (kW : F.SiteGauge) (Γ Γ' : F.SiteGauge)
def changeWeight : VariationSlot F → ℝ := fun u =>
  _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (slotSourceChange Γ Γ' u) + _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (slotTargetChange W kW Γ Γ' u)
def targetChange : VariationSlot F → ℝ
  | Sum.inl b => _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange Γ Γ' b.1 (b.2.1 + unitStep b.1 b.2.2))
  | Sum.inr _ => 0
theorem changeWeight_nonneg (u : VariationSlot F) : 0 ≤ changeWeight W kW Γ Γ' u :=
  add_nonneg (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg _) (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg _)
theorem targetChange_nonneg (u : VariationSlot F) : 0 ≤ targetChange Γ Γ' u := by
  rcases u with b | c
  · exact _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg _
  · exact le_rfl
theorem targetChange_le_changeWeight (u : VariationSlot F) : targetChange Γ Γ' u ≤ changeWeight W kW Γ Γ' u := by
  rcases u with b | c
  · show _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne _ ≤ _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne _ + _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne _
    simp only [slotTargetChange, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_conj]
    have := _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg (slotSourceChange Γ Γ' (Sum.inl b))
    linarith
  · exact changeWeight_nonneg W kW Γ Γ' _
theorem scaledQuarticBound_changeWeight (hodd : Odd F.blockSide)
    (hinj : ∀ j, j < F.top → Function.Injective (_root_.YangMills.Construction.BlockAverages.refineSite (F := F) (j := j)))
    {R : Finset F.Cell} (hcard : R.card ≤ 17 ^ 4) {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ j, j < F.top → ∀ y ∈ R, EvaluationSums.levelScale F j ^ 4 *
      ∑ x ∈ sitesOfCells {y} j, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange Γ Γ' j x) ^ 4 ≤ r ^ 4)
    (htop : ∀ x, gaugeChange Γ Γ' F.top x = 1) :
    ScaledQuarticBound S R (51 * r) (changeWeight W kW Γ Γ') := by
  classical
  have hcr : (R.card : ℝ) ≤ 17 ^ 4 := by exact_mod_cast hcard
  have hr4 : 0 ≤ r ^ 4 := by positivity
  have hsite : ∀ j, j < F.top → EvaluationSums.levelScale F j ^ 4 *
      ∑ x ∈ sitesOfCells R j, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange Γ Γ' j x) ^ 4 ≤ 17 ^ 4 * r ^ 4 := by
    intro j hj
    have hsc : 0 < EvaluationSums.levelScale F j := by
      unfold EvaluationSums.levelScale
      have : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
      positivity
    have h1 := sum_sitesOfCells_le hodd R j (fun x => _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange Γ Γ' j x) ^ 4)
      (fun x => by have := _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg (gaugeChange Γ Γ' j x); positivity)
      (A := r ^ 4 / EvaluationSums.levelScale F j ^ 4) (fun y hy => by
        rw [le_div_iff₀ (by positivity), mul_comm]
        exact hs j hj y hy)
    calc _ ≤ EvaluationSums.levelScale F j ^ 4 * (R.card * (r ^ 4 / EvaluationSums.levelScale F j ^ 4)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = R.card * r ^ 4 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcr hr4
  have c51 : (51 * r) ^ 4 = 81 * (17 ^ 4 * r ^ 4) := by ring
  intro j hj
  have hsj := EvaluationSums.levelScale_nonneg F j
  have hs4 : 0 ≤ EvaluationSums.levelScale F j ^ 4 := by positivity
  set f : F.Site j → ℝ := fun x => _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange Γ Γ' j x) ^ 4 with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => by have := _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg (gaugeChange Γ Γ' j x); positivity
  obtain ⟨e1, e2⟩ := sum_bondsOnRegion_ends_le (S := S) hodd R j f hf0
  have hA := hsite j hj
  constructor
  · have h1 : ∑ b ∈ bondsOnRegion S R j, changeWeight W kW Γ Γ' (slotOfBond j b.1 b.2) ^ 4 ≤
        8 * (∑ b ∈ bondsOnRegion S R j, f b.1 + ∑ b ∈ bondsOnRegion S R j, f (b.1 + unitStep j b.2)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => ?_
      have := add_pow_four_le (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg (slotSourceChange Γ Γ' (slotOfBond j b.1 b.2)))
        (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg (slotTargetChange W kW Γ Γ' (slotOfBond j b.1 b.2)))
      simpa only [changeWeight, slotTargetChange, slotSourceChange, slotOfBond, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_conj, hf] using this
    have h2 : EvaluationSums.levelScale F j ^ 4 *
        ∑ b ∈ bondsOnRegion S R j, changeWeight W kW Γ Γ' (slotOfBond j b.1 b.2) ^ 4 ≤
        64 * (EvaluationSums.levelScale F j ^ 4 * ∑ x ∈ sitesOfCells R j, f x) := by
      have := mul_le_mul_of_nonneg_left h1 hs4
      nlinarith
    rw [c51]
    nlinarith
  · have hd : ∑ y ∈ sitesOfCells R (j + 1), f (_root_.YangMills.Construction.BlockAverages.refineSite y) ≤ ∑ x ∈ sitesOfCells R j, f x :=
      EvaluationSums.sum_comp_le_of_injOn _ _ _root_.YangMills.Construction.BlockAverages.refineSite (hinj j hj).injOn (fun y hy => by
        have := ChartCoordinates.refineSite_add_mem_sitesOfCells hodd (j := j) hj hy (a := 0) (by
          refine Fintype.mem_piFinset.2 fun i => ?_
          have : 0 < F.blockSide := hodd.pos
          simp only [Pi.zero_apply, Finset.mem_Icc]
          omega)
        rwa [_root_.YangMills.Construction.BlockAverages.siteOfCoords_zero, add_zero] at this) f hf0
    have hup : EvaluationSums.levelScale F j ^ 4 *
        ∑ y ∈ sitesOfCells R (j + 1), _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange Γ Γ' (j + 1) y) ^ 4 ≤ 17 ^ 4 * r ^ 4 := by
      by_cases hjn : j + 1 < F.top
      · refine le_trans ?_ (hsite (j + 1) hjn)
        refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun y _ => by
          have := _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg (gaugeChange Γ Γ' (j + 1) y); positivity)
        exact pow_le_pow_left₀ hsj (levelScale_le_succ hodd hj) 4
      · have hn : F.top = F.depth + 1 := rfl
        obtain rfl : j = F.depth := by omega
        have : ∀ y : F.Site (F.depth + 1), _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange Γ Γ' (F.depth + 1) y) = 0 := by
          intro y
          have h1 := htop y
          show _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange Γ Γ' F.top y) = 0
          rw [h1, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_one]
        simp only [this]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, mul_zero]
        positivity
    have h1 : ∑ y ∈ sitesOfCells R (j + 1), changeWeight W kW Γ Γ' (slotOfLink j y) ^ 4 ≤
        8 * (∑ y ∈ sitesOfCells R (j + 1), _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange Γ Γ' (j + 1) y) ^ 4 +
          ∑ y ∈ sitesOfCells R (j + 1), f (_root_.YangMills.Construction.BlockAverages.refineSite y)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      have := add_pow_four_le (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg (slotSourceChange Γ Γ' (slotOfLink j y)))
        (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_nonneg (slotTargetChange W kW Γ Γ' (slotOfLink j y)))
      simpa only [changeWeight, slotTargetChange, slotSourceChange, slotOfLink, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne_conj, hf] using this
    have h2 := mul_le_mul_of_nonneg_left h1 hs4
    have h3 := mul_le_mul_of_nonneg_left hd hs4
    rw [c51]
    nlinarith
end Change
end YangMills.Construction.BlockAverages.VariationRates
end
