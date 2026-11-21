import YangMills.Construction.ColdChainAtEveryLevel.ComplexCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction
open BlockAverages ComplexDifferences LevelRecursion ComplexCells ComplexLevels ComplexContours HullBounds
  ComplexRemainders ComplexPlaquettes ComplexifiedQuaternions FiniteDifferences
namespace CellSources
variable {F : BlockFrame}
def baseSource (W : ComplexChainChart F) (x : F.Site 0) (i : Fin 4) : ComplexQuat :=
  complexifiedImaginary (W.re.fine x i) (W.im.fine x i)
def upperSource (W : ComplexChainChart F) (x : Σ m : ℕ, F.Site (m + 1) × Fin 4) : ComplexQuat :=
  complexifiedImaginary (W.re.coarse x.1 x.2.1 x.2.2) (W.im.coarse x.1 x.2.1 x.2.2)
theorem complexChartField_zero (R : F.FieldChain) (W : ComplexChainChart F) :
    complexChartField R W 0 = expField (R 0) (baseSource W) := rfl
theorem levelDeviation_zero (R : F.FieldChain) (W : ComplexChainChart F) (x : F.Site 0) (i : Fin 4) :
    levelDeviation R W 0 x i = unitExp (baseSource W x i) - 1 := by
  simp only [levelDeviation, linkDeviation, complexChartField, mul_assoc, ofUnit_mul_inv, mul_one]
  rfl
theorem levelSource_eq_unitExp (W : ComplexChainChart F) (x : Σ m : ℕ, F.Site (m + 1) × Fin 4) :
    levelSource W x.1 x.2.1 x.2.2 = unitExp (upperSource W x) := rfl
theorem finsetLpNorm_level_le_lowerBonds {D : Finset F.Cell} {m : ℕ} (hm : m + 1 < F.top)
    (f : (Σ m : ℕ, F.Site (m + 1) × Fin 4) → ℝ) :
    finsetLpNorm 2 (innerBonds D (m + 1)) (fun c => f ⟨m, c⟩) ≤ finsetLpNorm 2 (lowerBonds D) f := by
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) ?_ (by positivity)
  refine sum_comp_le_of_injOn (innerBonds D (m + 1)) (lowerBonds D)
    (fun c => (⟨m, c⟩ : Σ m : ℕ, F.Site (m + 1) × Fin 4)) ?_ ?_
    (fun x => |f x| ^ 2) (fun _ => by positivity)
  · intro c _ c' _ e
    simpa using e
  · intro c hc
    exact Finset.mem_sigma.2 ⟨Finset.mem_range.2 (show m < F.top - 1 by omega), hc⟩
structure SourcesSmall (D : Finset F.Cell) (W : ComplexChainChart F) : Prop where
  base_le : ∀ b ∈ innerBonds D 0, ‖baseSource W b.1 b.2‖ ≤ 1 / 8000
  upper_le : ∀ x ∈ lowerBonds D, ‖upperSource W x‖ ≤ 1 / 8000
theorem deviationBall_of_finsetLpNorm_le {R : F.FieldChain} {D : Finset F.Cell} {W : ComplexChainChart F} {B₀ : ℝ}
    (hlev : Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D 0, ‖levelDeviation R W 0 b.1 b.2‖ ^ 4)) ≤ 2 * B₀ →
      (∀ j, j + 1 < F.top →
        Real.sqrt (∑ c ∈ innerBonds D (j + 1), ‖levelSource W j c.1 c.2 - 1‖ ^ 2) ≤ 2 * B₀) →
      ∀ j, j < F.top →
        Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, ‖levelDeviation R W j b.1 b.2‖ ^ 4)) ≤ 4 * (2 * B₀))
    (h0 : finsetLpNorm 4 (innerBonds D 0) (fun b => ‖baseSource W b.1 b.2‖) ≤ B₀)
    (hm : finsetLpNorm 2 (lowerBonds D) (fun x => ‖upperSource W x‖) ≤ B₀) (hsmall : B₀ ≤ 1 / 8000) :
    SourcesSmall D W ∧ DeviationBall R D W (8 * B₀) (8 * B₀) := by
  have hB0 : 0 ≤ B₀ := (finsetLpNorm_nonneg _ _ _).trans h0
  have hss : SourcesSmall D W := by
    refine ⟨fun b hb => ?_, fun x hx => ?_⟩
    · have := abs_le_finsetLpNorm (P := 4) (by norm_num) (s := innerBonds D 0)
        (fun b => ‖baseSource W b.1 b.2‖) hb
      rw [abs_of_nonneg (norm_nonneg _)] at this
      linarith
    · have := abs_le_finsetLpNorm (P := 2) (by norm_num) (s := lowerBonds D) (fun x => ‖upperSource W x‖) hx
      rw [abs_of_nonneg (norm_nonneg _)] at this
      linarith
  have hg0 : finsetLpNorm 4 (innerBonds D 0) (fun b => ‖levelDeviation R W 0 b.1 b.2‖) ≤ 2 * B₀ := by
    have h1 := finsetLpNorm_const_mul_le (P := 4) (by norm_num) (innerBonds D 0)
      (fun b => ‖baseSource W b.1 b.2‖) (a := 2) (by norm_num)
    refine le_trans (finsetLpNorm_mono (by norm_num) _ fun b hb => ?_) (h1.trans (by linarith))
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity), levelDeviation_zero]
    exact ComplexDifferences.norm_unitExp_sub_one_le ((hss.base_le b hb).trans (by norm_num))
  have hsrc : ∀ j, j + 1 < F.top →
      finsetLpNorm 2 (innerBonds D (j + 1)) (fun c => ‖levelSource W j c.1 c.2 - 1‖) ≤ 2 * B₀ := by
    intro j hj
    have h1 := finsetLpNorm_level_le_lowerBonds (D := D) hj (fun x => ‖upperSource W x‖)
    have h2 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) (innerBonds D (j + 1))
      (fun c => ‖upperSource W ⟨j, c⟩‖) (a := 2) (by norm_num)
    refine le_trans (finsetLpNorm_mono (by norm_num) _ fun c hc => ?_) (h2.trans (by linarith))
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)]
    have hx : (⟨j, c⟩ : Σ m : ℕ, F.Site (m + 1) × Fin 4) ∈ lowerBonds D :=
      Finset.mem_sigma.2 ⟨Finset.mem_range.2 (show j < F.top - 1 by omega), hc⟩
    have e : levelSource W j c.1 c.2 = unitExp (upperSource W ⟨j, c⟩) := levelSource_eq_unitExp W ⟨j, c⟩
    rw [e]
    exact ComplexDifferences.norm_unitExp_sub_one_le ((hss.upper_le _ hx).trans (by norm_num))
  have hl := hlev
    (by rw [← finsetLpNorm_four_eq_sqrt_sqrt (innerBonds D 0) fun b => ‖levelDeviation R W 0 b.1 b.2‖]; exact hg0)
    (fun j hj => by
      rw [← finsetLpNorm_two_eq_sqrt (innerBonds D (j + 1)) fun c => ‖levelSource W j c.1 c.2 - 1‖]
      exact hsrc j hj)
  have hg4 : ∀ m, m < F.top →
      finsetLpNorm 4 (innerBonds D m) (fun b => ‖levelDeviation R W m b.1 b.2‖) ≤ 8 * B₀ := by
    intro m hm'
    rw [finsetLpNorm_four_eq_sqrt_sqrt]
    have := hl m hm'
    linarith
  refine ⟨hss, fun m hm' b hb => ?_, hg4, fun m hm' c hc => ?_, fun m hm' => ?_⟩
  · have := abs_le_finsetLpNorm (P := 4) (by norm_num) (s := innerBonds D m)
      (fun b => ‖levelDeviation R W m b.1 b.2‖) hb
    rw [abs_of_nonneg (norm_nonneg _)] at this
    exact this.trans (hg4 m hm')
  · have := abs_le_finsetLpNorm (P := 2) (by norm_num) (s := innerBonds D (m + 1))
      (fun c => ‖levelSource W m c.1 c.2 - 1‖) hc
    rw [abs_of_nonneg (norm_nonneg _)] at this
    have h3 := hsrc m hm'
    linarith
  · have h3 := hsrc m hm'
    have h4 := finsetLpNorm_four_le_two (innerBonds D (m + 1)) (fun c => ‖levelSource W m c.1 c.2 - 1‖)
    linarith
section Bounds
def lowerScaleWeight (p : F.Site 0) (θ : ℝ) (x : Σ m : ℕ, F.Site (m + 1) × Fin 4) : ℝ :=
  scaleWeight p θ (x.1 + 1) x.2.1
theorem lowerScaleWeight_pos (hodd : Odd F.blockSide) (p : F.Site 0) (θ : ℝ)
    (x : Σ m : ℕ, F.Site (m + 1) × Fin 4) : 0 < lowerScaleWeight p θ x :=
  scaleWeight_pos hodd p θ _ _
theorem mem_lowerBonds {D : Finset F.Cell} {m : ℕ} (hm : m + 1 < F.top) {c : F.Site (m + 1) × Fin 4}
    (hc : c ∈ innerBonds D (m + 1)) : (⟨m, c⟩ : Σ m : ℕ, F.Site (m + 1) × Fin 4) ∈ lowerBonds D :=
  Finset.mem_sigma.2 ⟨Finset.mem_range.2 (show m < F.top - 1 by omega), hc⟩
theorem weightedScaleNorm_deviationFirstDiff_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    {D : Finset F.Cell} (hD : D.card ≤ 81) (p : F.Site 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {W W' : ComplexChainChart F} {C₀ s η B : ℝ}
    (hC : 0 < C₀) (hs : 0 < s) (hnear : ContoursNearUnit R D C₀ s) (hb : DeviationBall R D W η B)
    (hb' : DeviationBall R D W' η B) (ss : SourcesSmall D W) (ss' : SourcesSmall D W') (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hB0 : 0 ≤ B) (hσ : C₀ * s ≤ 1 / 64)
    (hsm : 3 * (2 * (hullBondCount F.blockSide * η) + C₀ * s) < hullBallRadius F.blockSide)
    (hfac : 568 * firstDiffFactor F.blockSide C₀ s B * hullFactor F.blockSide ≤ 1) (m : ℕ) (hm : m < F.top) :
    weightedScaleNorm D p θ 4 m (deviationFirstDiff R W W' m) ≤
      2 * (20000 * (2 * weightedScaleNorm D p θ 4 0 (fun x i => ‖baseSource W' x i - baseSource W x i‖)) +
        284 * (4 * finsetLpNorm 2 (lowerBonds D)
          (fun x => lowerScaleWeight p θ x * ‖upperSource W' x - upperSource W x‖))) := by
  set A := finsetLpNorm 2 (lowerBonds D)
    (fun x => lowerScaleWeight p θ x * ‖upperSource W' x - upperSource W x‖) with hA
  have hA0 : 0 ≤ A := finsetLpNorm_nonneg _ _ _
  have hS : ∀ m, m + 1 < F.top → weightedScaleNorm D p θ 2 (m + 1)
      (fun y d => 2 * ‖levelSource W' m y d - levelSource W m y d‖) ≤ 4 * A := by
    intro m hm
    have h1 := finsetLpNorm_level_le_lowerBonds (D := D) hm
      (fun x => lowerScaleWeight p θ x * ‖upperSource W' x - upperSource W x‖)
    have h3 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) (innerBonds D (m + 1))
      (fun c => lowerScaleWeight p θ ⟨m, c⟩ * ‖upperSource W' ⟨m, c⟩ - upperSource W ⟨m, c⟩‖) (a := 4) (by norm_num)
    refine le_trans (finsetLpNorm_mono (by norm_num) _ fun c hc => ?_) (h3.trans (by linarith))
    have hv := lowerScaleWeight_pos hodd p θ ⟨m, c⟩
    have hv' : scaleWeight p θ (m + 1) c.1 = lowerScaleWeight p θ ⟨m, c⟩ := rfl
    have hx := mem_lowerBonds hm hc
    have e1 : levelSource W m c.1 c.2 = unitExp (upperSource W ⟨m, c⟩) := levelSource_eq_unitExp W ⟨m, c⟩
    have e2 : levelSource W' m c.1 c.2 = unitExp (upperSource W' ⟨m, c⟩) := levelSource_eq_unitExp W' ⟨m, c⟩
    have hl := norm_unitExp_sub_le ((ss.upper_le _ hx).trans (by norm_num))
      ((ss'.upper_le _ hx).trans (by norm_num))
    beta_reduce
    rw [hv', e1, e2]
    have p1 : 0 ≤ lowerScaleWeight p θ ⟨m, c⟩ *
        (2 * ‖unitExp (upperSource W' ⟨m, c⟩) - unitExp (upperSource W ⟨m, c⟩)‖) :=
      mul_nonneg hv.le (mul_nonneg (by norm_num) (norm_nonneg _))
    have p2 : 0 ≤ 4 * (lowerScaleWeight p θ ⟨m, c⟩ * ‖upperSource W' ⟨m, c⟩ - upperSource W ⟨m, c⟩‖) :=
      mul_nonneg (by norm_num) (mul_nonneg hv.le (norm_nonneg _))
    rw [abs_of_nonneg p1, abs_of_nonneg p2]
    have : 2 * ‖unitExp (upperSource W' ⟨m, c⟩) - unitExp (upperSource W ⟨m, c⟩)‖ ≤
        4 * ‖upperSource W' ⟨m, c⟩ - upperSource W ⟨m, c⟩‖ := by linarith
    calc _ ≤ lowerScaleWeight p θ ⟨m, c⟩ * (4 * ‖upperSource W' ⟨m, c⟩ - upperSource W ⟨m, c⟩‖) :=
          mul_le_mul_of_nonneg_left this hv.le
      _ = _ := by ring
  have hf := weightedScaleNorm_first_diff_le hodd h2 hD p hθ hC hs hnear hb hb' hη0 hη1 hB0 (by positivity) hσ hsm
    hfac hS m hm
  refine hf.trans ?_
  have h0 : weightedScaleNorm D p θ 4 0 (fun z d => ‖(levelDeviation R W' 0 - levelDeviation R W 0) z d‖) ≤
      2 * weightedScaleNorm D p θ 4 0 (fun x i => ‖baseSource W' x i - baseSource W x i‖) := by
    have h3 := finsetLpNorm_const_mul_le (P := 4) (by norm_num) (innerBonds D 0)
      (fun b => scaleWeight p θ 0 b.1 * ‖baseSource W' b.1 b.2 - baseSource W b.1 b.2‖) (a := 2) (by norm_num)
    refine le_trans (finsetLpNorm_mono (by norm_num) _ fun b hb => ?_) h3
    have hv := scaleWeight_pos hodd p θ 0 b.1
    have e : ‖(levelDeviation R W' 0 - levelDeviation R W 0) b.1 b.2‖ =
        ‖unitExp (baseSource W' b.1 b.2) - unitExp (baseSource W b.1 b.2)‖ := by
      simp only [Pi.sub_apply, levelDeviation_zero]
      congr 1
      abel
    have hl := norm_unitExp_sub_le ((ss.base_le b hb).trans (by norm_num)) ((ss'.base_le b hb).trans (by norm_num))
    beta_reduce
    rw [e]
    have p1 : 0 ≤ scaleWeight p θ 0 b.1 * ‖unitExp (baseSource W' b.1 b.2) - unitExp (baseSource W b.1 b.2)‖ :=
      mul_nonneg hv.le (norm_nonneg _)
    have p2 : 0 ≤ 2 * (scaleWeight p θ 0 b.1 * ‖baseSource W' b.1 b.2 - baseSource W b.1 b.2‖) :=
      mul_nonneg (by norm_num) (mul_nonneg hv.le (norm_nonneg _))
    rw [abs_of_nonneg p1, abs_of_nonneg p2]
    calc _ ≤ scaleWeight p θ 0 b.1 * (2 * ‖baseSource W' b.1 b.2 - baseSource W b.1 b.2‖) :=
          mul_le_mul_of_nonneg_left hl hv.le
      _ = _ := by ring
  linarith
end Bounds
section SecondBound
structure SourceParallelogram (W₀ W₁ W₂ W₃ : ComplexChainChart F) : Prop where
  base : ∀ x i, baseSource W₃ x i = baseSource W₁ x i + baseSource W₂ x i - baseSource W₀ x i
  upper : ∀ x, upperSource W₃ x = upperSource W₁ x + upperSource W₂ x - upperSource W₀ x
theorem norm_unitExp_parallelogram_le {a b c d : ComplexQuat} (hd : d = b + c - a) (ha : ‖a‖ ≤ 1 / 8000)
    (hb : ‖b‖ ≤ 1 / 8000) (hc : ‖c‖ ≤ 1 / 8000) :
    ‖unitExp d - unitExp b - unitExp c + unitExp a‖ ≤ 8256 * ‖b - a‖ * ‖c - a‖ := by
  have h1 : ‖b - a‖ ≤ 1 / 4000 := (norm_sub_le _ _).trans (by linarith)
  have h2 : ‖c - a‖ ≤ 1 / 4000 := (norm_sub_le _ _).trans (by linarith)
  have h := norm_unitExp_second_diff_le (y := a) (e₁ := b - a) (e₂ := c - a) (ha.trans (by norm_num)) h1 h2
  have e1 : a + (b - a) + (c - a) = d := by
    rw [hd]
    abel
  have e2 : a + (b - a) = b := by abel
  have e3 : a + (c - a) = c := by abel
  rw [e1, e2, e3] at h
  exact h
theorem finsetLpNorm_le_of_le {ι : Type} {P : ℕ} (hP : 1 ≤ P) {s : Finset ι} {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) : finsetLpNorm P s f ≤ finsetLpNorm P s g :=
  finsetLpNorm_mono hP s fun i hi => by
    rw [abs_of_nonneg (hf i hi), abs_of_nonneg ((hf i hi).trans (hfg i hi))]
    exact hfg i hi
set_option maxHeartbeats 1000000 in
theorem weightedScaleNorm_deviationSecondDiff_le {R : F.FieldChain} {D : Finset F.Cell}
    {W₀ W₁ W₂ W₃ : ComplexChainChart F} {C₀ s η B : ℝ}
    (h : FourDeviationBalls R D W₀ W₁ W₂ W₃ C₀ s η B) (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    (s₀ : SourcesSmall D W₀) (s₁ : SourcesSmall D W₁) (s₂ : SourcesSmall D W₂) (s₃ : SourcesSmall D W₃)
    (par : SourceParallelogram W₀ W₁ W₂ W₃)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) {T₁ T₂ : ℝ} (hT₁0 : 0 ≤ T₁) (hT₂0 : 0 ≤ T₂)
    (hT₁ : ∀ m, m < F.top → weightedScaleNorm D p θ 4 m (deviationFirstDiff R W₀ W₁ m) ≤ T₁)
    (hT₂ : ∀ m, m < F.top → weightedScaleNorm D p (-θ) 4 m (deviationFirstDiff R W₀ W₂ m) ≤ T₂)
    (hfac : 568 * secondDiffFactor F.blockSide C₀ s η * hullFactor F.blockSide ≤ 1) (m : ℕ) (hm : m < F.top) :
    weightedScaleNorm D p 0 2 m (deviationSecondDiff R W₀ W₁ W₂ W₃ m) ≤
      2 * (142 * (8256 * (weightedScaleNorm D p θ 4 0 (fun x i => ‖baseSource W₁ x i - baseSource W₀ x i‖) *
            weightedScaleNorm D p (-θ) 4 0 (fun x i => ‖baseSource W₂ x i - baseSource W₀ x i‖))) +
        284 * (128 * (200000 * (F.blockSide : ℝ) ^ 2) *
            ((hullFactor F.blockSide * T₁) * (hullFactor F.blockSide * T₂)) +
          6 * 8256 * (finsetLpNorm 2 (lowerBonds D)
              (fun x => lowerScaleWeight p θ x * ‖upperSource W₁ x - upperSource W₀ x‖) *
            finsetLpNorm 2 (lowerBonds D)
              (fun x => lowerScaleWeight p (-θ) x * ‖upperSource W₂ x - upperSource W₀ x‖)) +
          4 * (finsetLpNorm 2 (lowerBonds D)
              (fun x => lowerScaleWeight p θ x * ‖upperSource W₁ x - upperSource W₀ x‖) *
            (hullFactor F.blockSide * T₂)) +
          4 * (finsetLpNorm 2 (lowerBonds D)
              (fun x => lowerScaleWeight p (-θ) x * ‖upperSource W₂ x - upperSource W₀ x‖) *
            (hullFactor F.blockSide * T₁)))) := by
  have hθ' : |(-θ)| ≤ 1 / 8 := by rwa [abs_neg]
  have hF0 := hullFactor_nonneg F.blockSide
  set K₁ := hullFactor F.blockSide * T₁ with hK₁
  set K₂ := hullFactor F.blockSide * T₂ with hK₂
  have hK₁0 : 0 ≤ K₁ := mul_nonneg hF0 hT₁0
  set A₁ := finsetLpNorm 2 (lowerBonds D)
    (fun x => lowerScaleWeight p θ x * ‖upperSource W₁ x - upperSource W₀ x‖) with hA₁
  set A₂ := finsetLpNorm 2 (lowerBonds D)
    (fun x => lowerScaleWeight p (-θ) x * ‖upperSource W₂ x - upperSource W₀ x‖) with hA₂
  have hA₁0 : 0 ≤ A₁ := finsetLpNorm_nonneg _ _ _
  have hA₂0 : 0 ≤ A₂ := finsetLpNorm_nonneg _ _ _
  set S₂ := 128 * (200000 * (F.blockSide : ℝ) ^ 2) * (K₁ * K₂) + 6 * 8256 * (A₁ * A₂) + 4 * (A₁ * K₂) +
    4 * (A₂ * K₁) with hS₂
  have hS₂0 : 0 ≤ S₂ := by positivity
  have hS : ∀ m, m + 1 < F.top →
      weightedScaleNorm D p 0 2 (m + 1) (secondDiffSource R W₀ W₁ W₂ W₃ m) ≤ S₂ := by
    intro m hm
    have hm' : m < F.top := by omega
    rw [weightedScaleNorm_zero_weight]
    set sB := innerBonds D (m + 1) with hsB
    set N1 : F.Site (m + 1) × Fin 4 → ℝ :=
      fun c => scaleWeight p θ (m + 1) c.1 * bondHullSum (c.1, c.2) (deviationFirstDiff R W₀ W₁ m) with hN1
    set N2 : F.Site (m + 1) × Fin 4 → ℝ :=
      fun c => scaleWeight p (-θ) (m + 1) c.1 * bondHullSum (c.1, c.2) (deviationFirstDiff R W₀ W₂ m) with hN2
    set b₁ : F.Site (m + 1) × Fin 4 → ℝ :=
      fun c => lowerScaleWeight p θ ⟨m, c⟩ * ‖upperSource W₁ ⟨m, c⟩ - upperSource W₀ ⟨m, c⟩‖ with hb₁
    set b₂ : F.Site (m + 1) × Fin 4 → ℝ :=
      fun c => lowerScaleWeight p (-θ) ⟨m, c⟩ * ‖upperSource W₂ ⟨m, c⟩ - upperSource W₀ ⟨m, c⟩‖ with hb₂
    have l1 : finsetLpNorm 4 sB N1 ≤ K₁ := (weightedScaleNorm_bondHullSum_le (D := D) hodd hθ hm' p 4 (by norm_num)
      (g := deviationFirstDiff R W₀ W₁ m) (fun _ _ => norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hT₁ m hm') hF0)
    have l2 : finsetLpNorm 4 sB N2 ≤ K₂ := (weightedScaleNorm_bondHullSum_le (D := D) hodd hθ' hm' p 4 (by norm_num)
      (g := deviationFirstDiff R W₀ W₂ m) (fun _ _ => norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hT₂ m hm') hF0)
    have l3 : finsetLpNorm 4 sB b₁ ≤ A₁ := (finsetLpNorm_four_le_two _ _).trans
      (finsetLpNorm_level_le_lowerBonds (D := D) hm
        (fun x => lowerScaleWeight p θ x * ‖upperSource W₁ x - upperSource W₀ x‖))
    have l4 : finsetLpNorm 4 sB b₂ ≤ A₂ := (finsetLpNorm_four_le_two _ _).trans
      (finsetLpNorm_level_le_lowerBonds (D := D) hm
        (fun x => lowerScaleWeight p (-θ) x * ‖upperSource W₂ x - upperSource W₀ x‖))
    have n1 := finsetLpNorm_nonneg 4 sB N1
    have n2 := finsetLpNorm_nonneg 4 sB N2
    have n4 := finsetLpNorm_nonneg 4 sB b₂
    have P1 : finsetLpNorm 2 sB (fun c => N1 c * N2 c) ≤ K₁ * K₂ :=
      (finsetLpNorm_two_mul_le sB N1 N2).trans (mul_le_mul l1 l2 n2 hK₁0)
    have P2 : finsetLpNorm 2 sB (fun c => b₁ c * b₂ c) ≤ A₁ * A₂ :=
      (finsetLpNorm_two_mul_le sB b₁ b₂).trans (mul_le_mul l3 l4 n4 hA₁0)
    have P3 : finsetLpNorm 2 sB (fun c => b₁ c * N2 c) ≤ A₁ * K₂ :=
      (finsetLpNorm_two_mul_le sB b₁ N2).trans (mul_le_mul l3 l2 n2 hA₁0)
    have P4 : finsetLpNorm 2 sB (fun c => b₂ c * N1 c) ≤ A₂ * K₁ :=
      (finsetLpNorm_two_mul_le sB b₂ N1).trans (mul_le_mul l4 l1 n1 hA₂0)
    set G : F.Site (m + 1) × Fin 4 → ℝ := fun c => 128 * (200000 * (F.blockSide : ℝ) ^ 2) * (N1 c * N2 c) +
      6 * 8256 * (b₁ c * b₂ c) + 4 * (b₁ c * N2 c) + 4 * (b₂ c * N1 c) with hG
    have hpt : ∀ c ∈ sB, secondDiffSource R W₀ W₁ W₂ W₃ m c.1 c.2 ≤ G c := by
      intro c hc
      have hx := mem_lowerBonds hm hc
      have hw : scaleWeight p θ (m + 1) c.1 * scaleWeight p (-θ) (m + 1) c.1 = 1 :=
        scaleWeight_mul_scaleWeight_neg hodd p θ (m + 1) c.1
      set w := scaleWeight p θ (m + 1) c.1 with hwd
      set w' := scaleWeight p (-θ) (m + 1) c.1 with hwd'
      set n₁ := bondHullSum (c.1, c.2) (deviationFirstDiff R W₀ W₁ m) with hn₁
      set n₂ := bondHullSum (c.1, c.2) (deviationFirstDiff R W₀ W₂ m) with hn₂
      have hn₁0 : 0 ≤ n₁ := bondHullSum_nonneg _ fun _ _ => norm_nonneg _
      have hn₂0 : 0 ≤ n₂ := bondHullSum_nonneg _ fun _ _ => norm_nonneg _
      set a₁ := ‖upperSource W₁ ⟨m, c⟩ - upperSource W₀ ⟨m, c⟩‖ with ha₁
      set a₂ := ‖upperSource W₂ ⟨m, c⟩ - upperSource W₀ ⟨m, c⟩‖ with ha₂
      have E₀e : levelSource W₀ m c.1 c.2 = unitExp (upperSource W₀ ⟨m, c⟩) := levelSource_eq_unitExp W₀ ⟨m, c⟩
      have E₁e : levelSource W₁ m c.1 c.2 = unitExp (upperSource W₁ ⟨m, c⟩) := levelSource_eq_unitExp W₁ ⟨m, c⟩
      have E₂e : levelSource W₂ m c.1 c.2 = unitExp (upperSource W₂ ⟨m, c⟩) := levelSource_eq_unitExp W₂ ⟨m, c⟩
      have E₃e : levelSource W₃ m c.1 c.2 = unitExp (upperSource W₃ ⟨m, c⟩) := levelSource_eq_unitExp W₃ ⟨m, c⟩
      have q1 : ‖unitExp (upperSource W₁ ⟨m, c⟩) - unitExp (upperSource W₀ ⟨m, c⟩)‖ ≤ 2 * a₁ :=
        norm_unitExp_sub_le ((s₀.upper_le _ hx).trans (by norm_num)) ((s₁.upper_le _ hx).trans (by norm_num))
      have q2 : ‖unitExp (upperSource W₂ ⟨m, c⟩) - unitExp (upperSource W₀ ⟨m, c⟩)‖ ≤ 2 * a₂ :=
        norm_unitExp_sub_le ((s₀.upper_le _ hx).trans (by norm_num)) ((s₂.upper_le _ hx).trans (by norm_num))
      have q3 : ‖unitExp (upperSource W₃ ⟨m, c⟩) - unitExp (upperSource W₁ ⟨m, c⟩) -
          unitExp (upperSource W₂ ⟨m, c⟩) + unitExp (upperSource W₀ ⟨m, c⟩)‖ ≤ 8256 * a₁ * a₂ :=
        norm_unitExp_parallelogram_le (par.upper _) (s₀.upper_le _ hx) (s₁.upper_le _ hx) (s₂.upper_le _ hx)
      have hsrc : secondDiffSource R W₀ W₁ W₂ W₃ m c.1 c.2 = 128 * (200000 * (F.blockSide : ℝ) ^ 2) * n₁ * n₂ +
          6 * ‖unitExp (upperSource W₃ ⟨m, c⟩) - unitExp (upperSource W₁ ⟨m, c⟩) -
            unitExp (upperSource W₂ ⟨m, c⟩) + unitExp (upperSource W₀ ⟨m, c⟩)‖ +
          2 * ‖unitExp (upperSource W₁ ⟨m, c⟩) - unitExp (upperSource W₀ ⟨m, c⟩)‖ * n₂ +
          2 * ‖unitExp (upperSource W₂ ⟨m, c⟩) - unitExp (upperSource W₀ ⟨m, c⟩)‖ * n₁ := by
        simp only [secondDiffSource, E₀e, E₁e, E₂e, E₃e]
        rfl
      rw [hsrc]
      have eG : G c = 128 * (200000 * (F.blockSide : ℝ) ^ 2) * ((w * w') * (n₁ * n₂)) +
          6 * 8256 * ((w * w') * (a₁ * a₂)) + 4 * ((w * w') * (a₁ * n₂)) + 4 * ((w * w') * (a₂ * n₁)) := by
        have t1 : lowerScaleWeight p θ ⟨m, c⟩ = w := rfl
        have t2 : lowerScaleWeight p (-θ) ⟨m, c⟩ = w' := rfl
        simp only [hG, hN1, hN2, hb₁, hb₂, t1, t2]
        ring
      rw [eG, hw]
      have r1 : 2 * ‖unitExp (upperSource W₁ ⟨m, c⟩) - unitExp (upperSource W₀ ⟨m, c⟩)‖ * n₂ ≤ 2 * (2 * a₁) * n₂ :=
        mul_le_mul_of_nonneg_right (by linarith) hn₂0
      have r2 : 2 * ‖unitExp (upperSource W₂ ⟨m, c⟩) - unitExp (upperSource W₀ ⟨m, c⟩)‖ * n₁ ≤ 2 * (2 * a₂) * n₁ :=
        mul_le_mul_of_nonneg_right (by linarith) hn₁0
      linarith
    have hsrc0 : ∀ c ∈ sB, 0 ≤ secondDiffSource R W₀ W₁ W₂ W₃ m c.1 c.2 := by
      intro c _
      have h1 : 0 ≤ bondHullNorm (c.1, c.2) (levelDeviation R W₁ m - levelDeviation R W₀ m) :=
        bondHullSum_nonneg _ fun _ _ => norm_nonneg _
      have h3 : 0 ≤ bondHullNorm (c.1, c.2) (levelDeviation R W₂ m - levelDeviation R W₀ m) :=
        bondHullSum_nonneg _ fun _ _ => norm_nonneg _
      simp only [secondDiffSource]
      exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by positivity) h1) h3)
        (mul_nonneg (by norm_num) (norm_nonneg _))) (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) h3))
        (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) h1)
    refine (finsetLpNorm_le_of_le (by norm_num) hsrc0 hpt).trans ?_
    have a1 := finsetLpNorm_add_le (P := 2) (by norm_num) sB
      (fun c => 128 * (200000 * (F.blockSide : ℝ) ^ 2) * (N1 c * N2 c) +
        6 * 8256 * (b₁ c * b₂ c) + 4 * (b₁ c * N2 c)) (fun c => 4 * (b₂ c * N1 c))
    have a2 := finsetLpNorm_add_le (P := 2) (by norm_num) sB
      (fun c => 128 * (200000 * (F.blockSide : ℝ) ^ 2) * (N1 c * N2 c) +
        6 * 8256 * (b₁ c * b₂ c)) (fun c => 4 * (b₁ c * N2 c))
    have a3 := finsetLpNorm_add_le (P := 2) (by norm_num) sB
      (fun c => 128 * (200000 * (F.blockSide : ℝ) ^ 2) * (N1 c * N2 c))
      (fun c => 6 * 8256 * (b₁ c * b₂ c))
    have c1 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) sB (fun c => N1 c * N2 c)
      (a := 128 * (200000 * (F.blockSide : ℝ) ^ 2)) (by positivity)
    have c2 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) sB (fun c => b₁ c * b₂ c) (a := 6 * 8256)
      (by norm_num)
    have c3 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) sB (fun c => b₁ c * N2 c) (a := 4) (by norm_num)
    have c4 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) sB (fun c => b₂ c * N1 c) (a := 4) (by norm_num)
    have d1 := mul_le_mul_of_nonneg_left P1 (by positivity : (0 : ℝ) ≤ 128 * (200000 * (F.blockSide : ℝ) ^ 2))
    show finsetLpNorm 2 sB G ≤ S₂
    rw [hG, hS₂]
    linarith
  have hη1 : 9 * η ≤ 1 := h.nine_radius_le_one
  have ht8 := h.hull_radius_small
  have hmain := weightedScaleNorm_second_diff_le hodd h2 p h.const_pos h.scale_pos h.near h.ball₀ h.ball₁ h.ball₂
    h.ball₃ h.radius_nonneg hη1 hS₂0 h.spread_le h.lt_hullBallRadius h.lipschitz_small
    (by linarith) hfac hS m hm
  refine hmain.trans ?_
  have h0 : weightedScaleNorm D p 0 2 0 (fun z d =>
        ‖(levelDeviation R W₃ 0 - levelDeviation R W₁ 0 - levelDeviation R W₂ 0 + levelDeviation R W₀ 0) z d‖) ≤
      8256 * (weightedScaleNorm D p θ 4 0 (fun x i => ‖baseSource W₁ x i - baseSource W₀ x i‖) *
        weightedScaleNorm D p (-θ) 4 0 (fun x i => ‖baseSource W₂ x i - baseSource W₀ x i‖)) := by
    rw [weightedScaleNorm_zero_weight]
    set f₁ : F.Site 0 × Fin 4 → ℝ :=
      fun b => scaleWeight p θ 0 b.1 * ‖baseSource W₁ b.1 b.2 - baseSource W₀ b.1 b.2‖ with hf₁
    set f₂ : F.Site 0 × Fin 4 → ℝ :=
      fun b => scaleWeight p (-θ) 0 b.1 * ‖baseSource W₂ b.1 b.2 - baseSource W₀ b.1 b.2‖ with hf₂
    have c1 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) (innerBonds D 0) (fun b => f₁ b * f₂ b)
      (a := 8256) (by norm_num)
    have c2 := finsetLpNorm_two_mul_le (innerBonds D 0) f₁ f₂
    have hpt : ∀ b ∈ innerBonds D 0,
        ‖(levelDeviation R W₃ 0 - levelDeviation R W₁ 0 - levelDeviation R W₂ 0 + levelDeviation R W₀ 0) b.1 b.2‖ ≤
          8256 * (f₁ b * f₂ b) := by
      intro b hb
      have hw := scaleWeight_mul_scaleWeight_neg hodd p θ 0 b.1
      have q := norm_unitExp_parallelogram_le (par.base b.1 b.2) (s₀.base_le b hb) (s₁.base_le b hb)
        (s₂.base_le b hb)
      have e1 : (levelDeviation R W₃ 0 - levelDeviation R W₁ 0 - levelDeviation R W₂ 0 + levelDeviation R W₀ 0)
          b.1 b.2 = unitExp (baseSource W₃ b.1 b.2) - unitExp (baseSource W₁ b.1 b.2) -
            unitExp (baseSource W₂ b.1 b.2) + unitExp (baseSource W₀ b.1 b.2) := by
        simp only [Pi.add_apply, Pi.sub_apply, levelDeviation_zero]
        abel
      rw [e1]
      refine q.trans (le_of_eq ?_)
      have e2 : f₁ b * f₂ b = (scaleWeight p θ 0 b.1 * scaleWeight p (-θ) 0 b.1) *
          (‖baseSource W₁ b.1 b.2 - baseSource W₀ b.1 b.2‖ * ‖baseSource W₂ b.1 b.2 - baseSource W₀ b.1 b.2‖) := by
        simp only [hf₁, hf₂]
        ring
      rw [e2, hw]
      ring
    have h3 := finsetLpNorm_le_of_le (P := 2) (by norm_num) (s := innerBonds D 0)
      (f := fun b =>
        ‖(levelDeviation R W₃ 0 - levelDeviation R W₁ 0 - levelDeviation R W₂ 0 + levelDeviation R W₀ 0) b.1 b.2‖)
      (fun _ _ => norm_nonneg _) hpt
    refine h3.trans (c1.trans ?_)
    exact mul_le_mul_of_nonneg_left c2 (by norm_num)
  linarith
end SecondBound
end CellSources
end YangMills.Construction
end
