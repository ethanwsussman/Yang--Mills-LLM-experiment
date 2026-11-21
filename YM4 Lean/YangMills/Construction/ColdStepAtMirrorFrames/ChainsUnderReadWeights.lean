import YangMills.Construction.ColdStepAtMirrorFrames.EnergyOfAFlatChainNearACellProof
import YangMills.Construction.ColdStepAtMirrorFrames.BlockMeansOfFormsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def weightedNorm {j : ℕ} (u : F.Site j → ℝ) (B : LevelForm F j) : ℝ := Real.sqrt (weightedNormSq u B)
theorem weightedNorm_nonneg {j : ℕ} (u : F.Site j → ℝ) (B : LevelForm F j) : 0 ≤ weightedNorm u B := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatChainEnergy.weightedNorm_nonneg <;> assumption
theorem weightedNorm_sq {j : ℕ} (u : F.Site j → ℝ) (B : LevelForm F j) :
    weightedNorm u B ^ 2 = weightedNormSq u B := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatChainEnergy.weightedNorm_sq <;> assumption
theorem weightedNormSq_eq_sum_product {j : ℕ} (u : F.Site j → ℝ) (B : LevelForm F j) :
    weightedNormSq u B =
      ∑ p ∈ allSites F j ×ˢ (Finset.univ : Finset (Fin 4)), (u p.1 * B p.1 p.2) ^ 2 := by
  unfold weightedNormSq
  rw [Finset.sum_product]
theorem weightedInner_le {j : ℕ} (u v : F.Site j → ℝ) (B D : LevelForm F j) :
    ∑ x ∈ allSites F j, ∑ i : Fin 4, (u x * B x i) * (v x * D x i) ≤
      weightedNorm u B * weightedNorm v D := by
  have h0 := Finset.sum_mul_sq_le_sq_mul_sq (allSites F j ×ˢ (Finset.univ : Finset (Fin 4)))
    (fun p => u p.1 * B p.1 p.2) (fun p => v p.1 * D p.1 p.2)
  have h1 := Real.abs_le_sqrt h0
  rw [Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h1
  have h := (le_abs_self _).trans h1
  unfold weightedNorm
  rw [weightedNormSq_eq_sum_product u B, weightedNormSq_eq_sum_product v D]
  rw [Finset.sum_product] at h
  exact h
theorem abs_weightedInner_le {j : ℕ} (u v : F.Site j → ℝ) (B D : LevelForm F j) :
    |∑ x ∈ allSites F j, ∑ i : Fin 4, (u x * B x i) * (v x * D x i)| ≤
      weightedNorm u B * weightedNorm v D := by
  rw [abs_le]
  refine ⟨?_, weightedInner_le u v B D⟩
  have h := weightedInner_le u v B (-D)
  have hneg : weightedNorm v (-D) = weightedNorm v D := by
    unfold weightedNorm weightedNormSq
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp
  have hsum : ∑ x ∈ allSites F j, ∑ i : Fin 4, (u x * B x i) * (v x * (-D) x i) =
      - ∑ x ∈ allSites F j, ∑ i : Fin 4, (u x * B x i) * (v x * D x i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [hneg, hsum] at h
  linarith
theorem weightedNorm_add_le {j : ℕ} (u : F.Site j → ℝ) (B D : LevelForm F j) :
    weightedNorm u (B + D) ≤ weightedNorm u B + weightedNorm u D := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatChainEnergy.weightedNorm_add_le <;> assumption
theorem weightedNorm_neg {j : ℕ} (u : F.Site j → ℝ) (B : LevelForm F j) :
    weightedNorm u (-B) = weightedNorm u B := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatChainEnergy.weightedNorm_neg <;> assumption
theorem weightedNorm_sub_le {j : ℕ} (u : F.Site j → ℝ) (B D : LevelForm F j) :
    weightedNorm u (B - D) ≤ weightedNorm u B + weightedNorm u D := by
  rw [sub_eq_add_neg]
  refine (weightedNorm_add_le u B (-D)).trans ?_
  rw [weightedNorm_neg]
def IsReadMonotone (U : (j : ℕ) → F.Site j → ℝ) : Prop :=
  ∀ j, j + 1 ≤ F.top → ∀ (y : F.Site (j + 1)) (k l : Fin 4), ∀ h ∈ centredCube F.blockSide,
    ∀ m ∈ Finset.range F.blockSide, ∀ m' ∈ Finset.range F.blockSide,
      U (j + 1) y ^ 2 ≤
        U j (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (m : ℤ) + axisOffset j l (m' : ℤ)) ^ 2
theorem weightedNorm_lineAverage_le (hL : Odd F.blockSide) (hext : ∀ i, 0 < F.extent i)
    {U : (j : ℕ) → F.Site j → ℝ} (hU : IsReadMonotone U) {j : ℕ} (hj : j + 1 ≤ F.top)
    (X : LevelForm F j) :
    weightedNorm (U (j + 1)) (lineAverage X) ≤ (1 / (F.blockSide : ℝ)) * weightedNorm (U j) X := by
  have hLpos : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have h := weightedNormSq_lineAverage_le hL hext hj (U (j + 1)) (U j) 1 zero_le_one X
    (fun i y h hh l hl => by
      have := hU j hj y i i h hh l hl 0 (Finset.mem_range.2 hL.pos)
      simp only [Nat.cast_zero, axisOffset_zero, add_zero] at this
      simpa using this)
  unfold weightedNorm
  refine (Real.sqrt_le_sqrt h).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by positivity),
    show (1 / (F.blockSide : ℝ) ^ 2) = (1 / (F.blockSide : ℝ)) ^ 2 by field_simp,
    Real.sqrt_sq (by positivity)]
def chainDefect (B : FormChain F) (j : ℕ) : LevelForm F j := iteratedLineAverage (B 0) j - B j
theorem chainDefect_zero (B : FormChain F) : chainDefect B 0 = 0 := by
  unfold chainDefect
  exact sub_self _
theorem chainDefect_succ (B : FormChain F) (j : ℕ) :
    chainDefect B (j + 1) = lineAverage (chainDefect B j) + chainMisfit B j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatChainEnergy.iterated_sub_succ <;> assumption
theorem formChain_succ_eq (B : FormChain F) (j : ℕ) :
    B (j + 1) = lineAverage (B j) - chainMisfit B j := by
  funext y i
  simp only [chainMisfit, Pi.sub_apply]
  ring
def totalMisfit (U : (j : ℕ) → F.Site j → ℝ) (B : FormChain F) : ℝ :=
  ∑ j ∈ Finset.range F.top, weightedNormSq (U (j + 1)) (chainMisfit B j)
theorem totalMisfit_nonneg (U : (j : ℕ) → F.Site j → ℝ) (B : FormChain F) : 0 ≤ totalMisfit U B :=
  Finset.sum_nonneg fun _ _ => weightedNormSq_nonneg _ _
theorem weightedNorm_chainMisfit_le (U : (j : ℕ) → F.Site j → ℝ) (B : FormChain F) {j : ℕ}
    (hj : j + 1 ≤ F.top) :
    weightedNorm (U (j + 1)) (chainMisfit B j) ≤ Real.sqrt (totalMisfit U B) := by
  refine Real.sqrt_le_sqrt ?_
  exact Finset.single_le_sum (f := fun j => weightedNormSq (U (j + 1)) (chainMisfit B j))
    (fun _ _ => weightedNormSq_nonneg _ _) (Finset.mem_range.2 (by omega))
theorem weightedNorm_chainDefect_le (hL : Odd F.blockSide) (hext : ∀ i, 0 < F.extent i)
    (h3 : 3 ≤ F.blockSide) {U : (j : ℕ) → F.Site j → ℝ} (hU : IsReadMonotone U) (B : FormChain F)
    {j : ℕ} (hj : j ≤ F.top) :
    weightedNorm (U j) (chainDefect B j) ≤ 3 / 2 * Real.sqrt (totalMisfit U B) := by
  have hL3 : (3 : ℝ) ≤ F.blockSide := by exact_mod_cast h3
  induction j with
  | zero =>
    rw [chainDefect_zero]
    have : weightedNorm (U 0) (0 : LevelForm F 0) = 0 := by
      unfold weightedNorm weightedNormSq
      simp
    rw [this]
    positivity
  | succ j ih =>
    have ih' := ih (by omega)
    rw [chainDefect_succ]
    refine (weightedNorm_add_le _ _ _).trans ?_
    have a1 := weightedNorm_lineAverage_le hL hext hU hj (chainDefect B j)
    have a2 := weightedNorm_chainMisfit_le U B hj
    have a3 : (1 / (F.blockSide : ℝ)) * weightedNorm (U j) (chainDefect B j) ≤
        1 / 3 * (3 / 2 * Real.sqrt (totalMisfit U B)) := by
      refine mul_le_mul ?_ ih' (weightedNorm_nonneg _ _) (by norm_num)
      exact one_div_le_one_div_of_le (by norm_num) hL3
    linarith
theorem pow_mul_weightedNorm_le (hL : Odd F.blockSide) (hext : ∀ i, 0 < F.extent i)
    (h3 : 3 ≤ F.blockSide) {U : (j : ℕ) → F.Site j → ℝ} (hU : IsReadMonotone U) (B : FormChain F)
    {j : ℕ} (hj : j ≤ F.top) :
    (F.blockSide : ℝ) ^ j * weightedNorm (U j) (B j) ≤
      weightedNorm (U 0) (B 0) + 3 / 2 * (F.blockSide : ℝ) ^ j * Real.sqrt (totalMisfit U B) := by
  have hL3 : (3 : ℝ) ≤ F.blockSide := by exact_mod_cast h3
  have hS := Real.sqrt_nonneg (totalMisfit U B)
  induction j with
  | zero =>
    simp only [pow_zero, one_mul, mul_one]
    nlinarith
  | succ j ih =>
    have ih' := ih (by omega)
    have a1 : weightedNorm (U (j + 1)) (B (j + 1)) ≤
        (1 / (F.blockSide : ℝ)) * weightedNorm (U j) (B j) + Real.sqrt (totalMisfit U B) := by
      rw [formChain_succ_eq B j]
      refine (weightedNorm_sub_le _ _ _).trans ?_
      have := weightedNorm_lineAverage_le hL hext hU hj (B j)
      have := weightedNorm_chainMisfit_le U B hj
      linarith
    have a2 : (F.blockSide : ℝ) ^ (j + 1) * weightedNorm (U (j + 1)) (B (j + 1)) ≤
        (F.blockSide : ℝ) ^ j * weightedNorm (U j) (B j) +
          (F.blockSide : ℝ) ^ (j + 1) * Real.sqrt (totalMisfit U B) := by
      have := mul_le_mul_of_nonneg_left a1 (by positivity : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ (j + 1))
      refine this.trans (le_of_eq ?_)
      rw [pow_succ]
      field_simp
    have a3 : 3 / 2 * (F.blockSide : ℝ) ^ j * Real.sqrt (totalMisfit U B) +
        (F.blockSide : ℝ) ^ (j + 1) * Real.sqrt (totalMisfit U B) ≤
          3 / 2 * (F.blockSide : ℝ) ^ (j + 1) * Real.sqrt (totalMisfit U B) := by
      rw [pow_succ]
      have : 0 ≤ (F.blockSide : ℝ) ^ j * Real.sqrt (totalMisfit U B) := by positivity
      nlinarith
    linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
