import YangMills.Construction.ColdStepAtMirrorFrames.SumsThatAgreeNearAPointProof
import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponsesProof
import YangMills.Construction.SummableBoundsOfTheFlow.SumOfTheWeightsAboutACell
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.CellCounting
open Finset BlockAverages
theorem sum_pow_natAbs_Icc_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (R : ℕ) :
    ∑ k ∈ Icc (-(R : ℤ)) R, q ^ k.natAbs ≤ 2 * (1 - q)⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.sum_Icc_pow_natAbs_le <;> assumption
theorem sum_prod_pow_natAbs_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (S : Finset (Fin 4 → ℤ)) :
    ∑ v ∈ S, ∏ i, q ^ (v i).natAbs ≤ (2 * (1 - q)⁻¹) ^ 4 := by
  set R : ℕ := S.sup fun v => ∑ i, (v i).natAbs
  have hsub : S ⊆ Fintype.piFinset fun _ : Fin 4 => Icc (-(R : ℤ)) R := by
    intro v hv
    rw [Fintype.mem_piFinset]
    intro i
    have h1 : (v i).natAbs ≤ ∑ i, (v i).natAbs :=
      single_le_sum (f := fun i => (v i).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
    have h2 : ∑ i, (v i).natAbs ≤ R := le_sup (f := fun v : Fin 4 → ℤ => ∑ i, (v i).natAbs) hv
    rw [mem_Icc]
    omega
  calc ∑ v ∈ S, ∏ i, q ^ (v i).natAbs
      ≤ ∑ v ∈ Fintype.piFinset fun _ : Fin 4 => Icc (-(R : ℤ)) R, ∏ i, q ^ (v i).natAbs :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => prod_nonneg fun _ _ => pow_nonneg hq0 _
    _ = ∏ _i : Fin 4, ∑ k ∈ Icc (-(R : ℤ)) R, q ^ k.natAbs := by
        rw [prod_univ_sum]
    _ ≤ ∏ _i : Fin 4, 2 * (1 - q)⁻¹ :=
        prod_le_prod (fun _ _ => sum_nonneg fun _ _ => pow_nonneg hq0 _) fun _ _ =>
          sum_pow_natAbs_Icc_le hq0 hq1 R
    _ = (2 * (1 - q)⁻¹) ^ 4 := by simp
variable {F : BlockFrame}
def relCoords (z c : F.Cell) : Fin 4 → ℤ := fun i => (c i - z i).valMinAbs
theorem relCoords_injective (z : F.Cell) : Function.Injective (relCoords z) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.DecayingSums.offset_injective <;> assumption
theorem exp_neg_cellSupDist_le_prod {κ : ℝ} (hκ : 0 < κ) (z c : F.Cell) :
    Real.exp (-(κ * (cellSupDist c z : ℝ))) ≤
      ∏ i, Real.exp (-(κ / 4)) ^ (relCoords z c i).natAbs := by
  rw [prod_pow_eq_pow_sum, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h1 : ∑ i, (relCoords z c i).natAbs ≤ 4 * cellSupDist c z := by
    have : ∀ i ∈ (univ : Finset (Fin 4)), (relCoords z c i).natAbs ≤ cellSupDist c z := fun i _ =>
      le_sup (f := fun i => ((c i - z i).valMinAbs).natAbs) (mem_univ i)
    have h := sum_le_card_nsmul _ _ _ this
    simpa using h
  have h2 : ((∑ i, (relCoords z c i).natAbs : ℕ) : ℝ) ≤ 4 * (cellSupDist c z : ℝ) := by
    exact_mod_cast h1
  nlinarith
theorem expDecaySumBounded_holds : ExpDecaySumBounded := by
  intro N κ hκ
  set q : ℝ := Real.exp (-(κ / 4)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    have := Real.exp_lt_exp.mpr (show -(κ / 4) < 0 by linarith)
    rw [Real.exp_zero] at this
    exact this
  refine ⟨N * (2 * (1 - q)⁻¹) ^ 4, by positivity, ?_⟩
  intro F ι _ y hy z
  classical
  set T : Finset F.Cell := univ.image y with hT
  have hfib : ∑ b, Real.exp (-(κ * (cellSupDist (y b) z : ℝ))) =
      ∑ c ∈ T, ∑ b ∈ univ.filter (fun b => y b = c), Real.exp (-(κ * (cellSupDist (y b) z : ℝ))) := by
    rw [sum_fiberwise_of_maps_to]
    intro b _
    exact mem_image_of_mem _ (mem_univ b)
  have hfiber : ∀ c ∈ T,
      ∑ b ∈ univ.filter (fun b => y b = c), Real.exp (-(κ * (cellSupDist (y b) z : ℝ))) ≤
        N * ∏ i, q ^ (relCoords z c i).natAbs := by
    intro c _
    have hconst : ∀ b ∈ univ.filter (fun b => y b = c),
        Real.exp (-(κ * (cellSupDist (y b) z : ℝ))) ≤ ∏ i, q ^ (relCoords z c i).natAbs := by
      intro b hb
      rw [(mem_filter.mp hb).2]
      exact exp_neg_cellSupDist_le_prod hκ z c
    have hs := sum_le_card_nsmul _ _ _ hconst
    rw [nsmul_eq_mul] at hs
    have hc : ((univ.filter fun b => y b = c).card : ℝ) ≤ N := by
      have := hy c
      convert (Nat.cast_le (α := ℝ)).mpr this using 2
    have hnn : 0 ≤ ∏ i, q ^ (relCoords z c i).natAbs := prod_nonneg fun _ _ => pow_nonneg hq0 _
    exact hs.trans (mul_le_mul_of_nonneg_right hc hnn)
  rw [hfib]
  calc ∑ c ∈ T, ∑ b ∈ univ.filter (fun b => y b = c), Real.exp (-(κ * (cellSupDist (y b) z : ℝ)))
      ≤ ∑ c ∈ T, N * ∏ i, q ^ (relCoords z c i).natAbs := sum_le_sum hfiber
    _ = N * ∑ v ∈ T.image (relCoords z), ∏ i, q ^ (v i).natAbs := by
        rw [← mul_sum, sum_image (fun a _ b _ h => relCoords_injective z h)]
    _ ≤ N * (2 * (1 - q)⁻¹) ^ 4 :=
        mul_le_mul_of_nonneg_left (sum_prod_pow_natAbs_le hq0 hq1 _) (Nat.cast_nonneg _)
end YangMills.Construction.CellCounting
