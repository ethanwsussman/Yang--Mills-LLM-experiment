import YangMills.Construction.ColdChainAtEveryLevel.CurlOfTheTopAverageProof
import YangMills.Construction.ColdChainAtEveryLevel.TopAverageNearACell
import YangMills.Construction.ColdChainAtEveryLevel.TopAverageOfAnyChainProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace TopAverageLocal
open YangMills.Construction.BlockLines
variable {F : BlockFrame}
def coarseOnlyChart (U : ChainChart F) : ChainChart F := ⟨fun _ _ => 0, U.coarse⟩
theorem adjointAction_add (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p + q) = adjointAction g p + adjointAction g q := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem parallelAverage_add {j : ℕ} (A : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ])
    (e : F.Site (j + 1) × Fin 4) :
    parallelAverage A (fun x i => f x i + g x i) e =
      parallelAverage A f e + parallelAverage A g e := by
  simp only [parallelAverage, _root_.YangMills.Construction.BlockAverages.TopAverageLocal.adjointAction_add, Finset.sum_add_distrib, smul_add]
theorem linearPart_eq_add (A : F.FieldChain) (U : ChainChart F) (k : ℕ) :
    linearPart A U k = fun x i => linearPart A (baseOnlyChart U.fine) k x i + linearPart A (coarseOnlyChart U) k x i := by apply _root_.YangMills.Construction.BlockAverages.LinearPartBound.linearPart_eq_add <;> assumption
theorem norm_add_sq_le (p q : ℍ[ℝ]) : ‖p + q‖ ^ 2 ≤ 2 * ‖p‖ ^ 2 + 2 * ‖q‖ ^ 2 := by apply _root_.YangMills.Construction.TopAverageCurl.norm_add_sq_le <;> assumption
theorem sum_norm_linearPart_fine_pow_four_le (hL : Odd F.blockSide) (B : Finset F.Cell) (A : F.FieldChain)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (k : ℕ) (hk : k ≤ F.top) :
    ∑ b ∈ innerBonds B k, ‖linearPart A (baseOnlyChart u) k b.1 b.2‖ ^ 4 ≤
      ∑ b ∈ innerBonds B 0, ‖(u b.1 b.2 : ℍ[ℝ])‖ ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.LinearPartBound.sum_norm_linearPart_baseOnly_pow_four_le <;> assumption
theorem sum_norm_linearPart_coarse_sq_le (hL : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide) (B : Finset F.Cell)
    (A : F.FieldChain) (U : ChainChart F) (k : ℕ) (hk : k ≤ F.top) :
    ∑ b ∈ innerBonds B k, ‖linearPart A (coarseOnlyChart U) k b.1 b.2‖ ^ 2 ≤
      4 * ∑ j ∈ (Finset.range k).filter (fun j => j + 1 < F.top), ∑ e ∈ innerBonds B (j + 1),
        ‖(U.coarse j e.1 e.2 : ℍ[ℝ])‖ ^ 2 := by apply _root_.YangMills.Construction.TopAverageCurl.sum_linearPart_coarseOnly_sq_le <;> assumption
theorem sqrt_sqrt_add_two_mul_sqrt_le (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (Real.sqrt x) + 2 * Real.sqrt y ≤ 3 * Real.sqrt (Real.sqrt x + z + y) := by apply _root_.YangMills.Construction.BlockAverages.LinearPartBound.sqrt_sqrt_add_two_mul_sqrt_le <;> assumption
end TopAverageLocal
open YangMills.Construction.BlockLines
theorem topAverageLocalBound : topAverageLocalBoundStatement := by
  refine ⟨3, by norm_num, fun F S hL hL5 hamb U c hc => ?_⟩
  classical
  set A := referenceFieldChain S (flatTopField : F.GaugeField F.top) with hA
  set z := enclosingCell c.1 with hz
  set B := cellBall S z 1 with hB
  have hcB : c ∈ innerBonds B F.top := by
    have : c ∈ bondsOver S {z} F.top := Finset.mem_filter.2 ⟨hc, Finset.mem_singleton.2 rfl⟩
    exact mem_innerBonds_cellBall_of_mem_bondsOver hamb hL S z le_rfl this
  have hsplit : linearPart A U F.top c.1 c.2 = linearPart A (baseOnlyChart U.fine) F.top c.1 c.2 +
      linearPart A (TopAverageLocal.coarseOnlyChart U) F.top c.1 c.2 :=
    congrFun (congrFun (TopAverageLocal.linearPart_eq_add A U F.top) c.1) c.2
  rw [hsplit]
  have h4 := TopAverageLocal.sum_norm_linearPart_fine_pow_four_le hL B A U.fine F.top le_rfl
  have h2 := TopAverageLocal.sum_norm_linearPart_coarse_sq_le hL (by omega) B A U F.top le_rfl
  set X : ℝ := ∑ b ∈ bondsOver S (cellBall S z 3) 0,
      ((fun _ _ => (1 : ℝ) : F.SiteWeights) 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 with hX
  set Y : ℝ := ∑ j ∈ Finset.range (F.top - 1), ∑ e ∈ bondsOver S (cellBall S z 3) (j + 1),
      ((fun _ _ => (1 : ℝ) : F.SiteWeights) (j + 1) e.1 * ‖U.coarse j e.1 e.2‖) ^ 2 with hY
  set Z : ℝ := ∑ p ∈ plaquettesOver S (cellBall S z 3) 0,
      ((fun _ _ => (1 : ℝ) : F.SiteWeights) 0 p.1 * ‖linearizedCurl (A 0) U.fine p‖) ^ 2 with hZ
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => pow_nonneg (mul_nonneg zero_le_one (norm_nonneg _)) 4
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    pow_nonneg (mul_nonneg zero_le_one (norm_nonneg _)) 2
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => pow_nonneg (mul_nonneg zero_le_one (norm_nonneg _)) 2
  have hu : ‖linearPart A (baseOnlyChart U.fine) F.top c.1 c.2‖ ^ 4 ≤ X := by
    have a1 : ‖linearPart A (baseOnlyChart U.fine) F.top c.1 c.2‖ ^ 4 ≤
        ∑ b ∈ innerBonds B F.top, ‖linearPart A (baseOnlyChart U.fine) F.top b.1 b.2‖ ^ 4 :=
      Finset.single_le_sum (f := fun b : F.Site F.top × Fin 4 => ‖linearPart A (baseOnlyChart U.fine) F.top b.1 b.2‖ ^ 4)
        (fun _ _ => pow_nonneg (norm_nonneg _) _) hcB
    refine (a1.trans h4).trans ?_
    have a2 : ∑ b ∈ innerBonds B 0, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 ≤
        ∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => mem_bondsOver_of_mem_innerBonds_cellBall hL S z 0 hb)
        (fun _ _ _ => pow_nonneg (norm_nonneg _) _)
    refine a2.trans (le_of_eq ?_)
    simp only [hX, one_mul]
    rfl
  have hm : ‖linearPart A (TopAverageLocal.coarseOnlyChart U) F.top c.1 c.2‖ ^ 2 ≤ 4 * Y := by
    have a1 : ‖linearPart A (TopAverageLocal.coarseOnlyChart U) F.top c.1 c.2‖ ^ 2 ≤
        ∑ b ∈ innerBonds B F.top, ‖linearPart A (TopAverageLocal.coarseOnlyChart U) F.top b.1 b.2‖ ^ 2 :=
      Finset.single_le_sum (f := fun b : F.Site F.top × Fin 4 =>
        ‖linearPart A (TopAverageLocal.coarseOnlyChart U) F.top b.1 b.2‖ ^ 2) (fun _ _ => pow_nonneg (norm_nonneg _) _) hcB
    refine (a1.trans h2).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hfil : (Finset.range F.top).filter (fun j => j + 1 < F.top) ⊆ Finset.range (F.top - 1) := by
      intro j hj
      have := (Finset.mem_filter.1 hj).2
      exact Finset.mem_range.2 (by omega)
    have a3 : ∑ j ∈ (Finset.range F.top).filter (fun j => j + 1 < F.top), ∑ e ∈ innerBonds B (j + 1),
        ‖(U.coarse j e.1 e.2 : ℍ[ℝ])‖ ^ 2 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ e ∈ innerBonds B (j + 1),
        ‖(U.coarse j e.1 e.2 : ℍ[ℝ])‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hfil
        (fun _ _ _ => Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 2)
    refine a3.trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    have a4 : ∑ e ∈ innerBonds B (j + 1), ‖(U.coarse j e.1 e.2 : ℍ[ℝ])‖ ^ 2 ≤
        ∑ e ∈ bondsOver S (cellBall S z 3) (j + 1), ‖(U.coarse j e.1 e.2 : ℍ[ℝ])‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => mem_bondsOver_of_mem_innerBonds_cellBall hL S z (j + 1) hb)
        (fun _ _ _ => pow_nonneg (norm_nonneg _) _)
    refine a4.trans (le_of_eq ?_)
    simp only [one_mul]
    rfl
  have hu' : ‖linearPart A (baseOnlyChart U.fine) F.top c.1 c.2‖ ≤ Real.sqrt (Real.sqrt X) := by
    refine Real.le_sqrt_of_sq_le (Real.le_sqrt_of_sq_le ?_)
    calc (‖linearPart A (baseOnlyChart U.fine) F.top c.1 c.2‖ ^ 2) ^ 2 =
          ‖linearPart A (baseOnlyChart U.fine) F.top c.1 c.2‖ ^ 4 := by ring
      _ ≤ X := hu
  have hm' : ‖linearPart A (TopAverageLocal.coarseOnlyChart U) F.top c.1 c.2‖ ≤ 2 * Real.sqrt Y := by
    have : ‖linearPart A (TopAverageLocal.coarseOnlyChart U) F.top c.1 c.2‖ ≤ Real.sqrt (4 * Y) :=
      Real.le_sqrt_of_sq_le hm
    refine this.trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by norm_num)]
    congr 1
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine (norm_add_le _ _).trans ?_
  have hfin := TopAverageLocal.sqrt_sqrt_add_two_mul_sqrt_le X Y Z hX0 hY0 hZ0
  refine (add_le_add hu' hm').trans (hfin.trans (le_of_eq ?_))
  rfl
end YangMills.Construction.BlockAverages
end
