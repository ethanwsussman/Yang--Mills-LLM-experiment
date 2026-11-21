import YangMills.Construction.ClusterExpansionOfAStep.BondsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheWeightsOfFreeBonds
import YangMills.Construction.LawInAState.DecayOverATorusProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields StepSettings TorusLumps
theorem summable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Summable fun k : ℤ => Real.exp (-(a * |(k : ℝ)|)) := by apply _root_.YangMills.SharedProofs.p3695 <;> assumption
theorem sum_exp_valMinAbs_le_tsum {a : ℝ} (ha : 0 < a) (N : ℕ) [NeZero N] (c : ZMod N) :
    ∑ z : ZMod N, Real.exp (-(a * (((z - c).valMinAbs.natAbs : ℕ) : ℝ))) ≤
      ∑' k : ℤ, Real.exp (-(a * |(k : ℝ)|)) := by
  have hshift := (Equiv.subRight c).sum_comp
    (fun z : ZMod N => Real.exp (-(a * ((z.valMinAbs.natAbs : ℕ) : ℝ))))
  simp only [Equiv.subRight_apply] at hshift
  rw [hshift]
  have hinj : Function.Injective (ZMod.valMinAbs : ZMod N → ℤ) := by
    intro x y h
    have := congrArg (Int.cast : ℤ → ZMod N) h
    simpa [ZMod.coe_valMinAbs] using this
  have hterm : ∀ z : ZMod N, Real.exp (-(a * ((z.valMinAbs.natAbs : ℕ) : ℝ))) =
      (fun k : ℤ => Real.exp (-(a * |(k : ℝ)|))) z.valMinAbs := by
    intro z
    simp only [Nat.cast_natAbs, Int.cast_abs]
  simp only [hterm]
  rw [← Finset.sum_image (f := fun k : ℤ => Real.exp (-(a * |(k : ℝ)|)))
    (g := ZMod.valMinAbs) (s := Finset.univ) (fun x _ y _ h => hinj h)]
  exact (summable_exp_neg_mul_abs ha).sum_le_tsum _ fun k _ => (Real.exp_pos _).le
theorem sum_exp_supDist_le_pow {a : ℝ} (ha : 0 < a) (N : ℕ) [NeZero N] (x₀ : TorusSite N) :
    ∑ x : TorusSite N, Real.exp (-(4 * a * (supDist x x₀ : ℝ))) ≤
      (∑' k : ℤ, Real.exp (-(a * |(k : ℝ)|))) ^ 4 := by
  have hprod : ∀ x : TorusSite N, Real.exp (-(4 * a * (supDist x x₀ : ℝ))) ≤
      ∏ i : Fin 4, Real.exp (-(a * ((((x i - x₀ i).valMinAbs.natAbs : ℕ)) : ℝ))) := by
    intro x
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    have hcoord : ∀ i : Fin 4, (((x i - x₀ i).valMinAbs.natAbs : ℕ) : ℝ) ≤ supDist x x₀ := by
      intro i
      exact_mod_cast (supDist_le_iff x x₀ (supDist x x₀)).mp le_rfl i
    have hsum : ∑ i : Fin 4, (((x i - x₀ i).valMinAbs.natAbs : ℕ) : ℝ) ≤ 4 * supDist x x₀ := by
      calc _ ≤ ∑ _i : Fin 4, (supDist x x₀ : ℝ) := Finset.sum_le_sum fun i _ => hcoord i
        _ = _ := by simp
    have hneg : ∑ i : Fin 4, -(a * (((x i - x₀ i).valMinAbs.natAbs : ℕ) : ℝ)) =
        -(a * ∑ i : Fin 4, (((x i - x₀ i).valMinAbs.natAbs : ℕ) : ℝ)) := by
      rw [Finset.sum_neg_distrib, Finset.mul_sum]
    rw [hneg]
    nlinarith
  refine (Finset.sum_le_sum fun x _ => hprod x).trans ?_
  have hfactor := Finset.prod_univ_sum (fun _ : Fin 4 => (Finset.univ : Finset (ZMod N)))
    (fun i z => Real.exp (-(a * ((((z - x₀ i).valMinAbs.natAbs : ℕ)) : ℝ))))
  rw [Fintype.piFinset_univ] at hfactor
  rw [← hfactor]
  calc _ ≤ ∏ _i : Fin 4, ∑' k : ℤ, Real.exp (-(a * |(k : ℝ)|)) :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun z _ => (Real.exp_pos _).le)
          fun i _ => sum_exp_valMinAbs_le_tsum ha N (x₀ i)
    _ = _ := by simp
theorem freeBondWeightsSummable_of_bondsPerBlockBound (hB : BondsPerBlockBound) :
    FreeBondWeightsSummable := by
  intro S hrt N _ s b₀
  set x₀ := bondBlock (R := S) b₀.1 with hx₀
  set blk : s.free → TorusSite N := fun b => bondBlock (R := S) b.1 with hblk
  set w : TorusSite N → ℝ := fun x => Real.exp (-(4 * (S.params.rt / 2) * (supDist x x₀ : ℝ))) with hw
  have hweight : ∀ b : s.free, Real.exp (-(2 * S.params.rt * s.bondDist b b₀)) = w (blk b) := by
    intro b
    simp only [hw, hblk, ChartSetting.bondDist, bondBlockDist, hx₀]
    congr 2
    ring
  simp only [hweight]
  have hcard : ∀ x : TorusSite N, (((Finset.univ.filter fun b : s.free => blk b = x).card : ℕ) : ℝ) ≤
      S.params.blockBondBound := by
    intro x
    refine le_trans ?_ (hB S.params.side N x)
    have : (Finset.univ.filter fun b : s.free => blk b = x).card ≤
        (Finset.univ.filter fun b : TorusBond (N * S.params.side) => parentBlock S.params.side b.1 = x).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro b hb
        simpa [hblk, bondBlock] using hb
      · exact fun p _ q _ h => Subtype.ext h
    exact_mod_cast this
  have hnonneg : ∀ x, 0 ≤ w x := fun x => (Real.exp_pos _).le
  calc ∑ b : s.free, w (blk b) = ∑ x : TorusSite N, ∑ b ∈ Finset.univ.filter (fun b : s.free => blk b = x),
        w (blk b) := (Finset.sum_fiberwise _ _ _).symm
    _ = ∑ x : TorusSite N, ((Finset.univ.filter fun b : s.free => blk b = x).card : ℝ) * w x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_congr rfl (g := fun _ => w x) (fun b hb => by
          rw [(Finset.mem_filter.mp hb).2]), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x : TorusSite N, S.params.blockBondBound * w x :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hcard x) (hnonneg x)
    _ = S.params.blockBondBound * ∑ x : TorusSite N, w x := by rw [Finset.mul_sum]
    _ ≤ S.params.bondWeightBound := by
        have hb0 : 0 ≤ S.params.blockBondBound := by
          unfold StepParameters.blockBondBound
          positivity
        exact mul_le_mul_of_nonneg_left (sum_exp_supDist_le_pow (by positivity) N x₀) hb0
end YangMills.Construction.ClusterExpansionOfAStep
end
