import YangMills.Construction.ColdStepAtMirrorFrames.SumOfADecayOverTheCells
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
namespace ExpDecaySum
def geomWeight (r : ℝ) (z : ℤ) : ℝ := r ^ z.natAbs
theorem summable_geomWeight {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : Summable (geomWeight r) := by
  apply Summable.of_nat_of_neg
  · simpa [geomWeight] using summable_geometric_of_lt_one h0 h1
  · simpa [geomWeight] using summable_geometric_of_lt_one h0 h1
theorem geomWeight_nonneg {r : ℝ} (h0 : 0 ≤ r) (z : ℤ) : 0 ≤ geomWeight r z := pow_nonneg h0 _
def minimalDisplacement {F : BlockFrame} {j : ℕ} (Y Z : F.Site j) : Fin 4 → ℤ :=
  fun i => ((Y i - Z i).valMinAbs)
theorem minimalDisplacement_injective {F : BlockFrame} {j : ℕ} (Y : F.Site j) :
    Function.Injective (minimalDisplacement Y) := by
  intro Z Z' h
  funext i
  have h1 : (Y i - Z i).valMinAbs = (Y i - Z' i).valMinAbs := congrFun h i
  have h2 : Y i - Z i = Y i - Z' i := ZMod.valMinAbs_inj.1 h1
  exact sub_right_injective h2
theorem exp_neg_le_prod_geomWeight {F : BlockFrame} {j : ℕ} {γ : ℝ} (hγ : 0 < γ) (Y Z : F.Site j) :
    Real.exp (-(γ * siteSupDist Y Z)) ≤ ∏ i, geomWeight (Real.exp (-(γ / 4))) (minimalDisplacement Y Z i) := by
  have h1 : ∀ i, (minimalDisplacement Y Z i).natAbs ≤ siteSupDist Y Z := fun i =>
    Finset.le_sup (f := fun i => ((Y i - Z i).valMinAbs).natAbs) (Finset.mem_univ i)
  have h2 : ∏ i, geomWeight (Real.exp (-(γ / 4))) (minimalDisplacement Y Z i) =
      Real.exp (-(γ / 4) * ∑ i, ((minimalDisplacement Y Z i).natAbs : ℝ)) := by
    simp only [geomWeight, ← Real.exp_nat_mul]
    rw [← Real.exp_sum, Finset.mul_sum]
    refine congrArg Real.exp (Finset.sum_congr rfl fun i _ => ?_)
    ring
  rw [h2, Real.exp_le_exp]
  have h3 : ∑ i, ((minimalDisplacement Y Z i).natAbs : ℝ) ≤ 4 * (siteSupDist Y Z : ℝ) := by
    have : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
        ((minimalDisplacement Y Z i).natAbs : ℝ) ≤ (siteSupDist Y Z : ℝ) :=
      fun i _ => by exact_mod_cast h1 i
    simpa using Finset.sum_le_sum this
  nlinarith
theorem expDecaySumBounded_holds : ExpDecaySumBounded := by
  intro γ hγ
  set r : ℝ := Real.exp (-(γ / 4)) with hr
  have h0 : 0 ≤ r := (Real.exp_pos _).le
  have h1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith
  have hs := summable_geomWeight h0 h1
  set S0 : ℝ := ∑' z, geomWeight r z with hS0
  refine ⟨S0 ^ 4 + 1, by positivity, ?_⟩
  intro F j Y W
  classical
  set A : Fin 4 → Finset ℤ := fun i => W.image fun Z => minimalDisplacement Y Z i with hA
  have hle : ∑ Z ∈ W, Real.exp (-(γ * siteSupDist Y Z)) ≤
      ∑ Z ∈ W, ∏ i, geomWeight r (minimalDisplacement Y Z i) :=
    Finset.sum_le_sum fun Z _ => exp_neg_le_prod_geomWeight hγ Y Z
  have himg : ∑ Z ∈ W, ∏ i, geomWeight r (minimalDisplacement Y Z i) =
      ∑ z ∈ W.image (minimalDisplacement Y), ∏ i, geomWeight r (z i) := by
    rw [Finset.sum_image fun Z _ Z' _ h => minimalDisplacement_injective Y h]
  have hsub : W.image (minimalDisplacement Y) ⊆ Fintype.piFinset A := by
    intro z hz
    obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.1 hz
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image.2 ⟨Z, hZ, rfl⟩
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun z : Fin 4 → ℤ => ∏ i, geomWeight r (z i))
    (fun z _ _ => Finset.prod_nonneg fun i _ => geomWeight_nonneg h0 _)
  have hprod : ∑ z ∈ Fintype.piFinset A, ∏ i, geomWeight r (z i) = ∏ i, ∑ z ∈ A i, geomWeight r z :=
    (Finset.prod_univ_sum A fun _ z => geomWeight r z).symm
  have hb : ∏ i, ∑ z ∈ A i, geomWeight r z ≤ ∏ _i : Fin 4, S0 :=
    Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun z _ => geomWeight_nonneg h0 z)
      fun i _ => hs.sum_le_tsum _ fun z _ => geomWeight_nonneg h0 z
  have hc : ∏ _i : Fin 4, S0 = S0 ^ 4 := by simp
  linarith
end ExpDecaySum
end ColdStepAtMirrorFrames
end YangMills.Construction
end
