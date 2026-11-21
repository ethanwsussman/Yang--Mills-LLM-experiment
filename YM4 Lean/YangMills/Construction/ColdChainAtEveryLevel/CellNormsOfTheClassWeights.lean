import YangMills.Construction.ColdChainAtEveryLevel.SmallMultiplesOfTwoDirections
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.SmallMultiples
variable {F : BlockAverages.BlockFrame}
open BlockAverages LevelRecursion
private theorem innerBonds_subset_bondsOver {S D : Finset F.Cell} {z : F.Cell} (hodd : Odd F.blockSide)
    (hD : D = cellBall S z 1) (j : ℕ) :
    innerBonds D j ⊆ bondsOver S (cellBall S z 3) j := by
  classical
  subst hD
  intro b hb
  have h1 : cellBall S z 1 ⊆ S := by
    intro y hy
    unfold cellBall at hy
    exact (Finset.mem_filter.1 hy).1
  unfold bondsOver
  refine Finset.mem_filter.2 ⟨BlockLines.innerBonds_mono h1 j hb, BlockLines.cellBall_mono S z (by norm_num : 1 ≤ 3) ?_⟩
  exact BlockLines.enclosingCell_mem hodd (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
private theorem lpNorm_four_le_localNorm {S D : Finset F.Cell} {z : F.Cell} (hodd : Odd F.blockSide)
    (hD : D = cellBall S z 1) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    finsetLpNorm 4 (innerBonds D 0) (fun b => w 0 b.1 * ‖(U.fine b.1 b.2 : ℍ[ℝ])‖) ≤ localNorm S R U w z := by
  have e : ∀ a : imaginaryQuaternions, ‖(a : ℍ[ℝ])‖ = ‖a‖ := fun _ => rfl
  simp only [e]
  rw [finsetLpNorm_four_eq_sqrt_sqrt]
  unfold localNorm
  refine Real.sqrt_le_sqrt ?_
  have h1 : ∑ b ∈ innerBonds D 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤
      ∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 :=
    Finset.sum_le_sum_of_subset_of_nonneg (innerBonds_subset_bondsOver hodd hD 0) fun _ _ _ => by positivity
  have h2 := Real.sqrt_le_sqrt h1
  have h3 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have h4 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  unfold localNormSq
  exact h2.trans (by linarith)
private theorem lpNorm_two_le_localNorm {S D : Finset F.Cell} {z : F.Cell} (hodd : Odd F.blockSide)
    (hD : D = cellBall S z 1) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) {m : ℕ} (hm : m + 1 < F.top) :
    finsetLpNorm 2 (innerBonds D (m + 1)) (fun b => w (m + 1) b.1 * ‖(U.coarse m b.1 b.2 : ℍ[ℝ])‖) ≤
      localNorm S R U w z := by
  have e : ∀ a : imaginaryQuaternions, ‖(a : ℍ[ℝ])‖ = ‖a‖ := fun _ => rfl
  simp only [e]
  rw [finsetLpNorm_two_eq_sqrt]
  unfold localNorm
  refine Real.sqrt_le_sqrt ?_
  have h1 : ∑ b ∈ innerBonds D (m + 1), (w (m + 1) b.1 * ‖U.coarse m b.1 b.2‖) ^ 2 ≤
      ∑ b ∈ bondsOver S (cellBall S z 3) (m + 1), (w (m + 1) b.1 * ‖U.coarse m b.1 b.2‖) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (innerBonds_subset_bondsOver hodd hD (m + 1)) fun _ _ _ => by positivity
  have hmem : m ∈ Finset.range (F.top - 1) := Finset.mem_range.2 (by omega)
  have h2 : ∑ b ∈ bondsOver S (cellBall S z 3) (m + 1), (w (m + 1) b.1 * ‖U.coarse m b.1 b.2‖) ^ 2 ≤
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.single_le_sum (f := fun j => ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hmem
  have h3 := Real.sqrt_nonneg (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4)
  have h4 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  unfold localNormSq
  linarith
private theorem finsetLpNorm_weight_le {ι : Type} {P : ℕ} (hP : 1 ≤ P) (s : Finset ι) {a b f : ι → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (ha : ∀ i ∈ s, 0 ≤ a i) (hf : ∀ i ∈ s, 0 ≤ f i) (hab : ∀ i ∈ s, a i ≤ K * b i) :
    finsetLpNorm P s (fun i => a i * f i) ≤ K * finsetLpNorm P s (fun i => b i * f i) := by
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hPne : (P : ℝ) ≠ 0 := hPR.ne'
  have hK' : K = (K ^ P) ^ (1 / (P : ℝ)) := by
    rw [← Real.rpow_natCast K P, ← Real.rpow_mul hK, mul_one_div_cancel hPne, Real.rpow_one]
  have hmono : finsetLpNorm P s (fun i => a i * f i) ≤ finsetLpNorm P s (fun i => K * (b i * f i)) := by
    refine finsetLpNorm_mono hP s fun i hi => ?_
    have h1 : a i * f i ≤ K * b i * f i := mul_le_mul_of_nonneg_right (hab i hi) (hf i hi)
    rw [abs_of_nonneg (mul_nonneg (ha i hi) (hf i hi))]
    have : K * b i * f i = K * (b i * f i) := by ring
    rw [this] at h1
    exact h1.trans (le_abs_self _)
  refine hmono.trans (le_of_eq ?_)
  unfold finsetLpNorm
  have hsum : ∑ i ∈ s, |K * (b i * f i)| ^ P = K ^ P * ∑ i ∈ s, |b i * f i| ^ P := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_mul, abs_of_nonneg hK, mul_pow]
  rw [hsum, Real.mul_rpow (by positivity) (Finset.sum_nonneg fun _ _ => by positivity), ← hK']
private theorem classWeight_eq_exp_mul (hodd : Odd F.blockSide) (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0) (j : ℕ)
    (x : F.Site j) :
    classWeight F φ θ p j x =
      Real.exp (φ (enclosingCell x)) * (scaleWeight p θ j x * ((F.blockSide : ℝ) ^ F.top) ^ θ) := by
  have hρ : 0 < scaleRadius F j p x := WeightedAverages.Chains.scaleRadius_pos hodd.pos _ _ _
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  unfold classWeight scaleWeight
  rw [Real.div_rpow hρ.le hN.le, Real.rpow_neg hN.le θ, div_inv_eq_mul]
theorem pairWeightedNorms_of_classWeight (hodd : Odd F.blockSide) {S : Finset F.Cell} {z : F.Cell} (_hz : z ∈ S)
    {φ : F.Cell → ℝ} {δ θ : ℝ} (hδ : 0 ≤ δ) (hφ : ∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y') (p : F.Site 0)
    (R : F.FieldChain) (U A : ChainChart F) :
    PairWeightedNorms (cellBall S z 1) p θ U A
      (Real.exp δ * localNorm S R U (classWeight F φ θ p) z /
        (Real.exp (φ z) * ((F.blockSide : ℝ) ^ F.top) ^ θ))
      (Real.exp δ * (Real.exp (φ z) * ((F.blockSide : ℝ) ^ F.top) ^ θ) *
        localNorm S R A (invertedWeights (classWeight F φ θ p)) z) := by
  classical
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  set Nθ := ((F.blockSide : ℝ) ^ F.top) ^ θ with hNθ
  have hNθ0 : 0 < Nθ := Real.rpow_pos_of_pos hN _
  set lam := Real.exp (φ z) * Nθ with hlam
  set w := classWeight F φ θ p with hw
  have near : ∀ {j : ℕ}, ∀ b ∈ innerBonds (cellBall S z 1) j, |φ (enclosingCell (b.1 : F.Site j)) - φ z| ≤ δ := by
    intro j b hb
    have hc : enclosingCell (b.1 : F.Site j) ∈ cellBall S z 1 :=
      BlockLines.enclosingCell_mem hodd (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
    have hd : cellSupDist z (enclosingCell (b.1 : F.Site j)) ≤ 1 := by
      unfold cellBall at hc
      exact (Finset.mem_filter.1 hc).2
    have h1 := hφ z (enclosingCell (b.1 : F.Site j))
    have h2 : ((cellSupDist z (enclosingCell (b.1 : F.Site j)) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hd
    have h3 : δ * (cellSupDist z (enclosingCell (b.1 : F.Site j)) : ℝ) ≤ δ * 1 := mul_le_mul_of_nonneg_left h2 hδ
    rw [abs_sub_comm]
    linarith
  have up : ∀ {j : ℕ}, ∀ b ∈ innerBonds (cellBall S z 1) j,
      scaleWeight p θ j b.1 ≤ Real.exp δ / lam * w j b.1 := by
    intro j b hb
    have hr := scaleWeight_pos hodd p θ j b.1
    have hn := near b hb
    have hle : φ z - δ ≤ φ (enclosingCell (b.1 : F.Site j)) := by
      have := (abs_le.1 hn).1
      linarith
    have e : Real.exp δ / lam * w j b.1 =
        Real.exp (φ (enclosingCell (b.1 : F.Site j)) - (φ z - δ)) * scaleWeight p θ j b.1 := by
      rw [hw, classWeight_eq_exp_mul hodd, ← hNθ, hlam, Real.exp_sub, Real.exp_sub]
      field_simp
    rw [e]
    have h1 : 1 ≤ Real.exp (φ (enclosingCell (b.1 : F.Site j)) - (φ z - δ)) :=
      Real.one_le_exp (by linarith)
    nlinarith
  have down : ∀ {j : ℕ}, ∀ b ∈ innerBonds (cellBall S z 1) j,
      scaleWeight p (-θ) j b.1 ≤ Real.exp δ * lam * invertedWeights w j b.1 := by
    intro j b hb
    have hr := scaleWeight_pos hodd p θ j b.1
    have hr' := scaleWeight_pos hodd p (-θ) j b.1
    have hinv : scaleWeight p (-θ) j b.1 = (scaleWeight p θ j b.1)⁻¹ := by
      unfold scaleWeight
      rw [neg_neg, Real.rpow_neg (WeightedAverages.Chains.scaleRadius_pos hodd.pos _ _ _).le, inv_inv]
    have hn := near b hb
    have hle : φ (enclosingCell (b.1 : F.Site j)) ≤ φ z + δ := by
      have := (abs_le.1 hn).2
      linarith
    have e : Real.exp δ * lam * invertedWeights w j b.1 =
        Real.exp (φ z + δ - φ (enclosingCell (b.1 : F.Site j))) * scaleWeight p (-θ) j b.1 := by
      rw [hinv]
      unfold invertedWeights
      rw [hw, classWeight_eq_exp_mul hodd, ← hNθ, hlam, Real.exp_sub, Real.exp_add]
      field_simp
    rw [e]
    have h1 : 1 ≤ Real.exp (φ z + δ - φ (enclosingCell (b.1 : F.Site j))) :=
      Real.one_le_exp (by linarith)
    nlinarith
  have hK1 : 0 ≤ Real.exp δ / lam := by positivity
  have hK2 : 0 ≤ Real.exp δ * lam := by positivity
  have e1 : Real.exp δ * localNorm S R U w z / lam = Real.exp δ / lam * localNorm S R U w z := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (lpNorm_four_le_localNorm hodd rfl R U w) hK1)
    exact finsetLpNorm_weight_le (by norm_num) _ hK1 (fun b _ => (scaleWeight_pos hodd p θ 0 b.1).le)
      (fun _ _ => norm_nonneg _) (fun b hb => up b hb)
  · intro m hm
    rw [e1]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (lpNorm_two_le_localNorm hodd rfl R U w hm) hK1)
    exact finsetLpNorm_weight_le (by norm_num) _ hK1 (fun b _ => (scaleWeight_pos hodd p θ (m + 1) b.1).le)
      (fun _ _ => norm_nonneg _) (fun b hb => up b hb)
  · refine le_trans ?_ (mul_le_mul_of_nonneg_left (lpNorm_four_le_localNorm hodd rfl R A (invertedWeights w)) hK2)
    exact finsetLpNorm_weight_le (by norm_num) _ hK2 (fun b _ => (scaleWeight_pos hodd p (-θ) 0 b.1).le)
      (fun _ _ => norm_nonneg _) (fun b hb => down b hb)
  · intro m hm
    refine le_trans ?_
      (mul_le_mul_of_nonneg_left (lpNorm_two_le_localNorm hodd rfl R A (invertedWeights w) hm) hK2)
    exact finsetLpNorm_weight_le (by norm_num) _ hK2 (fun b _ => (scaleWeight_pos hodd p (-θ) (m + 1) b.1).le)
      (fun _ _ => norm_nonneg _) (fun b hb => down b hb)
end YangMills.Construction.SmallMultiples
end
