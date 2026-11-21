import YangMills.Construction.LawByMomentsOfTheFlow.ColdLawOfAGoodStateProof
import YangMills.Construction.LawByMomentsOfTheFlow.ContractionAtTheWeightsOfThePointProof
import YangMills.Construction.LawByMomentsOfTheFlow.HessianOverTheFieldOfAFormProof
import YangMills.Construction.LawByMomentsOfTheFlow.PotentialOfAGoodStateNearItsHessian
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps TorusFrame TopLevelSites TorusBalls StepCosts RenormalizationStepParameters BlockAverages ColdStepAtMirrorFrames
  ResponseInTheExpansion WeightedResponses LinearResponse MomentMethod
namespace GradientBoundSteps
private theorem bondFrameCoord_norm_le (hMF : ReflectedFieldSmallCurvature) {a : ℝ} {L : ℕ} {c : ColdChainParameters} (hL : Odd L)
    (hc : c.Admissible a L) (hρ : c.ρA ≤ 1) {G : BlockFrame} (hG : G.blockSide = L) (m : ℕ) (hm : 16 ≤ m)
    (hside : ∀ i, 4 * m + 5 < G.extent i) (V : G.GaugeField G.top) (s : ℝ)
    (hs : 0 < s) (hsA : s ≤ c.σA) (hV : IsSmallCurvature s V) (b : G.Site G.depth × Fin 4) :
    ‖bondFrameCoord a c.ρA m b V‖ ≤ c.N 0 * s := by apply _root_.YangMills.SharedProofs.p62111 <;> assumption
private theorem one_add_mul_exp_le {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    (1 + t) * Real.exp (-(δ / 2 * t)) ≤ (1 + 4 / δ) * Real.exp (-(δ / 4 * t)) := by apply _root_.YangMills.SharedProofs.p70520 <;> assumption
section Algebra
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem sq_weighted_sum_le (κ a : ι → ℝ) (hκ : ∀ b, 0 ≤ κ b) {Sκ : ℝ} (hS : ∑ b, κ b ≤ Sκ) :
    (∑ b, κ b * a b) ^ 2 ≤ Sκ * ∑ b, κ b * a b ^ 2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι) (r := fun b => κ b * a b) (f := κ)
    (g := fun b => κ b * a b ^ 2) (fun b _ => hκ b) (fun b _ => mul_nonneg (hκ b) (sq_nonneg _)) (fun b _ => le_of_eq (by ring))
  refine h.trans (mul_le_mul_of_nonneg_right hS (Finset.sum_nonneg fun b _ => mul_nonneg (hκ b) (sq_nonneg _)))
private theorem abs_apply_le_norm (z : BondVector) (e : Fin 3) : |z e| ≤ ‖z‖ := by
  have := PiLp.norm_apply_le z e
  simpa using this
private theorem inverse_drift_bound (Hf Hi : Matrix ι ι ℝ) (H : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (hHi : Hi * Hf = 1) {x K₀ Sκ : ℝ}
    (hx : 0 < x) (hK₀ : 0 ≤ K₀) (k : BondField ι) (g : Fin 3 × ι → ℝ) (κ D : ι → ι → ℝ)
    (hκ0 : ∀ b b', 0 ≤ κ b b') (hκS : ∀ b, ∑ b', κ b b' ≤ Sκ)
    (hg : ∀ j : Fin 3 × ι, |g j - x * ∑ r : ι × Fin 3, H (j.2, j.1) r * k r.1 r.2| ≤
      K₀ * (1 + x * (∑ b, κ j.2 b * ‖k b‖) ^ 2))
    (hD : ∀ (b : ι) (e : Fin 3) (r : ι × Fin 3), |H (b, e) r - (if r.2 = e then Hf b r.1 else 0)| ≤ D b r.1)
    (j : Fin 3 × ι) :
    |(∑ i : Fin 3 × ι, (if j.1 = i.1 then x⁻¹ * Hi j.2 i.2 else 0) * g i) - k j.2 j.1| ≤
      x⁻¹ * K₀ * ∑ b, |Hi j.2 b| + K₀ * Sκ * ∑ b', (∑ b, |Hi j.2 b| * κ b b') * ‖k b'‖ ^ 2 +
        3 * ∑ b', (∑ b, |Hi j.2 b| * D b b') * ‖k b'‖ := by
  classical
  obtain ⟨e, p⟩ := j
  simp only
  have s1 : ∑ i : Fin 3 × ι, (if e = i.1 then x⁻¹ * Hi p i.2 else 0) * g i = x⁻¹ * ∑ b, Hi p b * g (e, b) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single e]
    · simp only [if_true, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    · intro e' _ he
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [Ne.symm he]
    · simp
  have s2 : k p e = ∑ b, Hi p b * ∑ b', Hf b b' * k b' e := by
    have h1 := congrFun (Matrix.mulVec_mulVec (fun b' => k b' e) Hi Hf) p
    rw [hHi, Matrix.one_mulVec] at h1
    simpa [Matrix.mulVec, dotProduct] using h1.symm
  set T : ι → ℝ := fun b => ∑ r : ι × Fin 3, (H (b, e) r - (if r.2 = e then Hf b r.1 else 0)) * k r.1 r.2 with hT
  have s3 : ∀ b, ∑ r : ι × Fin 3, H (b, e) r * k r.1 r.2 = T b + ∑ b', Hf b b' * k b' e := by
    intro b
    have h1 : ∑ r : ι × Fin 3, (if r.2 = e then Hf b r.1 else 0) * k r.1 r.2 = ∑ b', Hf b b' * k b' e := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [Finset.sum_eq_single e]
      · simp
      · intro e' _ he
        simp [he]
      · simp
    rw [← h1, hT]
    simp only
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  set Er : ι → ℝ := fun b => g (e, b) - x * ∑ r : ι × Fin 3, H (b, e) r * k r.1 r.2 with hEr
  have s4 : (∑ i : Fin 3 × ι, (if e = i.1 then x⁻¹ * Hi p i.2 else 0) * g i) - k p e =
      ∑ b, Hi p b * (x⁻¹ * Er b + T b) := by
    rw [s1, s2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 : g (e, b) = Er b + x * (T b + ∑ b', Hf b b' * k b' e) := by
      rw [← s3 b, hEr]
      ring
    rw [h1]
    field_simp
    ring
  rw [s4]
  have hEb : ∀ b, |Er b| ≤ K₀ * (1 + x * (Sκ * ∑ b', κ b b' * ‖k b'‖ ^ 2)) := by
    intro b
    refine (hg (e, b)).trans ?_
    have h1 := sq_weighted_sum_le (κ b) (fun b' => ‖k b'‖) (hκ0 b) (hκS b)
    gcongr
  have hD0 : ∀ b b', 0 ≤ D b b' := fun b b' => (abs_nonneg _).trans (hD b e (b', e))
  have hTb : ∀ b, |T b| ≤ 3 * ∑ b', D b b' * ‖k b'‖ := by
    intro b
    calc |T b| ≤ ∑ r : ι × Fin 3, |(H (b, e) r - (if r.2 = e then Hf b r.1 else 0)) * k r.1 r.2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r : ι × Fin 3, D b r.1 * ‖k r.1‖ := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hD b e r) (abs_apply_le_norm _ _) (abs_nonneg _) (hD0 _ _)
      _ = 3 * ∑ b', D b b' * ‖k b'‖ := by
          rw [Fintype.sum_prod_type, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b' _ => ?_
          simp
  have hx1 : 0 ≤ x⁻¹ := by positivity
  have hterm : ∀ b, |Hi p b * (x⁻¹ * Er b + T b)| ≤
      x⁻¹ * K₀ * |Hi p b| + K₀ * Sκ * (|Hi p b| * ∑ b', κ b b' * ‖k b'‖ ^ 2) +
        3 * (|Hi p b| * ∑ b', D b b' * ‖k b'‖) := by
    intro b
    rw [abs_mul]
    have h1 : |x⁻¹ * Er b + T b| ≤ x⁻¹ * (K₀ * (1 + x * (Sκ * ∑ b', κ b b' * ‖k b'‖ ^ 2))) + 3 * ∑ b', D b b' * ‖k b'‖ := by
      refine (abs_add_le _ _).trans (add_le_add ?_ (hTb b))
      rw [abs_mul, abs_of_nonneg hx1]
      exact mul_le_mul_of_nonneg_left (hEb b) hx1
    have h2 : x⁻¹ * (K₀ * (1 + x * (Sκ * ∑ b', κ b b' * ‖k b'‖ ^ 2))) =
        x⁻¹ * K₀ + K₀ * Sκ * ∑ b', κ b b' * ‖k b'‖ ^ 2 := by
      field_simp
    rw [h2] at h1
    calc |Hi p b| * |x⁻¹ * Er b + T b| ≤ |Hi p b| * (x⁻¹ * K₀ + K₀ * Sκ * ∑ b', κ b b' * ‖k b'‖ ^ 2 + 3 * ∑ b', D b b' * ‖k b'‖) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = _ := by ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun b _ => hterm b).trans (le_of_eq ?_))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 2
  · congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun b _ => by ring
  · simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun b _ => by ring
end Algebra
section Sites
variable {n : ℕ}
private theorem supDist_parentBlock_le [NeZero n] {L : ℕ} [NeZero L] (hL : 2 ≤ L) (p q : TorusSite (n * L)) :
    TorusFields.supDist (parentBlock L p) (parentBlock L q) ≤ TorusFields.supDist p q := by apply _root_.YangMills.SharedProofs.p12740 <;> assumption
end Sites
private theorem log_le_two_mul_sqrt (x : ℝ) (hx : 0 < x) : Real.log x ≤ 2 * x ^ ((1 : ℝ) / 2) := by apply _root_.YangMills.SharedProofs.p12056 <;> assumption
section Numbers
private theorem half_le_and_le_two_mul {xs x cn : ℝ} (hx2 : 2 ≤ xs) (hcn : 0 ≤ cn) (hxn : 16 * cn ^ 2 ≤ xs)
    (hnear : |x - xs| ≤ cn * Real.log xs) : xs / 2 ≤ x ∧ x ≤ 2 * xs := by
  have hx0 : 0 < xs := by linarith
  have hh0 : 0 < xs ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
  have hhh : xs ^ ((1 : ℝ) / 2) * xs ^ ((1 : ℝ) / 2) = xs := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hfloor : cn * Real.log xs ≤ xs / 2 := by
    have h1 := log_le_two_mul_sqrt xs hx0
    have h2 : 4 * cn ≤ xs ^ ((1 : ℝ) / 2) := by
      by_contra hc'
      push Not at hc'
      nlinarith
    nlinarith
  have h3 := abs_le.1 (le_trans hnear hfloor)
  exact ⟨by linarith [h3.1], by linarith [h3.2]⟩
private theorem rangeSq_mul_curvature_lt {x σ : ℝ} (hσ : 0 < σ) (hx1 : 1 ≤ x) (hX : (128 / σ + 1) ^ 5 ≤ x) {r : ℕ}
    (hr : (r : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 100)) : 32 * ((r ^ 2 : ℕ) : ℝ) * x ^ (-(1 / 4) : ℝ) < σ := by
  have hx0 : 0 < x := by linarith
  set a := x ^ ((1 : ℝ) / 100) with ha
  have ha1 : 1 ≤ a := Real.one_le_rpow hx1 (by norm_num)
  have e25 : a ^ 25 = x ^ ((1 : ℝ) / 4) := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have e20 : a ^ 20 = x ^ ((1 : ℝ) / 5) := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hneg : x ^ (-(1 / 4) : ℝ) = (a ^ 25)⁻¹ := by
    rw [e25, Real.rpow_neg hx0.le]
  have h5 : 128 / σ + 1 ≤ a ^ 20 := by
    have h1 : 0 ≤ 128 / σ + 1 := by positivity
    have h2 := Real.rpow_le_rpow (by positivity) hX (by norm_num : (0 : ℝ) ≤ 1 / 5)
    rw [← Real.rpow_natCast, ← Real.rpow_mul h1] at h2
    rw [e20]
    simpa using h2
  have h6 : σ * (128 / σ + 1) = 128 + σ := by
    field_simp
  have h7 : a ^ 20 ≤ a ^ 23 := pow_le_pow_right₀ ha1 (by norm_num)
  have h8 : 128 + σ ≤ σ * a ^ 23 := by
    rw [← h6]
    exact mul_le_mul_of_nonneg_left (h5.trans h7) hσ.le
  have hr2 : ((r ^ 2 : ℕ) : ℝ) ≤ 4 * a ^ 2 := by
    push_cast
    nlinarith
  have hp : 0 < a ^ 25 := by positivity
  rw [hneg, ← div_eq_mul_inv, div_lt_iff₀ hp]
  have ha2 : 0 < a ^ 2 := by positivity
  have h9 : a ^ 2 * (128 + σ) ≤ a ^ 2 * (σ * a ^ 23) := mul_le_mul_of_nonneg_left h8 ha2.le
  nlinarith
set_option exponentiation.threshold 2000 in
private theorem two_le_of_two_pow_le {xs : ℝ} (hxs : (2 : ℝ) ^ 1601 ≤ xs) : 2 ≤ xs := by
  have h1 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ 1601 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  rw [pow_one] at h1
  exact h1.trans hxs
set_option exponentiation.threshold 2000 in
private theorem clusterRange_div_bounds {xs x : ℝ} {N n L : ℕ} (hxs : (2 : ℝ) ^ 1601 ≤ xs) (hlo : xs / 2 ≤ x) (hhi : x ≤ 2 * xs)
    (hN : (2 : ℝ) ^ (-(N : ℝ)) ≤ xs ^ (-(1 / 2) : ℝ)) (hL : 2 ≤ L) (hn : L ^ N ≤ n) :
    16 ≤ clusterRange x / 2 ^ 11 ∧ 4 * (clusterRange x / 2 ^ 11) + 5 < n := by
  have hxs0 : 0 < xs := lt_of_lt_of_le (by positivity) hxs
  have hx1600 : (2 : ℝ) ^ 1600 ≤ x := by
    have : (2 : ℝ) ^ 1601 = 2 * 2 ^ 1600 := pow_succ' 2 1600
    linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx1600
  have ha16 : (2 : ℝ) ^ 16 ≤ x ^ ((1 : ℝ) / 100) := by
    have h1 : ((2 : ℝ) ^ 1600) ^ ((1 : ℝ) / 100) ≤ x ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (by positivity) hx1600 (by norm_num)
    have h2 : ((2 : ℝ) ^ 1600) ^ ((1 : ℝ) / 100) = (2 : ℝ) ^ 16 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
      norm_num
    rwa [h2] at h1
  have hR : 2 ^ 16 ≤ clusterRange x := by
    have h2 : ((2 ^ 16 : ℕ) : ℝ) ≤ x ^ ((1 : ℝ) / 100) := by
      have e : ((2 ^ 16 : ℕ) : ℝ) = (2 : ℝ) ^ 16 := by norm_num
      rw [e]
      exact ha16
    exact Nat.cast_le.1 (h2.trans (Nat.le_ceil _))
  refine ⟨by omega, ?_⟩
  have h4 : 4 * (clusterRange x / 2 ^ 11) + 5 ≤ clusterRange x := by omega
  refine lt_of_le_of_lt h4 ?_
  have hRle : (clusterRange x : ℝ) < x ^ ((1 : ℝ) / 100) + 1 := Nat.ceil_lt_add_one (by positivity)
  set y := xs ^ ((1 : ℝ) / 50) with hy
  have hy2 : 2 ≤ y := by
    have h1 : ((2 : ℝ) ^ 1601) ^ ((1 : ℝ) / 50) ≤ y := Real.rpow_le_rpow (by positivity) hxs (by norm_num)
    have h2 : (2 : ℝ) ≤ ((2 : ℝ) ^ 1601) ^ ((1 : ℝ) / 50) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ (((1601 : ℕ) : ℝ) * ((1 : ℝ) / 50)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      simpa using this
    linarith
  have hax : x ^ ((1 : ℝ) / 100) ≤ y := by
    have h1 : x ≤ xs ^ 2 := by nlinarith
    have h2 := Real.rpow_le_rpow hx0.le h1 (by norm_num : (0 : ℝ) ≤ 1 / 100)
    have h3 : (xs ^ 2) ^ ((1 : ℝ) / 100) = y := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hxs0.le]
      norm_num
    rwa [h3] at h2
  have h25 : xs ^ ((1 : ℝ) / 2) = y ^ 25 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hxs0.le]
    norm_num
  have hbig : y + 1 < y ^ 25 := by
    have h1 : y ^ 2 ≤ y ^ 25 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  have h2N : xs ^ ((1 : ℝ) / 2) ≤ (2 : ℝ) ^ N := by
    have e1 : (2 : ℝ) ^ (-(N : ℝ)) = ((2 : ℝ) ^ N)⁻¹ := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    have e2 : xs ^ (-(1 / 2) : ℝ) = (xs ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [Real.rpow_neg hxs0.le]
    rw [e1, e2] at hN
    exact (inv_le_inv₀ (by positivity) (by positivity)).1 hN
  have hLN : (2 : ℝ) ^ N ≤ (n : ℝ) := by
    have h1 : 2 ^ N ≤ L ^ N := Nat.pow_le_pow_left hL N
    exact_mod_cast h1.trans hn
  have : (clusterRange x : ℝ) < n := by
    have : (clusterRange x : ℝ) < y ^ 25 := by linarith
    linarith [h25]
  exact_mod_cast this
end Numbers
section Cut
variable {n : ℕ} [NeZero n]
private theorem abs_cutoffProfile_le_one (o : TorusSite n) (m : ℕ) (z : TorusSite n) : |cutoffProfile o m z| ≤ 1 := by
  unfold cutoffProfile
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (min_le_left _ _)
private theorem cutoffProfile_eq_zero (o : TorusSite n) {m : ℕ} (hm : 2 ≤ m) (z : TorusSite n)
    (h : 2 * (m : ℝ) - 1 ≤ (TorusFields.supDist z o : ℝ)) : cutoffProfile o m z = 0 := by
  unfold cutoffProfile
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have h1 : (2 * (m : ℝ) - 1 - (TorusFields.supDist z o : ℝ)) / ((m : ℝ) - 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hm1.le
  exact max_eq_left ((min_le_right _ _).trans h1)
private theorem norm_cutoffCoords_le (ℓ : TorusLumps.StepParameters) (W : TorusField n) (O : TorusSite n) {m : ℕ} (hm : 2 ≤ m)
    {v : ℝ} (hv : 0 ≤ v)
    (hax : ∀ c : TorusBond n, c.1 ∈ supBall O (2 * (m : ℝ)) → c.1 + TorusFields.unitStep n c.2 ∈ supBall O (2 * (m : ℝ)) →
      ‖(axialCoords ℓ W O c : Quaternion ℝ)‖ ≤ 4 * ((TorusFields.supDist c.1 O : ℝ) + 1) * v) (c : TorusBond n) :
    ‖cutoffCoords ℓ W O m c‖ ≤ 4 * ((TorusFields.supDist c.1 O : ℝ) + 1) * v ∧ ‖cutoffCoords ℓ W O m c‖ ≤ 8 * (m : ℝ) * v := by
  by_cases h : 2 * (m : ℝ) - 1 ≤ (TorusFields.supDist c.1 O : ℝ)
  · have h0 : cutoffCoords ℓ W O m c = 0 := by
      unfold cutoffCoords
      rw [cutoffProfile_eq_zero O hm c.1 h, zero_smul]
    rw [h0, norm_zero]
    exact ⟨by positivity, by positivity⟩
  · push Not at h
    have hnat : TorusFields.supDist c.1 O + 1 ≤ 2 * m - 1 := by
      have h1 : ((TorusFields.supDist c.1 O : ℕ) : ℝ) < ((2 * m - 1 : ℕ) : ℝ) := by
        have : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        rw [this]
        exact h
      have h2 : TorusFields.supDist c.1 O < 2 * m - 1 := by exact_mod_cast h1
      omega
    have hnatR : (TorusFields.supDist c.1 O : ℝ) + 1 ≤ 2 * (m : ℝ) := by
      have : ((TorusFields.supDist c.1 O + 1 : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
        exact_mod_cast (by omega : TorusFields.supDist c.1 O + 1 ≤ 2 * m)
      push_cast at this
      exact this
    have hb1 : c.1 ∈ supBall O (2 * (m : ℝ)) := by
      unfold supBall
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      linarith
    have hb2 : c.1 + TorusFields.unitStep n c.2 ∈ supBall O (2 * (m : ℝ)) := by
      unfold supBall
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      have t1 := supDist_triangle (c.1 + TorusFields.unitStep n c.2) c.1 O
      have t2 := supDist_add_unitStep_le c.1 c.2
      rw [supDist_comm] at t2
      have : ((TorusFields.supDist (c.1 + TorusFields.unitStep n c.2) O : ℕ) : ℝ) ≤ ((TorusFields.supDist c.1 O + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : TorusFields.supDist (c.1 + TorusFields.unitStep n c.2) O ≤ TorusFields.supDist c.1 O + 1)
      push_cast at this
      linarith
    have hA := hax c hb1 hb2
    have hcn : ‖cutoffCoords ℓ W O m c‖ ≤ ‖(axialCoords ℓ W O c : Quaternion ℝ)‖ := by
      unfold cutoffCoords
      have e : ‖(cutoffProfile O m c.1 • axialCoords ℓ W O c : imaginaryQuaternions)‖ =
          |cutoffProfile O m c.1| * ‖(axialCoords ℓ W O c : Quaternion ℝ)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        rfl
      rw [e]
      have h1 := abs_cutoffProfile_le_one O m c.1
      have h2 := norm_nonneg (axialCoords ℓ W O c : Quaternion ℝ)
      nlinarith
    refine ⟨hcn.trans hA, (hcn.trans hA).trans ?_⟩
    have : 4 * ((TorusFields.supDist c.1 O : ℝ) + 1) * v ≤ 4 * (2 * (m : ℝ)) * v := by gcongr
    linarith
end Cut
section Chart
variable {L u n : ℕ} [NeZero L] [NeZero n]
private theorem enclosingCell_eq_parentBlock (b : ChartBondIndex L u n) :
    enclosingCell b.1.1 = torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top (parentBlock L (toTorusSite (n * L) b.1.1)) := by
  have hp : ∀ i, (torusFrame L u n).period (torusFrame L u n).depth i = n * L := fun i => by
    simp [BlockFrame.period, torusFrame, BlockFrame.top]
  have e : torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth (toTorusSite (n * L) b.1.1) = b.1.1 :=
    torusSiteInFrame_toTorusSite hp b.1.1
  have : NeZero (n * (torusFrame L u n).blockSide) := inferInstanceAs (NeZero (n * L))
  have h := enclosingCell_torusSiteInFrame (F := torusFrame L u n) (n := n) (fun _ => rfl) (toTorusSite (n * L) b.1.1)
  exact (congrArg enclosingCell e).symm.trans h
private theorem chordBondDist_eq (b b' : ChartBondIndex L u n) :
    chordBondDist (torusFrame L u n) b b' =
      (TorusFields.supDist (parentBlock L (toTorusSite (n * L) b.1.1)) (parentBlock L (toTorusSite (n * L) b'.1.1)) : ℝ) := by
  unfold chordBondDist
  rw [enclosingCell_eq_parentBlock, enclosingCell_eq_parentBlock, cellSupDist_torusFrame, siteOfCell_torusSiteInFrame,
    siteOfCell_torusSiteInFrame]
private theorem chordBondDist_le (hL : 2 ≤ L) (b b' : ChartBondIndex L u n) :
    chordBondDist (torusFrame L u n) b b' ≤ (TorusFields.supDist (toTorusSite (n * L) b.1.1) (toTorusSite (n * L) b'.1.1) : ℝ) := by
  rw [chordBondDist_eq]
  exact_mod_cast supDist_parentBlock_le hL _ _
end Chart
section Weights
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem sum_abs_cov_row (Hi : Matrix ι ι ℝ) (x : ℝ) (hx : 0 < x) (p : ι) (e : Fin 3) :
    ∑ i : Fin 3 × ι, |(if e = i.1 then x⁻¹ * Hi p i.2 else 0)| = x⁻¹ * ∑ b, |Hi p b| := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single e]
  · simp only [if_true, abs_mul, abs_of_pos (inv_pos.2 hx), Finset.mul_sum]
  · intro e' _ he
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Ne.symm he]
  · simp
private theorem weighted_drift_bound (Hf Hi : Matrix ι ι ℝ) (H : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (hHi : Hi * Hf = 1)
    {x xs K₀ Sκ Ah P₁ v fj Z : ℝ} (p : ι) (hx : 0 < x) (hxs : 0 < xs) (hlow : xs / 2 ≤ x) (hK₀ : 0 ≤ K₀) (hSκ : 0 ≤ Sκ)
    (hP₁ : 0 ≤ P₁) (hv : 0 ≤ v) (hfj : 0 ≤ fj) (dj : ι → ℝ) (hdj : ∀ b, 0 ≤ dj b) (κ E₂ : ι → ι → ℝ)
    (hκ0 : ∀ b b', 0 ≤ κ b b') (hκS : ∀ b, ∑ b', κ b b' ≤ Sκ) (hE0 : ∀ b b', 0 ≤ E₂ b b')
    (hAh : ∑ b, |Hi p b| * (1 + dj b) ≤ Ah) (hZ1 : 2 * K₀ * Ah ≤ Z) (hZ2 : K₀ * Sκ ≤ Z) (hZ3 : 6 * P₁ ≤ Z)
    (k : BondField ι) (g : Fin 3 × ι → ℝ)
    (hg : ∀ j : Fin 3 × ι, |g j - x * ∑ r : ι × Fin 3, H (j.2, j.1) r * k r.1 r.2| ≤
      K₀ * (1 + x * (∑ b, κ j.2 b * ‖k b‖) ^ 2))
    (hD : ∀ (b : ι) (e : Fin 3) (r : ι × Fin 3), |H (b, e) r - (if r.2 = e then Hf b r.1 else 0)| ≤
      2 * P₁ * (1 + fj) * (1 + dj b) * E₂ b r.1 * v) (e : Fin 3) :
    |(∑ i : Fin 3 × ι, (if e = i.1 then x⁻¹ * Hi p i.2 else 0) * g i) - k p e| ≤
      Z * xs⁻¹ * (1 + xs * ∑ b', (∑ b, |Hi p b| * (κ b b' + E₂ b b' * (1 + dj b))) * (‖k b'‖ ^ 2 + (1 + fj) * v * ‖k b'‖)) := by
  have h0 := inverse_drift_bound Hf Hi H hHi hx hK₀ k g κ (fun b b' => 2 * P₁ * (1 + fj) * (1 + dj b) * E₂ b b' * v)
    hκ0 hκS hg hD (e, p)
  simp only at h0
  refine h0.trans ?_
  set w : ι → ℝ := fun b' => ∑ b, |Hi p b| * (κ b b' + E₂ b b' * (1 + dj b)) with hw
  have hd1 : ∀ b, 0 ≤ 1 + dj b := fun b => by have := hdj b; linarith
  have hw0 : ∀ b', 0 ≤ w b' := fun b' => Finset.sum_nonneg fun b _ =>
    mul_nonneg (abs_nonneg _) (add_nonneg (hκ0 _ _) (mul_nonneg (hE0 _ _) (hd1 _)))
  have hxi : x⁻¹ ≤ 2 * xs⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, div_le_div_iff₀ hx hxs]
    linarith
  have hH1 : ∑ b, |Hi p b| ≤ Ah := by
    refine le_trans (Finset.sum_le_sum fun b _ => ?_) hAh
    have := abs_nonneg (Hi p b)
    have := hdj b
    nlinarith
  have t1 : x⁻¹ * K₀ * ∑ b, |Hi p b| ≤ Z * xs⁻¹ := by
    have h1 : x⁻¹ * K₀ * ∑ b, |Hi p b| ≤ (2 * xs⁻¹) * K₀ * Ah := by
      have h2 : 0 ≤ ∑ b, |Hi p b| := Finset.sum_nonneg fun b _ => abs_nonneg _
      have h3 : 0 ≤ x⁻¹ := by positivity
      gcongr
    have h4 : 0 ≤ xs⁻¹ := by positivity
    nlinarith
  set A1 : ℝ := ∑ b', w b' * ‖k b'‖ ^ 2 with hA1
  set A2 : ℝ := ∑ b', w b' * ‖k b'‖ with hA2
  have hA10 : 0 ≤ A1 := Finset.sum_nonneg fun b _ => mul_nonneg (hw0 b) (by positivity)
  have hA20 : 0 ≤ A2 := Finset.sum_nonneg fun b _ => mul_nonneg (hw0 b) (norm_nonneg _)
  have t2 : K₀ * Sκ * ∑ b', (∑ b, |Hi p b| * κ b b') * ‖k b'‖ ^ 2 ≤ Z * A1 := by
    have h1 : ∑ b', (∑ b, |Hi p b| * κ b b') * ‖k b'‖ ^ 2 ≤ A1 := by
      refine Finset.sum_le_sum fun b' _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := mul_nonneg (hE0 b b') (hd1 b)
      linarith
    have h2 : 0 ≤ K₀ * Sκ := by positivity
    calc _ ≤ K₀ * Sκ * A1 := mul_le_mul_of_nonneg_left h1 h2
      _ ≤ Z * A1 := mul_le_mul_of_nonneg_right hZ2 hA10
  have t3 : 3 * ∑ b', (∑ b, |Hi p b| * (2 * P₁ * (1 + fj) * (1 + dj b) * E₂ b b' * v)) * ‖k b'‖ ≤ Z * ((1 + fj) * v * A2) := by
    have h1 : ∑ b', (∑ b, |Hi p b| * (2 * P₁ * (1 + fj) * (1 + dj b) * E₂ b b' * v)) * ‖k b'‖ ≤
        2 * P₁ * ((1 + fj) * v * A2) := by
      rw [hA2, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun b' _ => ?_
      have h2 : ∑ b, |Hi p b| * (2 * P₁ * (1 + fj) * (1 + dj b) * E₂ b b' * v) ≤ 2 * P₁ * ((1 + fj) * v * w b') := by
        rw [hw]
        simp only
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun b _ => ?_
        have h3 : 0 ≤ 2 * P₁ * (1 + fj) * v := by positivity
        have h4 := abs_nonneg (Hi p b)
        have h5 := hκ0 b b'
        have h6 := mul_nonneg h3 (mul_nonneg h4 h5)
        nlinarith
      have h7 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (k b'))
      linarith
    have h2 : 0 ≤ (1 + fj) * v * A2 := by positivity
    nlinarith
  have hfin : Z * xs⁻¹ * (1 + xs * ∑ b', w b' * (‖k b'‖ ^ 2 + (1 + fj) * v * ‖k b'‖)) =
      Z * xs⁻¹ + Z * A1 + Z * ((1 + fj) * v * A2) := by
    have e1 : ∑ b', w b' * (‖k b'‖ ^ 2 + (1 + fj) * v * ‖k b'‖) = A1 + (1 + fj) * v * A2 := by
      rw [hA1, hA2, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e1]
    field_simp
    ring
  rw [hfin]
  linarith
end Weights
section Frames
private theorem bondFrameCoord_norm_le_of_forall (hMF : ReflectedFieldSmallCurvature) {a : ℝ} {L : ℕ} {c : ColdChainParameters}
    (hL : Odd L) (hc : c.Admissible a L) (hρ : c.ρA ≤ 1) {G : BlockFrame} (hG : G.blockSide = L) (m : ℕ) (hm : 16 ≤ m)
    (hside : ∀ i, 4 * m + 5 < G.extent i) (V : G.GaugeField G.top)
    {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (hsA : s₀ < c.σA) (hV : ∀ s, s₀ < s → IsSmallCurvature s V) (b : G.Site G.depth × Fin 4) :
    ‖bondFrameCoord a c.ρA m b V‖ ≤ c.N 0 * s₀ := by
  have hN : 0 < c.N 0 := hc.positivity.2.2.2.2.2.1 0
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set ε₁ := min (ε / c.N 0) (c.σA - s₀) with hε₁
  have h1 : 0 < ε₁ := lt_min (by positivity) (by linarith)
  have h2 : ε₁ ≤ ε / c.N 0 := min_le_left _ _
  have h3 : ε₁ ≤ c.σA - s₀ := min_le_right _ _
  have h4 := bondFrameCoord_norm_le hMF hL hc hρ hG m hm hside V (s₀ + ε₁) (by linarith) (by linarith) (hV _ (by linarith)) b
  have h5 : c.N 0 * ε₁ ≤ ε := by
    have := mul_le_mul_of_nonneg_left h2 hN.le
    rwa [mul_div_cancel₀ _ hN.ne'] at this
  nlinarith
end Frames
section Origin
variable {n : ℕ} [NeZero n] {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem supDist_parentBlock_originSite_le_one (hL : 2 ≤ Λ.stepParams.side) (u : ℕ) :
    TorusFields.supDist (parentBlock Λ.stepParams.side (S.originSite u (n * Λ.stepParams.side))) (S.originSite (u + 1) n) ≤ 1 := by apply _root_.YangMills.SharedProofs.p66617 <;> assumption
end Origin
section Parameters
private theorem forAllParameters_mono {Q Q' : MomentParameters → Prop} (h : ForAllParameters Q) (f : ∀ Λ, Q Λ → Q' Λ) :
    ForAllParameters Q' := by apply _root_.YangMills.SharedProofs.p9549 <;> assumption
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁) (h₂ : ForAllParameters Q₂) :
    ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_of_holdsOnAllParameters {P : ParameterAssignment → ℝ → Prop} (h : HoldsOnParameterFamilies P) :
    ForAllParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p27928 <;> assumption
private theorem forAllParameters_admissible : ForAllParameters fun Λ => Λ.table.Admissible := by apply _root_.YangMills.SharedProofs.p23915 <;> assumption
private theorem forAllParameters_coldStep : ForAllParameters fun Λ => Λ.table.ColdStepHolds := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ _ hS _ _ _ _ _
  exact ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => hS⟩
end Parameters
end GradientBoundSteps
open GradientBoundSteps in
set_option exponentiation.threshold 2000 in
set_option maxHeartbeats 3000000 in
theorem potentialGradientBoundsStatement_holds (hNH : goodStatePotentialNearHessianStatement)
    (hHF : hessianOverExpFieldStatement) (hD : decaySumOnTorusStatement) (hMF : ReflectedFieldSmallCurvature)
    (hFl : gaussianChainFluctuationsStatement)
    (hHess : stepHessianPosDefStatement) (hCutS : goodConfigCutoffStatement)
    (hWin : scaleWindowStatement) : potentialGradientBoundsStatement := by
  unfold goodStatePotentialNearHessianStatement ForAllPoints at hNH
  unfold gaussianChainFluctuationsStatement ForAllPoints at hFl
  unfold goodConfigCutoffStatement ForAllPoints at hCutS
  unfold scaleWindowStatement ForAllPoints at hWin
  unfold potentialGradientBoundsStatement ForAllPoints
  refine forAllParameters_mono (forAllParameters_and forAllParameters_admissible (forAllParameters_and forAllParameters_coldStep
    (forAllParameters_and (forAllParameters_of_holdsOnAllParameters hHess) (forAllParameters_and hNH
    (forAllParameters_and hFl (forAllParameters_and hCutS hWin)))))) ?_
  rintro Λ ⟨hDr, ⟨c, nss, hties, -⟩, hH, ⟨Cn, _, Xn, _, hyn, hnh⟩, ⟨_, cf, _, hcf, _, hfl⟩, ⟨_, _, Xc, _, hyc, hcut⟩,
    ⟨Cw, _, Xw, _, _, hwin⟩⟩
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, hc⟩ := hties
  have ha : 1 ≤ Λ.stepParams.coupling := hDr.a_ge
  have hL : Odd Λ.stepParams.side := hDr.L_odd
  have hL40 : 2 ^ 40 ≤ Λ.stepParams.side := hDr.L_ge
  have hL2 : 2 ≤ Λ.stepParams.side := by omega
  have hc' : c.Admissible Λ.stepParams.coupling Λ.stepParams.side := hc
  have hσ : 0 < Λ.table.threshold := hDr.σ_pos
  have hlam : 0 < Λ.table.lam := hDr.chain.2.2.1
  have hLp : (1 : ℝ) ≤ Λ.table.side := by exact_mod_cast hDr.L_odd.pos
  have hN0 : 0 < c.N 0 := hc.positivity.2.2.2.2.2.1 0
  have hN0' : 0 < Λ.table.N 0 := by rw [← t6]; exact hN0
  set e₀ : ℝ := Λ.table.N 0 * Λ.table.threshold with he₀
  have he₀0 : 0 ≤ e₀ := by positivity
  have hroom : e₀ ≤ 1 / (64 * ((Λ.stepParams.side : ℕ) : ℝ)) := by
    have h1 := hDr.σ_L
    have e : ((Λ.stepParams.side : ℕ) : ℝ) = (Λ.table.side : ℝ) := rfl
    rw [e, le_div_iff₀ (by positivity)]
    have h2 : 0 < Λ.table.threshold * Λ.table.side := by positivity
    rw [he₀]
    have h3 : 0 < Λ.table.N 0 * Λ.table.threshold * Λ.table.side := by positivity
    nlinarith only [h1, h2, h3]
  have hcold1 : Λ.table.threshold + 8 * e₀ < c.σA := by
    have h1 := hDr.cold_le
    rw [t4]
    have h2 : Λ.table.ballRadius = Λ.table.threshold / 64 := rfl
    rw [h2] at h1
    rw [he₀]
    linarith only [h1, hσ]
  have hCw0 : 0 ≤ 64 * c.N 0 := by positivity
  obtain ⟨P, r, hP, hr, hnear⟩ := hHF Λ.stepParams.coupling Λ.stepParams.side c ha hL hL40 hc' Λ.table.threshold e₀
    (64 * c.N 0) hσ he₀0 hroom hcold1 hCw0
  have hδ : 0 < Λ.table.δ₁ := hDr.δ₁_pos
  obtain ⟨S₁, hS₁⟩ := hD Λ.stepParams.side (Λ.table.δ₁ / 2) hL (by positivity)
  obtain ⟨S₂, hS₂⟩ := hD Λ.stepParams.side (r / 2) hL (by positivity)
  obtain ⟨S₃, hS₃⟩ := hD Λ.stepParams.side cf hL hcf
  set K₀ : ℝ := |Cn 0| with hK₀d
  have hK₀ : 0 ≤ K₀ := abs_nonneg _
  set Ah : ℝ := 2 / Λ.table.lam * (1 + 1 / cf) * |S₃| with hAhd
  have hAh0 : 0 ≤ Ah := by positivity
  set P₁ : ℝ := P * (1 + 2 / r) with hP₁d
  have hP₁ : 0 ≤ P₁ := by positivity
  set Z : ℝ := K₀ + 2 * K₀ * Ah + K₀ * |S₁| + 6 * P₁ + Ah * (|S₁| + |S₂|) + 2 * Ah with hZd
  have hS₁0 : 0 ≤ |S₁| := abs_nonneg _
  have hS₂0 : 0 ≤ |S₂| := abs_nonneg _
  have z1 : 0 ≤ 2 * K₀ * Ah := by positivity
  have z2 : 0 ≤ K₀ * |S₁| := by positivity
  have z3 : 0 ≤ Ah * (|S₁| + |S₂|) := by positivity
  have hZ0 : K₀ ≤ Z := by rw [hZd]; linarith
  have hZ1 : 2 * K₀ * Ah ≤ Z := by rw [hZd]; linarith
  have hZ2 : K₀ * |S₁| ≤ Z := by rw [hZd]; linarith
  have hZ3 : 6 * P₁ ≤ Z := by rw [hZd]; linarith
  have hZ4 : Ah * (|S₁| + |S₂|) ≤ Z := by rw [hZd]; linarith
  have hZ5 : 2 * Ah ≤ Z := by rw [hZd]; linarith
  set cn : ℝ := |Cw 0| with hcn
  refine ⟨fun _ => Z, 1, max (max (max Xn Xc) Xw) (max ((2 : ℝ) ^ 1601) (max ((128 / Λ.table.threshold + 1) ^ 5) (16 * cn ^ 2))),
    one_pos, le_trans hyn (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))), ?_⟩
  intro S hx d n _ hd hn V Y hg
  have hxn : Xn ≤ S.scaleCoupling := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxc : Xc ≤ S.scaleCoupling := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxw : Xw ≤ S.scaleCoupling := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx16 : (2 : ℝ) ^ 1601 ≤ S.scaleCoupling := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxσ : (128 / Λ.table.threshold + 1) ^ 5 ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hxcn : 16 * cn ^ 2 ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hx2 : 2 ≤ S.scaleCoupling := two_le_of_two_pow_le hx16
  have hx1 : 1 ≤ S.scaleCoupling := by linarith only [hx2]
  have hx0 : 0 < S.scaleCoupling := by linarith only [hx2]
  obtain ⟨-, hN2, -, -, -, hKle, hwn⟩ := hwin S hxw
  have hnear0 := (hwn (S.lastSeparated + d) (by omega) (by omega)).1
  have hnside := (hwn (S.lastSeparated + d + 1) (by omega) (by omega)).2
  rw [← hn] at hnside
  have hlog0 : 0 ≤ Real.log S.scaleCoupling := Real.log_nonneg hx1
  have hnear' : |S.coupling (S.lastSeparated + d) - S.scaleCoupling| ≤ cn * Real.log S.scaleCoupling :=
    le_trans hnear0 (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0)
  obtain ⟨hhalf, hdbl⟩ := half_le_and_le_two_mul hx2 (abs_nonneg _) hxcn hnear'
  have hxu0 : 0 < S.coupling (S.lastSeparated + d) := by linarith only [hhalf, hx0]
  have hKP : S.lastSeparated + d ≤ S.data.windowLevel := by omega
  have hstand : StageOnFlow Λ.table Λ.response Λ.floor S.β (S.lastSeparated + d)
      ⟨S.tower.stage (S.lastSeparated + d), S.resp (S.lastSeparated + d)⟩ := by
    have h := S.onFlow (S.lastSeparated + d) hKP
    rwa [← S.stage_eq (S.lastSeparated + d) hKP] at h
  have hRx : (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling = S.coupling (S.lastSeparated + d) := hstand.coupling_eq
  have hside : Λ.table.n₀ ≤ n := by
    have h1 : Λ.stepParams.side * Λ.stepParams.n₀ ≤ S.data.period Λ.stepParams.side := S.side_le
    have h2 : S.data.period Λ.stepParams.side ≤ n := by
      rw [hn]
      exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
    have h3 : Λ.stepParams.n₀ ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.le_mul_of_pos_left _ (by omega)
    exact h3.trans (h1.trans h2)
  have hn₀ : 4096 ≤ Λ.table.n₀ := hDr.n₀_ge
  have h64 : 64 ≤ n := by omega
  have h2n : 2 ≤ n := by omega
  have hHn : (trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n).PosDef :=
    hH (S.lastSeparated + d) n hside
  have hsym : ∀ b b', trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n b b' =
      trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n b' b := fun b b' => by
    have := hHn.isHermitian.apply b b'
    simpa using this.symm
  have hinv : (trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ *
      trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hHn.det_pos.ne')
  obtain ⟨hax, -, hcurv, -⟩ := hcut S hxc (S.lastSeparated + d + 1) (by omega) (by omega) n hn V Y hg
  have hv0 : 0 ≤ S.localCurvature (S.lastSeparated + d + 1) n V := Real.iSup_nonneg fun _ => norm_nonneg _
  have hvs : S.localCurvature (S.lastSeparated + d + 1) n V ≤ S.scaleCoupling ^ (-(1 / 4) : ℝ) := hg.curvature_le
  have hrad := clusterRange_div_bounds (x := S.scaleCoupling) hx16 (by linarith only [hx0]) (by linarith only [hx0]) hN2 hL2 hnside
  have hr16 : 2 ≤ S.range := by
    have : 16 ≤ clusterRange S.scaleCoupling / 2 ^ 11 := hrad.1
    show 2 ≤ clusterRange S.scaleCoupling
    omega
  have hm2 : 2 ≤ S.rangeSq := by
    show 2 ≤ S.range ^ 2
    calc 2 ≤ 2 ^ 2 := by norm_num
      _ ≤ S.range ^ 2 := Nat.pow_le_pow_left hr16 2
  have hrr : (S.range : ℝ) ≤ 2 * S.scaleCoupling ^ ((1 : ℝ) / 100) := by
    have h1 : (S.range : ℝ) < S.scaleCoupling ^ ((1 : ℝ) / 100) + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : 1 ≤ S.scaleCoupling ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx1 (by norm_num)
    linarith only [h1, h2]
  have hm32 : 32 * (S.rangeSq : ℝ) * S.scaleCoupling ^ (-(1 / 4) : ℝ) < Λ.table.threshold :=
    rangeSq_mul_curvature_lt hσ hx1 hxσ hrr
  have hm2R : (2 : ℝ) ≤ S.rangeSq := by exact_mod_cast hm2
  have hq0 : 0 ≤ S.scaleCoupling ^ (-(1 / 4) : ℝ) := by positivity
  have h32v : 32 * (S.rangeSq : ℝ) * S.localCurvature (S.lastSeparated + d + 1) n V < Λ.table.threshold :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hvs (by positivity)) hm32
  have h64v : 64 * S.localCurvature (S.lastSeparated + d + 1) n V < Λ.table.threshold := by
    have h1 := mul_le_mul_of_nonneg_right hm2R hv0
    linarith only [h1, h32v]
  have hB := norm_cutoffCoords_le Λ.stepParams V (S.originSite (S.lastSeparated + d + 1) n) hm2 hv0 hax
  have hσA : Λ.table.threshold < c.σA := by linarith only [hcold1, he₀0]
  have hρ1 : c.ρA ≤ 1 := by
    rw [t3]
    exact hDr.chain.2.2.2.2.1
  have hm₀e : (S.tower.stage (S.lastSeparated + d)).toStepSetup.frameReach =
      clusterRange (S.coupling (S.lastSeparated + d)) / 2 ^ 11 := by
    show clusterRange (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling / 2 ^ 11 = _
    rw [hRx]
  obtain ⟨hm₁₆, hm₄⟩ := clusterRange_div_bounds (x := S.coupling (S.lastSeparated + d)) hx16 hhalf hdbl hN2 hL2 hnside
  rw [← hm₀e] at hm₁₆ hm₄
  have hcoldT : ∀ s, 64 * S.localCurvature (S.lastSeparated + d + 1) n V < s →
      IsSmallCurvature s (readAtLevel (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)
        (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top (S.smoothedField (S.lastSeparated + d + 1) n V)) := by
    rintro s hs ⟨x, μ, ν⟩ hq
    have hp : ∀ i, (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).period
        (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top i = n := fun i => period_torusFrame i
    rw [plaquetteDefect_readAtLevel_eq hp]
    exact lt_of_le_of_lt (hcurv 1 zero_le_one le_rfl _ μ ν hq) hs
  have hsideF : ∀ i, 4 * (S.tower.stage (S.lastSeparated + d)).toStepSetup.frameReach + 5 <
      (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).extent i := fun _ => hm₄
  have hw1 : ∀ dd ∈ chordBonds (finiteCells (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)),
      ‖frameCoordField false Λ.stepParams.coupling Λ.table.ρA (S.tower.stage (S.lastSeparated + d)).toStepSetup.frameReach
        (readAtLevel (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top
          (S.smoothedField (S.lastSeparated + d + 1) n V)) dd.1 dd.2‖ ≤ e₀ := by
    intro dd _
    have h1 := bondFrameCoord_norm_le_of_forall hMF hL hc' hρ1 (G := (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)) rfl _
      hm₁₆ hsideF _ hσ.le hσA (fun s hs => hcoldT s (by linarith only [hs, h64v])) dd
    rw [t3, t6] at h1
    exact h1
  have hw2 : ∀ dd ∈ chordBonds (finiteCells (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)),
      ‖frameCoordField false Λ.stepParams.coupling Λ.table.ρA (S.tower.stage (S.lastSeparated + d)).toStepSetup.frameReach
        (readAtLevel (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top
          (S.smoothedField (S.lastSeparated + d + 1) n V)) dd.1 dd.2‖ ≤
          64 * c.N 0 * S.localCurvature (S.lastSeparated + d + 1) n V := by
    intro dd _
    have h1 := bondFrameCoord_norm_le_of_forall hMF hL hc' hρ1 (G := (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)) rfl _
      hm₁₆ hsideF _ (by positivity : 0 ≤ 64 * S.localCurvature (S.lastSeparated + d + 1) n V)
      (by linarith only [h64v, hσA]) hcoldT dd
    rw [t3] at h1
    calc _ ≤ c.N 0 * (64 * S.localCurvature (S.lastSeparated + d + 1) n V) := h1
      _ = _ := by ring
  have hDm := fun b e q => hnear (S.lastSeparated + d) n h64 hsym
    (S.cutoffLie (S.lastSeparated + d + 1) n V) (S.originSite (S.lastSeparated + d + 1) n)
    (S.localCurvature (S.lastSeparated + d + 1) n V) (8 * (S.rangeSq : ℝ) * S.localCurvature (S.lastSeparated + d + 1) n V) hv0
    (fun dd => (hB dd).1) (fun dd => (hB dd).2) (by linarith only [h32v]) _ hw1 hw2 b e q
  have hκS : ∀ b : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n,
      ∑ b', Real.exp (-(Λ.table.δ₁ / 2 * chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) b b')) ≤ |S₁| := by
    intro b
    have h1 := (hS₁ (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) n rfl h2n (fun _ => rfl) (enclosingCell b.1.1)).1
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun b' _ => ?_)) (h1.trans (le_abs_self _))
    unfold chordBondDist
    rw [CellSums.cellSupDist_comm]
  have hES : ∀ b : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n,
      ∑ b', Real.exp (-(r / 2 * chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) b b')) ≤ |S₂| := by
    intro b
    have h1 := (hS₂ (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) n rfl h2n (fun _ => rfl) (enclosingCell b.1.1)).1
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun b' _ => ?_)) (h1.trans (le_abs_self _))
    unfold chordBondDist
    rw [CellSums.cellSupDist_comm]
  have hρ0 : 0 < (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius := by
    show 0 < Λ.table.threshold / 64
    positivity
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have h1 := hnh S hxn d n hd hn V Y hg 0 (fun b => by simpa using hρ0) j
    simp only [Pi.zero_apply, PiLp.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_one] at h1
    exact h1.trans ((le_abs_self _).trans hZ0)
  · have hdj0 : ∀ b : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n,
        0 ≤ (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) : ℝ) :=
      fun b => by positivity
    have hAh : ∑ b, |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ j.2 b| *
        (1 + (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) : ℝ)) ≤ Ah := by
      have hterm : ∀ b : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n,
          |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ j.2 b| *
          (1 + (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) : ℝ)) ≤
          2 / Λ.table.lam * (1 + 1 / cf) * Real.exp (-(cf * (cellSupDist (enclosingCell b.1.1) (enclosingCell j.2.1.1) : ℝ))) := by
        intro b
        set t : ℝ := (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) : ℝ) with ht
        have ht0 : 0 ≤ t := hdj0 b
        have h1 := (hfl S).2 (S.lastSeparated + d) n h64 j.2 b
        have h2 := one_add_mul_exp_le (δ := 4 * cf) (t := t) (by positivity) ht0
        have e1 : 4 * cf / 2 * t = 2 * cf * t := by ring
        have e2 : 4 / (4 * cf) = 1 / cf := by
          field_simp
        have e3 : 4 * cf / 4 * t = cf * t := by ring
        rw [e1, e2, e3] at h2
        have h3 : (cellSupDist (enclosingCell b.1.1) (enclosingCell j.2.1.1) : ℝ) ≤ t := by
          have := chordBondDist_le (L := Λ.stepParams.side) hL2 j.2 b
          unfold chordBondDist at this
          rw [CellSums.cellSupDist_comm]
          exact this
        have h4 : Real.exp (-(cf * t)) ≤ Real.exp (-(cf * (cellSupDist (enclosingCell b.1.1) (enclosingCell j.2.1.1) : ℝ))) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_left h3 hcf.le
          linarith only [this]
        have hl : 0 ≤ 2 / Λ.table.lam := by positivity
        have h5 : 0 ≤ 1 + t := by linarith only [ht0]
        calc _ ≤ (2 / Λ.table.lam * Real.exp (-(2 * cf * t))) * (1 + t) := mul_le_mul_of_nonneg_right h1 h5
          _ = 2 / Λ.table.lam * ((1 + t) * Real.exp (-(2 * cf * t))) := by ring
          _ ≤ 2 / Λ.table.lam * ((1 + 1 / cf) * Real.exp (-(cf * t))) := mul_le_mul_of_nonneg_left h2 hl
          _ ≤ 2 / Λ.table.lam * ((1 + 1 / cf) *
                Real.exp (-(cf * (cellSupDist (enclosingCell b.1.1) (enclosingCell j.2.1.1) : ℝ)))) := by
              apply mul_le_mul_of_nonneg_left _ hl
              exact mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = _ := by ring
      have hs3 := (hS₃ (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) n rfl h2n (fun _ => rfl) (enclosingCell j.2.1.1)).1
      calc _ ≤ ∑ b : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n, 2 / Λ.table.lam * (1 + 1 / cf) *
              Real.exp (-(cf * (cellSupDist (enclosingCell b.1.1) (enclosingCell j.2.1.1) : ℝ))) :=
            Finset.sum_le_sum fun b _ => hterm b
        _ = 2 / Λ.table.lam * (1 + 1 / cf) * ∑ b : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n,
              Real.exp (-(cf * (cellSupDist (enclosingCell b.1.1) (enclosingCell j.2.1.1) : ℝ))) := by rw [Finset.mul_sum]
        _ ≤ Ah := mul_le_mul_of_nonneg_left (hs3.trans (le_abs_self _)) (by positivity)
    have hh1 : ∑ b, |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ j.2 b| ≤ Ah := by
      refine le_trans (Finset.sum_le_sum fun b _ => ?_) hAh
      have h1 := abs_nonneg ((trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ j.2 b)
      have h2 := hdj0 b
      exact le_mul_of_one_le_right h1 (by linarith only [h2])
    refine ⟨fun b' => ∑ b, |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ j.2 b| *
      (Real.exp (-(Λ.table.δ₁ / 2 * chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) b b')) +
        Real.exp (-(r / 2 * chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) b b')) *
        (1 + (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) : ℝ))),
      fun b' => ?_, ?_, ?_, fun k hk => ?_⟩
    · refine Finset.sum_nonneg fun b _ => mul_nonneg (abs_nonneg _) (add_nonneg (Real.exp_pos _).le
        (mul_nonneg (Real.exp_pos _).le (by have := hdj0 b; linarith only [this])))
    · rw [Finset.sum_comm]
      have hrow : ∀ b : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n,
          ∑ b', |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ j.2 b| *
          (Real.exp (-(Λ.table.δ₁ / 2 * chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) b b')) +
            Real.exp (-(r / 2 * chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) b b')) *
            (1 + (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) : ℝ))) ≤
          |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ j.2 b| *
            (1 + (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) : ℝ)) *
            (|S₁| + |S₂|) := by
        intro b
        have hd0 := hdj0 b
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have h1 := hκS b
        have h2 := mul_le_mul_of_nonneg_right (hES b) (by linarith only [hd0] :
          0 ≤ 1 + (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) : ℝ))
        have h3 := mul_nonneg hd0 hS₁0
        linarith only [h1, h2, h3]
      calc _ ≤ ∑ b, |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ j.2 b| *
              (1 + (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) : ℝ)) *
              (|S₁| + |S₂|) :=
            Finset.sum_le_sum fun b _ => hrow b
        _ = (∑ b, |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ j.2 b| *
              (1 + (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) : ℝ))) *
              (|S₁| + |S₂|) := by
            rw [Finset.sum_mul]
        _ ≤ Ah * (|S₁| + |S₂|) := mul_le_mul_of_nonneg_right hAh (by positivity)
        _ ≤ Z := hZ4
    · have e := sum_abs_cov_row (trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹
        (S.coupling (S.lastSeparated + d)) hxu0 j.2 j.1
      have hxi : (S.coupling (S.lastSeparated + d))⁻¹ ≤ 2 * S.scaleCoupling⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, div_le_div_iff₀ hxu0 hx0]
        linarith only [hhalf]
      have e' : ∑ i, |fluctuationCov Λ.stepParams.coupling Λ.stepParams.side (S.coupling (S.lastSeparated + d))
          (S.lastSeparated + d) n j i| =
          (S.coupling (S.lastSeparated + d))⁻¹ *
            ∑ b, |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ j.2 b| := e
      rw [e']
      have h0 : 0 ≤ S.scaleCoupling⁻¹ := by positivity
      have h1 : 0 ≤ ∑ b, |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ j.2 b| :=
        Finset.sum_nonneg fun b _ => abs_nonneg _
      calc _ ≤ (2 * S.scaleCoupling⁻¹) * Ah := mul_le_mul hxi hh1 h1 (by positivity)
        _ = (2 * Ah) * S.scaleCoupling⁻¹ := by ring
        _ ≤ Z * S.scaleCoupling⁻¹ := mul_le_mul_of_nonneg_right hZ5 h0
    · have hfj : 0 ≤ (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1)
          (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) := by positivity
      have hg' : ∀ i : Fin 3 × ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n,
          |(fun i => fderiv ℝ (chartPotential (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.lastSeparated + d)
              (S.smoothedField (S.lastSeparated + d + 1) n V)) k (unitVariation i)) i -
            S.coupling (S.lastSeparated + d) * ∑ q : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n × Fin 3,
              bondCoordinateHessian (chartedEnergyAt Λ.stepParams.coupling
                (frameCoordField false Λ.stepParams.coupling Λ.table.ρA (S.tower.stage (S.lastSeparated + d)).toStepSetup.frameReach
                  (readAtLevel (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)
                    (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top (S.smoothedField (S.lastSeparated + d + 1) n V)))
                (readAtLevel (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)
                  (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top (S.smoothedField (S.lastSeparated + d + 1) n V)))
                (i.2, i.1) q * k q.1 q.2| ≤
          K₀ * (1 + S.coupling (S.lastSeparated + d) * (∑ b, Real.exp (-(Λ.table.δ₁ / 2 *
            chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) i.2 b)) * ‖k b‖) ^ 2) := by
        intro i
        refine (hnh S hxn d n hd hn V Y hg k hk i).trans (mul_le_mul_of_nonneg_right (le_abs_self _) ?_)
        have : 0 ≤ S.coupling (S.lastSeparated + d) * (∑ b, Real.exp (-(Λ.table.δ₁ / 2 *
            chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) i.2 b)) * ‖k b‖) ^ 2 := by positivity
        linarith only [this]
      refine weighted_drift_bound (trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)
        (trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ _ hinv j.2 hxu0 hx0 hhalf hK₀ hS₁0
        hP₁ hv0 hfj
        (fun b => (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) : ℝ)) hdj0
        (fun b b' => Real.exp (-(Λ.table.δ₁ / 2 * chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) b b')))
        (fun b b' => Real.exp (-(r / 2 * chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) b b')))
        (fun _ _ => (Real.exp_pos _).le) hκS (fun _ _ => (Real.exp_pos _).le) hAh hZ1 hZ2 hZ3 k _ hg' ?_ j.1
      intro b e q
      refine (hDm b e q).trans ?_
      have hcb : (cellSupDist (enclosingCell b.1.1) (torusSiteInFrame (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)
          (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top (S.originSite (S.lastSeparated + d + 1) n)) : ℝ) ≤
          (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) : ℝ) +
            (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ)
              + 1 := by
        rw [enclosingCell_eq_parentBlock, cellSupDist_torusFrame, siteOfCell_torusSiteInFrame, siteOfCell_torusSiteInFrame]
        have a1 := supDist_triangle (parentBlock Λ.stepParams.side (toTorusSite (n * Λ.stepParams.side) b.1.1))
          (parentBlock Λ.stepParams.side (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)))
          (S.originSite (S.lastSeparated + d + 1) n)
        have a2 := supDist_parentBlock_le hL2 (toTorusSite (n * Λ.stepParams.side) b.1.1)
          (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side))
        have a3 := supDist_parentBlock_originSite_le_one S (n := n) hL2 (S.lastSeparated + d)
        have a4 := supDist_triangle (toTorusSite (n * Λ.stepParams.side) b.1.1) (toTorusSite (n * Λ.stepParams.side) j.2.1.1)
          (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side))
        have a5 := supDist_comm (toTorusSite (n * Λ.stepParams.side) b.1.1) (toTorusSite (n * Λ.stepParams.side) j.2.1.1)
        have : TorusFields.supDist (parentBlock Λ.stepParams.side (toTorusSite (n * Λ.stepParams.side) b.1.1))
            (S.originSite (S.lastSeparated + d + 1) n) ≤
            TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) +
              TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side))
                + 1 := by omega
        exact_mod_cast this
      have hs0 : ∀ i, 0 < (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).extent i := fun i => by
        show 0 < n
        omega
      have htri : (cellSupDist (enclosingCell q.1.1.1) (torusSiteInFrame (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)
          (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top (S.originSite (S.lastSeparated + d + 1) n)) : ℝ) ≤
          chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) b q.1 +
            (cellSupDist (enclosingCell b.1.1) (torusSiteInFrame (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)
              (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top (S.originSite (S.lastSeparated + d + 1) n)) : ℝ) := by
        have h1 := CellSums.cellSupDist_triangle hs0 (enclosingCell q.1.1.1) (enclosingCell b.1.1)
          (torusSiteInFrame (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)
            (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top (S.originSite (S.lastSeparated + d + 1) n))
        have h2 : chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) b q.1 =
            (cellSupDist (enclosingCell q.1.1.1) (enclosingCell b.1.1) : ℝ) := by
          unfold chordBondDist
          rw [CellSums.cellSupDist_comm]
        rw [h2]
        exact_mod_cast h1
      have hcomm : chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) q.1 b =
          chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) b q.1 := by
        unfold chordBondDist
        rw [CellSums.cellSupDist_comm]
      rw [hcomm]
      set t : ℝ := chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) b q.1 with ht
      have ht0 : 0 ≤ t := by
        rw [ht]
        unfold chordBondDist
        positivity
      set g₁ : ℝ := (cellSupDist (enclosingCell q.1.1.1) (torusSiteInFrame (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)
        (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top (S.originSite (S.lastSeparated + d + 1) n)) : ℝ) with hg₁
      set g₂ : ℝ := (cellSupDist (enclosingCell b.1.1) (torusSiteInFrame (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)
        (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top (S.originSite (S.lastSeparated + d + 1) n)) : ℝ) with hg₂
      set db : ℝ := (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1) (toTorusSite (n * Λ.stepParams.side) b.1.1) : ℝ)
        with hdb
      set fj : ℝ := (TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) j.2.1.1)
        (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) with hfjd
      have hdb0 : 0 ≤ db := hdj0 b
      have hg₂0 : 0 ≤ g₂ := by rw [hg₂]; positivity
      have h1 := one_add_mul_exp_le (δ := 2 * r) (t := t) (by positivity) ht0
      have e1 : 2 * r / 2 * t = r * t := by ring
      have e2 : 4 / (2 * r) = 2 / r := by
        field_simp
        ring
      have e3 : 2 * r / 4 * t = r / 2 * t := by ring
      rw [e1, e2, e3] at h1
      have h2 : 1 + g₁ ≤ (1 + t) * (2 * (1 + fj) * (1 + db)) := by
        have h3 : 1 + g₂ ≤ 2 * (1 + fj) * (1 + db) := by nlinarith only [hcb, mul_nonneg hfj hdb0, hfj, hdb0]
        have h4 : 1 + g₁ ≤ (1 + t) * (1 + g₂) := by nlinarith only [htri, mul_nonneg ht0 hg₂0]
        exact h4.trans (mul_le_mul_of_nonneg_left h3 (by linarith only [ht0]))
      have hpos : 0 ≤ 2 * (1 + fj) * (1 + db) := by positivity
      calc P * Real.exp (-(r * t)) * (1 + g₁) * S.localCurvature (S.lastSeparated + d + 1) n V
          ≤ P * Real.exp (-(r * t)) * ((1 + t) * (2 * (1 + fj) * (1 + db))) *
              S.localCurvature (S.lastSeparated + d + 1) n V := by
            gcongr
        _ = P * ((1 + t) * Real.exp (-(r * t))) * (2 * (1 + fj) * (1 + db)) *
              S.localCurvature (S.lastSeparated + d + 1) n V := by ring
        _ ≤ P * ((1 + 2 / r) * Real.exp (-(r / 2 * t))) * (2 * (1 + fj) * (1 + db)) *
              S.localCurvature (S.lastSeparated + d + 1) n V := by
            gcongr
        _ = _ := by
            rw [hP₁d]
            ring
end YangMills.Construction.MomentLaw
end
