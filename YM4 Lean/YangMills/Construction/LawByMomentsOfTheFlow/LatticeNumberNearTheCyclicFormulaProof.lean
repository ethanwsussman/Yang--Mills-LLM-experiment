import YangMills.Construction.RegionSequence.TorusHodgeIdentityProof
import YangMills.Construction.LawByMomentsOfTheFlow.CumulantOfTheBottomCurvatureProof
import YangMills.Construction.LawByMomentsOfTheFlow.FactsOfAReflection
import YangMills.Construction.LawByMomentsOfTheFlow.IntegrandOfTheCyclicFormula
import YangMills.Construction.LawByMomentsOfTheFlow.LatticeNumberNearTheCyclicFormula
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheLastFarLevelInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.TorusSumNearTheLatticeNumberProof
import YangMills.Construction.LawInAState.ReflectionKernelAtADistanceProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.CyclicFormula YangMills.Construction.TestFunctions
private theorem abs_apply_le_norm (x : EuclideanFourSpace) (a : Fin 4) : |x a| ≤ ‖x‖ := by
  simpa using PiLp.norm_apply_le x a
private theorem norm_le_two_mul_of_abs_apply_le (x : EuclideanFourSpace) (c : ℝ) (hc : ∀ a, |x a| ≤ c) :
    ‖x‖ ≤ 2 * c := by apply _root_.YangMills.SharedProofs.p52306 <;> assumption
private theorem supDist_le_norm_sub (x y : EuclideanFourSpace) : supDist x y ≤ ‖x - y‖ := by
  refine ciSup_le fun a => ?_
  simpa using abs_apply_le_norm (x - y) a
private def unitCoord (v : EuclideanFourSpace) (a : Fin 4) : ℝ := v a / ‖v‖
private theorem abs_unitCoord_le_one (v : EuclideanFourSpace) (a : Fin 4) : |unitCoord v a| ≤ 1 := by
  rw [unitCoord, abs_div, abs_norm]
  exact div_le_one_of_le₀ (abs_apply_le_norm v a) (norm_nonneg _)
private theorem abs_unitCoord_sub_le {r : ℝ} (hr : 0 < r) {v w : EuclideanFourSpace} (hv : r ≤ ‖v‖) (hw : r ≤ ‖w‖)
    (a : Fin 4) : |unitCoord v a - unitCoord w a| ≤ 2 * ‖v - w‖ / r := by
  have hv0 : 0 < ‖v‖ := hr.trans_le hv
  have hw0 : 0 < ‖w‖ := hr.trans_le hw
  have e : unitCoord v a - unitCoord w a = (v a - w a) / ‖v‖ + unitCoord w a * ((‖w‖ - ‖v‖) / ‖v‖) := by
    simp only [unitCoord]; field_simp; ring
  have h1 : |v a - w a| ≤ ‖v - w‖ := by simpa using abs_apply_le_norm (v - w) a
  have h2 : |‖w‖ - ‖v‖| ≤ ‖v - w‖ := by
    rw [abs_sub_comm]; exact abs_norm_sub_norm_le v w
  have h3 : |unitCoord w a * ((‖w‖ - ‖v‖) / ‖v‖)| ≤ ‖v - w‖ / ‖v‖ := by
    rw [abs_mul, abs_div, abs_norm]
    calc |unitCoord w a| * (|‖w‖ - ‖v‖| / ‖v‖) ≤ 1 * (|‖w‖ - ‖v‖| / ‖v‖) :=
          mul_le_mul_of_nonneg_right (abs_unitCoord_le_one w a) (by positivity)
      _ ≤ ‖v - w‖ / ‖v‖ := by rw [one_mul]; exact div_le_div_of_nonneg_right h2 hv0.le
  have h4 : |(v a - w a) / ‖v‖| ≤ ‖v - w‖ / ‖v‖ := by
    rw [abs_div, abs_norm]; exact div_le_div_of_nonneg_right h1 hv0.le
  have h5 : ‖v - w‖ / ‖v‖ ≤ ‖v - w‖ / r := div_le_div_of_nonneg_left (norm_nonneg _) hr hv
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have : 2 * ‖v - w‖ / r = ‖v - w‖ / r + ‖v - w‖ / r := by ring
  linarith
private theorem inversionMatrix_apply_eq (v : EuclideanFourSpace) (a b : Fin 4) :
    inversionMatrix v a b = (1 : Matrix (Fin 4) (Fin 4) ℝ) a b - 2 * (unitCoord v a * unitCoord v b) := by
  by_cases hv : ‖v‖ = 0
  · simp [inversionMatrix, unitCoord, hv]
  · simp only [inversionMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, unitCoord]
    field_simp
private theorem abs_one_apply_le (a b : Fin 4) : |(1 : Matrix (Fin 4) (Fin 4) ℝ) a b| ≤ 1 := by
  by_cases h : a = b <;> simp [Matrix.one_apply, h]
private theorem abs_inversionMatrix_apply_le (v : EuclideanFourSpace) (a b : Fin 4) : |inversionMatrix v a b| ≤ 3 := by
  rw [inversionMatrix_apply_eq]
  have h1 := abs_one_apply_le a b
  have h2 : |unitCoord v a * unitCoord v b| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (abs_unitCoord_le_one v a) (abs_nonneg _) (abs_unitCoord_le_one v b)
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private theorem abs_inversionMatrix_sub_le {r : ℝ} (hr : 0 < r) {v w : EuclideanFourSpace} (hv : r ≤ ‖v‖)
    (hw : r ≤ ‖w‖) (a b : Fin 4) :
    |inversionMatrix v a b - inversionMatrix w a b| ≤ 8 * ‖v - w‖ / r := by
  rw [inversionMatrix_apply_eq, inversionMatrix_apply_eq]
  have e : (1 : Matrix (Fin 4) (Fin 4) ℝ) a b - 2 * (unitCoord v a * unitCoord v b) -
      ((1 : Matrix (Fin 4) (Fin 4) ℝ) a b - 2 * (unitCoord w a * unitCoord w b)) =
      -2 * ((unitCoord v a - unitCoord w a) * unitCoord v b + unitCoord w a * (unitCoord v b - unitCoord w b)) := by
    ring
  rw [e, abs_mul]
  have h1 : |(unitCoord v a - unitCoord w a) * unitCoord v b| ≤ 2 * ‖v - w‖ / r := by
    rw [abs_mul]
    calc _ ≤ (2 * ‖v - w‖ / r) * 1 :=
          mul_le_mul (abs_unitCoord_sub_le hr hv hw a) (abs_unitCoord_le_one v b) (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  have h2 : |unitCoord w a * (unitCoord v b - unitCoord w b)| ≤ 2 * ‖v - w‖ / r := by
    rw [abs_mul]
    calc _ ≤ 1 * (2 * ‖v - w‖ / r) :=
          mul_le_mul (abs_unitCoord_le_one w a) (abs_unitCoord_sub_le hr hv hw b) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h3 := abs_add_le ((unitCoord v a - unitCoord w a) * unitCoord v b)
    (unitCoord w a * (unitCoord v b - unitCoord w b))
  have h4 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h4]
  have : 8 * ‖v - w‖ / r = 2 * (2 * ‖v - w‖ / r + 2 * ‖v - w‖ / r) := by ring
  linarith
private theorem abs_exteriorSquare_inversion_le (v : EuclideanFourSpace) (α β : OrderedDirectionPair) :
    |exteriorSquareMap (inversionMatrix v) α β| ≤ 18 := by
  simp only [exteriorSquareMap]
  have h : ∀ a b c e : Fin 4, |inversionMatrix v a b * inversionMatrix v c e| ≤ 9 := fun a b c e => by
    rw [abs_mul]
    calc _ ≤ (3 : ℝ) * 3 :=
          mul_le_mul (abs_inversionMatrix_apply_le v a b) (abs_inversionMatrix_apply_le v c e) (abs_nonneg _)
            (by norm_num)
      _ = 9 := by norm_num
  obtain ⟨a1, a2⟩ := abs_le.mp (h α.1.1 β.1.1 α.1.2 β.1.2)
  obtain ⟨b1, b2⟩ := abs_le.mp (h α.1.1 β.1.2 α.1.2 β.1.1)
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private theorem abs_mul_sub_mul_le {x y x' y' M δ : ℝ} (hx : |x| ≤ M) (hy' : |y'| ≤ M) (h1 : |x - x'| ≤ δ)
    (h2 : |y - y'| ≤ δ) (hM : 0 ≤ M) (hδ : 0 ≤ δ) : |x * y - x' * y'| ≤ 2 * M * δ := by
  have e : x * y - x' * y' = x * (y - y') + (x - x') * y' := by ring
  rw [e]
  have a1 : |x * (y - y')| ≤ M * δ := by
    rw [abs_mul]; exact mul_le_mul hx h2 (abs_nonneg _) hM
  have a2 : |(x - x') * y'| ≤ δ * M := by
    rw [abs_mul]; exact mul_le_mul h1 hy' (abs_nonneg _) hδ
  have := abs_add_le (x * (y - y')) ((x - x') * y')
  nlinarith
private theorem abs_exteriorSquare_inversion_sub_le {r : ℝ} (hr : 0 < r) {v w : EuclideanFourSpace}
    (hv : r ≤ ‖v‖) (hw : r ≤ ‖w‖) (α β : OrderedDirectionPair) :
    |exteriorSquareMap (inversionMatrix v) α β - exteriorSquareMap (inversionMatrix w) α β| ≤ 96 * ‖v - w‖ / r := by
  simp only [exteriorSquareMap]
  have hδ : 0 ≤ 8 * ‖v - w‖ / r := by positivity
  have h : ∀ a b c e : Fin 4, |inversionMatrix v a b * inversionMatrix v c e -
      inversionMatrix w a b * inversionMatrix w c e| ≤ 2 * 3 * (8 * ‖v - w‖ / r) := fun a b c e =>
    abs_mul_sub_mul_le (abs_inversionMatrix_apply_le v a b) (abs_inversionMatrix_apply_le w c e)
      (abs_inversionMatrix_sub_le hr hv hw a b) (abs_inversionMatrix_sub_le hr hv hw c e) (by norm_num) hδ
  obtain ⟨a1, a2⟩ := abs_le.mp (h α.1.1 β.1.1 α.1.2 β.1.2)
  obtain ⟨b1, b2⟩ := abs_le.mp (h α.1.1 β.1.2 α.1.2 β.1.1)
  have : 96 * ‖v - w‖ / r = 2 * (2 * 3 * (8 * ‖v - w‖ / r)) := by ring
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def radialWeight (v : EuclideanFourSpace) : ℝ := (Real.pi ^ 2 * ‖v‖ ^ 4)⁻¹
private def linkKernel (α β : OrderedDirectionPair) (v : EuclideanFourSpace) : ℝ :=
  radialWeight v * exteriorSquareMap (inversionMatrix v) α β
private theorem one_le_sq_pi : (1 : ℝ) ≤ Real.pi ^ 2 := by apply _root_.YangMills.Construction.ReflectionKernel.one_le_pi_sq <;> assumption
private theorem radialWeight_eq (v : EuclideanFourSpace) : radialWeight v = (Real.pi ^ 2)⁻¹ * (‖v‖⁻¹) ^ 4 := by
  simp only [radialWeight, mul_inv, inv_pow]
private theorem radialWeight_nonneg (v : EuclideanFourSpace) : 0 ≤ radialWeight v := by
  simp only [radialWeight]; positivity
private theorem radialWeight_le {r : ℝ} (hr : 0 < r) {v : EuclideanFourSpace} (hv : r ≤ ‖v‖) :
    radialWeight v ≤ (r⁻¹) ^ 4 := by
  rw [radialWeight_eq]
  have h1 : ‖v‖⁻¹ ≤ r⁻¹ := inv_anti₀ hr hv
  have h2 : (‖v‖⁻¹) ^ 4 ≤ (r⁻¹) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
  have h3 : (Real.pi ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ one_le_sq_pi
  calc (Real.pi ^ 2)⁻¹ * (‖v‖⁻¹) ^ 4 ≤ 1 * (‖v‖⁻¹) ^ 4 := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ ≤ (r⁻¹) ^ 4 := by rw [one_mul]; exact h2
private theorem abs_radialWeight_sub_le {r : ℝ} (hr : 0 < r) {v w : EuclideanFourSpace} (hv : r ≤ ‖v‖)
    (hw : r ≤ ‖w‖) : |radialWeight v - radialWeight w| ≤ 4 * (r⁻¹) ^ 5 * ‖v - w‖ := by
  rw [radialWeight_eq, radialWeight_eq]
  have hv0 : 0 < ‖v‖ := hr.trans_le hv
  have hw0 : 0 < ‖w‖ := hr.trans_le hw
  set t := ‖v‖⁻¹ with ht
  set u := ‖w‖⁻¹ with hu
  set q := r⁻¹ with hq
  have t0 : 0 ≤ t := by positivity
  have u0 : 0 ≤ u := by positivity
  have q0 : 0 ≤ q := by positivity
  have tq : t ≤ q := inv_anti₀ hr hv
  have uq : u ≤ q := inv_anti₀ hr hw
  have hdiff : |t - u| ≤ q ^ 2 * ‖v - w‖ := by
    have e : t - u = (‖w‖ - ‖v‖) * (t * u) := by
      simp only [ht, hu]; field_simp
    rw [e, abs_mul, abs_of_nonneg (mul_nonneg t0 u0)]
    have h2 : |‖w‖ - ‖v‖| ≤ ‖v - w‖ := by
      rw [abs_sub_comm]; exact abs_norm_sub_norm_le v w
    have h3 : t * u ≤ q ^ 2 := by nlinarith
    calc _ ≤ ‖v - w‖ * q ^ 2 := mul_le_mul h2 h3 (mul_nonneg t0 u0) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hsum : t ^ 3 + t ^ 2 * u + t * u ^ 2 + u ^ 3 ≤ 4 * q ^ 3 := by
    have a1 : t ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ t0 tq 3
    have a4 : u ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ u0 uq 3
    have a2 : t ^ 2 * u ≤ q ^ 2 * q := mul_le_mul (pow_le_pow_left₀ t0 tq 2) uq u0 (by positivity)
    have a3 : t * u ^ 2 ≤ q * q ^ 2 := mul_le_mul tq (pow_le_pow_left₀ u0 uq 2) (by positivity) q0
    nlinarith
  have hsum0 : 0 ≤ t ^ 3 + t ^ 2 * u + t * u ^ 2 + u ^ 3 := by positivity
  have e : (Real.pi ^ 2)⁻¹ * t ^ 4 - (Real.pi ^ 2)⁻¹ * u ^ 4 =
      (Real.pi ^ 2)⁻¹ * ((t - u) * (t ^ 3 + t ^ 2 * u + t * u ^ 2 + u ^ 3)) := by ring
  rw [e, abs_mul, abs_mul, abs_of_nonneg hsum0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.pi ^ 2)⁻¹)]
  have h3 : (Real.pi ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ one_le_sq_pi
  calc (Real.pi ^ 2)⁻¹ * (|t - u| * (t ^ 3 + t ^ 2 * u + t * u ^ 2 + u ^ 3))
      ≤ 1 * (|t - u| * (t ^ 3 + t ^ 2 * u + t * u ^ 2 + u ^ 3)) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ ≤ 1 * ((q ^ 2 * ‖v - w‖) * (4 * q ^ 3)) := by
        rw [one_mul, one_mul]; exact mul_le_mul hdiff hsum hsum0 (by positivity)
    _ = 4 * q ^ 5 * ‖v - w‖ := by ring
private theorem abs_linkKernel_le {r : ℝ} (hr : 0 < r) {v : EuclideanFourSpace} (hv : r ≤ ‖v‖)
    (α β : OrderedDirectionPair) : |linkKernel α β v| ≤ 18 * (r⁻¹) ^ 4 := by
  rw [linkKernel, abs_mul, abs_of_nonneg (radialWeight_nonneg v), mul_comm]
  exact mul_le_mul (abs_exteriorSquare_inversion_le v α β) (radialWeight_le hr hv) (radialWeight_nonneg v)
    (by norm_num)
private theorem abs_linkKernel_sub_le {r : ℝ} (hr : 0 < r) {v w : EuclideanFourSpace} (hv : r ≤ ‖v‖)
    (hw : r ≤ ‖w‖) (α β : OrderedDirectionPair) :
    |linkKernel α β v - linkKernel α β w| ≤ 168 * (r⁻¹) ^ 5 * ‖v - w‖ := by
  have e : linkKernel α β v - linkKernel α β w =
      radialWeight v * (exteriorSquareMap (inversionMatrix v) α β - exteriorSquareMap (inversionMatrix w) α β) +
      (radialWeight v - radialWeight w) * exteriorSquareMap (inversionMatrix w) α β := by
    simp only [linkKernel]; ring
  rw [e]
  have a1 : |radialWeight v * (exteriorSquareMap (inversionMatrix v) α β -
      exteriorSquareMap (inversionMatrix w) α β)| ≤ (r⁻¹) ^ 4 * (96 * ‖v - w‖ / r) := by
    rw [abs_mul, abs_of_nonneg (radialWeight_nonneg v)]
    exact mul_le_mul (radialWeight_le hr hv) (abs_exteriorSquare_inversion_sub_le hr hv hw α β) (abs_nonneg _)
      (by positivity)
  have a2 : |(radialWeight v - radialWeight w) * exteriorSquareMap (inversionMatrix w) α β| ≤
      (4 * (r⁻¹) ^ 5 * ‖v - w‖) * 18 := by
    rw [abs_mul]
    exact mul_le_mul (abs_radialWeight_sub_le hr hv hw) (abs_exteriorSquare_inversion_le w α β) (abs_nonneg _)
      (by positivity)
  have := abs_add_le (radialWeight v * (exteriorSquareMap (inversionMatrix v) α β -
      exteriorSquareMap (inversionMatrix w) α β))
    ((radialWeight v - radialWeight w) * exteriorSquareMap (inversionMatrix w) α β)
  have e2 : (r⁻¹) ^ 4 * (96 * ‖v - w‖ / r) + (4 * (r⁻¹) ^ 5 * ‖v - w‖) * 18 = 168 * (r⁻¹) ^ 5 * ‖v - w‖ := by
    field_simp; ring
  linarith
private theorem radialWeight_smul {e : ℝ} (he : 0 < e) (v : EuclideanFourSpace) :
    radialWeight (e • v) = (e⁻¹) ^ 4 * radialWeight v := by
  simp only [radialWeight, norm_smul, Real.norm_eq_abs, abs_of_pos he]
  by_cases hv : ‖v‖ = 0
  · simp [hv]
  · field_simp
private theorem abs_prod_le_pow {ι : Type} (s : Finset ι) (a : ι → ℝ) {M : ℝ} (ha : ∀ i ∈ s, |a i| ≤ M) :
    |∏ i ∈ s, a i| ≤ M ^ s.card := by
  rw [Finset.abs_prod]
  calc ∏ i ∈ s, |a i| ≤ ∏ _i ∈ s, M := Finset.prod_le_prod (fun i _ => abs_nonneg _) ha
    _ = M ^ s.card := by simp
private theorem abs_prod_sub_prod_le {ι : Type} (s : Finset ι) (a b : ι → ℝ) {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (ha : ∀ i ∈ s, |a i| ≤ M) (hb : ∀ i ∈ s, |b i| ≤ M) (hab : ∀ i ∈ s, |a i - b i| ≤ δ) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ s.card * M ^ s.card * δ := by apply _root_.YangMills.SharedProofs.p14264 <;> assumption
private theorem trace_listProd_ofFn {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ) [NeZero k]
    (A : Fin k → Matrix ι ι ℝ) :
    Matrix.trace (List.ofFn A).prod = ∑ b : Fin k → ι, ∏ c : Fin k, A c (b c) (b (c + 1)) := by apply _root_.YangMills.SharedProofs.p55566 <;> assumption
private theorem sum_orderedDirectionPair (f : OrderedDirectionPair → ℝ) : ∑ r, f r =
    f ⟨(0, 1), by decide⟩ + f ⟨(0, 2), by decide⟩ + f ⟨(0, 3), by decide⟩ + f ⟨(1, 2), by decide⟩ +
      f ⟨(1, 3), by decide⟩ + f ⟨(2, 3), by decide⟩ := by apply _root_.YangMills.Construction.RegionSequence.TorusHodge.sum_ordered_pairs <;> assumption
private theorem exteriorSquareMap_mul (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    exteriorSquareMap (A * B) = exteriorSquareMap A * exteriorSquareMap B := by
  ext p q
  rw [Matrix.mul_apply, sum_orderedDirectionPair]
  simp only [exteriorSquareMap, Matrix.mul_apply, Fin.sum_univ_four]
  ring
private theorem exteriorSquareMap_listProd : ∀ (m : ℕ) (f : Fin (m + 1) → Matrix (Fin 4) (Fin 4) ℝ),
    exteriorSquareMap (List.ofFn f).prod = (List.ofFn fun c => exteriorSquareMap (f c)).prod := by
  intro m
  induction m with
  | zero => intro f; simp [List.ofFn_succ]
  | succ m ih =>
    intro f
    rw [List.ofFn_succ, List.prod_cons, exteriorSquareMap_mul, ih,
      List.ofFn_succ (f := fun c => exteriorSquareMap (f c)), List.prod_cons]
private theorem cycleKernel_eq_sum {k : ℕ} [NeZero k] (σ : Equiv.Perm (Fin k)) (x : Fin k → EuclideanFourSpace) :
    cycleKernel σ x = ∑ α : Fin k → OrderedDirectionPair,
      ∏ c : Fin k, linkKernel (α (σ c)) (α (σ (c + 1))) (x (σ c) - x (σ (c + 1))) := by
  have htr : exteriorSquareTrace (List.ofFn fun c : Fin k => inversionMatrix (x (σ c) - x (σ (c + 1)))).prod =
      ∑ b : Fin k → OrderedDirectionPair,
        ∏ c : Fin k, exteriorSquareMap (inversionMatrix (x (σ c) - x (σ (c + 1)))) (b c) (b (c + 1)) := by
    rw [exteriorSquareTrace]
    have : exteriorSquareMap (List.ofFn fun c : Fin k => inversionMatrix (x (σ c) - x (σ (c + 1)))).prod =
        (List.ofFn fun c : Fin k => exteriorSquareMap (inversionMatrix (x (σ c) - x (σ (c + 1))))).prod := by
      cases k with
      | zero => exact absurd rfl (NeZero.ne 0)
      | succ m => exact exteriorSquareMap_listProd m _
    rw [this, trace_listProd_ofFn]
  rw [cycleKernel, htr, Finset.mul_sum, ← (σ.symm.arrowCongr (Equiv.refl OrderedDirectionPair)).sum_comp]
  refine Fintype.sum_congr _ _ fun α => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  simp [linkKernel, radialWeight, Equiv.arrowCongr]
private theorem measurable_apply_coord (a : Fin 4) : Measurable fun x : EuclideanFourSpace => x a :=
  (EuclideanSpace.proj (𝕜 := ℝ) a).continuous.measurable
private def roundingCell {k : ℕ} (e : ℝ) (x : Fin k → EuclideanFourSpace) : Fin k → Fin 4 → ℤ :=
  fun i a => ⌊x i a / e + 1 / 2⌋
private theorem measurable_roundingCell {k : ℕ} (e : ℝ) : Measurable (roundingCell (k := k) e) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun a => ?_
  exact Int.measurable_floor.comp ((((measurable_apply_coord a).comp (measurable_pi_apply i)).div_const e).add_const _)
private def roundingCube (e : ℝ) (w : Fin 4 → ℤ) : Set EuclideanFourSpace := {y | ∀ a, ⌊y a / e + 1 / 2⌋ = w a}
private theorem volume_roundingCube {e : ℝ} (he : 0 < e) (w : Fin 4 → ℤ) :
    volume (roundingCube e w) = ENNReal.ofReal e ^ 4 := by
  have h : roundingCube e w = (WithLp.ofLp : EuclideanFourSpace → (Fin 4 → ℝ)) ⁻¹'
      Set.pi Set.univ (fun a => Set.Ico (e * ((w a : ℝ) - 1 / 2)) (e * ((w a : ℝ) + 1 / 2))) := by
    ext y
    simp only [roundingCube, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff,
      Set.mem_Ico, Int.floor_eq_iff]
    refine forall_congr' fun a => ?_
    have hy : y a = e * (y a / e) := by field_simp
    show _ ↔ e * ((w a : ℝ) - 1 / 2) ≤ y a ∧ y a < e * ((w a : ℝ) + 1 / 2)
    generalize y a / e = t at hy
    rw [hy]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨mul_le_mul_of_nonneg_left (by linarith) he.le, mul_lt_mul_of_pos_left (by linarith) he⟩
    · rintro ⟨h1, h2⟩
      have h1' := le_of_mul_le_mul_left h1 he
      have h2' := lt_of_mul_lt_mul_left h2 he.le
      exact ⟨by linarith, by linarith⟩
  rw [h, (PiLp.volume_preserving_ofLp (Fin 4)).measure_preimage
    (MeasurableSet.univ_pi fun a => measurableSet_Ico).nullMeasurableSet, volume_pi, Measure.pi_pi]
  simp only [Real.volume_Ico]
  have : ∀ a, e * ((w a : ℝ) + 1 / 2) - e * ((w a : ℝ) - 1 / 2) = e := fun a => by ring
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
private theorem volume_roundingCell_preimage {k : ℕ} {e : ℝ} (he : 0 < e) (z : Fin k → Fin 4 → ℤ) :
    (volume : Measure (Fin k → EuclideanFourSpace)) (roundingCell e ⁻¹' {z}) = ENNReal.ofReal e ^ (4 * k) := by
  have h : roundingCell (k := k) e ⁻¹' {z} = Set.pi Set.univ fun i => roundingCube e (z i) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_imp_iff, roundingCube,
      Set.mem_ofPred_eq, roundingCell, funext_iff]
  rw [h, volume_pi, Measure.pi_pi]
  simp only [volume_roundingCube he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul]
private theorem measureReal_roundingCell_preimage {k : ℕ} {e : ℝ} (he : 0 < e) (z : Fin k → Fin 4 → ℤ) :
    (volume : Measure (Fin k → EuclideanFourSpace)).real (roundingCell e ⁻¹' {z}) = e ^ (4 * k) := by
  rw [Measure.real, volume_roundingCell_preimage he, ENNReal.toReal_pow, ENNReal.toReal_ofReal he.le]
private theorem abs_riemannSum_sub_integral_le {k : ℕ} {e : ℝ} (he : 0 < e)
    (F : (Fin k → EuclideanFourSpace) → ℝ) (hF : Integrable F)
    (Box : Finset (Fin k → Fin 4 → ℤ)) (g : (Fin k → Fin 4 → ℤ) → ℝ) {δ : ℝ}
    (hs : ∀ x, F x ≠ 0 → roundingCell e x ∈ Box) (hg : ∀ z ∈ Box, ∀ x, roundingCell e x = z → |g z - F x| ≤ δ) :
    |e ^ (4 * k) * ∑ z ∈ Box, g z - ∫ x, F x| ≤ δ * e ^ (4 * k) * Box.card := by
  have hm : ∀ z, MeasurableSet (roundingCell (k := k) e ⁻¹' {z}) := fun z =>
    measurable_roundingCell e (measurableSet_singleton z)
  have hfin : ∀ z, volume (roundingCell (k := k) e ⁻¹' {z}) < ⊤ := fun z => by
    rw [volume_roundingCell_preimage he]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  have hI : ∫ x, F x = ∑ z ∈ Box, ∫ x in roundingCell e ⁻¹' {z}, F x := by
    rw [← integral_biUnion_finset Box (fun z _ => hm z) ?_ (fun z _ => hF.integrableOn)]
    · symm
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      by_contra h
      exact hx (Set.mem_biUnion (hs x h) rfl)
    · intro z _ z' _ hz
      refine Set.disjoint_left.mpr fun x hx hx' => hz ?_
      exact (Set.mem_singleton_iff.mp hx).symm.trans (Set.mem_singleton_iff.mp hx')
  have key : ∀ z ∈ Box, |e ^ (4 * k) * g z - ∫ x in roundingCell e ⁻¹' {z}, F x| ≤ δ * e ^ (4 * k) := by
    intro z hz
    have e1 : e ^ (4 * k) * g z - ∫ x in roundingCell e ⁻¹' {z}, F x =
        ∫ x in roundingCell e ⁻¹' {z}, (g z - F x) := by
      have hc : Integrable (fun _ => g z) (volume.restrict (roundingCell (k := k) e ⁻¹' {z})) :=
        integrableOn_const (hfin z).ne (by simp)
      have hF' : Integrable F (volume.restrict (roundingCell (k := k) e ⁻¹' {z})) := hF.integrableOn
      rw [integral_sub hc hF', setIntegral_const, measureReal_roundingCell_preimage he, smul_eq_mul]
    rw [e1]
    have h2 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := roundingCell (k := k) e ⁻¹' {z})
      (f := fun x => g z - F x) (C := δ) (hfin z) (fun x hx => by
        rw [Real.norm_eq_abs]; exact hg z hz x (Set.mem_singleton_iff.mp hx))
    rw [measureReal_roundingCell_preimage he, Real.norm_eq_abs] at h2
    exact h2
  rw [hI, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _z ∈ Box, δ * e ^ (4 * k) := Finset.sum_le_sum key
    _ = _ := by simp; ring
section LinkBounds
variable {k : ℕ} [NeZero k]
private theorem ne_add_one_of_two_le (hk : 2 ≤ k) (c : Fin k) : c ≠ c + 1 := by apply _root_.YangMills.SharedProofs.p48899 <;> assumption
private def testProduct (φ : Fin k → EuclideanFourSpace → ℝ) (x : Fin k → EuclideanFourSpace) : ℝ := ∏ i, φ i (x i)
private def cycleKernelProduct (σ : Equiv.Perm (Fin k)) (α : Fin k → OrderedDirectionPair)
    (x : Fin k → EuclideanFourSpace) : ℝ :=
  ∏ c : Fin k, linkKernel (α (σ c)) (α (σ (c + 1))) (x (σ c) - x (σ (c + 1)))
omit [NeZero k] in
private theorem abs_testProduct_le_one {R d : ℝ} {φ : Fin k → EuclideanFourSpace → ℝ}
    (hφ : IsSupTestFamily R d φ) (x : Fin k → EuclideanFourSpace) : |testProduct φ x| ≤ 1 := by
  have := abs_prod_le_pow Finset.univ (fun i => φ i (x i)) (M := 1) (fun i _ => hφ.abs_le_one i _)
  simpa [testProduct] using this
omit [NeZero k] in
private theorem apply_ne_zero_of_testProduct_ne_zero {φ : Fin k → EuclideanFourSpace → ℝ}
    {x : Fin k → EuclideanFourSpace} (h : testProduct φ x ≠ 0) (i : Fin k) : φ i (x i) ≠ 0 :=
  Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ _)
private theorem le_norm_link_of_testProduct_ne_zero {R d : ℝ} {φ : Fin k → EuclideanFourSpace → ℝ}
    (hφ : IsSupTestFamily R d φ) (hk : 2 ≤ k) {x : Fin k → EuclideanFourSpace} (h : testProduct φ x ≠ 0)
    (σ : Equiv.Perm (Fin k)) (c : Fin k) : d ≤ ‖x (σ c) - x (σ (c + 1))‖ := by
  have hne : σ c ≠ σ (c + 1) := fun e => ne_add_one_of_two_le hk c (σ.injective e)
  exact (hφ.le_supDist _ _ hne _ (subset_tsupport _ (apply_ne_zero_of_testProduct_ne_zero h _)) _
    (subset_tsupport _ (apply_ne_zero_of_testProduct_ne_zero h _))).trans (supDist_le_norm_sub _ _)
private def linkKernelBound (r : ℝ) : ℝ := 1 + 18 * (r⁻¹) ^ 4
private theorem one_le_linkKernelBound {r : ℝ} (hr : 0 < r) : 1 ≤ linkKernelBound r := by
  have : 0 ≤ 18 * (r⁻¹) ^ 4 := by positivity
  simp only [linkKernelBound]; linarith
private theorem abs_linkKernel_le_bound {r : ℝ} (hr : 0 < r) {v : EuclideanFourSpace} (hv : r ≤ ‖v‖)
    (α β : OrderedDirectionPair) : |linkKernel α β v| ≤ linkKernelBound r := by
  have := abs_linkKernel_le hr hv α β
  simp only [linkKernelBound]; linarith
private theorem abs_cycleKernelProduct_le {r : ℝ} (hr : 0 < r) (σ : Equiv.Perm (Fin k))
    (α : Fin k → OrderedDirectionPair) {x : Fin k → EuclideanFourSpace}
    (hsep : ∀ c, r ≤ ‖x (σ c) - x (σ (c + 1))‖) : |cycleKernelProduct σ α x| ≤ linkKernelBound r ^ k := by
  have := abs_prod_le_pow Finset.univ (fun c => linkKernel (α (σ c)) (α (σ (c + 1))) (x (σ c) - x (σ (c + 1))))
    (M := linkKernelBound r) (fun c _ => abs_linkKernel_le_bound hr (hsep c) _ _)
  simpa [cycleKernelProduct] using this
private def cellLipschitzConst (k : ℕ) (d : ℝ) : ℝ :=
  k * linkKernelBound (d / 2) ^ k * (336 * ((d / 2)⁻¹) ^ 5 + 1)
private theorem cellLipschitzConst_nonneg (k : ℕ) {d : ℝ} (hd : 0 < d) : 0 ≤ cellLipschitzConst k d := by
  have := one_le_linkKernelBound (half_pos hd)
  simp only [cellLipschitzConst]; positivity
private theorem le_norm_sub_of_near {d η : ℝ} {a b a' b' : EuclideanFourSpace} (h : d ≤ ‖a - b‖)
    (ha : ‖a - a'‖ ≤ η) (hb : ‖b - b'‖ ≤ η) : d - 2 * η ≤ ‖a' - b'‖ := by
  have e : a - b = (a - a') + (a' - b') - (b - b') := by abel
  have h1 : ‖a - b‖ ≤ ‖a - a'‖ + ‖a' - b'‖ + ‖b - b'‖ := by
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  linarith
private theorem abs_cycleTerm_sub_le {R d : ℝ} {φ : Fin k → EuclideanFourSpace → ℝ} (hφ : IsSupTestFamily R d φ)
    (hk : 2 ≤ k) (hd : 0 < d) (σ : Equiv.Perm (Fin k)) (α : Fin k → OrderedDirectionPair) {η : ℝ} (hη : 0 ≤ η)
    (h4 : 4 * η ≤ d) {x y : Fin k → EuclideanFourSpace} (hxy : ∀ i, ‖x i - y i‖ ≤ η) :
    |testProduct φ x * cycleKernelProduct σ α x - testProduct φ y * cycleKernelProduct σ α y| ≤
      cellLipschitzConst k d * η := by
  have hr : 0 < d / 2 := half_pos hd
  by_cases h0 : testProduct φ x = 0 ∧ testProduct φ y = 0
  · rw [h0.1, h0.2]
    simpa using mul_nonneg (cellLipschitzConst_nonneg k hd) hη
  have hyx : ∀ i, ‖y i - x i‖ ≤ η := fun i => by rw [norm_sub_rev]; exact hxy i
  have hsep : (∀ c, d / 2 ≤ ‖x (σ c) - x (σ (c + 1))‖) ∧ (∀ c, d / 2 ≤ ‖y (σ c) - y (σ (c + 1))‖) := by
    rcases not_and_or.mp h0 with h | h
    · refine ⟨fun c => ?_, fun c => ?_⟩
      · have := le_norm_link_of_testProduct_ne_zero hφ hk h σ c; linarith
      · have := le_norm_sub_of_near (le_norm_link_of_testProduct_ne_zero hφ hk h σ c) (hxy _) (hxy _); linarith
    · refine ⟨fun c => ?_, fun c => ?_⟩
      · have := le_norm_sub_of_near (le_norm_link_of_testProduct_ne_zero hφ hk h σ c) (hyx _) (hyx _); linarith
      · have := le_norm_link_of_testProduct_ne_zero hφ hk h σ c; linarith
  obtain ⟨hsx, hsy⟩ := hsep
  set M := linkKernelBound (d / 2) with hM
  have hM1 : 1 ≤ M := one_le_linkKernelBound hr
  set q := (d / 2)⁻¹ with hq
  have hP : |testProduct φ x - testProduct φ y| ≤ k * η := by
    have := abs_prod_sub_prod_le Finset.univ (fun i => φ i (x i)) (fun i => φ i (y i)) (M := 1) (δ := η) le_rfl hη
      (fun i _ => hφ.abs_le_one i _) (fun i _ => hφ.abs_le_one i _)
      (fun i _ => (hφ.lipschitz i _ _).trans ((supDist_le_norm_sub _ _).trans (hxy i)))
    simpa [testProduct] using this
  have hQ : |cycleKernelProduct σ α x - cycleKernelProduct σ α y| ≤ k * M ^ k * (336 * q ^ 5 * η) := by
    have := abs_prod_sub_prod_le Finset.univ
      (fun c => linkKernel (α (σ c)) (α (σ (c + 1))) (x (σ c) - x (σ (c + 1))))
      (fun c => linkKernel (α (σ c)) (α (σ (c + 1))) (y (σ c) - y (σ (c + 1)))) (M := M) (δ := 336 * q ^ 5 * η)
      hM1 (by positivity) (fun c _ => abs_linkKernel_le_bound hr (hsx c) _ _)
      (fun c _ => abs_linkKernel_le_bound hr (hsy c) _ _)
      (fun c _ => by
        refine (abs_linkKernel_sub_le hr (hsx c) (hsy c) _ _).trans ?_
        have e : x (σ c) - x (σ (c + 1)) - (y (σ c) - y (σ (c + 1))) =
            (x (σ c) - y (σ c)) - (x (σ (c + 1)) - y (σ (c + 1))) := by abel
        have h2 : ‖x (σ c) - x (σ (c + 1)) - (y (σ c) - y (σ (c + 1)))‖ ≤ η + η := by
          rw [e]
          exact (norm_sub_le _ _).trans (add_le_add (hxy _) (hxy _))
        calc 168 * q ^ 5 * ‖x (σ c) - x (σ (c + 1)) - (y (σ c) - y (σ (c + 1)))‖
            ≤ 168 * q ^ 5 * (η + η) := mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = 336 * q ^ 5 * η := by ring)
    simpa [cycleKernelProduct] using this
  have hQy : |cycleKernelProduct σ α y| ≤ M ^ k := abs_cycleKernelProduct_le hr σ α hsy
  have hPx := abs_testProduct_le_one hφ x
  have e : testProduct φ x * cycleKernelProduct σ α x - testProduct φ y * cycleKernelProduct σ α y =
      testProduct φ x * (cycleKernelProduct σ α x - cycleKernelProduct σ α y) +
        (testProduct φ x - testProduct φ y) * cycleKernelProduct σ α y := by ring
  rw [e]
  have t1 : |testProduct φ x * (cycleKernelProduct σ α x - cycleKernelProduct σ α y)| ≤
      1 * (k * M ^ k * (336 * q ^ 5 * η)) := by
    rw [abs_mul]; exact mul_le_mul hPx hQ (abs_nonneg _) zero_le_one
  have t2 : |(testProduct φ x - testProduct φ y) * cycleKernelProduct σ α y| ≤ (k * η) * M ^ k := by
    rw [abs_mul]; exact mul_le_mul hP hQy (abs_nonneg _) (by positivity)
  have t3 := abs_add_le (testProduct φ x * (cycleKernelProduct σ α x - cycleKernelProduct σ α y))
    ((testProduct φ x - testProduct φ y) * cycleKernelProduct σ α y)
  have e2 : cellLipschitzConst k d * η = 1 * (k * M ^ k * (336 * q ^ 5 * η)) + (k * η) * M ^ k := by
    simp only [cellLipschitzConst, hM, hq]; ring
  rw [e2]
  linarith
private theorem testProduct_mul_cycleKernel_eq (φ : Fin k → EuclideanFourSpace → ℝ) (σ : Equiv.Perm (Fin k))
    (x : Fin k → EuclideanFourSpace) :
    (∏ i, φ i (x i)) * cycleKernel σ x =
      ∑ α : Fin k → OrderedDirectionPair, testProduct φ x * cycleKernelProduct σ α x := by
  rw [cycleKernel_eq_sum, Finset.mul_sum]
  rfl
private def siteCube (k b : ℕ) : Finset (Fin k → Fin 4 → ℤ) :=
  Fintype.piFinset fun _ : Fin k => Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(b : ℤ)) (b : ℤ)
private theorem card_siteCube (k b : ℕ) : (siteCube k b).card = (2 * b + 1) ^ (4 * k) := by
  have h : (Finset.Icc (-(b : ℤ)) (b : ℤ)).card = 2 * b + 1 := by
    simp only [Int.card_Icc]; omega
  simp [siteCube, Fintype.card_piFinset, h, pow_mul, mul_comm]
  rw [← pow_mul, ← pow_mul, mul_comm 4 k]
private theorem mem_siteCube {k b : ℕ} {z : Fin k → Fin 4 → ℤ} :
    z ∈ siteCube k b ↔ ∀ i a, -(b : ℤ) ≤ z i a ∧ z i a ≤ b := by
  simp [siteCube, Fintype.mem_piFinset]
private theorem sum_piFinset_plaquetteBox (b : ℕ) (h : (Fin k → IntPlaquette) → ℝ) :
    ∑ p ∈ Fintype.piFinset (fun _ : Fin k => plaquetteBox b), h p =
      ∑ z ∈ siteCube k b, ∑ α : Fin k → OrderedDirectionPair, h fun i => (z i, α i) := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij' (fun p _ => ((fun i => (p i).1), (fun i => (p i).2))) (fun q _ i => (q.1 i, q.2 i))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_univ, and_true, siteCube, Fintype.mem_piFinset]
    intro i
    have := (Fintype.mem_piFinset.mp hp) i
    simp only [plaquetteBox, Finset.mem_product] at this
    exact Fintype.mem_piFinset.mp this.1
  · intro q hq
    simp only [Finset.mem_product, Finset.mem_univ, and_true, siteCube, Fintype.mem_piFinset] at hq
    simp only [Fintype.mem_piFinset, plaquetteBox, Finset.mem_product, Finset.mem_univ, and_true]
    exact hq
  · intro p _; rfl
  · intro q _; rfl
  · intro p _; rfl
private theorem roundingCell_mem_siteCube {e R : ℝ} (he : 0 < e) {b : ℕ} (hb : R / e + 1 ≤ b)
    {x : Fin k → EuclideanFourSpace} (hx : ∀ i a, |x i a| ≤ R) : roundingCell e x ∈ siteCube k b := by
  refine mem_siteCube.mpr fun i a => ?_
  have h1 : |x i a / e| ≤ R / e := by
    rw [abs_div, abs_of_pos he]; exact div_le_div_of_nonneg_right (hx i a) he.le
  obtain ⟨l, u⟩ := abs_le.mp h1
  have f1 : ((⌊x i a / e + 1 / 2⌋ : ℤ) : ℝ) ≤ x i a / e + 1 / 2 := Int.floor_le _
  have f2 : x i a / e + 1 / 2 < ((⌊x i a / e + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  simp only [roundingCell]
  generalize ⌊x i a / e + 1 / 2⌋ = n at f1 f2 ⊢
  constructor
  · have : -(b : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  · have : (n : ℝ) ≤ b := by linarith
    exact_mod_cast this
end LinkBounds
section LatticeTerms
variable {k : ℕ} [NeZero k]
private def scaledBarycenters (e : ℝ) (p : Fin k → IntPlaquette) : Fin k → EuclideanFourSpace :=
  fun i => e • intBarycenter (p i)
private def rescaledLink (e : ℝ) (P P' : IntPlaquette) : ℝ := (e⁻¹) ^ 4 * intCurvatureProjection P P'
private structure IntKernelFacts (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  abs_le_one : ∀ P P' : IntPlaquette, |intCurvatureProjection P P'| ≤ 1
  far_approx : ∀ P P' : IntPlaquette, 2 ≤ ‖intBarycenter P - intBarycenter P'‖ →
    |intCurvatureProjection P P' - linkKernel P.2 P'.2 (intBarycenter P - intBarycenter P')| ≤
      C * (‖intBarycenter P - intBarycenter P'‖ ^ 5)⁻¹
private def combinedBound (C d : ℝ) : ℝ := linkKernelBound d + (34 + C) * (d⁻¹) ^ 4
private theorem one_le_combinedBound {C d : ℝ} (hC : 0 ≤ C) (hd : 0 < d) : 1 ≤ combinedBound C d := by
  have h1 := one_le_linkKernelBound hd
  have h2 : 0 ≤ (34 + C) * (d⁻¹) ^ 4 := by positivity
  simp only [combinedBound]; linarith
private theorem norm_smul_sub_smul {e : ℝ} (he : 0 < e) (a b : EuclideanFourSpace) :
    ‖e • a - e • b‖ = e * ‖a - b‖ := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos he]
private theorem abs_rescaledLink_le {C d e : ℝ} (hK : IntKernelFacts C) (hd : 0 < d) (he : 0 < e)
    {P P' : IntPlaquette} (h : d ≤ ‖e • intBarycenter P - e • intBarycenter P'‖) :
    |rescaledLink e P P'| ≤ combinedBound C d := by
  rw [norm_smul_sub_smul he] at h
  set w := ‖intBarycenter P - intBarycenter P'‖ with hw
  have hw0 : 0 < w := by
    by_contra h0
    have : w ≤ 0 := not_lt.mp h0
    nlinarith
  have hinv : e⁻¹ ≤ w * d⁻¹ := by
    rw [inv_le_comm₀ he (by positivity), mul_inv, inv_inv]
    calc w⁻¹ * d ≤ w⁻¹ * (e * w) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = e := by field_simp
  have hp : (e⁻¹) ^ 4 ≤ (w * d⁻¹) ^ 4 := pow_le_pow_left₀ (by positivity) hinv 4
  have hC := hK.nonneg
  have hd4 : 0 ≤ (d⁻¹) ^ 4 := by positivity
  have hmain : |rescaledLink e P P'| ≤ (34 + C) * (d⁻¹) ^ 4 := by
    rw [rescaledLink, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e⁻¹) ^ 4)]
    by_cases h2 : 2 ≤ w
    · have h3 := hK.far_approx P P' h2
      have h4 : |linkKernel P.2 P'.2 (intBarycenter P - intBarycenter P')| ≤ 18 * (w⁻¹) ^ 4 :=
        abs_linkKernel_le hw0 (le_of_eq hw) _ _
      have h5 : (w ^ 5)⁻¹ ≤ (w⁻¹) ^ 4 := by
        rw [← inv_pow]
        have hw1 : w⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
        have : (w⁻¹) ^ 5 = (w⁻¹) ^ 4 * w⁻¹ := by ring
        rw [this]
        exact mul_le_of_le_one_right (by positivity) hw1
      have h6 : |intCurvatureProjection P P'| ≤ (18 + C) * (w⁻¹) ^ 4 := by
        have h7 : C * (w ^ 5)⁻¹ ≤ C * (w⁻¹) ^ 4 := mul_le_mul_of_nonneg_left h5 hC
        obtain ⟨a1, a2⟩ := abs_le.mp h3
        obtain ⟨b1, b2⟩ := abs_le.mp h4
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      calc (e⁻¹) ^ 4 * |intCurvatureProjection P P'| ≤ (w * d⁻¹) ^ 4 * ((18 + C) * (w⁻¹) ^ 4) :=
            mul_le_mul hp h6 (abs_nonneg _) (by positivity)
        _ = (18 + C) * (d⁻¹) ^ 4 := by field_simp
        _ ≤ (34 + C) * (d⁻¹) ^ 4 := mul_le_mul_of_nonneg_right (by linarith) hd4
    · have h3 := hK.abs_le_one P P'
      have hw2 : w ≤ 2 := (not_le.mp h2).le
      calc (e⁻¹) ^ 4 * |intCurvatureProjection P P'| ≤ (w * d⁻¹) ^ 4 * 1 :=
            mul_le_mul hp h3 (abs_nonneg _) (by positivity)
        _ ≤ (2 * d⁻¹) ^ 4 * 1 := by
            rw [mul_one, mul_one]
            exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hw2 (by positivity)) 4
        _ = 16 * (d⁻¹) ^ 4 := by ring
        _ ≤ (34 + C) * (d⁻¹) ^ 4 := mul_le_mul_of_nonneg_right (by linarith) hd4
  have := one_le_linkKernelBound hd
  simp only [combinedBound]; linarith
private theorem linkKernel_smul (hF : InversionMatrixProperties) {e : ℝ} (he : 0 < e)
    (α β : OrderedDirectionPair) (v : EuclideanFourSpace) :
    linkKernel α β (e • v) = (e⁻¹) ^ 4 * linkKernel α β v := by
  simp only [linkKernel, radialWeight_smul he]
  rw [hF.2.2.2.1 e v he.ne']
  ring
private theorem abs_rescaledLink_sub_linkKernel_le (hF : InversionMatrixProperties) {C d e : ℝ}
    (hK : IntKernelFacts C) (hd : 0 < d) (he : 0 < e) (h2 : 2 * e ≤ d) {P P' : IntPlaquette}
    (h : d ≤ ‖e • intBarycenter P - e • intBarycenter P'‖) :
    |rescaledLink e P P' - linkKernel P.2 P'.2 (e • intBarycenter P - e • intBarycenter P')| ≤
      C * (d⁻¹) ^ 5 * e := by
  rw [norm_smul_sub_smul he] at h
  set w := ‖intBarycenter P - intBarycenter P'‖ with hw
  have hw2 : 2 ≤ w := by
    by_contra h0
    have : w < 2 := not_le.mp h0
    nlinarith
  have hw0 : 0 < w := by linarith
  have hinv : w⁻¹ ≤ e * d⁻¹ := by
    rw [inv_le_comm₀ hw0 (by positivity), mul_inv, inv_inv]
    calc e⁻¹ * d ≤ e⁻¹ * (e * w) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = w := by field_simp
  have e1 : rescaledLink e P P' - linkKernel P.2 P'.2 (e • intBarycenter P - e • intBarycenter P') =
      (e⁻¹) ^ 4 * (intCurvatureProjection P P' - linkKernel P.2 P'.2 (intBarycenter P - intBarycenter P')) := by
    rw [← smul_sub, linkKernel_smul hF he, rescaledLink]; ring
  rw [e1, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e⁻¹) ^ 4)]
  have h3 := hK.far_approx P P' hw2
  have h5 : (w ^ 5)⁻¹ ≤ (e * d⁻¹) ^ 5 := by
    rw [← inv_pow]; exact pow_le_pow_left₀ (by positivity) hinv 5
  calc (e⁻¹) ^ 4 * |intCurvatureProjection P P' - linkKernel P.2 P'.2 (intBarycenter P - intBarycenter P')|
      ≤ (e⁻¹) ^ 4 * (C * (e * d⁻¹) ^ 5) :=
        mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h5 hK.nonneg)) (by positivity)
    _ = C * (d⁻¹) ^ 5 * e := by field_simp
private theorem prod_intCurvature_eq {e : ℝ} (he : 0 < e) (σ : Equiv.Perm (Fin k)) (p : Fin k → IntPlaquette) :
    ∏ c : Fin k, intCurvatureProjection (p (σ c)) (p (σ (c + 1))) =
      e ^ (4 * k) * ∏ c : Fin k, rescaledLink e (p (σ c)) (p (σ (c + 1))) := by
  have h : ∀ c : Fin k, intCurvatureProjection (p (σ c)) (p (σ (c + 1))) =
      e ^ 4 * rescaledLink e (p (σ c)) (p (σ (c + 1))) := by
    intro c
    simp only [rescaledLink]
    field_simp
  simp only [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pow_mul]
private theorem abs_latticeTerm_le {R C d e : ℝ} {φ : Fin k → EuclideanFourSpace → ℝ} (hφ : IsSupTestFamily R d φ)
    (hk : 2 ≤ k) (hK : IntKernelFacts C) (hd : 0 < d) (he : 0 < e) (σ : Equiv.Perm (Fin k))
    (p : Fin k → IntPlaquette) :
    |testProduct φ (scaledBarycenters e p) * ∏ c : Fin k, intCurvatureProjection (p (σ c)) (p (σ (c + 1)))| ≤
      e ^ (4 * k) * combinedBound C d ^ k := by
  have hM := one_le_combinedBound hK.nonneg hd
  by_cases h0 : testProduct φ (scaledBarycenters e p) = 0
  · rw [h0]; simp only [zero_mul, abs_zero]; positivity
  rw [prod_intCurvature_eq he, abs_mul]
  have h1 := abs_testProduct_le_one hφ (scaledBarycenters e p)
  have h2 : |e ^ (4 * k) * ∏ c : Fin k, rescaledLink e (p (σ c)) (p (σ (c + 1)))| ≤
      e ^ (4 * k) * combinedBound C d ^ k := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < e ^ (4 * k))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := abs_prod_le_pow Finset.univ (fun c : Fin k => rescaledLink e (p (σ c)) (p (σ (c + 1))))
      (M := combinedBound C d)
      (fun c _ => abs_rescaledLink_le hK hd he (le_norm_link_of_testProduct_ne_zero hφ hk h0 σ c))
    simpa using this
  calc _ ≤ 1 * (e ^ (4 * k) * combinedBound C d ^ k) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = _ := one_mul _
private theorem abs_latticeTerm_sub_le (hF : InversionMatrixProperties) {R C d e : ℝ}
    {φ : Fin k → EuclideanFourSpace → ℝ} (hφ : IsSupTestFamily R d φ) (hk : 2 ≤ k) (hK : IntKernelFacts C)
    (hd : 0 < d) (he : 0 < e) (h2 : 2 * e ≤ d) (σ : Equiv.Perm (Fin k)) (p : Fin k → IntPlaquette) :
    |testProduct φ (scaledBarycenters e p) * ∏ c : Fin k, intCurvatureProjection (p (σ c)) (p (σ (c + 1))) -
        e ^ (4 * k) * (testProduct φ (scaledBarycenters e p) *
          cycleKernelProduct σ (fun i => (p i).2) (scaledBarycenters e p))| ≤
      e ^ (4 * k) * (k * combinedBound C d ^ k * (C * (d⁻¹) ^ 5 * e)) := by
  have hM := one_le_combinedBound hK.nonneg hd
  have hX : 0 ≤ C * (d⁻¹) ^ 5 * e := mul_nonneg (mul_nonneg hK.nonneg (by positivity)) he.le
  by_cases h0 : testProduct φ (scaledBarycenters e p) = 0
  · rw [h0]; simp only [zero_mul, mul_zero, sub_zero, abs_zero]; positivity
  rw [prod_intCurvature_eq he]
  have e1 : testProduct φ (scaledBarycenters e p) *
        (e ^ (4 * k) * ∏ c : Fin k, rescaledLink e (p (σ c)) (p (σ (c + 1)))) -
      e ^ (4 * k) * (testProduct φ (scaledBarycenters e p) *
        cycleKernelProduct σ (fun i => (p i).2) (scaledBarycenters e p)) =
      e ^ (4 * k) * (testProduct φ (scaledBarycenters e p) *
        ((∏ c : Fin k, rescaledLink e (p (σ c)) (p (σ (c + 1)))) -
          cycleKernelProduct σ (fun i => (p i).2) (scaledBarycenters e p))) := by ring
  rw [e1, abs_mul, abs_of_pos (by positivity : 0 < e ^ (4 * k))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [abs_mul]
  have h1 := abs_testProduct_le_one hφ (scaledBarycenters e p)
  have hsep := le_norm_link_of_testProduct_ne_zero hφ hk h0 σ
  have hpsi : ∀ c : Fin k, |linkKernel (p (σ c)).2 (p (σ (c + 1))).2
      (scaledBarycenters e p (σ c) - scaledBarycenters e p (σ (c + 1)))| ≤ combinedBound C d := fun c => by
    have := abs_linkKernel_le_bound hd (hsep c) (p (σ c)).2 (p (σ (c + 1))).2
    have h3 : 0 ≤ (34 + C) * (d⁻¹) ^ 4 := by have := hK.nonneg; positivity
    simp only [combinedBound]; linarith
  have h3 := abs_prod_sub_prod_le Finset.univ (fun c : Fin k => rescaledLink e (p (σ c)) (p (σ (c + 1))))
    (fun c : Fin k => linkKernel (p (σ c)).2 (p (σ (c + 1))).2
      (scaledBarycenters e p (σ c) - scaledBarycenters e p (σ (c + 1))))
    (M := combinedBound C d) (δ := C * (d⁻¹) ^ 5 * e) hM hX
    (fun c _ => abs_rescaledLink_le hK hd he (hsep c)) (fun c _ => hpsi c)
    (fun c _ => abs_rescaledLink_sub_linkKernel_le hF hK hd he h2 (hsep c))
  have h4 : |(∏ c : Fin k, rescaledLink e (p (σ c)) (p (σ (c + 1)))) -
      cycleKernelProduct σ (fun i => (p i).2) (scaledBarycenters e p)| ≤
      k * combinedBound C d ^ k * (C * (d⁻¹) ^ 5 * e) := by
    simpa [cycleKernelProduct] using h3
  calc _ ≤ 1 * (k * combinedBound C d ^ k * (C * (d⁻¹) ^ 5 * e)) := mul_le_mul h1 h4 (abs_nonneg _) zero_le_one
    _ = _ := one_mul _
private theorem norm_sub_scaledBarycenter_roundingCell_le {e : ℝ} (he : 0 < e) {x : Fin k → EuclideanFourSpace}
    (i : Fin k) (β : OrderedDirectionPair) :
    ‖x i - e • intBarycenter (roundingCell e x i, β)‖ ≤ 3 * e := by
  have h : ‖x i - e • intBarycenter (roundingCell e x i, β)‖ ≤ 2 * (3 / 2 * e) := by
    refine norm_le_two_mul_of_abs_apply_le _ _ fun a => ?_
    have f1 : ((⌊x i a / e + 1 / 2⌋ : ℤ) : ℝ) ≤ x i a / e + 1 / 2 := Int.floor_le _
    have f2 : x i a / e + 1 / 2 < ((⌊x i a / e + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hy : x i a = e * (x i a / e) := by field_simp
    simp only [intBarycenter, roundingCell, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    generalize ⌊x i a / e + 1 / 2⌋ = n at f1 f2 ⊢
    generalize x i a / e = t at hy f1 f2
    rw [hy]
    have o1 : (0 : ℝ) ≤ (if a = β.1.1 then 1 / 2 else 0) := by split_ifs <;> norm_num
    have o2 : (if a = β.1.1 then (1 : ℝ) / 2 else 0) ≤ 1 / 2 := by split_ifs <;> norm_num
    have o3 : (0 : ℝ) ≤ (if a = β.1.2 then 1 / 2 else 0) := by split_ifs <;> norm_num
    have o4 : (if a = β.1.2 then (1 : ℝ) / 2 else 0) ≤ 1 / 2 := by split_ifs <;> norm_num
    generalize (if a = β.1.1 then (1 : ℝ) / 2 else 0) = u at o1 o2 ⊢
    generalize (if a = β.1.2 then (1 : ℝ) / 2 else 0) = u' at o3 o4 ⊢
    have e2 : e * t - e * ((n : ℝ) + u + u') = e * (t - n - u - u') := by ring
    rw [e2, abs_mul, abs_of_pos he, mul_comm (3 / 2 : ℝ) e]
    refine mul_le_mul_of_nonneg_left ?_ he.le
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  linarith
private theorem abs_sum_sum_le_card_mul {A B : Type} [Fintype B] (S : Finset A) (f : A → B → ℝ) (X : ℝ)
    (h : ∀ z ∈ S, ∀ α, |f z α| ≤ X) : |∑ z ∈ S, ∑ α, f z α| ≤ S.card * (Fintype.card B * X) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ z ∈ S, |∑ α, f z α| ≤ Fintype.card B * X := fun z hz => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ α, |f z α| ≤ ∑ _α : B, X := Finset.sum_le_sum fun α _ => h z hz α
      _ = _ := by simp
  calc _ ≤ ∑ _z ∈ S, (Fintype.card B * X) := Finset.sum_le_sum h1
    _ = _ := by simp
private theorem scaled_card_siteCube_le {R : ℝ} (hR : 0 ≤ R) {T : ℝ} (hT : 1 ≤ T) :
    (T⁻¹) ^ (4 * k) * ((siteCube k (⌈R * T⌉₊ + 2)).card : ℝ) ≤ (2 * R + 7) ^ (4 * k) := by
  rw [card_siteCube, Nat.cast_pow, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  have h1 : ((⌈R * T⌉₊ : ℕ) : ℝ) < R * T + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : (((2 * (⌈R * T⌉₊ + 2) + 1 : ℕ)) : ℝ) ≤ (2 * R + 7) * T := by
    push_cast
    nlinarith
  calc T⁻¹ * (((2 * (⌈R * T⌉₊ + 2) + 1 : ℕ)) : ℝ) ≤ T⁻¹ * ((2 * R + 7) * T) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * R + 7 := by field_simp
end LatticeTerms
section Approximation
variable {k : ℕ} [NeZero k]
private def orderLatticeSum (L s b : ℕ) (φ : Fin k → EuclideanFourSpace → ℝ) (σ : Equiv.Perm (Fin k)) : ℝ :=
  ∑ p ∈ Fintype.piFinset (fun _ : Fin k => plaquetteBox b),
    (∏ i, scaledWeight L s (φ i) (p i)) * ∏ c : Fin k, intCurvatureProjection (p (σ c)) (p (σ (c + 1)))
private def orderIntegral (φ : Fin k → EuclideanFourSpace → ℝ) (σ : Equiv.Perm (Fin k)) : ℝ :=
  ∫ x : Fin k → EuclideanFourSpace, (∏ i, φ i (x i)) * cycleKernel σ x
private def planeChoices (k : ℕ) : ℝ := (Fintype.card (Fin k → OrderedDirectionPair) : ℝ)
private theorem planeChoices_nonneg (k : ℕ) : 0 ≤ planeChoices k := Nat.cast_nonneg _
private theorem orderLatticeSum_eq (L s b : ℕ) (φ : Fin k → EuclideanFourSpace → ℝ) (σ : Equiv.Perm (Fin k)) :
    orderLatticeSum L s b φ σ = ∑ z ∈ siteCube k b, ∑ α : Fin k → OrderedDirectionPair,
      testProduct φ (scaledBarycenters ((L : ℝ) ^ s)⁻¹ fun i => (z i, α i)) *
        ∏ c : Fin k, intCurvatureProjection ((z (σ c), α (σ c)) : IntPlaquette) (z (σ (c + 1)), α (σ (c + 1))) := by
  rw [orderLatticeSum, sum_piFinset_plaquetteBox]
  rfl
private theorem abs_orderLatticeSum_le {R C d : ℝ} {φ : Fin k → EuclideanFourSpace → ℝ}
    (hφ : IsSupTestFamily R d φ) (hk : 2 ≤ k) (hR : 0 ≤ R) (hK : IntKernelFacts C) (hd : 0 < d) {L s : ℕ}
    (hL : 1 ≤ L) (σ : Equiv.Perm (Fin k)) :
    |orderLatticeSum L s (⌈R * (L : ℝ) ^ s⌉₊ + 2) φ σ| ≤
      (2 * R + 7) ^ (4 * k) * (planeChoices k * combinedBound C d ^ k) := by
  have hT : (1 : ℝ) ≤ (L : ℝ) ^ s := one_le_pow₀ (by exact_mod_cast hL)
  set e := ((L : ℝ) ^ s)⁻¹ with he
  have he0 : 0 < e := by positivity
  rw [orderLatticeSum_eq]
  refine (abs_sum_sum_le_card_mul _ _ (e ^ (4 * k) * combinedBound C d ^ k) fun z _ α =>
    abs_latticeTerm_le hφ hk hK hd he0 σ fun i => (z i, α i)).trans ?_
  have hv := scaled_card_siteCube_le (k := k) hR hT
  have hM : 0 ≤ combinedBound C d ^ k :=
    pow_nonneg ((zero_le_one).trans (one_le_combinedBound hK.nonneg hd)) k
  calc ((siteCube k (⌈R * (L : ℝ) ^ s⌉₊ + 2)).card : ℝ) *
        ((Fintype.card (Fin k → OrderedDirectionPair) : ℝ) * (e ^ (4 * k) * combinedBound C d ^ k))
      = (e ^ (4 * k) * ((siteCube k (⌈R * (L : ℝ) ^ s⌉₊ + 2)).card : ℝ)) *
          (planeChoices k * combinedBound C d ^ k) := by
        simp only [planeChoices]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hv (mul_nonneg (planeChoices_nonneg k) hM)
private theorem integrable_orderIntegrand (hI : CycleIntegrandIntegrable) {R d : ℝ}
    {φ : Fin k → EuclideanFourSpace → ℝ} (hφ : IsSupTestFamily R d φ) (hk : 2 ≤ k) (hR : 0 ≤ R) (hd : 0 < d)
    (σ : Equiv.Perm (Fin k)) :
    Integrable fun x : Fin k → EuclideanFourSpace => (∏ i, φ i (x i)) * cycleKernel σ x := by
  refine hI k hk (2 * R) d φ hd ⟨fun i => ?_, hφ.abs_le_one, fun i => ?_, fun i j hij x hx y hy => ?_⟩ σ
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm]
    simpa using (hφ.lipschitz i x y).trans (supDist_le_norm_sub x y)
  · intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_two_mul_of_abs_apply_le _ _ (hφ.abs_coord_le i x hx)
  · rw [dist_eq_norm]
    exact (hφ.le_supDist i j hij x hx y hy).trans (supDist_le_norm_sub x y)
private theorem abs_coord_le_of_orderIntegrand_ne_zero {R d : ℝ} {φ : Fin k → EuclideanFourSpace → ℝ}
    (hφ : IsSupTestFamily R d φ) (σ : Equiv.Perm (Fin k)) {x : Fin k → EuclideanFourSpace}
    (h : (∏ i, φ i (x i)) * cycleKernel σ x ≠ 0) (i : Fin k) (a : Fin 4) : |x i a| ≤ R :=
  hφ.abs_coord_le i _ (subset_tsupport _ (apply_ne_zero_of_testProduct_ne_zero (left_ne_zero_of_mul h) i)) a
private theorem abs_orderIntegral_le (hI : CycleIntegrandIntegrable) {R d : ℝ}
    {φ : Fin k → EuclideanFourSpace → ℝ} (hφ : IsSupTestFamily R d φ) (hk : 2 ≤ k) (hR : 0 ≤ R) (hd : 0 < d)
    (σ : Equiv.Perm (Fin k)) :
    |orderIntegral φ σ| ≤ planeChoices k * linkKernelBound d ^ k * ((siteCube k (⌈R * 1⌉₊ + 2)).card : ℝ) := by
  have h := abs_riemannSum_sub_integral_le (k := k) (e := 1) one_pos _
    (integrable_orderIntegrand hI hφ hk hR hd σ) (siteCube k (⌈R * 1⌉₊ + 2))
    (fun _ => 0) (δ := planeChoices k * linkKernelBound d ^ k)
    (fun x hx => roundingCell_mem_siteCube one_pos (by
      have := Nat.le_ceil (R * 1)
      push_cast
      simp only [mul_one, div_one] at this ⊢
      linarith) (abs_coord_le_of_orderIntegrand_ne_zero hφ σ hx))
    (fun z _ x _ => by
      rw [zero_sub, abs_neg, testProduct_mul_cycleKernel_eq]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hb : ∀ α : Fin k → OrderedDirectionPair,
          |testProduct φ x * cycleKernelProduct σ α x| ≤ linkKernelBound d ^ k := fun α => by
        by_cases h0 : testProduct φ x = 0
        · rw [h0]; simp only [zero_mul, abs_zero]
          exact pow_nonneg ((zero_le_one).trans (one_le_linkKernelBound hd)) k
        · rw [abs_mul]
          calc _ ≤ 1 * linkKernelBound d ^ k := mul_le_mul (abs_testProduct_le_one hφ x)
                (abs_cycleKernelProduct_le hd σ α (le_norm_link_of_testProduct_ne_zero hφ hk h0 σ))
                (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
      calc _ ≤ ∑ _α : Fin k → OrderedDirectionPair, linkKernelBound d ^ k := Finset.sum_le_sum fun α _ => hb α
        _ = _ := by simp [planeChoices])
  simpa [orderIntegral] using h
private theorem abs_orderLatticeSum_sub_orderIntegral_le (hF : InversionMatrixProperties)
    (hI : CycleIntegrandIntegrable) {R C d : ℝ} {φ : Fin k → EuclideanFourSpace → ℝ} (hφ : IsSupTestFamily R d φ)
    (hk : 2 ≤ k) (hR : 0 ≤ R) (hK : IntKernelFacts C) (hd : 0 < d) {L s : ℕ} (hL : 1 ≤ L)
    (h12 : 12 * ((L : ℝ) ^ s)⁻¹ ≤ d) (σ : Equiv.Perm (Fin k)) :
    |orderLatticeSum L s (⌈R * (L : ℝ) ^ s⌉₊ + 2) φ σ - orderIntegral φ σ| ≤
      (2 * R + 7) ^ (4 * k) * (planeChoices k * (k * combinedBound C d ^ k * (C * (d⁻¹) ^ 5)) +
        planeChoices k * cellLipschitzConst k d * 3) * ((L : ℝ) ^ s)⁻¹ := by
  have hT : (1 : ℝ) ≤ (L : ℝ) ^ s := one_le_pow₀ (by exact_mod_cast hL)
  set b := ⌈R * (L : ℝ) ^ s⌉₊ + 2 with hb
  set e := ((L : ℝ) ^ s)⁻¹ with he
  have he0 : 0 < e := by positivity
  have hv := scaled_card_siteCube_le (k := k) hR hT
  rw [← hb, ← he] at hv
  set g : (Fin k → Fin 4 → ℤ) → ℝ := fun z => ∑ α : Fin k → OrderedDirectionPair,
    testProduct φ (scaledBarycenters e fun i => (z i, α i)) *
      cycleKernelProduct σ α (scaledBarycenters e fun i => (z i, α i)) with hg
  have hC := hK.nonneg
  have step1 : |orderLatticeSum L s b φ σ - e ^ (4 * k) * ∑ z ∈ siteCube k b, g z| ≤
      ((siteCube k b).card : ℝ) * ((Fintype.card (Fin k → OrderedDirectionPair) : ℝ) *
        (e ^ (4 * k) * (k * combinedBound C d ^ k * (C * (d⁻¹) ^ 5 * e)))) := by
    rw [orderLatticeSum_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [hg, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine abs_sum_sum_le_card_mul _ _ _ fun z _ α => ?_
    exact abs_latticeTerm_sub_le hF hφ hk hK hd he0 (by linarith) σ fun i => (z i, α i)
  have step2 : |e ^ (4 * k) * ∑ z ∈ siteCube k b, g z - orderIntegral φ σ| ≤
      (planeChoices k * (cellLipschitzConst k d * (3 * e))) * e ^ (4 * k) * ((siteCube k b).card : ℝ) := by
    refine abs_riemannSum_sub_integral_le he0 _ (integrable_orderIntegrand hI hφ hk hR hd σ) (siteCube k b) g ?_ ?_
    · intro x hx
      refine roundingCell_mem_siteCube he0 ?_ (abs_coord_le_of_orderIntegrand_ne_zero hφ σ hx)
      have := Nat.le_ceil (R * (L : ℝ) ^ s)
      have e1 : R / e = R * (L : ℝ) ^ s := by rw [he, div_inv_eq_mul]
      rw [e1, hb]
      push_cast
      linarith
    · intro z _ x hz
      rw [testProduct_mul_cycleKernel_eq, hg]
      simp only
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hb' : ∀ α : Fin k → OrderedDirectionPair, |testProduct φ (scaledBarycenters e fun i => (z i, α i)) *
          cycleKernelProduct σ α (scaledBarycenters e fun i => (z i, α i)) -
            testProduct φ x * cycleKernelProduct σ α x| ≤ cellLipschitzConst k d * (3 * e) :=
        fun α => abs_cycleTerm_sub_le hφ hk hd σ α (by positivity) (by linarith) fun i => by
          have := norm_sub_scaledBarycenter_roundingCell_le he0 (x := x) i (α i)
          rw [hz] at this
          rw [norm_sub_rev]
          exact this
      calc _ ≤ ∑ _α : Fin k → OrderedDirectionPair, cellLipschitzConst k d * (3 * e) :=
            Finset.sum_le_sum fun α _ => hb' α
        _ = _ := by simp [planeChoices]
  have e1 : orderLatticeSum L s b φ σ - orderIntegral φ σ =
      (orderLatticeSum L s b φ σ - e ^ (4 * k) * ∑ z ∈ siteCube k b, g z) +
      (e ^ (4 * k) * ∑ z ∈ siteCube k b, g z - orderIntegral φ σ) := by ring
  rw [e1]
  refine (abs_add_le _ _).trans ?_
  have hA : 0 ≤ planeChoices k * (k * combinedBound C d ^ k * (C * (d⁻¹) ^ 5)) +
      planeChoices k * cellLipschitzConst k d * 3 := by
    have := one_le_combinedBound hC hd
    have := cellLipschitzConst_nonneg k hd
    have := planeChoices_nonneg k
    positivity
  calc _ ≤ (e ^ (4 * k) * ((siteCube k b).card : ℝ)) *
        ((planeChoices k * (k * combinedBound C d ^ k * (C * (d⁻¹) ^ 5)) +
          planeChoices k * cellLipschitzConst k d * 3) * e) := by
        refine (add_le_add step1 step2).trans (le_of_eq ?_)
        simp only [planeChoices]; ring
    _ ≤ (2 * R + 7) ^ (4 * k) *
        ((planeChoices k * (k * combinedBound C d ^ k * (C * (d⁻¹) ^ 5)) +
          planeChoices k * cellLipschitzConst k d * 3) * e) :=
        mul_le_mul_of_nonneg_right hv (by positivity)
    _ = _ := by ring
end Approximation
private theorem three_mul_le_of_nonneg_add {N A E : ℝ} (hN : 0 ≤ N) (hE : 0 ≤ E) :
    3 * (N * A) ≤ 3 * N * (A + E) := by
  nlinarith [mul_nonneg hN hE]
private theorem three_mul_le_mul_of_nonneg_add {N A E e : ℝ} (hN : 0 ≤ N) (hA : 0 ≤ A) (he : 0 ≤ e) :
    3 * (N * (E * e)) ≤ 3 * N * (A + E) * e := by
  have : 0 ≤ N * A * e := mul_nonneg (mul_nonneg hN hA) he
  nlinarith
private theorem le_add_mul_mul_of_one_le {x S D e u : ℝ} (hx : x ≤ S) (hS : 0 ≤ S) (hu : 1 ≤ u * e) (hD : 0 ≤ D)
    (he : 0 ≤ e) : x ≤ (D + S * u) * e := by
  have h5 : S * 1 ≤ S * (u * e) := mul_le_mul_of_nonneg_left hu hS
  have h6 : 0 ≤ D * e := mul_nonneg hD he
  nlinarith
theorem latticeCycleSumApprox_of_kernelBounds (hK : curvatureKernelBoundsStatement)
    (hI : CycleIntegrandIntegrable) (hF : InversionMatrixProperties) :
    latticeCycleSumApproxStatement := by
  intro k _ hk R d hR hd
  obtain ⟨C₀, hC₀⟩ := hK
  obtain ⟨-, h1, -, h3⟩ := hC₀ 1
  have hFacts : IntKernelFacts |C₀| := ⟨abs_nonneg _, h1, fun P P' hfar => by
    refine (h3 P P' hfar).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))⟩
  set C := |C₀| with hCdef
  have hC := hFacts.nonneg
  set A : ℝ := (2 * R + 7) ^ (4 * k) * (planeChoices k * combinedBound C d ^ k) with hA
  set B : ℝ := planeChoices k * linkKernelBound d ^ k * ((siteCube k (⌈R * 1⌉₊ + 2)).card : ℝ) with hB
  set D : ℝ := (2 * R + 7) ^ (4 * k) * (planeChoices k * (k * combinedBound C d ^ k * (C * (d⁻¹) ^ 5)) +
    planeChoices k * cellLipschitzConst k d * 3) with hD
  have hj := one_le_combinedBound hC hd
  have hl := one_le_linkKernelBound hd
  have hcc := cellLipschitzConst_nonneg k hd
  have hp := planeChoices_nonneg k
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hD0 : 0 ≤ D := by positivity
  set E : ℝ := D + (A + B) * (12 * d⁻¹) with hE
  have hE0 : 0 ≤ E := by positivity
  set N : ℝ := ((unorientedCyclicOrders k).card : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨3 * N * (A + E), fun φ L s hL hφ => ?_⟩
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  have hT : (1 : ℝ) ≤ (L : ℝ) ^ s := one_le_pow₀ hL1
  have hrp : (L : ℝ) ^ (-(s : ℝ)) = ((L : ℝ) ^ s)⁻¹ := by
    rw [Real.rpow_neg hLpos.le, Real.rpow_natCast]
  rw [hrp]
  set e := ((L : ℝ) ^ s)⁻¹ with he
  have he0 : 0 < e := by positivity
  set b := ⌈R * (L : ℝ) ^ s⌉₊ + 2 with hb
  have hcoef : |3 * (if k = 2 then (1 : ℝ) / 2 else 1)| ≤ 3 := by
    split_ifs <;> norm_num
  have hnum : latticeCycleSum L s b φ =
      3 * (if k = 2 then 1 / 2 else 1) * ∑ σ ∈ unorientedCyclicOrders k, orderLatticeSum L s b φ σ := rfl
  have hform : cyclicMomentFormula k φ =
      3 * (if k = 2 then 1 / 2 else 1) * ∑ σ ∈ unorientedCyclicOrders k, orderIntegral φ σ := rfl
  have hin : ∀ σ, |orderLatticeSum L s b φ σ| ≤ A := fun σ => abs_orderLatticeSum_le hφ hk hR hFacts hd hL σ
  have hint : ∀ σ, |orderIntegral φ σ| ≤ B := fun σ => abs_orderIntegral_le hI hφ hk hR hd σ
  have hdiff : ∀ σ, |orderLatticeSum L s b φ σ - orderIntegral φ σ| ≤ E * e := by
    intro σ
    by_cases h12 : 12 * e ≤ d
    · have := abs_orderLatticeSum_sub_orderIntegral_le hF hI hφ hk hR hFacts hd hL h12 σ
      refine this.trans (mul_le_mul_of_nonneg_right ?_ he0.le)
      have h9 : 0 ≤ (A + B) * (12 * d⁻¹) := by positivity
      exact le_add_of_nonneg_right h9
    · have h2 : d < 12 * e := not_le.mp h12
      have h3 : 1 ≤ 12 * d⁻¹ * e := by
        have : 12 * d⁻¹ * e = (12 * e) / d := by field_simp
        rw [this]
        exact (one_le_div hd).mpr h2.le
      have h4 : |orderLatticeSum L s b φ σ - orderIntegral φ σ| ≤ A + B := by
        refine (abs_sub _ _).trans (add_le_add (hin σ) (hint σ))
      exact le_add_mul_mul_of_one_le h4 (add_nonneg hA0 hB0) h3 hD0 he0.le
  constructor
  · rw [hnum, abs_mul]
    have h1 : |∑ σ ∈ unorientedCyclicOrders k, orderLatticeSum L s b φ σ| ≤ N * A := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _σ ∈ unorientedCyclicOrders k, A := Finset.sum_le_sum fun σ _ => hin σ
        _ = _ := by simp [hN]
    calc _ ≤ 3 * (N * A) := mul_le_mul hcoef h1 (abs_nonneg _) (by norm_num)
      _ ≤ 3 * N * (A + E) := three_mul_le_of_nonneg_add hN0 hE0
  · rw [hnum, hform, ← mul_sub, abs_mul, ← Finset.sum_sub_distrib]
    have h1 : |∑ σ ∈ unorientedCyclicOrders k, (orderLatticeSum L s b φ σ - orderIntegral φ σ)| ≤ N * (E * e) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _σ ∈ unorientedCyclicOrders k, E * e := Finset.sum_le_sum fun σ _ => hdiff σ
        _ = _ := by simp [hN]
    calc _ ≤ 3 * (N * (E * e)) := mul_le_mul hcoef h1 (abs_nonneg _) (by norm_num)
      _ ≤ 3 * N * (A + E) * e := three_mul_le_mul_of_nonneg_add hN0 hA0 he0.le
end YangMills.Construction.MomentLaw
end
