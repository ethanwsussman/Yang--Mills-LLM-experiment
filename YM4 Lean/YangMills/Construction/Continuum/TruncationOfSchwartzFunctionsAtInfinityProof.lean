import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import YangMills.Construction.Continuum.RulesOfThePartialDerivatives
import YangMills.Construction.Continuum.TruncationOfSchwartzFunctionsAtInfinity
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces.SchwartzTruncation
open BumpApprox DerivRules
variable {n : ℕ}
def toEuclidean (x : PointTuple n) : EuclideanSpace ℝ (Fin n × Fin 4) :=
  WithLp.toLp 2 fun p => x p.1 p.2
theorem norm_toEuclidean (x : PointTuple n) : ‖toEuclidean x‖ = tupleNorm x := by
  simp [toEuclidean, EuclideanSpace.norm_eq, tupleNorm, Fintype.sum_prod_type]
theorem tupleNorm_add_le (x y : PointTuple n) :
    tupleNorm (x + y) ≤ tupleNorm x + tupleNorm y := by
  have hsplit : toEuclidean (x + y) = toEuclidean x + toEuclidean y := by
    ext p
    simp [toEuclidean]
  rw [← norm_toEuclidean, ← norm_toEuclidean, ← norm_toEuclidean, hsplit]
  exact norm_add_le _ _
theorem tupleNorm_sub_comm (x y : PointTuple n) :
    tupleNorm (x - y) = tupleNorm (y - x) := by apply _root_.YangMills.SharedProofs.p39081 <;> assumption
theorem continuous_tupleNorm : Continuous (tupleNorm : PointTuple n → ℝ) := by
  unfold tupleNorm
  fun_prop
theorem abs_coord_le_tupleNorm (x : PointTuple n) (i : Fin n) (μ : Fin 4) :
    |x i μ| ≤ tupleNorm x := by apply _root_.YangMills.SharedProofs.p97156 <;> assumption
theorem hasCompactSupport_of_eq_zero_far (g : PointTuple n → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hg : ∀ x, R ≤ tupleNorm x → g x = 0) : HasCompactSupport g := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : PointTuple n) R) fun x hx => hg x ?_
  by_contra hlt
  apply hx
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg hR).2 fun i => (pi_norm_le_iff_of_nonneg hR).2 fun μ => ?_
  rw [Real.norm_eq_abs]
  exact (abs_coord_le_tupleNorm x i μ).trans (not_le.1 hlt).le
theorem idxOrder_mono {α γ : MultiIdx4 n} (h : γ ≤ α) : idxOrder γ ≤ idxOrder α :=
  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ => h i μ
theorem idxOrder_sub_le (α γ : MultiIdx4 n) : idxOrder (α - γ) ≤ idxOrder α :=
  Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Nat.sub_le _ _
theorem le_const_of_idxOrder_le {γ : MultiIdx4 n} {k : ℕ} (h : idxOrder γ ≤ k) :
    γ ≤ fun _ _ => k := by
  intro i μ
  refine le_trans ?_ h
  exact (Finset.single_le_sum (f := fun μ => γ i μ) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ μ)).trans
    (Finset.single_le_sum (f := fun i => ∑ μ, γ i μ) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i))
theorem schwartzTruncationApprox_holds (hRules : DerivRules.Combined)
    (hBumps : BumpApprox.BumpLemma) :
    SchwartzTruncationApprox := by
  intro n k hn hk V φ hφ hflat ε hε
  obtain ⟨-, hRulesC, hLeibniz, hBinom⟩ := hRules
  obtain ⟨j, hj⟩ := (hBumps n hn).1
  have hFacts := (hBumps n hn).2.1 j hj
  have hφs := hφ.1
  have hMfin : weightedSeminorm (k + 1) φ ≠ ⊤ := (hφ.2 (k + 1) (Nat.succ_pos k)).ne
  obtain ⟨C, hCnn, hCγ⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : MultiIdx4 n, idxOrder γ ≤ k → derivL1Mass j γ ≤ C := by
    have hC0 : ∀ γ : MultiIdx4 n, 0 ≤ derivL1Mass j γ :=
      fun γ => MeasureTheory.integral_nonneg fun x => abs_nonneg _
    refine ⟨∑ γ ∈ Finset.Icc (0 : MultiIdx4 n) (fun _ _ => k), derivL1Mass j γ,
      Finset.sum_nonneg fun γ _ => hC0 γ, fun γ hγ => ?_⟩
    exact Finset.single_le_sum (f := fun γ => derivL1Mass j γ) (fun γ _ => hC0 γ)
      (Finset.mem_Icc.2 ⟨fun i μ => Nat.zero_le _, le_const_of_idxOrder_le hγ⟩)
  obtain ⟨M, hMnn, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ M = (weightedSeminorm (k + 1) φ).toReal :=
    ⟨_, ENNReal.toReal_nonneg, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = 1 + 2 ^ k * C * M / ε := ⟨_, rfl⟩
  have hT : 0 ≤ 2 ^ k * C * M / ε := by positivity
  have hr1 : 1 ≤ r := by rw [hrdef]; linarith
  have hr : 0 < r := by linarith
  have hWopen : IsOpen {x : PointTuple n | 3 * r < tupleNorm x} :=
    isOpen_lt continuous_const continuous_tupleNorm
  obtain ⟨-, hχs, -, hχone, hχzero, hχder⟩ := hFacts _ hWopen.measurableSet r hr
  generalize regularizedIndicator j {x : PointTuple n | 3 * r < tupleNorm x} r = χ at hχs hχone hχzero hχder
  have hχ0 : ∀ x, tupleNorm x < 2 * r → χ x = 0 := by
    intro x hx
    apply hχzero
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro z ⟨hz, hzW⟩
    have h1 : tupleNorm z ≤ tupleNorm (z - x) + tupleNorm x := by
      simpa using tupleNorm_add_le (z - x) x
    have h2 : tupleNorm (z - x) < r := hz
    have h3 : 3 * r < tupleNorm z := hzW
    linarith
  have hχ1 : ∀ x, 4 * r ≤ tupleNorm x → χ x = 1 := by
    intro x hx
    apply hχone
    intro z hz
    have h1 : tupleNorm x ≤ tupleNorm (x - z) + tupleNorm z := by
      simpa using tupleNorm_add_le (x - z) z
    rw [tupleNorm_sub_comm] at h1
    have h2 : tupleNorm (z - x) < r := hz
    change 3 * r < tupleNorm z
    linarith
  obtain ⟨P, hPdef⟩ : ∃ P : PointTuple n → ℂ, P = fun y => (χ y : ℂ) * φ y := ⟨_, rfl⟩
  have hPs : ContDiff ℝ ∞ P := by
    rw [hPdef]
    exact (Complex.ofRealCLM.contDiff.comp hχs).mul hφs
  have hLP : ∀ (α : MultiIdx4 n) (x : PointTuple n), multiDeriv α P x =
      ∑ γ ∈ Finset.Icc 0 α,
        (idxChoose α γ : ℂ) * ((multiDeriv γ χ x : ℝ) : ℂ) *
          multiDeriv (α - γ) φ x := by
    intro α x
    rw [hPdef]
    exact hLeibniz n χ φ hχs hφs α x
  have hnegs : ContDiff ℝ ∞ (fun y => (-1 : ℂ) * P y) := contDiff_const.mul hPs
  have hφ₁s : ContDiff ℝ ∞ (φ + fun y => (-1 : ℂ) * P y) := hφs.add hnegs
  have hderφ₁ : ∀ (α : MultiIdx4 n) (x : PointTuple n),
      multiDeriv α (φ + fun y => (-1 : ℂ) * P y) x =
        multiDeriv α φ x + (-1 : ℂ) * multiDeriv α P x := by
    intro α x
    have h1 := (hRulesC n φ hφs).2.2.2.2.2.1 _ hnegs α
    have h2 := (hRulesC n P hPs).2.2.2.2.2.2.1 (-1) α
    rw [h1, h2]
    rfl
  refine ⟨φ + fun y => (-1 : ℂ) * P y, hφ₁s, ?_, ?_, ?_, ?_⟩
  · refine hasCompactSupport_of_eq_zero_far _ (by positivity : (0 : ℝ) ≤ 4 * r) fun x hx => ?_
    simp [hPdef, hχ1 x hx]
  · refine ⟨hφ₁s, hflat.2.1, fun x hx => ?_⟩
    have hfl := hflat.2.2 x hx
    refine ⟨hφ₁s, ?_, fun α => ?_⟩
    · simp [hPdef, hfl.2.1]
    · rw [hderφ₁, hfl.2.2 α, hLP]
      rw [Finset.sum_eq_zero, mul_zero, add_zero]
      intro γ _
      rw [hfl.2.2 (α - γ), mul_zero]
  · have hdiff : φ - (φ + fun y => (-1 : ℂ) * P y) = P := by
      funext y
      simp
    rw [hdiff]
    unfold weightedSeminorm
    refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ENNReal.ofReal_le_ofReal ?_
    by_cases hx : tupleNorm x < 2 * r
    · have hz : multiDeriv α P x = 0 :=
        (hRulesC n P hPs).2.2.2.2.2.2.2 {y | tupleNorm y < 2 * r}
          (isOpen_lt continuous_tupleNorm continuous_const)
          (fun y hy => by simp [hPdef, hχ0 y hy]) α x hx
      rw [hz]
      simpa using hε.le
    · have hx' : 2 * r ≤ tupleNorm x := not_lt.1 hx
      obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = 1 + tupleNorm x ^ 2 := ⟨_, rfl⟩
      rw [← hwdef]
      have hw : 0 < w := by rw [hwdef]; positivity
      have hsq : 2 * r ≤ Real.sqrt w := by
        refine (Real.le_sqrt' (by positivity)).2 ?_
        have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * r) hx' 2
        rw [hwdef]
        linarith
      obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = w ^ ((k : ℝ) / 2) := ⟨_, rfl⟩
      have hA : 0 ≤ A := by rw [hAdef]; positivity
      rw [← hAdef]
      have hdecay : ∀ β : MultiIdx4 n, idxOrder β ≤ k + 1 →
          A * ‖multiDeriv β φ x‖ ≤ M / (2 * r) := by
        intro β hβ
        have h1 : ENNReal.ofReal (w ^ (((k + 1 : ℕ) : ℝ) / 2) * ‖multiDeriv β φ x‖) ≤
            weightedSeminorm (k + 1) φ := by
          unfold weightedSeminorm
          rw [hwdef]
          exact le_iSup_of_le x (le_iSup_of_le β (le_iSup_of_le hβ le_rfl))
        have h2 : w ^ (((k + 1 : ℕ) : ℝ) / 2) * ‖multiDeriv β φ x‖ ≤ M := by
          rw [hM]
          exact (ENNReal.ofReal_le_iff_le_toReal hMfin).1 h1
        have h3 : w ^ (((k + 1 : ℕ) : ℝ) / 2) = A * Real.sqrt w := by
          rw [Real.sqrt_eq_rpow, hAdef, ← Real.rpow_add hw]
          congr 1
          push_cast
          ring
        rw [le_div_iff₀ (by positivity)]
        calc A * ‖multiDeriv β φ x‖ * (2 * r)
            ≤ A * ‖multiDeriv β φ x‖ * Real.sqrt w :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = w ^ (((k + 1 : ℕ) : ℝ) / 2) * ‖multiDeriv β φ x‖ := by rw [h3]; ring
          _ ≤ M := h2
      have hterm : ∀ γ ∈ Finset.Icc (0 : MultiIdx4 n) α,
          A * ‖(idxChoose α γ : ℂ) * ((multiDeriv γ χ x : ℝ) : ℂ) *
              multiDeriv (α - γ) φ x‖ ≤ (idxChoose α γ : ℝ) * (C * (M / (2 * r))) := by
        intro γ hγ
        have hγα : γ ≤ α := (Finset.mem_Icc.1 hγ).2
        have hγk : idxOrder γ ≤ k := (idxOrder_mono hγα).trans hα
        have hd : |multiDeriv γ χ x| ≤ C := by
          have h1 := (hχder γ).2 x
          have h0 : 0 ≤ derivL1Mass j γ := MeasureTheory.integral_nonneg fun x => abs_nonneg _
          have h2 : (r ^ idxOrder γ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hr1)
          calc |multiDeriv γ χ x| ≤ derivL1Mass j γ * (r ^ idxOrder γ)⁻¹ := h1
            _ ≤ derivL1Mass j γ * 1 := mul_le_mul_of_nonneg_left h2 h0
            _ = derivL1Mass j γ := mul_one _
            _ ≤ C := hCγ γ hγk
        have hβ := hdecay (α - γ) (((idxOrder_sub_le α γ).trans hα).trans (Nat.le_succ k))
        have hb : (0 : ℝ) ≤ idxChoose α γ := Nat.cast_nonneg _
        rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
        calc A * ((idxChoose α γ : ℝ) * |multiDeriv γ χ x| * ‖multiDeriv (α - γ) φ x‖)
            = (idxChoose α γ : ℝ) * (|multiDeriv γ χ x| *
                (A * ‖multiDeriv (α - γ) φ x‖)) := by ring
          _ ≤ (idxChoose α γ : ℝ) * (C * (M / (2 * r))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hd hβ (by positivity) hCnn) hb
      rw [hLP]
      have hsum : ((∑ γ ∈ Finset.Icc (0 : MultiIdx4 n) α, idxChoose α γ : ℕ) : ℝ) =
          2 ^ idxOrder α := by
        rw [hBinom n α]
        push_cast
        rfl
      have hpow : (2 : ℝ) ^ idxOrder α ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hα
      calc A * ‖∑ γ ∈ Finset.Icc 0 α, (idxChoose α γ : ℂ) *
              ((multiDeriv γ χ x : ℝ) : ℂ) * multiDeriv (α - γ) φ x‖
          ≤ A * ∑ γ ∈ Finset.Icc 0 α, ‖(idxChoose α γ : ℂ) *
              ((multiDeriv γ χ x : ℝ) : ℂ) * multiDeriv (α - γ) φ x‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) hA
        _ = ∑ γ ∈ Finset.Icc 0 α, A * ‖(idxChoose α γ : ℂ) *
              ((multiDeriv γ χ x : ℝ) : ℂ) * multiDeriv (α - γ) φ x‖ :=
            Finset.mul_sum _ _ _
        _ ≤ ∑ γ ∈ Finset.Icc 0 α, (idxChoose α γ : ℝ) * (C * (M / (2 * r))) :=
            Finset.sum_le_sum hterm
        _ = 2 ^ idxOrder α * (C * (M / (2 * r))) := by
            rw [← Finset.sum_mul, ← hsum]
            push_cast
            rfl
        _ ≤ 2 ^ k * (C * (M / (2 * r))) :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
        _ ≤ ε := by
            have h1 : 2 ^ k * (C * (M / (2 * r))) = 2 ^ k * C * M / (2 * r) := by ring
            rw [h1, div_le_iff₀ (by positivity)]
            have h2 : 2 ^ k * C * M = (2 ^ k * C * M / ε) * ε := by field_simp
            have h3 : r * ε = ε + (2 ^ k * C * M / ε) * ε := by rw [hrdef]; ring
            nlinarith
  · intro hreal x
    have h0 := hreal x
    simp [hPdef, Complex.add_im, Complex.mul_im, h0]
end YangMills.Construction.TestSpaces.SchwartzTruncation
