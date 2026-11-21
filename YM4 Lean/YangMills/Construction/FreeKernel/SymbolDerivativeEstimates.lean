import YangMills.Construction.Constants.HeatKernelNumbersFiniteBounds
import YangMills.Construction.FreeKernel.MonomialFactorDerivativesProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeKernel
open YangMills.Construction.Constants.HeatKernel
open scoped ContDiff
namespace SymbolEstimates
lemma two_le_symmetryConstant : 2 ≤ symmetryConstant := by apply _root_.YangMills.Construction.FreeKernel.MonomialFactors.two_le_symmetryConstant <;> assumption
lemma one_le_symmetryConstant : 1 ≤ symmetryConstant := by
  linarith [two_le_symmetryConstant]
lemma heatDecay_pos : 0 < heatDecay := by apply _root_.YangMills.Construction.Constants.HeatKernel.heatDecay_pos <;> assumption
lemma two_mul_heatDecay : 2 * heatDecay = 4 / Real.pi ^ 2 := by
  unfold heatDecay
  ring
lemma four_div_sq_pi_le_one : 4 / Real.pi ^ 2 ≤ 1 := by
  have hpi := Real.pi_pos
  rw [div_le_one (by positivity)]
  nlinarith [Real.pi_gt_three]
lemma laplacianSymbol_eq_four_sin_sq (θ : ℝ) :
    laplacianSymbol θ = 4 * Real.sin (θ / 2) ^ 2 := by
  have hcos : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]
    congr 1
    ring
  have hpy := Real.sin_sq_add_cos_sq (θ / 2)
  unfold laplacianSymbol
  rw [hcos]
  linarith
lemma jordan_le_laplacianSymbol {θ : ℝ} (hθ : |θ| ≤ Real.pi) :
    4 / Real.pi ^ 2 * θ ^ 2 ≤ laplacianSymbol θ := by
  have hx0 : 0 ≤ |θ| / 2 := by positivity
  have hx1 : |θ| / 2 ≤ Real.pi / 2 := by linarith
  have hs := Real.mul_le_sin hx0 hx1
  have hpos : 0 ≤ 2 / Real.pi * (|θ| / 2) := by positivity
  have hsq : (2 / Real.pi * (|θ| / 2)) ^ 2 ≤ Real.sin (|θ| / 2) ^ 2 :=
    pow_le_pow_left₀ hpos hs 2
  have hsym : Real.sin (|θ| / 2) ^ 2 = Real.sin (θ / 2) ^ 2 := by
    rcases abs_cases θ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_div, Real.sin_neg]
      ring
  have hexp : (2 / Real.pi * (|θ| / 2)) ^ 2 = θ ^ 2 / Real.pi ^ 2 := by
    rw [← sq_abs θ]
    field_simp
  rw [laplacianSymbol_eq_four_sin_sq, ← hsym]
  rw [hexp] at hsq
  have : 4 / Real.pi ^ 2 * θ ^ 2 = 4 * (θ ^ 2 / Real.pi ^ 2) := by ring
  rw [this]
  linarith
lemma homotopySymbol_eq_convex (ς θ : ℝ) :
    homotopySymbol ς θ = (1 - ς) * θ ^ 2 + ς * laplacianSymbol θ := by
  unfold homotopySymbol symbolError
  ring
lemma homotopySymbol_lower : HomotopySymbolLowerBound := by
  intro θ hθ ς hς
  have habs : |θ| ≤ Real.pi := abs_le.2 hθ
  have h1 := jordan_le_laplacianSymbol habs
  have h2 : 4 / Real.pi ^ 2 * θ ^ 2 ≤ θ ^ 2 := by
    nlinarith [four_div_sq_pi_le_one, sq_nonneg θ]
  rw [homotopySymbol_eq_convex]
  have h3 := mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hς.2)
  have h4 := mul_le_mul_of_nonneg_left h1 hς.1
  nlinarith
lemma norm_le_of_norm_deriv_le_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Differentiable ℝ f) (h0 : f 0 = 0) {K : ℝ} (hK : 0 ≤ K) {m : ℕ}
    (hb : ∀ y, ‖deriv f y‖ ≤ K * |y| ^ m) (x : ℝ) : ‖f x‖ ≤ K * |x| ^ (m + 1) := by
  have hbound : ∀ y ∈ Metric.closedBall (0 : ℝ) |x|, ‖deriv f y‖ ≤ K * |x| ^ m := by
    intro y hy
    have hy' : |y| ≤ |x| := by simpa [Real.norm_eq_abs] using hy
    exact (hb y).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg y) hy' m) hK)
  have hx : x ∈ Metric.closedBall (0 : ℝ) |x| := by simp [Real.norm_eq_abs]
  have h0m : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) |x| := by simp
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (fun y _ => hf y) hbound
    (convex_closedBall 0 |x|) h0m hx
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs] at h
  calc ‖f x‖ ≤ K * |x| ^ m * |x| := h
    _ = K * |x| ^ (m + 1) := by ring
lemma hasDerivAt_laplacianSymbol (θ : ℝ) :
    HasDerivAt laplacianSymbol (2 * Real.sin θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).const_mul 2).const_sub 2
  have e : -(2 * -Real.sin θ) = 2 * Real.sin θ := by ring
  rw [e] at h
  exact h
lemma deriv_laplacianSymbol : deriv laplacianSymbol = fun θ => 2 * Real.sin θ :=
  funext fun θ => (hasDerivAt_laplacianSymbol θ).deriv
lemma hasDerivAt_symbolError (θ : ℝ) :
    HasDerivAt symbolError (2 * Real.sin θ - 2 * θ) θ := by
  have h := (hasDerivAt_laplacianSymbol θ).sub (hasDerivAt_pow 2 θ)
  have e : 2 * Real.sin θ - ((2 : ℕ) : ℝ) * θ ^ (2 - 1) = 2 * Real.sin θ - 2 * θ := by
    norm_num
  rw [e] at h
  exact h
lemma hasDerivAt_sinError (θ : ℝ) :
    HasDerivAt (fun x => 2 * Real.sin x - 2 * x) (2 * Real.cos θ - 2) θ := by
  have h := ((Real.hasDerivAt_sin θ).const_mul 2).sub ((hasDerivAt_id θ).const_mul 2)
  exact h.congr_deriv (by simp)
lemma hasDerivAt_cosError (θ : ℝ) :
    HasDerivAt (fun x => 2 * Real.cos x - 2) (-2 * Real.sin θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).const_mul 2).sub_const 2
  have e : 2 * -Real.sin θ = -2 * Real.sin θ := by ring
  rw [e] at h
  exact h
lemma deriv_symbolError :
    deriv symbolError = fun θ => 2 * Real.sin θ - 2 * θ :=
  funext fun θ => (hasDerivAt_symbolError θ).deriv
lemma deriv_sinError :
    deriv (fun x : ℝ => 2 * Real.sin x - 2 * x) = fun θ => 2 * Real.cos θ - 2 :=
  funext fun θ => (hasDerivAt_sinError θ).deriv
lemma deriv_cosError : deriv (fun x : ℝ => 2 * Real.cos x - 2) = fun θ => -2 * Real.sin θ :=
  funext fun θ => (hasDerivAt_cosError θ).deriv
lemma iteratedDeriv_two_symbolError (θ : ℝ) :
    iteratedDeriv 2 symbolError θ = 2 * Real.cos θ - 2 := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ', deriv_symbolError, deriv_sinError]
  simp
lemma iteratedDeriv_add_three_symbolError (κ : ℕ) (θ : ℝ) :
    iteratedDeriv (κ + 3) symbolError θ = -2 * iteratedDeriv κ Real.sin θ := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', deriv_symbolError,
    deriv_sinError, deriv_cosError, iteratedDeriv_const_mul_field]
lemma abs_neg_two_sin_le (θ : ℝ) : |-2 * Real.sin θ| ≤ 2 * |θ| ^ 1 := by
  rw [abs_mul, pow_one]
  have := Real.abs_sin_le_abs (x := θ)
  norm_num
  exact this
lemma abs_cosError_le (θ : ℝ) : |2 * Real.cos θ - 2| ≤ 2 * |θ| ^ 2 := by
  have h := norm_le_of_norm_deriv_le_pow (f := fun x : ℝ => 2 * Real.cos x - 2)
    (fun x => (hasDerivAt_cosError x).differentiableAt) (by simp) (by norm_num : (0 : ℝ) ≤ 2)
    (m := 1) (fun y => by rw [deriv_cosError]; exact abs_neg_two_sin_le y) θ
  simpa [Real.norm_eq_abs] using h
lemma abs_sinError_le (θ : ℝ) : |2 * Real.sin θ - 2 * θ| ≤ 2 * |θ| ^ 3 := by
  have h := norm_le_of_norm_deriv_le_pow (f := fun x : ℝ => 2 * Real.sin x - 2 * x)
    (fun x => (hasDerivAt_sinError x).differentiableAt) (by simp) (by norm_num : (0 : ℝ) ≤ 2)
    (m := 2) (fun y => by rw [deriv_sinError]; exact abs_cosError_le y) θ
  simpa [Real.norm_eq_abs] using h
lemma abs_symbolError_le (θ : ℝ) : |symbolError θ| ≤ 2 * |θ| ^ 4 := by
  have h := norm_le_of_norm_deriv_le_pow (f := symbolError)
    (fun x => (hasDerivAt_symbolError x).differentiableAt)
    (by simp [symbolError, laplacianSymbol]) (by norm_num : (0 : ℝ) ≤ 2)
    (m := 3) (fun y => by rw [deriv_symbolError]; exact abs_sinError_le y) θ
  simpa [Real.norm_eq_abs] using h
lemma abs_iteratedDeriv_symbolError_le (κ : ℕ) (θ : ℝ) :
    |iteratedDeriv κ symbolError θ| ≤ 2 * |θ| ^ (4 - κ) := by
  match κ with
  | 0 => simpa using abs_symbolError_le θ
  | 1 =>
    rw [iteratedDeriv_one, deriv_symbolError]
    exact abs_sinError_le θ
  | 2 =>
    rw [iteratedDeriv_two_symbolError]
    exact abs_cosError_le θ
  | 3 =>
    rw [iteratedDeriv_add_three_symbolError 0 θ, iteratedDeriv_zero]
    exact abs_neg_two_sin_le θ
  | k + 4 =>
    rw [show k + 4 = (k + 1) + 3 by ring, iteratedDeriv_add_three_symbolError, abs_mul]
    have h := Real.abs_iteratedDeriv_sin_le_one (k + 1) θ
    have e : 4 - (k + 1 + 3) = 0 := by omega
    rw [e, pow_zero, mul_one]
    have h2 : |(-2 : ℝ)| = 2 := by norm_num
    rw [h2]
    linarith
lemma abs_iteratedDeriv_laplacianSymbol_le (κ : ℕ) (θ : ℝ) :
    |iteratedDeriv κ laplacianSymbol θ| ≤ 2 * |θ| ^ (2 - κ) := by
  match κ with
  | 0 =>
    have h1 : 0 ≤ laplacianSymbol θ := by
      rw [laplacianSymbol_eq_four_sin_sq]
      positivity
    have h2 : laplacianSymbol θ ≤ θ ^ 2 := by
      have := Real.one_sub_sq_div_two_le_cos (x := θ)
      unfold laplacianSymbol
      linarith
    rw [iteratedDeriv_zero, abs_of_nonneg h1, Nat.sub_zero, sq_abs]
    nlinarith [sq_nonneg θ]
  | 1 =>
    rw [iteratedDeriv_one, deriv_laplacianSymbol, abs_mul]
    have := Real.abs_sin_le_abs (x := θ)
    norm_num
    exact this
  | k + 2 =>
    rw [iteratedDeriv_succ', deriv_laplacianSymbol, iteratedDeriv_const_mul_field, abs_mul]
    have h := Real.abs_iteratedDeriv_sin_le_one (k + 1) θ
    have e : 2 - (k + 2) = 0 := by omega
    rw [e, pow_zero, mul_one]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    linarith
lemma hasDerivAt_homotopySymbol (ς θ : ℝ) :
    HasDerivAt (homotopySymbol ς) (2 * θ + ς * (2 * Real.sin θ - 2 * θ)) θ := by
  have h := (hasDerivAt_pow 2 θ).add ((hasDerivAt_symbolError θ).const_mul ς)
  exact h.congr_deriv (by norm_num)
lemma deriv_homotopySymbol (ς : ℝ) :
    deriv (homotopySymbol ς) = fun θ => 2 * θ + ς * (2 * Real.sin θ - 2 * θ) :=
  funext fun θ => (hasDerivAt_homotopySymbol ς θ).deriv
lemma hasDerivAt_homotopyFirst (ς θ : ℝ) :
    HasDerivAt (fun x => 2 * x + ς * (2 * Real.sin x - 2 * x))
      (2 + ς * (2 * Real.cos θ - 2)) θ := by
  have h := ((hasDerivAt_id θ).const_mul 2).add ((hasDerivAt_sinError θ).const_mul ς)
  exact h.congr_deriv (by simp)
lemma deriv_homotopyFirst (ς : ℝ) :
    deriv (fun x => 2 * x + ς * (2 * Real.sin x - 2 * x)) =
      fun θ => 2 + ς * (2 * Real.cos θ - 2) :=
  funext fun θ => (hasDerivAt_homotopyFirst ς θ).deriv
lemma hasDerivAt_homotopySecond (ς θ : ℝ) :
    HasDerivAt (fun x => 2 + ς * (2 * Real.cos x - 2)) (ς * -2 * Real.sin θ) θ := by
  have h := ((hasDerivAt_cosError θ).const_mul ς).const_add 2
  exact h.congr_deriv (by ring)
lemma deriv_homotopySecond (ς : ℝ) :
    deriv (fun x => 2 + ς * (2 * Real.cos x - 2)) = fun θ => ς * -2 * Real.sin θ :=
  funext fun θ => (hasDerivAt_homotopySecond ς θ).deriv
lemma iteratedDeriv_two_homotopySymbol (ς θ : ℝ) :
    iteratedDeriv 2 (homotopySymbol ς) θ = 2 + ς * (2 * Real.cos θ - 2) := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ', deriv_homotopySymbol,
    deriv_homotopyFirst]
  simp
lemma iteratedDeriv_add_three_homotopySymbol (ς : ℝ) (κ : ℕ) (θ : ℝ) :
    iteratedDeriv (κ + 3) (homotopySymbol ς) θ = ς * -2 * iteratedDeriv κ Real.sin θ := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', deriv_homotopySymbol,
    deriv_homotopyFirst, deriv_homotopySecond, iteratedDeriv_const_mul_field]
lemma abs_deriv_homotopySymbol_le {ς : ℝ} (hς : ς ∈ Set.Icc (0 : ℝ) 1) (θ : ℝ) :
    |deriv (homotopySymbol ς) θ| ≤ symmetryConstant * |θ| := by
  rw [deriv_homotopySymbol]
  have hs := Real.abs_sin_le_abs (x := θ)
  have e : 2 * θ + ς * (2 * Real.sin θ - 2 * θ) =
      (1 - ς) * (2 * θ) + ς * (2 * Real.sin θ) := by ring
  have h1 : |(1 - ς) * (2 * θ)| = (1 - ς) * (2 * |θ|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.2 hς.2)]
    norm_num
  have h2 : |ς * (2 * Real.sin θ)| ≤ ς * (2 * |θ|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hς.1]
    have : |(2 : ℝ)| = 2 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hς.1
  have h3 : (0 : ℝ) ≤ |θ| := abs_nonneg θ
  have h4 := mul_le_mul_of_nonneg_right two_le_symmetryConstant h3
  show |2 * θ + ς * (2 * Real.sin θ - 2 * θ)| ≤ symmetryConstant * |θ|
  rw [e]
  calc |(1 - ς) * (2 * θ) + ς * (2 * Real.sin θ)|
      ≤ |(1 - ς) * (2 * θ)| + |ς * (2 * Real.sin θ)| := abs_add_le _ _
    _ ≤ (1 - ς) * (2 * |θ|) + ς * (2 * |θ|) := by rw [h1]; linarith
    _ = 2 * |θ| := by ring
    _ ≤ symmetryConstant * |θ| := h4
lemma abs_iteratedDeriv_homotopySymbol_le {ς : ℝ} (hς : ς ∈ Set.Icc (0 : ℝ) 1) (θ : ℝ)
    {κ : ℕ} (hκ : 2 ≤ κ) : |iteratedDeriv κ (homotopySymbol ς) θ| ≤ symmetryConstant := by
  have hC := two_le_symmetryConstant
  obtain ⟨k, rfl⟩ : ∃ k, κ = k + 2 := ⟨κ - 2, by omega⟩
  cases k with
  | zero =>
    rw [show 0 + 2 = 2 by rfl, iteratedDeriv_two_homotopySymbol]
    have e : 2 + ς * (2 * Real.cos θ - 2) = 2 * (1 - ς) + ς * (2 * Real.cos θ) := by ring
    have h1 := Real.abs_cos_le_one θ
    obtain ⟨h2, h3⟩ := abs_le.1 h1
    rw [e]
    refine le_trans (abs_le.2 ⟨?_, ?_⟩) hC
    · nlinarith [hς.1, hς.2]
    · nlinarith [hς.1, hς.2]
  | succ j =>
    rw [show j + 1 + 2 = j + 3 by ring, iteratedDeriv_add_three_homotopySymbol, abs_mul,
      abs_mul]
    have h1 := Real.abs_iteratedDeriv_sin_le_one j θ
    have h2 : |ς| ≤ 1 := abs_le.2 ⟨by linarith [hς.1], hς.2⟩
    have h3 : |(-2 : ℝ)| = 2 := by norm_num
    rw [h3]
    have h4 : |ς| * 2 ≤ 2 := by linarith
    calc |ς| * 2 * |iteratedDeriv j Real.sin θ| ≤ 2 * 1 :=
          mul_le_mul h4 h1 (abs_nonneg _) (by norm_num)
      _ ≤ symmetryConstant := by linarith
lemma contDiff_symbolError : ContDiff ℝ ∞ symbolError := by
  unfold symbolError laplacianSymbol
  fun_prop
lemma contDiff_laplacianSymbol : ContDiff ℝ ∞ laplacianSymbol := by
  unfold laplacianSymbol
  fun_prop
lemma contDiff_homotopySymbol (ς : ℝ) : ContDiff ℝ ∞ (homotopySymbol ς) := by
  have h := contDiff_symbolError
  unfold homotopySymbol
  fun_prop
lemma iteratedDeriv_ofReal_comp {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (κ : ℕ) :
    iteratedDeriv κ (fun x => (g x : ℂ)) = fun x => ((iteratedDeriv κ g x : ℝ) : ℂ) := by
  induction κ with
  | zero =>
    funext x
    simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hd : DifferentiableAt ℝ (iteratedDeriv k g) x :=
      (hg.differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt
    rw [iteratedDeriv_succ]
    exact hd.hasDerivAt.ofReal_comp.deriv
lemma hasDerivAt_cexp_mul_ofReal (c : ℂ) (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ))) (c * Complex.exp (c * (θ : ℂ))) θ := by
  have h : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c θ := by
    simpa using ((hasDerivAt_id θ).ofReal_comp).const_mul c
  have h2 := h.cexp
  exact h2.congr_deriv (by ring)
lemma iteratedDeriv_cexp_mul_ofReal (c : ℂ) (κ : ℕ) :
    iteratedDeriv κ (fun x : ℝ => Complex.exp (c * (x : ℂ))) =
      fun θ : ℝ => c ^ κ * Complex.exp (c * (θ : ℂ)) := by
  induction κ with
  | zero =>
    funext θ
    simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext θ
    rw [((hasDerivAt_cexp_mul_ofReal c θ).const_mul (c ^ k)).deriv]
    ring
def expSubOne (c : ℂ) (θ : ℝ) : ℂ := Complex.exp (c * (θ : ℂ)) - 1
def expTaylorRem (c : ℂ) (θ : ℝ) : ℂ := Complex.exp (c * (θ : ℂ)) - 1 - c * (θ : ℂ)
lemma hasDerivAt_expSubOne (c : ℂ) (θ : ℝ) :
    HasDerivAt (expSubOne c) (c * Complex.exp (c * (θ : ℂ))) θ :=
  (hasDerivAt_cexp_mul_ofReal c θ).sub_const 1
lemma hasDerivAt_expTaylorRem (c : ℂ) (θ : ℝ) :
    HasDerivAt (expTaylorRem c) (c * expSubOne c θ) θ := by
  have h : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c θ := by
    simpa using ((hasDerivAt_id θ).ofReal_comp).const_mul c
  have h2 := (hasDerivAt_expSubOne c θ).sub h
  refine h2.congr_deriv ?_
  unfold expSubOne
  ring
lemma deriv_expSubOne (c : ℂ) :
    deriv (expSubOne c) = fun θ : ℝ => c * Complex.exp (c * (θ : ℂ)) :=
  funext fun θ => (hasDerivAt_expSubOne c θ).deriv
lemma deriv_expTaylorRem (c : ℂ) : deriv (expTaylorRem c) = fun θ : ℝ => c * expSubOne c θ :=
  funext fun θ => (hasDerivAt_expTaylorRem c θ).deriv
lemma iteratedDeriv_succ_expSubOne (c : ℂ) (k : ℕ) (θ : ℝ) :
    iteratedDeriv (k + 1) (expSubOne c) θ = c ^ (k + 1) * Complex.exp (c * (θ : ℂ)) := by
  rw [iteratedDeriv_succ', deriv_expSubOne, iteratedDeriv_const_mul_field,
    iteratedDeriv_cexp_mul_ofReal]
  ring
lemma iteratedDeriv_add_two_expTaylorRem (c : ℂ) (k : ℕ) (θ : ℝ) :
    iteratedDeriv (k + 2) (expTaylorRem c) θ = c ^ (k + 2) * Complex.exp (c * (θ : ℂ)) := by
  rw [iteratedDeriv_succ', deriv_expTaylorRem, iteratedDeriv_const_mul_field,
    iteratedDeriv_succ_expSubOne]
  ring
lemma norm_cexp_unit_mul {c : ℂ} (hc : c = Complex.I ∨ c = -Complex.I) (x : ℝ) :
    ‖Complex.exp (c * (x : ℂ))‖ = 1 := by
  rcases hc with rfl | rfl
  · rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I x
  · have e : -Complex.I * (x : ℂ) = ((-x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e]
    exact Complex.norm_exp_ofReal_mul_I _
lemma norm_eq_one_of_unit {c : ℂ} (hc : c = Complex.I ∨ c = -Complex.I) : ‖c‖ = 1 := by
  rcases hc with rfl | rfl <;> simp
lemma norm_expSubOne_le {c : ℂ} (hc : c = Complex.I ∨ c = -Complex.I) (θ : ℝ) :
    ‖expSubOne c θ‖ ≤ |θ| := by
  have h := norm_le_of_norm_deriv_le_pow (f := expSubOne c) (K := 1) (m := 0)
    (fun x => (hasDerivAt_expSubOne c x).differentiableAt) (by simp [expSubOne]) (by norm_num)
    (fun y => by
      rw [deriv_expSubOne]
      simp only [norm_mul, norm_cexp_unit_mul hc, norm_eq_one_of_unit hc]
      simp) θ
  simpa using h
lemma norm_expTaylorRem_le {c : ℂ} (hc : c = Complex.I ∨ c = -Complex.I) (θ : ℝ) :
    ‖expTaylorRem c θ‖ ≤ |θ| ^ 2 := by
  have h := norm_le_of_norm_deriv_le_pow (f := expTaylorRem c) (K := 1) (m := 1)
    (fun x => (hasDerivAt_expTaylorRem c x).differentiableAt) (by simp [expTaylorRem])
    (by norm_num)
    (fun y => by
      rw [deriv_expTaylorRem]
      simp only [norm_mul, norm_eq_one_of_unit hc]
      simpa using norm_expSubOne_le hc y) θ
  simpa using h
lemma norm_iteratedDeriv_expSubOne_le {c : ℂ} (hc : c = Complex.I ∨ c = -Complex.I)
    (κ : ℕ) (θ : ℝ) : ‖iteratedDeriv κ (expSubOne c) θ‖ ≤ |θ| ^ (1 - κ) := by
  cases κ with
  | zero => simpa using norm_expSubOne_le hc θ
  | succ k =>
    rw [iteratedDeriv_succ_expSubOne, norm_mul, norm_pow, norm_eq_one_of_unit hc,
      norm_cexp_unit_mul hc]
    have e : 1 - (k + 1) = 0 := by omega
    simp [e]
lemma norm_iteratedDeriv_expTaylorRem_le {c : ℂ} (hc : c = Complex.I ∨ c = -Complex.I)
    (κ : ℕ) (θ : ℝ) : ‖iteratedDeriv κ (expTaylorRem c) θ‖ ≤ |θ| ^ (2 - κ) := by
  match κ with
  | 0 => simpa using norm_expTaylorRem_le hc θ
  | 1 =>
    rw [iteratedDeriv_one, deriv_expTaylorRem]
    simp only [norm_mul, norm_eq_one_of_unit hc]
    simpa using norm_expSubOne_le hc θ
  | k + 2 =>
    rw [iteratedDeriv_add_two_expTaylorRem, norm_mul, norm_pow, norm_eq_one_of_unit hc,
      norm_cexp_unit_mul hc]
    have e : 2 - (k + 2) = 0 := by omega
    simp [e]
lemma diffMultiplier_forward : diffMultiplier .forward = expSubOne Complex.I := rfl
lemma diffMultiplier_backward : diffMultiplier .backward = -expSubOne (-Complex.I) := by
  funext θ
  simp only [diffMultiplier, expSubOne, Pi.neg_apply, neg_mul, neg_sub]
lemma multiplierError_forward :
    multiplierError .forward = expTaylorRem Complex.I := by
  funext θ
  simp [multiplierError, diffMultiplier, diffOrder, expTaylorRem]
lemma multiplierError_backward :
    multiplierError .backward = -expTaylorRem (-Complex.I) := by
  funext θ
  simp only [multiplierError, diffMultiplier, diffOrder, expTaylorRem, Pi.neg_apply, neg_mul,
    pow_one]
  ring
lemma diffMultiplier_laplacian :
    diffMultiplier .laplacian = -fun θ => (laplacianSymbol θ : ℂ) := rfl
lemma multiplierError_laplacian :
    multiplierError .laplacian = -fun θ => (symbolError θ : ℂ) := by
  funext θ
  simp only [multiplierError, diffMultiplier, diffOrder, symbolError, Pi.neg_apply]
  push_cast
  rw [mul_pow, Complex.I_sq]
  ring
lemma norm_iteratedDeriv_diffMultiplier_le (α : DiffKind) (κ : ℕ) (θ : ℝ) :
    ‖iteratedDeriv κ (diffMultiplier α) θ‖ ≤ symmetryConstant * |θ| ^ (diffOrder α - κ) := by
  have hC := two_le_symmetryConstant
  have hp : ∀ m : ℕ, 0 ≤ |θ| ^ m := fun m => by positivity
  cases α with
  | identity =>
    have e : diffMultiplier .identity = fun _ => (1 : ℂ) := rfl
    rw [e, iteratedDeriv_const]
    have h1 : (diffOrder .identity - κ) = 0 := by simp [diffOrder]
    rw [h1, pow_zero, mul_one]
    split_ifs <;> simp <;> linarith
  | forward =>
    rw [diffMultiplier_forward]
    have h := norm_iteratedDeriv_expSubOne_le (Or.inl rfl) κ θ
    have := hp (1 - κ)
    show _ ≤ symmetryConstant * |θ| ^ (1 - κ)
    nlinarith
  | backward =>
    rw [diffMultiplier_backward, iteratedDeriv_neg, norm_neg]
    have h := norm_iteratedDeriv_expSubOne_le (c := -Complex.I) (Or.inr rfl) κ θ
    have := hp (1 - κ)
    show _ ≤ symmetryConstant * |θ| ^ (1 - κ)
    nlinarith
  | laplacian =>
    rw [diffMultiplier_laplacian, iteratedDeriv_neg, norm_neg,
      iteratedDeriv_ofReal_comp contDiff_laplacianSymbol, Complex.norm_real, Real.norm_eq_abs]
    have h := abs_iteratedDeriv_laplacianSymbol_le κ θ
    have := hp (2 - κ)
    show _ ≤ symmetryConstant * |θ| ^ (2 - κ)
    nlinarith
lemma norm_iteratedDeriv_multiplierError_le (α : DiffKind) (κ : ℕ) {θ : ℝ}
    (hθ : |θ| ≤ Real.pi) :
    ‖iteratedDeriv κ (multiplierError α) θ‖ ≤
      symmetryConstant * |θ| ^ (diffOrder α + 1 - κ) := by
  have hC := two_le_symmetryConstant
  have hp : ∀ m : ℕ, 0 ≤ |θ| ^ m := fun m => by positivity
  cases α with
  | identity =>
    have e : multiplierError .identity = fun _ => (0 : ℂ) := by
      funext θ
      simp [multiplierError, diffMultiplier, diffOrder]
    rw [e, iteratedDeriv_const]
    have := hp (diffOrder .identity + 1 - κ)
    have h0 : 0 ≤ symmetryConstant * |θ| ^ (diffOrder .identity + 1 - κ) := by
      apply mul_nonneg <;> linarith
    split_ifs <;> simpa using h0
  | forward =>
    rw [multiplierError_forward]
    have h := norm_iteratedDeriv_expTaylorRem_le (Or.inl rfl) κ θ
    have := hp (2 - κ)
    show _ ≤ symmetryConstant * |θ| ^ (2 - κ)
    nlinarith
  | backward =>
    rw [multiplierError_backward, iteratedDeriv_neg, norm_neg]
    have h := norm_iteratedDeriv_expTaylorRem_le (c := -Complex.I) (Or.inr rfl) κ θ
    have := hp (2 - κ)
    show _ ≤ symmetryConstant * |θ| ^ (2 - κ)
    nlinarith
  | laplacian =>
    rw [multiplierError_laplacian, iteratedDeriv_neg, norm_neg,
      iteratedDeriv_ofReal_comp contDiff_symbolError, Complex.norm_real, Real.norm_eq_abs]
    have h := abs_iteratedDeriv_symbolError_le κ θ
    show _ ≤ symmetryConstant * |θ| ^ (3 - κ)
    by_cases hκ : κ ≤ 3
    · have e : 4 - κ = (3 - κ) + 1 := by omega
      rw [e, pow_succ] at h
      have h3 := hp (3 - κ)
      have h4 : 2 * (|θ| ^ (3 - κ) * |θ|) ≤ symmetryConstant * |θ| ^ (3 - κ) := by
        have : 2 * |θ| ≤ symmetryConstant := by
          unfold symmetryConstant
          linarith
        nlinarith
      linarith
    · have e1 : 4 - κ = 0 := by omega
      have e2 : 3 - κ = 0 := by omega
      rw [e1, pow_zero, mul_one] at h
      rw [e2, pow_zero, mul_one]
      linarith
lemma symbolVanishingOrders : SymbolVanishingOrders := by
  refine ⟨fun ς hς θ => ⟨abs_deriv_homotopySymbol_le hς θ,
    fun κ hκ => abs_iteratedDeriv_homotopySymbol_le hς θ hκ⟩, fun κ θ => ?_,
    fun α κ θ hθ => ⟨norm_iteratedDeriv_diffMultiplier_le α κ θ,
      norm_iteratedDeriv_multiplierError_le α κ (abs_le.2 hθ)⟩⟩
  have h := abs_iteratedDeriv_symbolError_le κ θ
  have h2 := two_le_symmetryConstant
  have h3 : 0 ≤ |θ| ^ (4 - κ) := by positivity
  nlinarith
lemma abs_iteratedDeriv_exp_comp_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {θ Q : ℝ} (hQ : 0 ≤ Q)
    (hb : ∀ κ, 1 ≤ κ → |iteratedDeriv κ f θ| ≤ Q ^ κ) (n : ℕ) :
    |iteratedDeriv n (fun x => Real.exp (f x)) θ| ≤
      (n.factorial : ℝ) * Q ^ n * Real.exp (f θ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      simp [abs_of_pos (Real.exp_pos _)]
    | succ m =>
      have hu : ContDiff ℝ ∞ (fun x => Real.exp (f x)) := hf.exp
      have hdf : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.1 hf).2
      have hdiff : Differentiable ℝ f := (contDiff_infty_iff_deriv.1 hf).1
      have hd : deriv (fun x => Real.exp (f x)) = deriv f * fun x => Real.exp (f x) := by
        funext x
        rw [((hdiff x).hasDerivAt.exp).deriv]
        simp [mul_comm]
      have hm : ((m : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
      rw [iteratedDeriv_succ', hd,
        iteratedDeriv_mul (hdf.of_le hm).contDiffAt (hu.of_le hm).contDiffAt]
      calc |∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * iteratedDeriv i (deriv f) θ *
            iteratedDeriv (m - i) (fun x => Real.exp (f x)) θ|
          ≤ ∑ _i ∈ Finset.range (m + 1), (m.factorial : ℝ) * Q ^ (m + 1) * Real.exp (f θ) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
            have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
            have h1 : |iteratedDeriv i (deriv f) θ| ≤ Q ^ (i + 1) := by
              rw [← iteratedDeriv_succ']
              exact hb (i + 1) (by omega)
            have h2 := ih (m - i) (by omega)
            have h3 : (m.choose i : ℝ) * ((m - i).factorial : ℝ) ≤ (m.factorial : ℝ) := by
              have e := Nat.choose_mul_factorial_mul_factorial hi'
              have : m.choose i * (m - i).factorial ≤ m.factorial := by
                rw [← e]
                calc m.choose i * (m - i).factorial
                    = m.choose i * 1 * (m - i).factorial := by ring
                  _ ≤ m.choose i * i.factorial * (m - i).factorial := by
                    gcongr
                    exact Nat.factorial_pos i
              exact_mod_cast this
            have hpow : Q ^ (i + 1) * Q ^ (m - i) = Q ^ (m + 1) := by
              rw [← pow_add]
              congr 1
              omega
            rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            calc (m.choose i : ℝ) * |iteratedDeriv i (deriv f) θ| *
                  |iteratedDeriv (m - i) (fun x => Real.exp (f x)) θ|
                ≤ (m.choose i : ℝ) * Q ^ (i + 1) *
                    (((m - i).factorial : ℝ) * Q ^ (m - i) * Real.exp (f θ)) := by
                  gcongr
              _ = (m.choose i : ℝ) * ((m - i).factorial : ℝ) *
                    (Q ^ (i + 1) * Q ^ (m - i)) * Real.exp (f θ) := by ring
              _ ≤ (m.factorial : ℝ) * Q ^ (m + 1) * Real.exp (f θ) := by
                  rw [hpow]
                  gcongr
        _ = ((m + 1).factorial : ℝ) * Q ^ (m + 1) * Real.exp (f θ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.factorial_succ]
            push_cast
            ring
lemma expSymbolRange_facts {t ς θ : ℝ} (h : ExpSymbolRange t ς θ) :
    0 < t ∧ ς ∈ Set.Icc (0 : ℝ) 1 ∧ 4 / Real.pi ^ 2 * θ ^ 2 ≤ homotopySymbol ς θ := by
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨rfl, h1⟩
  · exact ⟨by linarith, ⟨h2, h3⟩, homotopySymbol_lower θ (abs_le.1 h4) ς ⟨h2, h3⟩⟩
  · refine ⟨h1, ⟨le_rfl, zero_le_one⟩, ?_⟩
    have : homotopySymbol 0 θ = θ ^ 2 := by simp [homotopySymbol]
    rw [this]
    nlinarith [four_div_sq_pi_le_one, sq_nonneg θ]
lemma abs_iteratedDeriv_neg_mul_homotopySymbol_le {t ς θ : ℝ} (h : ExpSymbolRange t ς θ)
    {κ : ℕ} (hκ : 1 ≤ κ) :
    |iteratedDeriv κ (fun x => -t * homotopySymbol ς x) θ| ≤
      (symmetryConstant * Real.sqrt t * (1 + Real.sqrt t * |θ|)) ^ κ := by
  obtain ⟨ht, hς, -⟩ := expSymbolRange_facts h
  have hC := one_le_symmetryConstant
  have ha : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have ha2 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hy : 0 ≤ Real.sqrt t * |θ| := by positivity
  rw [iteratedDeriv_const_mul_field, abs_mul, abs_neg, abs_of_pos ht]
  have hQ2 : t * symmetryConstant ≤
      (symmetryConstant * Real.sqrt t * (1 + Real.sqrt t * |θ|)) ^ 2 := by
    have e : (symmetryConstant * Real.sqrt t * (1 + Real.sqrt t * |θ|)) ^ 2 =
        t * (symmetryConstant * (symmetryConstant * (1 + Real.sqrt t * |θ|) ^ 2)) := by
      rw [mul_pow, mul_pow, sq (Real.sqrt t), ha2]
      ring
    rw [e]
    have h1 : 1 ≤ (1 + Real.sqrt t * |θ|) ^ 2 := one_le_pow₀ (by linarith)
    have h2 : 1 ≤ symmetryConstant * (1 + Real.sqrt t * |θ|) ^ 2 := by nlinarith
    have h3 : symmetryConstant ≤
        symmetryConstant * (symmetryConstant * (1 + Real.sqrt t * |θ|) ^ 2) := by nlinarith
    exact mul_le_mul_of_nonneg_left h3 ht.le
  match κ, hκ with
  | 1, _ =>
    rw [iteratedDeriv_one, pow_one]
    have h1 := abs_deriv_homotopySymbol_le hς θ
    have e : symmetryConstant * Real.sqrt t * (1 + Real.sqrt t * |θ|) =
        symmetryConstant * Real.sqrt t + symmetryConstant * (t * |θ|) := by
      have e2 : symmetryConstant * Real.sqrt t * (1 + Real.sqrt t * |θ|) =
          symmetryConstant * Real.sqrt t +
            symmetryConstant * ((Real.sqrt t * Real.sqrt t) * |θ|) := by ring
      rw [e2, ha2]
    have h2 : 0 ≤ symmetryConstant * Real.sqrt t := by positivity
    calc t * |deriv (homotopySymbol ς) θ| ≤ t * (symmetryConstant * |θ|) :=
          mul_le_mul_of_nonneg_left h1 ht.le
      _ = symmetryConstant * (t * |θ|) := by ring
      _ ≤ symmetryConstant * Real.sqrt t * (1 + Real.sqrt t * |θ|) := by rw [e]; linarith
  | 2, _ =>
    have h1 := abs_iteratedDeriv_homotopySymbol_le hς θ (le_refl 2)
    exact (mul_le_mul_of_nonneg_left h1 ht.le).trans hQ2
  | k + 3, _ =>
    rcases h with ⟨h1, -, -, -⟩ | ⟨rfl, -⟩
    · have ha1 : 1 ≤ Real.sqrt t := by
        rw [Real.one_le_sqrt]
        exact h1
      have hQ1 : 1 ≤ symmetryConstant * Real.sqrt t * (1 + Real.sqrt t * |θ|) := by
        have h2 : 1 ≤ symmetryConstant * Real.sqrt t := by nlinarith
        nlinarith
      have h3 := abs_iteratedDeriv_homotopySymbol_le hς θ (κ := k + 3) (by omega)
      calc t * |iteratedDeriv (k + 3) (homotopySymbol ς) θ| ≤ t * symmetryConstant :=
            mul_le_mul_of_nonneg_left h3 ht.le
        _ ≤ (symmetryConstant * Real.sqrt t * (1 + Real.sqrt t * |θ|)) ^ 2 := hQ2
        _ ≤ (symmetryConstant * Real.sqrt t * (1 + Real.sqrt t * |θ|)) ^ (k + 3) :=
            pow_le_pow_right₀ hQ1 (by omega)
    · rw [iteratedDeriv_add_three_homotopySymbol]
      simp only [zero_mul, abs_zero, mul_zero]
      positivity
lemma rpow_div_two_eq_sqrt_pow {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ ((n : ℝ) / 2) = Real.sqrt t ^ n := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  congr 1
  ring
lemma abs_iteratedDeriv_exp_homotopySymbol_le {t ς θ : ℝ} (h : ExpSymbolRange t ς θ) (n : ℕ) :
    |iteratedDeriv n (fun x => Real.exp (-t * homotopySymbol ς x)) θ| ≤
      factorialPower n * t ^ ((n : ℝ) / 2) * (1 + Real.sqrt t * |θ|) ^ n *
        Real.exp (-t * homotopySymbol ς θ) := by
  obtain ⟨ht, -, -⟩ := expSymbolRange_facts h
  have hC := one_le_symmetryConstant
  have hf : ContDiff ℝ ∞ (fun x => -t * homotopySymbol ς x) :=
    contDiff_const.mul (contDiff_homotopySymbol ς)
  have hQ : 0 ≤ symmetryConstant * Real.sqrt t * (1 + Real.sqrt t * |θ|) := by positivity
  have hmain := abs_iteratedDeriv_exp_comp_le hf hQ
    (fun κ hκ => abs_iteratedDeriv_neg_mul_homotopySymbol_le h hκ) n
  refine hmain.trans (le_of_eq ?_)
  rw [rpow_div_two_eq_sqrt_pow ht, mul_pow, mul_pow]
  unfold factorialPower
  ring
lemma ofReal_exp_homotopySymbol_bound_le {t ς θ : ℝ} (h : ExpSymbolRange t ς θ) (n : ℕ) :
    ENNReal.ofReal
        (factorialPower n * t ^ ((n : ℝ) / 2) * (1 + Real.sqrt t * |θ|) ^ n *
          Real.exp (-t * homotopySymbol ς θ)) ≤
      weightedFactorialPower n *
        ENNReal.ofReal (t ^ ((n : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2))) := by
  obtain ⟨ht, -, hlow⟩ := expSymbolRange_facts h
  have hC := one_le_symmetryConstant
  have hy : 0 ≤ Real.sqrt t * |θ| := by positivity
  have hy2 : (Real.sqrt t * |θ|) ^ 2 = t * θ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ht.le, sq_abs]
  have hA : 0 ≤ factorialPower n := by
    unfold factorialPower
    positivity
  have hE : Real.exp (-t * homotopySymbol ς θ) ≤
      Real.exp (-(heatDecay * (Real.sqrt t * |θ|) ^ 2)) *
        Real.exp (-(heatDecay * t * θ ^ 2)) := by
    rw [← Real.exp_add, Real.exp_le_exp, hy2]
    have h1 := mul_le_mul_of_nonneg_left hlow ht.le
    rw [← two_mul_heatDecay] at h1
    nlinarith
  have hmain : factorialPower n * t ^ ((n : ℝ) / 2) * (1 + Real.sqrt t * |θ|) ^ n *
        Real.exp (-t * homotopySymbol ς θ) ≤
      factorialPower n * ((1 + Real.sqrt t * |θ|) ^ n *
          Real.exp (-(heatDecay * (Real.sqrt t * |θ|) ^ 2))) *
        (t ^ ((n : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2))) := by
    calc factorialPower n * t ^ ((n : ℝ) / 2) * (1 + Real.sqrt t * |θ|) ^ n *
          Real.exp (-t * homotopySymbol ς θ)
        ≤ factorialPower n * t ^ ((n : ℝ) / 2) * (1 + Real.sqrt t * |θ|) ^ n *
          (Real.exp (-(heatDecay * (Real.sqrt t * |θ|) ^ 2)) *
            Real.exp (-(heatDecay * t * θ ^ 2))) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = _ := by ring
  calc ENNReal.ofReal (factorialPower n * t ^ ((n : ℝ) / 2) * (1 + Real.sqrt t * |θ|) ^ n *
          Real.exp (-t * homotopySymbol ς θ))
      ≤ ENNReal.ofReal (factorialPower n * ((1 + Real.sqrt t * |θ|) ^ n *
            Real.exp (-(heatDecay * (Real.sqrt t * |θ|) ^ 2))) *
          (t ^ ((n : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2)))) :=
        ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal (factorialPower n) * ENNReal.ofReal ((1 + Real.sqrt t * |θ|) ^ n *
            Real.exp (-(heatDecay * (Real.sqrt t * |θ|) ^ 2))) *
          ENNReal.ofReal (t ^ ((n : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hA]
    _ ≤ weightedFactorialPower n *
          ENNReal.ofReal (t ^ ((n : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2))) := by
        unfold weightedFactorialPower halfLineSup
        gcongr
        exact le_iSup₂_of_le (Real.sqrt t * |θ|) hy le_rfl
end SymbolEstimates
theorem symbolDerivativeBounds_holds : SymbolDerivativeBounds :=
  ⟨SymbolEstimates.one_le_symmetryConstant, SymbolEstimates.heatDecay_pos,
    SymbolEstimates.homotopySymbol_lower, SymbolEstimates.symbolVanishingOrders,
    fun n _ _ _ h => ⟨SymbolEstimates.abs_iteratedDeriv_exp_homotopySymbol_le h n,
      SymbolEstimates.ofReal_exp_homotopySymbol_bound_le h n⟩⟩
end YangMills.Construction.LatticeKernel
