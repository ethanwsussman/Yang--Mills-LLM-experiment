import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Towers.AsymptoticsOfTheMassiveCoefficient
import YangMills.Construction.Towers.PowersOfTheMassivePropagatorProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
open PeriodicOperators (torusAverage toComplexVec castVec bilinDot)
open Tower.MassivePropagator (brillouinAverage)
namespace Tower.Massive.CoefficientAsymptoticsProof
abbrev brillouinBox : Set AmbientSpace := Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)
instance isFiniteMeasure_restrict_brillouinBox :
    IsFiniteMeasure ((volume : Measure AmbientSpace).restrict brillouinBox) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
theorem integrableOn_brillouinBox {E : Type*} [NormedAddCommGroup E] {f : AmbientSpace → E}
    (hf : Continuous f) : IntegrableOn f brillouinBox :=
  hf.continuousOn.integrableOn_compact isCompact_Icc
theorem sum_axis_nonneg (q : AmbientSpace) : 0 ≤ ∑ μ, (2 - 2 * Real.cos (q μ)) :=
  Finset.sum_nonneg fun μ _ => by linarith [Real.cos_le_one (q μ)]
theorem resolvent_pos {z : ℝ} (hz : 0 < z) (q : AmbientSpace) :
    0 < MassivePropagator.resolvent z q := by apply _root_.YangMills.Construction.Tower.MassivePropagator.resolvent_pos <;> assumption
theorem resolvent_le_inv {z : ℝ} (hz : 0 < z) (q : AmbientSpace) :
    MassivePropagator.resolvent z q ≤ z⁻¹ := by
  unfold MassivePropagator.resolvent
  exact inv_anti₀ hz (by linarith [sum_axis_nonneg q])
theorem continuous_resolvent {z : ℝ} (hz : 0 < z) :
    Continuous (MassivePropagator.resolvent z) := by apply _root_.YangMills.Construction.Tower.MassivePropagator.continuous_resolvent <;> assumption
theorem hasDerivAt_resolvent_pow (k : ℕ) {z : ℝ} (hz : 0 < z) (q : AmbientSpace) :
    HasDerivAt (fun w => MassivePropagator.resolvent w q ^ k)
      (-(k : ℝ) * MassivePropagator.resolvent z q ^ (k + 1)) z := by
  have hne : (∑ μ, (2 - 2 * Real.cos (q μ)) + z) ≠ 0 := ne_of_gt (by linarith [sum_axis_nonneg q])
  have h1 : HasDerivAt (fun w => MassivePropagator.resolvent w q)
      (-(MassivePropagator.resolvent z q) ^ 2 * 1) z := by
    have h := (((hasDerivAt_id z).const_add (∑ μ, (2 - 2 * Real.cos (q μ)))).fun_inv hne)
    refine HasDerivAt.congr_deriv (f := fun w => MassivePropagator.resolvent w q) h ?_
    simp only [MassivePropagator.resolvent, id]
    field_simp
  have h2 := h1.fun_pow k
  refine h2.congr_deriv ?_
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring
theorem brillouinAverage_add {f g : AmbientSpace → ℝ} (hf : Continuous f) (hg : Continuous g) :
    brillouinAverage (fun q => f q + g q) = brillouinAverage f + brillouinAverage g := by
  unfold brillouinAverage
  rw [integral_add (integrableOn_brillouinBox hf) (integrableOn_brillouinBox hg)]
  ring
theorem brillouinAverage_sub {f g : AmbientSpace → ℝ} (hf : Continuous f) (hg : Continuous g) :
    brillouinAverage (fun q => f q - g q) = brillouinAverage f - brillouinAverage g := by
  unfold brillouinAverage
  rw [integral_sub (integrableOn_brillouinBox hf) (integrableOn_brillouinBox hg)]
  ring
theorem brillouinAverage_const_mul (r : ℝ) (f : AmbientSpace → ℝ) :
    brillouinAverage (fun q => r * f q) = r * brillouinAverage f := by
  unfold brillouinAverage
  rw [integral_const_mul]
  ring
theorem abs_brillouinAverage_le {f g : AmbientSpace → ℝ} (hg : Continuous g)
    (h : ∀ q, |f q| ≤ g q) : |brillouinAverage f| ≤ brillouinAverage g := by
  unfold brillouinAverage
  have hc : (0 : ℝ) ≤ ((2 * Real.pi) ^ 4)⁻¹ := by positivity
  rw [abs_mul, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have h2 := norm_integral_le_of_norm_le (μ := (volume : Measure AmbientSpace).restrict brillouinBox)
    (f := f) (integrableOn_brillouinBox hg) (Eventually.of_forall fun q => h q)
  simpa only [Real.norm_eq_abs] using h2
def resolventMoment (k : ℕ) (c : AmbientSpace → ℝ) (z : ℝ) : ℝ :=
  brillouinAverage fun q => MassivePropagator.resolvent z q ^ k * c q
theorem hasDerivAt_resolventMoment (k : ℕ) {c : AmbientSpace → ℝ} (hc : Continuous c) {M : ℝ}
    (hM : ∀ q, |c q| ≤ M) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (resolventMoment k c) (-(k : ℝ) * resolventMoment (k + 1) c z) z := by
  have hcont : ∀ {w : ℝ} (j : ℕ), 0 < w →
      Continuous fun q => MassivePropagator.resolvent w q ^ j * c q :=
    fun j hw => ((continuous_resolvent hw).pow j).mul hc
  have hs : Ioi (z / 2) ∈ 𝓝 z := Ioi_mem_nhds (by linarith)
  have main : Integrable (fun q => -(k : ℝ) * MassivePropagator.resolvent z q ^ (k + 1) * c q)
        ((volume : Measure AmbientSpace).restrict brillouinBox) ∧
      HasDerivAt (fun w => ∫ q, MassivePropagator.resolvent w q ^ k * c q
          ∂((volume : Measure AmbientSpace).restrict brillouinBox))
        (∫ q, -(k : ℝ) * MassivePropagator.resolvent z q ^ (k + 1) * c q
          ∂((volume : Measure AmbientSpace).restrict brillouinBox)) z := by
    refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun w q => MassivePropagator.resolvent w q ^ k * c q)
      (F' := fun w q => -(k : ℝ) * MassivePropagator.resolvent w q ^ (k + 1) * c q)
      (bound := fun _ => (k : ℝ) * (z / 2)⁻¹ ^ (k + 1) * M) hs ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [Ioi_mem_nhds hz] with w hw
      exact (hcont k hw).aestronglyMeasurable
    · exact integrableOn_brillouinBox (hcont k hz)
    · exact ((continuous_const.mul ((continuous_resolvent hz).pow (k + 1))).mul
        hc).aestronglyMeasurable
    · refine Eventually.of_forall fun q w hw => ?_
      have hw2 : z / 2 < w := hw
      have hw0 : 0 < w := by linarith
      have h1 : MassivePropagator.resolvent w q ≤ (z / 2)⁻¹ :=
        (resolvent_le_inv hw0 q).trans (inv_anti₀ (by linarith) hw2.le)
      have h0 := (resolvent_pos hw0 q).le
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg k),
        abs_of_nonneg (pow_nonneg h0 _)]
      have h3 : MassivePropagator.resolvent w q ^ (k + 1) ≤ (z / 2)⁻¹ ^ (k + 1) :=
        pow_le_pow_left₀ h0 h1 _
      have hMn : 0 ≤ M := (abs_nonneg _).trans (hM q)
      exact mul_le_mul (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg k)) (hM q) (abs_nonneg _)
        (by positivity)
    · exact integrable_const _
    · refine Eventually.of_forall fun q w hw => ?_
      have hw2 : z / 2 < w := hw
      exact (hasDerivAt_resolvent_pow k (by linarith) q).mul_const (c q)
  have h3 := main.2.const_mul (((2 * Real.pi) ^ 4)⁻¹ : ℝ)
  have h4 : HasDerivAt (resolventMoment k c) _ z := h3
  refine h4.congr_deriv ?_
  unfold resolventMoment brillouinAverage
  have : ∀ q, -(k : ℝ) * MassivePropagator.resolvent z q ^ (k + 1) * c q =
      -(k : ℝ) * (MassivePropagator.resolvent z q ^ (k + 1) * c q) := fun q => by ring
  simp_rw [this]
  rw [integral_const_mul]
  ring
theorem contDiffOn_resolventMoment {c : AmbientSpace → ℝ} (hc : Continuous c) {M : ℝ}
    (hM : ∀ q, |c q| ≤ M) (n : ℕ) : ∀ k, ContDiffOn ℝ n (resolventMoment k c) (Ioi 0) := by
  induction n with
  | zero =>
    intro k
    simp only [Nat.cast_zero]
    exact contDiffOn_zero.2 fun z hz =>
      (hasDerivAt_resolventMoment k hc hM hz).continuousAt.continuousWithinAt
  | succ n ih =>
    intro k
    have hn : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [hn, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun z hz =>
        (hasDerivAt_resolventMoment k hc hM hz).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    refine ((ih (k + 1)).const_smul (-(k : ℝ))).congr fun z hz => ?_
    simpa using (hasDerivAt_resolventMoment k hc hM hz).deriv
theorem abs_resolventMoment_le (k : ℕ) {c : AmbientSpace → ℝ} {M : ℝ} (hM : ∀ q, |c q| ≤ M)
    {z : ℝ} (hz : 0 < z) :
    |resolventMoment k c z| ≤ M * brillouinAverage fun q => MassivePropagator.resolvent z q ^ k := by
  rw [← brillouinAverage_const_mul]
  refine abs_brillouinAverage_le (continuous_const.mul ((continuous_resolvent hz).pow k))
    fun q => ?_
  rw [abs_mul, abs_of_nonneg (pow_nonneg (resolvent_pos hz q).le _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM q) (pow_nonneg (resolvent_pos hz q).le _)
structure BddLipschitz (f : AmbientSpace → ℂ) : Prop where
  bdd : ∃ M, ∀ q, ‖f q‖ ≤ M
  lip : ∃ K, ∀ q q', ‖f q - f q'‖ ≤ K * euclidNormVec (q - q')
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem euclidNormVec_zero : euclidNormVec 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
theorem BddLipschitz.continuous {f : AmbientSpace → ℂ} (h : BddLipschitz f) : Continuous f := by
  obtain ⟨K, hK⟩ := h.lip
  refine continuous_iff_continuousAt.2 fun q' => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun q => K * euclidNormVec (q - q')) (𝓝 q') (𝓝 0) := by
    have hc : Continuous fun q => K * euclidNormVec (q - q') :=
      continuous_const.mul (continuous_euclidNormVec.comp (continuous_id.sub continuous_const))
    have := hc.tendsto q'
    simpa [euclidNormVec_zero] using this
  exact squeeze_zero (fun _ => norm_nonneg _) (fun q => hK q q') h0
theorem BddLipschitz.const (c : ℂ) : BddLipschitz fun _ => c :=
  ⟨⟨‖c‖, fun _ => le_rfl⟩, ⟨0, fun q q' => by simp⟩⟩
theorem BddLipschitz.add {f g : AmbientSpace → ℂ} (hf : BddLipschitz f) (hg : BddLipschitz g) :
    BddLipschitz fun q => f q + g q := by
  obtain ⟨Mf, hMf⟩ := hf.bdd
  obtain ⟨Mg, hMg⟩ := hg.bdd
  obtain ⟨Kf, hKf⟩ := hf.lip
  obtain ⟨Kg, hKg⟩ := hg.lip
  refine ⟨⟨Mf + Mg, fun q => (norm_add_le _ _).trans (add_le_add (hMf q) (hMg q))⟩,
    ⟨Kf + Kg, fun q q' => ?_⟩⟩
  have : f q + g q - (f q' + g q') = (f q - f q') + (g q - g q') := by ring
  rw [this, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hKf q q') (hKg q q'))
theorem BddLipschitz.mul {f g : AmbientSpace → ℂ} (hf : BddLipschitz f) (hg : BddLipschitz g) :
    BddLipschitz fun q => f q * g q := by
  obtain ⟨Mf, hMf⟩ := hf.bdd
  obtain ⟨Mg, hMg⟩ := hg.bdd
  obtain ⟨Kf, hKf⟩ := hf.lip
  obtain ⟨Kg, hKg⟩ := hg.lip
  have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf 0)
  refine ⟨⟨Mf * Mg, fun q => ?_⟩, ⟨Mf * Kg + Kf * Mg, fun q q' => ?_⟩⟩
  · rw [norm_mul]
    exact mul_le_mul (hMf q) (hMg q) (norm_nonneg _) hMf0
  · have : f q * g q - f q' * g q' = f q * (g q - g q') + (f q - f q') * g q' := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖f q‖ * ‖g q - g q'‖ ≤ Mf * (Kg * euclidNormVec (q - q')) :=
      mul_le_mul (hMf q) (hKg q q') (norm_nonneg _) hMf0
    have h2 : ‖f q - f q'‖ * ‖g q'‖ ≤ (Kf * euclidNormVec (q - q')) * Mg :=
      mul_le_mul (hKf q q') (hMg q') (norm_nonneg _) ((norm_nonneg _).trans (hKf q q'))
    nlinarith [h1, h2]
theorem BddLipschitz.sum {ι : Type*} (s : Finset ι) {f : ι → AmbientSpace → ℂ}
    (hf : ∀ i, BddLipschitz (f i)) : BddLipschitz fun q => ∑ i ∈ s, f i q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BddLipschitz.const 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i).add ih
theorem norm_exp_I_sub_exp_I_le (s t : ℝ) :
    ‖Complex.exp (Complex.I * s) - Complex.exp (Complex.I * t)‖ ≤ |s - t| := by
  have h : Complex.exp (Complex.I * s) - Complex.exp (Complex.I * t) =
      Complex.exp (Complex.I * t) * (Complex.exp (Complex.I * ((s - t : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := s - t)
theorem abs_cos_sub_cos_le_abs (s t : ℝ) : |Real.cos s - Real.cos t| ≤ |s - t| := by
  refine le_trans ?_ (norm_exp_I_sub_exp_I_le s t)
  have h : Real.cos s - Real.cos t =
      (Complex.exp (Complex.I * s) - Complex.exp (Complex.I * t)).re := by
    rw [Complex.sub_re, mul_comm Complex.I, mul_comm Complex.I, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_re]
  rw [h]
  exact Complex.abs_re_le_norm _
theorem abs_apply_le_euclidNormVec (v : AmbientSpace) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
theorem bddLipschitz_cos (μ : Fin 4) : BddLipschitz fun q : AmbientSpace => Complex.cos (q μ : ℂ) := by
  refine ⟨⟨1, fun q => ?_⟩, ⟨1, fun q q' => ?_⟩⟩
  · rw [← Complex.ofReal_cos, Complex.norm_real]
    exact Real.abs_cos_le_one _
  · rw [← Complex.ofReal_cos, ← Complex.ofReal_cos, ← Complex.ofReal_sub, Complex.norm_real,
      one_mul, Real.norm_eq_abs]
    refine (abs_cos_sub_cos_le_abs _ _).trans ?_
    simpa using abs_apply_le_euclidNormVec (q - q') μ
theorem norm_fourierChar (n : Fin 4 → ℤ) (q : AmbientSpace) : ‖MagneticWeyl.fourierChar n q‖ = 1 := by
  have h : MagneticWeyl.intDot n q = ((∑ μ, (n μ : ℝ) * q μ : ℝ) : ℂ) := by
    simp [MagneticWeyl.intDot, bilinDot, castVec, toComplexVec]
  rw [MagneticWeyl.fourierChar, h, mul_comm, Complex.norm_exp_ofReal_mul_I]
theorem abs_sum_mul_le_euclid (a b : AmbientSpace) :
    |∑ μ, a μ * b μ| ≤ euclidNormVec a * euclidNormVec b := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.abs_inner_le_euclidNormVec_mul <;> assumption
theorem norm_fourierChar_sub_le (n : Fin 4 → ℤ) (q q' : AmbientSpace) :
    ‖MagneticWeyl.fourierChar n q - MagneticWeyl.fourierChar n q'‖ ≤
      (1 + euclidNormVec (castVec n)) * euclidNormVec (q - q') := by
  have h : ∀ p : AmbientSpace, MagneticWeyl.intDot n p = ((∑ μ, castVec n μ * p μ : ℝ) : ℂ) :=
    fun p => by simp [MagneticWeyl.intDot, bilinDot, toComplexVec]
  simp only [MagneticWeyl.fourierChar, h]
  refine (norm_exp_I_sub_exp_I_le _ _).trans ?_
  have h2 : (∑ μ, castVec n μ * q μ) - ∑ μ, castVec n μ * q' μ =
      ∑ μ, castVec n μ * (q - q') μ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun μ _ => by simp only [Pi.sub_apply]; ring
  rw [h2]
  refine (abs_sum_mul_le_euclid _ _).trans ?_
  have h3 : 0 ≤ euclidNormVec (q - q') := Real.sqrt_nonneg _
  nlinarith
theorem bddLipschitz_of_hasSum {γ : (Fin 4 → ℤ) → ℂ} {f : AmbientSpace → ℂ}
    (hf : ∀ q, HasSum (fun n => MagneticWeyl.fourierChar n q * γ n) (f q))
    (h0 : Summable fun n => ‖γ n‖)
    (h1 : Summable fun n => ‖γ n‖ * (1 + euclidNormVec (castVec n))) : BddLipschitz f := by
  refine ⟨⟨∑' n, ‖γ n‖, fun q => ?_⟩, ⟨∑' n, ‖γ n‖ * (1 + euclidNormVec (castVec n)),
    fun q q' => ?_⟩⟩
  · refine (hf q).norm_le_of_bounded h0.hasSum fun n => ?_
    rw [norm_mul, norm_fourierChar, one_mul]
  · have hsum := (hf q).sub (hf q')
    refine hsum.norm_le_of_bounded (h1.hasSum.mul_right (euclidNormVec (q - q'))) fun n => ?_
    rw [← sub_mul, norm_mul, mul_comm ‖_‖, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_fourierChar_sub_le n q q') (norm_nonneg _)
section Entries
variable {N' N'' : ℕ} [NeZero N'] [NeZero N'']
theorem norm_apply_le_opNormValue (X : Matrix (Fin N') (Fin N'') ℂ) (i : Fin N') (k : Fin N'') :
    ‖X i k‖ ≤ Matrices.RectangularMatrix.opNormValue X := by
  have h : ‖Matrix.toEuclideanLin X (EuclideanSpace.single k (1 : ℂ))‖ ≤
      Matrices.RectangularMatrix.opNormValue X * ‖EuclideanSpace.single k (1 : ℂ)‖ :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)).le_opNorm _
  rw [EuclideanSpace.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  have h2 := PiLp.norm_apply_le (Matrix.toEuclideanLin X (EuclideanSpace.single k (1 : ℂ))) i
  simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_single] using h2
theorem bddLipschitz_apply {a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    (h : MagneticWeyl.IsFiniteFourierSymbol a) (i : Fin N') (k : Fin N'') :
    BddLipschitz fun q => a q i k := by
  obtain ⟨c, hc, hs⟩ := h.1
  have hnn : ∀ n, 0 ≤ 1 + euclidNormVec (castVec n) := fun n => by
    have : 0 ≤ euclidNormVec (castVec n) := Real.sqrt_nonneg _
    linarith
  refine bddLipschitz_of_hasSum (γ := fun n => c n i k) (fun q => ?_) ?_ ?_
  · have h2 := (hc q).map (Matrix.entryAddMonoidHom ℂ i k)
      (Continuous.matrix_elem continuous_id i k)
    simpa [Function.comp_def, smul_eq_mul] using h2
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hs 0 (by norm_num))
    simpa using norm_apply_le_opNormValue (c n) i k
  · refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (hnn n)) (fun n => ?_)
      (hs 1 (by norm_num))
    rw [pow_one]
    exact mul_le_mul_of_nonneg_right (norm_apply_le_opNormValue (c n) i k) (hnn n)
end Entries
theorem bddLipschitz_trace_sq {σ : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ}
    (h : MagneticWeyl.IsFiniteFourierSymbol σ) : BddLipschitz fun q => ((σ q) ^ 2).trace := by
  have h2 : (fun q => ((σ q) ^ 2).trace) = fun q => ∑ i, ∑ j, σ q i j * σ q j i := by
    funext q
    simp [Matrix.trace, pow_two, Matrix.mul_apply]
  rw [h2]
  exact BddLipschitz.sum _ fun i => BddLipschitz.sum _ fun j =>
    (bddLipschitz_apply h i j).mul (bddLipschitz_apply h j i)
theorem bddLipschitz_trace {σ : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ}
    (h : MagneticWeyl.IsFiniteFourierSymbol σ) : BddLipschitz fun q => (σ q).trace := by
  have h2 : (fun q => (σ q).trace) = fun q => ∑ i, σ q i i := by
    funext q
    simp [Matrix.trace]
  rw [h2]
  exact BddLipschitz.sum _ fun i => bddLipschitz_apply h i i
theorem partialIn_latticeSymbol (μ : Fin 4) (κ : Fin 4 → ℂ) :
    partialIn μ latticeSymbol κ = 2 * Complex.sin (κ μ) := by
  have h : HasDerivAt (fun t : ℂ => latticeSymbol (Function.update κ μ t))
      (2 * Complex.sin (κ μ)) (κ μ) := by
    have h1 : ∀ ν ∈ (Finset.univ : Finset (Fin 4)),
        HasDerivAt (fun t : ℂ => axisSymbol ν (Function.update κ μ t))
          (if ν = μ then 2 * Complex.sin (κ μ) else 0) (κ μ) := by
      intro ν _
      by_cases hν : ν = μ
      · subst hν
        simp only [axisSymbol, Function.update_self, if_true]
        have h2 := ((Complex.hasDerivAt_cos (κ ν)).const_mul (2 : ℂ)).const_sub (2 : ℂ)
        refine h2.congr_deriv ?_
        ring
      · simp only [axisSymbol, Function.update_of_ne hν, if_neg hν]
        exact hasDerivAt_const _ _
    have h3 := HasDerivAt.fun_sum h1
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h3
    exact h3
  exact h.deriv
theorem partialIn_partialIn_latticeSymbol (μ : Fin 4) (κ : Fin 4 → ℂ) :
    partialIn μ (partialIn μ latticeSymbol) κ = 2 * Complex.cos (κ μ) := by
  have h : (fun t : ℂ => partialIn μ latticeSymbol (Function.update κ μ t)) =
      fun t => 2 * Complex.sin t := by
    funext t
    rw [partialIn_latticeSymbol, Function.update_self]
  unfold partialIn at h ⊢
  rw [h]
  exact ((Complex.hasDerivAt_sin (κ μ)).const_mul (2 : ℂ)).deriv
theorem resolvent_ofReal (z : ℝ) (q : AmbientSpace) :
    Massive.resolvent (z : ℂ) (toComplexVec q) = ((MassivePropagator.resolvent z q : ℝ) : ℂ) := by
  simp [Massive.resolvent, latticeSymbol, axisSymbol, toComplexVec, MassivePropagator.resolvent]
theorem re_torusAverage {g : AmbientSpace → ℂ} (hg : Continuous g) :
    (torusAverage g).re = brillouinAverage fun q => (g q).re := by
  unfold torusAverage brillouinAverage
  rw [Complex.re_ofReal_mul]
  congr 1
  exact (Complex.reCLM.integral_comp_comm (integrableOn_brillouinBox hg)).symm
theorem torusAverage_linear_combination {f g : AmbientSpace → ℂ} (hf : Continuous f)
    (hg : Continuous g) :
    8 * torusAverage f + 1 / 2 * torusAverage g = torusAverage fun q => 8 * f q + 1 / 2 * g q := by
  unfold torusAverage
  rw [integral_add ((integrableOn_brillouinBox hf).const_mul 8)
      ((integrableOn_brillouinBox hg).const_mul (1 / 2)),
    integral_const_mul, integral_const_mul]
  ring
theorem re_formula {T S P₀ P₁ D : AmbientSpace → ℂ} (hT : Continuous T) (hS : Continuous S)
    (hP₀ : Continuous P₀) (hP₁ : Continuous P₁) (hD : Continuous D) {z : ℝ} (hz : 0 < z) :
    (8 * torusAverage (fun q =>
        1 / 2 * ((MassivePropagator.resolvent z q : ℝ) : ℂ) ^ 2 * T q -
          1 / 12 * ((MassivePropagator.resolvent z q : ℝ) : ℂ) ^ 2 * P₀ q * P₁ q -
            ((MassivePropagator.resolvent z q : ℝ) : ℂ) * S q) +
      1 / 2 * torusAverage (fun q => ((MassivePropagator.resolvent z q : ℝ) : ℂ) * D q)).re =
    resolventMoment 2 (fun q => (8 * (1 / 2 * T q - 1 / 12 * P₀ q * P₁ q)).re) z +
      resolventMoment 1 (fun q => (8 * -S q + 1 / 2 * D q).re) z := by
  have hr := continuous_resolvent hz
  have hA : Continuous fun q => (8 * (1 / 2 * T q - 1 / 12 * P₀ q * P₁ q)).re :=
    Complex.continuous_re.comp (by fun_prop)
  have hB : Continuous fun q => (8 * -S q + 1 / 2 * D q).re :=
    Complex.continuous_re.comp (by fun_prop)
  rw [torusAverage_linear_combination (by fun_prop) (by fun_prop), re_torusAverage (by fun_prop)]
  unfold resolventMoment
  have c1 : Continuous fun q => MassivePropagator.resolvent z q ^ 2 *
      (8 * (1 / 2 * T q - 1 / 12 * P₀ q * P₁ q)).re := (hr.pow 2).mul hA
  have c2 : Continuous fun q => MassivePropagator.resolvent z q ^ 1 *
      (8 * -S q + 1 / 2 * D q).re := (hr.pow 1).mul hB
  refine Eq.trans ?_ (brillouinAverage_add c1 c2)
  congr 1
  funext q
  have h : 8 * (1 / 2 * ((MassivePropagator.resolvent z q : ℝ) : ℂ) ^ 2 * T q -
          1 / 12 * ((MassivePropagator.resolvent z q : ℝ) : ℂ) ^ 2 * P₀ q * P₁ q -
            ((MassivePropagator.resolvent z q : ℝ) : ℂ) * S q) +
        1 / 2 * (((MassivePropagator.resolvent z q : ℝ) : ℂ) * D q) =
      ((MassivePropagator.resolvent z q ^ 2 : ℝ) : ℂ) * (8 * (1 / 2 * T q - 1 / 12 * P₀ q * P₁ q)) +
        ((MassivePropagator.resolvent z q ^ 1 : ℝ) : ℂ) * (8 * -S q + 1 / 2 * D q) := by
    push_cast
    ring
  rw [h, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
theorem abs_mul_le_mul_of_le {w x M m C : ℝ} (hw : 0 ≤ w) (hx : |x| ≤ M * m) (hM : 0 ≤ M)
    (hm : w * m ≤ C) : |w * x| ≤ M * C := by
  rw [abs_mul, abs_of_nonneg hw]
  calc w * |x| ≤ w * (M * m) := mul_le_mul_of_nonneg_left hx hw
    _ = M * (w * m) := by ring
    _ ≤ M * C := mul_le_mul_of_nonneg_left hm hM
theorem brillouinAverage_pow_nonneg (k : ℕ) {z : ℝ} (hz : 0 < z) :
    0 ≤ brillouinAverage fun q => MassivePropagator.resolvent z q ^ k :=
  (abs_nonneg _).trans (abs_brillouinAverage_le ((continuous_resolvent hz).pow k)
    fun q => le_of_eq (abs_of_nonneg (pow_nonneg (resolvent_pos hz q).le _)))
theorem of_resolventMoments {a b : AmbientSpace → ℝ} (ha : Continuous a) (hb : Continuous b)
    {Ma Mb Ka : ℝ} (hMa : ∀ q, |a q| ≤ Ma) (hMb : ∀ q, |b q| ≤ Mb) (hKa0 : 0 ≤ Ka)
    (hKa : ∀ q, |a q - 88 / 3| ≤ Ka * euclidNormVec q)
    (hP : MassivePropagator.PowerBounds) {β : ℝ → ℝ}
    (hβ : ∀ z, 0 < z → β z = resolventMoment 2 a z + resolventMoment 1 b z) :
    ContDiffOn ℝ 2 β (Ioi 0) ∧
      ∃ C : ℝ, ∀ z : ℝ, 0 < z → z ≤ 1 →
        |β z - 11 / (6 * Real.pi ^ 2) * Real.log (1 / z)| + |z * deriv β z| +
          |z ^ 2 * deriv (deriv β) z| ≤ C := by
  have hMa0 : 0 ≤ Ma := (abs_nonneg _).trans (hMa 0)
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans (hMb 0)
  have hG : ∀ z, 0 < z → HasDerivAt (fun w => resolventMoment 2 a w + resolventMoment 1 b w)
      (-2 * resolventMoment 3 a z - resolventMoment 2 b z) z := fun z hz => by
    have h1 : HasDerivAt (resolventMoment 2 a) (-2 * resolventMoment 3 a z) z := by
      simpa using hasDerivAt_resolventMoment 2 ha hMa hz
    have h2 : HasDerivAt (resolventMoment 1 b) (-resolventMoment 2 b z) z := by
      simpa using hasDerivAt_resolventMoment 1 hb hMb hz
    exact (h1.fun_add h2).congr_deriv (by ring)
  have hG₁ : ∀ z, 0 < z → HasDerivAt (fun w => -2 * resolventMoment 3 a w - resolventMoment 2 b w)
      (6 * resolventMoment 4 a z + 2 * resolventMoment 3 b z) z := fun z hz => by
    have h1 : HasDerivAt (resolventMoment 3 a) (-3 * resolventMoment 4 a z) z := by
      simpa using hasDerivAt_resolventMoment 3 ha hMa hz
    have h2 : HasDerivAt (resolventMoment 2 b) (-2 * resolventMoment 3 b z) z := by
      simpa using hasDerivAt_resolventMoment 2 hb hMb hz
    exact ((h1.const_mul (-2)).fun_sub h2).congr_deriv (by ring)
  have heq : ∀ z, 0 < z → β =ᶠ[𝓝 z] fun w => resolventMoment 2 a w + resolventMoment 1 b w :=
    fun z hz => by
      filter_upwards [Ioi_mem_nhds hz] with w hw using hβ w hw
  have hd1 : ∀ z, 0 < z → deriv β z = -2 * resolventMoment 3 a z - resolventMoment 2 b z :=
    fun z hz => (heq z hz).deriv_eq.trans (hG z hz).deriv
  have hd1e : ∀ z, 0 < z →
      deriv β =ᶠ[𝓝 z] fun w => -2 * resolventMoment 3 a w - resolventMoment 2 b w :=
    fun z hz => by
      filter_upwards [Ioi_mem_nhds hz] with w hw using hd1 w hw
  have hd2 : ∀ z, 0 < z →
      deriv (deriv β) z = 6 * resolventMoment 4 a z + 2 * resolventMoment 3 b z :=
    fun z hz => (hd1e z hz).deriv_eq.trans (hG₁ z hz).deriv
  refine ⟨?_, ?_⟩
  · have h : ContDiffOn ℝ 2 (fun w => resolventMoment 2 a w + resolventMoment 1 b w) (Ioi 0) := by
      have h1 := contDiffOn_resolventMoment ha hMa 2 2
      have h2 := contDiffOn_resolventMoment hb hMb 2 1
      exact_mod_cast h1.add h2
    exact h.congr fun z hz => hβ z hz
  · obtain ⟨C, hC⟩ := hP
    refine ⟨(Ka + Mb + 88 / 3) * C + (2 * Ma + Mb) * C + (6 * Ma + 2 * Mb) * C,
      fun z hz hz1 => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hC z hz
    have h6' := h6 hz1
    have hr := continuous_resolvent hz
    have e1 : (brillouinAverage fun q => MassivePropagator.resolvent z q ^ 1) =
        brillouinAverage (MassivePropagator.resolvent z) := by
      simp only [pow_one]
    have hJ : |resolventMoment 2 a z -
        88 / 3 * brillouinAverage fun q => MassivePropagator.resolvent z q ^ 2| ≤ Ka * C := by
      have e : resolventMoment 2 a z -
            88 / 3 * (brillouinAverage fun q => MassivePropagator.resolvent z q ^ 2) =
          brillouinAverage fun q => MassivePropagator.resolvent z q ^ 2 * (a q - 88 / 3) := by
        unfold resolventMoment
        have c1 : Continuous fun q => MassivePropagator.resolvent z q ^ 2 * a q := (hr.pow 2).mul ha
        have c2 : Continuous fun q => (88 / 3 : ℝ) * MassivePropagator.resolvent z q ^ 2 :=
          continuous_const.mul (hr.pow 2)
        rw [← brillouinAverage_const_mul, ← brillouinAverage_sub c1 c2]
        congr 1
        funext q
        ring
      rw [e]
      have h := abs_brillouinAverage_le
        (f := fun q => MassivePropagator.resolvent z q ^ 2 * (a q - 88 / 3))
        (g := fun q => Ka * (MassivePropagator.resolvent z q ^ 2 * euclidNormVec q))
        (continuous_const.mul ((hr.pow 2).mul continuous_euclidNormVec)) fun q => by
          have hp := pow_nonneg (resolvent_pos hz q).le 2
          rw [abs_mul, abs_of_nonneg hp]
          calc MassivePropagator.resolvent z q ^ 2 * |a q - 88 / 3|
              ≤ MassivePropagator.resolvent z q ^ 2 * (Ka * euclidNormVec q) :=
                mul_le_mul_of_nonneg_left (hKa q) hp
            _ = Ka * (MassivePropagator.resolvent z q ^ 2 * euclidNormVec q) := by ring
      rw [brillouinAverage_const_mul] at h
      exact h.trans (mul_le_mul_of_nonneg_left h2 hKa0)
    have hb1 : |resolventMoment 1 b z| ≤ Mb * C := by
      have h := abs_resolventMoment_le 1 hMb hz
      rw [e1] at h
      exact h.trans (mul_le_mul_of_nonneg_left h1 hMb0)
    have hL : 11 / (6 * Real.pi ^ 2) * Real.log (1 / z) =
        88 / 3 * (1 / (16 * Real.pi ^ 2) * Real.log (1 / z)) := by
      have hpi := Real.pi_ne_zero
      field_simp
      ring
    have hl := abs_le.1 h6'
    have hJ' := abs_le.1 hJ
    have hb1' := abs_le.1 hb1
    have t0 : |β z - 11 / (6 * Real.pi ^ 2) * Real.log (1 / z)| ≤ (Ka + Mb + 88 / 3) * C := by
      rw [hβ z hz, hL]
      exact abs_le.2 ⟨by linarith [hl.1, hJ'.1, hb1'.1], by linarith [hl.2, hJ'.2, hb1'.2]⟩
    have t1 := abs_le.1
      (abs_mul_le_mul_of_le hz.le (abs_resolventMoment_le 3 (c := a) hMa hz) hMa0 h4)
    have t2 := abs_le.1
      (abs_mul_le_mul_of_le hz.le (abs_resolventMoment_le 2 (c := b) hMb hz) hMb0 h3)
    have u1 : |z * deriv β z| ≤ (2 * Ma + Mb) * C := by
      rw [hd1 z hz]
      exact abs_le.2 ⟨by nlinarith [t1.1, t1.2, t2.1, t2.2], by nlinarith [t1.1, t1.2, t2.1, t2.2]⟩
    have hz2 : 0 ≤ z ^ 2 := by positivity
    have h7 : z ^ 2 * (brillouinAverage fun q => MassivePropagator.resolvent z q ^ 3) ≤ C := by
      have hm := mul_nonneg hz.le (brillouinAverage_pow_nonneg 3 hz)
      have : z ^ 2 * (brillouinAverage fun q => MassivePropagator.resolvent z q ^ 3) =
          z * (z * brillouinAverage fun q => MassivePropagator.resolvent z q ^ 3) := by ring
      rw [this]
      exact (mul_le_of_le_one_left hm hz1).trans h4
    have t3 := abs_le.1
      (abs_mul_le_mul_of_le hz2 (abs_resolventMoment_le 4 (c := a) hMa hz) hMa0 h5)
    have t4 := abs_le.1
      (abs_mul_le_mul_of_le hz2 (abs_resolventMoment_le 3 (c := b) hMb hz) hMb0 h7)
    have u2 : |z ^ 2 * deriv (deriv β) z| ≤ (6 * Ma + 2 * Mb) * C := by
      rw [hd2 z hz]
      exact abs_le.2 ⟨by nlinarith [t3.1, t3.2, t4.1, t4.2], by nlinarith [t3.1, t3.2, t4.1, t4.2]⟩
    linarith
theorem BddLipschitz.re_bdd {f : AmbientSpace → ℂ} (h : BddLipschitz f) :
    ∃ M, ∀ q, |(f q).re| ≤ M := by
  obtain ⟨M, hM⟩ := h.bdd
  exact ⟨M, fun q => (Complex.abs_re_le_norm _).trans (hM q)⟩
theorem BddLipschitz.neg {f : AmbientSpace → ℂ} (h : BddLipschitz f) :
    BddLipschitz fun q => -f q := by
  have h2 := (BddLipschitz.const (-1)).mul h
  simpa using h2
theorem BddLipschitz.sub {f g : AmbientSpace → ℂ} (hf : BddLipschitz f) (hg : BddLipschitz g) :
    BddLipschitz fun q => f q - g q := by
  have h2 := hf.add hg.neg
  simpa [sub_eq_add_neg] using h2
theorem massiveCoefficientAsymptotics_of_powerBounds (hP : MassivePropagator.PowerBounds) :
    MassiveCoefficientAsymptotics := by
  intro σ₁ σ₂ h₁ h₂ h₈ β hβ
  have hT := bddLipschitz_trace_sq h₁
  have hS := bddLipschitz_trace h₂
  have hP2 : ∀ μ, BddLipschitz fun q : AmbientSpace =>
      partialIn μ (partialIn μ latticeSymbol) (toComplexVec q) := fun μ => by
    simp only [partialIn_partialIn_latticeSymbol]
    exact (BddLipschitz.const 2).mul (bddLipschitz_cos μ)
  have hD : ∀ μ, BddLipschitz fun q : AmbientSpace => axisSymbol μ (toComplexVec q) := fun μ =>
    (BddLipschitz.const 2).sub ((BddLipschitz.const 2).mul (bddLipschitz_cos μ))
  have hA := (BddLipschitz.const 8).mul (((BddLipschitz.const (1 / 2)).mul hT).sub
    (((BddLipschitz.const (1 / 12)).mul (hP2 0)).mul (hP2 1)))
  have hB := ((BddLipschitz.const 8).mul hS.neg).add
    ((BddLipschitz.const (1 / 2)).mul ((hD 0).add (hD 1)))
  have hc : ∀ μ, toComplexVec (0 : AmbientSpace) μ = 0 := fun μ => by simp [toComplexVec]
  have hA0 : (8 * (1 / 2 * ((σ₁ 0) ^ 2).trace - 1 / 12 *
      partialIn 0 (partialIn 0 latticeSymbol) (toComplexVec 0) *
      partialIn 1 (partialIn 1 latticeSymbol) (toComplexVec 0)) : ℂ) = 88 / 3 := by
    rw [h₈, partialIn_partialIn_latticeSymbol, partialIn_partialIn_latticeSymbol, hc, hc,
      Complex.cos_zero]
    norm_num
  obtain ⟨Ma, hMa⟩ := hA.re_bdd
  obtain ⟨Mb, hMb⟩ := hB.re_bdd
  obtain ⟨Ka, hKa⟩ := hA.lip
  refine of_resolventMoments (a := fun q => (8 * (1 / 2 * ((σ₁ q) ^ 2).trace - 1 / 12 *
      partialIn 0 (partialIn 0 latticeSymbol) (toComplexVec q) *
      partialIn 1 (partialIn 1 latticeSymbol) (toComplexVec q))).re)
    (b := fun q => (8 * -(σ₂ q).trace + 1 / 2 * (axisSymbol 0 (toComplexVec q) +
      axisSymbol 1 (toComplexVec q))).re)
    (Complex.continuous_re.comp hA.continuous) (Complex.continuous_re.comp hB.continuous)
    hMa hMb (abs_nonneg Ka) (fun q => ?_) hP fun z hz => ?_
  · have h := hKa q 0
    rw [hA0] at h
    have h2 := Complex.abs_re_le_norm (8 * (1 / 2 * ((σ₁ q) ^ 2).trace - 1 / 12 *
      partialIn 0 (partialIn 0 latticeSymbol) (toComplexVec q) *
      partialIn 1 (partialIn 1 latticeSymbol) (toComplexVec q)) - 88 / 3)
    have h3 : (8 * (1 / 2 * ((σ₁ q) ^ 2).trace - 1 / 12 *
        partialIn 0 (partialIn 0 latticeSymbol) (toComplexVec q) *
        partialIn 1 (partialIn 1 latticeSymbol) (toComplexVec q) : ℂ) - 88 / 3).re =
        (8 * (1 / 2 * ((σ₁ q) ^ 2).trace - 1 / 12 *
        partialIn 0 (partialIn 0 latticeSymbol) (toComplexVec q) *
        partialIn 1 (partialIn 1 latticeSymbol) (toComplexVec q))).re - 88 / 3 := by
      rw [Complex.sub_re]
      norm_num
    rw [h3] at h2
    have hd : 0 ≤ euclidNormVec q := Real.sqrt_nonneg _
    rw [sub_zero] at h
    exact h2.trans (h.trans (mul_le_mul_of_nonneg_right (le_abs_self Ka) hd))
  · have h := hβ z hz
    simp only [resolvent_ofReal] at h
    have h2 := congrArg Complex.re h
    rw [Complex.ofReal_re] at h2
    exact h2.trans (re_formula hT.continuous hS.continuous (hP2 0).continuous (hP2 1).continuous
      ((hD 0).add (hD 1)).continuous hz)
end Tower.Massive.CoefficientAsymptoticsProof
end YangMills.Construction
end
