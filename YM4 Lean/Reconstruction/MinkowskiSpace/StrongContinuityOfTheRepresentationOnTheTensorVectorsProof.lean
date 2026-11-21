import YangMills.Construction.Continuum.TaylorFormulaAtAPointOfTheDiagonalsProof
import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import Reconstruction.Continuum.TimeTranslationsOfASequenceProof
import Reconstruction.MinkowskiSpace.RepresentationOnTheTensorVectors
import Reconstruction.MinkowskiSpace.ScalarProductsAndDensityOfTheTensorVectors
import Reconstruction.MinkowskiSpace.StrongContinuityOfTheRepresentationOnTheTensorVectors
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter MeasureTheory Topology Matrix
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.TensorRepContinuity
open MinkowskiSpace TestSpaces MotionsTranslations RealPointVectors WightmanReconstruction
variable {n : ℕ}
theorem foldr_id_eq {ι X : Type*} (F : ι → X → X) (l : List ι)
    (h : ∀ j ∈ l, F j = id) (g : X) : l.foldr F g = g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldr_cons]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj)), h a List.mem_cons_self]
    rfl
theorem multiDeriv_zero_index (φ : PointTuple n → ℂ) :
    multiDeriv (0 : MultiIdx4 n) φ = φ := by
  unfold multiDeriv
  refine foldr_id_eq _ _ (fun i _ => ?_) φ
  funext h
  exact foldr_id_eq _ _ (fun μ _ => rfl) h
theorem multiDeriv_single_index (i : Fin n) (μ : Fin 4) (φ : PointTuple n → ℂ) :
    multiDeriv (Pi.single i (Pi.single μ 1) : MultiIdx4 n) φ = coordDeriv i μ φ := by apply _root_.YangMills.Construction.TestSpaces.ShiftEstimates.multiDeriv_single <;> assumption
theorem coordDeriv_mem_schwartzSet (hD : DerivSchwartzBounds) (hn : 0 < n)
    {φ : PointTuple n → ℂ} (hφ : φ ∈ TestSpaces.schwartzSet n) (i : Fin n) (μ : Fin 4) :
    coordDeriv i μ φ ∈ TestSpaces.schwartzSet n := by
  rw [← multiDeriv_single_index]
  exact (hD n hn φ hφ _).1
theorem norm_le_tupleNorm (x : PointTuple n) : ‖x‖ ≤ tupleNorm x := by apply _root_.YangMills.SharedProofs.p25561 <;> assumption
theorem exists_decay_bound {φ : PointTuple n → ℂ} (hφ : φ ∈ TestSpaces.schwartzSet n) (N : ℕ) :
    ∃ B : ℝ, ∀ x, (1 + ‖x‖) ^ N * ‖φ x‖ ≤ B := by
  have hW := hφ.2 (2 * N + 2) (by omega)
  refine ⟨2 ^ N * (weightedSeminorm (2 * N + 2) φ).toReal, fun x => ?_⟩
  have hterm : ENNReal.ofReal ((1 + tupleNorm x ^ 2) ^ (((2 * N + 2 : ℕ) : ℝ) / 2) *
      ‖multiDeriv (0 : MultiIdx4 n) φ x‖) ≤ weightedSeminorm (2 * N + 2) φ := by
    unfold weightedSeminorm
    exact le_iSup_of_le x (le_iSup_of_le 0 (le_iSup_of_le (by simp [idxOrder]) le_rfl))
  have h1 := (ENNReal.ofReal_le_iff_le_toReal hW.ne).1 hterm
  have hexp : (((2 * N + 2 : ℕ) : ℝ) / 2) = ((N + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_natCast, multiDeriv_zero_index] at h1
  have ha := norm_le_tupleNorm x
  set e := tupleNorm x
  have hq : (1 : ℝ) ≤ 1 + e ^ 2 := by nlinarith [sq_nonneg e]
  have h2 : (1 + ‖x‖) ≤ 2 * (1 + e ^ 2) := by nlinarith [sq_nonneg (e - 1)]
  have h3 : (1 + ‖x‖) ^ N ≤ 2 ^ N * (1 + e ^ 2) ^ (N + 1) := by
    calc (1 + ‖x‖) ^ N ≤ (2 * (1 + e ^ 2)) ^ N := pow_le_pow_left₀ (by positivity) h2 N
      _ = 2 ^ N * (1 + e ^ 2) ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + e ^ 2) ^ (N + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq (by omega)) (by positivity)
  calc (1 + ‖x‖) ^ N * ‖φ x‖ ≤ (2 ^ N * (1 + e ^ 2) ^ (N + 1)) * ‖φ x‖ :=
        mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    _ = 2 ^ N * ((1 + e ^ 2) ^ (N + 1) * ‖φ x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
def coordFunctional (c : Fin n × Fin 4) : ℂ →L[ℝ] (PointTuple n →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRight (1 : ℂ →L[ℝ] ℂ)
    (Complex.ofRealCLM.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) c.2).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin 4 → ℝ) c.1)))
theorem eq_sum_basis (v : PointTuple n) :
    v = ∑ c : Fin n × Fin 4, v c.1 c.2 • (Pi.single c.1 (Pi.single c.2 1) : PointTuple n) := by apply _root_.YangMills.Construction.ConfigSpace.TaylorNearDiagonal.eq_sum_coordDir <;> assumption
theorem fderiv_eq_sum_coordDeriv {φ : PointTuple n → ℂ} (hφ : Differentiable ℝ φ) :
    fderiv ℝ φ = fun y => ∑ c : Fin n × Fin 4,
      coordFunctional c (coordDeriv c.1 c.2 φ y) := by
  funext y
  refine ContinuousLinearMap.ext fun v => ?_
  conv_lhs => rw [eq_sum_basis v]
  rw [map_sum, _root_.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, coordDeriv, (hφ y).lineDeriv_eq_fderiv]
  simp [coordFunctional, mul_comm]
theorem exists_decay_bound_iteratedFDeriv (hD : DerivSchwartzBounds) (hn : 0 < n) (j : ℕ) :
    ∀ φ ∈ TestSpaces.schwartzSet n, ∀ N : ℕ,
      ∃ B : ℝ, ∀ y, (1 + ‖y‖) ^ N * ‖iteratedFDeriv ℝ j φ y‖ ≤ B := by
  induction j with
  | zero =>
    intro φ hφ N
    obtain ⟨B, hB⟩ := exists_decay_bound hφ N
    exact ⟨B, fun y => by simpa using hB y⟩
  | succ j ih =>
    intro φ hφ N
    have hdiff : Differentiable ℝ φ := hφ.1.differentiable (by simp)
    have hmem := fun c : Fin n × Fin 4 => coordDeriv_mem_schwartzSet hD hn hφ c.1 c.2
    choose B hB using fun c : Fin n × Fin 4 => ih _ (hmem c) N
    refine ⟨∑ c, ‖coordFunctional c‖ * B c, fun y => ?_⟩
    have hsmooth : ∀ c : Fin n × Fin 4, ContDiff ℝ j
        (fun y => coordFunctional c (coordDeriv c.1 c.2 φ y)) := fun c =>
      (coordFunctional c).contDiff.comp ((hmem c).1.of_le (by exact_mod_cast le_top))
    rw [← norm_iteratedFDeriv_fderiv, fderiv_eq_sum_coordDeriv hdiff,
      iteratedFDeriv_sum (fun c _ => hsmooth c)]
    have hterm : ∀ c : Fin n × Fin 4,
        ‖iteratedFDeriv ℝ j (fun y => coordFunctional c (coordDeriv c.1 c.2 φ y)) y‖ ≤
          ‖coordFunctional c‖ * ‖iteratedFDeriv ℝ j (coordDeriv c.1 c.2 φ) y‖ := by
      intro c
      have h := (coordFunctional c).iteratedFDeriv_comp_left (f := coordDeriv c.1 c.2 φ)
        (x := y) (i := j) (n := j) (((hmem c).1.of_le (by exact_mod_cast le_top)).contDiffAt) le_rfl
      have h' : iteratedFDeriv ℝ j
          (fun y => coordFunctional c (coordDeriv c.1 c.2 φ y)) y = _ := h
      rw [h']
      exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    have hpos : (0 : ℝ) ≤ (1 + ‖y‖) ^ N := by positivity
    calc (1 + ‖y‖) ^ N * ‖(∑ c : Fin n × Fin 4, iteratedFDeriv ℝ j
            (fun y => coordFunctional c (coordDeriv c.1 c.2 φ y))) y‖
        ≤ (1 + ‖y‖) ^ N * ∑ c : Fin n × Fin 4,
            ‖coordFunctional c‖ * ‖iteratedFDeriv ℝ j (coordDeriv c.1 c.2 φ) y‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hpos
          rw [Finset.sum_apply]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hterm c)
      _ = ∑ c : Fin n × Fin 4, ‖coordFunctional c‖ *
            ((1 + ‖y‖) ^ N * ‖iteratedFDeriv ℝ j (coordDeriv c.1 c.2 φ) y‖) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ _ := Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (hB c y) (ContinuousLinearMap.opNorm_nonneg _)
def timeVector (n : ℕ) : PointTuple n :=
  ∑ i : Fin n, (((i : ℕ) + 1 : ℕ) : ℝ) • (Pi.single i (Pi.single 0 1) : PointTuple n)
theorem timeWeightedDeriv_eq_fderiv {F : PointTuple n → ℂ} (hF : Differentiable ℝ F) :
    timeWeightedDeriv F = fun x => fderiv ℝ F x (timeVector n) := by
  funext x
  simp only [timeWeightedDeriv, timeVector, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordDeriv, (hF x).lineDeriv_eq_fderiv, Complex.real_smul]
  push_cast
  rfl
theorem iterate_timeWeightedDeriv {F : PointTuple n → ℂ} (hF : ContDiff ℝ ∞ F) (j : ℕ) :
    timeWeightedDeriv^[j] F = fun x => iteratedFDeriv ℝ j F x fun _ => timeVector n := by
  induction j with
  | zero =>
    funext x
    simp
  | succ j ih =>
    have hI : ContDiff ℝ 1 (iteratedFDeriv ℝ j F) :=
      (hF.of_le (by exact_mod_cast le_top)).iteratedFDeriv_right'
    have hdI : Differentiable ℝ (iteratedFDeriv ℝ j F) := hI.differentiable (by simp)
    have hev : ∀ x, HasFDerivAt (fun y => iteratedFDeriv ℝ j F y fun _ => timeVector n)
        ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => PointTuple n) ℂ
          fun _ => timeVector n).comp (fderiv ℝ (iteratedFDeriv ℝ j F) x)) x := fun x =>
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => PointTuple n) ℂ
          fun _ => timeVector n).hasFDerivAt.comp x (hdI x).hasFDerivAt
    rw [Function.iterate_succ_apply', ih,
      timeWeightedDeriv_eq_fderiv (fun x => (hev x).differentiableAt)]
    funext x
    rw [iteratedFDeriv_succ_apply_left, (hev x).fderiv]
    rfl
def diagMatMap (M : RealMat4) : PointTuple n →L[ℝ] PointTuple n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i => M *ᵥ x i
      map_add' := fun x y => by
        funext i
        simp [Matrix.mulVec_add]
      map_smul' := fun c x => by
        funext i
        simp [Matrix.mulVec_smul] }
def translationPart (g : RealVec4 × RealMat4) : PointTuple n := fun _ => -(g.2⁻¹ *ᵥ g.1)
def pulledBackPoint (g : RealVec4 × RealMat4) (x : PointTuple n) : PointTuple n :=
  diagMatMap g.2⁻¹ x + translationPart g
theorem pulledBackPoint_apply (g : RealVec4 × RealMat4) (x : PointTuple n) (i : Fin n) :
    pulledBackPoint g x i = g.2⁻¹ *ᵥ (x i - g.1) := by
  change g.2⁻¹ *ᵥ x i + -(g.2⁻¹ *ᵥ g.1) = g.2⁻¹ *ᵥ (x i - g.1)
  rw [Matrix.mulVec_sub, sub_eq_add_neg]
theorem poincarePullback_eq_comp (g : RealVec4 × RealMat4) (φ : PointTuple n → ℂ) :
    poincarePullback g φ = fun x => φ (pulledBackPoint g x) := by
  funext x
  simp only [poincarePullback]
  congr 1
  funext i
  rw [pulledBackPoint_apply]
theorem contDiff_poincarePullback (g : RealVec4 × RealMat4) {φ : PointTuple n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (poincarePullback g φ) := by
  rw [poincarePullback_eq_comp]
  exact hφ.comp ((diagMatMap g.2⁻¹).contDiff.add contDiff_const)
theorem iteratedFDeriv_poincarePullback (g : RealVec4 × RealMat4) {φ : PointTuple n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (j : ℕ) (x v : PointTuple n) :
    iteratedFDeriv ℝ j (poincarePullback g φ) x (fun _ => v) =
      iteratedFDeriv ℝ j φ (pulledBackPoint g x) fun _ => diagMatMap g.2⁻¹ v := by
  have hψ : ContDiff ℝ ∞ (fun y => φ (y + translationPart g)) :=
    hφ.comp (contDiff_id.add contDiff_const)
  have h : poincarePullback g φ =
      (fun y => φ (y + translationPart g)) ∘ diagMatMap g.2⁻¹ := by
    rw [poincarePullback_eq_comp]
    rfl
  rw [h, (diagMatMap g.2⁻¹).iteratedFDeriv_comp_right hψ x (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  rfl
def absEntrySum (M : RealMat4) : ℝ := ∑ μ, ∑ ν, |M μ ν|
theorem absEntrySum_nonneg (M : RealMat4) : 0 ≤ absEntrySum M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem continuous_absEntrySum {X : Type*} [TopologicalSpace X] {f : X → RealMat4}
    (hf : Continuous f) : Continuous fun x => absEntrySum (f x) :=
  continuous_finsetSum _ fun μ _ => continuous_finsetSum _ fun ν _ => (hf.matrix_elem μ ν).abs
theorem norm_mulVec_le_absEntrySum (M : RealMat4) (y : RealVec4) :
    ‖M *ᵥ y‖ ≤ absEntrySum M * ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (absEntrySum_nonneg M) (norm_nonneg _))).2
    fun μ => ?_
  have hrow : ∑ ν, |M μ ν| ≤ absEntrySum M :=
    Finset.single_le_sum (f := fun μ => ∑ ν, |M μ ν|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ μ)
  calc ‖(M *ᵥ y) μ‖ = |∑ ν, M μ ν * y ν| := by
        simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ ν, |M μ ν * y ν| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ν, |M μ ν| * ‖y‖ := Finset.sum_le_sum fun ν _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm y ν) (abs_nonneg _)
    _ = (∑ ν, |M μ ν|) * ‖y‖ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow (norm_nonneg _)
theorem norm_diagMatMap_le (M : RealMat4) (x : PointTuple n) :
    ‖diagMatMap M x‖ ≤ absEntrySum M * ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (mul_nonneg (absEntrySum_nonneg M) (norm_nonneg _))).2 fun i =>
    (norm_mulVec_le_absEntrySum M (x i)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (absEntrySum_nonneg M))
open WightmanTheory in
theorem det_lorentz_eq_one (g : PoincareElt) : g.1.2.det = 1 := by
  have h : g.1.2 ∈ restrictedLorentz := (Set.mem_prod.1 g.2).2
  obtain ⟨-, h1, -⟩ := h
  exact h1
open WightmanTheory in
theorem continuous_lorentz_inv : Continuous fun g : PoincareElt => (g.1.2⁻¹ : RealMat4) := by
  have h : (fun g : PoincareElt => (g.1.2⁻¹ : RealMat4)) = fun g => g.1.2.adjugate := by
    funext g
    rw [Matrix.inv_def, det_lorentz_eq_one g]
    simp
  rw [h]
  exact (continuous_snd.comp continuous_subtype_val).matrix_adjugate
open WightmanTheory in
theorem norm_le_of_pulledBackPoint (g : PoincareElt) (x : PointTuple n) :
    ‖x‖ ≤ absEntrySum g.1.2 * ‖pulledBackPoint g.1 x‖ + ‖g.1.1‖ := by
  have hdet : IsUnit g.1.2.det := by
    rw [det_lorentz_eq_one g]
    exact isUnit_one
  have hs := absEntrySum_nonneg g.1.2
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hx : x i = g.1.2 *ᵥ pulledBackPoint g.1 x i + g.1.1 := by
    rw [pulledBackPoint_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec]
    abel
  have h1 := norm_add_le (g.1.2 *ᵥ pulledBackPoint g.1 x i) g.1.1
  have h2 := norm_mulVec_le_absEntrySum g.1.2 (pulledBackPoint g.1 x i)
  have h3 := mul_le_mul_of_nonneg_left (norm_le_pi_norm (pulledBackPoint g.1 x) i) hs
  rw [← hx] at h1
  linarith
def pulledBackDeriv (φ : PointTuple n → ℂ) (j : ℕ) (v : PointTuple n) (g : RealVec4 × RealMat4)
    (x : PointTuple n) : ℂ :=
  iteratedFDeriv ℝ j φ (pulledBackPoint g x) fun _ => diagMatMap g.2⁻¹ v
open WightmanTheory in
theorem continuous_diagMatMap_inv (x : PointTuple n) :
    Continuous fun g : PoincareElt => diagMatMap g.1.2⁻¹ x :=
  continuous_pi fun _ => continuous_lorentz_inv.matrix_mulVec continuous_const
open WightmanTheory in
theorem continuous_pulledBackPoint (x : PointTuple n) :
    Continuous fun g : PoincareElt => pulledBackPoint g.1 x := by
  refine (continuous_diagMatMap_inv x).add (continuous_pi fun _ => ?_)
  exact (continuous_lorentz_inv.matrix_mulVec
    (continuous_fst.comp continuous_subtype_val)).neg
open WightmanTheory in
theorem continuous_pulledBackDeriv_group {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ) (j : ℕ)
    (v x : PointTuple n) : Continuous fun g : PoincareElt => pulledBackDeriv φ j v g.1 x := by
  have hI : Continuous (iteratedFDeriv ℝ j φ) :=
    hφ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  exact (hI.comp (continuous_pulledBackPoint x)).eval
    (continuous_pi fun _ => continuous_diagMatMap_inv v)
theorem continuous_pulledBackDeriv_space {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ) (j : ℕ)
    (v : PointTuple n) (g : RealVec4 × RealMat4) : Continuous (pulledBackDeriv φ j v g) := by
  have hI : Continuous (iteratedFDeriv ℝ j φ) :=
    hφ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hA : Continuous fun x : PointTuple n => pulledBackPoint g x :=
    (diagMatMap g.2⁻¹).continuous.add continuous_const
  exact (hI.comp hA).eval continuous_const
instance instFirstCountableRealMat4 : FirstCountableTopology RealMat4 :=
  inferInstanceAs (FirstCountableTopology (Fin 4 → Fin 4 → ℝ))
open WightmanTheory in
theorem tendsto_integral_norm_pulledBackDeriv_sub (hD : DerivSchwartzBounds) (hn : 0 < n)
    {φ : PointTuple n → ℂ} (hφ : φ ∈ TestSpaces.schwartzSet n) (j : ℕ) (v : PointTuple n)
    (g₀ : PoincareElt) :
    Tendsto (fun g : PoincareElt => ∫ x, ‖pulledBackDeriv φ j v g.1 x -
      pulledBackDeriv φ j v g₀.1 x‖) (𝓝 g₀) (𝓝 0) := by
  obtain ⟨B, hB⟩ := exists_decay_bound_iteratedFDeriv hD hn j φ hφ (4 * n + 1)
  obtain ⟨c, hc⟩ : ∃ c, c = absEntrySum g₀.1.2 + 1 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ‖g₀.1.1‖ + 1 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = absEntrySum g₀.1.2⁻¹ + 1 := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    have := absEntrySum_nonneg g₀.1.2
    linarith
  have hb0 : 0 < b := by
    have := norm_nonneg g₀.1.1
    linarith
  have hd0 : 0 < d := by
    have := absEntrySum_nonneg g₀.1.2⁻¹
    linarith
  have hev : ∀ᶠ g : PoincareElt in 𝓝 g₀,
      absEntrySum g.1.2 < c ∧ ‖g.1.1‖ < b ∧ absEntrySum g.1.2⁻¹ < d := by
    have h1 : ∀ᶠ g : PoincareElt in 𝓝 g₀, absEntrySum g.1.2 < c :=
      (continuous_absEntrySum (continuous_snd.comp continuous_subtype_val)).continuousAt.eventually_lt
        continuousAt_const (by simp only [Function.comp]; linarith)
    have h2 : ∀ᶠ g : PoincareElt in 𝓝 g₀, ‖g.1.1‖ < b :=
      (continuous_fst.comp continuous_subtype_val).norm.continuousAt.eventually_lt
        continuousAt_const (by simp only [Function.comp]; linarith)
    have h3 : ∀ᶠ g : PoincareElt in 𝓝 g₀, absEntrySum g.1.2⁻¹ < d :=
      (continuous_absEntrySum continuous_lorentz_inv).continuousAt.eventually_lt
        continuousAt_const (by linarith)
    filter_upwards [h1, h2, h3] with g a1 a2 a3
    exact ⟨a1, a2, a3⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = 1 + c + b := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by linarith
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = B * (d * ‖v‖) ^ j * κ ^ (4 * n + 1) := ⟨_, rfl⟩
  have hdom : ∀ g : PoincareElt, absEntrySum g.1.2 < c → ‖g.1.1‖ < b →
      absEntrySum g.1.2⁻¹ < d → ∀ x, ‖pulledBackDeriv φ j v g.1 x‖ ≤
        C₀ * (1 + ‖x‖) ^ (-(((4 * n + 1 : ℕ) : ℝ))) := by
    intro g h1 h2 h3 x
    obtain ⟨y, hy⟩ : ∃ y, y = pulledBackPoint g.1 x := ⟨_, rfl⟩
    have hxy := norm_le_of_pulledBackPoint g x
    rw [← hy] at hxy
    have hy0 := norm_nonneg y
    have hκ : 1 + ‖x‖ ≤ κ * (1 + ‖y‖) := by
      have h4 : absEntrySum g.1.2 * ‖y‖ ≤ c * ‖y‖ := mul_le_mul_of_nonneg_right h1.le hy0
      rw [hκdef]
      nlinarith
    have hpow : (1 + ‖x‖) ^ (4 * n + 1) ≤ κ ^ (4 * n + 1) * (1 + ‖y‖) ^ (4 * n + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hκ _
    have hu : ‖diagMatMap g.1.2⁻¹ v‖ ≤ d * ‖v‖ :=
      (norm_diagMatMap_le _ _).trans (mul_le_mul_of_nonneg_right h3.le (norm_nonneg _))
    have hT : ‖pulledBackDeriv φ j v g.1 x‖ ≤
        ‖iteratedFDeriv ℝ j φ y‖ * (d * ‖v‖) ^ j := by
      have h5 := (iteratedFDeriv ℝ j φ y).le_opNorm (fun _ => diagMatMap g.1.2⁻¹ v)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h5
      rw [pulledBackDeriv, ← hy]
      exact h5.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu j)
        (norm_nonneg _))
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity)]
    calc ‖pulledBackDeriv φ j v g.1 x‖ * (1 + ‖x‖) ^ (4 * n + 1)
        ≤ (‖iteratedFDeriv ℝ j φ y‖ * (d * ‖v‖) ^ j) *
            (κ ^ (4 * n + 1) * (1 + ‖y‖) ^ (4 * n + 1)) :=
          mul_le_mul hT hpow (by positivity) (by positivity)
      _ = ((1 + ‖y‖) ^ (4 * n + 1) * ‖iteratedFDeriv ℝ j φ y‖) *
            ((d * ‖v‖) ^ j * κ ^ (4 * n + 1)) := by ring
      _ ≤ B * ((d * ‖v‖) ^ j * κ ^ (4 * n + 1)) :=
          mul_le_mul_of_nonneg_right (hB y) (by positivity)
      _ = C₀ := by
          rw [hC₀]
          ring
  have hrank : ((Module.finrank ℝ (PointTuple n) : ℕ) : ℝ) < (((4 * n + 1 : ℕ) : ℝ)) := by
    have h : Module.finrank ℝ (PointTuple n) = n * 4 := by
      rw [Module.finrank_pi_fintype]
      simp
    rw [h]
    push_cast
    linarith
  have hint : Integrable (fun x : PointTuple n =>
      2 * C₀ * (1 + ‖x‖) ^ (-(((4 * n + 1 : ℕ) : ℝ)))) :=
    (integrable_one_add_norm hrank).const_mul _
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 g₀)
    (F := fun (g : PoincareElt) x => ‖pulledBackDeriv φ j v g.1 x -
      pulledBackDeriv φ j v g₀.1 x‖) (f := fun _ => (0 : ℝ))
    (fun x => 2 * C₀ * (1 + ‖x‖) ^ (-(((4 * n + 1 : ℕ) : ℝ))))
    (Eventually.of_forall fun g =>
      ((continuous_pulledBackDeriv_space hφ.1 j v g.1).sub
        (continuous_pulledBackDeriv_space hφ.1 j v g₀.1)).norm.aestronglyMeasurable)
    (hev.mono fun g hg => Eventually.of_forall fun x => by
      rw [norm_norm]
      have a1 := hdom g hg.1 hg.2.1 hg.2.2 x
      have a2 := hdom g₀ (by linarith) (by linarith) (by linarith) x
      have a3 := norm_sub_le (pulledBackDeriv φ j v g.1 x)
        (pulledBackDeriv φ j v g₀.1 x)
      linarith)
    hint
    (Eventually.of_forall fun x => tendsto_iff_norm_sub_tendsto_zero.1
      ((continuous_pulledBackDeriv_group hφ.1 j v x).tendsto g₀))
  simpa using hlim
open WightmanTheory in
theorem tendsto_fieldFormNorm_sub (hD : DerivSchwartzBounds) (℘ : ℝ) {m : ℕ}
    {φ : PointTuple (m + 1) → ℂ} (hφ : φ ∈ TestSpaces.schwartzSet (m + 1))
    (g₀ : PoincareElt) :
    Tendsto (fun g : PoincareElt => fieldFormNorm ℘
      ((1 : ℂ) • poincarePullback g.1 φ + (-1 : ℂ) • poincarePullback g₀.1 φ))
      (𝓝 g₀) (𝓝 0) := by
  have hval : ∀ (g : PoincareElt) (j : ℕ), WightmanReconstruction.lOneNorm
      (timeWeightedDeriv^[j]
        ((1 : ℂ) • poincarePullback g.1 φ + (-1 : ℂ) • poincarePullback g₀.1 φ)) =
      ∫ x, ‖pulledBackDeriv φ j (timeVector (m + 1)) g.1 x -
        pulledBackDeriv φ j (timeVector (m + 1)) g₀.1 x‖ := by
    intro g j
    have ha := contDiff_poincarePullback g.1 hφ.1
    have hb := contDiff_poincarePullback g₀.1 hφ.1
    have hdiff : (1 : ℂ) • poincarePullback g.1 φ + (-1 : ℂ) • poincarePullback g₀.1 φ =
        poincarePullback g.1 φ - poincarePullback g₀.1 φ := by
      rw [one_smul, neg_smul, one_smul, sub_eq_add_neg]
    rw [hdiff, iterate_timeWeightedDeriv
      (show ContDiff ℝ ∞ (poincarePullback g.1 φ - poincarePullback g₀.1 φ) from ha.sub hb)]
    unfold WightmanReconstruction.lOneNorm
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have ha' : ContDiffAt ℝ j (poincarePullback g.1 φ) x :=
      (ha.of_le (by exact_mod_cast le_top)).contDiffAt
    have hb' : ContDiffAt ℝ j (poincarePullback g₀.1 φ) x :=
      (hb.of_le (by exact_mod_cast le_top)).contDiffAt
    simp only
    rw [iteratedFDeriv_sub_apply ha' hb', _root_.sub_apply,
      iteratedFDeriv_poincarePullback g.1 hφ.1, iteratedFDeriv_poincarePullback g₀.1 hφ.1]
    rfl
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hall : ∀ᶠ g : PoincareElt in 𝓝 g₀,
      ∀ j ∈ Finset.range ((FieldForms.boundOrder ℘ (m + 1)).toNat + 1),
        ∫ x, ‖pulledBackDeriv φ j (timeVector (m + 1)) g.1 x -
          pulledBackDeriv φ j (timeVector (m + 1)) g₀.1 x‖ < ε :=
    (Filter.eventually_all_finset _).2 fun j _ =>
      (tendsto_integral_norm_pulledBackDeriv_sub hD (Nat.succ_pos m) hφ j _ g₀).eventually
        (Iio_mem_nhds hε)
  filter_upwards [hall] with g hg
  have hsup : fieldFormNorm ℘
      ((1 : ℂ) • poincarePullback g.1 φ + (-1 : ℂ) • poincarePullback g₀.1 φ) < ε := by
    unfold fieldFormNorm maxTimeDerivL1
    rw [Finset.sup'_lt_iff]
    intro j hj
    rw [hval]
    exact hg j hj
  have h0 : 0 ≤ fieldFormNorm ℘
      ((1 : ℂ) • poincarePullback g.1 φ + (-1 : ℂ) • poincarePullback g₀.1 φ) := by
    unfold fieldFormNorm maxTimeDerivL1
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_range.2 (Nat.succ_pos _)))
    exact integral_nonneg fun _ => norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  exact hsup
section Vectors
open WightmanTheory
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem continuous_testState_pullback (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K)
    (Ω : K) (A : ℝ → OneLoopNotation.BddOp K) (℘ C : ℝ)
    (hv : RealPointVectors.BoundaryVectorFacts E Ω A ℘ C)
    (hD : DerivSchwartzBounds) {m : ℕ}
    (hO : TestSpaces.Elementary.SchwartzClosedUnderOps (m + 1))
    {φ : PointTuple (m + 1) → ℂ} (hφ : φ ∈ TestSpaces.schwartzSet (m + 1))
    (hmem : ∀ g : PoincareElt,
      poincarePullback g.1 φ ∈ TestSpaces.schwartzSet (m + 1)) :
    Continuous fun g : PoincareElt =>
      testState E Ω A (m + 1) (poincarePullback g.1 φ) := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc := (tendsto_fieldFormNorm_sub hD ℘ hφ g₀).const_mul (4 * ((2 : ℝ) ^ ℘ * C) ^ (m + 1))
  rw [mul_zero] at hc
  refine squeeze_zero (fun _ => norm_nonneg _) (fun g => ?_) hc
  have hlin := hv.testState_linear m _ _ (hmem g) (hmem g₀) 1 (-1)
  have hS : (1 : ℂ) • poincarePullback g.1 φ + (-1 : ℂ) • poincarePullback g₀.1 φ ∈
      TestSpaces.schwartzSet (m + 1) :=
    (hO.1 _ (hmem g) _ (hmem g₀) 1 (-1)).1.1
  have hn := hv.norm_testState_le m _ hS
  rw [hlin, one_smul, neg_smul, one_smul, ← sub_eq_add_neg] at hn
  exact hn
end Vectors
theorem stronglyContinuous_of_claims (hScalar : TensorVecInner.Claim)
    (hRep : TensorPoincareRep.Claim)
    (hVec : RealPointVectors.BoundaryVectorsStatement)
    (hFirst : TestSpaces.Elementary.BasicProperties)
    (hMotions : MotionsTranslations.Statement) : StronglyContinuous := by
  intro K _ _ _ E Ω A ℘ C hform hEuc U hU
  have hs := hScalar E Ω A ℘ C hform
  have hr := hRep E Ω A ℘ C hform hEuc
  have hv := hVec E Ω A ℘ C hform
  have hD := hMotions.2.2.2.2
  have htensor : ∀ (k : ℕ) (f : Fin k → WightmanTheory.TestFn),
      Continuous fun g => U g (FieldFormHilbert.tensorVec E Ω A f) := by
    intro k f
    refine continuous_induced_rng.2 ?_
    cases k with
    | zero =>
      have hconst : ∀ g : WightmanTheory.PoincareElt,
          ((U g (FieldFormHilbert.tensorVec E Ω A f) :
            FieldFormHilbert.tensorHilbert E Ω A) : K) =
          testState E Ω A 0 (tensorVal Fin.elim0) := by
        intro g
        rw [hU g 0 f]
        congr 2
        funext i
        exact i.elim0
      have hfun : ((↑) ∘ fun g => U g (FieldFormHilbert.tensorVec E Ω A f)) =
          fun _ => testState E Ω A 0 (tensorVal Fin.elim0) := funext hconst
      rw [hfun]
      exact continuous_const
    | succ m =>
      have hφ : tensorProd (fun i => (f i).1) ∈ TestSpaces.schwartzSet (m + 1) :=
        hv.tensorVal_mem (m + 1) _ fun i => (f i).2
      have hfun : ∀ g : WightmanTheory.PoincareElt,
          tensorProd (fun i => FieldFormHilbert.poincareActR4 g (f i).1) =
            poincarePullback g.1 (tensorProd fun i => (f i).1) := fun g => rfl
      have hmem : ∀ g : WightmanTheory.PoincareElt,
          poincarePullback g.1 (tensorProd fun i => (f i).1) ∈
            TestSpaces.schwartzSet (m + 1) := by
        intro g
        rw [← hfun g]
        exact hv.tensorVal_mem (m + 1) _ fun i => hr.act_mem_schwartz g (f i)
      have hcont := continuous_testState_pullback E Ω A ℘ C hv hD
        (hFirst (m + 1) (Nat.succ_pos m)).1 hφ hmem
      have heq : ((↑) ∘ fun g => U g (FieldFormHilbert.tensorVec E Ω A f)) =
          fun g : WightmanTheory.PoincareElt =>
            testState E Ω A (m + 1)
              (poincarePullback g.1 (tensorProd fun i => (f i).1)) := by
        funext g
        exact hU g (m + 1) f
      rw [heq]
      exact hcont
  have hspan : ∀ ψ ∈ FieldFormHilbert.tensorDomainIn E Ω A,
      Continuous fun g => U g ψ := by
    intro ψ hψ
    rw [hs.domain_eq_span] at hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact htensor p.1 p.2
    | zero => simpa using continuous_const
    | add x y _ _ hx hy => exact (hx.add hy).congr fun g => by simp [map_add]
    | smul a x _ hx => exact (hx.const_smul a).congr fun g => by simp [map_smul]
  intro ψ
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨χ, hχ, hd⟩ := Metric.mem_closure_iff.1 (hs.dense_domain ψ) ε hε
  refine ⟨fun g => U g χ, hspan χ hχ, fun g => hεu ?_⟩
  rw [(U g).dist_map]
  exact hd
end YangMills.Construction.TensorRepContinuity
