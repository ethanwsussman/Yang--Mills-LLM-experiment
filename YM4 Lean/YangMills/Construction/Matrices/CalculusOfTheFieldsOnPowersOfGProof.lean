import YangMills.Construction.InfiniteLattice.TraceOnTheGroupAndOneBondWeight
import YangMills.Construction.Matrices.CalculusOfTheFieldsOnPowersOfG
import YangMills.Construction.Matrices.UnitaryLogConjugation
import YangMills.Construction.TransferOperators.PeriodicStatesHaarMeasureCubicLatticesAndIntegralOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open YangMills.Construction.Matrices (ComplexMatrix2)
open YangMills.Construction.Matrices.ComplexMatrix2
open scoped ContDiff Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.SpinHarmonics.FieldCalculus
theorem pauli_mul_self (ι : Fin 3) : pauli ι * pauli ι = 1 := by
  ext i j
  fin_cases ι <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, pauliOne, pauliTwo, pauliThree, Matrix.mul_apply, Fin.sum_univ_two]
theorem ofReal_smul_pauli_mem_hermitianTraceless (ι : Fin 3) (x : ℝ) :
    ((x : ℂ) • pauli ι) ∈ hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases ι <;> fin_cases i <;> fin_cases j <;>
      simp [pauli, pauliOne, pauliTwo, pauliThree]
  · fin_cases ι <;> simp [fullTrace, pauli, pauliOne, pauliTwo, pauliThree, Matrix.trace_fin_two]
theorem sincAngle_abs_mul (x : ℝ) : sincAngle |x| * x = Real.sin x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : |x| ≠ 0 := abs_ne_zero.mpr hx
    rw [sincAngle, if_neg hx']
    rcases abs_cases x with ⟨hab, _⟩ | ⟨hab, _⟩
    · rw [hab]; field_simp
    · rw [hab, Real.sin_neg]; field_simp
theorem matExp_smul_lieGenerator (h : UnitaryLogConjugationProperties) (ι : Fin 3) (t : ℝ) :
    matExp ((t : ℂ) • lieGenerator ι) =
      ((Real.cos (t / 2) : ℝ) : ℂ) • (1 : ComplexMatrix2) +
        (Complex.I * ((Real.sin (t / 2) : ℝ) : ℂ)) • pauli ι := by
  set x : ℝ := t / 2 with hx
  have hA := ofReal_smul_pauli_mem_hermitianTraceless ι x
  obtain ⟨hsq, hexp, -⟩ := h.1 _ hA
  have hI : Complex.I • ((x : ℂ) • pauli ι) = (t : ℂ) • lieGenerator ι := by
    rw [lieGenerator, smul_smul, smul_smul]
    congr 1
    rw [hx]
    push_cast
    ring
  have hnorm : operatorNorm ((x : ℂ) • pauli ι) = |x| := by
    have h₁ : ((x : ℂ) • pauli ι) ^ 2 = ((x : ℂ) ^ 2) • (1 : ComplexMatrix2) := by
      rw [pow_two, smul_mul_smul_comm, pauli_mul_self, pow_two]
    rw [h₁] at hsq
    have h₂ := congrFun (congrFun hsq 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h₂
    have h₃ : x ^ 2 = operatorNorm ((x : ℂ) • pauli ι) ^ 2 := by exact_mod_cast h₂
    have h₄ : 0 ≤ operatorNorm ((x : ℂ) • pauli ι) := norm_nonneg _
    rw [← abs_of_nonneg h₄]
    exact ((sq_eq_sq_iff_abs_eq_abs _ _).mp h₃).symm
  rw [← hI, hexp, hnorm, Real.cos_abs, smul_smul, mul_assoc]
  congr 2
  have := sincAngle_abs_mul x
  rw [← this]
  push_cast
  ring
theorem oneParam_add (ι : Fin 3) (t t' : ℝ) :
    oneParam ι (t + t') = oneParam ι t * oneParam ι t' := by
  apply Subtype.ext
  change matExp (((t + t' : ℝ) : ℂ) • lieGenerator ι) =
    matExp ((t : ℂ) • lieGenerator ι) * matExp ((t' : ℂ) • lieGenerator ι)
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left _).smul_right _)
theorem oneParam_zero (ι : Fin 3) : oneParam ι 0 = 1 := by
  apply Subtype.ext
  change matExp (((0 : ℝ) : ℂ) • lieGenerator ι) = 1
  simp [matExp]
theorem continuous_oneParam (ι : Fin 3) : Continuous (oneParam ι) := by
  refine Continuous.subtype_mk ?_ _
  let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
  have hc : Continuous fun Z : ComplexMatrix2 => matExp Z := NormedSpace.exp_continuous
  exact hc.comp ((Complex.continuous_ofReal).smul continuous_const)
theorem oneParameterSubgroups_holds (h : UnitaryLogConjugationProperties) :
    OneParameterSubgroups := fun ι t t' =>
  ⟨matExp_smul_lieGenerator h ι t, matExp_real_smul_lieGenerator_mem ι t,
    congrArg Subtype.val (oneParam_add ι t t')⟩
theorem hasDerivAt_oneParam_entry (h : UnitaryLogConjugationProperties)
    (ι : Fin 3) (r s : Fin 2) :
    HasDerivAt (fun t : ℝ => (oneParam ι t : ComplexMatrix2) r s) (lieGenerator ι r s) 0 := by
  have hform : (fun t : ℝ => (oneParam ι t : ComplexMatrix2) r s) = fun t : ℝ =>
      ((Real.cos (t / 2) : ℝ) : ℂ) * (1 : ComplexMatrix2) r s +
        (Complex.I * ((Real.sin (t / 2) : ℝ) : ℂ)) * pauli ι r s := by
    funext t
    change matExp ((t : ℂ) • lieGenerator ι) r s = _
    rw [matExp_smul_lieGenerator h]
    simp
  rw [hform]
  have hlin : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) 0 := (hasDerivAt_id _).div_const 2
  have hc : HasDerivAt (fun t : ℝ => ((Real.cos (t / 2) : ℝ) : ℂ)) (0 : ℝ) 0 := by
    refine HasDerivAt.ofReal_comp ?_
    simpa using hlin.cos
  have hs : HasDerivAt (fun t : ℝ => ((Real.sin (t / 2) : ℝ) : ℂ)) ((1 / 2 : ℝ) : ℂ) 0 := by
    refine HasDerivAt.ofReal_comp ?_
    simpa using hlin.sin
  have := (hc.mul_const ((1 : ComplexMatrix2) r s)).fun_add
    ((hs.const_mul Complex.I).mul_const (pauli ι r s))
  refine this.congr_deriv ?_
  simp only [lieGenerator, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring
section Moved
variable {J : Type}
theorem shiftAt_apply_self (u : J → specialUnitary) (b : J) (ι : Fin 3) (t : ℝ) :
    shiftAt u b ι t b = u b * oneParam ι t := by
  simp [shiftAt]
theorem shiftAt_apply_of_ne (u : J → specialUnitary) {b c : J} (hc : c ≠ b) (ι : Fin 3) (t : ℝ) :
    shiftAt u b ι t c = u c := by
  simp [shiftAt, hc]
theorem shiftAt_zero (u : J → specialUnitary) (b : J) (ι : Fin 3) : shiftAt u b ι 0 = u := by
  simp [shiftAt, oneParam_zero]
theorem shiftAt_shiftAt (u : J → specialUnitary) (b : J) (ι : Fin 3) (t s : ℝ) :
    shiftAt (shiftAt u b ι t) b ι s = shiftAt u b ι (t + s) := by
  simp [shiftAt, oneParam_add, mul_assoc]
theorem continuous_shiftAt_time (u : J → specialUnitary) (b : J) (ι : Fin 3) :
    Continuous fun t : ℝ => shiftAt u b ι t := by
  classical
  unfold shiftAt
  exact continuous_const.update b (continuous_const.mul (continuous_oneParam ι))
theorem continuous_shiftAt_config (b : J) (ι : Fin 3) (t : ℝ) :
    Continuous fun u : J → specialUnitary => shiftAt u b ι t := by
  classical
  unfold shiftAt
  exact continuous_id.update b ((continuous_apply b).mul continuous_const)
theorem mem_smoothOrder_succ {q : ℕ} {F : (J → specialUnitary) → ℂ} :
    F ∈ smoothOrder (q + 1) ↔ Continuous F ∧ ∀ (b : J) (ι : Fin 3),
      (∀ u, HasDirDerivAt b ι F u) ∧ rightField b ι F ∈ smoothOrder q := Iff.rfl
theorem continuous_of_mem_smoothOrder {q : ℕ} {F : (J → specialUnitary) → ℂ}
    (hF : F ∈ smoothOrder q) : Continuous F := by
  cases q with
  | zero => exact hF
  | succ q => exact hF.1
theorem smoothOrder_succ_subset (q : ℕ) :
    (smoothOrder (q + 1) : Set ((J → specialUnitary) → ℂ)) ⊆ smoothOrder q := by
  induction q with
  | zero => exact fun F hF => hF.1
  | succ q ih =>
    intro F hF
    exact ⟨hF.1, fun b ι => ⟨(hF.2 b ι).1, ih (hF.2 b ι).2⟩⟩
theorem smoothOrder_antitone {p q : ℕ} (hpq : p ≤ q) :
    (smoothOrder q : Set ((J → specialUnitary) → ℂ)) ⊆ smoothOrder p := by
  induction hpq with
  | refl => exact subset_rfl
  | step _ ih => exact (smoothOrder_succ_subset _).trans ih
theorem mem_smoothSet {F : (J → specialUnitary) → ℂ} :
    F ∈ smoothSet ↔ ∀ q, F ∈ smoothOrder q := Set.mem_iInter
theorem rightField_mem_smoothSet {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet) (b : J)
    (ι : Fin 3) : rightField b ι F ∈ smoothSet :=
  mem_smoothSet.2 fun q => ((mem_smoothSet.1 hF (q + 1)).2 b ι).2
theorem hasDerivAt_comp_shiftAt {F : (J → specialUnitary) → ℂ} {b : J} {ι : Fin 3}
    (hF : ∀ u, HasDirDerivAt b ι F u) (u : J → specialUnitary) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (shiftAt u b ι s)) (rightField b ι F (shiftAt u b ι t)) t := by
  have h₀ : HasDerivAt (fun s : ℝ => F (shiftAt (shiftAt u b ι t) b ι s))
      (rightField b ι F (shiftAt u b ι t)) (t + -t) := by
    rw [add_neg_cancel]
    exact (hF (shiftAt u b ι t)).hasDerivAt
  have h₁ := h₀.comp_add_const t (-t)
  refine h₁.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [shiftAt_shiftAt]
  congr 2
  ring
theorem hasDirDerivAt_of_hasDerivAt {F : (J → specialUnitary) → ℂ} {b : J} {ι : Fin 3}
    {u : J → specialUnitary} {c : ℂ}
    (h : HasDerivAt (fun t : ℝ => F (shiftAt u b ι t)) c 0) :
    HasDirDerivAt b ι F u ∧ rightField b ι F u = c :=
  ⟨h.differentiableAt, h.deriv⟩
theorem hasDerivAt_at_zero {F : (J → specialUnitary) → ℂ} {b : J} {ι : Fin 3}
    {u : J → specialUnitary} (h : HasDirDerivAt b ι F u) :
    HasDerivAt (fun t : ℝ => F (shiftAt u b ι t)) (rightField b ι F u) 0 := h.hasDerivAt
theorem hasDerivAlongField_holds (J : Type) : HasDerivAlongField J := by
  intro b ι F hF u
  have hdir := fun v => ((mem_smoothOrder_succ.1 hF).2 b ι).1 v
  have hcont : Continuous (rightField b ι F) :=
    continuous_of_mem_smoothOrder ((mem_smoothOrder_succ.1 hF).2 b ι).2
  have hd := hasDerivAt_comp_shiftAt hdir u
  refine ⟨contDiff_one_iff_deriv.2 ⟨fun t => (hd t).differentiableAt, ?_⟩, hd⟩
  have : deriv (fun s : ℝ => F (shiftAt u b ι s)) =
      fun t => rightField b ι F (shiftAt u b ι t) := funext fun t => (hd t).deriv
  rw [this]
  exact hcont.comp (continuous_shiftAt_time u b ι)
theorem const_mem_smoothOrder (q : ℕ) (c : ℂ) :
    (fun _ : J → specialUnitary => c) ∈ smoothOrder q := by
  induction q generalizing c with
  | zero => exact continuous_const
  | succ q ih =>
    refine ⟨continuous_const, fun b ι => ?_⟩
    have hd : ∀ u : J → specialUnitary, HasDerivAt
        (fun t : ℝ => (fun _ : J → specialUnitary => c) (shiftAt u b ι t)) 0 0 :=
      fun u => hasDerivAt_const _ _
    refine ⟨fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).1, ?_⟩
    have : rightField b ι (fun _ : J → specialUnitary => c) = fun _ => 0 :=
      funext fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).2
    rw [this]
    exact ih 0
theorem add_mem_smoothOrder (q : ℕ) {F H : (J → specialUnitary) → ℂ} (hF : F ∈ smoothOrder q)
    (hH : H ∈ smoothOrder q) : (fun u => F u + H u) ∈ smoothOrder q := by
  induction q generalizing F H with
  | zero => exact Continuous.add hF hH
  | succ q ih =>
    refine ⟨hF.1.add hH.1, fun b ι => ?_⟩
    have hd : ∀ u : J → specialUnitary, HasDerivAt
        (fun t : ℝ => (fun v => F v + H v) (shiftAt u b ι t))
        (rightField b ι F u + rightField b ι H u) 0 :=
      fun u => ((hF.2 b ι).1 u).hasDerivAt.fun_add ((hH.2 b ι).1 u).hasDerivAt
    refine ⟨fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).1, ?_⟩
    have : rightField b ι (fun u => F u + H u) = fun u => rightField b ι F u + rightField b ι H u :=
      funext fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).2
    rw [this]
    exact ih (hF.2 b ι).2 (hH.2 b ι).2
theorem hasDerivAt_rightField_mul {F H : (J → specialUnitary) → ℂ} {b : J} {ι : Fin 3}
    {u : J → specialUnitary} (hF : HasDirDerivAt b ι F u) (hH : HasDirDerivAt b ι H u) :
    HasDerivAt (fun t : ℝ => (fun v => F v * H v) (shiftAt u b ι t))
      (rightField b ι F u * H u + F u * rightField b ι H u) 0 := by
  have := (hasDerivAt_at_zero hF).fun_mul (hasDerivAt_at_zero hH)
  rw [shiftAt_zero] at this
  exact this
theorem hasDerivAt_rightField_star {F : (J → specialUnitary) → ℂ} {b : J} {ι : Fin 3}
    {u : J → specialUnitary} (hF : HasDirDerivAt b ι F u) :
    HasDerivAt (fun t : ℝ => (fun v => star (F v)) (shiftAt u b ι t))
      (star (rightField b ι F u)) 0 :=
  hF.hasDerivAt.star
theorem mul_mem_smoothOrder (q : ℕ) {F H : (J → specialUnitary) → ℂ} (hF : F ∈ smoothOrder q)
    (hH : H ∈ smoothOrder q) : (fun u => F u * H u) ∈ smoothOrder q := by
  induction q generalizing F H with
  | zero => exact Continuous.mul hF hH
  | succ q ih =>
    refine ⟨hF.1.mul hH.1, fun b ι => ?_⟩
    have hd := fun u => hasDerivAt_rightField_mul ((hF.2 b ι).1 u) ((hH.2 b ι).1 u)
    refine ⟨fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).1, ?_⟩
    have : rightField b ι (fun u => F u * H u) =
        fun u => rightField b ι F u * H u + F u * rightField b ι H u :=
      funext fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).2
    rw [this]
    exact add_mem_smoothOrder q (ih (hF.2 b ι).2 (smoothOrder_succ_subset q hH))
      (ih (smoothOrder_succ_subset q hF) (hH.2 b ι).2)
theorem star_mem_smoothOrder (q : ℕ) {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothOrder q) :
    (fun u => star (F u)) ∈ smoothOrder q := by
  induction q generalizing F with
  | zero => exact continuous_star.comp hF
  | succ q ih =>
    refine ⟨continuous_star.comp hF.1, fun b ι => ?_⟩
    have hd := fun u => hasDerivAt_rightField_star ((hF.2 b ι).1 u)
    refine ⟨fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).1, ?_⟩
    have : rightField b ι (fun u => star (F u)) = fun u => star (rightField b ι F u) :=
      funext fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).2
    rw [this]
    exact ih (hF.2 b ι).2
theorem leibnizRules_holds (J : Type) : LeibnizRules J := by
  intro b ι F H hF hH
  refine ⟨funext fun u => ?_, funext fun u => ?_⟩
  · exact (hasDirDerivAt_of_hasDerivAt
      (hasDerivAt_rightField_mul ((hF.2 b ι).1 u) ((hH.2 b ι).1 u))).2
  · exact (hasDirDerivAt_of_hasDerivAt (hasDerivAt_rightField_star ((hF.2 b ι).1 u))).2
theorem isStarClosedSubalgebraSet_of_closed {S : Set ((J → specialUnitary) → ℂ)}
    (hc : ∀ c : ℂ, (fun _ => c) ∈ S)
    (ha : ∀ F H, F ∈ S → H ∈ S → (fun u => F u + H u) ∈ S)
    (hm : ∀ F H, F ∈ S → H ∈ S → (fun u => F u * H u) ∈ S)
    (hs : ∀ F, F ∈ S → (fun u => star (F u)) ∈ S) : IsStarClosedSubalgebraSet S :=
  ⟨⟨{ carrier := S
      mul_mem' := fun {F H} hF hH => hm F H hF hH
      add_mem' := fun {F H} hF hH => ha F H hF hH
      algebraMap_mem' := fun c => hc c }, rfl⟩, hs⟩
theorem smoothOfENatOrder_coe (q : ℕ) :
    smoothOfENatOrder (J := J) (q : ℕ∞) = smoothOrder q := by
  simp [smoothOfENatOrder]
theorem smoothOfENatOrder_top :
    smoothOfENatOrder (J := J) (⊤ : ℕ∞) = smoothSet := by
  simp [smoothOfENatOrder]
theorem add_mem_smoothSet {F H : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet)
    (hH : H ∈ smoothSet) : (fun u => F u + H u) ∈ smoothSet :=
  mem_smoothSet.2 fun q =>
    add_mem_smoothOrder q (mem_smoothSet.1 hF q) (mem_smoothSet.1 hH q)
theorem mul_mem_smoothSet {F H : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet)
    (hH : H ∈ smoothSet) : (fun u => F u * H u) ∈ smoothSet :=
  mem_smoothSet.2 fun q =>
    mul_mem_smoothOrder q (mem_smoothSet.1 hF q) (mem_smoothSet.1 hH q)
theorem star_mem_smoothSet {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet) :
    (fun u => star (F u)) ∈ smoothSet :=
  mem_smoothSet.2 fun q => star_mem_smoothOrder q (mem_smoothSet.1 hF q)
theorem const_mem_smoothSet (c : ℂ) : (fun _ : J → specialUnitary => c) ∈ smoothSet :=
  mem_smoothSet.2 fun q => const_mem_smoothOrder q c
theorem isStarClosedSubalgebraSet_smoothOfENatOrder (q : ℕ∞) :
    IsStarClosedSubalgebraSet (smoothOfENatOrder (J := J) q) := by
  induction q using ENat.recTopCoe with
  | top =>
    rw [smoothOfENatOrder_top]
    exact isStarClosedSubalgebraSet_of_closed const_mem_smoothSet (fun _ _ => add_mem_smoothSet)
      (fun _ _ => mul_mem_smoothSet) (fun _ => star_mem_smoothSet)
  | coe q =>
    rw [smoothOfENatOrder_coe]
    exact isStarClosedSubalgebraSet_of_closed (const_mem_smoothOrder q)
      (fun _ _ => add_mem_smoothOrder q) (fun _ _ => mul_mem_smoothOrder q)
      (fun _ => star_mem_smoothOrder q)
end Moved
section Chain
variable {J : Type}
theorem hasDerivAt_ofReal_comp_re {F : (J → specialUnitary) → ℂ} (hre : ∀ u, (F u).im = 0)
    {b : J} {ι : Fin 3} {u : J → specialUnitary} (hF : HasDirDerivAt b ι F u) {φ : ℝ → ℝ}
    (hφ : DifferentiableAt ℝ φ (F u).re) :
    HasDerivAt (fun t : ℝ => (fun v => ((φ (F v).re : ℝ) : ℂ)) (shiftAt u b ι t))
      (((deriv φ (F u).re : ℝ) : ℂ) * rightField b ι F u) 0 := by
  have hg := hasDerivAt_at_zero hF
  have him : (rightField b ι F u).im = 0 := by
    have h₁ : HasDerivAt (fun t : ℝ => (F (shiftAt u b ι t)).im) (rightField b ι F u).im 0 :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hg
    have h₂ : (fun t : ℝ => (F (shiftAt u b ι t)).im) = fun _ => 0 := funext fun t => hre _
    rw [h₂] at h₁
    exact h₁.unique (hasDerivAt_const _ _)
  have hr : HasDerivAt (fun t : ℝ => (F (shiftAt u b ι t)).re) (rightField b ι F u).re 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hg
  have hφ' : HasDerivAt φ (deriv φ (F u).re) (F (shiftAt u b ι 0)).re := by
    rw [shiftAt_zero]
    exact hφ.hasDerivAt
  have hc := (hφ'.comp 0 hr).ofReal_comp
  refine hc.congr_deriv ?_
  apply Complex.ext <;> simp [him]
theorem realComp_mem_smoothOrder (q : ℕ) {F : (J → specialUnitary) → ℂ} {I : Set ℝ} {φ : ℝ → ℝ}
    (hF : F ∈ smoothOrder q) (hre : ∀ u, (F u).im = 0) (hI : IsOpen I) (hv : ∀ u, (F u).re ∈ I)
    (hφ : ContDiffOn ℝ ∞ φ I) : (fun u => ((φ (F u).re : ℝ) : ℂ)) ∈ smoothOrder q := by
  have hcont : ∀ {φ : ℝ → ℝ} {F : (J → specialUnitary) → ℂ}, Continuous F →
      (∀ u, (F u).re ∈ I) → ContDiffOn ℝ ∞ φ I → Continuous fun u => ((φ (F u).re : ℝ) : ℂ) := by
    intro φ F hF hv hφ
    exact Complex.continuous_ofReal.comp
      (hφ.continuousOn.comp_continuous (Complex.continuous_re.comp hF) hv)
  induction q generalizing F φ with
  | zero => exact hcont hF hv hφ
  | succ q ih =>
    refine ⟨hcont hF.1 hv hφ, fun b ι => ?_⟩
    have hdiff : ∀ u, DifferentiableAt ℝ φ (F u).re := fun u =>
      (hφ.differentiableOn (by simp)).differentiableAt (hI.mem_nhds (hv u))
    have hd := fun u => hasDerivAt_ofReal_comp_re hre ((hF.2 b ι).1 u) (hdiff u)
    refine ⟨fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).1, ?_⟩
    have : rightField b ι (fun u => ((φ (F u).re : ℝ) : ℂ)) =
        fun u => ((deriv φ (F u).re : ℝ) : ℂ) * rightField b ι F u :=
      funext fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).2
    rw [this]
    exact mul_mem_smoothOrder q (ih (smoothOrder_succ_subset q hF) hre hv
      ((contDiffOn_infty_iff_deriv_of_isOpen hI).1 hφ).2) (hF.2 b ι).2
theorem chainRule_holds (J : Type) : ChainRuleHolds J := by
  intro q F I φ hF hre hI _ hv hφ
  have hfield : F ∈ smoothOrder 1 → ∀ (b : J) (ι : Fin 3) (u : J → specialUnitary),
      rightField b ι (fun v => ((φ (F v).re : ℝ) : ℂ)) u =
        ((deriv φ (F u).re : ℝ) : ℂ) * rightField b ι F u := fun h1 b ι u =>
    (hasDirDerivAt_of_hasDerivAt (hasDerivAt_ofReal_comp_re hre ((h1.2 b ι).1 u)
      ((hφ.differentiableOn (by simp)).differentiableAt (hI.mem_nhds (hv u))))).2
  induction q using ENat.recTopCoe with
  | top =>
    rw [smoothOfENatOrder_top] at hF ⊢
    exact ⟨mem_smoothSet.2 fun n =>
        realComp_mem_smoothOrder n (mem_smoothSet.1 hF n) hre hI hv hφ,
      fun _ => hfield (mem_smoothSet.1 hF 1)⟩
  | coe q =>
    rw [smoothOfENatOrder_coe] at hF ⊢
    refine ⟨realComp_mem_smoothOrder q hF hre hI hv hφ,
      fun h1 => hfield (smoothOrder_antitone ?_ hF)⟩
    exact_mod_cast h1
theorem realComp_mem_smoothSet {F : (J → specialUnitary) → ℂ} {I : Set ℝ} {φ : ℝ → ℝ}
    (hF : F ∈ smoothSet) (hre : ∀ u, (F u).im = 0) (hI : IsOpen I) (hv : ∀ u, (F u).re ∈ I)
    (hφ : ContDiffOn ℝ ∞ φ I) : (fun u => ((φ (F u).re : ℝ) : ℂ)) ∈ smoothSet :=
  mem_smoothSet.2 fun n => realComp_mem_smoothOrder n (mem_smoothSet.1 hF n) hre hI hv hφ
theorem cexp_mem_smoothSet {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet)
    (hre : ∀ u, (F u).im = 0) : (fun u => Complex.exp (F u)) ∈ smoothSet := by
  have h := realComp_mem_smoothSet (I := Set.univ) (φ := Real.exp) hF hre isOpen_univ
    (fun _ => trivial) Real.contDiff_exp.contDiffOn
  have he : (fun u => Complex.exp (F u)) = fun u => ((Real.exp (F u).re : ℝ) : ℂ) := by
    funext u
    have : F u = (((F u).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hre u])
    rw [Complex.ofReal_exp, ← this]
  rw [he]
  exact h
theorem expAndInvSmooth_holds (J : Type) : ExpAndInvSmooth J := by
  refine ⟨fun F hF hre => cexp_mem_smoothSet hF hre, fun F hF hpos => ?_⟩
  have hφ : ContDiffOn ℝ ∞ (Inv.inv : ℝ → ℝ) (Set.Ioi 0) :=
    (contDiffOn_inv ℝ).mono fun x hx => ne_of_gt hx
  have h := realComp_mem_smoothSet (I := Set.Ioi 0) (φ := Inv.inv) hF (fun u => (hpos u).1)
    isOpen_Ioi (fun u => (hpos u).2) hφ
  have he : (fun u => (F u)⁻¹) = fun u => ((((F u).re)⁻¹ : ℝ) : ℂ) := by
    funext u
    have : F u = (((F u).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [(hpos u).1])
    rw [Complex.ofReal_inv, ← this]
  rw [he]
  exact h
def entryFn (b : J) (r s : Fin 2) (u : J → specialUnitary) : ℂ := (u b : ComplexMatrix2) r s
theorem continuous_entryFn (b : J) (r s : Fin 2) : Continuous (entryFn b r s) :=
  Continuous.matrix_elem (A := fun u : J → specialUnitary => (u b : ComplexMatrix2))
    (continuous_subtype_val.comp (continuous_apply b)) r s
theorem hasDerivAt_entryFn_shiftAt (h : UnitaryLogConjugationProperties)
    (u : J → specialUnitary) (b : J) (ι : Fin 3) (r s : Fin 2) :
    HasDerivAt (fun t : ℝ => entryFn b r s (shiftAt u b ι t))
      ((u b : ComplexMatrix2) r 0 * lieGenerator ι 0 s +
        (u b : ComplexMatrix2) r 1 * lieGenerator ι 1 s) 0 := by
  have he : (fun t : ℝ => entryFn b r s (shiftAt u b ι t)) = fun t : ℝ =>
      (u b : ComplexMatrix2) r 0 * (oneParam ι t : ComplexMatrix2) 0 s +
        (u b : ComplexMatrix2) r 1 * (oneParam ι t : ComplexMatrix2) 1 s := by
    funext t
    simp [entryFn, shiftAt_apply_self, Matrix.mul_apply, Fin.sum_univ_two]
  rw [he]
  exact ((hasDerivAt_oneParam_entry h ι 0 s).const_mul _).fun_add
    ((hasDerivAt_oneParam_entry h ι 1 s).const_mul _)
theorem entryFn_mem_smoothOrder (h : UnitaryLogConjugationProperties) (q : ℕ) (b : J)
    (r s : Fin 2) : entryFn b r s ∈ smoothOrder q := by
  induction q generalizing b r s with
  | zero => exact continuous_entryFn b r s
  | succ q ih =>
    refine ⟨continuous_entryFn b r s, fun c ι => ?_⟩
    by_cases hc : c = b
    · subst hc
      have hd := fun u : J → specialUnitary => hasDerivAt_entryFn_shiftAt h u c ι r s
      refine ⟨fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).1, ?_⟩
      have : rightField c ι (entryFn c r s) = fun u =>
          entryFn c r 0 u * lieGenerator ι 0 s + entryFn c r 1 u * lieGenerator ι 1 s :=
        funext fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).2
      rw [this]
      exact add_mem_smoothOrder q (mul_mem_smoothOrder q (ih c r 0) (const_mem_smoothOrder q _))
        (mul_mem_smoothOrder q (ih c r 1) (const_mem_smoothOrder q _))
    · have hd : ∀ u : J → specialUnitary, HasDerivAt
          (fun t : ℝ => entryFn b r s (shiftAt u c ι t)) 0 0 := by
        intro u
        have : (fun t : ℝ => entryFn b r s (shiftAt u c ι t)) =
            fun _ => entryFn b r s u := by
          funext t
          simp [entryFn, shiftAt_apply_of_ne u (Ne.symm hc)]
        rw [this]
        exact hasDerivAt_const _ _
      refine ⟨fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).1, ?_⟩
      have : rightField c ι (entryFn b r s) = fun _ => 0 :=
        funext fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).2
      rw [this]
      exact const_mem_smoothOrder q 0
theorem entryFn_mem_smoothSet (h : UnitaryLogConjugationProperties) (b : J)
    (r s : Fin 2) : entryFn b r s ∈ smoothSet :=
  mem_smoothSet.2 fun q => entryFn_mem_smoothOrder h q b r s
theorem polynomial_mem_smoothSet (h : UnitaryLogConjugationProperties)
    (p : MvPolynomial (EntryVar J) ℂ) :
    (fun u : J → specialUnitary => MvPolynomial.eval (entryEval u) p) ∈ smoothSet := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact const_mem_smoothSet a
  | add p p' hp hp' =>
    simp only [map_add]
    exact add_mem_smoothSet hp hp'
  | mul_X p n hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine mul_mem_smoothSet hp ?_
    rcases n with ⟨b, r, s⟩ | ⟨b, r, s⟩
    · exact entryFn_mem_smoothSet h b r s
    · exact star_mem_smoothSet (entryFn_mem_smoothSet h b r s)
theorem singleBondWeight_comp_mem_smoothSet (β : ℝ) (G : (J → specialUnitary) → specialUnitary)
    (hs : (fun u => fullTrace (G u : ComplexMatrix2)) ∈ smoothSet)
    (hre : ∀ w : specialUnitary, (fullTrace (w : ComplexMatrix2)).im = 0) :
    (fun u => InfiniteLattice.singleBondWeight β (G u)) ∈ smoothSet := by
  have hF : (fun u => ((-β : ℝ) : ℂ) + ((β / 2 : ℝ) : ℂ) * fullTrace (G u : ComplexMatrix2)) ∈
      smoothSet :=
    add_mem_smoothSet (const_mem_smoothSet _) (mul_mem_smoothSet (const_mem_smoothSet _) hs)
  have h := cexp_mem_smoothSet hF (fun u => by simp [Complex.mul_im, hre (G u)])
  have he : (fun u => InfiniteLattice.singleBondWeight β (G u)) =
      fun u => Complex.exp (((-β : ℝ) : ℂ) + ((β / 2 : ℝ) : ℂ) * fullTrace (G u : ComplexMatrix2)) := by
    funext u
    rw [InfiniteLattice.singleBondWeight]
    congr 1
    push_cast
    ring
  rw [he]
  exact h
theorem coe_inv_specialUnitary (w : specialUnitary) :
    ((w⁻¹ : specialUnitary) : ComplexMatrix2) = star (w : ComplexMatrix2) := rfl
theorem fullTrace_mul_inv (v w : specialUnitary) :
    fullTrace ((v * w⁻¹ : specialUnitary) : ComplexMatrix2) =
      (v : ComplexMatrix2) 0 0 * star ((w : ComplexMatrix2) 0 0) +
        (v : ComplexMatrix2) 0 1 * star ((w : ComplexMatrix2) 0 1) +
        ((v : ComplexMatrix2) 1 0 * star ((w : ComplexMatrix2) 1 0) +
          (v : ComplexMatrix2) 1 1 * star ((w : ComplexMatrix2) 1 1)) := by
  simp [fullTrace, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, coe_inv_specialUnitary,
    Matrix.star_apply]
theorem fullTrace_mul_inv_mem_smoothSet (h : UnitaryLogConjugationProperties) (b b' : J) :
    (fun u : J → specialUnitary => fullTrace ((u b * (u b')⁻¹ : specialUnitary) : ComplexMatrix2)) ∈
      smoothSet := by
  have he : (fun u : J → specialUnitary =>
      fullTrace ((u b * (u b')⁻¹ : specialUnitary) : ComplexMatrix2)) = fun u =>
      entryFn b 0 0 u * star (entryFn b' 0 0 u) +
        entryFn b 0 1 u * star (entryFn b' 0 1 u) +
        (entryFn b 1 0 u * star (entryFn b' 1 0 u) +
          entryFn b 1 1 u * star (entryFn b' 1 1 u)) :=
    funext fun u => fullTrace_mul_inv _ _
  rw [he]
  have hp : ∀ r s, (fun u => entryFn b r s u * star (entryFn b' r s u)) ∈ smoothSet :=
    fun r s => mul_mem_smoothSet (entryFn_mem_smoothSet h b r s)
      (star_mem_smoothSet (entryFn_mem_smoothSet h b' r s))
  exact add_mem_smoothSet (add_mem_smoothSet (hp 0 0) (hp 0 1))
    (add_mem_smoothSet (hp 1 0) (hp 1 1))
theorem fullTrace_im (h : InfiniteLattice.TraceAndSingleBondWeight) (w : specialUnitary) :
    (fullTrace (w : ComplexMatrix2)).im = 0 :=
  (h.1.2 w).2.2.2.2.2.1
theorem singleWeightSmooth_holds (h : UnitaryLogConjugationProperties)
    (h' : InfiniteLattice.TraceAndSingleBondWeight) : SingleWeightSmooth := by
  intro β _ K _
  refine singleBondWeight_comp_mem_smoothSet β (fun v : K → specialUnitary => v default) ?_
    (fullTrace_im h')
  have he : (fun v : K → specialUnitary => fullTrace (v default : ComplexMatrix2)) =
      fun v => entryFn default 0 0 v + entryFn default 1 1 v := by
    funext v
    simp [fullTrace, Matrix.trace_fin_two, entryFn]
  rw [he]
  exact add_mem_smoothSet (entryFn_mem_smoothSet h _ 0 0) (entryFn_mem_smoothSet h _ 1 1)
theorem polynomialAndBondWeightSmooth_holds (h : UnitaryLogConjugationProperties)
    (h' : InfiniteLattice.TraceAndSingleBondWeight) (J : Type) :
    PolynomialAndBondWeightSmooth J := by
  refine ⟨fun F ⟨p, hp⟩ => ?_, fun β hβ b b' _ => ⟨?_, fun u => ⟨?_, ?_⟩⟩⟩
  · rw [show F = fun u => MvPolynomial.eval (entryEval u) p from funext hp]
    exact polynomial_mem_smoothSet h p
  · exact singleBondWeight_comp_mem_smoothSet β (fun u : J → specialUnitary => u b * (u b')⁻¹)
      (fullTrace_mul_inv_mem_smoothSet h b b') (fullTrace_im h')
  · exact (h'.2 β hβ).1.1 _
  · exact (Real.exp_pos _).trans_le ((h'.2 β hβ).2.1 _).1
end Chain
section Integrals
open TransferOperators.GibbsHaarKernels
variable {J : Type}
theorem isProbabilityMeasure_haarPi (K : Type) [Countable K] :
    IsProbabilityMeasure (haarPi K) := by
  unfold haarPi
  infer_instance
theorem exists_norm_bound {F : (J → specialUnitary) → ℂ} (hF : Continuous F) :
    ∃ C, ∀ u, ‖F u‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_range hF.norm).bddAbove
  exact ⟨C, fun u => hC ⟨u, rfl⟩⟩
theorem integrable_haarPi_of_continuous [Finite J] {F : (J → specialUnitary) → ℂ}
    (hF : Continuous F) : Integrable F (haarPi J) := by
  have := isProbabilityMeasure_haarPi J
  obtain ⟨C, hC⟩ := exists_norm_bound hF
  exact Integrable.of_bound hF.aestronglyMeasurable C (Eventually.of_forall hC)
theorem hasDerivAt_integral_of_bounded {X : Type} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {g g' : ℝ → X → ℂ} (hm : ∀ t, AEStronglyMeasurable (g t) μ)
    (hm' : AEStronglyMeasurable (g' 0) μ) {C : ℝ} (hb : ∀ t x, ‖g' t x‖ ≤ C)
    (hd : ∀ t x, HasDerivAt (fun s => g s x) (g' t x) t) (hi : Integrable (g 0) μ) :
    HasDerivAt (fun t => ∫ x, g t x ∂μ) (∫ x, g' 0 x ∂μ) 0 :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) (bound := fun _ => C)
    univ_mem (Eventually.of_forall hm) hi hm' (Eventually.of_forall fun x t _ => hb t x)
    (integrable_const C) (Eventually.of_forall fun x t _ => hd t x)).2
theorem integral_comp_shiftAt [Finite J] (hs : HaarPiInvariance J)
    {K : (J → specialUnitary) → ℂ} (hK : Continuous K) (b : J) (ι : Fin 3) (t : ℝ) :
    ∫ u, K (shiftAt u b ι t) ∂haarPi J = ∫ u, K u ∂haarPi J := by
  classical
  have hmp := hs.1 1 (Function.update 1 b (oneParam ι t))
  have hT : (fun (u : J → specialUnitary) (c : J) =>
      (1 : J → specialUnitary) c * u c *
        Function.update (1 : J → specialUnitary) b (oneParam ι t) c) =
      fun u => shiftAt u b ι t := by
    funext u c
    by_cases hc : c = b
    · subst hc
      simp [shiftAt_apply_self]
    · simp [shiftAt_apply_of_ne u hc, Function.update_of_ne hc]
  rw [hT] at hmp
  have hK' : AEStronglyMeasurable K
      (Measure.map (fun u : J → specialUnitary => shiftAt u b ι t) (haarPi J)) := by
    rw [hmp.map_eq]
    exact hK.aestronglyMeasurable
  rw [← integral_map hmp.aemeasurable hK', hmp.map_eq]
theorem integral_rightField_eq_zero [Finite J] (hs : HaarPiInvariance J)
    {K : (J → specialUnitary) → ℂ} (hK : K ∈ smoothOrder 1) (b : J) (ι : Fin 3) :
    ∫ u, rightField b ι K u ∂haarPi J = 0 := by
  have := isProbabilityMeasure_haarPi J
  have hdir := (hK.2 b ι).1
  have hcont : Continuous (rightField b ι K) := continuous_of_mem_smoothOrder (hK.2 b ι).2
  obtain ⟨C, hC⟩ := exists_norm_bound hcont
  have hd := hasDerivAt_integral_of_bounded (μ := haarPi J)
    (g := fun t u => K (shiftAt u b ι t)) (g' := fun t u => rightField b ι K (shiftAt u b ι t))
    (fun t => (hK.1.comp (continuous_shiftAt_config b ι t)).aestronglyMeasurable)
    (hcont.comp (continuous_shiftAt_config b ι 0)).aestronglyMeasurable
    (fun t u => hC _) (fun t u => hasDerivAt_comp_shiftAt hdir u t)
    (integrable_haarPi_of_continuous (hK.1.comp (continuous_shiftAt_config b ι 0)))
  have hconst : (fun t : ℝ => ∫ u, K (shiftAt u b ι t) ∂haarPi J) =
      fun _ => ∫ u, K u ∂haarPi J := funext fun t => integral_comp_shiftAt hs hK.1 b ι t
  rw [hconst] at hd
  simp only [shiftAt_zero] at hd
  exact hd.unique (hasDerivAt_const _ _)
theorem integral_rightField_mul [Finite J] (hs : HaarPiInvariance J) (b : J) (ι : Fin 3)
    {F H : (J → specialUnitary) → ℂ} (hF : F ∈ smoothOrder 1) (hH : H ∈ smoothOrder 1) :
    ∫ u, rightField b ι F u * H u ∂haarPi J = -∫ u, F u * rightField b ι H u ∂haarPi J := by
  have h₀ := integral_rightField_eq_zero hs (mul_mem_smoothOrder 1 hF hH) b ι
  rw [(leibnizRules_holds J b ι F H hF hH).1] at h₀
  have hcF : Continuous (rightField b ι F) := continuous_of_mem_smoothOrder (hF.2 b ι).2
  have hcH : Continuous (rightField b ι H) := continuous_of_mem_smoothOrder (hH.2 b ι).2
  have hadd : ∫ u, (rightField b ι F u * H u + F u * rightField b ι H u) ∂haarPi J =
      ∫ u, rightField b ι F u * H u ∂haarPi J + ∫ u, F u * rightField b ι H u ∂haarPi J :=
    integral_add (integrable_haarPi_of_continuous (hcF.mul hH.1))
      (integrable_haarPi_of_continuous (hF.1.mul hcH))
  exact eq_neg_of_add_eq_zero_left (hadd.symm.trans h₀)
theorem fieldsSkewAdjoint_holds [Finite J] (hs : HaarPiInvariance J) : FieldsSkewAdjoint J := by
  intro b ι F H hF hH
  refine ⟨integral_rightField_mul hs b ι hF hH, ?_⟩
  have := integral_rightField_mul hs b ι (star_mem_smoothOrder 1 hF) hH
  rw [(leibnizRules_holds J b ι F H hF hH).2] at this
  exact this
theorem norm_le_supNorm {F : (J → specialUnitary) → ℂ} (hF : Continuous F)
    (u : J → specialUnitary) : ‖F u‖ ≤ supNorm F :=
  le_ciSup (f := fun u => ‖F u‖) (isCompact_range hF.norm).bddAbove u
theorem fieldWord_append_singleton (w : List (J × Fin 3)) (x : J × Fin 3)
    (F : (J → specialUnitary) → ℂ) :
    fieldWord (w ++ [x]) F = fieldWord w (rightField x.1 x.2 F) := by
  simp [fieldWord, List.foldr_append]
section Series
variable {A : Type} {F : A → (J → specialUnitary) → ℂ}
theorem continuous_of_mem_smoothSet {G : (J → specialUnitary) → ℂ} (hG : G ∈ smoothSet) :
    Continuous G :=
  continuous_of_mem_smoothOrder (mem_smoothSet.1 hG 0)
theorem summable_apply (hF : ∀ α, F α ∈ smoothSet)
    (hw : ∀ w : List (J × Fin 3), Summable fun α => supNorm (fieldWord w (F α)))
    (u : J → specialUnitary) : Summable fun α => F α u :=
  Summable.of_norm_bounded (hw []) fun α =>
    norm_le_supNorm (continuous_of_mem_smoothSet (hF α)) u
theorem continuous_tsum_apply (hF : ∀ α, F α ∈ smoothSet)
    (hw : ∀ w : List (J × Fin 3), Summable fun α => supNorm (fieldWord w (F α))) :
    Continuous fun u => ∑' α, F α u :=
  continuous_tsum (fun α => continuous_of_mem_smoothSet (hF α)) (hw [])
    fun α u => norm_le_supNorm (continuous_of_mem_smoothSet (hF α)) u
theorem hasDerivAt_tsum_comp_shiftAt (hF : ∀ α, F α ∈ smoothSet)
    (hw : ∀ w : List (J × Fin 3), Summable fun α => supNorm (fieldWord w (F α)))
    (b : J) (ι : Fin 3) (u : J → specialUnitary) :
    HasDerivAt (fun t : ℝ => (fun v => ∑' α, F α v) (shiftAt u b ι t))
      (∑' α, rightField b ι (F α) u) 0 := by
  have h₁ : ∀ α, F α ∈ smoothOrder 1 := fun α => mem_smoothSet.1 (hF α) 1
  have hd := hasDerivAt_tsum (y₀ := (0 : ℝ)) (u := fun α => supNorm (rightField b ι (F α)))
    (g := fun α t => F α (shiftAt u b ι t))
    (g' := fun α t => rightField b ι (F α) (shiftAt u b ι t)) (hw [(b, ι)])
    (fun α t => hasDerivAt_comp_shiftAt ((h₁ α).2 b ι).1 u t)
    (fun α t => norm_le_supNorm (continuous_of_mem_smoothOrder ((h₁ α).2 b ι).2) _)
    (summable_apply hF hw _) 0
  simpa only [shiftAt_zero] using hd
theorem summable_supNorm_rightField
    (hw : ∀ w : List (J × Fin 3), Summable fun α => supNorm (fieldWord w (F α)))
    (b : J) (ι : Fin 3) (w : List (J × Fin 3)) :
    Summable fun α => supNorm (fieldWord w (rightField b ι (F α))) := by
  have := hw (w ++ [(b, ι)])
  simpa only [fieldWord_append_singleton] using this
theorem tsum_mem_smoothOrder (q : ℕ) (hF : ∀ α, F α ∈ smoothSet)
    (hw : ∀ w : List (J × Fin 3), Summable fun α => supNorm (fieldWord w (F α))) :
    (fun u => ∑' α, F α u) ∈ smoothOrder q := by
  induction q generalizing F with
  | zero => exact continuous_tsum_apply hF hw
  | succ q ih =>
    refine ⟨continuous_tsum_apply hF hw, fun b ι => ?_⟩
    have hd := hasDerivAt_tsum_comp_shiftAt hF hw b ι
    refine ⟨fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).1, ?_⟩
    have : rightField b ι (fun u => ∑' α, F α u) = fun u => ∑' α, rightField b ι (F α) u :=
      funext fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).2
    rw [this]
    exact ih (fun α => rightField_mem_smoothSet (hF α) b ι) (summable_supNorm_rightField hw b ι)
theorem hasSum_fieldWord (w : List (J × Fin 3)) (hF : ∀ α, F α ∈ smoothSet)
    (hw : ∀ w : List (J × Fin 3), Summable fun α => supNorm (fieldWord w (F α)))
    (u : J → specialUnitary) :
    HasSum (fun α => fieldWord w (F α) u) (fieldWord w (fun v => ∑' α, F α v) u) := by
  induction w using List.reverseRecOn generalizing F with
  | nil => exact (summable_apply hF hw u).hasSum
  | append_singleton w x ih =>
    have hfield : rightField x.1 x.2 (fun v => ∑' α, F α v) =
        fun v => ∑' α, rightField x.1 x.2 (F α) v :=
      funext fun v =>
        (hasDirDerivAt_of_hasDerivAt (hasDerivAt_tsum_comp_shiftAt hF hw x.1 x.2 v)).2
    simp only [fieldWord_append_singleton, hfield]
    exact ih (fun α => rightField_mem_smoothSet (hF α) x.1 x.2)
      (summable_supNorm_rightField hw x.1 x.2)
end Series
theorem seriesSmooth_holds (J : Type) : SeriesSmooth J := by
  intro A _ F hF hw
  exact ⟨mem_smoothSet.2 fun q => tsum_mem_smoothOrder q hF hw,
    fun w u => hasSum_fieldWord w hF hw u⟩
theorem comp_mem_smoothOrder_of_equivariant {K : Type}
    (e : (K → specialUnitary) → (J → specialUnitary)) (he : Continuous e)
    (hmove : ∀ b : K, (∃ c : J, ∀ v ι t, e (shiftAt v b ι t) = shiftAt (e v) c ι t) ∨
      ∀ v ι t, e (shiftAt v b ι t) = e v)
    (q : ℕ) {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothOrder q) :
    (fun v => F (e v)) ∈ smoothOrder q := by
  induction q generalizing F with
  | zero => exact Continuous.comp hF he
  | succ q ih =>
    refine ⟨hF.1.comp he, fun b ι => ?_⟩
    rcases hmove b with ⟨c, hc⟩ | hc
    · have hd : ∀ v : K → specialUnitary, HasDerivAt
          (fun t : ℝ => (fun v => F (e v)) (shiftAt v b ι t)) (rightField c ι F (e v)) 0 := by
        intro v
        simp only [hc]
        exact hasDerivAt_at_zero ((hF.2 c ι).1 (e v))
      refine ⟨fun v => (hasDirDerivAt_of_hasDerivAt (hd v)).1, ?_⟩
      have : rightField b ι (fun v => F (e v)) = fun v => rightField c ι F (e v) :=
        funext fun v => (hasDirDerivAt_of_hasDerivAt (hd v)).2
      rw [this]
      exact ih (hF.2 c ι).2
    · have hd : ∀ v : K → specialUnitary, HasDerivAt
          (fun t : ℝ => (fun v => F (e v)) (shiftAt v b ι t)) 0 0 := by
        intro v
        simp only [hc]
        exact hasDerivAt_const _ _
      refine ⟨fun v => (hasDirDerivAt_of_hasDerivAt (hd v)).1, ?_⟩
      have : rightField b ι (fun v => F (e v)) = fun _ => 0 :=
        funext fun v => (hasDirDerivAt_of_hasDerivAt (hd v)).2
      rw [this]
      exact const_mem_smoothOrder q 0
theorem precomp_mem_smoothOrder {K : Type} {c : J → K} (hc : Function.Injective c) (q : ℕ)
    {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothOrder q) :
    (fun x : K → specialUnitary => F (x ∘ c)) ∈ smoothOrder q := by
  classical
  refine comp_mem_smoothOrder_of_equivariant (fun x : K → specialUnitary => x ∘ c)
    (continuous_pi fun a => continuous_apply (c a)) (fun b => ?_) q hF
  by_cases hb : b ∈ Set.range c
  · obtain ⟨a, rfl⟩ := hb
    refine Or.inl ⟨a, fun v ι t => ?_⟩
    simp only [shiftAt]
    rw [Function.update_comp_eq_of_injective _ hc]
    rfl
  · exact Or.inr fun v ι t => Function.update_comp_eq_of_notMem_range _ _ hb
theorem precomp_mem_smoothSet {K : Type} {c : J → K} (hc : Function.Injective c)
    {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothSet) :
    (fun x : K → specialUnitary => F (x ∘ c)) ∈ smoothSet :=
  mem_smoothSet.2 fun q => precomp_mem_smoothOrder hc q (mem_smoothSet.1 hF q)
theorem glue_shiftAt (B : Set J) (z : ↥Bᶜ → specialUnitary) (v : ↥B → specialUnitary) (b : ↥B)
    (ι : Fin 3) (t : ℝ) :
    glue B (shiftAt v b ι t) z = shiftAt (glue B v z) b.1 ι t := by
  funext x
  by_cases hx : x = b.1
  · subst hx
    rw [glue_of_mem, shiftAt_apply_self, shiftAt_apply_self, glue_of_mem]
  · rw [shiftAt_apply_of_ne _ hx]
    by_cases hxB : x ∈ B
    · have hne : (⟨x, hxB⟩ : ↥B) ≠ b := fun e => hx (congrArg Subtype.val e)
      have h₁ := glue_of_mem B (shiftAt v b ι t) z ⟨x, hxB⟩
      have h₂ := glue_of_mem B v z ⟨x, hxB⟩
      rw [shiftAt_apply_of_ne v hne] at h₁
      exact h₁.trans h₂.symm
    · exact (glue_of_notMem B _ z ⟨x, hxB⟩).trans
        (glue_of_notMem B v z ⟨x, hxB⟩).symm
theorem glue_mem_smoothOrder (B : Set J) (z : ↥Bᶜ → specialUnitary) (q : ℕ)
    {F : (J → specialUnitary) → ℂ} (hF : F ∈ smoothOrder q) :
    (fun v : ↥B → specialUnitary => F (glue B v z)) ∈ smoothOrder q := by
  refine comp_mem_smoothOrder_of_equivariant (fun v : ↥B → specialUnitary => glue B v z) ?_
    (fun b => Or.inl ⟨b.1, fun v ι t => glue_shiftAt B z v b ι t⟩) q hF
  refine continuous_pi fun x => ?_
  by_cases hx : x ∈ B
  · have : (fun v : ↥B → specialUnitary => glue B v z x) = fun v => v ⟨x, hx⟩ :=
      funext fun v => glue_of_mem B v z ⟨x, hx⟩
    rw [this]
    exact continuous_apply _
  · have : (fun v : ↥B → specialUnitary => glue B v z x) = fun _ => z ⟨x, hx⟩ :=
      funext fun v => glue_of_notMem B v z ⟨x, hx⟩
    rw [this]
    exact continuous_const
theorem shiftAt_sumElim_inl {K : Type} (u : J → specialUnitary) (v : K → specialUnitary) (b : J)
    (ι : Fin 3) (t : ℝ) :
    shiftAt (Sum.elim u v) (Sum.inl b) ι t = Sum.elim (shiftAt u b ι t) v := by
  classical
  simp only [shiftAt, Sum.elim_inl, Sum.update_elim_inl]
theorem continuous_sumElim_right {K : Type} (u : J → specialUnitary) :
    Continuous fun v : K → specialUnitary => (Sum.elim u v : J ⊕ K → specialUnitary) :=
  continuous_pi fun x => by
    cases x with
    | inl a => exact continuous_const
    | inr a => exact continuous_apply a
theorem continuous_integral_sumElim {K : Type} [Finite J] [Finite K]
    {Φ : (J ⊕ K → specialUnitary) → ℂ} (hΦ : Continuous Φ) :
    Continuous fun u : J → specialUnitary => ∫ v, Φ (Sum.elim u v) ∂haarPi K := by
  have := isProbabilityMeasure_haarPi K
  have hcu : Continuous (Function.uncurry fun (u : J → specialUnitary) (v : K → specialUnitary) =>
      Φ (Sum.elim u v)) := by
    refine hΦ.comp (continuous_pi fun x => ?_)
    cases x with
    | inl a => exact (continuous_apply a).comp continuous_fst
    | inr a => exact (continuous_apply a).comp continuous_snd
  have := continuous_parametric_integral_of_continuous (μ := haarPi K) hcu
    (isCompact_univ (X := K → specialUnitary))
  simpa only [Measure.restrict_univ] using this
theorem integral_sumElim_mem_smoothOrder {K : Type} [Finite J] [Finite K] (q : ℕ)
    {Φ : (J ⊕ K → specialUnitary) → ℂ} (hΦ : Φ ∈ smoothOrder q) :
    (fun u : J → specialUnitary => ∫ v, Φ (Sum.elim u v) ∂haarPi K) ∈ smoothOrder q := by
  have := isProbabilityMeasure_haarPi K
  induction q generalizing Φ with
  | zero => exact continuous_integral_sumElim hΦ
  | succ q ih =>
    refine ⟨continuous_integral_sumElim hΦ.1, fun b ι => ?_⟩
    have hdir := (hΦ.2 (Sum.inl b) ι).1
    have hcont : Continuous (rightField (Sum.inl b) ι Φ) :=
      continuous_of_mem_smoothOrder (hΦ.2 (Sum.inl b) ι).2
    obtain ⟨C, hC⟩ := exists_norm_bound hcont
    have hd : ∀ u : J → specialUnitary, HasDerivAt
        (fun t : ℝ => (fun u : J → specialUnitary => ∫ v, Φ (Sum.elim u v) ∂haarPi K)
          (shiftAt u b ι t))
        (∫ v, rightField (Sum.inl b) ι Φ (Sum.elim u v) ∂haarPi K) 0 := by
      intro u
      have hm : ∀ {G : (J ⊕ K → specialUnitary) → ℂ}, Continuous G → ∀ t : ℝ,
          Continuous fun v : K → specialUnitary =>
            G (shiftAt (Sum.elim u v) (Sum.inl b) ι t) := fun hG t =>
        hG.comp ((continuous_shiftAt_config _ ι t).comp (continuous_sumElim_right u))
      have := hasDerivAt_integral_of_bounded (μ := haarPi K)
        (g := fun t v => Φ (shiftAt (Sum.elim u v) (Sum.inl b) ι t))
        (g' := fun t v => rightField (Sum.inl b) ι Φ (shiftAt (Sum.elim u v) (Sum.inl b) ι t))
        (fun t => (hm hΦ.1 t).aestronglyMeasurable) (hm hcont 0).aestronglyMeasurable
        (fun t v => hC _) (fun t v => hasDerivAt_comp_shiftAt hdir _ t)
        (integrable_haarPi_of_continuous (hm hΦ.1 0))
      simpa only [shiftAt_sumElim_inl, shiftAt_zero] using this
    refine ⟨fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).1, ?_⟩
    have : rightField b ι (fun u : J → specialUnitary => ∫ v, Φ (Sum.elim u v) ∂haarPi K) =
        fun u => ∫ v, rightField (Sum.inl b) ι Φ (Sum.elim u v) ∂haarPi K :=
      funext fun u => (hasDirDerivAt_of_hasDerivAt (hd u)).2
    rw [this]
    exact ih (hΦ.2 (Sum.inl b) ι).2
theorem partialVariablesSmooth_holds (h : UnitaryLogConjugationProperties)
    (h' : InfiniteLattice.TraceAndSingleBondWeight) (J : Type) [Finite J] :
    PartialVariablesSmooth J := by
  classical
  intro B _ _
  refine ⟨fun F hF z => mem_smoothSet.2 fun q => glue_mem_smoothOrder B z q
    (mem_smoothSet.1 hF q), fun φ hφ => precomp_mem_smoothSet Subtype.val_injective hφ,
    fun F A hF hA => ?_⟩
  let c₁ : ↥B ⊕ ↥B → J ⊕ ↥B := Sum.map Subtype.val id
  have hc₁ : Function.Injective c₁ := Subtype.val_injective.sumMap Function.injective_id
  let c₂ : J → J ⊕ ↥B := fun x => if hx : x ∈ B then Sum.inr ⟨x, hx⟩ else Sum.inl x
  have hc₂ : Function.Injective c₂ := by
    intro x y hxy
    by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> simp [c₂, hx, hy] at hxy
    · exact hxy
    · exact hxy
  have hP := (polynomialAndBondWeightSmooth_holds h h' (↥B ⊕ ↥B)).1 _ hA
  have hΦ := mul_mem_smoothSet (precomp_mem_smoothSet hc₁ hP) (precomp_mem_smoothSet hc₂ hF)
  have hint : (fun u : J → specialUnitary => ∫ v, (fun x : J ⊕ ↥B → specialUnitary =>
      A ((x ∘ c₁) ∘ Sum.inl) ((x ∘ c₁) ∘ Sum.inr) * F (x ∘ c₂)) (Sum.elim u v)
        ∂haarPi ↥B) ∈ smoothSet :=
    mem_smoothSet.2 fun q => integral_sumElim_mem_smoothOrder q (mem_smoothSet.1 hΦ q)
  have heq : (fun u : J → specialUnitary => ∫ v', A (restrictTo B u) v' *
      F (glue B v' (restrictTo Bᶜ u)) ∂haarPi ↥B) =
      fun u : J → specialUnitary => ∫ v, (fun x : J ⊕ ↥B → specialUnitary =>
        A ((x ∘ c₁) ∘ Sum.inl) ((x ∘ c₁) ∘ Sum.inr) * F (x ∘ c₂)) (Sum.elim u v)
          ∂haarPi ↥B := by
    funext u
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    have hj : (Sum.elim u v ∘ c₂ : J → specialUnitary) = glue B v (restrictTo Bᶜ u) := by
      funext x
      by_cases hx : x ∈ B
      · simp only [Function.comp, c₂, dif_pos hx, Sum.elim_inr]
        exact (glue_of_mem B v _ ⟨x, hx⟩).symm
      · simp only [Function.comp, c₂, dif_neg hx, Sum.elim_inl]
        exact (glue_of_notMem B v (restrictTo Bᶜ u) ⟨x, hx⟩).symm
    simp only [hj]
    rfl
  rw [heq]
  exact hint
end Integrals
theorem allRules_holds (h₁ : UnitaryLogConjugationProperties)
    (h₂ : TransferOperators.GibbsHaarKernels.Statement)
    (h₃ : InfiniteLattice.TraceAndSingleBondWeight) : AllRules :=
  ⟨oneParameterSubgroups_holds h₁, singleWeightSmooth_holds h₁ h₃, fun J _ _ =>
    ⟨hasDerivAlongField_holds J, fun q => isStarClosedSubalgebraSet_smoothOfENatOrder q,
      leibnizRules_holds J, chainRule_holds J, expAndInvSmooth_holds J,
      polynomialAndBondWeightSmooth_holds h₁ h₃ J, fieldsSkewAdjoint_holds (h₂.2.1 J),
      seriesSmooth_holds J, partialVariablesSmooth_holds h₁ h₃ J⟩⟩
end YangMills.Construction.SpinHarmonics.FieldCalculus
