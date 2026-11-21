import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrability
import YangMills.Construction.Continuum.MotionsTensorProductsTranslationsAndTheReflection
import Reconstruction.MinkowskiSpace.FieldOnTheTensorVectorsProof
import Reconstruction.MinkowskiSpace.TimeDerivativesOfATensorInTheL1Norm
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.TensorTimeDerivatives
abbrev dt : ((Fin 4 → ℝ) → ℂ) → (Fin 4 → ℝ) → ℂ := TestFunctions.partialDerivR4 0
theorem coordDeriv_asOnePointFn (f : (Fin 4 → ℝ) → ℂ) :
    TestSpaces.coordDeriv (0 : Fin 1) 0 (WightmanTheory.asOnePointFn f) =
      WightmanTheory.asOnePointFn (dt f) := by
  funext x
  simp only [TestSpaces.coordDeriv, WightmanTheory.asOnePointFn, lineDeriv, dt,
    TestFunctions.partialDerivR4]
  congr 1
theorem dt_mem_schwartzR4 (hMot : MotionsTranslations.Statement)
    {f : (Fin 4 → ℝ) → ℂ} (hf : f ∈ WightmanTheory.schwartzR4) :
    dt f ∈ WightmanTheory.schwartzR4 := by
  have hs := (hMot.2.2.2.2 1 one_pos _ hf (Pi.single 0 (Pi.single 0 1))).1
  have e : TestSpaces.multiDeriv (Pi.single 0 (Pi.single 0 1) : TestSpaces.MultiIdx4 1)
      (WightmanTheory.asOnePointFn f) =
        TestSpaces.coordDeriv (0 : Fin 1) 0 (WightmanTheory.asOnePointFn f) := by
    simp [TestSpaces.multiDeriv, List.finRange_succ]
  rw [e, coordDeriv_asOnePointFn] at hs
  exact hs
theorem iterate_dt_mem_schwartzR4 (hMot : MotionsTranslations.Statement)
    {f : (Fin 4 → ℝ) → ℂ} (hf : f ∈ WightmanTheory.schwartzR4) (a : ℕ) :
    dt^[a] f ∈ WightmanTheory.schwartzR4 := by
  induction a with
  | zero => exact hf
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    exact dt_mem_schwartzR4 hMot ih
theorem integrable_of_mem_schwartzR4 (hTool : WightmanReconstruction.SmoothToolkit.Toolkit)
    {f : (Fin 4 → ℝ) → ℂ} (hf : f ∈ WightmanTheory.schwartzR4) : Integrable f := by
  have hi : Integrable (WightmanTheory.asOnePointFn f) := (hTool.2.2.2.2.2.2.2 1 le_rfl _ hf).1
  exact ((volume_preserving_funUnique (Fin 1) (Fin 4 → ℝ)).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).1 hi
theorem differentiable_of_mem_schwartzR4 {f : (Fin 4 → ℝ) → ℂ}
    (hf : f ∈ WightmanTheory.schwartzR4) : Differentiable ℝ f := by
  have hs : WightmanTheory.asOnePointFn f ∈ TestSpaces.schwartzSet 1 := hf
  have hc : ContDiff ℝ ∞ f :=
    hs.1.comp (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun (y : Fin 4 → ℝ) (_ : Fin 1) => y)
  exact hc.differentiable (by simp)
variable {m : ℕ}
theorem differentiable_tensorProd {g : Fin m → (Fin 4 → ℝ) → ℂ}
    (hg : ∀ l, Differentiable ℝ (g l)) :
    Differentiable ℝ (TestSpaces.tensorProd g : TestSpaces.PointTuple m → ℂ) := by
  intro x
  show DifferentiableAt ℝ (fun y : TestSpaces.PointTuple m => ∏ l, g l (y l)) x
  have hl : ∀ l ∈ (Finset.univ : Finset (Fin m)),
      DifferentiableAt ℝ (fun y : TestSpaces.PointTuple m => g l (y l)) x := fun l _ =>
    (hg l).differentiableAt.comp x (differentiableAt_apply l x)
  exact (HasFDerivAt.finsetProd (u := Finset.univ)
    (g := fun (l : Fin m) (y : TestSpaces.PointTuple m) => g l (y l))
    fun l hmem => (hl l hmem).hasFDerivAt).differentiableAt
theorem coordDeriv_tensorProd (g : Fin m → (Fin 4 → ℝ) → ℂ) (i : Fin m)
    (x : TestSpaces.PointTuple m) :
    TestSpaces.coordDeriv i 0 (TestSpaces.tensorProd g) x =
      TestSpaces.tensorProd (Function.update g i (dt (g i))) x := by
  have e : ∀ s : ℝ, TestSpaces.tensorProd g
      (x + s • (Pi.single i (Pi.single 0 1) : TestSpaces.PointTuple m)) =
      (∏ l ∈ Finset.univ.erase i, g l (x l)) * g i (x i + s • Pi.single 0 (1 : ℝ)) := by
    intro s
    simp only [TestSpaces.tensorProd]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    congr 1
    · refine Finset.prod_congr rfl fun l hl => ?_
      have hne : l ≠ i := Finset.ne_of_mem_erase hl
      simp [hne]
    · simp
  have e₂ : TestSpaces.tensorProd (Function.update g i (dt (g i))) x =
      (∏ l ∈ Finset.univ.erase i, g l (x l)) * dt (g i) (x i) := by
    simp only [TestSpaces.tensorProd]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    congr 1
    · refine Finset.prod_congr rfl fun l hl => ?_
      have hne : l ≠ i := Finset.ne_of_mem_erase hl
      simp [hne]
    · simp
  rw [e₂]
  simp only [TestSpaces.coordDeriv, lineDeriv, e]
  rw [deriv_const_mul_field]
  rfl
theorem coordDeriv_linearComb {ι : Type} [Fintype ι] (c : ι → ℂ)
    (F : ι → TestSpaces.PointTuple m → ℂ)
    (hF : ∀ t, Differentiable ℝ (F t)) (i : Fin m) (x : TestSpaces.PointTuple m) :
    TestSpaces.coordDeriv i 0 (fun y => ∑ t, c t * F t y) x =
      ∑ t, c t * TestSpaces.coordDeriv i 0 (F t) x := by
  have hd : ∀ t, HasLineDerivAt ℝ (F t)
      (lineDeriv ℝ (F t) x (Pi.single i (Pi.single 0 1))) x (Pi.single i (Pi.single 0 1)) :=
    fun t => (hF t x).lineDifferentiableAt.hasLineDerivAt
  have hD : HasDerivAt
      (fun s : ℝ => ∑ t, c t * F t (x + s • (Pi.single i (Pi.single 0 1) : TestSpaces.PointTuple m)))
      (∑ t, c t * lineDeriv ℝ (F t) x (Pi.single i (Pi.single 0 1))) 0 :=
    HasDerivAt.fun_sum fun t _ => (hd t).const_mul (c t)
  exact hD.deriv
def triangularSum (m : ℕ) : ℝ := ∑ i : Fin m, (((i : ℕ) + 1 : ℕ) : ℝ)
theorem triangularSum_nonneg : 0 ≤ triangularSum m :=
  Finset.sum_nonneg fun _ _ => by positivity
theorem triangularSum_le_sq : triangularSum m ≤ (m : ℝ) ^ 2 := by
  have hb : ∀ i ∈ (Finset.univ : Finset (Fin m)), (((i : ℕ) + 1 : ℕ) : ℝ) ≤ m := fun i _ => by
    exact_mod_cast i.isLt
  have := Finset.sum_le_card_nsmul _ _ _ hb
  simpa [triangularSum, pow_two] using this
def tensorOfIterates (g : Fin m → (Fin 4 → ℝ) → ℂ) (a : Fin m → ℕ) :
    TestSpaces.PointTuple m → ℂ :=
  TestSpaces.tensorProd fun l => dt^[a l] (g l)
theorem coordDeriv_tensorOfIterates (g : Fin m → (Fin 4 → ℝ) → ℂ) (a : Fin m → ℕ) (i : Fin m)
    (x : TestSpaces.PointTuple m) :
    TestSpaces.coordDeriv i 0 (tensorOfIterates g a) x =
      tensorOfIterates g (Function.update a i (a i + 1)) x := by
  rw [tensorOfIterates, coordDeriv_tensorProd, tensorOfIterates]
  congr 1
  funext l
  by_cases hl : l = i
  · subst hl
    simp [Function.iterate_succ_apply']
  · simp [hl]
theorem iterate_timeWeightedDeriv_expansion (g : Fin m → (Fin 4 → ℝ) → ℂ)
    (hg : ∀ (a : ℕ) (l : Fin m), Differentiable ℝ (dt^[a] (g l))) (j : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ) (a : ι → Fin m → ℕ),
      (∀ t, 0 ≤ c t) ∧ ∑ t, c t ≤ triangularSum m ^ j ∧ (∀ t l, a t l ≤ j) ∧
      RealPointVectors.timeWeightedDeriv^[j] (TestSpaces.tensorProd g) =
        fun x => ∑ t, (c t : ℂ) * tensorOfIterates g (a t) x := by
  induction j with
  | zero =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => 0, by simp, by simp, by simp, ?_⟩
    funext x
    simp [tensorOfIterates]
  | succ j ih =>
    obtain ⟨ι, _, c, a, hc, hs, ha, he⟩ := ih
    refine ⟨ι × Fin m, inferInstance, fun p => c p.1 * (((p.2 : ℕ) + 1 : ℕ) : ℝ),
      fun p => Function.update (a p.1) p.2 (a p.1 p.2 + 1), ?_, ?_, ?_, ?_⟩
    · exact fun p => mul_nonneg (hc _) (by positivity)
    · have e : ∑ p : ι × Fin m, c p.1 * (((p.2 : ℕ) + 1 : ℕ) : ℝ) =
          (∑ t, c t) * triangularSum m := by
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [triangularSum, Finset.mul_sum]
      rw [e, pow_succ]
      exact mul_le_mul_of_nonneg_right hs triangularSum_nonneg
    · intro p l
      by_cases hl : l = p.2
      · subst hl
        simpa using ha p.1 _
      · simpa [hl] using (ha p.1 l).trans (Nat.le_succ j)
    · rw [Function.iterate_succ_apply', he]
      funext x
      have hF : ∀ t, Differentiable ℝ (tensorOfIterates g (a t)) := fun t =>
        differentiable_tensorProd fun l => hg _ l
      simp only [RealPointVectors.timeWeightedDeriv]
      rw [Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coordDeriv_linearComb _ _ hF i x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [coordDeriv_tensorOfIterates]
      push_cast
      ring
theorem lOneNorm_nonneg {E F : Type*} [MeasureSpace E] [NormedAddCommGroup F] (φ : E → F) :
    0 ≤ WightmanReconstruction.lOneNorm φ :=
  integral_nonneg fun _ => norm_nonneg _
theorem lOneNorm_tensorProd (g : Fin m → (Fin 4 → ℝ) → ℂ) :
    WightmanReconstruction.lOneNorm (TestSpaces.tensorProd g : TestSpaces.PointTuple m → ℂ) =
      ∏ l, WightmanReconstruction.lOneNorm (g l) := by
  simp only [WightmanReconstruction.lOneNorm, TestSpaces.tensorProd, norm_prod]
  exact integral_fintype_prod_volume_eq_prod fun l y => ‖g l y‖
theorem lOneNorm_nonneg_comb_le {ι : Type} [Fintype ι] (c : ι → ℝ) (hc : ∀ t, 0 ≤ c t)
    (F : ι → TestSpaces.PointTuple m → ℂ) (hF : ∀ t, Integrable (F t)) :
    WightmanReconstruction.lOneNorm (fun x => ∑ t, (c t : ℂ) * F t x) ≤
      ∑ t, c t * WightmanReconstruction.lOneNorm (F t) := by
  have hi : ∀ t, Integrable fun x => c t * ‖F t x‖ := fun t => (hF t).norm.const_mul _
  have hs : Integrable fun x => ∑ t, (c t : ℂ) * F t x :=
    integrable_finsetSum _ fun t _ => (hF t).const_mul _
  have hle : ∀ x, ‖∑ t, (c t : ℂ) * F t x‖ ≤ ∑ t, c t * ‖F t x‖ := fun x => by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc t)]
  calc WightmanReconstruction.lOneNorm (fun x => ∑ t, (c t : ℂ) * F t x)
      ≤ ∫ x, ∑ t, c t * ‖F t x‖ :=
        integral_mono hs.norm (integrable_finsetSum _ fun t _ => hi t) hle
    _ = ∑ t, c t * WightmanReconstruction.lOneNorm (F t) := by
        rw [integral_finsetSum _ fun t _ => hi t]
        exact Finset.sum_congr rfl fun t _ => integral_const_mul _ _
theorem lOneNorm_iterate_le_maxPartialL1 {k a : ℕ} (ha : a ≤ k) (f : (Fin 4 → ℝ) → ℂ) :
    WightmanReconstruction.lOneNorm (dt^[a] f) ≤ RealPointVectors.maxPartialL1 k f :=
  Finset.le_sup' (fun j => WightmanReconstruction.lOneNorm ((TestFunctions.partialDerivR4 0)^[j] f))
    (Finset.mem_range.2 (Nat.lt_succ_of_le ha))
theorem maxPartialL1_nonneg (k : ℕ) (f : (Fin 4 → ℝ) → ℂ) :
    0 ≤ RealPointVectors.maxPartialL1 k f := by apply _root_.YangMills.Construction.FieldOnTensorVecs.maxPartialL1_nonneg <;> assumption
theorem tensorTimeDerivBound_holds (hMot : MotionsTranslations.Statement)
    (hTool : WightmanReconstruction.SmoothToolkit.Toolkit) :
    RealPointVectors.TensorTimeDerivBound := by
  intro k n g hg
  have hmem : ∀ (a : ℕ) (l : Fin (n + 1)), dt^[a] (g l) ∈ WightmanTheory.schwartzR4 :=
    fun a l => iterate_dt_mem_schwartzR4 hMot (hg l) a
  have hP : 0 ≤ ∏ l, RealPointVectors.maxPartialL1 k (g l) :=
    Finset.prod_nonneg fun l _ => maxPartialL1_nonneg k (g l)
  have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  refine Finset.sup'_le _ _ fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  obtain ⟨ι, _, c, a, hc, hs, ha, he⟩ :=
    iterate_timeWeightedDeriv_expansion g (fun a l => differentiable_of_mem_schwartzR4 (hmem a l)) j
  have hint : ∀ t, Integrable (tensorOfIterates g (a t)) := fun t =>
    Integrable.fintype_prod fun l => integrable_of_mem_schwartzR4 hTool (hmem _ l)
  have hterm : ∀ t, WightmanReconstruction.lOneNorm (tensorOfIterates g (a t)) ≤
      ∏ l, RealPointVectors.maxPartialL1 k (g l) := fun t => by
    rw [tensorOfIterates, lOneNorm_tensorProd]
    exact Finset.prod_le_prod (fun l _ => lOneNorm_nonneg _)
      fun l _ => lOneNorm_iterate_le_maxPartialL1 ((ha t l).trans hjk) (g l)
  have hpow : triangularSum (n + 1) ^ j ≤ ((n + 1 : ℕ) : ℝ) ^ (2 * k) :=
    calc triangularSum (n + 1) ^ j ≤ (((n + 1 : ℕ) : ℝ) ^ 2) ^ j :=
          pow_le_pow_left₀ triangularSum_nonneg triangularSum_le_sq j
      _ = ((n + 1 : ℕ) : ℝ) ^ (2 * j) := (pow_mul _ _ _).symm
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ (2 * k) := pow_le_pow_right₀ hone (by omega)
  rw [he]
  calc WightmanReconstruction.lOneNorm (fun x => ∑ t, (c t : ℂ) * tensorOfIterates g (a t) x)
      ≤ ∑ t, c t * WightmanReconstruction.lOneNorm (tensorOfIterates g (a t)) :=
        lOneNorm_nonneg_comb_le c hc _ hint
    _ ≤ ∑ t, c t * ∏ l, RealPointVectors.maxPartialL1 k (g l) :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hterm t) (hc t)
    _ = (∑ t, c t) * ∏ l, RealPointVectors.maxPartialL1 k (g l) := (Finset.sum_mul _ _ _).symm
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ (2 * k) * ∏ l, RealPointVectors.maxPartialL1 k (g l) :=
        mul_le_mul_of_nonneg_right (hs.trans hpow) hP
end YangMills.Construction.TensorTimeDerivatives
