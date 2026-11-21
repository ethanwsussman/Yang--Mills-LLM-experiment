import YangMills.Construction.HilbertSpaces.JointSpectralMeasureOfAContractionAndAUnitaryProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology ComplexConjugate
open scoped InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction.SpectralMeasures
open OneLoopNotation ComplexHilbert LatticeConventions
namespace BddCalculus
variable {X H : Type} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem diagMeasure_real_eq_norm_sq (E : PVM X H) (ψ : H)
    (Y : MeasSet X) : (E.diagMeasure ψ).real Y.1 = ‖E Y ψ‖ ^ 2 := by
  have h := E.diagMeasure_real ψ Y
  rw [E.diagForm_eq_norm_sq] at h
  exact_mod_cast h
theorem inner_apply_eq_diagMeasure_real (E : PVM X H) (ψ : H)
    (Y : MeasSet X) : ⟪ψ, E Y ψ⟫_ℂ = (((E.diagMeasure ψ).real Y.1 : ℝ) : ℂ) :=
  (E.diagMeasure_real ψ Y).symm
theorem diagMeasure_real_univ (E : PVM X H) (ψ : H) :
    (E.diagMeasure ψ).real Set.univ = ‖ψ‖ ^ 2 := by
  have h := diagMeasure_real_eq_norm_sq E ψ ⟨Set.univ, MeasurableSet.univ⟩
  rw [E.isPVM.map_univ] at h
  exact h
theorem apply_empty_eq_zero (E : PVM X H) : E ⟨∅, MeasurableSet.empty⟩ = 0 := by
  ext ψ
  have h := diagMeasure_real_eq_norm_sq E ψ ⟨∅, MeasurableSet.empty⟩
  have h₀ : (E.diagMeasure ψ).real (∅ : Set X) = 0 := by simp
  have h₁ : ‖E ⟨∅, MeasurableSet.empty⟩ ψ‖ ^ 2 = 0 := by
    rw [← h]
    exact h₀
  simpa using h₁
theorem apply_mul_self (E : PVM X H) (Y : MeasSet X) :
    E Y * E Y = E Y := by
  have h := (E.isPVM.isOrthProj Y).idempotent
  rwa [pow_two] at h
theorem apply_mul_apply_of_disjoint (E : PVM X H) {Y Y' : MeasSet X}
    (h : Disjoint Y.1 Y'.1) : E Y * E Y' = 0 := by
  rw [← E.isPVM.map_inter Y Y']
  have h₁ : (⟨Y.1 ∩ Y'.1, Y.2.inter Y'.2⟩ : MeasSet X) = ⟨∅, MeasurableSet.empty⟩ :=
    Subtype.ext (Set.disjoint_iff_inter_eq_empty.mp h)
  rw [h₁, apply_empty_eq_zero]
theorem ext_of_inner_self {B B' : BddOp H} (h : ∀ ψ, ⟪ψ, B ψ⟫_ℂ = ⟪ψ, B' ψ⟫_ℂ) : B = B' := by apply _root_.YangMills.Construction.ContractionUnitary.JointSpectral.eq_of_inner_self <;> assumption
theorem bddIntegral_eq_of_isBddIntegral (E : PVM X H) {f : X → ℂ} {B : BddOp H}
    (h : E.IsBddIntegral f B) : E.bddIntegral f = B :=
  ext_of_inner_self fun ψ => (E.isBddIntegral_bddIntegral ⟨B, h⟩ ψ).trans (h ψ).symm
theorem integrable_of_isBddMeasurable (E : PVM X H) {f : X → ℂ}
    (hf : IsBddMeasurable f) (ψ : H) : Integrable f (E.diagMeasure ψ) := by
  obtain ⟨hm, C, hC⟩ := hf
  exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
theorem integrable_norm_sq_of_isBddMeasurable (E : PVM X H) {f : X → ℂ}
    (hf : IsBddMeasurable f) (ψ : H) :
    Integrable (fun x => ‖f x‖ ^ 2) (E.diagMeasure ψ) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable (C ^ 2) (ae_of_all _ ?_)
  intro x
  have h₁ : ‖‖f x‖ ^ 2‖ = ‖f x‖ ^ 2 := by simp
  rw [h₁]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
theorem isBddMeasurable_sub {f g : X → ℂ} (hf : IsBddMeasurable f)
    (hg : IsBddMeasurable g) : IsBddMeasurable (f - g) := by
  obtain ⟨hm, C, hC⟩ := hf
  obtain ⟨hm', C', hC'⟩ := hg
  exact ⟨hm.sub hm', C + C', fun x => (norm_sub_le _ _).trans (add_le_add (hC x) (hC' x))⟩
theorem isBddMeasurable_mul {f g : X → ℂ} (hf : IsBddMeasurable f)
    (hg : IsBddMeasurable g) : IsBddMeasurable (f * g) := by apply _root_.YangMills.Construction.ContractionUnitary.JointSpectral.isBddMeasurable_mul <;> assumption
theorem isBddMeasurable_conj {f : X → ℂ} (hf : IsBddMeasurable f) :
    IsBddMeasurable (fun x => conj (f x)) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨Complex.continuous_conj.measurable.comp hm, C, fun x => ?_⟩
  rw [RCLike.norm_conj]
  exact hC x
theorem isBddMeasurable_simpleFunc (s : SimpleFunc X ℂ) : IsBddMeasurable s := by
  refine ⟨s.measurable, ∑ z ∈ s.range, ‖z‖, fun x => ?_⟩
  exact Finset.single_le_sum (f := fun z : ℂ => ‖z‖) (fun _ _ => norm_nonneg _) (s.mem_range_self x)
theorem isBddMeasurable_indicatorOne (Y : MeasSet X) :
    IsBddMeasurable (indicatorOne Y.1 : X → ℂ) := by apply _root_.YangMills.Construction.ContractionUnitary.JointSpectral.isBddMeasurable_indicatorOne <;> assumption
theorem isBddIntegral_add (E : PVM X H) {f g : X → ℂ} {B B' : BddOp H}
    (hf : IsBddMeasurable f) (hg : IsBddMeasurable g)
    (h : E.IsBddIntegral f B) (h' : E.IsBddIntegral g B') : E.IsBddIntegral (f + g) (B + B') := by
  intro ψ
  rw [add_apply, inner_add_right, h ψ, h' ψ]
  exact (integral_add (integrable_of_isBddMeasurable E hf ψ) (integrable_of_isBddMeasurable E hg ψ)).symm
theorem isBddIntegral_sub (E : PVM X H) {f g : X → ℂ} {B B' : BddOp H}
    (hf : IsBddMeasurable f) (hg : IsBddMeasurable g)
    (h : E.IsBddIntegral f B) (h' : E.IsBddIntegral g B') : E.IsBddIntegral (f - g) (B - B') := by
  intro ψ
  rw [sub_apply, inner_sub_right, h ψ, h' ψ]
  exact (integral_sub (integrable_of_isBddMeasurable E hf ψ) (integrable_of_isBddMeasurable E hg ψ)).symm
theorem isBddIntegral_smul (E : PVM X H) {f : X → ℂ} {B : BddOp H}
    (z : ℂ) (h : E.IsBddIntegral f B) : E.IsBddIntegral (z • f) (z • B) := by
  intro ψ
  rw [smul_apply, inner_smul_right, h ψ]
  exact (integral_smul z f).symm
theorem isBddIntegral_adjoint (E : PVM X H) {f : X → ℂ} {B : BddOp H}
    (h : E.IsBddIntegral f B) :
    E.IsBddIntegral (fun x => conj (f x)) (ContinuousLinearMap.adjoint B) := by
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, h ψ, integral_conj]
def fiberSet {α : Type} (u : SimpleFunc X α) (w : α) : MeasSet X :=
  ⟨u ⁻¹' {w}, u.measurableSet_fiber w⟩
def fiberSum (E : PVM X H) {α : Type} (u : SimpleFunc X α) (g : α → ℂ) :
    BddOp H :=
  ∑ w ∈ u.range, g w • E (fiberSet u w)
theorem isBddIntegral_fiberSum (E : PVM X H) {α : Type}
    (u : SimpleFunc X α) (g : α → ℂ) :
    E.IsBddIntegral (fun x => g (u x)) (fiberSum E u g) := by
  intro ψ
  have h₁ : (fun x => g (u x)) =
      fun x => ∑ w ∈ u.range, (fiberSet u w).1.indicator (fun _ => g w) x := by
    funext x
    rw [Finset.sum_eq_single (u x)]
    · have hx : x ∈ (fiberSet u (u x)).1 := rfl
      rw [Set.indicator_of_mem hx]
    · intro w _ hw
      refine Set.indicator_of_notMem ?_ _
      intro hx
      exact hw (Eq.symm hx)
    · intro hx
      exact absurd (u.mem_range_self x) hx
  rw [h₁, integral_finsetSum _ fun w _ => (integrable_const _).indicator (fiberSet u w).2]
  simp only [fiberSum, sum_apply, smul_apply,
    inner_sum, inner_smul_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [integral_indicator_const _ (fiberSet u w).2, inner_apply_eq_diagMeasure_real, Complex.real_smul,
    mul_comm]
theorem fiberSum_mul (E : PVM X H) {α : Type} (u : SimpleFunc X α)
    (g h : α → ℂ) :
    fiberSum E u g * fiberSum E u h = fiberSum E u (fun w => g w * h w) := by
  simp only [fiberSum]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.sum_eq_single w]
  · rw [smul_mul_smul_comm, apply_mul_self]
  · intro w' _ hne
    have hd : Disjoint (fiberSet u w).1 (fiberSet u w').1 :=
      Set.disjoint_left.mpr fun x hx hx' => hne ((Eq.symm hx').trans hx)
    rw [smul_mul_smul_comm, apply_mul_apply_of_disjoint E hd, smul_zero]
  · intro h'
    exact absurd hw h'
theorem isBddIntegral_simpleFunc (E : PVM X H) (s : SimpleFunc X ℂ) :
    E.IsBddIntegral s (E.bddIntegral s) :=
  E.isBddIntegral_bddIntegral ⟨_, isBddIntegral_fiberSum E s id⟩
theorem bddIntegral_simpleFunc_mul (E : PVM X H) (s t : SimpleFunc X ℂ) :
    E.bddIntegral (s * t : SimpleFunc X ℂ) = E.bddIntegral s * E.bddIntegral t := by
  have h₁ : E.bddIntegral s = fiberSum E (s.pair t) Prod.fst :=
    bddIntegral_eq_of_isBddIntegral E (isBddIntegral_fiberSum E (s.pair t) Prod.fst)
  have h₂ : E.bddIntegral t = fiberSum E (s.pair t) Prod.snd :=
    bddIntegral_eq_of_isBddIntegral E (isBddIntegral_fiberSum E (s.pair t) Prod.snd)
  have h₃ : E.bddIntegral (s * t : SimpleFunc X ℂ) =
      fiberSum E (s.pair t) (fun w => w.1 * w.2) :=
    bddIntegral_eq_of_isBddIntegral E (isBddIntegral_fiberSum E (s.pair t) (fun w => w.1 * w.2))
  rw [h₁, h₂, h₃, fiberSum_mul]
theorem norm_bddIntegral_apply_sq_of_mul (E : PVM X H) {f : X → ℂ}
    (hex : ∃ B, E.IsBddIntegral f B)
    (hexm : ∃ B, E.IsBddIntegral ((fun x => conj (f x)) * f) B)
    (hmul : E.bddIntegral ((fun x => conj (f x)) * f) =
      E.bddIntegral (fun x => conj (f x)) * E.bddIntegral f) (ψ : H) :
    ‖E.bddIntegral f ψ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(E.diagMeasure ψ) := by
  have hA : E.bddIntegral (fun x => conj (f x)) = ContinuousLinearMap.adjoint (E.bddIntegral f) :=
    bddIntegral_eq_of_isBddIntegral E (isBddIntegral_adjoint E (E.isBddIntegral_bddIntegral hex))
  have h₁ := E.isBddIntegral_bddIntegral hexm ψ
  rw [hmul, hA] at h₁
  have h₂ : ⟪ψ, (ContinuousLinearMap.adjoint (E.bddIntegral f) * E.bddIntegral f) ψ⟫_ℂ =
      ⟪E.bddIntegral f ψ, E.bddIntegral f ψ⟫_ℂ :=
    ContinuousLinearMap.adjoint_inner_right (E.bddIntegral f) ψ (E.bddIntegral f ψ)
  have h₃ : ((fun x => conj (f x)) * f) = fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [Pi.mul_apply, Complex.conj_mul']
    push_cast
    rfl
  have h₄ : ∫ x, (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) x ∂(E.diagMeasure ψ) =
      ((∫ x, ‖f x‖ ^ 2 ∂(E.diagMeasure ψ) : ℝ) : ℂ) := integral_ofReal
  rw [h₂, h₃, h₄] at h₁
  have h₅ := congrArg Complex.re h₁
  rw [Complex.ofReal_re] at h₅
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (E.bddIntegral f ψ)).symm.trans h₅
theorem integral_norm_sq_le_mul (E : PVM X H) {f : X → ℂ}
    (hf : IsBddMeasurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ^ 2 ≤ C) (ψ : H) :
    ∫ x, ‖f x‖ ^ 2 ∂(E.diagMeasure ψ) ≤ C * ‖ψ‖ ^ 2 := by
  calc ∫ x, ‖f x‖ ^ 2 ∂(E.diagMeasure ψ) ≤ ∫ _, C ∂(E.diagMeasure ψ) :=
        integral_mono (integrable_norm_sq_of_isBddMeasurable E hf ψ) (integrable_const _) hC
    _ = C * ‖ψ‖ ^ 2 := by
        rw [integral_const, smul_eq_mul, diagMeasure_real_univ, mul_comm]
theorem norm_bddIntegral_simpleFunc_le (E : PVM X H) (t : SimpleFunc X ℂ) {C : ℝ}
    (hC₀ : 0 ≤ C) (hC : ∀ x, ‖t x‖ ≤ C) : ‖E.bddIntegral t‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC₀ fun ψ => ?_
  have h₁ : ‖E.bddIntegral t ψ‖ ^ 2 = ∫ x, ‖t x‖ ^ 2 ∂(E.diagMeasure ψ) :=
    norm_bddIntegral_apply_sq_of_mul E ⟨_, isBddIntegral_simpleFunc E t⟩
      ⟨_, isBddIntegral_simpleFunc E (t.map (starRingEnd ℂ) * t)⟩
      (bddIntegral_simpleFunc_mul E (t.map (starRingEnd ℂ)) t) ψ
  have h₂ := integral_norm_sq_le_mul E (isBddMeasurable_simpleFunc t) (C := C ^ 2)
    (fun x => pow_le_pow_left₀ (norm_nonneg _) (hC x) 2) ψ
  rw [← h₁, ← mul_pow] at h₂
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hC₀ (norm_nonneg _)) two_ne_zero).mp h₂
def latticePoint (N : ℕ) (p : ℤ × ℤ) : ℂ :=
  ⟨(p.1 : ℝ) / ((N : ℝ) + 1), (p.2 : ℝ) / ((N : ℝ) + 1)⟩
def latticeIndex (N : ℕ) (z : ℂ) : ℤ × ℤ :=
  (⌊((N : ℝ) + 1) * z.re⌋, ⌊((N : ℝ) + 1) * z.im⌋)
theorem abs_floor_mul_div_sub_le (N : ℕ) (a : ℝ) :
    |(⌊((N : ℝ) + 1) * a⌋ : ℝ) / ((N : ℝ) + 1) - a| ≤ 1 / ((N : ℝ) + 1) := by
  have hM : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h₁ := Int.floor_le (((N : ℝ) + 1) * a)
  have h₂ := Int.lt_floor_add_one (((N : ℝ) + 1) * a)
  have h₃ : (⌊((N : ℝ) + 1) * a⌋ : ℝ) / ((N : ℝ) + 1) - a =
      ((⌊((N : ℝ) + 1) * a⌋ : ℝ) - ((N : ℝ) + 1) * a) / ((N : ℝ) + 1) := by
    field_simp
  rw [h₃, abs_div, abs_of_pos hM]
  refine div_le_div_of_nonneg_right ?_ hM.le
  rw [abs_le]
  constructor <;> linarith
theorem norm_latticePoint_sub_le (N : ℕ) (z : ℂ) :
    ‖latticePoint N (latticeIndex N z) - z‖ ≤ 2 * (1 / ((N : ℝ) + 1)) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h₁ := abs_floor_mul_div_sub_le N z.re
  have h₂ := abs_floor_mul_div_sub_le N z.im
  have h₃ : (latticePoint N (latticeIndex N z) - z).re =
      (⌊((N : ℝ) + 1) * z.re⌋ : ℝ) / ((N : ℝ) + 1) - z.re := rfl
  have h₄ : (latticePoint N (latticeIndex N z) - z).im =
      (⌊((N : ℝ) + 1) * z.im⌋ : ℝ) / ((N : ℝ) + 1) - z.im := rfl
  rw [h₃, h₄]
  linarith
def latticeIndexSimpleFunc {f : X → ℂ} (hf : IsBddMeasurable f) (N : ℕ) :
    SimpleFunc X (ℤ × ℤ) where
  toFun := fun x => latticeIndex N (f x)
  measurableSet_fiber' := fun p => by
    have hk : Measurable fun x => latticeIndex N (f x) :=
      (((Complex.measurable_re.comp hf.1).const_mul _).floor).prodMk
        (((Complex.measurable_im.comp hf.1).const_mul _).floor)
    exact hk (measurableSet_singleton p)
  finite_range' := by
    obtain ⟨_, C, hC⟩ := hf
    have hM : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
    refine ((Set.finite_Icc ⌊-(((N : ℝ) + 1) * C)⌋ ⌊((N : ℝ) + 1) * C⌋).prod
      (Set.finite_Icc ⌊-(((N : ℝ) + 1) * C)⌋ ⌊((N : ℝ) + 1) * C⌋)).subset ?_
    rintro _ ⟨x, rfl⟩
    have hre := abs_le.mp ((Complex.abs_re_le_norm (f x)).trans (hC x))
    have him := abs_le.mp ((Complex.abs_im_le_norm (f x)).trans (hC x))
    refine ⟨⟨Int.floor_le_floor ?_, Int.floor_le_floor ?_⟩, ⟨Int.floor_le_floor ?_, Int.floor_le_floor ?_⟩⟩
    · nlinarith [hre.1]
    · exact mul_le_mul_of_nonneg_left hre.2 hM
    · nlinarith [him.1]
    · exact mul_le_mul_of_nonneg_left him.2 hM
def simpleApprox {f : X → ℂ} (hf : IsBddMeasurable f) (N : ℕ) : SimpleFunc X ℂ :=
  (latticeIndexSimpleFunc hf N).map (latticePoint N)
theorem norm_simpleApprox_sub_le {f : X → ℂ} (hf : IsBddMeasurable f) (N : ℕ) (x : X) :
    ‖simpleApprox hf N x - f x‖ ≤ 2 * (1 / ((N : ℝ) + 1)) :=
  norm_latticePoint_sub_le N (f x)
theorem tendsto_two_div_succ : Tendsto (fun N : ℕ => 2 * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
theorem tendsto_simpleApprox {f : X → ℂ} (hf : IsBddMeasurable f) (x : X) :
    Tendsto (fun N => simpleApprox hf N x) atTop (𝓝 (f x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun N => norm_simpleApprox_sub_le hf N x) tendsto_two_div_succ
theorem exists_norm_simpleApprox_le {f : X → ℂ} (hf : IsBddMeasurable f) :
    ∃ C : ℝ, ∀ N x, ‖simpleApprox hf N x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.2
  refine ⟨2 + C, fun N x => ?_⟩
  have h₁ := norm_simpleApprox_sub_le hf N x
  have h₂ : 1 / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have h₃ : ‖simpleApprox hf N x‖ ≤ ‖simpleApprox hf N x - f x‖ + ‖f x‖ :=
    norm_le_norm_sub_add _ _
  have h₄ := hC x
  linarith
theorem tendsto_integral_of_uniform_bound {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (E : PVM X H) {F : ℕ → X → G} {f : X → G} {C : ℝ} (ψ : H)
    (hF : ∀ n, AEStronglyMeasurable (F n) (E.diagMeasure ψ)) (hC : ∀ n x, ‖F n x‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, F n x ∂(E.diagMeasure ψ)) atTop
      (𝓝 (∫ x, f x ∂(E.diagMeasure ψ))) :=
  tendsto_integral_of_dominated_convergence (fun _ => C) hF (integrable_const _)
    (fun n => ae_of_all _ (hC n)) (ae_of_all _ hlim)
theorem exists_isBddIntegral_tendsto (E : PVM X H) {f : X → ℂ}
    (hf : IsBddMeasurable f) :
    ∃ B, E.IsBddIntegral f B ∧
      Tendsto (fun N => E.bddIntegral (simpleApprox hf N)) atTop (𝓝 B) := by
  have hd : ∀ n m : ℕ, ‖E.bddIntegral (simpleApprox hf n) - E.bddIntegral (simpleApprox hf m)‖ ≤
      2 * (1 / ((n : ℝ) + 1)) + 2 * (1 / ((m : ℝ) + 1)) := by
    intro n m
    have h₁ : E.bddIntegral (simpleApprox hf n) - E.bddIntegral (simpleApprox hf m) =
        E.bddIntegral (simpleApprox hf n - simpleApprox hf m : SimpleFunc X ℂ) :=
      (bddIntegral_eq_of_isBddIntegral E (isBddIntegral_sub E (isBddMeasurable_simpleFunc _) (isBddMeasurable_simpleFunc _)
        (isBddIntegral_simpleFunc E _) (isBddIntegral_simpleFunc E _))).symm
    rw [h₁]
    refine norm_bddIntegral_simpleFunc_le E _ (by positivity) fun x => ?_
    have h₂ : (simpleApprox hf n - simpleApprox hf m : SimpleFunc X ℂ) x =
        (simpleApprox hf n x - f x) - (simpleApprox hf m x - f x) := by
      rw [SimpleFunc.sub_apply]
      ring
    rw [h₂]
    exact (norm_sub_le _ _).trans (add_le_add (norm_simpleApprox_sub_le hf n x)
      (norm_simpleApprox_sub_le hf m x))
  have hc : CauchySeq fun N => E.bddIntegral (simpleApprox hf N) := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 * (2 * (1 / ((N : ℝ) + 1)))) ?_ ?_
    · intro n m K hn hm
      rw [dist_eq_norm]
      refine (hd n m).trans ?_
      have hmono : ∀ k : ℕ, K ≤ k → 2 * (1 / ((k : ℝ) + 1)) ≤ 2 * (1 / ((K : ℝ) + 1)) := by
        intro k hk
        have hk' : (K : ℝ) ≤ k := Nat.cast_le.mpr hk
        have : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith
      linarith [hmono n hn, hmono m hm]
    · simpa using tendsto_two_div_succ.const_mul 2
  obtain ⟨B, hB⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨B, fun ψ => ?_, hB⟩
  have hcont : Continuous fun T : BddOp H => ⟪ψ, T ψ⟫_ℂ :=
    continuous_const.inner (continuous_id.clm_apply continuous_const)
  have h₁ := (hcont.tendsto B).comp hB
  obtain ⟨C, hC⟩ := exists_norm_simpleApprox_le hf
  have h₂ := tendsto_integral_of_uniform_bound E ψ
    (fun n => (simpleApprox hf n).measurable.aestronglyMeasurable) hC (tendsto_simpleApprox hf)
  refine tendsto_nhds_unique (h₁.congr fun N => ?_) h₂
  exact isBddIntegral_simpleFunc E _ ψ
theorem isBddIntegral_of_isBddMeasurable (E : PVM X H) {f : X → ℂ}
    (hf : IsBddMeasurable f) : E.IsBddIntegral f (E.bddIntegral f) := by
  obtain ⟨B, hB, _⟩ := exists_isBddIntegral_tendsto E hf
  exact E.isBddIntegral_bddIntegral ⟨B, hB⟩
theorem tendsto_bddIntegral_simpleApprox (E : PVM X H) {f : X → ℂ}
    (hf : IsBddMeasurable f) :
    Tendsto (fun N => E.bddIntegral (simpleApprox hf N)) atTop (𝓝 (E.bddIntegral f)) := by
  obtain ⟨B, hB, ht⟩ := exists_isBddIntegral_tendsto E hf
  rw [bddIntegral_eq_of_isBddIntegral E hB]
  exact ht
theorem bddIntegral_mul_of_isBddMeasurable (E : PVM X H) {f g : X → ℂ}
    (hf : IsBddMeasurable f) (hg : IsBddMeasurable g) :
    E.bddIntegral (f * g) = E.bddIntegral f * E.bddIntegral g := by
  refine ext_of_inner_self fun ψ => ?_
  have hcont : Continuous fun T : BddOp H => ⟪ψ, T ψ⟫_ℂ :=
    continuous_const.inner (continuous_id.clm_apply continuous_const)
  have h₁ := (hcont.tendsto _).comp
    ((tendsto_bddIntegral_simpleApprox E hf).mul (tendsto_bddIntegral_simpleApprox E hg))
  obtain ⟨C, hC⟩ := exists_norm_simpleApprox_le hf
  obtain ⟨C', hC'⟩ := exists_norm_simpleApprox_le hg
  have h₂ := tendsto_integral_of_uniform_bound E
    (F := fun N x => simpleApprox hf N x * simpleApprox hg N x)
    (f := f * g) (C := C * C') ψ
    (fun n => ((simpleApprox hf n).measurable.mul
      (simpleApprox hg n).measurable).aestronglyMeasurable)
    (fun n x => by
      rw [norm_mul]
      exact mul_le_mul (hC n x) (hC' n x) (norm_nonneg _) ((norm_nonneg _).trans (hC n x)))
    (fun x => (tendsto_simpleApprox hf x).mul (tendsto_simpleApprox hg x))
  rw [isBddIntegral_of_isBddMeasurable E (isBddMeasurable_mul hf hg) ψ]
  refine tendsto_nhds_unique h₂ (h₁.congr fun N => ?_)
  have h₃ := isBddIntegral_simpleFunc E (simpleApprox hf N * simpleApprox hg N) ψ
  rw [bddIntegral_simpleFunc_mul] at h₃
  exact h₃
theorem norm_bddIntegral_apply_sq (E : PVM X H) {f : X → ℂ}
    (hf : IsBddMeasurable f) (ψ : H) :
    ‖E.bddIntegral f ψ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(E.diagMeasure ψ) :=
  norm_bddIntegral_apply_sq_of_mul E ⟨_, isBddIntegral_of_isBddMeasurable E hf⟩
    ⟨_, isBddIntegral_of_isBddMeasurable E (isBddMeasurable_mul (isBddMeasurable_conj hf) hf)⟩
    (bddIntegral_mul_of_isBddMeasurable E (isBddMeasurable_conj hf) hf) ψ
theorem bddIntegral_conj_eq_adjoint (E : PVM X H) {f : X → ℂ}
    (hf : IsBddMeasurable f) :
    E.bddIntegral (fun x => conj (f x)) = ContinuousLinearMap.adjoint (E.bddIntegral f) :=
  bddIntegral_eq_of_isBddIntegral E (isBddIntegral_adjoint E (isBddIntegral_of_isBddMeasurable E hf))
theorem inner_bddIntegral_eq (E : PVM X H) {f : X → ℂ}
    (hf : IsBddMeasurable f) (φ ψ : H) :
    ⟪φ, E.bddIntegral f ψ⟫_ℂ = ⟪E.bddIntegral (fun x => conj (f x)) φ, ψ⟫_ℂ := by
  rw [bddIntegral_conj_eq_adjoint E hf, ContinuousLinearMap.adjoint_inner_left]
theorem bddIntegral_indicatorOne (E : PVM X H) (Y : MeasSet X) :
    E.bddIntegral (indicatorOne Y.1) = E Y := by
  refine bddIntegral_eq_of_isBddIntegral E fun ψ => ?_
  have h₁ : (indicatorOne Y.1 : X → ℂ) = Y.1.indicator (fun _ => (1 : ℂ)) := rfl
  rw [h₁, integral_indicator_const _ Y.2, inner_apply_eq_diagMeasure_real, Complex.real_smul, mul_one]
theorem bddIntegral_sub (E : PVM X H) {f g : X → ℂ}
    (hf : IsBddMeasurable f) (hg : IsBddMeasurable g) :
    E.bddIntegral (f - g) = E.bddIntegral f - E.bddIntegral g :=
  bddIntegral_eq_of_isBddIntegral E (isBddIntegral_sub E hf hg (isBddIntegral_of_isBddMeasurable E hf)
    (isBddIntegral_of_isBddMeasurable E hg))
theorem isPVM_pushforward {X' : Type} [MeasurableSpace X']
    (E : PVM X H) (κ : X → X') (hκ : Measurable κ) :
    IsPVM (E.pushforward κ hκ) where
  isOrthProj Y := E.isPVM.isOrthProj _
  map_univ := E.isPVM.map_univ
  map_inter Y Y' := E.isPVM.map_inter ⟨κ ⁻¹' Y.1, hκ Y.2⟩ ⟨κ ⁻¹' Y'.1, hκ Y'.2⟩
  countablyAdditive ψ := by
    intro Y hY
    have h := E.isPVM.countablyAdditive ψ
      (fun k => ⟨κ ⁻¹' (Y k).1, hκ (Y k).2⟩) (fun k l hkl => (hY hkl).preimage κ)
    have e : (⟨⋃ k, κ ⁻¹' (Y k).1, MeasurableSet.iUnion fun k => hκ (Y k).2⟩ :
        MeasSet X) =
        ⟨κ ⁻¹' ⋃ k, (Y k).1, hκ (MeasurableSet.iUnion fun k => (Y k).2)⟩ :=
      Subtype.ext Set.preimage_iUnion.symm
    rw [e] at h
    exact h
theorem diagMeasure_pushforward {X' : Type} [MeasurableSpace X']
    (E : PVM X H) (κ : X → X') (hκ : Measurable κ)
    (h : IsPVM (E.pushforward κ hκ)) (ψ : H) :
    (PVM.mk (E.pushforward κ hκ) h).diagMeasure ψ =
      (E.diagMeasure ψ).map κ := by
  refine Measure.ext fun Y hY => ?_
  rw [Measure.map_apply hκ hY]
  exact ((PVM.mk (E.pushforward κ hκ) h).diagMeasure_apply ψ ⟨Y, hY⟩).trans
    (E.diagMeasure_apply ψ ⟨κ ⁻¹' Y, hκ hY⟩).symm
theorem bddIntegral_pushforward {X' : Type} [MeasurableSpace X']
    (E : PVM X H) (κ : X → X') (hκ : Measurable κ)
    (h : IsPVM (E.pushforward κ hκ)) {f' : X' → ℂ}
    (hf : IsBddMeasurable f') :
    (PVM.mk (E.pushforward κ hκ) h).bddIntegral f' = E.bddIntegral (f' ∘ κ) := by
  have hb : IsBddMeasurable (f' ∘ κ) := by
    obtain ⟨hm, C, hC⟩ := hf
    exact ⟨hm.comp hκ, C, fun x => hC (κ x)⟩
  refine bddIntegral_eq_of_isBddIntegral _ fun ψ => ?_
  rw [diagMeasure_pushforward, integral_map hκ.aemeasurable hf.1.aestronglyMeasurable]
  exact isBddIntegral_of_isBddMeasurable E hb ψ
section UnitaryConjugation
variable {H' : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
theorem inner_map_map_of_isUnitaryMap {W : H →ₗ[ℂ] H'} (hW : IsUnitaryMap W) (φ ψ : H) :
    ⟪W φ, W ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ :=
  (⟨W, hW.isometric⟩ : H →ₗᵢ[ℂ] H').inner_map_map φ ψ
theorem unitary_comp_comp_apply {W : H →ₗ[ℂ] H'} (hW : IsUnitaryMap W)
    (B : BddOp H) (ψ : H) :
    (unitaryToBdd hW ∘L B ∘L unitaryInvToBdd hW) (W ψ) = W (B ψ) := by
  have h₁ : unitaryInvToBdd hW (W ψ) = ψ := hW.toLinearEquiv.symm_apply_apply ψ
  change unitaryToBdd hW (B (unitaryInvToBdd hW (W ψ))) = W (B ψ)
  rw [h₁]
  rfl
theorem isPVM_conj (E : PVM X H) {W : H →ₗ[ℂ] H'}
    (hW : IsUnitaryMap W) : IsPVM (E.conj hW) where
  isOrthProj Y := by
    refine ⟨fun χ χ' => ?_, ?_⟩
    · obtain ⟨φ, rfl⟩ := hW.onto χ
      obtain ⟨ψ, rfl⟩ := hW.onto χ'
      rw [E.conj_apply, E.conj_apply, inner_map_map_of_isUnitaryMap hW, inner_map_map_of_isUnitaryMap hW]
      exact (E.isPVM.isOrthProj Y).selfAdjoint φ ψ
    · ext χ
      obtain ⟨ψ, rfl⟩ := hW.onto χ
      have h₁ : E Y (E Y ψ) = E Y ψ := by
        have h₂ := apply_mul_self E Y
        exact congrArg (fun T : BddOp H => T ψ) h₂
      rw [pow_two]
      change E.conj hW Y (E.conj hW Y (W ψ)) = E.conj hW Y (W ψ)
      rw [E.conj_apply, E.conj_apply, h₁]
  map_univ := by
    ext χ
    obtain ⟨ψ, rfl⟩ := hW.onto χ
    rw [E.conj_apply, E.isPVM.map_univ]
    rfl
  map_inter Y Y' := by
    ext χ
    obtain ⟨ψ, rfl⟩ := hW.onto χ
    change _ = E.conj hW Y (E.conj hW Y' (W ψ))
    rw [E.conj_apply, E.conj_apply, E.conj_apply,
      E.isPVM.map_inter]
    rfl
  countablyAdditive χ := by
    obtain ⟨ψ, rfl⟩ := hW.onto χ
    have h₁ : diagForm (E.conj hW) (W ψ) = diagForm E ψ := by
      funext Y
      change ⟪W ψ, E.conj hW Y (W ψ)⟫_ℂ = ⟪ψ, E Y ψ⟫_ℂ
      rw [E.conj_apply, inner_map_map_of_isUnitaryMap hW]
    rw [h₁]
    exact E.isPVM.countablyAdditive ψ
theorem diagMeasure_conj (E : PVM X H) {W : H →ₗ[ℂ] H'}
    (hW : IsUnitaryMap W) (h : IsPVM (E.conj hW)) (ψ : H) :
    (PVM.mk (E.conj hW) h).diagMeasure (W ψ) = E.diagMeasure ψ := by
  refine Measure.ext fun Y hY => ?_
  have h₁ : diagForm (E.conj hW) (W ψ) ⟨Y, hY⟩ = diagForm E ψ ⟨Y, hY⟩ := by
    change ⟪W ψ, E.conj hW ⟨Y, hY⟩ (W ψ)⟫_ℂ = ⟪ψ, E ⟨Y, hY⟩ ψ⟫_ℂ
    rw [E.conj_apply, inner_map_map_of_isUnitaryMap hW]
  refine ((PVM.mk (E.conj hW) h).diagMeasure_apply (W ψ)
    ⟨Y, hY⟩).trans ?_
  refine Eq.trans ?_ (E.diagMeasure_apply ψ ⟨Y, hY⟩).symm
  exact congrArg (fun z : ℂ => ENNReal.ofReal z.re) h₁
theorem bddIntegral_conj (E : PVM X H) {W : H →ₗ[ℂ] H'}
    (hW : IsUnitaryMap W) (h : IsPVM (E.conj hW)) {f : X → ℂ}
    (hf : IsBddMeasurable f) :
    (PVM.mk (E.conj hW) h).bddIntegral f =
      unitaryToBdd hW ∘L E.bddIntegral f ∘L unitaryInvToBdd hW := by
  refine bddIntegral_eq_of_isBddIntegral _ fun χ => ?_
  obtain ⟨ψ, rfl⟩ := hW.onto χ
  rw [diagMeasure_conj, unitary_comp_comp_apply, inner_map_map_of_isUnitaryMap hW]
  exact isBddIntegral_of_isBddMeasurable E hf ψ
end UnitaryConjugation
theorem laws (E : PVM X H) : Laws E where
  diag_finite ψ := inferInstance
  diag_real_eq := diagMeasure_real_eq_norm_sq E
  diag_real_univ := diagMeasure_real_univ E
  apply_empty := apply_empty_eq_zero E
  existsUnique_bddIntegral f hf := by
    refine ⟨E.bddIntegral f, isBddIntegral_of_isBddMeasurable E hf, fun B hB => ?_⟩
    exact (bddIntegral_eq_of_isBddIntegral E hB).symm
  bddIntegral_add f g hf hg :=
    bddIntegral_eq_of_isBddIntegral E (isBddIntegral_add E hf hg (isBddIntegral_of_isBddMeasurable E hf)
      (isBddIntegral_of_isBddMeasurable E hg))
  bddIntegral_smul z f hf := bddIntegral_eq_of_isBddIntegral E (isBddIntegral_smul E z (isBddIntegral_of_isBddMeasurable E hf))
  bddIntegral_mul f g hf hg := bddIntegral_mul_of_isBddMeasurable E hf hg
  bddIntegral_indicator := bddIntegral_indicatorOne E
  bddIntegral_one := by
    refine bddIntegral_eq_of_isBddIntegral E fun ψ => ?_
    have h₁ := inner_apply_eq_diagMeasure_real E ψ ⟨Set.univ, MeasurableSet.univ⟩
    rw [E.isPVM.map_univ] at h₁
    refine h₁.trans ?_
    rw [integral_const, Complex.real_smul, mul_one]
  inner_bddIntegral f hf φ ψ := inner_bddIntegral_eq E hf φ ψ
  norm_bddIntegral_sq f hf ψ := norm_bddIntegral_apply_sq E hf ψ
  integral_norm_sq_le f hf ψ := by
    refine integral_norm_sq_le_mul E hf (fun x => ?_) ψ
    obtain ⟨C, hC⟩ := hf.2
    refine le_ciSup (f := fun x => ‖f x‖ ^ 2) ⟨C ^ 2, ?_⟩ x
    rintro _ ⟨y, rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (hC y) 2
  isSymmetricOp_bddIntegral f hf hre φ ψ := by
    have h₁ : (fun x => conj (f x)) = f := funext fun x => Complex.conj_eq_iff_im.mpr (hre x)
    have h₂ := inner_bddIntegral_eq E hf φ ψ
    rw [h₁] at h₂
    exact h₂
  bddIntegral_nonneg f hf hpos := by
    have hre : ∀ x, (f x).im = 0 := fun x => (Complex.le_def.mp (hpos x)).2.symm
    have hs : IsSymmetricOp (E.bddIntegral f) := by
      intro φ ψ
      have h₁ : (fun x => conj (f x)) = f := funext fun x => Complex.conj_eq_iff_im.mpr (hre x)
      have h₂ := inner_bddIntegral_eq E hf φ ψ
      rw [h₁] at h₂
      exact h₂
    refine ⟨fun φ ψ => by simp, hs, fun ψ => ?_⟩
    have h₁ : ⟪ψ, (0 : BddOp H) ψ⟫_ℂ = 0 := by simp
    rw [h₁, isBddIntegral_of_isBddMeasurable E hf ψ]
    have h₂ : f = fun x => (((f x).re : ℝ) : ℂ) := funext fun x =>
      Complex.ext (by simp) (by simp [hre x])
    have h₃ : ∫ x, (((f x).re : ℝ) : ℂ) ∂(E.diagMeasure ψ) =
        ((∫ x, (f x).re ∂(E.diagMeasure ψ) : ℝ) : ℂ) := integral_ofReal
    rw [h₂, h₃]
    exact Complex.zero_le_real.mpr
      (MeasureTheory.integral_nonneg fun x => (Complex.le_def.mp (hpos x)).1)
  tendsto_bddIntegral F f hF hf hlim hbound ψ := by
    obtain ⟨C, hC⟩ := hbound
    obtain ⟨C', hC'⟩ := hf.2
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h₁ : ∀ n, ‖E.bddIntegral (F n) ψ - E.bddIntegral f ψ‖ =
        Real.sqrt (∫ x, ‖(F n - f) x‖ ^ 2 ∂(E.diagMeasure ψ)) := by
      intro n
      rw [← norm_bddIntegral_apply_sq E (isBddMeasurable_sub (hF n) hf), bddIntegral_sub E (hF n) hf,
        Real.sqrt_sq (norm_nonneg _)]
      rfl
    have h₂ := tendsto_integral_of_uniform_bound E (f := fun _ : X => (0 : ℝ))
      (F := fun n x => ‖(F n - f) x‖ ^ 2) (C := (C + C') ^ 2) ψ
      (fun n => (((hF n).1.sub hf.1).norm.pow_const 2).aestronglyMeasurable)
      (fun n x => by
        have h₃ : ‖(F n - f) x‖ ≤ C + C' :=
          (norm_sub_le _ _).trans (add_le_add (hC n x) (hC' x))
        have h₄ : ‖‖(F n - f) x‖ ^ 2‖ = ‖(F n - f) x‖ ^ 2 := by simp
        rw [h₄]
        exact pow_le_pow_left₀ (norm_nonneg _) h₃ 2)
      (fun x => by
        have h₃ : Tendsto (fun n => F n x - f x) atTop (𝓝 0) := by
          simpa using (hlim x).sub_const (f x)
        simpa using (h₃.norm).pow 2)
    have h₃ : (∫ _ : X, (0 : ℝ) ∂(E.diagMeasure ψ)) = 0 := by simp
    rw [h₃] at h₂
    have h₄ := (Real.continuous_sqrt.tendsto 0).comp h₂
    rw [Real.sqrt_zero] at h₄
    exact h₄.congr fun n => (h₁ n).symm
  bddIntegral_congr f g hf hg Y₀ h₀ hoff := by
    refine ext_of_inner_self fun ψ => ?_
    rw [isBddIntegral_of_isBddMeasurable E hf ψ, isBddIntegral_of_isBddMeasurable E hg ψ]
    refine integral_congr_ae ?_
    have hz : E.diagMeasure ψ Y₀.1 = 0 := by
      rw [E.diagMeasure_apply ψ Y₀]
      have h₁ : diagForm E ψ Y₀ = 0 := by
        change ⟪ψ, E Y₀ ψ⟫_ℂ = 0
        rw [h₀]
        simp
      rw [h₁]
      simp
    have hae : ∀ᵐ x ∂(E.diagMeasure ψ), x ∉ Y₀.1 := measure_eq_zero_iff_ae_notMem.mp hz
    filter_upwards [hae] with x hx using hoff x hx
  diag_bddIntegral f hf Y ψ := by
    have h₂ : E Y (E.bddIntegral f ψ) = E.bddIntegral (indicatorOne Y.1 * f) ψ := by
      rw [bddIntegral_mul_of_isBddMeasurable E (isBddMeasurable_indicatorOne Y) hf, bddIntegral_indicatorOne]
      rfl
    rw [diagMeasure_real_eq_norm_sq, h₂, norm_bddIntegral_apply_sq E (isBddMeasurable_mul (isBddMeasurable_indicatorOne Y) hf),
      ← integral_indicator Y.2]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ Y.1
    · simp [indicatorOne, constOne, hx]
    · simp [indicatorOne, hx]
  pushforward_laws X' _ κ hκ := by
    refine ⟨isPVM_pushforward E κ hκ, fun ψ => diagMeasure_pushforward E κ hκ _ ψ,
      fun f' hf => bddIntegral_pushforward E κ hκ _ hf⟩
  conj_laws H' _ _ _ W hW := by
    refine ⟨isPVM_conj E hW, fun ψ => diagMeasure_conj E hW _ ψ,
      fun f hf => bddIntegral_conj E hW _ hf⟩
theorem statement_holds : Statement := fun _ _ _ _ _ _ E => laws E
end BddCalculus
end YangMills.Construction.SpectralMeasures
