import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ComplexOrder NNReal ENNReal
noncomputable section
namespace YangMills.Construction.SpectralCalculus
section Forms
variable {V : Type*}
def formSeminorm (b : V → V → ℂ) (f : V) : ℝ := Real.sqrt (b f f).re
def IsNullForForm (b : V → V → ℂ) (f : V) : Prop := formSeminorm b f = 0
variable [AddCommGroup V] [Module ℂ V]
structure IsPosHermitianForm (b : V → V → ℂ) : Prop where
  add_left : ∀ f₁ f₂ h, b (f₁ + f₂) h = b f₁ h + b f₂ h
  smul_left : ∀ (a : ℂ) f h, b (a • f) h = conj a * b f h
  add_right : ∀ f h₁ h₂, b f (h₁ + h₂) = b f h₁ + b f h₂
  smul_right : ∀ (a : ℂ) f h, b f (a • h) = a * b f h
  conj_symm : ∀ f h, b h f = conj (b f h)
  nonneg : ∀ f, 0 ≤ b f f
structure IsDefiniteForm (b : V → V → ℂ) : Prop extends IsPosHermitianForm b where
  eq_zero_of_null : ∀ f, IsNullForForm b f → f = 0
def IsFormCauchy (b : V → V → ℂ) (f : ℕ → V) : Prop :=
  Tendsto (fun p : ℕ × ℕ => formSeminorm b (f p.1 - f p.2)) atTop (𝓝 0)
def FormTendsto (b : V → V → ℂ) (f : ℕ → V) (x : V) : Prop :=
  Tendsto (fun j => formSeminorm b (f j - x)) atTop (𝓝 0)
structure IsCompleteForm (b : V → V → ℂ) : Prop extends IsDefiniteForm b where
  exists_tendsto : ∀ f, IsFormCauchy b f → ∃ x, FormTendsto b f x
def FormEquivalent (b : V → V → ℂ) (f h : ℕ → V) : Prop :=
  Tendsto (fun j => formSeminorm b (f j - h j)) atTop (𝓝 0)
theorem isPosHermitianForm_zero : IsPosHermitianForm (fun _ _ => 0 : V → V → ℂ) where
  add_left := by simp
  smul_left := by simp
  add_right := by simp
  smul_right := by simp
  conj_symm := by simp
  nonneg := by simp
def posHermitianPart (b : V → V → ℂ) : V → V → ℂ :=
  open Classical in if IsPosHermitianForm b then b else fun _ _ => 0
theorem isPosHermitianForm_posHermitianPart (b : V → V → ℂ) :
    IsPosHermitianForm (posHermitianPart b) := by
  unfold posHermitianPart
  split_ifs with h
  · exact h
  · exact isPosHermitianForm_zero
theorem posHermitianPart_of_isPosHermitianForm {b : V → V → ℂ}
    (h : IsPosHermitianForm b) : posHermitianPart b = b :=
  if_pos h
@[reducible] def formPreInnerCore (b : V → V → ℂ) : PreInnerProductSpace.Core ℂ V where
  inner := posHermitianPart b
  conj_inner_symm x y := ((isPosHermitianForm_posHermitianPart b).conj_symm y x).symm
  re_inner_nonneg x := (Complex.le_def.mp ((isPosHermitianForm_posHermitianPart b).nonneg x)).1
  add_left := (isPosHermitianForm_posHermitianPart b).add_left
  smul_left x y r := (isPosHermitianForm_posHermitianPart b).smul_left r x y
def FormSpace (_b : V → V → ℂ) : Type _ := V
instance (b : V → V → ℂ) : SeminormedAddCommGroup (FormSpace b) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ V _ _ _ (formPreInnerCore b)
instance (b : V → V → ℂ) : InnerProductSpace ℂ (FormSpace b) :=
  InnerProductSpace.ofCore (formPreInnerCore b)
def toFormSpace (b : V → V → ℂ) (x : V) : FormSpace b := x
theorem norm_formSpace (b : V → V → ℂ) (x : FormSpace b) :
    ‖x‖ = formSeminorm (posHermitianPart b) x :=
  norm_eq_sqrt_re_inner (𝕜 := ℂ) x
theorem isFormCauchy_iff_cauchySeq (b : V → V → ℂ) (f : ℕ → V) :
    IsFormCauchy (posHermitianPart b) f ↔ CauchySeq (fun j => toFormSpace b (f j)) := by
  rw [cauchySeq_iff_tendsto_dist_atTop_0]
  refine iff_of_eq (congrArg (fun u => Tendsto u atTop (𝓝 0)) (funext fun p => ?_))
  rw [dist_eq_norm, norm_formSpace]
  rfl
end Forms
section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsSeqDense (S : Set H) : Prop :=
  ∀ v : H, ∃ u : ℕ → H, (∀ j, u j ∈ S) ∧ Tendsto u atTop (𝓝 v)
omit [InnerProductSpace ℂ H] in
theorem isSeqDense_iff_dense (S : Set H) : IsSeqDense S ↔ Dense S := by
  constructor
  · intro h v
    obtain ⟨u, hu, hl⟩ := h v
    exact mem_closure_of_tendsto hl (Eventually.of_forall hu)
  · intro h v
    obtain ⟨u, hu, hl⟩ := mem_closure_iff_seq_limit.mp (h v)
    exact ⟨u, hu, hl⟩
theorem formSeminorm_inner (v : H) : formSeminorm (fun u w : H => inner ℂ u w) v = ‖v‖ :=
  (norm_eq_sqrt_re_inner (𝕜 := ℂ) v).symm
theorem isCompleteForm_inner [CompleteSpace H] :
    IsCompleteForm (fun u v : H => inner ℂ u v) where
  add_left := fun _ _ _ => inner_add_left _ _ _
  smul_left := fun _ _ _ => inner_smul_left _ _ _
  add_right := fun _ _ _ => inner_add_right _ _ _
  smul_right := fun _ _ _ => inner_smul_right _ _ _
  conj_symm := fun _ _ => (inner_conj_symm _ _).symm
  nonneg := fun v => Complex.le_def.mpr
    ⟨by simpa using inner_self_nonneg (𝕜 := ℂ) (x := v), by simpa using (inner_self_im (𝕜 := ℂ) v).symm⟩
  eq_zero_of_null := fun f hf => by
    rw [IsNullForForm, formSeminorm_inner] at hf
    exact norm_eq_zero.mp hf
  exists_tendsto := fun f hf => by
    have hc : CauchySeq f := by
      rw [cauchySeq_iff_tendsto_dist_atTop_0]
      simpa only [IsFormCauchy, formSeminorm_inner, dist_eq_norm] using hf
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨x, ?_⟩
    simpa only [FormTendsto, formSeminorm_inner] using tendsto_iff_norm_sub_tendsto_zero.mp hx
end Hilbert
section Completion
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def formCauchySubmodule (b : V → V → ℂ) : Submodule ℂ (ℕ → V) where
  carrier := {f | IsFormCauchy (posHermitianPart b) f}
  add_mem' := fun {f h} hf hh => (isFormCauchy_iff_cauchySeq b _).mpr
    (((isFormCauchy_iff_cauchySeq b f).mp hf).add ((isFormCauchy_iff_cauchySeq b h).mp hh))
  zero_mem' := (isFormCauchy_iff_cauchySeq b _).mpr
    (cauchySeq_const (0 : FormSpace b))
  smul_mem' := fun a f hf => (isFormCauchy_iff_cauchySeq b _).mpr
    ((uniformContinuous_const_smul (M := ℂ) (X := FormSpace b) a).comp_cauchySeq
      ((isFormCauchy_iff_cauchySeq b f).mp hf))
theorem mem_formCauchySubmodule (b : V → V → ℂ) (f : ℕ → V) :
    f ∈ formCauchySubmodule b ↔ IsFormCauchy (posHermitianPart b) f :=
  Iff.rfl
def toFormCauchySubmodule (b : V → V → ℂ) (f : ℕ → V) (hf : IsFormCauchy (posHermitianPart b) f) :
    formCauchySubmodule b :=
  ⟨f, (mem_formCauchySubmodule b f).mpr hf⟩
abbrev FormCompletion (b : V → V → ℂ) : Type _ := UniformSpace.Completion (FormSpace b)
def coeSeqFormCompletion (b : V → V → ℂ) (f : ℕ → V) (j : ℕ) : FormCompletion b :=
  ((toFormSpace b (f j) : FormSpace b) : FormCompletion b)
theorem cauchySeq_coeSeqFormCompletion (b : V → V → ℂ) (f : formCauchySubmodule b) :
    CauchySeq (coeSeqFormCompletion b f.1) :=
  (UniformSpace.Completion.uniformContinuous_coe (FormSpace b)).comp_cauchySeq
    ((isFormCauchy_iff_cauchySeq b f.1).mp ((mem_formCauchySubmodule b f.1).mp f.2))
def seqLimit (b : V → V → ℂ) (f : formCauchySubmodule b) : FormCompletion b :=
  limUnder atTop (coeSeqFormCompletion b f.1)
theorem tendsto_seqLimit (b : V → V → ℂ) (f : formCauchySubmodule b) :
    Tendsto (coeSeqFormCompletion b f.1) atTop (𝓝 (seqLimit b f)) :=
  (cauchySeq_coeSeqFormCompletion b f).tendsto_limUnder
def seqLimitLinear (b : V → V → ℂ) : formCauchySubmodule b →ₗ[ℂ] FormCompletion b where
  toFun := seqLimit b
  map_add' f h := tendsto_nhds_unique (tendsto_seqLimit b (f + h)) <| by
    refine ((tendsto_seqLimit b f).add (tendsto_seqLimit b h)).congr fun j => ?_
    exact (UniformSpace.Completion.coe_add (toFormSpace b (f.1 j)) (toFormSpace b (h.1 j))).symm
  map_smul' a f := tendsto_nhds_unique (tendsto_seqLimit b (a • f)) <| by
    refine ((tendsto_seqLimit b f).const_smul a).congr fun j => ?_
    exact (UniformSpace.Completion.coe_smul a (toFormSpace b (f.1 j))).symm
theorem seqLimitLinear_surjective (b : V → V → ℂ) : Function.Surjective (seqLimitLinear b) := by
  intro y
  obtain ⟨u, hu, hl⟩ := mem_closure_iff_seq_limit.mp
    (UniformSpace.Completion.denseRange_coe (α := FormSpace b) y)
  choose x hx using hu
  have hc : CauchySeq x := by
    have h₁ := cauchySeq_iff_tendsto_dist_atTop_0.mp hl.cauchySeq
    refine cauchySeq_iff_tendsto_dist_atTop_0.mpr (h₁.congr fun p => ?_)
    rw [← hx p.1, ← hx p.2]
    exact UniformSpace.Completion.dist_eq _ _
  let f : formCauchySubmodule b := toFormCauchySubmodule b x ((isFormCauchy_iff_cauchySeq b x).mpr hc)
  refine ⟨f, tendsto_nhds_unique (tendsto_seqLimit b f) ?_⟩
  exact hl.congr fun j => (hx j).symm
def formNullSubmodule (b : V → V → ℂ) : Submodule ℂ (formCauchySubmodule b) := LinearMap.ker (seqLimitLinear b)
theorem sub_mem_formNullSubmodule_iff (b : V → V → ℂ) (f h : formCauchySubmodule b) :
    f - h ∈ formNullSubmodule b ↔ FormEquivalent (posHermitianPart b) f.1 h.1 := by
  have hlim := tendsto_seqLimit b (f - h)
  have hnorm : ∀ j, ‖coeSeqFormCompletion b (f - h).1 j‖ = formSeminorm (posHermitianPart b) (f.1 j - h.1 j) :=
    fun j => (UniformSpace.Completion.norm_coe (toFormSpace b (f.1 j - h.1 j))).trans
      (norm_formSpace b _)
  constructor
  · intro hm
    have h0 : seqLimit b (f - h) = 0 := hm
    rw [h0] at hlim
    simpa only [FormEquivalent, ← hnorm, norm_zero] using hlim.norm
  · intro he
    have h0 : Tendsto (coeSeqFormCompletion b (f - h).1) atTop (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
      simpa only [FormEquivalent, ← hnorm] using he
    exact tendsto_nhds_unique hlim h0
def SeparatedCompletion (b : V → V → ℂ) : Type _ := formCauchySubmodule b ⧸ formNullSubmodule b
instance (b : V → V → ℂ) : AddCommGroup (SeparatedCompletion b) :=
  inferInstanceAs (AddCommGroup (formCauchySubmodule b ⧸ formNullSubmodule b))
instance (b : V → V → ℂ) : Module ℂ (SeparatedCompletion b) :=
  inferInstanceAs (Module ℂ (formCauchySubmodule b ⧸ formNullSubmodule b))
def seqClass (b : V → V → ℂ) (f : ℕ → V) (hf : IsFormCauchy (posHermitianPart b) f) :
    SeparatedCompletion b :=
  (formNullSubmodule b).mkQ (toFormCauchySubmodule b f hf)
def separatedCompletionEquiv (b : V → V → ℂ) : SeparatedCompletion b ≃ₗ[ℂ] FormCompletion b :=
  (seqLimitLinear b).quotKerEquivOfSurjective (seqLimitLinear_surjective b)
instance (b : V → V → ℂ) : NormedAddCommGroup (SeparatedCompletion b) :=
  NormedAddCommGroup.induced _ _ (separatedCompletionEquiv b) (separatedCompletionEquiv b).injective
instance (b : V → V → ℂ) : NormedSpace ℂ (SeparatedCompletion b) :=
  NormedSpace.induced ℂ _ _ (separatedCompletionEquiv b)
instance (b : V → V → ℂ) : InnerProductSpace ℂ (SeparatedCompletion b) where
  inner x y := inner ℂ (separatedCompletionEquiv b x) (separatedCompletionEquiv b y)
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (𝕜 := ℂ) (separatedCompletionEquiv b x)
  conj_inner_symm x y := inner_conj_symm _ _
  add_left x y z := by simp only [map_add, inner_add_left]
  smul_left x y a := by simp only [map_smul, inner_smul_left]
instance (b : V → V → ℂ) : CompleteSpace (SeparatedCompletion b) := by
  have hi : Isometry (separatedCompletionEquiv b) := AddMonoidHomClass.isometry_of_norm _ fun _ => rfl
  exact (completeSpace_congr (e := (separatedCompletionEquiv b).toEquiv) hi.isUniformEmbedding).mpr inferInstance
theorem separatedCompletionEquiv_seqClass (b : V → V → ℂ) (f : ℕ → V)
    (hf : IsFormCauchy (posHermitianPart b) f) :
    separatedCompletionEquiv b (seqClass b f hf) = seqLimit b (toFormCauchySubmodule b f hf) :=
  rfl
theorem exists_eq_seqClass (b : V → V → ℂ) (x : SeparatedCompletion b) :
    ∃ f hf, x = seqClass b f hf := by
  obtain ⟨f, rfl⟩ := (formNullSubmodule b).mkQ_surjective x
  exact ⟨f.1, (mem_formCauchySubmodule b f.1).mp f.2, rfl⟩
theorem seqClass_eq_seqClass_iff (b : V → V → ℂ) {f h : ℕ → V}
    (hf : IsFormCauchy (posHermitianPart b) f) (hh : IsFormCauchy (posHermitianPart b) h) :
    seqClass b f hf = seqClass b h hh ↔ FormEquivalent (posHermitianPart b) f h :=
  (Submodule.Quotient.eq _).trans
    (sub_mem_formNullSubmodule_iff b (toFormCauchySubmodule b f hf) (toFormCauchySubmodule b h hh))
theorem seqClass_add_smul (b : V → V → ℂ) {f h : ℕ → V} (a : ℂ)
    (hf : IsFormCauchy (posHermitianPart b) f) (hh : IsFormCauchy (posHermitianPart b) h)
    (hs : IsFormCauchy (posHermitianPart b) fun j => f j + a • h j) :
    seqClass b (fun j => f j + a • h j) hs =
      seqClass b f hf + a • seqClass b h hh :=
  rfl
theorem tendsto_inner_seqClass (b : V → V → ℂ) {f h : ℕ → V}
    (hf : IsFormCauchy (posHermitianPart b) f) (hh : IsFormCauchy (posHermitianPart b) h) :
    Tendsto (fun j => posHermitianPart b (f j) (h j)) atTop
      (𝓝 (inner ℂ (seqClass b f hf) (seqClass b h hh))) := by
  have h₁ := tendsto_seqLimit b (toFormCauchySubmodule b f hf)
  have h₂ := tendsto_seqLimit b (toFormCauchySubmodule b h hh)
  refine (h₁.inner (𝕜 := ℂ) h₂).congr fun j => ?_
  exact UniformSpace.Completion.inner_coe (𝕜 := ℂ) (toFormSpace b (f j)) (toFormSpace b (h j))
theorem isFormCauchy_const (b : V → V → ℂ) (f : V) :
    IsFormCauchy (posHermitianPart b) fun _ : ℕ => f :=
  (isFormCauchy_iff_cauchySeq b _).mpr (cauchySeq_const (toFormSpace b f))
def constClass (b : V → V → ℂ) (f : V) : SeparatedCompletion b :=
  seqClass b (fun _ => f) (isFormCauchy_const b f)
end Completion
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsSymmetricBounded [CompleteSpace H] (B : H →L[ℂ] H) : Prop := ∀ u v, inner ℂ (B u) v = inner ℂ u (B v)
def IsPositiveBounded [CompleteSpace H] (B : H →L[ℂ] H) : Prop :=
  IsSymmetricBounded B ∧ ∀ v, 0 ≤ inner ℂ v (B v)
def IsContractive [CompleteSpace H] (B : H →L[ℂ] H) : Prop := ‖B‖ ≤ 1
def IsUnitaryBounded [CompleteSpace H] (B : H →L[ℂ] H) : Prop := Function.Bijective B ∧ ∀ v, ‖B v‖ = ‖v‖
def IsOrthogonalProjection [CompleteSpace H] (B : H →L[ℂ] H) : Prop := IsSymmetricBounded B ∧ B * B = B
structure IsSelfAdjointContractionSemigroup [CompleteSpace H] (T : ℝ≥0 → H →L[ℂ] H) : Prop where
  isSymmetricBounded : ∀ t, IsSymmetricBounded (T t)
  isContractive : ∀ t, IsContractive (T t)
  map_zero : T 0 = 1
  map_add : ∀ t t', T t * T t' = T (t + t')
  tendsto : ∀ v, Tendsto (fun t => T t v) (𝓝[>] 0) (𝓝 v)
structure IsStronglyContinuousUnitaryGroup [CompleteSpace H] (U : ℝ → H →L[ℂ] H) : Prop where
  isUnitaryBounded : ∀ s, IsUnitaryBounded (U s)
  map_zero : U 0 = 1
  map_add : ∀ s s', U s * U s' = U (s + s')
  tendsto : ∀ v, Tendsto (fun s => U s v) (𝓝[≠] 0) (𝓝 v)
structure IsCommutingSemigroupGroup [CompleteSpace H] (T : ℝ≥0 → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H) : Prop where
  semigroup : IsSelfAdjointContractionSemigroup T
  group : IsStronglyContinuousUnitaryGroup U
  commute : ∀ t s, Commute (T t) (U s)
end Operators
section Measures
variable {α : Type*} [MeasurableSpace α]
abbrev MeasurableSubtype (α : Type*) [MeasurableSpace α] : Type _ := {B : Set α // MeasurableSet B}
instance variation_isFiniteMeasure (μ : ComplexMeasure α) : IsFiniteMeasure μ.variation := by
  let jr := (ComplexMeasure.re μ).toJordanDecomposition
  let ji := (ComplexMeasure.im μ).toJordanDecomposition
  let m : Measure α := jr.posPart + jr.negPart + ji.posPart + ji.negPart
  have hm : IsFiniteMeasure m := by
    simp only [m]
    infer_instance
  have hle : μ.variation ≤ m := by
    refine VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_
    have key : ∀ s : SignedMeasure α, s E = s.toJordanDecomposition.posPart.real E -
        s.toJordanDecomposition.negPart.real E := fun s => by
      have := congrArg (fun r : SignedMeasure α => r E) s.toSignedMeasure_toJordanDecomposition
      simpa [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_apply_measurable hE,
        sub_apply, hE] using this.symm
    have hr : (μ E).re = jr.posPart.real E - jr.negPart.real E := key (ComplexMeasure.re μ)
    have hi : (μ E).im = ji.posPart.real E - ji.negPart.real E := key (ComplexMeasure.im μ)
    have hnorm : ‖μ E‖ ≤ m.real E := by
      have h₁ : ‖μ E‖ ≤ |(μ E).re| + |(μ E).im| := Complex.norm_le_abs_re_add_abs_im _
      have h₂ : m.real E = jr.posPart.real E + jr.negPart.real E + ji.posPart.real E +
          ji.negPart.real E := by
        simp only [m, Measure.real, Measure.add_apply]
        rw [ENNReal.toReal_add (by finiteness) (by finiteness),
          ENNReal.toReal_add (by finiteness) (by finiteness),
          ENNReal.toReal_add (by finiteness) (by finiteness)]
      rw [hr, hi] at h₁
      have p₁ := abs_sub (jr.posPart.real E) (jr.negPart.real E)
      have p₂ := abs_sub (ji.posPart.real E) (ji.negPart.real E)
      have q₁ : |jr.posPart.real E| = jr.posPart.real E := abs_of_nonneg measureReal_nonneg
      have q₂ : |jr.negPart.real E| = jr.negPart.real E := abs_of_nonneg measureReal_nonneg
      have q₃ : |ji.posPart.real E| = ji.posPart.real E := abs_of_nonneg measureReal_nonneg
      have q₄ : |ji.negPart.real E| = ji.negPart.real E := abs_of_nonneg measureReal_nonneg
      linarith
    calc ‖μ E‖ₑ = ENNReal.ofReal ‖μ E‖ := (ofReal_norm_eq_enorm _).symm
      _ ≤ ENNReal.ofReal (m.real E) := ENNReal.ofReal_le_ofReal hnorm
      _ = m E := ofReal_measureReal
  exact isFiniteMeasure_of_le m hle
abbrev mulPairing : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
def complexIntegral (μ : ComplexMeasure α) (F : α → ℂ) : ℂ := μ.integral F mulPairing
def conjMeasure (μ : ComplexMeasure α) : ComplexMeasure α :=
  μ.mapRange (starAddEquiv (R := ℂ)).toAddMonoidHom continuous_star
theorem conjMeasure_apply (μ : ComplexMeasure α) (B : Set α) : conjMeasure μ B = conj (μ B) :=
  rfl
def IsBoundedMeasurable (F : α → ℂ) : Prop := Measurable F ∧ ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C
def withDensityComplex (F : α → ℂ) (μ : ComplexMeasure α) : ComplexMeasure α := μ.withDensity F mulPairing
theorem withDensityComplex_apply {F : α → ℂ} (hF : IsBoundedMeasurable F) (μ : ComplexMeasure α) (B : Set α) :
    withDensityComplex F μ B = (μ.restrict B).integral F mulPairing := by
  obtain ⟨hm, C, hC⟩ := hF
  have hi : μ.Integrable F :=
    Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)
  exact VectorMeasure.withDensity_apply hi
end Measures
abbrev SpectralPlane : Type := ℝ≥0 × ℝ
def spectralCharacter (t : ℝ≥0) (s : ℝ) (p : SpectralPlane) : ℂ :=
  Complex.exp (((-(t : ℝ) * (p.1 : ℝ) : ℝ) : ℂ) + Complex.I * ((s * p.2 : ℝ) : ℂ))
def laplaceFourier (μ : ComplexMeasure SpectralPlane) (t : ℝ≥0) (s : ℝ) : ℂ :=
  complexIntegral μ (spectralCharacter t s)
def coordFst (p : SpectralPlane) : ℂ := ((p.1 : ℝ) : ℂ)
def coordSnd (p : SpectralPlane) : ℂ := (p.2 : ℂ)
section ProjectionValued
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
structure ProjValuedMeasure [CompleteSpace H] where
  toFun : MeasurableSubtype SpectralPlane → H →L[ℂ] H
  isOrthogonalProjection : ∀ B, IsOrthogonalProjection (toFun B)
  map_univ : toFun ⟨univ, MeasurableSet.univ⟩ = 1
  map_inter : ∀ B B', toFun B * toFun B' = toFun ⟨B.1 ∩ B'.1, B.2.inter B'.2⟩
  exists_complexMeasure : ∀ u v : H, ∃ μ : ComplexMeasure SpectralPlane,
    ∀ B : MeasurableSubtype SpectralPlane, μ B.1 = inner ℂ u (toFun B v)
variable {H}
namespace ProjValuedMeasure
instance [CompleteSpace H] :
    CoeFun (ProjValuedMeasure H) fun _ => MeasurableSubtype SpectralPlane → H →L[ℂ] H :=
  ⟨toFun⟩
def matrixCoeff [CompleteSpace H] (P : ProjValuedMeasure H) (u v : H) : ComplexMeasure SpectralPlane :=
  Classical.choose (P.exists_complexMeasure u v)
theorem matrixCoeff_apply [CompleteSpace H] (P : ProjValuedMeasure H) (u v : H)
    (B : MeasurableSubtype SpectralPlane) : P.matrixCoeff u v B.1 = inner ℂ u (P B v) :=
  Classical.choose_spec (P.exists_complexMeasure u v) B
def IsBoundedSpectralIntegral [CompleteSpace H] (P : ProjValuedMeasure H) (F : SpectralPlane → ℂ)
    (B : H →L[ℂ] H) : Prop :=
  ∀ u v, inner ℂ u (B v) = complexIntegral (P.matrixCoeff u v) F
def boundedSpectralIntegral [CompleteSpace H] (P : ProjValuedMeasure H) (F : SpectralPlane → ℂ) : H →L[ℂ] H :=
  Classical.epsilon (P.IsBoundedSpectralIntegral F)
def truncate (F : SpectralPlane → ℂ) (n : ℕ) : SpectralPlane → ℂ :=
  {p | ‖F p‖ ≤ n}.indicator F
def spectralDomain [CompleteSpace H] (P : ProjValuedMeasure H) (F : SpectralPlane → ℂ) : Set H :=
  {v | ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(P.matrixCoeff v v).variation < ∞}
end ProjValuedMeasure
end ProjectionValued
section Domains
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
abbrev PartialOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Type _ :=
  H →ₗ.[ℂ] H
structure IsSelfAdjointPartial [CompleteSpace H] (A : PartialOperator H) : Prop where
  dense_domain : IsSeqDense (A.domain : Set H)
  symmetric : ∀ u v : A.domain, inner ℂ (A u) (v : H) = inner ℂ (u : H) (A v)
  mem_domain : ∀ u : H, (∃ w : H, ∀ v : A.domain, inner ℂ u (A v) = inner ℂ w (v : H)) →
    u ∈ A.domain
def IsPositivePartial [CompleteSpace H] (A : PartialOperator H) : Prop :=
  IsSelfAdjointPartial A ∧ ∀ v : A.domain, 0 ≤ inner ℂ (v : H) (A v)
namespace ProjValuedMeasure
def IsSpectralIntegral [CompleteSpace H] (P : ProjValuedMeasure H) (F : SpectralPlane → ℂ)
    (A : PartialOperator H) : Prop :=
  (A.domain : Set H) = P.spectralDomain F ∧
    ∀ v : A.domain, Tendsto (fun n => P.boundedSpectralIntegral (truncate F n) (v : H)) atTop (𝓝 (A v))
def spectralIntegral [CompleteSpace H] (P : ProjValuedMeasure H) (F : SpectralPlane → ℂ) :
    PartialOperator H :=
  Classical.epsilon (P.IsSpectralIntegral F)
end ProjValuedMeasure
def cylinderSet (B' : MeasurableSubtype ℝ) : MeasurableSubtype SpectralPlane :=
  ⟨univ ×ˢ B'.1, MeasurableSet.univ.prod B'.2⟩
def IsSpectralIntegralSnd [CompleteSpace H] (P : ProjValuedMeasure H) (A : PartialOperator H) : Prop :=
  A = P.spectralIntegral coordSnd
def HasSpectralResolution [CompleteSpace H] (A : PartialOperator H) : Prop :=
  ∃ P : ProjValuedMeasure H, IsSpectralIntegralSnd P A
open Classical in
def spectralProjection [CompleteSpace H] (A : PartialOperator H) (B' : MeasurableSubtype ℝ) : H →L[ℂ] H :=
  if h : HasSpectralResolution A then (Classical.choose h) (cylinderSet B') else 0
open Classical in
def functionalCalculus [CompleteSpace H] (F : ℝ → ℂ) (A : PartialOperator H) : PartialOperator H :=
  if h : HasSpectralResolution A then
    (Classical.choose h).spectralIntegral fun p => F p.2
  else ⊥
def expNegMul [CompleteSpace H] (t : ℝ≥0) (A : PartialOperator H) : PartialOperator H :=
  functionalCalculus (fun x => Complex.exp ((-(t : ℝ) * x : ℝ) : ℂ)) A
def expIMul [CompleteSpace H] (s : ℝ) (A : PartialOperator H) : PartialOperator H :=
  functionalCalculus (fun x => Complex.exp (Complex.I * ((s * x : ℝ) : ℂ))) A
def CommuteSpectrally [CompleteSpace H] (A A' : PartialOperator H) : Prop :=
  HasSpectralResolution A ∧ HasSpectralResolution A' ∧
    ∀ B B' : MeasurableSubtype ℝ, Commute (spectralProjection A B) (spectralProjection A' B')
end Domains
end YangMills.Construction.SpectralCalculus
