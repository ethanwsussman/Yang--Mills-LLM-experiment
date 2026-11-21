import Mathlib
open MeasureTheory Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Matrices
abbrev ComplexMatrix2 : Type := Matrix (Fin 2) (Fin 2) ℂ
namespace ComplexMatrix2
abbrev fullTrace (X : ComplexMatrix2) : ℂ := Matrix.trace X
abbrev halfTrace (X : ComplexMatrix2) : ℂ := (1 / 2 : ℂ) * fullTrace X
abbrev operatorNorm (X : ComplexMatrix2) : ℝ := ‖X‖
abbrev specialUnitary : Submonoid ComplexMatrix2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

theorem quaternion_entries_of_mem_specialUnitary {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    g 1 1 = star (g 0 0) ∧ g 1 0 = -star (g 0 1) := by
  have hu : g * star g = 1 :=
    Matrix.mem_unitaryGroup_iff.1 (Matrix.mem_specialUnitaryGroup_iff.1 hg).1
  have hd : g.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.1 hg).2
  have hadj : Matrix.adjugate g = star g := by
    calc Matrix.adjugate g = Matrix.adjugate g * (g * star g) := by rw [hu, mul_one]
      _ = star g := by rw [← mul_assoc, Matrix.adjugate_mul, hd]; simp
  have h00 := congrFun (congrFun hadj 0) 0
  have h10 := congrFun (congrFun hadj 1) 0
  simp only [Matrix.adjugate_fin_two, Matrix.star_apply] at h00 h10
  simp at h00 h10
  refine ⟨h00, ?_⟩
  rw [← neg_eq_iff_eq_neg]
  simpa using h10

theorem det_quaternionMatrix {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M 1 1 = star (M 0 0) ∧ M 1 0 = -star (M 0 1)) :
    M.det = ((Complex.normSq (M 0 0) + Complex.normSq (M 0 1) : ℝ) : ℂ) := by
  obtain ⟨h1, h2⟩ := hM
  rw [Matrix.det_fin_two, h1, h2]
  simp only [Complex.star_def, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self]
  ring

theorem det_quaternionMatrix_mem_slitPlane {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M 1 1 = star (M 0 0) ∧ M 1 0 = -star (M 0 1))
    (h : M.det ≠ 0) : M.det ∈ Complex.slitPlane := by
  rw [det_quaternionMatrix hM] at h ⊢
  have hnn : 0 ≤ Complex.normSq (M 0 0) + Complex.normSq (M 0 1) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hne : Complex.normSq (M 0 0) + Complex.normSq (M 0 1) ≠ 0 := by
    intro h0
    exact h (by rw [h0]; simp)
  exact Complex.ofReal_mem_slitPlane.2 (lt_of_le_of_ne hnn hne.symm)

theorem normalize_quaternionMatrix_mem_specialUnitary
    {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M 1 1 = star (M 0 0) ∧ M 1 0 = -star (M 0 1))
    (h : M.det ≠ 0) :
    (M.det ^ (1 / 2 : ℂ))⁻¹ • M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hdet := det_quaternionMatrix hM
  obtain ⟨h1, h2⟩ := hM
  set D : ℝ := Complex.normSq (M 0 0) + Complex.normSq (M 0 1) with hD
  have hDp : 0 < D := by
    have hp : 0 ≤ D := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    refine lt_of_le_of_ne hp fun h0 => h ?_
    rw [hdet, ← h0]; simp
  have hr : M.det ^ (1 / 2 : ℂ) = ((Real.sqrt D : ℝ) : ℂ) := by
    rw [hdet, Real.sqrt_eq_rpow, Complex.ofReal_cpow hDp.le]
    simp
  have hs : Real.sqrt D ^ 2 = D := Real.sq_sqrt hDp.le
  have hs0 : (Real.sqrt D) ≠ 0 := (Real.sqrt_pos.2 hDp).ne'
  have hsc : ((Real.sqrt D : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hsq : ((Real.sqrt D : ℝ) : ℂ) * ((Real.sqrt D : ℝ) : ℂ) = (D : ℂ) := by
    rw [← Complex.ofReal_mul, ← pow_two, hs]
  rw [hr]
  have hMs : M * star M = (D : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, h1, h2, hD,
        Complex.normSq_eq_conj_mul_self] <;> ring
  refine Matrix.mem_specialUnitaryGroup_iff.2 ⟨Matrix.mem_unitaryGroup_iff.2 ?_, ?_⟩
  · rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, hMs, smul_smul, smul_smul]
    have hx : (((Real.sqrt D : ℝ) : ℂ))⁻¹ * (star (((Real.sqrt D : ℝ) : ℂ))⁻¹ * (D : ℂ)) = 1 := by
      rw [← hsq]
      simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
      field_simp
    rw [← mul_assoc] at hx
    rw [hx, one_smul]
  · rw [Matrix.det_smul, hdet]
    simp only [Fintype.card_fin]
    rw [inv_pow, pow_two, hsq]
    have : (D : ℂ) ≠ 0 := by exact_mod_cast hDp.ne'
    field_simp

abbrev specialLinear : Type := Matrix.SpecialLinearGroup (Fin 2) ℂ
def unitDeterminant : Set ComplexMatrix2 := {X | X.det = 1}
def hermitianTraceless : Submodule ℝ ComplexMatrix2 where
  carrier := {A | A = A.conjTranspose ∧ fullTrace A = 0}
  add_mem' := by
    rintro A B ⟨hA, tA⟩ ⟨hB, tB⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_add, ← hA, ← hB]
    · simp [fullTrace, Matrix.trace_add, tA, tB]
  zero_mem' := by simp [fullTrace]
  smul_mem' := by
    rintro c A ⟨hA, tA⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_smul, ← hA]; simp
    · simp only [fullTrace] at tA ⊢
      rw [Matrix.trace_smul, tA, smul_zero]
def realLieDimension : ℕ := Module.finrank ℝ hermitianTraceless
def traceless : Submodule ℂ ComplexMatrix2 where
  carrier := {A | fullTrace A = 0}
  add_mem' := by
    intro A B tA tB
    simp only [mem_ofPred_eq, fullTrace] at tA tB ⊢
    rw [Matrix.trace_add, tA, tB, add_zero]
  zero_mem' := by simp [fullTrace]
  smul_mem' := by
    intro c A tA
    simp only [mem_ofPred_eq, fullTrace] at tA ⊢
    rw [Matrix.trace_smul, tA, smul_zero]
def conjugateBy (V A : ComplexMatrix2) : ComplexMatrix2 := V * A * V⁻¹
abbrev matExp (Z : ComplexMatrix2) : ComplexMatrix2 := NormedSpace.exp Z
def expTimesUnitary (A' U : ComplexMatrix2) : ComplexMatrix2 := matExp (Complex.I • A') * U
def logBall : Set ComplexMatrix2 := {X | operatorNorm (X - 1) < 1}
def logSeries (X : ComplexMatrix2) : ComplexMatrix2 :=
  -∑' n : ℕ, ((n + 1 : ℂ)⁻¹) • (1 - X) ^ (n + 1)
def unitaryLogDomain : Set ComplexMatrix2 := (specialUnitary : Set ComplexMatrix2) \ {-1}
def unitaryLieLog (U : ComplexMatrix2) : ComplexMatrix2 :=
  Classical.epsilon fun Y : ComplexMatrix2 =>
    Y ∈ hermitianTraceless ∧ operatorNorm Y < Real.pi ∧ matExp (Complex.I • Y) = U
def unitaryLog (U : ComplexMatrix2) : ComplexMatrix2 := Complex.I • unitaryLieLog U
def bchRemainder (X Z : ComplexMatrix2) : ComplexMatrix2 := logSeries (matExp X * matExp Z) - X - Z
instance : ContinuousInv specialUnitary where
  continuous_inv := by
    have h : Continuous fun U : specialUnitary => star (U : ComplexMatrix2) :=
      (Continuous.matrix_conjTranspose continuous_subtype_val)
    exact h.subtype_mk fun U => (U⁻¹).2
instance : IsTopologicalGroup specialUnitary where
instance : CompactSpace specialUnitary := by
  have closed : IsClosed (specialUnitary : Set ComplexMatrix2) := by
    have h₁ : IsClosed {A : ComplexMatrix2 | A * star A = 1} :=
      isClosed_eq (continuous_id.mul (Continuous.matrix_conjTranspose continuous_id))
        continuous_const
    have h₂ : IsClosed {A : ComplexMatrix2 | A.det = 1} :=
      isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
    convert h₁.inter h₂ using 1
    ext A
    simp [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  have box : IsCompact (Set.pi univ fun _ : Fin 2 => Set.pi univ fun _ : Fin 2 =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have compact : IsCompact (specialUnitary : Set ComplexMatrix2) := by
    refine IsCompact.of_isClosed_subset box closed ?_
    intro A hA i _ j _
    have := entry_norm_bound_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup hA) i j
    simpa using this
  exact isCompact_iff_compactSpace.mp compact
instance : MeasurableSpace specialUnitary := borel specialUnitary
instance : BorelSpace specialUnitary := ⟨rfl⟩
def haarProb : Measure specialUnitary := Measure.haarMeasure ⊤
instance : IsProbabilityMeasure haarProb := ⟨Measure.haarMeasure_self⟩
def haarPi (ι : Type) [Countable ι] : Measure (ι → specialUnitary) :=
  Measure.infinitePi fun _ => haarProb
def LieElement : Type := hermitianTraceless
namespace LieElement
instance : AddCommGroup LieElement := inferInstanceAs (AddCommGroup hermitianTraceless)
instance : Module ℝ LieElement := inferInstanceAs (Module ℝ hermitianTraceless)
def toMatrix (Y : LieElement) : ComplexMatrix2 := Subtype.val (p := (· ∈ hermitianTraceless)) Y
end LieElement
namespace LieElement
theorem toMatrix_entry_swap (A : LieElement) (i j : Fin 2) :
    A.toMatrix j i = star (A.toMatrix i j) :=
  congrFun (congrFun A.2.1 j) i
theorem fullTrace_mul_self (A : LieElement) :
    fullTrace (A.toMatrix * A.toMatrix) = ((∑ i, ∑ j, ‖A.toMatrix i j‖ ^ 2 : ℝ) : ℂ) := by
  have h : ∀ i j, A.toMatrix i j * A.toMatrix j i = ((‖A.toMatrix i j‖ ^ 2 : ℝ) : ℂ) := by
    intro i j
    rw [toMatrix_entry_swap A i j, ← Complex.normSq_eq_norm_sq]
    exact Complex.mul_conj _
  simp only [fullTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply, h]
  push_cast
  rfl
theorem star_fullTrace_mul (A B : LieElement) :
    star (fullTrace (A.toMatrix * B.toMatrix)) = fullTrace (A.toMatrix * B.toMatrix) := by
  have h₁ : star (fullTrace (A.toMatrix * B.toMatrix)) =
      fullTrace (A.toMatrix * B.toMatrix).conjTranspose :=
    (Matrix.trace_conjTranspose _).symm
  have hA : A.toMatrix.conjTranspose = A.toMatrix := A.2.1.symm
  have hB : B.toMatrix.conjTranspose = B.toMatrix := B.2.1.symm
  rw [h₁, Matrix.conjTranspose_mul, hA, hB]
  exact Matrix.trace_mul_comm _ _
@[instance_reducible]
def innerProductCore : InnerProductSpace.Core ℝ LieElement where
  inner A B := (halfTrace (A.toMatrix * B.toMatrix)).re
  conj_inner_symm A B := by
    simp only [conj_trivial, halfTrace, fullTrace]
    rw [Matrix.trace_mul_comm]
  re_inner_nonneg A := by
    simp only [halfTrace, RCLike.re_to_real]
    rw [fullTrace_mul_self]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    norm_num
    positivity
  add_left A B C := by
    have : (A + B).toMatrix = A.toMatrix + B.toMatrix := rfl
    simp only [this, add_mul, halfTrace, fullTrace, Matrix.trace_add, mul_add, Complex.add_re]
  smul_left A B c := by
    have : (c • A).toMatrix = c • A.toMatrix := rfl
    simp only [this, Matrix.smul_mul, halfTrace, fullTrace, Matrix.trace_smul, conj_trivial]
    simp [Complex.mul_re]
    ring
  definite A h := by
    simp only [halfTrace] at h
    rw [fullTrace_mul_self] at h
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h
    norm_num at h
    have hz : ∑ i, ∑ j, ‖A.toMatrix i j‖ ^ 2 = 0 := by simpa using h
    have hall : ∀ i j, A.toMatrix i j = 0 := by
      intro i j
      have h₁ := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => by positivity)).mp hz i (Finset.mem_univ i)
      have h₂ := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h₁ j
        (Finset.mem_univ j)
      simpa using h₂
    apply Subtype.ext
    ext i j
    exact hall i j
instance : NormedAddCommGroup LieElement :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ LieElement _ _ _ innerProductCore
instance : InnerProductSpace ℝ LieElement := InnerProductSpace.ofCore innerProductCore.toCore
instance : FiniteDimensional ℝ LieElement :=
  inferInstanceAs (FiniteDimensional ℝ hermitianTraceless)
instance : MeasurableSpace LieElement := borel LieElement
instance : BorelSpace LieElement := ⟨rfl⟩
end LieElement
abbrev lieLebesgue : Measure LieElement := volume
def haarChartDensity : ℝ :=
  Filter.limUnder (𝓝[>] (0 : ℝ)) fun r =>
    (haarProb {U : specialUnitary | ∃ Y : LieElement, operatorNorm Y.toMatrix < r ∧
        (U : ComplexMatrix2) = matExp (Complex.I • Y.toMatrix)}).toReal /
      (lieLebesgue {Y : LieElement | operatorNorm Y.toMatrix < r}).toReal
def logGaussianIntegral : ℝ :=
  Real.log (∫ Y : LieElement, Real.exp (-(1 / 2) * operatorNorm Y.toMatrix ^ 2) ∂lieLebesgue)
inductive FactorKind : Type
  | group
  | algebra
def FactorKind.complexified : FactorKind → Set ComplexMatrix2
  | .group => unitDeterminant
  | .algebra => (traceless : Set ComplexMatrix2)
def FactorKind.compactReal : FactorKind → Set ComplexMatrix2
  | .group => (specialUnitary : Set ComplexMatrix2)
  | .algebra => (hermitianTraceless : Set ComplexMatrix2)
def complexifiedProduct {ι : Type} (s : ι → FactorKind) : Set (ι → ComplexMatrix2) :=
  {x | ∀ i, x i ∈ (s i).complexified}
def compactProduct {ι : Type} (s : ι → FactorKind) : Set (ι → ComplexMatrix2) :=
  {x | ∀ i, x i ∈ (s i).compactReal}
def IsRelativelyOpen {E : Type} [TopologicalSpace E] (P D : Set E) : Prop :=
  ∃ O : Set E, IsOpen O ∧ D = O ∩ P
def IsHolomorphicBetween {ι κ : Type} [Fintype ι] [Fintype κ] (s : ι → FactorKind)
    (t : κ → FactorKind) (D : Set (ι → ComplexMatrix2))
    (f : (ι → ComplexMatrix2) → κ → ComplexMatrix2) : Prop :=
  IsRelativelyOpen (complexifiedProduct s) D ∧ MapsTo f D (complexifiedProduct t) ∧
    ∀ x ∈ D, ∃ F : (ι → ComplexMatrix2) → κ → ComplexMatrix2,
      AnalyticAt ℂ F x ∧ ∀ᶠ y in 𝓝[D] x, f y = F y
def IsRealAnalyticBetween {ι κ : Type} [Fintype ι] [Fintype κ] (s : ι → FactorKind)
    (t : κ → FactorKind) (D : Set (ι → ComplexMatrix2))
    (f : (ι → ComplexMatrix2) → κ → ComplexMatrix2) : Prop :=
  IsRelativelyOpen (compactProduct s) D ∧
    ∀ x ∈ D, ∃ (W : Set (ι → ComplexMatrix2)) (h : (ι → ComplexMatrix2) → κ → ComplexMatrix2),
      x ∈ W ∧ IsHolomorphicBetween s t W h ∧ ∀ᶠ y in 𝓝[D] x, f y = h y
end ComplexMatrix2
end YangMills.Construction.Matrices
