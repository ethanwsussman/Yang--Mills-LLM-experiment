import YangMills.Construction.HilbertSpaces.JointSpectralMeasureOfAContractionAndAUnitaryProof
import YangMills.Construction.SpectralMeasures.IntegralsOfBoundedFunctionsAgainstAProjectionValuedMeasureProof
import YangMills.Construction.ComplexMeasures.UniquenessOfMeasuresAndTheIntegralOfAComplexMeasure
import YangMills.Construction.EuclideanAnalysis.GaussianCharactersDenseAndMeasureUnique
import YangMills.Construction.MeasureTheory.ComplexMeasureFacts
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open YangMills.Construction.BorelComplexMeasures (IsJordanCombination combinedIntegral
  IsIntegralOf conjMeasure densityMul)
open YangMills.Construction.SetFunctions (CountablyAdditiveFn IsCountablyAdditive MeasurableSets
  pushforward iUnionSets PairwiseDisjointSeq)
open scoped ComplexConjugate ENNReal Matrix NNReal
noncomputable section
namespace YangMills.Construction.MeasureUniqueness
section General
variable {X X' : Type} [MeasurableSpace X] [MeasurableSpace X']
def indicatorC (S : Set X) : X → ℂ := S.indicator fun _ => (1 : ℂ)
theorem isBoundedMeasurable_indicatorC {S : Set X} (hS : MeasurableSet S) :
    IsBoundedMeasurable (indicatorC S) := by
  refine ⟨measurable_const.indicator hS, 1, fun x => ?_⟩
  by_cases hx : x ∈ S <;> simp [indicatorC, hx]
theorem IsBoundedMeasurable.integrable {f : X → ℂ} (hf : IsBoundedMeasurable f)
    (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ := by apply _root_.YangMills.Construction.ContractionUnitary.JointSpectral.integrable_of_isBddMeasurable <;> assumption
theorem IsBoundedMeasurable.mul {f f' : X → ℂ} (hf : IsBoundedMeasurable f)
    (hf' : IsBoundedMeasurable f') : IsBoundedMeasurable fun x => f x * f' x := by
  obtain ⟨hm, C, hC⟩ := hf
  obtain ⟨hm', C', hC'⟩ := hf'
  refine ⟨hm.mul hm', C * C', fun x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC x) (hC' x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
theorem IsBoundedMeasurable.add {f f' : X → ℂ} (hf : IsBoundedMeasurable f)
    (hf' : IsBoundedMeasurable f') : IsBoundedMeasurable fun x => f x + f' x := by
  obtain ⟨hm, C, hC⟩ := hf
  obtain ⟨hm', C', hC'⟩ := hf'
  exact ⟨hm.add hm', C + C', fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hC' x))⟩
theorem IsBoundedMeasurable.const (z : ℂ) : IsBoundedMeasurable fun _ : X => z :=
  ⟨measurable_const, ‖z‖, fun _ => le_rfl⟩
theorem IsBoundedMeasurable.conj {f : X → ℂ} (hf : IsBoundedMeasurable f) :
    IsBoundedMeasurable fun x => conj (f x) := by apply _root_.YangMills.Construction.SpectralMeasures.BddCalculus.isBddMeasurable_conj <;> assumption
theorem IsBoundedMeasurable.comp {f : X' → ℂ} (hf : IsBoundedMeasurable f) {φ : X → X'}
    (hφ : Measurable φ) : IsBoundedMeasurable (f ∘ φ) := by
  obtain ⟨hm, C, hC⟩ := hf
  exact ⟨hm.comp hφ, C, fun x => hC _⟩
theorem integral_indicatorC (μ : Measure X) [IsFiniteMeasure μ] (A : MeasurableSets X) :
    ∫ x, indicatorC (A : Set X) x ∂μ = ((μ.real (A : Set X) : ℝ) : ℂ) := by
  rw [indicatorC, integral_indicator A.2, setIntegral_const]
  simp
theorem combinedIntegral_eq (μ₁ μ₂ μ₃ μ₄ : Measure X) (f : X → ℂ) :
    combinedIntegral μ₁ μ₂ μ₃ μ₄ f =
      (∫ x, f x ∂μ₁ - ∫ x, f x ∂μ₂) + Complex.I * (∫ x, f x ∂μ₃ - ∫ x, f x ∂μ₄) := by
  rw [combinedIntegral]
  ring
theorem combinedIntegral_indicatorC {ν : MeasurableSets X → ℂ} {μ₁ μ₂ μ₃ μ₄ : Measure X}
    (h : IsJordanCombination ν μ₁ μ₂ μ₃ μ₄) (A : MeasurableSets X) :
    combinedIntegral μ₁ μ₂ μ₃ μ₄ (indicatorC (A : Set X)) = ν A := by
  obtain ⟨_, _, _, _, h⟩ := h
  rw [h A, combinedIntegral_eq, integral_indicatorC, integral_indicatorC, integral_indicatorC,
    integral_indicatorC]
  push_cast
  ring
theorem isJordanCombination_of_indicatorC {ν : MeasurableSets X → ℂ} {μ₁ μ₂ μ₃ μ₄ : Measure X}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (h : ∀ A : MeasurableSets X, combinedIntegral μ₁ μ₂ μ₃ μ₄ (indicatorC (A : Set X)) = ν A) :
    IsJordanCombination ν μ₁ μ₂ μ₃ μ₄ := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun A => ?_⟩
  rw [← h A, combinedIntegral_eq, integral_indicatorC, integral_indicatorC, integral_indicatorC,
    integral_indicatorC]
  push_cast
  ring
theorem add_eq_add_of_measureReal_sub_eq {m₁ m₂ m₁' m₂' : Measure X} [IsFiniteMeasure m₁]
    [IsFiniteMeasure m₂] [IsFiniteMeasure m₁'] [IsFiniteMeasure m₂']
    (h : ∀ A : MeasurableSets X, m₁.real (A : Set X) - m₂.real (A : Set X) =
      m₁'.real (A : Set X) - m₂'.real (A : Set X)) : m₁ + m₂' = m₁' + m₂ := by
  refine Measure.ext fun s hs => ?_
  have e := h ⟨s, hs⟩
  simp only [Measure.real] at e
  rw [Measure.add_apply, Measure.add_apply,
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  linarith
theorem integral_sub_integral_eq {m₁ m₂ m₁' m₂' : Measure X} (h : m₁ + m₂' = m₁' + m₂)
    {f : X → ℂ} (h₁ : Integrable f m₁) (h₂ : Integrable f m₂) (h₁' : Integrable f m₁')
    (h₂' : Integrable f m₂') :
    ∫ x, f x ∂m₁ - ∫ x, f x ∂m₂ = ∫ x, f x ∂m₁' - ∫ x, f x ∂m₂' := by
  have e := congrArg (fun m => ∫ x, f x ∂m) h
  simp only [integral_add_measure h₁ h₂', integral_add_measure h₁' h₂] at e
  linear_combination e
theorem combinedIntegral_unique {ν : MeasurableSets X → ℂ}
    {μ₁ μ₂ μ₃ μ₄ μ₁' μ₂' μ₃' μ₄' : Measure X} {f : X → ℂ}
    (h : IsJordanCombination ν μ₁ μ₂ μ₃ μ₄)
    (h' : IsJordanCombination ν μ₁' μ₂' μ₃' μ₄')
    (i₁ : Integrable f μ₁) (i₂ : Integrable f μ₂) (i₃ : Integrable f μ₃) (i₄ : Integrable f μ₄)
    (i₁' : Integrable f μ₁') (i₂' : Integrable f μ₂') (i₃' : Integrable f μ₃')
    (i₄' : Integrable f μ₄') :
    combinedIntegral μ₁ μ₂ μ₃ μ₄ f = combinedIntegral μ₁' μ₂' μ₃' μ₄' f := by
  obtain ⟨_, _, _, _, h⟩ := h
  obtain ⟨_, _, _, _, h'⟩ := h'
  have e₁ : μ₁ + μ₂' = μ₁' + μ₂ := add_eq_add_of_measureReal_sub_eq fun A => by
    simpa using congrArg Complex.re ((h A).symm.trans (h' A))
  have e₂ : μ₃ + μ₄' = μ₃' + μ₄ := add_eq_add_of_measureReal_sub_eq fun A => by
    simpa using congrArg Complex.im ((h A).symm.trans (h' A))
  rw [combinedIntegral_eq, combinedIntegral_eq, integral_sub_integral_eq e₁ i₁ i₂ i₁' i₂',
    integral_sub_integral_eq e₂ i₃ i₄ i₃' i₄']
theorem integralOf_eq_of_isIntegralOf {ν : MeasurableSets X → ℂ} {f : X → ℂ} {z : ℂ}
    (h : IsIntegralOf ν f z) : BorelComplexMeasures.integralOf ν f = z := by
  have e : IsIntegralOf ν f (BorelComplexMeasures.integralOf ν f) :=
    Classical.epsilon_spec (p := IsIntegralOf ν f) ⟨z, h⟩
  obtain ⟨μ₁, μ₂, μ₃, μ₄, hc, _, i₁, i₂, i₃, i₄, rfl⟩ := h
  obtain ⟨μ₁', μ₂', μ₃', μ₄', hc', _, i₁', i₂', i₃', i₄', e'⟩ := e
  rw [e']
  exact combinedIntegral_unique hc' hc i₁' i₂' i₃' i₄' i₁ i₂ i₃ i₄
def RepresentedBy (ν : MeasurableSets X → ℂ) (L : (X → ℂ) → ℂ) : Prop :=
  ∃ μ₁ μ₂ μ₃ μ₄ : Measure X, IsJordanCombination ν μ₁ μ₂ μ₃ μ₄ ∧
    ∀ f, IsBoundedMeasurable f → combinedIntegral μ₁ μ₂ μ₃ μ₄ f = L f
theorem representedBy_of (μ₁ μ₂ μ₃ μ₄ : Measure X) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄] {ν : MeasurableSets X → ℂ} {L : (X → ℂ) → ℂ}
    (hL : ∀ f, IsBoundedMeasurable f → combinedIntegral μ₁ μ₂ μ₃ μ₄ f = L f)
    (hν : ∀ A : MeasurableSets X, L (indicatorC (A : Set X)) = ν A) : RepresentedBy ν L :=
  ⟨μ₁, μ₂, μ₃, μ₄, isJordanCombination_of_indicatorC fun A => by
    rw [hL _ (isBoundedMeasurable_indicatorC A.2), hν], hL⟩
namespace RepresentedBy
variable {ν ν' : MeasurableSets X → ℂ} {L M : (X → ℂ) → ℂ}
theorem indicatorC_eq (R : RepresentedBy ν L) (A : MeasurableSets X) :
    L (indicatorC (A : Set X)) = ν A := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h, hL⟩ := R
  rw [← hL _ (isBoundedMeasurable_indicatorC A.2), combinedIntegral_indicatorC h]
theorem integralOf_eq (R : RepresentedBy ν L) {f : X → ℂ} (hf : IsBoundedMeasurable f) :
    BorelComplexMeasures.integralOf ν f = L f := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h, hL⟩ := R
  obtain ⟨_, _, _, _, _⟩ := id h
  exact integralOf_eq_of_isIntegralOf ⟨μ₁, μ₂, μ₃, μ₄, h, hf.1, hf.integrable μ₁,
    hf.integrable μ₂, hf.integrable μ₃, hf.integrable μ₄, (hL f hf).symm⟩
theorem linear (R : RepresentedBy ν L) {f f' : X → ℂ} (hf : IsBoundedMeasurable f)
    (hf' : IsBoundedMeasurable f') (p q : ℂ) :
    L (fun x => p * f x + q * f' x) = p * L f + q * L f' := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h, hL⟩ := R
  obtain ⟨_, _, _, _, _⟩ := id h
  have hpf := ((IsBoundedMeasurable.const p).mul hf)
  have hqf := ((IsBoundedMeasurable.const q).mul hf')
  rw [← hL _ (hpf.add hqf), ← hL _ hf, ← hL _ hf']
  have key : ∀ (μ : Measure X) [IsFiniteMeasure μ],
      ∫ x, (p * f x + q * f' x) ∂μ = p * ∫ x, f x ∂μ + q * ∫ x, f' x ∂μ := fun μ _ => by
    rw [integral_add (hpf.integrable μ) (hqf.integrable μ), integral_const_mul,
      integral_const_mul]
  simp only [combinedIntegral, key]
  ring
theorem congrOn (R : RepresentedBy ν L) (hν : ∀ A, ν A = ν' A)
    (hL : ∀ f, IsBoundedMeasurable f → L f = M f) : RepresentedBy ν' M := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h, hL'⟩ := R
  obtain ⟨_, _, _, _, h'⟩ := id h
  exact ⟨μ₁, μ₂, μ₃, μ₄, ⟨‹_›, ‹_›, ‹_›, ‹_›, fun A => by rw [← hν A, h' A]⟩,
    fun f hf => by rw [hL' f hf, hL f hf]⟩
theorem add (R : RepresentedBy ν L) (S : RepresentedBy ν' M) :
    RepresentedBy (fun A => ν A + ν' A) (fun f => L f + M f) := by
  have iR := R.indicatorC_eq
  have iS := S.indicatorC_eq
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h, hL⟩ := R
  obtain ⟨μ₁', μ₂', μ₃', μ₄', h', hM⟩ := S
  obtain ⟨_, _, _, _, _⟩ := id h
  obtain ⟨_, _, _, _, _⟩ := id h'
  refine representedBy_of (μ₁ + μ₁') (μ₂ + μ₂') (μ₃ + μ₃') (μ₄ + μ₄') (fun f hf => ?_)
    (fun A => by rw [iR, iS])
  rw [← hL f hf, ← hM f hf]
  simp only [combinedIntegral]
  rw [integral_add_measure (hf.integrable μ₁) (hf.integrable μ₁'),
    integral_add_measure (hf.integrable μ₂) (hf.integrable μ₂'),
    integral_add_measure (hf.integrable μ₃) (hf.integrable μ₃'),
    integral_add_measure (hf.integrable μ₄) (hf.integrable μ₄')]
  ring
theorem smul (R : RepresentedBy ν L) (t : ℝ≥0) :
    RepresentedBy (fun A => (t : ℂ) * ν A) (fun f => (t : ℂ) * L f) := by
  have iR := R.indicatorC_eq
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h, hL⟩ := R
  obtain ⟨_, _, _, _, _⟩ := id h
  refine representedBy_of (t • μ₁) (t • μ₂) (t • μ₃) (t • μ₄) (fun f hf => ?_)
    (fun A => by rw [iR])
  rw [← hL f hf]
  simp only [combinedIntegral, integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul]
  ring
theorem neg (R : RepresentedBy ν L) : RepresentedBy (fun A => -ν A) (fun f => -L f) := by
  have iR := R.indicatorC_eq
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h, hL⟩ := R
  obtain ⟨_, _, _, _, _⟩ := id h
  refine representedBy_of μ₂ μ₁ μ₄ μ₃ (fun f hf => ?_) (fun A => by rw [iR])
  rw [← hL f hf]
  simp only [combinedIntegral]
  ring
theorem mulI (R : RepresentedBy ν L) :
    RepresentedBy (fun A => Complex.I * ν A) (fun f => Complex.I * L f) := by
  have iR := R.indicatorC_eq
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h, hL⟩ := R
  obtain ⟨_, _, _, _, _⟩ := id h
  refine representedBy_of μ₄ μ₃ μ₁ μ₂ (fun f hf => ?_) (fun A => by rw [iR])
  rw [← hL f hf]
  simp only [combinedIntegral]
  linear_combination (-(∫ x, f x ∂μ₃) + ∫ x, f x ∂μ₄) * Complex.I_mul_I
theorem realMul (R : RepresentedBy ν L) (t : ℝ) :
    RepresentedBy (fun A => (t : ℂ) * ν A) (fun f => (t : ℂ) * L f) := by
  rcases le_total 0 t with ht | ht
  · simpa [Real.coe_toNNReal t ht] using R.smul t.toNNReal
  · have e := (R.neg).smul (-t).toNNReal
    have ht' : 0 ≤ -t := by linarith
    refine e.congrOn (fun A => ?_) (fun f _ => ?_) <;>
      simp [Real.coe_toNNReal (-t) ht']
theorem cmul (R : RepresentedBy ν L) (z : ℂ) :
    RepresentedBy (fun A => z * ν A) (fun f => z * L f) := by
  refine ((R.realMul z.re).add (R.mulI.realMul z.im)).congrOn (fun A => ?_) (fun f _ => ?_)
  · conv_rhs => rw [← Complex.re_add_im z]
    ring
  · conv_rhs => rw [← Complex.re_add_im z]
    ring
theorem conjugate (R : RepresentedBy ν L) :
    RepresentedBy (conjMeasure ν) (fun f => conj (L fun x => conj (f x))) := by
  have iR := R.indicatorC_eq
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h, hL⟩ := R
  obtain ⟨_, _, _, _, _⟩ := id h
  have key : ∀ f, IsBoundedMeasurable f →
      combinedIntegral μ₁ μ₂ μ₄ μ₃ f = (starRingEnd ℂ) (L fun x => (starRingEnd ℂ) (f x)) := by
    intro f hf
    rw [← hL _ hf.conj]
    simp only [combinedIntegral, integral_conj, map_sub, map_add, map_mul,
      Complex.conj_I, Complex.conj_conj]
    ring
  refine representedBy_of μ₁ μ₂ μ₄ μ₃ key (fun A => ?_)
  have e : (fun x => (starRingEnd ℂ) (indicatorC (A : Set X) x)) = indicatorC (A : Set X) := by
    funext x
    by_cases hx : x ∈ (A : Set X) <;> simp [indicatorC, hx]
  rw [e, iR]
  rfl
theorem mapAlong (R : RepresentedBy ν L) {φ : X → X'} (hφ : Measurable φ) :
    RepresentedBy (SetFunctions.pushforward φ hφ ν) (fun f => L (f ∘ φ)) := by
  have iR := R.indicatorC_eq
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h, hL⟩ := R
  obtain ⟨_, _, _, _, _⟩ := id h
  have key : ∀ (μ : Measure X) (f : X' → ℂ), IsBoundedMeasurable f →
      ∫ x, f x ∂(μ.map φ) = ∫ x, (f ∘ φ) x ∂μ := fun μ f hf =>
    integral_map hφ.aemeasurable hf.1.aestronglyMeasurable
  refine representedBy_of (μ₁.map φ) (μ₂.map φ) (μ₃.map φ) (μ₄.map φ) (fun f hf => ?_)
    (fun A => ?_)
  · rw [← hL _ (hf.comp hφ)]
    simp only [combinedIntegral, key _ f hf]
  · have e : indicatorC (A : Set X') ∘ φ = indicatorC (φ ⁻¹' (A : Set X')) := by
      funext x
      by_cases hx : φ x ∈ (A : Set X') <;> simp [indicatorC, hx]
    rw [e]
    exact iR ⟨φ ⁻¹' (A : Set X'), hφ A.2⟩
theorem nnDensity (R : RepresentedBy ν L) {u : X → ℝ≥0} (hu : Measurable u) (C : ℝ≥0)
    (hC : ∀ x, u x ≤ C) :
    RepresentedBy (fun A => L fun x => indicatorC (A : Set X) x * ((u x : ℝ) : ℂ))
      (fun f => L fun x => f x * ((u x : ℝ) : ℂ)) := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h, hL⟩ := R
  obtain ⟨_, _, _, _, _⟩ := id h
  have hub : IsBoundedMeasurable fun x => ((u x : ℝ) : ℂ) :=
    ⟨Complex.measurable_ofReal.comp (measurable_coe_nnreal_real.comp hu), C, fun x => by
      simpa using hC x⟩
  have fin : ∀ (μ : Measure X) [IsFiniteMeasure μ],
      IsFiniteMeasure (μ.withDensity fun x => (u x : ℝ≥0∞)) := fun μ _ => by
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ x, (u x : ℝ≥0∞) ∂μ ≤ ∫⁻ _, (C : ℝ≥0∞) ∂μ :=
          lintegral_mono fun x => ENNReal.coe_le_coe.2 (hC x)
      _ < ∞ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ _)
  have key : ∀ (μ : Measure X) (f : X → ℂ),
      ∫ x, f x ∂(μ.withDensity fun x => (u x : ℝ≥0∞)) = ∫ x, f x * ((u x : ℝ) : ℂ) ∂μ := by
    intro μ f
    rw [integral_withDensity_eq_integral_smul hu]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [NNReal.smul_def, mul_comm]
  have := fin μ₁
  have := fin μ₂
  have := fin μ₃
  have := fin μ₄
  refine representedBy_of (μ₁.withDensity fun x => (u x : ℝ≥0∞))
    (μ₂.withDensity fun x => (u x : ℝ≥0∞)) (μ₃.withDensity fun x => (u x : ℝ≥0∞))
    (μ₄.withDensity fun x => (u x : ℝ≥0∞)) (fun f hf => ?_) (fun A => rfl)
  rw [← hL _ (hf.mul hub)]
  simp only [combinedIntegral, key]
theorem isCountablyAdditive (R : RepresentedBy ν L) : IsCountablyAdditive ν := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, ⟨_, _, _, _, h⟩, -⟩ := R
  intro A hA
  have key : ∀ (μ : Measure X) [IsFiniteMeasure μ],
      Tendsto (fun N => ∑ j ∈ Finset.range N, ((μ.real (A j : Set X) : ℝ) : ℂ)) atTop
        (𝓝 ((μ.real (iUnionSets A : Set X) : ℝ) : ℂ)) := by
    intro μ _
    have hd : Pairwise (Function.onFun Disjoint fun j => (A j : Set X)) := hA
    have hU : μ (⋃ j, (A j : Set X)) = ∑' j, μ (A j : Set X) :=
      measure_iUnion hd fun j => (A j).2
    have hne : ∑' j, μ (A j : Set X) ≠ ∞ := by
      rw [← hU]
      finiteness
    have e := ENNReal.hasSum_toReal hne
    rw [← ENNReal.tsum_toReal_eq (fun j => by finiteness), ← hU] at e
    have e' := (Complex.continuous_ofReal.tendsto _).comp e.tendsto_sum_nat
    refine e'.congr fun N => ?_
    simp [Function.comp_def, Measure.real]
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, Complex.ofReal_sub,
    Finset.sum_sub_distrib]
  exact ((key μ₁).sub (key μ₂)).add (((key μ₃).sub (key μ₄)).const_mul Complex.I)
theorem mulBounded (R : RepresentedBy ν L) {g : X → ℂ} (hg : IsBoundedMeasurable g) :
    RepresentedBy (fun A => L fun x => indicatorC (A : Set X) x * g x)
      (fun f => L fun x => f x * g x) := by
  obtain ⟨hgm, C, hC⟩ := id hg
  have hre : ∀ x, |(g x).re| ≤ C := fun x => (Complex.abs_re_le_norm _).trans (hC x)
  have him : ∀ x, |(g x).im| ≤ C := fun x => (Complex.abs_im_le_norm _).trans (hC x)
  have part : ∀ t : X → ℝ, Measurable t → (∀ x, |t x| ≤ C) →
      Measurable (fun x => (t x).toNNReal) ∧ ∀ x, (t x).toNNReal ≤ C.toNNReal := fun t ht hb =>
    ⟨measurable_real_toNNReal.comp ht, fun x =>
      Real.toNNReal_le_toNNReal ((le_abs_self _).trans (hb x))⟩
  have m₁ := part (fun x => (g x).re) (Complex.measurable_re.comp hgm) hre
  have m₂ := part (fun x => -(g x).re) (Complex.measurable_re.comp hgm).neg
    (fun x => by simpa using hre x)
  have m₃ := part (fun x => (g x).im) (Complex.measurable_im.comp hgm) him
  have m₄ := part (fun x => -(g x).im) (Complex.measurable_im.comp hgm).neg
    (fun x => by simpa using him x)
  have cast : ∀ u : X → ℝ≥0, (Measurable u ∧ ∀ x, u x ≤ C.toNNReal) →
      IsBoundedMeasurable fun x => ((u x : ℝ) : ℂ) := fun u hu =>
    ⟨Complex.measurable_ofReal.comp (measurable_coe_nnreal_real.comp hu.1), C.toNNReal,
      fun x => by
        rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
        exact_mod_cast hu.2 x⟩
  have split : ∀ f : X → ℂ, IsBoundedMeasurable f → L (fun x => f x * g x) =
      (L (fun x => f x * (((g x).re.toNNReal : ℝ) : ℂ)) +
        -L (fun x => f x * (((-(g x).re).toNNReal : ℝ) : ℂ))) +
      Complex.I * (L (fun x => f x * (((g x).im.toNNReal : ℝ) : ℂ)) +
        -L (fun x => f x * (((-(g x).im).toNNReal : ℝ) : ℂ))) := by
    intro f hf
    have b₁ := hf.mul (cast _ m₁)
    have b₂ := hf.mul (cast _ m₂)
    have b₃ := hf.mul (cast _ m₃)
    have b₄ := hf.mul (cast _ m₄)
    have eA := R.linear b₁ b₂ 1 (-1)
    have eB := R.linear b₃ b₄ 1 (-1)
    have bA := ((IsBoundedMeasurable.const (1 : ℂ)).mul b₁).add
      ((IsBoundedMeasurable.const (-1 : ℂ)).mul b₂)
    have bB := ((IsBoundedMeasurable.const (1 : ℂ)).mul b₃).add
      ((IsBoundedMeasurable.const (-1 : ℂ)).mul b₄)
    have eC := R.linear bA bB 1 Complex.I
    have pt : (fun x => f x * g x) = fun x =>
        1 * (1 * (f x * (((g x).re.toNNReal : ℝ) : ℂ)) +
          -1 * (f x * (((-(g x).re).toNNReal : ℝ) : ℂ))) +
        Complex.I * (1 * (f x * (((g x).im.toNNReal : ℝ) : ℂ)) +
          -1 * (f x * (((-(g x).im).toNNReal : ℝ) : ℂ))) := by
      funext x
      have r₁ : (((g x).re.toNNReal : ℝ) : ℂ) - (((-(g x).re).toNNReal : ℝ) : ℂ) =
          ((g x).re : ℂ) := by
        rw [← Complex.ofReal_sub, Real.coe_toNNReal', Real.coe_toNNReal',
          max_zero_sub_eq_self]
      have r₂ : (((g x).im.toNNReal : ℝ) : ℂ) - (((-(g x).im).toNNReal : ℝ) : ℂ) =
          ((g x).im : ℂ) := by
        rw [← Complex.ofReal_sub, Real.coe_toNNReal', Real.coe_toNNReal',
          max_zero_sub_eq_self]
      have r₃ : g x = ((g x).re : ℂ) + ((g x).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
      rw [← r₁, ← r₂] at r₃
      conv_lhs => rw [r₃]
      ring
    rw [pt, eC, eA, eB]
    ring
  have D₁ := R.nnDensity m₁.1 C.toNNReal m₁.2
  have D₂ := R.nnDensity m₂.1 C.toNNReal m₂.2
  have D₃ := R.nnDensity m₃.1 C.toNNReal m₃.2
  have D₄ := R.nnDensity m₄.1 C.toNNReal m₄.2
  exact ((D₁.add D₂.neg).add (D₃.add D₄.neg).mulI).congrOn
    (fun A => (split _ (isBoundedMeasurable_indicatorC A.2)).symm)
    (fun f hf => (split f hf).symm)
end RepresentedBy
theorem exists_jordan_parts (hF : SetFunctions.ComplexMeasureFacts) {μ : MeasurableSets X → ℂ}
    (hμ : IsCountablyAdditive μ) (him : ∀ A, (μ A).im = 0) :
    ∃ p n : Measure X, IsFiniteMeasure p ∧ IsFiniteMeasure n ∧
      ∀ A : MeasurableSets X, (μ A).re = p.real (A : Set X) - n.real (A : Set X) := by
  obtain ⟨-, h₂, -⟩ := hF X
  obtain ⟨p₁, p₂, -, -, e⟩ := h₂ μ hμ him
  have v : ∀ m : MeasurableSets X → ℂ, SetFunctions.IsFiniteNonnegMeasure m →
      ∀ A : MeasurableSets X,
        (SetFunctions.nonnegToMeasure m).real (A : Set X) = (m A).re := by
    intro m hm A
    have e₁ := hm.2.2.2 A
    have e₂ : (SetFunctions.nonnegToMeasure m) (A : Set X) =
        ENNReal.ofReal (m A).re := e₁
    rw [Measure.real, e₂, ENNReal.toReal_ofReal (hm.2.1 A).2]
  refine ⟨SetFunctions.nonnegToMeasure (SetFunctions.posPart μ),
    SetFunctions.nonnegToMeasure (SetFunctions.negPart μ), p₁.2.2.1, p₂.2.2.1,
    fun A => ?_⟩
  rw [v _ p₁, v _ p₂, e A, Complex.sub_re]
theorem representedBy_integralOf (hF : SetFunctions.ComplexMeasureFacts)
    {ν : MeasurableSets X → ℂ} (hν : IsCountablyAdditive ν) :
    RepresentedBy ν (BorelComplexMeasures.integralOf ν) := by
  obtain ⟨h₁, -⟩ := hF X
  obtain ⟨-, -, hre, him, -⟩ := h₁ ν hν
  obtain ⟨μ₁, μ₂, f₁, f₂, e⟩ := exists_jordan_parts hF hre
    (fun A => by simp [SetFunctions.reFn])
  obtain ⟨μ₃, μ₄, f₃, f₄, e'⟩ := exists_jordan_parts hF him
    (fun A => by simp [SetFunctions.imFn])
  have comb : IsJordanCombination ν μ₁ μ₂ μ₃ μ₄ := by
    refine ⟨f₁, f₂, f₃, f₄, fun A => ?_⟩
    have x := e A
    have y := e' A
    simp only [SetFunctions.reFn, SetFunctions.imFn, Complex.ofReal_re] at x y
    apply Complex.ext <;> simp [x, y]
  exact ⟨μ₁, μ₂, μ₃, μ₄, comb, fun f hf => (integralOf_eq_of_isIntegralOf
    ⟨μ₁, μ₂, μ₃, μ₄, comb, hf.1, hf.integrable μ₁, hf.integrable μ₂, hf.integrable μ₃,
      hf.integrable μ₄, rfl⟩).symm⟩
theorem representedBy_densityMul {ν : MeasurableSets X → ℂ}
    (R : RepresentedBy ν (BorelComplexMeasures.integralOf ν)) {g : X → ℂ}
    (hg : IsBoundedMeasurable g) :
    RepresentedBy (densityMul g ν)
      (fun f => BorelComplexMeasures.integralOf ν fun x => f x * g x) :=
  R.mulBounded hg
theorem eq_zero_of_isPiSystem {ν : MeasurableSets X → ℂ} {L : (X → ℂ) → ℂ}
    (R : RepresentedBy ν L) {C : Set (Set X)} (hC : IsPiSystem C)
    (hgen : ‹MeasurableSpace X› = .generateFrom C)
    (hu : Set.univ ∈ C) (hz : ∀ A : MeasurableSets X, (A : Set X) ∈ C → ν A = 0) :
    ∀ A, ν A = 0 := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, ⟨f₁, f₂, f₃, f₄, h⟩, -⟩ := R
  have meas : ∀ s ∈ C, MeasurableSet s := fun s hs => by
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hs
  have eq : ∀ m m' : Measure X, IsFiniteMeasure m → IsFiniteMeasure m' →
      (∀ s ∈ C, m.real s = m'.real s) → m = m' := by
    intro m m' _ _ e
    refine ext_of_generate_finite C hgen hC (fun s hs => ?_) ?_
    · exact (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).1 (e s hs)
    · exact (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).1 (e _ hu)
  have e₁ : μ₁ = μ₂ := eq μ₁ μ₂ f₁ f₂ fun s hs => by
    have e := congrArg Complex.re ((h ⟨s, meas s hs⟩).symm.trans (hz ⟨s, meas s hs⟩ hs))
    simp at e
    linarith
  have e₂ : μ₃ = μ₄ := eq μ₃ μ₄ f₃ f₄ fun s hs => by
    have e := congrArg Complex.im ((h ⟨s, meas s hs⟩).symm.trans (hz ⟨s, meas s hs⟩ hs))
    simp at e
    linarith
  intro A
  rw [h A, e₁, e₂]
  simp
theorem eq_zero_of_pushforward {ν : MeasurableSets X → ℂ} {φ : X → X'} (hφ : Measurable φ)
    {ψ : X' → X} (hψ : Measurable ψ) (h : ∀ x, ψ (φ x) = x)
    (hz : ∀ A, pushforward φ hφ ν A = 0) : ∀ A, ν A = 0 := by
  intro A
  have e : A = ⟨φ ⁻¹' (ψ ⁻¹' (A : Set X)), hφ (hψ A.2)⟩ :=
    Subtype.ext (by ext x; simp [h])
  rw [e]
  exact hz ⟨ψ ⁻¹' (A : Set X), hψ A.2⟩
end General
section Characters
def halfPlaneExp (k : ℕ) (s : ℝ) (x : Set.Ici (0 : ℝ) × ℝ) : ℂ :=
  Complex.exp (-(k : ℂ) * (x.1 : ℝ) + Complex.I * s * x.2)
theorem isBoundedMeasurable_halfPlaneExp (k : ℕ) (s : ℝ) :
    IsBoundedMeasurable (halfPlaneExp k s) := by
  refine ⟨Continuous.measurable ?_, 1, fun x => ?_⟩
  · unfold halfPlaneExp
    fun_prop
  · have hE : (0 : ℝ) ≤ (x.1 : ℝ) := x.1.2
    rw [halfPlaneExp, Complex.norm_exp, Real.exp_le_one_iff]
    simp
    positivity
theorem isBoundedMeasurable_expLaplaceFourier {r : ℕ} (k : ℕ) (v : Fin r → ℝ) :
    IsBoundedMeasurable (expLaplaceFourier k v) := by
  refine ⟨Continuous.measurable ?_, 1, fun x => ?_⟩
  · have hd : Continuous fun p : Set.Ici (0 : ℝ) × (Fin r → ℝ) => v ⬝ᵥ p.2 := by
      simp only [dotProduct]
      fun_prop
    unfold expLaplaceFourier
    fun_prop
  · have hE : (0 : ℝ) ≤ (x.1 : ℝ) := x.1.2
    rw [expLaplaceFourier, Complex.norm_exp, Real.exp_le_one_iff]
    simp
    positivity
def firstCoordMap {r : ℕ} (p : Set.Ici (0 : ℝ) × (Fin (r + 1) → ℝ)) : Set.Ici (0 : ℝ) × ℝ :=
  (p.1, p.2 0)
def restCoordMap {r : ℕ} (p : Set.Ici (0 : ℝ) × (Fin (r + 1) → ℝ)) :
    Set.Ici (0 : ℝ) × (Fin r → ℝ) :=
  (⟨0, Set.self_mem_Ici⟩, fun i => p.2 i.succ)
theorem measurable_firstCoordMap {r : ℕ} : Measurable (firstCoordMap (r := r)) :=
  measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)
theorem measurable_restCoordMap {r : ℕ} : Measurable (restCoordMap (r := r)) :=
  measurable_const.prodMk (measurable_pi_lambda _ fun i =>
    (measurable_pi_apply i.succ).comp measurable_snd)
theorem expLaplaceFourier_restCoordMap {r : ℕ} (k : ℕ) (v : Fin r → ℝ)
    (p : Set.Ici (0 : ℝ) × (Fin (r + 1) → ℝ)) :
    expLaplaceFourier k v (restCoordMap p) = expLaplaceFourier 0 v (restCoordMap p) := by
  simp [expLaplaceFourier, restCoordMap]
theorem halfPlaneExp_mul {r : ℕ} (k : ℕ) (s : ℝ) (v : Fin r → ℝ)
    (p : Set.Ici (0 : ℝ) × (Fin (r + 1) → ℝ)) :
    halfPlaneExp k s (firstCoordMap p) * expLaplaceFourier 0 v (restCoordMap p) =
      expLaplaceFourier k (Matrix.vecCons s v) p := by
  simp only [halfPlaneExp, expLaplaceFourier, firstCoordMap, restCoordMap, ← Complex.exp_add]
  congr 1
  rw [Matrix.cons_dotProduct]
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_def]
  push_cast
  ring
theorem eq_zero_of_halfPlane (hF : SetFunctions.ComplexMeasureFacts)
    (hD : EuclideanAnalysis.Strip.ModulatedDenseAndMeasureUnique)
    (ν : CountablyAdditiveFn (Set.Ici (0 : ℝ) × ℝ))
    (h : ∀ (k : ℕ) (s : ℝ), BorelComplexMeasures.integralOf ν.1 (halfPlaneExp k s) = 0) :
    ∀ A, ν.1 A = 0 := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, hc, hL⟩ := representedBy_integralOf hF ν.2
  obtain ⟨f₁, f₂, f₃, f₄, hv⟩ := id hc
  have hz : ∀ (k : ℕ) (s : ℝ), combinedIntegral μ₁ μ₂ μ₃ μ₄ (halfPlaneExp k s) = 0 :=
    fun k s => (hL _ (isBoundedMeasurable_halfPlaneExp k s)).trans (h k s)
  have cj : ∀ (m : Measure (Set.Ici (0 : ℝ) × ℝ)) (k : ℕ) (s : ℝ),
      (starRingEnd ℂ) (∫ x, halfPlaneExp k (-s) x ∂m) = ∫ x, halfPlaneExp k s x ∂m := by
    intro m k s
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [halfPlaneExp, ← Complex.exp_conj, map_add, map_mul, map_neg, Complex.conj_I,
      Complex.conj_ofReal, Complex.conj_natCast]
    congr 1
    push_cast
    ring
  have E₁ : ∀ (k : ℕ) (s : ℝ), ∫ x, halfPlaneExp k s x ∂μ₁ = ∫ x, halfPlaneExp k s x ∂μ₂ := by
    intro k s
    have e₁ := hz k s
    have e₂ := congrArg (starRingEnd ℂ) (hz k (-s))
    simp only [combinedIntegral, map_sub, map_add, map_mul, Complex.conj_I, cj,
      map_zero] at e₁ e₂
    linear_combination (1 / 2) * (e₁ + e₂)
  have E₂ : ∀ (k : ℕ) (s : ℝ), ∫ x, halfPlaneExp k s x ∂μ₃ = ∫ x, halfPlaneExp k s x ∂μ₄ := by
    intro k s
    have e₁ := hz k s
    have e₂ := congrArg (starRingEnd ℂ) (hz k (-s))
    simp only [combinedIntegral, map_sub, map_add, map_mul, Complex.conj_I, cj,
      map_zero] at e₁ e₂
    linear_combination (-Complex.I / 2) * (e₁ - e₂) +
      (∫ x, halfPlaneExp k s x ∂μ₃ - ∫ x, halfPlaneExp k s x ∂μ₄) * Complex.I_mul_I
  have h₁₂ : μ₁ = μ₂ := hD.2.2 μ₁ μ₂ f₁ f₂ E₁
  have h₃₄ : μ₃ = μ₄ := hD.2.2 μ₃ μ₄ f₃ f₄ E₂
  intro A
  rw [hv A, h₁₂, h₃₄]
  simp
def splitMap {r : ℕ} (p : Set.Ici (0 : ℝ) × (Fin (r + 1) → ℝ)) :
    (Set.Ici (0 : ℝ) × ℝ) × (Fin r → ℝ) :=
  (firstCoordMap p, fun i => p.2 i.succ)
def joinMap {r : ℕ} (y : (Set.Ici (0 : ℝ) × ℝ) × (Fin r → ℝ)) :
    Set.Ici (0 : ℝ) × (Fin (r + 1) → ℝ) :=
  (y.1.1, Fin.cons y.1.2 y.2)
theorem measurable_splitMap {r : ℕ} : Measurable (splitMap (r := r)) :=
  measurable_firstCoordMap.prodMk (measurable_pi_lambda _ fun i =>
    (measurable_pi_apply i.succ).comp measurable_snd)
theorem measurable_joinMap {r : ℕ} : Measurable (joinMap (r := r)) := by
  refine (measurable_fst.comp measurable_fst).prodMk (measurable_pi_lambda _ fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [Function.comp_def, joinMap] using measurable_snd.comp measurable_fst
  · simpa [Function.comp_def, joinMap] using (measurable_pi_apply j).comp measurable_snd
theorem joinMap_splitMap {r : ℕ} (p : Set.Ici (0 : ℝ) × (Fin (r + 1) → ℝ)) :
    joinMap (splitMap p) = p := by
  refine Prod.ext rfl (funext fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [joinMap, splitMap, firstCoordMap]
theorem eq_zero_succ (hF : SetFunctions.ComplexMeasureFacts) {r : ℕ}
    (h₁ : ∀ ν : CountablyAdditiveFn (Set.Ici (0 : ℝ) × ℝ),
      (∀ (k : ℕ) (s : ℝ), BorelComplexMeasures.integralOf ν.1 (halfPlaneExp k s) = 0) →
      ∀ A, ν.1 A = 0)
    (IH : ∀ ν : CountablyAdditiveFn (Set.Ici (0 : ℝ) × (Fin r → ℝ)),
      (∀ (k : ℕ) (v : Fin r → ℝ),
        BorelComplexMeasures.integralOf ν.1 (expLaplaceFourier k v) = 0) →
      ∀ A, ν.1 A = 0)
    (ν : CountablyAdditiveFn (Set.Ici (0 : ℝ) × (Fin (r + 1) → ℝ)))
    (h : ∀ (k : ℕ) (v : Fin (r + 1) → ℝ),
      BorelComplexMeasures.integralOf ν.1 (expLaplaceFourier k v) = 0) :
    ∀ A, ν.1 A = 0 := by
  have R := representedBy_integralOf hF ν.2
  have step₁ : ∀ (v : Fin r → ℝ) (A : MeasurableSets (Set.Ici (0 : ℝ) × ℝ)),
      BorelComplexMeasures.integralOf ν.1 (fun p =>
        indicatorC (firstCoordMap ⁻¹' (A : Set _)) p *
          expLaplaceFourier 0 v (restCoordMap p)) = 0 := by
    intro v A
    have he : IsBoundedMeasurable fun p : Set.Ici (0 : ℝ) × (Fin (r + 1) → ℝ) =>
        expLaplaceFourier 0 v (restCoordMap p) :=
      (isBoundedMeasurable_expLaplaceFourier 0 v).comp measurable_restCoordMap
    have Ri := (representedBy_densityMul R he).mapAlong measurable_firstCoordMap
    refine h₁ ⟨_, Ri.isCountablyAdditive⟩ (fun k s => ?_) A
    refine (Ri.integralOf_eq (isBoundedMeasurable_halfPlaneExp k s)).trans ?_
    have e : (fun x => (halfPlaneExp k s ∘ firstCoordMap) x *
          expLaplaceFourier 0 v (restCoordMap x)) =
        expLaplaceFourier k (Matrix.vecCons s v) := funext fun x => halfPlaneExp_mul k s v x
    simp only [e]
    exact h _ _
  have step₂ : ∀ (A : MeasurableSets (Set.Ici (0 : ℝ) × ℝ))
      (S : MeasurableSets (Set.Ici (0 : ℝ) × (Fin r → ℝ))),
      BorelComplexMeasures.integralOf ν.1 (fun p =>
        indicatorC (restCoordMap ⁻¹' (S : Set _)) p *
          indicatorC (firstCoordMap ⁻¹' (A : Set _)) p) = 0 := by
    intro A S
    have hb := isBoundedMeasurable_indicatorC (measurable_firstCoordMap (r := r) A.2)
    have Rt := (representedBy_densityMul R hb).mapAlong measurable_restCoordMap
    refine IH ⟨_, Rt.isCountablyAdditive⟩ (fun k v => ?_) S
    refine (Rt.integralOf_eq (isBoundedMeasurable_expLaplaceFourier k v)).trans ?_
    have e : (fun x => (expLaplaceFourier k v ∘ restCoordMap) x *
          indicatorC (firstCoordMap ⁻¹' (A : Set _)) x) = fun p =>
        indicatorC (firstCoordMap ⁻¹' (A : Set _)) p *
          expLaplaceFourier 0 v (restCoordMap p) :=
      funext fun x => by
        rw [Function.comp_apply, expLaplaceFourier_restCoordMap, mul_comm]
    simp only [e]
    exact step₁ v A
  have step₃ : ∀ (A : MeasurableSets (Set.Ici (0 : ℝ) × ℝ))
      (S : MeasurableSets (Set.Ici (0 : ℝ) × (Fin r → ℝ))),
      ν.1 ⟨restCoordMap ⁻¹' (S : Set _) ∩ firstCoordMap ⁻¹' (A : Set _),
        (measurable_restCoordMap S.2).inter (measurable_firstCoordMap A.2)⟩ = 0 := by
    intro A S
    have hm : MeasurableSet (restCoordMap (r := r) ⁻¹' (S : Set _) ∩
        firstCoordMap (r := r) ⁻¹' (A : Set _)) :=
      (measurable_restCoordMap S.2).inter (measurable_firstCoordMap A.2)
    have e := (R.integralOf_eq (isBoundedMeasurable_indicatorC hm)).trans
      (R.indicatorC_eq ⟨_, hm⟩)
    refine Eq.trans ?_ (step₂ A S)
    rw [← e]
    congr 1
    funext p
    by_cases h₁ : p ∈ restCoordMap ⁻¹' (S : Set _) <;>
      by_cases h₂ : p ∈ firstCoordMap ⁻¹' (A : Set _) <;>
      simp [indicatorC, h₁, h₂]
  have Rp := R.mapAlong measurable_splitMap
  refine eq_zero_of_pushforward measurable_splitMap measurable_joinMap joinMap_splitMap ?_
  refine eq_zero_of_isPiSystem Rp isPiSystem_prod generateFrom_prod.symm
    ⟨Set.univ, by simp, Set.univ, by simp, Set.univ_prod_univ⟩ ?_
  rintro A ⟨B₁, hB₁, B₂, hB₂, e⟩
  have z := step₃ ⟨B₁, hB₁⟩ ⟨Set.univ ×ˢ B₂, MeasurableSet.univ.prod hB₂⟩
  refine Eq.trans (congrArg ν.1 (Subtype.ext ?_)) z
  simp only [← e]
  ext p
  simp [splitMap, restCoordMap, and_comm]
end Characters
theorem zeroOfFourierLaplaceZero_holds (hF : SetFunctions.ComplexMeasureFacts)
    (hD : EuclideanAnalysis.Strip.ModulatedDenseAndMeasureUnique) :
    ZeroOfFourierLaplaceZero := by
  have h₁ := eq_zero_of_halfPlane hF hD
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro ν h
    have R := representedBy_integralOf hF ν.2
    have Ri := R.mapAlong (measurable_firstCoordMap (r := 0))
    have ψm : Measurable fun y : Set.Ici (0 : ℝ) × ℝ =>
        ((y.1, fun _ => y.2) : Set.Ici (0 : ℝ) × (Fin 1 → ℝ)) :=
      measurable_fst.prodMk (measurable_pi_lambda _ fun _ => measurable_snd)
    refine eq_zero_of_pushforward (measurable_firstCoordMap (r := 0)) ψm (fun p => ?_)
      (h₁ ⟨_, Ri.isCountablyAdditive⟩ ?_)
    · refine Prod.ext rfl (funext fun i => ?_)
      rw [Subsingleton.elim i 0]
      rfl
    · intro k s
      refine (Ri.integralOf_eq (isBoundedMeasurable_halfPlaneExp k s)).trans ?_
      have e : halfPlaneExp k s ∘ firstCoordMap =
          expLaplaceFourier k (Matrix.vecCons s Fin.elim0) := funext fun p => by
        rw [← halfPlaneExp_mul k s Fin.elim0 p, Function.comp_apply]
        simp [expLaplaceFourier]
      simp only [e]
      exact h _ _
  | succ r _ IH => exact eq_zero_succ hF h₁ IH
theorem zeroOfFourierZero_holds (hF : SetFunctions.ComplexMeasureFacts)
    (hc : ZeroOfFourierLaplaceZero) :
    ZeroOfFourierZero := by
  intro r hr ν h
  have R := representedBy_integralOf hF ν.2
  have φm : Measurable fun q : Fin r → ℝ =>
      (((⟨0, Set.self_mem_Ici⟩ : Set.Ici (0 : ℝ)), q) : Set.Ici (0 : ℝ) × (Fin r → ℝ)) :=
    measurable_const.prodMk measurable_id
  have Ri := R.mapAlong φm
  refine eq_zero_of_pushforward φm measurable_snd (fun _ => rfl)
    (hc r hr ⟨_, Ri.isCountablyAdditive⟩ fun k v => ?_)
  refine (Ri.integralOf_eq (isBoundedMeasurable_expLaplaceFourier k v)).trans ?_
  have e : expLaplaceFourier k v ∘ (fun q : Fin r → ℝ =>
      (((⟨0, Set.self_mem_Ici⟩ : Set.Ici (0 : ℝ)), q) : Set.Ici (0 : ℝ) × (Fin r → ℝ))) =
      fourierExp v := funext fun q => by
    simp [expLaplaceFourier, fourierExp]
  simp only [e]
  exact h v
theorem zeroOfLaplaceNatZero_holds (hF : SetFunctions.ComplexMeasureFacts)
    (hc : ZeroOfFourierLaplaceZero) :
    ZeroOfLaplaceNatZero := by
  intro ν h
  have R := representedBy_integralOf hF ν.2
  have φm : Measurable fun E : Set.Ici (0 : ℝ) =>
      ((E, 0) : Set.Ici (0 : ℝ) × (Fin 1 → ℝ)) :=
    measurable_id.prodMk measurable_const
  have Ri := R.mapAlong φm
  refine eq_zero_of_pushforward φm measurable_fst (fun _ => rfl)
    (hc 1 le_rfl ⟨_, Ri.isCountablyAdditive⟩ fun k v => ?_)
  refine (Ri.integralOf_eq (isBoundedMeasurable_expLaplaceFourier k v)).trans ?_
  have e : expLaplaceFourier k v ∘ (fun E : Set.Ici (0 : ℝ) =>
      ((E, 0) : Set.Ici (0 : ℝ) × (Fin 1 → ℝ))) = laplaceExp k := funext fun E => by
    simp [expLaplaceFourier, laplaceExp]
  simp only [e]
  exact h k
theorem zeroOfZeroOnBoxes_holds (hF : SetFunctions.ComplexMeasureFacts) :
    ZeroOfZeroOnBoxes := by
  intro r _ n _ X _ ν hz
  refine eq_zero_of_isPiSystem (representedBy_integralOf hF ν.2)
    (C := Set.pi Set.univ '' Set.pi Set.univ fun k => {s | MeasurableSet s})
    isPiSystem_pi generateFrom_pi.symm
    ⟨fun _ => Set.univ, fun _ _ => by simp, Set.pi_univ _⟩ ?_
  rintro A ⟨t, ht, e⟩
  exact Eq.trans (congrArg ν.1 (Subtype.ext e.symm)) (hz fun k => ⟨t k, ht k trivial⟩)
theorem eqOfIntegralCompactSupportEq_holds : EqOfIntegralCompactSupportEq := by
  intro n _ m m' _ _ h
  refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f => ?_
  exact h (fun x => (f x : ℝ))
    ⟨NNReal.continuous_coe.comp f.continuous, f.hasCompactSupport.comp_left rfl⟩
    (fun x => (f x).2)
theorem integralRulesBounded_holds (hF : SetFunctions.ComplexMeasureFacts) :
    IntegralRulesBounded := by
  intro n n' _ _ X X' _ _ ν ν' c g g' φ hφ g'' hg hg' hg''
  have R := representedBy_integralOf hF ν.2
  have R' := representedBy_integralOf hF ν'.2
  have Rs := R.add (R'.cmul c)
  exact
    { add_smul_isCountablyAdditive := Rs.isCountablyAdditive
      conj_isCountablyAdditive := R.conjugate.isCountablyAdditive
      densityMul_isCountablyAdditive := (representedBy_densityMul R hg).isCountablyAdditive
      pushforward_isCountablyAdditive := (R.mapAlong hφ).isCountablyAdditive
      integralOf_linear := fun a b => by
        rw [R.integralOf_eq (((IsBoundedMeasurable.const a).mul hg).add
          ((IsBoundedMeasurable.const b).mul hg')), R.linear hg hg' a b, R.integralOf_eq hg,
          R.integralOf_eq hg']
      integralOf_indicator := fun A =>
        (R.integralOf_eq (isBoundedMeasurable_indicatorC A.2)).trans (R.indicatorC_eq A)
      integralOf_add_smul := Rs.integralOf_eq hg
      integralOf_conj := R.conjugate.integralOf_eq hg
      integralOf_densityMul := (representedBy_densityMul R hg).integralOf_eq hg'
      integralOf_pushforward := (R.mapAlong hφ).integralOf_eq hg'' }
theorem lIntegralRules_holds : LIntegralRules := by
  intro n n' _ _ X X' _ _ m φ u _ hφ hu _
  refine ⟨fun f hf => ?_, fun f'' hf'' => ?_⟩
  · exact (lintegral_withDensity_eq_lintegral_mul m hu.coe_nnreal_ennreal
      hf.coe_nnreal_ennreal).trans (lintegral_congr fun x => by simp [mul_comm])
  · exact lintegral_map hf''.coe_nnreal_ennreal hφ
theorem uniquenessAndIntegral_holds (hD : EuclideanAnalysis.Strip.ModulatedDenseAndMeasureUnique)
    (hF : SetFunctions.ComplexMeasureFacts) : UniquenessAndIntegral := by
  have hc := zeroOfFourierLaplaceZero_holds hF hD
  refine ⟨zeroOfZeroOnBoxes_holds hF, eqOfIntegralCompactSupportEq_holds, hc,
    ⟨zeroOfFourierZero_holds hF hc, zeroOfLaplaceNatZero_holds hF hc⟩, ?_,
    integralRulesBounded_holds hF, lIntegralRules_holds⟩
  intro n _ X _
  exact ⟨fun ν μ₁ μ₂ μ₃ μ₄ μ₁' μ₂' μ₃' μ₄' f h h' _ i₁ i₂ i₃ i₄ i₁' i₂' i₃' i₄' =>
    combinedIntegral_unique h h' i₁ i₂ i₃ i₄ i₁' i₂' i₃' i₄',
    fun ν f z h => integralOf_eq_of_isIntegralOf h⟩
end YangMills.Construction.MeasureUniqueness
end
