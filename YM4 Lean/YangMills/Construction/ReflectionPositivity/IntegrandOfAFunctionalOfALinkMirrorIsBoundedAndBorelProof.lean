import YangMills.Construction.ReflectionPositivity.BondsAndPlaquettesAreNotDegenerateProof
import YangMills.Construction.InfiniteLattice.FirstFactsOnArraysAndPerturbedSpecificationsProof
import YangMills.Construction.InfiniteLattice.FunctionsOfASetOfBondsProof
import YangMills.Construction.Lattice.LatticesOfATorusAndTheProductTopologyOfConfigurations
import YangMills.Construction.ReflectionPositivity.ActionInTheDoubledVariablesOfALinkMirror
import YangMills.Construction.ReflectionPositivity.IntegrandOfAFunctionalOfALinkMirrorIsBoundedAndBorel
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.IntegrandBounded
theorem borelMeasurable_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) : @Measurable X Y (borel X) (borel Y) f := by apply _root_.YangMills.Construction.InfiniteLattice.LinkSetFunctions.continuous_measurable_borel <;> assumption
theorem borelMeasurable_complex_of_continuous {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    (hf : Continuous f) : Measurable[borel X] f := by apply _root_.YangMills.Construction.InfiniteLattice.continuous_complex_measurable_borel <;> assumption
theorem borelMeasurable_comp_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {g : Y → ℂ} {f : X → Y} (hg : Measurable[borel Y] g) (hf : Continuous f) :
    Measurable[borel X] (g ∘ f) :=
  @Measurable.comp X Y ℂ (borel X) (borel Y) _ g f hg (borelMeasurable_of_continuous hf)
theorem borelMeasurable_mul {X : Type*} [TopologicalSpace X] {f g : X → ℂ}
    (hf : Measurable[borel X] f) (hg : Measurable[borel X] g) :
    Measurable[borel X] fun x => f x * g x := by
  let _ : MeasurableSpace X := borel X
  exact hf.mul hg
variable {D : MirrorData}
theorem not_positive_opposite {e : D.Edge} (h : e.IsPositivelyOriented) :
    ¬e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.ReflectionPositivity.PlaquetteNondegeneracy.not_opposite_positive <;> assumption
theorem coe_inv_specialUnitary (x : Matrices.ComplexMatrix2.specialUnitary) :
    ((x⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      (x : Matrices.ComplexMatrix2)⁻¹ := by apply _root_.YangMills.Construction.InfiniteLattice.specialUnitary_coe_inv <;> assumption
variable (C : LinkLevel D)
theorem halfCoords_pos_surjective : Function.Surjective (C.halfCoords .pos) := by
  classical
  intro u
  let v : PeriodicLattice.PositivelyOrientedBond D.L D.m (D.K : ℕ) →
      Matrices.ComplexMatrix2.specialUnitary :=
    fun e => LinkLevel.extendByOne u e.1
  let W : D.Edge → Matrices.ComplexMatrix2 := PeriodicLattice.gaugeFieldOfPositive v
  have hpos : ∀ (e : D.Edge) (h : e.IsPositivelyOriented),
      W e = (v ⟨e, h⟩ : Matrices.ComplexMatrix2) :=
    fun e h => dif_pos h
  have hneg : ∀ (e : D.Edge) (h' : e.opposite.IsPositivelyOriented), ¬e.IsPositivelyOriented →
      W e = (((v ⟨e.opposite, h'⟩)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
        Matrices.ComplexMatrix2) := by
    intro e h' h
    rw [coe_inv_specialUnitary]
    exact (dif_neg h).trans (dif_pos h')
  have hmem : ∀ e : D.Edge, W e ∈ PeriodicLattice.compactGaugeGroup := by
    intro e
    by_cases h : e.IsPositivelyOriented
    · rw [hpos e h]
      exact (v ⟨e, h⟩).2
    · have h' := (PeriodicLattice.Bond.positive_or_opposite_positive e).resolve_left h
      rw [hneg e h' h]
      exact ((v ⟨e.opposite, h'⟩)⁻¹).2
  have hopp : ∀ e : D.Edge, W e.opposite = (W e)⁻¹ := by
    intro e
    by_cases h : e.IsPositivelyOriented
    · have h' : e.opposite.opposite.IsPositivelyOriented := by
        rw [PeriodicLattice.Bond.opposite_opposite]
        exact h
      rw [hneg e.opposite h' (not_positive_opposite h), hpos e h, coe_inv_specialUnitary]
      rfl
    · have h' := (PeriodicLattice.Bond.positive_or_opposite_positive e).resolve_left h
      rw [hneg e h' h, hpos e.opposite h', ← coe_inv_specialUnitary, inv_inv]
  refine ⟨⟨W, fun e _ => hmem e, fun e _ => hopp e⟩, ?_⟩
  funext e
  apply Subtype.ext
  change W e.1 = _
  rw [hpos e.1 e.2.1]
  change ((LinkLevel.extendByOne u e.1 : Matrices.ComplexMatrix2.specialUnitary) :
    Matrices.ComplexMatrix2) = _
  rw [LinkLevel.extendByOne, dif_pos e.2]
theorem halfFunction_eq_of_mem {F : D.FieldSpace → ℂ}
    {Φ : (C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary) → ℂ}
    (hF : F ∈ C.halfAlgebra .pos) (hΦ : F = fun U => Φ (D.linkValues (C.halfEdges .pos) U)) :
    C.halfFunction .pos F = Φ := by
  funext u
  obtain ⟨U, rfl⟩ := halfCoords_pos_surjective C u
  rw [← C.halfFunction_spec hF U, hΦ]
  rfl
theorem linkIntegrand_boundedMeasurable (hA : Continuous C.halfAction)
    (hA₀ : ∀ u, 0 ≤ C.halfAction u)
    (hφ : ∀ γ : C.KernelLabel, Continuous (C.kernelFn γ) ∧
      ∀ ω, ‖C.kernelFn γ ω‖ ≤ 1) : LinkIntegrandBoundedMeasurable C := by
  intro n γ F hF
  obtain ⟨Φ, hΦm, ⟨c, hc⟩, hΦ⟩ := id hF
  have hhalf : C.halfFunction .pos F = Φ := halfFunction_eq_of_mem C hF hΦ
  have hprod : Continuous (C.kernelProd γ) := by
    unfold LinkLevel.kernelProd
    exact continuous_finsetProd _ fun j _ => (hφ (γ j)).1
  have hexp : Continuous fun ω : C.DoubleSpace =>
      ((Real.exp (-D.coupling * C.halfAction ω.1) : ℝ) : ℂ) := by
    exact Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (hA.comp continuous_fst)))
  constructor
  · refine ⟨c, fun ω => ?_⟩
    have h₁ : ‖((Real.exp (-D.coupling * C.halfAction ω.1) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.2
      have := mul_nonneg D.coupling_pos.le (hA₀ ω.1)
      linarith
    have h₂ : ‖C.kernelProd γ ω‖ ≤ 1 := by
      unfold LinkLevel.kernelProd
      rw [norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun j _ => (hφ (γ j)).2 ω
    unfold linkIntegrand
    rw [hhalf, norm_mul, norm_mul]
    calc ‖Φ ω.1‖ * ‖((Real.exp (-D.coupling * C.halfAction ω.1) : ℝ) : ℂ)‖ * ‖C.kernelProd γ ω‖
        ≤ ‖Φ ω.1‖ * 1 * 1 := by gcongr
      _ ≤ c := by simpa using hc ω.1
  · have hfun : linkIntegrand C γ F = fun ω =>
        (Φ ω.1 * ((Real.exp (-D.coupling * C.halfAction ω.1) : ℝ) : ℂ)) * C.kernelProd γ ω := by
      funext ω
      simp only [linkIntegrand, hhalf]
    rw [hfun]
    exact borelMeasurable_mul
      (borelMeasurable_mul (borelMeasurable_comp_continuous hΦm continuous_fst)
        (borelMeasurable_complex_of_continuous hexp))
      (borelMeasurable_complex_of_continuous hprod)
theorem continuous_reflectField : Continuous C.reflectField := by
  refine Continuous.subtype_mk (f := fun U : D.FieldSpace => fun e => U.1 (C.reflectedEdge e)) ?_ _
  exact continuous_pi fun e => (continuous_apply _).comp continuous_subtype_val
theorem reflect_preserves_boundedMeasurable : ReflectPreservesBoundedMeasurable C := by
  rintro F ⟨c, hc⟩ hF
  exact ⟨⟨c, fun U => hc _⟩, borelMeasurable_comp_continuous hF (continuous_reflectField C)⟩
theorem boundedMeasurableFacts_holds (h : DoubledAction.DoubledActionProperties) :
    BoundedMeasurableFacts := by
  intro D C
  obtain ⟨hOne, -, hKernel, -⟩ := h D C
  exact ⟨linkIntegrand_boundedMeasurable C hOne.2.1 hOne.2.2.1 hKernel.1,
    reflect_preserves_boundedMeasurable C⟩
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.IntegrandBounded
end
