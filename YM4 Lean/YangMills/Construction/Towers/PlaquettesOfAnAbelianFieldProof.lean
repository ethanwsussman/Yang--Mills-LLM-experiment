import YangMills.Construction.Towers.CovariantShiftsOfAnAbelianFieldProof
import YangMills.Construction.Towers.DerivativeOfTheActionAtAnAbelianFieldProof
import YangMills.Construction.Towers.TheAlgebraOfTheCharges
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldPlaquettes
open AbelianFieldFacts Matrices
theorem cartanPhase_diagonal_form (ϑ : ℝ) :
    cartanPhase ϑ =
      Matrix.diagonal ![Complex.exp (Complex.I * ϑ), Complex.exp (-(Complex.I * ϑ))] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.cartanPhase_eq_diagonal <;> assumption
theorem cartanPhase_explicit (ϑ : ℝ) :
    cartanPhase ϑ = !![Complex.exp (Complex.I * ϑ), 0; 0, Complex.exp (-(Complex.I * ϑ))] := by apply _root_.YangMills.Construction.Tower.AbelianActionGradient.cartanPhase_eq_diagonal <;> assumption
theorem cartanPhase_at_zero : cartanPhase 0 = 1 := by
  rw [cartanPhase_diagonal_form]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
theorem cartanPhase_add_angle (s t : ℝ) : cartanPhase (s + t) = cartanPhase s * cartanPhase t := by
  simp only [cartanPhase_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add, mul_add, add_comm]
theorem cartanPhase_inverse (s : ℝ) : (cartanPhase s)⁻¹ = cartanPhase (-s) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← cartanPhase_add_angle, add_neg_cancel, cartanPhase_at_zero]
theorem star_cartanPhase_eq (s : ℝ) : star (cartanPhase s) = cartanPhase (-s) := by
  simp only [cartanPhase_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [← Complex.exp_conj]
theorem cartanPhase_mem_compact (s : ℝ) : cartanPhase s ∈ PeriodicLattice.compactGaugeGroup := by
  refine Matrix.mem_specialUnitaryGroup_iff.2 ⟨Matrix.mem_unitaryGroup_iff.2 ?_, ?_⟩
  · rw [star_cartanPhase_eq, ← cartanPhase_add_angle, add_neg_cancel, cartanPhase_at_zero]
  · rw [cartanPhase_explicit, Matrix.det_fin_two_of, mul_zero, sub_zero, ← Complex.exp_add]
    simp
theorem conjugateBy_cartanPhase_third (s : ℝ) :
    ComplexMatrix2.conjugateBy (cartanPhase s) (ComplexMatrix2.pauliFamily 2) =
      ComplexMatrix2.pauliFamily 2 := by
  rw [ComplexMatrix2.conjugateBy, cartanPhase_inverse, ComplexMatrix2.pauliFamily_apply.2.2]
  simp only [cartanPhase_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
section LinkField
variable {a : ℝ}
theorem not_isPositivelyOriented_opposite (ha : 0 < a) (b : InfiniteLattice.Link a)
    (h : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem abelianLinkField_of_positive (θ : FullSpace.PositiveEdge a → ℝ)
    (b : InfiniteLattice.Link a) (h : b.IsPositivelyOriented) :
    FullSpace.abelianLinkField θ b = cartanPhase (θ ⟨b, h⟩) := by
  simp only [FullSpace.abelianLinkField, dif_pos h, cartanPhase]
theorem abelianLinkField_of_opposite (ha : 0 < a) (θ : FullSpace.PositiveEdge a → ℝ)
    (b : InfiniteLattice.Link a) (h : b.IsPositivelyOriented) :
    FullSpace.abelianLinkField θ b.opposite = cartanPhase (-θ ⟨b, h⟩) := by
  have hn := not_isPositivelyOriented_opposite ha b h
  have h' : b.opposite.opposite.IsPositivelyOriented := h
  rw [← cartanPhase_inverse]
  simp only [FullSpace.abelianLinkField, dif_neg hn, dif_pos h', cartanPhase]
  rfl
theorem abelianLinkField_forward (θ : FullSpace.PositiveEdge a → ℝ)
    (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    FullSpace.abelianLinkField θ (InfiniteLattice.Link.forwardFrom x μ) =
      cartanPhase (θ (FullSpace.forwardEdge x μ)) :=
  abelianLinkField_of_positive θ _ (FullSpace.forwardEdge x μ).2
theorem abelianLinkField_backward (ha : 0 < a) (θ : FullSpace.PositiveEdge a → ℝ)
    (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    FullSpace.abelianLinkField θ (InfiniteLattice.Link.forwardFrom x μ).opposite =
      cartanPhase (-θ (FullSpace.forwardEdge x μ)) :=
  abelianLinkField_of_opposite ha θ _ (FullSpace.forwardEdge x μ).2
theorem abelianLinkField_isFieldIn (ha : 0 < a) (θ : FullSpace.PositiveEdge a → ℝ) :
    FullSpace.IsFieldIn PeriodicLattice.compactGaugeGroup (FullSpace.abelianLinkField θ) := by
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases h : b.IsPositivelyOriented
    · rw [abelianLinkField_of_positive θ b h]
      exact cartanPhase_mem_compact _
    · by_cases h' : b.opposite.IsPositivelyOriented
      · have e := abelianLinkField_of_opposite ha θ b.opposite h'
        change FullSpace.abelianLinkField θ b = _ at e
        rw [e]
        exact cartanPhase_mem_compact _
      · have e : FullSpace.abelianLinkField θ b = 1 := by
          simp only [FullSpace.abelianLinkField, dif_neg h, dif_neg h']
        rw [e]
        exact Submonoid.one_mem _
  · by_cases h : b.IsPositivelyOriented
    · rw [abelianLinkField_of_opposite ha θ b h, abelianLinkField_of_positive θ b h,
        cartanPhase_inverse]
    · by_cases h' : b.opposite.IsPositivelyOriented
      · have e := abelianLinkField_of_opposite ha θ b.opposite h'
        change FullSpace.abelianLinkField θ b = _ at e
        rw [e, abelianLinkField_of_positive θ b.opposite h', cartanPhase_inverse, neg_neg]
      · have h'' : ¬ b.opposite.opposite.IsPositivelyOriented := h
        have e : FullSpace.abelianLinkField θ b = 1 := by
          simp only [FullSpace.abelianLinkField, dif_neg h, dif_neg h']
        have e' : FullSpace.abelianLinkField θ b.opposite = 1 := by
          simp only [FullSpace.abelianLinkField, dif_neg h', dif_neg h'']
        rw [e, e', inv_one]
def faceTransportAngles (θ : FullSpace.PositiveEdge a → ℝ)
    (p : InfiniteLattice.ElementaryPlaquette a) : Fin 4 → ℝ :=
  ![0, θ (FullSpace.forwardEdge p.corner p.lowAxis),
    θ (FullSpace.forwardEdge p.corner p.lowAxis) +
        θ (FullSpace.forwardEdge (p.corner + InfiniteLattice.axisStep a p.lowAxis) p.highAxis) -
      θ (FullSpace.forwardEdge (p.corner + InfiniteLattice.axisStep a p.highAxis) p.lowAxis),
    FullSpace.faceAngle θ p]
theorem faceVariable_abelian (ha : 0 < a) (θ : FullSpace.PositiveEdge a → ℝ)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    FullSpace.faceVariable (FullSpace.abelianLinkField θ) p =
      cartanPhase (FullSpace.faceAngle θ p) := by
  simp only [FullSpace.faceVariable, FullSpace.linkHolonomy, FullSpace.faceBoundary,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    abelianLinkField_forward, abelianLinkField_backward ha]
  simp only [← cartanPhase_add_angle]
  congr 1
  simp only [FullSpace.faceAngle, FullSpace.edgeDifference]
  ring
theorem faceTransports_abelian (ha : 0 < a) (θ : FullSpace.PositiveEdge a → ℝ)
    (p : InfiniteLattice.ElementaryPlaquette a) (i : Fin 4) :
    FullSpace.faceTransports (FullSpace.abelianLinkField θ) p i =
      cartanPhase (faceTransportAngles θ p i) := by
  have h2 : FullSpace.faceEdge p 2 =
      InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.highAxis)
        p.lowAxis := rfl
  fin_cases i
  · simpa [FullSpace.faceTransports, faceTransportAngles] using cartanPhase_at_zero.symm
  · exact abelianLinkField_forward θ _ _
  · change FullSpace.abelianLinkField θ (FullSpace.faceEdge p 0) *
        FullSpace.abelianLinkField θ (FullSpace.faceEdge p 1) *
        (FullSpace.abelianLinkField θ (FullSpace.faceEdge p 2))⁻¹ = _
    have h0 : FullSpace.faceEdge p 0 = InfiniteLattice.Link.forwardFrom p.corner p.lowAxis := rfl
    have h1 : FullSpace.faceEdge p 1 =
      InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.lowAxis)
        p.highAxis := rfl
    rw [h0, h1, h2, abelianLinkField_forward, abelianLinkField_forward, abelianLinkField_forward,
      cartanPhase_inverse, ← cartanPhase_add_angle, ← cartanPhase_add_angle]
    rfl
  · exact faceVariable_abelian ha θ p
end LinkField
theorem raisingPauli_explicit : raisingPauli = !![0, 1; 0, 0] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.raisingPauli_eq_matrix <;> assumption
theorem loweringPauli_explicit : loweringPauli = !![0, 0; 1, 0] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.loweringPauli_eq_matrix <;> assumption
theorem conjugateBy_cartanPhase_combination (hA : ChargeAlgebra) (s : ℝ) (c y z : ℂ) :
    ComplexMatrix2.conjugateBy (cartanPhase s)
        (c • ComplexMatrix2.pauliFamily 2 + y • raisingPauli + z • loweringPauli) =
      c • ComplexMatrix2.pauliFamily 2 +
          (Complex.exp (2 * Complex.I * (s : ℂ)) * y) • raisingPauli +
        (Complex.exp (-(2 * Complex.I * (s : ℂ))) * z) • loweringPauli := by
  have h3 := conjugateBy_cartanPhase_third s
  have hp := (hA.1 s).1
  have hm := (hA.1 s).2
  simp only [ComplexMatrix2.conjugateBy] at h3 hp hm ⊢
  simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, h3, hp, hm, smul_smul]
  rw [mul_comm y, mul_comm z]
theorem conj_transportSign (i : Fin 4) : conj (transportSign i) = transportSign i := by
  fin_cases i <;> simp [transportSign]
theorem conj_exp_two_I_mul (s : ℝ) :
    conj (Complex.exp (2 * Complex.I * (s : ℂ))) = Complex.exp (-(2 * Complex.I * (s : ℂ))) := by
  rw [← Complex.exp_conj]
  simp [map_ofNat (starRingEnd ℂ) 2]
section FaceNumbers
variable {a : ℝ}
theorem faceNumbers_explicit (θ : FullSpace.PositiveEdge a → ℝ) (w : FullSpace.PositiveEdge a → ℂ)
    (p : InfiniteLattice.ElementaryPlaquette a) (i : Fin 4) :
    FullSpace.faceNumbers θ w p i =
      transportSign i * Complex.exp (2 * Complex.I * (faceTransportAngles θ p i : ℂ)) *
        w (facePositiveEdge p i) := by
  fin_cases i
  · simp [FullSpace.faceNumbers, transportSign, faceTransportAngles, facePositiveEdge,
      FullSpace.edgeComponent]
  · simp [FullSpace.faceNumbers, transportSign, faceTransportAngles, facePositiveEdge,
      FullSpace.edgeComponent, FullSpace.chargedShift]
  · have e : faceTransportAngles θ p 2 =
        FullSpace.faceAngle θ p + θ (FullSpace.forwardEdge p.corner p.highAxis) := by
      simp only [faceTransportAngles, FullSpace.faceAngle, FullSpace.edgeDifference]
      simp
    change FullSpace.faceNumbers θ w p 2 = transportSign 2 *
      Complex.exp (2 * Complex.I * (faceTransportAngles θ p 2 : ℂ)) * w (facePositiveEdge p 2)
    rw [e]
    simp only [FullSpace.faceNumbers, transportSign, facePositiveEdge, FullSpace.edgeComponent,
      FullSpace.chargedShift]
    simp only [Complex.ofReal_add, mul_add, Complex.exp_add]
    simp
    ring_nf
  · simp [FullSpace.faceNumbers, transportSign, faceTransportAngles, facePositiveEdge,
      FullSpace.edgeComponent]
end FaceNumbers
theorem transportedForm_abelian {a : ℝ} (ha : 0 < a) (hA : ChargeAlgebra)
    (hF : FormsChargeDecomposition a) (θ : FullSpace.PositiveEdge a → ℝ)
    (B : InfiniteLattice.Link a → ComplexMatrix2) (hB : B ∈ FullSpace.edgeFormSpace a)
    (p : InfiniteLattice.ElementaryPlaquette a) (i : Fin 4) :
    FullSpace.transportedForm (FullSpace.abelianLinkField θ) B p i =
      (transportSign i * ((FullSpace.diagonalComponent B (facePositiveEdge p i) : ℝ) : ℂ)) •
          ComplexMatrix2.pauliFamily 2 +
        FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i • raisingPauli +
        conj (FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i) • loweringPauli := by
  rw [FullSpace.transportedForm, faceTransports_abelian ha, ← facePositiveEdge_val p i,
    (hF B hB (facePositiveEdge p i)).1, conjugateBy_cartanPhase_combination hA,
    faceNumbers_explicit]
  simp only [smul_add, smul_smul, map_mul, conj_transportSign, conj_exp_two_I_mul]
  simp only [mul_assoc]
theorem trace_lie_mul_third (c c' y y' : ℂ) :
    (Complex.I / 2) * ComplexMatrix2.fullTrace
        (⁅c • ComplexMatrix2.pauliFamily 2 + y • raisingPauli + conj y • loweringPauli,
          c' • ComplexMatrix2.pauliFamily 2 + y' • raisingPauli + conj y' • loweringPauli⁆ *
            ComplexMatrix2.pauliFamily 2) =
      ((-2 * (y * conj y').im : ℝ) : ℂ) := by
  have hz := Complex.sub_conj (y * conj y')
  simp only [map_mul, Complex.conj_conj] at hz
  have hr : ((-2 * (y * conj y').im : ℝ) : ℂ) = Complex.I * (y * conj y' - conj y * y') := by
    rw [hz]
    push_cast
    linear_combination (-(2 * ((y * conj y').im : ℂ))) * Complex.I_mul_I
  have ht : ComplexMatrix2.fullTrace
      (⁅c • ComplexMatrix2.pauliFamily 2 + y • raisingPauli + conj y • loweringPauli,
        c' • ComplexMatrix2.pauliFamily 2 + y' • raisingPauli + conj y' • loweringPauli⁆ *
          ComplexMatrix2.pauliFamily 2) =
      2 * (y * conj y' - conj y * y') := by
    rw [raisingPauli_explicit, loweringPauli_explicit, ComplexMatrix2.pauliFamily_apply.2.2,
      Ring.lie_def, ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [ht, hr]
  ring
theorem half_fullTrace_cartanPhase (f : ℝ) :
    (1 / 2 : ℂ) * ComplexMatrix2.fullTrace (cartanPhase f) = ((Real.cos f : ℝ) : ℂ) := by
  rw [cartanPhase_explicit, ComplexMatrix2.fullTrace, Matrix.trace_fin_two_of, Complex.ofReal_cos,
    Complex.cos]
  have e₁ : Complex.I * (f : ℂ) = (f : ℂ) * Complex.I := mul_comm _ _
  have e₂ : -((f : ℂ) * Complex.I) = -(f : ℂ) * Complex.I := by ring
  rw [e₁, e₂]
  ring
theorem two_I_mul_real_sin (f : ℝ) :
    2 * Complex.I * ((Real.sin f : ℝ) : ℂ) =
      Complex.exp (Complex.I * f) - Complex.exp (-(Complex.I * f)) := by
  rw [Complex.ofReal_sin, Complex.sin]
  have e₁ : Complex.I * (f : ℂ) = (f : ℂ) * Complex.I := mul_comm _ _
  have e₂ : -((f : ℂ) * Complex.I) = -(f : ℂ) * Complex.I := by ring
  rw [e₁, e₂]
  linear_combination
    (Complex.exp (-(f : ℂ) * Complex.I) - Complex.exp ((f : ℂ) * Complex.I)) * Complex.I_mul_I
theorem cartanPhase_sub_inv (f : ℝ) :
    cartanPhase f - (cartanPhase f)⁻¹ =
      (2 * Complex.I * ((Real.sin f : ℝ) : ℂ)) • ComplexMatrix2.pauliFamily 2 := by
  rw [cartanPhase_inverse, two_I_mul_real_sin, ComplexMatrix2.pauliFamily_apply.2.2]
  simp only [cartanPhase_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
theorem claim_holds (hCharges : ChargeAlgebraAndForms) : Claim := by
  intro L hL θ
  have ha : 0 < meshAt L 0 0 := by simp [meshAt]
  have hA := hCharges.1
  have hF := hCharges.2 L hL
  have hU := faceVariable_abelian ha θ
  refine ⟨abelianLinkField_isFieldIn ha θ, hU, fun p => ?_, fun p => ?_, fun B hB p i => ?_,
    fun B hB p i j => ?_⟩
  · rw [hU]
    exact half_fullTrace_cartanPhase _
  · rw [hU]
    exact cartanPhase_sub_inv _
  · exact transportedForm_abelian ha hA hF θ B hB p i
  · rw [transportedForm_abelian ha hA hF θ B hB p i, transportedForm_abelian ha hA hF θ B hB p j]
    exact trace_lie_mul_third _ _ _ _
end YangMills.Construction.Tower.AbelianFieldPlaquettes
end
