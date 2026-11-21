import YangMills.Construction.Towers.FunctionalInTheBackgroundGaugeInTheExponentialChartProof
import YangMills.Construction.Towers.SecondDifferentialOfTheFunctionalAndItsComplexExtension
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower
namespace HessianExtension
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem deriv_deriv_smul_add_eq_fderiv_fderiv {f : E → ℝ} (hf : ContDiffAt ℝ ∞ f 0) (u v : E) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => f (s • u + t • v)) 0) 0 =
      fderiv ℝ (fderiv ℝ f) 0 u v := by
  have htwo : (2 : WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) 0 := by
    have hone : ContDiffAt ℝ 1 (fderiv ℝ f) 0 :=
      hf.fderiv_right (m := 1) (by rw [one_add_one_eq_two]; exact htwo)
    exact (hone.differentiableAt (by simp)).hasFDerivAt
  have hdiff : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℝ f x := by
    have hf2 : ContDiffAt ℝ 2 f 0 := hf.of_le htwo
    filter_upwards [hf2.eventually (by simp)] with x hx
    exact hx.differentiableAt (by simp)
  have hu : HasDerivAt (fun s : ℝ => s • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have htend : Tendsto (fun s : ℝ => s • u) (𝓝 0) (𝓝 0) := by
    have hc := hu.continuousAt.tendsto
    simpa using hc
  have heq : (fun s : ℝ => deriv (fun t : ℝ => f (s • u + t • v)) 0) =ᶠ[𝓝 0]
      fun s : ℝ => fderiv ℝ f (s • u) v := by
    filter_upwards [htend.eventually hdiff] with s hs
    have hv : HasDerivAt (fun t : ℝ => s • u + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (s • u)
    have hfs : HasFDerivAt f (fderiv ℝ f (s • u)) (s • u + (0 : ℝ) • v) := by
      simpa using hs.hasFDerivAt
    exact (hfs.comp_hasDerivAt (0 : ℝ) hv).deriv
  rw [heq.deriv_eq]
  have hD0 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) ((0 : ℝ) • u) := by
    simpa using hD
  have hcomp := hD0.comp_hasDerivAt (0 : ℝ) hu
  have happ := hcomp.clm_apply (hasDerivAt_const (0 : ℝ) v)
  simpa using happ.deriv
end
section
variable {E V : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℂ V]
theorem exists_complexBilin_extension (ι : E → V) (re im : V → E)
    (re_add : ∀ v w, re (v + w) = re v + re w) (im_add : ∀ v w, im (v + w) = im v + im w)
    (re_smul : ∀ (c : ℂ) v, re (c • v) = c.re • re v - c.im • im v)
    (im_smul : ∀ (c : ℂ) v, im (c • v) = c.re • im v + c.im • re v)
    (re_of : ∀ x, re (ι x) = x) (im_of : ∀ x, im (ι x) = 0) (B : LinearMap.BilinForm ℝ E) :
    ∃ β : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, ∀ x y, β (ι x) (ι y) = (B x y : ℂ) := by
  refine ⟨LinearMap.mk₂ ℂ (fun v w => ((B (re v) (re w) - B (im v) (im w) : ℝ) : ℂ) +
      Complex.I * ((B (re v) (im w) + B (im v) (re w) : ℝ) : ℂ)) ?_ ?_ ?_ ?_, ?_⟩
  · intro v v' w
    simp only [re_add, im_add, map_add, LinearMap.add_apply]
    push_cast
    ring
  · intro c v w
    simp only [re_smul, im_smul, map_add, map_sub, map_smul, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Complex.ext <;> simp <;> ring
  · intro v w w'
    simp only [re_add, im_add, map_add]
    push_cast
    ring
  · intro c v w
    simp only [re_smul, im_smul, map_add, map_sub, map_smul, smul_eq_mul]
    apply Complex.ext <;> simp <;> ring
  · intro x y
    simp [re_of, im_of]
omit [AddCommGroup E] [Module ℝ E] in
theorem bilin_symm_of_symm_on_real (ι : E → V) (re im : V → E)
    (hdec : ∀ v, v = ι (re v) + Complex.I • ι (im v)) (β : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hsymm : ∀ x y, β (ι x) (ι y) = β (ι y) (ι x)) (v w : V) : β v w = β w v := by
  obtain ⟨a, a', rfl⟩ : ∃ a a', v = ι a + Complex.I • ι a' := ⟨_, _, hdec v⟩
  obtain ⟨c, c', rfl⟩ : ∃ c c', w = ι c + Complex.I • ι c' := ⟨_, _, hdec w⟩
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm a c, hsymm a c', hsymm a' c, hsymm a' c']
  ring
end
section
def hermPart (X : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (X + X.conjTranspose)
def antiHermPart (X : ComplexMatrix2) : ComplexMatrix2 := (-Complex.I / 2) • (X - X.conjTranspose)
theorem hermPart_add_I_smul_antiHermPart (X : ComplexMatrix2) :
    hermPart X + Complex.I • antiHermPart X = X := by
  ext i j
  simp only [hermPart, antiHermPart, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul]
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(X i j - X.conjTranspose i j) / 2) * hII
theorem hermPart_antiHermPart_of_eq_conjTranspose {X : ComplexMatrix2}
    (h : X = X.conjTranspose) : hermPart X = X ∧ antiHermPart X = 0 := by
  unfold hermPart antiHermPart
  rw [← h]
  constructor
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · simp
theorem hermPart_add (X Y : ComplexMatrix2) : hermPart (X + Y) = hermPart X + hermPart Y := by
  simp only [hermPart, Matrix.conjTranspose_add, ← smul_add]
  congr 1
  abel
theorem antiHermPart_add (X Y : ComplexMatrix2) :
    antiHermPart (X + Y) = antiHermPart X + antiHermPart Y := by
  simp only [antiHermPart, Matrix.conjTranspose_add, ← smul_add]
  congr 1
  abel
theorem hermPart_neg (X : ComplexMatrix2) : hermPart (-X) = -hermPart X := by
  simp only [hermPart, Matrix.conjTranspose_neg, ← smul_neg]
  congr 1
  abel
theorem antiHermPart_neg (X : ComplexMatrix2) : antiHermPart (-X) = -antiHermPart X := by
  simp only [antiHermPart, Matrix.conjTranspose_neg, ← smul_neg]
  congr 1
  abel
theorem hermPart_smul (c : ℂ) (X : ComplexMatrix2) :
    hermPart (c • X) = c.re • hermPart X - c.im • antiHermPart X := by
  ext i j
  simp only [hermPart, antiHermPart, Matrix.conjTranspose_smul, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring
theorem antiHermPart_smul (c : ℂ) (X : ComplexMatrix2) :
    antiHermPart (c • X) = c.re • antiHermPart X + c.im • hermPart X := by
  ext i j
  simp only [hermPart, antiHermPart, Matrix.conjTranspose_smul, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring
theorem hermPart_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    hermPart X ∈ ComplexMatrix2.hermitianTraceless := by
  have htr : Matrix.trace X = 0 := h
  refine ⟨?_, ?_⟩
  · unfold hermPart
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      add_comm]
    congr 1
    simp
  · show Matrix.trace _ = 0
    unfold hermPart
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_conjTranspose, htr]
    simp
theorem antiHermPart_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    antiHermPart X ∈ ComplexMatrix2.hermitianTraceless := by
  have htr : Matrix.trace X = 0 := h
  refine ⟨?_, ?_⟩
  · unfold antiHermPart
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      ← neg_sub, smul_neg, ← neg_smul]
    congr 1
    simp
    ring
  · show Matrix.trace _ = 0
    unfold antiHermPart
    rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose, htr]
    simp
end
section
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ c, x c • ComplexMatrix2.pauliFamily c) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_ofReal_smul_pauliFamily_mem (x : Fin 3 → ℝ) :
    ∑ a, (x a : ℂ) • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.real_pauli_sum_mem_hermitianTraceless <;> assumption
theorem sum_re_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ∑ a, (((pauliCoeff a X).re : ℝ) : ℂ) • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ExpChartFunctionalProof.realPauliCombo_re_pauliCoeff <;> assumption
def pauliCoordFunctions (σ : Type) :
    (Fin 3 × σ → ℝ) ≃ₗ[ℝ] GroupLieProduct.hermitianTracelessFunctions σ where
  toFun x := ⟨fun s => ∑ a, (x (a, s) : ℂ) • ComplexMatrix2.pauliFamily a,
    fun s _ => sum_ofReal_smul_pauliFamily_mem fun a => x (a, s)⟩
  map_add' x x' := by
    apply Subtype.ext
    funext s
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' t x := by
    apply Subtype.ext
    funext s
    ext i j
    simp [Matrix.sum_apply, Finset.mul_sum, mul_assoc]
  invFun X p := (pauliCoeff p.1 ((X : σ → ComplexMatrix2) p.2)).re
  left_inv x := by
    funext p
    have hc := pauliCoeff_sum_smul (fun a => (x (a, p.2) : ℂ)) p.1
    simp only [hc, Complex.ofReal_re]
  right_inv X := by
    apply Subtype.ext
    funext s
    exact sum_re_pauliCoeff_smul (X.2 s (mem_univ s))
end
section
variable {L n k j : ℕ}
theorem isPos_or_opposite_isPos (e : Edge L n k j) :
    e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem not_opposite_isPos (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) (e : Edge L n k j) (h : e.IsPositivelyOriented) :
    ¬ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p24505 <;> assumption
theorem edgeFormOfPositiveValues_of_pos (w : PositiveEdge L n k j → ComplexMatrix2)
    {e : Edge L n k j} (h : e.IsPositivelyOriented) :
    edgeFormOfPositiveValues w e = w ⟨e, h⟩ := by
  simp [edgeFormOfPositiveValues, h]
theorem edgeFormOfPositiveValues_of_not_pos (w : PositiveEdge L n k j → ComplexMatrix2)
    {e : Edge L n k j} (h : ¬ e.IsPositivelyOriented) :
    edgeFormOfPositiveValues w e =
      -w ⟨e.opposite, (isPos_or_opposite_isPos e).resolve_left h⟩ := by
  simp [edgeFormOfPositiveValues, h, (isPos_or_opposite_isPos e).resolve_left h]
theorem edgeFormOfPositiveValues_restrict (A : edgeFormSpace L n k j) :
    edgeFormOfPositiveValues (restrictToPositiveEdges (A : Edge L n k j → ComplexMatrix2)) = A := by apply _root_.YangMills.Construction.Tower.ExpChartFunctionalProof.edgeFormOfPositiveValues_restrict <;> assumption
def edgeFormEquivFunctions (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) :
    edgeFormSpace L n k j ≃ₗ[ℝ]
      GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k j) where
  toFun A := ⟨restrictToPositiveEdges (A : Edge L n k j → ComplexMatrix2),
    fun e _ => A.2.1 e.1 e.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨edgeFormOfPositiveValues (w : PositiveEdge L n k j → ComplexMatrix2), by
    refine ⟨fun e he => ?_, fun e => ?_⟩
    · rw [edgeFormOfPositiveValues_of_pos _ he]
      exact w.2 _ (mem_univ _)
    · by_cases h : e.IsPositivelyOriented
      · rw [edgeFormOfPositiveValues_of_not_pos _ (not_opposite_isPos hL hn hj e h),
          edgeFormOfPositiveValues_of_pos _ h]
        rfl
      · rw [edgeFormOfPositiveValues_of_pos _ ((isPos_or_opposite_isPos e).resolve_left h),
          edgeFormOfPositiveValues_of_not_pos _ h, neg_neg]⟩
  left_inv A := Subtype.ext (edgeFormOfPositiveValues_restrict A)
  right_inv w := by
    apply Subtype.ext
    funext p
    exact edgeFormOfPositiveValues_of_pos _ p.2
def edgeFormPauliCoords (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) : edgeFormSpace L n k j ≃ₗ[ℝ] (Fin 3 × PositiveEdge L n k j → ℝ) :=
  (edgeFormEquivFunctions hL hn hj).trans (pauliCoordFunctions _).symm
def fieldTripleCoordEquiv (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    FieldTriple L n k ≃ₗ[ℝ] (FieldTripleIndex L n k → ℝ) :=
  (((edgeFormPauliCoords hL hn (Nat.zero_le k)).prodCongr
      ((edgeFormPauliCoords hL hn (Nat.zero_le k)).prodCongr
        (edgeFormPauliCoords hL hn le_rfl))).trans
    ((LinearEquiv.refl ℝ _).prodCongr (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm)).trans
  (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm
theorem fieldTripleCoordEquiv_apply (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (x : FieldTriple L n k) : fieldTripleCoordEquiv hL hn x = fieldTripleCoords x := by
  funext i
  rcases i with i | i | i <;> rfl
end
section
variable {L n k j : ℕ}
def complexify (A : edgeFormSpace L n k j) : complexEdgeForms L n k j :=
  ⟨A, fun e he => (A.2.1 e he).2, A.2.2⟩
def hermForm (A : complexEdgeForms L n k j) : edgeFormSpace L n k j :=
  ⟨fun e => hermPart ((A : Edge L n k j → ComplexMatrix2) e),
    fun e he => hermPart_mem (A.2.1 e he),
    fun e => by
      show hermPart ((A : Edge L n k j → ComplexMatrix2) e.opposite) = _
      rw [A.2.2 e, hermPart_neg]⟩
def antiHermForm (A : complexEdgeForms L n k j) : edgeFormSpace L n k j :=
  ⟨fun e => antiHermPart ((A : Edge L n k j → ComplexMatrix2) e),
    fun e he => antiHermPart_mem (A.2.1 e he),
    fun e => by
      show antiHermPart ((A : Edge L n k j → ComplexMatrix2) e.opposite) = _
      rw [A.2.2 e, antiHermPart_neg]⟩
def ofRealField (x : RealPeriodicField L n k) : PeriodicField L n k :=
  (complexify x.1, complexify x.2.1, complexify x.2.2)
def hermField (ζ : PeriodicField L n k) : RealPeriodicField L n k :=
  (hermForm ζ.1, hermForm ζ.2.1, hermForm ζ.2.2)
def antiHermField (ζ : PeriodicField L n k) : RealPeriodicField L n k :=
  (antiHermForm ζ.1, antiHermForm ζ.2.1, antiHermForm ζ.2.2)
theorem eq_ofRealField {ζ : PeriodicField L n k} {x : RealPeriodicField L n k}
    (h : ζ.RealizedBy x) : ζ = ofRealField x :=
  Prod.ext (Subtype.ext h.1) (Prod.ext (Subtype.ext h.2.1) (Subtype.ext h.2.2))
theorem eq_complexify_hermForm_add (A : complexEdgeForms L n k j) :
    A = complexify (hermForm A) + Complex.I • complexify (antiHermForm A) := by
  apply Subtype.ext
  funext e
  exact (hermPart_add_I_smul_antiHermPart _).symm
theorem eq_ofRealField_hermField_add (ζ : PeriodicField L n k) :
    ζ = ofRealField (hermField ζ) + Complex.I • ofRealField (antiHermField ζ) :=
  Prod.ext (eq_complexify_hermForm_add _)
    (Prod.ext (eq_complexify_hermForm_add _) (eq_complexify_hermForm_add _))
theorem hermForm_add (A A' : complexEdgeForms L n k j) :
    hermForm (A + A') = hermForm A + hermForm A' :=
  Subtype.ext (funext fun _ => hermPart_add _ _)
theorem antiHermForm_add (A A' : complexEdgeForms L n k j) :
    antiHermForm (A + A') = antiHermForm A + antiHermForm A' :=
  Subtype.ext (funext fun _ => antiHermPart_add _ _)
theorem hermForm_smul (c : ℂ) (A : complexEdgeForms L n k j) :
    hermForm (c • A) = c.re • hermForm A - c.im • antiHermForm A :=
  Subtype.ext (funext fun _ => hermPart_smul _ _)
theorem antiHermForm_smul (c : ℂ) (A : complexEdgeForms L n k j) :
    antiHermForm (c • A) = c.re • antiHermForm A + c.im • hermForm A :=
  Subtype.ext (funext fun _ => antiHermPart_smul _ _)
theorem edgeForm_apply_eq_conjTranspose (A : edgeFormSpace L n k j) (e : Edge L n k j) :
    (A : Edge L n k j → ComplexMatrix2) e =
      ((A : Edge L n k j → ComplexMatrix2) e).conjTranspose := by
  rcases isPos_or_opposite_isPos e with h | h
  · exact (A.2.1 e h).1
  · have hopp : (A : Edge L n k j → ComplexMatrix2) e.opposite =
        -(A : Edge L n k j → ComplexMatrix2) e := A.2.2 e
    have hh := (A.2.1 e.opposite h).1
    have he : (A : Edge L n k j → ComplexMatrix2) e =
        -(A : Edge L n k j → ComplexMatrix2) e.opposite := by
      rw [hopp, neg_neg]
    rw [he, Matrix.conjTranspose_neg, ← hh]
theorem hermForm_complexify (A : edgeFormSpace L n k j) : hermForm (complexify A) = A :=
  Subtype.ext (funext fun e =>
    (hermPart_antiHermPart_of_eq_conjTranspose (edgeForm_apply_eq_conjTranspose A e)).1)
theorem antiHermForm_complexify (A : edgeFormSpace L n k j) : antiHermForm (complexify A) = 0 :=
  Subtype.ext (funext fun e =>
    (hermPart_antiHermPart_of_eq_conjTranspose (edgeForm_apply_eq_conjTranspose A e)).2)
theorem hermField_add (ζ ζ' : PeriodicField L n k) :
    hermField (ζ + ζ') = hermField ζ + hermField ζ' :=
  Prod.ext (hermForm_add _ _) (Prod.ext (hermForm_add _ _) (hermForm_add _ _))
theorem antiHermField_add (ζ ζ' : PeriodicField L n k) :
    antiHermField (ζ + ζ') = antiHermField ζ + antiHermField ζ' :=
  Prod.ext (antiHermForm_add _ _) (Prod.ext (antiHermForm_add _ _) (antiHermForm_add _ _))
theorem hermField_smul (c : ℂ) (ζ : PeriodicField L n k) :
    hermField (c • ζ) = c.re • hermField ζ - c.im • antiHermField ζ :=
  Prod.ext (hermForm_smul _ _) (Prod.ext (hermForm_smul _ _) (hermForm_smul _ _))
theorem antiHermField_smul (c : ℂ) (ζ : PeriodicField L n k) :
    antiHermField (c • ζ) = c.re • antiHermField ζ + c.im • hermField ζ :=
  Prod.ext (antiHermForm_smul _ _) (Prod.ext (antiHermForm_smul _ _) (antiHermForm_smul _ _))
theorem hermField_ofRealField (x : RealPeriodicField L n k) : hermField (ofRealField x) = x :=
  Prod.ext (hermForm_complexify _)
    (Prod.ext (hermForm_complexify _) (hermForm_complexify _))
theorem antiHermField_ofRealField (x : RealPeriodicField L n k) :
    antiHermField (ofRealField x) = 0 :=
  Prod.ext (antiHermForm_complexify _)
    (Prod.ext (antiHermForm_complexify _) (antiHermForm_complexify _))
end
section
variable {L n k : ℕ}
theorem matExp_mul_matExp_neg (Z : ComplexMatrix2) :
    ComplexMatrix2.matExp Z * ComplexMatrix2.matExp (-Z) = 1 := by apply _root_.YangMills.Construction.SpinHarmonics.matExp_mul_matExp_neg <;> assumption
theorem expForm_eq_expGaugeField (Y : edgeFormSpace L n k 0) :
    IdentityExpChart.expForm (Y : Edge L n k 0 → ComplexMatrix2) =
      PeriodicLattice.expGaugeField (Y : Edge L n k 0 → ComplexMatrix2) := by
  funext e
  unfold IdentityExpChart.expForm PeriodicLattice.expTwist PeriodicLattice.expGaugeField
  by_cases h : e.IsPositivelyOriented
  · simp [h]
  · simp only [h, if_false, Pi.one_apply, mul_one]
    have hopp : (Y : Edge L n k 0 → ComplexMatrix2) e.opposite =
        -(Y : Edge L n k 0 → ComplexMatrix2) e := Y.2.2 e
    rw [hopp, smul_neg]
    exact Matrix.inv_eq_left_inv (matExp_mul_matExp_neg _)
theorem fieldFunctional_eq_inCoords (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (x : RealPeriodicField L n k) :
    fieldFunctional x = expChartFunctionalInCoords L n k (fieldTripleCoords x) := by
  have hinj : Function.Injective (fieldTripleCoords (L := L) (m := n) (k := k)) := by
    intro y y' h
    apply (fieldTripleCoordEquiv hL hn).injective
    simpa [fieldTripleCoordEquiv_apply] using h
  have hc := congrArg expChartFunctional (Function.leftInverse_invFun hinj x)
  unfold fieldFunctional
  rw [expForm_eq_expGaugeField]
  exact hc.symm
variable [Fintype (PositiveEdge L n k 0)] [Fintype (PositiveEdge L n k k)]
theorem contDiffAt_inCoords_zero (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hfin : FiniteDimensional ℝ (FieldTriple L n k))
    (hexp : ExpChartFunctionalExpansion L n k) :
    ContDiffAt ℝ ∞ (expChartFunctionalInCoords L n k) 0 := by
  obtain ⟨U, hU⟩ := hexp.exists_nhd
  have hcont : Continuous (fieldTripleCoordEquiv (k := k) hL hn).symm :=
    (fieldTripleCoordEquiv (k := k) hL hn).symm.toLinearMap.continuous_of_finiteDimensional
  have hzero : fieldTripleCoords (0 : FieldTriple L n k) = 0 := by
    rw [← fieldTripleCoordEquiv_apply hL hn, map_zero]
  have hinv : ∀ y : FieldTriple L n k,
      (fieldTripleCoordEquiv hL hn).symm (fieldTripleCoords y) = y := by
    intro y
    rw [← fieldTripleCoordEquiv_apply hL hn]
    simp
  have hopen : IsOpen (fieldTripleCoords '' U) := by
    have himg : fieldTripleCoords '' U = (fieldTripleCoordEquiv hL hn).symm ⁻¹' U := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [hinv y] using hy
      · intro hz
        refine ⟨_, hz, ?_⟩
        rw [← fieldTripleCoordEquiv_apply hL hn]
        simp
    rw [himg]
    exact hU.1.preimage hcont
  exact hU.2.2.2.2.contDiffAt (hopen.mem_nhds ⟨0, hU.2.1, hzero⟩)
theorem fieldFunctionalSecondDeriv_eq (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hf : ContDiffAt ℝ ∞ (expChartFunctionalInCoords L n k) 0)
    (x x' : RealPeriodicField L n k) :
    fieldFunctionalSecondDeriv L n k x x' = expChartSecondDeriv x x' := by
  have hplane : ∀ s t : ℝ, fieldFunctional (s • x + t • x') =
      expChartFunctionalInCoords L n k
        (s • fieldTripleCoords x + t • fieldTripleCoords x') := by
    intro s t
    rw [fieldFunctional_eq_inCoords hL hn]
    simp only [← fieldTripleCoordEquiv_apply hL hn, map_add, map_smul]
  unfold fieldFunctionalSecondDeriv expChartSecondDeriv
  simp only [hplane]
  exact deriv_deriv_smul_add_eq_fderiv_fderiv hf _ _
theorem hessianAndComplexExtension (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hfin : FiniteDimensional ℝ (FieldTriple L n k))
    (hexp : ExpChartFunctionalExpansion L n k) :
    HessianAndComplexExtension L n k := by
  have hf := contDiffAt_inCoords_zero hL hn hfin hexp
  have hagree := fieldFunctionalSecondDeriv_eq (L := L) (n := n) (k := k) hL hn hf
  obtain ⟨B, hB, hBs⟩ := hexp.symmetric
  have hval : ∀ x x' : RealPeriodicField L n k, B x x' = fieldFunctionalSecondDeriv L n k x x' :=
    fun x x' => (hB x x').trans (hagree x x').symm
  have hex : ∃ β, IsComplexSecondDeriv L n k β := by
    obtain ⟨β, hβ⟩ := exists_complexBilin_extension ofRealField hermField antiHermField
      hermField_add antiHermField_add hermField_smul antiHermField_smul hermField_ofRealField
      antiHermField_ofRealField B
    refine ⟨β, fun ζ ζ' x x' h h' => ?_⟩
    rw [eq_ofRealField h, eq_ofRealField h', hβ, hval]
  have hext : IsComplexSecondDeriv L n k (complexSecondDeriv L n k) :=
    Classical.epsilon_spec hex
  refine ⟨hagree, ⟨B, hval, hBs⟩, hext, ?_⟩
  refine bilin_symm_of_symm_on_real ofRealField hermField antiHermField
    eq_ofRealField_hermField_add _ ?_
  intro x x'
  have h₁ := hext (ofRealField x) (ofRealField x') x x' ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  have h₂ := hext (ofRealField x') (ofRealField x) x' x ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  rw [h₁, h₂, ← hval, ← hval, hBs]
end
end HessianExtension
theorem hessianAndComplexExtensionHolds_of_expChartFunctionalClaim
    (hclaim : ExpChartFunctionalClaim) : HessianAndComplexExtensionHolds := by
  intro L n k hL hn hk _ _
  obtain ⟨hfin, hexp⟩ := hclaim L n k hL hn hk
  exact HessianExtension.hessianAndComplexExtension hL hn hfin hexp
end Tower
end YangMills.Construction
end
