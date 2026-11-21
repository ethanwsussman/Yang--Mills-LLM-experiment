import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Towers.FirstDifferentialInTheExponentialChartVanishes
import YangMills.Construction.Towers.FunctionalInTheBackgroundGaugeIsGaugeInvariant
import YangMills.Construction.Towers.LinearMapsOnTheRealSpacesProof
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnASideProof
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
namespace Tower
namespace FirstDerivVanishing
def pauliQuaternion : Fin 3 → ComplexMatrix2 :=
  ![!![0, Complex.I; Complex.I, 0], !![0, 1; -1, 0], !![Complex.I, 0; 0, -Complex.I]]
theorem pauliQuaternion_mul_self (a : Fin 3) : pauliQuaternion a * pauliQuaternion a = -1 := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [pauliQuaternion, Matrix.mul_apply, Fin.sum_univ_two]
theorem pauliQuaternion_conjTranspose (a : Fin 3) :
    (pauliQuaternion a).conjTranspose = -pauliQuaternion a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [pauliQuaternion, Matrix.conjTranspose_apply]
theorem pauliQuaternion_det (a : Fin 3) : (pauliQuaternion a).det = 1 := by
  rw [Matrix.det_fin_two]
  fin_cases a <;> simp [pauliQuaternion]
theorem pauliQuaternion_mem_compactGaugeGroup (a : Fin 3) :
    pauliQuaternion a ∈ PeriodicLattice.compactGaugeGroup := by
  refine Matrix.mem_specialUnitaryGroup_iff.2 ⟨?_, pauliQuaternion_det a⟩
  refine Matrix.mem_unitaryGroup_iff.2 ?_
  rw [Matrix.star_eq_conjTranspose, pauliQuaternion_conjTranspose, mul_neg, pauliQuaternion_mul_self,
    neg_neg]
theorem pauliQuaternion_inv (a : Fin 3) : (pauliQuaternion a)⁻¹ = -pauliQuaternion a :=
  Matrix.inv_eq_right_inv (by rw [mul_neg, pauliQuaternion_mul_self, neg_neg])
theorem conjugateBy_pauliQuaternion (a : Fin 3) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (pauliQuaternion a) X = -(pauliQuaternion a * X * pauliQuaternion a) := by
  rw [ComplexMatrix2.conjugateBy, pauliQuaternion_inv, mul_neg]
theorem conjugateBy_pauliQuaternion_mem (a : Fin 3) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy (pauliQuaternion a) X ∈ ComplexMatrix2.hermitianTraceless := by
  obtain ⟨hH, ht⟩ := hX
  refine ⟨?_, ?_⟩
  · rw [conjugateBy_pauliQuaternion, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, pauliQuaternion_conjTranspose, ← hH]
    simp [mul_assoc]
  · have h : Matrix.trace (pauliQuaternion a * X * pauliQuaternion a) =
        -Matrix.trace X := by
      rw [Matrix.trace_mul_comm, ← mul_assoc, pauliQuaternion_mul_self]
      simp
    show Matrix.trace _ = 0
    rw [conjugateBy_pauliQuaternion, Matrix.trace_neg, h, neg_neg]
    exact ht
theorem add_conjugateBy_pauliRotations_eq_zero {X : ComplexMatrix2} (hX : Matrix.trace X = 0) :
    X + ComplexMatrix2.conjugateBy (pauliQuaternion 0) X + ComplexMatrix2.conjugateBy (pauliQuaternion 1) X +
      ComplexMatrix2.conjugateBy (pauliQuaternion 2) X = 0 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℂ, X = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two X⟩
  rw [Matrix.trace_fin_two] at hX
  simp only [conjugateBy_pauliQuaternion]
  have hd : d = -a := by
    have h : a + d = 0 := by simpa using hX
    linear_combination h
  subst hd
  simp only [pauliQuaternion, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf <;> simp
theorem conjugateBy_neg (g X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (-X) = -ComplexMatrix2.conjugateBy g X := by
  simp [ComplexMatrix2.conjugateBy]
theorem conjugateBy_real_smul (g : ComplexMatrix2) (t : ℝ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (t • X) = t • ComplexMatrix2.conjugateBy g X := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.conjugateBy_real_smul <;> assumption
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
theorem pauliCoeff_real_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) (t : ℝ)
    (a : Fin 3) : pauliCoeff a (t • X) = (t : ℂ) * pauliCoeff a X := by
  have e : t • X = (t : ℂ) • X := by
    ext i j
    simp
  have hs : (t : ℂ) • X ∈ ComplexMatrix2.traceless := ComplexMatrix2.traceless.smul_mem _ hX
  unfold pauliCoeff
  rw [e, dif_pos hX, dif_pos hs]
  exact congrFun (map_smul OneLoop.pauliCoordinateEquiv (t : ℂ) ⟨X, hX⟩) a
theorem pauliCoeff_re {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    (pauliCoeff 0 X).re = (X 0 1).re ∧ (pauliCoeff 1 X).re = -(X 0 1).im ∧
      (pauliCoeff 2 X).re = (X 0 0).re := by
  have hs : X ∈ ComplexMatrix2.traceless := hX.2
  have h10 : X 1 0 = star (X 0 1) := congrFun (congrFun hX.1 1) 0
  unfold pauliCoeff
  rw [dif_pos hs, dif_pos hs, dif_pos hs]
  refine ⟨?_, ?_, ?_⟩
  · show (((X 0 1 + X 1 0) / 2 : ℂ)).re = _
    rw [h10]
    simp
  · show (((X 1 0 - X 0 1) / (2 * Complex.I) : ℂ)).re = _
    rw [h10]
    simp [Complex.div_re, Complex.normSq_apply]
    ring
  · rfl
theorem eq_of_pauliCoeff_re {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless)
    (h : ∀ a, (pauliCoeff a X).re = (pauliCoeff a Y).re) : X = Y := by
  obtain ⟨x0, x1, x2⟩ := pauliCoeff_re hX
  obtain ⟨y0, y1, y2⟩ := pauliCoeff_re hY
  have e01 : X 0 1 = Y 0 1 :=
    Complex.ext (by rw [← x0, ← y0, h 0]) (by linarith [h 1])
  have e10 : X 1 0 = Y 1 0 := by
    rw [show X 1 0 = star (X 0 1) from congrFun (congrFun hX.1 1) 0,
      show Y 1 0 = star (Y 0 1) from congrFun (congrFun hY.1 1) 0, e01]
  have im : ∀ {Z : ComplexMatrix2}, Z ∈ ComplexMatrix2.hermitianTraceless → (Z 0 0).im = 0 := by
    intro Z hZ
    exact Complex.conj_eq_iff_im.1 (congrFun (congrFun hZ.1 0) 0).symm
  have e00 : X 0 0 = Y 0 0 :=
    Complex.ext (by rw [← x2, ← y2, h 2]) (by rw [im hX, im hY])
  have tr : ∀ {Z : ComplexMatrix2}, Z ∈ ComplexMatrix2.hermitianTraceless → Z 1 1 = -Z 0 0 := by
    intro Z hZ
    have h := hZ.2
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] at h
    linear_combination h
  ext i j
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e10
  · show X 1 1 = Y 1 1
    rw [tr hX, tr hY, e00]
variable {L n k j : ℕ}
theorem edgeForm_mem (hO : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (B : edgeFormSpace L n k j) (b : Edge L n k j) :
    (B : Edge L n k j → ComplexMatrix2) b ∈ ComplexMatrix2.hermitianTraceless := by
  rcases hO b with ⟨hp, -⟩ | ⟨hp, -⟩
  · exact B.2.1 b hp
  · have h1 : (B : Edge L n k j → ComplexMatrix2) b.opposite ∈ ComplexMatrix2.hermitianTraceless :=
      B.2.1 _ hp
    rw [B.2.2 b] at h1
    simpa using ComplexMatrix2.hermitianTraceless.neg_mem h1
def conjEdgeForm (a : Fin 3) (B : edgeFormSpace L n k j) : edgeFormSpace L n k j :=
  ⟨fun b => ComplexMatrix2.conjugateBy (pauliQuaternion a) ((B : Edge L n k j → ComplexMatrix2) b),
    fun b hb => conjugateBy_pauliQuaternion_mem a (B.2.1 b hb), fun b => by
      show ComplexMatrix2.conjugateBy _ ((B : Edge L n k j → ComplexMatrix2) b.opposite) = _
      rw [B.2.2 b, conjugateBy_neg]⟩
theorem adjointForm_const (a : Fin 3) (B : edgeFormSpace L n k j) :
    adjointForm (fun _ => pauliQuaternion a) (B : Edge L n k j → ComplexMatrix2) = conjEdgeForm a B := by
  funext b
  unfold adjointForm extendOddly
  by_cases h : b.IsPositivelyOriented
  · simp only [if_pos h]
    rfl
  · simp only [if_neg h]
    rw [B.2.2 b, conjugateBy_neg, neg_neg]
    rfl
theorem conjEdgeForm_smul (a : Fin 3) (t : ℝ) (B : edgeFormSpace L n k j) :
    conjEdgeForm a (t • B) = t • conjEdgeForm a B := by
  apply Subtype.ext
  funext b
  exact conjugateBy_real_smul _ _ _
def conjugateTriple (a : Fin 3) (x : FieldTriple L n k) : FieldTriple L n k :=
  (conjEdgeForm a x.1, conjEdgeForm a x.2.1, conjEdgeForm a x.2.2)
theorem conjugateTriple_smul (a : Fin 3) (t : ℝ) (x : FieldTriple L n k) :
    conjugateTriple a (t • x) = t • conjugateTriple a x := by
  simp only [conjugateTriple, Prod.smul_fst, Prod.smul_snd, conjEdgeForm_smul, Prod.smul_mk]
theorem add_reversedEdgeForms_eq_zero
    (hO : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (B : edgeFormSpace L n k j) :
    B + conjEdgeForm 0 B + conjEdgeForm 1 B + conjEdgeForm 2 B = 0 := by
  apply Subtype.ext
  funext b
  exact add_conjugateBy_pauliRotations_eq_zero (edgeForm_mem hO B b).2
theorem add_reversedTriples_eq_zero
    (h₀ : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hk : ∀ b : Edge L n k k, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (x : FieldTriple L n k) :
    x + conjugateTriple 0 x + conjugateTriple 1 x + conjugateTriple 2 x = 0 := by
  refine Prod.ext (add_reversedEdgeForms_eq_zero h₀ x.1) (Prod.ext (add_reversedEdgeForms_eq_zero h₀ x.2.1) ?_)
  exact add_reversedEdgeForms_eq_zero hk x.2.2
theorem edgeCoeffs_add (B B' : edgeFormSpace L n k j) (ι : Fin 3 × PositiveEdge L n k j) :
    (toPauliCoeffs (restrictToPositiveEdges
        ((B + B' : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2)) ι).re =
      (toPauliCoeffs (restrictToPositiveEdges (B : Edge L n k j → ComplexMatrix2)) ι).re +
        (toPauliCoeffs (restrictToPositiveEdges (B' : Edge L n k j → ComplexMatrix2)) ι).re := by
  have h := pauliCoeff_add (B.2.1 ι.2.1 ι.2.2).2 (B'.2.1 ι.2.1 ι.2.2).2 ι.1
  exact congrArg Complex.re h
theorem edgeCoeffs_smul (t : ℝ) (B : edgeFormSpace L n k j) (ι : Fin 3 × PositiveEdge L n k j) :
    (toPauliCoeffs (restrictToPositiveEdges
        ((t • B : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2)) ι).re =
      t * (toPauliCoeffs (restrictToPositiveEdges (B : Edge L n k j → ComplexMatrix2)) ι).re := by
  have h := pauliCoeff_real_smul (B.2.1 ι.2.1 ι.2.2).2 t ι.1
  exact show (pauliCoeff ι.1 (t • (B : Edge L n k j → ComplexMatrix2) ι.2.1)).re =
      t * (pauliCoeff ι.1 ((B : Edge L n k j → ComplexMatrix2) ι.2.1)).re from by
    rw [h]
    simp
theorem edgeForm_ext
    (hO : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {B B' : edgeFormSpace L n k j}
    (h : ∀ ι, (toPauliCoeffs (restrictToPositiveEdges (B : Edge L n k j → ComplexMatrix2)) ι).re =
      (toPauliCoeffs (restrictToPositiveEdges (B' : Edge L n k j → ComplexMatrix2)) ι).re) :
    B = B' := by
  apply Subtype.ext
  funext b
  rcases hO b with ⟨hp, -⟩ | ⟨hp, -⟩
  · exact eq_of_pauliCoeff_re (B.2.1 b hp) (B'.2.1 b hp) fun a => h (a, ⟨b, hp⟩)
  · have e := eq_of_pauliCoeff_re (B.2.1 _ hp) (B'.2.1 _ hp) fun a => h (a, ⟨b.opposite, hp⟩)
    rw [B.2.2 b, B'.2.2 b] at e
    exact neg_injective e
theorem fieldTripleCoords_add (x y : FieldTriple L n k) :
    fieldTripleCoords (x + y) = fieldTripleCoords x + fieldTripleCoords y := by
  funext i
  rcases i with i | i | i
  · exact edgeCoeffs_add x.1 y.1 i
  · exact edgeCoeffs_add x.2.1 y.2.1 i
  · exact edgeCoeffs_add x.2.2 y.2.2 i
theorem fieldTripleCoords_smul (t : ℝ) (x : FieldTriple L n k) :
    fieldTripleCoords (t • x) = t • fieldTripleCoords x := by
  funext i
  rcases i with i | i | i
  · exact edgeCoeffs_smul t x.1 i
  · exact edgeCoeffs_smul t x.2.1 i
  · exact edgeCoeffs_smul t x.2.2 i
theorem fieldTripleCoords_zero : fieldTripleCoords (0 : FieldTriple L n k) = 0 := by
  have h := fieldTripleCoords_smul (L := L) (n := n) (k := k) 0 0
  simpa using h
theorem fieldTripleCoords_injective
    (h₀ : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hk : ∀ b : Edge L n k k, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    Function.Injective (fieldTripleCoords (L := L) (m := n) (k := k)) := by
  intro x y h
  refine Prod.ext (edgeForm_ext h₀ fun ι => ?_) (Prod.ext (edgeForm_ext h₀ fun ι => ?_)
    (edgeForm_ext hk fun ι => ?_))
  · exact congrFun h (.inl ι)
  · exact congrFun h (.inr (.inl ι))
  · exact congrFun h (.inr (.inr ι))
theorem continuous_matExp : Continuous (fun X : ComplexMatrix2 => ComplexMatrix2.matExp X) := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.continuous_matExp <;> assumption
theorem expGaugeField_mem (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    (h₀ : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (B : edgeFormSpace L n k 0) :
    PeriodicLattice.expGaugeField (B : Edge L n k 0 → ComplexMatrix2) ∈ fieldSpace L n k 0 := by
  refine ⟨fun b _ => (hI.1 _ (edgeForm_mem h₀ B b)).2.2.2, fun b _ => ?_⟩
  change ComplexMatrix2.matExp (Complex.I • (B : Edge L n k 0 → ComplexMatrix2) b.opposite) =
    (ComplexMatrix2.matExp (Complex.I • (B : Edge L n k 0 → ComplexMatrix2) b))⁻¹
  rw [B.2.2 b, smul_neg, ComplexMatrix2.matExp, ComplexMatrix2.matExp, Matrix.exp_neg]
theorem tendsto_expGaugeField (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    (h₀ : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (x : FieldTriple L n k) :
    Tendsto (fun t : ℝ =>
        PeriodicLattice.expGaugeField
          (((t • x).1 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2))
      (𝓝 0) (𝓝[fieldSpace L n k 0] fun _ => (1 : ComplexMatrix2)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun t => expGaugeField_mem hI h₀ _⟩
  refine tendsto_pi_nhds.2 fun b => ?_
  have hc : Continuous fun t : ℝ =>
      ComplexMatrix2.matExp (Complex.I • (t • (x.1 : Edge L n k 0 → ComplexMatrix2) b)) :=
    continuous_matExp.comp ((continuous_id.smul continuous_const).const_smul Complex.I)
  have h := hc.tendsto 0
  have e : ComplexMatrix2.matExp
      (Complex.I • ((0 : ℝ) • (x.1 : Edge L n k 0 → ComplexMatrix2) b)) = 1 := by
    simp [ComplexMatrix2.matExp]
  rw [e] at h
  exact h
theorem gaugeTransform_expGaugeField (a : Fin 3) (B : edgeFormSpace L n k 0) :
    PeriodicLattice.gaugeTransform (fun _ => pauliQuaternion a)
        (PeriodicLattice.expGaugeField (B : Edge L n k 0 → ComplexMatrix2)) =
      PeriodicLattice.expGaugeField
        ((conjEdgeForm a B : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) := by
  funext b
  have hu : IsUnit (pauliQuaternion a) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (by rw [pauliQuaternion_det]; exact isUnit_one)
  show pauliQuaternion a * ComplexMatrix2.matExp (Complex.I • (B : Edge L n k 0 → ComplexMatrix2) b) *
      (pauliQuaternion a)⁻¹ =
    ComplexMatrix2.matExp
      (Complex.I • ComplexMatrix2.conjugateBy (pauliQuaternion a) ((B : Edge L n k 0 → ComplexMatrix2) b))
  rw [ComplexMatrix2.matExp, ComplexMatrix2.matExp, ← Matrix.exp_conj _ _ hu]
  simp [ComplexMatrix2.conjugateBy, mul_assoc]
section Differential
variable [Fintype (PositiveEdge L n k 0)] [Fintype (PositiveEdge L n k k)]
theorem hasDerivAt_expChartFunctional_line
    (hinj : Function.Injective (fieldTripleCoords (L := L) (m := n) (k := k)))
    (hd : DifferentiableAt ℝ (expChartFunctionalInCoords L n k) 0) (x : FieldTriple L n k) :
    HasDerivAt (fun t : ℝ => expChartFunctional (t • x)) (expChartFirstDeriv x) 0 := by
  have hl : HasDerivAt (fun t : ℝ => t • fieldTripleCoords x) (fieldTripleCoords x) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (fieldTripleCoords x)
  have hf : HasFDerivAt (expChartFunctionalInCoords L n k)
      (fderiv ℝ (expChartFunctionalInCoords L n k) 0)
      ((0 : ℝ) • fieldTripleCoords x) := by
    rw [zero_smul]
    exact hd.hasFDerivAt
  have h := hf.comp_hasDerivAt (0 : ℝ) hl
  have e : (expChartFunctionalInCoords L n k ∘ fun t : ℝ => t • fieldTripleCoords x) =
      fun t : ℝ => expChartFunctional (t • x) := by
    funext t
    show expChartFunctional
      (Function.invFun fieldTripleCoords (t • fieldTripleCoords x)) = _
    rw [← fieldTripleCoords_smul, Function.leftInverse_invFun hinj]
  rw [e] at h
  exact h
theorem expChartFunctional_rotate_eventuallyEq (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    (h₀ : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hinv : ForGaugesNearOneOrConstant (L := L) (n := n) (k := k) (j := 0)
      BackgroundFunctionalGaugeInvariant)
    {W : Set (FieldTriple L n k)} (hW : IsExpChartNhd W) (a : Fin 3)
    (x : FieldTriple L n k) :
    (fun t : ℝ => expChartFunctional (t • conjugateTriple a x)) =ᶠ[𝓝 0]
      fun t : ℝ => expChartFunctional (t • x) := by
  have hline : Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => t • x := continuous_id.smul continuous_const
    simpa using hc.tendsto 0
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, t • x ∈ W := hline.eventually (hW.1.mem_nhds hW.2.1)
  have hP := (tendsto_expGaugeField hI h₀ x).eventually hinv.2
  filter_upwards [hmem, hP] with t ht hp
  obtain ⟨J', μ', hJ, hμ, -, he⟩ := hp (fun _ => pauliQuaternion a)
    (fun _ => pauliQuaternion_mem_compactGaugeGroup a) (fun _ _ => rfl) (t • x).2.1 (t • x).2.2
    (hW.2.2.1 _ ht)
  have eJ : J' = conjEdgeForm a (t • x).2.1 :=
    Subtype.ext (hJ.trans (adjointForm_const a _))
  have eμ : μ' = conjEdgeForm a (t • x).2.2 :=
    Subtype.ext (hμ.trans (adjointForm_const a _))
  rw [← conjugateTriple_smul]
  subst eJ eμ
  rw [gaugeTransform_expGaugeField] at he
  exact he
end Differential
end FirstDerivVanishing
open FirstDerivVanishing in
theorem expChartFirstDeriv_vanishes_of_claims
    (hU : ExpChartFunctionalClaim)
    (hInv : BackgroundFunctionalIsGaugeInvariant)
    (hO : PeriodicLattice.LevelBondOrientationDichotomy)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) :
    ExpChartFirstDerivVanishes := by
  intro L n k hL hn hk _ _ x
  have h₀ : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => hO L n k hL hn (by omega) 0 (Nat.zero_le k) b
  have hkk : ∀ b : Edge L n k k, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => hO L n k hL hn (by omega) k le_rfl b
  by_cases hd : DifferentiableAt ℝ (expChartFunctionalInCoords L n k) 0
  · have hinj := fieldTripleCoords_injective (L := L) (n := n) (k := k) h₀ hkk
    obtain ⟨W, hW⟩ := ((hU L n k hL hn hk).2).exists_nhd
    have hinv := hInv L n k hL hn hk
    have inv : ∀ a : Fin 3, expChartFirstDeriv (conjugateTriple a x) = expChartFirstDeriv x := fun a =>
      ((hasDerivAt_expChartFunctional_line hinj hd (conjugateTriple a x)).congr_of_eventuallyEq
        (expChartFunctional_rotate_eventuallyEq hI h₀ hinv hW a x).symm).unique
          (hasDerivAt_expChartFunctional_line hinj hd x)
    have hsum := congrArg fieldTripleCoords (add_reversedTriples_eq_zero h₀ hkk x)
    simp only [fieldTripleCoords_add, fieldTripleCoords_zero] at hsum
    have h := congrArg (fderiv ℝ (expChartFunctionalInCoords L n k) 0) hsum
    simp only [map_add, map_zero] at h
    have e : ∀ y : FieldTriple L n k, fderiv ℝ (expChartFunctionalInCoords L n k) 0
        (fieldTripleCoords y) = expChartFirstDeriv y := fun _ => rfl
    simp only [e, inv] at h
    linarith
  · simp [expChartFirstDeriv, fderiv_zero_of_not_differentiableAt hd]
end Tower
end YangMills.Construction
end
