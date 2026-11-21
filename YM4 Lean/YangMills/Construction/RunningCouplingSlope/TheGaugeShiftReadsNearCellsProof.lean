import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Lattice.ActionOfABareGaugeTransformation
import YangMills.Construction.Lattice.AveragingMapIsABorelMapProof
import YangMills.Construction.Lattice.LatticesOfATorusAndTheProductTopologyOfConfigurations
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Matrices.NormExpLogBasicsProof
import YangMills.Construction.Matrices.SpecialUnitaryExpSurjective
import YangMills.Construction.RunningCouplingSlope.IndicesInACellAreBounded
import YangMills.Construction.RunningCouplingSlope.KernelsNearTheCellsAreBounded
import YangMills.Construction.RunningCouplingSlope.MapsOfAFamilyThroughOne
import YangMills.Construction.RunningCouplingSlope.TheFieldsOfTheChainReadNearCells
import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheMovementAndTheDriftReadNearCells
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.StepKernelsNearOneOnASideProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace GaugeCorrectionLocality
open Matrices Tower
section Coefficients
private def pauliCoordLinear (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
  map_add' X Y := by
    fin_cases a <;> simp <;> ring
  map_smul' c X := by
    fin_cases a <;> simp <;> ring
private theorem coeff_eq_linear {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a X = pauliCoordLinear a X := by
  unfold pauliCoeff
  rw [dif_pos hX]
  rfl
private theorem coeff_zero_matrix (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private theorem coeff_analyticOnNhd {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {s : Set P}
    (hs : IsOpen s) {g : P → ComplexMatrix2} (hg : AnalyticOnNhd ℂ g s)
    (hm : ∀ z ∈ s, g z ∈ ComplexMatrix2.traceless)
    (a : Fin 3) : AnalyticOnNhd ℂ (fun z => pauliCoeff a (g z)) s := fun z hz => by
  have h : AnalyticAt ℂ (fun w => LinearMap.toContinuousLinearMap (pauliCoordLinear a) (g w)) z :=
    ((LinearMap.toContinuousLinearMap (pauliCoordLinear a)).analyticAt _).comp (hg z hz)
  refine h.congr ?_
  filter_upwards [hs.mem_nhds hz] with w hw
  exact (coeff_eq_linear (hm w hw) a).symm
private theorem entry_norm_le_opNorm (A : ComplexMatrix2) (a b : Fin 2) : ‖A a b‖ ≤ ‖A‖ := by apply _root_.YangMills.SharedProofs.p14523 <;> assumption
private theorem coeff_norm_le {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    ‖pauliCoeff a X‖ ≤ ‖X‖ := by
  rw [coeff_eq_linear hX]
  have h01 := entry_norm_le_opNorm X 0 1
  have h10 := entry_norm_le_opNorm X 1 0
  have h00 := entry_norm_le_opNorm X 0 0
  fin_cases a
  · show ‖(X 0 1 + X 1 0) / 2‖ ≤ ‖X‖
    rw [norm_div]
    have := norm_add_le (X 0 1) (X 1 0)
    simp only [Complex.norm_ofNat]
    linarith
  · show ‖(X 1 0 - X 0 1) / (2 * Complex.I)‖ ≤ ‖X‖
    rw [norm_div, norm_mul, Complex.norm_I]
    have := norm_sub_le (X 1 0) (X 0 1)
    simp only [Complex.norm_ofNat]
    linarith
  · exact h00
private theorem pauli_expansion {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    X = ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.NearIdentityStepKernels.eq_sum_pauliCoeff_smul <;> assumption
private theorem eq_zero_of_coeffs {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (h : ∀ a, pauliCoeff a X = 0) : X = 0 := by
  rw [pauli_expansion hX]
  simp [h]
private theorem norm_le_of_coeffs {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (h : ∀ a, ‖pauliCoeff a X‖ ≤ 1) :
    ‖X‖ ≤ ∑ a, ‖ComplexMatrix2.pauliFamily a‖ := by
  have e := congrArg norm (pauli_expansion hX)
  refine e.le.trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_))
  rw [norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (h a)
end Coefficients
section BasisForms
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
  [Fintype (Fin 3 × PositiveEdge L n k k)] [Fintype (GhostCoordIndex L n k)]
  [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
private def basisForm (P : PauliCoordinates L n k) (q : LevelFormIndex L n k) :
    LevelForms L n k :=
  P.formCoords.symm fun q' => if q = q' then 1 else 0
private theorem formCoords_basisForm (P : PauliCoordinates L n k) (q q' : LevelFormIndex L n k) :
    P.formCoords (basisForm P q) q' = if q = q' then 1 else 0 := by
  simp [basisForm]
private theorem basisForm_base (P : PauliCoordinates L n k) (q : LevelFormIndex L n k)
    (a : Fin 3) (b : PositiveEdge L n k 0) :
    pauliCoeff a (((basisForm P q).1 : Edge L n k 0 → ComplexMatrix2) b.1) =
      (((if q = .inl (a, b) then 1 else 0 : ℝ)) : ℂ) := by
  have h := P.formCoords_base (basisForm P q) (a, b)
  rw [formCoords_basisForm] at h
  exact h
private theorem basisForm_level (P : PauliCoordinates L n k) (q : LevelFormIndex L n k) (i : Fin k)
    (a : Fin 3) (b : PositiveEdge L n k (i + 1)) :
    pauliCoeff a (((basisForm P q).2 i : Edge L n k (i + 1) → ComplexMatrix2) b.1) =
      (((if q = .inr ⟨i, (a, b)⟩ then 1 else 0 : ℝ)) : ℂ) := by
  have h := P.formCoords_level (basisForm P q) i (a, b)
  rw [formCoords_basisForm] at h
  exact h
private theorem norm_indicator_le (p : Prop) [Decidable p] :
    ‖(((if p then 1 else 0 : ℝ)) : ℂ)‖ ≤ 1 := by
  split_ifs <;> simp
private theorem mem_traceless_of_mem_hermitian {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.hermitianTraceless) : X ∈ ComplexMatrix2.traceless := h.2
private theorem norm_le_of_positive {j : ℕ} {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) {β : ℝ}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → ‖B b‖ ≤ β) (b : Edge L n k j) :
    ‖B b‖ ≤ β := by
  by_cases hb : b.IsPositivelyOriented
  · exact h b hb
  · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hb
    have e := hB.2 b.opposite
    have e2 : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
    rw [e2] at e
    rw [e, norm_neg]
    exact h _ hr
private theorem basisForm_bounded (P : PauliCoordinates L n k) (q : LevelFormIndex L n k) :
    LevelFormsBounded (∑ a, ‖ComplexMatrix2.pauliFamily a‖) (basisForm P q) where
  bottom_le := norm_le_of_positive (basisForm P q).1.2 fun b hb =>
    norm_le_of_coeffs (mem_traceless_of_mem_hermitian ((basisForm P q).1.2.1 b hb)) fun a => by
      rw [basisForm_base P q a ⟨b, hb⟩]
      exact norm_indicator_le _
  level_le := fun i => norm_le_of_positive ((basisForm P q).2 i).2 fun b hb =>
    norm_le_of_coeffs (mem_traceless_of_mem_hermitian (((basisForm P q).2 i).2.1 b hb)) fun a => by
      rw [basisForm_level P q i a ⟨b, hb⟩]
      exact norm_indicator_le _
private theorem basisForm_supported (P : PauliCoordinates L n k) (q : LevelFormIndex L n k) :
    LevelFormsSupportedInCell (levelFormIndexCell q) (basisForm P q) := by
  refine ⟨fun b hb => ?_, fun i b hb => ?_⟩
  · refine eq_zero_of_coeffs (mem_traceless_of_mem_hermitian ((basisForm P q).1.2.1 b.1 b.2))
      fun a => ?_
    rw [basisForm_base P q a b, if_neg]
    · simp
    · rintro rfl
      exact hb rfl
  · refine eq_zero_of_coeffs (mem_traceless_of_mem_hermitian (((basisForm P q).2 i).2.1 b.1 b.2))
      fun a => ?_
    rw [basisForm_level P q i a b, if_neg]
    · simp
    · rintro rfl
      exact hb rfl
end BasisForms
section ZeroExtension
variable {L n k : ℕ}
private theorem gaugeCorrection_of_exists {X : ChainPoint L n k} {ξ : LevelForms L n k}
    {x : Vertex L n k 0}
    (h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = x) :
    gaugeCorrection X ξ x = chainDrift X ξ k h.choose := by
  unfold gaugeCorrection extendByZero
  rw [dif_pos h]
private theorem gaugeCorrection_of_not_exists {X : ChainPoint L n k} {ξ : LevelForms L n k}
    {x : Vertex L n k 0}
    (h : ¬∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = x) :
    gaugeCorrection X ξ x = 0 := by
  unfold gaugeCorrection extendByZero
  rw [dif_neg h]
private theorem levelVertexCell_eq_of_coe (hL : 0 < L) {x : Vertex L n k 0} {y : Vertex L n k k}
    (h : (y : PeriodicLattice.FourTorus L n) = x) : levelVertexCell x = levelVertexCell y := by
  unfold levelVertexCell
  congr 1
  refine Subtype.ext ?_
  rw [PeriodicLattice.coe_toSublattice_finest hL x, PeriodicLattice.coe_toSublattice_finest hL y, h]
end ZeroExtension
section CoordinateFamily
variable {L n k j : ℕ}
private theorem unitary_inv_mem {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem expTwist_of_pos {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
private theorem expTwist_of_not_pos {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
private theorem matExp_smul_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.ExpSurjective.matExp_I_smul_mem_specialUnitary <;> assumption
private theorem inv_inv_of_unitary {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    (g⁻¹)⁻¹ = g := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
private theorem unit_mem_fieldSpace :
    (fun _ : Edge L n k j => (1 : ComplexMatrix2)) ∈ fieldSpace L n k j :=
  ⟨fun _ _ => ComplexMatrix2.specialUnitary.one_mem, fun _ => by simp⟩
private theorem expTwist_mem_fieldSpace
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A U : Edge L n k j → ComplexMatrix2} (hA : A ∈ edgeFormSpace L n k j)
    (hU : U ∈ fieldSpace L n k j) :
    PeriodicLattice.expTwist A U ∈ fieldSpace L n k j := by
  have hU' : PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup Set.univ U := hU
  have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • A b) * U b ∈ ComplexMatrix2.specialUnitary := fun b hb =>
    ComplexMatrix2.specialUnitary.mul_mem (matExp_smul_mem (hA.1 b hb)) (hU'.1 b (Set.mem_univ b))
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [expTwist_of_pos h₁]
      exact hpos b h₁
    · rw [expTwist_of_not_pos h₂]
      exact unitary_inv_mem (hpos _ h₁)
  · rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hc : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
      rw [expTwist_of_pos h₁, expTwist_of_not_pos h₂, hc]
    · rw [expTwist_of_pos h₁, expTwist_of_not_pos h₂, inv_inv_of_unitary (hpos _ h₁)]
abbrev _root_.YangMills.SharedProofs.p8814 := @expTwist_mem_fieldSpace
private theorem expMove_zero_unitPoint :
    expMove (0 : LevelForms L n k) (unitPoint L n k) = unitPoint L n k := by
  have he : ComplexMatrix2.matExp (0 : ComplexMatrix2) = 1 := NormedSpace.exp_zero
  unfold expMove unitPoint
  congr 1
  · funext b
    by_cases hb : b.IsPositivelyOriented <;> simp [PeriodicLattice.expTwist, hb, he]
  · funext i c
    simp [he]
abbrev _root_.YangMills.DeltaSharedProofs.p500473 := @expMove_zero_unitPoint
abbrev _root_.YangMills.SharedProofs.p5970 := @expMove_zero_unitPoint
section Analyticity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}
private theorem analytic_inv_comp {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀)
    (hu : (f p₀).det ≠ 0) : AnalyticAt ℝ (fun y => (f y)⁻¹) p₀ := by
  have e : (fun y => (f y)⁻¹) = Ring.inverse ∘ f := by
    funext y
    simp [Matrix.nonsing_inv_eq_ringInverse]
  have hu' : IsUnit (f p₀) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hu)
  obtain ⟨u, hu2⟩ := hu'
  rw [e]
  exact AnalyticAt.comp (by rw [← hu2]; exact analyticAt_inverse (𝕜 := ℝ) u) hf
abbrev _root_.YangMills.SharedProofs.p24898 := @analytic_inv_comp
private theorem analytic_csmul_comp (c : ℂ) {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) :
    AnalyticAt ℝ (fun p => c • f p) p₀ := by
  have h : AnalyticAt ℝ (fun p => (c • (1 : ComplexMatrix2)) * f p) p₀ := analyticAt_const.mul hf
  exact h.congr (Eventually.of_forall fun p => by simp)
abbrev _root_.YangMills.SharedProofs.p44577 := @analytic_csmul_comp
private theorem analytic_matExp_comp {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) :
    AnalyticAt ℝ (fun p => ComplexMatrix2.matExp (f p)) p₀ :=
  AnalyticAt.comp (g := ComplexMatrix2.matExp) (NormedSpace.exp_analytic (𝕂 := ℝ) _) hf
end Analyticity
variable [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [Fintype (Fin 3 × Vertex L n k 0)]
  [Fintype (Fin 3 × Vertex L n k k)]
private theorem base_value_eq (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ)
    (b : PositiveEdge L n k 0) :
    ((tripleOfCoords P x).1.1 : Edge L n k 0 → ComplexMatrix2) b.1 =
      ∑ a, ((x (.inl (.inl (a, b))) : ℝ) : ℂ) • ComplexMatrix2.pauliFamily a := by
  have hm := mem_traceless_of_mem_hermitian ((tripleOfCoords P x).1.1.2.1 b.1 b.2)
  refine (pauli_expansion hm).trans (Finset.sum_congr rfl fun a _ => ?_)
  have h := P.formCoords_base (tripleOfCoords P x).1 (a, b)
  have e : pauliCoeff a (((tripleOfCoords P x).1.1 : Edge L n k 0 → ComplexMatrix2) b.1) =
      ((P.formCoords (tripleOfCoords P x).1 (.inl (a, b)) : ℝ) : ℂ) := h
  rw [e]
  simp [tripleOfCoords]
abbrev _root_.YangMills.DeltaSharedProofs.p502055 := @base_value_eq
private theorem level_value_eq (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ)
    (i : Fin k) (b : PositiveEdge L n k (i + 1)) :
    ((tripleOfCoords P x).1.2 i : Edge L n k (i + 1) → ComplexMatrix2) b.1 =
      ∑ a, ((x (.inl (.inr ⟨i, (a, b)⟩)) : ℝ) : ℂ) • ComplexMatrix2.pauliFamily a := by
  have hm := mem_traceless_of_mem_hermitian (((tripleOfCoords P x).1.2 i).2.1 b.1 b.2)
  refine (pauli_expansion hm).trans (Finset.sum_congr rfl fun a _ => ?_)
  have h := P.formCoords_level (tripleOfCoords P x).1 i (a, b)
  have e : pauliCoeff a
      (((tripleOfCoords P x).1.2 i : Edge L n k (i + 1) → ComplexMatrix2) b.1) =
      ((P.formCoords (tripleOfCoords P x).1 (.inr ⟨i, (a, b)⟩) : ℝ) : ℂ) := h
  rw [e]
  simp [tripleOfCoords]
abbrev _root_.YangMills.DeltaSharedProofs.p502402 := @level_value_eq
private theorem analytic_pauli_combination (u : Fin 3 → TripleCoordIndex L n k) :
    AnalyticAt ℝ (fun x : TripleCoordIndex L n k → ℝ =>
      ∑ a, ((x (u a) : ℝ) : ℂ) • ComplexMatrix2.pauliFamily a) 0 := by
  have h : ∀ a, AnalyticAt ℝ (fun x : TripleCoordIndex L n k → ℝ =>
      ((x (u a) : ℝ) : ℂ) • ComplexMatrix2.pauliFamily a) 0 := fun a => by
    have h1 : AnalyticAt ℝ (fun x : TripleCoordIndex L n k → ℝ =>
        x (u a) • ComplexMatrix2.pauliFamily a) 0 :=
      AnalyticAt.smul
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TripleCoordIndex L n k => ℝ)
          (u a)).analyticAt _)
        analyticAt_const
    exact h1.congr (Eventually.of_forall fun x => by simp)
  simp only [Fin.sum_univ_three]
  exact ((h 0).add (h 1)).add (h 2)
private theorem pointOfCoords_isFamily
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (P : PauliCoordinates L n k) : IsAnalyticFamilyThroughUnit (pointOfCoords P) 0 := by
  have hval : ∀ b : PositiveEdge L n k 0, AnalyticAt ℝ (fun x : TripleCoordIndex L n k → ℝ =>
      ComplexMatrix2.matExp
        (Complex.I • ((tripleOfCoords P x).1.1 : Edge L n k 0 → ComplexMatrix2) b.1)) 0 :=
    fun b =>
    (analytic_matExp_comp (analytic_csmul_comp Complex.I
      (analytic_pauli_combination fun a => .inl (.inl (a, b))))).congr
      (Eventually.of_forall fun x => by
        beta_reduce
        rw [base_value_eq])
  refine ⟨?_, fun b => ?_, fun i c => ?_, ?_⟩
  · have e : (tripleOfCoords P 0).1 = 0 := P.formCoords.symm.map_zero
    show expMove (tripleOfCoords P 0).1 (unitPoint L n k) = _
    rw [e]
    exact expMove_zero_unitPoint
  · by_cases hb : b.IsPositivelyOriented
    · refine (hval ⟨b, hb⟩).congr (Eventually.of_forall fun x => ?_)
      show _ = PeriodicLattice.expTwist _ _ b
      rw [expTwist_of_pos hb]
      simp [unitPoint]
    · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hb
      refine (analytic_inv_comp (hval ⟨b.opposite, hr⟩) ?_).congr
        (Eventually.of_forall fun x => ?_)
      · have e : (tripleOfCoords P 0).1 = 0 := P.formCoords.symm.map_zero
        rw [e]
        simp [NormedSpace.exp_zero]
      · show _ = PeriodicLattice.expTwist _ _ b
        rw [expTwist_of_not_pos hb]
        simp [unitPoint]
  · refine (analytic_matExp_comp (analytic_csmul_comp Complex.I
      (analytic_pauli_combination fun a => .inl (.inr ⟨i, (a, c)⟩)))).congr
      (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [← level_value_eq P]
    simp [pointOfCoords, expMove, unitPoint]
  · refine Eventually.of_forall fun x => ⟨expTwist_mem_fieldSpace hx (tripleOfCoords P x).1.1.2
      unit_mem_fieldSpace, fun i c => ?_⟩
    have h : ((tripleOfCoords P x).1.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 ∈
        ComplexMatrix2.hermitianTraceless :=
      ((tripleOfCoords P x).1.2 i).2.1 c.1 c.2
    simpa [pointOfCoords, expMove, unitPoint] using matExp_smul_mem h
end CoordinateFamily
end GaugeCorrectionLocality
open GaugeCorrectionLocality Matrices Tower in
theorem gaugeCorrectionIsLocal
    (hM : TransportAndDriftAreLocal)
    (hF : LevelFieldsHolomorphicAndLocal)
    (hMaps : AnalyticFamilyTransportAndGauge)
    (hK : CellLocalKernelNormBound)
    (hI : IndicesPerCellBounded)
    (hO : PeriodicLattice.LevelBondOrientationDichotomy) :
    GaugeCorrectionIsLocal := by
  intro L hL k hk
  obtain ⟨ρ, Cm, R, hρ, hCm, hR, HM⟩ := hM L hL k hk
  obtain ⟨ρ₀, C₀, s₀, -, -, -, HF⟩ := hF L hL k hk
  obtain ⟨N, hN, HK⟩ := hK R
  obtain ⟨m, hm, HI⟩ := hI L hL k hk
  obtain ⟨β, hβ₀⟩ : ∃ β : ℝ, β = ∑ a, ‖ComplexMatrix2.pauliFamily a‖ + 1 := ⟨_, rfl⟩
  have hβ : 0 < β := by
    rw [hβ₀]
    have : 0 ≤ ∑ a, ‖ComplexMatrix2.pauliFamily a‖ := Finset.sum_nonneg fun a _ => norm_nonneg _
    linarith
  have hE : 0 ≤ Cm * β := by positivity
  refine ⟨ρ, N * Real.sqrt (m * m) * (Cm * β), R, hρ, by positivity, hR, ?_⟩
  filter_upwards [HM, HF, eventually_gt_atTop 0] with n HMn HFn hn
  intro _ _ _ _ _ _ _ _ _ P
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hv : ∀ (q : LevelFormIndex L n k) (y : Vertex L n k k), IsLocalValueNearCell
      (fun z => chainDrift (complexChainPoint z) (basisForm P q) k y) ρ (Cm * β) R
      (levelVertexCell y) (levelFormIndexCell q) := fun q y => by
    have hb : LevelFormsBounded β (basisForm P q) :=
      ⟨fun b => ((basisForm_bounded P q).bottom_le b).trans (by linarith),
        fun i b => ((basisForm_bounded P q).level_le i b).trans (by linarith)⟩
    exact (HMn P _ _ β hβ (basisForm_supported P q) hb k le_rfl).2 y
  let G : (TripleCoordIndex L n k → ℂ) →
      Matrix (Fin 3 × Vertex L n k 0) (LevelFormIndex L n k) ℂ :=
    fun z p q => pauliCoeff p.1 (gaugeCorrection (complexChainPoint z) (basisForm P q) p.2)
  have Gof : ∀ (p : Fin 3 × Vertex L n k 0) (q : LevelFormIndex L n k)
      (h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = p.2)
      (z : TripleCoordIndex L n k → ℂ),
      G z p q = pauliCoeff p.1
        (chainDrift (complexChainPoint z) (basisForm P q) k h.choose) := fun p q h z => by
    show pauliCoeff p.1 (gaugeCorrection _ _ p.2) = _
    rw [gaugeCorrection_of_exists h]
  have Gnone : ∀ (p : Fin 3 × Vertex L n k 0) (q : LevelFormIndex L n k)
      (_ : ¬∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = p.2)
      (z : TripleCoordIndex L n k → ℂ),
      G z p q = 0 := fun p q h z => by
    show pauliCoeff p.1 (gaugeCorrection _ _ p.2) = _
    rw [gaugeCorrection_of_not_exists h, coeff_zero_matrix]
  have Gcell : ∀ (p : Fin 3 × Vertex L n k 0)
      (h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = p.2),
      fineIndexCell p = levelVertexCell h.choose := fun p h =>
    levelVertexCell_eq_of_coe hL0 h.choose_spec
  have Gfar : ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ, ∀ p q,
      R < cellDist (fineIndexCell p) (levelFormIndexCell q) → G z p q = 0 := by
    intro z hz p q hd
    by_cases h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = p.2
    · rw [Gof p q h, (hv q _).eq_zero_of_far (by rwa [← Gcell p h]) z hz, coeff_zero_matrix]
    · exact Gnone p q h z
  have Gbound : ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ, ∀ p q,
      ‖G z p q‖ ≤ Cm * β := by
    intro z hz p q
    by_cases h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = p.2
    · rw [Gof p q h]
      exact (coeff_norm_le ((hv q _).traceless z hz) _).trans ((hv q _).norm_le z hz)
    · rw [Gnone p q h z, norm_zero]
      exact hE
  refine ⟨G, ⟨fun p q => ?_, fun z hz => ?_, fun p q z hz z' hz' a => ?_, Gfar⟩, ?_⟩
  · by_cases h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = p.2
    · have e : (fun z => G z p q) = fun z => pauliCoeff p.1
          (chainDrift (complexChainPoint z) (basisForm P q) k h.choose) := funext (Gof p q h)
      rw [e]
      exact coeff_analyticOnNhd Metric.isOpen_ball (hv q _).holomorphic (hv q _).traceless _
    · have e : (fun z => G z p q) = fun _ => 0 := funext (Gnone p q h)
      rw [e]
      exact analyticOnNhd_const
  · exact HK L n k hL hn levelFormIndexCell fineIndexCell m m (Cm * β) (G z) hm hm hE
      (fun y => (HI n hn y).2.2) (fun y => (HI n hn y).1 0 (Nat.zero_le k)) (Gbound z hz)
      (Gfar z hz)
  · by_cases h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = p.2
    · rw [Gof p q h, Gof p q h, (hv q _).depends_near z hz z' hz' fun i hi => a i (by
        rw [Gcell p h]
        exact hi)]
    · rw [Gnone p q h, Gnone p q h]
  · have hxor : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
      fun b => hO L n k hL hn hk 0 (Nat.zero_le k) b
    have hfam := pointOfCoords_isFamily hxor P
    obtain ⟨f1, -⟩ := HFn P
    filter_upwards [(hMaps L hL k n hk hn (TripleCoordIndex L n k → ℝ) (pointOfCoords P) 0
      hfam).2] with x hx ξ
    obtain ⟨-, -, S, hS⟩ := hx
    refine ⟨S ξ, hS ξ, ?_⟩
    funext p
    let Λ : (LevelFormIndex L n k → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.proj (.inl p)) ∘ₗ P.ghostCoords.toLinearMap ∘ₗ
        (LinearMap.inl ℝ (vertexFunctionSpace L n k 0) (vertexFunctionSpace L n k k)) ∘ₗ S ∘ₗ
          P.formCoords.symm.toLinearMap
    have hΛ : ∀ ξ' : LevelForms L n k,
        Λ (P.formCoords ξ') = P.ghostCoords (S ξ', 0) (.inl p) :=
      fun ξ' => by simp [Λ]
    have hsum := LinearMap.pi_apply_eq_sum_univ Λ (P.formCoords ξ)
    rw [hΛ] at hsum
    have hu : ∀ q, (fun q' => if q = q' then (1 : ℝ) else 0) = P.formCoords (basisForm P q) :=
      fun q => funext fun q' => (formCoords_basisForm P q q').symm
    have hG : ∀ q, G (complexifyCoords x) p q =
        ((P.ghostCoords (S (basisForm P q), 0) (.inl p) : ℝ) : ℂ) := fun q => by
      show pauliCoeff p.1 (gaugeCorrection (complexChainPoint (complexifyCoords x))
        (basisForm P q) p.2) = _
      have e := hS (basisForm P q)
      rw [f1 x, ← e]
      exact P.ghostCoords_fst (S (basisForm P q), 0) p
    show ((P.ghostCoords (S ξ, 0) (.inl p) : ℝ) : ℂ) =
      ∑ q, G (complexifyCoords x) p q * ((P.formCoords ξ q : ℝ) : ℂ)
    rw [hsum]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hG q, hu q, hΛ, smul_eq_mul]
    push_cast
    ring
end YangMills.Construction.RunningCouplingSlope
end
