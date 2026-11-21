import YangMills.Construction.Matrices.CalculusOfTheFieldsOnPowersOfGProof
import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.OneLoop.PauliMatrixRelations
import YangMills.Construction.OneLoopLaw.FirstDerivativeOfAMemberVanishes
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace YangMills.Construction.OneLoopLaw.MemberDerivative
open Matrices Matrices.PowerExpCharts Tower PeriodicOperators.Tempered
private theorem sigma_mul_self (a : Fin 3) : pauliFamily a * pauliFamily a = 1 := by apply _root_.YangMills.Construction.SpinHarmonics.FieldCalculus.pauli_mul_self <;> assumption
private theorem sandwich_mem (a : Fin 3) (X : ComplexMatrix2.LieElement) :
    pauliFamily a * X.toMatrix * pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by
  have hσ : (pauliFamily a).conjTranspose = pauliFamily a :=
    (pauliFamily_mem_hermitianTraceless a).1.symm
  have hX : X.toMatrix.conjTranspose = X.toMatrix := X.2.1.symm
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hσ, hX, mul_assoc]
  · have htr : ComplexMatrix2.fullTrace (pauliFamily a * X.toMatrix * pauliFamily a) =
        ComplexMatrix2.fullTrace X.toMatrix := by
      simp only [ComplexMatrix2.fullTrace]
      rw [Matrix.trace_mul_comm, ← mul_assoc, sigma_mul_self, one_mul]
    rw [htr]
    exact X.2.2
private def sandwich (a : Fin 3) (X : ComplexMatrix2.LieElement) : ComplexMatrix2.LieElement :=
  (⟨pauliFamily a * X.toMatrix * pauliFamily a, sandwich_mem a X⟩ :
    ComplexMatrix2.hermitianTraceless)
private theorem sandwich_toMatrix (a : Fin 3) (X : ComplexMatrix2.LieElement) :
    (sandwich a X).toMatrix = pauliFamily a * X.toMatrix * pauliFamily a := rfl
private theorem sandwich_smul (a : Fin 3) (t : ℝ) (X : ComplexMatrix2.LieElement) :
    sandwich a (t • X) = t • sandwich a X := by
  apply Subtype.ext
  change pauliFamily a * (t • X.toMatrix) * pauliFamily a =
    t • (pauliFamily a * X.toMatrix * pauliFamily a)
  simp
private theorem self_add_sandwiches (X : ComplexMatrix2.LieElement) :
    X + (sandwich 0 X + sandwich 1 X + sandwich 2 X) = 0 := by
  apply Subtype.ext
  change X.toMatrix + (pauliFamily 0 * X.toMatrix * pauliFamily 0 +
    pauliFamily 1 * X.toMatrix * pauliFamily 1 + pauliFamily 2 * X.toMatrix * pauliFamily 2) = 0
  have htr : X.toMatrix 0 0 + X.toMatrix 1 1 = 0 := by
    have := X.2.2
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] at this
    exact this
  have hI := Complex.I_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
      OneLoop.pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  · linear_combination 2 * htr - X.toMatrix 1 1 * hI
  · linear_combination X.toMatrix 1 0 * hI
  · linear_combination X.toMatrix 0 1 * hI
  · linear_combination 2 * htr - X.toMatrix 0 0 * hI
private def iSigma (a : Fin 3) : ComplexMatrix2 := Complex.I • pauliFamily a
private theorem iSigma_mul (a : Fin 3) : iSigma a * ((-Complex.I) • pauliFamily a) = 1 := by
  rw [iSigma, smul_mul_smul_comm, sigma_mul_self]
  simp
private theorem mul_iSigma (a : Fin 3) : ((-Complex.I) • pauliFamily a) * iSigma a = 1 := by
  rw [iSigma, smul_mul_smul_comm, sigma_mul_self]
  simp
private theorem iSigma_inv (a : Fin 3) : (iSigma a)⁻¹ = (-Complex.I) • pauliFamily a :=
  Matrix.inv_eq_right_inv (iSigma_mul a)
private theorem iSigma_isUnit (a : Fin 3) : IsUnit (iSigma a) :=
  ⟨⟨iSigma a, _, iSigma_mul a, mul_iSigma a⟩, rfl⟩
private theorem iSigma_mem (a : Fin 3) : iSigma a ∈ PeriodicLattice.compactGaugeGroup := by
  have hσ : star (pauliFamily a) = pauliFamily a := (pauliFamily_mem_hermitianTraceless a).1.symm
  change iSigma a ∈ ComplexMatrix2.specialUnitary
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · have hs : star (iSigma a) = (-Complex.I) • pauliFamily a := by
      rw [iSigma, star_smul, hσ]
      simp
    rw [hs]
    exact iSigma_mul a
  · fin_cases a <;>
      simp [iSigma, pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
        OneLoop.pauliZ, Matrix.det_fin_two]
private def expI (X : ComplexMatrix2.LieElement) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (Complex.I • X.toMatrix)
private theorem expI_inv (X : ComplexMatrix2.LieElement) : (expI X)⁻¹ = expI (-X) := by
  have hneg : (-X).toMatrix = -X.toMatrix := rfl
  simp only [expI, hneg, smul_neg]
  exact (Matrix.exp_neg _).symm
abbrev _root_.YangMills.DeltaSharedProofs.p501014 := @expI_inv
private theorem expI_sandwich (a : Fin 3) (X : ComplexMatrix2.LieElement) :
    expI (sandwich a X) = iSigma a * expI X * (iSigma a)⁻¹ := by
  have hc : iSigma a * (Complex.I • X.toMatrix) * (iSigma a)⁻¹ =
      Complex.I • (pauliFamily a * X.toMatrix * pauliFamily a) := by
    rw [iSigma_inv, iSigma]
    simp [smul_smul, mul_assoc]
  simp only [expI, sandwich_toMatrix]
  rw [← hc]
  exact Matrix.exp_conj _ _ (iSigma_isUnit a)
private theorem opposite_pos {L n : ℕ} {e : UnitEdge L n} (he : ¬e.IsPositivelyOriented) :
    e.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h | h⟩ := e.isNeighbour
  · exact absurd ⟨μ, h⟩ he
  · refine ⟨μ, ?_⟩
    change e.source - e.target = _
    rw [← neg_sub, h, neg_neg]
abbrev _root_.YangMills.SharedProofs.p9846 := @opposite_pos
private def expIField {L n : ℕ} (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement) :
    UnitEdge L n → ComplexMatrix2 :=
  fieldOfPositiveValues (k := 0) (j := 0) fun s => expI (Y s)
private theorem expIField_pos {L n : ℕ} (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement)
    {e : UnitEdge L n} (he : e.IsPositivelyOriented) : expIField Y e = expI (Y ⟨e, he⟩) := by
  simp only [expIField, fieldOfPositiveValues, dif_pos he]
private theorem expIField_neg {L n : ℕ} (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement)
    {e : UnitEdge L n} (he : ¬e.IsPositivelyOriented) :
    expIField Y e = expI (-Y ⟨e.opposite, opposite_pos he⟩) := by
  simp only [expIField, fieldOfPositiveValues, dif_neg he, dif_pos (opposite_pos he)]
  exact expI_inv _
private theorem expIField_sandwich {L n : ℕ} (a : Fin 3)
    (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement) :
    expIField (fun s => sandwich a (Y s)) =
      PeriodicLattice.gaugeTransform (fun _ : Vertex L n 0 0 => iSigma a) (expIField Y) := by
  funext e
  simp only [PeriodicLattice.gaugeTransform]
  by_cases he : e.IsPositivelyOriented
  · rw [expIField_pos _ he, expIField_pos _ he, expI_sandwich]
  · rw [expIField_neg _ he, expIField_neg _ he, ← expI_inv,
      ← expI_inv, expI_sandwich, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (iSigma_isUnit a)),
      mul_assoc]
private theorem expTwist_eq_expIField {L n : ℕ} (t : ℝ)
    (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement)
    (B : UnitEdge L n → ComplexMatrix2) (hY : ∀ s, (Y s).toMatrix = B s.1) :
    PeriodicLattice.expTwist ((algebraMap ℝ ℂ t) • B) (identityField L n) =
      expIField (t • Y) := by
  have hv : ∀ s, (t • Y s).toMatrix = (algebraMap ℝ ℂ t) • B s.1 := by
    intro s
    change t • (Y s).toMatrix = _
    rw [hY]
    ext i j
    simp
  funext e
  by_cases he : e.IsPositivelyOriented
  · rw [expIField_pos _ he]
    simp only [PeriodicLattice.expTwist, if_pos he, identityField, mul_one, expI,
      hv ⟨e, he⟩, Pi.smul_apply]
  · rw [expIField_neg _ he, ← expI_inv]
    simp only [PeriodicLattice.expTwist, if_neg he, identityField, mul_one, expI,
      hv ⟨e.opposite, opposite_pos he⟩, Pi.smul_apply]
private theorem tendsto_expIField {L n : ℕ} (hL : 2 ≤ L) (hn : 0 < n)
    (hmem : ∀ X : ComplexMatrix2.LieElement, expI X ∈ PeriodicLattice.compactGaugeGroup)
    (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement) :
    Tendsto (fun t : ℝ => expIField (t • Y)) (𝓝 0)
      (𝓝[fieldSpace L n 0 0] fun _ => (1 : ComplexMatrix2)) := by
  have hX : ∀ X : ComplexMatrix2.LieElement,
      Tendsto (fun t : ℝ => expI (t • X)) (𝓝 0) (𝓝 1) := by
    intro X
    let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
    have hc : Continuous fun t : ℝ => ComplexMatrix2.matExp (Complex.I • (t • X.toMatrix)) :=
      NormedSpace.exp_continuous.comp (by fun_prop)
    have h := hc.tendsto 0
    simp only [zero_smul, smul_zero, ComplexMatrix2.matExp, NormedSpace.exp_zero] at h
    exact h
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun e => ?_, Eventually.of_forall fun t => ?_⟩
  · by_cases he : e.IsPositivelyOriented
    · simp only [expIField_pos _ he]
      exact hX _
    · simp only [expIField_neg _ he]
      have h' := hX (-Y ⟨e.opposite, opposite_pos he⟩)
      simpa only [Pi.smul_apply, smul_neg] using h'
  · have hoo : ∀ e : UnitEdge L n, e.opposite.opposite = e :=
      fun e => PeriodicLattice.Bond.ext rfl rfl
    refine ⟨fun e _ => ?_, fun e _ => ?_⟩
    · by_cases he : e.IsPositivelyOriented
      · rw [expIField_pos _ he]
        exact hmem _
      · rw [expIField_neg _ he]
        exact hmem _
    · have hx := PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (L := L) (m := n)
        (j := PeriodicLattice.levelDepth 0 0) (by omega)
        (by simp [PeriodicLattice.levelDepth]; omega) e
      by_cases he : e.IsPositivelyOriented
      · have hr : ¬e.opposite.IsPositivelyOriented := by
          rcases hx with ⟨-, h'⟩ | ⟨-, h'⟩
          · exact h'
          · exact absurd he h'
        rw [expIField_neg _ hr, expIField_pos _ he, expI_inv]
        rfl
      · rw [expIField_pos _ (opposite_pos he), expIField_neg _ he,
          expI_inv, neg_neg]
theorem memberFirstDerivativeVanishes_of_expCharts (hC : ExpChartsStatement)
    (hP : OneLoop.PauliMatrixRelations) : MemberFirstDerivativeVanishes := by
  intro L n hL hn f hf B hB
  obtain ⟨inst, O, hO, hone, hA⟩ := hf.analytic
  have hne : Nonempty (PositiveUnitEdge L n) :=
    ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, 0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩
  obtain ⟨-, -, -, ⟨β, -⟩, -⟩ := hP
  obtain ⟨hCh, -, -, -, -, -, -, hb⟩ := hC (PositiveUnitEdge L n) (PositiveUnitEdge L n)
  obtain ⟨hR, -⟩ := hb β
  have hser := ((hR O hO).1 _ (hA β)).1
  have hp : (fun _ => (1 : ComplexMatrix2)) ∈ specialUnitaryPower (PositiveUnitEdge L n) := by
    obtain ⟨W, -, rfl⟩ := hO
    exact hone.2
  obtain ⟨-, hval, -⟩ := hCh _ hp
  obtain ⟨N, hN, -, hsm, -⟩ := hser.1 _ hone
  have hchart : ∀ Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement,
      expChartI (fun _ => (1 : ComplexMatrix2)) Y = fun s => expI (Y s) := by
    intro Y
    rw [(hval Y).2.1]
    funext s
    simp [expI]
  have hmem : ∀ X, expI X ∈ PeriodicLattice.compactGaugeGroup := by
    intro X
    obtain ⟨s⟩ := hne
    have h := (hval fun _ => X).2.2 s
    rw [hchart] at h
    exact h
  let G : (PositiveUnitEdge L n → ComplexMatrix2.LieElement) → ℝ := fun Y => f (expIField Y)
  have hcomp : ((fun w => f (fieldOfPositiveValues (k := 0) (j := 0) w)) ∘
      expChartI (fun _ => (1 : ComplexMatrix2))) = G := by
    funext Y
    simp only [Function.comp, hchart]
    rfl
  rw [hcomp] at hsm
  have hd : DifferentiableAt ℝ G 0 := (hsm.contDiffAt hN).differentiableAt (by simp)
  have hline : ∀ Y, HasDerivAt (fun t : ℝ => G (t • Y)) (fderiv ℝ G 0 Y) 0 := by
    intro Y
    have h := hd.hasFDerivAt.hasLineDerivAt Y
    simpa [HasLineDerivAt] using h
  have hinv : ∀ (a : Fin 3) (Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement),
      fderiv ℝ G 0 (fun s => sandwich a (Y s)) = fderiv ℝ G 0 Y := by
    intro a Y
    have hev : (fun t : ℝ => G (t • fun s => sandwich a (Y s))) =ᶠ[𝓝 0]
        fun t => G (t • Y) := by
      filter_upwards [(tendsto_expIField (by have := hL.2; omega) hn hmem Y).eventually
        hf.globalGauge] with t ht
      have h1 := ht _ (iSigma_mem a)
      rw [← expIField_sandwich] at h1
      have h2 : (fun s => sandwich a ((t • Y) s)) = t • fun s => sandwich a (Y s) := by
        funext s
        exact sandwich_smul a t (Y s)
      rw [h2] at h1
      exact h1
    exact (hline _).unique ((hline Y).congr_of_eventuallyEq hev)
  have hzero : ∀ Y, fderiv ℝ G 0 Y = 0 := by
    intro Y
    have hs : Y + ((fun s => sandwich 0 (Y s)) + (fun s => sandwich 1 (Y s)) +
        (fun s => sandwich 2 (Y s))) = 0 := by
      funext s
      exact self_add_sandwiches (Y s)
    have h := congrArg (fderiv ℝ G 0) hs
    simp only [map_add, map_zero, hinv] at h
    linarith
  let Y : PositiveUnitEdge L n → ComplexMatrix2.LieElement :=
    fun s => (⟨B s.1, hB.1 s.1 s.2⟩ : ComplexMatrix2.hermitianTraceless)
  have hder : leftDeriv (k := 0) (j := 0) f (identityField L n) B = fderiv ℝ G 0 Y := by
    have h : (fun t : ℝ => f (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • B)
        (identityField L n))) = fun t => G (t • Y) := by
      funext t
      rw [expTwist_eq_expIField t Y B fun _ => rfl]
    simp only [leftDeriv, directionalDeriv, h]
    exact (hline Y).deriv
  rw [hder, hzero]
end YangMills.Construction.OneLoopLaw.MemberDerivative
end
