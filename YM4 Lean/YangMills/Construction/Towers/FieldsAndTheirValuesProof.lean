import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperatorsProof
import YangMills.Construction.Matrices.NormAndPairingInPauliCoordinates
import YangMills.Construction.Towers.AverageIsDifferentiableOnThePolydiscProof
import YangMills.Construction.Towers.FieldsAndTheirValues
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.SymbolsOfTheAveragesOnPlaneWavesProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.FieldValues
open PeriodicOperators
open InfiniteLattice (AmbientSpace latticeSubgroup)
open Matrices (ComplexMatrix2)
theorem pauliCombo_mem_traceless (c : Fin 3 → ℂ) :
    (∑ a, c a • ComplexMatrix2.pauliFamily a) ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_sum_smul (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ i, c i • ComplexMatrix2.pauliFamily i) = c a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
variable {a : ℝ}
theorem opposite_pos_of_not_pos {b : InfiniteLattice.Link a} (hb : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem not_pos_opposite (ha : a ≠ 0) {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    ¬b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.PolydiscSmoothing.not_opposite_isPositivelyOriented <;> assumption
theorem opposite_opposite (b : InfiniteLattice.Link a) : b.opposite.opposite = b := rfl
variable {L k j : ℕ}
theorem meshAt_ne_zero (hL : 0 < L) (k j : ℕ) : meshAt L k j ≠ 0 :=
  zpow_ne_zero _ (Nat.cast_ne_zero.2 hL.ne')
theorem ofCoeffs_coeffs (B : Edge L k j → ComplexMatrix2) (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    (edgePauliCoordinates L k j).ofCoeffs ((edgePauliCoordinates L k j).coeffs B) = B := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofCoeffs_coeffs <;> assumption
theorem ofCoeffs_mem (hL : 0 < L) (c : Fin 3 × PositiveEdge (meshAt L k j) → ℂ) :
    (edgePauliCoordinates L k j).ofCoeffs c ∈ complexEdgeForms (meshAt L k j) := by
  have ha := meshAt_ne_zero hL k j
  have pos : ∀ b : Edge L k j, ∀ hb : b.IsPositivelyOriented,
      (edgePauliCoordinates L k j).ofCoeffs c b = ∑ a, c (a, ⟨b, hb⟩) • ComplexMatrix2.pauliFamily a :=
    fun b hb => by
    change (open Classical in if b.IsPositivelyOriented then
      (if hb : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, hb⟩ else 0)
      else -(if hb : b.opposite.IsPositivelyOriented then
        ofPauliCoeffs c ⟨b.opposite, hb⟩ else 0)) = _
    rw [if_pos hb, dif_pos hb]
    rfl
  have neg : ∀ b : Edge L k j, ∀ hb : b.IsPositivelyOriented,
      (edgePauliCoordinates L k j).ofCoeffs c b.opposite =
        -∑ a, c (a, ⟨b, hb⟩) • ComplexMatrix2.pauliFamily a := fun b hb => by
    change (open Classical in if b.opposite.IsPositivelyOriented then
      (if hb : b.opposite.IsPositivelyOriented then ofPauliCoeffs c ⟨b.opposite, hb⟩ else 0)
      else -(if hb : b.opposite.opposite.IsPositivelyOriented then
        ofPauliCoeffs c ⟨b.opposite.opposite, hb⟩ else 0)) = _
    have hb' : b.opposite.opposite.IsPositivelyOriented := hb
    rw [if_neg (not_pos_opposite ha hb), dif_pos hb']
    rfl
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [pos b hb]
    exact pauliCombo_mem_traceless _
  · by_cases hb : b.IsPositivelyOriented
    · rw [pos b hb, neg b hb]
    · have hb' := opposite_pos_of_not_pos hb
      have e := neg b.opposite hb'
      rw [opposite_opposite] at e
      rw [pos _ hb', e, neg_neg]
theorem coeffs_ofCoeffs (c : Fin 3 × PositiveEdge (meshAt L k j) → ℂ) :
    (edgePauliCoordinates L k j).coeffs ((edgePauliCoordinates L k j).ofCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.FreeOperators.toPauliCoeffs_restrict_edgeValue <;> assumption
theorem exists_int_mul_meshAt_eq_one (hL : 0 < L) {j : ℕ} (hj : j ≤ k) :
    ∃ m : ℤ, (m : ℝ) * meshAt L k j = 1 := by
  have h0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
  refine ⟨(L : ℤ) ^ (k - j), ?_⟩
  have e : ((k - j : ℕ) : ℤ) + ((j : ℤ) - (k : ℤ)) = 0 := by omega
  rw [meshAt]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ h0, e, zpow_zero]
theorem castVec_mem (h : ∃ m : ℤ, (m : ℝ) * a = 1) (v : Fin 4 → ℤ) : castVec v ∈ latticeSubgroup a := by
  obtain ⟨m, hm⟩ := h
  refine ⟨fun μ => v μ * m, fun μ => ?_⟩
  simp only [castVec, Int.cast_mul]
  rw [mul_assoc, hm, mul_one]
theorem coe_vertexImage_intShift (h : ∃ m : ℤ, (m : ℝ) * a = 1) (v : Fin 4 → ℤ)
    (x : InfiniteLattice.LatticePoint a) :
    ((vertexImage (intShift v) x : InfiniteLattice.LatticePoint a) : AmbientSpace) =
      (x : AmbientSpace) + castVec v :=
  Classical.epsilon_spec
    (p := fun x' : InfiniteLattice.LatticePoint a => (x' : AmbientSpace) = intShift v x)
    ⟨⟨(x : AmbientSpace) + castVec v, add_mem x.2 (castVec_mem h v)⟩, rfl⟩
theorem coe_vertexPreimage_intShift (h : ∃ m : ℤ, (m : ℝ) * a = 1) (v : Fin 4 → ℤ)
    (x : InfiniteLattice.LatticePoint a) :
    ((vertexPreimage (intShift v) x : InfiniteLattice.LatticePoint a) : AmbientSpace) =
      (x : AmbientSpace) - castVec v := by
  have e : intShift v (vertexPreimage (intShift v) x : InfiniteLattice.LatticePoint a) =
      (x : AmbientSpace) :=
    Classical.epsilon_spec
      (p := fun x' : InfiniteLattice.LatticePoint a =>
        intShift v (x' : AmbientSpace) = (x : AmbientSpace))
      ⟨⟨(x : AmbientSpace) - castVec v, sub_mem x.2 (castVec_mem h v)⟩, sub_add_cancel _ _⟩
  exact eq_sub_of_add_eq e
theorem castVec_neg (v : Fin 4 → ℤ) : castVec (-v) = -castVec v := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.castVec_neg <;> assumption
def translateLink (h : ∃ m : ℤ, (m : ℝ) * a = 1) (v : Fin 4 → ℤ) (b : InfiniteLattice.Link a) :
    InfiniteLattice.Link a where
  initial := ⟨(b.initial : AmbientSpace) + castVec v, add_mem b.initial.2 (castVec_mem h v)⟩
  terminal := ⟨(b.terminal : AmbientSpace) + castVec v, add_mem b.terminal.2 (castVec_mem h v)⟩
  isAdjacent := by
    obtain ⟨μ, e⟩ := b.isAdjacent
    refine ⟨μ, ?_⟩
    have d : (⟨(b.terminal : AmbientSpace) + castVec v, add_mem b.terminal.2 (castVec_mem h v)⟩ :
        InfiniteLattice.LatticePoint a) -
        ⟨(b.initial : AmbientSpace) + castVec v, add_mem b.initial.2 (castVec_mem h v)⟩ =
        b.terminal - b.initial := Subtype.ext (add_sub_add_right_eq_sub _ _ _)
    rwa [d]
theorem translateLink_sub (h : ∃ m : ℤ, (m : ℝ) * a = 1) (v : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) :
    (translateLink h v b).terminal - (translateLink h v b).initial = b.terminal - b.initial :=
  Subtype.ext (add_sub_add_right_eq_sub _ _ _)
theorem edgeImage_intShift (h : ∃ m : ℤ, (m : ℝ) * a = 1) (v : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) : edgeImage (intShift v) b = translateLink h v b := by
  have hs : ∀ x : InfiniteLattice.LatticePoint a,
      (⟨(x : AmbientSpace) + castVec v, add_mem x.2 (castVec_mem h v)⟩ :
        InfiniteLattice.LatticePoint a) = vertexImage (intShift v) x :=
    fun x => Subtype.ext (coe_vertexImage_intShift h v x).symm
  have e := Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a => b'.initial = vertexImage (intShift v) b.initial ∧
      b'.terminal = vertexImage (intShift v) b.terminal) ⟨translateLink h v b, hs _, hs _⟩
  exact InfiniteLattice.Link.ext (e.1.trans (hs _).symm) (e.2.trans (hs _).symm)
theorem edgePreimage_intShift (h : ∃ m : ℤ, (m : ℝ) * a = 1) (v : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) : edgePreimage (intShift v) b = translateLink h (-v) b := by
  have hs : ∀ x : InfiniteLattice.LatticePoint a,
      (⟨(x : AmbientSpace) + castVec (-v), add_mem x.2 (castVec_mem h (-v))⟩ :
        InfiniteLattice.LatticePoint a) = vertexPreimage (intShift v) x := fun x => Subtype.ext (by
    rw [coe_vertexPreimage_intShift h v x]
    change (x : AmbientSpace) + castVec (-v) = _
    rw [castVec_neg, sub_eq_add_neg])
  have e := Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a => b'.initial = vertexPreimage (intShift v) b.initial ∧
      b'.terminal = vertexPreimage (intShift v) b.terminal) ⟨translateLink h (-v) b, hs _, hs _⟩
  exact InfiniteLattice.Link.ext (e.1.trans (hs _).symm) (e.2.trans (hs _).symm)
theorem translateLink_pos (h : ∃ m : ℤ, (m : ℝ) * a = 1) (v : Fin 4 → ℤ)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    (translateLink h v b).IsPositivelyOriented := by
  obtain ⟨μ, e⟩ := hb
  exact ⟨μ, (translateLink_sub h v b).trans e⟩
theorem translateLink_opposite (h : ∃ m : ℤ, (m : ℝ) * a = 1) (v : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) : translateLink h v b.opposite = (translateLink h v b).opposite :=
  rfl
theorem pushField_mem (h : ∃ m : ℤ, (m : ℝ) * a = 1) (v : Fin 4 → ℤ)
    {B : InfiniteLattice.Link a → ComplexMatrix2} (hB : B ∈ complexEdgeForms a) :
    pushField (intShift v) B ∈ complexEdgeForms a := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · change B (edgePreimage (intShift v) b) ∈ _
    rw [edgePreimage_intShift h]
    exact hB.1 _ (translateLink_pos h _ hb)
  · change B (edgePreimage (intShift v) b.opposite) = -B (edgePreimage (intShift v) b)
    rw [edgePreimage_intShift h, edgePreimage_intShift h, translateLink_opposite]
    exact hB.2 _
theorem shiftEdge_val (hL : 0 < L) (hj : j ≤ k) (v : Fin 4 → ℤ) (b : PosEdge L k j) :
    (shiftEdge v b).1 = translateLink (exists_int_mul_meshAt_eq_one hL hj) v b.1 := by
  have h := exists_int_mul_meshAt_eq_one (k := k) hL hj
  have e := Classical.epsilon_spec
    (p := fun b' : PosEdge L k j => b'.1 = edgeImage (intShift v) b.1)
    ⟨⟨translateLink h v b.1, translateLink_pos h v b.2⟩, (edgeImage_intShift h v b.1).symm⟩
  exact e.trans (edgeImage_intShift h v b.1)
theorem coeffs_pushField (hL : 0 < L) (hj : j ≤ k) (v : Fin 4 → ℤ)
    (B : Edge L k j → ComplexMatrix2) (ι : Fin 3 × PosEdge L k j) :
    (edgePauliCoordinates L k j).coeffs (pushField (intShift v) B) ι =
      (edgePauliCoordinates L k j).coeffs B (ι.1, shiftEdge (-v) ι.2) := by
  change pauliCoeff ι.1 (B (edgePreimage (intShift v) ι.2.1)) =
    pauliCoeff ι.1 (B (shiftEdge (-v) ι.2).1)
  rw [edgePreimage_intShift (exists_int_mul_meshAt_eq_one hL hj), shiftEdge_val hL hj]
theorem operatorNorm_le_of_pauliCoeff (hP : Matrices.PauliNormPairing.Statement) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) {r : ℝ} (hr : ∀ a, ‖pauliCoeff a X‖ ≤ r) :
    ComplexMatrix2.operatorNorm X ≤ Real.sqrt 6 * r := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hr 0)
  have e : ComplexMatrix2.pauliCombination (fun a => pauliCoeff a X) = X := by
    conv_rhs => rw [← sum_pauliCoeff_smul hX]
    simp only [ComplexMatrix2.pauliCombination, Fin.sum_univ_three]
    rfl
  have h := (hP.1 (fun a => pauliCoeff a X) (fun a => pauliCoeff a X)).2.2
  rw [e] at h
  refine h.trans ?_
  have h3 : ComplexMatrix2.hermitianNormFin3 (fun a => pauliCoeff a X) ≤ Real.sqrt 3 * r := by
    rw [ComplexMatrix2.hermitianNormFin3]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by norm_num), Fin.sum_univ_three]
    have := fun a => pow_le_pow_left₀ (norm_nonneg _) (hr a) 2
    nlinarith [this 0, this 1, this 2]
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  rw [h6, mul_assoc]
  exact mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
theorem fieldsAndValuesClaim_holds (hP : Matrices.PauliNormPairing.Statement) :
    FieldsAndValuesClaim := by
  intro L hL k
  have h0 := Nat.zero_le k
  have hk : k ≤ k := le_rfl
  refine ⟨fun ζ => ?_, fun f => ?_, fun v ζ => ?_, fun ζ r hr b => ?_⟩
  · have e₁ : backgroundOfCoeffs hL (ζ.pauliCoeffs hL) = (ζ.1 : Edge L k 0 → ComplexMatrix2) :=
      ofCoeffs_coeffs _ ζ.1.2
    have e₂ : sourceOfCoeffs hL (ζ.pauliCoeffs hL) = (ζ.2.1 : Edge L k 0 → ComplexMatrix2) :=
      ofCoeffs_coeffs _ ζ.2.1.2
    have e₃ : coarseOfCoeffs hL (ζ.pauliCoeffs hL) = (ζ.2.2 : Edge L k k → ComplexMatrix2) :=
      ofCoeffs_coeffs _ ζ.2.2.2
    refine ⟨e₁, e₂, e₃, ?_, ?_, ?_⟩
    · change hessianSaddle (expForm (backgroundOfCoeffs hL (ζ.pauliCoeffs hL)))
        (sourceOfCoeffs hL (ζ.pauliCoeffs hL)) (coarseOfCoeffs hL (ζ.pauliCoeffs hL)) =
        hessianSaddle (expForm (ζ.1 : Edge L k 0 → ComplexMatrix2)) ζ.2.1 ζ.2.2
      rw [e₁, e₂, e₃]
    · change laplacianSaddle L k (expForm (backgroundOfCoeffs hL (ζ.pauliCoeffs hL))) =
        laplacianSaddle L k (expForm (ζ.1 : Edge L k 0 → ComplexMatrix2))
      rw [e₁]
    · change expForm (backgroundOfCoeffs hL (ζ.pauliCoeffs hL)) =
        expForm (ζ.1 : Edge L k 0 → ComplexMatrix2)
      rw [e₁]
  · refine ⟨(⟨backgroundOfCoeffs hL f, ofCoeffs_mem hL _⟩,
      ⟨sourceOfCoeffs hL f, ofCoeffs_mem hL _⟩,
      ⟨coarseOfCoeffs hL f, ofCoeffs_mem hL _⟩), ?_⟩
    funext κ
    obtain ⟨p, ι⟩ := κ
    cases p
    · exact congrFun (coeffs_ofCoeffs _) ι
    · exact congrFun (coeffs_ofCoeffs _) ι
    · exact congrFun (coeffs_ofCoeffs _) ι
  · have m₀ := exists_int_mul_meshAt_eq_one (k := k) hL h0
    have mk := exists_int_mul_meshAt_eq_one (k := k) hL hk
    refine ⟨(⟨pushField (intShift v) ζ.1, pushField_mem m₀ v ζ.1.2⟩,
      ⟨pushField (intShift v) ζ.2.1, pushField_mem m₀ v ζ.2.1.2⟩,
      ⟨pushField (intShift v) ζ.2.2, pushField_mem mk v ζ.2.2.2⟩),
      ⟨rfl, rfl, rfl⟩, ?_⟩
    funext κ
    obtain ⟨p, ι⟩ := κ
    cases p
    · exact coeffs_pushField hL h0 v _ ι
    · exact coeffs_pushField hL h0 v _ ι
    · exact coeffs_pushField hL hk v _ ι
  · have coeff : ∀ (c : Edge L k 0), c.IsPositivelyOriented → ∀ a,
        ‖pauliCoeff a ((ζ.1 : Edge L k 0 → ComplexMatrix2) c)‖ ≤ r := fun c hc a =>
      hr ⟨.background, (a, ⟨c, hc⟩)⟩
    by_cases hb : b.IsPositivelyOriented
    · exact operatorNorm_le_of_pauliCoeff hP (ζ.1.2.1 b hb) (coeff b hb)
    · have hb' := opposite_pos_of_not_pos hb
      have e : (ζ.1 : Edge L k 0 → ComplexMatrix2) b =
          -(ζ.1 : Edge L k 0 → ComplexMatrix2) b.opposite :=
        ζ.1.2.2 b.opposite
      rw [e]
      change ‖-(ζ.1 : Edge L k 0 → ComplexMatrix2) b.opposite‖ ≤ _
      rw [norm_neg]
      exact operatorNorm_le_of_pauliCoeff hP (ζ.1.2.1 _ hb') (coeff _ hb')
end YangMills.Construction.Tower.FullSpace.FieldValues
end
