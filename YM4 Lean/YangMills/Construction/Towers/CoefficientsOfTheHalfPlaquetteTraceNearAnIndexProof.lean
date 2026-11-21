import YangMills.Construction.Matrices.ExpProductExpansionAndConjugation
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsFromAnExpansion
import YangMills.Construction.Towers.CoefficientsOfTheHalfPlaquetteTraceNearAnIndex
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChartProof
import YangMills.Construction.Towers.HalfPlaquetteTraceKernelOfAFieldIsLocalProof
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.HalfFaceTraceNearIndex
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.Tower.FullSpace.FinestLatticeNeighbours
open YangMills.Construction.Tower.FullSpace.EntireDependence
def traceLin : ComplexMatrix2 →ₗ[ℂ] ℂ := Matrix.traceLinearMap (Fin 2) ℂ ℂ
def traceNormBound : ℝ := ‖LinearMap.toContinuousLinearMap traceLin‖
theorem traceNormBound_nonneg : 0 ≤ traceNormBound := norm_nonneg _
theorem norm_trace_le_bound (X : ComplexMatrix2) : ‖Matrix.trace X‖ ≤ traceNormBound * ‖X‖ :=
  (LinearMap.toContinuousLinearMap traceLin).le_opNorm X
theorem trace_halfCommutatorSum_eq_zero (Y : Fin 4 → ComplexMatrix2) :
    Matrix.trace (ComplexMatrix2.halfCommutatorSum Y) = 0 := by
  have h : ∀ i, Matrix.trace (∑ j ∈ Finset.Ioi i, (Y i * Y j - Y j * Y i)) = 0 := fun i => by
    rw [Matrix.trace_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  unfold ComplexMatrix2.halfCommutatorSum
  rw [Matrix.trace_smul, Matrix.trace_sum, Finset.sum_eq_zero fun i _ => h i, smul_zero]
theorem half_trace_four_exp_expansion (hP : ComplexMatrix2.ExpProductExpansionAndConjugation)
    (X : Fin 4 → ComplexMatrix2) (htr : ∀ i, Matrix.trace (X i) = 0) :
    ‖(1 / 2 : ℂ) * Matrix.trace (ComplexMatrix2.matExp (X 0) * (ComplexMatrix2.matExp (X 1) *
          (ComplexMatrix2.matExp (X 2) * ComplexMatrix2.matExp (X 3)))) -
        1 - (1 / 4 : ℂ) * Matrix.trace ((∑ i, X i) * ∑ i, X i)‖ ≤
      1 / 2 * traceNormBound *
        (1 / 6 * (∑ i, ComplexMatrix2.operatorNorm (X i)) ^ 3 *
          Real.exp (∑ i, ComplexMatrix2.operatorNorm (X i))) := by
  obtain ⟨-, -, h, h'⟩ := hP.1 4 X _ _ _ _ rfl rfl rfl rfl
  have eP : (List.ofFn fun i => ComplexMatrix2.matExp (X i)).prod =
      ComplexMatrix2.matExp (X 0) * (ComplexMatrix2.matExp (X 1) *
        (ComplexMatrix2.matExp (X 2) * ComplexMatrix2.matExp (X 3))) := by
    simp [List.ofFn_succ]
  rw [eP] at h
  have hs : Matrix.trace (∑ i, X i) = 0 := by
    rw [Matrix.trace_sum]
    exact Finset.sum_eq_zero fun i _ => htr i
  generalize hQ : ComplexMatrix2.matExp (X 0) * (ComplexMatrix2.matExp (X 1) *
    (ComplexMatrix2.matExp (X 2) * ComplexMatrix2.matExp (X 3))) = Q at h ⊢
  have e : (1 / 2 : ℂ) * Matrix.trace Q - 1 - (1 / 4 : ℂ) * Matrix.trace ((∑ i, X i) * ∑ i, X i) =
      (1 / 2 : ℂ) * Matrix.trace (Q - 1 - ∑ i, X i - (1 / 2 : ℂ) • (∑ i, X i) ^ 2 -
        ComplexMatrix2.halfCommutatorSum X) := by
    simp only [Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, trace_halfCommutatorSum_eq_zero, hs,
      Matrix.trace_one, pow_two, Fintype.card_fin]
    push_cast
    ring
  rw [e, norm_mul]
  have h₂ : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h₂, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (norm_trace_le_bound _).trans (mul_le_mul_of_nonneg_left ?_ traceNormBound_nonneg)
  exact (show _ ≤ _ from h).trans h'
theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
def pauliNormSum : ℝ := ∑ a, ‖ComplexMatrix2.pauliFamily a‖
theorem pauliNormSum_nonneg : 0 ≤ pauliNormSum := Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem norm_ofPauliCoeffs_le {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) {m : ℝ}
    (h : ∀ a, ‖c (a, x)‖ ≤ m) : ‖ofPauliCoeffs c x‖ ≤ pauliNormSum * m := by
  have hm : ∀ a, ‖c (a, x) • ComplexMatrix2.pauliFamily a‖ ≤
      ‖ComplexMatrix2.pauliFamily a‖ * m := fun a => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left (h a) (norm_nonneg _)
  calc ‖ofPauliCoeffs c x‖ ≤ ∑ a, ‖c (a, x) • ComplexMatrix2.pauliFamily a‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖ComplexMatrix2.pauliFamily a‖ * m := Finset.sum_le_sum fun a _ => hm a
    _ = pauliNormSum * m := by rw [pauliNormSum, Finset.sum_mul]
theorem pauli_combination_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
variable {L k : ℕ}
theorem halfFaceTraceKernel_diag (hF : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (U : Edge L k 0 → ComplexMatrix2) (ι : Fin 3 × Face L k 0) :
    halfFaceTraceKernel L k U ι ι = halfFaceTrace U ι.2 := by apply _root_.YangMills.Construction.Tower.FullSpace.HalfFaceTraceLocality.halfFaceTraceKernel_diag <;> assumption
theorem halfFaceTraceKernel_of_ne (hF : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (U : Edge L k 0 → ComplexMatrix2) {ι' ι : Fin 3 × Face L k 0} (h : ι' ≠ ι) :
    halfFaceTraceKernel L k U ι' ι = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.HalfFaceTraceLocality.halfFaceTraceKernel_of_ne <;> assumption
theorem finestMesh_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.finestMesh_pos <;> assumption
theorem finestMesh_le_one (hL : Conventions.IsAdmissibleBlockingFactor L) : finestMesh L k ≤ 1 := by
  have hL1 : (1 : ℝ) ≤ L := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  have e : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := by
    simp [finestMesh, meshAt, zpow_neg, zpow_natCast]
  rw [e]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
theorem withinBox_self (hL : Conventions.IsAdmissibleBlockingFactor L)
    (y : InfiniteLattice.AmbientSpace) : WithinBox (2 * finestMesh L k) y y := fun μ => by
  have hη := finestMesh_pos (k := k) hL
  rw [sub_self, abs_zero]
  linarith
theorem withinBox_add_axisStep (hL : Conventions.IsAdmissibleBlockingFactor L) (x : Vertex L k 0)
    (μ : Fin 4) :
    WithinBox (2 * finestMesh L k)
      ((x + InfiniteLattice.axisStep _ μ : Vertex L k 0) : InfiniteLattice.AmbientSpace)
      (x : InfiniteLattice.AmbientSpace) := fun ν => by
  have hη := finestMesh_pos (k := k) hL
  have e : ((x + InfiniteLattice.axisStep _ μ : Vertex L k 0) : InfiniteLattice.AmbientSpace) ν -
        (x : InfiniteLattice.AmbientSpace) ν =
      (Pi.single μ (finestMesh L k) : InfiniteLattice.AmbientSpace) ν := by
    rw [AddSubgroup.coe_add, Pi.add_apply, add_sub_cancel_left]
    rfl
  rw [e]
  by_cases h : ν = μ
  · subst h
    rw [Pi.single_eq_same, abs_of_pos hη]
    linarith
  · rw [Pi.single_eq_of_ne h, abs_zero]
    linarith
def forwardEdge (x : Vertex L k 0) (μ : Fin 4) : PeriodicOperators.PosEdge L k 0 :=
  ⟨InfiniteLattice.Link.forwardFrom x μ, μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
def boundaryEdge (p : Face L k 0) : Fin 4 → PeriodicOperators.PosEdge L k 0 :=
  ![forwardEdge p.corner p.lowAxis,
    forwardEdge (p.corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis,
    forwardEdge (p.corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis,
    forwardEdge p.corner p.highAxis]
theorem withinBox_boundaryEdge_initial (hL : Conventions.IsAdmissibleBlockingFactor L)
    (p : Face L k 0) (i : Fin 4) :
    WithinBox (2 * finestMesh L k) ((boundaryEdge p i).1.initial : InfiniteLattice.AmbientSpace)
      (p.corner : InfiniteLattice.AmbientSpace) := by
  fin_cases i
  · exact withinBox_self hL _
  · exact withinBox_add_axisStep hL _ _
  · exact withinBox_add_axisStep hL _ _
  · exact withinBox_self hL _
open Classical in
def faceIndices (p : Face L k 0) : Finset (remainderIndex L k).Carrier :=
  Finset.univ.biUnion fun i => edgeIndices L k (boundaryEdge p i)
theorem mem_faceIndices (p : Face L k 0) (i : Fin 4) (e : Fin 3) :
    ((e, boundaryEdge p i) : (remainderIndex L k).Carrier) ∈ faceIndices p := by
  let _ : DecidableEq (Fin 3 × PeriodicOperators.PosEdge L k 0) :=
    fun x y => Classical.propDecidable (x = y)
  refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.2 ⟨e, Finset.mem_univ _, rfl⟩
theorem faceVariable_eq (U : Edge L k 0 → ComplexMatrix2) (hU : ∀ b, U b.opposite = (U b)⁻¹)
    (p : Face L k 0) :
    faceVariable U p = U (boundaryEdge p 0).1 * (U (boundaryEdge p 1).1 *
      ((U (boundaryEdge p 2).1)⁻¹ * (U (boundaryEdge p 3).1)⁻¹)) := by
  simp [faceVariable, linkHolonomy, faceBoundary, hU, boundaryEdge, forwardEdge]
theorem ofPauliCoeffs_add {σ : Type} (c c' : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs (c + c') x = ofPauliCoeffs c x + ofPauliCoeffs c' x := by
  simp [ofPauliCoeffs, add_smul, Finset.sum_add_distrib]
theorem ofPauliCoeffs_smul {σ : Type} (z : ℂ) (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs (z • c) x = z • ofPauliCoeffs c x := by
  simp [ofPauliCoeffs, mul_smul, Finset.smul_sum]
def formMatrix (b : PeriodicOperators.PosEdge L k 0) :
    ((remainderIndex L k).Carrier → ℂ) →ₗ[ℂ] ComplexMatrix2 where
  toFun ζ := Complex.I • ofPauliCoeffs ζ b
  map_add' ζ ζ' :=
    (congrArg (Complex.I • ·) (ofPauliCoeffs_add ζ ζ' b)).trans (smul_add _ _ _)
  map_smul' c ζ :=
    (congrArg (Complex.I • ·) (ofPauliCoeffs_smul c ζ b)).trans (smul_comm _ _ _)
theorem formMatrix_apply (b : PeriodicOperators.PosEdge L k 0)
    (ζ : (remainderIndex L k).Carrier → ℂ) :
    formMatrix b ζ = Complex.I • ofPauliCoeffs ζ b := rfl
theorem norm_formMatrix (b : PeriodicOperators.PosEdge L k 0)
    (ζ : (remainderIndex L k).Carrier → ℂ) : ‖formMatrix b ζ‖ = ‖ofPauliCoeffs ζ b‖ := by
  rw [formMatrix_apply, norm_smul, Complex.norm_I, one_mul]
theorem trace_formMatrix (b : PeriodicOperators.PosEdge L k 0)
    (ζ : (remainderIndex L k).Carrier → ℂ) : Matrix.trace (formMatrix b ζ) = 0 := by
  rw [formMatrix_apply, Matrix.trace_smul]
  have h : Matrix.trace (ofPauliCoeffs ζ b) = 0 :=
    pauli_combination_mem_traceless (fun a => ζ (a, b))
  rw [h, smul_zero]
theorem gaugeFieldOfForm_edge (ζ : (remainderIndex L k).Carrier → ℂ)
    (b : PeriodicOperators.PosEdge L k 0) :
    gaugeFieldOfForm L k ζ b.1 = ComplexMatrix2.matExp (formMatrix b ζ) := by
  classical
  have hb := b.2
  change expTwist ((edgePauliCoordinates L k 0).ofCoeffs ζ) 1 b.1 = _
  simp [expTwist, hb, edgePauliCoordinates, extendOddly, formMatrix_apply]
def faceExponents (p : Face L k 0) (ζ : (remainderIndex L k).Carrier → ℂ) :
    Fin 4 → ComplexMatrix2 :=
  ![formMatrix (boundaryEdge p 0) ζ, formMatrix (boundaryEdge p 1) ζ,
    -formMatrix (boundaryEdge p 2) ζ, -formMatrix (boundaryEdge p 3) ζ]
def faceExponentSum (p : Face L k 0) :
    ((remainderIndex L k).Carrier → ℂ) →ₗ[ℂ] ComplexMatrix2 :=
  formMatrix (boundaryEdge p 0) + formMatrix (boundaryEdge p 1) -
    formMatrix (boundaryEdge p 2) - formMatrix (boundaryEdge p 3)
theorem sum_faceExponents (p : Face L k 0) (ζ : (remainderIndex L k).Carrier → ℂ) :
    ∑ i, faceExponents p ζ i = faceExponentSum p ζ := by
  simp [Fin.sum_univ_four, faceExponents, faceExponentSum]
  abel
theorem trace_faceExponents (p : Face L k 0) (ζ : (remainderIndex L k).Carrier → ℂ)
    (i : Fin 4) : Matrix.trace (faceExponents p ζ i) = 0 := by
  fin_cases i <;> simp [faceExponents, trace_formMatrix]
theorem norm_faceExponents_le (p : Face L k 0) (ζ : (remainderIndex L k).Carrier → ℂ)
    {m : ℝ} (h : ∀ i, ‖ofPauliCoeffs ζ (boundaryEdge p i)‖ ≤ m) (i : Fin 4) :
    ‖faceExponents p ζ i‖ ≤ m := by
  have h' : ∀ i, ‖formMatrix (boundaryEdge p i) ζ‖ ≤ m := fun i => by
    rw [norm_formMatrix]
    exact h i
  fin_cases i
  · exact h' 0
  · exact h' 1
  · exact (norm_neg _).le.trans (h' 2)
  · exact (norm_neg _).le.trans (h' 3)
theorem halfFaceTrace_gaugeFieldOfForm (hE : GaugeFieldOfFormEntries)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (p : Face L k 0)
    (ζ : (remainderIndex L k).Carrier → ℂ) :
    halfFaceTrace (gaugeFieldOfForm L k ζ) p =
      (1 / 2 : ℂ) * Matrix.trace (ComplexMatrix2.matExp (faceExponents p ζ 0) *
        (ComplexMatrix2.matExp (faceExponents p ζ 1) *
          (ComplexMatrix2.matExp (faceExponents p ζ 2) *
            ComplexMatrix2.matExp (faceExponents p ζ 3)))) := by
  have hcfg : IsFieldIn PeriodicLattice.complexGaugeGroup (gaugeFieldOfForm L k ζ) :=
    ((hE L hL k).1 ζ)
  rw [halfFaceTrace, faceVariable_eq _ hcfg.2, ComplexMatrix2.fullTrace]
  simp only [gaugeFieldOfForm_edge, matExp_inv]
  rfl
theorem halfFaceTrace_gaugeFieldOfForm_zero (hE : GaugeFieldOfFormEntries)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (p : Face L k 0) :
    halfFaceTrace (gaugeFieldOfForm L k 0) p = 1 := by
  rw [halfFaceTrace_gaugeFieldOfForm hE hL]
  have h : ∀ i, faceExponents p (0 : (remainderIndex L k).Carrier → ℂ) i = 0 := fun i => by
    fin_cases i <;> simp [faceExponents]
  simp [h, NormedSpace.exp_zero, Matrix.trace_one]
def faceForm (p : Face L k 0) :
    ((remainderIndex L k).Carrier → ℂ) →ₗ[ℂ] ((remainderIndex L k).Carrier → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun ζ ζ' => (1 / 2 : ℂ) * Matrix.trace (faceExponentSum p ζ * faceExponentSum p ζ'))
    (fun ζ₁ ζ₂ ζ' => by
      simp only [map_add, add_mul, Matrix.trace_add]
      ring)
    (fun c ζ ζ' => by
      simp only [map_smul, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]
      ring)
    (fun ζ ζ₁ ζ₂ => by
      simp only [map_add, mul_add, Matrix.trace_add])
    (fun c ζ ζ' => by
      simp only [map_smul, mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
      ring)
theorem faceForm_apply (p : Face L k 0) (ζ ζ' : (remainderIndex L k).Carrier → ℂ) :
    faceForm p ζ ζ' = (1 / 2 : ℂ) * Matrix.trace (faceExponentSum p ζ * faceExponentSum p ζ') :=
  rfl
theorem faceForm_symm (p : Face L k 0) (ζ ζ' : (remainderIndex L k).Carrier → ℂ) :
    faceForm p ζ ζ' = faceForm p ζ' ζ := by
  rw [faceForm_apply, faceForm_apply, Matrix.trace_mul_comm]
theorem faceExponentSum_congr (p : Face L k 0) {ξ ξ' : (remainderIndex L k).Carrier → ℂ}
    (h : ∀ κ ∈ (faceIndices p : Set (remainderIndex L k).Carrier), ξ κ = ξ' κ) :
    faceExponentSum p ξ = faceExponentSum p ξ' := by
  have e : ∀ i, formMatrix (boundaryEdge p i) ξ = formMatrix (boundaryEdge p i) ξ' := fun i => by
    simp only [formMatrix_apply, ofPauliCoeffs]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by
      rw [h _ (Finset.mem_coe.2 (mem_faceIndices p i a))]
  simp only [faceExponentSum, LinearMap.sub_apply, LinearMap.add_apply, e]
def cubicRemainderConst : ℝ :=
  1 / 2 * traceNormBound * (1 / 6 * (4 * pauliNormSum) ^ 3 * Real.exp (4 * pauliNormSum))
theorem cubic_remainder_le (hP : ComplexMatrix2.ExpProductExpansionAndConjugation)
    (p : Face L k 0) (ξ : (remainderIndex L k).Carrier → ℂ) {m : ℝ} (hm1 : m ≤ 1)
    (hξ : ∀ κ ∈ (faceIndices p : Set (remainderIndex L k).Carrier), ‖ξ κ‖ ≤ m) :
    ‖(1 / 2 : ℂ) * Matrix.trace (ComplexMatrix2.matExp (faceExponents p ξ 0) *
          (ComplexMatrix2.matExp (faceExponents p ξ 1) *
            (ComplexMatrix2.matExp (faceExponents p ξ 2) *
              ComplexMatrix2.matExp (faceExponents p ξ 3)))) - 1 -
        (1 / 2 : ℂ) * faceForm p ξ ξ‖ ≤ cubicRemainderConst * m ^ 3 := by
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (hξ _ (Finset.mem_coe.2 (mem_faceIndices p 0 0)))
  have hτ := pauliNormSum_nonneg
  have hX : ∀ i, ‖faceExponents p ξ i‖ ≤ pauliNormSum * m :=
    norm_faceExponents_le p ξ fun i => norm_ofPauliCoeffs_le ξ _ fun a =>
      hξ _ (Finset.mem_coe.2 (mem_faceIndices p i a))
  have hσ : ∑ i, ComplexMatrix2.operatorNorm (faceExponents p ξ i) ≤ 4 * pauliNormSum * m := by
    calc ∑ i, ComplexMatrix2.operatorNorm (faceExponents p ξ i) ≤ ∑ _i : Fin 4, pauliNormSum * m :=
          Finset.sum_le_sum fun i _ => hX i
      _ = 4 * pauliNormSum * m := by simp; ring
  have hσ1 : ∑ i, ComplexMatrix2.operatorNorm (faceExponents p ξ i) ≤ 4 * pauliNormSum :=
    hσ.trans (by nlinarith)
  have h := half_trace_four_exp_expansion hP (faceExponents p ξ) (trace_faceExponents p ξ)
  rw [sum_faceExponents] at h
  have e : (1 / 2 : ℂ) * faceForm p ξ ξ =
      (1 / 4 : ℂ) * Matrix.trace (faceExponentSum p ξ * faceExponentSum p ξ) := by
    rw [faceForm_apply]
    ring
  rw [e]
  refine h.trans ?_
  have hb := traceNormBound_nonneg
  calc 1 / 2 * traceNormBound * (1 / 6 * (∑ i, ComplexMatrix2.operatorNorm (faceExponents p ξ i)) ^ 3 *
          Real.exp (∑ i, ComplexMatrix2.operatorNorm (faceExponents p ξ i)))
      ≤ 1 / 2 * traceNormBound *
          (1 / 6 * (4 * pauliNormSum * m) ^ 3 * Real.exp (4 * pauliNormSum)) := by
        gcongr
    _ = cubicRemainderConst * m ^ 3 := by
        rw [cubicRemainderConst]
        ring
abbrev kernelOfForm (L k : ℕ) :
    ((remainderIndex L k).Carrier → ℂ) → (colourFaces L k 0).Carrier →
      (colourFaces L k 0).Carrier → ℂ :=
  fun f => halfFaceTraceKernel L k (gaugeFieldOfForm L k f)
theorem coeffs_diag (hLoc : HalfFaceTraceLocality.HalfFaceTraceKernelIsLocal)
    (hE : GaugeFieldOfFormEntries)
    (hK : FiniteSupportKernel.KernelOfFiniteSupportMap) (hIdx : TowerIndexSets.Claim)
    (hTay : ExpansionCoefficients.Claim)
    (hP : ComplexMatrix2.ExpProductExpansionAndConjugation)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (ι : Fin 3 × Face L k 0)
    (ζ ζ' : (remainderIndex L k).Carrier → ℂ) :
    coeffOne (remainderIndex L k) (colourFaces L k 0) (colourFaces L k 0)
        (kernelOfForm L k) ζ ι ι = 0 ∧
      coeffTwo (remainderIndex L k) (colourFaces L k 0)
        (colourFaces L k 0) (kernelOfForm L k) ζ ζ' ι ι = faceForm ι.2 ζ ζ' := by
  classical
  obtain ⟨-, hF, hQ⟩ := hIdx L hL k 0 (Nat.zero_le k)
  refine hTay _ _ _ hF hQ hQ _ ⟨1, 2 * finestMesh L k, (hLoc L hL k hk).1 1 one_pos⟩ ι ι
    (faceIndices ι.2 : Set (remainderIndex L k).Carrier) (Finset.finite_toSet _)
    0 (faceForm ι.2) 1 cubicRemainderConst one_pos (faceForm_symm _) ?_ ?_ ζ ζ'
  · intro ξ ξ' h
    have e := faceExponentSum_congr ι.2 h
    exact ⟨rfl, fun χ => by rw [faceForm_apply, faceForm_apply, e]⟩
  · intro ξ m hm hξ
    have h := cubic_remainder_le hP ι.2 ξ hm hξ
    have e₁ : kernelOfForm L k ξ ι ι = (1 / 2 : ℂ) *
        Matrix.trace (ComplexMatrix2.matExp (faceExponents ι.2 ξ 0) *
          (ComplexMatrix2.matExp (faceExponents ι.2 ξ 1) *
            (ComplexMatrix2.matExp (faceExponents ι.2 ξ 2) *
              ComplexMatrix2.matExp (faceExponents ι.2 ξ 3)))) :=
      (halfFaceTraceKernel_diag hK _ ι).trans (halfFaceTrace_gaugeFieldOfForm hE hL ι.2 ξ)
    have e₀ : kernelOfForm L k 0 ι ι = 1 :=
      (halfFaceTraceKernel_diag hK _ ι).trans (halfFaceTrace_gaugeFieldOfForm_zero hE hL ι.2)
    change ‖kernelOfForm L k ξ ι ι - kernelOfForm L k 0 ι ι -
      (0 : ((remainderIndex L k).Carrier → ℂ) →ₗ[ℂ] ℂ) ξ -
      (1 / 2 : ℂ) * faceForm ι.2 ξ ξ‖ ≤ _
    rw [e₁, e₀, LinearMap.zero_apply, sub_zero]
    exact h
theorem coeffs_of_ne (hLoc : HalfFaceTraceLocality.HalfFaceTraceKernelIsLocal)
    (hK : FiniteSupportKernel.KernelOfFiniteSupportMap) (hIdx : TowerIndexSets.Claim)
    (hTay : ExpansionCoefficients.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {ι' ι : Fin 3 × Face L k 0}
    (hne : ι' ≠ ι) (ζ ζ' : (remainderIndex L k).Carrier → ℂ) :
    coeffOne (remainderIndex L k) (colourFaces L k 0) (colourFaces L k 0)
        (kernelOfForm L k) ζ ι' ι = 0 ∧
      coeffTwo (remainderIndex L k) (colourFaces L k 0)
        (colourFaces L k 0) (kernelOfForm L k) ζ ζ' ι' ι = 0 := by
  classical
  obtain ⟨-, hF, hQ⟩ := hIdx L hL k 0 (Nat.zero_le k)
  refine hTay _ _ _ hF hQ hQ _ ⟨1, 2 * finestMesh L k, (hLoc L hL k hk).1 1 one_pos⟩ ι' ι
    ∅ Set.finite_empty 0 0 1 0 one_pos (fun _ _ => rfl) (fun _ _ _ => ⟨rfl, fun _ => rfl⟩) ?_ ζ ζ'
  intro ξ m _ _
  have e₁ : ∀ f, kernelOfForm L k f ι' ι = 0 := fun f => halfFaceTraceKernel_of_ne hK _ hne
  simp [e₁]
theorem norm_faceExponentSum_le {p : Face L k 0} {a : (remainderIndex L k).Carrier → ℂ}
    {M : ℝ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (ha : FieldBoundedNear L k (p.corner : InfiniteLattice.AmbientSpace) a M) :
    ‖faceExponentSum p (((finestMesh L k : ℝ) : ℂ) • a)‖ ≤ 4 * M := by
  have hη := finestMesh_pos (k := k) hL
  have hη1 := finestMesh_le_one (k := k) hL
  have hb : ∀ i, ‖formMatrix (boundaryEdge p i) (((finestMesh L k : ℝ) : ℂ) • a)‖ ≤ M :=
    fun i => by
    have h : ‖ofPauliCoeffs a (boundaryEdge p i)‖ ≤ M :=
      ha.1 _ (withinBox_boundaryEdge_initial hL p i)
    have hM : 0 ≤ M := (norm_nonneg _).trans h
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη, norm_formMatrix]
    calc finestMesh L k * ‖ofPauliCoeffs a (boundaryEdge p i)‖ ≤ 1 * M := by gcongr
      _ = M := one_mul M
  simp only [faceExponentSum, LinearMap.sub_apply, LinearMap.add_apply]
  have h₁ := norm_sub_le (formMatrix (boundaryEdge p 0) (((finestMesh L k : ℝ) : ℂ) • a) +
      formMatrix (boundaryEdge p 1) (((finestMesh L k : ℝ) : ℂ) • a) -
      formMatrix (boundaryEdge p 2) (((finestMesh L k : ℝ) : ℂ) • a))
    (formMatrix (boundaryEdge p 3) (((finestMesh L k : ℝ) : ℂ) • a))
  have h₂ := norm_sub_le (formMatrix (boundaryEdge p 0) (((finestMesh L k : ℝ) : ℂ) • a) +
      formMatrix (boundaryEdge p 1) (((finestMesh L k : ℝ) : ℂ) • a))
    (formMatrix (boundaryEdge p 2) (((finestMesh L k : ℝ) : ℂ) • a))
  have h₃ := norm_add_le (formMatrix (boundaryEdge p 0) (((finestMesh L k : ℝ) : ℂ) • a))
    (formMatrix (boundaryEdge p 1) (((finestMesh L k : ℝ) : ℂ) • a))
  have := hb 0
  have := hb 1
  have := hb 2
  have := hb 3
  linarith
theorem halfFaceTraceCoeffsBounded_holds (hLoc : HalfFaceTraceLocality.HalfFaceTraceKernelIsLocal)
    (hE : GaugeFieldOfFormEntries)
    (hK : FiniteSupportKernel.KernelOfFiniteSupportMap) (hIdx : TowerIndexSets.Claim)
    (hTay : ExpansionCoefficients.Claim)
    (hP : ComplexMatrix2.ExpProductExpansionAndConjugation) : HalfFaceTraceCoeffsBounded := by
  classical
  intro L hL
  have hb := traceNormBound_nonneg
  refine ⟨8 * traceNormBound, by linarith, fun k hk => ⟨?_, ?_⟩⟩
  · rintro ζ ζ' ι' ι hfar
    have hne : ι' ≠ ι := by
      rintro rfl
      exact hfar (withinBox_self hL _)
    exact coeffs_of_ne hLoc hK hIdx hTay hL hk hne ζ ζ'
  · rintro A A' M ι' ι hM hA hA'
    by_cases e : ι' = ι
    · subst e
      obtain ⟨h₁, h₂⟩ := coeffs_diag hLoc hE hK hIdx hTay hP hL hk ι'
        (((finestMesh L k : ℝ) : ℂ) • A) (((finestMesh L k : ℝ) : ℂ) • A')
      refine ⟨?_, ?_⟩
      · refine (congrArg norm h₁).le.trans ?_
        rw [norm_zero]
        positivity
      · refine (congrArg norm h₂).le.trans ?_
        have hS := norm_faceExponentSum_le (p := ι'.2) hL hA
        have hS' := norm_faceExponentSum_le (p := ι'.2) hL hA'
        rw [faceForm_apply, norm_mul]
        have h₃ : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
        rw [h₃]
        have h₄ := norm_trace_le_bound (faceExponentSum ι'.2 (((finestMesh L k : ℝ) : ℂ) • A) *
          faceExponentSum ι'.2 (((finestMesh L k : ℝ) : ℂ) • A'))
        have h₅ := norm_mul_le (faceExponentSum ι'.2 (((finestMesh L k : ℝ) : ℂ) • A))
          (faceExponentSum ι'.2 (((finestMesh L k : ℝ) : ℂ) • A'))
        have h₆ : ‖faceExponentSum ι'.2 (((finestMesh L k : ℝ) : ℂ) • A)‖ *
            ‖faceExponentSum ι'.2 (((finestMesh L k : ℝ) : ℂ) • A')‖ ≤ 4 * M * (4 * M) := by
          gcongr
        have h₇ := mul_le_mul_of_nonneg_left (h₅.trans h₆) hb
        nlinarith
    · obtain ⟨h₁, h₂⟩ := coeffs_of_ne hLoc hK hIdx hTay hL hk e
        (((finestMesh L k : ℝ) : ℂ) • A) (((finestMesh L k : ℝ) : ℂ) • A')
      refine ⟨(congrArg norm h₁).le.trans ?_, (congrArg norm h₂).le.trans ?_⟩
      · rw [norm_zero]
        positivity
      · rw [norm_zero]
        positivity
end YangMills.Construction.Tower.FullSpace.HalfFaceTraceNearIndex
end
