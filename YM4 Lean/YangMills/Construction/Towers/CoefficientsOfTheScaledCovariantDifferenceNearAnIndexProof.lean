import YangMills.Construction.Towers.CoefficientsOfTheHalfPlaquetteTraceNearAnIndexProof
import YangMills.Construction.Towers.CoefficientsOfTheHessianCurvatureNearAnIndexProof
import YangMills.Construction.Towers.CoefficientsOfTheScaledCovariantDifferenceNearAnIndex
import YangMills.Construction.Towers.ScaledDifferenceKernelOfAFieldIsLocalProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.CovariantDifferenceCoeffs
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.Tower.FullSpace.FinestLatticeNeighbours
open YangMills.Construction.Tower.FullSpace.EntireDependence
open YangMills.Construction.Matrices.ComplexMatrix2.FourExpConjugation (bracket)
def coeffOfEntries (a : Fin 3) (X : ComplexMatrix2) : ℂ :=
  ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
theorem pauliCoeff_eq_coeffOfEntries (a : Fin 3) {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a X = coeffOfEntries a X := by
  classical
  simp only [pauliCoeff, dif_pos h]
  rfl
def coeffForm (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun := coeffOfEntries a
  map_add' X Y := by
    fin_cases a <;> simp [coeffOfEntries] <;> ring
  map_smul' c X := by
    fin_cases a <;> simp [coeffOfEntries] <;> ring
def coeffFormBound : ℝ := ∑ a, ‖LinearMap.toContinuousLinearMap (coeffForm a)‖
theorem coeffFormBound_nonneg : 0 ≤ coeffFormBound := Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem norm_coeffForm_le (a : Fin 3) (X : ComplexMatrix2) :
    ‖coeffForm a X‖ ≤ coeffFormBound * ‖X‖ := by
  have h := (LinearMap.toContinuousLinearMap (coeffForm a)).le_opNorm X
  have h' : ‖LinearMap.toContinuousLinearMap (coeffForm a)‖ ≤ coeffFormBound :=
    Finset.single_le_sum (f := fun a => ‖LinearMap.toContinuousLinearMap (coeffForm a)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  exact h.trans (mul_le_mul_of_nonneg_right h' (norm_nonneg _))
def pauliNormSum : ℝ := ∑ a, ‖ComplexMatrix2.pauliFamily a‖
theorem pauliNormSum_nonneg : 0 ≤ pauliNormSum := Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem norm_ofPauliCoeffs_le {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) {m : ℝ}
    (h : ∀ a, ‖c (a, x)‖ ≤ m) : ‖ofPauliCoeffs c x‖ ≤ pauliNormSum * m := by apply _root_.YangMills.Construction.Tower.FullSpace.HalfFaceTraceNearIndex.norm_ofPauliCoeffs_le <;> assumption
theorem bracket_add_left (X X' Y : ComplexMatrix2) :
    bracket (X + X') Y = bracket X Y + bracket X' Y := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelCoeffs.bracket_add_fst <;> assumption
theorem bracket_add_right (X Y Y' : ComplexMatrix2) :
    bracket X (Y + Y') = bracket X Y + bracket X Y' := by
  simp only [bracket]
  noncomm_ring
theorem bracket_smul_left (c : ℂ) (X Y : ComplexMatrix2) : bracket (c • X) Y = c • bracket X Y := by
  simp [bracket, smul_sub]
theorem bracket_smul_right (c : ℂ) (X Y : ComplexMatrix2) : bracket X (c • Y) = c • bracket X Y := by
  simp [bracket, smul_sub]
theorem bracket_zero_right (X : ComplexMatrix2) : bracket X 0 = 0 := by simp [bracket]
theorem bracket_zero_left (X : ComplexMatrix2) : bracket 0 X = 0 := by simp [bracket]
theorem norm_bracket_le (X Y : ComplexMatrix2) : ‖bracket X Y‖ ≤ 2 * ‖X‖ * ‖Y‖ := by apply _root_.YangMills.SharedProofs.p42284 <;> assumption
section Forms
variable {E : Type} [AddCommGroup E] [Module ℂ E]
def linearPart (φ : ComplexMatrix2 →ₗ[ℂ] ℂ) (Z : E →ₗ[ℂ] ComplexMatrix2) (Y : ComplexMatrix2) :
    E →ₗ[ℂ] ℂ where
  toFun ζ := φ (bracket (Z ζ) Y)
  map_add' ζ ζ' := by simp only [map_add, bracket_add_left]
  map_smul' c ζ := by simp only [map_smul, bracket_smul_left, RingHom.id_apply]
def symmBracket (P P' Y : ComplexMatrix2) : ComplexMatrix2 :=
  (1 / 2 : ℂ) • (bracket P (bracket P' Y) + bracket P' (bracket P Y))
def quadraticPart (φ : ComplexMatrix2 →ₗ[ℂ] ℂ) (Z : E →ₗ[ℂ] ComplexMatrix2) (Y : ComplexMatrix2) :
    E →ₗ[ℂ] E →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun ζ ζ' => φ (symmBracket (Z ζ) (Z ζ') Y))
    (fun ζ₁ ζ₂ ζ' => by
      simp only [symmBracket, map_add, map_smul, bracket_add_left, bracket_add_right, smul_eq_mul]
      ring)
    (fun c ζ ζ' => by
      simp only [symmBracket, map_add, map_smul, bracket_smul_left, bracket_smul_right, smul_eq_mul]
      ring)
    (fun ζ ζ₁ ζ₂ => by
      simp only [symmBracket, map_add, map_smul, bracket_add_left, bracket_add_right, smul_eq_mul]
      ring)
    (fun c ζ ζ' => by
      simp only [symmBracket, map_add, map_smul, bracket_smul_left, bracket_smul_right, smul_eq_mul]
      ring)
theorem linearPart_apply (φ : ComplexMatrix2 →ₗ[ℂ] ℂ) (Z : E →ₗ[ℂ] ComplexMatrix2)
    (Y : ComplexMatrix2) (ζ : E) :
    linearPart φ Z Y ζ = φ (bracket (Z ζ) Y) := rfl
theorem quadraticPart_apply (φ : ComplexMatrix2 →ₗ[ℂ] ℂ) (Z : E →ₗ[ℂ] ComplexMatrix2)
    (Y : ComplexMatrix2) (ζ ζ' : E) :
    quadraticPart φ Z Y ζ ζ' = φ (symmBracket (Z ζ) (Z ζ') Y) := rfl
theorem quadraticPart_comm (φ : ComplexMatrix2 →ₗ[ℂ] ℂ) (Z : E →ₗ[ℂ] ComplexMatrix2)
    (Y : ComplexMatrix2) (ζ ζ' : E) :
    quadraticPart φ Z Y ζ ζ' = quadraticPart φ Z Y ζ' ζ := by
  simp only [quadraticPart_apply, symmBracket, add_comm]
end Forms
theorem conjugateBy_matExp_expansion
    (hC : ComplexMatrix2.FourExpConjugation.SecondOrderExpansion) (Z Y : ComplexMatrix2)
    (hZ : ‖Z‖ ≤ 1) :
    ‖ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp Z) Y - Y - bracket Z Y -
        (1 / 2 : ℂ) • bracket Z (bracket Z Y)‖ ≤
      10 * Real.exp 1 ^ 2 * ‖Z‖ ^ 3 * ‖Y‖ := by
  have h₁ : ‖Z‖ = ∑ j, ComplexMatrix2.operatorNorm (if j = (0 : Fin 4) then Z else 0) := by
    simp [Fin.sum_univ_four]
  have h₂ : Z = ∑ j, (if j = (0 : Fin 4) then Z else 0) := by
    simp
  have h₃ : (0 : ComplexMatrix2) =
      ComplexMatrix2.halfCommutatorSum fun j : Fin 4 => if j = 0 then Z else 0 := by
    symm
    unfold ComplexMatrix2.halfCommutatorSum
    rw [Finset.sum_eq_zero, smul_zero]
    intro i _
    refine Finset.sum_eq_zero fun i' hi' => ?_
    have : i' ≠ 0 := by
      have := Finset.mem_Ioi.1 hi'
      exact (lt_of_le_of_lt (Fin.zero_le i) this).ne'
    simp [this]
  have h₄ : ComplexMatrix2.matExp Z =
      (List.ofFn fun j : Fin 4 => ComplexMatrix2.matExp (if j = 0 then Z else 0)).prod := by
    simp [List.ofFn_succ, NormedSpace.exp_zero]
  have h := (hC (fun j => if j = 0 then Z else 0) Y ‖Z‖ Z 0 (ComplexMatrix2.matExp Z)
    h₁ hZ h₂ h₃ h₄).1
  rw [bracket_zero_left, add_zero] at h
  exact h
theorem norm_remainder_le
    (hC : ComplexMatrix2.FourExpConjugation.SecondOrderExpansion)
    {E : Type} [AddCommGroup E] [Module ℂ E] (φ : ComplexMatrix2 →ₗ[ℂ] ℂ) {C : ℝ} (hC₀ : 0 ≤ C)
    (hφ : ∀ X, ‖φ X‖ ≤ C * ‖X‖) (Z : E →ₗ[ℂ] ComplexMatrix2) (Y Y' : ComplexMatrix2) (ζ : E)
    (hZ : ‖Z ζ‖ ≤ 1) :
    ‖φ (ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp (Z ζ)) Y - Y') - φ (Y - Y') -
        linearPart φ Z Y ζ - (1 / 2 : ℂ) * quadraticPart φ Z Y ζ ζ‖ ≤
      C * (10 * Real.exp 1 ^ 2 * ‖Z ζ‖ ^ 3 * ‖Y‖) := by
  have e : φ (ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp (Z ζ)) Y - Y') - φ (Y - Y') -
        linearPart φ Z Y ζ - (1 / 2 : ℂ) * quadraticPart φ Z Y ζ ζ =
      φ (ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp (Z ζ)) Y - Y - bracket (Z ζ) Y -
        (1 / 2 : ℂ) • bracket (Z ζ) (bracket (Z ζ) Y)) := by
    simp only [linearPart_apply, quadraticPart_apply, symmBracket, map_sub, map_add, map_smul,
      smul_eq_mul]
    ring
  rw [e]
  exact (hφ _).trans (mul_le_mul_of_nonneg_left (conjugateBy_matExp_expansion hC _ _ hZ) hC₀)
theorem norm_apply_bracket_le {φ : ComplexMatrix2 →ₗ[ℂ] ℂ} {C : ℝ} (hC₀ : 0 ≤ C)
    (hφ : ∀ X, ‖φ X‖ ≤ C * ‖X‖) {P Y : ComplexMatrix2} {p t : ℝ} (hP : ‖P‖ ≤ p) (hY : ‖Y‖ ≤ t) :
    ‖φ (bracket P Y)‖ ≤ C * (2 * p * t) := by
  have hp : 0 ≤ p := (norm_nonneg _).trans hP
  refine (hφ _).trans (mul_le_mul_of_nonneg_left ((norm_bracket_le _ _).trans ?_) hC₀)
  gcongr
theorem norm_apply_symmBracket_le {φ : ComplexMatrix2 →ₗ[ℂ] ℂ} {C : ℝ} (hC₀ : 0 ≤ C)
    (hφ : ∀ X, ‖φ X‖ ≤ C * ‖X‖) {P P' Y : ComplexMatrix2} {p t : ℝ} (hP : ‖P‖ ≤ p)
    (hP' : ‖P'‖ ≤ p) (hY : ‖Y‖ ≤ t) :
    ‖φ (symmBracket P P' Y)‖ ≤ C * (4 * p ^ 2 * t) := by
  have hp : 0 ≤ p := (norm_nonneg _).trans hP
  have hb : ∀ {A B : ComplexMatrix2}, ‖A‖ ≤ p → ‖B‖ ≤ p →
      ‖bracket A (bracket B Y)‖ ≤ 4 * p ^ 2 * t := by
    intro A B hA hB
    have h₁ := norm_bracket_le B Y
    have h₂ : ‖bracket B Y‖ ≤ 2 * p * t := h₁.trans (by gcongr)
    refine (norm_bracket_le _ _).trans ?_
    calc 2 * ‖A‖ * ‖bracket B Y‖ ≤ 2 * p * (2 * p * t) := by gcongr
      _ = 4 * p ^ 2 * t := by ring
  refine (hφ _).trans (mul_le_mul_of_nonneg_left ?_ hC₀)
  have h₃ := norm_add_le (bracket P (bracket P' Y)) (bracket P' (bracket P Y))
  have h₄ := hb hP hP'
  have h₅ := hb hP' hP
  simp only [symmBracket, norm_smul]
  have h₆ : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h₆]
  linarith
theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem trace_conjugateBy {V A : ComplexMatrix2} (hV : V.det = 1) :
    Matrix.trace (ComplexMatrix2.conjugateBy V A) = Matrix.trace A := by apply _root_.YangMills.Construction.Tower.FullSpace.RescaledDifferenceLocality.trace_conjugateBy <;> assumption
def scaledDiff (η : ℝ) (V X Y : ComplexMatrix2) : ComplexMatrix2 :=
  ((η⁻¹ : ℝ) : ℂ) • (ComplexMatrix2.conjugateBy V X - Y)
theorem scaledDiff_mem_traceless (η : ℝ) {V X Y : ComplexMatrix2} (hV : V.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    scaledDiff η V X Y ∈ ComplexMatrix2.traceless := by
  have hA : ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.traceless := by
    change Matrix.trace _ = 0
    rw [trace_conjugateBy hV]
    exact hX
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hA hY)
theorem scaledDiff_add (η : ℝ) (V X X' Y Y' : ComplexMatrix2) :
    scaledDiff η V (X + X') (Y + Y') = scaledDiff η V X Y + scaledDiff η V X' Y' := by
  simp only [scaledDiff, ComplexMatrix2.conjugateBy, mul_add, add_mul, smul_sub, smul_add]
  abel
theorem scaledDiff_smul (η : ℝ) (V X Y : ComplexMatrix2) (c : ℂ) :
    scaledDiff η V (c • X) (c • Y) = c • scaledDiff η V X Y := by
  simp only [scaledDiff, ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub,
    smul_comm c]
variable {L k : ℕ}
theorem finestMesh_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.finestMesh_pos <;> assumption
theorem finestMesh_le_one (hL : Conventions.IsAdmissibleBlockingFactor L) : finestMesh L k ≤ 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.HalfFaceTraceNearIndex.finestMesh_le_one <;> assumption
def covDiffOnCoeffs (U : Edge L k 0 → ComplexMatrix2) :
    (Fin 3 × Vertex L k 0 → ℂ) → Fin 3 × PeriodicOperators.PosEdge L k 0 → ℂ :=
  (vertexCoordinate (Vertex L k 0)).mapOnCoeffs (edgePauliCoordinates L k 0)
    fun l => (finestMesh L k)⁻¹ • covDiff U l
theorem covDiffOnCoeffs_apply {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (f : Fin 3 × Vertex L k 0 → ℂ) (a : Fin 3) (b : PeriodicOperators.PosEdge L k 0) :
    covDiffOnCoeffs U f (a, b) =
      coeffOfEntries a (scaledDiff (finestMesh L k) (U b.1)
        (ofPauliCoeffs f b.1.terminal) (ofPauliCoeffs f b.1.initial)) := by
  classical
  have e : ((finestMesh L k)⁻¹ • covDiff U (ofPauliCoeffs f)) b.1 =
      scaledDiff (finestMesh L k) (U b.1)
        (ofPauliCoeffs f b.1.terminal) (ofPauliCoeffs f b.1.initial) := by
    simp only [Pi.smul_apply, covDiff, extendOddly, if_pos b.2, scaledDiff]
    ext r s
    simp
  change pauliCoeff a (((finestMesh L k)⁻¹ • covDiff U (ofPauliCoeffs f)) b.1) = _
  rw [e, pauliCoeff_eq_coeffOfEntries]
  exact scaledDiff_mem_traceless _ (hU.1 _) (ofPauliCoeffs_mem_traceless _ _)
    (ofPauliCoeffs_mem_traceless _ _)
theorem rescaledOperators_D_apply (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (a : Fin 3) (b : PeriodicOperators.PosEdge L k 0) (ι : Fin 3 × Vertex L k 0) :
    (rescaledOperators L k U).D (a, b) ι =
      coeffOfEntries a (scaledDiff (finestMesh L k) (U b.1)
        (ofPauliCoeffs (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) b.1.terminal)
        (ofPauliCoeffs (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) b.1.initial)) := by
  classical
  have h := (hK (Fin 3 × Vertex L k 0) (Fin 3 × PeriodicOperators.PosEdge L k 0)
    (covDiffOnCoeffs U) ?_ ?_ ?_).2
  · change kernelOfMap (covDiffOnCoeffs U) (a, b) ι = _
    rw [h]
    exact covDiffOnCoeffs_apply hU _ a b
  · intro f g
    funext ⟨a, b⟩
    have hadd : ∀ x, ofPauliCoeffs (f + g) x = ofPauliCoeffs f x + ofPauliCoeffs g x :=
      fun x => by
        simp [ofPauliCoeffs, add_smul, Finset.sum_add_distrib]
    rw [Pi.add_apply, covDiffOnCoeffs_apply hU, covDiffOnCoeffs_apply hU,
      covDiffOnCoeffs_apply hU, hadd, hadd, scaledDiff_add]
    exact (coeffForm a).map_add _ _
  · intro c f
    funext ⟨a, b⟩
    have hsm : ∀ x, ofPauliCoeffs (c • f) x = c • ofPauliCoeffs f x := fun x => by
      simp [ofPauliCoeffs, mul_smul, Finset.smul_sum]
    rw [Pi.smul_apply, covDiffOnCoeffs_apply hU, covDiffOnCoeffs_apply hU, hsm, hsm,
      scaledDiff_smul]
    exact (coeffForm a).map_smul _ _
  · rintro ⟨a, b⟩
    refine ⟨Finset.univ.image (fun e : Fin 3 => (e, b.1.terminal)) ∪
      Finset.univ.image (fun e : Fin 3 => (e, b.1.initial)), fun f g h => ?_⟩
    rw [covDiffOnCoeffs_apply hU, covDiffOnCoeffs_apply hU]
    have hh : ofPauliCoeffs f b.1.terminal = ofPauliCoeffs g b.1.terminal := by
      simp only [ofPauliCoeffs]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [h (e, b.1.terminal)
        (Finset.mem_union_left _ (Finset.mem_image.2 ⟨e, Finset.mem_univ _, rfl⟩))]
    have ht : ofPauliCoeffs f b.1.initial = ofPauliCoeffs g b.1.initial := by
      simp only [ofPauliCoeffs]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [h (e, b.1.initial)
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨e, Finset.mem_univ _, rfl⟩))]
    rw [hh, ht]
theorem ofPauliCoeffs_basisFunction_of_ne {c : Fin 3} {x y : Vertex L k 0} (h : y ≠ x) :
    ofPauliCoeffs (basisFunction (c, x) : Fin 3 × Vertex L k 0 → ℂ) y = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.RescaledDifferenceLocality.ofPauliCoeffs_basisFunction_of_ne <;> assumption
theorem norm_ofPauliCoeffs_basisFunction_le (ι : Fin 3 × Vertex L k 0) (y : Vertex L k 0) :
    ‖ofPauliCoeffs (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) y‖ ≤ pauliNormSum := by
  classical
  have h := norm_ofPauliCoeffs_le (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) y (m := 1)
    fun a => by
      by_cases e : (a, y) = ι
      · have : (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) (a, y) = 1 := if_pos e
        rw [this, norm_one]
      · have : (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) (a, y) = 0 := if_neg e
        rw [this, norm_zero]
        exact zero_le_one
  simpa using h
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
theorem gaugeFieldOfForm_posEdge (ζ : (remainderIndex L k).Carrier → ℂ)
    (b : PeriodicOperators.PosEdge L k 0) :
    gaugeFieldOfForm L k ζ b.1 = ComplexMatrix2.matExp (formMatrix b ζ) := by
  classical
  have hb := b.2
  change expTwist ((edgePauliCoordinates L k 0).ofCoeffs ζ) 1 b.1 = _
  simp [expTwist, hb, edgePauliCoordinates, extendOddly, formMatrix_apply]
def scaledCoeffForm (L k : ℕ) (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ :=
  ((((finestMesh L k)⁻¹ : ℝ)) : ℂ) • coeffForm a
theorem norm_scaledCoeffForm_le (hL : Conventions.IsAdmissibleBlockingFactor L) (a : Fin 3)
    (X : ComplexMatrix2) :
    ‖scaledCoeffForm L k a X‖ ≤ (finestMesh L k)⁻¹ * coeffFormBound * ‖X‖ := by
  have hη := finestMesh_pos (k := k) hL
  simp only [scaledCoeffForm, LinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hη)]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_coeffForm_le a X) (inv_pos.2 hη).le
theorem rescaledOperators_D_gaugeFieldOfForm (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (hEnt : GaugeFieldOfFormEntries) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (ζ : (remainderIndex L k).Carrier → ℂ) (a : Fin 3)
    (b : PeriodicOperators.PosEdge L k 0) (ι : Fin 3 × Vertex L k 0) :
    (rescaledOperators L k (gaugeFieldOfForm L k ζ)).D (a, b) ι =
      scaledCoeffForm L k a (ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp (formMatrix b ζ))
          (ofPauliCoeffs (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) b.1.terminal) -
        ofPauliCoeffs (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) b.1.initial) := by
  rw [rescaledOperators_D_apply hK ((hEnt L hL k).1 ζ), gaugeFieldOfForm_posEdge]
  simp only [scaledDiff, scaledCoeffForm, LinearMap.smul_apply, smul_eq_mul]
  exact (coeffForm a).map_smul _ _
theorem withinBox_self (hL : Conventions.IsAdmissibleBlockingFactor L)
    (y : InfiniteLattice.AmbientSpace) :
    WithinBox (2 * finestMesh L k) y y := by apply _root_.YangMills.Construction.Tower.FullSpace.HalfFaceTraceNearIndex.withinBox_self <;> assumption
theorem withinBox_terminal_initial (hL : Conventions.IsAdmissibleBlockingFactor L)
    (b : PeriodicOperators.PosEdge L k 0) :
    WithinBox (2 * finestMesh L k) (b.1.terminal : InfiniteLattice.AmbientSpace)
      (b.1.initial : InfiniteLattice.AmbientSpace) := fun ν => by
  have hη := finestMesh_pos (k := k) hL
  obtain ⟨μ, hμ⟩ := b.2
  have e : (b.1.terminal : InfiniteLattice.AmbientSpace) -
      (b.1.initial : InfiniteLattice.AmbientSpace) = Pi.single μ (finestMesh L k) :=
    congrArg (fun z : Vertex L k 0 => (z : InfiniteLattice.AmbientSpace)) hμ
  have e' : (b.1.terminal : InfiniteLattice.AmbientSpace) ν -
      (b.1.initial : InfiniteLattice.AmbientSpace) ν =
      (Pi.single μ (finestMesh L k) : InfiniteLattice.AmbientSpace) ν := by
    rw [← e]
    rfl
  rw [e']
  by_cases h : ν = μ
  · subst h
    rw [Pi.single_eq_same, abs_of_pos hη]
    linarith
  · rw [Pi.single_eq_of_ne h, abs_zero]
    linarith
theorem coeffs_eq (hLoc : RescaledDifferenceLocality.RescaledDifferenceKernelIsLocal)
    (hEnt : GaugeFieldOfFormEntries)
    (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hTay : PeriodicOperators.ExpansionCoefficients.Claim)
    (hC : ComplexMatrix2.FourExpConjugation.SecondOrderExpansion)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (a : Fin 3)
    (b : PeriodicOperators.PosEdge L k 0) (ι : Fin 3 × Vertex L k 0)
    (ζ ζ' : (remainderIndex L k).Carrier → ℂ) :
    coeffOne (remainderIndex L k) (colourVertices L k 0) (colourEdges L k 0)
        (fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).D) ζ (a, b) ι =
      linearPart (scaledCoeffForm L k a) (formMatrix b)
        (ofPauliCoeffs (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) b.1.terminal) ζ ∧
    coeffTwo (remainderIndex L k) (colourVertices L k 0) (colourEdges L k 0)
        (fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).D) ζ ζ' (a, b) ι =
      quadraticPart (scaledCoeffForm L k a) (formMatrix b)
        (ofPauliCoeffs (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) b.1.terminal) ζ ζ' := by
  classical
  obtain ⟨hI, hF, -⟩ := hIdx L hL k 0 (Nat.zero_le k)
  have hη := finestMesh_pos (k := k) hL
  have hτ := pauliNormSum_nonneg
  have hC₀ : 0 ≤ (finestMesh L k)⁻¹ * coeffFormBound :=
    mul_nonneg (inv_pos.2 hη).le coeffFormBound_nonneg
  have hφ : ∀ X, ‖scaledCoeffForm L k a X‖ ≤ (finestMesh L k)⁻¹ * coeffFormBound * ‖X‖ :=
    norm_scaledCoeffForm_le hL a
  have hmem : ∀ e : Fin 3, ((e, b) : (remainderIndex L k).Carrier) ∈
      (edgeIndices L k b : Set (remainderIndex L k).Carrier) := fun e => by
    let _ : DecidableEq (Fin 3 × PeriodicOperators.PosEdge L k 0) :=
      fun x y => Classical.propDecidable (x = y)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨e, Finset.mem_univ _, rfl⟩)
  generalize hY : ofPauliCoeffs (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) b.1.terminal = Y
  refine hTay _ _ _ hF hI hF _ ⟨1, 2 * finestMesh L k, (hLoc L hL k hk).1 1 one_pos⟩ (a, b) ι
    (edgeIndices L k b : Set (remainderIndex L k).Carrier) (Finset.finite_toSet _)
    (linearPart (scaledCoeffForm L k a) (formMatrix b) Y)
    (quadraticPart (scaledCoeffForm L k a) (formMatrix b) Y) (pauliNormSum + 1)⁻¹
    ((finestMesh L k)⁻¹ * coeffFormBound * (10 * Real.exp 1 ^ 2 * pauliNormSum ^ 3 * ‖Y‖))
    (inv_pos.2 (by linarith)) (quadraticPart_comm _ _ _) ?_ ?_ ζ ζ'
  · intro ξ ξ' h
    have e : formMatrix b ξ = formMatrix b ξ' := by
      simp only [formMatrix_apply, ofPauliCoeffs]
      congr 1
      exact Finset.sum_congr rfl fun e _ => by rw [h _ (hmem e)]
    exact ⟨by rw [linearPart_apply, linearPart_apply, e], fun χ => by
      rw [quadraticPart_apply, quadraticPart_apply, e]⟩
  · intro ξ m hm hξ
    have hm0 : 0 ≤ m := (norm_nonneg _).trans (hξ _ (hmem 0))
    have hZ : ‖formMatrix b ξ‖ ≤ pauliNormSum * m := by
      rw [norm_formMatrix]
      exact norm_ofPauliCoeffs_le ξ b fun e => hξ _ (hmem e)
    have hZ1 : ‖formMatrix b ξ‖ ≤ 1 := by
      refine hZ.trans ?_
      have h₁ : (pauliNormSum + 1) * (pauliNormSum + 1)⁻¹ = 1 :=
        mul_inv_cancel₀ (by linarith)
      calc pauliNormSum * m ≤ (pauliNormSum + 1) * (pauliNormSum + 1)⁻¹ := by
            gcongr
            linarith
        _ = 1 := h₁
    have hR := norm_remainder_le hC (scaledCoeffForm L k a) hC₀ hφ (formMatrix b) Y
      (ofPauliCoeffs (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) b.1.initial) ξ hZ1
    have e₁ := rescaledOperators_D_gaugeFieldOfForm hK hEnt hL ξ a b ι
    have e₀ := rescaledOperators_D_gaugeFieldOfForm hK hEnt hL 0 a b ι
    rw [hY] at e₁ e₀
    have hAd : ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp (formMatrix b 0)) Y = Y := by
      simp [ComplexMatrix2.conjugateBy, NormedSpace.exp_zero]
    rw [hAd] at e₀
    change ‖(rescaledOperators L k (gaugeFieldOfForm L k ξ)).D (a, b) ι -
      (rescaledOperators L k (gaugeFieldOfForm L k 0)).D (a, b) ι -
      linearPart (scaledCoeffForm L k a) (formMatrix b) Y ξ -
      (1 / 2 : ℂ) * quadraticPart (scaledCoeffForm L k a) (formMatrix b) Y ξ ξ‖ ≤ _
    rw [e₁, e₀]
    refine hR.trans ?_
    calc (finestMesh L k)⁻¹ * coeffFormBound *
          (10 * Real.exp 1 ^ 2 * ‖formMatrix b ξ‖ ^ 3 * ‖Y‖)
        ≤ (finestMesh L k)⁻¹ * coeffFormBound *
            (10 * Real.exp 1 ^ 2 * (pauliNormSum * m) ^ 3 * ‖Y‖) := by
          gcongr
      _ = (finestMesh L k)⁻¹ * coeffFormBound *
            (10 * Real.exp 1 ^ 2 * pauliNormSum ^ 3 * ‖Y‖) * m ^ 3 := by ring
theorem covariantDifferenceCoeffsBounded_holds
    (hLoc : RescaledDifferenceLocality.RescaledDifferenceKernelIsLocal)
    (hEnt : GaugeFieldOfFormEntries)
    (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hTay : PeriodicOperators.ExpansionCoefficients.Claim)
    (hC : ComplexMatrix2.FourExpConjugation.SecondOrderExpansion) :
    CovariantDifferenceCoeffsBounded := by
  classical
  intro L hL
  have hc : 0 ≤ coeffFormBound * pauliNormSum := mul_nonneg coeffFormBound_nonneg pauliNormSum_nonneg
  refine ⟨4 * (coeffFormBound * pauliNormSum), by linarith, fun k hk => ⟨?_, ?_⟩⟩
  · rintro ζ ζ' ⟨a, b⟩ ⟨c, x⟩ hfar
    have hh : b.1.terminal ≠ x := by
      rintro rfl
      exact hfar (withinBox_terminal_initial hL b)
    obtain ⟨h₁, h₂⟩ := coeffs_eq hLoc hEnt hK hIdx hTay hC hL hk a b (c, x) ζ ζ'
    have hY : ofPauliCoeffs (basisFunction (c, x) : Fin 3 × Vertex L k 0 → ℂ) b.1.terminal = 0 :=
      ofPauliCoeffs_basisFunction_of_ne hh
    rw [hY] at h₁ h₂
    refine ⟨h₁.trans ?_, h₂.trans ?_⟩
    · rw [linearPart_apply, bracket_zero_right, map_zero]
    · rw [quadraticPart_apply]
      simp [symmBracket, bracket_zero_right]
  · rintro A A' M ⟨a, b⟩ ⟨c, x⟩ hM hA hA'
    have hη := finestMesh_pos (k := k) hL
    have hη1 := finestMesh_le_one (k := k) hL
    have hC₀ : 0 ≤ (finestMesh L k)⁻¹ * coeffFormBound :=
      mul_nonneg (inv_pos.2 hη).le coeffFormBound_nonneg
    have hφ : ∀ X, ‖scaledCoeffForm L k a X‖ ≤ (finestMesh L k)⁻¹ * coeffFormBound * ‖X‖ :=
      norm_scaledCoeffForm_le hL a
    have hb : ‖ofPauliCoeffs A b‖ ≤ M := hA.1 b (withinBox_self hL _)
    have hb' : ‖ofPauliCoeffs A' b‖ ≤ M := hA'.1 b (withinBox_self hL _)
    have hP : ∀ B : (remainderIndex L k).Carrier → ℂ, ‖ofPauliCoeffs B b‖ ≤ M →
        ‖formMatrix b (((finestMesh L k : ℝ) : ℂ) • B)‖ ≤ finestMesh L k * M := by
      intro B hB
      rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη,
        norm_formMatrix]
      exact mul_le_mul_of_nonneg_left hB hη.le
    have hY := norm_ofPauliCoeffs_basisFunction_le (c, x) b.1.terminal
    obtain ⟨h₁, h₂⟩ := coeffs_eq hLoc hEnt hK hIdx hTay hC hL hk a b (c, x)
      (((finestMesh L k : ℝ) : ℂ) • A) (((finestMesh L k : ℝ) : ℂ) • A')
    refine ⟨?_, ?_⟩
    · refine (congrArg norm h₁).le.trans ?_
      rw [linearPart_apply]
      refine (norm_apply_bracket_le hC₀ hφ (hP A hb) hY).trans ?_
      have e : (finestMesh L k)⁻¹ * coeffFormBound * (2 * (finestMesh L k * M) * pauliNormSum) =
          2 * (coeffFormBound * pauliNormSum) * M := by
        field_simp
      rw [e]
      have := mul_nonneg hc hM
      linarith
    · refine (congrArg norm h₂).le.trans ?_
      rw [quadraticPart_apply]
      refine (norm_apply_symmBracket_le hC₀ hφ (hP A hb) (hP A' hb') hY).trans ?_
      have e : (finestMesh L k)⁻¹ * coeffFormBound *
            (4 * (finestMesh L k * M) ^ 2 * pauliNormSum) =
          4 * (coeffFormBound * pauliNormSum) * M ^ 2 * finestMesh L k := by
        field_simp
      rw [e]
      have h₂ : 0 ≤ 4 * (coeffFormBound * pauliNormSum) * M ^ 2 := by positivity
      exact mul_le_of_le_one_right h₂ hη1
end YangMills.Construction.Tower.FullSpace.CovariantDifferenceCoeffs
end
