import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Matrices.SpecialUnitaryScalarVectorParts
import YangMills.Construction.RunningCouplingSlope.TheAverageOfTheChainReadsNearCellsProof
import YangMills.Construction.Towers.ActionOfTheDifferencesOnPlaneWavesProof
import YangMills.Construction.Towers.SaddleOperatorsOfTheScaledPictureOnASideProof
import YangMills.Construction.RunningCouplingSlope.FinePartsAtAnAbelianField
import YangMills.Construction.RunningCouplingSlope.TheLaplacianOfTheFineLatticeReadsNearCellsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower
private def pauliSum (w : Fin 3 → ℂ) : Matrices.ComplexMatrix2 :=
  ∑ a, w a • Matrices.ComplexMatrix2.pauliFamily a
private theorem pauliSum_eq_matrix (w : Fin 3 → ℂ) :
    pauliSum w = !![w 2, w 0 - Complex.I * w 1; w 0 + Complex.I * w 1, -w 2] := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.sum_smul_pauliFamily <;> assumption
private theorem pauliSum_mem_traceless (w : Fin 3 → ℂ) :
    pauliSum w ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.LieInnerProductProof.pauliCombination_mem_traceless <;> assumption
private theorem pauliCoeff_pauliSum (c : Fin 3) (w : Fin 3 → ℂ) :
    pauliCoeff c (pauliSum w) = w c := by apply _root_.YangMills.DeltaSharedProofs.p502539 <;> assumption
private theorem pauliSum_sub (u v : Fin 3 → ℂ) :
    pauliSum u - pauliSum v = pauliSum fun c => u c - v c := by
  simp only [pauliSum, sub_smul, Finset.sum_sub_distrib]
private theorem pauliSum_smul (t : ℂ) (u : Fin 3 → ℂ) :
    t • pauliSum u = pauliSum fun c => t * u c := by apply _root_.YangMills.Construction.Tower.PlaneWaveCoboundaries.smul_pauliSum <;> assumption
private theorem pauliSum_real_smul (t : ℝ) (u : Fin 3 → ℂ) :
    t • pauliSum u = pauliSum fun c => (t : ℂ) * u c := by apply _root_.YangMills.Construction.Tower.PlaneWaveCoboundaries.real_smul_pauliSum <;> assumption
private theorem pauliSum_sum {κ : Type} (S : Finset κ) (u : κ → Fin 3 → ℂ) :
    ∑ i ∈ S, pauliSum (u i) = pauliSum fun c => ∑ i ∈ S, u i c := by apply _root_.YangMills.Construction.Tower.PlaneWaveCoboundaries.sum_pauliSum <;> assumption
private theorem diagExpAngle_mul (a b : ℝ) :
    diagExpAngle a * diagExpAngle b = diagExpAngle (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagExpAngle, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add] <;> ring_nf
private theorem diagExpAngle_zero : diagExpAngle 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagExpAngle]
private theorem diagExpAngle_inv (a : ℝ) : (diagExpAngle a)⁻¹ = diagExpAngle (-a) :=
  Matrix.inv_eq_right_inv (by rw [diagExpAngle_mul]; simp [diagExpAngle_zero])
private theorem cos_two_mul_eq_exp (ψ : ℝ) :
    ((Real.cos (2 * ψ) : ℝ) : ℂ) = (Complex.exp (ψ * Complex.I) * Complex.exp (ψ * Complex.I) +
      Complex.exp (-(ψ * Complex.I)) * Complex.exp (-(ψ * Complex.I))) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, ← Complex.exp_add, ← Complex.exp_add]
  push_cast
  ring_nf
private theorem sin_two_mul_eq_exp (ψ : ℝ) :
    ((Real.sin (2 * ψ) : ℝ) : ℂ) = (Complex.exp (ψ * Complex.I) * Complex.exp (ψ * Complex.I) -
      Complex.exp (-(ψ * Complex.I)) * Complex.exp (-(ψ * Complex.I))) / (2 * Complex.I) := by
  rw [Complex.ofReal_sin, Complex.sin, ← Complex.exp_add, ← Complex.exp_add]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring_nf
private theorem conjugateBy_pauliSum (ψ : ℝ) (w : Fin 3 → ℂ) :
    Matrices.ComplexMatrix2.conjugateBy (diagExpAngle ψ) (pauliSum w) =
      pauliSum fun c => ∑ a, adjointRotation ψ c a * w a := by
  have hI : (2 * Complex.I) ≠ 0 := by simp
  have hEF : Complex.exp (ψ * Complex.I) * Complex.exp (-(ψ * Complex.I)) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [Matrices.ComplexMatrix2.conjugateBy, diagExpAngle_inv, pauliSum_eq_matrix, pauliSum_eq_matrix]
  simp only [Fin.sum_univ_three, adjointRotation, cos_two_mul_eq_exp, sin_two_mul_eq_exp]
  set E := Complex.exp (ψ * Complex.I) with hE
  set F := Complex.exp (-(ψ * Complex.I)) with hF
  have hS : (E * E - F * F) / (2 * Complex.I) = -Complex.I * (E * E - F * F) / 2 := by
    rw [div_eq_iff hI]
    linear_combination (E * E - F * F) * Complex.I_mul_I
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagExpAngle, Matrix.mul_apply, Fin.sum_univ_two, neg_mul, ← hE, ← hF, hS]
  · linear_combination (w 2) * hEF
  · linear_combination (w 0 * (E * E - F * F) / 2) * Complex.I_mul_I
  · linear_combination (-w 0 * (E * E - F * F) / 2) * Complex.I_mul_I
  · linear_combination (w 2) * hEF
private theorem kernelOfMap_eq {N N' : Type} [Fintype N] (M : (N → ℂ) → N' → ℂ)
    (T : KernelMatrix N N') (h : ∀ f ι', M f ι' = ∑ ι, T ι' ι * f ι) : kernelOfMap M = T := by apply _root_.YangMills.SharedProofs.p41761 <;> assumption
open Classical in
private theorem sum_indicator_snd {σ : Type} [Fintype (Fin 3 × σ)] (y : σ) (g : Fin 3 → ℂ)
    (f : Fin 3 × σ → ℂ) :
    ∑ ι : Fin 3 × σ, (if ι.2 = y then g ι.1 else 0) * f ι = ∑ a, g a * f (a, y) := by
  have hinj : Function.Injective fun a : Fin 3 => (a, y) := fun a b h => (Prod.ext_iff.1 h).1
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image fun a : Fin 3 => (a, y)))]
  · rw [Finset.sum_image fun a _ b _ h => hinj h]
    simp
  · intro ι _ hι
    have : ¬ ι.2 = y := fun h => hι (Finset.mem_image.2 ⟨ι.1, Finset.mem_univ _, Prod.ext rfl h.symm⟩)
    simp [this]
variable {L n k : ℕ}
private theorem abelianGaugeField_opposite (φ : Edge L n k 0 → ℝ)
    (hφ : ∀ b, φ b.opposite = -φ b) (b : Edge L n k 0) :
    abelianGaugeField φ b.opposite = (abelianGaugeField φ b)⁻¹ := by
  simp only [abelianGaugeField, hφ, diagExpAngle_inv]
private theorem faceTransports_abelian (φ : Edge L n k 0 → ℝ) (hφ : ∀ b, φ b.opposite = -φ b)
    (p : Face L n k 0) (i : Fin 4) :
    faceTransports (abelianGaugeField φ) p i = diagExpAngle (holonomyAngle φ p i) := by
  have h2 : faceTransports (abelianGaugeField φ) p 2 =
      diagExpAngle (holonomyAngle φ p 2) := by
    simp only [faceTransports, holonomyAngle, abelianGaugeField]
    simp [diagExpAngle_mul, diagExpAngle_inv, sub_eq_add_neg]
  fin_cases i
  · simp [faceTransports, holonomyAngle, diagExpAngle_zero]
  · simp [faceTransports, holonomyAngle, abelianGaugeField]
  · exact h2
  · change faceTransports (abelianGaugeField φ) p 3 = _
    rw [faceTransports_three _ (abelianGaugeField_opposite φ hφ), h2]
    simp only [abelianGaugeField, diagExpAngle_inv, diagExpAngle_mul, holonomyAngle]
    simp [sub_eq_add_neg]
private theorem plaquetteHolonomy_abelian (φ : Edge L n k 0 → ℝ) (hφ : ∀ b, φ b.opposite = -φ b)
    (p : Face L n k 0) :
    PeriodicLattice.plaquetteHolonomy (abelianGaugeField φ) p =
      diagExpAngle (holonomyAngle φ p 3) :=
  faceTransports_abelian φ hφ p 3
private theorem ofPauliCoeffs_apply {σ : Type} (f : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs f x = pauliSum fun a => f (a, x) := rfl
private theorem edgePauliCoordinates_apply (f : Fin 3 × PositiveEdge L n k 0 → ℂ)
    (q : PositiveEdge L n k 0) :
    (edgePauliCoordinates L n k 0).ofCoeffs f q.1 = pauliSum fun a => f (a, q) := by apply _root_.YangMills.Construction.Tower.RescaledSaddleOperators.formOfCoeffs_pos <;> assumption
private theorem covDiff_kernel_abelian [Fintype (Fin 3 × Vertex L n k 0)]
    (φ : Edge L n k 0 → ℝ) :
    (rescaledOperators L n k (abelianGaugeField φ)).D = covDiffEntry L n k φ := by
  classical
  refine kernelOfMap_eq (N := Fin 3 × Vertex L n k 0) (N' := Fin 3 × PositiveEdge L n k 0) _ _ ?_
  rintro f ⟨a', b⟩
  change pauliCoeff a' (((finestMesh L k)⁻¹ • covDiff (abelianGaugeField φ)
    (ofPauliCoeffs f)) b.1) = _
  have e : ((finestMesh L k)⁻¹ • covDiff (abelianGaugeField φ) (ofPauliCoeffs f)) b.1 =
      pauliSum fun c => (((finestMesh L k)⁻¹ : ℝ) : ℂ) *
        ((∑ a, adjointRotation (φ b.1) c a * f (a, b.1.target)) - f (c, b.1.source)) := by
    simp only [Pi.smul_apply, covDiff, extendOddly, if_pos b.2]
    rw [ofPauliCoeffs_apply, ofPauliCoeffs_apply, abelianGaugeField, conjugateBy_pauliSum,
      pauliSum_sub, pauliSum_real_smul]
  rw [e, pauliCoeff_pauliSum]
  have hrow : ∀ ι : Fin 3 × Vertex L n k 0, covDiffEntry L n k φ (a', b) ι * f ι =
      (((finestMesh L k)⁻¹ : ℝ) : ℂ) *
        ((if ι.2 = b.1.target then adjointRotation (φ b.1) a' ι.1 else 0) * f ι -
          (if ι.2 = b.1.source then (if ι.1 = a' then 1 else 0) else 0) * f ι) := by
    intro ι
    unfold covDiffEntry
    dsimp only
    have e1 : (if ι.2 = b.1.source ∧ ι.1 = a' then (1 : ℂ) else 0) =
        if ι.2 = b.1.source then (if ι.1 = a' then 1 else 0) else 0 := by
      by_cases h2 : ι.2 = b.1.source <;> by_cases h3 : ι.1 = a' <;> simp [h2, h3]
    rw [e1]
    ring
  simp only [hrow]
  have s1 : ∑ ι : Fin 3 × Vertex L n k 0,
      (if ι.2 = b.1.target then adjointRotation (φ b.1) a' ι.1 else 0) * f ι =
      ∑ a, adjointRotation (φ b.1) a' a * f (a, b.1.target) := by
    convert sum_indicator_snd b.1.target (fun a => adjointRotation (φ b.1) a' a) f
  have s2 : ∑ ι : Fin 3 × Vertex L n k 0,
      (if ι.2 = b.1.source then (if ι.1 = a' then (1 : ℂ) else 0) else 0) * f ι =
      ∑ a, (if a = a' then (1 : ℂ) else 0) * f (a, b.1.source) := by
    convert sum_indicator_snd b.1.source (fun a => if a = a' then (1 : ℂ) else 0) f
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, s1, s2]
  simp
private theorem holonomyDefectKernel_abelian [Fintype (Fin 3 × PositiveEdge L n k 0)]
    (φ : Edge L n k 0 → ℝ) (hφ : ∀ b, φ b.opposite = -φ b) :
    holonomyDefectKernel L n k (abelianGaugeField φ) = holonomyDefectEntry L n k φ := by
  classical
  refine kernelOfMap_eq (N := Fin 3 × PositiveEdge L n k 0) (N' := Fin 3 × Face L n k 0)
    _ _ ?_
  rintro f ⟨a', p⟩
  change pauliCoeff a' (holonomyDefect (abelianGaugeField φ)
    ((edgePauliCoordinates L n k 0).ofCoeffs f) p) = _
  have hb : ∀ i, (edgePauliCoordinates L n k 0).ofCoeffs f (faceEdge p i) =
      pauliSum fun a => f (a, facePositiveEdge p i) :=
    fun i => edgePauliCoordinates_apply f (facePositiveEdge p i)
  have e : holonomyDefect (abelianGaugeField φ) ((edgePauliCoordinates L n k 0).ofCoeffs f) p =
      pauliSum fun c => (((finestMesh L k)⁻¹ : ℝ) : ℂ) * ∑ i, transportSign i *
        ((∑ a, adjointRotation (holonomyAngle φ p i) c a * f (a, facePositiveEdge p i)) -
          f (c, facePositiveEdge p i)) := by
    unfold holonomyDefect
    simp only [hb, faceTransports_abelian φ hφ, conjugateBy_pauliSum, pauliSum_sub, pauliSum_smul,
      pauliSum_sum, pauliSum_real_smul]
  rw [e, pauliCoeff_pauliSum]
  have hrow : ∀ ι : Fin 3 × PositiveEdge L n k 0, holonomyDefectEntry L n k φ (a', p) ι * f ι =
      (((finestMesh L k)⁻¹ : ℝ) : ℂ) * ∑ i, transportSign i *
        ((if ι.2 = facePositiveEdge p i then
          adjointRotation (holonomyAngle φ p i) a' ι.1 - (if ι.1 = a' then 1 else 0) else 0) *
            f ι) := by
    intro ι
    unfold holonomyDefectEntry
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [hrow]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have s1 : ∑ ι : Fin 3 × PositiveEdge L n k 0,
      (if ι.2 = facePositiveEdge p i then
        adjointRotation (holonomyAngle φ p i) a' ι.1 - (if ι.1 = a' then 1 else 0) else 0) * f ι =
      ∑ a, (adjointRotation (holonomyAngle φ p i) a' a - if a = a' then 1 else 0) *
        f (a, facePositiveEdge p i) := by
    convert sum_indicator_snd (facePositiveEdge p i)
      (fun a => adjointRotation (holonomyAngle φ p i) a' a - if a = a' then 1 else 0) f
  rw [← Finset.mul_sum, s1]
  congr 1
  simp [sub_mul, Finset.sum_sub_distrib]
private theorem half_fullTrace_diagExpAngle (ψ : ℝ) :
    (1 / 2 : ℂ) * Matrices.ComplexMatrix2.fullTrace (diagExpAngle ψ) = (Real.cos ψ : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos, Matrices.ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
  simp [diagExpAngle]
  ring
private theorem halfFaceTraceKernel_abelian [Fintype (Fin 3 × Face L n k 0)]
    (φ : Edge L n k 0 → ℝ) (hφ : ∀ b, φ b.opposite = -φ b) :
    halfFaceTraceKernel L n k (abelianGaugeField φ) = faceTraceEntry L n k φ := by
  classical
  refine kernelOfMap_eq (N := Fin 3 × Face L n k 0) (N' := Fin 3 × Face L n k 0)
    _ _ ?_
  rintro f ⟨a', p⟩
  change pauliCoeff a' (halfFaceTraceMul (abelianGaugeField φ)
    (ofPauliCoeffs f) p) = _
  have e : halfFaceTraceMul (abelianGaugeField φ) (ofPauliCoeffs f) p =
      pauliSum fun c => (Real.cos (holonomyAngle φ p 3) : ℂ) * f (c, p) := by
    unfold halfFaceTraceMul halfFaceTrace
    rw [plaquetteHolonomy_abelian φ hφ, half_fullTrace_diagExpAngle, ofPauliCoeffs_apply,
      pauliSum_smul]
  rw [e, pauliCoeff_pauliSum]
  simp [faceTraceEntry]
private theorem ofCoeffs_basisFunction (ι : Fin 3 × PositiveEdge L n k 0) :
    (edgePauliCoordinates L n k 0).ofCoeffs (basisFunction ι).1 = basisForm ι.1 ι.2 := by
  classical
  unfold basisForm edgePauliCoordinates
  dsimp only
  refine congrArg (@extendOddly L n k 0) (funext fun b => ?_)
  by_cases hb : b.IsPositivelyOriented
  · rw [dif_pos hb]
    by_cases e : b = ι.2.1
    · have e' : (⟨b, hb⟩ : PositiveEdge L n k 0) = ι.2 := Subtype.ext e
      rw [if_pos e, e']
      unfold ofPauliCoeffs
      rw [Finset.sum_eq_single ι.1]
      · have : (basisFunction ι).1 (ι.1, ι.2) = 1 := if_pos rfl
        rw [this, one_smul]
      · intro a _ ha
        have : (basisFunction ι).1 (a, ι.2) = 0 := if_neg fun h => ha (Prod.ext_iff.1 h).1
        rw [this, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg e]
      unfold ofPauliCoeffs
      refine Finset.sum_eq_zero fun a _ => ?_
      have : (basisFunction ι).1 (a, ⟨b, hb⟩) = 0 :=
        if_neg fun h => e (congrArg Subtype.val (Prod.ext_iff.1 h).2)
      rw [this, zero_smul]
  · rw [dif_neg hb, if_neg]
    intro e
    exact hb (e ▸ ι.2.2)
private theorem curvatureKernel_apply (hF : CurvatureHessianFacts.Claim)
    (hS : SymmetricKernels.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hn : 0 < n) (U : Edge L n k 0 → Matrices.ComplexMatrix2)
    (ι' ι : Fin 3 × PositiveEdge L n k 0) :
    curvatureKernel U ι' ι = (1 / 2 : ℂ) * (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) *
      (curvatureBilinear U (basisForm ι'.1 ι'.2) (basisForm ι.1 ι.2) +
        curvatureBilinear U (basisForm ι.1 ι.2) (basisForm ι'.1 ι'.2)) := by
  obtain ⟨⟨β, hβ⟩, -, huniq⟩ := ((hF L hL k hk).1 n hn).1 U
  have hL0 : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  have hη : 0 < finestMesh L k := zpow_pos hL0 _
  have hw : ∀ κ : Fin 3 × PositiveEdge L n k 0,
      0 < meshWeight (σ := PositiveEdge L n k 0) (finestMesh L k) κ :=
    fun _ => pow_pos hη 4
  have hq := (hS.1 _ _ hw β).2
  have hX := huniq _ ⟨hq.2.1.1, fun f => (hq.2.1.2 f).trans (hβ f f)⟩
  have hv : ∀ κ' κ : Fin 3 × PositiveEdge L n k 0,
      β (basisFunction κ') (basisFunction κ) =
        curvatureBilinear U (basisForm κ'.1 κ'.2) (basisForm κ.1 κ.2) := by
    intro κ' κ
    rw [hβ, ofCoeffs_basisFunction, ofCoeffs_basisFunction]
  rw [← hX]
  have hne : finestMesh L k ^ 4 ≠ 0 := (pow_pos hη 4).ne'
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, wTranspose, bilinKernel,
    meshWeight, div_self hne, hv]
  push_cast
  ring
private theorem curvatureMatrix_abelian (φ : Edge L n k 0 → ℝ) (hφ : ∀ b, φ b.opposite = -φ b)
    (hη : finestMesh L k ≠ 0) (p : Face L n k 0) :
    curvatureMatrix (abelianGaugeField φ) p =
      (((finestMesh L k ^ 2)⁻¹ * Real.sin (holonomyAngle φ p 3) : ℝ) : ℂ) •
        Matrices.ComplexMatrix2.pauliFamily 2 := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hη' : (finestMesh L k : ℂ) ≠ 0 := by exact_mod_cast hη
  unfold curvatureMatrix
  rw [plaquetteHolonomy_abelian φ hφ, diagExpAngle_inv]
  set ψ := holonomyAngle φ p 3
  have hs : Complex.sin (ψ : ℂ) =
      (Complex.exp (ψ * Complex.I) - Complex.exp (-(ψ * Complex.I))) / (2 * Complex.I) := by
    rw [Complex.sin]
    have e1 : -(ψ : ℂ) * Complex.I = -(ψ * Complex.I) := by ring
    rw [e1]
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hp : Matrices.ComplexMatrix2.pauliFamily 2 = !![1, 0; 0, -1] :=
    Matrices.ComplexMatrix2.pauliFamily_apply.2.2
  ext i j
  rw [hp]
  push_cast
  rw [hs]
  fin_cases i <;> fin_cases j <;> simp [diagExpAngle, neg_mul] <;> field_simp <;> ring_nf <;>
    simp only [Complex.I_sq] <;> ring
private theorem fullTrace_commutator_pauli (u v : Fin 3 → ℂ) (κ : ℂ) :
    (Complex.I / 2) * Matrices.ComplexMatrix2.fullTrace
      ((pauliSum u * pauliSum v - pauliSum v * pauliSum u) *
        (κ • Matrices.ComplexMatrix2.pauliFamily 2)) =
      κ * crossThird u v := by
  have hp : Matrices.ComplexMatrix2.pauliFamily 2 = !![1, 0; 0, -1] :=
    Matrices.ComplexMatrix2.pauliFamily_apply.2.2
  rw [pauliSum_eq_matrix, pauliSum_eq_matrix, hp, Matrices.ComplexMatrix2.fullTrace,
    Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two, crossThird]
  linear_combination (2 * κ * (u 0 * v 1 - u 1 * v 0)) * Complex.I_mul_I
private theorem transportedForm_basisForm_abelian (φ : Edge L n k 0 → ℝ)
    (hφ : ∀ b, φ b.opposite = -φ b)
    (ι : Fin 3 × PositiveEdge L n k 0) (p : Face L n k 0) (i : Fin 4) :
    transportedForm (abelianGaugeField φ) (basisForm ι.1 ι.2) p i =
      pauliSum fun c => open Classical in if facePositiveEdge p i = ι.2 then
        transportSign i * adjointRotation (holonomyAngle φ p i) c ι.1 else 0 := by
  classical
  unfold transportedForm
  rw [faceTransports_abelian φ hφ]
  have e : basisForm ι.1 ι.2 (faceEdge p i) =
      if facePositiveEdge p i = ι.2 then Matrices.ComplexMatrix2.pauliFamily ι.1 else 0 := by
    unfold basisForm extendOddly
    rw [if_pos (faceEdge_isPositive p i)]
    by_cases h : facePositiveEdge p i = ι.2
    · rw [if_pos h]
      exact if_pos (congrArg Subtype.val h)
    · rw [if_neg h]
      exact if_neg fun h' => h (Subtype.ext h')
  rw [e]
  by_cases h : facePositiveEdge p i = ι.2
  · have hpa : Matrices.ComplexMatrix2.pauliFamily ι.1 =
        pauliSum fun c => if c = ι.1 then 1 else 0 := by
      simp [pauliSum]
    simp only [if_pos h]
    rw [hpa, conjugateBy_pauliSum, pauliSum_smul]
    congr 1
    funext c
    simp
  · simp only [if_neg h]
    simp [Matrices.ComplexMatrix2.conjugateBy, pauliSum]
private theorem curvatureBilinear_basisForm_abelian [Fintype (Face L n k 0)]
    (φ : Edge L n k 0 → ℝ)
    (hφ : ∀ b, φ b.opposite = -φ b) (hη : finestMesh L k ≠ 0)
    (ι' ι : Fin 3 × PositiveEdge L n k 0) :
    curvatureBilinear (abelianGaugeField φ) (basisForm ι'.1 ι'.2) (basisForm ι.1 ι.2) =
      ((finestMesh L k : ℂ) ^ 4) * curvatureHalfSum L n k φ ι' ι := by
  classical
  unfold curvatureBilinear curvatureHalfSum
  rw [finsum_eq_sum_of_fintype]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [curvatureMatrix_abelian φ hφ hη]
  unfold bracketSumOrdered
  simp only [transportedForm_basisForm_abelian φ hφ]
  rw [Finset.sum_mul, Matrices.ComplexMatrix2.fullTrace, Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := fullTrace_commutator_pauli
    (fun c => if facePositiveEdge p i = ι'.2 then
      transportSign i * adjointRotation (holonomyAngle φ p i) c ι'.1 else 0)
    (fun c => if facePositiveEdge p j = ι.2 then
      transportSign j * adjointRotation (holonomyAngle φ p j) c ι.1 else 0)
    ((((finestMesh L k ^ 2)⁻¹ * Real.sin (holonomyAngle φ p 3) : ℝ) : ℂ))
  refine (Eq.trans ?_ this).trans ?_
  · rfl
  · by_cases h1 : facePositiveEdge p i = ι'.2 <;>
      by_cases h2 : facePositiveEdge p j = ι.2 <;>
      simp [h1, h2, crossThird]
    ring
theorem abelianFineKernels_holds (hF : CurvatureHessianFacts.Claim)
    (hS : SymmetricKernels.Claim) : AbelianFineKernels := by
  intro L hL k hk n hn _ _ _ _ φ hφ
  refine ⟨covDiff_kernel_abelian φ, holonomyDefectKernel_abelian φ hφ,
    halfFaceTraceKernel_abelian φ hφ, ?_⟩
  have hL0 : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  have hη : 0 < finestMesh L k := zpow_pos hL0 _
  have hη' : (finestMesh L k : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  funext ι' ι
  rw [curvatureKernel_apply hF hS hL hk hn, curvatureBilinear_basisForm_abelian φ hφ hη.ne',
    curvatureBilinear_basisForm_abelian φ hφ hη.ne']
  push_cast
  field_simp
end YangMills.Construction.RunningCouplingSlope
end
