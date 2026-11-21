import YangMills.Construction.Towers.KernelsOfThreeMapsOfATower
import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
import YangMills.Construction.Towers.TheTorusMatricesOfTheMassiveOperatorFunctionsProof
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.Tower
open LocalKernels LocalKernels.Periodisation
open PeriodicOperators (KernelMatrix swapKernel applyKernel)
def BackgroundHessianFromFormMatrix : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    ∀ (U : Edge L n k 0 → Matrices.ComplexMatrix2) (J : edgeFormSpace L n k 0)
      (μ : edgeFormSpace L n k k)
      (M : KernelMatrix ((edgesAtZero k).colourPairs.ImageCarrier L n)
        ((edgesAtZero k).colourPairs.ImageCarrier L n)),
      (∀ B : edgeFormSpace L n k 0,
        quotBracket L n (edgesAtZero k).colourPairs
            (CellClass.quotCoeffsOn L n (edgesAtZero k)
              (B : Edge L n k 0 → Matrices.ComplexMatrix2))
            (applyKernel M (CellClass.quotCoeffsOn L n (edgesAtZero k)
              (B : Edge L n k 0 → Matrices.ComplexMatrix2))) =
          (backgroundHessianForm U J μ B : ℂ)) →
      ∀ B : edgeFormSpace L n k 0,
        CellClass.quotCoeffsOn L n (edgesAtZero k)
            ((backgroundHessian U J μ B : edgeFormSpace L n k 0) :
              Edge L n k 0 → Matrices.ComplexMatrix2) =
          applyKernel ((1 / 2 : ℂ) • (M + swapKernel M))
            (CellClass.quotCoeffsOn L n (edgesAtZero k)
              (B : Edge L n k 0 → Matrices.ComplexMatrix2))
end YangMills.Construction.Tower
end

open Set
noncomputable section
namespace YangMills.Construction.Tower.HessianOfFormMatrix
open LocalKernels LocalKernels.Periodisation
open PeriodicOperators (KernelMatrix swapKernel applyKernel)
open Matrices
section RealMatrices
variable {ι : Type} [Fintype ι]
def bilinSum (A : ι → ι → ℝ) (u w : ι → ℝ) : ℝ := ∑ i, ∑ j, u i * A i j * w j
theorem bilinSum_add_add (A : ι → ι → ℝ) (u w : ι → ℝ) :
    bilinSum A (u + w) (u + w) = bilinSum A u u + bilinSum A u w + bilinSum A w u + bilinSum A w w := by
  simp only [bilinSum, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring
theorem bilinSum_single_single [DecidableEq ι] (A : ι → ι → ℝ) (i j : ι) :
    bilinSum A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [bilinSum, Pi.single_apply]
theorem eq_zero_of_bilinSum_diag {A : ι → ι → ℝ} (hsymm : ∀ i j, A i j = A j i)
    (hdiag : ∀ u, bilinSum A u u = 0) (i j : ι) : A i j = 0 := by
  classical
  have key := bilinSum_add_add A (Pi.single i 1) (Pi.single j 1)
  rw [hdiag, hdiag, hdiag, bilinSum_single_single, bilinSum_single_single, hsymm j i] at key
  linarith
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
theorem exists_real_symm_part (φ : V ≃ₗ[ℝ] (ι → ℝ)) (q : V → ℝ) (M : ι → ι → ℂ)
    (hM : ∀ x, ∑ i, (φ x i : ℂ) * ∑ j, M i j * (φ x j : ℂ) = (q x : ℂ)) :
    ∃ R : ι → ι → ℝ, (∀ i j, R i j = R j i) ∧
      (∀ i j, (R i j : ℂ) = (1 / 2 : ℂ) * (M i j + M j i)) ∧
      ∀ x, bilinSum R (φ x) (φ x) = q x := by
  set S : ι → ι → ℂ := fun i j => (1 / 2 : ℂ) * (M i j + M j i) with hS
  have hSsymm : ∀ i j, S i j = S j i := fun i j => by
    simp only [hS]
    ring
  have hSform : ∀ u : ι → ℝ, ∑ i, ∑ j, (u i : ℂ) * S i j * (u j : ℂ) = (q (φ.symm u) : ℂ) := by
    intro u
    have hu := hM (φ.symm u)
    simp only [LinearEquiv.apply_symm_apply] at hu
    rw [← hu]
    have hswap : ∑ i, ∑ j, (u i : ℂ) * M j i * (u j : ℂ) =
        ∑ i, ∑ j, (u i : ℂ) * M i j * (u j : ℂ) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hsplit : ∀ i j, (u i : ℂ) * S i j * (u j : ℂ) =
        (1 / 2 : ℂ) * ((u i : ℂ) * M i j * (u j : ℂ)) +
          (1 / 2 : ℂ) * ((u i : ℂ) * M j i * (u j : ℂ)) := fun i j => by
      simp only [hS]
      ring
    have hinner : ∑ i, (u i : ℂ) * ∑ j, M i j * (u j : ℂ) =
        ∑ i, ∑ j, (u i : ℂ) * M i j * (u j : ℂ) := by
      simp only [Finset.mul_sum, mul_assoc]
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hswap, hinner]
    ring
  have hreal : ∀ u, bilinSum (fun i j => (S i j).re) u u = q (φ.symm u) := fun u => by
    have hre := congrArg Complex.re (hSform u)
    simpa [bilinSum, Complex.re_sum] using hre
  have himag : ∀ u, bilinSum (fun i j => (S i j).im) u u = 0 := fun u => by
    have him := congrArg Complex.im (hSform u)
    simpa [bilinSum, Complex.im_sum] using him
  have himzero := eq_zero_of_bilinSum_diag (A := fun i j => (S i j).im)
    (fun i j => congrArg Complex.im (hSsymm i j)) himag
  refine ⟨fun i j => (S i j).re, fun i j => congrArg Complex.re (hSsymm i j), fun i j => ?_,
    fun x => ?_⟩
  · have hz : (S i j).im = 0 := himzero i j
    exact Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im]; exact hz.symm)
  · simpa using hreal (φ x)
theorem exists_linearMap_of_matrix (φ : V ≃ₗ[ℝ] (ι → ℝ)) (R : ι → ι → ℝ) :
    ∃ T : V →ₗ[ℝ] V, ∀ x i, φ (T x) i = ∑ j, R i j * φ x j := by
  classical
  refine ⟨φ.symm.toLinearMap ∘ₗ (Matrix.of R).mulVecLin ∘ₗ φ.toLinearMap, fun x i => ?_⟩
  simp [Matrix.mulVec, dotProduct]
theorem coords_apply_of_symm_form (φ : V ≃ₗ[ℝ] (ι → ℝ)) (T : V →ₗ[ℝ] V) (q : V → ℝ)
    {R : ι → ι → ℝ} (hRsymm : ∀ i j, R i j = R j i) (hRq : ∀ x, bilinSum R (φ x) (φ x) = q x)
    (hTsymm : ∀ x y, ∑ i, φ x i * φ (T y) i = ∑ i, φ (T x) i * φ y i)
    (hTq : ∀ x, ∑ i, φ x i * φ (T x) i = q x) (x : V) (i : ι) :
    φ (T x) i = ∑ j, R i j * φ x j := by
  classical
  set C : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := φ.toLinearMap ∘ₗ T ∘ₗ φ.symm.toLinearMap with hC
  set E := LinearMap.toMatrix' C with hEdef
  have hCE : ∀ u i, C u i = ∑ j, E i j * u j := fun u i => by
    rw [← LinearMap.toMatrix'_mulVec C u]
    rfl
  have hTC : ∀ x, φ (T x) = C (φ x) := fun x => by simp [hC]
  have hEsymm : ∀ a b, E a b = E b a := fun a b => by
    have hab := hTsymm (φ.symm (Pi.single a 1)) (φ.symm (Pi.single b 1))
    simp only [hTC, LinearEquiv.apply_symm_apply, Pi.single_apply, ite_mul, one_mul, zero_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hab
    rw [hCE, hCE] at hab
    simpa [Pi.single_apply] using hab
  have hEq : ∀ u, bilinSum (fun a b => E a b) u u = q (φ.symm u) := fun u => by
    have hu := hTq (φ.symm u)
    simp only [hTC, LinearEquiv.apply_symm_apply] at hu
    rw [← hu]
    simp only [bilinSum, hCE, Finset.mul_sum, mul_assoc]
  have hRu : ∀ u, bilinSum R u u = q (φ.symm u) := fun u => by
    have hu := hRq (φ.symm u)
    simpa using hu
  have hdiff := eq_zero_of_bilinSum_diag (A := fun a b => E a b - R a b)
    (fun a b => by simp only [hEsymm a b, hRsymm a b]) (fun u => by
      have h₁ := hEq u
      have h₂ := hRu u
      simp only [bilinSum, mul_sub, sub_mul, Finset.sum_sub_distrib] at h₁ h₂ ⊢
      linarith)
  rw [hTC, hCE]
  exact Finset.sum_congr rfl fun j _ => by
    rw [sub_eq_zero.1 (hdiff i j)]
end RealMatrices
section PauliCoefficients
open OneLoop (pauliCoordinateEquiv)
theorem pauliCoeff_eq_coord {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a X = pauliCoordinateEquiv ⟨X, hX⟩ a := dif_pos hX
theorem pauliCoeff_pauliSum (z : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, z b • ComplexMatrix2.pauliFamily b) = z a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliSum_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
theorem pauliCoeff_smul (w : ℂ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a (w • X) = w * pauliCoeff a X := by
  rw [pauliCoeff_eq_coord hX, pauliCoeff_eq_coord (ComplexMatrix2.traceless.smul_mem w hX)]
  exact congrFun (map_smul pauliCoordinateEquiv w ⟨X, hX⟩) a
theorem pauliCoeff_im_eq_zero {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff a X).im = 0 := by apply _root_.YangMills.SharedProofs.p23717 <;> assumption
theorem halfTrace_mul_eq_sum {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.halfTrace (X * Y) = ∑ a, pauliCoeff a X * pauliCoeff a Y := by
  have hX11 : X 1 1 = -X 0 0 := by
    have htr : Matrix.trace X = 0 := hX
    rw [Matrix.trace_fin_two] at htr
    linear_combination htr
  have hY11 : Y 1 1 = -Y 0 0 := by
    have htr : Matrix.trace Y = 0 := hY
    rw [Matrix.trace_fin_two] at htr
    linear_combination htr
  have hdivI : ∀ z : ℂ, z / (2 * Complex.I) = -(Complex.I / 2) * z := fun z => by
    rw [div_eq_iff (by simp)]
    linear_combination z * Complex.I_mul_I
  simp only [Fin.sum_univ_three, pauliCoeff_eq_coord hX, pauliCoeff_eq_coord hY]
  show (1 / 2 : ℂ) * Matrix.trace (X * Y) =
    ((X 0 1 + X 1 0) / 2) * ((Y 0 1 + Y 1 0) / 2) +
      ((X 1 0 - X 0 1) / (2 * Complex.I)) * ((Y 1 0 - Y 0 1) / (2 * Complex.I)) + X 0 0 * Y 0 0
  rw [Matrix.trace_fin_two, hdivI, hdivI]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hX11, hY11]
  linear_combination (-(X 1 0 - X 0 1) * (Y 1 0 - Y 0 1) / 4) * Complex.I_mul_I
theorem realPauliSum_mem (t : Fin 3 → ℝ) :
    ∑ a, (t a : ℂ) • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.real_pauli_sum_mem_hermitianTraceless <;> assumption
end PauliCoefficients
section RealCoordinates
variable {L n k : ℕ} {ι : Type} (σ : ι ≃ Fin 3 × PositiveEdge L n k 0)
def formOfReal (t : ι → ℝ) : Edge L n k 0 → ComplexMatrix2 :=
  open Classical in extendOddly fun v =>
    if hv : v.IsPositivelyOriented then
      ∑ a, ((t (σ.symm (a, ⟨v, hv⟩)) : ℝ) : ℂ) • ComplexMatrix2.pauliFamily a
    else 0
theorem formOfReal_of_pos (t : ι → ℝ) {v : Edge L n k 0} (hv : v.IsPositivelyOriented) :
    formOfReal σ t v = ∑ a, ((t (σ.symm (a, ⟨v, hv⟩)) : ℝ) : ℂ) • ComplexMatrix2.pauliFamily a := by
  unfold formOfReal
  rw [extendOddly, if_pos hv]
  exact dif_pos hv
theorem formOfReal_of_not_pos (t : ι → ℝ) {v : Edge L n k 0} (hv : ¬v.IsPositivelyOriented)
    (hv' : v.opposite.IsPositivelyOriented) :
    formOfReal σ t v =
      -∑ a, ((t (σ.symm (a, ⟨v.opposite, hv'⟩)) : ℝ) : ℂ) • ComplexMatrix2.pauliFamily a := by
  unfold formOfReal
  rw [extendOddly, if_neg hv]
  exact congrArg Neg.neg (dif_pos hv')
variable (hxor : ∀ v : Edge L n k 0, Xor v.IsPositivelyOriented v.opposite.IsPositivelyOriented)
include hxor in
theorem formOfReal_mem (t : ι → ℝ) : formOfReal σ t ∈ edgeFormSpace L n k 0 := by
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · rw [formOfReal_of_pos σ t hv]
    exact realPauliSum_mem fun a => t (σ.symm (a, ⟨v, hv⟩))
  · rcases hxor v with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [formOfReal_of_not_pos σ t h₂ h₁, formOfReal_of_pos σ t h₁]
      rfl
    · rw [formOfReal_of_pos σ t h₁, formOfReal_of_not_pos σ t h₂ h₁, neg_neg]
theorem restrict_mem_hermitianTraceless {F : Edge L n k 0 → ComplexMatrix2}
    (hF : F ∈ edgeFormSpace L n k 0) (p : Fin 3 × PositiveEdge L n k 0) :
    restrictToPositiveEdges F p.2 ∈ ComplexMatrix2.hermitianTraceless :=
  hF.1 p.2.1 p.2.2
def realCoords : edgeFormSpace L n k 0 ≃ₗ[ℝ] (ι → ℝ) where
  toFun F i := (toPauliCoeffs (restrictToPositiveEdges (F : Edge L n k 0 → ComplexMatrix2)) (σ i)).re
  map_add' F G := by
    funext i
    have hsum := pauliCoeff_add (restrict_mem_hermitianTraceless F.2 (σ i)).2
      (restrict_mem_hermitianTraceless G.2 (σ i)).2 (σ i).1
    exact congrArg Complex.re hsum
  map_smul' w F := by
    funext i
    have hw := pauliCoeff_smul (w : ℂ) (restrict_mem_hermitianTraceless F.2 (σ i)).2 (σ i).1
    have hres : (w : ℂ) • restrictToPositiveEdges (F : Edge L n k 0 → ComplexMatrix2) (σ i).2 =
        restrictToPositiveEdges ((w • F : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2)
          (σ i).2 := by
      ext p q
      simp [restrictToPositiveEdges]
    rw [hres] at hw
    simp only [toPauliCoeffs, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, hw]
    simp
  invFun t := ⟨formOfReal σ t, formOfReal_mem σ hxor t⟩
  left_inv F := by
    apply Subtype.ext
    have hposEq : ∀ (p : Edge L n k 0) (hp : p.IsPositivelyOriented), formOfReal σ
        (fun i => (toPauliCoeffs (restrictToPositiveEdges (F : Edge L n k 0 → ComplexMatrix2))
          (σ i)).re) p = (F : Edge L n k 0 → ComplexMatrix2) p := fun p hp => by
      rw [formOfReal_of_pos σ _ hp]
      have hmem : (F : Edge L n k 0 → ComplexMatrix2) p ∈ ComplexMatrix2.hermitianTraceless :=
        F.2.1 p hp
      conv_rhs => rw [← pauliSum_pauliCoeff hmem.2]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Equiv.apply_symm_apply]
      congr 1
      exact Complex.ext rfl (by simpa using (pauliCoeff_im_eq_zero hmem a).symm)
    funext v
    show formOfReal σ
      (fun i => (toPauliCoeffs (restrictToPositiveEdges (F : Edge L n k 0 → ComplexMatrix2))
        (σ i)).re) v = _
    rcases hxor v with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hposEq v h₁
    · have hopp := hposEq _ h₁
      rw [formOfReal_of_pos σ _ h₁] at hopp
      rw [formOfReal_of_not_pos σ _ h₂ h₁, hopp, F.2.2 v, neg_neg]
  right_inv t := by
    funext i
    have hcoef := pauliCoeff_pauliSum
      (fun a => ((t (σ.symm (a, (σ i).2)) : ℝ) : ℂ)) (σ i).1
    have hread : toPauliCoeffs (restrictToPositiveEdges (formOfReal σ t)) (σ i) =
        ((t i : ℝ) : ℂ) := by
      show pauliCoeff (σ i).1 (formOfReal σ t (σ i).2.1) = _
      rw [formOfReal_of_pos σ t (σ i).2.2]
      refine hcoef.trans ?_
      simp
    show (toPauliCoeffs (restrictToPositiveEdges (formOfReal σ t)) (σ i)).re = t i
    rw [hread]
    simp
theorem ofReal_realCoords (F : edgeFormSpace L n k 0) (i : ι) :
    ((realCoords σ hxor F i : ℝ) : ℂ) =
      toPauliCoeffs (restrictToPositiveEdges (F : Edge L n k 0 → ComplexMatrix2)) (σ i) :=
  Complex.ext (Complex.ofReal_re _) (by
    rw [Complex.ofReal_im]
    exact (pauliCoeff_im_eq_zero (restrict_mem_hermitianTraceless F.2 (σ i)) (σ i).1).symm)
theorem edgeFormPairing_eq_sum [Fintype ι] (F G : edgeFormSpace L n k 0) :
    edgeFormPairing (F : Edge L n k 0 → ComplexMatrix2) (G : Edge L n k 0 → ComplexMatrix2) =
      ∑ i, ((realCoords σ hxor F i : ℝ) : ℂ) * ((realCoords σ hxor G i : ℝ) : ℂ) := by
  have hfin : Finite (PositiveEdge L n k 0) :=
    Finite.of_surjective (fun i : ι => (σ i).2) fun v => ⟨σ.symm (0, v), by simp⟩
  have := Fintype.ofFinite (PositiveEdge L n k 0)
  simp only [ofReal_realCoords]
  rw [Equiv.sum_comp σ (fun p => toPauliCoeffs (restrictToPositiveEdges
      (F : Edge L n k 0 → ComplexMatrix2)) p *
    toPauliCoeffs (restrictToPositiveEdges (G : Edge L n k 0 → ComplexMatrix2)) p),
    Fintype.sum_prod_type_right]
  unfold edgeFormPairing traceFinsumPairing
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun v _ => ?_
  exact halfTrace_mul_eq_sum (F.2.1 v.1 v.2).2 (G.2.1 v.1 v.2).2
end RealCoordinates
section Conclusion
variable {L n k : ℕ}
def colourPairEquiv (hproj : Function.Surjective
      (Cell.proj n : Cell L k 0 .edge → QuotientCell L n k 0 .edge)) :
    (edgesAtZero k).colourPairs.ImageCarrier L n ≃ Fin 3 × PositiveEdge L n k 0 :=
  Equiv.ofBijective (fun p => p.2.1) (by
    constructor
    · rintro ⟨⟨⟩, s, hs⟩ ⟨⟨⟩, s', hs'⟩ hss
      have hst : s = s' := hss
      subst hst
      rfl
    · rintro ⟨a, v⟩
      obtain ⟨x, hxv⟩ := hproj v
      exact ⟨⟨(), ⟨(a, v), ⟨(a, x), congrArg (Prod.mk a) hxv⟩⟩⟩, rfl⟩)
theorem quotCoeffsOn_backgroundHessian
    (hproj : Function.Surjective (Cell.proj n : Cell L k 0 .edge → QuotientCell L n k 0 .edge))
    (hfin : Finite ((edgesAtZero k).colourPairs.ImageCarrier L n))
    (hxor : ∀ v : Edge L n k 0, Xor v.IsPositivelyOriented v.opposite.IsPositivelyOriented)
    (U : Edge L n k 0 → ComplexMatrix2) (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k)
    (M : KernelMatrix ((edgesAtZero k).colourPairs.ImageCarrier L n)
      ((edgesAtZero k).colourPairs.ImageCarrier L n))
    (hM : ∀ F : edgeFormSpace L n k 0,
      quotBracket L n (edgesAtZero k).colourPairs
          (CellClass.quotCoeffsOn L n (edgesAtZero k) (F : Edge L n k 0 → ComplexMatrix2))
          (applyKernel M
            (CellClass.quotCoeffsOn L n (edgesAtZero k) (F : Edge L n k 0 → ComplexMatrix2))) =
        (backgroundHessianForm U J μ F : ℂ))
    (F : edgeFormSpace L n k 0) :
    CellClass.quotCoeffsOn L n (edgesAtZero k)
        ((backgroundHessian U J μ F : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) =
      applyKernel ((1 / 2 : ℂ) • (M + swapKernel M))
        (CellClass.quotCoeffsOn L n (edgesAtZero k) (F : Edge L n k 0 → ComplexMatrix2)) := by
  have := Fintype.ofFinite ((edgesAtZero k).colourPairs.ImageCarrier L n)
  set σ := colourPairEquiv hproj with hσ
  set φ := realCoords σ hxor with hφ
  have hread : ∀ (G : edgeFormSpace L n k 0) (p : (edgesAtZero k).colourPairs.ImageCarrier L n),
      CellClass.quotCoeffsOn L n (edgesAtZero k) (G : Edge L n k 0 → ComplexMatrix2) p =
        ((φ G p : ℝ) : ℂ) := fun G p => (ofReal_realCoords σ hxor G p).symm
  have hreadFun : ∀ G : edgeFormSpace L n k 0,
      CellClass.quotCoeffsOn L n (edgesAtZero k) (G : Edge L n k 0 → ComplexMatrix2) =
        fun p => ((φ G p : ℝ) : ℂ) := fun G => funext (hread G)
  have hpairSum := edgeFormPairing_eq_sum σ hxor
  obtain ⟨R, hRsymm, hRM, hRq⟩ := exists_real_symm_part φ (backgroundHessianForm U J μ) M
    (fun G => by
      have hG := hM G
      rw [hreadFun] at hG
      unfold quotBracket PeriodicOperators.wPairing at hG
      rw [tsum_fintype] at hG
      rw [← hG]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hwt : (((edgesAtZero k).colourPairs.imageWeight L n i : ℝ) : ℂ) = 1 := by
        show (((1 : ℝ) : ℝ) : ℂ) = 1
        simp
      rw [hwt, one_mul]
      unfold applyKernel
      rw [tsum_fintype])
  obtain ⟨T, hT⟩ := exists_linearMap_of_matrix φ R
  have hpair : ∀ F₁ F₂ : edgeFormSpace L n k 0,
      edgeFormPairing (F₁ : Edge L n k 0 → ComplexMatrix2) (F₂ : Edge L n k 0 → ComplexMatrix2) =
        ((∑ i, φ F₁ i * φ F₂ i : ℝ) : ℂ) := fun F₁ F₂ => by
    rw [hpairSum]
    push_cast
    rfl
  have hTsymm : ∀ F₁ F₂ : edgeFormSpace L n k 0,
      ∑ i, φ F₁ i * φ (T F₂) i = ∑ i, φ (T F₁) i * φ F₂ i := by
    intro F₁ F₂
    simp only [hT, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hRsymm j i]
      ring
  have hTq : ∀ F₁ : edgeFormSpace L n k 0,
      ∑ i, φ F₁ i * φ (T F₁) i = backgroundHessianForm U J μ F₁ := fun F₁ => by
    rw [← hRq F₁]
    simp only [hT, bilinSum, Finset.mul_sum, mul_assoc]
  have hexists : ∃ H, IsBackgroundHessian U J μ H :=
    ⟨T, fun F₁ F₂ => by rw [hpair, hpair, hTsymm], fun F₁ => by rw [hpair, hTq]⟩
  have hH : IsBackgroundHessian U J μ (backgroundHessian U J μ) := Classical.epsilon_spec hexists
  have hHsymm : ∀ F₁ F₂ : edgeFormSpace L n k 0,
      ∑ i, φ F₁ i * φ (backgroundHessian U J μ F₂) i =
        ∑ i, φ (backgroundHessian U J μ F₁) i * φ F₂ i := fun F₁ F₂ => by
    have h := hH.1 F₁ F₂
    rw [hpair, hpair] at h
    exact_mod_cast h
  have hHq : ∀ F₁ : edgeFormSpace L n k 0,
      ∑ i, φ F₁ i * φ (backgroundHessian U J μ F₁) i = backgroundHessianForm U J μ F₁ :=
    fun F₁ => by
      have h := hH.2 F₁
      rw [hpair] at h
      exact_mod_cast h
  funext i
  rw [hread, coords_apply_of_symm_form φ _ _ hRsymm hRq hHsymm hHq F i, hreadFun]
  unfold applyKernel
  rw [tsum_fintype]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hRM i j]
  rfl
end Conclusion
theorem backgroundHessianFromFormMatrix_holds (hper : Periodisation.PeriodisationHolds)
    (horient : PeriodicLattice.BondEndpointsOrientation.Statement) :
    BackgroundHessianFromFormMatrix := by
  intro L hL k hk n hn U J μ M hM F
  obtain ⟨hcells, hclasses, -⟩ := hper L hL k n hn
  exact quotCoeffsOn_backgroundHessian ((hcells 0 (Nat.zero_le k)).1 .edge |>.1)
    (hclasses _).1
    (fun v => ((horient ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ 0 (Nat.zero_le _)).2.2.2 v).2.2.2.2.2)
    U J μ M hM F
end YangMills.Construction.Tower.HessianOfFormMatrix
end
