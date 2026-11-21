import YangMills.Construction.LinearAlgebra.ExteriorSquaresTracesAndTheStarProof
import YangMills.Construction.LinearAlgebra.FreeCurvaturePropagatorIsSymmetricEvenAndContinuousProof
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction.Exterior
namespace BivectorProof
private theorem wedgeProd_apply (a b : Fin 4 → ℝ) (i j : Fin 4) :
    (wedgeProd a b).1 i j = a i * b j - b i * a j := by
  simp [wedgeProd, Matrix.sub_apply, vecMulVec_apply]
private theorem inner_wedgeProd_wedgeProd (a b c d : Fin 4 → ℝ) :
    inner ℝ (wedgeProd a b) (wedgeProd c d) = (a ⬝ᵥ c) * (b ⬝ᵥ d) - (a ⬝ᵥ d) * (b ⬝ᵥ c) := by
  rw [inner_eq_bivInner, bivInner_eq_sum_six]
  simp only [wedgeProd_apply, dotProduct, Fin.sum_univ_four]
  ring
private theorem eq_sum_basis_wedgeProd (w : Bivector) :
    w = w.1 0 1 • wedgeProd (Pi.single 0 1) (Pi.single 1 1) +
        w.1 0 2 • wedgeProd (Pi.single 0 1) (Pi.single 2 1) +
        w.1 0 3 • wedgeProd (Pi.single 0 1) (Pi.single 3 1) +
        w.1 1 2 • wedgeProd (Pi.single 1 1) (Pi.single 2 1) +
        w.1 1 3 • wedgeProd (Pi.single 1 1) (Pi.single 3 1) +
        w.1 2 3 • wedgeProd (Pi.single 2 1) (Pi.single 3 1) := by
  ext i j
  have s01 := w.apply_swap 0 1
  have s02 := w.apply_swap 0 2
  have s03 := w.apply_swap 0 3
  have s12 := w.apply_swap 1 2
  have s13 := w.apply_swap 1 3
  have s23 := w.apply_swap 2 3
  have s00 := w.apply_swap 0 0
  have s11 := w.apply_swap 1 1
  have s22 := w.apply_swap 2 2
  have s33 := w.apply_swap 3 3
  fin_cases i <;> fin_cases j <;>
    simp [wedgeProd_apply, Matrix.add_apply, Matrix.smul_apply] <;> linarith
private theorem eq_zero_of_on_wedgeProd (g : Bivector → ℝ) (hadd : ∀ p q, g (p + q) = g p + g q)
    (hsmul : ∀ (r : ℝ) p, g (r • p) = r * g p) (hzero : ∀ a b, g (wedgeProd a b) = 0)
    (w : Bivector) : g w = 0 := by
  rw [eq_sum_basis_wedgeProd w]
  simp only [hadd, hsmul, hzero, mul_zero, add_zero]
private theorem core_inner_eq (C : InnerProductSpace.Core ℝ Bivector)
    (hC : ∀ a b c d : Fin 4 → ℝ,
      C.toInner.inner (wedgeProd a b) (wedgeProd c d) =
        (a ⬝ᵥ c) * (b ⬝ᵥ d) - (a ⬝ᵥ d) * (b ⬝ᵥ c)) (w z : Bivector) :
    C.toInner.inner w z = inner ℝ w z := by
  have hsym : ∀ p q : Bivector, C.toInner.inner p q = C.toInner.inner q p := fun p q => by
    simpa using C.conj_inner_symm q p
  have hfirst : ∀ a b : Fin 4 → ℝ, ∀ y : Bivector,
      C.toInner.inner y (wedgeProd a b) - inner ℝ y (wedgeProd a b) = 0 := by
    intro a b y
    refine eq_zero_of_on_wedgeProd
      (fun y => C.toInner.inner y (wedgeProd a b) - inner ℝ y (wedgeProd a b)) ?_ ?_ ?_ y
    · intro p q
      simp only [C.add_left, inner_add_left]
      ring
    · intro r p
      simp only [C.smul_left, real_inner_smul_left]
      simp
      ring
    · intro c d
      simp only [hC, inner_wedgeProd_wedgeProd, sub_self]
  have hsecond : C.toInner.inner w z - inner ℝ w z = 0 := by
    refine eq_zero_of_on_wedgeProd (fun y => C.toInner.inner w y - inner ℝ w y) ?_ ?_ ?_ z
    · intro p q
      simp only [hsym w, C.add_left, inner_add_right]
      ring
    · intro r p
      simp only [hsym w, C.smul_left, real_inner_smul_right]
      simp
      ring
    · intro a b
      exact hfirst a b w
  linarith
private theorem exteriorSq_wedgeProd (M : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin 4 → ℝ) :
    exteriorSq M (wedgeProd a b) = wedgeProd (M *ᵥ a) (M *ᵥ b) := by apply _root_.YangMills.SharedProofs.p95030 <;> assumption
private theorem inner_basis_exteriorSq (M : Matrix (Fin 4) (Fin 4) ℝ) (i j k l : Fin 4) :
    inner ℝ (wedgeProd (Pi.single i 1) (Pi.single j 1))
        (exteriorSq M (wedgeProd (Pi.single k 1) (Pi.single l 1))) =
      M i k * M j l - M i l * M j k := by
  rw [exteriorSq_wedgeProd, inner_wedgeProd_wedgeProd]
  simp
private theorem dotProduct_self_eq_one {a : Fin 4 → ℝ} (ha : TorusMetric.euclidNormVec a = 1) :
    a ⬝ᵥ a = 1 := by
  have hs : ∑ i, a i ^ 2 = 1 := Real.sqrt_eq_one.1 ha
  simpa [dotProduct, sq] using hs
abbrev _root_.YangMills.DeltaSharedProofs.p3944 := @dotProduct_self_eq_one
private theorem householder_mulVec (a x : Fin 4 → ℝ) :
    householder a *ᵥ x = x - (2 * (a ⬝ᵥ x)) • a := by
  rw [householder, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, vecMulVec_apply,
    Fin.sum_univ_four]
  ring
abbrev _root_.YangMills.SharedProofs.p79454 := @householder_mulVec
private theorem householder_transpose (a : Fin 4 → ℝ) : (householder a)ᵀ = householder a := by apply _root_.YangMills.Construction.Exterior.PropagatorSymmetry.householder_transpose <;> assumption
private theorem householder_mul_self {a : Fin 4 → ℝ} (ha : a ⬝ᵥ a = 1) :
    householder a * householder a = 1 := by
  ext i j
  have hcol : householder a *ᵥ (householder a *ᵥ Pi.single j 1) = Pi.single j 1 := by
    rw [householder_mulVec, householder_mulVec]
    ext k
    simp only [dotProduct_sub, dotProduct_smul, ha, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hi := congrFun hcol i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hi
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using hi
private theorem ker_wedgeProd {a : Fin 4 → ℝ} (ha : a ⬝ᵥ a = 1) :
    LinearMap.ker (wedgeProd a) = Submodule.span ℝ {a} := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hx
    refine ⟨a ⬝ᵥ x, ?_⟩
    ext j
    have hcomp : ∀ i, a i * x j - x i * a j = 0 := fun i => by
      have hij := congrArg (fun w : Bivector => w.1 i j) hx
      simpa [wedgeProd_apply] using hij
    have c0 := hcomp 0
    have c1 := hcomp 1
    have c2 := hcomp 2
    have c3 := hcomp 3
    simp only [dotProduct, Fin.sum_univ_four] at ha
    simp only [Pi.smul_apply, smul_eq_mul, dotProduct, Fin.sum_univ_four]
    linear_combination (x j) * ha - a 0 * c0 - a 1 * c1 - a 2 * c2 - a 3 * c3
  · rintro ⟨r, rfl⟩
    ext i j
    simp [wedgeProd_apply]
private theorem finrank_wedgeRange {a : Fin 4 → ℝ} (ha : a ⬝ᵥ a = 1) :
    Module.finrank ℝ (wedgeRange a) = 3 := by
  have hne : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hrk := LinearMap.finrank_range_add_finrank_ker (wedgeProd a)
  rw [ker_wedgeProd ha, finrank_span_singleton hne] at hrk
  simp at hrk
  change Module.finrank ℝ (LinearMap.range (wedgeProd a)) = 3
  omega
private theorem wedgeVolume_eq_det (a b c d : Fin 4 → ℝ) :
    wedgeVolume (wedgeProd a b) (wedgeProd c d) = ((Matrix.of ![a, b, c, d])ᵀ).det := by
  rw [Matrix.det_transpose, Matrix.det_succ_row_zero]
  simp only [wedgeVolume, wedgeProd_apply, Fin.sum_univ_four, Matrix.det_fin_three,
    Matrix.submatrix_apply, Matrix.of_apply]
  simp [Fin.succAbove, Fin.succ]
  ring
end BivectorProof
open BivectorProof in
theorem bivectorInnerMinorsReflectionDet_holds : BivectorInnerMinorsReflectionDet := by
  refine ⟨inner_wedgeProd_wedgeProd, fun C hC w z => core_inner_eq C hC w z,
    fun M i j k l _ _ => inner_basis_exteriorSq M i j k l, fun a ha => ?_, wedgeVolume_eq_det⟩
  have hdot := dotProduct_self_eq_one ha
  refine ⟨householder_transpose a, ?_, ?_, ?_, finrank_wedgeRange hdot⟩
  · rw [Matrix.mem_orthogonalGroup_iff, householder_transpose]
    exact householder_mul_self hdot
  · rw [householder_mulVec, hdot]
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    ring
  · intro x hx
    rw [householder_mulVec, hx]
    simp
end YangMills.Construction.Exterior
end
