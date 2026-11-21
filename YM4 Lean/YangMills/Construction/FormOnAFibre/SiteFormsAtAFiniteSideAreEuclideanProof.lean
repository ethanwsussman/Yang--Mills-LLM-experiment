import YangMills.Construction.FormOnAFibre.SiteFormsAtAFiniteSideAreEuclidean
import YangMills.Construction.Towers.PlaquettesAndSumsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FormOnAFibre
namespace VertexInner
open Tower
section Functions
variable {ι : Type} [Fintype ι]
def lieValue (f : Matrices.GroupLieProduct.hermitianTracelessFunctions ι) (i : ι) :
    Matrices.ComplexMatrix2.LieElement :=
  ⟨(f : ι → Matrices.ComplexMatrix2) i, f.2 i (Set.mem_univ i)⟩
@[instance_reducible]
def innerCore : InnerProductSpace.Core ℝ (Matrices.GroupLieProduct.hermitianTracelessFunctions ι) where
  inner f g := ∑ i, Matrices.ComplexMatrix2.LieElement.innerProductCore.inner (lieValue f i) (lieValue g i)
  conj_inner_symm f g := by
    simp only [conj_trivial]
    refine Finset.sum_congr rfl fun i _ => ?_
    simpa using Matrices.ComplexMatrix2.LieElement.innerProductCore.conj_inner_symm (lieValue f i) (lieValue g i)
  re_inner_nonneg f := by
    simp only [RCLike.re_to_real]
    exact Finset.sum_nonneg fun i _ =>
      Matrices.ComplexMatrix2.LieElement.innerProductCore.re_inner_nonneg (lieValue f i)
  add_left f f' g := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      Matrices.ComplexMatrix2.LieElement.innerProductCore.add_left (lieValue f i) (lieValue f' i) (lieValue g i)
  smul_left f g c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Matrices.ComplexMatrix2.LieElement.innerProductCore.smul_left (lieValue f i) (lieValue g i) c
  definite f h := by
    have hEach := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Matrices.ComplexMatrix2.LieElement.innerProductCore.re_inner_nonneg (lieValue f i)).mp h
    refine Subtype.ext (funext fun i => ?_)
    have := Matrices.ComplexMatrix2.LieElement.innerProductCore.definite _ (hEach i (Finset.mem_univ i))
    exact congrArg Matrices.ComplexMatrix2.LieElement.toMatrix this
theorem traceFinsumPairing_eq_inner (f g : Matrices.GroupLieProduct.hermitianTracelessFunctions ι) :
    traceFinsumPairing (f : ι → Matrices.ComplexMatrix2) (g : ι → Matrices.ComplexMatrix2) =
      (((innerCore (ι := ι)).inner f g : ℝ) : ℂ) := by
  unfold traceFinsumPairing
  rw [finsum_eq_sum_of_fintype]
  show ∑ i, _ = ((∑ i, Matrices.ComplexMatrix2.LieElement.innerProductCore.inner (lieValue f i) (lieValue g i) : ℝ) : ℂ)
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have him : (Matrices.ComplexMatrix2.fullTrace
      ((lieValue f i).toMatrix * (lieValue g i).toMatrix)).im = 0 :=
    Complex.conj_eq_iff_im.mp
      (Matrices.ComplexMatrix2.LieElement.star_fullTrace_mul (lieValue f i) (lieValue g i))
  apply Complex.ext
  · rw [Complex.ofReal_re]
    rfl
  · show (Matrices.ComplexMatrix2.halfTrace ((lieValue f i).toMatrix * (lieValue g i).toMatrix)).im = _
    simp [Matrices.ComplexMatrix2.halfTrace, him]
end Functions
end VertexInner
open Tower in
theorem VertexFunctionsAreEuclidean.holds (hP : FaceSums.FacesAndPairings) :
    VertexFunctionsAreEuclidean.Statement := by
  intro L n k j hL hn hj
  have : Finite (Vertex L n k j) :=
    Set.finite_univ_iff.mp (((hP L hL k j hj).1 n hn).2.1 Set.univ).2.1
  let := Fintype.ofFinite (Vertex L n k j)
  refine ⟨inferInstance, VertexInner.innerCore, fun l l' => ?_⟩
  rw [VertexInner.traceFinsumPairing_eq_inner, Complex.ofReal_re]
end YangMills.Construction.FormOnAFibre
end
