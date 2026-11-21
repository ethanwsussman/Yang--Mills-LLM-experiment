import YangMills.Construction.Coordinates.HolomorphicIffDifferentiable
import YangMills.Construction.Matrices.TracelessHolomorphyDifferentiable
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology Matrix.Norms.L2Operator
open YangMills.Construction.Coordinates YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct
namespace TracelessDifferentiable
variable {ι : Type}
theorem mem_tracelessPi_iff_mem_submodule (A : ι → ComplexMatrix2) :
    A ∈ tracelessPi ι ↔ A ∈ tracelessPiSubmodule ι := by
  simp [tracelessPi, tracelessPiSubmodule, ComplexMatrix2.complexifiedProduct,
    ComplexMatrix2.FactorKind.complexified, Submodule.mem_pi]
theorem supNorm_eq_norm [Fintype ι] (A : ι → ComplexMatrix2) : supNorm A = ‖A‖ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : A = 0 := Subsingleton.elim _ _
    simp [supNorm, h0]
  · refine le_antisymm (ciSup_le fun i => norm_le_pi_norm A i) ?_
    refine (pi_norm_le_iff_of_nonneg (Real.iSup_nonneg fun i => norm_nonneg _)).2 fun i => ?_
    exact le_ciSup (f := fun i => ComplexMatrix2.operatorNorm (A i))
      (Set.finite_range _).bddAbove i
def coordsLinearEquiv [Fintype ι] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : ι ≃ Fin (Fintype.card ι)) :
    ComplexCoordinates (Fintype.card ι * 3) ≃ₗ[ℂ] ↥(tracelessPiSubmodule ι) where
  toFun v := ⟨tupleOfCoords b e v, by
    refine (Submodule.mem_pi).2 fun i _ => ?_
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (b c).2⟩
  map_add' v v' := by
    apply Subtype.ext
    funext i
    simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    apply Subtype.ext
    funext i
    simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, Finset.smul_sum, smul_smul]
  invFun A k :=
    b.repr ⟨A.1 (e.symm (finProdFinEquiv.symm k).1), (Submodule.mem_pi.1 A.2) _ (mem_univ _)⟩
      (finProdFinEquiv.symm k).2
  left_inv v := by
    funext k
    obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective k
    have hsum : (⟨tupleOfCoords b e v (e.symm i),
        (Submodule.mem_pi.1 (show tupleOfCoords b e v ∈ tracelessPiSubmodule ι from
          (Submodule.mem_pi).2 fun i _ =>
            Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (b c).2)) _ (mem_univ _)⟩ :
          ↥ComplexMatrix2.traceless) = ∑ c', v (finProdFinEquiv (i, c')) • b c' := by
      apply Subtype.ext
      simp [tupleOfCoords, ComplexCoordinates.tracelessTuple]
    simp only [Equiv.symm_apply_apply]
    rw [hsum, b.repr_sum_self]
  right_inv A := by
    apply Subtype.ext
    funext i
    have hA : A.1 i ∈ ComplexMatrix2.traceless := (Submodule.mem_pi.1 A.2) i (mem_univ _)
    have h : ∑ c, b.repr ⟨A.1 i, hA⟩ c • (b c : ComplexMatrix2) = A.1 i := by
      have h' := congrArg Subtype.val (b.sum_repr ⟨A.1 i, hA⟩)
      rw [AddSubmonoidClass.coe_finsetSum] at h'
      exact h'
    simpa [tupleOfCoords, ComplexCoordinates.tracelessTuple] using h
theorem isOpen_subtype_of_isSupOpen [Fintype ι] {U : Set (ι → ComplexMatrix2)}
    (hU : IsSupOpen U) :
    IsOpen ((↑) ⁻¹' U : Set ↥(tracelessPiSubmodule ι)) := by
  refine Metric.isOpen_iff.2 fun A hA => ?_
  obtain ⟨r, hr, hball⟩ := hU.2 A.1 hA
  refine ⟨r, hr, fun B hB => ?_⟩
  refine hball B.1 ((mem_tracelessPi_iff_mem_submodule _).2 B.2) ?_
  rw [supNorm_eq_norm]
  have hB' : ‖B - A‖ < r := by simpa [dist_eq_norm] using hB
  simpa using hB'
theorem holomorphicOnTracelessIffDifferentiable_of_holomorphicIff
    (h : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement) :
    GroupLieProduct.HolomorphicOnTracelessIffDifferentiable := by
  intro ι E _ _ _ _ l b e he U f
  let eL : E ≃ₗ[ℂ] ComplexCoordinates l :=
    { e with map_add' := he.map_add, map_smul' := he.map_smul }
  let eC : E ≃L[ℂ] ComplexCoordinates l := eL.toContinuousLinearEquiv
  have main : ∀ ν : ι ≃ Fin (Fintype.card ι),
      (ComplexCoordinates.IsHolomorphicIn (tupleOfCoords b ν ⁻¹' U)
          (e ∘ f ∘ tupleOfCoords b ν) ↔
        IsOpen ((↑) ⁻¹' U : Set ↥(tracelessPiSubmodule ι)) ∧
          DifferentiableOn ℂ (fun A : ↥(tracelessPiSubmodule ι) => f (A : ι → ComplexMatrix2))
            (Subtype.val ⁻¹' U)) := by
    intro ν
    let T : ComplexCoordinates (Fintype.card ι * 3) ≃L[ℂ] ↥(tracelessPiSubmodule ι) :=
      (coordsLinearEquiv b ν).toContinuousLinearEquiv
    have hpre : tupleOfCoords b ν ⁻¹' U = T ⁻¹' ((↑) ⁻¹' U) := rfl
    have hmap : (e ∘ f ∘ tupleOfCoords b ν) =
        eC ∘ (fun A : ↥(tracelessPiSubmodule ι) => f (A : ι → ComplexMatrix2)) ∘ T := rfl
    have hopen : IsOpen (T ⁻¹' ((↑) ⁻¹' U : Set ↥(tracelessPiSubmodule ι))) ↔
        IsOpen ((↑) ⁻¹' U : Set ↥(tracelessPiSubmodule ι)) :=
      T.toHomeomorph.isOpen_preimage
    have hdiff : DifferentiableOn ℂ
        (eC ∘ (fun A : ↥(tracelessPiSubmodule ι) => f (A : ι → ComplexMatrix2)) ∘ T)
          (T ⁻¹' ((↑) ⁻¹' U)) ↔
        DifferentiableOn ℂ (fun A : ↥(tracelessPiSubmodule ι) => f (A : ι → ComplexMatrix2))
          (Subtype.val ⁻¹' U) := by
      rw [eC.comp_differentiableOn_iff]
      exact T.comp_right_differentiableOn_iff
    rw [hpre, hmap]
    constructor
    · intro hh
      have ho := hh.1
      exact ⟨hopen.1 ho, hdiff.1 ((h _ _ _ _ ho).1 hh)⟩
    · rintro ⟨ho, hd⟩
      have ho' := hopen.2 ho
      exact (h _ _ _ _ ho').2 (hdiff.2 hd)
  constructor
  · rintro ⟨ho, hh⟩
    exact ⟨ho, ((main (Fintype.equivFin ι)).1 (hh _)).2⟩
  · rintro ⟨ho, hd⟩
    exact ⟨ho, fun ν => (main ν).2 ⟨isOpen_subtype_of_isSupOpen ho, hd⟩⟩
end TracelessDifferentiable
end YangMills.Construction.Matrices.GroupLieProduct
end
