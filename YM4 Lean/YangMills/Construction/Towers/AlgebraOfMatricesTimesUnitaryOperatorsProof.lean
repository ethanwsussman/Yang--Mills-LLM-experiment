import YangMills.Construction.Towers.AlgebraOfMatricesTimesUnitaryOperators
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations YangMills.Construction.OneLoopNotation
noncomputable section
namespace YangMills.Construction.Tower
open MagneticWeyl
section Auxiliary
variable {L p r : ℕ}
private theorem matMulUnitary_entry (X : Matrix (Fin p) (Fin r) ℂ)
    (V : ScalarL2 L →ₗ[ℂ] ScalarL2 L) (w : VectorL2 L r)
    (x : FullSpace.Vertex L 0 0) (i : Fin p) :
    matMulUnitary X V w x i = ∑ l, X i l * V (coord w l) x 0 := by
  simp [matMulUnitary, applyCoordwise, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
private theorem finsetSum_smul_apply {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → ScalarL2 L) (x : FullSpace.Vertex L 0 0) :
    (∑ l ∈ s, c l • f l) x 0 = ∑ l ∈ s, c l * f l x 0 := by
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp
private theorem coord_eq_finsetSum (Y : Matrix (Fin p) (Fin r) ℂ) (u : VectorL2 L p)
    (c : Fin r → ScalarL2 L) (hu : ∀ x i, u x i = ∑ l, Y i l * c l x 0) (k : Fin p) :
    coord u k = ∑ l, Y k l • c l := by
  refine lp.ext (funext fun x => ?_)
  ext j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [finsetSum_smul_apply, ← hu]
  simp [coord]
private theorem inner_eq_sum_coord (u w : VectorL2 L r) :
    inner ℂ u w = ∑ i, inner ℂ (coord u i) (coord w i) := by
  have hc : ∀ i, ∀ x, inner ℂ (coord u i x) (coord w i x) =
      inner ℂ (u x i) (w x i) := by
    intro i x
    simp [coord, EuclideanSpace.inner_single_left]
    exact mul_comm _ _
  simp only [lp.inner_eq_tsum]
  rw [← Summable.tsum_finsetSum (fun i _ => lp.summable_inner (coord u i) (coord w i))]
  refine tsum_congr fun x => ?_
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => (hc i x).symm
private theorem coord_vectorAtZero_single (k l : Fin r) :
    coord (MagneticWeyl.vectorAtZero L (EuclideanSpace.single k (1 : ℂ))) l =
      if l = k then MagneticWeyl.vectorAtZero L (EuclideanSpace.single 0 (1 : ℂ)) else 0 := by
  refine lp.ext (funext fun x => ?_)
  ext j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  by_cases h : l = k
  · subst h
    simp [coord, MagneticWeyl.vectorAtZero_apply]
  · simp [coord, MagneticWeyl.vectorAtZero_apply, h]
end Auxiliary
theorem matMulUnitaryOpAlgebra_holds (hSeries : UnitaryOperatorSeriesClaim) :
    MatMulUnitaryOpAlgebra := by
  intro L N' N'' _ _ V hV
  have val : ∀ {p r : ℕ} [NeZero p] [NeZero r] (X : Matrix (Fin p) (Fin r) ℂ)
      (U : ScalarL2 L →ₗ[ℂ] ScalarL2 L), IsUnitaryOp U →
      ∀ (w : VectorL2 L r) (x : FullSpace.Vertex L 0 0) (i : Fin p),
        matMulUnitaryOp X U w x i = ∑ l, X i l * U (coord w l) x 0 := by
    intro p r _ _ X U hU w x i
    rw [((hSeries L p r).1 X U hU).1 w x, matMulUnitary_entry]
  refine ⟨fun s X Y => ?_, fun N''' _ V' hV' X Y => ?_, fun V' hV' hadj X => ?_, fun X => ?_⟩
  · refine ContinuousLinearMap.ext fun w => lp.ext (funext fun x => ?_)
    ext i
    rw [val _ _ hV]
    change _ = s * matMulUnitaryOp X V w x i + matMulUnitaryOp Y V w x i
    rw [val _ _ hV, val _ _ hV, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · have hVV' : IsUnitaryOp (V ∘ₗ V') := by
      refine ⟨?_, fun w => ?_⟩
      · rw [LinearMap.coe_comp]
        exact hV.1.comp hV'.1
      · rw [LinearMap.comp_apply, hV.2, hV'.2]
    refine ContinuousLinearMap.ext fun w => lp.ext (funext fun x => ?_)
    ext i
    rw [val _ _ hVV']
    change matMulUnitaryOp X V (matMulUnitaryOp Y V' w) x i = _
    rw [val _ _ hV]
    have hc : ∀ k, coord (matMulUnitaryOp Y V' w) k =
        ∑ l, Y k l • V' (coord w l) := fun k =>
      coord_eq_finsetSum Y _ _ (fun x i => val Y V' hV' w x i) k
    simp only [hc, map_sum, map_smul, finsetSum_smul_apply, Matrix.mul_apply, LinearMap.comp_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  · symm
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun ψ χ => ?_
    have hc1 : ∀ k, coord (matMulUnitaryOp X.conjTranspose V' ψ) k =
        ∑ l, X.conjTranspose k l • V' (coord ψ l) := fun k =>
      coord_eq_finsetSum X.conjTranspose _ _ (fun x i => val X.conjTranspose V' hV' ψ x i) k
    have hc2 : ∀ l, coord (matMulUnitaryOp X V χ) l =
        ∑ k, X l k • V (coord χ k) := fun l =>
      coord_eq_finsetSum X _ _ (fun x i => val X V hV χ x i) l
    rw [inner_eq_sum_coord, inner_eq_sum_coord]
    simp only [hc1, hc2, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hadj,
      Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
    simp
  · ext i k
    change matMulUnitaryOp X V (MagneticWeyl.vectorAtZero L (EuclideanSpace.single k 1)) 0 i = _
    rw [val _ _ hV, Finset.sum_eq_single k]
    · rw [coord_vectorAtZero_single, if_pos rfl]
      simp [mul_comm]
    · intro l _ h
      rw [coord_vectorAtZero_single, if_neg h]
      simp
    · simp
end YangMills.Construction.Tower
end
