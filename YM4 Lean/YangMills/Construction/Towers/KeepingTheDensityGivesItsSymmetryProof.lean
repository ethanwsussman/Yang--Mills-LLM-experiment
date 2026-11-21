import YangMills.Construction.Towers.FactsOfAbelianFields
import YangMills.Construction.Towers.KeepingTheDensityGivesItsSymmetry
import YangMills.Construction.Towers.LogarithmOfAShiftedOperatorAndIntertwiners
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open OperatorCalculus OneLoopNotation Tower.UnitLatticeL2
namespace Tower.AbelianFieldDensity.SectorDecomposition.DensityInvariance
section Operators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem addScalar_boundedBelow_of_nonneg {T : BddOp H} {z : ℝ} (hz : 0 < z)
    (hT : IsBoundedBelowBy T 0) :
    IsBoundedBelowBy (addScalar T z) (z / 2) := by
  intro u
  obtain ⟨him, hre⟩ := hT u
  have hu : inner ℂ u u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have e : inner ℂ u (addScalar T z u) - ((z / 2 : ℝ) : ℂ) * inner ℂ u u =
      (inner ℂ u (T u) - ((0 : ℝ) : ℂ) * inner ℂ u u) + ((z / 2 * ‖u‖ ^ 2 : ℝ) : ℂ) := by
    simp only [addScalar, scalarOp, add_apply,
      smul_apply, ContinuousLinearMap.id_apply, inner_add_right,
      inner_smul_right, hu]
    push_cast
    ring
  rw [e]
  constructor
  · rw [Complex.add_im, Complex.ofReal_im, him, add_zero]
  · rw [Complex.add_re, Complex.ofReal_re]
    have : 0 ≤ z / 2 * ‖u‖ ^ 2 := by positivity
    linarith
theorem boundedBelow_of_intertwiner {U : H → H} (hU : IsUnitaryMap U) {A A' : BddOp H}
    {z c : ℝ} (hc : ∀ f, U (A f) = A' (U f)) (hA : IsBoundedBelowBy (addScalar A z) c) :
    IsBoundedBelowBy (addScalar A' z) c := by
  obtain ⟨hlin, hbij, hnorm⟩ := hU
  let W : H →ₗᵢ[ℂ] H := ⟨hlin.mk' U, hnorm⟩
  have hinner : ∀ f g : H, inner ℂ (U f) (U g) = inner ℂ f g := fun f g => W.inner_map_map f g
  have hshift : ∀ f : H, addScalar A' z (U f) = U (addScalar A z f) := by
    intro f
    simp only [addScalar, scalarOp, add_apply,
      smul_apply, ContinuousLinearMap.id_apply]
    rw [hlin.map_add, hlin.map_smul, hc]
  intro u
  obtain ⟨f, rfl⟩ := hbij.2 u
  rw [hshift, hinner, hinner]
  exact hA f
theorem toBddOp_conj_eq {U : H → H} (hU : Function.Bijective U) {S S' : BddOp H}
    (hc : ∀ f, U (S f) = S' (U f)) :
    toBddOp (fun f => U (S (Function.invFun U f))) = S' := by
  have hv : ∀ u, S' u = U (S (Function.invFun U u)) := by
    intro u
    rw [hc, Function.rightInverse_invFun hU.2 u]
  have hs := Classical.epsilon_spec
    (p := fun B : BddOp H => ∀ u, B u = U (S (Function.invFun U u))) ⟨S', hv⟩
  exact ContinuousLinearMap.ext fun u => (hs u).trans (hv u).symm
theorem isNormBounded_of_isUnitaryMap {U : H → H} (hU : IsUnitaryMap U) : IsNormBounded U :=
  ⟨1, zero_le_one, fun f => by rw [hU.2.2 f, one_mul]⟩
end Operators
theorem holds (hfacts : Tower.AbelianFieldFacts.AllFacts)
    (hlog : LogShiftedAndIntertwiners) :
    DensityPreservationGivesInvariance := by
  intro L hL z hz n Us Ub hs hb
  refine ⟨hs, hb, ?_⟩
  intro θ θ' hform hΔ hK
  obtain ⟨-, -, hF⟩ := hfacts
  obtain ⟨-, -, -, hθ⟩ := hF L hL z hz
  have hK' : DensityDefined (L := L) z θ' := boundedBelow_of_intertwiner hb.1 hK hform
  refine ⟨hK', fun x => ?_⟩
  obtain ⟨hO, -, -, -, -, hLow, -⟩ := hθ θ
  obtain ⟨hO', -, -, -, -, hLow', -⟩ := hθ θ'
  have sΔ : ShiftedHalfPositive z (laplacianOp θ) :=
    ⟨hO.laplacian_isSelfAdjoint, addScalar_boundedBelow_of_nonneg hz hLow.2⟩
  have sΔ' : ShiftedHalfPositive z (laplacianOp θ') :=
    ⟨hO'.laplacian_isSelfAdjoint, addScalar_boundedBelow_of_nonneg hz hLow'.2⟩
  have sK : ShiftedHalfPositive z (massiveOp θ) := ⟨hO.hessian_isSelfAdjoint, hform⟩
  have sK' : ShiftedHalfPositive z (massiveOp θ') := ⟨hO'.hessian_isSelfAdjoint, hK'⟩
  have cs := (hlog (L2Field (FullSpace.Vertex L 0 0))
    (L2Field (FullSpace.Vertex L 0 0)) z hz).2.2
    (laplacianOp θ) (laplacianOp θ') Us sΔ sΔ' (Or.inl hs.1.1)
    (isNormBounded_of_isUnitaryMap hs.1) hΔ
  have cb := (hlog (L2Field (PeriodicOperators.PosEdge L 0 0))
    (L2Field (PeriodicOperators.PosEdge L 0 0)) z hz).2.2
    (massiveOp θ) (massiveOp θ') Ub sK sK' (Or.inl hb.1.1)
    (isNormBounded_of_isUnitaryMap hb.1) hK
  have keepS := (hs.2 (opLog (addScalar (laplacianOp θ) z))).2 x
  have keepB := (hb.2 (opLog (addScalar (massiveOp θ) z))).2 x
  rw [toBddOp_conj_eq hs.1.2.1 cs] at keepS
  rw [toBddOp_conj_eq hb.1.2.1 cb] at keepB
  unfold densityAt
  rw [keepS, keepB]
end Tower.AbelianFieldDensity.SectorDecomposition.DensityInvariance
end YangMills.Construction
end
