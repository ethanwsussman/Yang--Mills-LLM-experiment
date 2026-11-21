import YangMills.Construction.Continuum.EuclideanMotionsAndOperationsOnFunctionsAndTuples
import YangMills.Construction.Conventions.SpatialRotationDefs
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open Motions TestSpaces RotationNotation
namespace UpperHalfTensors
def translateMotion (a : Point4) : RigidMotion :=
  ⟨1, one_mem _, a⟩
theorem translateMotion_toFun (a p : Point4) : (translateMotion a).toFun p = p + a := by
  simp [translateMotion, RigidMotion.toFun]
def translateFun {E : Type*} (a : Point4) (g : Point4 → E) : Point4 → E :=
  actOnPointFun (translateMotion a) g
theorem translateFun_apply {E : Type*} (a : Point4) (g : Point4 → E)
    (p : Point4) : translateFun a g p = g (p - a) := by
  simp [translateFun, actOnPointFun, RigidMotion.invFun, translateMotion]
def rigidHomeomorph (r : RigidMotion) : Point4 ≃ₜ Point4 where
  toFun := r.toFun
  invFun := r.invFun
  left_inv := r.invFun_toFun
  right_inv := r.toFun_invFun
  continuous_toFun := by
    have hL : Continuous (LinearMap.toContinuousLinearMap (Matrix.toLin' r.mat)) :=
      ContinuousLinearMap.continuous _
    have h : r.toFun = fun u => LinearMap.toContinuousLinearMap (Matrix.toLin' r.mat) u + r.shift := by
      funext u
      simp [RigidMotion.toFun, Matrix.toLin'_apply]
    rw [h]
    exact hL.add continuous_const
  continuous_invFun := by
    have hL : Continuous (LinearMap.toContinuousLinearMap (Matrix.toLin' r.mat⁻¹)) :=
      ContinuousLinearMap.continuous _
    have h : r.invFun =
        fun u => LinearMap.toContinuousLinearMap (Matrix.toLin' r.mat⁻¹) (u - r.shift) := by
      funext u
      simp [RigidMotion.invFun, Matrix.toLin'_apply]
    rw [h]
    exact hL.comp (continuous_id.sub continuous_const)
theorem contDiff_invFun (r : RigidMotion) : ContDiff ℝ 1 r.invFun := by
  have h : r.invFun =
      fun u => LinearMap.toContinuousLinearMap (Matrix.toLin' r.mat⁻¹) (u - r.shift) := by
    funext u
    simp [RigidMotion.invFun, Matrix.toLin'_apply]
  rw [h]
  exact (ContinuousLinearMap.contDiff _).comp (contDiff_id.sub contDiff_const)
theorem tsupport_actOnPointFun (r : RigidMotion) (g : Point4 → ℝ) :
    tsupport (actOnPointFun r g) = (rigidHomeomorph r).symm ⁻¹' tsupport g :=
  tsupport_comp_eq_preimage g (rigidHomeomorph r).symm
theorem actOnTuple_mem_disjointSupportTuples (r : RigidMotion) {k : ℕ}
    {Φ : Fin k → Point4 → ℝ} (hΦ : Φ ∈ disjointSupportTuples (Set.univ : Set Point4) k) :
    actOnTuple r Φ ∈ disjointSupportTuples (Set.univ : Set Point4) k := by
  refine ⟨fun i => ⟨(hΦ.1 i).1.comp (contDiff_invFun r), ?_, Set.subset_univ _⟩,
    fun i j hij => ?_⟩
  · exact (hΦ.1 i).2.1.comp_homeomorph (rigidHomeomorph r).symm
  · simp only [actOnTuple, tsupport_actOnPointFun]
    exact (hΦ.2 hij).preimage _
def actOnSTuple (r : RigidMotion) (X : STuple) : STuple :=
  ⟨X.1, actOnTuple r X.2.1, actOnTuple_mem_disjointSupportTuples r X.2.2⟩
end UpperHalfTensors
end YangMills.Construction
