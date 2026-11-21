import YangMills.Construction.ConfigurationSpace.IterDirDerivLinear
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
namespace DirDerivLinearity
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
def LinearOnSmoothSet (D : (V → ℂ) → V → ℂ) : Prop :=
  (∀ f ∈ smoothSet V, D f ∈ smoothSet V) ∧
    (∀ f ∈ smoothSet V, ∀ g ∈ smoothSet V, D (f + g) = D f + D g) ∧
    ∀ (c : ℂ), ∀ f ∈ smoothSet V, D (c • f) = c • D f
theorem linearOnSmoothSet_id : LinearOnSmoothSet (fun f : V → ℂ => f) :=
  ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
theorem LinearOnSmoothSet.comp {D E : (V → ℂ) → V → ℂ} (hD : LinearOnSmoothSet D)
    (hE : LinearOnSmoothSet E) : LinearOnSmoothSet (fun f => D (E f)) := by
  refine ⟨fun f hf => hD.1 _ (hE.1 f hf), fun f hf g hg => ?_, fun c f hf => ?_⟩
  · show D (E (f + g)) = D (E f) + D (E g)
    rw [hE.2.1 f hf g hg, hD.2.1 _ (hE.1 f hf) _ (hE.1 g hg)]
  · show D (E (c • f)) = c • D (E f)
    rw [hE.2.2 c f hf, hD.2.2 c _ (hE.1 f hf)]
theorem LinearOnSmoothSet.iterate {D : (V → ℂ) → V → ℂ} (hD : LinearOnSmoothSet D) (m : ℕ) :
    LinearOnSmoothSet (fun f => D^[m] f) := by
  induction m with
  | zero => exact linearOnSmoothSet_id
  | succ m ih =>
    have h : (fun f => D^[m + 1] f) = fun f => D (D^[m] f) := by
      funext f
      exact Function.iterate_succ_apply' D m f
    rw [h]
    exact hD.comp ih
theorem hasFDerivAt_of_mem_smoothSet {f : V → ℂ} (hf : f ∈ smoothSet V) (x : V) :
    HasFDerivAt f (fderiv ℝ f x) x :=
  ((ContDiff.differentiable (show ContDiff ℝ ∞ f from hf) (by simp)) x).hasFDerivAt
theorem dirDeriv_eq_fderiv {f : V → ℂ} (hf : f ∈ smoothSet V) (v x : V) :
    dirDeriv v f x = fderiv ℝ f x v :=
  ((hasFDerivAt_of_mem_smoothSet hf x).hasLineDerivAt v).lineDeriv
theorem linearOnSmoothSet_dirDeriv (v : V) :
    LinearOnSmoothSet (dirDeriv v : (V → ℂ) → V → ℂ) := by
  refine ⟨fun f hf => ?_, fun f hf g hg => ?_, fun c f hf => ?_⟩
  · have h : dirDeriv v f = fun x => fderiv ℝ f x v := funext (dirDeriv_eq_fderiv hf v)
    rw [h]
    exact (ContDiff.fderiv_right (m := ∞) (show ContDiff ℝ ∞ f from hf) (by simp)).clm_apply
      contDiff_const
  · funext x
    have h := (((hasFDerivAt_of_mem_smoothSet hf x).add
      (hasFDerivAt_of_mem_smoothSet hg x)).hasLineDerivAt v).lineDeriv
    simp only [Pi.add_apply]
    rw [dirDeriv_eq_fderiv hf, dirDeriv_eq_fderiv hg]
    exact h
  · funext x
    have h := (((hasFDerivAt_of_mem_smoothSet hf x).const_smul c).hasLineDerivAt v).lineDeriv
    simp only [Pi.smul_apply]
    rw [dirDeriv_eq_fderiv hf]
    exact h
end DirDerivLinearity
open DirDerivLinearity in
theorem iterDirDerivLinear_holds : IterDirDerivLinear := by
  intro V _ _ I _ _ e α
  have h : ∀ l : List I, LinearOnSmoothSet
      (fun f : V → ℂ => l.foldr (fun ι g => (dirDeriv (e ι))^[α ι] g) f) := by
    intro l
    induction l with
    | nil => exact linearOnSmoothSet_id
    | cons a l ih => exact ((linearOnSmoothSet_dirDeriv (e a)).iterate (α a)).comp ih
  exact h _
end YangMills.Construction.ConfigurationSpace
end
