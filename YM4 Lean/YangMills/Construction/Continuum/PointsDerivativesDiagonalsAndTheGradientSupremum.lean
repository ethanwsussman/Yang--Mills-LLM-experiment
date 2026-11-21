import YangMills.Construction.Continuum.ConfigurationSpace
import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.ConfigGradients
abbrev Pt (n : ℕ) : Type := ConfigurationSpace.Config n
abbrev ptNorm {n : ℕ} (x : Pt n) : ℝ := ConfigurationSpace.configNorm x
abbrev Idx (n : ℕ) : Type :=
  ConfigurationSpace.MultiIdx (ConfigurationSpace.CoordIndex n)
abbrev idxDegree {n : ℕ} (α : Idx n) : ℕ :=
  ConfigurationSpace.MultiIdx.order α
abbrev partialD {n : ℕ} (α : Idx n) (f : Pt n → ℂ) : Pt n → ℂ :=
  ConfigurationSpace.configMultiDeriv α f
abbrev smoothFns (n : ℕ) : Set (Pt n → ℂ) :=
  ConfigurationSpace.smoothSet (Pt n)
abbrev diagLocus (n : ℕ) : Set (Pt n) := ConfigurationSpace.fatDiagonal n
def gradLen (φ : (Fin 4 → ℝ) → ℝ) (y : Fin 4 → ℝ) : ℝ :=
  TorusMetric.euclidNormVec fun c => TestFunctions.partialDerivR4 c φ y
def gradSup (φ : (Fin 4 → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ y, ENNReal.ofReal (gradLen φ y)
theorem gradNorm_ofRealFun {φ : (Fin 4 → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (y : Fin 4 → ℝ) :
    ConfigSpace.gradNorm (ConfigurationSpace.ofRealFun φ) y = gradLen φ y := by
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcoord : ∀ c : Fin 4,
      TestFunctions.partialDerivR4 c (ConfigurationSpace.ofRealFun φ) y =
        ((TestFunctions.partialDerivR4 c φ y : ℝ) : ℂ) := by
    intro c
    have hl : DifferentiableAt ℝ (fun t : ℝ => φ (y + t • Pi.single c (1 : ℝ))) 0 :=
      hdiff.differentiableAt.comp (0 : ℝ) (by fun_prop)
    exact hl.hasDerivAt.ofReal_comp.deriv
  unfold ConfigSpace.gradNorm gradLen TorusMetric.euclidNormVec
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hcoord c, Complex.norm_real, Real.norm_eq_abs, sq_abs]
theorem toReal_gradSup {φ : (Fin 4 → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    (gradSup φ).toReal = ConfigSpace.gradSupNorm (ConfigurationSpace.ofRealFun φ) := by
  unfold gradSup ConfigSpace.gradSupNorm
  rw [ENNReal.toReal_iSup fun _ => ENNReal.ofReal_ne_top]
  refine iSup_congr fun y => ?_
  rw [gradNorm_ofRealFun hφ y]
  exact ENNReal.toReal_ofReal (Real.sqrt_nonneg _)
end YangMills.Construction.ConfigGradients
end
