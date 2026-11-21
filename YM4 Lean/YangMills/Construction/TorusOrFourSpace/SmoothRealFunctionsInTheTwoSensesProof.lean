import YangMills.Construction.TorusOrFourSpace.ContinuousPartialsAreContinuousDifferentiability
import YangMills.Construction.TorusOrFourSpace.SmoothRealFunctionsInTheTwoSenses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.SmoothTwoSenses
def singleBlock (x : Coords 1) : Fin 4 → ℝ := x.block ⟨0, (1 : ℕ+).pos⟩
def ofSingleBlock (a : Fin 4 → ℝ) : Coords 1 :=
  fun j => a ⟨j, by
    have h := j.2
    simpa using h⟩
theorem singleBlock_ofSingleBlock (a : Fin 4 → ℝ) : singleBlock (ofSingleBlock a) = a := by
  funext μ
  exact congrArg a (Fin.ext (by simp))
theorem contDiff_singleBlock (ν : ℕ) : ContDiff ℝ ν singleBlock :=
  contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ _
theorem contDiff_ofSingleBlock (ν : ℕ) : ContDiff ℝ ν ofSingleBlock :=
  contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ _
theorem smoothIffSmoothAsTuple_holds (contPartials : ContPartialsIffContDiff) :
    SmoothIffSmoothAsTuple := by
  intro D E u
  unfold IsSmoothFn Tuple.IsSmoothT Tuple.IsClassC
  constructor
  · intro h ν
    rw [contPartials 1 ν]
    have e : (Tuple.ofSingle D E fun y => (u y : ℂ)) ∘ Tuple.proj D E =
        Complex.ofRealCLM ∘ (u ∘ E.quotMap D) ∘ singleBlock := rfl
    rw [e]
    exact Complex.ofRealCLM.contDiff.comp ((contDiff_infty.1 h ν).comp (contDiff_singleBlock ν))
  · intro h
    refine contDiff_infty.2 fun ν => ?_
    have hν := (contPartials 1 ν _).1 (h ν)
    have e : u ∘ E.quotMap D = Complex.reCLM ∘
        ((Tuple.ofSingle D E fun y => (u y : ℂ)) ∘ Tuple.proj D E) ∘
          ofSingleBlock := by
      funext a
      show u (E.quotMap D a) = ((u (E.quotMap D (singleBlock (ofSingleBlock a))) : ℂ)).re
      rw [singleBlock_ofSingleBlock, Complex.ofReal_re]
    rw [e]
    exact Complex.reCLM.contDiff.comp (hν.comp (contDiff_ofSingleBlock ν))
end YangMills.Construction.PeriodicSpace.Kind.SmoothTwoSenses
