import YangMills.Construction.EuclideanFunctionals.ConeConditionOfTheSystemOfAReconstruction
import YangMills.Construction.EuclideanFunctionals.FormsOfTheOperatorsOverTheWedge
import YangMills.Construction.EuclideanFunctionals.TubeOperatorOfTheSystemOfAReconstruction
import YangMills.Construction.SpectralTheory.MeasuresOnRealSpaceOfTheEarlierSettings
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TubeOperator
open DefinitionComparison
open SettingsComparison (euclideanToCoords liftToCoords totalOp)
open BorelSpectral
theorem measurable_tubeKernel (v : ℂ × ℂ) : Measurable (tubeKernel v) :=
  Complex.measurable_exp.comp
    ((measurable_const.mul (Complex.measurable_ofReal.comp measurable_energyCoord)).neg.add
      (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_momCoord 0))))
theorem norm_tubeKernel_le {v : ℂ × ℂ}
    (hle : ∀ q ∈ SpectralPoint.wedge.1, ‖SpectralPoint.planeExpKernel v q‖ ≤ 1)
    {x : MomSpace} (hx : x ∈ momentumPyramid.1) : ‖tubeKernel v x‖ ≤ 1 :=
  hle (SpectralPoint.planeProj ⟨x.ofLp, Set.mem_univ _⟩) (hx 0)
theorem setIntegralOp_congr {n : ℕ} {X : Set (Fin n → ℝ)} {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (E : SpectralMeasure X K)
    {A A' : BorelSubsets X} (h : A = A') (g : X → ℂ) :
    SpectralMeasure.setIntegralOp E A (fun y => g y.1) =
      SpectralMeasure.setIntegralOp E A' (fun y => g y.1) := by
  subst h
  rfl
theorem main_holds (forms : TubeOperatorForms.Holds)
    (cone : SystemConeCondition.Holds)
    (measures : SettingsComparison.FullSpaceMeasuresAgreeForAllSpaces) : Main := by
  intro m S σ s hc v hv
  obtain ⟨-, ⟨-, -, hle⟩, -, -, hpyr⟩ := forms m S σ v hv
  have heq := (measures σ.space 4).setIntegralOp_eq _ _ s.corresponds.measure_eq momentumPyramid
    (tubeKernel v) (measurable_tubeKernel v)
    ⟨1, fun x hx => norm_tubeKernel_le (hle v hv) hx⟩
  refine (hpyr hc).1.trans (Eq.trans ?_ heq)
  exact (setIntegralOp_congr _ (cone m S σ s).2.2 (liftToCoords (tubeKernel v))).symm
end YangMills.Construction.EuclideanFunctionals.TubeOperator
