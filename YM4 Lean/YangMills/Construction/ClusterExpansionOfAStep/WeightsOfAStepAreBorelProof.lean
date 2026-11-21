import YangMills.Construction.ClusterExpansionOfAStep.AdmissionReadsVOnItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsBorelProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusLumps TorusFields StepSettings StepCosts
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem bondMark_measurable (hR : R.IsWellPosed) (V : TorusField n) (b : TorusBond (n * R.params.side)) :
    Measurable fun W : TorusField (n * R.params.side) => bondMark R V W b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_bondMark <;> assumption
theorem baseLaw_measurable (hK : BondKernelBorel) (b : BaseChoice R.params.side n) :
    Measurable fun W : TorusField (n * R.params.side) => baseLaw (R := R) W b := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_baseLaw <;> assumption
theorem configurationWeight_measurable (hK : BondKernelBorel) : ConfigurationWeightMeasurable := by
  classical
  intro R hR n _ hn C V bad Yt b
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [mul_comm R.params.side R.params.n₀]; exact Nat.mul_le_mul_right _ hn⟩
  have hD := (hR.hasExpansions.2.borel (n * R.params.side) hside Yt).1
  have hbl : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => baseLaw (R := R) p.1 b :=
    (baseLaw_measurable hK b).comp measurable_fst
  have hker : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 p.1)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c := by
    refine Finset.measurable_prod _ fun c _ => ?_
    obtain ⟨-, -, -, -, -, hk, -⟩ := hK R.params R.coupling n
    exact Measurable.comp (g := fun p : TorusField (n * R.params.side) × TorusField n =>
        bondKernel R.params R.coupling (fineLevelField R.params n p.1) (coarseLevelField R.params n p.2) b c)
      (f := fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => (p.1, V)) (hk b c)
      (measurable_fst.prodMk measurable_const)
  have hmk : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => markProduct R C V p.1 bad := by
    unfold markProduct
    refine Finset.measurable_prod _ fun c _ => ?_
    by_cases hc : c ∈ bad
    · simp only [if_pos hc]
      exact measurable_const.sub ((bondMark_measurable hR V c).comp measurable_fst)
    · simp only [if_neg hc]
      exact (bondMark_measurable hR V c).comp measurable_fst
  have hkey : (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      configurationWeight R C V bad Yt b p.1 p.2) =
      fun p => ENNReal.ofReal ((if IsHullState R.params R.range p.1 Yt then
          R.labelWeight (n * R.params.side) p.1 Yt p.2 else 0) *
        baseLaw (R := R) p.1 b * (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
          bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 p.1)
            (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) *
        markProduct R C V p.1 bad) := by
    funext p
    unfold configurationWeight stepWeight
    by_cases hh : IsHullState R.params R.range p.1 Yt
    · simp only [if_pos hh]
    · simp only [if_neg hh, zero_mul, ENNReal.ofReal_zero]
  rw [hkey]
  exact ENNReal.measurable_ofReal.comp (((hD.mul hbl).mul hker).mul hmk)
end YangMills.Construction.ClusterExpansionOfAStep
end
