import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsOfSeveralVariablesProof
import YangMills.Construction.Cumulants.GeneratingFunctionIsEntireWithItsPrincipalLogarithm
import YangMills.Construction.Cumulants.TupleGeneratingFunctionAndItsLogarithm
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Cumulants.GeneratingLog
open ComplexVariables TorusBoundNotation
variable {n : ℕ}
private theorem principalLog_eq_log {w : ℂ} (hw : ‖w - 1‖ < 1) : principalLog w = Complex.log w := by apply _root_.YangMills.Construction.SeveralComplexVariables.principalLog_eq_log <;> assumption
private theorem partialDeriv_congr_of_eqOn {U : Set (Coordinates.ComplexCoordinates n)}
    (hU : IsOpen U) {F G : Coordinates.ComplexCoordinates n → ℂ} (hFG : EqOn F G U) (j : Fin n) :
    EqOn (partialDeriv j F) (partialDeriv j G) U := by
  intro z hz
  have hline : Continuous fun ζ : ℂ => z + ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by
    fun_prop
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), z + ζ • Coordinates.ComplexCoordinates.stdBasisVector j ∈ U :=
    hline.continuousAt.eventually_mem (by simpa using hU.mem_nhds hz)
  have hq : diffQuot F z j =ᶠ[𝓝[≠] 0] diffQuot G z j := by
    refine (hnear.filter_mono nhdsWithin_le_nhds).mono fun ζ hζ => ?_
    simp only [diffQuot, hFG hζ, hFG hz]
  change lim (map _ _) = lim (map _ _)
  rw [Filter.map_congr hq]
private theorem iteratedPartials_eqOn_foldr {U : Set (Coordinates.ComplexCoordinates n)}
    (hU : IsOpen U) {F G : Coordinates.ComplexCoordinates n → ℂ} (hFG : EqOn F G U) :
    ∀ l : List (Fin n), FormedSuccessively U G l →
      EqOn (iteratedPartials l F) (l.foldr coordDeriv G) U
  | [], _ => hFG
  | j :: l, hl => by
    obtain ⟨hl₁, hl₂⟩ := hl
    intro z hz
    have ih := iteratedPartials_eqOn_foldr hU hFG l hl₁
    change partialDeriv j (iteratedPartials l F) z =
      coordDeriv j (l.foldr coordDeriv G) z
    rw [partialDeriv_congr_of_eqOn hU ih j hz]
    exact partialDeriv_eq_coordDeriv hl₂ hz j
private theorem integrable_cexp_linear {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Probability.IsBoundedRealRV (X i)) (z : Coordinates.ComplexCoordinates n) :
    Integrable (fun ω => Complex.exp (∑ i, z i * (X i ω : ℂ))) ν := by
  choose C hC using fun i => (hX i).bounded
  have hmeas : Measurable fun ω => Complex.exp (∑ i, z i * (X i ω : ℂ)) := by
    refine Complex.measurable_exp.comp (Finset.measurable_sum _ fun i _ => ?_)
    exact measurable_const.mul (Complex.measurable_ofReal.comp (hX i).measurable)
  refine Integrable.of_bound hmeas.aestronglyMeasurable (Real.exp (∑ i, ‖z i‖ * C i))
    (Eventually.of_forall fun ω => ?_)
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_))
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC i ω) (norm_nonneg _)
theorem entireAndLogCumulant_holds (hCalc : SeveralComplexVariables.HolomorphicCalculusRules)
    (hTup : TupleLogMGF.TupleMGFAndLogTheorem) : EntireAndLogCumulant := by
  intro Ω _ ν _ n X hn hX
  obtain ⟨hE, hL, -, -, -⟩ := hTup Ω ν n X hn hX
  have hM : IsEntireFun (momentGeneratingFunction ν X) := hE.entire
  have hU : IsOpen (nearOneSet ν X) := hL.isOpen
  have h0 : (0 : Coordinates.ComplexCoordinates n) ∈ nearOneSet ν X := hL.zero_mem
  obtain ⟨-, hRes, -, -, -, -, -, -, -, hpl⟩ := hCalc n hn univ isOpen_univ _ _ hM hM
  have hMU : IsHolomorphicScalar (nearOneSet ν X) (momentGeneratingFunction ν X) :=
    hRes _ hU (subset_univ _)
  obtain ⟨-, -, -, hcomp, -, -, -, -, -, -⟩ := hCalc n hn _ hU _ _ hMU hMU
  have hdisc : IsOpen discAtOne :=
    isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
  have hG : IsHolomorphicScalar (nearOneSet ν X) (logOfGenerating ν X) :=
    hcomp discAtOne principalLog hdisc hpl.1 fun z hz => hz
  obtain ⟨-, -, -, -, -, -, hmix, -, hloc, -⟩ := hCalc n hn _ hU _ _ hG hG
  have hagree : EqOn (logMomentGeneratingFunction ν X) (logOfGenerating ν X) (nearOneSet ν X) :=
    fun z hz => (principalLog_eq_log hz).symm
  have hcum : mixedCumulant ν X = mixedDeriv (logOfGenerating ν X) 0 := by
    rw [hL.mixedCumulant_eq, partialOverFinset, Fin.sort_univ]
    exact iteratedPartials_eqOn_foldr hU hagree (List.finRange n) hmix.1 h0
  have hone : momentGeneratingFunction ν X 0 = 1 := hE.apply_zero
  refine ⟨⟨integrable_cexp_linear ν X hX, hM, hone, hU, h0, hG, fun z hz => hpl.2.1 _ hz, ?_,
    hmix.1, hcum⟩, fun i hi => ?_⟩
  · change principalLog (momentGeneratingFunction ν X 0) = 0
    rw [hone]
    exact hpl.2.2.1
  · rw [hcum]
    refine (hloc i fun z _ z' _ hzz => ?_).2 h0
    have hsame : momentGeneratingFunction ν X z = momentGeneratingFunction ν X z' := by
      refine congrArg (fun f : Ω → ℂ => ∫ ω, f ω ∂ν) (funext fun ω => ?_)
      refine congrArg Complex.exp (Finset.sum_congr rfl fun j _ => ?_)
      by_cases hj : j = i
      · subst hj
        simp [hi]
      · rw [hzz j hj]
    exact congrArg principalLog hsame
end YangMills.Construction.Cumulants.GeneratingLog
