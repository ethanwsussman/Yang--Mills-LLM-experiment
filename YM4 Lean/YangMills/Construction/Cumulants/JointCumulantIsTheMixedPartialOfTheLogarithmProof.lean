import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsAreSmooth
import YangMills.Construction.Cumulants.MixedCumulantAsIteratedPartial
import YangMills.Construction.Cumulants.MomentGeneratingFunctionStatement
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.Cumulants.CumulantAsPartial
open YangMills.Construction.ComplexVariables
open YangMills.Construction.Coordinates
variable {n : ℕ}
private theorem isHolomorphicOnOpen_of_differentiableOn {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    SeveralComplexVariables.IsHolomorphicOnOpen U F := by
  refine ⟨hU, hF.continuousOn, fun c hc q => ?_⟩
  have hline : Continuous fun ζ : ℂ => c + ζ • SeveralComplexVariables.basisVector q := by fun_prop
  have hmem : ∀ᶠ ζ in 𝓝 (0 : ℂ), c + ζ • SeveralComplexVariables.basisVector q ∈ U :=
    hline.continuousAt.eventually_mem (by simpa using hU.mem_nhds hc)
  filter_upwards [hmem] with ζ hζ
  have hd : DifferentiableAt ℂ F (c + ζ • SeveralComplexVariables.basisVector q) :=
    hF.differentiableAt (hU.mem_nhds hζ)
  exact DifferentiableAt.comp ζ hd (by fun_prop)
private theorem tendsto_diffQuot_iteratedFDeriv {U : Set (ComplexCoordinates n)}
    {F P : ComplexCoordinates n → ℂ} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) {k : ℕ}
    (v : Fin k → ComplexCoordinates n) (hP : ∀ z ∈ U, P z = iteratedFDeriv ℂ k F z v)
    (j : Fin n) {z : ComplexCoordinates n} (hz : z ∈ U) :
    Tendsto (diffQuot P z j) (𝓝[≠] 0)
      (𝓝 (iteratedFDeriv ℂ (k + 1) F z (Fin.cons (ComplexCoordinates.stdBasisVector j) v))) := by
  have hzU := hU.mem_nhds hz
  have hD : DifferentiableAt ℂ (iteratedFDeriv ℂ k F) z :=
    (hF.contDiffAt hzU).differentiableAt_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
  have hG : HasFDerivAt (fun w => iteratedFDeriv ℂ k F w v)
      ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ComplexCoordinates n) ℂ v).comp
        (fderiv ℂ (iteratedFDeriv ℂ k F) z)) z :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ComplexCoordinates n) ℂ v).hasFDerivAt.comp z
      hD.hasFDerivAt
  have hline : HasDerivAt (fun ζ : ℂ => z + ζ • ComplexCoordinates.stdBasisVector j)
      (ComplexCoordinates.stdBasisVector j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (ComplexCoordinates.stdBasisVector j)).const_add z
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hG hline (by simp)
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hcomp
  have hval : iteratedFDeriv ℂ (k + 1) F z (Fin.cons (ComplexCoordinates.stdBasisVector j) v) =
      fderiv ℂ (iteratedFDeriv ℂ k F) z (ComplexCoordinates.stdBasisVector j) v := by
    rw [iteratedFDeriv_succ_apply_left]
    simp [Fin.tail_def]
  rw [hval]
  refine hslope.congr' ?_
  have hcont : Continuous fun ζ : ℂ => z + ζ • ComplexCoordinates.stdBasisVector j := by fun_prop
  have hmem : ∀ᶠ ζ in 𝓝 (0 : ℂ), z + ζ • ComplexCoordinates.stdBasisVector j ∈ U :=
    hcont.continuousAt.eventually_mem (by simpa using hzU)
  filter_upwards [nhdsWithin_le_nhds hmem] with ζ hζ
  simp only [diffQuot, hP _ hζ, hP z hz, zero_add, zero_smul, add_zero, smul_eq_mul,
    Function.comp_apply]
private theorem iteratedPartials_eq_iteratedFDeriv {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (l : List (Fin n)) :
    HasIteratedPartials U l F ∧ ∀ z ∈ U, iteratedPartials l F z =
      iteratedFDeriv ℂ l.length F z fun i => ComplexCoordinates.stdBasisVector (l.get i) := by
  induction l with
  | nil =>
    refine ⟨hU, fun z _ => ?_⟩
    simp [iteratedPartials]
  | cons j l ih =>
    obtain ⟨hl, heq⟩ := ih
    have hlim := fun z (hz : z ∈ U) => tendsto_diffQuot_iteratedFDeriv hU hF _ heq j hz
    have hcons : (fun i : Fin (j :: l).length => ComplexCoordinates.stdBasisVector ((j :: l).get i)) =
        Fin.cons (ComplexCoordinates.stdBasisVector j)
          fun i : Fin l.length => ComplexCoordinates.stdBasisVector (l.get i) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    refine ⟨?_, fun z hz => ?_⟩
    · rw [HasIteratedPartials]
      exact ⟨hl, hU, fun z hz => ⟨_, hlim z hz⟩⟩
    · rw [hcons]
      exact (hlim z hz).limUnder_eq
private theorem iteratedFDeriv_congr_of_length_eq {F : ComplexCoordinates n → ℂ}
    {z : ComplexCoordinates n} {k m : ℕ} (h : k = m) (v : Fin k → ComplexCoordinates n)
    (w : Fin m → ComplexCoordinates n) (hv : ∀ i, v i = w (Fin.cast h i)) :
    iteratedFDeriv ℂ k F z v = iteratedFDeriv ℂ m F z w := by
  subst h
  congr 1
  funext i
  simpa using hv i
theorem mixedCumulantEqPartialOfLog_of_smooth (hGen : MomentGeneratingFunctionRegularity)
    (hSmooth : SeveralComplexVariables.HolomorphicContDiff.Statement) :
    MixedCumulantEqPartialOfLog := by
  intro Ω _ ν _ n x hn hx
  obtain ⟨hDiff, h1, -, -⟩ :=
    (hGen Ω ν).1 n x (fun i => (hx i).measurable) (fun i => (hx i).bounded)
  have hΓ : tupleMomentGeneratingFunction ν x = momentGeneratingFunction ν x :=
    tupleMomentGeneratingFunction_eq_momentGeneratingFunction ν x
  have hU : IsOpen (logDomain ν x) := by
    change IsOpen {z | ‖tupleMomentGeneratingFunction ν x z - 1‖ < 1}
    rw [hΓ]
    exact isOpen_lt (hDiff.continuous.sub continuous_const).norm continuous_const
  have h0 : (0 : ComplexCoordinates n) ∈ logDomain ν x := by
    change ‖tupleMomentGeneratingFunction ν x 0 - 1‖ < 1
    rw [hΓ, h1]
    simp
  have hslit : ∀ z ∈ logDomain ν x, momentGeneratingFunction ν x z ∈ Complex.slitPlane := by
    intro z hz
    have hz' : ‖momentGeneratingFunction ν x z - 1‖ < 1 := by
      have : ‖tupleMomentGeneratingFunction ν x z - 1‖ < 1 := hz
      rwa [hΓ] at this
    simpa using Complex.mem_slitPlane_of_norm_lt_one hz'
  have hL : DifferentiableOn ℂ (logMomentGeneratingFunction ν x) (logDomain ν x) := fun z hz =>
    ((hDiff z).clog (hslit z hz)).differentiableWithinAt
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hs : ContDiffOn ℂ ∞ (logMomentGeneratingFunction ν x) (logDomain ν x) :=
    hSmooth (Fin n) _ _ (isHolomorphicOnOpen_of_differentiableOn hU hL)
  obtain ⟨hhas, hval⟩ := iteratedPartials_eq_iteratedFDeriv hU hs (List.finRange n)
  refine ⟨?_, ?_⟩
  · rw [HasPartialOverFinset, Fin.sort_univ]
    exact hhas
  · rw [partialOverFinset, Fin.sort_univ, hval 0 h0]
    refine Eq.symm ?_
    refine (iteratedFDeriv_congr_of_length_eq (List.length_finRange (n := n)) _
      (fun i => Pi.single i 1) fun i => ?_).trans ?_
    · simp [ComplexCoordinates.stdBasisVector]
    · rfl
end YangMills.Construction.Cumulants.CumulantAsPartial
