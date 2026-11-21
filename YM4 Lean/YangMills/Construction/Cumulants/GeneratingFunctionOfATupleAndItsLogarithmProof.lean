import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsAreSmooth
import YangMills.Construction.Cumulants.GeneratingFunctionOfATupleAndItsLogarithm
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.RandomTuple.TupleLaplaceLog
variable {n : ℕ}
private theorem isHolomorphicOnOpen_of_isHolomorphicScalar
    {U : Set (Coordinates.ComplexCoordinates n)} {F : Coordinates.ComplexCoordinates n → ℂ}
    (h : ComplexVariables.IsHolomorphicScalar U F) :
    SeveralComplexVariables.IsHolomorphicOnOpen U F := by
  obtain ⟨hU, hc, hd⟩ := h
  have he : ∀ w : ℂ, ((Equiv.funUnique (Fin 1) ℂ).symm w) 0 = w := fun w =>
    (Equiv.funUnique (Fin 1) ℂ).apply_symm_apply w
  refine ⟨hU, ?_, fun c hcU q => ?_⟩
  · have := (continuous_apply (0 : Fin 1)).comp_continuousOn hc
    simpa [Function.comp_def, he] using this
  · have hq : SeveralComplexVariables.basisVector q =
        Coordinates.ComplexCoordinates.stdBasisVector q := by
      funext q'
      by_cases h : q' = q
      · subst h
        simp [SeveralComplexVariables.basisVector, Coordinates.ComplexCoordinates.stdBasisVector]
      · simp [SeveralComplexVariables.basisVector, Coordinates.ComplexCoordinates.stdBasisVector, h]
    rw [hq]
    filter_upwards [hd c hcU q] with ζ hζ
    have := differentiableAt_pi.1 hζ 0
    simpa [Function.comp_def, he] using this
private theorem contDiffAt_log_mgf_zero {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
    (Y : Fin n → Ω → ℝ) (hn : 1 ≤ n)
    (hSmooth : SeveralComplexVariables.HolomorphicContDiff.Statement)
    (hU : IsOpen (logRegion ν Y)) (h0 : (0 : Coordinates.ComplexCoordinates n) ∈ logRegion ν Y)
    (hL : ComplexVariables.IsHolomorphicScalar (logRegion ν Y) (logLaplace ν Y)) :
    ContDiffAt ℂ (n : WithTop ℕ∞)
      (fun t : Fin n → ℂ => Complex.log (Cumulants.momentGeneratingFunction ν Y t)) 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hs : ContDiffOn ℂ ∞ (logLaplace ν Y) (logRegion ν Y) :=
    hSmooth (Fin n) (logRegion ν Y) (logLaplace ν Y)
      (isHolomorphicOnOpen_of_isHolomorphicScalar hL)
  have ha : ContDiffAt ℂ ∞ (logLaplace ν Y) 0 := hs.contDiffAt (hU.mem_nhds h0)
  exact ha.of_le (by exact_mod_cast le_top)
theorem laplaceAndLogTheorem_holds
    (hGenerating : Cumulants.TupleLogMGF.TupleMGFAndLogTheorem)
    (hSmooth : SeveralComplexVariables.HolomorphicContDiff.Statement) :
    LaplaceAndLogTheorem := by
  intro Ω _ ν _ n Y hn hY
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hGenerating Ω ν n Y hn hY
  refine ⟨⟨h₁.entire, h₁.apply_zero, h₁.hasPartial, fun B => ?_⟩,
    ⟨h₂.isOpen, h₂.zero_mem, h₂.holomorphic, h₂.exp_log, h₂.hasPartial, fun j => ?_,
      h₂.partialDeriv_eq,
      contDiffAt_log_mgf_zero ν Y hn hSmooth h₂.isOpen h₂.zero_mem h₂.holomorphic,
      h₂.hasMixedPartial, h₂.mixedCumulant_eq⟩,
    ⟨rfl, h₃.pos, h₃.zero_mem, h₃.hasPartials, h₃.mixedCumulant_eq⟩,
    ⟨h₄.hasPartial, h₄.finsetCumulant_eq⟩,
    fun c => ⟨(h₅ c).isOpen, (h₅ c).zero_mem, (h₅ c).hasPartial_shift, (h₅ c).hasPartial,
      (h₅ c).partialDeriv_shift⟩⟩
  · refine (h₁.partial_apply_zero B).trans ?_
    unfold Cumulants.finsetMoment
    split_ifs with hB
    · subst hB
      simp [Probability.complexExpectation]
    · rfl
  · have hj : ComplexVariables.HasPartialOverFinset univ {j} (laplaceTransform ν Y) :=
      h₁.hasPartial {j}
    simp only [ComplexVariables.HasPartialOverFinset, Finset.sort_singleton,
      ComplexVariables.HasIteratedPartials] at hj
    exact ⟨h₂.isOpen, fun z _ => hj.2.2 z (mem_univ z)⟩
end YangMills.Construction.RandomTuple.TupleLaplaceLog
