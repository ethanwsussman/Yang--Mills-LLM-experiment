import YangMills.Construction.ClusterExpansionOfAStep.GasAtColdTops
import YangMills.Construction.ClusterExpansionOfAStep.GasDensitiesForget
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreTheGas
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ClusterExpansionOfAStep.RatiosOfXiProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings RenormalizationStepParameters Dobrushin
namespace StepGas
namespace ColdCase
def frozenCoupling (R : StepSetup) : StepSetup := { R with nextCoupling := R.coupling }
theorem frozenCoupling_onParameters {R : StepSetup} {T : ParameterAssignment} {y : ℝ} (h : R.OnParameters T y)
    (hx : 0 ≤ R.coupling) : (frozenCoupling R).OnParameters T y where
  params_eq := h.params_eq
  anchorRadius_eq := h.anchorRadius_eq
  barrierFn_eq := h.barrierFn_eq
  le_coupling := h.le_coupling
  isStep := ⟨h.isStep.1, by show R.coupling ≤ 1.01 * R.coupling; linarith, Nat.le_succ _⟩
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem measurableSet_noSpinMeets (G : GasGround R n) (Y : TorusSite n) :
    MeasurableSet (G.NoSpinMeets Y) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.measurableSet_noSpinMeets <;> assumption
theorem partitionFunction_insert (G : GasGround R n) (A : Finset (TorusSite n)) (Y : TorusSite n) :
    G.partitionFunction (insert Y A) =
      ∫⁻ σ in G.NoSpinMeets Y, G.pairConstraint.weightDensity G.weight σ
        ∂Measure.pi (G.referenceMeasure A) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.partitionFunction_insert <;> assumption
theorem gibbsLaw_apply (G : GasGround R n) (A : Finset (TorusSite n)) {B : Set G.Config}
    (hB : MeasurableSet B) :
    G.gibbsLaw A B = (G.partitionFunction A)⁻¹ *
      ∫⁻ σ in B, G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure A) := by
  unfold GasGround.gibbsLaw GasGround.gibbsLawOff PairConstraint.gibbsLaw GasGround.partitionFunction
    GasGround.referenceMeasure
  rw [Measure.smul_apply, withDensity_apply _ hB, smul_eq_mul]
theorem partitionFunction_of_gibbsLaw (G : GasGround R n) (A : Finset (TorusSite n)) (Y : TorusSite n)
    (hp : IsProbabilityMeasure (G.gibbsLaw A)) :
    G.partitionFunction A ≠ 0 ∧ G.partitionFunction A ≠ ⊤ ∧
      (G.partitionFunction (insert Y A)).toReal =
        (G.gibbsLaw A).real (G.NoSpinMeets Y) * (G.partitionFunction A).toReal := by
  have h1 := gibbsLaw_apply G A (MeasurableSet.univ (α := G.Config))
  rw [measure_univ, Measure.restrict_univ] at h1
  have h2 : (G.partitionFunction A)⁻¹ * G.partitionFunction A = 1 := h1.symm
  have h0 : G.partitionFunction A ≠ 0 := by
    intro h
    rw [h] at h2
    simp at h2
  have ht : G.partitionFunction A ≠ ⊤ := by
    intro h
    rw [h] at h2
    simp at h2
  refine ⟨h0, ht, ?_⟩
  have h3 := gibbsLaw_apply G A (measurableSet_noSpinMeets G Y)
  rw [← partitionFunction_insert] at h3
  have h4 : G.partitionFunction (insert Y A) = G.gibbsLaw A (G.NoSpinMeets Y) * G.partitionFunction A := by
    rw [h3, mul_comm (G.partitionFunction A)⁻¹, mul_assoc, ENNReal.inv_mul_cancel h0 ht, mul_one]
  rw [h4, ENNReal.toReal_mul]
  rfl
theorem noSpinMeets_ge_of_integral (G : GasGround R n) (A : Finset (TorusSite n)) (Y : TorusSite n) {e : ℝ}
    (hp : IsProbabilityMeasure (G.gibbsLaw A))
    (hm : ∀ F : G.Config → ℝ, Measurable F → (∀ σ, |F σ| ≤ 1) → (∀ σ ∈ G.NoSpinMeets Y, F σ = 0) →
      |∫ σ, F σ ∂G.gibbsLaw A| ≤ e) : 1 - e ≤ (G.gibbsLaw A).real (G.NoSpinMeets Y) := by
  have hN := measurableSet_noSpinMeets G Y
  have hF := hm ((G.NoSpinMeets Y)ᶜ.indicator fun _ => (1 : ℝ)) (measurable_const.indicator hN.compl)
    (fun σ => by
      by_cases h : σ ∈ (G.NoSpinMeets Y)ᶜ
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h])
    (fun σ h => by
      have h' : σ ∉ (G.NoSpinMeets Y)ᶜ := fun c => c h
      exact Set.indicator_of_notMem h' _)
  rw [integral_indicator hN.compl, setIntegral_const, smul_eq_mul, mul_one,
    probReal_compl_eq_one_sub hN] at hF
  linarith [(abs_le.mp hF).2]
end ColdCase
open ColdCase in
theorem coldGasBounds_holds (hz : MarkedIntegralEqPartition) (hc : ClusterExpansionOfAStep.GasColumnsSmall)
    (hf : ClusterExpansionOfAStep.GasDensityForgets) : ColdGasBounds := by
  obtain ⟨a₁, pa₁, hz⟩ := hz
  obtain ⟨a₂, pa₂, hc⟩ := hc
  obtain ⟨a₃, pa₃, hf⟩ := hf
  refine ⟨fun c => min (a₁ c) (min (a₂ c) (a₃ c)), fun c => lt_min (pa₁ c) (lt_min (pa₂ c) (pa₃ c)), ?_⟩
  intro T hT hrt
  obtain ⟨y₁, hz⟩ := hz T hT (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, hc⟩ := hc T hT (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨y₃, hf⟩ := hf T hT (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨max 0 (max y₁ (max y₂ y₃)), fun y hy R hR hA => ?_⟩
  have hy0 : 0 ≤ y := (le_max_left _ _).trans hy
  have hy1 : y₁ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy2 : y₂ ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hy3 : y₃ ≤ y := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hx : 0 ≤ R.coupling := hy0.trans hR.le_coupling
  have hR₀ := frozenCoupling_onParameters hR hx
  have hn₀ : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hrt' : R.params.rt = T.rt := by rw [hR.params_eq]; rfl
  have tie := hz y hy1 (frozenCoupling R) hR₀ hA rfl
  have col := hc y hy2 (frozenCoupling R) hR₀ (by show R.coupling ≤ 1.01 * R.coupling; linarith)
  have fgt := hf y hy3 (frozenCoupling R) hR₀ (by show R.coupling ≤ 1.01 * R.coupling; linarith)
  have cold : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n,
      IsCold (9 / 8 * R.params.threshold) V → (coldCaseGround (frozenCoupling R) V).IsAdmissibleGround :=
    fun n _ hn V hV => Or.inl ⟨hn, hV, rfl, rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · intro n _ hn V hV A Y
    have hV' : IsCold (9 / 8 * T.threshold) V := hσ ▸ hV
    obtain ⟨hZ, -⟩ := tie n (hn₀ ▸ hn) V hV'
    obtain ⟨hw, hs⟩ := col n (coldCaseGround (frozenCoupling R) V) (cold n hn V hV) (fun j => j.1.Touches A)
    have hprob : IsProbabilityMeasure ((coldCaseGround (frozenCoupling R) V).gibbsLaw A) :=
      hs.isProbabilityMeasure
    obtain ⟨h0, ht, hins⟩ := partitionFunction_of_gibbsLaw (coldCaseGround (frozenCoupling R) V) A Y hprob
    have hmean := noSpinMeets_ge_of_integral (coldCaseGround (frozenCoupling R) V) A Y hprob
      (fun F hF hb hn' => hs.abs_integral_le Y F hF hb hn')
    have hσ0 : 0 < R.params.threshold := by
      have h1 : (0 : ℝ) ≤ curvature V 0 0 1 := norm_nonneg _
      have h2 := hV 0 0 1 (by decide)
      linarith
    have hside : R.params.n₀ ≤ n * R.params.side :=
      hn.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero R.params.side_ne.out))
    have hD : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side)) := by
      refine hR.isStep.1.1.positive _ hside _ fun x μ ν _ => ?_
      simpa [curvature, holonomy_trivialField] using hσ0
    have hP : 0 < ((coldCaseGround (frozenCoupling R) V).partitionFunction A).toReal :=
      ENNReal.toReal_pos h0 ht
    have eA : R.markedIntegral A V = R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
        ((coldCaseGround (frozenCoupling R) V).partitionFunction A).toReal := hZ A
    have eY : R.markedIntegral (insert Y A) V =
        R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
        ((coldCaseGround (frozenCoupling R) V).partitionFunction (insert Y A)).toReal := hZ (insert Y A)
    have hle : ((coldCaseGround (frozenCoupling R) V).gibbsLaw A).real
        ((coldCaseGround (frozenCoupling R) V).NoSpinMeets Y) ≤ 1 :=
      measureReal_le_one
    have hpos := mul_pos hD hP
    rw [eA, eY, hins]
    refine ⟨hpos, ?_, ?_⟩
    · have : 1 - Real.exp (-(7 * T.gasRate * R.coupling)) ≤
          ((coldCaseGround (frozenCoupling R) V).gibbsLaw A).real
            ((coldCaseGround (frozenCoupling R) V).NoSpinMeets Y) := hmean
      nlinarith
    · nlinarith
  · intro n n' _ _ hn hn' V V' Y Y' m hm h1 h2 hV hV' hag
    have c1 : IsCold (9 / 8 * T.threshold) V := hσ ▸ hV
    have c2 : IsCold (9 / 8 * T.threshold) V' := hσ ▸ hV'
    have e1 : (coldCaseGround (frozenCoupling R) V).blockDensity Y = R.blockDensity n Y V :=
      (tie n (hn₀ ▸ hn) V c1).2 Y
    have e2 : (coldCaseGround (frozenCoupling R) V').blockDensity Y' = R.blockDensity n' Y' V' :=
      (tie n' (hn₀ ▸ hn') V' c2).2 Y'
    have hg : GroundsAgreeNear (coldCaseGround (frozenCoupling R) V) (coldCaseGround (frozenCoupling R) V')
        Y Y' m :=
      ⟨h1, h2, hag, fun _ _ => by simp [coldCaseGround], fun _ _ => by
        simp [coldCaseGround, emptyCoarseState, CoarseState.markAt]⟩
    have := fgt n n' _ _ Y Y' m (cold n hn V hV) (cold n' hn' V' hV') hm hg
    rw [e1, e2, ← hrt'] at this
    exact this
end StepGas
end YangMills.Construction
end
