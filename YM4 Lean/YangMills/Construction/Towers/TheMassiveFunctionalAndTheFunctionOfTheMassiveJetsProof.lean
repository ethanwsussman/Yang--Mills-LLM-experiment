import YangMills.Construction.OneLoopLaw.CoefficientOfATemperedFunctional
import YangMills.Construction.Towers.TheMassiveCoefficientIsRealAnalytic
import YangMills.Construction.Towers.TheMassiveFamilyIsTempered
import YangMills.Construction.Towers.TheMassiveFunctionIsLocallyHolomorphic
import YangMills.Construction.Towers.TheMassiveFunctionalAndTheFunctionOfTheMassiveJets
import YangMills.Construction.Towers.TheMixedDerivativeOfTheMassiveFunction
import YangMills.Construction.Towers.TheSharpFunctionOfTheMassiveJets
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
open Coordinates Coordinates.ComplexCoordinates
open Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn asLine)
namespace Tower.FullSpace.BackgroundJets.MassiveFunctionalAndJets
theorem isRealAnalyticIn_of_eventuallyEq {N N' : ℕ} {D : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'}
    (hD : Matrices.ComplexMatrix2.IsRelativelyOpen (realLocus N) D)
    (h : ∀ a ∈ D, ∃ (D' : Set (ComplexCoordinates N)) (g : ComplexCoordinates N → ComplexCoordinates N'),
      IsRealAnalyticIn D' g ∧ a ∈ D' ∧ ∀ᶠ z in 𝓝[realLocus N] a, g z = f z) :
    IsRealAnalyticIn D f := by
  refine ⟨hD, fun a ha => ?_⟩
  obtain ⟨D', g, hg, haD', he⟩ := h a ha
  obtain ⟨c, hc⟩ := hg.2 a haD'
  refine ⟨c, ?_⟩
  filter_upwards [hc, he] with z hz hez
  rw [← hez]
  exact hz
theorem isRealAnalyticIn_asLine (hH : PowerSeriesHolomorphy.Properties) {N : ℕ}
    {O : Set (ComplexCoordinates N)} {g : ComplexCoordinates N → ℂ} (hg : IsHolomorphicScalarIn O g) :
    IsRealAnalyticIn (O ∩ realLocus N) (asLine g) :=
  ((hH.1 N O hg.1).1 1 (asLine g) hg).2.2.2.2
theorem mixedPartialAtZero_eq_secondPartial (g : (Fin 4 → ℂ) → ℂ) :
    mixedPartialAtZero (fun p => g (ofRealMomentum p)) =
      OneLoopLaw.TemperedStiffness.secondPartialAtZero g 0 1 := by
  have hpoint : ∀ s t : ℝ, ofRealMomentum (Function.update (Function.update (0 : Fin 4 → ℝ) 0 s) 1 t) =
      PeriodicOperators.toComplexVec (Pi.single 0 s + Pi.single 1 t) := by
    intro s t
    funext μ
    fin_cases μ <;> simp [ofRealMomentum, PeriodicOperators.toComplexVec, Function.update]
  simp only [mixedPartialAtZero, realPartialDeriv, OneLoopLaw.TemperedStiffness.secondPartialAtZero]
  simp only [hpoint, Pi.zero_apply, Function.update_apply]
  simp
theorem stripHalfWidth_pos {L : ℕ} (hL : 0 < L) (hS : Conventions.IsAdmissibleBlockingFactor L)
    (hM : MassiveOpFunctions.SharpLogFn.SharpMixedDerivative) : 0 < stripHalfWidth := by
  obtain ⟨⟨O, h0, hsub, G, hG, -⟩, -⟩ := hM L hL hS 1 le_rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hG.1 0 h0
  have hw : (fun _ => ((ε / 2 : ℝ) : ℂ) : ComplexCoordinates 4) ∈
      Metric.ball (0 : ComplexCoordinates 4) ε := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
    intro i
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have := hsub (hball hw) 0
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)] at this
  linarith
theorem massWidth_pos (hs : 0 < stripHalfWidth) {z : ℝ} (hz : 0 < z) : 0 < massWidth z :=
  lt_min hs (by have := Real.sqrt_pos.2 hz; positivity)
theorem continuous_massWidth : Continuous massWidth := by
  unfold massWidth
  fun_prop
def complexWithinMassWidth : Set (ComplexCoordinates 5) :=
  {w | 0 < (w 0).re ∧ ∀ μ : Fin 4, ‖w μ.succ‖ < massWidth (w 0).re}
theorem isOpen_complexWithinMassWidth : IsOpen complexWithinMassWidth := by
  have h0 : Continuous fun w : ComplexCoordinates 5 => (w 0).re := by fun_prop
  have hw : Continuous fun w : ComplexCoordinates 5 => massWidth (w 0).re :=
    continuous_massWidth.comp h0
  have : complexWithinMassWidth = {w | 0 < (w 0).re} ∩
      ⋂ μ : Fin 4, {w : ComplexCoordinates 5 | ‖w μ.succ‖ < massWidth (w 0).re} := by
    ext w
    simp [complexWithinMassWidth]
  rw [this]
  refine (isOpen_lt continuous_const h0).inter (isOpen_iInter_of_finite fun μ => ?_)
  exact isOpen_lt (by fun_prop) hw
theorem withinMassWidth_eq :
    withinMassWidth = complexWithinMassWidth ∩ realLocus 5 := by
  ext w
  simp only [withinMassWidth, complexWithinMassWidth, mem_ofPred_eq, mem_inter_iff]
  tauto
theorem massiveLogFnCoords_realAnalytic {L k : ℕ} (hs : 0 < stripHalfWidth)
    (hH : PowerSeriesHolomorphy.Properties)
    (hI : ∀ z₀ : ℝ, 0 < z₀ → ∃ O : Set (ComplexCoordinates 5),
      (∃ w₀ ∈ O, w₀ 0 = (z₀ : ℂ) ∧ ∀ i : Fin 4, w₀ i.succ = 0) ∧
        ∃ H : ComplexCoordinates 5 → ℂ, IsHolomorphicScalarIn O H ∧
          ∀ w ∈ O, w ∈ realLocus 5 → 0 < (w 0).re →
            (∀ μ : Fin 4, ‖w μ.succ‖ < massWidth (w 0).re) →
              H w = massiveLogFn L k (fun μ => w μ.succ) 0 1 (w 0).re) :
    ∃ D : Set (ComplexCoordinates 5), IsRealAnalyticIn D (massiveLogFnCoords L k) ∧
      (∀ z : ℝ, 0 < z → pointOfMassAndMomentum z 0 ∈ D) ∧ D ⊆ withinMassWidth := by
  classical
  choose! O hw₀ H hH' hval using hI
  let V : Set (ComplexCoordinates 5) := (⋃ z₀ ∈ Ioi (0 : ℝ), O z₀) ∩ complexWithinMassWidth
  have hVopen : IsOpen V := by
    refine (isOpen_biUnion fun z₀ hz₀ => (hH' z₀ hz₀).1).inter isOpen_complexWithinMassWidth
  refine ⟨V ∩ realLocus 5, ?_, ?_, ?_⟩
  · refine isRealAnalyticIn_of_eventuallyEq ⟨V, hVopen, rfl⟩ fun a ha => ?_
    obtain ⟨⟨hU, hP⟩, hreal⟩ := ha
    obtain ⟨z₀, hz₀, haO⟩ := mem_iUnion₂.1 hU
    refine ⟨O z₀ ∩ realLocus 5, asLine (H z₀), isRealAnalyticIn_asLine hH (hH' z₀ hz₀),
      ⟨haO, hreal⟩, ?_⟩
    have hO : O z₀ ∩ complexWithinMassWidth ∈ 𝓝 a :=
      ((hH' z₀ hz₀).1.inter isOpen_complexWithinMassWidth).mem_nhds ⟨haO, hP⟩
    filter_upwards [mem_nhdsWithin_of_mem_nhds hO, self_mem_nhdsWithin] with w hw hwr
    funext i
    exact hval z₀ hz₀ w hw.1 hwr hw.2.1 hw.2.2
  · intro z hz
    obtain ⟨w₀, hw₀O, h0, hsucc⟩ := hw₀ z hz
    have hpt : pointOfMassAndMomentum z 0 = w₀ := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pointOfMassAndMomentum, h0]
      · simp [pointOfMassAndMomentum, hsucc]
    have hP : pointOfMassAndMomentum z 0 ∈ complexWithinMassWidth := by
      refine ⟨by simpa [pointOfMassAndMomentum] using hz, fun μ => ?_⟩
      simpa [pointOfMassAndMomentum] using massWidth_pos hs hz
    refine ⟨⟨mem_iUnion₂.2 ⟨z, hz, hpt ▸ hw₀O⟩, hP⟩, fun j => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) j <;> simp [pointOfMassAndMomentum]
  · rintro w ⟨⟨-, hP⟩, hr⟩
    rw [withinMassWidth_eq]
    exact ⟨hP, hr⟩
theorem stiffnessCoords_realAnalytic {L : ℕ} (hL : 0 < L)
    (hK : AnalyticOnNhd ℝ (massiveStiffness hL) (Ioi 0)) :
    IsRealAnalyticIn positiveReals (stiffnessCoords hL) := by
  have hopen : IsOpen {w : ComplexCoordinates 1 | 0 < (w 0).re} :=
    isOpen_lt continuous_const (by fun_prop)
  refine ⟨⟨_, hopen, ?_⟩, fun a ha => ?_⟩
  · ext w
    simp only [positiveReals, mem_ofPred_eq, mem_inter_iff]
    tauto
  obtain ⟨p, hp⟩ := hK (a 0).re ha.2
  refine ⟨fun m _ => ((p.coeff (m 0) : ℝ) : ℂ), ?_⟩
  have hcont : Tendsto (fun w : ComplexCoordinates 1 => (w 0).re - (a 0).re) (𝓝 a) (𝓝 0) := by
    have : Continuous fun w : ComplexCoordinates 1 => (w 0).re - (a 0).re := by fun_prop
    simpa using this.tendsto a
  have hev := (hcont.eventually hp.eventually_hasSum).filter_mono
    (nhdsWithin_le_nhds (s := realLocus 1))
  filter_upwards [hev, self_mem_nhdsWithin] with w hw hwr
  rw [Pi.hasSum]
  intro i
  have hwre : w 0 = (((w 0).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using hwr 0)
  have hare : a 0 = (((a 0).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using ha.1 0)
  have hsum : HasSum (fun n : ℕ => ((((w 0).re - (a 0).re) ^ n * p.coeff n : ℝ) : ℂ))
      ((massiveStiffness hL (w 0).re : ℝ) : ℂ) := by
    have h1 := Complex.hasSum_ofReal.2 hw
    simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff] using h1
  have hcast := (Equiv.funUnique (Fin 1) ℕ).hasSum_iff.2 hsum
  have hd : w 0 - a 0 = (((w 0).re - (a 0).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, ← hwre, ← hare]
  have hterm : ∀ m : Fin 1 → ℕ,
      ((∏ j, (w j - a j) ^ m j) • (fun _ => ((p.coeff (m 0) : ℝ) : ℂ)) : ComplexCoordinates 1) i =
        ((fun n : ℕ => ((((w 0).re - (a 0).re) ^ n * p.coeff n : ℝ) : ℂ)) ∘
          Equiv.funUnique (Fin 1) ℕ) m := by
    intro m
    simp only [Fin.prod_univ_one, Pi.smul_apply, smul_eq_mul, Function.comp_apply, hd,
      Equiv.funUnique_apply]
    push_cast
    rfl
  convert hcast using 1
  · exact funext hterm
  · rfl
theorem claim_holds (hE : MassiveOpFunctions.Tempered.MassiveFamilyTempered)
    (hI : MassiveOpFunctions.LocallyHolomorphic.Claim)
    (hJ : MassiveOpFunctions.MixedPartialOfMassiveLogFn.Claim)
    (hK : MassiveStiffnessFunctions.StiffnessAnalytic)
    (hM : MassiveOpFunctions.SharpLogFn.SharpMixedDerivative)
    (hC : OneLoopLaw.TemperedStiffness.TemperedStiffnessClaim)
    (hH : PowerSeriesHolomorphy.Properties) : Claim := by
  intro L hL hS
  have hs := stripHalfWidth_pos hL hS hM
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    have hT := (hE L hS z hz).1
    refine ⟨hT, ?_⟩
    obtain ⟨hF, δ, π, e, hc⟩ := hT
    obtain ⟨-, -, -, b, -, hco, -⟩ := hC L hL hS _ δ π e hF hc
    exact ⟨_, hco⟩
  · intro k hk
    unfold AtLevel
    refine ⟨massiveLogFnCoords_realAnalytic hs hH (hI L hS k hk), fun z hz => ?_⟩
    rw [mixedPartialAtZero_eq_secondPartial fun p => massiveLogFn L k p 0 1 z]
    exact hJ L hL hS k hk z hz
  · unfold StiffnessAnalytic
    have hA := hK L hL hS
    exact ⟨stiffnessCoords_realAnalytic hL hA, fun z hz =>
      ⟨(hA z hz).differentiableAt, (hA.deriv z hz).differentiableAt⟩⟩
  · intro k hk
    unfold SharpAtLevel
    obtain ⟨⟨O, h0, hsub, G, hG, hval⟩, hform⟩ := hM L hL hS k hk
    refine ⟨?_, ?_⟩
    · unfold PeriodicOperators.ExistsOpenNear
      refine ⟨O ∩ realLocus 4, ⟨O, hG.1, rfl⟩, ?_, fun w hw => hsub hw.1, ?_⟩
      · exact singleton_subset_iff.2 ⟨h0, fun j => by simp⟩
      · refine isRealAnalyticIn_of_eventuallyEq ⟨O, hG.1, rfl⟩ fun a ha =>
          ⟨O ∩ realLocus 4, asLine G, isRealAnalyticIn_asLine hH hG, ha, ?_⟩
        filter_upwards [mem_nhdsWithin_of_mem_nhds (hG.1.mem_nhds ha.1), self_mem_nhdsWithin]
          with w hw hwr
        funext i
        exact hval w hw hwr
    · rw [mixedPartialAtZero_eq_secondPartial fun p => massiveLogFnSharp L k p 0 1]
      exact hform
end Tower.FullSpace.BackgroundJets.MassiveFunctionalAndJets
end YangMills.Construction
end
