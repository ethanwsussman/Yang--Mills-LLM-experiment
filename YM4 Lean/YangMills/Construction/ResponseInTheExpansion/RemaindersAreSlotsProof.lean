import YangMills.Construction.ResponseInTheExpansion.MajorisedObservablesAreAdmittedProof
import YangMills.Construction.ResponseInTheExpansion.RemainderAtTwoTopsProof
import YangMills.Construction.ResponseInTheExpansion.RemaindersAreSlots
import YangMills.Construction.ResponseInTheExpansion.RightShiftNearZero
import YangMills.Construction.ResponseInTheExpansion.SizeFromBoundedSlopes
import YangMills.Construction.ResponseInTheExpansion.SlopeAlongAFieldOfTheBonds
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongTheFieldsOfTheTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAtATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftOfTheChart
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.TorusComparison YangMills.Construction.WeightedResponses YangMills.Construction.Estimates YangMills.Construction.ConvexObservables YangMills.Construction.LinearResponse YangMills.Construction.CellCounting YangMills.Construction.FamilyNorms
namespace YangMills.Construction.ResponseInTheExpansion
namespace SlotLemmas
section Abstract
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem isOpen_ballSet (ρ : ℝ) : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.SharedProofs.p5886 <;> assumption
theorem sqrt_mul_rpow_neg_half {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * x ^ (-(1 / 2) : ℝ) = 1 ∧ x * x ^ (-(1 / 2) : ℝ) = Real.sqrt x := by
  have h1 : x ^ (-(1 / 2) : ℝ) = (Real.sqrt x)⁻¹ := by
    rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  rw [h1]
  refine ⟨mul_inv_cancel₀ hs.ne', ?_⟩
  field_simp
  nlinarith
variable {ρ : ℝ} {p : ℝ → ℝ}
theorem radialWeightProd_eq_zero_of_not_mem {η : BondField ι} (hη : ¬ ∀ b, ‖η b‖ < ρ) :
    radialWeightProd (cutoffFactor ρ p) η = 0 := by apply _root_.YangMills.Construction.Interpolation.ExpansionThirdDeriv.radialWeightProd_eq_zero_of_not_mem <;> assumption
theorem ballDensity_congr {Φ Φ' : BondField ι → ℝ} (he : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Φ' η = Φ η) :
    ballDensity (cutoffFactor ρ p) Φ = ballDensity (cutoffFactor ρ p) Φ' := by
  funext η
  unfold ballDensity
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · rw [he η hη]
  · rw [radialWeightProd_eq_zero_of_not_mem hη]
    simp
structure IsBallLaw (ρ : ℝ) (p : ℝ → ℝ) (Φ : BondField ι → ℝ) : Prop where
  density_nonneg : ∀ η, 0 ≤ ballDensity (cutoffFactor ρ p) Φ η
  integrable : Integrable (ballDensity (cutoffFactor ρ p) Φ)
  integral_pos : 0 < ∫ η, ballDensity (cutoffFactor ρ p) Φ η
  continuousOn : ContinuousOn (ballDensity (cutoffFactor ρ p) Φ) {η | ∀ b, ‖η b‖ < ρ}
  eq_zero_off : ∀ η : BondField ι, ¬ (∀ b, ‖η b‖ < ρ) → ballDensity (cutoffFactor ρ p) Φ η = 0
theorem isBallLaw_of_continuous (hLaw : normalizedBallLawIsProbabilityStatement) (hρ : 0 < ρ) (hcut : IsCutoff ρ p)
    {Φ Φ' : BondField ι → ℝ} (hc : Continuous Φ') (he : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Φ' η = Φ η) :
    IsBallLaw ρ p Φ := by
  obtain ⟨-, -, -, -, -, h1, h2, h3, h4, h5, -⟩ := hLaw ι ρ p Φ' hρ hcut hc
  rw [← ballDensity_congr he] at h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, fun η hη => by
    by_contra hne
    exact hη ((h5 η).1 hne)⟩
variable {Φ : BondField ι → ℝ}
theorem abs_ballExpectation_le (hL : IsBallLaw ρ p Φ) {G : BondField ι → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |G η| ≤ B) : |ballExpectation (cutoffFactor ρ p) Φ G| ≤ B := by
  unfold ballExpectation
  rw [abs_div, abs_of_pos hL.integral_pos, div_le_iff₀ hL.integral_pos, ← integral_const_mul]
  have hb : Integrable (fun η => B * ballDensity (cutoffFactor ρ p) Φ η) := hL.integrable.const_mul B
  have := norm_integral_le_of_norm_le (f := fun η => G η * ballDensity (cutoffFactor ρ p) Φ η) hb
    (Filter.Eventually.of_forall fun η => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hL.density_nonneg η)]
      by_cases hη : ∀ b, ‖η b‖ < ρ
      · exact mul_le_mul_of_nonneg_right (hG η hη) (hL.density_nonneg η)
      · rw [hL.eq_zero_off η hη]
        simp)
  simpa [Real.norm_eq_abs] using this
theorem integrable_mul_density_of_bounded (hL : IsBallLaw ρ p Φ) {G : BondField ι → ℝ} {B : ℝ}
    (hc : ContinuousOn G {η | ∀ b, ‖η b‖ < ρ}) (hG : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |G η| ≤ B) :
    Integrable fun η => G η * ballDensity (cutoffFactor ρ p) Φ η := by
  have hU := (isOpen_ballSet (ι := ι) ρ).measurableSet
  have e : (fun η => G η * ballDensity (cutoffFactor ρ p) Φ η) =
      Set.indicator {η | ∀ b, ‖η b‖ < ρ} fun η => G η * ballDensity (cutoffFactor ρ p) Φ η := by
    funext η
    by_cases hη : ∀ b, ‖η b‖ < ρ
    · rw [Set.indicator_of_mem (show η ∈ {η : BondField ι | ∀ b, ‖η b‖ < ρ} from hη)]
    · rw [Set.indicator_of_notMem (show η ∉ {η : BondField ι | ∀ b, ‖η b‖ < ρ} from hη), hL.eq_zero_off η hη, mul_zero]
  have hm : AEStronglyMeasurable (fun η => G η * ballDensity (cutoffFactor ρ p) Φ η) volume := by
    rw [e, aestronglyMeasurable_indicator_iff hU]
    exact (hc.mul hL.continuousOn).aestronglyMeasurable hU
  refine Integrable.mono' (hL.integrable.const_mul |B|) hm (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hL.density_nonneg η)]
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · exact mul_le_mul_of_nonneg_right ((hG η hη).trans (le_abs_self B)) (hL.density_nonneg η)
  · rw [hL.eq_zero_off η hη]
    simp
theorem momentBound_of_bounded (hL : IsBallLaw ρ p Φ) {G : BondField ι → ℝ} {B : ℝ} (q : ℕ) (hB : 0 ≤ B)
    (hc : ContinuousOn G {η | ∀ b, ‖η b‖ < ρ}) (hG : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |G η| ≤ B) :
    MomentBound (cutoffFactor ρ p) Φ G q B := by
  have hq : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |(|G η| ^ q)| ≤ B ^ q := fun η hη => by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hG η hη) q
  refine ⟨integrable_mul_density_of_bounded hL (hc.abs.pow q) hq, ?_⟩
  exact (le_abs_self _).trans (abs_ballExpectation_le hL (by positivity) hq)
theorem abs_ballExpectation_sub_le (hL : IsBallLaw ρ p Φ) {G : BondField ι → ℝ} {c B : ℝ} (hB : 0 ≤ B)
    (hc : ContinuousOn G {η | ∀ b, ‖η b‖ < ρ}) (hG : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |G η - c| ≤ B) :
    |ballExpectation (cutoffFactor ρ p) Φ G - c| ≤ B := by
  have h1 := abs_ballExpectation_le hL hB hG
  have hi : Integrable fun η => (G η - c) * ballDensity (cutoffFactor ρ p) Φ η :=
    integrable_mul_density_of_bounded hL (hc.sub continuousOn_const) hG
  have hi2 : Integrable fun η => c * ballDensity (cutoffFactor ρ p) Φ η := hL.integrable.const_mul c
  have e : ballExpectation (cutoffFactor ρ p) Φ (fun η => G η - c) = ballExpectation (cutoffFactor ρ p) Φ G - c := by
    unfold ballExpectation
    have e1 : (fun η => G η * ballDensity (cutoffFactor ρ p) Φ η) =
        fun η => (G η - c) * ballDensity (cutoffFactor ρ p) Φ η + c * ballDensity (cutoffFactor ρ p) Φ η := by
      funext η
      ring
    rw [e1, integral_add hi hi2, integral_const_mul, add_div, mul_div_assoc, div_self hL.integral_pos.ne']
    ring
  rw [← e]
  exact h1
theorem continuousOn_bondGradNorm {H : BondField ι → ℝ} (hH : ContDiffOn ℝ 1 H {η | ∀ b, ‖η b‖ < ρ}) (b : ι) :
    ContinuousOn (bondGradNorm H b) {η | ∀ b, ‖η b‖ < ρ} := by
  have h1 : ContinuousOn (fderiv ℝ H) {η | ∀ b, ‖η b‖ < ρ} :=
    hH.continuousOn_fderiv_of_isOpen (isOpen_ballSet ρ) le_rfl
  unfold bondGradNorm
  exact (h1.clm_comp continuousOn_const).norm
theorem hasGradientBound_of_pointwise (hL : IsBallLaw ρ p Φ) {x κ h M : ℝ} {dZ g : ι → ℝ} {H : BondField ι → ℝ}
    (hH : ContDiffOn ℝ 1 H {η | ∀ b, ‖η b‖ < ρ}) (hM : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |H η| ≤ M)
    (hg : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm H b η ≤ g b)
    (hgb : ∀ b, g b ≤ Real.sqrt x * h * Real.exp (-(2 * κ * dZ b))) (hg0 : ∀ b, 0 ≤ g b) :
    HasGradientBound ρ (cutoffFactor ρ p) Φ x κ h dZ H := by
  have hM0 : ∀ q : ℕ, ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |(|H η| ^ q)| ≤ |M| ^ q := fun q η hη => by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (abs_nonneg _) ((hM η hη).trans (le_abs_self M)) q
  have hgq : ∀ (b : ι) (q : ℕ) (η : BondField ι), (∀ b, ‖η b‖ < ρ) →
      |(|bondGradNorm H b η| ^ q)| ≤ (g b) ^ q := fun b q η hη => by
    have hnn : 0 ≤ bondGradNorm H b η := norm_nonneg _
    rw [abs_of_nonneg (by positivity), abs_of_nonneg hnn]
    exact pow_le_pow_left₀ hnn (hg η hη b) q
  refine ⟨fun η hη => (hH.contDiffAt ((isOpen_ballSet ρ).mem_nhds hη)).differentiableAt (by simp),
    fun q hq => ⟨?_, fun b => ?_⟩, fun b => ?_⟩
  · exact integrable_mul_density_of_bounded hL (hH.continuousOn.abs.pow q) (hM0 q)
  · exact integrable_mul_density_of_bounded hL ((continuousOn_bondGradNorm hH b).abs.pow q) (hgq b q)
  · refine momentBound_of_bounded hL 2 ((hg0 b).trans (hgb b)) (continuousOn_bondGradNorm hH b) fun η hη => ?_
    have hnn : 0 ≤ bondGradNorm H b η := norm_nonneg _
    rw [abs_of_nonneg hnn]
    exact (hg η hη b).trans (hgb b)
end Abstract
section Torus
variable {F : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι]
open Classical in
def extendByZeroCLM (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι) :
    BondField ι →L[ℝ] StepVariable (finiteCells F) :=
  ContinuousLinearMap.pi fun b => ∑ i ∈ Λ,
    if j i = b then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) i else 0
theorem extendByZeroCLM_apply (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι) (ζ : BondField ι) :
    extendByZeroCLM j Λ ζ = _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ := by
  classical
  funext b
  simp only [extendByZeroCLM, _root_.YangMills.Construction.Interpolation.extendByZero, ContinuousLinearMap.coe_pi', sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : j i = b <;> simp [h]
theorem extendByZero_mem_ball {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (Λ : Finset ι)
    {ρ : ℝ} (hρ : 0 < ρ) {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < ρ) (b : ↥(chordBonds (finiteCells F))) :
    ‖_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b‖ < ρ := by apply _root_.YangMills.SharedProofs.p46738 <;> assumption
theorem extendByZero_single {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (Λ : Finset ι)
    (i : ι) (u : BondVector) :
    _root_.YangMills.Construction.Interpolation.extendByZero j Λ (Pi.single i u) = if i ∈ Λ then Pi.single (j i) u else 0 := by
  classical
  funext b
  unfold _root_.YangMills.Construction.Interpolation.extendByZero
  by_cases hi : i ∈ Λ
  · rw [if_pos hi, Finset.sum_eq_single_of_mem i hi (fun i' _ hne => by simp [Pi.single_eq_of_ne hne])]
    by_cases hb : j i = b
    · subst hb
      simp
    · rw [if_neg hb, Pi.single_eq_of_ne (Ne.symm hb)]
  · rw [if_neg hi]
    refine Finset.sum_eq_zero fun i' hi' => ?_
    have : i' ≠ i := fun h => hi (h ▸ hi')
    simp [Pi.single_eq_of_ne this]
theorem bondGradNorm_comp_extendByZero_le {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j)
    (Λ : Finset ι) {A : StepVariable (finiteCells F) → ℝ} {ζ : BondField ι}
    (hA : DifferentiableAt ℝ A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) (i : ι) {g : ℝ}
    (hg0 : 0 ≤ g) (hg : i ∈ Λ → bondGradNorm A (j i) (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) ≤ g) :
    bondGradNorm (fun ζ' => A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ')) i ζ ≤ g := by
  have e : (fun ζ' => A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ')) = A ∘ extendByZeroCLM j Λ := by
    funext ζ'
    simp [extendByZeroCLM_apply]
  have hA' : DifferentiableAt ℝ A (extendByZeroCLM j Λ ζ) := by rwa [extendByZeroCLM_apply]
  have hd : fderiv ℝ (A ∘ extendByZeroCLM j Λ) ζ = (fderiv ℝ A (extendByZeroCLM j Λ ζ)).comp (extendByZeroCLM j Λ) :=
    fderiv_comp _ hA' (extendByZeroCLM j Λ).differentiableAt |>.trans (by rw [(extendByZeroCLM j Λ).fderiv])
  unfold bondGradNorm
  rw [e, hd, extendByZeroCLM_apply]
  refine ContinuousLinearMap.opNorm_le_bound _ hg0 fun u => ?_
  have e2 : (((fderiv ℝ A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)).comp (extendByZeroCLM j Λ)).comp
      (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) i)) u =
      fderiv ℝ A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) (_root_.YangMills.Construction.Interpolation.extendByZero j Λ (Pi.single i u)) := by
    show fderiv ℝ A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) (extendByZeroCLM j Λ (Pi.single i u)) = _
    rw [extendByZeroCLM_apply]
  rw [e2, extendByZero_single hj]
  by_cases hi : i ∈ Λ
  · rw [if_pos hi]
    have h1 := ((fderiv ℝ A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)).comp
      (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) (j i))).le_opNorm u
    exact h1.trans (mul_le_mul_of_nonneg_right (hg hi) (norm_nonneg _))
  · rw [if_neg hi]
    simp
    positivity
variable {ρ : ℝ} {p : ℝ → ℝ}
theorem isBallLaw_freezingHomotopy (hLaw : normalizedBallLawIsProbabilityStatement) (hρ : 0 < ρ) (hcut : IsCutoff ρ p)
    {Ψ Ψ' : StepVariable (finiteCells F) → ℝ} (hc : Continuous Ψ')
    (he : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → Ψ' η = Ψ η)
    (lam x v : ℝ) (Λ : Finset ↥(chordBonds (finiteCells F))) : IsBallLaw ρ p (freezingHomotopy lam x Λ Ψ v) := by
  refine isBallLaw_of_continuous hLaw hρ hcut (Φ' := freezingHomotopy lam x Λ Ψ' v) ?_ fun η hη => ?_
  · have hp : Continuous fun ζ : StepVariable (finiteCells F) =>
        _root_.YangMills.Construction.Interpolation.extendByZero (id : ↥(chordBonds (finiteCells F)) → _) Λ ζ := by
      have : (fun ζ : StepVariable (finiteCells F) => _root_.YangMills.Construction.Interpolation.extendByZero (id : ↥(chordBonds (finiteCells F)) → _) Λ ζ) =
          extendByZeroCLM id Λ := by
        funext ζ
        rw [extendByZeroCLM_apply]
      rw [this]
      exact (extendByZeroCLM id Λ).continuous
    unfold freezingHomotopy frozenExponent
    refine (continuous_const.mul hc).add (continuous_const.mul ((hc.comp hp).add ?_))
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (((continuous_apply i).norm).pow 2)
  · unfold freezingHomotopy frozenExponent
    rw [he η hη, he _ (extendByZero_mem_ball Function.injective_id Λ hρ hη)]
theorem isBallLaw_pairingHomotopy (hLaw : normalizedBallLawIsProbabilityStatement) (hρ : 0 < ρ) (hcut : IsCutoff ρ p)
    {j j' : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (hj' : Function.Injective j')
    {Ψ Ψ' Ψ₂ Ψ₂' : StepVariable (finiteCells F) → ℝ} (hc : Continuous Ψ')
    (he : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → Ψ' η = Ψ η)
    (hc₂ : Continuous Ψ₂') (he₂ : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → Ψ₂' η = Ψ₂ η)
    (th : ℝ) : IsBallLaw ρ p (pairingHomotopy j j' Ψ Ψ₂ th) := by
  refine isBallLaw_of_continuous hLaw hρ hcut (Φ' := pairingHomotopy j j' Ψ' Ψ₂' th) ?_ fun η hη => ?_
  · have hp : ∀ l : ι → ↥(chordBonds (finiteCells F)), Continuous fun ζ : BondField ι => toTorus l ζ := fun l => by
      have : (fun ζ : BondField ι => toTorus l ζ) = extendByZeroCLM l Finset.univ := by
        funext ζ
        rw [extendByZeroCLM_apply]
        rfl
      rw [this]
      exact (extendByZeroCLM l Finset.univ).continuous
    unfold pairingHomotopy
    exact (continuous_const.mul (hc.comp (hp j))).add (continuous_const.mul (hc₂.comp (hp j')))
  · unfold pairingHomotopy
    rw [he (toTorus j η) (extendByZero_mem_ball hj Finset.univ hρ hη),
      he₂ (toTorus j' η) (extendByZero_mem_ball hj' Finset.univ hρ hη)]
theorem comparisonBoundsOnTorus_of_pointwise (hLaw : normalizedBallLawIsProbabilityStatement) (hρ : 0 < ρ)
    (hcut : IsCutoff ρ p) {Ψ Ψ' : StepVariable (finiteCells F) → ℝ} (hc : Continuous Ψ')
    (he : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → Ψ' η = Ψ η)
    {lam x κ α M : ℝ} {q : ℕ} {Y : F.Cell} {A : StepVariable (finiteCells F) → ℝ}
    {Dd : ↥(chordBonds (finiteCells F)) → ℝ}
    (hα : 0 ≤ α) (hA : ContDiffOn ℝ 1 A {η | ∀ b, ‖η b‖ < ρ})
    (hM : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → |A η| ≤ M)
    (hg : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm A b η ≤ Dd b) (hD0 : ∀ b, 0 ≤ Dd b)
    (hDb : ∀ b, Dd b ≤ Real.sqrt x * α * Real.exp (-(2 * κ * bondDistToCell Y b)))
    (hfr : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      |A η - A (freezeOutside (bondsNearCell Y q) η)| ≤ α * Real.exp (-(4 * κ * q))) :
    ComparisonHypothesesOnTorus ρ lam x κ α p q Y Ψ A := by
  set Λ := bondsNearCell Y q with hΛ
  have hinj : Function.Injective (id : ↥(chordBonds (finiteCells F)) → _) := Function.injective_id
  have hL0 : IsBallLaw ρ p (fun _ : StepVariable (finiteCells F) => (0 : ℝ)) :=
    isBallLaw_of_continuous hLaw hρ hcut continuous_const fun _ _ => rfl
  have hrim : ∀ η : StepVariable (finiteCells F), radialWeightProd (cutoffFactor ρ p) η =
      ballDensity (cutoffFactor ρ p) (fun _ : StepVariable (finiteCells F) => (0 : ℝ)) η := fun η => by
    simp [ballDensity]
  have hmaps : Set.MapsTo (extendByZeroCLM (id : ↥(chordBonds (finiteCells F)) → _) Λ)
      {η | ∀ b, ‖η b‖ < ρ} {η | ∀ b, ‖η b‖ < ρ} :=
    fun η hη b => by
      rw [extendByZeroCLM_apply]
      exact extendByZero_mem_ball hinj Λ hρ hη b
  have hfz : ContDiffOn ℝ 1 (fun η => A (freezeOutside Λ η)) {η | ∀ b, ‖η b‖ < ρ} := by
    have := hA.comp (extendByZeroCLM (id : ↥(chordBonds (finiteCells F)) → _) Λ).contDiff.contDiffOn hmaps
    refine this.congr fun η _ => ?_
    simp only [Function.comp, extendByZeroCLM_apply]
    rfl
  have hfM : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → |A (freezeOutside Λ η)| ≤ M := fun η hη =>
    hM _ (extendByZero_mem_ball hinj Λ hρ hη)
  have hfg : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      ∀ b, bondGradNorm (fun η => A (freezeOutside Λ η)) b η ≤ Dd b := fun η hη b => by
    have hin := extendByZero_mem_ball hinj Λ hρ hη
    have hdiff : DifferentiableAt ℝ A (_root_.YangMills.Construction.Interpolation.extendByZero id Λ η) :=
      (hA.contDiffAt ((isOpen_ballSet ρ).mem_nhds hin)).differentiableAt (by simp)
    exact bondGradNorm_comp_extendByZero_le hinj Λ hdiff b (hD0 b) fun _ => hg _ hin b
  refine ⟨?_, ?_, fun v _ _ => ?_, fun v _ _ => ?_, fun v _ _ => ?_⟩
  · have := integrable_mul_density_of_bounded hL0 hA.continuousOn hM
    refine this.congr (Filter.Eventually.of_forall fun η => ?_)
    simp only [hrim]
  · have := integrable_mul_density_of_bounded hL0 hfz.continuousOn hfM
    refine this.congr (Filter.Eventually.of_forall fun η => ?_)
    simp only [hrim]
    rfl
  · exact hasGradientBound_of_pointwise (isBallLaw_freezingHomotopy hLaw hρ hcut hc he lam x v Λ) hA hM hg hDb hD0
  · exact hasGradientBound_of_pointwise (isBallLaw_freezingHomotopy hLaw hρ hcut hc he lam x v Λ) hfz hfM hfg hDb hD0
  · exact abs_ballExpectation_le (isBallLaw_freezingHomotopy hLaw hρ hcut hc he lam x v Λ) (by positivity) hfr
end Torus
section Shift
theorem imaginaryCoords_add (v w : imaginaryQuaternions) :
    _root_.YangMills.Construction.Interpolation.imaginaryCoords (v + w) = _root_.YangMills.Construction.Interpolation.imaginaryCoords v + _root_.YangMills.Construction.Interpolation.imaginaryCoords w := by
  ext i
  fin_cases i <;> simp [_root_.YangMills.Construction.Interpolation.imaginaryCoords]
theorem imaginaryCoords_smul (c : ℝ) (w : imaginaryQuaternions) : _root_.YangMills.Construction.Interpolation.imaginaryCoords (c • w) = c • _root_.YangMills.Construction.Interpolation.imaginaryCoords w := by
  ext i
  fin_cases i <;> simp [_root_.YangMills.Construction.Interpolation.imaginaryCoords]
def imaginaryCoordsCLM : imaginaryQuaternions →L[ℝ] BondVector :=
  LinearMap.toContinuousLinearMap
    { toFun := _root_.YangMills.Construction.Interpolation.imaginaryCoords, map_add' := imaginaryCoords_add, map_smul' := imaginaryCoords_smul }
theorem toImaginary_smul (c : ℝ) (v : BondVector) : toImaginary (c • v) = c • toImaginary v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.toImaginary_smul <;> assumption
theorem toImaginary_add (v w : BondVector) : toImaginary (v + w) = toImaginary v + toImaginary w := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.toImaginary_add <;> assumption
def toImaginaryCLM : BondVector →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := toImaginary, map_add' := toImaginary_add, map_smul' := toImaginary_smul }
theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
theorem norm_imaginaryCoords (w : imaginaryQuaternions) : ‖_root_.YangMills.Construction.Interpolation.imaginaryCoords w‖ = ‖w‖ := by apply _root_.YangMills.SharedProofs.p6124 <;> assumption
theorem translatedField_contDiffAt_and_fderiv_le {Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions}
    {C : ℝ} {w₀ D X : imaginaryQuaternions} {v : BondVector} (hC0 : 0 ≤ C) (hX : ‖X‖ = 1)
    (hw : ‖w₀ + toImaginary v‖ ≤ 1) (hT : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Th (w₀ + toImaginary v))
    (hb : ‖iteratedFDeriv ℝ 1 Th (w₀ + toImaginary v)‖ ≤ C) :
    ContDiffAt ℝ 1 (fun v' : BondVector => _root_.YangMills.Construction.Interpolation.imaginaryCoords (D + Th (w₀ + toImaginary v') X)) v ∧
      ‖fderiv ℝ (fun v' : BondVector => _root_.YangMills.Construction.Interpolation.imaginaryCoords (D + Th (w₀ + toImaginary v') X)) v‖ ≤ C := by
  have hTd : HasFDerivAt Th (fderiv ℝ Th (w₀ + toImaginary v)) (w₀ + toImaginaryCLM v) :=
    (hT.differentiableAt (by simp)).hasFDerivAt
  have h1 : HasFDerivAt (fun v' : BondVector => w₀ + toImaginaryCLM v') toImaginaryCLM v :=
    toImaginaryCLM.hasFDerivAt.const_add w₀
  have h2 : HasFDerivAt (fun v' : BondVector => Th (w₀ + toImaginaryCLM v'))
      ((fderiv ℝ Th (w₀ + toImaginary v)).comp toImaginaryCLM) v :=
    HasFDerivAt.comp (g := Th) (f := fun v' : BondVector => w₀ + toImaginaryCLM v') v hTd h1
  have h3 := h2.clm_apply (hasFDerivAt_const X v)
  have h4 := h3.const_add D
  have h5 := imaginaryCoordsCLM.hasFDerivAt.comp v h4
  have e : (fun v' : BondVector => _root_.YangMills.Construction.Interpolation.imaginaryCoords (D + Th (w₀ + toImaginary v') X)) =
      imaginaryCoordsCLM ∘ fun x => D + (Th (w₀ + toImaginaryCLM x)) X := rfl
  constructor
  · rw [e]
    refine imaginaryCoordsCLM.contDiff.contDiffAt.comp v (contDiffAt_const.add ?_)
    have hc : ContDiffAt ℝ 1 (fun v' : BondVector => w₀ + toImaginaryCLM v') v :=
      contDiffAt_const.add toImaginaryCLM.contDiff.contDiffAt
    have hT1 : ContDiffAt ℝ 1 Th (w₀ + toImaginaryCLM v) := hT.of_le (by norm_num)
    exact (ContDiffAt.comp v hT1 hc).clm_apply contDiffAt_const
  · rw [e, h5.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun u => ?_
    have e2 : ∀ a : imaginaryQuaternions, ‖fderiv ℝ Th (w₀ + toImaginary v) a‖ ≤ C * ‖a‖ := fun a => by
      have h6 := (iteratedFDeriv ℝ 1 Th (w₀ + toImaginary v)).le_opNorm (fun _ => a)
      rw [iteratedFDeriv_one_apply] at h6
      simp only [Finset.univ_unique, Finset.prod_singleton] at h6
      exact h6.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    have e3 : (imaginaryCoordsCLM.comp (((Th (w₀ + toImaginaryCLM v)).comp (0 : BondVector →L[ℝ] imaginaryQuaternions)) +
        ((fderiv ℝ Th (w₀ + toImaginary v)).comp toImaginaryCLM).flip X)) u =
        _root_.YangMills.Construction.Interpolation.imaginaryCoords (fderiv ℝ Th (w₀ + toImaginary v) (toImaginary u) X) := by
      have e4 : (((Th (w₀ + toImaginaryCLM v)).comp (0 : BondVector →L[ℝ] imaginaryQuaternions)) +
          ((fderiv ℝ Th (w₀ + toImaginary v)).comp toImaginaryCLM).flip X) u =
          fderiv ℝ Th (w₀ + toImaginary v) (toImaginary u) X := by
        simp
        rfl
      exact congrArg _root_.YangMills.Construction.Interpolation.imaginaryCoords e4
    rw [e3, norm_imaginaryCoords]
    calc ‖fderiv ℝ Th (w₀ + toImaginary v) (toImaginary u) X‖ ≤
          ‖fderiv ℝ Th (w₀ + toImaginary v) (toImaginary u)‖ * ‖X‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖toImaginary u‖ * 1 := by
          rw [hX]
          exact mul_le_mul_of_nonneg_right (e2 _) zero_le_one
      _ = C * ‖u‖ := by
          rw [mul_one, norm_toImaginary]
end Shift
section Block
variable {F : BlockFrame}
theorem cellSupDist_le_cellSetDiameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
theorem bondSpan_le_cellSetDiameter (Y : F.Cell) {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (c : Fin k → F.Site F.top × Fin 4) :
    bondSpan Y c ≤ cellSetDiameter (insert Y (chordBondCells b ∪ topBondCells c)) := by
  classical
  set P := insert Y (chordBondCells b ∪ topBondCells c) with hP
  have hY : Y ∈ P := Finset.mem_insert_self _ _
  have hc : ∀ l, (c l).1 ∈ P := fun l =>
    Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩))
  exact max_le (Finset.sup_le fun l _ => cellSupDist_le_cellSetDiameter hY (hc l))
    (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => cellSupDist_le_cellSetDiameter (hc l) (hc l'))
theorem enclosingCell_dist_le_cellSetDiameter (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x) (Y : F.Cell)
    {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (c : Fin k → F.Site F.top × Fin 4) (i : Fin l) :
    cellSupDist (enclosingCell (b i).1.1) Y ≤ cellSetDiameter (insert Y (chordBondCells b ∪ topBondCells c)) := by
  classical
  refine cellSupDist_le_cellSetDiameter
    (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)))
    (Finset.mem_insert_self _ _)
open Classical in
def sitesOfBlock (Y : F.Cell) : Finset (F.Site F.depth) :=
  (sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y
structure BlockSumDerivBounds (ρ κ B : ℝ) (Y : F.Cell) (K : AboveFrames F) (V : F.GaugeField F.top) : Prop where
  smooth : JointlyContDiffOnBalls ρ V K
  deriv_one : ∀ (ξ : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3))
    (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), (∀ b, ‖ξ b‖ ≤ ρ) → ‖u‖ = 1 → k ≤ 2 →
    AreUnitVectors X →
    |jointMixedDeriv K ξ V ![b] ![u] c X| ≤
      B * Real.exp (-(2 ^ 5 * κ * bondSpan Y c)) * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y))
  deriv_two : ∀ (ξ : StepVariable (finiteCells F)) (b b' : ↥(chordBonds (finiteCells F)))
    (u u' : EuclideanSpace ℝ (Fin 3)),
    (∀ b, ‖ξ b‖ ≤ ρ) → ‖u‖ = 1 → ‖u'‖ = 1 →
    |jointMixedDeriv K ξ V ![b, b'] ![u, u'] (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions)| ≤
      B * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) *
        Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b'.1.1) Y))
theorem blockSumDerivBounds_of_expansion (hD : mixedDerivativesOnBallsStatement)
    (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    {ρ κ Cb e e₃ N : ℝ} {Q : ColdHalfLaw} {r : F.Site F.depth → F.GaugeField F.depth → ℝ} {Y : F.Cell}
    {V : F.GaugeField F.top} (hκ : 0 < κ)
    (hCb : 0 ≤ Cb) (he : 0 ≤ e) (hee : e ≤ e₃) (hN : ((sitesOfBlock Y).card : ℝ) ≤ N)
    (hs : HasMixedDerivBounds ρ κ Cb e e₃ (Q.liftedExpansion r) V) :
    BlockSumDerivBounds ρ κ (N * (Cb * e₃)) Y (Q.blockSum r Y) V := by
  classical
  have he₃ : 0 ≤ e₃ := he.trans hee
  have hK : Q.blockSum r Y = fun ζ V' => ∑ y ∈ sitesOfBlock Y, Q.liftedExpansion r y ζ V' := rfl
  have hsm : ∀ y ∈ sitesOfBlock Y, JointlyContDiffOnBalls ρ V (Q.liftedExpansion r y) := fun y _ => hs.smooth y
  have hY : ∀ y ∈ sitesOfBlock Y, enclosingCell y = Y := fun y hy => (Finset.mem_filter.1 hy).2
  obtain ⟨hadd, -⟩ := hD F ρ V
  refine ⟨?_, fun ξ b u k c X hξ hu hk hX => ?_, fun ξ b b' u u' hξ hu hu' => ?_⟩
  · rw [hK]
    intro k c X η hη
    exact ContDiffAt.sum fun y hy => hsm y hy k c X η hη
  · rw [hK, hadd.sum_one _ _ _ c X ξ b u hsm hk hξ]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ y ∈ sitesOfBlock Y, |jointMixedDeriv (Q.liftedExpansion r y) ξ V ![b] ![u] c X| ≤
        Cb * e₃ * Real.exp (-(2 ^ 5 * κ * bondSpan Y c)) *
          Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) := by
      intro y hy
      refine (hs.deriv_one y ξ b u k c X hξ hu hk hX).trans ?_
      rw [hY y hy]
      set Sp : ℝ := ((cellSetDiameter (insert Y (chordBondCells ![b] ∪ topBondCells c)) : ℕ) : ℝ) with hSp
      have h1 : (bondSpan Y c : ℝ) ≤ Sp := Nat.cast_le.2 (bondSpan_le_cellSetDiameter Y ![b] c)
      have h2 : (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤ Sp :=
        Nat.cast_le.2 (enclosingCell_dist_le_cellSetDiameter hsym Y ![b] c 0)
      have h3 : (if k = 2 then e₃ else e) ≤ e₃ := by
        split_ifs
        · exact le_rfl
        · exact hee
      calc Cb * (if k = 2 then e₃ else e) * Real.exp (-(2 ^ 7 * κ * Sp)) ≤ Cb * e₃ * Real.exp (-(2 ^ 7 * κ * Sp)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hCb) (Real.exp_pos _).le
        _ ≤ Cb * e₃ * (Real.exp (-(2 ^ 5 * κ * bondSpan Y c)) *
              Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [← Real.exp_add, Real.exp_le_exp]
            have h5 := mul_nonneg hκ.le (sub_nonneg.2 h1)
            have h6 := mul_nonneg hκ.le (sub_nonneg.2 h2)
            have h7 : 0 ≤ κ * Sp := mul_nonneg hκ.le (le_trans (Nat.cast_nonneg _) h1)
            nlinarith
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hE1 := Real.exp_pos (-(2 ^ 5 * κ * bondSpan Y c))
    have hE2 := Real.exp_pos (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y))
    calc ((sitesOfBlock Y).card : ℝ) * (Cb * e₃ * Real.exp (-(2 ^ 5 * κ * bondSpan Y c)) *
          Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)))
        ≤ N * (Cb * e₃ * Real.exp (-(2 ^ 5 * κ * bondSpan Y c)) *
          Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y))) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = _ := by ring
  · rw [hK, hadd.sum_two _ _ _ ξ b b' u u' hsm hξ]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ y ∈ sitesOfBlock Y, |jointMixedDeriv (Q.liftedExpansion r y) ξ V ![b, b'] ![u, u']
        (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)| ≤
        Cb * e₃ * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) *
          Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b'.1.1) Y)) := by
      intro y hy
      refine (hs.deriv_two y ξ b b' u u' hξ hu hu').trans ?_
      rw [hY y hy]
      set Sp : ℝ := ((cellSetDiameter (insert Y (chordBondCells ![b, b'] ∪
        topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) : ℕ) : ℝ) with hSp
      have h1 : (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤ Sp :=
        Nat.cast_le.2 (enclosingCell_dist_le_cellSetDiameter hsym Y ![b, b'] (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) 0)
      have h2 : (cellSupDist (enclosingCell b'.1.1) Y : ℝ) ≤ Sp :=
        Nat.cast_le.2 (enclosingCell_dist_le_cellSetDiameter hsym Y ![b, b'] (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) 1)
      calc Cb * e * Real.exp (-(2 ^ 7 * κ * Sp)) ≤ Cb * e₃ * Real.exp (-(2 ^ 7 * κ * Sp)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hee hCb) (Real.exp_pos _).le
        _ ≤ Cb * e₃ * (Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) *
              Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b'.1.1) Y))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [← Real.exp_add, Real.exp_le_exp]
            have h5 := mul_nonneg hκ.le (sub_nonneg.2 h1)
            have h6 := mul_nonneg hκ.le (sub_nonneg.2 h2)
            nlinarith
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hE1 := Real.exp_pos (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y))
    have hE2 := Real.exp_pos (-(2 ^ 6 * κ * cellSupDist (enclosingCell b'.1.1) Y))
    calc ((sitesOfBlock Y).card : ℝ) * (Cb * e₃ * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) *
          Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b'.1.1) Y)))
        ≤ N * (Cb * e₃ * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) *
          Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b'.1.1) Y))) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = _ := by ring
theorem isPseudoMetricOnBonds_chordBondDist (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) :
    IsPseudoMetricOnBonds (_root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist F) where
  self b := by simp [_root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist, cellSupDist]
  symm b b' := by simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist]; rw [hsym]
  triangle b b' b'' := by
    simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist]
    exact_mod_cast htri _ _ _
theorem norm_le_of_lt {ρ : ℝ} {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < ρ) : ∀ b, ‖η b‖ ≤ ρ :=
  fun b => (hη b).le
theorem isSlot_blockSum (hSl : LocalSizeOfBoundedPartials) (hD : mixedDerivativesOnBallsStatement)
    {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {f : LocalFamily} {V : F.GaugeField F.top} {Y : F.Cell} {K : AboveFrames F}
    {B G W W₆ : ℝ} {Cq : ℕ → ℝ}
    (hρ : 0 < T.ballRadius) (hx1 : 1 ≤ x) (hlam : 0 < T.chainParams.lam) (hκ : 0 < T.κ) (hcut : IsCutoff T.ballRadius T.p)
    (hdist : IsPseudoMetricOnBonds (_root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist F))
    (hconv : HasUniformlyConvexLaw T.ballRadius T.chainParams.lam x T.κ T.Ct (_root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist F)
      ((coldHalfLawAt T x f).exponent V)) (hW0 : 0 ≤ W)
    (hW : ∀ b₀ : ↥(chordBonds (finiteCells F)), ∑ b, Real.exp (-(2 * T.κ * _root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist F b b₀)) ≤ W)
    (hW₆ : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * T.κ * cellSupDist (enclosingCell b.1.1) Y)) ≤ W₆)
    (hCq : ∀ q, |lpMomentConstant T.chainParams.lam (1 / 2) W q * 1| ≤ Cq q) (hB0 : 0 ≤ B) (hG1 : B * W₆ ≤ G)
    (hG2 : B ≤ G)
    (hbs : BlockSumDerivBounds T.ballRadius T.κ B Y K V)
    (hal : DecaysAlongTopField (coldHalfLawAt T x f) Cq (G * x ^ (-(1 / 2) : ℝ)) Y K V) :
    IsSlot (coldHalfLawAt T x f) Cq (G * x ^ (-(1 / 2) : ℝ)) Y K V := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hs1, hs2⟩ := sqrt_mul_rpow_neg_half hx0
  set s₀ : ℝ := x ^ (-(1 / 2) : ℝ) with hs₀
  have hs₀0 : 0 ≤ s₀ := (Real.rpow_pos_of_pos hx0 _).le
  have hRead := (hD F T.ballRadius V).2 K hbs.smooth
  obtain ⟨Ψ', Kk, hΨ', hconvex, hsl, -⟩ := hconv
  have hdens : ballDensity (cutoffFactor T.ballRadius T.p) Ψ' =
      ballDensity (cutoffFactor T.ballRadius T.p) ((coldHalfLawAt T x f).exponent V) :=
    (ballDensity_congr hΨ').symm
  have hG0 : 0 ≤ G := hB0.trans hG2
  refine ⟨⟨fun η k c X hη => ?_, fun k c X hk hX => ?_⟩, fun η hη => ?_, hal⟩
  · exact_mod_cast hbs.smooth k c X η hη
  · have hk2 : k ≤ 2 := by omega
    set E : ℝ := Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) with hE
    have hE0 : 0 < E := Real.exp_pos _
    set Dd : ↥(chordBonds (finiteCells F)) → ℝ :=
      fun b => B * E * Real.exp (-(2 ^ 6 * T.κ * cellSupDist (enclosingCell b.1.1) Y)) with hDd
    have hD0 : ∀ b, 0 ≤ Dd b := fun b => by positivity
    have hbound : ∀ ξ : StepVariable (finiteCells F), (∀ b, ‖ξ b‖ ≤ T.ballRadius) →
        ∀ (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3)), ‖u‖ = 1 →
        |jointMixedDeriv K ξ V ![b] ![u] c X| ≤ Dd b :=
      fun ξ hξ b u hu => hbs.deriv_one ξ b u k c X hξ hu hk2 hX
    have hJ : ContDiffOn ℝ 1 (fieldDeriv K V c X) {η | ∀ b, ‖η b‖ < T.ballRadius} := fun η hη =>
      (hRead.contDiffAt_one c X η hk2 (norm_le_of_lt hη)).contDiffWithinAt
    have h0 : ∀ b, ‖(0 : StepVariable (finiteCells F)) b‖ ≤ T.ballRadius := fun b => by simpa using hρ.le
    have hsize := hSl (dZ := fun b => (cellSupDist (enclosingCell b.1.1) Y : ℝ)) (h := G * s₀ * E) hρ hx0 hlam hκ.le
      hW0 hcut hdist hconvex hW hsl hJ hD0
      (by positivity) (fun η hη => by
        have := hRead.abs_sub_le c X Dd 0 η hk2 hbound h0 (norm_le_of_lt hη)
        simpa using this)
      (fun η hη b => hRead.bondGradNorm_le c X η b (Dd b) hk2 (hD0 b) (norm_le_of_lt hη)
        fun u hu => hbound η (norm_le_of_lt hη) b u hu)
      (by
        have h1 : ∑ b, Dd b ≤ B * E * W₆ := by
          simp only [hDd]
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hW₆ (by positivity)
        have h2 : B * E * W₆ ≤ G * E := by
          have := mul_le_mul_of_nonneg_right hG1 hE0.le
          linarith [this]
        calc s₀ * ∑ b, Dd b ≤ s₀ * (G * E) := mul_le_mul_of_nonneg_left (h1.trans h2) hs₀0
          _ = G * s₀ * E := by ring)
      (fun b => by
        simp only [hDd]
        have e1 : Real.sqrt x * (G * s₀ * E) = G * E := by
          calc Real.sqrt x * (G * s₀ * E) = (Real.sqrt x * s₀) * (G * E) := by ring
            _ = G * E := by rw [hs1, one_mul]
        rw [e1]
        have hd0 : (0 : ℝ) ≤ cellSupDist (enclosingCell b.1.1) Y := by positivity
        have h3 : Real.exp (-(2 ^ 6 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤
            Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) := by
          rw [Real.exp_le_exp]
          have := mul_nonneg hκ.le hd0
          nlinarith
        have h4 : B * E ≤ G * E := mul_le_mul_of_nonneg_right hG2 hE0.le
        exact mul_le_mul h4 h3 (Real.exp_pos _).le (by positivity))
    have h2 := hasLocalSize_congr_density hdens hsize
    exact hasLocalSize_mono hCq (by positivity) le_rfl h2
  · exact (hRead.contDiffAt_three η (norm_le_of_lt hη)).of_le (by norm_num)
theorem abs_apply_le_of_unit {L : BondVector →L[ℝ] ℝ} {D : ℝ} (hD : 0 ≤ D) (h : ∀ u : BondVector, ‖u‖ = 1 → |L u| ≤ D)
    (v : BondVector) : |L v| ≤ D * ‖v‖ := by
  by_cases h0 : v = 0
  · subst h0
    simp
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    have hu1 : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hdec : v = ‖v‖ • (‖v‖⁻¹ • v) := by
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    conv_lhs => rw [hdec]
    rw [map_smul, smul_eq_mul, abs_mul, abs_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right (h _ hu1) (norm_nonneg _)
theorem topVariationField_congr {Th Th' : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions}
    {a ρA : ℝ} {m : ℕ} {c : F.Site F.top × Fin 4} {X u : imaginaryQuaternions}
    {b : F.Site F.depth × Fin 4} {V : F.GaugeField F.top}
    (h : Th (interpolatedFrame 1 a ρA m b V + u) X = Th' (interpolatedFrame 1 a ρA m b V + u) X) :
    topVariationField Th 1 a ρA m c X b u V = topVariationField Th' 1 a ρA m c X b u V := by
  unfold topVariationField
  rw [h]
set_option maxHeartbeats 2000000 in
theorem decaysAlongTopField_blockSum (hSz : LocalSizeOfQuadraticBounds) (hD : mixedDerivativesOnBallsStatement)
    (hAl : PartialAlongBondFieldRegular)
    {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {f : LocalFamily} {V : F.GaugeField F.top} {Y : F.Cell} {K : AboveFrames F}
    {B G W Cs CT r₁ : ℝ} {Cq : ℕ → ℝ}
    (hρ : 0 < T.ballRadius) (hx1 : 1 ≤ x) (hlam : 0 < T.chainParams.lam) (hκ : 0 < T.κ) (hcut : IsCutoff T.ballRadius T.p)
    (hdist : IsPseudoMetricOnBonds (_root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist F))
    (hconv : HasUniformlyConvexLaw T.ballRadius T.chainParams.lam x T.κ T.Ct (_root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist F)
      ((coldHalfLawAt T x f).exponent V)) (hW0 : 0 ≤ W)
    (hW : ∀ b₀ : ↥(chordBonds (finiteCells F)), ∑ b, Real.exp (-(2 * T.κ * _root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist F b b₀)) ≤ W)
    (hCq : ∀ q, |lpMomentConstant T.chainParams.lam (1 / 2) W q * 1| ≤ Cq q) (hB0 : 0 ≤ B) (hCs0 : 0 ≤ Cs)
    (hCT0 : 0 ≤ CT)
    (hG : B * (Cs + CT) ≤ G) (hbs : BlockSumDerivBounds T.ballRadius T.κ B Y K V)
    (Th₀ : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions)
    (hTs : ∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Th₀ w)
    (hTb : ∀ (w : imaginaryQuaternions), ‖w‖ ≤ 1 → ‖iteratedFDeriv ℝ 1 Th₀ w‖ ≤ CT)
    (hsame : ∀ Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions,
      (∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (Th w X)) →
      ∀ w X : imaginaryQuaternions, ‖w‖ < r₁ → Th w X = Th₀ w X)
    (hsmall : ∀ (b : ↥(chordBonds (finiteCells F))) (v : BondVector), ‖v‖ < T.ballRadius →
      ‖interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b.1 V + toImaginary v‖ < r₁ ∧
      ‖interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b.1 V + toImaginary v‖ ≤ 1)
    (hfld : ∀ (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (b : ↥(chordBonds (finiteCells F)))
      (u : imaginaryQuaternions), ‖X‖ = 1 → ‖u‖ < T.ballRadius →
      ‖topVariationField (fun w X' => Th₀ w X') 1 T.a T.chainParams.ρA (frameRadius x) c X b.1 u V‖ ≤
        Cs * Real.exp (-(2 ^ 8 * T.κ * cellSupDist (enclosingCell b.1.1) c.1))) :
    DecaysAlongTopField (coldHalfLawAt T x f) Cq (G * x ^ (-(1 / 2) : ℝ)) Y K V := by
  classical
  intro Th hTh c X b hX
  have hx0 : 0 < x := by linarith
  obtain ⟨hs1, hs2⟩ := sqrt_mul_rpow_neg_half hx0
  set s₀ : ℝ := x ^ (-(1 / 2) : ℝ) with hs₀
  have hRead := (hD F T.ballRadius V).2 K hbs.smooth
  obtain ⟨Ψ', Kk, hΨ', hconvex, hsl, -⟩ := hconv
  have hdens : ballDensity (cutoffFactor T.ballRadius T.p) Ψ' =
      ballDensity (cutoffFactor T.ballRadius T.p) ((coldHalfLawAt T x f).exponent V) :=
    (ballDensity_congr hΨ').symm
  have hG0 : 0 ≤ G := le_trans (by positivity) hG
  set a := T.a with ha
  set ρA := T.chainParams.ρA with hρA
  set m := frameRadius x with hm
  set A : StepVariable (finiteCells F) → ℝ := fun ζ => K ζ V with hA
  set d : ↥(chordBonds (finiteCells F)) → ℝ := fun b' => (cellSupDist (enclosingCell b'.1.1) Y : ℝ) with hd
  have hd0 : ∀ b', 0 ≤ d b' := fun b' => by positivity
  set dc : ℝ := (cellSupDist (enclosingCell b.1.1) c.1 : ℝ) with hdc
  have hdc0 : 0 ≤ dc := by positivity
  set z : BondVector → BondVector :=
    fun v => _root_.YangMills.Construction.Interpolation.imaginaryCoords (topVariationField (fun w X' => Th₀ w X') 1 a ρA m c X b.1 (toImaginary v) V) with hz
  set cond : Prop := IsCrossingBond b.1 ∧ (enclosingCell b.1.1, b.1.2) = c with hcond
  set Mz : ℝ := Cs * Real.exp (-(2 ^ 8 * T.κ * dc)) with hMz
  set Mz' : ℝ := if cond then CT else 0 with hMz'
  set B₁ : ℝ := B * Real.exp (-(2 ^ 6 * T.κ * d b)) with hB₁
  set B₂ : ↥(chordBonds (finiteCells F)) → ℝ :=
    fun b' => B * Real.exp (-(2 ^ 6 * T.κ * d b')) * Real.exp (-(2 ^ 6 * T.κ * d b)) with hB₂
  have hMz0 : 0 ≤ Mz := by positivity
  have hMz'0 : 0 ≤ Mz' := by
    simp only [hMz']
    split_ifs
    · exact hCT0
    · exact le_rfl
  have hB₁0 : 0 ≤ B₁ := by positivity
  have hB₂0 : ∀ b', 0 ≤ B₂ b' := fun b' => by positivity
  have hfA : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ < T.ballRadius) → ContDiffAt ℝ 3 A ζ := fun ζ hζ =>
    hRead.contDiffAt_three ζ (norm_le_of_lt hζ)
  have hval := hRead.fieldDeriv_zero (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
    (Fin.elim0 : Fin 0 → imaginaryQuaternions) rfl
  have hzprop : ∀ v : BondVector, ‖v‖ < T.ballRadius → ContDiffAt ℝ 1 z v ∧ ‖fderiv ℝ z v‖ ≤ Mz' := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hsmall b v hv
    by_cases hc : cond
    · have e : z = fun v' => _root_.YangMills.Construction.Interpolation.imaginaryCoords (bondDeriv (interpolatedFrame 1 a ρA m b.1) V (fun _ : Fin 1 => c) (fun _ => X) +
          Th₀ (interpolatedFrame 1 a ρA m b.1 V + toImaginary v') X) := by
        funext v'
        simp only [hz, topVariationField,
          if_pos (show IsCrossingBond b.1 ∧ (enclosingCell b.1.1, b.1.2) = c from hc)]
      have hb := translatedField_contDiffAt_and_fderiv_le (Th := Th₀) (C := CT)
        (D := bondDeriv (interpolatedFrame 1 a ρA m b.1) V (fun _ : Fin 1 => c) (fun _ => X))
        hCT0 hX hv2 (hTs _ hv2) (hTb _ hv2)
      rw [e]
      refine ⟨hb.1, hb.2.trans ?_⟩
      simp only [hMz', if_pos hc]
      exact le_rfl
    · have e : z = fun _ => _root_.YangMills.Construction.Interpolation.imaginaryCoords (bondDeriv (interpolatedFrame 1 a ρA m b.1) V (fun _ : Fin 1 => c)
          (fun _ => X) + 0) := by
        funext v'
        simp only [hz, topVariationField,
          if_neg (show ¬ (IsCrossingBond b.1 ∧ (enclosingCell b.1.1, b.1.2) = c) from hc)]
      rw [e]
      refine ⟨contDiffAt_const, ?_⟩
      rw [fderiv_fun_const]
      simpa using hMz'0
  have hzM : ∀ v : BondVector, ‖v‖ < T.ballRadius → ‖z v‖ ≤ Mz := fun v hv => by
    simp only [hz]
    rw [norm_imaginaryCoords]
    exact hfld c X b (toImaginary v) hX (by rwa [norm_toImaginary])
  have hFirst : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ < T.ballRadius) →
      ∀ (b' : ↥(chordBonds (finiteCells F))) (u : BondVector),
      |fderiv ℝ A ζ (Pi.single b' u)| ≤ B * Real.exp (-(2 ^ 6 * T.κ * d b')) * ‖u‖ := by
    intro ζ hζ b' u
    have hnn : 0 ≤ B * Real.exp (-(2 ^ 6 * T.κ * d b')) := by positivity
    refine abs_apply_le_of_unit (L := (fderiv ℝ A ζ).comp
      (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b')) hnn (fun u hu => ?_) u
    have e := hRead.fderiv_eq (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)
      ζ b' u (Nat.zero_le _) (norm_le_of_lt hζ)
    rw [hval] at e
    show |fderiv ℝ A ζ (Pi.single b' u)| ≤ _
    have e' : fderiv ℝ A ζ (Pi.single b' u) = _ := e
    rw [e']
    refine (hbs.deriv_one ζ b' u 0 Fin.elim0 Fin.elim0 (norm_le_of_lt hζ) hu (Nat.zero_le _)
      (fun i => i.elim0)).trans ?_
    have hE : Real.exp (-(2 ^ 5 * T.κ * (bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) := by positivity
      have := mul_nonneg hκ.le this
      nlinarith
    have hE2 := Real.exp_pos (-(2 ^ 6 * T.κ * d b'))
    calc _ ≤ B * 1 * Real.exp (-(2 ^ 6 * T.κ * d b')) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hB0) hE2.le
      _ = _ := by ring
  have hSecond : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ < T.ballRadius) →
      ∀ (b' : ↥(chordBonds (finiteCells F))) (u u' : BondVector),
      |fderiv ℝ (fderiv ℝ A) ζ (Pi.single b' u) (Pi.single b u')| ≤ B₂ b' * ‖u‖ * ‖u'‖ := by
    intro ζ hζ b' u u'
    have hunit : ∀ v v' : BondVector, ‖v‖ = 1 → ‖v'‖ = 1 →
        |fderiv ℝ (fderiv ℝ A) ζ (Pi.single b' v) (Pi.single b v')| ≤ B₂ b' := by
      intro v v' hv hv'
      have e := hRead.fderiv_fderiv_eq ζ b' b v v' (norm_le_of_lt hζ)
      have e' : fderiv ℝ (fderiv ℝ A) ζ (Pi.single b' v) (Pi.single b v') = _ := e
      rw [e']
      exact hbs.deriv_two ζ b' b v v' (norm_le_of_lt hζ) hv hv'
    have h1 : ∀ v : BondVector, ‖v‖ = 1 →
        |fderiv ℝ (fderiv ℝ A) ζ (Pi.single b' v) (Pi.single b u')| ≤ B₂ b' * ‖u'‖ := fun v hv =>
      abs_apply_le_of_unit (L := (fderiv ℝ (fderiv ℝ A) ζ (Pi.single b' v)).comp
        (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b))
        (hB₂0 b') (fun v' hv' => hunit v v' hv hv') u'
    have h2 := abs_apply_le_of_unit (L := (((fderiv ℝ (fderiv ℝ A) ζ).comp
      (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b')).flip
      (Pi.single b u'))) (by have := hB₂0 b'; positivity) h1 u
    refine h2.trans (le_of_eq ?_)
    ring
  obtain ⟨hH1, hH2, hH3⟩ := hAl (ρ := T.ballRadius) (A := A) (b := b) (z := z) (B₁ := B₁) (Mz := Mz) (Mz' := Mz')
    (B₂ := B₂) hfA (fun v hv => (hzprop v hv).1) hzM (fun v hv => (hzprop v hv).2) hB₁0 hB₂0 hMz0 hMz'0
    (fun ζ hζ u => hFirst ζ hζ b u) hSecond
  set E₁ : ℝ := Real.exp (-(2 ^ 4 * T.κ * d b) - 2 ^ 6 * T.κ * dc) with hE₁
  have hE₁0 : 0 < E₁ := Real.exp_pos _
  have hκd : ∀ b', 0 ≤ T.κ * d b' := fun b' => mul_nonneg hκ.le (hd0 b')
  have hκc : 0 ≤ T.κ * dc := mul_nonneg hκ.le hdc0
  have hGB : B * Cs ≤ G := le_trans (by nlinarith) hG
  have hGC : B * (Cs + CT) ≤ G := hG
  have hsq1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx1
  have hval2 : IsQuadraticallyBoundedOnBalls T.ballRadius x (1 / 2) 1 (G * E₁)
      (fun η => bondPartialDeriv A b η (z (η b))) := by
    refine ⟨fun _ => 0, G * E₁, by positivity, le_rfl, fun _ => le_rfl, ?_, fun η hη => ?_⟩
    · simp only [Finset.sum_const_zero]
      positivity
    · simp only [zero_mul, Finset.sum_const_zero, mul_zero, zero_add, one_mul]
      refine (hH2 η hη).trans ?_
      have h1 : Real.exp (-(2 ^ 6 * T.κ * d b)) * Real.exp (-(2 ^ 8 * T.κ * dc)) ≤ E₁ := by
        rw [← Real.exp_add, hE₁, Real.exp_le_exp]
        nlinarith [hκd b]
      calc B₁ * Mz = (B * Cs) * (Real.exp (-(2 ^ 6 * T.κ * d b)) * Real.exp (-(2 ^ 8 * T.κ * dc))) := by
            simp only [hB₁, hMz]
            ring
        _ ≤ G * E₁ := mul_le_mul hGB h1 (by positivity) hG0
  have hgr2 : ∀ b' : ↥(chordBonds (finiteCells F)), IsQuadraticallyBoundedOnBalls T.ballRadius x (1 / 2)
      (Real.sqrt x * 1) (G * E₁ * Real.exp (-(2 * T.κ * d b')))
      (bondGradNorm (fun η => bondPartialDeriv A b η (z (η b))) b') := by
    intro b'
    have he' := Real.exp_pos (-(2 * T.κ * d b'))
    refine ⟨fun _ => 0, G * E₁ * Real.exp (-(2 * T.κ * d b')), by positivity, le_rfl, fun _ => le_rfl, ?_,
      fun η hη => ?_⟩
    · simp only [Finset.sum_const_zero]
      positivity
    · simp only [zero_mul, Finset.sum_const_zero, mul_zero, zero_add, mul_one]
      have hnn : 0 ≤ bondGradNorm (fun η => bondPartialDeriv A b η (z (η b))) b' η := norm_nonneg _
      rw [abs_of_nonneg hnn]
      refine (hH3 η hη b').trans ?_
      have t1 : B₂ b' * Mz ≤ (B * Cs) * (E₁ * Real.exp (-(2 * T.κ * d b'))) := by
        have h1 : Real.exp (-(2 ^ 6 * T.κ * d b')) * Real.exp (-(2 ^ 6 * T.κ * d b)) *
            Real.exp (-(2 ^ 8 * T.κ * dc)) ≤ E₁ * Real.exp (-(2 * T.κ * d b')) := by
          rw [← Real.exp_add, ← Real.exp_add, hE₁, ← Real.exp_add, Real.exp_le_exp]
          nlinarith [hκd b, hκd b']
        calc B₂ b' * Mz = (B * Cs) * (Real.exp (-(2 ^ 6 * T.κ * d b')) * Real.exp (-(2 ^ 6 * T.κ * d b)) *
              Real.exp (-(2 ^ 8 * T.κ * dc))) := by
              simp only [hB₂, hMz]
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
      have t2 : (if b' = b then B₁ * Mz' else 0) ≤ (B * CT) * (E₁ * Real.exp (-(2 * T.κ * d b'))) := by
        by_cases hb : b' = b
        · subst hb
          rw [if_pos rfl]
          by_cases hc : cond
          · have hdc' : dc = 0 := by
              have h1 : c = (enclosingCell b'.1.1, b'.1.2) := hc.2.symm
              simp only [hdc]
              rw [h1]
              simp [cellSupDist]
            have h2 : Real.exp (-(2 ^ 6 * T.κ * d b')) ≤ E₁ * Real.exp (-(2 * T.κ * d b')) := by
              rw [hE₁, hdc', ← Real.exp_add, Real.exp_le_exp]
              nlinarith [hκd b']
            calc B₁ * Mz' = (B * CT) * Real.exp (-(2 ^ 6 * T.κ * d b')) := by
                  simp only [hB₁, hMz', if_pos hc]
                  ring
              _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
          · have : Mz' = 0 := by
              simp only [hMz', if_neg hc]
            rw [this, mul_zero]
            positivity
        · rw [if_neg hb]
          positivity
      have t3 : (B * Cs) * (E₁ * Real.exp (-(2 * T.κ * d b'))) + (B * CT) * (E₁ * Real.exp (-(2 * T.κ * d b'))) ≤
          G * E₁ * Real.exp (-(2 * T.κ * d b')) := by
        have e1 : (B * Cs) * (E₁ * Real.exp (-(2 * T.κ * d b'))) + (B * CT) * (E₁ * Real.exp (-(2 * T.κ * d b'))) =
            (B * (Cs + CT)) * (E₁ * Real.exp (-(2 * T.κ * d b'))) := by ring
        have e2 : G * E₁ * Real.exp (-(2 * T.κ * d b')) = G * (E₁ * Real.exp (-(2 * T.κ * d b'))) := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_right hGC (by positivity)
      have t4 : G * E₁ * Real.exp (-(2 * T.κ * d b')) ≤ Real.sqrt x * (G * E₁ * Real.exp (-(2 * T.κ * d b'))) :=
        le_mul_of_one_le_left (by positivity) hsq1
      linarith
  have hsz := hSz _ T.ballRadius x T.chainParams.lam T.κ W (1 / 2) (_root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist F) Ψ' Kk T.p hρ hx0 hlam hκ.le
    hW0 (by norm_num) hcut hdist hconvex hW hsl
    (fun η => bondPartialDeriv A b η (z (η b))) 1 (G * E₁) d zero_le_one (by positivity) hH1 hval2 hgr2
  have hs2' := hasLocalSize_congr_density hdens hsz
  have hcong : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
      bondPartialDeriv A b η (z (η b)) = topFieldPartial Th 1 a ρA m c X V b A η := by
    intro η hη
    have hv : ‖η b‖ < T.ballRadius := hη b
    have h1 := (hsmall b (η b) hv).1
    have h2 := hsame Th hTh _ X h1
    simp only [topFieldPartial, hz]
    rw [topVariationField_congr (Th := fun w X' => Th₀ w X') (Th' := Th) (c := c) h2.symm]
  have hs3 := hasLocalSize_congr_of_eqOn_balls (isOpen_ballSet T.ballRadius) (fun η hη => by
    unfold ballDensity
    rw [radialWeightProd_eq_zero_of_not_mem hη, zero_mul]) hcong hs2'
  have e4 : Real.sqrt x * (G * s₀) *
      Real.exp (-(2 ^ 4 * T.κ * bondDistToCell Y b) - 2 ^ 6 * T.κ * bondDistToTopBond b c) = G * E₁ := by
    have : Real.sqrt x * (G * s₀) = G := by
      calc Real.sqrt x * (G * s₀) = (Real.sqrt x * s₀) * G := by ring
        _ = G := by rw [hs1, one_mul]
    rw [this]
    rfl
  have hs4 := hasLocalSize_mono hCq (by positivity) (le_of_eq e4.symm) hs3
  exact hs4
theorem blockSum_pointwise (hD : mixedDerivativesOnBallsStatement) {ρ κ B : ℝ} {Y : F.Cell} {K : AboveFrames F}
    {V : F.GaugeField F.top} (hρ : 0 < ρ) (hκ : 0 < κ) (hB0 : 0 ≤ B) (hbs : BlockSumDerivBounds ρ κ B Y K V) :
    ContDiffOn ℝ 1 (fun η => K η V) {η | ∀ b, ‖η b‖ < ρ} ∧
    (∀ η ζ : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) → (∀ b, ‖ζ b‖ ≤ ρ) →
      |K ζ V - K η V| ≤ ∑ b, ‖ζ b - η b‖ * (B * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)))) ∧
    ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → ∀ b,
      bondGradNorm (fun ζ => K ζ V) b η ≤ B * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) := by
  have hRead := (hD F ρ V).2 K hbs.smooth
  have hval := hRead.fieldDeriv_zero (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
    (Fin.elim0 : Fin 0 → imaginaryQuaternions) rfl
  have hbound : ∀ ξ : StepVariable (finiteCells F), (∀ b, ‖ξ b‖ ≤ ρ) → ∀ (b : ↥(chordBonds (finiteCells F)))
      (u : EuclideanSpace ℝ (Fin 3)), ‖u‖ = 1 → |jointMixedDeriv K ξ V ![b] ![u]
        (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)| ≤
        B * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) := by
    intro ξ hξ b u hu
    refine (hbs.deriv_one ξ b u 0 Fin.elim0 Fin.elim0 hξ hu (Nat.zero_le _) (fun i => i.elim0)).trans ?_
    have hE : Real.exp (-(2 ^ 5 * κ * (bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) := by positivity
      have := mul_nonneg hκ.le this
      nlinarith
    have hE2 := Real.exp_pos (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y))
    calc _ ≤ B * 1 * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hB0) hE2.le
      _ = _ := by ring
  refine ⟨fun η hη => ((hRead.contDiffAt_three η (norm_le_of_lt hη)).of_le (by norm_num)).contDiffWithinAt,
    fun η ζ hη hζ => ?_, fun η hη b => ?_⟩
  · have h1 := hRead.abs_sub_le (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)
      (fun b => B * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y))) η ζ (Nat.zero_le _) hbound hη hζ
    rw [hval] at h1
    exact h1
  · have h1 := hRead.bondGradNorm_le (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
      (Fin.elim0 : Fin 0 → imaginaryQuaternions) η b _ (Nat.zero_le _)
      (by positivity) (norm_le_of_lt hη) (hbound η (norm_le_of_lt hη) b)
    rw [hval] at h1
    exact h1
theorem comparisonBoundsOnTorus_blockSum (hLaw : normalizedBallLawIsProbabilityStatement)
    (hD : mixedDerivativesOnBallsStatement)
    {ρ lam x κ B α W₅ : ℝ} {p : ℝ → ℝ} {q : ℕ} {Y : F.Cell} {K : AboveFrames F} {V : F.GaugeField F.top}
    {Ψ Ψ' : StepVariable (finiteCells F) → ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hcut : IsCutoff ρ p) (hB0 : 0 ≤ B) (hx : 1 ≤ x) (hc : Continuous Ψ')
    (he : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → Ψ' η = Ψ η) (hBα : B ≤ α) (hBα₂ : ρ * B * W₅ ≤ α)
    (hW₅ : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 5 * κ * cellSupDist (enclosingCell b.1.1) Y)) ≤ W₅)
    (hbs : BlockSumDerivBounds ρ κ B Y K V) : ComparisonHypothesesOnTorus ρ lam x κ α p q Y Ψ (fun η => K η V) := by
  classical
  obtain ⟨hA, hmove, hgrad⟩ := blockSum_pointwise hD hρ hκ hB0 hbs
  set Dd : ↥(chordBonds (finiteCells F)) → ℝ :=
    fun b => B * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) with hDd
  have hD0 : ∀ b, 0 ≤ Dd b := fun b => by positivity
  have hα : 0 ≤ α := hB0.trans hBα
  have h0 : ∀ b, ‖(0 : StepVariable (finiteCells F)) b‖ ≤ ρ := fun b => by simpa using hρ.le
  have hM : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → |K η V| ≤ |K 0 V| + ρ * ∑ b, Dd b := fun η hη => by
    have h1 := hmove 0 η h0 (norm_le_of_lt hη)
    have h2 : ∑ b, ‖η b - (0 : StepVariable (finiteCells F)) b‖ * Dd b ≤ ρ * ∑ b, Dd b := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right ?_ (hD0 b)
      simpa using (hη b).le
    have h3 : |K η V| ≤ |K η V - K 0 V| + |K 0 V| := by
      have := abs_add_le (K η V - K 0 V) (K 0 V)
      simpa using this
    linarith [h1.trans h2]
  have hDb : ∀ b, Dd b ≤ Real.sqrt x * α * Real.exp (-(2 * κ * bondDistToCell Y b)) := fun b => by
    have hd0 : (0 : ℝ) ≤ cellSupDist (enclosingCell b.1.1) Y := by positivity
    have h3 : Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤
        Real.exp (-(2 * κ * bondDistToCell Y b)) := by
      rw [Real.exp_le_exp]
      show -(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ)) ≤ -(2 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))
      have := mul_nonneg hκ.le hd0
      nlinarith
    have hsq1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
    have h4 : B ≤ Real.sqrt x * α := hBα.trans (le_mul_of_one_le_left hα hsq1)
    exact mul_le_mul h4 h3 (Real.exp_pos _).le (by positivity)
  have hfr : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      |K η V - K (freezeOutside (bondsNearCell Y q) η) V| ≤ α * Real.exp (-(4 * κ * q)) := by
    intro η hη
    set ηf := freezeOutside (bondsNearCell Y q) η with hηf
    have hin : ∀ b, ‖ηf b‖ < ρ := extendByZero_mem_ball Function.injective_id _ hρ hη
    have h1 := hmove ηf η (norm_le_of_lt hin) (norm_le_of_lt hη)
    have hterm : ∀ b : ↥(chordBonds (finiteCells F)), ‖η b - ηf b‖ * Dd b ≤
        ρ * B * Real.exp (-(4 * κ * q)) * Real.exp (-(2 ^ 5 * κ * cellSupDist (enclosingCell b.1.1) Y)) := by
      intro b
      by_cases hb : b ∈ bondsNearCell Y q
      · have e : ηf b = η b := by
          simp only [hηf, freezeOutside, _root_.YangMills.Construction.Interpolation.extendByZero, id]
          rw [Finset.sum_eq_single_of_mem b hb (fun i _ hne => by simp [hne])]
          simp
        rw [e, sub_self, norm_zero, zero_mul]
        positivity
      · have e : ηf b = 0 := by
          simp only [hηf, freezeOutside, _root_.YangMills.Construction.Interpolation.extendByZero, id]
          refine Finset.sum_eq_zero fun i hi => ?_
          rw [if_neg]
          exact fun h2 => hb (h2 ▸ hi)
        rw [e, sub_zero]
        have hd : (q : ℝ) < 2 * cellSupDist (enclosingCell b.1.1) Y := by
          have : ¬ 2 * cellSupDist (enclosingCell b.1.1) Y ≤ q := fun h2 =>
            hb (Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩)
          have h3 : q < 2 * cellSupDist (enclosingCell b.1.1) Y := by omega
          exact_mod_cast h3
        have hE : Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) ≤
            Real.exp (-(4 * κ * q)) * Real.exp (-(2 ^ 5 * κ * cellSupDist (enclosingCell b.1.1) Y)) := by
          rw [← Real.exp_add, Real.exp_le_exp]
          have := mul_nonneg hκ.le (sub_nonneg.2 hd.le)
          have h2 : (0 : ℝ) ≤ q := by positivity
          have := mul_nonneg hκ.le h2
          nlinarith
        simp only [hDd]
        calc ‖η b‖ * (B * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y))) ≤
            ρ * (B * (Real.exp (-(4 * κ * q)) * Real.exp (-(2 ^ 5 * κ * cellSupDist (enclosingCell b.1.1) Y)))) :=
              mul_le_mul (hη b).le (mul_le_mul_of_nonneg_left hE hB0) (by positivity) hρ.le
          _ = _ := by ring
    have hE4 := Real.exp_pos (-(4 * κ * q))
    have h2 : ∑ b, ‖η b - ηf b‖ * Dd b ≤ ρ * B * Real.exp (-(4 * κ * q)) * W₅ := by
      refine (Finset.sum_le_sum fun b _ => hterm b).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hW₅ (by positivity)
    have h3 : ρ * B * Real.exp (-(4 * κ * q)) * W₅ ≤ α * Real.exp (-(4 * κ * q)) := by
      have e2 : ρ * B * Real.exp (-(4 * κ * q)) * W₅ = (ρ * B * W₅) * Real.exp (-(4 * κ * q)) := by ring
      rw [e2]
      exact mul_le_mul_of_nonneg_right hBα₂ hE4.le
    have h4 : |K η V - K ηf V| = |K η V - K ηf V| := rfl
    exact h1.trans (h2.trans h3)
  exact comparisonBoundsOnTorus_of_pointwise hLaw hρ hcut hc he hα hA hM hgrad hD0 hDb hfr
theorem hasGradientBound_blockSum_toTorus (hLaw : normalizedBallLawIsProbabilityStatement)
    (hD : mixedDerivativesOnBallsStatement)
    {ι : Type} [Fintype ι] [DecidableEq ι] {ρ x κ B α : ℝ} {p : ℝ → ℝ} {Y : F.Cell} {K : AboveFrames F}
    {V : F.GaugeField F.top}
    {Φ : BondField ι → ℝ} {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j)
    (hρ : 0 < ρ) (hκ : 0 < κ) (hB0 : 0 ≤ B) (hx : 1 ≤ x) (hBα : B ≤ α) (hL : IsBallLaw ρ p Φ)
    (hbs : BlockSumDerivBounds ρ κ B Y K V) :
    HasGradientBound ρ (cutoffFactor ρ p) Φ x κ α (fun i => bondDistToCell Y (j i)) (fun ζ => K (toTorus j ζ) V) := by
  classical
  obtain ⟨hA, hmove, hgrad⟩ := blockSum_pointwise hD hρ hκ hB0 hbs
  have hα : 0 ≤ α := hB0.trans hBα
  set Dd : ↥(chordBonds (finiteCells F)) → ℝ :=
    fun b => B * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) with hDd
  have h0 : ∀ b, ‖(0 : StepVariable (finiteCells F)) b‖ ≤ ρ := fun b => by simpa using hρ.le
  have hin : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → ∀ b, ‖toTorus j ζ b‖ < ρ := fun ζ hζ =>
    extendByZero_mem_ball hj Finset.univ hρ hζ
  have hH : ContDiffOn ℝ 1 (fun ζ => K (toTorus j ζ) V) {ζ : BondField ι | ∀ i, ‖ζ i‖ < ρ} := by
    have hm : Set.MapsTo (extendByZeroCLM j Finset.univ) {ζ : BondField ι | ∀ i, ‖ζ i‖ < ρ}
        {η | ∀ b, ‖η b‖ < ρ} := fun ζ hζ b => by
      rw [extendByZeroCLM_apply]
      exact hin ζ hζ b
    have := hA.comp (extendByZeroCLM j Finset.univ).contDiff.contDiffOn hm
    refine this.congr fun ζ _ => ?_
    simp only [Function.comp, extendByZeroCLM_apply]
    rfl
  have hM : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → |K (toTorus j ζ) V| ≤ |K 0 V| + ρ * ∑ b, Dd b := fun ζ hζ => by
    have h1 := hmove 0 (toTorus j ζ) h0 fun b => (hin ζ hζ b).le
    have h2 : ∑ b, ‖toTorus j ζ b - (0 : StepVariable (finiteCells F)) b‖ * Dd b ≤ ρ * ∑ b, Dd b := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
      simpa using (hin ζ hζ b).le
    have h3 : |K (toTorus j ζ) V| ≤ |K (toTorus j ζ) V - K 0 V| + |K 0 V| := by
      have := abs_add_le (K (toTorus j ζ) V - K 0 V) (K 0 V)
      simpa using this
    linarith [h1.trans h2]
  refine hasGradientBound_of_pointwise hL hH hM (g := fun i => Dd (j i)) (fun ζ hζ i => ?_) (fun i => ?_)
    (fun i => by positivity)
  · have hi := hin ζ hζ
    have hdiff : DifferentiableAt ℝ (fun η => K η V) (_root_.YangMills.Construction.Interpolation.extendByZero j Finset.univ ζ) :=
      (hA.contDiffAt ((isOpen_ballSet ρ).mem_nhds hi)).differentiableAt (by simp)
    exact bondGradNorm_comp_extendByZero_le hj Finset.univ hdiff i (by positivity) fun _ => hgrad _ hi (j i)
  · have hd0 : (0 : ℝ) ≤ cellSupDist (enclosingCell (j i).1.1) Y := by positivity
    have h3 : Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell (j i).1.1) Y : ℝ))) ≤
        Real.exp (-(2 * κ * bondDistToCell Y (j i))) := by
      rw [Real.exp_le_exp]
      show -(2 ^ 6 * κ * (cellSupDist (enclosingCell (j i).1.1) Y : ℝ)) ≤
        -(2 * κ * (cellSupDist (enclosingCell (j i).1.1) Y : ℝ))
      have := mul_nonneg hκ.le hd0
      nlinarith
    have hsq1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
    have h4 : B ≤ Real.sqrt x * α := hBα.trans (le_mul_of_one_le_left hα hsq1)
    exact mul_le_mul h4 h3 (Real.exp_pos _).le (by positivity)
theorem comparisonBounds_blockSum (hLaw : normalizedBallLawIsProbabilityStatement)
    (hD : mixedDerivativesOnBallsStatement)
    {ι : Type} [Fintype ι] [DecidableEq ι] {ρ lam x κ B α W₅ M₀ : ℝ} {p : ℝ → ℝ} {r₂ q : ℕ} {Y : F.Cell}
    {K : AboveFrames F}
    {V V' : F.GaugeField F.top} {Ψ₁ Ψ₂ Ψ₁' Ψ₂' : StepVariable (finiteCells F) → ℝ}
    {j j' : ι → ↥(chordBonds (finiteCells F))}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hcut : IsCutoff ρ p) (hB0 : 0 ≤ B) (hx : 1 ≤ x)
    (hc₁ : Continuous Ψ₁') (he₁ : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → Ψ₁' η = Ψ₁ η)
    (hc₂ : Continuous Ψ₂') (he₂ : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → Ψ₂' η = Ψ₂ η)
    (hBα : B ≤ α) (hBα₂ : ρ * B * W₅ ≤ α)
    (hW₅ : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 5 * κ * cellSupDist (enclosingCell b.1.1) Y)) ≤ W₅)
    (hbs : BlockSumDerivBounds ρ κ B Y K V) (hbs' : BlockSumDerivBounds ρ κ B Y K V')
    (hpair : IsShortPairing Y Y q j j')
    (hM₀0 : 0 ≤ M₀) (hM₀ : 2 * M₀ ≤ α)
    (hcl : ∀ ζ ζ' : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ < ρ) → (∀ b, ‖ζ' b‖ < ρ) → |K ζ V - K ζ' V'| ≤ M₀)
    (hcl' : ∀ ζ ζ' : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ < ρ) → (∀ b, ‖ζ' b‖ < ρ) → |K ζ V' - K ζ' V'| ≤ M₀)
    (hnr : r₂ ≤ q → ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      |K η V - K η V'| ≤ α * Real.exp (-(4 * κ * q))) :
    ComparisonHypotheses ρ lam x κ α p r₂ q Y Y j j' Ψ₁ (fun η => K η V) Ψ₂ (fun η => K η V') := by
  have hjj : j' = j := by
    funext i
    obtain ⟨h, o, k, -, -, h1, h2⟩ := hpair.short_offsets i
    exact Subtype.ext (h2.trans h1.symm)
  subst hjj
  have hinj := hpair.isBoxPairing.injective_left
  have hα : 0 ≤ α := hB0.trans hBα
  have hA := (blockSum_pointwise hD hρ hκ hB0 hbs).1
  have hA' := (blockSum_pointwise hD hρ hκ hB0 hbs').1
  have hL₁ := isBallLaw_of_continuous (p := p) hLaw hρ hcut hc₁ he₁
  have hL₂ := isBallLaw_of_continuous (p := p) hLaw hρ hcut hc₂ he₂
  have h0 : ∀ b, ‖(0 : StepVariable (finiteCells F)) b‖ < ρ := fun b => by simpa using hρ
  refine ⟨comparisonBoundsOnTorus_blockSum hLaw hD hρ hκ hcut hB0 hx hc₁ he₁ hBα hBα₂ hW₅ hbs,
    comparisonBoundsOnTorus_blockSum hLaw hD hρ hκ hcut hB0 hx hc₂ he₂ hBα hBα₂ hW₅ hbs', ?_,
    fun th _ _ => ?_, fun hq th _ _ => ?_⟩
  · have m1 := abs_ballExpectation_sub_le hL₁ (c := K 0 V') hM₀0 hA.continuousOn fun ζ hζ => hcl ζ 0 hζ h0
    have m2 := abs_ballExpectation_sub_le hL₂ (c := K 0 V') hM₀0 hA'.continuousOn fun ζ hζ => hcl' ζ 0 hζ h0
    have a1 := abs_le.1 m1
    have a2 := abs_le.1 m2
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  · have hL := isBallLaw_pairingHomotopy (p := p) hLaw hρ hcut hinj hinj hc₁ he₁ hc₂ he₂ th
    exact ⟨hasGradientBound_blockSum_toTorus hLaw hD hinj hρ hκ hB0 hx hBα hL hbs,
      hasGradientBound_blockSum_toTorus hLaw hD hinj hρ hκ hB0 hx hBα hL hbs'⟩
  · have hL := isBallLaw_pairingHomotopy (p := p) hLaw hρ hcut hinj hinj hc₁ he₁ hc₂ he₂ th
    exact abs_ballExpectation_le hL (by positivity) fun ζ hζ =>
      hnr hq _ (extendByZero_mem_ball hinj Finset.univ hρ hζ)
theorem sum_chordBonds_le_sum_fineBonds (g : F.Site F.depth × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b) :
    ∑ b : ↥(chordBonds (finiteCells F)), g b.1 ≤ ∑ b ∈ fineBonds F, g b := by apply _root_.YangMills.Construction.ResponseInTheExpansion.TwoFieldsLemmas.sum_chordBonds_le_sum_fineBonds <;> assumption
theorem card_sitesOfBlock_le (hFew : SitesPerCellLePow) (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (Y : F.Cell) : ((sitesOfBlock Y).card : ℝ) ≤ (F.blockSide : ℝ) ^ 4 := by
  classical
  have h1 := hFew F (finiteCells F) hodd hs Y
  have e : sitesOfBlock Y = (Finset.univ.filter fun y : ↥(sitesOfCells (finiteCells F) F.depth) =>
      enclosingCell y.1 = Y).image Subtype.val := by
    ext y
    simp only [sitesOfBlock, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y, h1⟩, h2, rfl⟩
    · rintro ⟨z, h2, rfl⟩
      exact ⟨z.2, h2⟩
  have h2 : (sitesOfBlock Y).card ≤ (Finset.univ.filter fun y : ↥(sitesOfCells (finiteCells F) F.depth) =>
      enclosingCell y.1 = Y).card := by
    rw [e]
    exact Finset.card_image_le
  exact_mod_cast h2.trans h1
theorem bondDeriv_zero_top {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : F.GaugeField F.top → E)
    (V : F.GaugeField F.top) (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G V c X = G V := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.bondDeriv_zero <;> assumption
theorem bondDeriv_zero_fine {j : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) : bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
theorem one_le_torusDecayFactor_zero (L : ℕ) (δ : ℝ) : 1 ≤ torusDecayFactor L δ ((0 : ℕ) : ℝ) := by
  unfold torusDecayFactor
  simp
theorem abs_remainder_sub_le {L : ℕ} {σ δ e e₃ : ℝ} {r : F.Site F.depth → F.GaugeField F.depth → ℝ}
    (hr : IsTorusRemainder L σ δ e e₃ r) (he : 0 ≤ e)
    (hper : ∀ i, 2 < F.period F.depth i) (y : F.Site F.depth) {W W' : F.GaugeField F.depth}
    (hW : IsSmallCurvature σ W) (hW' : IsSmallCurvature σ W') :
    |r y W - r y W'| ≤ e := by
  have hag : AgreeOnBox W W' y y 0 := by
    refine ⟨fun i => by simpa using hper i, fun i => by simpa using hper i, fun b hb => ?_⟩
    exfalso
    have h1 := hb.1 b.2
    have h2 := hb.2 b.2
    have h3 : |b.1 b.2| ≤ 0 := by simpa using h1
    have h4 : b.1 b.2 = 0 := abs_nonpos_iff.1 h3
    have h5 : |b.1 b.2 + 1| ≤ 0 := by simpa using h2
    simp [h4] at h5
  have h1 := hr.agreement y W W' 0 0 Fin.elim0 Fin.elim0 hW hW' hag (Nat.zero_le _) (fun l => l.elim0)
    (fun l => l.elim0)
  rw [bondDeriv_zero_fine, bondDeriv_zero_fine] at h1
  simp only [remainderHat, sub_sub_sub_cancel_right] at h1
  refine h1.trans ?_
  have hw := one_le_torusDecayFactor_zero L δ
  exact div_le_self he hw
end Block
structure ParameterLowerBounds (r₁ : ℝ) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop where
  L_ge : 3 ≤ T.L
  Ct_ge : 1 ≤ T.Ct
  small : (T.Ct + 1) * T.σ < min r₁ 1
  Cs_nonneg : 0 ≤ T.Cs
  n₀_ge : 64 ≤ T.n₀
  coupling_ge : 1 ≤ T.coupling
theorem eventuallyInParameters_lowerBounds {r₁ : ℝ} (h : 0 < r₁) : EventuallyInParameters (ParameterLowerBounds r₁) := by
  intro a ha
  have hm : 0 < min r₁ 1 := lt_min h one_pos
  refine ⟨3, fun L hodd hL c hc => ⟨1, fun Ct hCt => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun nss _ => ?_⟩⟩⟩⟩⟩
  have hCt0 : 0 < Ct + 1 := by linarith
  refine ⟨min r₁ 1 / (2 * (Ct + 1)), by positivity, fun σ hσ hσ' p _ => ⟨0, fun Cs hCs E _ => ⟨64, fun n₀ hn₀ =>
    ⟨0, fun CE _ => ⟨1, fun y hy => ?_⟩⟩⟩⟩⟩
  refine ⟨hL, hCt, ?_, hCs, hn₀, hy⟩
  show (Ct + 1) * σ < min r₁ 1
  have h1 : (Ct + 1) * σ ≤ (Ct + 1) * (min r₁ 1 / (2 * (Ct + 1))) := mul_le_mul_of_nonneg_left hσ' hCt0.le
  have h2 : (Ct + 1) * (min r₁ 1 / (2 * (Ct + 1))) = min r₁ 1 / 2 := by
    field_simp
  linarith
end SlotLemmas
open SlotLemmas in
set_option maxHeartbeats 4000000 in
theorem remaindersAreSlots (hRow : remainderExpansionAboveFramesStatement) (hAt : liftedExpansionTwoFieldsStatement)
    (hD : mixedDerivativesOnBallsStatement) (hFB : interpolatedFramesStatement)
    (hLaw : normalizedBallLawIsProbabilityStatement)
    (hSz : LocalSizeOfQuadraticBounds) (hSl : LocalSizeOfBoundedPartials) (hAl : PartialAlongBondFieldRegular)
    (hUn : RightTranslationDerivUniqueNearZero) (hRS : rightTranslationChartStatement) (hFew : SitesPerCellLePow)
    (hG : CubicTorusCellGeometry) (hJ : EventuallyInParametersCombines) : remaindersAreSlotsStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cr, hCr, hExpansionT⟩ := hRow
  obtain ⟨C₂, hC₂, hAtT⟩ := hAt
  obtain ⟨Cq₀, Cz, Crm, hP⟩ := hFB
  obtain ⟨hg1, hg2⟩ := hG
  choose! Wc hWc0 hWc using hg2
  obtain ⟨Th₀, CT, hCT0, hTh₀, hTs, hTb⟩ := hRS
  obtain ⟨r₀, hr₀, huniq⟩ := hUn
  set r₁ : ℝ := min r₀ Real.pi with hr₁
  have hr₁0 : 0 < r₁ := lt_min hr₀ Real.pi_pos
  let Cq : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ := fun U q =>
    |lpMomentConstant U.chainParams.lam (1 / 2) (Wc (2 * U.κ) * (U.L : ℝ) ^ 4) q * 1|
  let C : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U =>
    |((U.L : ℝ) ^ 4 * Cr U) * (Wc (2 ^ 6 * U.κ) * (U.L : ℝ) ^ 4)| + |(U.L : ℝ) ^ 4 * Cr U| +
      |((U.L : ℝ) ^ 4 * Cr U) * (U.Cs + CT)| +
      |U.ballRadius * ((U.L : ℝ) ^ 4 * Cr U) * (Wc (2 ^ 5 * U.κ) * (U.L : ℝ) ^ 4)| + |2 * (U.L : ℝ) ^ 4| +
      |(U.L : ℝ) ^ 4 * C₂ U|
  refine ⟨Cq, C, fun _ _ => abs_nonneg _, fun U => by positivity, ?_⟩
  refine weaken _ _ ?_ (join _ _ hP (join _ _ hExpansionT (join _ _ hAtT (eventuallyInParameters_lowerBounds hr₁0))))
  rintro T hDr ⟨hPT, hRT, hAT, hB⟩
  set Cb := Cr (parametersBeforeSide T) with hCb
  set C2 := C₂ (parametersBeforeSide T) with hC2
  set Cc := C (parametersBeforeSide T) with hCc
  set N : ℝ := (T.L : ℝ) ^ 4 with hN
  set W₂ : ℝ := Wc (2 * T.κ) * N with hW₂
  set W₅ : ℝ := Wc (2 ^ 5 * T.κ) * N with hW₅
  set W₆ : ℝ := Wc (2 ^ 6 * T.κ) * N with hW₆
  have hCc' : Cc = |(N * Cb) * W₆| + |N * Cb| + |(N * Cb) * (T.Cs + CT)| + |T.ballRadius * (N * Cb) * W₅| +
      |2 * N| + |N * C2| := rfl
  have hκ := hDr.κ_pos
  have hσ := hDr.σ_pos
  have hη₃ := hDr.η₃_pos
  have hη1 := hDr.η₃_le_one
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hcut : IsCutoff T.ballRadius T.p := hDr.cutoff
  have hlam : 0 < T.chainParams.lam := hDr.chain_admissible.positivity.2.2.1
  have hCb0 : 0 < Cb := hCr _
  have hC20 : 0 ≤ C2 := hC₂ _
  have hW₂0 : 0 ≤ W₂ := by
    have := hWc0 (2 * T.κ) (by positivity)
    positivity
  have hc1 : (N * Cb) * W₆ ≤ Cc := by
    rw [hCc']
    have := le_abs_self ((N * Cb) * W₆)
    have h2 := abs_nonneg (N * Cb)
    have h3 := abs_nonneg ((N * Cb) * (T.Cs + CT))
    have h4 := abs_nonneg (T.ballRadius * (N * Cb) * W₅)
    have h5 := abs_nonneg (2 * N)
    have h6 := abs_nonneg (N * C2)
    linarith
  have hc2 : N * Cb ≤ Cc := by
    rw [hCc']
    have := le_abs_self (N * Cb)
    have h2 := abs_nonneg ((N * Cb) * W₆)
    have h3 := abs_nonneg ((N * Cb) * (T.Cs + CT))
    have h4 := abs_nonneg (T.ballRadius * (N * Cb) * W₅)
    have h5 := abs_nonneg (2 * N)
    have h6 := abs_nonneg (N * C2)
    linarith
  have hc3 : (N * Cb) * (T.Cs + CT) ≤ Cc := by
    rw [hCc']
    have := le_abs_self ((N * Cb) * (T.Cs + CT))
    have h2 := abs_nonneg ((N * Cb) * W₆)
    have h3 := abs_nonneg (N * Cb)
    have h4 := abs_nonneg (T.ballRadius * (N * Cb) * W₅)
    have h5 := abs_nonneg (2 * N)
    have h6 := abs_nonneg (N * C2)
    linarith
  have hc4 : T.ballRadius * (N * Cb) * W₅ ≤ Cc := by
    rw [hCc']
    have := le_abs_self (T.ballRadius * (N * Cb) * W₅)
    have h2 := abs_nonneg ((N * Cb) * W₆)
    have h3 := abs_nonneg (N * Cb)
    have h4 := abs_nonneg ((N * Cb) * (T.Cs + CT))
    have h5 := abs_nonneg (2 * N)
    have h6 := abs_nonneg (N * C2)
    linarith
  have hc5 : 2 * N ≤ Cc := by
    rw [hCc']
    have := le_abs_self (2 * N)
    have h2 := abs_nonneg ((N * Cb) * W₆)
    have h3 := abs_nonneg (N * Cb)
    have h4 := abs_nonneg ((N * Cb) * (T.Cs + CT))
    have h5 := abs_nonneg (T.ballRadius * (N * Cb) * W₅)
    have h6 := abs_nonneg (N * C2)
    linarith
  have hc6 : N * C2 ≤ Cc := by
    rw [hCc']
    have := le_abs_self (N * C2)
    have h2 := abs_nonneg ((N * Cb) * W₆)
    have h3 := abs_nonneg (N * Cb)
    have h4 := abs_nonneg ((N * Cb) * (T.Cs + CT))
    have h5 := abs_nonneg (T.ballRadius * (N * Cb) * W₅)
    have h6 := abs_nonneg (2 * N)
    linarith
  have geo : ∀ (t : ℕ) (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F →
      Odd F.blockSide ∧ (∀ x y : F.Cell, cellSupDist x y = cellSupDist y x) ∧ IsPseudoMetricOnBonds (_root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist F) ∧
      (∀ b₀ : ↥(chordBonds (finiteCells F)), ∑ b, Real.exp (-(2 * T.κ * _root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist F b b₀)) ≤ W₂) ∧
      (∀ Y : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(2 ^ 5 * T.κ * cellSupDist (enclosingCell b.1.1) Y)) ≤ W₅) ∧
      (∀ Y : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(2 ^ 6 * T.κ * cellSupDist (enclosingCell b.1.1) Y)) ≤ W₆) ∧
      (∀ Y : F.Cell, ((sitesOfBlock Y).card : ℝ) ≤ N) ∧ ∀ i, 2 < F.period F.depth i := by
    intro t F hF
    obtain ⟨hLF, -, n, hside, hn⟩ := id hF
    have hodd : Odd F.blockSide := by rw [hLF]; exact hDr.odd_L
    have hn64 : 64 ≤ n := hB.n₀_ge.trans hn
    have hcub : BlockAverages.IsLargeCubicTorus F := ⟨n, hn64, hside⟩
    obtain ⟨-, -, hsym, htri, -⟩ := hg1 F hodd hcub
    have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
    have hsum : ∀ (u : ℝ), 0 < u → ∀ Y : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(u * cellSupDist (enclosingCell b.1.1) Y)) ≤ Wc u * N := by
      intro u hu Y
      have h1 := sum_chordBonds_le_sum_fineBonds (F := F)
        (fun b => Real.exp (-(u * (cellSupDist (enclosingCell b.1) Y : ℝ)))) fun _ => (Real.exp_pos _).le
      have h2 := hWc u hu F hodd hcub Y
      rw [hLF] at h2
      exact h1.trans h2
    refine ⟨hodd, hsym, isPseudoMetricOnBonds_chordBondDist hsym htri, fun b₀ => hsum (2 * T.κ) (by positivity) _,
      hsum (2 ^ 5 * T.κ) (by positivity), hsum (2 ^ 6 * T.κ) (by positivity), fun Y => ?_, fun i => ?_⟩
    · have := card_sitesOfBlock_le hFew hodd hs2 Y
      rwa [hLF] at this
    · rw [BlockOffsets.period_depth, hside i]
      have hL1 : 1 ≤ F.blockSide := hodd.pos
      nlinarith
  have hconvF : ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top),
      IsAdmissibleAt T t x f F V →
      HasUniformlyConvexLaw T.ballRadius T.chainParams.lam x T.κ T.Ct (_root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist F)
        ((coldHalfLawAt T x f).exponent V) := by
    intro t x f F V hst
    have hPT' := hPT t x hst.coupling_le
    let M : LawOnBondVariables ↥(chordBonds (finiteCells F)) := lawAtTop V ((coldHalfLawAt T x f).exponent V)
    have hadm : M.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
        (frameRadius x) (_root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist F) :=
      ⟨hst.torus, hst.small_curvature, IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hst.family_bounded,
        Function.injective_id, fun _ _ => rfl⟩
    obtain ⟨hconv, -, -⟩ := hPT'.laws _ (_root_.YangMills.Construction.ColdStepAtMirrorFrames.chordBondDist F) 1 (fun _ => 1) (fun _ => M) ⟨fun _ => zero_le_one, by simp⟩
      (fun _ => hadm)
    rw [convexCombinationExponent_lawAtTop] at hconv
    exact hconv
  have hsl : ∀ (t : ℕ) (x e : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
      (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell),
      T.coupling ≤ x → IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 < e →
      IsDecayingSiteFamily T.L T.σ T.decayRate e (e / T.η₃) r →
      BlockSumDerivBounds T.ballRadius T.κ (N * (Cb * (e / T.η₃))) Y ((coldHalfLawAt T x f).blockSum r Y) V := by
    intro t x e f F V r Y hx hF hV he hr
    obtain ⟨-, hsym, -, -, -, -, hNy, -⟩ := geo t F hF
    have hs := hRT t x e f F V r hx hF hV he hr
    have hee : e ≤ e / T.η₃ := by
      rw [le_div_iff₀ hη₃]
      nlinarith
    exact blockSumDerivBounds_of_expansion hD hsym hκ hCb0.le he.le hee (hNy Y) hs
  have hsame : ∀ Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions,
      (∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (Th w X)) →
      ∀ w X : imaginaryQuaternions, ‖w‖ < r₁ → Th w X = Th₀ w X := fun Th hTh w X hw =>
    huniq w X _ _ (lt_of_lt_of_le hw (min_le_left _ _)) (hTh w X (lt_of_lt_of_le hw (min_le_right _ _)))
      (hTh₀ w X (lt_of_lt_of_le hw (min_le_right _ _)))
  have hsmallF : ∀ (t : ℕ) (x : ℝ) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
      IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → ∀ (b : ↥(chordBonds (finiteCells F))) (u : imaginaryQuaternions),
      ‖u‖ < T.ballRadius →
      ‖interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b.1 V + u‖ < r₁ ∧
      ‖interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b.1 V + u‖ ≤ 1 := by
    intro t x F V hx hF hV b u hu
    have hsz := ((hPT t x hx).one_torus F V 1 hF hV zero_le_one le_rfl).small.norm_le b.1 b.2
    have h1 : ‖interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b.1 V + u‖ < min r₁ 1 := by
      have hu' : ‖u‖ < T.σ / 64 := hu
      calc ‖interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b.1 V + u‖ ≤
            ‖interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b.1 V‖ + ‖u‖ :=
            norm_add_le _ _
        _ ≤ (T.Ct + 1) * T.σ := by nlinarith
        _ < min r₁ 1 := hB.small
    exact ⟨lt_of_lt_of_le h1 (min_le_left _ _), (lt_of_lt_of_le h1 (min_le_right _ _)).le⟩
  have hfldF : ∀ (t : ℕ) (x : ℝ) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
      IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → ∀ (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions)
      (b : ↥(chordBonds (finiteCells F))) (u : imaginaryQuaternions),
      ‖X‖ = 1 → ‖u‖ < T.ballRadius →
      ‖topVariationField (fun w X' => Th₀ w X') 1 T.a T.chainParams.ρA (frameRadius x) c X b.1 u V‖ ≤
        T.Cs * Real.exp (-(2 ^ 8 * T.κ * cellSupDist (enclosingCell b.1.1) c.1)) := by
    intro t x F V hx hF hV c X b u hX hu
    obtain ⟨Th₂, hTh₂, -, hdec⟩ :=
      ((hPT t x hx).one_torus F V 1 hF hV zero_le_one le_rfl).variation.exists_representation
    have h1 := hdec c X b u 0 Fin.elim0 Fin.elim0 hX hu (Nat.zero_le _) (fun i => i.elim0)
    rw [bondDeriv_zero_top] at h1
    have hw := (hsmallF t x F V hx hF hV b u hu).1
    have h2 := hsame Th₂ hTh₂ _ X hw
    rw [topVariationField_congr (Th := fun w X' => Th₀ w X') (Th' := Th₂) (c := c) h2.symm]
    refine h1.trans ?_
    have hsp : cellSupDist (enclosingCell b.1.1) c.1 ≤
        bondSpan (enclosingCell b.1.1) (Fin.cons c Fin.elim0 : Fin (0 + 1) → F.Site F.top × Fin 4) :=
      le_trans (Finset.le_sup (f := fun l : Fin (0 + 1) => siteSupDist (enclosingCell b.1.1)
        ((Fin.cons c Fin.elim0 : Fin (0 + 1) → F.Site F.top × Fin 4) l).1)
        (Finset.mem_univ 0)) (le_max_left _ _)
    have hsp' : (cellSupDist (enclosingCell b.1.1) c.1 : ℝ) ≤
        (bondSpan (enclosingCell b.1.1) (Fin.cons c Fin.elim0 : Fin (0 + 1) → F.Site F.top × Fin 4) : ℝ) :=
      Nat.cast_le.2 hsp
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB.Cs_nonneg
    have h3 : (0 : ℝ) < 2 ^ 8 * T.κ := by positivity
    nlinarith
  refine ⟨fun t x e f F V r Y hst hrow he hr => ?_,
    fun t x e f F V V' r Y q ι _ _ j j' hst hst' hrow he hr hag hpair => ?_⟩
  · obtain ⟨-, -, hdist, hW, -, hW6, -, -⟩ := geo t F hst.torus
    have hx1 : 1 ≤ x := hB.coupling_ge.trans hst.coupling_le
    have hbs := hsl t x e f F V r Y hst.coupling_le hst.torus hst.small_curvature he hr.decaying
    have hconv := hconvF t x f F V hst
    have he₃ : 0 ≤ e / T.η₃ := by positivity
    have hB0 : 0 ≤ N * (Cb * (e / T.η₃)) := by positivity
    have hCqle : ∀ q, |lpMomentConstant T.chainParams.lam (1 / 2) W₂ q * 1| ≤ Cq (sizeParameters T) q :=
      fun q => le_refl _
    have hG1 : N * (Cb * (e / T.η₃)) * W₆ ≤ Cc * (e / T.η₃) := by
      have e1 : N * (Cb * (e / T.η₃)) * W₆ = ((N * Cb) * W₆) * (e / T.η₃) := by ring
      rw [e1]
      exact mul_le_mul_of_nonneg_right hc1 he₃
    have hG2 : N * (Cb * (e / T.η₃)) ≤ Cc * (e / T.η₃) := by
      have e1 : N * (Cb * (e / T.η₃)) = (N * Cb) * (e / T.η₃) := by ring
      rw [e1]
      exact mul_le_mul_of_nonneg_right hc2 he₃
    have hG3 : N * (Cb * (e / T.η₃)) * (T.Cs + CT) ≤ Cc * (e / T.η₃) := by
      have e1 : N * (Cb * (e / T.η₃)) * (T.Cs + CT) = ((N * Cb) * (T.Cs + CT)) * (e / T.η₃) := by ring
      rw [e1]
      exact mul_le_mul_of_nonneg_right hc3 he₃
    have hal := decaysAlongTopField_blockSum hSz hD hAl (r₁ := r₁) hρ hx1 hlam hκ hcut hdist hconv hW₂0 hW hCqle hB0
      hB.Cs_nonneg hCT0 hG3 hbs Th₀ hTs
      (fun w hw => hTb w 1 hw (by norm_num)) hsame
      (fun b v hv => by
        have := hsmallF t x F V hst.coupling_le hst.torus hst.small_curvature b (toImaginary v)
          (by rwa [norm_toImaginary])
        exact this)
      (fun c X b u hX hu => hfldF t x F V hst.coupling_le hst.torus hst.small_curvature c X b u hX hu)
    exact isSlot_blockSum hSl hD hρ hx1 hlam hκ hcut hdist hconv hW₂0 hW (hW6 Y) hCqle hB0 hG1 hG2 hbs hal
  · obtain ⟨-, -, -, -, hW5, -, hNy, hper⟩ := geo t F hst.torus
    have hx1 : 1 ≤ x := hB.coupling_ge.trans hst.coupling_le
    have hbs := hsl t x e f F V r Y hst.coupling_le hst.torus hst.small_curvature he hr.decaying
    have hbs' := hsl t x e f F V' r Y hst.coupling_le hst.torus hst'.small_curvature he hr.decaying
    have he₃ : 0 ≤ e / T.η₃ := by positivity
    have hee : e ≤ e / T.η₃ := by
      rw [le_div_iff₀ hη₃]
      nlinarith
    have hB0 : 0 ≤ N * (Cb * (e / T.η₃)) := by positivity
    obtain ⟨Ψ₁, K₁, hΨ₁, hcv₁, -, -⟩ := hconvF t x f F V hst
    obtain ⟨Ψ₂, K₂, hΨ₂, hcv₂, -, -⟩ := hconvF t x f F V' hst'
    have hBα : N * (Cb * (e / T.η₃)) ≤ Cc * (e / T.η₃) := by
      have e1 : N * (Cb * (e / T.η₃)) = (N * Cb) * (e / T.η₃) := by ring
      rw [e1]
      exact mul_le_mul_of_nonneg_right hc2 he₃
    have hBα₂ : T.ballRadius * (N * (Cb * (e / T.η₃))) * W₅ ≤ Cc * (e / T.η₃) := by
      have e1 : T.ballRadius * (N * (Cb * (e / T.η₃))) * W₅ = (T.ballRadius * (N * Cb) * W₅) * (e / T.η₃) := by ring
      rw [e1]
      exact mul_le_mul_of_nonneg_right hc4 he₃
    have hM₀ : 2 * (N * e) ≤ Cc * (e / T.η₃) := by
      calc 2 * (N * e) = (2 * N) * e := by ring
        _ ≤ (2 * N) * (e / T.η₃) := mul_le_mul_of_nonneg_left hee (by positivity)
        _ ≤ Cc * (e / T.η₃) := mul_le_mul_of_nonneg_right hc5 he₃
    have hcoldF : ∀ (U : F.GaugeField F.top), IsSmallCurvature (5 / 4 * T.σ) U →
        ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ < T.ballRadius) →
        IsSmallCurvature T.σ (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) U ζ) := fun U hU ζ hζ p hp =>
      (((hPT t x hst.coupling_le).one_torus F U 1 hst.torus hU zero_le_one le_rfl).small.small_curvature_nearby ζ
        (norm_le_of_lt hζ) p hp).trans (by linarith)
    have hcl : ∀ (U U' : F.GaugeField F.top), IsSmallCurvature (5 / 4 * T.σ) U → IsSmallCurvature (5 / 4 * T.σ) U' →
        ∀ ζ ζ' : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ < T.ballRadius) → (∀ b, ‖ζ' b‖ < T.ballRadius) →
        |(coldHalfLawAt T x f).blockSum r Y ζ U - (coldHalfLawAt T x f).blockSum r Y ζ' U'| ≤ N * e := by
      intro U U' hU hU' ζ ζ' hζ hζ'
      have e1 : (coldHalfLawAt T x f).blockSum r Y ζ U - (coldHalfLawAt T x f).blockSum r Y ζ' U' =
          ∑ y ∈ sitesOfBlock Y, ((coldHalfLawAt T x f).liftedExpansion r y ζ U - (coldHalfLawAt T x f).liftedExpansion r y ζ' U') :=
        (Finset.sum_sub_distrib _ _).symm
      rw [e1]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h1 : ∀ y ∈ sitesOfBlock Y,
          |(coldHalfLawAt T x f).liftedExpansion r y ζ U - (coldHalfLawAt T x f).liftedExpansion r y ζ' U'| ≤ e := fun y _ =>
        abs_remainder_sub_le hr he.le hper y (hcoldF U hU ζ hζ) (hcoldF U' hU' ζ' hζ')
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hNy Y) he.le
    have hnr : T.blockIndex ≤ q → ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        |(coldHalfLawAt T x f).blockSum r Y η V - (coldHalfLawAt T x f).blockSum r Y η V'| ≤
          Cc * (e / T.η₃) * Real.exp (-(4 * T.κ * q)) := by
      intro hq η hη
      have e1 : (coldHalfLawAt T x f).blockSum r Y η V - (coldHalfLawAt T x f).blockSum r Y η V' =
          ∑ y ∈ sitesOfBlock Y, ((coldHalfLawAt T x f).liftedExpansion r y η V - (coldHalfLawAt T x f).liftedExpansion r y η V') :=
        (Finset.sum_sub_distrib _ _).symm
      rw [e1]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h1 : ∀ y ∈ sitesOfBlock Y,
          |(coldHalfLawAt T x f).liftedExpansion r y η V - (coldHalfLawAt T x f).liftedExpansion r y η V'| ≤
          C2 * (e / T.η₃) * Real.exp (-(4 * T.κ * q)) := fun y hy =>
        hAT t x e f F V V' r Y q y η hst.coupling_le hst.torus hst.small_curvature hst'.small_curvature he hr hag hq
          (Finset.mem_filter.1 hy).2 (norm_le_of_lt hη)
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hE := Real.exp_pos (-(4 * T.κ * q))
      calc ((sitesOfBlock Y).card : ℝ) * (C2 * (e / T.η₃) * Real.exp (-(4 * T.κ * q))) ≤
          N * (C2 * (e / T.η₃) * Real.exp (-(4 * T.κ * q))) := mul_le_mul_of_nonneg_right (hNy Y) (by positivity)
        _ = ((N * C2) * (e / T.η₃)) * Real.exp (-(4 * T.κ * q)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc6 he₃) hE.le
    refine ⟨(blockSum_pointwise hD hρ hκ hB0 hbs).1, (blockSum_pointwise hD hρ hκ hB0 hbs').1, ?_⟩
    exact comparisonBounds_blockSum hLaw hD hρ hκ hcut hB0 hx1 hcv₁.smooth.continuous hΨ₁ hcv₂.smooth.continuous hΨ₂
      hBα hBα₂ (hW5 Y) hbs hbs' hpair
      (by positivity) hM₀ (hcl V V' hst.small_curvature hst'.small_curvature)
      (hcl V' V' hst'.small_curvature hst'.small_curvature) hnr
end YangMills.Construction.ResponseInTheExpansion
end
