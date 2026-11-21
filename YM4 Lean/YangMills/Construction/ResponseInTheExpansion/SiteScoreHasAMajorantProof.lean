import YangMills.Construction.ResponseInTheExpansion.PartsOfTheGasAreColdMeansProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
open Dobrushin StepGas StepSettings WeightedResponses TorusFields RenormalizationStepParameters
namespace ResponseInTheExpansion
namespace SiteScoreMajorant
section Spins
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
  {C : PairConstraint S} {μ : ∀ i, Measure (S i)} {W : (∀ i, S i) → ℝ} {z : I → ℝ}
private theorem lintegral_single_spin_le [∀ i, SigmaFinite (μ i)] (h : C.IsActivityBounded μ W z) (i : I)
    (g : S i → ℝ≥0∞) (hg : Measurable g) (hg0 : g (C.vacant i) = 0) (c : ℝ≥0∞)
    (hpaid : ∀ x, C.IsAdmissible x →
      ∫⁻ v in {C.vacant i}ᶜ, g v * C.weightDensity W (Function.update x i v) ∂μ i ≤
        c * C.weightDensity W (Function.update x i (C.vacant i))) :
    ∫⁻ σ, g (σ i) * C.weightDensity W σ ∂Measure.pi μ ≤ c * ∫⁻ σ, C.weightDensity W σ ∂Measure.pi μ := by apply _root_.YangMills.SharedProofs.p71899 <;> assumption
end Spins
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def occupiedScoreExp (A : ResponseSetup R) {G : GasGround R n} (i : G.GasSpin) :
    G.SpinValue i → ℝ≥0∞ :=
  Sum.elim (fun _ => 0) fun v => ENNReal.ofReal (Real.exp (_root_.YangMills.Construction.WeightedResponses.spinScore A i (Sum.inr v)))
private theorem measurable_occupiedScoreExp (A : ResponseSetup R) (hs : Measurable A.score) {G : GasGround R n}
    (i : G.GasSpin) : Measurable (occupiedScoreExp A i) := by apply _root_.YangMills.DeltaSharedProofs.p501890 <;> assumption
private theorem exists_spin_of_mem_sites (G : GasGround R n) (σ : G.Config)
    {y : TorusSite (n * R.params.side)} (h : y ∈ (G.familyOf σ).sites) :
    ∃ (i : G.GasSpin) (v : G.SpinState i) (hy : y ∈ i.1.2), σ i = Sum.inr v ∧
      (G.familyOf σ).labelAt h = v.1.2.1 ⟨y, hy⟩ := by apply _root_.YangMills.SharedProofs.p29352 <;> assumption
private theorem ofReal_chartSiteScore_le (A : ResponseSetup R) (hnn : ∀ w, 0 ≤ A.score w) (G : GasGround R n)
    (σ : G.Config) (y : TorusSite (n * R.params.side)) :
    ENNReal.ofReal (chartSiteScore A (configSetting G σ) y) ≤
      ENNReal.ofReal (recordedSiteScore A G y) + ∑ i : G.GasSpin, occupiedScoreExp A i (σ i) := by
  classical
  unfold chartSiteScore siteScore
  by_cases hy : y ∈ (configSetting G σ).support
  · rw [dif_pos hy]
    by_cases hs : y ∈ (G.familyOf σ).sites
    · have e1 : (configSetting G σ).labelling ⟨y, hy⟩ = (G.familyOf σ).labelAt hs := dif_pos hs
      obtain ⟨i, v, hz, hv, e2⟩ := exists_spin_of_mem_sites G σ hs
      rw [e1, e2]
      refine le_trans ?_ (le_add_left (Finset.single_le_sum (f := fun i => occupiedScoreExp A i (σ i))
        (fun _ _ => zero_le) (Finset.mem_univ i)))
      show _ ≤ occupiedScoreExp A i (σ i)
      rw [hv]
      show _ ≤ ENNReal.ofReal (Real.exp (∑ w : i.1.2, A.score (v.1.2.1 w)))
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : A.score (v.1.2.1 ⟨y, hz⟩) ≤ ∑ w : i.1.2, A.score (v.1.2.1 w) :=
        Finset.single_le_sum (f := fun w => A.score (v.1.2.1 w)) (fun _ _ => hnn _) (Finset.mem_univ _)
      have h2 := Real.add_one_le_exp (∑ w : i.1.2, A.score (v.1.2.1 w))
      linarith
    · have hst : y ∈ G.recordedSites := (Finset.mem_union.mp hy).resolve_right hs
      have e1 : (configSetting G σ).labelling ⟨y, hy⟩ = G.recordedLabel ⟨y, hst⟩ := dif_neg hs
      have e2 : recordedSiteScore A G y = A.score (G.recordedLabel ⟨y, hst⟩) := by
        unfold recordedSiteScore siteScore
        rw [dif_pos hst]
      rw [e1, ← e2]
      exact le_self_add
  · rw [dif_neg hy]
    simp
end SiteScoreMajorant
open SiteScoreMajorant in
theorem siteScoreHasIntegrableMajorant_holds (hP : clusterScoreIntegralBound)
    (hW : ClusterExpansionOfAStep.GasIsActivityBounded) (hC : Dobrushin.ActivityConditionalLawsStatement) :
    siteScoreHasIntegrableMajorant := by
  obtain ⟨r₁, p₁, g₁⟩ := hP
  obtain ⟨r₂, p₂, g₂⟩ := hW
  refine ⟨fun c => min (r₁ c) (r₂ c), fun c => lt_min (p₁ c) (p₂ c), fun T hD hrt K => ?_⟩
  obtain ⟨y₁, G₁⟩ := g₁ T hD (hrt.trans (min_le_left _ _)) K
  obtain ⟨y₂, G₂⟩ := g₂ T hD (hrt.trans (min_le_right _ _))
  refine ⟨max (max y₁ y₂) (200 * T.B), fun y hy R A hK hAt n _ G hG x₀ => ?_⟩
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
  have hy2 : y₂ ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
  have hyB : 200 * T.B ≤ y := (le_max_right _ _).trans hy
  have hR := hAt.onFamily
  have hx : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAt.abs_sub_le).2
    have h2 := hR.le_coupling
    linarith
  have hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity T.gasRate) :=
    G₂ y hy2 R hR hx n G hG _
  have hpaid := G₁ y hy1 R A hK hAt n G hG
  have hprob := (hC _ _ G.pairConstraint (G.referenceMeasure ∅) G.weight (G.spinActivity T.gasRate) hw).1
  set Z : ℝ≥0∞ := ∫⁻ σ, G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure ∅) with hZ
  have hZtop : Z ≠ ⊤ := by
    intro htop
    have h1 : G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight Set.univ = 1 := hprob.measure_univ
    simp only [PairConstraint.gibbsLaw, ← hZ, htop, ENNReal.inv_top, zero_smul, Measure.coe_zero,
      Pi.zero_apply] at h1
    exact zero_ne_one h1
  have hsn := hAt.admissible.price.nonneg
  have hsb := hAt.admissible.price.borel
  have hd := hw.measurable_weightDensity
  refine ⟨fun σ => ENNReal.ofReal (recordedSiteScore A G x₀) + ∑ i : G.GasSpin, occupiedScoreExp A i (σ i),
    ?_, ?_, ?_⟩
  · exact measurable_const.add (Finset.measurable_sum _ fun i _ =>
      (measurable_occupiedScoreExp A hsb i).comp (measurable_pi_apply i))
  · exact fun σ _ => ofReal_chartSiteScore_le A hsn G σ x₀
  · have hspin : ∀ i : G.GasSpin, ∫⁻ σ, occupiedScoreExp A i (σ i) * G.pairConstraint.weightDensity G.weight σ
        ∂Measure.pi (G.referenceMeasure ∅) ≤ ENNReal.ofReal (G.spinActivity T.gasRate i) * Z := by
      intro i
      refine lintegral_single_spin_le hw i _ (measurable_occupiedScoreExp A hsb i) rfl _ fun x hx' => ?_
      refine le_trans (le_of_eq ?_) (hpaid i x hx')
      refine setLIntegral_congr_fun (hw.measurableSet_vacant i).compl fun v hv => ?_
      rcases v with u | v
      · exact absurd (by rfl) hv
      · rfl
    have e : ∀ σ : G.Config, (ENNReal.ofReal (recordedSiteScore A G x₀) +
        ∑ i : G.GasSpin, occupiedScoreExp A i (σ i)) * G.pairConstraint.weightDensity G.weight σ =
          ENNReal.ofReal (recordedSiteScore A G x₀) * G.pairConstraint.weightDensity G.weight σ +
          ∑ i : G.GasSpin, occupiedScoreExp A i (σ i) * G.pairConstraint.weightDensity G.weight σ := by
      intro σ
      rw [add_mul, Finset.sum_mul]
    simp only [e]
    rw [lintegral_add_left (hd.const_mul _), lintegral_const_mul _ hd,
      lintegral_finsetSum _ (f := fun (i : G.GasSpin) (σ : G.Config) =>
        occupiedScoreExp A i (σ i) * G.pairConstraint.weightDensity G.weight σ)
        fun i _ => ((measurable_occupiedScoreExp A hsb i).comp (measurable_pi_apply i)).mul hd]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZtop, ?_⟩
    refine ENNReal.sum_ne_top.mpr fun i _ => ne_top_of_le_ne_top ?_ (hspin i)
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZtop
end ResponseInTheExpansion
end YangMills.Construction
end
