import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.EntriesAndFloorOfTheCost
import YangMills.Construction.ClusterExpansionOfAStep.FieldOfASettingIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.GroundHasWeightAtItsFrames
import YangMills.Construction.ClusterExpansionOfAStep.GroundOfANonzeroState
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfPointsOfWeight
import YangMills.Construction.ClusterExpansionOfAStep.TheMeanOfABondIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours TorusFields TorusLumps StepSettings StepGas StepCosts StateMeasurability RenormalizationStepParameters
  StepFrames ColdChain CostDerivatives LevelAction ShareMeasurability HoledShares BlockTrees
namespace BlockActivityMeasurability
section Deriv
variable {α : Type} [MeasurableSpace α] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]
theorem measurable_lineDeriv_indicator (C : α → E → ℝ) {B : Set E} (hB : IsOpen B)
    (hC : Measurable fun q : α × E => B.indicator (C q.1) q.2)
    (hd : ∀ a, ∀ ζ ∈ B, DifferentiableAt ℝ (C a) ζ) :
    Measurable fun q : α × E × E => B.indicator (fun ζ => deriv (fun τ : ℝ => C q.1 (ζ + τ • q.2.2)) 0) q.2.1 := by
  classical
  have hBm : MeasurableSet B := hB.measurableSet
  let f : ℕ → α × E × E → ℝ := fun k q =>
    B.indicator (fun ζ => (((k : ℝ) + 1)⁻¹)⁻¹ •
      (B.indicator (C q.1) (ζ + ((k : ℝ) + 1)⁻¹ • q.2.2) - B.indicator (C q.1) ζ)) q.2.1
  have hf : ∀ k, Measurable (f k) := by
    intro k
    have h1 : Measurable fun q : α × E × E => (q.1, q.2.1 + ((k : ℝ) + 1)⁻¹ • q.2.2) :=
      measurable_fst.prodMk ((measurable_fst.comp measurable_snd).add
        ((measurable_snd.comp measurable_snd).const_smul _))
    have h2 : Measurable fun q : α × E × E => (q.1, q.2.1) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have h3 := ((hC.comp h1).sub (hC.comp h2)).const_smul ((((k : ℝ) + 1)⁻¹)⁻¹)
    have hS : MeasurableSet {q : α × E × E | q.2.1 ∈ B} := (measurable_fst.comp measurable_snd) hBm
    have e : f k = {q : α × E × E | q.2.1 ∈ B}.indicator (fun q => (((k : ℝ) + 1)⁻¹)⁻¹ •
        (B.indicator (C q.1) (q.2.1 + ((k : ℝ) + 1)⁻¹ • q.2.2) - B.indicator (C q.1) q.2.1)) := by
      funext q
      by_cases h : q.2.1 ∈ B
      · simp only [f, Set.indicator_of_mem h, Set.indicator_of_mem (show q ∈ {q : α × E × E | q.2.1 ∈ B} from h)]
      · simp only [f, Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show q ∉ {q : α × E × E | q.2.1 ∈ B} from h)]
    rw [e]
    exact Measurable.indicator h3 hS
  refine measurable_of_tendsto_metrizable hf ?_
  rw [tendsto_pi_nhds]
  intro q
  by_cases h : q.2.1 ∈ B
  · have hder : HasDerivAt (fun τ : ℝ => C q.1 (q.2.1 + τ • q.2.2))
        (deriv (fun τ : ℝ => C q.1 (q.2.1 + τ • q.2.2)) 0) 0 := by
      have h1 : HasDerivAt (fun τ : ℝ => q.2.1 + τ • q.2.2) q.2.2 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const q.2.2).const_add q.2.1
      have h2 : HasFDerivAt (C q.1) (fderiv ℝ (C q.1) (q.2.1 + (0 : ℝ) • q.2.2)) (q.2.1 + (0 : ℝ) • q.2.2) := by
        simpa using (hd q.1 _ h).hasFDerivAt
      exact (h2.comp_hasDerivAt (0 : ℝ) h1).differentiableAt.hasDerivAt
    have hs := hasDerivAt_iff_tendsto_slope_zero.mp hder
    have ht : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) Filter.atTop (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_zero.comp
        (Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop),
        Filter.Eventually.of_forall fun k => ?_⟩
      have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      simpa using this.ne'
    have hlim := hs.comp ht
    have hc : Filter.Tendsto (fun t : ℝ => q.2.1 + t • q.2.2) (nhds 0) (nhds q.2.1) := by
      have : Continuous fun t : ℝ => q.2.1 + t • q.2.2 := by fun_prop
      simpa using this.tendsto 0
    have hev : ∀ᶠ k : ℕ in Filter.atTop, q.2.1 + ((k : ℝ) + 1)⁻¹ • q.2.2 ∈ B :=
      (hc.comp (ht.mono_right nhdsWithin_le_nhds)) (hB.mem_nhds h)
    rw [Set.indicator_of_mem h]
    refine hlim.congr' ?_
    filter_upwards [hev] with k hk
    simp only [Function.comp, f, Set.indicator_of_mem h, Set.indicator_of_mem hk, zero_add, zero_smul, add_zero]
  · simp only [f, Set.indicator_of_notMem h]
    exact tendsto_const_nhds
end Deriv
section Mean
variable {β : Type} [MeasurableSpace β] {m : ℕ} {free : Finset (TorusBond m)}
theorem measurable_weightedMean (d G : β → FreeCoords free → ℝ) (hd : Measurable fun q : β × FreeCoords free => d q.1 q.2)
    (hG : Measurable fun q : β × FreeCoords free => G q.1 q.2 * d q.1 q.2) :
    Measurable fun b => weightedMean (d b) (G b) := by
  unfold weightedMean
  exact (hG.stronglyMeasurable.integral_prod_right'.measurable).div
    hd.stronglyMeasurable.integral_prod_right'.measurable
theorem measurable_intervalIntegral_unit {f : β × ℝ → ℝ} (hf : Measurable f) :
    Measurable fun b => ∫ v in (0 : ℝ)..1, f (b, v) := by
  simp only [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable
end Mean
section Family
variable {R : StepSetup} {n : ℕ} [NeZero n] {free : Finset (TorusBond (n * R.params.side))} {α : Type} [MeasurableSpace α]
def MeasurableOnBalls (R : StepSetup) {n : ℕ} {free : Finset (TorusBond (n * R.params.side))} {α : Type} [MeasurableSpace α]
    (F : α → FreeCoords free → ℝ) : Prop :=
  Measurable fun q : α × FreeCoords free => (openBallsIn R free).indicator (F q.1) q.2
theorem MeasurableOnBalls.add {F G : α → FreeCoords free → ℝ} (hF : MeasurableOnBalls R F) (hG : MeasurableOnBalls R G) :
    MeasurableOnBalls R fun a η => F a η + G a η := by
  unfold MeasurableOnBalls at *
  convert hF.add hG using 2 with q
  by_cases h : q.2 ∈ openBallsIn R free
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]
theorem MeasurableOnBalls.sub {F G : α → FreeCoords free → ℝ} (hF : MeasurableOnBalls R F) (hG : MeasurableOnBalls R G) :
    MeasurableOnBalls R fun a η => F a η - G a η := by
  unfold MeasurableOnBalls at *
  convert hF.sub hG using 2 with q
  by_cases h : q.2 ∈ openBallsIn R free
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]
theorem MeasurableOnBalls.const_mul {F : α → FreeCoords free → ℝ} (hF : MeasurableOnBalls R F) (c : ℝ) :
    MeasurableOnBalls R fun a η => c * F a η := by
  unfold MeasurableOnBalls at *
  convert hF.const_mul c using 2 with q
  by_cases h : q.2 ∈ openBallsIn R free
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]
theorem MeasurableOnBalls.sum {ι : Type} (s : Finset ι) {F : ι → α → FreeCoords free → ℝ}
    (hF : ∀ i ∈ s, MeasurableOnBalls R (F i)) : MeasurableOnBalls R fun a η => ∑ i ∈ s, F i a η := by
  unfold MeasurableOnBalls at *
  have h := Finset.measurable_fun_sum s hF
  convert h using 2 with q
  by_cases h : q.2 ∈ openBallsIn R free
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]
theorem MeasurableOnBalls.of_measurable {F : α → FreeCoords free → ℝ}
    (hF : Measurable fun q : α × FreeCoords free => F q.1 q.2) : MeasurableOnBalls R F := by
  unfold MeasurableOnBalls
  have hS : MeasurableSet {q : α × FreeCoords free | q.2 ∈ openBallsIn R free} :=
    measurable_snd measurableSet_openBallsIn
  convert Measurable.indicator hF hS using 2 with q
  by_cases h : q.2 ∈ openBallsIn R free
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show q ∈ {q : α × FreeCoords free | q.2 ∈ openBallsIn R free} from h)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (show q ∉ {q : α × FreeCoords free | q.2 ∈ openBallsIn R free} from h)]
theorem zero_mem_openBallsIn (hρ : 0 < R.ballRadius) : (0 : FreeCoords free) ∈ openBallsIn R free := by
  intro b
  rw [coordNorm_eq_norm]
  simpa using hρ
theorem smul_mem_openBallsIn (hρ : 0 < R.ballRadius) {η : FreeCoords free} (h : η ∈ openBallsIn R free) {v : ℝ}
    (hv : v ∈ Ioc (0 : ℝ) 1) : v • η ∈ openBallsIn R free := by
  intro b
  have h1 := h b
  rw [coordNorm_eq_norm] at h1 ⊢
  show ‖v • η b‖ < R.ballRadius
  rw [norm_smul, Real.norm_of_nonneg hv.1.le]
  nlinarith [norm_nonneg (η b), hv.1, hv.2]
theorem MeasurableOnBalls.at_zero {F : α → FreeCoords free → ℝ} (hF : MeasurableOnBalls R F) (hρ : 0 < R.ballRadius) :
    Measurable fun a => F a 0 := by
  have h := hF.comp (measurable_id.prodMk (measurable_const (a := (0 : FreeCoords free))))
  convert h using 2 with a
  simp [Function.comp, Set.indicator_of_mem (zero_mem_openBallsIn (free := free) hρ)]
theorem MeasurableOnBalls.const {F : α → ℝ} (hF : Measurable F) :
    MeasurableOnBalls R fun a (_ : FreeCoords free) => F a :=
  MeasurableOnBalls.of_measurable (hF.comp measurable_fst)
theorem MeasurableOnBalls.reindex {β : Type} [MeasurableSpace β] {F : α → FreeCoords free → ℝ} (hF : MeasurableOnBalls R F)
    {u : β → α} (hu : Measurable u) :
    Measurable fun q : β × FreeCoords free => (openBallsIn R free).indicator (F (u q.1)) q.2 :=
  Measurable.comp (g := fun q : α × FreeCoords free => (openBallsIn R free).indicator (F q.1) q.2)
    (f := fun q : β × FreeCoords free => (u q.1, q.2)) hF ((hu.comp measurable_fst).prodMk measurable_snd)
theorem measurable_interpolated_form {γ : Type} [MeasurableSpace γ] {c t a g : γ → ℝ} (hc : Measurable c) (ht : Measurable t)
    (ha : Measurable a) (hg : Measurable g) :
    Measurable fun q => c q * Real.exp (-(t q * a q) - (1 - t q) * g q) :=
  hc.mul (((ht.mul ha).neg.sub ((measurable_const.sub ht).mul hg)).exp)
theorem measurable_perturbed_form {γ : Type} [MeasurableSpace γ] {c t a g : γ → ℝ} (hc : Measurable c) (ht : Measurable t)
    (ha : Measurable a) (hg : Measurable g) :
    Measurable fun q => c q * Real.exp (-a q + t q * g q) :=
  hc.mul ((ha.neg.add (ht.mul hg)).exp)
theorem measurableOnBalls_segmentIntegral (D : α → BlockDensitySplit R n free) (hρ : 0 < R.ballRadius)
    (hc : MeasurableOnBalls R fun a => (D a).totalCost)
    (hd : ∀ a, ∀ ζ ∈ openBallsIn R free, DifferentiableAt ℝ (D a).totalCost ζ) (b : free) :
    MeasurableOnBalls R fun a η => ∫ v in (0 : ℝ)..1,
      deriv (fun τ : ℝ => (D a).totalCost (v • η + τ • singleBond b η)) 0 := by
  have hg := measurable_lineDeriv_indicator (fun a => (D a).totalCost) (B := openBallsIn R free) isOpen_openBallsIn hc hd
  have hm : Measurable fun p : (α × FreeCoords free) × ℝ =>
      (p.1.1, p.2 • p.1.2, singleBond b p.1.2) :=
    (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.smul (measurable_snd.comp measurable_fst)).prodMk
      ((continuous_singleBond b).measurable.comp (measurable_snd.comp measurable_fst)))
  have h1 := measurable_intervalIntegral_unit (hg.comp hm)
  have hS : MeasurableSet {q : α × FreeCoords free | q.2 ∈ openBallsIn R free} :=
    measurable_snd measurableSet_openBallsIn
  unfold MeasurableOnBalls
  convert Measurable.indicator h1 hS using 2 with q
  by_cases h : q.2 ∈ openBallsIn R free
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show q ∈ {q : α × FreeCoords free | q.2 ∈ openBallsIn R free} from h)]
    simp only [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    simp only [Function.comp, Set.indicator_of_mem (smul_mem_openBallsIn hρ h hv)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (show q ∉ {q : α × FreeCoords free | q.2 ∈ openBallsIn R free} from h)]
set_option maxHeartbeats 1600000 in
theorem measurable_activity (D : α → BlockDensitySplit R n free) (lam : ℝ) (Y : TorusSite n) (hρ : 0 < R.ballRadius)
    (hp : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn)
    (hc : ∀ Y, MeasurableOnBalls R fun a => (D a).cost Y)
    (hj : ∀ Y, MeasurableOnBalls R fun a => (D a).logJacobian Y)
    (hphi : ∀ Y, MeasurableOnBalls R fun a => (D a).density Y)
    (hd : ∀ a, ∀ ζ ∈ openBallsIn R free, DifferentiableAt ℝ (D a).totalCost ζ) :
    Measurable fun a => (D a).activity lam Y := by
  classical
  have hcs : MeasurableOnBalls R fun a => (D a).totalCost :=
    MeasurableOnBalls.sum Finset.univ fun Y _ => hc Y
  have hpsi : ∀ Y, MeasurableOnBalls R fun a => (D a).interaction Y := by
    intro Y
    have h1 : MeasurableOnBalls R fun a η => ∑ b ∈ freeBondsAt free Y, ∫ v in (0 : ℝ)..1,
        deriv (fun τ : ℝ => (D a).totalCost (v • η + τ • singleBond b η)) 0 :=
      MeasurableOnBalls.sum _ fun b _ => measurableOnBalls_segmentIntegral D hρ hcs hd b
    exact ((h1.const_mul R.coupling).sub (hj Y)).add (MeasurableOnBalls.const ((hj Y).at_zero hρ))
  have hpsum : MeasurableOnBalls R fun a => (D a).totalInteraction :=
    MeasurableOnBalls.sum Finset.univ fun Y _ => hpsi Y
  have hphisum : MeasurableOnBalls R fun a η => ∑ Y : TorusSite n, (D a).density Y η :=
    MeasurableOnBalls.sum Finset.univ fun Y _ => hphi Y
  have hcut : Measurable (cutoffProd (R := R) (free := free)) := measurable_cutoffProd hp
  have hgauss : ∀ Y, Measurable (gaussianPart (R := R) (free := free) lam Y) := fun Y =>
    (continuous_gaussianPart lam Y).measurable
  have hgs : Measurable fun η : FreeCoords free => ∑ Y : TorusSite n, gaussianPart (R := R) lam Y η :=
    Finset.measurable_fun_sum _ fun Y _ => hgauss Y
  have hfst : Measurable (Prod.fst : α × ℝ → α) := measurable_fst
  have hq2 : Measurable (Prod.snd : (α × ℝ) × FreeCoords free → FreeCoords free) := measurable_snd
  have hτ : Measurable fun q : (α × ℝ) × FreeCoords free => q.1.2 := measurable_snd.comp measurable_fst
  have hc' : Measurable fun q : (α × ℝ) × FreeCoords free => cutoffProd (R := R) q.2 := hcut.comp hq2
  have hgs' : Measurable fun q : (α × ℝ) × FreeCoords free => ∑ Y : TorusSite n, gaussianPart (R := R) lam Y q.2 :=
    hgs.comp hq2
  have ha := MeasurableOnBalls.reindex hpsum hfst
  have hb := MeasurableOnBalls.reindex hphisum hfst
  have hT : Measurable fun q : (α × ℝ) × FreeCoords free => (D q.1.1).interpolatedDensity lam q.1.2 q.2 := by
    have h1 := measurable_interpolated_form hc' hτ ha hgs'
    have e : (fun q : (α × ℝ) × FreeCoords free => (D q.1.1).interpolatedDensity lam q.1.2 q.2) = fun q =>
        cutoffProd (R := R) q.2 * Real.exp (-(q.1.2 * (openBallsIn R free).indicator ((D q.1.1).totalInteraction) q.2) -
          (1 - q.1.2) * ∑ Y : TorusSite n, gaussianPart (R := R) lam Y q.2) := by
      funext q
      unfold BlockDensitySplit.interpolatedDensity
      by_cases h : q.2 ∈ openBallsIn R free
      · rw [Set.indicator_of_mem h]
      · rw [cutoffProd_eq_zero h, zero_mul, zero_mul]
    rw [e]
    exact h1
  have hN : Measurable fun q : (α × ℝ) × FreeCoords free => (D q.1.1).perturbedDensity q.1.2 q.2 := by
    have h1 := measurable_perturbed_form hc' hτ ha hb
    have e : (fun q : (α × ℝ) × FreeCoords free => (D q.1.1).perturbedDensity q.1.2 q.2) = fun q =>
        cutoffProd (R := R) q.2 * Real.exp (-(openBallsIn R free).indicator ((D q.1.1).totalInteraction) q.2 +
          q.1.2 * (openBallsIn R free).indicator (fun η => ∑ Y : TorusSite n, (D q.1.1).density Y η) q.2) := by
      funext q
      unfold BlockDensitySplit.perturbedDensity
      by_cases h : q.2 ∈ openBallsIn R free
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [cutoffProd_eq_zero h, zero_mul, zero_mul]
    rw [e]
    exact h1
  have hTG : Measurable fun q : (α × ℝ) × FreeCoords free =>
      ((D q.1.1).interaction Y q.2 - gaussianPart (R := R) lam Y q.2) * (D q.1.1).interpolatedDensity lam q.1.2 q.2 := by
    have ha' := MeasurableOnBalls.reindex (hpsi Y) hfst
    have hg' : Measurable fun q : (α × ℝ) × FreeCoords free => gaussianPart (R := R) lam Y q.2 := (hgauss Y).comp hq2
    have h1 := (ha'.sub hg').mul hT
    have e : (fun q : (α × ℝ) × FreeCoords free =>
        ((D q.1.1).interaction Y q.2 - gaussianPart (R := R) lam Y q.2) * (D q.1.1).interpolatedDensity lam q.1.2 q.2) =
        fun q => ((openBallsIn R free).indicator ((D q.1.1).interaction Y) q.2 - gaussianPart (R := R) lam Y q.2) *
          (D q.1.1).interpolatedDensity lam q.1.2 q.2 := by
      funext q
      by_cases h : q.2 ∈ openBallsIn R free
      · rw [Set.indicator_of_mem h]
      · have : (D q.1.1).interpolatedDensity lam q.1.2 q.2 = 0 := by
          unfold BlockDensitySplit.interpolatedDensity
          rw [cutoffProd_eq_zero h, zero_mul]
        rw [this, mul_zero, mul_zero]
    rw [e]
    exact h1
  have hNG : Measurable fun q : (α × ℝ) × FreeCoords free =>
      (D q.1.1).density Y q.2 * (D q.1.1).perturbedDensity q.1.2 q.2 := by
    have ha' := MeasurableOnBalls.reindex (hphi Y) hfst
    have h1 := ha'.mul hN
    have e : (fun q : (α × ℝ) × FreeCoords free => (D q.1.1).density Y q.2 * (D q.1.1).perturbedDensity q.1.2 q.2) =
        fun q => (openBallsIn R free).indicator ((D q.1.1).density Y) q.2 * (D q.1.1).perturbedDensity q.1.2 q.2 := by
      funext q
      by_cases h : q.2 ∈ openBallsIn R free
      · rw [Set.indicator_of_mem h]
      · have : (D q.1.1).perturbedDensity q.1.2 q.2 = 0 := by
          unfold BlockDensitySplit.perturbedDensity
          rw [cutoffProd_eq_zero h, zero_mul]
        rw [this, mul_zero, mul_zero]
    rw [e]
    exact h1
  have hI1 := measurable_intervalIntegral_unit (measurable_weightedMean
    (fun b : α × ℝ => (D b.1).interpolatedDensity lam b.2)
    (fun b η => (D b.1).interaction Y η - gaussianPart (R := R) lam Y η) hT hTG)
  have hI2 := measurable_intervalIntegral_unit (measurable_weightedMean
    (fun b : α × ℝ => (D b.1).perturbedDensity b.2) (fun b => (D b.1).density Y) hN hNG)
  unfold BlockDensitySplit.activity
  exact ((((((hc Y).at_zero hρ).const_mul R.coupling).neg.add ((hj Y).at_zero hρ)).add measurable_const).sub hI1).add hI2
end Family
section Fields
variable {F : BlockFrame} {j : ℕ}
theorem measurable_pathHolonomy (l : List PathStep) (x : F.Site j) :
    Measurable fun X : F.GaugeField j => pathHolonomy X x l := by apply _root_.YangMills.Construction.BlockTrees.measurable_pathHolonomy <;> assumption
theorem measurable_readAtLevel {m : ℕ} (j : ℕ) : Measurable (readAtLevel (n := m) F j) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun i => ?_
  exact (measurable_pi_apply i).comp (measurable_pi_apply (fun k => ((siteCoords x k : ℤ) : ZMod m)))
end Fields
section Quaternions
theorem measurable_re_mul {Ξ : Type} [MeasurableSpace Ξ] {f g : Ξ → ℍ[ℝ]} (hf : MeasurableQuaternion f)
    (hg : MeasurableQuaternion g) : Measurable fun ξ => (f ξ * g ξ).re := by
  obtain ⟨a0, a1, a2, a3⟩ := hf
  obtain ⟨b0, b1, b2, b3⟩ := hg
  have e : (fun ξ => (f ξ * g ξ).re) = fun ξ => (f ξ).re * (g ξ).re - (f ξ).imI * (g ξ).imI -
      (f ξ).imJ * (g ξ).imJ - (f ξ).imK * (g ξ).imK := by
    funext ξ
    simp
  rw [e]
  exact (((a0.mul b0).sub (a1.mul b1)).sub (a2.mul b2)).sub (a3.mul b3)
theorem measurableQuaternion_of_unit {Ξ : Type} [MeasurableSpace Ξ] {g : Ξ → UnitQuaternion} (hg : Measurable g) :
    MeasurableQuaternion fun ξ => ((g ξ : UnitQuaternion) : ℍ[ℝ]) :=
  ⟨(Quaternion.continuous_re.comp continuous_subtype_val).measurable.comp hg,
    (Quaternion.continuous_imI.comp continuous_subtype_val).measurable.comp hg,
    (Quaternion.continuous_imJ.comp continuous_subtype_val).measurable.comp hg,
    (Quaternion.continuous_imK.comp continuous_subtype_val).measurable.comp hg⟩
theorem measurable_toCoords {Ξ : Type} [MeasurableSpace Ξ] {f : Ξ → imaginaryQuaternions}
    (hf : MeasurableQuaternion fun ξ => ((f ξ : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun ξ => toCoords (f ξ) := by
  obtain ⟨_, a1, a2, a3⟩ := hf
  have h : Measurable fun ξ => (![((f ξ : imaginaryQuaternions) : ℍ[ℝ]).imI, ((f ξ : imaginaryQuaternions) : ℍ[ℝ]).imJ,
      ((f ξ : imaginaryQuaternions) : ℍ[ℝ]).imK] : Fin 3 → ℝ) := by
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i
    · exact a1
    · exact a2
    · exact a3
  exact (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp h
theorem add_toImaginary (w : imaginaryQuaternions) (v : EuclideanSpace ℝ (Fin 3)) :
    w + ColdStepAtMirrorFrames.toImaginary v = ColdStepAtMirrorFrames.toImaginary (toCoords w + v) := by
  have h : ColdStepAtMirrorFrames.toImaginary (toCoords w + v) =
      ColdStepAtMirrorFrames.toImaginary (toCoords w) + ColdStepAtMirrorFrames.toImaginary v := by
    apply Subtype.ext
    refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
    · show (0 : ℝ) = 0 + 0
      simp
    · show (toCoords w + v) 0 = toCoords w 0 + v 0
      simp
    · show (toCoords w + v) 1 = toCoords w 1 + v 1
      simp
    · show (toCoords w + v) 2 = toCoords w 2 + v 2
      simp
  rw [h, toImaginary_toCoords]
theorem measurable_haarLogDensity : Measurable ColdStepAtMirrorFrames.haarLogDensity := by
  unfold ColdStepAtMirrorFrames.haarLogDensity
  refine Measurable.ite (measurableSet_lt measurable_norm measurable_const) ?_ measurable_const
  have hc : Continuous fun v : EuclideanSpace ℝ (Fin 3) => (Real.sinc ‖v‖) ^ 2 / (2 * Real.pi ^ 2) :=
    ((Real.continuous_sinc.comp continuous_norm).pow 2).div_const _
  exact hc.measurable
end Quaternions
section Costs
variable {n : ℕ} [NeZero n]
theorem measurable_bondFit (hm : MeasurableContourMeanStatement) (ℓ : StepParameters) (b : BaseChoice ℓ.side n)
    (c : TorusBond n) :
    Measurable fun p : TorusField (n * ℓ.side) × TorusField n => bondFit ℓ p.1 p.2 b c := by
  have hmean : ∀ f : ℍ[ℝ] → ℝ, Continuous f → Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
      f (contourMean ℓ.baseDepth (stepHotLumps ℓ p.1) b (readAtLevel (stepBlockFrame ℓ.side n) 0 p.1)
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)) := by
    intro f hf
    have h := hm ℓ n b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) f hf
    exact Measurable.comp (g := fun W : TorusField (n * ℓ.side) =>
      f (contourMean ℓ.baseDepth (stepHotLumps ℓ W) b (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2))) h measurable_fst
  have hq : MeasurableQuaternion fun p : TorusField (n * ℓ.side) × TorusField n =>
      contourMean ℓ.baseDepth (stepHotLumps ℓ p.1) b (readAtLevel (stepBlockFrame ℓ.side n) 0 p.1)
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) :=
    ⟨hmean _ Quaternion.continuous_re, hmean _ Quaternion.continuous_imI, hmean _ Quaternion.continuous_imJ,
      hmean _ Quaternion.continuous_imK⟩
  have hg : Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
      ((readAtLevel (stepBlockFrame ℓ.side n) 1 p.2 (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1) c.2)⁻¹ :
        UnitQuaternion) := by
    have h1 : Measurable fun V : TorusField n =>
        readAtLevel (stepBlockFrame ℓ.side n) 1 V (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1) c.2 :=
      (measurable_pi_apply c.2).comp ((measurable_pi_apply (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1)).comp
        (measurable_readAtLevel 1))
    exact (h1.comp measurable_snd).inv
  have h1 := measurable_re_mul hq (measurableQuaternion_of_unit hg)
  have h2 := hmean _ continuous_norm
  have h3 := h2.sub h1
  exact h3
theorem measurable_levelShare (hS : LevelShareOffHotMeasurable) {ℓ : StepParameters} {δ lam ρA σA cg : ℝ}
    {N : ℕ → ℝ} (hfit : ℓ.Admissible) (hch : ColdChainConstants ℓ.coupling δ ℓ.side lam ρA σA cg N)
    (hσ : ℓ.threshold ≤ σA) (t : ℕ) (hB : IsBlockTorusSide ℓ n) (y : TorusSite n) :
    Measurable fun W : TorusField n => levelShare ℓ.coupling ℓ.side t (coldRegion ℓ W) y W := by
  cases t with
  | zero =>
    refine measurable_of_eqOn_torusHotLumps_fibres hfit hB.1 fun W₀ =>
      ⟨fun W => levelShare ℓ.coupling ℓ.side 0 (coldRegion ℓ W₀) y W, ?_, ?_⟩
    · simp only [levelShare]
      refine Finset.measurable_fun_sum _ fun p _ => ?_
      exact (continuous_plaquetteEnergy p.1 p.2.1 p.2.2).measurable.const_mul _
    · intro W h
      have : coldRegion ℓ W = coldRegion ℓ W₀ := by
        unfold coldRegion torusHotSites
        rw [h]
      rw [this]
  | succ t => exact hS ℓ δ lam ρA σA cg N hfit hch hσ t n hB y
theorem measurable_blockCost (hS : LevelShareOffHotMeasurable) (hm : MeasurableContourMeanStatement)
    {ℓ : StepParameters} {δ lam ρA σA cg : ℝ} {N : ℕ → ℝ}
    (hfit : ℓ.Admissible) (hch : ColdChainConstants ℓ.coupling δ ℓ.side lam ρA σA cg N) (hσ : ℓ.threshold ≤ σA) (t : ℕ)
    (hB : IsBlockTorusSide ℓ (n * ℓ.side)) (b : BaseChoice ℓ.side n) (Y : TorusSite n) :
    Measurable fun p : TorusField (n * ℓ.side) × TorusField n => blockCost ℓ t p.1 p.2 b Y := by
  unfold blockCost
  refine Measurable.add (Finset.measurable_fun_sum _ fun y _ => ?_) (Measurable.const_mul ?_ _)
  · have h := measurable_levelShare hS hfit hch hσ t hB y
    exact Measurable.comp (g := fun W : TorusField (n * ℓ.side) =>
      levelShare ℓ.coupling ℓ.side t (coldRegion ℓ W) y W) h measurable_fst
  · exact Finset.measurable_fun_sum _ fun i _ => (measurable_bondFit hm ℓ b _).add (measurable_bondFit hm ℓ b _)
end Costs
section Settings
variable {R : StepSetup} {n : ℕ} [NeZero n] {α : Type} [MeasurableSpace α]
abbrev withData (s : ChartSetting R n) (F : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (lab : Yt → R.labels.Ω) (b : BaseChoice R.params.side n) :
    ChartSetting R n :=
  { s with free := F, support := Yt, labelling := lab, bases := b }
theorem withData_eq (s : ChartSetting R n) {F : Finset (TorusBond (n * R.params.side))}
    {Yt : Finset (TorusSite (n * R.params.side))} {b : BaseChoice R.params.side n} (hF : s.free = F)
    (hY : s.support = Yt) (hb : s.bases = b) :
    withData s F Yt (fun z => s.labelling ⟨z.1, hY ▸ z.2⟩) b = s := by
  subst hF hY hb
  rfl
variable {s : α → ChartSetting R n} {F : Finset (TorusBond (n * R.params.side))}
  {Yt : Finset (TorusSite (n * R.params.side))} {lab : α → Yt → R.labels.Ω} {b : BaseChoice R.params.side n}
theorem measurable_gaugeAt (x : TorusSite (n * R.params.side)) :
    Measurable fun W : TorusField (n * R.params.side) => gaugeAt (R := R) W x := by
  unfold gaugeAt axialGauge
  exact (measurable_pathHolonomy _ _).comp (measurable_readAtLevel 0)
theorem measurable_expUnit_toImaginary {Ξ : Type} [MeasurableSpace Ξ] {u : Ξ → EuclideanSpace ℝ (Fin 3)}
    (hu : Measurable u) : Measurable fun ξ => expUnit (ColdStepAtMirrorFrames.toImaginary (u ξ)) :=
  (continuous_expUnit.comp continuous_toImaginary).measurable.comp hu
theorem measurable_withData_field (hV : Measurable fun a => (s a).coarse) (hbase : Measurable fun a => (s a).fine)
    (hfr : ∀ c ∈ F, Measurable fun a =>
      toCoords (frameCoord R.params R.anchorRadius R.depth R.frameReach (s a).coarse c)) :
    Measurable fun q : α × FreeCoords F => (withData (s q.1) F Yt (lab q.1) b).field q.2 := by
  classical
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun i => ?_
  by_cases h : (x, i) ∈ F
  · have e : (fun q : α × FreeCoords F => (withData (s q.1) F Yt (lab q.1) b).field q.2 x i) = fun q =>
        (gaugeAt (s q.1).fine x)⁻¹ *
          (if IsCrossingBond (F := stepBlockFrame R.params.side n)
              (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)
            then expUnit (ColdStepAtMirrorFrames.toImaginary
                (toCoords (frameCoord R.params R.anchorRadius R.depth R.frameReach (s q.1).coarse (x, i)) +
                  q.2 ⟨(x, i), h⟩)) *
              (s q.1).coarse (parentBlock R.params.side x) i
            else expUnit (ColdStepAtMirrorFrames.toImaginary
                (toCoords (frameCoord R.params R.anchorRadius R.depth R.frameReach (s q.1).coarse (x, i)) +
                  q.2 ⟨(x, i), h⟩))) *
          gaugeAt (s q.1).fine (x + TorusFields.unitStep (n * R.params.side) i) := by
      funext q
      have h1 : (withData (s q.1) F Yt (lab q.1) b).field q.2 x i =
          chartLink (withData (s q.1) F Yt (lab q.1) b) x i
            ((withData (s q.1) F Yt (lab q.1) b).frame (x, i) +
              ColdStepAtMirrorFrames.toImaginary (q.2 ⟨(x, i), h⟩)) := dif_pos h
      rw [h1]
      unfold chartLink
      simp only [ChartSetting.frame, add_toImaginary]
    rw [e]
    have hb1 : Measurable fun q : α × FreeCoords F => (s q.1).fine := hbase.comp measurable_fst
    have ht1 := (measurable_gaugeAt (R := R) x).comp hb1
    have ht2 := (measurable_gaugeAt (R := R) (x + TorusFields.unitStep (n * R.params.side) i)).comp hb1
    have hu : Measurable fun q : α × FreeCoords F =>
        toCoords (frameCoord R.params R.anchorRadius R.depth R.frameReach (s q.1).coarse (x, i)) + q.2 ⟨(x, i), h⟩ :=
      ((hfr _ h).comp measurable_fst).add ((measurable_pi_apply _).comp measurable_snd)
    have hE := measurable_expUnit_toImaginary hu
    have hv : Measurable fun q : α × FreeCoords F => (s q.1).coarse (parentBlock R.params.side x) i :=
      (measurable_pi_apply i).comp ((measurable_pi_apply _).comp (hV.comp measurable_fst))
    by_cases hc : IsCrossingBond (F := stepBlockFrame R.params.side n)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)
    · simp only [if_pos hc]
      exact (ht1.inv.mul (hE.mul hv)).mul ht2
    · simp only [if_neg hc]
      exact (ht1.inv.mul hE).mul ht2
  · have e : (fun q : α × FreeCoords F => (withData (s q.1) F Yt (lab q.1) b).field q.2 x i) = fun q =>
        (s q.1).fine x i := funext fun q => dif_neg h
    rw [e]
    exact (measurable_pi_apply i).comp ((measurable_pi_apply x).comp (hbase.comp measurable_fst))
theorem measurable_activity_withData (hS : LevelShareOffHotMeasurable) (hm : MeasurableContourMeanStatement)
    {δ lam ρA σA cg : ℝ} {N : ℕ → ℝ} (hfit : R.params.Admissible)
    (hch : ColdChainConstants R.params.coupling δ R.params.side lam ρA σA cg N)
    (hσ : R.params.threshold ≤ σA) (hB : IsBlockTorusSide R.params (n * R.params.side)) (hrow : R.HasExpansions)
    (hρ : 0 < R.ballRadius) (hp : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn)
    (hV : Measurable fun a => (s a).coarse) (hbase : Measurable fun a => (s a).fine)
    (hfr : ∀ c ∈ F, Measurable fun a =>
      toCoords (frameCoord R.params R.anchorRadius R.depth R.frameReach (s a).coarse c))
    (hlab : Measurable lab)
    (hset : ∀ a, (withData (s a) F Yt (lab a) b).IsAdmissible)
    (hd : ∀ a, ∀ ζ ∈ openBallsIn R F, DifferentiableAt ℝ (withData (s a) F Yt (lab a) b).totalCost ζ)
    (l : ℝ) (Y : TorusSite n) :
    Measurable fun a => (withData (s a) F Yt (lab a) b).blockActivity l Y := by
  classical
  have hW := measurable_withData_field (Yt := Yt) (lab := lab) (b := b) hV hbase hfr
  have hV' : Measurable fun q : α × FreeCoords F => (s q.1).coarse := hV.comp measurable_fst
  have hc : ∀ Y, MeasurableOnBalls R fun a => (withData (s a) F Yt (lab a) b).densitySplit.cost Y := by
    intro Y
    refine MeasurableOnBalls.of_measurable ?_
    have h := (measurable_blockCost hS hm hfit hch hσ R.depth hB b Y).comp (hW.prodMk hV')
    exact h
  have hj : ∀ Y, MeasurableOnBalls R fun a => (withData (s a) F Yt (lab a) b).densitySplit.logJacobian Y := by
    intro Y
    refine MeasurableOnBalls.of_measurable ?_
    have h1 : ∀ i : Fin 4, Measurable fun q : α × FreeCoords F =>
        logPartitionGap (R.params.coupling * R.coupling *
          meanNorm R.params ((withData (s q.1) F Yt (lab q.1) b).field q.2) b (Y, i)) := by
      intro i
      have h2 := hm R.params n b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Y, i) (fun q => ‖q‖) continuous_norm
      have h3 : Measurable fun W : TorusField (n * R.params.side) => meanNorm R.params W b (Y, i) := h2
      exact measurable_logPartitionGap.comp ((h3.comp hW).const_mul _)
    have h4 : ∀ c : F, Measurable fun q : α × FreeCoords F =>
        if bondBlock (R := R) c.1 = Y then
          Real.log (ColdStepAtMirrorFrames.haarLogDensity
            (toCoords (frameCoord R.params R.anchorRadius R.depth R.frameReach (s q.1).coarse c.1) + q.2 c))
        else 0 := by
      intro c
      by_cases hb : bondBlock (R := R) c.1 = Y
      · simp only [if_pos hb]
        exact Real.measurable_log.comp (measurable_haarLogDensity.comp
          (((hfr c.1 c.2).comp measurable_fst).add ((measurable_pi_apply c).comp measurable_snd)))
      · simp only [if_neg hb]
        exact measurable_const
    have h5 := (Finset.measurable_fun_sum Finset.univ fun i _ => h1 i).add
      (Finset.measurable_fun_sum Finset.univ fun c _ => h4 c)
    exact h5
  have hphi : ∀ Y, MeasurableOnBalls R fun a => (withData (s a) F Yt (lab a) b).densitySplit.density Y := by
    intro Y
    have hlab' : Measurable fun q : α × FreeCoords F => lab q.1 := hlab.comp measurable_fst
    have h1 : ∀ y : TorusSite (n * R.params.side), Measurable fun q : α × FreeCoords F =>
        if IsHullState R.params (clusterRange R.coupling) ((withData (s q.1) F Yt (lab q.1) b).field q.2) Yt ∧
          ∀ X ∈ chainComponents (clusterRange R.coupling) Yt,
            R.clusterFactor (n * R.params.side) ((withData (s q.1) F Yt (lab q.1) b).field q.2) Yt (lab q.1) X ≠ 0
        then R.siteDensity (n * R.params.side) y ((withData (s q.1) F Yt (lab q.1) b).field q.2) Yt (lab q.1)
        else 0 := by
      intro y
      have h := ((hrow.2.borel (n * R.params.side) hB Yt).2.2 y).comp (hW.prodMk hlab')
      exact h
    have h2 := MeasurableOnBalls.of_measurable (R := R) (F := fun (a : α) (η : FreeCoords F) =>
      ∑ y ∈ sitesInBlocks R.params.side {Y},
        if IsHullState R.params (clusterRange R.coupling) ((withData (s a) F Yt (lab a) b).field η) Yt ∧
          ∀ X ∈ chainComponents (clusterRange R.coupling) Yt,
            R.clusterFactor (n * R.params.side) ((withData (s a) F Yt (lab a) b).field η) Yt (lab a) X ≠ 0
        then R.siteDensity (n * R.params.side) y ((withData (s a) F Yt (lab a) b).field η) Yt (lab a) else 0)
      (Finset.measurable_fun_sum (sitesInBlocks R.params.side {Y}) fun y _ => h1 y)
    unfold MeasurableOnBalls at h2 ⊢
    convert h2 using 2 with q
    by_cases hη : q.2 ∈ openBallsIn R F
    · rw [Set.indicator_of_mem hη, Set.indicator_of_mem hη]
      have hb : (withData (s q.1) F Yt (lab q.1) b).InBalls q.2 := fun c => (hη c).le
      have ha := (hset q.1).isHull q.2 hb
      have hf := (hset q.1).factor_ne_zero q.2 hb
      show ∑ y ∈ sitesInBlocks R.params.side {Y}, R.siteDensity (n * R.params.side) y _ Yt (lab q.1) = _
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [if_pos ⟨ha, hf⟩]
    · rw [Set.indicator_of_notMem hη, Set.indicator_of_notMem hη]
  have hd' : ∀ a, ∀ ζ ∈ openBallsIn R F,
      DifferentiableAt ℝ (withData (s a) F Yt (lab a) b).densitySplit.totalCost ζ := hd
  have h := measurable_activity (fun a => (withData (s a) F Yt (lab a) b).densitySplit) l Y hρ hp hc hj hphi hd'
  exact h
end Settings
section Numbers
theorem add_two_pow_le {u : ℝ} (hu : 1000000 ≤ u) : (u + 2) ^ 100 ≤ 1.01 * u ^ 100 := by
  have hu2 : 0 < u + 2 := by linarith
  have ha : (-2 : ℝ) ≤ -2 / (u + 2) := by
    rw [le_div_iff₀ hu2]
    nlinarith
  have h1 := one_add_mul_le_pow ha 100
  have e : 1 + -2 / (u + 2) = u / (u + 2) := by
    field_simp
    ring
  rw [e, div_pow] at h1
  have hp : 0 < (u + 2) ^ 100 := by positivity
  have h2 : (0.999 : ℝ) ≤ 1 + ((100 : ℕ) : ℝ) * (-2 / (u + 2)) := by
    have : 200 / (u + 2) ≤ 0.001 := by
      rw [div_le_iff₀ hu2]
      nlinarith
    have e2 : ((100 : ℕ) : ℝ) * (-2 / (u + 2)) = -(200 / (u + 2)) := by
      push_cast
      ring
    rw [e2]
    linarith
  have h3 : (0.999 : ℝ) ≤ u ^ 100 / (u + 2) ^ 100 := h2.trans h1
  rw [le_div_iff₀ hp] at h3
  have h4 : 0 < u ^ 100 := by positivity
  nlinarith
theorem le_clusterRange {q : ℕ} {x : ℝ} (hx : (q : ℝ) ^ 100 ≤ x) : q ≤ clusterRange x := by
  have h0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have h1 : (q : ℝ) = ((q : ℝ) ^ 100) ^ ((1 : ℝ) / 100) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
    norm_num
  have h2 : (q : ℝ) ≤ x ^ ((1 : ℝ) / 100) := by
    conv_lhs => rw [h1]
    exact Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have h3 := h2.trans (Nat.le_ceil _)
  unfold clusterRange
  exact_mod_cast h3
theorem exists_exp_tail_le {δ A τ : ℝ} (hδ : 0 < δ) (hτ : 0 < τ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → A * Real.exp (-(δ * (q : ℝ))) ≤ τ := by
  have hx : Filter.Tendsto (fun q : ℕ => δ * (q : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hδ
  have h1 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hx).const_mul A
  rw [mul_zero] at h1
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.1 h1).2 τ hτ)
  exact ⟨q₀, fun q hq => (hq₀ q hq).le⟩
theorem coupling_le_of_clusterRange {x x' : ℝ} (hx : 0 < x) (hr : clusterRange x' ≤ clusterRange x + 1)
    (hbig : 2000000 ≤ clusterRange x) : x' ≤ 1.01 * x := by
  by_cases hx' : x' ≤ 0
  · linarith
  have hx'0 : 0 < x' := not_le.mp hx'
  set u := x ^ ((1 : ℝ) / 100) with hu
  set u' := x' ^ ((1 : ℝ) / 100) with hu'
  have hu0 : 0 ≤ u := Real.rpow_nonneg hx.le _
  have hu'0 : 0 ≤ u' := Real.rpow_nonneg hx'0.le _
  have h1 : u' ≤ (clusterRange x' : ℝ) := Nat.le_ceil _
  have h2 : (clusterRange x : ℝ) < u + 1 := Nat.ceil_lt_add_one hu0
  have h3 : (clusterRange x' : ℝ) ≤ (clusterRange x : ℝ) + 1 := by exact_mod_cast hr
  have h4 : u' ≤ u + 2 := by linarith
  have h5 : (2000000 : ℝ) ≤ (clusterRange x : ℝ) := by exact_mod_cast hbig
  have h6 : 1000000 ≤ u := by linarith
  have e : ∀ {z : ℝ}, 0 < z → (z ^ ((1 : ℝ) / 100)) ^ 100 = z := by
    intro z hz
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    norm_num
  have h7 : x' = u' ^ 100 := (e hx'0).symm
  have h8 : x = u ^ 100 := (e hx).symm
  rw [h7, h8]
  exact (pow_le_pow_left₀ hu'0 h4 100).trans (add_two_pow_le h6)
end Numbers
section Empty
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem fieldAt_empty (b : TorusBond (n * R.params.side)) :
    (GasFamily.empty : GasFamily R n).fieldAt b = Sum.inl () := by
  unfold GasFamily.fieldAt
  rw [dif_neg]
  rintro ⟨θ, h, _⟩
  simp [GasFamily.Occupies, GasFamily.empty] at h
theorem baseAt_empty (y : TorusSite n) : (GasFamily.empty : GasFamily R n).baseAt y = Sum.inl () := by
  unfold GasFamily.baseAt
  rw [dif_neg]
  rintro ⟨θ, h, _⟩
  simp [GasFamily.Occupies, GasFamily.empty] at h
theorem sites_empty : (GasFamily.empty : GasFamily R n).sites = ∅ := by
  classical
  unfold GasFamily.sites
  rw [Finset.filter_false_of_mem]
  · simp
  · intro θ _ h
    simp [GasFamily.Occupies, GasFamily.empty] at h
variable (G : GasGround R n)
theorem groundSetting_free : G.groundSetting.free = G.freeBonds := by
  classical
  show (G.freeBonds.filter fun b => (GasFamily.empty : GasFamily R n).fieldAt b = Sum.inl ()) = _
  exact Finset.filter_true_of_mem fun b _ => fieldAt_empty b
theorem groundSetting_support : G.groundSetting.support = G.recordedSites := by
  show G.recordedSites ∪ (GasFamily.empty : GasFamily R n).sites = _
  rw [sites_empty, Finset.union_empty]
theorem groundSetting_bases : G.groundSetting.bases = G.groundBases := by
  funext c
  show (match (GasFamily.empty : GasFamily R n).baseAt
      (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
    | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
    | Sum.inl _ => G.groundBases c) = _
  rw [baseAt_empty]
theorem settingWithFamily_empty_fine : (G.settingWithFamily GasFamily.empty).fine = G.state.storedField := by
  funext x i
  show (match (GasFamily.empty : GasFamily R n).fieldAt (x, i) with
    | Sum.inr g => g
    | Sum.inl _ => G.state.fieldWithStoredLinks (trivialField _) x i) = _
  rw [fieldAt_empty]
  rfl
theorem getRight_eq_getOrDefault {Ω : Type} (m : WithNone Ω) (h : m.isRight = true) (d : Ω) :
    m.getRight h = getOrDefault m d := by
  rcases m with u | a
  · simp at h
  · rfl
theorem groundSetting_labelling (z : TorusSite (n * R.params.side)) (hz : z ∈ G.groundSetting.support) (d : R.labels.Ω) :
    G.groundSetting.labelling ⟨z, hz⟩ = getOrDefault (G.state.labelAt z) d := by
  have hn : z ∉ (GasFamily.empty : GasFamily R n).sites := by
    rw [sites_empty]
    exact Finset.notMem_empty _
  have h1 : G.groundSetting.labelling ⟨z, hz⟩ =
      G.recordedLabel ⟨z, (Finset.mem_union.mp hz).resolve_right hn⟩ := dif_neg hn
  rw [h1]
  exact getRight_eq_getOrDefault _ _ d
end Empty
section TwoGrounds
variable {R : StepSetup} {n : ℕ} [NeZero n] {G G' : GasGround R n}
theorem recordedSites_eq (h : ShapeEquivalent G.state G'.state) : G.recordedSites = G'.recordedSites := by
  classical
  unfold GasGround.recordedSites
  refine Finset.filter_congr fun z _ => ?_
  rw [labelAt_isRight_eq h z]
theorem isRecorded_iff (h : ShapeEquivalent G.state G'.state) (b : TorusBond (n * R.params.side)) :
    G.IsRecorded b ↔ G'.IsRecorded b := by
  unfold GasGround.IsRecorded
  rcases markAt_shape h (parentBlock R.params.side b.1) with ⟨h1, h2⟩ | ⟨s, s', h1, h2, _, _, _, _, h3⟩
  · simp [h1, h2]
  · simp only [h1, h2, Option.some.injEq, exists_eq_left']
    rw [h3]
theorem freeBonds_eq (hC : G.cut = G'.cut) (h : ShapeEquivalent G.state G'.state) : G.freeBonds = G'.freeBonds := by
  classical
  unfold GasGround.freeBonds
  rw [hC]
  refine Finset.filter_congr fun b _ => ?_
  rw [isRecorded_iff h b]
theorem groundBases_eq (h : ShapeEquivalent G.state G'.state) : G.groundBases = G'.groundBases := by
  funext c
  unfold GasGround.groundBases
  rcases markAt_shape h (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
    ⟨h1, h2⟩ | ⟨s, s', h1, h2, _, _, _, h3, _⟩
  · rw [h1, h2]
  · rw [h1, h2]
    simp only [h3]
theorem shapeEquivalent_of {Z : Finset (TorusSite n)} {ω ω' : Z → CoarseLabel R.labels.Ω R.params.side}
    (e : ∀ y, markShape (ω y) = markShape (ω' y)) :
    ShapeEquivalent (⟨Z, ω⟩ : CoarseState R n) ⟨Z, ω'⟩ := by
  classical
  refine ⟨rfl, fun y => ?_⟩
  by_cases hy : y ∈ Z
  · have h1 : coarseLabelAt (⟨Z, ω⟩ : CoarseState R n) y = ω ⟨y, hy⟩ := dif_pos hy
    have h2 : coarseLabelAt (⟨Z, ω'⟩ : CoarseState R n) y = ω' ⟨y, hy⟩ := dif_pos hy
    rw [h1, h2]
    exact e _
  · have h1 : coarseLabelAt (⟨Z, ω⟩ : CoarseState R n) y = Sum.inl () := dif_neg hy
    have h2 : coarseLabelAt (⟨Z, ω'⟩ : CoarseState R n) y = Sum.inl () := dif_neg hy
    rw [h1, h2]
end TwoGrounds
section Cold
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem measurableQuaternion_of_continuousOn {s : Set (TorusField n)} {f : TorusField n → ℍ[ℝ]}
    (hf : ContinuousOn f s) {α : Type} [MeasurableSpace α] {v : α → TorusField n} (hv : Measurable v)
    (hs : ∀ a, v a ∈ s) : MeasurableQuaternion fun a => f (v a) := by apply _root_.YangMills.Construction.CoarseMeasurability.measurableQuaternion_of_continuousOn <;> assumption
theorem coldNearSite_of_not_mem (hfit : R.params.Admissible) (hLn : R.params.side ∣ n)
    (hm : R.frameReach ≤ 2 * R.nextRange) {V : TorusField n} {y : TorusSite n} (hy : y ∉ hotCoreSites R V) :
    ColdNearSite R.params.threshold R.frameReach y V := by apply _root_.YangMills.Construction.CoarseMeasurability.coldNearSite_of_not_mem_hotCoreSites <;> assumption
theorem isCold_of_small (hfit : R.params.Admissible) (hLn : R.params.side ∣ n) (hsm : n ≤ 4 * R.nextRange)
    {V : TorusField n} {y : TorusSite n} (hy : y ∉ hotCoreSites R V) : IsCold R.params.threshold V := by apply _root_.YangMills.Construction.CoarseMeasurability.isCold_of_not_mem_hotCoreSites_of_small <;> assumption
end Cold
section Piece
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem differentiableAt_withData (s : ChartSetting R n) {F : Finset (TorusBond (n * R.params.side))}
    {Yt : Finset (TorusSite (n * R.params.side))} {b : BaseChoice R.params.side n} (hF : s.free = F)
    (hY : s.support = Yt) (hb : s.bases = b)
    (h : ∀ ζ : FreeCoords s.free, s.InBalls ζ → DifferentiableAt ℝ s.totalCost ζ) :
    ∀ ζ ∈ openBallsIn R F,
      DifferentiableAt ℝ (withData s F Yt (fun z => s.labelling ⟨z.1, hY ▸ z.2⟩) b).totalCost ζ := by
  subst hF hY hb
  intro ζ hζ
  exact h ζ fun c => (hζ c).le
theorem measurable_activity_on_piece (hS : LevelShareOffHotMeasurable) (hm : MeasurableContourMeanStatement)
    {δ lam ρA σA cg : ℝ} {N : ℕ → ℝ} (hfit : R.params.Admissible)
    (hch : ColdChainConstants R.params.coupling δ R.params.side lam ρA σA cg N)
    (hσ : R.params.threshold ≤ σA) (hB : IsBlockTorusSide R.params (n * R.params.side)) (hrow : R.HasExpansions)
    (hρ : 0 < R.ballRadius) (hp : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn)
    (Y : Finset (TorusSite n)) (Pc : Set (TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side)))
    (C : Finset (TorusSite n))
    (hC : ∀ p ∈ Pc, hotCoreSites R p.1 = C)
    (hsh : ∀ p ∈ Pc, ∀ p' ∈ Pc, ∀ y, markShape (p.2 y) = markShape (p'.2 y))
    (hcont : ∀ c ∈ markedBonds R C, ContinuousOn
      (fun V : TorusField n =>
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach V c : imaginaryQuaternions) : ℍ[ℝ]))
      {V | hotCoreSites R V = C})
    (hset : ∀ p ∈ Pc, (hotCaseGround R p.1 ⟨Y, p.2⟩).groundSetting.IsAdmissible)
    (hcost : ∀ p ∈ Pc, ∀ ζ : FreeCoords (hotCaseGround R p.1 ⟨Y, p.2⟩).groundSetting.free,
      (hotCaseGround R p.1 ⟨Y, p.2⟩).groundSetting.InBalls ζ →
        DifferentiableAt ℝ (hotCaseGround R p.1 ⟨Y, p.2⟩).groundSetting.totalCost ζ)
    (l : ℝ) (y' : TorusSite n) :
    Measurable fun a : Pc => (hotCaseGround R a.1.1 ⟨Y, a.1.2⟩).groundSetting.blockActivity l y' := by
  classical
  by_cases hne : Nonempty Pc
  swap
  · have : IsEmpty Pc := not_nonempty_iff.mp hne
    exact measurable_of_empty _
  obtain ⟨a₀⟩ := hne
  let G : Pc → GasGround R n := fun a => hotCaseGround R a.1.1 ⟨Y, a.1.2⟩
  have hsame : ∀ a, ShapeEquivalent (G a).state (G a₀).state :=
    fun a => shapeEquivalent_of fun y => hsh _ a.2 _ a₀.2 y
  have hCe : ∀ a, (G a).cut = (G a₀).cut := fun a => (hC _ a.2).trans (hC _ a₀.2).symm
  let F := (G a₀).freeBonds
  let Yt := (G a₀).recordedSites
  let b := (G a₀).groundBases
  have hFe : ∀ a, (G a).groundSetting.free = F :=
    fun a => (groundSetting_free _).trans (freeBonds_eq (hCe a) (hsame a))
  have hYe : ∀ a, (G a).groundSetting.support = Yt :=
    fun a => (groundSetting_support _).trans (recordedSites_eq (hsame a))
  have hbe : ∀ a, (G a).groundSetting.bases = b :=
    fun a => (groundSetting_bases _).trans (groundBases_eq (hsame a))
  let lab : Pc → Yt → R.labels.Ω := fun a z => (G a).groundSetting.labelling ⟨z.1, by rw [hYe a]; exact z.2⟩
  have hfix : ∀ a, withData (G a).groundSetting F Yt (lab a) b = (G a).groundSetting :=
    fun a => withData_eq _ (hFe a) (hYe a) (hbe a)
  let o : Pc → ChartSetting R n := fun a => (G a).settingWithFamily GasFamily.empty
  have hFo : ∀ a, (o a).free = F := hFe
  have hYo : ∀ a, (o a).support = Yt := hYe
  have hbo : ∀ a, (o a).bases = b := hbe
  let labo : Pc → Yt → R.labels.Ω := fun a z => (o a).labelling ⟨z.1, by rw [hYo a]; exact z.2⟩
  have hfixo : ∀ a, withData (o a) F Yt (labo a) b = o a := fun a => withData_eq _ (hFo a) (hYo a) (hbo a)
  have hV : Measurable fun a : Pc => a.1.1 := measurable_fst.comp measurable_subtype_coe
  have hω : Measurable fun a : Pc => a.1.2 := measurable_snd.comp measurable_subtype_coe
  have hFm : ∀ c ∈ F, c ∈ markedBonds R C := by
    intro c hc
    have h1 : c ∈ markedBonds R (G a₀).cut := (Finset.mem_filter.mp hc).1
    rwa [show (G a₀).cut = C from hC _ a₀.2] at h1
  have hfr : ∀ c ∈ F, Measurable fun a : Pc =>
      toCoords (frameCoord R.params R.anchorRadius R.depth R.frameReach a.1.1 c) := by
    intro c hc
    exact measurable_toCoords (measurableQuaternion_of_continuousOn (hcont c (hFm c hc)) hV fun a => hC _ a.2)
  have hbo' : Measurable fun a : Pc => (o a).fine := by
    have e : (fun a : Pc => (o a).fine) = fun a => CoarseState.storedField (⟨Y, a.1.2⟩ : CoarseState R n) :=
      funext fun a => settingWithFamily_empty_fine (G a)
    rw [e]
    exact (measurable_storedField Y).comp hω
  have hbase : Measurable fun a : Pc => (G a).groundSetting.fine := by
    have h := measurable_withData_field (s := o) (F := F) (Yt := Yt) (lab := labo) (b := b) hV hbo' hfr
    have h2 := h.comp (measurable_id.prodMk (measurable_const (a := (0 : FreeCoords F))))
    have e : (fun a : Pc => (G a).groundSetting.fine) = fun a => (withData (o a) F Yt (labo a) b).field 0 := by
      funext a
      show (o a).field 0 = _
      exact congrArg (fun t : ChartSetting R n => t.field 0) (hfixo a).symm
    rw [e]
    exact h2
  have hlab : Measurable lab := by
    refine measurable_pi_iff.mpr fun z => ?_
    have e : (fun a : Pc => lab a z) = fun a => getOrDefault ((G a).state.labelAt z.1) (lab a₀ z) :=
      funext fun a => groundSetting_labelling (G a) _ _ _
    rw [e]
    have h1 : Measurable fun a : Pc => CoarseState.labelAt (⟨Y, a.1.2⟩ : CoarseState R n) z.1 :=
      (measurable_labelAt (R := R) Y z.1).comp hω
    exact measurable_getOrDefault.comp (h1.prodMk measurable_const)
  have hset' : ∀ a, (withData (G a).groundSetting F Yt (lab a) b).IsAdmissible := fun a => by
    rw [hfix a]
    exact hset _ a.2
  have hd : ∀ a, ∀ ζ ∈ openBallsIn R F,
      DifferentiableAt ℝ (withData (G a).groundSetting F Yt (lab a) b).totalCost ζ :=
    fun a => differentiableAt_withData _ (hFe a) (hYe a) (hbe a) (hcost _ a.2)
  have hz := measurable_activity_withData (s := fun a => (G a).groundSetting) (F := F) (Yt := Yt) (lab := lab) (b := b)
    hS hm hfit hch hσ hB hrow hρ hp hV hbase hfr hlab hset' hd l y'
  have e : (fun a : Pc => (hotCaseGround R a.1.1 ⟨Y, a.1.2⟩).groundSetting.blockActivity l y') =
      fun a => (withData (G a).groundSetting F Yt (lab a) b).blockActivity l y' :=
    funext fun a => (congrArg (fun t : ChartSetting R n => t.blockActivity l y') (hfix a)).symm
  rw [e]
  exact hz
end Piece
section Hull
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
theorem measurableSet_of_torusHotLumps (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (P : Finset (Finset (TorusSite n)) → Prop) :
    MeasurableSet {W : TorusField n | P (torusHotLumps ℓ W)} := by apply _root_.YangMills.Construction.CoarseMeasurability.measurableSet_of_torusHotLumps <;> assumption
theorem measurableSet_isHullState (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (r : ℕ) (Y : Finset (TorusSite n)) :
    MeasurableSet {W : TorusField n | IsHullState ℓ r W Y} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.measurableSet_setOf_isHullState <;> assumption
end Hull
end BlockActivityMeasurability
open BlockActivityMeasurability in
set_option maxHeartbeats 1600000 in
theorem groundBlockActivityMeasurable (hF : CoarseFactorExpansionMeasurable) (hS : LevelShareOffHotMeasurable)
    (hm : MeasurableContourMeanStatement) (hFC : continuousOn_frameCoord_of_cold)
    (hG : NonvanishingStateHotGround) (hP : SettingAdmissibleOfHasWeight)
    (hW : GroundWeightAtEmpty) (hSh : SharesSumToAction)
    (hAct : ActionSmoothAlongMoves) (hReg : ComplementOfThickenedLumpsRegular)
    (hFr : FrameNearMinimizer) : GroundBlockActivityMeasurable := by
  classical
  intro T hT
  obtain ⟨y₁, h₁⟩ := hF T hT
  obtain ⟨y₂, h₂⟩ := hG T hT
  obtain ⟨y₃, h₃⟩ := hP T hT
  obtain ⟨y₄, h₄⟩ := hW T hT
  have hchainT := hT.chain
  have hδ : 0 < T.δ₁ := hchainT.1
  have hσT := hT.σ_pos
  obtain ⟨CA, _, hAF⟩ := hAct T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N (by linarith [hT.a_ge]) hT.L_odd hchainT
  have hAF' : ActionDerivativeBounds T.coupling T.δ₁ T.σA CA T.side := hAF
  obtain ⟨q₀, hq₀⟩ := exists_exp_tail_le (δ := T.δ₁) (A := T.N 0 * (2 * T.threshold)) (τ := T.threshold / 64) hδ
    (by positivity)
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (((2 ^ 11 * q₀ : ℕ) : ℝ) ^ 100), fun y hy R hOn hForm n _ hB Y y' => ?_⟩
  have hy0 := (le_max_left _ _).trans hy
  have ey₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy0
  have ey₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy0
  have ey₃ : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy0
  have ey₄ : y₄ ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy0
  have hyr : ((2 ^ 11 * q₀ : ℕ) : ℝ) ^ 100 ≤ R.coupling := ((le_max_right _ _).trans hy).trans hOn.le_coupling
  have hrq : 2 ^ 11 * q₀ ≤ R.range := le_clusterRange hyr
  have hfit := hForm.admissible
  have hLn : R.params.side ∣ n := hB.1
  have hLpos : 0 < R.params.side := hfit.L_odd.pos
  have hl := hOn.params_eq
  have haR : R.params.coupling = T.coupling := by rw [hl]; rfl
  have hLR : R.params.side = T.side := by rw [hl]; rfl
  have hσR : R.params.threshold = T.threshold := by rw [hl]; rfl
  have hJR : R.params.baseDepth = T.baseDepth := by rw [hl]; rfl
  have hch : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [haR, hLR, hOn.anchorRadius_eq]
    exact hchainT
  have hσ : R.params.threshold ≤ T.σA := by
    rw [hσR]
    linarith [hT.σ_le]
  have hρR : R.ballRadius = T.threshold / 64 := by
    unfold StepSetup.ballRadius
    rw [hσR]
  have hρ : 0 < R.ballRadius := by
    rw [hρR]
    positivity
  have hrb : 2 ^ 40 * R.params.side ≤ R.range := hForm.range_ge_side
  have hr40 : 2 ^ 40 ≤ R.range := le_trans (Nat.le_mul_of_pos_right _ hLpos) hrb
  have hra : R.range ≤ R.nextRange + 1 := hForm.range_le
  have hrg : 2 ^ 16 ≤ R.nextRange := hForm.nextRange_ge
  have hxx : R.nextCoupling ≤ 1.01 * R.coupling := coupling_le_of_clusterRange hForm.coupling_pos hForm.nextRange_le (by
    have : 2000000 ≤ R.range := le_trans (by norm_num) hr40
    exact this)
  have hm16 : 16 ≤ R.frameReach := by
    show 16 ≤ R.range / 2 ^ 11
    norm_num at hr40 ⊢
    omega
  have hm₀ : R.frameReach = R.range / 2 ^ 11 := rfl
  have hm2 : R.frameReach ≤ 2 * R.nextRange := by
    rw [hm₀]
    norm_num at hrg ⊢
    omega
  have hn₀ : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) hB.2
  have n64 : 64 ≤ n := le_trans (by have := hfit.n₀_ge; omega) hn₀
  have hblock : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  have hcont : ∀ (C : Finset (TorusSite n)), ∀ b ∈ markedBonds R C,
      ContinuousOn (fun V : TorusField n =>
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ]))
        {V | hotCoreSites R V = C} := by
    intro C b hb
    have hb' := Finset.mem_filter.mp hb
    obtain ⟨c1, c2⟩ := hFC R.params T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N hfit hch hσ R.depth R.frameReach n hm16 n64
      b hb'.1
    by_cases hs : 4 * R.frameReach + 5 < n
    · refine (c1 hs).mono fun V hV => ?_
      have hV' : hotCoreSites R V = C := hV
      exact coldNearSite_of_not_mem hfit hLn hm2 (by rw [hV']; exact hb'.2)
    · refine (c2 hs).mono fun V hV => ?_
      have hV' : hotCoreSites R V = C := hV
      have hsm : n ≤ 4 * R.nextRange := by
        rw [hm₀] at hs
        norm_num at hrg hs ⊢
        omega
      exact isCold_of_small hfit hLn hsm (y := parentBlock R.params.side b.1) (by rw [hV']; exact hb'.2)
  let cond : Set (TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side)) := {p |
    IsHullState R.params R.nextRange p.1 Y ∧ ∀ X ∈ chainComponents R.nextRange Y, coarseFactorExpansion R n p.1 Y p.2 X ≠ 0}
  have hcond : MeasurableSet cond := by
    have e : cond = (Prod.fst ⁻¹' {V | IsHullState R.params R.nextRange V Y}) ∩
        ⋂ X ∈ chainComponents R.nextRange Y, {p | coarseFactorExpansion R n p.1 Y p.2 X ≠ 0} := by
      ext p
      simp [cond]
    rw [e]
    refine (measurable_fst (measurableSet_isHullState hfit hLn _ Y)).inter
      (Finset.measurableSet_biInter _ fun X _ => ?_)
    exact ((h₁ y ey₁ R hOn hForm n hB Y X) (measurableSet_singleton 0)).compl
  have hground : ∀ p ∈ cond, (hotCaseGround R p.1 ⟨Y, p.2⟩).IsAdmissibleGround := by
    intro p hp
    refine Or.inr (h₂ y ey₂ R hOn hForm hxx n hB p.1 ⟨Y, p.2⟩ hp.1 fun X hX => ?_).isHot
    have e : coarseFactorExpansion R n p.1 Y p.2 X = coarseFactor p.1 (⟨Y, p.2⟩ : CoarseState R n) X :=
      dif_neg (NeZero.ne n)
    rw [← e]
    exact hp.2 X hX
  have hset : ∀ p ∈ cond, (hotCaseGround R p.1 ⟨Y, p.2⟩).groundSetting.IsAdmissible := by
    intro p hp
    have hg := hground p hp
    refine h₃ y ey₃ R hOn hxx n _ hg GasFamily.empty ?_ 0 (h₄ y ey₄ R hOn hxx n _ hg)
    exact ⟨fun θ h => by simp [GasFamily.Occupies, GasFamily.empty] at h, fun θ _ h => by
      simp [GasFamily.Occupies, GasFamily.empty] at h⟩
  have hF' : ActionDerivativeBounds R.params.coupling T.δ₁ T.σA CA R.params.side := by
    rw [hl]
    exact hAF'
  have hgap : T.N 0 * (2 * R.params.threshold) * Real.exp (-(T.δ₁ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤
      R.ballRadius := by
    rw [hρR, hσR]
    exact hq₀ _ ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega))
  have hcost : ∀ p ∈ cond, ∀ ζ : FreeCoords (hotCaseGround R p.1 ⟨Y, p.2⟩).groundSetting.free,
      (hotCaseGround R p.1 ⟨Y, p.2⟩).groundSetting.InBalls ζ →
        DifferentiableAt ℝ (hotCaseGround R p.1 ⟨Y, p.2⟩).groundSetting.totalCost ζ := by
    intro p hp ζ hζ
    have hctx : (hotCaseGround R p.1 ⟨Y, p.2⟩).groundSetting.ChainContext T.δ₁ T.lam T.σA T.cg T.N :=
      { admissible := hset p hp
        params_admissible := hfit
        large_range := ⟨by
          have : 64 * R.params.side + 2 ^ 16 ≤ 2 ^ 40 * R.params.side := by nlinarith
          omega, hra⟩
        n₀_le := hn₀
        chain := hch
        baseDepth_pos := by
          have := hT.J₀_ge
          omega
        threshold_le := by
          rw [hσR]
          exact hT.σ_le
        anchor_ge := by
          have h1 := hT.ρ_le
          rw [hOn.anchorRadius_eq, hρR, hσR]
          have h2 : T.ballRadius = T.threshold / 64 := rfl
          rw [h2] at h1
          linarith
        ballRadius_ge := hgap
        complement_regular := hReg
        frame_near := hFr }
    have h := (contDiffAt_costSum hSh hctx hF' hζ).differentiableAt (by norm_num)
    exact h
  let S : Option (Finset (TorusSite n) × (Y → CoarseStateShape R.params.side)) →
      Set (TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side)) := fun i =>
    match i with
    | none => condᶜ
    | some c => cond ∩ ({p | hotCoreSites R p.1 = c.1} ∩ {p | ∀ y, markShape (p.2 y) = c.2 y})
  have hSm : ∀ i, MeasurableSet (S i) := by
    intro i
    rcases i with _ | ⟨C, τ⟩
    · exact hcond.compl
    · refine hcond.inter (MeasurableSet.inter ?_ ?_)
      · exact measurable_fst (measurableSet_of_torusHotLumps hfit hLn fun H =>
          thickening (2 * R.nextRange) (H.biUnion id) = C)
      · have e : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | ∀ y, markShape (p.2 y) = τ y} =
            ⋂ y, {p | markShape (p.2 y) = τ y} := by
          ext p
          simp
        rw [e]
        refine MeasurableSet.iInter fun y => ?_
        have hq : Measurable fun p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) => p.2 y :=
          (measurable_pi_apply y).comp measurable_snd
        exact hq (measurableSet_configShape (τ y))
  refine measurable_of_countable_cover S hSm (fun p => ?_) fun i => ?_
  · by_cases h : p ∈ cond
    · exact ⟨some (hotCoreSites R p.1, fun y => markShape (p.2 y)), h, rfl, fun _ => rfl⟩
    · exact ⟨none, h⟩
  · rcases i with _ | ⟨C, τ⟩
    · have e : (fun x : S none => if IsHullState R.params R.nextRange x.1.1 Y ∧
          ∀ X ∈ chainComponents R.nextRange Y, coarseFactorExpansion R n x.1.1 Y x.1.2 X ≠ 0
          then (hotCaseGround R x.1.1 ⟨Y, x.1.2⟩).groundSetting.blockActivity T.lam y' else 0) = fun _ => 0 :=
        funext fun x => if_neg x.2
      exact e ▸ measurable_const
    · have hz := measurable_activity_on_piece hS hm hfit hch hσ hblock hForm.hasExpansions hρ hForm.isCutoff Y
        (S (some (C, τ))) C
        (fun p hp => hp.2.1) (fun p hp p' hp' y => (hp.2.2 y).trans (hp'.2.2 y).symm) (hcont C)
        (fun p hp => hset p hp.1) (fun p hp => hcost p hp.1) T.lam y'
      have e : (fun x : S (some (C, τ)) => if IsHullState R.params R.nextRange x.1.1 Y ∧
          ∀ X ∈ chainComponents R.nextRange Y, coarseFactorExpansion R n x.1.1 Y x.1.2 X ≠ 0
          then (hotCaseGround R x.1.1 ⟨Y, x.1.2⟩).groundSetting.blockActivity T.lam y' else 0) =
          fun x => (hotCaseGround R x.1.1 ⟨Y, x.1.2⟩).groundSetting.blockActivity T.lam y' :=
        funext fun x => if_pos x.2.1
      exact e ▸ hz
end YangMills.Construction.ClusterExpansionOfAStep
end
