import YangMills.Construction.ClusterExpansionOfAStep.ColdAlongAMove
import YangMills.Construction.ColdStepAtMirrorFrames.StepInFixedVariables
import YangMills.Construction.RunningCouplingSlope.ColdImageOnASmallTorus
import YangMills.Construction.RunningCouplingSlope.KernelOfTheLaplaceTotalProof
import YangMills.Construction.SummableBoundsOfTheFlow.FromTheMirrorFramesToTheLeastFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open MeasureTheory Filter
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields RenormalizationStepParameters StepSettings StepMarks TorusLumps
  TopLevelSites LaplaceAsymptotics
namespace RunningCouplingSlope
namespace LaplaceNearTrivial
theorem integral_cutoff_mul_exp_pos {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (hcut : CutoffFactorIsRadialCutoff)
    (ρ x : ℝ) (p : ℝ → ℝ) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (Q B : (Fin k → ℝ) × BondField ι → ℝ)
    (hQ : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 Q (0, η))
    (hB : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 B (0, η)) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ),
      0 < ∫ η, radialWeightProd (cutoffFactor ρ p) η * Real.exp (-(x * Q (τ, η) + B (τ, η))) := by
  set K : Set (BondField ι) := Set.pi Set.univ fun _ => Metric.closedBall 0 ρ with hKdef
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have memK : ∀ η, η ∈ K ↔ ∀ b, ‖η b‖ ≤ ρ := by
    intro η
    simp [hKdef, Set.mem_pi]
  set f : (Fin k → ℝ) × BondField ι → ℝ := fun z => x * Q z + B z with hf
  have hcont : ∀ η ∈ K, ∀ᶠ z : (Fin k → ℝ) × BondField ι in 𝓝 ((0 : Fin k → ℝ), η), ContinuousAt f z := by
    intro η hη
    have h := (memK η).1 hη
    have h1 : ContDiffAt ℝ 3 f (0, η) := (contDiffAt_const.mul (hQ η h)).add (hB η h)
    exact (h1.eventually (by simp)).mono fun z hz => hz.continuousAt
  have hev := hK.eventually_forall_of_forall_eventually (P := fun τ η => ContinuousAt f (τ, η)) hcont
  refine hev.mono fun τ hτ => ?_
  have hrw := hcut ρ p hρ hp
  set r : ℝ → ℝ := fun u => cutoffFactor ρ p (max u 0) with hr
  have hrr : ∀ η : BondField ι, radialWeightProd (cutoffFactor ρ p) η = ∏ b, r ‖η b‖ := by
    intro η
    unfold radialWeightProd
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [hr]
    rw [max_eq_left (norm_nonneg _)]
  have hrc : Continuous r := hrw.smooth.continuous
  have hrnn : ∀ u, 0 ≤ u → 0 ≤ r u := by
    intro u hu
    rcases lt_or_ge u ρ with h | h
    · exact (hrw.pos u hu h).le
    · rw [hrw.zero u h]
  set g : BondField ι → ℝ := fun η => (∏ b, r ‖η b‖) * Real.exp (-(f (τ, η))) with hg
  have hgnn : ∀ η, 0 ≤ g η := fun η =>
    mul_nonneg (Finset.prod_nonneg fun b _ => hrnn _ (norm_nonneg _)) (Real.exp_pos _).le
  have hsupp : Function.support g ⊆ K := by
    intro η hη
    rw [memK]
    intro b
    by_contra hb
    apply hη
    simp only [hg]
    rw [Finset.prod_eq_zero (Finset.mem_univ b) (hrw.zero _ (not_le.1 hb).le), zero_mul]
  have hgc : ContinuousOn g K := by
    refine ContinuousOn.mul ?_ ?_
    · exact (continuous_finset_prod _ fun b _ => hrc.comp (continuous_norm.comp (continuous_apply b))).continuousOn
    · intro η hη
      have h1 : ContinuousAt (fun ζ : BondField ι => f (τ, ζ)) η :=
        ContinuousAt.comp (f := fun ζ : BondField ι => (τ, ζ)) (hτ η hη)
          (continuous_const.prodMk continuous_id).continuousAt
      exact (Real.continuous_exp.continuousAt.comp h1.neg).continuousWithinAt
  have hint : Integrable g := (integrableOn_iff_integrable_of_support_subset hsupp).1
    (hgc.integrableOn_compact hK)
  have hU : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun b =>
      isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have hUne : ({η : BondField ι | ∀ b, ‖η b‖ < ρ}).Nonempty := ⟨0, fun b => by simpa using hρ⟩
  have hsub : {η : BondField ι | ∀ b, ‖η b‖ < ρ} ⊆ Function.support g := by
    intro η hη
    have h1 : 0 < ∏ b, r ‖η b‖ := Finset.prod_pos fun b _ => hrw.pos _ (norm_nonneg _) (hη b)
    exact (mul_pos h1 (Real.exp_pos _)).ne'
  have hpos : 0 < ∫ η, g η := by
    rw [integral_pos_iff_support_of_nonneg hgnn hint]
    exact lt_of_lt_of_le (hU.measure_pos _ hUne) (measure_mono hsub)
  have e : ∀ η : BondField ι,
      radialWeightProd (cutoffFactor ρ p) η * Real.exp (-(x * Q (τ, η) + B (τ, η))) = g η := by
    intro η
    rw [hrr]
  simpa only [e] using hpos
theorem perturb_smul_eq {n k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (s : ℝ)
    (hs : s ≠ 0) (σ : Fin k → ℝ) (W : TorusField n) :
    perturb c X σ W = perturb c (fun l => s • X l) (s⁻¹ • σ) W := by apply _root_.YangMills.SharedProofs.p22089 <;> assumption
theorem curvature_trivialField {m : ℕ} (x : TorusSite m) (μ ν : Fin 4) :
    curvature (trivialField m) x μ ν = 0 := by
  simp [curvature, holonomy_trivialField]
theorem toImaginary_zero : toImaginary 0 = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
theorem haarRadialDensity_zero_pos : 0 < haarRadialDensity 0 := by apply _root_.YangMills.Construction.FrameInterpolationProof.haarRadialDensity_zero_pos <;> assumption
theorem norm_bondFrameCoord_le {F : BlockFrame} (a ρ : ℝ) (hρ : 0 ≤ ρ) (m : ℕ) (b : F.Site F.depth × Fin 4)
    (V : F.GaugeField F.top) : ‖bondFrameCoord a ρ m b V‖ ≤ ρ := by apply _root_.YangMills.Construction.LogJacobian.norm_bondFrameCoord_le <;> assumption
variable {n : ℕ} [NeZero n]
theorem stepFrame_false_eq_true {F : BlockFrame} (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (h : ¬ ∀ i, 4 * m + 5 < F.extent i) (m' : ℕ) (b : F.Site F.depth × Fin 4) :
    stepFrame false a ρ m b V = stepFrame true a ρ m' b V := by
  simp [stepFrame, bondFrameCoord, h]
theorem coordsAboveFrame_false_eq_true {F : BlockFrame} (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (h : ¬ ∀ i, 4 * m + 5 < F.extent i) (m' : ℕ) (η : StepVariable (finiteCells F)) :
    coordsAboveFrame false a ρ m V η = coordsAboveFrame true a ρ m' V η := by
  funext x i
  unfold coordsAboveFrame
  rw [stepFrame_false_eq_true a ρ m V h m']
theorem stepExponent_false_eq_true {F : BlockFrame} (a ρ x : ℝ) (m : ℕ) (f : LocalFamily) (ν : ℝ)
    (V : F.GaugeField F.top) (h : ¬ ∀ i, 4 * m + 5 < F.extent i) (m' : ℕ)
    (η : StepVariable (finiteCells F)) :
    stepExponent false a ρ x m f ν V η = stepExponent true a ρ x m' f ν V η := by
  simp only [stepExponent, centredExpansion, fieldAboveFrame, coordsAboveFrame_false_eq_true a ρ m V h m']
theorem chartedEnergy_eq_minimalActionTotal (hc : ComplementOfThickenedLumpsRegular) (T : ParameterAssignment)
    (hT : T.Admissible) (y : ℝ) (hy : T.floorMin ≤ y) (R : StepSetup) (hR : R.OnParameters T y) (hn : T.n₀ ≤ n)
    (hside : n ≤ 4 * R.frameReach + 5) (V : TorusField n) (hV : IsCold (9 / 8 * T.threshold) V) :
    chartedEnergy R.params.coupling (coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach
        (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V) 0)
        (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V) =
      minimalActionTotal R.params.coupling R.params.side (R.depth + 1) n V := by
  have hσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hn₀ : R.params.n₀ ≤ n := by
    have : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
    omega
  have hsit : IsStepSituation R.params R.range V Finset.univ ∅ (9 / 8 * R.params.threshold) :=
    Or.inr ⟨hn₀, by rw [hσ]; exact hV, rfl, rfl, rfl⟩
  have hfits : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y hy
  have hch : ColdChain.ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [hR.params_eq, hR.anchorRadius_eq]
    exact hT.chain
  have h2σ : 2 * R.params.threshold ≤ T.σA := by rw [hσ]; exact hT.σ_le
  obtain ⟨-, -, -, -, ρle, -, -, -, hbody⟩ := hch
  have hπ : R.anchorRadius < Real.pi := lt_of_le_of_lt ρle (by linarith [Real.pi_gt_three])
  obtain ⟨spos, sle, n4096, hF⟩ := stepSituation_regular_and_cold hc hfits hsit
  have hs : ∀ i, (torusFrame R.params.side R.depth n).extent i = n := fun _ => rfl
  obtain ⟨hreg, hcold⟩ := hF (torusFrame R.params.side R.depth n) hs
  have hamb : IsAdmissibleAmbient (torusFrame R.params.side R.depth n) := Or.inr fun i => by rw [hs]; omega
  have hs2 : ∀ i, 2 ≤ (torusFrame R.params.side R.depth n).extent i := fun i => by rw [hs]; omega
  have one := (hbody (torusFrame R.params.side R.depth n) 2047
    (cellsOfSites (torusFrame R.params.side R.depth n) Finset.univ) rfl hamb
    (by norm_num) hreg _ _ spos (sle.trans h2σ) hcold).1
  obtain ⟨w, hw, -, hlc⟩ := minimizingCoordinates_eq (ρ := R.anchorRadius) hfits.L_odd hs2 hπ le_rfl one
  have hS : cellsOfSites (torusFrame R.params.side R.depth n) (Finset.univ : Finset (TorusSite n)) =
      finiteCells (torusFrame R.params.side R.depth n) := cellsOfSites_univ hs
  rw [hS] at hw hlc
  set Vt : (torusFrame R.params.side R.depth n).GaugeField (torusFrame R.params.side R.depth n).top :=
    readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V with hVt
  have hnot : ¬ ∀ i, 4 * R.frameReach + 5 < (torusFrame R.params.side R.depth n).extent i := fun h => by
    have := h 0
    have h2 : (torusFrame R.params.side R.depth n).extent 0 = n := rfl
    omega
  have hab : coordsAboveFrame false R.params.coupling R.anchorRadius R.frameReach Vt 0 = w := by
    rw [coordsAboveFrame_false_eq_true R.params.coupling R.anchorRadius R.frameReach Vt hnot 0]
    funext x i
    unfold coordsAboveFrame
    have h0 : stepCoordinates (0 : StepVariable (finiteCells (torusFrame R.params.side R.depth n))) x i = 0 := by
      unfold stepCoordinates
      split_ifs
      · simpa using toImaginary_zero
      · rfl
    rw [h0, add_zero]
    simp only [stepFrame, if_true]
    unfold minimizingBondCoordinate
    rw [hlc]
  rw [hab]
  unfold chartedEnergy minimalActionTotal
  rw [dif_neg (NeZero.ne n)]
  show _ = minimalAction R.params.coupling (cellsOfSites (torusFrame R.params.side R.depth n) Finset.univ)
    (R.depth + 1) (readAtLevel (torusFrame R.params.side R.depth n) (R.depth + 1) V)
  rw [hS]
  show _ = ⨅ W : (torusFrame R.params.side R.depth n).GaugeField R.depth,
    (minimalAction R.params.coupling (finiteCells (torusFrame R.params.side R.depth n)) R.depth W +
    R.params.coupling * ∑ c ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n)) (R.depth + 1),
      blockFit W Vt c)
  have hle := hw.2.2
  have hbdd : BddBelow (Set.range fun W : (torusFrame R.params.side R.depth n).GaugeField R.depth =>
      minimalAction R.params.coupling (finiteCells (torusFrame R.params.side R.depth n)) R.depth W +
        R.params.coupling * ∑ c ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n)) (R.depth + 1),
          blockFit W Vt c) := by
    refine ⟨blockEnergy R.params.coupling (finiteCells (torusFrame R.params.side R.depth n))
      (torusFrame R.params.side R.depth n).depth (chartedField w Vt) Vt, ?_⟩
    rintro _ ⟨W, rfl⟩
    exact hle W
  exact le_antisymm (le_ciInf fun W => hle W) (ciInf_le hbdd (chartedField w Vt))
def integralAboveMinimizer (R : StepSetup) (ρ : ℝ) (p : ℝ → ℝ) (V : TorusField n) : ℝ :=
  ∫ η : StepVariable (finiteCells (torusFrame R.params.side R.depth n)), radialWeightProd (cutoffFactor ρ p) η *
    Real.exp (-(stepExponent true R.params.coupling R.anchorRadius R.coupling 0 (localFamilyOfDensity R.density) 1
      (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V) η))
def imagePrefactor (R : StepSetup) (n : ℕ) : ℝ :=
  R.functional (n * R.params.side) (trivialField _) *
    (Real.exp (∑ _c ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n))
        (torusFrame R.params.side R.depth n).top, haarGap (R.params.coupling * R.coupling)) *
      ∏ _b : ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))), haarRadialDensity 0)
theorem coldImageIntegral_eq (hA : coldImageIntegral_eq_on_small_torus) (hc : ComplementOfThickenedLumpsRegular)
    (hfix : stepIntegralInFixedVariables) (T : ParameterAssignment) (hT : T.Admissible)
    (y : ℝ) (hy : T.floorMin ≤ y) (R : StepSetup) (hR : R.OnParameters T y) (hn : T.n₀ ≤ n)
    (hside : n ≤ 4 * R.frameReach + 5) (V : TorusField n) (hV : IsCold (9 / 8 * T.threshold) V) :
    coldImageIntegral R V = imagePrefactor R n *
      Real.exp (-(R.coupling * minimalActionTotal R.params.coupling R.params.side (R.depth + 1) n V)) *
      integralAboveMinimizer R T.ballRadius T.cutoff V := by
  have h1 := hA T hT y hy R hR n hn hside V hV
  have hodd : Odd (torusFrame R.params.side R.depth n).blockSide := by
    show Odd R.params.side
    rw [hR.params_eq]
    exact hT.L_odd
  have hρA0 : 0 ≤ R.anchorRadius := by rw [hR.anchorRadius_eq]; exact hT.chain.2.2.2.1.le
  have hρA1 : R.anchorRadius ≤ 1 := by rw [hR.anchorRadius_eq]; exact hT.chain.2.2.2.2.1
  have hρ : R.ballRadius = T.ballRadius := by
    show R.params.threshold / 64 = T.threshold / 64
    rw [hR.params_eq]
    rfl
  have hσ1 : T.threshold ≤ 1 := hT.σ_one
  have hframes : ∀ b ∈ chordBonds (finiteCells (torusFrame R.params.side R.depth n)),
      ‖stepFrame false R.params.coupling R.anchorRadius R.frameReach b
        (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V)‖ +
        R.ballRadius < Real.pi := by
    intro b _
    have h5 : ‖stepFrame false R.params.coupling R.anchorRadius R.frameReach b
        (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V)‖ ≤
        R.anchorRadius :=
      norm_bondFrameCoord_le _ _ hρA0 _ _ _
    have h6 : R.ballRadius = T.threshold / 64 := hρ
    have h7 := Real.pi_gt_three
    linarith
  have h2 := hfix (torusFrame R.params.side R.depth n) R.params.coupling R.anchorRadius R.ballRadius R.coupling
    R.frameReach R.barrierFn (localFamilyOfDensity R.density)
    (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V) hodd
    (fun _ => Nat.pos_of_ne_zero (NeZero.ne n)) hframes
  have h3 := chartedEnergy_eq_minimalActionTotal hc T hT y hy R hR hn hside V hV
  have hnot : ¬ ∀ i, 4 * R.frameReach + 5 < (torusFrame R.params.side R.depth n).extent i := fun h => by
    have := h 0
    have h2 : (torusFrame R.params.side R.depth n).extent 0 = n := rfl
    omega
  have h4 : ∫ η : StepVariable (finiteCells (torusFrame R.params.side R.depth n)),
      cutoffWeight R.ballRadius R.barrierFn η *
        Real.exp (- stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
          (localFamilyOfDensity R.density) 1
          (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V) η) =
      integralAboveMinimizer R T.ballRadius T.cutoff V := by
    unfold integralAboveMinimizer
    refine integral_congr_ae (Eventually.of_forall fun η => ?_)
    simp only
    rw [stepExponent_false_eq_true _ _ _ _ _ _ _ hnot 0, hρ, hR.barrierFn_eq]
    rfl
  rw [h1]
  unfold coldStepIntegral
  rw [h2, h3, h4]
  unfold imagePrefactor
  have e : - R.coupling * minimalActionTotal R.params.coupling R.params.side (R.depth + 1) n V =
      -(R.coupling * minimalActionTotal R.params.coupling R.params.side (R.depth + 1) n V) := by ring
  rw [e]
  ring
end LaplaceNearTrivial
open LaplaceNearTrivial in
theorem laplaceRemainderNearTrivial (hA : coldImageIntegral_eq_on_small_torus)
    (hc : ComplementOfThickenedLumpsRegular) (hfix : stepIntegralInFixedVariables)
    (hB : stepExponentNearTrivialStatement) (hcutoff : CutoffFactorIsRadialCutoff)
    (hmove : ColdNearStatement) : laplaceRemainderNearTrivialStatement := by
  intro T hT y R hy hR n k _ c X hn hside
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold ParameterAssignment.ballRadius
    positivity
  have hσ0 : 0 < T.threshold := hT.σ_pos
  have hnL : NeZero (n * R.params.side) := by
    have h1 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have h2 : 0 < R.params.side := by
      have : Odd R.params.side := by rw [hR.params_eq]; exact hT.L_odd
      exact this.pos
    exact ⟨(Nat.mul_pos h1 h2).ne'⟩
  have hD : 0 < R.functional (n * R.params.side) (trivialField _) := by
    refine hR.isStep.1.1.positive (n * R.params.side) ?_ _ ?_
    · have h0 : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
      have h2 : 0 < R.params.side := by
        have : Odd R.params.side := by rw [hR.params_eq]; exact hT.L_odd
        exact this.pos
      nlinarith
    · intro x μ ν _
      have hσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
      rw [hσ, curvature_trivialField]
      exact hσ0
  have hnum : imagePrefactor R n ≠ 0 := by
    unfold imagePrefactor
    have h1 : 0 < ∏ _b : ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))), haarRadialDensity 0 :=
      Finset.prod_pos fun _ _ => haarRadialDensity_zero_pos
    have h2 := Real.exp_pos (∑ _c ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n))
      (torusFrame R.params.side R.depth n).top, haarGap (R.params.coupling * R.coupling))
    positivity
  refine ⟨Real.log (imagePrefactor R n) - Real.log (coldImageIntegral R (trivialField n)), ?_⟩
  have hcold : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), IsCold (9 / 8 * T.threshold) (perturb c X τ (trivialField n)) := by
    refine hmove n (trivialField n) k c X 0 _ ?_
    intro x μ ν _
    rw [perturb_zero, curvature_trivialField]
    positivity
  set s : ℝ := (1 + ∑ l, ‖X l‖)⁻¹ with hs
  have hs0 : 0 < s := by positivity
  set Y : Fin k → imaginaryQuaternions := fun l => s • X l with hY
  have hYle : ∀ l, ‖Y l‖ ≤ 1 := by
    intro l
    have h1 : ‖X l‖ ≤ ∑ l, ‖X l‖ :=
      Finset.single_le_sum (f := fun l => ‖X l‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)
    rw [hY]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    rw [hs, inv_mul_le_iff₀ (by positivity)]
    linarith
  obtain ⟨C, q, -, -, hfam⟩ := hB T hT k
  obtain ⟨-, -, hL⟩ := hfam y R hy hR n c Y hn hYle
  have hpos0 := integral_cutoff_mul_exp_pos hcutoff T.ballRadius R.coupling T.cutoff hρ hT.cut
    (chartEnergyAlongCurve R n c Y) (exponentRemainderAlongCurve R n c Y)
    (fun η hη => (hL.contDiff_Q η hη).of_le (by norm_num))
    (fun η hη => hL.contDiff_B η hη)
  have hlin : Tendsto (fun τ : Fin k → ℝ => s⁻¹ • τ) (𝓝 0) (𝓝 0) := by
    have := (continuous_const_smul (s⁻¹)).tendsto (0 : Fin k → ℝ)
    simpa using this
  have hpos := hlin.eventually hpos0
  have hexp : ∀ (Z : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
      (η : StepVariable (finiteCells (torusFrame R.params.side R.depth n))),
      R.coupling * chartEnergyAlongCurve R n c Z (σ, η) + exponentRemainderAlongCurve R n c Z (σ, η) =
        stepExponent true R.params.coupling R.anchorRadius R.coupling 0 (localFamilyOfDensity R.density) 1
          (perturbedTop R n c Z σ) η := by
    intro Z σ η
    show _ + (stepExponent true R.params.coupling R.anchorRadius R.coupling 0 (localFamilyOfDensity R.density) 1
      (perturbedTop R n c Z σ) η - R.coupling * chartEnergyAlongCurve R n c Z (σ, η)) = _
    ring
  have hint : ∀ (Z : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ),
      (∫ η, radialWeightProd (cutoffFactor T.ballRadius T.cutoff) η *
        Real.exp (-(R.coupling * chartEnergyAlongCurve R n c Z (σ, η) +
          exponentRemainderAlongCurve R n c Z (σ, η)))) =
      integralAboveMinimizer R T.ballRadius T.cutoff (perturb c Z σ (trivialField n)) := by
    intro Z σ
    unfold integralAboveMinimizer
    refine integral_congr_ae (Eventually.of_forall fun η => ?_)
    simp only
    rw [hexp]
    rfl
  filter_upwards [hcold, hpos] with τ hτc hτp
  have hmv : perturb c Y (s⁻¹ • τ) (trivialField n) = perturb c X τ (trivialField n) :=
    (perturb_smul_eq c X s hs0.ne' τ _).symm
  have hJ : 0 < integralAboveMinimizer R T.ballRadius T.cutoff (perturb c X τ (trivialField n)) := by
    rw [← hmv, ← hint]
    exact hτp
  have hI := coldImageIntegral_eq hA hc hfix T hT y hy R hR hn hside _ hτc
  have hcut : logCutoffIntegral T.ballRadius T.cutoff R.coupling (chartEnergyAlongCurve R n c X)
      (exponentRemainderAlongCurve R n c X) τ =
      Real.log (integralAboveMinimizer R T.ballRadius T.cutoff (perturb c X τ (trivialField n))) := by
    unfold logCutoffIntegral
    rw [hint]
  have hlog : goodFieldLogIntegral R n (perturb c X τ (trivialField n)) =
      Real.log (coldImageIntegral R (perturb c X τ (trivialField n))) -
        Real.log (coldImageIntegral R (trivialField n)) := by
    unfold goodFieldLogIntegral
    rw [dif_neg (NeZero.ne n)]
  have hL1 : Real.log (coldImageIntegral R (perturb c X τ (trivialField n))) = Real.log (imagePrefactor R n) -
      R.coupling * minimalActionTotal R.params.coupling R.params.side (R.depth + 1) n (perturb c X τ (trivialField n)) +
      Real.log (integralAboveMinimizer R T.ballRadius T.cutoff (perturb c X τ (trivialField n))) := by
    rw [hI, Real.log_mul (mul_ne_zero hnum (Real.exp_pos _).ne') hJ.ne',
      Real.log_mul hnum (Real.exp_pos _).ne', Real.log_exp]
    ring
  unfold laplaceRemainder
  rw [hcut, hlog, hL1]
  ring
end RunningCouplingSlope
end YangMills.Construction
end
