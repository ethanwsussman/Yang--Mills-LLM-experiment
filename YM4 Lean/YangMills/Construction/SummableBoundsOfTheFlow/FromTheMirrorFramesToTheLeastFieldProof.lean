import YangMills.Construction.ClusterExpansionOfAStep.SlopeOfTheLogOfASettingProof
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinatesProof
import YangMills.Construction.ColdStepAtMirrorFrames.PlainChainAtLevelZeroProof
import YangMills.Construction.SummableBoundsOfTheFlow.DensityBelowASizeAtOnePlane
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfADensityOnTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.FramesVanishAtTheFlatField
import YangMills.Construction.SummableBoundsOfTheFlow.FreezingOfTheGapObservable
import YangMills.Construction.SummableBoundsOfTheFlow.FromTheMirrorFramesToTheLeastField
import YangMills.Construction.SummableBoundsOfTheFlow.LawOfACutIsAProbability
import YangMills.Construction.SummableBoundsOfTheFlow.LogarithmAlongAMovingCut
import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheGapAreDominated
import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheGapAreInvariant
import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheGapDecay
import YangMills.Construction.SummableBoundsOfTheFlow.MoveOfTheTopAlongItsFieldProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheFramesBetween
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology
open MeasureTheory Set
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation Estimates ConvexObservables FamilyNorms
  DerivativeInterpolation BlockMeans TorusFreezing SummableBounds
namespace FrameInterpolationProof
variable {F : BlockFrame}
theorem toImaginary_imaginaryCoords (w : imaginaryQuaternions) : toImaginary (imaginaryCoords w) = w := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_imaginaryCoords <;> assumption
theorem imaginaryCoords_toImaginary (v : BondVector) : imaginaryCoords (toImaginary v) = v := by
  ext i
  fin_cases i <;> simp [toImaginary, imaginaryCoords]
theorem toImaginary_injective : Function.Injective toImaginary :=
  Function.LeftInverse.injective imaginaryCoords_toImaginary
theorem toImaginary_add (u v : BondVector) : toImaginary (u + v) = toImaginary u + toImaginary v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.toImaginary_add <;> assumption
theorem toImaginary_smul (c : ℝ) (v : BondVector) : toImaginary (c • v) = c • toImaginary v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.toImaginary_smul <;> assumption
theorem toImaginary_sub (u v : BondVector) : toImaginary (u - v) = toImaginary u - toImaginary v := by
  have h := toImaginary_add (u - v) v
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm
theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
theorem inner_toImaginary (v : BondVector) (w : imaginaryQuaternions) :
    ⟪((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]), (w : ℍ[ℝ])⟫ = ⟪v, imaginaryCoords w⟫ := by
  rw [Quaternion.inner_def, Quaternion.re_mul]
  simp [toImaginary, imaginaryCoords, PiLp.inner_apply, Fin.sum_univ_three]
  ring
theorem haarLaplace_pos (s : ℝ) : 0 < haarLaplace s := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianSlope.haarLaplace_pos <;> assumption
theorem haarCharacterMean_pos (s : ℝ) : 0 < haarCharacterMean s :=
  mul_pos (Real.exp_pos s) (haarLaplace_pos s)
theorem stepKernel_eq_exp (a x : ℝ) (W : F.GaugeField F.depth) (V : F.GaugeField F.top)
    (c : F.Site F.top × Fin 4) :
    stepKernel a x W V c =
      Real.exp (- (a * x) * blockFit W V c + haarGap (a * x * ‖contourAverage W c‖)) := by
  have hz := haarCharacterMean_pos (a * x * ‖contourAverage W c‖)
  unfold stepKernel blockFit haarGap
  rw [div_eq_mul_inv, ← Real.exp_log hz, ← Real.exp_neg, ← Real.exp_add, Real.log_exp]
  congr 1
  ring
theorem haarRadialDensity_zero_pos : 0 < haarRadialDensity 0 := by
  unfold haarRadialDensity
  rw [if_pos Real.pi_pos]
  simp only [Real.sinc_zero]
  have := Real.pi_pos
  positivity
theorem haarRadialDensity_pos {u : ℝ} (h0 : 0 ≤ u) (h1 : u < Real.pi) : 0 < haarRadialDensity u := by
  unfold haarRadialDensity
  rw [if_pos h1]
  have hs : Real.sinc u ≠ 0 := by
    rcases h0.lt_or_eq with h | h
    · rw [Real.sinc_of_ne_zero h.ne']
      exact (div_pos (Real.sin_pos_of_pos_of_lt_pi h h1) h).ne'
    · rw [← h, Real.sinc_zero]
      exact one_ne_zero
  positivity
def interpolatedFrameVector (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    StepVariable (finiteCells F) :=
  fun b => imaginaryCoords (interpolatedFrame s a ρA m b.1 V)
def frameGapVector (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) : StepVariable (finiteCells F) :=
  fun b => imaginaryCoords (frameGap a ρA m b.1 V)
theorem interpolatedFrameVector_eq (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    interpolatedFrameVector s a ρA m V =
      interpolatedFrameVector 0 a ρA m V + s • frameGapVector a ρA m V := by
  funext b
  apply toImaginary_injective
  simp only [Pi.add_apply, Pi.smul_apply, toImaginary_add, toImaginary_smul, interpolatedFrameVector,
    frameGapVector, toImaginary_imaginaryCoords, interpolatedFrame, frameGap]
  module
theorem norm_sub_toImaginary (w fr : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F)))
    (f : imaginaryQuaternions) (hf : fr b = imaginaryCoords f) :
    ‖((toImaginary (w b) : imaginaryQuaternions) : ℍ[ℝ]) - (f : imaginaryQuaternions)‖ = ‖(w - fr) b‖ := by
  have e : ((toImaginary (w b) : imaginaryQuaternions) : ℍ[ℝ]) - (f : imaginaryQuaternions) =
      ((toImaginary ((w - fr) b) : imaginaryQuaternions) : ℍ[ℝ]) := by
    rw [Pi.sub_apply, toImaginary_sub, hf, toImaginary_imaginaryCoords]
    rfl
  rw [e, ← norm_toImaginary]
  rfl
def uncutIntegrand (a x : ℝ) (φ : LocalFamily) (V : F.GaugeField F.top)
    (w : StepVariable (finiteCells F)) : ℝ :=
  lowerBoltzmann a x φ (finiteCells F) (chartedField (stepCoordinates w) V) *
    (∏ c ∈ innerBonds (finiteCells F) F.top,
      stepKernel a x (chartedField (stepCoordinates w) V) V c) *
    ∏ b : ↥(chordBonds (finiteCells F)), haarLogDensity (w b)
theorem interpolatedStepIntegrand_eq (s a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ : LocalFamily)
    (V : F.GaugeField F.top) (w : StepVariable (finiteCells F)) :
    interpolatedStepIntegrand s a ρA ρ x m p φ V w =
      uncutIntegrand a x φ V w *
        radialWeightProd (cutoffFactor ρ p) (w - interpolatedFrameVector s a ρA m V) := by
  have h : ∏ b : ↥(chordBonds (finiteCells F)), cutoffFactor ρ p
      ‖((toImaginary (w b) : imaginaryQuaternions) : ℍ[ℝ]) -
        (interpolatedFrame s a ρA m b.1 V : imaginaryQuaternions)‖ =
      radialWeightProd (cutoffFactor ρ p) (w - interpolatedFrameVector s a ρA m V) :=
    Finset.prod_congr rfl fun b _ => by
      rw [norm_sub_toImaginary w (interpolatedFrameVector s a ρA m V) b _ rfl]
  unfold interpolatedStepIntegrand uncutIntegrand
  rw [h]
  ring
def integrandConstant (s a ρA x : ℝ) (m : ℕ) (V : F.GaugeField F.top) : ℝ :=
  Real.exp (∑ _c ∈ innerBonds (finiteCells F) F.top, haarGap (a * x)) *
    (∏ _b : ↥(chordBonds (finiteCells F)), haarRadialDensity 0) *
    Real.exp (- x * chartedEnergy a (interpolatedCoords s a ρA m V 0) V)
theorem integrandConstant_pos (s a ρA x : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    0 < integrandConstant s a ρA x m V :=
  mul_pos (mul_pos (Real.exp_pos _) (Finset.prod_pos fun _ _ => haarRadialDensity_zero_pos))
    (Real.exp_pos _)
theorem interpolatedStepIntegrand_add_frame (hcover : BlocksCoverLowerLevel) (s a ρA ρ x : ℝ) (m : ℕ)
    (p : ℝ → ℝ) (φ : LocalFamily) (V : F.GaugeField F.top) (hodd : Odd F.blockSide)
    (hside : ∀ i, 0 < F.extent i)
    (hframe : ∀ b ∈ chordBonds (finiteCells F), ‖interpolatedFrame s a ρA m b V‖ + ρ < Real.pi)
    (η : StepVariable (finiteCells F)) :
    interpolatedStepIntegrand s a ρA ρ x m p φ V (η + interpolatedFrameVector s a ρA m V) =
      integrandConstant s a ρA x m V *
        (cutoffWeight ρ p η * Real.exp (- familyLawExponent s a ρA x m φ V η)) := by
  classical
  set fr : StepVariable (finiteCells F) := interpolatedFrameVector s a ρA m V with hfr
  have hcov := hcover F hodd hside
  have hchart : ∀ b : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond b → b ∈ chordBonds (finiteCells F) := by
    intro b hb
    unfold chordBonds innerBonds
    rw [Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨Finset.mem_product.mpr ⟨hcov _, Finset.mem_univ _⟩, hcov _⟩, hb⟩
  have hW : chartedField (stepCoordinates (η + fr)) V = interpolatedField s a ρA m V η := by
    funext z i
    unfold interpolatedField chartedField
    have key : ¬ IsAxialTreeBond (z, i) → stepCoordinates (η + fr) z i =
        interpolatedCoords s a ρA m V η z i := by
      intro ht
      have hb := hchart (z, i) ht
      simp only [stepCoordinates, interpolatedCoords, dif_pos hb, Pi.add_apply, toImaginary_add, hfr,
        interpolatedFrameVector, toImaginary_imaginaryCoords]
      rw [add_comm]
    by_cases hc : IsCrossingBond (z, i)
    · rw [if_pos hc, if_pos hc, key fun ht => ht.1 hc]
    · rw [if_neg hc, if_neg hc]
      by_cases ht : IsAxialTreeBond (z, i)
      · rw [if_pos ht, if_pos ht]
      · rw [if_neg ht, if_neg ht, key ht]
  have hcut : ∀ b : ↥(chordBonds (finiteCells F)),
      ‖((toImaginary ((η + fr) b) : imaginaryQuaternions) : ℍ[ℝ]) -
        (interpolatedFrame s a ρA m b.1 V : imaginaryQuaternions)‖ = ‖η b‖ := by
    intro b
    rw [norm_sub_toImaginary (η + fr) fr b _ rfl]
    simp
  unfold interpolatedStepIntegrand
  rw [hW]
  simp only [hcut]
  change lowerBoltzmann a x φ (finiteCells F) (interpolatedField s a ρA m V η) *
    cutoffWeight ρ p η * _ * _ = _
  by_cases hR : ∀ b : ↥(chordBonds (finiteCells F)), ‖η b‖ < ρ
  · set W := interpolatedField s a ρA m V η with hWdef
    have hk : ∏ c ∈ innerBonds (finiteCells F) F.top, stepKernel a x W V c =
        Real.exp (- (a * x) * (∑ c ∈ innerBonds (finiteCells F) F.top, blockFit W V c) +
          ∑ c ∈ innerBonds (finiteCells F) F.top, haarGap (a * x * ‖contourAverage W c‖)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Real.exp_sum]
      exact Finset.prod_congr rfl fun c _ => stepKernel_eq_exp a x W V c
    have hJ : ∏ b : ↥(chordBonds (finiteCells F)), haarLogDensity ((η + fr) b) =
        (∏ _b : ↥(chordBonds (finiteCells F)), haarRadialDensity 0) *
          Real.exp (∑ b : ↥(chordBonds (finiteCells F)),
            haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2)) := by
      rw [Real.exp_sum, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro b _
      have e1 : interpolatedCoords s a ρA m V η b.1.1 b.1.2 = toImaginary ((η + fr) b) := by
        have hb : (b.1.1, b.1.2) ∈ chordBonds (finiteCells F) := b.2
        simp only [interpolatedCoords, stepCoordinates, dif_pos hb, Pi.add_apply, toImaginary_add, hfr,
          interpolatedFrameVector, toImaginary_imaginaryCoords]
        rw [add_comm]
      have hlt : ‖(η + fr) b‖ < Real.pi := by
        have h1 : ‖(η + fr) b‖ ≤ ‖η b‖ + ‖fr b‖ := norm_add_le _ _
        have h2 : ‖fr b‖ = ‖interpolatedFrame s a ρA m b.1 V‖ := by
          rw [← norm_toImaginary, hfr]
          simp only [interpolatedFrameVector, toImaginary_imaginaryCoords]
        have h3 := hframe b.1 b.2
        have h4 := hR b
        linarith
      have hpos := haarRadialDensity_pos (norm_nonneg ((η + fr) b)) hlt
      have h0 := haarRadialDensity_zero_pos
      unfold haarLogRatio
      rw [e1, norm_toImaginary, Real.exp_log (div_pos hpos h0)]
      have e2 : haarLogDensity ((η + fr) b) = haarRadialDensity ‖(η + fr) b‖ := rfl
      rw [e2]
      field_simp
    rw [hk, hJ]
    set A := minimalAction a (finiteCells F) F.depth W with hA
    set Sf := ∑ c ∈ innerBonds (finiteCells F) F.top, blockFit W V c with hSf
    set Om := ∑ c ∈ innerBonds (finiteCells F) F.top, haarGap (a * x * ‖contourAverage W c‖) with hOm
    set Om0 := ∑ _c ∈ innerBonds (finiteCells F) F.top, haarGap (a * x) with hOm0
    set Hx := ∑ b : ↥(chordBonds (finiteCells F)),
      haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) with hHx
    set Ff := ∑ y ∈ sitesOfCells (finiteCells F) F.depth, subtractTrivial φ F y W with hFf
    set S0 := chartedEnergy a (interpolatedCoords s a ρA m V 0) V with hS0
    set J := ∏ _b : ↥(chordBonds (finiteCells F)), haarRadialDensity 0 with hJ0
    set R := cutoffWeight ρ p η with hRw
    have hΨ : familyLawExponent s a ρA x m φ V η = x * (A + a * Sf - S0) - (Om - Om0) - Hx - Ff := by
      have e1 : chartedEnergy a (interpolatedCoords s a ρA m V η) V = A + a * Sf := rfl
      have e2 : ∑ c ∈ innerBonds (finiteCells F) F.top,
          haarGapExcess a x (interpolatedField s a ρA m V η) c = Om - Om0 := by
        simp only [haarGapExcess]
        rw [Finset.sum_sub_distrib]
      unfold familyLawExponent interpolatedExponent
      rw [e1, e2]
      rfl
    have hlw : lowerBoltzmann a x φ (finiteCells F) W = Real.exp (- x * A + Ff) := rfl
    rw [hΨ, hlw]
    unfold integrandConstant
    have hsum : - x * A + Ff + (- (a * x) * Sf + Om) + Hx =
        Om0 + - x * S0 + -(x * (A + a * Sf - S0) - (Om - Om0) - Hx - Ff) := by ring
    calc Real.exp (- x * A + Ff) * R * Real.exp (- (a * x) * Sf + Om) * (J * Real.exp Hx)
        = R * J * (Real.exp (- x * A + Ff) * Real.exp (- (a * x) * Sf + Om) * Real.exp Hx) := by
          ring
      _ = R * J * Real.exp (- x * A + Ff + (- (a * x) * Sf + Om) + Hx) := by
          rw [Real.exp_add (- x * A + Ff + (- (a * x) * Sf + Om)) Hx,
            Real.exp_add (- x * A + Ff) (- (a * x) * Sf + Om)]
      _ = R * J * Real.exp (Om0 + - x * S0 +
            -(x * (A + a * Sf - S0) - (Om - Om0) - Hx - Ff)) := by rw [hsum]
      _ = Real.exp Om0 * J * Real.exp (- x * S0) *
            (R * Real.exp (-(x * (A + a * Sf - S0) - (Om - Om0) - Hx - Ff))) := by
          rw [Real.exp_add (Om0 + - x * S0), Real.exp_add Om0 (- x * S0)]
          ring
  · push Not at hR
    obtain ⟨b, hb⟩ := hR
    have h0 : cutoffWeight ρ p η = 0 := by
      unfold cutoffWeight
      apply Finset.prod_eq_zero (Finset.mem_univ b)
      unfold cutoffFactor
      rw [if_neg (not_lt.mpr hb)]
    rw [h0]
    simp
theorem familyLawExponent_local (T : StepParameters) {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {t : ℕ}
    {x : ℝ} (h : InterpolatedFrameBoundsAt T Cq Cz Cr t x) (V : F.GaugeField F.top) (s : ℝ)
    (φ : LocalFamily) (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) (h0 : 0 ≤ s) (h1 : s ≤ 1)
    (hφ : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ) :
    ∃ Ψ : StepVariable (finiteCells F) → ℝ, ContDiff ℝ 3 Ψ ∧
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V η = Ψ η) ∧
      ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
          |bondPartialDeriv Ψ b η e| ≤ T.Ct * x * ‖e‖ := by
  classical
  let d : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ :=
    fun i i' => cellSupDist (enclosingCell i.1.1) (enclosingCell i'.1.1)
  let M : LawOnBondVariables ↥(chordBonds (finiteCells F)) :=
    ⟨F, V, id, Finset.univ, familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V⟩
  have hadm : M.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t
      T.n₀ (frameRadius x) d :=
    ⟨hF, hV, .ofFamily s φ h0 h1 hφ, Function.injective_id, fun _ _ => rfl⟩
  have hl := (h.laws _ d 1 (fun _ => 1) (fun _ => M) ⟨fun _ => zero_le_one, by simp⟩
    (fun _ => hadm)).1
  obtain ⟨Ψ, K, hagree, hconv, -, hslope⟩ := hl
  have hpush : ∀ ζ : StepVariable (finiteCells F), _root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ ζ = ζ := by
    intro ζ
    funext b
    simp [_root_.YangMills.Construction.Interpolation.extendByZero]
  have hmix : ∀ ζ, convexCombinationExponent T.chainParams.lam x (fun _ : Fin 1 => (1 : ℝ)) (fun _ => M) ζ =
      familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V ζ := by
    intro ζ
    have e1 : M.exponent T.chainParams.lam x ζ =
        familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V ζ := by
      show familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V
          (_root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ ζ) +
        ∑ i ∈ Finset.univ \ Finset.univ, x * T.chainParams.lam / 2 * ‖ζ i‖ ^ 2 = _
      rw [hpush, Finset.sdiff_self, Finset.sum_empty, add_zero]
    simp [convexCombinationExponent, e1]
  exact ⟨Ψ, hconv.smooth, fun η hη => by rw [← hmix, ← hagree η hη], hslope⟩
theorem abs_sub_le_of_partial_bound {ι : Type} [Fintype ι] [DecidableEq ι] {ρ C : ℝ} (hρ : 0 < ρ)
    {Ψ : BondField ι → ℝ} (hΨ : ContDiff ℝ 3 Ψ) (hC : 0 ≤ C)
    (hs : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ (b : ι) (e : BondVector),
      |bondPartialDeriv Ψ b η e| ≤ C * ‖e‖)
    {η ζ : BondField ι} (hη : ∀ b, ‖η b‖ < ρ) (hζ : ∀ b, ‖ζ b‖ < ρ) :
    |Ψ η - Ψ ζ| ≤ Fintype.card ι * C * ‖η - ζ‖ := by
  have hmem : ∀ ξ : BondField ι, (∀ b, ‖ξ b‖ < ρ) ↔ ξ ∈ Metric.ball (0 : BondField ι) ρ := by
    intro ξ
    rw [mem_ball_zero_iff, pi_norm_lt_iff hρ]
  have hdiff : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hd : ∀ ξ ∈ Metric.ball (0 : BondField ι) ρ, ‖fderiv ℝ Ψ ξ‖ ≤ Fintype.card ι * C := by
    intro ξ hξ
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    have hu : u = ∑ b, bondVariation b (u b) := by
      unfold bondVariation
      exact (Finset.univ_sum_single u).symm
    have h1 : fderiv ℝ Ψ ξ u = ∑ b, bondPartialDeriv Ψ b ξ (u b) := by
      conv_lhs => rw [hu]
      rw [map_sum]
      rfl
    rw [h1]
    calc ‖∑ b, bondPartialDeriv Ψ b ξ (u b)‖ ≤ ∑ b, ‖bondPartialDeriv Ψ b ξ (u b)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _b : ι, C * ‖u‖ := Finset.sum_le_sum fun b _ => by
          rw [Real.norm_eq_abs]
          exact (hs ξ ((hmem ξ).mpr hξ) b (u b)).trans
            (mul_le_mul_of_nonneg_left (norm_le_pi_norm u b) hC)
      _ = Fintype.card ι * C * ‖u‖ := by
          simp [Finset.card_univ]
          ring
  have := (convex_ball (0 : BondField ι) ρ).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hdiff z) hd ((hmem ζ).mp hζ) ((hmem η).mp hη)
  simpa [Real.norm_eq_abs] using this
def cellGapVector (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) (Y : F.Cell) :
    StepVariable (finiteCells F) :=
  fun b => if enclosingCell b.1.1 = Y then frameGapVector a ρA m V b else 0
theorem blockGapObservable_eq_cutoffSlope (a ρA : ℝ) (m : ℕ) (p : ℝ → ℝ) (Y : F.Cell)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    blockGapObservable a ρA m p Y V η = cutoffSlope p (cellGapVector a ρA m V Y) η := by
  unfold blockGapObservable cutoffSlope cellGapVector
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [inner_toImaginary]
    rfl
  · simp
theorem sum_blockGapObservable (hmem : ∀ Y : F.Cell, Y ∈ finiteCells F) (a ρA : ℝ) (m : ℕ)
    (p : ℝ → ℝ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    ∑ Y ∈ finiteCells F, blockGapObservable a ρA m p Y V η =
      cutoffSlope p (frameGapVector a ρA m V) η := by
  simp only [blockGapObservable_eq_cutoffSlope]
  unfold cutoffSlope
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (enclosingCell b.1.1)]
  · simp [cellGapVector]
  · intro Y _ hY
    simp [cellGapVector, Ne.symm hY]
  · intro h
    exact absurd (hmem _) h
theorem cutoffWeight_pos {ρ : ℝ} {p : ℝ → ℝ} {η : StepVariable (finiteCells F)}
    (hη : ∀ b, ‖η b‖ < ρ) : 0 < cutoffWeight ρ p η := by
  unfold cutoffWeight
  refine Finset.prod_pos fun b _ => ?_
  unfold cutoffFactor
  rw [if_pos (hη b)]
  exact Real.exp_pos _
theorem cutoffWeight_eq_zero {ρ : ℝ} {p : ℝ → ℝ} {η : StepVariable (finiteCells F)}
    (hη : ¬ ∀ b, ‖η b‖ < ρ) : cutoffWeight ρ p η = 0 := by
  push Not at hη
  obtain ⟨b, hb⟩ := hη
  unfold cutoffWeight
  apply Finset.prod_eq_zero (Finset.mem_univ b)
  unfold cutoffFactor
  rw [if_neg (not_lt.mpr hb)]
theorem log_stepIntegral_eq (hcover : BlocksCoverLowerLevel)
    (hmove : logShiftedCutoffIntegralStatement) (hlawc : normalizedBallLawIsProbabilityStatement)
    (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ : LocalFamily) (V : F.GaugeField F.top) (C : ℝ)
    (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hodd : Odd F.blockSide) (hside : ∀ i, 0 < F.extent i)
    (hC : 0 ≤ C)
    (hframe : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ b ∈ chordBonds (finiteCells F),
      ‖interpolatedFrame s a ρA m b V‖ + ρ < Real.pi)
    (hlaw : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∃ Ψ : StepVariable (finiteCells F) → ℝ, ContDiff ℝ 3 Ψ ∧
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
        familyLawExponent s a ρA x m φ V η = Ψ η) ∧
      ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
        ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
          |bondPartialDeriv Ψ b η e| ≤ C * ‖e‖) :
    BlockGapIntegrable a ρA ρ x m p φ V ∧
      Real.log (stepIntegral a ρA ρ x m p φ (finiteCells F) V) =
        Real.log (interpolatedStepIntegral 0 a ρA ρ x m p φ V) +
          ∑ Y ∈ finiteCells F, blockGapDensity a ρA ρ x m p φ F Y V := by
  classical
  have hcov := hcover F hodd hside
  have hmem : ∀ Y : F.Cell, Y ∈ finiteCells F := by
    have hne : (finiteCells F).Nonempty := by
      have h0 := hcov 0
      unfold sitesOfCells at h0
      obtain ⟨z, hz, -⟩ := Finset.mem_biUnion.mp h0
      exact ⟨z, hz⟩
    intro Y
    unfold finiteCells at hne ⊢
    split_ifs at hne ⊢ with h
    · exact @Finset.mem_univ _ (Fintype.ofFinite _) Y
    · simp at hne
  set fr0 := interpolatedFrameVector 0 a ρA m V with hfr0
  set d := frameGapVector a ρA m V with hd
  have hfr : ∀ s, interpolatedFrameVector s a ρA m V = fr0 + s • d := fun s =>
    interpolatedFrameVector_eq s a ρA m V
  set G := uncutIntegrand a x φ V with hGdef
  let Kc : ℝ → ℝ := fun s => integrandConstant s a ρA x m V
  have hKc : ∀ s, 0 < Kc s := fun s => integrandConstant_pos s a ρA x m V
  let dens : ℝ → StepVariable (finiteCells F) → ℝ := fun s η =>
    cutoffWeight ρ p η * Real.exp (- familyLawExponent s a ρA x m φ V η)
  have hshift : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ η, interpolatedStepIntegrand s a ρA ρ x m p φ V
      (η + interpolatedFrameVector s a ρA m V) = Kc s * dens s η := fun s h0 h1 η =>
    interpolatedStepIntegrand_add_frame hcover s a ρA ρ x m p φ V hodd hside (hframe s h0 h1) η
  have hGη : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ η, G (η + interpolatedFrameVector s a ρA m V) *
      radialWeightProd (cutoffFactor ρ p) η = Kc s * dens s η := by
    intro s h0 h1 η
    rw [← hshift s h0 h1 η, interpolatedStepIntegrand_eq, add_sub_cancel_right]
  choose! Ψ hΨ hag hsl using hlaw
  have hdensΨ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → dens s = ballDensity (cutoffFactor ρ p) (Ψ s) := by
    intro s h0 h1
    funext η
    show cutoffWeight ρ p η * Real.exp (- familyLawExponent s a ρA x m φ V η) =
      cutoffWeight ρ p η * Real.exp (- Ψ s η)
    by_cases hη : ∀ b, ‖η b‖ < ρ
    · rw [hag s h0 h1 η hη]
    · rw [cutoffWeight_eq_zero hη]
      simp
  have hint : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → Integrable (dens s) ∧ 0 < ∫ η, dens s η := by
    intro s h0 h1
    obtain ⟨-, -, -, -, -, -, h7, h8, -⟩ := hlawc _ ρ p (Ψ s) hρ hp (hΨ s h0 h1).continuous
    rw [hdensΨ s h0 h1]
    exact ⟨h7, h8⟩
  have hIntg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      Integrable (interpolatedStepIntegrand s a ρA ρ x m p φ V) := by
    intro s h0 h1
    have h1' : Integrable (fun η => interpolatedStepIntegrand s a ρA ρ x m p φ V
        (η + interpolatedFrameVector s a ρA m V)) :=
      ((hint s h0 h1).1.const_mul (Kc s)).congr
        (Filter.Eventually.of_forall fun η => (hshift s h0 h1 η).symm)
    have h2 := h1'.comp_add_right (-(interpolatedFrameVector s a ρA m V))
    simpa using h2
  have hval : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → interpolatedStepIntegral s a ρA ρ x m p φ V =
      Kc s * ∫ η, dens s η := by
    intro s h0 h1
    unfold interpolatedStepIntegral
    rw [← integral_add_right_eq_self _ (interpolatedFrameVector s a ρA m V), ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => hshift s h0 h1 η)
  have hpos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < interpolatedStepIntegral s a ρA ρ x m p φ V := by
    intro s h0 h1
    rw [hval s h0 h1]
    exact mul_pos (hKc s) (hint s h0 h1).2
  have hGe : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      G (η + interpolatedFrameVector s a ρA m V) = Kc s * Real.exp (- Ψ s η) := by
    intro s h0 h1 η hη
    have hR := cutoffWeight_pos (ρ := ρ) (p := p) hη
    have e : G (η + interpolatedFrameVector s a ρA m V) * cutoffWeight ρ p η =
        (Kc s * Real.exp (- Ψ s η)) * cutoffWeight ρ p η := by
      have h := hGη s h0 h1 η
      have h' : G (η + interpolatedFrameVector s a ρA m V) * cutoffWeight ρ p η = Kc s * dens s η := h
      rw [h']
      show Kc s * (cutoffWeight ρ p η * Real.exp (- familyLawExponent s a ρA x m φ V η)) = _
      rw [hag s h0 h1 η hη]
      ring
    exact mul_right_cancel₀ hR.ne' e
  have hb0 : ∀ b : ↥(chordBonds (finiteCells F)), ‖(0 : StepVariable (finiteCells F)) b‖ < ρ := by
    intro b
    simpa using hρ
  set Lp : ℝ := (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * C with hLp
  have hLp0 : 0 ≤ Lp := by positivity
  set E : ℝ := Real.exp (Lp * ρ) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  let g : ℝ → ℝ := fun s => G (interpolatedFrameVector s a ρA m V)
  have hgpos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < g s := by
    intro s h0 h1
    have h := hGe s h0 h1 0 hb0
    rw [zero_add] at h
    show 0 < G (interpolatedFrameVector s a ρA m V)
    rw [h]
    exact mul_pos (hKc s) (Real.exp_pos _)
  have hL : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      G (η + interpolatedFrameVector s a ρA m V) ≤ g s * E := by
    intro s h0 h1 η hη
    have hz := hGe s h0 h1 0 hb0
    rw [zero_add] at hz
    show _ ≤ G (interpolatedFrameVector s a ρA m V) * E
    rw [hGe s h0 h1 η hη, hz, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hKc s).le
    have hl : |Ψ s η - Ψ s 0| ≤ Lp * ‖η - 0‖ :=
      abs_sub_le_of_partial_bound hρ (hΨ s h0 h1) hC (hsl s h0 h1) hη hb0
    rw [sub_zero] at hl
    have hn : ‖η‖ ≤ ρ := (pi_norm_le_iff_of_nonneg hρ.le).mpr fun b => (hη b).le
    have h3 : Lp * ‖η‖ ≤ Lp * ρ := mul_le_mul_of_nonneg_left hn hLp0
    rw [hE, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h4 := (abs_le.mp hl).1
    linarith
  set h : ℝ := ρ / (2 * (‖d‖ + 1)) with hh
  have hh0 : 0 < h := by positivity
  have hhd : h * ‖d‖ < ρ := by
    rw [hh, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg d]
  have hg : ∀ (j : ℕ) (s : ℝ), 0 ≤ s → s ≤ 1 → s ≤ j * h → g s ≤ g 0 * E ^ j := by
    intro j
    induction j with
    | zero =>
      intro s h0 h1 hs
      have : s = 0 := le_antisymm (by simpa using hs) h0
      subst this
      simp
    | succ j ih =>
      intro s h0 h1 hs
      have hg0 := hgpos 0 le_rfl zero_le_one
      by_cases hc : s ≤ j * h
      · refine (ih s h0 h1 hc).trans (mul_le_mul_of_nonneg_left ?_ hg0.le)
        exact pow_le_pow_right₀ hE1 (Nat.le_succ j)
      · push Not at hc
        set s' : ℝ := max (s - h) 0 with hs'
        have a0 : 0 ≤ s' := le_max_right _ _
        have a1 : s' ≤ 1 := max_le (by linarith) zero_le_one
        have a2 : s' ≤ j * h := by
          refine max_le ?_ (by positivity)
          push_cast at hs
          linarith
        have a3 : |s - s'| ≤ h := by
          rw [abs_le]
          have b1 : s - h ≤ s' := le_max_left _ _
          constructor <;> linarith
        have hbal : ∀ b, ‖((s - s') • d) b‖ < ρ := by
          intro b
          have c1 : ‖((s - s') • d) b‖ ≤ ‖(s - s') • d‖ := norm_le_pi_norm _ b
          rw [norm_smul, Real.norm_eq_abs] at c1
          have c2 : |s - s'| * ‖d‖ ≤ h * ‖d‖ := mul_le_mul_of_nonneg_right a3 (norm_nonneg _)
          linarith
        have hw : interpolatedFrameVector s a ρA m V =
            (s - s') • d + interpolatedFrameVector s' a ρA m V := by
          rw [hfr s, hfr s']
          module
        have e1 := hL s' a0 a1 _ hbal
        rw [← hw] at e1
        have e2 := ih s' a0 a1 a2
        calc g s ≤ g s' * E := e1
          _ ≤ g 0 * E ^ j * E := mul_le_mul_of_nonneg_right e2 (by positivity)
          _ = g 0 * E ^ (j + 1) := by rw [pow_succ]; ring
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / h)
  have hn' : (1 : ℝ) ≤ n * h := by
    rw [div_le_iff₀ hh0] at hn
    exact hn
  set M : ℝ := g 0 * E ^ n * E with hM
  have hGb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ w : StepVariable (finiteCells F),
      (∀ b, ‖(w - (fr0 + s • d)) b‖ < ρ) → |G w| ≤ M := by
    intro s hs w hw
    have hw' : w = (w - (fr0 + s • d)) + interpolatedFrameVector s a ρA m V := by
      rw [hfr]
      abel
    have e1 := hL s hs.1 hs.2 _ hw
    rw [← hw'] at e1
    have e2 := hg n s hs.1 hs.2 (hs.2.trans hn')
    have e3 := hGe s hs.1 hs.2 _ hw
    rw [← hw'] at e3
    have e4 : 0 < G w := by
      rw [e3]
      exact mul_pos (hKc s) (Real.exp_pos _)
    rw [abs_of_pos e4]
    exact e1.trans (mul_le_mul_of_nonneg_right e2 (by positivity))
  have hzeq : ∀ s, shiftedCutoffIntegral ρ p G fr0 d s =
      interpolatedStepIntegral s a ρA ρ x m p φ V := by
    intro s
    unfold shiftedCutoffIntegral interpolatedStepIntegral
    congr 1
    funext w
    rw [interpolatedStepIntegrand_eq, hfr]
  have A := hmove ↥(chordBonds (finiteCells F)) ρ p G fr0 d M hρ hp
    (fun s hs => by
      have e : (fun w => G w * radialWeightProd (cutoffFactor ρ p) (w - (fr0 + s • d))) =
          interpolatedStepIntegrand s a ρA ρ x m p φ V := by
        funext w
        rw [interpolatedStepIntegrand_eq, hfr]
      rw [e]
      exact (hIntg s hs.1 hs.2).aestronglyMeasurable)
    hGb (fun s hs => by rw [hzeq]; exact hpos s hs.1 hs.2)
  obtain ⟨A1, A2, A3⟩ := A
  have hsl2 : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ e : StepVariable (finiteCells F),
      shiftedCutoffSlopeIntegral ρ p G fr0 d e s = Kc s * ∫ η, cutoffSlope p e η * dens s η := by
    intro s h0 h1 e
    unfold shiftedCutoffSlopeIntegral
    rw [← integral_add_right_eq_self _ (interpolatedFrameVector s a ρA m V), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    have e1 : η + interpolatedFrameVector s a ρA m V - (fr0 + s • d) = η := by
      rw [hfr]
      abel
    show G (η + interpolatedFrameVector s a ρA m V) *
        (cutoffSlope p e (η + interpolatedFrameVector s a ρA m V - (fr0 + s • d)) *
          radialWeightProd (cutoffFactor ρ p)
            (η + interpolatedFrameVector s a ρA m V - (fr0 + s • d))) = _
    rw [e1]
    have h2 := hGη s h0 h1 η
    calc G (η + interpolatedFrameVector s a ρA m V) *
          (cutoffSlope p e η * radialWeightProd (cutoffFactor ρ p) η)
        = cutoffSlope p e η *
            (G (η + interpolatedFrameVector s a ρA m V) * radialWeightProd (cutoffFactor ρ p) η) := by
          ring
      _ = _ := by
          rw [h2]
          ring
  have hratio : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ e : StepVariable (finiteCells F),
      shiftedCutoffSlopeIntegral ρ p G fr0 d e s / shiftedCutoffIntegral ρ p G fr0 d s =
        (∫ η, cutoffSlope p e η * dens s η) / ∫ η, dens s η := by
    intro s h0 h1 e
    rw [hsl2 s h0 h1, hzeq, hval s h0 h1, mul_div_mul_left _ _ (hKc s).ne']
  have hmean : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ Y : F.Cell, blockGapMean s a ρA ρ x m p φ Y V =
      shiftedCutoffSlopeIntegral ρ p G fr0 d (cellGapVector a ρA m V Y) s /
        shiftedCutoffIntegral ρ p G fr0 d s := by
    intro s h0 h1 Y
    rw [hratio s h0 h1]
    unfold blockGapMean cutoffMean
    simp only [blockGapObservable_eq_cutoffSlope]
    rfl
  have hcontY : ∀ Y : F.Cell, ContinuousOn (fun s => blockGapMean s a ρA ρ x m p φ Y V)
      (Icc (0 : ℝ) 1) := fun Y =>
    (A2 (cellGapVector a ρA m V Y)).congr fun s hs => hmean s hs.1 hs.2 Y
  have hinS : ∀ Y : F.Cell,
      IntervalIntegrable (fun s => blockGapMean s a ρA ρ x m p φ Y V) volume 0 1 :=
    fun Y => (hcontY Y).intervalIntegrable_of_Icc zero_le_one
  have hobs : ∀ (s : ℝ) (Y : F.Cell), 0 ≤ s → s ≤ 1 →
      Integrable (fun η : StepVariable (finiteCells F) => blockGapObservable a ρA m p Y V η *
        (cutoffWeight ρ p η * Real.exp (- familyLawExponent s a ρA x m φ V η))) := by
    intro s Y h0 h1
    have h2 := (A1 (cellGapVector a ρA m V Y) s ⟨h0, h1⟩).comp_add_right
      (interpolatedFrameVector s a ρA m V)
    have h3 := h2.const_mul (Kc s)⁻¹
    refine h3.congr (Filter.Eventually.of_forall fun η => ?_)
    have e1 : η + interpolatedFrameVector s a ρA m V - (fr0 + s • d) = η := by
      rw [hfr]
      abel
    show (Kc s)⁻¹ * (G (η + interpolatedFrameVector s a ρA m V) *
        (cutoffSlope p (cellGapVector a ρA m V Y)
            (η + interpolatedFrameVector s a ρA m V - (fr0 + s • d)) *
          radialWeightProd (cutoffFactor ρ p)
            (η + interpolatedFrameVector s a ρA m V - (fr0 + s • d)))) = _
    rw [e1]
    show _ = blockGapObservable a ρA m p Y V η * dens s η
    rw [blockGapObservable_eq_cutoffSlope]
    have h4 := hGη s h0 h1 η
    have h5 : G (η + interpolatedFrameVector s a ρA m V) * (cutoffSlope p (cellGapVector a ρA m V Y) η *
        radialWeightProd (cutoffFactor ρ p) η) =
          cutoffSlope p (cellGapVector a ρA m V Y) η * (Kc s * dens s η) := by
      rw [← h4]
      ring
    rw [h5]
    have := (hKc s).ne'
    field_simp
  have hread : BlockGapIntegrable a ρA ρ x m p φ V :=
    ⟨hIntg, hpos, fun s h0 h1 => hint s h0 h1, hobs, hinS⟩
  refine ⟨hread, ?_⟩
  have hstep : interpolatedStepIntegral 1 a ρA ρ x m p φ V =
      stepIntegral a ρA ρ x m p φ (finiteCells F) V := by
    have hf : ∀ b : F.Site F.depth × Fin 4,
        interpolatedFrame 1 a ρA m b V = bondFrameCoord a ρA m b V := by
      intro b
      simp [interpolatedFrame, stepFrame]
    unfold interpolatedStepIntegral stepIntegral interpolatedStepIntegrand stepIntegrand
    simp only [hf]
  have hsum : ∀ s ∈ Set.uIcc (0 : ℝ) 1, shiftedCutoffSlopeIntegral ρ p G fr0 d d s /
      shiftedCutoffIntegral ρ p G fr0 d s =
        ∑ Y ∈ finiteCells F, blockGapMean s a ρA ρ x m p φ Y V := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    rw [hratio s hs.1 hs.2]
    unfold blockGapMean cutoffMean
    rw [← Finset.sum_div]
    congr 1
    rw [← integral_finsetSum _ fun Y _ => hobs s Y hs.1 hs.2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show cutoffSlope p d η * dens s η = _
    rw [← sum_blockGapObservable hmem, Finset.sum_mul]
  rw [hzeq 1, hzeq 0, hstep, intervalIntegral.integral_congr hsum,
    intervalIntegral.integral_finsetSum fun Y _ => hinS Y] at A3
  have e : ∑ Y ∈ finiteCells F, blockGapDensity a ρA ρ x m p φ F Y V =
      ∑ Y ∈ finiteCells F, ∫ s in (0 : ℝ)..1, blockGapMean s a ρA ρ x m p φ Y V := rfl
  rw [e]
  linarith
theorem bondDeriv_zero {j : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
theorem intervalIntegral_unit_eq (f : ℝ → ℝ) :
    ∫ s in (0 : ℝ)..1, f s = ∫ s, f s ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
theorem pow_le_mul_exp (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → u ^ k ≤ C * Real.exp (δ * u) := by
  refine ⟨1 + (k.factorial : ℝ) / δ ^ k, by have : 0 ≤ (k.factorial : ℝ) / δ ^ k := by positivity
                                            linarith, fun u hu => ?_⟩
  have h1 := Real.pow_div_factorial_le_exp (δ * u) (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h2 : u ^ k = (k.factorial : ℝ) / δ ^ k * ((δ * u) ^ k / k.factorial) := by
    rw [mul_pow]
    field_simp
  rw [h2]
  have h3 : (0 : ℝ) ≤ (k.factorial : ℝ) / δ ^ k := by positivity
  calc (k.factorial : ℝ) / δ ^ k * ((δ * u) ^ k / k.factorial)
      ≤ (k.factorial : ℝ) / δ ^ k * Real.exp (δ * u) := mul_le_mul_of_nonneg_left h1 h3
    _ ≤ (1 + (k.factorial : ℝ) / δ ^ k) * Real.exp (δ * u) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
theorem torusDecayFactor_le {L : ℕ} (hL : 1 ≤ L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℕ, torusDecayFactor L δ r ≤ C * Real.exp (2 * δ * r) := by
  obtain ⟨C, hC, h⟩ := pow_le_mul_exp 16000 hδ
  refine ⟨C, hC, fun r => ?_⟩
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hl : (1 : ℝ) ≤ (L : ℝ) ^ (1 / 640 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hL) (by norm_num)
  have h1 : ((r : ℝ) / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 ≤ (r : ℝ) ^ 16000 :=
    pow_le_pow_left₀ (by positivity) (div_le_self hr hl) _
  have hE : (1 : ℝ) ≤ Real.exp (δ * r) := Real.one_le_exp (by positivity)
  have h2 : max 1 (((r : ℝ) / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) ≤ C * Real.exp (δ * r) := by
    refine max_le ?_ (h1.trans (h r hr))
    nlinarith
  unfold torusDecayFactor
  calc max 1 (((r : ℝ) / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) * Real.exp (δ * r)
      ≤ C * Real.exp (δ * r) * Real.exp (δ * r) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = C * Real.exp (2 * δ * r) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
theorem torusDecayFactor_pos (L : ℕ) (δ : ℝ) (r : ℕ) : 0 < torusDecayFactor L δ r := by
  unfold torusDecayFactor
  exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
theorem interpolatedSize_le {σ B u : ℝ} {k : ℕ} (hσ : 0 < σ) (hB : 0 < B) (hk1 : 1 ≤ k)
    (hk2 : k ≤ 2) (hu : 0 ≤ u) :
    interpolatedSize σ (B * Real.exp (-(8 * u))) B k ≤
      B * ((1 + 64 / σ) ^ 2 + 1) * Real.exp (-(2 * u)) := by
  unfold interpolatedSize
  have hk : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
  have hc : (1 : ℝ) ≤ 1 + 64 / σ := by
    have : 0 < 64 / σ := by positivity
    linarith
  have h1 : B * Real.exp (-(8 * u)) / (σ / 64) ^ k ≤
      B * (1 + 64 / σ) ^ 2 * Real.exp (-(2 * u)) := by
    have e1 : B * Real.exp (-(8 * u)) / (σ / 64) ^ k = B * (64 / σ) ^ k * Real.exp (-(8 * u)) := by
      rw [div_pow, div_pow]
      field_simp
    rw [e1]
    have e2 : (64 / σ) ^ k ≤ (1 + 64 / σ) ^ 2 :=
      (pow_le_pow_left₀ (by positivity) (by linarith) k).trans (pow_le_pow_right₀ hc hk2)
    have e3 : Real.exp (-(8 * u)) ≤ Real.exp (-(2 * u)) := Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_left e2 hB.le) e3 (Real.exp_pos _).le (by positivity)
  have h2 : (B * Real.exp (-(8 * u))) ^ (1 - (k : ℝ) / 3) * B ^ ((k : ℝ) / 3) ≤
      B * Real.exp (-(2 * u)) := by
    rw [Real.mul_rpow hB.le (Real.exp_pos _).le, ← Real.exp_mul]
    have e1 : B ^ (1 - (k : ℝ) / 3) * Real.exp (-(8 * u) * (1 - (k : ℝ) / 3)) * B ^ ((k : ℝ) / 3) =
        (B ^ (1 - (k : ℝ) / 3) * B ^ ((k : ℝ) / 3)) * Real.exp (-(8 * u) * (1 - (k : ℝ) / 3)) := by
      ring
    rw [e1, ← Real.rpow_add hB]
    have e2 : 1 - (k : ℝ) / 3 + (k : ℝ) / 3 = 1 := by ring
    rw [e2, Real.rpow_one]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB.le
    nlinarith
  calc B * Real.exp (-(8 * u)) / (σ / 64) ^ k +
        (B * Real.exp (-(8 * u))) ^ (1 - (k : ℝ) / 3) * B ^ ((k : ℝ) / 3)
      ≤ B * (1 + 64 / σ) ^ 2 * Real.exp (-(2 * u)) + B * Real.exp (-(2 * u)) := add_le_add h1 h2
    _ = _ := by ring
theorem isSmallCurvature_mono {j : ℕ} {s s' : ℝ} {W : F.GaugeField j} (h : IsSmallCurvature s W)
    (hs : s ≤ s') : IsSmallCurvature s' W := fun p hp => (h p hp).trans_le hs
theorem isLocalDensity_mono {L t n₀ : ℕ} {s s' : ℝ} {g : TopLevelFamily}
    (h : IsLocalDensity L t n₀ s' g) (hs : s ≤ s') : IsLocalDensity L t n₀ s g :=
  ⟨fun F hF Y V hV => h.smooth F hF Y V (isSmallCurvature_mono hV hs),
    fun F hF Y V γ hV => h.gauge_invariant F hF Y V γ (isSmallCurvature_mono hV hs),
    fun F hF Y hh V hV => h.translation_invariant F hF Y hh V (isSmallCurvature_mono hV hs)⟩
theorem blockGapMean_eq_zero (s a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ : LocalFamily) (Y : F.Cell)
    (V : F.GaugeField F.top) (h : ∀ b ∈ chordBonds (finiteCells F), frameGap a ρA m b V = 0) :
    blockGapMean s a ρA ρ x m p φ Y V = 0 := by
  have e : ∀ η : StepVariable (finiteCells F), blockGapObservable a ρA m p Y V η = 0 := by
    intro η
    unfold blockGapObservable
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [h b.1 b.2]
    simp
  unfold blockGapMean cutoffMean
  simp [e]
section Parameters
abbrev blockGapDensityAt (T : StepParameters) (x : ℝ) (φ : LocalFamily) : TopLevelFamily :=
  blockGapDensity T.a T.chainParams.ρA T.ballRadius x (frameRadius x) T.p φ
theorem blockGapDensityAt_deriv (T : StepParameters) (hI : DifferentiationUnderIntegral)
    (hdom : GapMeansDominatedAt T) {t : ℕ} {x : ℝ} {φ : LocalFamily} {F : BlockFrame}
    (hx : T.coupling ≤ x)
    (hφ : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ)
    (hF : IsCubicTopTorus T.L t T.n₀ F) (Y : F.Cell) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ 3
        (fun τ : Fin k → ℝ => blockGapDensityAt T x φ F Y (leftTranslate (bondSpread c X τ) V)) 0 ∧
      (k ≤ 3 → bondDeriv (blockGapDensityAt T x φ F Y) V c X =
        ∫ s in (0 : ℝ)..1, bondDeriv (gapObservableMean T x s φ Y) V c X) := by
  obtain ⟨r, K, hr, hD⟩ := hdom t x φ F Y V k c X hx hφ hF hV
  obtain ⟨hc, hder⟩ := hI ℝ (volume.restrict (Icc (0 : ℝ) 1)) k 3 (Metric.ball 0 r) K _
    Metric.isOpen_ball hD
  have he : (fun τ : Fin k → ℝ => blockGapDensityAt T x φ F Y (leftTranslate (bondSpread c X τ) V)) =
      fun τ => ∫ s, gapObservableMean T x s φ Y (leftTranslate (bondSpread c X τ) V)
        ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
    funext τ
    exact intervalIntegral_unit_eq _
  refine ⟨?_, fun hk => ?_⟩
  · rw [he]
    have := hc.contDiffAt (Metric.ball_mem_nhds 0 hr)
    simpa using this
  · have h1 := hder 0 (Metric.mem_ball_self hr) k hk (fun l => Pi.single l 1)
    rw [intervalIntegral_unit_eq]
    show iteratedFDeriv ℝ k
      (fun τ : Fin k → ℝ => blockGapDensityAt T x φ F Y (leftTranslate (bondSpread c X τ) V)) 0
      (fun l => Pi.single l 1) = _
    rw [he, h1]
    rfl
theorem log_stepIntegral_eq_at (T : StepParameters) (hcover : BlocksCoverLowerLevel)
    (hmove : logShiftedCutoffIntegralStatement) (hlawc : normalizedBallLawIsProbabilityStatement)
    (hT : T.IsOrdered) (hn : 1 ≤ T.n₀) (hCt : 0 ≤ T.Ct) {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    {t : ℕ} {x : ℝ} (hx : 0 ≤ x) (hfb : InterpolatedFrameBoundsAt T Cq Cz Cr t x)
    {φ : LocalFamily}
    (hφ : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ)
    {F : BlockFrame} (hF : IsCubicTopTorus T.L t T.n₀ F)
    {V : F.GaugeField F.top} (hV : IsSmallCurvature (5 / 4 * T.σ) V) :
    BlockGapIntegrable T.a T.chainParams.ρA T.ballRadius x (frameRadius x) T.p φ V ∧
      Real.log (stepIntegral T.a T.chainParams.ρA T.ballRadius x (frameRadius x) T.p φ (finiteCells F) V) =
        Real.log (interpolatedStepIntegral 0 T.a T.chainParams.ρA T.ballRadius x (frameRadius x) T.p φ V) +
          ∑ Y ∈ finiteCells F, blockGapDensityAt T x φ F Y V := by
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    show 0 < T.σ / 64
    positivity
  have hodd : Odd F.blockSide := by
    rw [hF.1]
    exact hT.odd_L
  have hside : ∀ i, 0 < F.extent i := by
    obtain ⟨-, -, n, hs, h1⟩ := hF
    intro i
    rw [hs i]
    omega
  obtain ⟨⟨-, hρA, -⟩, -⟩ := hT.chain_admissible.classical
  refine log_stepIntegral_eq hcover hmove hlawc T.a T.chainParams.ρA T.ballRadius x (frameRadius x) T.p φ V
    (T.Ct * x) hρ hT.cutoff hodd hside (by positivity) ?_
    (fun s h0 h1 => familyLawExponent_local T hfb V s φ hF hV h0 h1 hφ)
  intro s h0 h1 b hb
  have h2 := (hfb.one_torus F V s hF hV h0 h1).small.norm_add_le b hb
  have h3 := Real.pi_gt_three
  show _ + T.σ / 64 < _
  linarith
def ParametersBounded (T : StepParameters) : Prop :=
  1 ≤ T.coupling ∧ 1 ≤ T.n₀ ∧ 0 ≤ T.Ct ∧ T.κ ≤ T.chainParams.δ₂ / 2 ^ 14
theorem eventually_parametersBounded : EventuallyInParameters ParametersBounded := by
  intro a _
  refine ⟨0, fun L _ _ c hc => ⟨0, fun Ct hCt => ⟨c.δ₂ / 2 ^ 14, ?_, fun κ _ hκ => ⟨1, one_pos,
    fun η₃ _ _ _ => ⟨0, fun bi _ => ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ E _ => ⟨1,
    fun n₀ hn => ⟨0, fun CE _ => ⟨1, fun y hy => ⟨hy, hn, hCt, hκ⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  obtain ⟨⟨-, -, -, h, -⟩, -⟩ := hc.classical
  positivity
theorem frameInterpolationAt_of (hcover : BlocksCoverLowerLevel)
    (hmove : logShiftedCutoffIntegralStatement) (hlawc : normalizedBallLawIsProbabilityStatement)
    (hI : DifferentiationUnderIntegral) (htwo : DensityDerivDiffLeOnTwoTori)
    (hflat : vanishingDensityPlaneBoundStatement) (T : StepParameters) (hT : T.IsOrdered)
    (hP : ParametersBounded T) {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    (hfb : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFrameBoundsAt T Cq Cz Cr t x)
    (hdom : GapMeansDominatedAt T) (hdec : GapMeansDecayAt T)
    (hinv : GapMeansInvariantAt T) (hfr : GapObservableExpectationDecouples T)
    (hvan : FramesVanishAtFlat T) :
    ∃ CN : ℕ → ℝ, (∀ N, 0 < CN N) ∧
      FrameInterpolationAt T.a T.chainParams.ρA T.κ T.decayRate T.chainParams.δ₂ T.η₃ T.σ T.E T.coupling CN T.L
        T.n₀ T.p := by
  obtain ⟨hy, hn, hCt, hκ⟩ := hP
  have hσ : 0 < T.σ := hT.σ_pos
  have hκ0 : 0 < T.κ := hT.κ_pos
  have hδe : T.decayRate = T.κ / 2 ^ 10 := rfl
  have hδ : 0 < T.decayRate := by
    rw [hδe]
    positivity
  have hL1 : 1 ≤ T.L := hT.odd_L.pos
  have hδ₂ : 0 < T.chainParams.δ₂ := by
    have : 0 < T.chainParams.δ₂ / 2 ^ 14 := lt_of_lt_of_le hκ0 hκ
    linarith
  choose Cd hCd0 hCd using hdec
  choose Cf hCf using hfr
  obtain ⟨C₁, hC₁, hw⟩ := torusDecayFactor_le hL1 hδ
  obtain ⟨C2, hC20, htw⟩ := htwo
  obtain ⟨S, hS0, hS⟩ := hflat (T.κ / 2 ^ 6) (by positivity)
  let A : ℕ → ℝ := fun N => Cd N + |Cf N| + 1
  have hA : ∀ N, 0 < A N := fun N => by
    have := hCd0 N
    have := abs_nonneg (Cf N)
    show 0 < Cd N + |Cf N| + 1
    linarith
  set Qc : ℝ := (1 + 64 / T.σ) ^ 2 + 1 with hQc
  have hQc0 : 0 < Qc := by positivity
  set K₀ : ℝ := 2 * C₁ + C2 * Qc * C₁ + 1 with hK₀
  have hK₀0 : 0 < K₀ := by positivity
  let CN₀ : ℕ → ℝ := fun N => K₀ * A N
  have hCN₀ : ∀ N, 0 < CN₀ N := fun N => mul_pos hK₀0 (hA N)
  have hCN₀l : ∀ N, CN₀ N ≤ (1 + S) * CN₀ N := fun N => by
    have := hCN₀ N
    nlinarith
  have hACN : ∀ N, A N ≤ CN₀ N := fun N => by
    have h1 : 1 ≤ K₀ := by
      rw [hK₀]
      have : 0 ≤ C2 * Qc * C₁ := by positivity
      nlinarith
    have := hA N
    show A N ≤ K₀ * A N
    nlinarith
  refine ⟨fun N => (1 + S) * CN₀ N, fun N => mul_pos (by linarith) (hCN₀ N), ?_⟩
  intro t x φ hx hφ'
  have hφ : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ := hφ'
  have hx1 : 1 ≤ x := hy.trans hx
  have hx0 : 0 < x := by linarith
  set m : ℕ := frameRadius x with hm
  set ω : ℝ := Real.exp (-(T.chainParams.δ₂ / 4 * m)) with hω
  have hω0 : 0 < ω := Real.exp_pos _
  have hω1 : ω ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ T.chainParams.δ₂ / 4 * (m : ℝ) := by positivity
    linarith)
  let g : TopLevelFamily := blockGapDensityAt T x φ
  let xN : ℕ → ℝ := fun N => (x ^ N)⁻¹
  have hxN : ∀ N, 0 < xN N := fun N => inv_pos.mpr (pow_pos hx0 N)
  let G : ℕ → ℝ := fun r => torusDecayFactor T.L T.decayRate r
  have hG : ∀ r, 0 < G r := fun r => torusDecayFactor_pos _ _ _
  have hread : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ V : F.GaugeField F.top,
      IsSmallCurvature (5 / 4 * T.σ) V → _ := fun F hF V hV =>
    log_stepIntegral_eq_at T hcover hmove hlawc hT hn hCt hx0.le (hfb t x hx) hφ hF hV
  have hin : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ V : F.GaugeField F.top,
      IsSmallCurvature (5 / 4 * T.σ) V → ∀ Y : F.Cell,
      IntervalIntegrable (fun s => gapObservableMean T x s φ Y V) volume 0 1 := fun F hF V hV Y =>
    (hread F hF V hV).1.intervalIntegrable Y
  have hexp1 : ∀ u : ℝ, 0 ≤ u → Real.exp (-u) ≤ 1 := fun u hu =>
    Real.exp_le_one_iff.mpr (by linarith)
  have hdec0 : ∀ (N : ℕ) (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F →
      ∀ (Y : F.Cell) (V : F.GaugeField F.top)
      (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      IsSmallCurvature (5 / 4 * T.σ) V → k ≤ 3 → AreUnitVectors X →
      |bondDeriv (g F Y) V c X| ≤ Cd N * xN N * ω * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c)) := by
    intro N F hF Y V k c X hV hk hX
    have e := (blockGapDensityAt_deriv T hI hdom hx hφ hF Y hV c X).2 hk
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun s => bondDeriv (gapObservableMean T x s φ Y) V c X)
      (C := Cd N * xN N * ω * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))) (fun s hs => by
        rw [uIoc_of_le zero_le_one] at hs
        exact hCd N t x s φ F Y V k c X hx hs.1.le hs.2 hφ hF hV hk hX)
    show |bondDeriv (blockGapDensityAt T x φ F Y) V c X| ≤ _
    rw [e]
    simpa using h1
  have hval0 : ∀ (N : ℕ) (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F →
      ∀ (Y : F.Cell) (V : F.GaugeField F.top),
      IsSmallCurvature (5 / 4 * T.σ) V → |g F Y V| ≤ Cd N * xN N * ω := by
    intro N F hF Y V hV
    have h1 := hdec0 N F hF Y V 0 Fin.elim0 Fin.elim0 hV (by omega) (fun l => l.elim0)
    rw [bondDeriv_zero] at h1
    have h2 : 0 < Cd N * xN N * ω := mul_pos (mul_pos (hCd0 N) (hxN N)) hω0
    exact h1.trans (mul_le_of_le_one_right h2.le (hexp1 _ (by positivity)))
  have hexpG : ∀ r : ℕ, Real.exp (-(2 * (T.decayRate * r))) ≤ C₁ / G r := by
    intro r
    rw [le_div_iff₀ (hG r)]
    have h1 := hw r
    calc Real.exp (-(2 * (T.decayRate * r))) * G r
        ≤ Real.exp (-(2 * (T.decayRate * r))) * (C₁ * Real.exp (2 * T.decayRate * r)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = C₁ := by
          rw [mul_comm C₁, ← mul_assoc, ← Real.exp_add]
          have : -(2 * (T.decayRate * r)) + 2 * T.decayRate * r = 0 := by ring
          rw [this, Real.exp_zero, one_mul]
  have hωG : ∀ r : ℕ, r ≤ 4 * m → ω ≤ C₁ / G r := by
    intro r hr
    refine le_trans ?_ (hexpG r)
    apply Real.exp_le_exp.mpr
    have h1 : (r : ℝ) ≤ 4 * m := by exact_mod_cast hr
    have h2 : 8 * T.decayRate ≤ T.chainParams.δ₂ / 4 := by
      rw [hδe]
      nlinarith
    have h3 : T.decayRate * r ≤ T.decayRate * (4 * m) := mul_le_mul_of_nonneg_left h1 hδ.le
    have h4 : 8 * T.decayRate * (m : ℝ) ≤ T.chainParams.δ₂ / 4 * m :=
      mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
    nlinarith
  have hclose : ∀ (N : ℕ) (F F' : BlockFrame), IsCubicTopTorus T.L t T.n₀ F →
      IsCubicTopTorus T.L t T.n₀ F' →
      ∀ (Y : F.Cell) (Y' : F'.Cell) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (q : ℕ),
      IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → 4 * m < q →
      |g F Y V - g F' Y' V'| ≤ |Cf N| * xN N * Real.exp (-(8 * (T.decayRate * q))) := by
    intro N F F' hF hF' Y Y' V V' q hV hV' hag hq
    have e : g F Y V - g F' Y' V' =
        ∫ s in (0 : ℝ)..1, (gapObservableMean T x s φ Y V - gapObservableMean T x s φ Y' V') :=
      (intervalIntegral.integral_sub (hin F hF V hV Y) (hin F' hF' V' hV' Y')).symm
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun s => gapObservableMean T x s φ Y V - gapObservableMean T x s φ Y' V')
      (C := |Cf N| * xN N * Real.exp (-(8 * (T.decayRate * q)))) (fun s hs => by
        rw [uIoc_of_le zero_le_one] at hs
        have h2 := hCf N t x s φ F F' V V' Y Y' q hx hs.1.le hs.2 hφ hF hF' hV hV' hag hq
        have e2 : T.κ * q / 2 ^ 7 = 8 * (T.decayRate * q) := by
          rw [hδe]
          ring
        rw [e2] at h2
        refine h2.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (hxN N).le)
    rw [e]
    simpa using h1
  have hsmallbound : ∀ (N : ℕ) (r : ℕ) (u v : ℝ), r ≤ 4 * m → |u| ≤ Cd N * xN N * ω →
      |v| ≤ Cd N * xN N * ω → |u - v| ≤ CN₀ N * xN N / G r := by
    intro N r u v hr hu hv
    have h1 : |u - v| ≤ 2 * (Cd N * xN N * ω) := by
      have := abs_sub u v
      linarith
    have h2 := hωG r hr
    have h3 : 0 < Cd N * xN N := mul_pos (hCd0 N) (hxN N)
    have h4 : 2 * (Cd N * xN N * ω) ≤ 2 * (Cd N * xN N * (C₁ / G r)) := by
      have := mul_le_mul_of_nonneg_left h2 h3.le
      linarith
    have h5 : 2 * (Cd N * xN N * (C₁ / G r)) = (2 * C₁ * Cd N) * xN N / G r := by ring
    have h6 : 2 * C₁ * Cd N ≤ CN₀ N := by
      show 2 * C₁ * Cd N ≤ K₀ * A N
      have a1 : Cd N ≤ A N := by
        show Cd N ≤ Cd N + |Cf N| + 1
        have := abs_nonneg (Cf N)
        linarith
      have a2 : 2 * C₁ ≤ K₀ := by
        rw [hK₀]
        have : 0 ≤ C2 * Qc * C₁ := by positivity
        linarith
      exact mul_le_mul a2 a1 (hCd0 N).le hK₀0.le
    have h7 : (2 * C₁ * Cd N) * xN N / G r ≤ CN₀ N * xN N / G r :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h6 (hxN N).le) (hG r).le
    linarith
  have hval : ∀ (N : ℕ) (F F' : BlockFrame), IsCubicTopTorus T.L t T.n₀ F →
      IsCubicTopTorus T.L t T.n₀ F' →
      ∀ (Y : F.Cell) (Y' : F'.Cell) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (r : ℕ),
      IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
      |g F Y V - g F' Y' V'| ≤ CN₀ N * xN N / G r := by
    intro N F F' hF hF' Y Y' V V' r hV hV' hag
    by_cases hr : r ≤ 4 * m
    · exact hsmallbound N r _ _ hr (hval0 N F hF Y V hV) (hval0 N F' hF' Y' V' hV')
    · push Not at hr
      have h1 := hclose N F F' hF hF' Y Y' V V' r hV hV' hag hr
      have h2 : Real.exp (-(8 * (T.decayRate * r))) ≤ C₁ / G r := by
        refine le_trans (Real.exp_le_exp.mpr ?_) (hexpG r)
        have : 0 ≤ T.decayRate * (r : ℝ) := by positivity
        linarith
      have h3 : 0 ≤ |Cf N| * xN N := mul_nonneg (abs_nonneg _) (hxN N).le
      have h4 : |Cf N| * xN N * Real.exp (-(8 * (T.decayRate * r))) ≤ (C₁ * |Cf N|) * xN N / G r := by
        calc _ ≤ |Cf N| * xN N * (C₁ / G r) := mul_le_mul_of_nonneg_left h2 h3
          _ = _ := by ring
      have h5 : C₁ * |Cf N| ≤ CN₀ N := by
        show C₁ * |Cf N| ≤ K₀ * A N
        have a1 : |Cf N| ≤ A N := by
          show |Cf N| ≤ Cd N + |Cf N| + 1
          have := hCd0 N
          linarith
        have a2 : C₁ ≤ K₀ := by
          rw [hK₀]
          have : 0 ≤ C2 * Qc * C₁ := by positivity
          linarith
        exact mul_le_mul a2 a1 (abs_nonneg _) hK₀0.le
      exact h1.trans (h4.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right h5 (hxN N).le) (hG r).le))
  have hden : IsLocalDensity T.L t T.n₀ (5 / 4 * T.σ) g := by
    refine ⟨fun F hF Y V hV k c X => (blockGapDensityAt_deriv T hI hdom hx hφ hF Y hV c X).1, ?_, ?_⟩
    · intro F hF Y V γ hV
      show ∫ s in (0 : ℝ)..1, gapObservableMean T x s φ Y (gaugeTransform γ V) =
        ∫ s in (0 : ℝ)..1, gapObservableMean T x s φ Y V
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le zero_le_one] at hs
      exact (hinv t x s φ F V hx hs.1 hs.2 hφ hF hV).1 Y γ
    · intro F hF Y h V hV
      show ∫ s in (0 : ℝ)..1, gapObservableMean T x s φ (Y + h) (translateField h V) =
        ∫ s in (0 : ℝ)..1, gapObservableMean T x s φ Y V
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le zero_le_one] at hs
      exact (hinv t x s φ F V hx hs.1 hs.2 hφ hF hV).2 Y h
  have hcold98 : ∀ {F : BlockFrame} {V : F.GaugeField F.top}, IsSmallCurvature (9 / 8 * T.σ) V →
      IsSmallCurvature (5 / 4 * T.σ) V := fun h => isSmallCurvature_mono h (by linarith)
  have hloc : ∀ N : ℕ, IsLocalOnTori T.L t T.n₀ (9 / 8 * T.σ) g
      (fun r => CN₀ N * xN N / G r) := by
    intro N F F' hF hF' Y Y' V V' r k h X hV hV' hag hk hbox hX
    have hV5 := hcold98 hV
    have hV5' := hcold98 hV'
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [bondDeriv_zero, bondDeriv_zero]
      exact hval N F F' hF hF' Y Y' V V' r hV5 hV5' hag
    by_cases hr : r ≤ 4 * m
    · have hb : ∀ (F₀ : BlockFrame), IsCubicTopTorus T.L t T.n₀ F₀ →
          ∀ (Y₀ : F₀.Cell) (V₀ : F₀.GaugeField F₀.top)
          (c₀ : Fin k → F₀.Site F₀.top × Fin 4), IsSmallCurvature (5 / 4 * T.σ) V₀ →
          |bondDeriv (g F₀ Y₀) V₀ c₀ X| ≤ Cd N * xN N * ω := by
        intro F₀ hF₀ Y₀ V₀ c₀ hV₀
        have h1 := hdec0 N F₀ hF₀ Y₀ V₀ k c₀ X hV₀ (by omega) hX
        have h2 : 0 < Cd N * xN N * ω := mul_pos (mul_pos (hCd0 N) (hxN N)) hω0
        exact h1.trans (mul_le_of_le_one_right h2.le (hexp1 _ (by positivity)))
      exact hsmallbound N r _ _ hr (hb F hF Y V _ hV5) (hb F' hF' Y' V' _ hV5')
    · push Not at hr
      set B : ℝ := A N * xN N with hB
      have hB0 : 0 < B := mul_pos (hA N) (hxN N)
      have hCdB : Cd N * xN N ≤ B := mul_le_mul_of_nonneg_right (by
        show Cd N ≤ Cd N + |Cf N| + 1
        have := abs_nonneg (Cf N)
        linarith) (hxN N).le
      have hCfB : |Cf N| * xN N ≤ B := mul_le_mul_of_nonneg_right (by
        show |Cf N| ≤ Cd N + |Cf N| + 1
        have := hCd0 N
        linarith) (hxN N).le
      have third : ∀ (F'' : BlockFrame) (Y'' : F''.Cell) (W : F''.GaugeField F''.top)
          (c : Fin 3 → F''.Site F''.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions),
          IsCubicTopTorus T.L t T.n₀ F'' →
          IsSmallCurvature (5 / 4 * T.σ) W → AreUnitVectors X' →
          |bondDeriv (g F'' Y'') W c X'| ≤ B := by
        intro F'' Y'' W c X' hF'' hW hX'
        have h1 := hdec0 N F'' hF'' Y'' W 3 c X' hW le_rfl hX'
        have h2 : Cd N * xN N * ω * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y'' c)) ≤ Cd N * xN N := by
          have h3 : 0 < Cd N * xN N := mul_pos (hCd0 N) (hxN N)
          have h4 : ω * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y'' c)) ≤ 1 :=
            mul_le_one₀ hω1 (Real.exp_pos _).le (hexp1 _ (by positivity))
          calc _ = Cd N * xN N * (ω * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y'' c))) := by ring
            _ ≤ _ := mul_le_of_le_one_right h3.le h4
        exact h1.trans (h2.trans hCdB)
      have closeW : ∀ (W : F.GaugeField F.top) (W' : F'.GaugeField F'.top),
          IsSmallCurvature (5 / 4 * T.σ) W →
          IsSmallCurvature (5 / 4 * T.σ) W' → AgreeOnBall (finiteCells F) W (finiteCells F') W' Y Y' r →
          |g F Y W - g F' Y' W'| ≤ B * Real.exp (-(8 * (T.decayRate * r))) := by
        intro W W' hW hW' hagW
        exact (hclose N F F' hF hF' Y Y' W W' r hW hW' hagW hr).trans
          (mul_le_mul_of_nonneg_right hCfB (Real.exp_pos _).le)
      have h1 := htw T.L t T.n₀ T.σ (B * Real.exp (-(8 * (T.decayRate * r)))) B g F F' Y Y' V V' r k h
        X hσ (mul_pos hB0 (Real.exp_pos _)) hB0.le hk1 hk hF hF' hden third closeW hV hV' hag hbox hX
      have h2 := interpolatedSize_le (σ := T.σ) (B := B) (u := T.decayRate * r) (k := k) hσ hB0 hk1 hk
        (by positivity)
      have h3 := hexpG r
      have h4 : C2 * (B * Qc * Real.exp (-(2 * (T.decayRate * r)))) ≤ (C2 * Qc * C₁) * B / G r := by
        have h5 : 0 ≤ C2 * (B * Qc) := by positivity
        calc C2 * (B * Qc * Real.exp (-(2 * (T.decayRate * r))))
            = C2 * (B * Qc) * Real.exp (-(2 * (T.decayRate * r))) := by ring
          _ ≤ C2 * (B * Qc) * (C₁ / G r) := mul_le_mul_of_nonneg_left h3 h5
          _ = _ := by ring
      have h6 : (C2 * Qc * C₁) * B / G r ≤ CN₀ N * xN N / G r := by
        refine div_le_div_of_nonneg_right ?_ (hG r).le
        show (C2 * Qc * C₁) * (A N * xN N) ≤ K₀ * A N * xN N
        have a2 : C2 * Qc * C₁ ≤ K₀ := by
          rw [hK₀]
          have : 0 ≤ 2 * C₁ := by positivity
          linarith
        have a3 : 0 < A N * xN N := mul_pos (hA N) (hxN N)
        nlinarith
      calc _ ≤ C2 * interpolatedSize T.σ (B * Real.exp (-(8 * (T.decayRate * r)))) B k := h1
        _ ≤ C2 * (B * Qc * Real.exp (-(2 * (T.decayRate * r)))) :=
            mul_le_mul_of_nonneg_left h2 hC20.le
        _ ≤ _ := h4.trans h6
  have hzero : ∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top),
      (∀ b ∈ chordBonds (finiteCells F), frameGap T.a T.chainParams.ρA m b V = 0) → g F Y V = 0 := by
    intro F Y V h
    have e : (fun s => blockGapMean s T.a T.chainParams.ρA T.ballRadius x m T.p φ Y V) = fun _ => 0 :=
      funext fun s => blockGapMean_eq_zero s T.a T.chainParams.ρA T.ballRadius x m T.p φ Y V h
    show ∫ s in (0 : ℝ)..1, blockGapMean s T.a T.chainParams.ρA T.ballRadius x m T.p φ Y V = 0
    rw [e]
    simp
  have hatflat : ∀ (F : BlockFrame) (Y : F.Cell), IsCubicTopTorus T.L t T.n₀ F →
      g F Y (flatTopField (F := F)) = 0 := by
    intro F Y hF
    refine hzero F Y (uniformField F F.top) fun b hb => ?_
    unfold frameGap
    rw [(hvan t x F false hx hF).1 b hb, (hvan t x F true hx hF).1 b hb]
    simp
  have hsmallForm : ∀ N : ℕ, HasBoundedLimitForm T.L t g (S * (CN₀ N * xN N)) := by
    intro N
    refine hS T.L t T.n₀ T.decayRate (9 / 8 * T.σ) (CN₀ N * xN N) g hT.odd_L hδ (by
      rw [hδe]
      nlinarith) (by positivity) (mul_pos (hCN₀ N) (hxN N)) (isLocalDensity_mono hden (by linarith))
      hatflat ?_ (hloc N)
    intro F hF Y V k c X hV hk1 hk3 hX
    have h1 := hdec0 N F hF Y V k c X (hcold98 hV) hk3 hX
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    have h2 : Cd N ≤ CN₀ N := le_trans (by
      show Cd N ≤ Cd N + |Cf N| + 1
      have := abs_nonneg (Cf N)
      linarith) (hACN N)
    have h3 : 0 < Cd N * xN N := mul_pos (hCd0 N) (hxN N)
    calc Cd N * xN N * ω ≤ Cd N * xN N := mul_le_of_le_one_right h3.le hω1
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (hxN N).le
  refine ⟨fun F hF V hV => (hread F hF V hV).1, fun F hF V hV => (hread F hF V hV).2, ?_, hden, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro F hF hs Y V hV
    refine hzero F Y V fun b _ => ?_
    have h1 := ((hfb t x hx).one_torus F V 1 hF hV zero_le_one le_rfl).near_minimizer.eq_on_small_torus hs b
    have h2 : interpolatedFrame 1 T.a T.chainParams.ρA m b V = stepFrame false T.a T.chainParams.ρA m b V := by
      simp [interpolatedFrame]
    unfold frameGap
    rw [← h2, h1]
    exact sub_self _
  · exact fun F hF Y => hatflat F Y hF
  · intro N F hF Y V k c X hV hk hX
    refine (hdec0 N F hF Y V k c X hV hk hX).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine mul_le_mul_of_nonneg_right ?_ hω0.le
    refine mul_le_mul_of_nonneg_right ?_ (hxN N).le
    refine le_trans ?_ (hCN₀l N)
    refine le_trans ?_ (hACN N)
    show Cd N ≤ Cd N + |Cf N| + 1
    have := abs_nonneg (Cf N)
    linarith
  · intro N F F' hF hF' Y Y' V V' r hV hV' hag
    refine (hval N F F' hF hF' Y Y' V V' r hV hV' hag).trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hCN₀l N) (hxN N).le) (hG r).le
  · intro N F F' hF hF' Y Y' V V' r k h X hV hV' hag hk hb hX
    refine (hloc N F F' hF hF' Y Y' V V' r k h X hV hV' hag hk hb hX).trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hCN₀l N) (hxN N).le) (hG r).le
  · obtain ⟨q, hq, hv0⟩ := hsmallForm 0
    refine ⟨q, hq, fun X μ ν B hX hμ hB => ?_⟩
    obtain ⟨v, hv, -⟩ := hv0 X μ ν B hX hμ hB
    refine ⟨v, hv, fun N => ?_⟩
    obtain ⟨q', hq', hvN⟩ := hsmallForm N
    have hqq : q' = q := by
      funext b b' X₁ X₂
      exact tendsto_nhds_unique (hq' b b' X₁ X₂) (hq b b' X₁ X₂)
    rw [hqq] at hvN
    obtain ⟨v', hv', hb⟩ := hvN X μ ν B hX hμ hB
    have hvv : v' = v := hv'.unique hv
    rw [hvv] at hb
    refine hb.trans ?_
    have h1 : 0 < CN₀ N * xN N := mul_pos (hCN₀ N) (hxN N)
    show S * (CN₀ N * xN N) ≤ (1 + S) * CN₀ N * xN N
    have h2 : (1 + S) * CN₀ N * xN N = CN₀ N * xN N + S * (CN₀ N * xN N) := by ring
    rw [h2]
    linarith
end Parameters
theorem frameInterpolationStatement_proof (hframes : interpolatedFramesStatement)
    (hcover : BlocksCoverLowerLevel) (hmove : logShiftedCutoffIntegralStatement)
    (hlawc : normalizedBallLawIsProbabilityStatement) (hjoin : EventuallyInParametersCombines)
    (hweighted : GibbsMeanDifferentiation)
    (htwo : DensityDerivDiffLeOnTwoTori)
    (hflat : vanishingDensityPlaneBoundStatement)
    (hdom : gapMeansDominated) (hdec : gapMeansDecay)
    (hinv : gapMeansInvariant) (hfreeze : gapObservableExpectationDecouples)
    (hvan : framesVanishAtFlatStatement) :
    frameInterpolationStatement := by
  obtain ⟨Cq, Cz, Cr, hfb⟩ := hframes
  have j := hjoin.1
  have J := j _ _ eventually_parametersBounded
    (j _ _ hfb (j _ _ hdom (j _ _ hdec (j _ _ hinv (j _ _ hfreeze hvan)))))
  exact hjoin.2 _ _ (fun T hT h => frameInterpolationAt_of hcover hmove hlawc hweighted.1 htwo hflat T hT
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2) J
end FrameInterpolationProof
end YangMills.Construction
end
