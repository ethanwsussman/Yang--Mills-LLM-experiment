import YangMills.Construction.ClusterExpansionOfAStep.TopFamiliesOnToriProof
import YangMills.Construction.FreeEnergiesOfTheFlow.MeansGivenAStateReadTheCasesProof
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheParts
import YangMills.Construction.ResponseInTheExpansion.FieldsOfOneColour
import YangMills.Construction.ResponseInTheExpansion.RemainderOfTheResponseReturnsProof
import YangMills.Construction.ResponseInTheExpansion.RestOfAStepAtTheFrameField
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory Filter
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames WeightedResponses Interpolation TorusFields TorusLumps StepSettings RenormalizationStepParameters StepGas StepCosts
namespace ResponseInTheExpansion
namespace FrameFieldRemainder
theorem isTorusRemainder_mono {F : BlockFrame} {L : ℕ} {σ δ e e' η₃ : ℝ} {r : F.Site F.depth → F.GaugeField F.depth → ℝ} (hδ : 0 ≤ δ) (he : 0 ≤ e)
    (hee : e ≤ e') (hη : 0 < η₃) (hr : IsTorusRemainder L σ δ e (e / η₃) r) :
    IsTorusRemainder L σ δ e' (e' / η₃) r := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderExpectation.torusRemainder_mono <;> assumption
section Frame
variable {F : BlockFrame}
theorem bondDeriv_add {G₁ G₂ : F.GaugeField F.top → ℝ} {V : F.GaugeField F.top} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4}
    {X : Fin k → imaginaryQuaternions}
    (h₁ : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G₁ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0)
    (h₂ : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G₂ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0) :
    bondDeriv (fun V => G₁ V + G₂ V) V c X = bondDeriv G₁ V c X + bondDeriv G₂ V c X := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.bondDeriv_add <;> assumption
theorem bondDeriv_const_mul (a : ℝ) {G : F.GaugeField F.top → ℝ} {V : F.GaugeField F.top} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4}
    {X : Fin k → imaginaryQuaternions}
    (h : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0) :
    bondDeriv (fun V => a * G V) V c X = a * bondDeriv G V c X := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.bondDeriv_const_mul <;> assumption
theorem natCast_le_three {k : ℕ} (hk : k ≤ 3) : (k : WithTop ℕ∞) ≤ 3 := by
  exact_mod_cast hk
def frameTerms (Q : ColdHalfLaw) (al : ℝ) (r r₂ : F.Site F.depth → F.GaugeField F.depth → ℝ) (w : F.Site F.depth → ℝ) (Y : F.Cell)
    (V : F.GaugeField F.top) : ℝ :=
  Q.expectationOf (Q.blockSum r Y) V + al * Q.weightedFrameShares w Y V + al * Q.expectationOf (Q.weightedShareIncrement w Y) V +
    Q.expectationOf (Q.blockSum r₂ Y) V
theorem frameTerms_contDiffThree {Q : ColdHalfLaw} {al : ℝ} {r r₂ : F.Site F.depth → F.GaugeField F.depth → ℝ} {w : F.Site F.depth → ℝ} {Y : F.Cell}
    {V : F.GaugeField F.top} (h₁ : ContDiffThreeAlongBonds (Q.expectationOf (Q.blockSum r Y)) V)
    (h₂ : ContDiffThreeAlongBonds (Q.weightedFrameShares w Y) V)
    (h₃ : ContDiffThreeAlongBonds (Q.expectationOf (Q.weightedShareIncrement w Y)) V)
    (h₄ : ContDiffThreeAlongBonds (Q.expectationOf (Q.blockSum r₂ Y)) V) :
    ContDiffThreeAlongBonds (frameTerms Q al r r₂ w Y) V := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.fourTermSum_contDiff <;> assumption
theorem bondDeriv_frameTerms {Q : ColdHalfLaw} {al : ℝ} {r r₂ : F.Site F.depth → F.GaugeField F.depth → ℝ} {w : F.Site F.depth → ℝ} {Y : F.Cell}
    {V : F.GaugeField F.top} (h₁ : ContDiffThreeAlongBonds (Q.expectationOf (Q.blockSum r Y)) V)
    (h₂ : ContDiffThreeAlongBonds (Q.weightedFrameShares w Y) V)
    (h₃ : ContDiffThreeAlongBonds (Q.expectationOf (Q.weightedShareIncrement w Y)) V)
    (h₄ : ContDiffThreeAlongBonds (Q.expectationOf (Q.blockSum r₂ Y)) V) {k : ℕ} (hk : k ≤ 3)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (frameTerms Q al r r₂ w Y) V c X = bondDeriv (Q.expectationOf (Q.blockSum r Y)) V c X +
      al * bondDeriv (Q.weightedFrameShares w Y) V c X + al * bondDeriv (Q.expectationOf (Q.weightedShareIncrement w Y)) V c X +
      bondDeriv (Q.expectationOf (Q.blockSum r₂ Y)) V c X := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.bondDeriv_fourTermSum <;> assumption
end Frame
section Weights
theorem abs_clamp_sub_clamp_le (b u v : ℝ) : |max (-b) (min b u) - max (-b) (min b v)| ≤ |u - v| := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.abs_clamp_sub_le <;> assumption
theorem abs_clamp_le {b : ℝ} (hb : 0 ≤ b) (u : ℝ) : |max (-b) (min b u)| ≤ b := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.abs_clamp_le <;> assumption
theorem clamp_eq_self {b u : ℝ} (hu : |u| ≤ b) : max (-b) (min b u) = u := by apply _root_.YangMills.DeltaSharedProofs.p15858 <;> assumption
def clampedShift {m : ℕ} (b c : ℝ) (h : PlaquetteWeight m) : PlaquetteWeight m := fun p => max (-b) (min b (h p - c))
variable {L t m : ℕ}
theorem barycentreDist_nonneg (p p' : TorusPlaquette m) : 0 ≤ barycentreDist L t p p' := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.barycentreDist_nonneg <;> assumption
theorem weightLipschitz_clampedShift_le (b c : ℝ) (h : PlaquetteWeight m) [Finite (TorusPlaquette m)] :
    weightLipschitz L t (clampedShift b c h) ≤ weightLipschitz L t h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.weightLipschitz_clampedShift_le <;> assumption
theorem weightSup_clampedShift_le {b : ℝ} (hb : 0 ≤ b) (c : ℝ) (h : PlaquetteWeight m) : weightSup (clampedShift b c h) ≤ b := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.weightSup_clampedShift_le <;> assumption
theorem mul_weightLipschitz_succ (hL : 0 < L) (h : PlaquetteWeight m) : (L : ℝ) * weightLipschitz L t h = weightLipschitz L (t + 1) h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.side_mul_weightLipschitz <;> assumption
end Weights
section Means
open YangMills.Construction.Dilation
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ}
def BallIntegrable (r : ℝ → ℝ) (Ψ g : BondField ι → ℝ) : Prop := Integrable fun η => g η * ballDensity r Ψ η
theorem ballExpectation_congr (hL : IsBallLaw ρ r Ψ) {f g : BondField ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → f η = g η) : ballExpectation r Ψ f = ballExpectation r Ψ g := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.ballExpectation_congr_on_balls <;> assumption
theorem BallIntegrable.congr {f g : BondField ι → ℝ} (hL : IsBallLaw ρ r Ψ) (hf : BallIntegrable r Ψ f)
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → f η = g η) : BallIntegrable r Ψ g := by
  refine Integrable.congr hf (Eventually.of_forall fun η => ?_)
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · simp only [h η hη]
  · simp only [hL.eq_zero_outside η hη, mul_zero]
theorem BallIntegrable.add {f g : BondField ι → ℝ} (hf : BallIntegrable r Ψ f) (hg : BallIntegrable r Ψ g) :
    BallIntegrable r Ψ fun η => f η + g η := by
  refine Integrable.congr (Integrable.add hf hg) (Eventually.of_forall fun η => ?_)
  simp only [Pi.add_apply, add_mul]
theorem BallIntegrable.const_mul {f : BondField ι → ℝ} (a : ℝ) (hf : BallIntegrable r Ψ f) :
    BallIntegrable r Ψ fun η => a * f η := by
  refine Integrable.congr (Integrable.const_mul hf a) (Eventually.of_forall fun η => ?_)
  simp only [mul_assoc]
theorem BallIntegrable.const (hL : IsBallLaw ρ r Ψ) (a : ℝ) : BallIntegrable r Ψ fun _ => a := hL.integrable.const_mul a
theorem BallIntegrable.sum {J : Type} (S : Finset J) {f : J → BondField ι → ℝ} (hL : IsBallLaw ρ r Ψ)
    (h : ∀ j ∈ S, BallIntegrable r Ψ (f j)) : BallIntegrable r Ψ fun η => ∑ j ∈ S, f j η := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using BallIntegrable.const hL 0
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
theorem ballExpectation_sum {J : Type} (S : Finset J) {f : J → BondField ι → ℝ} (hL : IsBallLaw ρ r Ψ)
    (h : ∀ j ∈ S, BallIntegrable r Ψ (f j)) :
    ballExpectation r Ψ (fun η => ∑ j ∈ S, f j η) = ∑ j ∈ S, ballExpectation r Ψ (f j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ballExpectation_const hL 0
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    have h₁ := h a (Finset.mem_insert_self _ _)
    have h₂ : ∀ j ∈ S, BallIntegrable r Ψ (f j) := fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [ballExpectation_add hL h₁ (BallIntegrable.sum S hL h₂), ih h₂]
theorem ballIntegrable_of_measurable (hL : IsBallLaw ρ r Ψ) {H g : BondField ι → ℝ} (hg : Measurable g) {C : ℝ}
    (hb : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |H η| ≤ C)
    (he : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → H η = g η) : BallIntegrable r Ψ H := by
  set O : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hO
  have hOm : MeasurableSet O := (isOpen_openBallProduct ρ).measurableSet
  have hG : AEStronglyMeasurable (O.indicator g) volume := (hg.indicator hOm).aestronglyMeasurable
  have hbd : ∀ η, ‖O.indicator g η‖ ≤ |C| := by
    intro η
    by_cases h : η ∈ O
    · rw [Set.indicator_of_mem h, Real.norm_eq_abs, ← he η h]
      exact (hb η h).trans (le_abs_self C)
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact abs_nonneg C
  have h1 := hL.integrable.bdd_mul (c := |C|) hG (Eventually.of_forall hbd)
  refine h1.congr (Eventually.of_forall fun η => ?_)
  by_cases h : η ∈ O
  · simp only [Set.indicator_of_mem h, he η h]
  · simp only [Set.indicator_of_notMem h, hL.eq_zero_outside η h, mul_zero, zero_mul]
end Means
section Torus
theorem abs_centered_le {ℓ : TorusLumps.StepParameters} {E E₃ : ℝ} {f : LocalDensity} (hf : ColdDensityBounds ℓ E E₃ f)
    (hσ : 0 < ℓ.threshold) {m : ℕ} [NeZero m]
    (hm : ℓ.n₀ ≤ m) (h3 : 2 < m) (y : TorusSite m) {W : TorusField m} (hW : IsCold ℓ.threshold W) :
    |centered f m y W| ≤ E / ℓ.weight 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.BlockImageOfOne.abs_centered_le_of_isCold <;> assumption
end Torus
section Step
open YangMills.Construction.Dilation
variable {R : StepSetup} {n : ℕ} [NeZero n]
abbrev stepFrame (R : StepSetup) (n : ℕ) : BlockFrame := torusFrame R.params.side R.depth n
theorem stepFrame_period_depth (i : Fin 4) : (stepFrame R n).period (stepFrame R n).depth i = n * R.params.side :=
  TopLevelSites.period_depth i
theorem readAtLevel_restrictToTorus (W : (stepFrame R n).GaugeField (stepFrame R n).depth) :
    readAtLevel (stepFrame R n) (stepFrame R n).depth (restrictToTorus (n * R.params.side) W) = W := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.readAtLevel_restrictToTorus <;> assumption
def frameWeight (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) (y : (stepFrame R n).Site (stepFrame R n).depth) : ℝ :=
  blockMean R.params.side R.depth (n * R.params.side) (toTorusSite (n * R.params.side) y) h
theorem block_expectations_eq_frameTerms (A : ResponseSetup R) (hr : A.IsAdmissible) (hσ : 0 < R.params.threshold)
    (hm : R.params.n₀ ≤ n * R.params.side) (hm3 : 2 < n * R.params.side) (V : TorusField n)
    (hlaw : IsBallLaw R.ballRadius (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V)))
    (hcont : Continuous (coldFieldAboveFrames R V))
    (hcold : ∀ k : StepVariable (finiteCells (stepFrame R n)), (∀ b, ‖k b‖ < R.ballRadius) →
      IsCold R.params.threshold (coldFieldAboveFrames R V k))
    (hC : ∀ G : TorusField (n * R.params.side) → ℝ, (∀ W, IsCold R.params.threshold W → ContDiffThreeAt G W) →
      ContinuousOn (fun k => G (coldFieldAboveFrames R V k))
        {k : StepVariable (finiteCells (stepFrame R n)) | ∀ b, ‖k b‖ < R.ballRadius})
    (hsum : open Classical in ∀ (g : (stepFrame R n).Site (stepFrame R n).depth → ℝ) (Y : TorusSite n),
      ∑ y ∈ (sitesOfCells (finiteCells (stepFrame R n)) (stepFrame R n).depth).filter
          (fun y => enclosingCell y = torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y), g y =
        ∑ x ∈ sitesInBlocks R.params.side {Y}, g (torusSiteInFrame (stepFrame R n) (stepFrame R n).depth x))
    (hshare : ∀ W : TorusField (n * R.params.side), IsCold R.params.threshold W → ∀ y : TorusSite (n * R.params.side),
      levelShare R.params.coupling R.params.side R.depth Finset.univ y W =
        minimalSiteShare (F := stepFrame R n) R.params.coupling (torusSiteInFrame (stepFrame R n) (stepFrame R n).depth y)
        (readAtLevel (stepFrame R n) (stepFrame R n).depth W))
    (hρ : 0 < R.ballRadius) (Y : TorusSite n) (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) :
    ∑ x ∈ sitesInBlocks R.params.side {Y}, coldExpectationAbove R V (fun W => centeredResponse A.cold (n * R.params.side) x W h) +
        ∑ x ∈ sitesInBlocks R.params.side {Y}, A.cold (n * R.params.side) x (trivialField (n * R.params.side)) h =
      frameTerms (coldHalfLawOf R) A.coeff (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h)
          (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (frameWeight h)) (frameWeight h)
          (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) (coldTopField R V) +
        ∑ x ∈ sitesInBlocks R.params.side {Y}, blockMean R.params.side R.depth (n * R.params.side) x h *
          A.cold (n * R.params.side) x (trivialField (n * R.params.side)) (constOneWeight _) := by
  classical
  have hwt : ∀ x : TorusSite (n * R.params.side), frameWeight h (torusSiteInFrame (stepFrame R n) (stepFrame R n).depth x) =
      blockMean R.params.side R.depth (n * R.params.side) x h := fun x => by
    unfold frameWeight
    rw [TopLevelSites.toTorusSite_torusSiteInFrame stepFrame_period_depth]
  have fA : ∀ (x : TorusSite (n * R.params.side)) (g : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))),
      BallIntegrable (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V))
        (fun k => centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) g) := by
    intro x g
    refine ballIntegrable_of_measurable hlaw (g := fun k => (if IsCold R.params.threshold (coldFieldAboveFrames R V k) then
        A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) g else 0) - A.cold (n * R.params.side) x (trivialField (n * R.params.side)) g)
      (((hr.bounds.cold_borel (n * R.params.side) hm x g).comp hcont.measurable).sub_const _)
      (C := A.responseParams.C₀ * weightNorm R.params.side R.depth g)
      (fun k hk => hr.bounds.size_cold _ hm x _ (hcold k hk) g) (fun k hk => ?_)
    simp only [if_pos (hcold k hk)]
    rfl
  have fD : ∀ x : TorusSite (n * R.params.side), BallIntegrable (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V))
      (fun k => centered A.siteRemainder (n * R.params.side) x (coldFieldAboveFrames R V k)) := by
    intro x
    refine integrable_mul_density_of_bounded hlaw (hC _ fun W hW k c X => ?_)
      (R := A.responseParams.Ka * R.coupling ^ (-(1 / 2) : ℝ) / R.params.weight 0)
      (fun k hk => abs_centered_le hr.bounds.site_family hσ hm hm3 x (hcold k hk))
    exact ((hr.bounds.site_family.smooth _ hm x W hW) k c X).sub contDiffAt_const
  have hk0 : ∀ b, ‖(0 : StepVariable (finiteCells (stepFrame R n))) b‖ < R.ballRadius := fun b => by simpa using hρ
  have shr : ∀ k : StepVariable (finiteCells (stepFrame R n)), (∀ b, ‖k b‖ < R.ballRadius) → ∀ x : TorusSite (n * R.params.side),
      minimalSiteShare (F := stepFrame R n) R.params.coupling (torusSiteInFrame (stepFrame R n) (stepFrame R n).depth x)
        (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) k) =
        levelShare R.params.coupling R.params.side R.depth Finset.univ x (coldFieldAboveFrames R V k) := by
    intro k hk x
    rw [hshare _ (hcold k hk) x]
    show _ = minimalSiteShare _ _ (readAtLevel _ _ (restrictToTorus _ _))
    rw [readAtLevel_restrictToTorus]
  have sB1 : ∀ k : StepVariable (finiteCells (stepFrame R n)),
      (coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) =
        ∑ x ∈ sitesInBlocks R.params.side {Y}, responseRemainder A.cold (n * R.params.side) x h (coldFieldAboveFrames R V k) := by
    intro k
    refine (hsum (fun y => remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h y
      (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) k)) Y).trans
      (Finset.sum_congr rfl fun x _ => ?_)
    show responseRemainder A.cold _ (toTorusSite _ (torusSiteInFrame _ _ x)) h _ = _
    rw [TopLevelSites.toTorusSite_torusSiteInFrame stepFrame_period_depth]
    rfl
  have sB2 : ∀ k : StepVariable (finiteCells (stepFrame R n)),
      (coldHalfLawOf R).blockSum (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (frameWeight h))
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) = ∑ x ∈ sitesInBlocks R.params.side {Y},
        blockMean R.params.side R.depth (n * R.params.side) x h * centered A.siteRemainder (n * R.params.side) x (coldFieldAboveFrames R V k) := by
    intro k
    refine (hsum (fun y => weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (frameWeight h) y
      (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) k)) Y).trans
      (Finset.sum_congr rfl fun x _ => ?_)
    show frameWeight h _ * centered A.siteRemainder _ (toTorusSite _ (torusSiteInFrame _ _ x)) _ = _
    rw [TopLevelSites.toTorusSite_torusSiteInFrame stepFrame_period_depth, hwt]
    rfl
  have sS : (coldHalfLawOf R).weightedFrameShares (frameWeight h) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) (coldTopField R V) =
      ∑ x ∈ sitesInBlocks R.params.side {Y}, blockMean R.params.side R.depth (n * R.params.side) x h *
        levelShare R.params.coupling R.params.side R.depth Finset.univ x (coldFieldAboveFrames R V 0) := by
    refine (hsum (fun y => frameWeight h y * minimalSiteShare (F := stepFrame R n) R.params.coupling y
      (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) 0)) Y).trans
      (Finset.sum_congr rfl fun x _ => ?_)
    show frameWeight h _ * minimalSiteShare _ _ _ = _
    rw [hwt, shr 0 hk0]
  have sM : ∀ k : StepVariable (finiteCells (stepFrame R n)), (∀ b, ‖k b‖ < R.ballRadius) →
      (coldHalfLawOf R).weightedShareIncrement (frameWeight h) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) =
        ∑ x ∈ sitesInBlocks R.params.side {Y}, blockMean R.params.side R.depth (n * R.params.side) x h *
          (levelShare R.params.coupling R.params.side R.depth Finset.univ x (coldFieldAboveFrames R V k) -
            levelShare R.params.coupling R.params.side R.depth Finset.univ x (coldFieldAboveFrames R V 0)) := by
    intro k hk
    refine (hsum (fun y => frameWeight h y * (minimalSiteShare (F := stepFrame R n) R.params.coupling y
      (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) k) -
      minimalSiteShare (F := stepFrame R n) R.params.coupling y
      (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) 0))) Y).trans
      (Finset.sum_congr rfl fun x _ => ?_)
    show frameWeight h _ * (minimalSiteShare _ _ _ - minimalSiteShare _ _ _) = _
    rw [hwt, shr k hk, shr 0 hk0]
  have hone : ∀ k : StepVariable (finiteCells (stepFrame R n)), (∀ b, ‖k b‖ < R.ballRadius) → ∀ x : TorusSite (n * R.params.side),
      centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) (constOneWeight _) =
        A.coeff * levelShare R.params.coupling R.params.side R.depth Finset.univ x (coldFieldAboveFrames R V k) +
          centered A.siteRemainder (n * R.params.side) x (coldFieldAboveFrames R V k) :=
    fun k hk x => hr.bounds.share_site _ hm x _ (hcold k hk)
  have hpt : ∀ k : StepVariable (finiteCells (stepFrame R n)), (∀ b, ‖k b‖ < R.ballRadius) →
      ∑ x ∈ sitesInBlocks R.params.side {Y}, centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) h =
        (coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h)
            (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) +
          A.coeff * (coldHalfLawOf R).weightedFrameShares (frameWeight h) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) (coldTopField R V) +
          A.coeff * (coldHalfLawOf R).weightedShareIncrement (frameWeight h) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) +
          (coldHalfLawOf R).blockSum (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (frameWeight h))
            (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) +
          ∑ x ∈ sitesInBlocks R.params.side {Y}, (blockMean R.params.side R.depth (n * R.params.side) x h *
            A.cold (n * R.params.side) x (trivialField (n * R.params.side)) (constOneWeight _) -
              A.cold (n * R.params.side) x (trivialField (n * R.params.side)) h) := by
    intro k hk
    rw [sB1, sS, sM k hk, sB2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hs := hone k hk x
    unfold centeredResponse at hs ⊢
    unfold responseRemainder
    linear_combination (blockMean R.params.side R.depth (n * R.params.side) x h) * hs
  have f1 : BallIntegrable (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V)) fun k =>
      (coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) := by
    have g1 := BallIntegrable.sum (sitesInBlocks R.params.side {Y}) hlaw (f := fun x k =>
      (centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) h +
        A.cold (n * R.params.side) x (trivialField (n * R.params.side)) h) +
      (-blockMean R.params.side R.depth (n * R.params.side) x h) *
        (centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) (constOneWeight _) +
        A.cold (n * R.params.side) x (trivialField (n * R.params.side)) (constOneWeight _))) fun x _ =>
      ((fA x h).add (BallIntegrable.const hlaw _)).add (((fA x _).add (BallIntegrable.const hlaw _)).const_mul _)
    refine g1.congr hlaw fun k _ => ?_
    rw [sB1]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold centeredResponse responseRemainder
    ring
  have f2 : BallIntegrable (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V)) fun k =>
      (coldHalfLawOf R).blockSum (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (frameWeight h))
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) := by
    have g1 := BallIntegrable.sum (sitesInBlocks R.params.side {Y}) hlaw (f := fun x k =>
      blockMean R.params.side R.depth (n * R.params.side) x h *
        centered A.siteRemainder (n * R.params.side) x (coldFieldAboveFrames R V k)) fun x _ => (fD x).const_mul _
    exact g1.congr hlaw fun k _ => (sB2 k).symm
  have f3 : BallIntegrable (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V)) fun k =>
      A.coeff * (coldHalfLawOf R).weightedShareIncrement (frameWeight h) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k
        (coldTopField R V) := by
    have g1 := BallIntegrable.sum (sitesInBlocks R.params.side {Y}) hlaw (f := fun x k =>
      blockMean R.params.side R.depth (n * R.params.side) x h *
        ((centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) (constOneWeight _) +
        (-1) * centered A.siteRemainder (n * R.params.side) x (coldFieldAboveFrames R V k)) +
        -(A.coeff * levelShare R.params.coupling R.params.side R.depth Finset.univ x (coldFieldAboveFrames R V 0)))) fun x _ =>
      (((fA x _).add ((fD x).const_mul _)).add (BallIntegrable.const hlaw _)).const_mul _
    refine g1.congr hlaw fun k hk => ?_
    rw [sM k hk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hone k hk x]
    ring
  have hmean := ballExpectation_sum (sitesInBlocks R.params.side {Y}) hlaw
    (f := fun x k => centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) h) fun x _ => fA x h
  have e0 := ballExpectation_congr hlaw hpt
  have c1 := BallIntegrable.const (ρ := R.ballRadius) (r := (coldHalfLawOf R).radialWeight)
    (Ψ := (coldHalfLawOf R).exponent (coldTopField R V)) hlaw
  rw [ballExpectation_add hlaw (((f1.add (c1 _)).add f3).add f2) (c1 _), ballExpectation_add hlaw ((f1.add (c1 _)).add f3) f2,
    ballExpectation_add hlaw (f1.add (c1 _)) f3, ballExpectation_add hlaw f1 (c1 _), ballExpectation_const hlaw,
    ballExpectation_const hlaw, ballExpectation_const_mul] at e0
  have e1 : ∑ x ∈ sitesInBlocks R.params.side {Y}, coldExpectationAbove R V (fun W => centeredResponse A.cold (n * R.params.side) x W h) =
      ∑ x ∈ sitesInBlocks R.params.side {Y}, ballExpectation (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V))
        (fun k => centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) h) := rfl
  rw [e1, ← hmean, e0, Finset.sum_sub_distrib]
  show _ = (coldHalfLawOf R).expectation (coldTopField R V) _ + _ + _ + _ + _
  simp only [ColdHalfLaw.expectation, ColdHalfLaw.expectationOf]
  ring
end Step
section Read
open YangMills.Construction.TopLevelSites
variable {L t n : ℕ}
theorem torusFrame_period_top (i : Fin 4) : (torusFrame L t n).period (torusFrame L t n).top i = n := period_top i
def frameBonds {k : ℕ} (L t : ℕ) (c : Fin k → TorusBond n) :
    Fin k → (torusFrame L t n).Site (torusFrame L t n).top × Fin 4 :=
  fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)
theorem readAtLevel_perturb [NeZero n] {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (V : TorusField n) :
    readAtLevel (torusFrame L t n) (torusFrame L t n).top (perturb c X σ V) =
      leftTranslate (ColdStepAtMirrorFrames.bondSpread (frameBonds L t c) X σ)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by apply _root_.YangMills.Construction.TopFamilyEvaluations.readAtLevel_perturb <;> assumption
theorem mixedDeriv_readAtLevel [NeZero n] (G : (torusFrame L t n).GaugeField (torusFrame L t n).top → ℝ) {k : ℕ}
    (V : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun W => G (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)) V c X =
      bondDeriv G (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) (frameBonds L t c) X := by apply _root_.YangMills.Construction.TopFamilyEvaluations.mixedDeriv_readAtLevel <;> assumption
theorem contDiffThreeAt_readAtLevel [NeZero n] {G : (torusFrame L t n).GaugeField (torusFrame L t n).top → ℝ} {V : TorusField n}
    (h : ContDiffThreeAlongBonds G (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)) :
    ContDiffThreeAt (fun W => G (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)) V := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.contDiffThreeAt_readAtLevel <;> assumption
theorem siteSupDist_torusSiteInFrame [NeZero n] (y z : TorusSite n) :
    siteSupDist (F := torusFrame L t n) (j := (torusFrame L t n).top)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z) = supDist y z := by apply _root_.YangMills.Construction.TopFamilyEvaluations.siteSupDist_torusSiteInFrame <;> assumption
theorem bondSpan_frameBonds [NeZero n] {k : ℕ} (y : TorusSite n) (c : Fin k → TorusBond n) :
    bondSpan (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y) (frameBonds L t c) = supportDiam y c := by apply _root_.YangMills.Construction.TopFamilyEvaluations.bondSpan_frameBonds <;> assumption
theorem isSmallCurvature_readAtLevel [NeZero n] {s : ℝ} {V : TorusField n} (hV : IsCold s V) :
    IsSmallCurvature (F := torusFrame L t n) s (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by apply _root_.YangMills.SharedProofs.p2155 <;> assumption
theorem eventually_isCold_perturb [NeZero n] {s : ℝ} {W : TorusField n} (hW : IsCold s W) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) : ∀ᶠ σ : Fin k → ℝ in 𝓝 0, IsCold s (perturb c X σ W) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.eventually_isCold_perturb <;> assumption
theorem contDiffThreeAt_and_mixedDeriv_of_eq [NeZero n] {G A B : TorusField n → ℝ} {d s : ℝ} {W : TorusField n} (hW : IsCold s W)
    (hkey : ∀ V, IsCold s V → G V = A V + B V + d) (hA : ContDiffThreeAt A W) (hB : ContDiffThreeAt B W) :
    ContDiffThreeAt G W ∧ ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
      mixedDeriv G W c X = mixedDeriv A W c X + mixedDeriv B W c X + mixedDeriv (fun _ => d) W c X := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.decomposition_contDiff_mixedDeriv <;> assumption
theorem mixedDeriv_const {d : ℝ} {k : ℕ} (hk : k ≠ 0) (W : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun _ => d) W c X = 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.mixedDeriv_const <;> assumption
end Read
section Numbers
theorem torusDecayFactor_pos (L : ℕ) (δ u : ℝ) : 0 < torusDecayFactor L δ u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
theorem exp_neg_le_div_torusDecayFactor {L : ℕ} {δ Cw κ u : ℝ} (hw : torusDecayFactor L δ u ≤ Cw * Real.exp (2 * δ * u))
    (hκ : 2 * δ ≤ κ) (hu : 0 ≤ u) : Real.exp (-(κ * u)) ≤ Cw / torusDecayFactor L δ u := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderExpectation.exp_neg_le_div_torusDecayFactor <;> assumption
end Numbers
end FrameFieldRemainder
set_option maxHeartbeats 1600000 in
open FrameFieldRemainder YangMills.Construction.TopLevelSites YangMills.Construction.Dilation YangMills.Construction.MomentLaw in
theorem stepRemainderAtFrameField_holds (hImg : coldStepAboveFramesStatement)
    (hLaw : coldHalfLawIsLawStatement) (hLin : coldStepLinearLocalStatement)
    (hOne : ResponseRemaindersOnTorus) (hGas : GasTermAtColdFields)
    (hWN : WeightsCloseToBlockMeans) (hMW : BlockMeanIsLinearAndLocal)
    (hExp : LinearResponse.DecayFactorExpBound) (hSh : ShareEvaluation.LevelShareEqMinimalSiteShare)
    (hRow : ColdExpansionRegular) (hCS : ColdChartSettingIsCold) :
    stepRemainderAtFrameFieldStatement := by
  classical
  intro a _
  obtain ⟨r₁, hr₁, hI⟩ := hImg
  obtain ⟨r₂, hr₂, hL⟩ := hLin
  obtain ⟨r₃, hr₃, hG⟩ := hGas
  refine ⟨0, fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)), ?_⟩
  intro T _ _ hD hCold hCH hrt
  obtain ⟨cn, nss, hties, hall⟩ := hCH
  obtain ⟨-, -, e_ρ, -, -, -, -, -⟩ := hties
  obtain ⟨hTs, Cnr, hNr⟩ : ColdRegimeEstimatesAt (T.stepParamsAt cn nss T.yC) ∧
      blockSumExpectationNearValueAt (T.stepParamsAt cn nss T.yC) := hall T.yC le_rfl
  have hLpos : 0 < T.side := lt_of_lt_of_le (by norm_num) hD.L_ge
  have hδ : 0 < T.rt / 2 ^ 10 := by
    have := hD.rt_pos
    positivity
  obtain ⟨Cw, hCw1, hCw⟩ := hExp T.side (T.rt / 2 ^ 10) hLpos hδ
  refine ⟨6 * T.Cs, fun K => ?_⟩
  obtain ⟨y₁, hy₁⟩ := hI T hD (hrt.trans (min_le_left _ _)) K
  obtain ⟨y₂, hy₂⟩ := hL T hD (hrt.trans ((min_le_right _ _).trans (min_le_left _ _))) K
  obtain ⟨y₃, hy₃⟩ := hG T hD (hrt.trans ((min_le_right _ _).trans (min_le_right _ _))) K
  obtain ⟨y₄, hy₄⟩ := hLaw T hD hCold
  obtain ⟨y₅, hy₅⟩ := hCS T hD
  let Ts : ColdStepAtMirrorFrames.StepParameters := T.stepParamsAt cn nss T.yC
  let Mx : ℝ := |Cnr| * |K.Kc| / Ts.η₃ * Cw + 12 * |Ts.CE| * Cw + 3 * |Ts.CE| * |K.Ka| / Ts.η₃ + 3
  have hch : 0 < T.gasRate := by
    have h1 := hD.cE_pos
    have h2 : 0 < T.threshold := hD.σ_pos
    have h3 : 0 < T.κ := hD.κ_pos
    have h4 : 0 < T.κ₁ := lt_min (by positivity) (by positivity)
    have h5 : 0 < min T.cE (min (T.κ * T.threshold ^ 2) (T.κ₁ * T.threshold ^ 2)) :=
      lt_min h1 (lt_min (by positivity) (by positivity))
    unfold RenormalizationStepParameters.ParameterAssignment.gasRate
    positivity
  have hch₂ : 0 < T.gasRate / 2 := by positivity
  obtain ⟨yE, hyE⟩ := TermCalculus.rpow_mul_exp_le_one hch₂ 1
  refine ⟨Mx, max (max y₁ y₂) (max (max y₃ y₄) (max (max y₅ T.yC) (max T.floorMin (max 1 yE)))), ?_⟩
  intro y hy R A hK hA hArr
  have f₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have f₂ : y₂ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have g₁ := le_trans (le_max_right _ _) hy
  have f₃ : y₃ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) g₁
  have f₄ : y₄ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) g₁
  have g₂ := le_trans (le_max_right _ _) g₁
  have f₅ : y₅ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) g₂
  have fC : T.yC ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) g₂
  have g₃ := le_trans (le_max_right _ _) g₂
  have f₀ : T.floorMin ≤ y := le_trans (le_max_left _ _) g₃
  have g₄ := le_trans (le_max_right _ _) g₃
  have fM : 1 ≤ y := le_trans (le_max_left _ _) g₄
  have fh : yE ≤ y := le_trans (le_max_right _ _) g₄
  have hI' := hy₁ y f₁ R A hK hA hCold
  have hL' := hy₂ y f₂ R A hK hA
  have hG' := hy₃ y f₃ R A hK hA hArr
  have hlaw' := hy₄ y f₄ R hA.onFamily
  have hcs' := hy₅ y f₅ R hA.onFamily
  have hresp := hA.admissible
  have hstep := hA.onFamily.isStep
  have hx : y ≤ R.coupling := hA.onFamily.le_coupling
  obtain ⟨ℓ, t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := R
  have e1 : ℓ = T.stepParameters y := hA.onFamily.params_eq
  have e2 : ρA = T.ρA := hA.onFamily.anchorRadius_eq
  have e3 : p = T.cutoff := hA.onFamily.barrierFn_eq
  subst e1 e2 e3
  let R : StepSetup := ⟨T.stepParameters y, t, x, x', D, f, Λ, Dq, Φ, φ, T.ρA, T.cutoff⟩
  have hσ : 0 < T.threshold := hD.σ_pos
  have hfits := hD.fits y f₀
  have hyx : y ≤ x := hx
  have hbelow : IsRegularFamily Ts.L t Ts.n₀ Ts.σ Ts.decayRate Ts.E Ts.energyRatio (localFamilyOfDensity f) :=
    hRow (T.stepParameters y) t x D f hfits rfl hstep.1.1
  have hxT : Ts.coupling ≤ x := fC.trans hx
  have hq : coldHalfLawAt Ts x (localFamilyOfDensity f) = coldHalfLawOf R := by
    show ColdHalfLaw.mk T.coupling cn.ρA _ x T.rt (frameRadius x) T.cutoff _ =
      ColdHalfLaw.mk T.coupling T.ρA _ x T.rt _ T.cutoff _
    rw [e_ρ]
    rfl
  have hKf : K.Admissible R.params := hK ▸ hresp.params_admissible
  have hrowK : ResponseBounds R.params K R.depth R.coupling A.coeff R.labels R.labelWeight A.score A.cold A.hull
      A.siteRemainder A.totalRemainder := hK ▸ hresp.bounds
  have hη₃ : K.η₃ = Ts.η₃ := by
    have h1 : T.E₃ = T.E / K.η₃ := hKf.E₃_eq
    have h2 : T.E₃ = T.E / T.η₃ := rfl
    have hE : 0 < T.E := hfits.E_pos
    have h3 := hKf.η₃_pos
    have h4 := hD.η₃_pos
    rw [h2, div_eq_div_iff h4.ne' h3.ne'] at h1
    exact mul_left_cancel₀ hE.ne' h1
  have hη₀ : 0 < Ts.η₃ := hD.η₃_pos
  have hη₁ : Ts.η₃ ≤ 1 := hD.η₃_le
  have hKc1 : 1 ≤ K.Kc := hKf.Kc_ge
  have hKa : 0 ≤ K.Ka := hKf.Ka_nonneg
  have hCE : 0 ≤ Ts.CE := hD.CE_pos.le
  have hCs : 0 < Ts.Cs := hD.Cs_pos
  have hCw0 : 0 ≤ Cw := by linarith
  have hx0 : 0 < x := by linarith
  have hxs : 0 ≤ x ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hx0.le _
  have hg0 : 0 ≤ Real.exp (-(T.gasRate * x / 2)) := (Real.exp_pos _).le
  have hal := hresp.abs_coeff_le
  have hwgt : ∀ s : ℕ, torusDecayFactor (T.stepParameters y).side Ts.decayRate s = (T.stepParameters y).weight s := fun s => rfl
  have hLodd : Odd R.params.side := hD.L_odd
  have hL1 : (1 : ℝ) ≤ (T.side : ℝ) := by exact_mod_cast hLpos
  have hn₀ : 4096 ≤ T.n₀ := hD.n₀_ge
  intro n _ hn Y h c₁ c₂
  have hnT : T.n₀ ≤ n := hn
  have hm : R.params.n₀ ≤ n * R.params.side := hn.trans (Nat.le_mul_of_pos_right n hLpos)
  have hm3 : 2 < n * R.params.side := by
    have h4 : T.n₀ ≤ n * R.params.side := hm
    omega
  have hlip0 : 0 ≤ weightLipschitz R.params.side (R.depth + 1) h :=
    Real.iSup_nonneg fun _ => div_nonneg (abs_nonneg _) (barycentreDist_nonneg _ _)
  obtain ⟨lip, hlipdef⟩ : ∃ lip, lip = weightLipschitz R.params.side (R.depth + 1) h := ⟨_, rfl⟩
  rw [← hlipdef] at hlip0 ⊢
  obtain ⟨c, hcdef⟩ : ∃ c, c = blockMean R.params.side (R.depth + 1) n Y h := ⟨_, rfl⟩
  obtain ⟨h₁, hh₁⟩ : ∃ h₁ : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n), h₁ = clampedShift (3 * lip) c h := ⟨_, rfl⟩
  have hB : 0 ≤ 3 * lip := by linarith
  have wn₁ := hWN R.params.side hLodd (R.depth + 1) n Y
  have hat_eq : ∀ p, IsPlaquetteAt R.params.side (R.depth + 1) Y p → h₁ p = h p - c := fun p hp => by
    rw [hh₁]
    refine clamp_eq_self ?_
    rw [hcdef, hlipdef]
    exact wn₁.2.1 h p hp
  have hat₀ : blockMean R.params.side (R.depth + 1) n Y h₁ = 0 := by
    have m₁ := hMW R.params.side hLodd (R.depth + 1) n Y
    have e₁ := m₁.2.2 h₁ (fun p => 1 * h p + (-c) * constOneWeight _ p) (fun p hp => by
      rw [hat_eq p hp]
      simp only [constOneWeight]
      ring)
    rw [e₁, m₁.2.1 1 (-c) h (constOneWeight _), m₁.1, ← hcdef]
    ring
  have hsup : weightSup h₁ ≤ 3 * lip := by
    rw [hh₁]
    exact weightSup_clampedShift_le hB c h
  have hlip₁ : weightLipschitz R.params.side R.depth h₁ ≤ weightLipschitz R.params.side R.depth h := by
    rw [hh₁]
    exact weightLipschitz_clampedShift_le _ _ h
  have hlevel : (T.side : ℝ) * weightLipschitz R.params.side R.depth h = lip := by
    rw [hlipdef]
    exact mul_weightLipschitz_succ hLpos h
  have hlip₁0 : 0 ≤ weightLipschitz R.params.side R.depth h₁ :=
    Real.iSup_nonneg fun _ => div_nonneg (abs_nonneg _) (barycentreDist_nonneg _ _)
  have hLe₁ : (T.side : ℝ) * weightLipschitz R.params.side R.depth h₁ ≤ lip := by
    rw [← hlevel]
    exact mul_le_mul_of_nonneg_left hlip₁ (by linarith)
  have hsize : weightNorm R.params.side R.depth h₁ ≤ 3 * lip := by
    refine max_le hsup ?_
    have h2 : weightLipschitz R.params.side R.depth h₁ ≤ (T.side : ℝ) * weightLipschitz R.params.side R.depth h₁ :=
      le_mul_of_one_le_left hlip₁0 hL1
    linarith
  have hw : ∀ z, |frameWeight (R := R) (n := n) h₁ z| ≤ 3 * lip := fun z =>
    ((hWN R.params.side hLodd R.depth (n * R.params.side) (toTorusSite _ z)).1 h₁).trans hsup
  have one := hOne (T.stepParameters y) R.depth (stepFrame R n) (n * R.params.side) Ts.decayRate hwgt stepFrame_period_depth hm
  have he : 0 ≤ K.Kc * weightLipschitz R.params.side R.depth h₁ := mul_nonneg (by linarith) hlip₁0
  have he₂ : 0 ≤ 3 * lip * (K.Ka * x ^ (-(1 / 2) : ℝ)) := mul_nonneg hB (mul_nonneg hKa hxs)
  have hr : IsTorusRemainder Ts.L Ts.σ Ts.decayRate (K.Kc * weightLipschitz R.params.side R.depth h₁)
      (K.Kc * weightLipschitz R.params.side R.depth h₁ / Ts.η₃)
      (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁) := by
    have h2 := one.1 K A.cold (fun z g W hW h' => hrowK.cold_gauge _ hm z g W hW h')
      ⟨hrowK.remainder_smooth, hrowK.remainder_decay, hrowK.remainder_local⟩ h₁
    rw [hη₃] at h2
    exact h2
  have hr₂ : IsTorusRemainder Ts.L Ts.σ Ts.decayRate (3 * lip * (K.Ka * x ^ (-(1 / 2) : ℝ)))
      (3 * lip * (K.Ka * x ^ (-(1 / 2) : ℝ)) / Ts.η₃)
      (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (frameWeight (R := R) (n := n) h₁)) := by
    have h2 := one.2 _ _ (3 * lip) A.siteRemainder _ hrowK.site_family hB hw
    rw [hη₃, ← mul_div_assoc] at h2
    exact h2
  have htop : IsCubicTopTorus Ts.L R.depth Ts.n₀ (stepFrame R n) := ⟨rfl, rfl, n, fun _ => rfl, hn⟩
  have c54 : ∀ {V : TorusField n}, IsCold R.params.threshold V →
      IsSmallCurvature (5 / 4 * Ts.σ) (readAtLevel (stepFrame R n) (stepFrame R n).top V) :=
    fun hV => isSmallCurvature_readAtLevel fun z μ ν hμ =>
      (hV z μ ν hμ).trans (by show T.threshold < 5 / 4 * T.threshold; linarith)
  have hflat : IsCold R.params.threshold (trivialField n) := TermCalculus.isCold_trivialField hσ n
  have hV9f : IsCold (9 / 8 * T.threshold) (trivialField n) := TermCalculus.isCold_trivialField (by positivity) n
  have hsum := (hlaw' n hnT (trivialField n) hV9f).2.2.2.2
  obtain ⟨b1, -⟩ := hTs.blockRemainder R.depth x _ (localFamilyOfDensity f) (stepFrame R n)
    (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y)
    hxT hbelow htop he hr
  obtain ⟨s1, -⟩ := hTs.frameShares R.depth x (3 * lip) (localFamilyOfDensity f) (stepFrame R n)
    (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) (frameWeight (R := R) (n := n) h₁) hxT htop hB hw
  obtain ⟨m1, -⟩ := (hTs.smoothIncrements R.depth x (localFamilyOfDensity f) hxT hbelow).2.2.2.2.2 (stepFrame R n)
    (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) (frameWeight (R := R) (n := n) h₁) (3 * lip) hB hw htop
  obtain ⟨r1, -⟩ := hTs.meanRemainder R.depth x _ (localFamilyOfDensity f) (stepFrame R n)
    (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (frameWeight (R := R) (n := n) h₁))
    (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) hxT hbelow htop he₂ hr₂
  rw [hq] at b1 s1 m1 r1
  have hsmH : ∀ V : TorusField n, IsCold R.params.threshold V → ContDiffThreeAlongBonds
      (frameTerms (coldHalfLawOf R) A.coeff (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁)
        (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (frameWeight (R := R) (n := n) h₁))
        (frameWeight (R := R) (n := n) h₁) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y))
      (readAtLevel (stepFrame R n) (stepFrame R n).top V) := fun V hV =>
    frameTerms_contDiffThree (b1 _ (c54 hV)).1 (s1 _ (c54 hV)).1 (m1 _ (c54 hV)).1 (r1 _ (c54 hV)).1
  have key : ∀ V : TorusField n, IsCold R.params.threshold V → responseRemainder A.coldStep n Y h V =
      frameTerms (coldHalfLawOf R) A.coeff (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁)
          (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (frameWeight (R := R) (n := n) h₁))
          (frameWeight (R := R) (n := n) h₁) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y)
          (readAtLevel (stepFrame R n) (stepFrame R n).top V) + gasTermAtBlock A (coldCaseGround R V) Y h₁ +
        ∑ z ∈ sitesInBlocks R.params.side {Y}, blockMean R.params.side R.depth (n * R.params.side) z h₁ *
          A.cold (n * R.params.side) z (trivialField (n * R.params.side)) (constOneWeight _) := by
    intro V hV
    have hV9 : IsCold (9 / 8 * T.threshold) V := fun z μ ν hμ =>
      (hV z μ ν hμ).trans (by show T.threshold < 9 / 8 * T.threshold; linarith)
    obtain ⟨L1, L2, L3, L4, L5⟩ := hlaw' n hnT V hV9
    have hcoldk : ∀ k : StepVariable (finiteCells (stepFrame R n)), (∀ b, ‖k b‖ < R.ballRadius) →
        IsCold R.params.threshold (coldFieldAboveFrames R V k) := by
      intro k hk
      obtain ⟨η, hηb, e⟩ := L3 k hk
      have h2 := hcs' n hnT V hV9 η fun b => (hηb b).le
      rw [← e]
      intro z μ ν hμ
      exact (h2 z μ ν hμ).trans (by show T.threshold / 4 < T.threshold; linarith)
    have hρ : 0 < R.ballRadius := by
      show 0 < T.threshold / 64
      positivity
    have mp := block_expectations_eq_frameTerms A hresp hfits.σ_pos hm hm3 V L1 L2 hcoldk L4 L5
      (fun W hW z => hSh T hD R.depth n hnT W hW z) hρ Y h₁
    have lin := hL' n hn Y V hV
    have l1 := lin.1 (-c) (constOneWeight _) h
    have l2 := lin.2 ((-c) • constOneWeight _ + h) h₁ (fun p hp => by
      rw [hat_eq p hp]
      simp only [Pi.add_apply, Pi.smul_apply, constOneWeight, smul_eq_mul]
      ring)
    have img := hI' n hn Y V hV h₁
    have e₀ : responseRemainder A.coldStep n Y h V = A.coldStep n Y V h₁ := by
      unfold responseRemainder
      rw [← l2, l1, ← hcdef]
      ring
    rw [e₀, img]
    unfold coldTermAbove
    rw [hat₀]
    simp only [mul_zero, zero_mul, add_zero]
    linarith
  have hc0 := c54 hflat
  have hgas := hG'.1 n hn Y (trivialField n) hflat h₁
  have pr := (contDiffThreeAt_and_mixedDeriv_of_eq hflat key (contDiffThreeAt_readAtLevel (hsmH _ hflat)) hgas.2.1).2 2
    ![c₁, c₂] ![unitGenerator, unitGenerator] (by norm_num)
  rw [mixedDeriv_readAtLevel, mixedDeriv_const (by norm_num), add_zero,
    bondDeriv_frameTerms (b1 _ hc0).1 (s1 _ hc0).1 (m1 _ hc0).1 (r1 _ hc0).1 (by norm_num)
      (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator]] at pr
  have hup : ∀ z ∈ sitesInBlocks R.params.side {Y}, ∀ p, IsPlaquetteAt R.params.side R.depth z p →
      IsPlaquetteAt R.params.side (R.depth + 1) Y p := fun z hz p hp => by
    obtain ⟨c', hc', hcz⟩ := hp.2
    exact ⟨hp.1, c', hc', Finset.mem_biUnion.mpr ⟨z, hz, hcz⟩⟩
  have hhat : ∀ z ∈ sitesInBlocks R.params.side {Y}, blockMean R.params.side R.depth (n * R.params.side) z h₁ =
      blockMean R.params.side R.depth (n * R.params.side) z h - blockMean R.params.side (R.depth + 1) n Y h := by
    intro z hz
    have m₁ := hMW R.params.side hLodd R.depth (n * R.params.side) z
    have e₃ := m₁.2.2 h₁ (fun p => 1 * h p + (-c) * constOneWeight _ p) (fun p hp => by
      rw [hat_eq p (hup z hz p hp)]
      simp only [constOneWeight]
      ring)
    rw [e₃, m₁.2.1 1 (-c) h (constOneWeight _), m₁.1, ← hcdef]
    ring
  have hrest : ∀ z ∈ sitesInBlocks R.params.side {Y}, ∀ W : TorusField (n * R.params.side), IsCold R.params.threshold W →
      responseRemainder A.cold (n * R.params.side) z h₁ W = responseRemainder A.cold (n * R.params.side) z h W := by
    intro z hz W hW
    obtain ⟨oneW, hone⟩ : ∃ oneW : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)),
      oneW = constOneWeight _ := ⟨_, rfl⟩
    obtain ⟨h', hh'⟩ : ∃ h' : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)), h' = h := ⟨_, rfl⟩
    have r₁ : A.cold (n * R.params.side) z W h₁ = A.cold (n * R.params.side) z W ((-c) • oneW + h') :=
      hrowK.cold_reads _ hm z W hW h₁ ((-c) • oneW + h') (fun p hp => by
        rw [hat_eq p (hup z hz p hp), hone, hh']
        show h p - c = (-c) * (1 : ℝ) + h p
        ring)
    have r₂ : A.cold (n * R.params.side) z W ((-c) • oneW + h') =
        (-c) * A.cold (n * R.params.side) z W oneW + A.cold (n * R.params.side) z W h' :=
      hrowK.cold_linear _ hm z W hW (-c) oneW h'
    have g₁ : responseRemainder A.cold (n * R.params.side) z h₁ W = A.cold (n * R.params.side) z W h₁ -
        blockMean R.params.side R.depth (n * R.params.side) z h₁ * A.cold (n * R.params.side) z W oneW := by
      rw [hone]
      rfl
    have g₂ : responseRemainder A.cold (n * R.params.side) z h W = A.cold (n * R.params.side) z W h' -
        blockMean R.params.side R.depth (n * R.params.side) z h * A.cold (n * R.params.side) z W oneW := by
      rw [hone, hh']
      rfl
    rw [g₁, g₂, r₁, r₂, hhat z hz, ← hcdef]
    ring
  have hcoldF : ∀ V : TorusField n, IsCold R.params.threshold V → IsCold R.params.threshold (coldFieldAboveFrames R V 0) := by
    intro V hV
    have hV9 : IsCold (9 / 8 * T.threshold) V := fun z μ ν hμ =>
      (hV z μ ν hμ).trans (by show T.threshold < 9 / 8 * T.threshold; linarith)
    obtain ⟨L1, L2, L3, L4, L5⟩ := hlaw' n hnT V hV9
    have hρ : 0 < R.ballRadius := by
      show 0 < T.threshold / 64
      positivity
    have hk0 : ∀ b, ‖(0 : StepVariable (finiteCells (stepFrame R n))) b‖ < R.ballRadius := fun b => by simpa using hρ
    obtain ⟨η, hηb, e⟩ := L3 0 hk0
    have h2 := hcs' n hnT V hV9 η fun b => (hηb b).le
    rw [← e]
    intro z μ ν hμ
    exact (h2 z μ ν hμ).trans (by show T.threshold / 4 < T.threshold; linarith)
  have e₁ : hessianAtIdentity (fun V : TorusField n => ∑ z ∈ sitesInBlocks R.params.side {Y},
      responseRemainder A.cold (n * R.params.side) z h (coldFieldAboveFrames R V 0)) c₁ c₂ =
      bondDeriv ((coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) 0) (readAtLevel (stepFrame R n) (stepFrame R n).top (trivialField n))
        (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator] := by
    have e : ∀ V : TorusField n, IsCold R.params.threshold V → ∑ z ∈ sitesInBlocks R.params.side {Y},
        responseRemainder A.cold (n * R.params.side) z h (coldFieldAboveFrames R V 0) =
        (coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁)
          (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) 0 (readAtLevel (stepFrame R n) (stepFrame R n).top V) := by
      intro V hV
      have e₀ : ∑ z ∈ sitesInBlocks R.params.side {Y}, responseRemainder A.cold (n * R.params.side) z h (coldFieldAboveFrames R V 0) =
          ∑ z ∈ sitesInBlocks R.params.side {Y}, responseRemainder A.cold (n * R.params.side) z h₁ (coldFieldAboveFrames R V 0) :=
        Finset.sum_congr rfl fun z hz => (hrest z hz _ (hcoldF V hV)).symm
      rw [e₀]
      refine ((hsum (fun z => remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁ z
        (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) 0)) Y).trans
        (Finset.sum_congr rfl fun z _ => ?_)).symm
      show responseRemainder A.cold _ (toTorusSite _ (torusSiteInFrame _ _ z)) h₁ _ = _
      rw [TopLevelSites.toTorusSite_torusSiteInFrame stepFrame_period_depth]
      rfl
    have hev : (fun σ : Fin 2 → ℝ => ∑ z ∈ sitesInBlocks R.params.side {Y}, responseRemainder A.cold (n * R.params.side) z h
        (coldFieldAboveFrames R (TorusFields.perturb ![c₁, c₂] ![unitGenerator, unitGenerator] σ (trivialField n)) 0)) =ᶠ[𝓝 0]
        fun σ => (coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁)
          (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) 0 (readAtLevel (stepFrame R n) (stepFrame R n).top
            (TorusFields.perturb ![c₁, c₂] ![unitGenerator, unitGenerator] σ (trivialField n))) :=
      (eventually_isCold_perturb hflat ![c₁, c₂] ![unitGenerator, unitGenerator]).mono fun σ hσ' => e _ hσ'
    have h₂ := mixedDeriv_readAtLevel (L := R.params.side) (t := R.depth)
      ((coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) 0) (trivialField n) ![c₁, c₂] ![unitGenerator, unitGenerator]
    rw [← h₂]
    unfold hessianAtIdentity mixedDeriv
    exact congrFun (congrArg _ ((hev.iteratedFDeriv ℝ 2).self_of_nhds)) _
  have hshV : ∀ V : TorusField n, IsCold R.params.threshold V → ∑ z ∈ sitesInBlocks R.params.side {Y},
      (blockMean R.params.side R.depth (n * R.params.side) z h - blockMean R.params.side (R.depth + 1) n Y h) *
        levelShare R.params.coupling R.params.side R.depth Finset.univ z (coldFieldAboveFrames R V 0) =
      (coldHalfLawOf R).weightedFrameShares (frameWeight (R := R) (n := n) h₁) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y)
        (readAtLevel (stepFrame R n) (stepFrame R n).top V) := by
    intro V hV
    have hW := hcoldF V hV
    have hwt : ∀ z : TorusSite (n * R.params.side), frameWeight (R := R) (n := n) h₁ (torusSiteInFrame (stepFrame R n) (stepFrame R n).depth z) =
        blockMean R.params.side R.depth (n * R.params.side) z h₁ := fun z => by
      unfold frameWeight
      rw [TopLevelSites.toTorusSite_torusSiteInFrame stepFrame_period_depth]
    refine ((hsum (fun z => frameWeight (R := R) (n := n) h₁ z * minimalSiteShare (F := stepFrame R n) R.params.coupling z
      (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) 0)) Y).trans
      (Finset.sum_congr rfl fun z hz => ?_)).symm
    show frameWeight _ _ * minimalSiteShare _ _ _ = _
    have hs : levelShare R.params.coupling R.params.side R.depth Finset.univ z (coldFieldAboveFrames R V 0) =
        minimalSiteShare (F := stepFrame R n) R.params.coupling (torusSiteInFrame (stepFrame R n) (stepFrame R n).depth z)
        (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) 0) := by
      have h3 := hSh T hD R.depth n hnT _ hW z
      refine h3.trans ?_
      exact congrArg (minimalSiteShare (F := stepFrame R n) R.params.coupling
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).depth z)) (readAtLevel_restrictToTorus _)
    rw [hwt, hs, hhat z hz]
  have e₂ : hessianAtIdentity (fun V : TorusField n => ∑ z ∈ sitesInBlocks R.params.side {Y},
      (blockMean R.params.side R.depth (n * R.params.side) z h - blockMean R.params.side (R.depth + 1) n Y h) *
        levelShare R.params.coupling R.params.side R.depth Finset.univ z (coldFieldAboveFrames R V 0)) c₁ c₂ =
      bondDeriv ((coldHalfLawOf R).weightedFrameShares (frameWeight (R := R) (n := n) h₁)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y)) (readAtLevel (stepFrame R n) (stepFrame R n).top (trivialField n))
        (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator] := by
    have hev : (fun σ : Fin 2 → ℝ => ∑ z ∈ sitesInBlocks R.params.side {Y},
        (blockMean R.params.side R.depth (n * R.params.side) z h - blockMean R.params.side (R.depth + 1) n Y h) *
        levelShare R.params.coupling R.params.side R.depth Finset.univ z
          (coldFieldAboveFrames R (TorusFields.perturb ![c₁, c₂] ![unitGenerator, unitGenerator] σ (trivialField n)) 0)) =ᶠ[𝓝 0]
        fun σ => (coldHalfLawOf R).weightedFrameShares (frameWeight (R := R) (n := n) h₁)
          (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) (readAtLevel (stepFrame R n) (stepFrame R n).top
            (TorusFields.perturb ![c₁, c₂] ![unitGenerator, unitGenerator] σ (trivialField n))) :=
      (eventually_isCold_perturb hflat ![c₁, c₂] ![unitGenerator, unitGenerator]).mono fun σ hσ' => hshV _ hσ'
    have h₂ := mixedDeriv_readAtLevel (L := R.params.side) (t := R.depth)
      ((coldHalfLawOf R).weightedFrameShares (frameWeight (R := R) (n := n) h₁) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y))
      (trivialField n) ![c₁, c₂] ![unitGenerator, unitGenerator]
    rw [← h₂]
    unfold hessianAtIdentity mixedDeriv
    exact congrFun (congrArg _ ((hev.iteratedFDeriv ℝ 2).self_of_nhds)) _
  have hunit : AreUnitVectors ![unitGenerator, unitGenerator] := by
    intro l
    fin_cases l <;> exact SingleColourFields.norm_unitGenerator
  have hGe : torusDecayFactor Ts.L Ts.decayRate (bondSpan (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y)
      (frameBonds R.params.side R.depth ![c₁, c₂])) = R.params.weight (tripleDiam Y c₁ c₂) := by
    rw [bondSpan_frameBonds]
    rfl
  obtain ⟨G, hGd⟩ : ∃ G, G = R.params.weight (tripleDiam Y c₁ c₂) := ⟨_, rfl⟩
  have hGp : 0 < G := by
    rw [hGd, ← hGe]
    exact torusDecayFactor_pos _ _ _
  have hu : (0 : ℝ) ≤ (bondSpan (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y)
      (frameBonds R.params.side R.depth ![c₁, c₂]) : ℝ) := Nat.cast_nonneg _
  have hex5 : Real.exp (-(Ts.κ / 2 ^ 5 * (bondSpan (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y)
      (frameBonds R.params.side R.depth ![c₁, c₂]) : ℝ))) ≤ Cw / G := by
    rw [hGd, ← hGe]
    exact exp_neg_le_div_torusDecayFactor (hCw _ hu) (by
      show 2 * (T.rt / 2 ^ 10) ≤ T.rt / 2 ^ 5
      have := hD.rt_pos
      linarith) hu
  have hex6 : Real.exp (-(Ts.κ / 2 ^ 6 * (bondSpan (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y)
      (frameBonds R.params.side R.depth ![c₁, c₂]) : ℝ))) ≤ Cw / G := by
    rw [hGd, ← hGe]
    exact exp_neg_le_div_torusDecayFactor (hCw _ hu) (by
      show 2 * (T.rt / 2 ^ 10) ≤ T.rt / 2 ^ 6
      have := hD.rt_pos
      linarith) hu
  have ts := (s1 _ hc0).2 2 (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator] (by norm_num) (by norm_num) hunit
  have tm := (m1 _ hc0).2 2 (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator] (by norm_num) (by norm_num) hunit
  have tr := (r1 _ hc0).2 2 (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator] (by norm_num) (by norm_num) hunit
  have tg := hgas.2.2 2 ![c₁, c₂] ![unitGenerator, unitGenerator] (by norm_num) (by norm_num) hunit
  rw [hGe, ← hGd] at ts tr
  set u := x ^ (-(1 / 2) : ℝ) with hu₀
  have hδs : 0 ≤ Ts.decayRate := by
    have := hD.rt_pos
    show 0 ≤ T.rt / 2 ^ 10
    positivity
  set E₆ := Real.exp (-(Ts.κ / 2 ^ 6 * (bondSpan (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y)
    (frameBonds R.params.side R.depth ![c₁, c₂]) : ℝ))) with hE₆
  have hE₆0 : 0 ≤ E₆ := (Real.exp_pos _).le
  have tb : |bondDeriv ((coldHalfLawOf R).expectationOf ((coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁)
      (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y))) (readAtLevel (stepFrame R n) (stepFrame R n).top (trivialField n))
      (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator] -
      bondDeriv ((coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁)
      (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) 0) (readAtLevel (stepFrame R n) (stepFrame R n).top (trivialField n))
      (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator]| ≤
      |Cnr| / Ts.η₃ * u * E₆ * (K.Kc * weightLipschitz R.params.side R.depth h₁) := by
    set P := |Cnr| / Ts.η₃ * u * E₆ with hP
    have hP0 : 0 ≤ P := by positivity
    refine le_of_forall_pos_le_add fun ε' hε' => ?_
    set ε := ε' / (P + 1) with hε
    have hε0 : 0 < ε := by positivity
    have hpos : 0 < K.Kc * weightLipschitz R.params.side R.depth h₁ + ε := add_pos_of_nonneg_of_pos he hε0
    have hr' := isTorusRemainder_mono hδs he (le_add_of_nonneg_right hε0.le) hη₀ hr
    have st : IsAdmissibleAt Ts R.depth x (localFamilyOfDensity f) (stepFrame R n)
        (readAtLevel (stepFrame R n) (stepFrame R n).top (trivialField n)) :=
      ⟨hxT, ⟨hbelow.smooth, hbelow.gauge_invariant, hbelow.translation_invariant, hbelow.decay, hbelow.locality⟩, htop, hc0⟩
    have hn₁ := hNr R.depth x _ (localFamilyOfDensity f) (stepFrame R n) (readAtLevel (stepFrame R n) (stepFrame R n).top (trivialField n))
      (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) 2
      (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator] st hbelow hpos hr'
      (by norm_num) le_rfl hunit
    rw [hq] at hn₁
    have hn₂ : |bondDeriv ((coldHalfLawOf R).expectationOf ((coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y))) (readAtLevel (stepFrame R n) (stepFrame R n).top (trivialField n))
        (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator] -
        bondDeriv ((coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) 0) (readAtLevel (stepFrame R n) (stepFrame R n).top (trivialField n))
        (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator]| ≤
        Cnr * ((K.Kc * weightLipschitz R.params.side R.depth h₁ + ε) / Ts.η₃) * u * E₆ := hn₁
    refine hn₂.trans ?_
    have hb₁ : Cnr * ((K.Kc * weightLipschitz R.params.side R.depth h₁ + ε) / Ts.η₃) * u * E₆ ≤
        P * (K.Kc * weightLipschitz R.params.side R.depth h₁ + ε) := by
      have e₁ : P * (K.Kc * weightLipschitz R.params.side R.depth h₁ + ε) =
          |Cnr| * ((K.Kc * weightLipschitz R.params.side R.depth h₁ + ε) / Ts.η₃) * u * E₆ := by
        rw [hP]
        ring
      rw [e₁]
      have : 0 ≤ (K.Kc * weightLipschitz R.params.side R.depth h₁ + ε) / Ts.η₃ := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self _) this) hxs) hE₆0
    have hb₂ : P * ε ≤ ε' := by
      rw [hε, mul_div_assoc']
      refine div_le_of_le_mul₀ (by positivity) hε'.le ?_
      rw [show ε' * (P + 1) = P * ε' + ε' by ring]
      linarith only [hε']
    have e₃ : P * (K.Kc * weightLipschitz R.params.side R.depth h₁ + ε) =
        P * (K.Kc * weightLipschitz R.params.side R.depth h₁) + P * ε := by ring
    linarith only [hb₁, hb₂, e₃]
  have hlt : weightLipschitz R.params.side R.depth h₁ ≤ lip := by
    have h2 : weightLipschitz R.params.side R.depth h₁ ≤ (T.side : ℝ) * weightLipschitz R.params.side R.depth h₁ :=
      le_mul_of_one_le_left hlip₁0 hL1
    exact h2.trans hLe₁
  have hxx : 1 ≤ x := fM.trans hx
  have hexp : Real.exp (-(T.gasRate * x / 2)) ≤ u := by
    have h₁' := hyE x (fh.trans hx)
    have e₃ : Real.exp (-(T.gasRate / 2 * x)) = Real.exp (-(T.gasRate * x / 2)) := by
      congr 1
      ring
    rw [e₃, one_mul] at h₁'
    have hE0 := Real.exp_pos (-(T.gasRate * x / 2))
    have hp : x ^ (1 / 2 : ℝ) ≤ x ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hxx (by norm_num)
    have hm₁ : u * x ^ (1 / 2 : ℝ) = 1 := by
      rw [hu₀, ← Real.rpow_add hx0]
      norm_num
    have hu0 : 0 ≤ u := hxs
    calc Real.exp (-(T.gasRate * x / 2)) = u * (x ^ (1 / 2 : ℝ) * Real.exp (-(T.gasRate * x / 2))) := by
          rw [← mul_assoc, hm₁, one_mul]
      _ ≤ u * (x ^ (3 / 2 : ℝ) * Real.exp (-(T.gasRate * x / 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp hE0.le) hu0
      _ ≤ u * 1 := mul_le_mul_of_nonneg_left h₁' hu0
      _ = u := mul_one _
  have hCE₀ : Ts.CE ≤ |Ts.CE| := le_abs_self _
  have hη₀' : 0 < Ts.η₃ := hη₀
  have hu0 : 0 ≤ u := hxs
  have hCwG : 0 ≤ Cw / G := by positivity
  rw [← hGd]
  refine ⟨?_, ?_⟩
  · rw [e₂]
    refine ts.trans ?_
    have hCsT : Ts.Cs = T.Cs := rfl
    rw [hCsT]
    have hz : 0 ≤ T.Cs * lip := mul_nonneg hCs.le hlip0
    rw [div_le_div_iff_of_pos_right hGp]
    linarith only [hz]
  · have pr' : hessianAtIdentity (responseRemainder A.coldStep n Y h) c₁ c₂ = _ := pr
    rw [pr', e₁, e₂]
    have a₁ : |bondDeriv ((coldHalfLawOf R).expectationOf ((coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y))) (readAtLevel (stepFrame R n) (stepFrame R n).top (trivialField n))
        (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator] -
        bondDeriv ((coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) 0) (readAtLevel (stepFrame R n) (stepFrame R n).top (trivialField n))
        (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator]| ≤
        (|Cnr| * |K.Kc| / Ts.η₃ * Cw) * u * lip / G := by
      refine tb.trans ?_
      have h₂ : K.Kc * weightLipschitz R.params.side R.depth h₁ ≤ |K.Kc| * lip :=
        mul_le_mul (le_abs_self _) hlt hlip₁0 (abs_nonneg _)
      have e₃ : (|Cnr| * |K.Kc| / Ts.η₃ * Cw) * u * lip / G = |Cnr| / Ts.η₃ * u * (Cw / G) * (|K.Kc| * lip) := by
        field_simp
      rw [e₃]
      have p₁ : 0 ≤ |Cnr| / Ts.η₃ * u := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left hex6 p₁) h₂ he (mul_nonneg p₁ hCwG)
    have a₂ : |A.coeff * bondDeriv ((coldHalfLawOf R).expectationOf ((coldHalfLawOf R).weightedShareIncrement
        (frameWeight (R := R) (n := n) h₁) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y)))
        (readAtLevel (stepFrame R n) (stepFrame R n).top (trivialField n))
        (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator]| ≤
        (6 * |Ts.CE| * Cw) * u * lip / G := by
      rw [abs_mul]
      have h₃ : |bondDeriv ((coldHalfLawOf R).expectationOf ((coldHalfLawOf R).weightedShareIncrement
          (frameWeight (R := R) (n := n) h₁) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y)))
          (readAtLevel (stepFrame R n) (stepFrame R n).top (trivialField n))
          (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator]| ≤
          |Ts.CE| * (3 * lip * u) * (Cw / G) := by
        refine tm.trans ?_
        exact mul_le_mul (mul_le_mul_of_nonneg_right hCE₀ (by positivity)) hex5 (Real.exp_pos _).le (by positivity)
      have e₃ : (6 * |Ts.CE| * Cw) * u * lip / G = 2 * (|Ts.CE| * (3 * lip * u) * (Cw / G)) := by
        field_simp
        ring
      rw [e₃]
      exact mul_le_mul hal h₃ (abs_nonneg _) (by norm_num)
    have a₃ : |bondDeriv ((coldHalfLawOf R).expectationOf ((coldHalfLawOf R).blockSum
        (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (frameWeight (R := R) (n := n) h₁))
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y))) (readAtLevel (stepFrame R n) (stepFrame R n).top (trivialField n))
        (frameBonds R.params.side R.depth ![c₁, c₂]) ![unitGenerator, unitGenerator]| ≤
        (3 * |Ts.CE| * |K.Ka| / Ts.η₃) * u * lip / G := by
      refine tr.trans ?_
      have e₃ : (3 * |Ts.CE| * |K.Ka| / Ts.η₃) * u * lip / G = |Ts.CE| * (3 * lip * (|K.Ka| * u) / Ts.η₃) / G := by
        field_simp
      rw [e₃]
      refine div_le_div_of_nonneg_right ?_ hGp.le
      refine mul_le_mul hCE₀ ?_ (by positivity) (abs_nonneg _)
      refine div_le_div_of_nonneg_right ?_ hη₀'.le
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hu0) hB
    have a₄ : |mixedDeriv (fun V' : TorusField n => gasTermAtBlock A (coldCaseGround R V') Y h₁) (trivialField n) ![c₁, c₂]
        ![unitGenerator, unitGenerator]| ≤ 3 * u * lip / G := by
      refine tg.trans ?_
      have e₃ : R.params.weight (supportDiam Y ![c₁, c₂]) = G := hGd.symm
      rw [e₃]
      refine div_le_div_of_nonneg_right ?_ hGp.le
      have hsz : 0 ≤ weightNorm R.params.side R.depth h₁ :=
        le_trans (abs_nonneg _) (((hWN R.params.side hLodd R.depth (n * R.params.side) 0).1 h₁).trans (le_max_left _ _))
      calc _ ≤ u * (3 * lip) := mul_le_mul hexp hsize hsz hu0
        _ = _ := by ring
    have hpos : 0 ≤ u * lip / G := by positivity
    have hCw1 : 0 ≤ 6 * |Ts.CE| * Cw * (u * lip / G) := by positivity
    have e₄ : ∀ m₁ m₂ m₃ m₄ m₅ m₆ al : ℝ, m₁ + al * m₂ + al * m₃ + m₄ + m₅ - m₆ - al * m₂ = (m₁ - m₆) + al * m₃ + m₄ + m₅ := by
      intros
      ring
    rw [e₄]
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add a₁ a₂)) a₃)) a₄).trans ?_
    have e₅ : ∀ q : ℝ, q * u * lip / G = q * (u * lip / G) := fun q => by ring
    rw [e₅, e₅, e₅, e₅ 3, e₅ Mx, ← add_mul, ← add_mul, ← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ hpos
    show _ ≤ |Cnr| * |K.Kc| / Ts.η₃ * Cw + 12 * |Ts.CE| * Cw + 3 * |Ts.CE| * |K.Ka| / Ts.η₃ + 3
    have : 0 ≤ 6 * |Ts.CE| * Cw := by positivity
    linarith only [this]
end ResponseInTheExpansion
end YangMills.Construction
end
