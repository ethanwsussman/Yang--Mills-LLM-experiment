import YangMills.Construction.LawByMomentsOfTheFlow.CanonicalGaussianInTheTreeGaugeProof
import YangMills.Construction.FormsOnATorus.FormsAlongPathsOfATorus
import YangMills.Construction.LawByMomentsOfTheFlow.ExactSquareOfAStepProof
import YangMills.Construction.LawByMomentsOfTheFlow.LeastValueOfAStep
import YangMills.Construction.ResponseInTheExpansion.TheStepsAddUpToTheMaxwellCovarianceProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.MomentLaw
namespace StepMinimumProof
section Chart
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem exists_potential_off_chart (hL : Odd L) (hn : 2 ≤ n) (A : TorusFields.TorusBond (n * L) → ℝ) :
    ∃ φ : TorusFields.TorusSite (n * L) → ℝ, ∀ b, b ∉ StepCosts.chartBonds L n →
      A b = ResponseInTheExpansion.latticeGradient φ b := by apply _root_.YangMills.SharedProofs.p87081 <;> assumption
private theorem responseKernel_eq_zero_of_not_mem (hL : Odd L) (hn : 2 ≤ n) (a ρA : ℝ) (u : ℕ)
    {b : TorusFields.TorusBond (n * L)} (c : TorusFields.TorusBond n) (hb : b ∉ StepCosts.chartBonds L n) :
    WeightedResponses.responseKernel a ρA L u b c = 0 := by apply _root_.YangMills.SharedProofs.p23899 <;> assumption
private theorem responseMap_eq_zero_of_not_mem (hL : Odd L) (hn : 2 ≤ n) (a ρA : ℝ) (u : ℕ)
    (B : TorusFields.TorusBond n → ℝ) (b : TorusFields.TorusBond (n * L)) (hb : b ∉ StepCosts.chartBonds L n) :
    WeightedResponses.responseMap a ρA L u B b = 0 := by
  unfold WeightedResponses.responseMap
  exact Finset.sum_eq_zero fun c _ => by rw [responseKernel_eq_zero_of_not_mem hL hn a ρA u c hb, zero_mul]
end Chart
section Contours
variable {N : ℕ}
private theorem sumAlongWord_pathToWord (θ : TorusFields.TorusBond N → ℝ) :
    ∀ (l : List BlockAverages.PathStep) (x : TorusFields.TorusSite N),
      MomentLaw.sumAlongWord θ (TorusContours.pathToWord x l) =
        ResponseInTheExpansion.SingleColourFields.sumAlongPath θ x l := by
  exact _root_.YangMills.SharedProofs.p6289 (N := N) θ
private theorem sumAlongWord_sub {m : ℕ} (A B : TorusFields.TorusBond m → ℝ) (w : TorusPaths.BondWord m) :
    MomentLaw.sumAlongWord (A - B) w = MomentLaw.sumAlongWord A w - MomentLaw.sumAlongWord B w := by
  induction w with
  | nil => simp [MomentLaw.sumAlongWord]
  | cons e r ih =>
    simp only [MomentLaw.sumAlongWord, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    by_cases h : e.2 <;> simp [h] <;> ring
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem contourAverage_sub (A B : TorusFields.TorusBond (n * L) → ℝ) (c : TorusFields.TorusBond n) :
    MomentLaw.contourAverage L (A - B) c = MomentLaw.contourAverage L A c - MomentLaw.contourAverage L B c := by
  unfold MomentLaw.contourAverage
  simp only [sumAlongWord_sub, Finset.sum_sub_distrib, mul_sub]
private theorem contourAverage_eq_sum_contourSum (W : TorusFields.TorusBond (n * L) → ℝ)
    (c : TorusFields.TorusBond n) :
    MomentLaw.contourAverage L W c = ∑ k ∈ ResponseInTheExpansion.SingleColourFields.contourIndex L,
      ResponseInTheExpansion.SingleColourFields.contourWeight L * ResponseInTheExpansion.SingleColourFields.contourSum L W c k := by
  unfold MomentLaw.contourAverage
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show TorusContours.contourWeight L * MomentLaw.sumAlongWord W
    (TorusContours.pathToWord (TorusBlocks.blockCentreSite L c.1) (BlockAverages.bondContour L k.1 k.2 c.2)) = _
  rw [sumAlongWord_pathToWord]
  rfl
abbrev _root_.YangMills.SharedProofs.p107193 := @contourAverage_eq_sum_contourSum
private theorem contourMeanSlope_eq_contourAverage (W : TorusFields.TorusBond (n * L) → ℝ)
    (c : TorusFields.TorusBond n) :
    ResponseInTheExpansion.contourMeanSlope L n W c = MomentLaw.contourAverage L W c := by
  have hp : ∀ i, (TorusLumps.stepBlockFrame L n).period 0 i = n * L := fun i =>
    TopLevelSites.period_depth_of_extent (F := TorusLumps.stepBlockFrame L n) (n := n) (fun _ => rfl) i
  have hq : ∀ i, (TorusLumps.stepBlockFrame L n).period (0 + 1) i = n := fun i =>
    TopLevelSites.period_top_of_extent (F := TorusLumps.stepBlockFrame L n) (n := n) (fun _ => rfl) i
  rw [contourAverage_eq_sum_contourSum]
  unfold ResponseInTheExpansion.contourMeanSlope
  have e : (fun τ : ℝ => -(BlockAverages.contourAverage
      (TorusFields.readAtLevel (TorusLumps.stepBlockFrame L n) 0 (ResponseInTheExpansion.expOfColourForm τ W))
      ((StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 c.1, c.2) :
        (TorusLumps.stepBlockFrame L n).Site (0 + 1) × Fin 4) *
        (WeightedResponses.unitGenerator : ℍ[ℝ])).re) =
      fun τ => ResponseInTheExpansion.SingleColourFields.contourSinMean L W c τ := by
    funext τ
    have h : BlockAverages.contourAverage
        (TorusFields.readAtLevel (TorusLumps.stepBlockFrame L n) 0 (ResponseInTheExpansion.expOfColourForm τ W))
        ((StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 c.1, c.2) :
          (TorusLumps.stepBlockFrame L n).Site (0 + 1) × Fin 4) =
        ResponseInTheExpansion.SingleColourFields.colourPlane
          (ResponseInTheExpansion.SingleColourFields.contourCosMean L W c τ)
          (ResponseInTheExpansion.SingleColourFields.contourSinMean L W c τ) :=
      ResponseInTheExpansion.SingleColourFields.contourAverage_readAtLevel (G := TorusLumps.stepBlockFrame L n) hp hq τ W c
    rw [h]
    simp [Quaternion.re_mul, ResponseInTheExpansion.SingleColourFields.unitGenerator_re,
      ResponseInTheExpansion.SingleColourFields.unitGenerator_imI, ResponseInTheExpansion.SingleColourFields.unitGenerator_imJ,
      ResponseInTheExpansion.SingleColourFields.unitGenerator_imK]
  refine (congrArg (fun g : ℝ → ℝ => deriv g 0) e).trans ?_
  have J := SecondOrder.SecondJet.sum (ResponseInTheExpansion.SingleColourFields.contourIndex L)
    (g := fun k τ => ResponseInTheExpansion.SingleColourFields.contourWeight L *
      Real.sin (τ * ResponseInTheExpansion.SingleColourFields.contourSum L W c k))
    (a0 := fun k => ResponseInTheExpansion.SingleColourFields.contourWeight L * 0)
    (a1 := fun k => ResponseInTheExpansion.SingleColourFields.contourWeight L *
      ResponseInTheExpansion.SingleColourFields.contourSum L W c k)
    (a2 := fun k => ResponseInTheExpansion.SingleColourFields.contourWeight L * 0)
    fun k _ => (SecondOrder.SecondJet.sin_mul (ResponseInTheExpansion.SingleColourFields.contourSum L W c k)).const_mul
      (ResponseInTheExpansion.SingleColourFields.contourWeight L)
  exact J.firstDeriv
private theorem contourAverage_latticeGradient (hL : Odd L) (φ : TorusFields.TorusSite (n * L) → ℝ)
    (c : TorusFields.TorusBond n) :
    MomentLaw.contourAverage L (ResponseInTheExpansion.latticeGradient φ) c =
      ResponseInTheExpansion.latticeGradient (fun Y => φ (TorusBlocks.blockCentreSite L Y)) c := by apply _root_.YangMills.DeltaSharedProofs.p501243 <;> assumption
end Contours
section MaxwellForms
variable {a : ℝ} {L u m : ℕ} [NeZero m]
private theorem maxwellForm_sub_left (A B C : TorusFields.TorusBond m → ℝ) :
    WeightedResponses.maxwellForm a L u (A - B) C =
      WeightedResponses.maxwellForm a L u A C - WeightedResponses.maxwellForm a L u B C := by
  simp only [WeightedResponses.maxwellForm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
private theorem maxwellForm_sub_right (A B C : TorusFields.TorusBond m → ℝ) :
    WeightedResponses.maxwellForm a L u A (B - C) =
      WeightedResponses.maxwellForm a L u A B - WeightedResponses.maxwellForm a L u A C := by
  simp only [WeightedResponses.maxwellForm, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
private theorem maxwellForm_smul_left (t : ℝ) (A C : TorusFields.TorusBond m → ℝ) :
    WeightedResponses.maxwellForm a L u (t • A) C = t * WeightedResponses.maxwellForm a L u A C := by
  simp only [WeightedResponses.maxwellForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
private theorem maxwellForm_smul_right (t : ℝ) (A C : TorusFields.TorusBond m → ℝ) :
    WeightedResponses.maxwellForm a L u A (t • C) = t * WeightedResponses.maxwellForm a L u A C := by
  simp only [WeightedResponses.maxwellForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
private theorem maxwellForm_sub_of_left_kernel
    (hpos : ∀ A : TorusFields.TorusBond m → ℝ, 0 ≤ WeightedResponses.maxwellForm a L u A A)
    (g : TorusFields.TorusBond m → ℝ)
    (hk : ∀ A : TorusFields.TorusBond m → ℝ, WeightedResponses.maxwellForm a L u g A = 0)
    (A : TorusFields.TorusBond m → ℝ) :
    WeightedResponses.maxwellForm a L u (A - g) (A - g) = WeightedResponses.maxwellForm a L u A A := by
  have hr : WeightedResponses.maxwellForm a L u A g = 0 := by
    by_contra hne
    have h := hpos (A - ((WeightedResponses.maxwellForm a L u A A + 1) /
      WeightedResponses.maxwellForm a L u A g) • g)
    rw [maxwellForm_sub_left, maxwellForm_sub_right, maxwellForm_sub_right, maxwellForm_smul_left,
      maxwellForm_smul_right, maxwellForm_smul_right, maxwellForm_smul_left, hk, hk] at h
    have e : (WeightedResponses.maxwellForm a L u A A + 1) / WeightedResponses.maxwellForm a L u A g *
        WeightedResponses.maxwellForm a L u A g = WeightedResponses.maxwellForm a L u A A + 1 :=
      div_mul_cancel₀ _ hne
    rw [e] at h
    simp only [mul_zero, sub_zero] at h
    linarith
  rw [maxwellForm_sub_left, maxwellForm_sub_right, maxwellForm_sub_right, hk, hk, hr]
  ring
end MaxwellForms
section ParameterAssignment
variable (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
private theorem stepMinimumAt_of (hD : Tb.Admissible) (h₁ : ResponseInTheExpansion.maxwellFormStepIdentityAt Tb y)
    (h₂ : ResponseInTheExpansion.GradientMaxwellPropertiesAt Tb y) (h₄ : ResponseInTheExpansion.StepHessianPosDefAt Tb y) :
    MomentLaw.stepMinimumAt Tb y := by
  intro u n _ hn
  have hodd : Odd (Tb.stepParameters y).side := hD.L_odd
  have hLp : 0 < (Tb.stepParameters y).side := hodd.pos
  have hn2 : 2 ≤ n := by
    have := hD.n₀_ge
    omega
  have hnL : Tb.n₀ ≤ n * (Tb.stepParameters y).side := hn.trans (Nat.le_mul_of_pos_right n hLp)
  have hpos : ∀ (v m : ℕ) [NeZero m], Tb.n₀ ≤ m → ∀ A : TorusFields.TorusBond m → ℝ,
      0 ≤ WeightedResponses.maxwellForm Tb.coupling (Tb.stepParameters y).side v A A := by
    intro v m _ hm A
    have h0 : 0 ≤ 2 * Tb.coercivity * ∑ p ∈ TorusFields.plaquettesIn
        (Finset.univ : Finset (TorusFields.TorusSite m)), WeightedResponses.curl A p ^ 2 :=
      mul_nonneg (by linarith [hD.cK_pos]) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact h0.trans ((h₂ v m hm).2.2 A)
  have hH : ∀ h : TorusFields.TorusBond (n * (Tb.stepParameters y).side) → ℝ,
      0 ≤ ResponseInTheExpansion.stepHessianForm Tb.coupling (Tb.stepParameters y).side u n h := by
    intro h
    unfold ResponseInTheExpansion.stepHessianForm
    by_cases hz : ResponseInTheExpansion.chartRestriction (Tb.stepParameters y).side u n h = 0
    · rw [hz]
      simp
    · exact ((h₄ u n hn).dotProduct_mulVec_pos hz).le
  constructor
  · intro W B
    obtain ⟨φ, hφ⟩ := exists_potential_off_chart hodd hn2 W
    set ψ : TorusFields.TorusSite n → ℝ := fun Y => φ (TorusBlocks.blockCentreSite (Tb.stepParameters y).side Y)
      with hψ
    have hW : ∀ b, b ∉ StepCosts.chartBonds (Tb.stepParameters y).side n →
        (W - ResponseInTheExpansion.latticeGradient φ) b = 0 := fun b hb => by
      simp [hφ b hb]
    have h := h₁ u n hn (W - ResponseInTheExpansion.latticeGradient φ) (B - ResponseInTheExpansion.latticeGradient ψ) hW
    rw [maxwellForm_sub_of_left_kernel (hpos u _ hnL) (ResponseInTheExpansion.latticeGradient φ) ((h₂ u _ hnL).2.1 φ) W,
      maxwellForm_sub_of_left_kernel (hpos (u + 1) _ hn) (ResponseInTheExpansion.latticeGradient ψ)
        ((h₂ (u + 1) _ hn).2.1 ψ) B] at h
    have hfit : ∀ c : TorusFields.TorusBond n,
        ResponseInTheExpansion.contourMeanSlope (Tb.stepParameters y).side n (W - ResponseInTheExpansion.latticeGradient φ) c -
          (B - ResponseInTheExpansion.latticeGradient ψ) c =
        MomentLaw.contourAverage (Tb.stepParameters y).side W c - B c := by
      intro c
      rw [contourMeanSlope_eq_contourAverage, contourAverage_sub, contourAverage_latticeGradient hodd, Pi.sub_apply]
      ring
    simp only [hfit] at h
    linarith [hH (W - ResponseInTheExpansion.latticeGradient φ -
      WeightedResponses.responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u
        (B - ResponseInTheExpansion.latticeGradient ψ))]
  · intro B
    have hM : ∀ b, b ∉ StepCosts.chartBonds (Tb.stepParameters y).side n →
        WeightedResponses.responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u B b = 0 :=
      fun b hb => responseMap_eq_zero_of_not_mem hodd hn2 _ _ u B b hb
    have h := h₁ u n hn _ B hM
    simp only [contourMeanSlope_eq_contourAverage] at h
    have h0 : ResponseInTheExpansion.stepHessianForm Tb.coupling (Tb.stepParameters y).side u n
        (WeightedResponses.responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u B -
          WeightedResponses.responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u B) = 0 := by
      have e : ResponseInTheExpansion.chartRestriction (Tb.stepParameters y).side u n
          (WeightedResponses.responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u B -
            WeightedResponses.responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u B) = 0 := by
        funext b
        simp [ResponseInTheExpansion.chartRestriction]
      unfold ResponseInTheExpansion.stepHessianForm
      rw [e]
      simp
    rw [h0, add_zero] at h
    exact h.symm
end ParameterAssignment
end StepMinimumProof
theorem stepMinimumStatement_holds (h₁ : ResponseInTheExpansion.maxwellFormStepIdentityStatement)
    (h₂ : ResponseInTheExpansion.gradientMaxwellStatement) (h₃ : ResponseInTheExpansion.stepHessianPosDefStatement) :
    MomentLaw.stepMinimumStatement := by
  intro a ha
  obtain ⟨L1, r1, C1, hr1, g1⟩ := h₁ a ha
  obtain ⟨L2, r2, C2, hr2, g2⟩ := h₂ a ha
  obtain ⟨L3, r3, C3, hr3, g3⟩ := h₃ a ha
  refine ⟨max L1 (max L2 L3), fun c => min (r1 c) (min (r2 c) (r3 c)), max C1 (max C2 C3),
    fun c => lt_min (hr1 c) (lt_min (hr2 c) (hr3 c)), ?_⟩
  intro L hodd hL Tb hTa hTL hD hCS hCH hrt hC
  obtain ⟨y1, f1⟩ := g1 L hodd ((le_max_left _ _).trans hL) Tb hTa hTL hD hCS hCH (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hC)
  obtain ⟨y2, f2⟩ := g2 L hodd (((le_max_left _ _).trans (le_max_right _ _)).trans hL) Tb hTa hTL hD hCS hCH
    (hrt.trans ((min_le_right _ _).trans (min_le_left _ _))) (((le_max_left _ _).trans (le_max_right _ _)).trans hC)
  obtain ⟨y3, f3⟩ := g3 L hodd (((le_max_right _ _).trans (le_max_right _ _)).trans hL) Tb hTa hTL hD hCS hCH
    (hrt.trans ((min_le_right _ _).trans (min_le_right _ _))) (((le_max_right _ _).trans (le_max_right _ _)).trans hC)
  refine ⟨max y1 (max y2 y3), fun y hy hR hW => ?_⟩
  exact StepMinimumProof.stepMinimumAt_of Tb y hD (f1 y ((le_max_left _ _).trans hy) hR hW)
    (f2 y (((le_max_left _ _).trans (le_max_right _ _)).trans hy) hR hW)
    (f3 y (((le_max_right _ _).trans (le_max_right _ _)).trans hy) hR hW)
end YangMills.Construction.MomentLaw
end
