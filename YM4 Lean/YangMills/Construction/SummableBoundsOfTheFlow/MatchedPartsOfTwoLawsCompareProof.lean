import YangMills.Construction.ColdStepAtMirrorFrames.CalculusOfLocalTerms
import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.GapsBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.HaarsBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.SlopesBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.ZeroFamilyIsAnExpansionProof
import YangMills.Construction.SummableBoundsOfTheFlow.DistancesOfOffsets
import YangMills.Construction.SummableBoundsOfTheFlow.MatchedPartsOfTwoLawsCompare
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames FamilyNorms TorusFreezing Interpolation Estimates
namespace TorusComparison
open ColdStepAtMirrorFrames.LocalCalculus
variable {F F' : BlockFrame}
private theorem eventuallyInParameters_of_imp {P Q : StepParameters → Prop}
    (h : ∀ T : StepParameters, T.IsOrdered → T.Ct ≤ T.Cs → 1 ≤ T.n₀ → 0 ≤ T.coupling → P T → Q T)
    (hP : EventuallyInParameters P) : EventuallyInParameters Q := by
  intro a ha
  obtain ⟨L₀, h1⟩ := hP a ha
  refine ⟨L₀, fun L hLo hL c hc => ?_⟩
  obtain ⟨Ct₀, h2⟩ := h1 L hLo hL c hc
  refine ⟨Ct₀, fun Ct hCt => ?_⟩
  obtain ⟨κ₀, hκ₀, h3⟩ := h2 Ct hCt
  refine ⟨κ₀, hκ₀, fun κ hκ hκ' => ?_⟩
  obtain ⟨η₀, hη₀, h4⟩ := h3 κ hκ hκ'
  refine ⟨η₀, hη₀, fun η₃ hη hη1 hη' => ?_⟩
  obtain ⟨N₀, h5⟩ := h4 η₃ hη hη1 hη'
  refine ⟨N₀, fun nb hn => ?_⟩
  obtain ⟨σ₀, hσ₀, h6⟩ := h5 nb hn
  refine ⟨σ₀, hσ₀, fun σ hσ hσ' p hp => ?_⟩
  obtain ⟨C₀, h7⟩ := h6 σ hσ hσ' p hp
  refine ⟨max C₀ Ct, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₀, h8⟩ := h7 Cs ((le_max_left _ _).trans hCs) E hE
  refine ⟨max m₀ 1, fun n₀ hn₀ => ?_⟩
  obtain ⟨C₁, h9⟩ := h8 n₀ ((le_max_left _ _).trans hn₀)
  refine ⟨C₁, fun CE hCE => ?_⟩
  obtain ⟨y₀, h10⟩ := h9 CE hCE
  refine ⟨max y₀ 0, fun y₁ hy => ?_⟩
  exact h _ ⟨ha, hLo, hc, hκ, hη, hη1, hσ, hp, hE⟩ ((le_max_right _ _).trans hCs)
    ((le_max_right _ _).trans hn₀) ((le_max_right _ _).trans hy) (h10 y₁ ((le_max_left _ _).trans hy))
private theorem interpolatedBlockExponent_eq (s a ρA x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    interpolatedBlockExponent s a ρA x m Y V η =
      interpolatedSlopePart s a ρA x m Y V η - interpolatedGapPart s a ρA x m Y V η -
        interpolatedHaarPart s a ρA m Y V η := rfl
private def zeroLocalFamily : LocalFamily := fun _ _ _ => 0
private theorem bondDeriv_const_zero {j k : ℕ} (W : F.GaugeField j) (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun _ : F.GaugeField j => (0 : ℝ)) W c X = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ZeroFamilyRegular.bondDeriv_zero <;> assumption
private theorem torusDecayFactor_nonneg (L : ℕ) (δ r : ℝ) : 0 ≤ torusDecayFactor L δ r := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ZeroFamilyRegular.torusDecayWeight_nonneg <;> assumption
private theorem zeroLocalFamily_isNormBounded (L t n₀ : ℕ) (σ δ : ℝ) {ε ε₃ : ℝ} (hε : 0 ≤ ε) (hε₃ : 0 ≤ ε₃) :
    IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ zeroLocalFamily where
  smooth := fun _ _ _ _ _ _ _ _ => contDiffAt_const
  gauge_invariant := fun _ _ _ _ _ _ => rfl
  translation_invariant := fun _ _ _ _ _ _ => rfl
  decay := by
    intro G _ y W k c X _ _ _ _
    have e : bondDeriv (zeroLocalFamily G y) W c X = 0 := bondDeriv_const_zero W c X
    rw [e, abs_zero]
    refine div_nonneg ?_ (torusDecayFactor_nonneg _ _ _)
    split_ifs
    · exact hε₃
    · exact hε
  locality := by
    intro G G' _ _ y y' W W' r k h X _ _ _ _ _ _
    have e : subtractTrivial zeroLocalFamily G y = fun _ => 0 := by
      funext U
      simp [subtractTrivial, zeroLocalFamily]
    have e' : subtractTrivial zeroLocalFamily G' y' = fun _ => 0 := by
      funext U
      simp [subtractTrivial, zeroLocalFamily]
    rw [e, e', bondDeriv_const_zero, bondDeriv_const_zero, sub_zero, abs_zero]
    exact div_nonneg hε (torusDecayFactor_nonneg _ _ _)
private theorem cellQuadratic_pushforwardField {ι : Type} [Fintype ι] [DecidableEq ι] (lam x : ℝ) (z : F.Cell)
    {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (ζ : BondField ι) :
    cellQuadratic lam x z (pushforwardField j ζ) =
      ∑ i, if enclosingCell (j i).1.1 = z then x * lam / 2 * ‖ζ i‖ ^ 2 else 0 := by
  unfold cellQuadratic
  symm
  refine Fintype.sum_of_injective j hj _ _ (fun b hb => ?_) (fun i => ?_)
  · have e : pushforwardField j ζ b = 0 :=
      pushforwardField_apply_of_not_mem_range j ζ b (fun k hk => hb ⟨k, hk⟩)
    simp [e]
  · rw [pushforwardField_apply_image j hj]
private theorem enclosingCell_fineBondAt_iff (hD : cellOffsetStatement) {q : ℕ} {Y : F.Cell} {Y' : F'.Cell}
    (oddF : Odd F.blockSide) (hL : F'.blockSide = F.blockSide) (hs : ∀ i, 2 * q + 2 < F.extent i)
    (hs' : ∀ i, 2 * q + 2 < F'.extent i)
    {g h o : Fin 4 → ℤ} {k : Fin 4} (hg : ∀ l, 2 * |g l| ≤ q) (hh : ∀ l, 2 * |h l| ≤ q)
    (ho : o ∈ centredCube F.blockSide) :
    enclosingCell (fineBondAt Y g o k).1 = Y + siteOfCoords F.top h ↔
      enclosingCell (fineBondAt Y' g o k).1 = Y' + siteOfCoords F'.top h := by
  have D := hD F oddF (fun i => by have := hs i; omega)
  have D' := hD F' (hL ▸ oddF) (fun i => by have := hs' i; omega)
  rw [D.1 Y g o k ho, D'.1 Y' g o k (hL ▸ ho)]
  have read : g = h ↔ Y + siteOfCoords F.top g = Y + siteOfCoords F.top h := by
    constructor
    · rintro rfl
      rfl
    · intro e
      have a := (D.2.2.2 q hs Y g h hg hh).1
      have b := (D.2.2.2 q hs Y h g hh hg).1
      rw [e] at a
      exact a.symm.trans b
  have read' : g = h ↔ Y' + siteOfCoords F'.top g = Y' + siteOfCoords F'.top h := by
    constructor
    · rintro rfl
      rfl
    · intro e
      have a := (D'.2.2.2 q hs' Y' g h hg hh).1
      have b := (D'.2.2.2 q hs' Y' h g hh hg).1
      rw [e] at a
      exact a.symm.trans b
  exact read.symm.trans read'
private theorem extent_gt_of_isCubicTopTorus {G : BlockFrame} {L t n₀ q : ℕ} (hG : IsCubicTopTorus L t n₀ G)
    (h1 : 1 ≤ n₀) (hd : ∀ i, G.extent i = 0 ∨ 2 * q + 2 < G.extent i) (i : Fin 4) : 2 * q + 2 < G.extent i := by
  obtain ⟨-, -, n, hn, hn₀⟩ := hG
  rcases hd i with h | h
  · rw [hn i] at h
    omega
  · exact h
private theorem bondGradNorm_sub_le {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} (hρ : 0 < ρ)
    {f g : BondField ι → ℝ} (hf : ContDiffOn ℝ 1 f (openPolyball ι ρ)) (hg : ContDiffOn ℝ 1 g (openPolyball ι ρ))
    {ξ : BondField ι} (hξ : ξ ∈ openPolyball ι ρ) (b : ι) :
    bondGradNorm (fun ζ => f ζ - g ζ) b ξ ≤ bondGradNorm f b ξ + bondGradNorm g b ξ := by
  have h := bondGradNorm_linear_combination_le hρ hf hg 1 (-1) hξ b
  rw [abs_neg, abs_one, one_mul, one_mul] at h
  have e : (fun ζ => 1 * f ζ + (-1) * g ζ) = fun ζ => f ζ - g ζ := by
    funext ζ
    ring
  rwa [e] at h
private theorem pairedPartsCompareSmoothly_three {ι : Type} [Fintype ι] [DecidableEq ι] {ρ Ct ε x κ : ℝ}
    (hρ : 0 < ρ)
    {j : ι → ↥(chordBonds (finiteCells F))} {j' : ι → ↥(chordBonds (finiteCells F'))} {z : F.Cell}
    {A B C : StepVariable (finiteCells F) → ℝ} {A' B' C' : StepVariable (finiteCells F') → ℝ}
    (h₁ : PairedPartsCompareSmoothly ρ (Ct / 3) ε x κ j j' z A A')
    (h₂ : PairedPartsCompareSmoothly ρ (Ct / 3) ε x κ j j' z B B')
    (h₃ : PairedPartsCompareSmoothly ρ (Ct / 3) ε x κ j j' z C C') :
    ContDiffOn ℝ 1 (fun ζ => (A' (pushforwardField j' ζ) - B' (pushforwardField j' ζ) - C' (pushforwardField j' ζ)) -
      (A (pushforwardField j ζ) - B (pushforwardField j ζ) - C (pushforwardField j ζ))) (openPolyball ι ρ) ∧
    ∀ ξ ∈ openPolyball ι ρ, ∀ k,
      bondGradNorm (fun ζ => (A' (pushforwardField j' ζ) - B' (pushforwardField j' ζ) -
          C' (pushforwardField j' ζ)) -
        (A (pushforwardField j ζ) - B (pushforwardField j ζ) - C (pushforwardField j ζ))) k ξ ≤
      Ct * ε * (x * Real.sqrt (weightedSqNormNear κ (fun k => bondBlock F (j k))
        (blockDist F) z ξ) + 1) *
        Real.exp (-(2 * κ * blockDist F (bondBlock F (j k)) z)) := by
  obtain ⟨s₁, b₁⟩ := h₁
  obtain ⟨s₂, b₂⟩ := h₂
  obtain ⟨s₃, b₃⟩ := h₃
  have e : (fun ζ => (A' (pushforwardField j' ζ) - B' (pushforwardField j' ζ) - C' (pushforwardField j' ζ)) -
      (A (pushforwardField j ζ) - B (pushforwardField j ζ) - C (pushforwardField j ζ))) =
      fun ζ => ((A' (pushforwardField j' ζ) - A (pushforwardField j ζ)) -
          (B' (pushforwardField j' ζ) - B (pushforwardField j ζ))) -
        (C' (pushforwardField j' ζ) - C (pushforwardField j ζ)) := by
    funext ζ
    ring
  rw [e]
  refine ⟨(s₁.sub s₂).sub s₃, fun ξ hξ k => ?_⟩
  have h1 := (b₁ ξ hξ).2 k
  have h2 := (b₂ ξ hξ).2 k
  have h3 := (b₃ ξ hξ).2 k
  have p := bondGradNorm_sub_le hρ (s₁.sub s₂) s₃ hξ k
  have p' := bondGradNorm_sub_le hρ s₁ s₂ hξ k
  refine p.trans ((add_le_add (p'.trans (add_le_add h1 h2)) h3).trans (le_of_eq ?_))
  ring
private theorem family_bound_add_le {Ct Cs E₃ ε A B u v : ℝ} (hu : u ≤ Ct * ε * A * B)
    (hv : v ≤ Ct * E₃ * ε * A * B)
    (hC : Ct ≤ Cs) (hE : 0 ≤ E₃) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    u + v ≤ Cs * (1 + E₃) * ε * A * B := by
  have h : 0 ≤ (Cs - Ct) * (1 + E₃) * ε * A * B :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 hC) (by linarith)) hε) hA) hB
  linarith
private theorem weight_bound_le {Ct Cs τ ε A B u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ Ct * ε * A * B) (h0 : 0 ≤ τ)
    (h1 : τ ≤ 1) (hC : Ct ≤ Cs) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |τ| * u + |(0 : ℝ)| * u ≤ Cs * 1 * ε * A * B := by
  rw [abs_zero, zero_mul, add_zero, abs_of_nonneg h0]
  have h : 0 ≤ (Cs - Ct) * ε * A * B :=
    mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 hC) hε) hA) hB
  have h2 : τ * u ≤ u := by nlinarith
  linarith
theorem matchedCellPartsGradientBound_holds (hs : interpolatedSlopesCompareStatement)
    (hg : GapPartsCompare) (hh : HaarDensitiesCompare)
    (hr : InterpolatedExpansionsCompare) (hj : EventuallyInParametersCombines) (hD : cellOffsetStatement) :
    matchedCellPartsGradientBound := by
  refine eventuallyInParameters_of_imp ?_ (hj.1 _ _ (hj.1 _ _ (hj.1 _ _ hs hg) hh) hr)
  rintro T hT hCs hn hy ⟨⟨⟨a, b⟩, c⟩, d⟩ t x s l F F' V V' Y Y' q ι _ _ j j' o hx h0 h1 hl hF hF' hc hc' hag hp hq ho
    ξ hξ k
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hE₃ : 0 ≤ T.energyRatio := by
    have := hT.η₃_pos
    have := hT.one_le_E
    unfold StepParameters.energyRatio
    positivity
  have hε : 0 ≤ Real.exp (-(4 * T.κ * q)) := (Real.exp_pos _).le
  have hx0 : 0 ≤ x := hy.trans hx
  have oddF : Odd F.blockSide := by
    rw [hF.1]
    exact hT.odd_L
  have hLL : F'.blockSide = F.blockSide := hF'.1.trans hF.1.symm
  have side := extent_gt_of_isCubicTopTorus hF hn hag.1
  have side' := extent_gt_of_isCubicTopTorus hF' hn hag.2.1
  have setting : ∀ φ : LocalFamily,
      IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ →
      InterpolatedComparisonSetting T t x s φ V V' Y Y' q j j' o := fun φ hφ =>
    { coupling_le := hx
      interp_mem := ⟨h0, h1⟩
      family := hφ
      top := hF
      top' := hF'
      small := hc
      small' := hc'
      agree := hag
      radius_le := hq
      injective := hp.isBoxPairing.injective_left
      injective' := hp.isBoxPairing.injective_right
      paired := fun i => by
        obtain ⟨g, u, m, hgs, hu, e, e'⟩ := hp.short_offsets i
        refine ⟨g, u, m, hu, fun l => ?_, e, e'⟩
        have := hgs l
        have := abs_nonneg (g l)
        linarith
      offset_le := ho }
  have hA : 0 ≤ x * Real.sqrt (weightedSqNormNear T.κ (fun k => bondBlock F (j k))
      (blockDist F) (Y + siteOfCoords F.top o) ξ) + 1 := by
    have := Real.sqrt_nonneg (weightedSqNormNear T.κ (fun k => bondBlock F (j k))
      (blockDist F) (Y + siteOfCoords F.top o) ξ)
    positivity
  have hB : 0 ≤ Real.exp (-(2 * T.κ * blockDist F (bondBlock F (j k))
      (Y + siteOfCoords F.top o))) := (Real.exp_pos _).le
  cases l with
  | ofFamily φ =>
    have hS := setting φ hl
    have core := pairedPartsCompareSmoothly_three hρ (a t x s φ F F' V V' Y Y' q ι j j' o hS)
      (b t x s φ F F' V V' Y Y' q ι j j' o hS) (c t x s φ F F' V V' Y Y' q ι j j' o hS)
    obtain ⟨sr, br⟩ := d t x s φ F F' V V' Y Y' q ι j j' o hS
    have p := bondGradNorm_sub_le hρ core.1 sr hξ k
    have b1 := core.2 ξ hξ k
    have b2 := (br ξ hξ).2 k
    refine (le_of_eq ?_).trans (p.trans ?_)
    · refine congrArg (fun f => bondGradNorm f k ξ) (funext fun ζ => ?_)
      simp only [stepLawCellPart, interpolatedBlockExponent_eq]
      ring
    · exact family_bound_add_le b1 b2 hCs hE₃ hε hA hB
  | ofWeight τ =>
    have hS := setting zeroLocalFamily
      (zeroLocalFamily_isNormBounded _ _ _ _ _ (by linarith [hT.one_le_E]) hE₃)
    have core := pairedPartsCompareSmoothly_three hρ (a t x s zeroLocalFamily F F' V V' Y Y' q ι j j' o hS)
      (b t x s zeroLocalFamily F F' V V' Y Y' q ι j j' o hS) (c t x s zeroLocalFamily F F' V V' Y Y' q ι j j' o hS)
    have p := bondGradNorm_linear_combination_le hρ core.1 core.1 τ 0 hξ k
    have b1 := core.2 ξ hξ k
    have square : ∀ ζ : BondField ι,
        cellQuadratic T.chainParams.lam x (Y' + siteOfCoords F'.top o) (pushforwardField j' ζ) =
          cellQuadratic T.chainParams.lam x (Y + siteOfCoords F.top o) (pushforwardField j ζ) := by
      intro ζ
      rw [cellQuadratic_pushforwardField _ _ _ hp.isBoxPairing.injective_right,
        cellQuadratic_pushforwardField _ _ _ hp.isBoxPairing.injective_left]
      refine Finset.sum_congr rfl fun i _ => ?_
      obtain ⟨g, u, m, hgs, hu, e₁, e₂⟩ := hp.short_offsets i
      have hm := enclosingCell_fineBondAt_iff hD (Y := Y) (Y' := Y') oddF hLL side side' (g := g) (h := o)
        (o := u) (k := m) hgs
        (fun l => by
          have := ho l
          have := abs_nonneg (o l)
          linarith) hu
      rw [e₁, e₂]
      by_cases hc₁ : enclosingCell (fineBondAt Y g u m).1 = Y + siteOfCoords F.top o
      · rw [if_pos hc₁, if_pos (hm.1 hc₁)]
      · rw [if_neg hc₁, if_neg (fun h => hc₁ (hm.2 h))]
    refine (le_of_eq ?_).trans (p.trans ?_)
    · refine congrArg (fun f => bondGradNorm f k ξ) (funext fun ζ => ?_)
      simp only [stepLawCellPart, interpolatedBlockExponent_eq]
      rw [square ζ]
      ring
    · exact weight_bound_le (bondGradNorm_nonneg _ _ _) b1 hl.1 hl.2 hCs hε hA hB
end TorusComparison
end YangMills.Construction
end
