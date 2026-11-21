import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.CovarianceOfAConvexMeasure
import YangMills.Construction.ColdStepAtMirrorFrames.MomentsOfAConvexMeasure
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import YangMills.Construction.SummableBoundsOfTheFlow.LawsBetweenAreConvex
import YangMills.Construction.SummableBoundsOfTheFlow.MomentsInTheLawsBetween
import YangMills.Construction.SummableBoundsOfTheFlow.RimMomentsOfALaw
import YangMills.Construction.SummableBoundsOfTheFlow.SumOfTheWeightsAboutACell
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
variable {F : BlockFrame}
private theorem cellOffset_mem_and_eq (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Site F.depth) :
    cellOffset z ∈ centredCube F.blockSide ∧
      z = cellCentre F.depth (enclosingCell z) + siteOfCoords F.depth (cellOffset z) := by
  obtain ⟨y, o, ho, hz⟩ := TopLevelSites.exists_centre_add hL hs z
  have h1 : enclosingCell z = y := by rw [hz]; exact TopLevelSites.enclosingCell_centre_add hL hs y o ho
  have h2 : cellOffset z = o := by rw [hz]; exact TopLevelSites.cellOffset_centre_add hL hs y o ho
  exact ⟨h2 ▸ ho, by rw [h1, h2, ← hz]⟩
private theorem card_fiber_le {ι : Type} [Fintype ι] [DecidableEq ι] (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    {e : ι → ↥(chordBonds (finiteCells F))} (he : Function.Injective e) (z : F.Cell) :
    (Finset.univ.filter fun i : ι => enclosingCell (e i).1.1 = z).card ≤ (centredCube F.blockSide).card * 4 := by
  classical
  have := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun i : ι => enclosingCell (e i).1.1 = z)
    (t := centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4)))
    (fun i => (cellOffset (e i).1.1, (e i).1.2)) ?_ ?_
  · simpa [Finset.card_product] using this
  · intro i _
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true]
    exact (cellOffset_mem_and_eq hL hs _).1
  · intro i hi i' hi' hii
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hi'
    simp only [Prod.mk.injEq] at hii
    apply he
    apply Subtype.ext
    apply Prod.ext
    · rw [(cellOffset_mem_and_eq hL hs (e i).1.1).2, (cellOffset_mem_and_eq hL hs (e i').1.1).2, hi, hi', hii.1]
    · exact hii.2
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
private theorem ballDensity_congr {ρ : ℝ} {p : ℝ → ℝ} {Φ Ψ : BondField ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Ψ η = Φ η) :
    ballDensity (cutoffFactor ρ p) Φ = ballDensity (cutoffFactor ρ p) Ψ := by
  funext η
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · simp only [ballDensity, h η hη]
  · push Not at hη
    obtain ⟨b, hb⟩ := hη
    have hz : radialWeightProd (cutoffFactor ρ p) η = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ b) (by unfold cutoffFactor; rw [if_neg (not_lt.2 hb)])
    simp only [ballDensity, hz, zero_mul]
omit [Fintype ι] [DecidableEq ι] in
private theorem isPseudoMetricOnBonds_of_preserves {e : ι → ↥(chordBonds (finiteCells F))} {d : ι → ι → ℝ}
    (h : PreservesCellDist e d) : IsPseudoMetricOnBonds d := by
  refine ⟨fun b => ?_, fun b b' => ?_, fun b b' b'' => ?_⟩
  · rw [h, PatchLocality.cellSupDist_self]; simp
  · rw [h, h, PatchLocality.cellSupDist_comm]
  · rw [h, h, h]
    exact_mod_cast PatchLocality.cellSupDist_triangle _ _ _
theorem intermediateLawMoments_of_estimates (hConvex : mixturesOfIntermediateLawsConvex)
    (hCov : BallCovarianceBound) (hMom : GaussianMomentBound)
    (hRim : Estimates.cutoffDerivMomentsStatement) (hSum : CellCounting.ExpDecaySumBounded)
    (hCut : CutoffFactorIsRadialCutoff) (hJ : EventuallyInParametersCombines) : intermediateLawMoments := by
  classical
  obtain ⟨hJ1, hJ2⟩ := hJ
  set Wt : StepParameters → ℝ := fun T =>
    if h : 0 < T.κ then Classical.choose (hSum ((centredCube T.L).card * 4) (2 * T.κ) (by positivity)) else 0
    with hWt
  have hWspec : ∀ T : StepParameters, 0 < T.κ → 0 ≤ Wt T ∧
      ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
        (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ (centredCube T.L).card * 4) →
        ∀ z : F.Cell, ∑ b, Real.exp (-(2 * T.κ * (cellSupDist (y b) z : ℝ))) ≤ Wt T := by
    intro T hT
    simp only [hWt, dif_pos hT]
    exact Classical.choose_spec (hSum ((centredCube T.L).card * 4) (2 * T.κ) (by positivity))
  set Cq : StepParameters → ℕ → ℝ := fun T q =>
    (∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * Wt T)) * (4 / T.chainParams.lam) ^ q with hCq
  set Cr : StepParameters → ℕ → ℕ → ℕ → ℝ := fun T j q N =>
    if h : 0 < T.ballRadius ∧ IsCutoff T.ballRadius T.p ∧ 0 < T.chainParams.lam ∧ 0 ≤ T.Ct ∧ 0 ≤ Wt T ∧ 1 ≤ j ∧ 1 ≤ q then
      Classical.choose (hRim T.ballRadius T.p T.chainParams.lam T.Ct (Wt T) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 j q N
        h.2.2.2.2.2.1 h.2.2.2.2.2.2) else 0 with hCr
  refine ⟨Cq, Cr, ?_⟩
  have hR : EventuallyInParameters fun T =>
      4 / T.chainParams.lam ≤ T.Cs ∧ 1 ≤ T.coupling ∧ 0 ≤ T.Ct ∧ 2 ≤ T.n₀ := by
    intro a ha
    exact ⟨0, fun L _ _ c hc => ⟨0, fun Ct hCt => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ =>
      ⟨0, fun m _ => ⟨1, one_pos, fun σ _ _ p _ => ⟨4 / c.lam, fun Cs hCs E _ => ⟨2, fun n₀ hn₀ =>
      ⟨0, fun CE _ => ⟨1, fun y hy => ⟨hCs, hy, hCt, hn₀⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine hJ2 _ _ ?_ (hJ1 _ _ hConvex hR)
  rintro T hT ⟨hP, hCs, hy, hCt0, hn2⟩ t x hx ι _ _ d n w M hw hM
  obtain ⟨Ψ, K, hag, hcv, hs0, hsl⟩ := hP t x hx ι d n w M hw hM
  have hx1 : 1 ≤ x := hy.trans hx
  have hlam : 0 < T.chainParams.lam := hT.chain_admissible.positivity.2.2.1
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hcut : IsCutoff T.ballRadius T.p := hT.cutoff
  have hκ := hT.κ_pos
  obtain ⟨hW0, hWs⟩ := hWspec T hκ
  have hm : 0 < x * T.chainParams.lam / 4 := by positivity
  have hn : 0 < n := by
    by_contra h
    have h0 : n = 0 := by omega
    subst h0
    have := hw.2
    simp at this
  set M₀ := M ⟨0, hn⟩ with hM₀
  have hA := hM ⟨0, hn⟩
  have hbd : IsPseudoMetricOnBonds d := isPseudoMetricOnBonds_of_preserves hA.preservesCellDist
  have hWsum : ∀ b₀ : ι, ∑ b, Real.exp (-(2 * T.κ * d b b₀)) ≤ Wt T := by
    intro b₀
    obtain ⟨hL1, -, nn, hnn, hn0⟩ := hA.isCubicTopTorus
    have hs : ∀ i, 2 ≤ M₀.frame.extent i := fun i => by rw [hnn i]; omega
    have hLodd : Odd M₀.frame.blockSide := hL1 ▸ hT.odd_L
    have h1 := hWs M₀.frame ι (fun i => enclosingCell (M₀.embed i).1.1) (fun z => by
      have := card_fiber_le hLodd hs hA.embed_injective z
      rw [hL1] at this
      convert this) (enclosingCell (M₀.embed b₀).1.1)
    refine le_trans (le_of_eq ?_) h1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hA.preservesCellDist]
  set Φ := convexCombinationExponent T.chainParams.lam x w M with hΦ
  have hd := ballDensity_congr (p := T.p) hag
  have hmean : ∀ f, ballExpectation (cutoffFactor T.ballRadius T.p) Φ f =
      ballExpectation (cutoffFactor T.ballRadius T.p) Ψ f := fun f => by
    simp only [ballExpectation, hd]
  have hdensr : ballDensity (fun u => cutoffFactor T.ballRadius T.p (max u 0)) Ψ =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ := by
    funext η
    simp [ballDensity, radialWeightProd, norm_nonneg]
  refine ⟨fun f g hf hg => ?_, fun q b => ?_, fun j q N b hj hq => ?_⟩
  · have hcov : ballCovariance (cutoffFactor T.ballRadius T.p) Φ f g =
        ballCovariance (cutoffFactor T.ballRadius T.p) Ψ f g := by
      simp only [ballCovariance, hmean]
    have hnorm : ∀ h, ballL2Norm (cutoffFactor T.ballRadius T.p) Φ h =
        ballL2Norm (cutoffFactor T.ballRadius T.p) Ψ h := fun h => by
      simp only [ballL2Norm, hmean]
    rw [hcov]
    simp only [hnorm]
    refine (hCov ι T.ballRadius (x * T.chainParams.lam / 4) T.κ d Ψ K T.p hρ hm hκ.le hcut hbd hcv f g hf hg).trans ?_
    have hS : 0 ≤ ∑ b, ∑ b', ballL2Norm (cutoffFactor T.ballRadius T.p) Ψ (bondGradNorm f b) *
        Real.exp (-(T.κ * d b b')) * ballL2Norm (cutoffFactor T.ballRadius T.p) Ψ (bondGradNorm g b') :=
      Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun b' _ => by
        unfold ballL2Norm
        positivity
    refine mul_le_mul_of_nonneg_right ?_ hS
    have e : (x * T.chainParams.lam / 4)⁻¹ = 4 / T.chainParams.lam / x := by field_simp
    rw [e]
    gcongr
  · rw [hmean]
    have h1 := hMom ι T.ballRadius (x * T.chainParams.lam / 4) T.κ (Wt T) d Ψ K _ hρ hm hκ.le
      (hCut T.ballRadius T.p hρ hcut) hbd hcv hWsum hs0 q b
    have e1 : ballExpectation (fun u => cutoffFactor T.ballRadius T.p (max u 0)) Ψ (fun η => ‖η b‖ ^ (2 * q)) =
        ballExpectation (cutoffFactor T.ballRadius T.p) Ψ (fun η => ‖η b‖ ^ (2 * q)) := by
      simp only [ballExpectation, hdensr]
    rw [e1] at h1
    refine h1.trans (le_of_eq ?_)
    show _ = (∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * Wt T)) * (4 / T.chainParams.lam) ^ q * (x ^ q)⁻¹
    rw [show x * T.chainParams.lam / 4 = x * (T.chainParams.lam / 4) by ring, mul_pow, div_pow, div_pow]
    field_simp
  · have hcond : 0 < T.ballRadius ∧ IsCutoff T.ballRadius T.p ∧ 0 < T.chainParams.lam ∧ 0 ≤ T.Ct ∧ 0 ≤ Wt T ∧
        1 ≤ j ∧ 1 ≤ q :=
      ⟨hρ, hcut, hlam, hCt0, hW0, hj, hq⟩
    have hspec := (Classical.choose_spec
      (hRim T.ballRadius T.p T.chainParams.lam T.Ct (Wt T) hρ hcut hlam hCt0 hW0 j q N hj hq)).2
      ι x T.κ d Ψ K hx1 hκ.le hbd hcv hWsum hs0 hsl b
    have e0 : Cr (momentParameters T) j q N =
        Classical.choose (hRim T.ballRadius T.p T.chainParams.lam T.Ct (Wt T) hρ hcut hlam hCt0 hW0 j q N hj hq) := by
      simp only [hCr]
      exact dif_pos hcond
    rw [hd, hmean, e0]
    exact hspec
end Interpolation
end YangMills.Construction
end
