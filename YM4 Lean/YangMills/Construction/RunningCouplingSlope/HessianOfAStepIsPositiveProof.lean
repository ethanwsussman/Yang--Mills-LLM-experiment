import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexAboveAChartPointProof
import YangMills.Construction.ColdStepAtMirrorFrames.EnergyAboutAChartPointProof
import YangMills.Construction.ColdStepAtMirrorFrames.FitsAlongMoves
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionAcrossFrames
import YangMills.Construction.ColdStepAtMirrorFrames.OneLeastChart
import YangMills.Construction.ColdStepAtMirrorFrames.PlainChainAtLevelZero
import YangMills.Construction.ColdStepAtMirrorFrames.SumsOverTheSitesOfATorus
import YangMills.Construction.ColdStepAtMirrorFrames.ThroughTheMovedChart
import YangMills.Construction.RunningCouplingSlope.HessianOfAStepIsPositive
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenBoundsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
section Transfer
variable {F G : BlockFrame}
private theorem transferSite_siteOfCoords {k : ℕ} (hper : ∀ i, F.period k i = G.period k i) (z : Fin 4 → ℤ) :
    transferSite G (siteOfCoords k z : F.Site k) = (siteOfCoords k z : G.Site k) := by apply _root_.YangMills.Construction.FrameTorusAction.transferSite_siteOfCoords <;> assumption
abbrev _root_.YangMills.SharedProofs.p84300 := @transferSite_siteOfCoords
private theorem transferSite_transferSite {k : ℕ} (hper : ∀ i, F.period k i = G.period k i) (x : F.Site k) :
    transferSite F (transferSite G x) = x := by apply _root_.YangMills.Construction.FrameTorusAction.transferSite_transferSite <;> assumption
private theorem transferField_leftTranslate {k n : ℕ} (hper : ∀ i, F.period k i = G.period k i)
    (c : Fin n → F.Site k × Fin 4) (X : Fin n → imaginaryQuaternions) (τ : Fin n → ℝ) (U : F.GaugeField k) :
    transferField G (leftTranslate (bondSpread c X τ) U) =
      leftTranslate (bondSpread (fun l => (transferSite G (c l).1, (c l).2)) X τ) (transferField G U) := by
  funext x i
  simp only [transferField, leftTranslate, bondSpread]
  congr 2
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : c l = (transferSite F x, i)
  · have h' : ((transferSite G (c l).1, (c l).2) : G.Site k × Fin 4) = (x, i) := by
      rw [h]
      exact Prod.ext (transferSite_transferSite (fun i => (hper i).symm) x) rfl
    rw [if_pos h, if_pos h']
  · have h' : ¬ ((transferSite G (c l).1, (c l).2) : G.Site k × Fin 4) = (x, i) := by
      intro e
      apply h
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      dsimp only at e1 e2
      exact Prod.ext (by rw [← e1, transferSite_transferSite hper]) e2
    rw [if_neg h, if_neg h']
abbrev _root_.YangMills.SharedProofs.p8763 := @transferField_leftTranslate
private theorem analyticAt_of_transfer {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k n : ℕ}
    (hper : ∀ i, F.period k i = G.period k i) {Φ : F.GaugeField k → E} {Ψ : G.GaugeField k → E}
    {U : F.GaugeField k} (c : Fin n → F.Site k × Fin 4) (X : Fin n → imaginaryQuaternions)
    (h : ∀ τ : Fin n → ℝ, Φ (leftTranslate (bondSpread c X τ) U) =
      Ψ (transferField G (leftTranslate (bondSpread c X τ) U)))
    (ha : AnalyticAt ℝ (fun τ : Fin n → ℝ =>
      Ψ (leftTranslate (bondSpread (fun l => (transferSite G (c l).1, (c l).2)) X τ) (transferField G U))) 0) :
    AnalyticAt ℝ (fun τ : Fin n → ℝ => Φ (leftTranslate (bondSpread c X τ) U)) 0 := by
  refine ha.congr (Filter.Eventually.of_forall fun τ => ?_)
  show Ψ _ = Φ _
  rw [h τ, transferField_leftTranslate hper]
private theorem plaquetteHolonomy_transferField (hA : MinimalActionTransfer) {A B : BlockFrame} {K k : ℕ}
    (a : ℝ) (h : SharePeriods A B K) (hk : k ≤ K) (U : A.GaugeField k) (p : A.Site k × Fin 4 × Fin 4) :
    plaquetteHolonomy (transferField B U) (transferSite B p.1, p.2) = plaquetteHolonomy U p := by
  obtain ⟨x, μ, ν⟩ := p
  have e := (hA A B K a h).2.2.2.2.1 k U [(μ, true), (ν, true), (μ, false), (ν, false)] (siteCoords x) hk
  unfold plaquetteHolonomy
  dsimp only
  rw [ColdStepAtMirrorFrames.siteOfCoords_siteCoords] at e
  exact e
abbrev _root_.YangMills.SharedProofs.p90208 := @plaquetteHolonomy_transferField
private theorem isSmallCurvature_transferField (hA : MinimalActionTransfer) {A B : BlockFrame} {K : ℕ}
    (a : ℝ) (h : SharePeriods A B K) {s : ℝ} {U : A.GaugeField K} (hU : IsSmallCurvature s U) :
    IsSmallCurvature s (transferField B U) := by
  rintro ⟨x, μ, ν⟩ hp
  have e := plaquetteHolonomy_transferField hA a h le_rfl U (transferSite A x, μ, ν)
  have hx : transferSite B (transferSite A x) = x :=
    transferSite_transferSite (fun i => (h.period_eq K le_rfl i).symm) x
  dsimp only at e
  rw [hx] at e
  unfold plaquetteDefect
  rw [e]
  exact hU _ hp
abbrev _root_.YangMills.SharedProofs.p56584 := @isSmallCurvature_transferField
end Transfer
section Levels
private abbrev upperFrame (L j : ℕ) (ext : Fin 4 → ℕ) : BlockFrame := ⟨L, j + 1, ext⟩
private abbrev lowerFrame (L j : ℕ) (ext : Fin 4 → ℕ) : BlockFrame := ⟨L, j, fun i => ext i * L⟩
variable {L j : ℕ} {ext : Fin 4 → ℕ}
private theorem lowerFrame_period :
    ∀ k, k ≤ j + 1 → ∀ i, (upperFrame L j ext).period k i = (lowerFrame L j ext).period k i := by
  intro k hk i
  show ext i * L ^ (j + 1 + 1 - k) = ext i * L * L ^ (j + 1 - k)
  have e : j + 1 + 1 - k = (j + 1 - k) + 1 := by omega
  rw [e, pow_succ]
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p501881 := @lowerFrame_period
private theorem sharePeriods_lowerFrame (hL : Odd L) (hext : ∀ i, 0 < ext i) :
    SharePeriods (upperFrame L j ext) (lowerFrame L j ext) (j + 1) :=
  ⟨rfl, hL, hext, fun i => Nat.mul_pos (hext i) hL.pos, Nat.le_succ _, le_rfl, lowerFrame_period⟩
end Levels
private theorem minimalAction_analyticAt (hA : MinimalActionTransfer) (hZ : WilsonActionColdEstimates)
    {a δ lam ρ σA cg : ℝ} {L' : ℕ} {N : ℕ → ℝ} (hL : Odd L')
    (hc : ColdChain.ColdChainConstants a δ L' lam ρ σA cg N)
    {F : BlockFrame} (hT : IsBlockTorus L' F) {s : ℝ} (hs : 0 < s) (hsσ : s ≤ σA) {U : F.GaugeField F.depth}
    (hU : IsSmallCurvature s U) (k : ℕ) (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) :
    AnalyticAt ℝ (fun τ : Fin k → ℝ =>
      minimalAction a (finiteCells F) F.depth (leftTranslate (bondSpread c X τ) U)) 0 := by
  obtain ⟨hδ, hδ8, -, -, -, -, -, -, hch⟩ := hc
  rcases F with ⟨L, t, ext⟩
  have hb : L = L' := hT.1
  subst hb
  cases t with
  | zero =>
    obtain ⟨N₀, -, hz⟩ := hZ
    exact ((hz a δ 0 0 hδ.le hδ8 le_rfl).1 _ s U rfl hL hT.2 hs hU).minimalAction_analytic k c X
  | succ j =>
    obtain ⟨n, hn, hsd⟩ := hT.2
    have hext : ∀ i, 0 < ext i := fun i => by
      have : ext i = n := hsd i
      omega
    have h := sharePeriods_lowerFrame (j := j) hL hext
    have hper := lowerFrame_period (L := L) (j := j) (ext := ext) (j + 1) le_rfl
    have hamb : IsAdmissibleAmbient (lowerFrame L j ext) := Or.inr fun i => by
      show 64 ≤ ext i * L
      have e : ext i = n := hsd i
      rw [e]
      exact hn.trans (Nat.le_mul_of_pos_right n hL.pos)
    have hreg : IsOrthantRegular (finiteCells (lowerFrame L j ext)) 1024 :=
      TopLevelSites.isOrthantRegular_finiteCells h.extent_pos_right 1024
    have hcold := isSmallCurvature_transferField hA a h hU
    obtain ⟨-, -, H3, -⟩ := hch (lowerFrame L j ext) 1024 _ rfl hamb le_rfl hreg s _ hs hsσ
      (fun p hp' => hcold p (Finset.mem_filter.1 hp').2.1)
    have h1 := H3.1 k (fun l => (transferSite (lowerFrame L j ext) (c l).1, (c l).2)) X
    exact analyticAt_of_transfer hper c X (fun τ => (hA _ _ (j + 1) a h).1 (j + 1) _ le_rfl) h1
section Chart
variable {F : BlockFrame}
private theorem finite_siteBonds (hL : 0 < F.blockSide) (hext : ∀ i, 0 < F.extent i) (k : ℕ) :
    Finite (F.Site k × Fin 4) := by
  have : ∀ i, Finite (ZMod (F.period k i)) := fun i => by
    have : NeZero (F.period k i) := ⟨(period_pos hL hext k i).ne'⟩
    exact inferInstance
  have : Finite (F.Site k) := Pi.finite
  exact inferInstance
private theorem chartRestriction_analyticAt (hth : TranslatedChartCompositeBound)
    (hfit : BlockFitAnalyticAlongTranslates) {a : ℝ} {L : ℕ}
    (hLo : Odd L) (hFL : F.blockSide = L) (hext : ∀ i, 2 ≤ F.extent i)
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    (hsmall : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ 1 / (64 * (L : ℝ)))
    (hAna : ∀ (k : ℕ) (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions),
      AnalyticAt ℝ (fun τ : Fin k → ℝ =>
        minimalAction a (finiteCells F) F.depth (leftTranslate (bondSpread c X τ) (chartedField w V))) 0)
    {k : ℕ} (q : Fin k → ChartDirection F) : AnalyticAt ℝ (chartRestriction a w V q) 0 := by
  classical
  obtain ⟨C1, -, hth⟩ := hth
  obtain ⟨C2, -, hfit⟩ := hfit L hLo
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    have := hext i
    omega
  have hfin := finite_siteBonds (F := F) (hFL ▸ hLo.pos) hpos F.depth
  have hfin' : Fintype (F.Site F.depth × Fin 4) := Fintype.ofFinite _
  set ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions := fun l => directionCoordinate (q l) with hξdef
  set μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions := fun l => directionMove (q l) with hμdef
  obtain ⟨hA1, -⟩ := hth F (minimalAction a (finiteCells F) F.depth) w V k ξ μ (fun _ => Finset.univ) 0 0
    (fun _ _ _ => Finset.mem_univ _) hAna
  have hSum : AnalyticAt ℝ (fun σ => ∑ cb ∈ innerBonds (finiteCells F) F.top,
      blockFit (translatedChart w V ξ μ σ) (translatedTop V μ σ) cb) 0 :=
    Finset.analyticAt_fun_sum _ fun cb _ => (hfit F w V k ξ μ cb hFL hext hsmall).1
  have hchart : chartRestriction a w V q = fun σ =>
      minimalAction a (finiteCells F) F.depth (translatedChart w V ξ μ σ) +
      a * ∑ cb ∈ innerBonds (finiteCells F) F.top,
        blockFit (translatedChart w V ξ μ σ) (translatedTop V μ σ) cb := rfl
  rw [hchart]
  exact hA1.add (analyticAt_const.mul hSum)
private def stepCoordsLinear (hLC : ImaginaryCoordinatesIsometric) (x : F.Site F.depth) (i : Fin 4) :
    StepVariable (finiteCells F) →ₗ[ℝ] imaginaryQuaternions where
  toFun η := stepCoordinates η x i
  map_add' η ζ := by
    classical
    obtain ⟨ha, _⟩ := hLC
    simp only [stepCoordinates]
    split_ifs
    · exact ha _ _
    · simp
  map_smul' c η := by
    classical
    obtain ⟨_, hs, _⟩ := hLC
    simp only [stepCoordinates, RingHom.id_apply]
    split_ifs
    · exact hs _ _
    · simp
private theorem contDiffAt_chartedEnergyAt (hLC : ImaginaryCoordinatesIsometric)
    (hCE : ChartedEnergyInCoordinates) (a : ℝ) (p : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (hodd : Odd F.blockSide) (hext : ∀ i, 2 ≤ F.extent i)
    (hA : AnalyticAt ℝ (chartRestriction a p V (chartDirections F)) 0) (n : ℕ) :
    ContDiffAt ℝ n (chartedEnergyAt a p V) 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedEnergyLocal.contDiffAt_chartedEnergyAt <;> assumption
end Chart
section Calculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem deriv_deriv_line {Ψ : E → ℝ} {η : E} (u : E) (h : ContDiffAt ℝ (2 : ℕ) Ψ η) :
    deriv (deriv fun τ : ℝ => Ψ (η + τ • u)) 0 = fderiv ℝ (fun y => fderiv ℝ Ψ y u) η u := by
  have hline : ∀ τ : ℝ, HasDerivAt (fun s : ℝ => η + s • u) u τ := fun τ => by
    simpa using ((hasDerivAt_id τ).smul_const u).const_add η
  have hnear : ∀ᶠ y in nhds η, ContDiffAt ℝ (2 : ℕ) Ψ y := h.eventually (by simp)
  have htend : Filter.Tendsto (fun s : ℝ => η + s • u) (nhds 0) (nhds η) := by
    have := (hline 0).continuousAt.tendsto
    simpa using this
  have h1 : (deriv fun τ : ℝ => Ψ (η + τ • u)) =ᶠ[nhds 0] fun τ => fderiv ℝ Ψ (η + τ • u) u := by
    filter_upwards [htend.eventually hnear] with τ hτ
    have hd : DifferentiableAt ℝ Ψ (η + τ • u) := hτ.differentiableAt (by norm_num)
    exact (hd.hasFDerivAt.comp_hasDerivAt τ (hline τ)).deriv
  rw [h1.deriv_eq]
  have hΨ : DifferentiableAt ℝ (fun y => fderiv ℝ Ψ y u) η := by
    have h3 : ContDiffAt ℝ (1 : ℕ) (fderiv ℝ Ψ) η := h.fderiv_right (by norm_num)
    exact (h3.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have h4 := hΨ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) (by simp)
  exact h4.deriv
abbrev _root_.YangMills.SharedProofs.p27006 := @deriv_deriv_line
private theorem fderiv_fderiv_apply_eq {g : E → ℝ} {y : E} (hg : ContDiffAt ℝ (2 : ℕ) g y) (u v : E) :
    fderiv ℝ (fun z => fderiv ℝ g z u) y v = fderiv ℝ (fderiv ℝ g) y v u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) y :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const u y)).fderiv
  have e : fderiv ℝ (fun z => fderiv ℝ g z u) y = (fderiv ℝ (fderiv ℝ g) y).flip u := by
    simpa using this
  rw [e]
  rfl
end Calculus
section Form
variable {β : Type} [Fintype β] [DecidableEq β]
private theorem posDef_of_secondDeriv_floor {Ψ : BondField β → ℝ} (h : ContDiffAt ℝ (2 : ℕ) Ψ 0) {lam : ℝ}
    (hl : 0 < lam) (hfl : ∀ u : BondField β, lam * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong Ψ 0 u u)
    {H : Matrix (β × Fin 3) (β × Fin 3) ℝ}
    (hH : ∀ i j, H i j = secondDerivAlong Ψ 0 (bondVariation i.1 (EuclideanSpace.single i.2 1))
      (bondVariation j.1 (EuclideanSpace.single j.2 1))) :
    H.PosDef := by
  set D := fderiv ℝ (fderiv ℝ Ψ) 0 with hD
  have hsec : ∀ u v, secondDerivAlong Ψ 0 u v = D v u := fun u v => fderiv_fderiv_apply_eq h u v
  have hsym : ∀ u v, D u v = D v u := fun u v => (h.isSymmSndFDerivAt (by simp)) u v
  set e : β × Fin 3 → BondField β := fun i => bondVariation i.1 (EuclideanSpace.single i.2 1) with he
  have hHD : ∀ i j, H i j = D (e i) (e j) := fun i j => by
    rw [hH, hsec, hsym]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    rw [hHD, hHD, hsym]
  · set u : BondField β := ∑ i, x i • e i with hu
    have hform : star x ⬝ᵥ (H.mulVec x) = D u u := by
      have e1 : D u u = ∑ i, ∑ j, x i * (D (e i) (e j) * x j) := by
        rw [hu]
        simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e1]
      simp only [dotProduct, Matrix.mulVec, star_trivial, Pi.star_apply, Finset.mul_sum, hHD]
    have hval : ∀ (b : β) (c : Fin 3), u b c = x (b, c) := by
      intro b c
      have hev := map_sum (((EuclideanSpace.proj c : BondVector →L[ℝ] ℝ) : BondVector →ₗ[ℝ] ℝ) ∘ₗ
        (LinearMap.proj b : BondField β →ₗ[ℝ] BondVector)) (fun i => x i • e i) Finset.univ
      have hev' : u b c = ∑ i, x i * e i b c := by
        refine hev.trans (Finset.sum_congr rfl fun i _ => ?_)
        simp
      rw [hev', Finset.sum_eq_single (b, c)]
      · simp [he, bondVariation]
      · intro i _ hi
        have : e i b c = 0 := by
          by_cases hb : i.1 = b
          · have hc : c ≠ i.2 := fun h => hi (Prod.ext hb h.symm)
            subst hb
            simp [he, bondVariation, hc]
          · simp [he, bondVariation, Ne.symm hb]
        rw [this, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hnorm : ∑ b, ‖u b‖ ^ 2 = ∑ i, x i ^ 2 := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hval, Real.norm_eq_abs, sq_abs]
    have hpos : 0 < ∑ i, x i ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      have hi' : x i ≠ 0 := hi
      exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩
    have h1 := hfl u
    rw [hnorm, hsec] at h1
    rw [hform]
    exact lt_of_lt_of_le (mul_pos hl hpos) h1
end Form
end ColdStepAtMirrorFrames
namespace RunningCouplingSlope
open ColdStepAtMirrorFrames RenormalizationStepParameters ReferenceDensity TorusFields
variable {F : BlockFrame}
private theorem mem_innerPlaquettes_of_lt (hodd : Odd F.blockSide) (hext : ∀ i, 0 < F.extent i) {k : ℕ}
    (hk : k ≤ F.top) (p : F.Site k × Fin 4 × Fin 4) (h : p.2.1 < p.2.2) :
    p ∈ innerPlaquettes (finiteCells F) k := by
  unfold innerPlaquettes
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
  exact ⟨⟨mem_allSites hodd hext hk _, Finset.mem_univ _, Finset.mem_univ _⟩, h,
    fun x _ => mem_allSites hodd hext hk x⟩
private theorem stepCoordinates_of_not_mem {η : StepVariable (finiteCells F)} {b : F.Site F.depth × Fin 4}
    (h : b ∉ chordBonds (finiteCells F)) : stepCoordinates η b.1 b.2 = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_of_not_mem <;> assumption
private theorem stepCoordinates_chord (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) :
    stepCoordinates η b.1.1 b.1.2 = toImaginary (η b) := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.stepCoordinates_of_chordBond <;> assumption
private theorem chartedHessian_posDef (hA : MinimalActionTransfer) (hZ : WilsonActionColdEstimates)
    (hth : TranslatedChartCompositeBound) (hfit : BlockFitAnalyticAlongTranslates)
    (hCE : ChartedEnergyInCoordinates) (hLC : ImaginaryCoordinatesIsometric) (hOLC : MinimizingChartUnique)
    (T : ParameterAssignment) (hT : T.Admissible) (hF : IsBlockTorus T.side F) (V : F.GaugeField F.top)
    (hV : IsSmallCurvature (9 / 8 * T.threshold) V) :
    (chartedHessian T.coupling T.ρA V 0).PosDef := by
  obtain ⟨hFL, n, hn, hext⟩ := id hF
  have hLo : Odd T.side := hT.L_odd
  have hoddF : Odd F.blockSide := hFL ▸ hLo
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hext i]
    omega
  have hs0 : ∀ i, 0 < F.extent i := fun i => by
    have := hs2 i
    omega
  have hcc := hT.chain
  obtain ⟨hδ, hδ8, hlam, hρ, hρ1, hσA, hcg, hN, hch⟩ := id hcc
  have hσ := hT.σ_pos
  have hs : 0 < 9 / 8 * T.threshold := by positivity
  have hsσ : 9 / 8 * T.threshold ≤ T.σA := by
    have := hT.σ_le
    linarith
  have hreg : IsOrthantRegular (finiteCells F) 1024 := TopLevelSites.isOrthantRegular_finiteCells hs0 1024
  have hamb : IsAdmissibleAmbient F := Or.inr fun i => by
    rw [hext i]
    exact hn
  obtain ⟨hOne, hFloor, -⟩ := hch F 1024 (finiteCells F) hFL hamb le_rfl hreg (9 / 8 * T.threshold) V hs hsσ
    (fun p hp => hV p (Finset.mem_filter.1 hp).2.1)
  obtain ⟨w₀, hw₀, -, -⟩ := id hOne
  have hw₁ : IsMinimizingChart T.coupling (finiteCells F) V T.ρA w₀ :=
    ⟨hw₀.1, fun b hb => (hw₀.2.1 b hb).trans (min_le_left _ _), hw₀.2.2⟩
  have hex : ∃ w, IsMinimizingChart T.coupling (finiteCells F) V T.ρA w := ⟨w₀, hw₁⟩
  have hlc : IsMinimizingChart T.coupling (finiteCells F) V T.ρA
      (minimizingCoordinates T.coupling (finiteCells F) V T.ρA) := by
    unfold minimizingCoordinates
    rw [dif_pos hex]
    exact hex.choose_spec
  generalize hlcd : minimizingCoordinates T.coupling (finiteCells F) V T.ρA = lc at hlc
  obtain ⟨huniq, hcoldS⟩ := hOLC F T.coupling T.ρA (T.N 0) (9 / 8 * T.threshold) V lc hoddF hs2 hρ1 hOne hlc
  have hw : w₀ = lc := huniq w₀ hw₁
  have hL0 : (0 : ℝ) < T.side := by exact_mod_cast hLo.pos
  have hN0 := hN 0
  have hsmall : ∀ b ∈ chordBonds (finiteCells F), ‖lc b.1 b.2‖ ≤ 1 / (64 * (T.side : ℝ)) := fun b hb => by
    have h1 := (hw₀.2.1 b hb).trans (min_le_right _ _)
    rw [hw] at h1
    refine h1.trans ?_
    rw [le_div_iff₀ (by positivity)]
    have h2 := hT.σ_L
    have h3 : 0 ≤ (T.side : ℝ) * T.N 0 * T.threshold := by positivity
    have h4 : 0 ≤ (T.side : ℝ) * T.threshold := by positivity
    have e1 : T.N 0 * (9 / 8 * T.threshold) * (64 * (T.side : ℝ)) =
        72 * ((T.side : ℝ) * T.N 0 * T.threshold) := by ring
    have e2 : 2 ^ 10 * (T.side : ℝ) * (T.N 0 + 1) * T.threshold =
        1024 * ((T.side : ℝ) * T.N 0 * T.threshold) + 1024 * ((T.side : ℝ) * T.threshold) := by ring
    rw [e1]
    rw [e2] at h2
    linarith
  have hcold' : IsSmallCurvature (9 / 8 * T.threshold / 8) (chartedField lc V) := fun p hp =>
    hcoldS p (mem_innerPlaquettes_of_lt hoddF hs0 (Nat.le_succ _) p hp)
  have hAna := minimalAction_analyticAt hA hZ hLo hcc hF (by positivity : 0 < 9 / 8 * T.threshold / 8)
    (by linarith) hcold'
  have hal := chartRestriction_analyticAt hth hfit hLo hFL hs2 hsmall hAna (chartDirections F)
  have hcd : ContDiffAt ℝ (2 : ℕ) (chartedEnergyAt T.coupling lc V) 0 :=
    contDiffAt_chartedEnergyAt hLC hCE T.coupling lc V hoddF hs2 hal 2
  have hΨ : chartedEnergyAtMinimizer T.coupling T.ρA V = chartedEnergyAt T.coupling lc V := by
    funext η
    rw [← hlcd]
    rfl
  have hfl : ∀ u : StepVariable (finiteCells F),
      T.lam * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong (chartedEnergyAt T.coupling lc V) 0 u u := by
    intro u
    have h1 := hFloor lc (stepCoordinates u) hlc.1 (fun b hb => stepCoordinates_of_not_mem hb) hlc.2.1
      (fun p hp => by
        have h2 := hcoldS p hp
        have h3 : 9 / 8 * T.threshold / 8 ≤ T.σA := by linarith
        exact lt_of_lt_of_le h2 h3)
    have hfun : (fun τ : ℝ => blockEnergy T.coupling (finiteCells F) F.depth
        (chartedField (fun x i => lc x i + τ • stepCoordinates u x i) V) V) =
        fun τ : ℝ => chartedEnergyAt T.coupling lc V (0 + τ • u) := by
      funext τ
      have e : (fun x i => lc x i + τ • stepCoordinates u x i) =
          fun x i => lc x i + stepCoordinates ((0 : StepVariable (finiteCells F)) + τ • u) x i := by
        funext x i
        rw [zero_add]
        congr 1
        exact ((stepCoordsLinear hLC x i).map_smul τ u).symm
      rw [e]
      rfl
    rw [hfun, deriv_deriv_line u hcd] at h1
    have hsum : ∑ b ∈ chordBonds (finiteCells F), ‖stepCoordinates u b.1 b.2‖ ^ 2 = ∑ b, ‖u b‖ ^ 2 := by
      rw [← Finset.sum_coe_sort]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [stepCoordinates_chord, hLC.2.2.1]
    rw [hsum] at h1
    exact h1
  refine posDef_of_secondDeriv_floor hcd hlam hfl fun i j => ?_
  show secondDerivAlong (chartedEnergyAtMinimizer T.coupling T.ρA V) 0 _ _ = _
  rw [hΨ]
private theorem isSmallCurvature_readAtLevel {L t n : ℕ} [NeZero n] {s : ℝ} {V : TorusField n}
    (hV : IsCold s V) :
    IsSmallCurvature (F := torusFrame L t n) s (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by
  rintro ⟨x, μ, ν⟩ hlt
  have hp : ∀ i, (torusFrame L t n).period (torusFrame L t n).top i = n := fun i => TopLevelSites.period_top i
  rw [TopLevelSites.plaquetteDefect_readAtLevel_eq hp]
  exact hV _ μ ν hlt
abbrev _root_.YangMills.SharedProofs.p2155 := @isSmallCurvature_readAtLevel
theorem stepHessianPosDefStatement_holds (hA : MinimalActionTransfer) (hZ : WilsonActionColdEstimates)
    (hth : TranslatedChartCompositeBound) (hfit : BlockFitAnalyticAlongTranslates)
    (hCE : ChartedEnergyInCoordinates) (hLC : ImaginaryCoordinatesIsometric) (hOLC : MinimizingChartUnique) :
    stepHessianPosDefStatement := by
  intro T hT t n _ V hn hV
  exact chartedHessian_posDef hA hZ hth hfit hCE hLC hOLC T hT ⟨rfl, n, hn, fun _ => rfl⟩ _
    (isSmallCurvature_readAtLevel hV)
end RunningCouplingSlope
end YangMills.Construction
end
