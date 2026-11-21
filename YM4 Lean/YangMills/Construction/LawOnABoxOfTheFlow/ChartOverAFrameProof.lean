import YangMills.Construction.LawOnABoxOfTheFlow.BorelChartOfABox
import YangMills.Construction.LawOnABoxOfTheFlow.ChartOverAFrame
import YangMills.Construction.LawOnABoxOfTheFlow.DensityGivenTheOutside
import YangMills.Construction.LawOnABoxOfTheFlow.DrawsBelowATopHaveTheirLaw
import YangMills.Construction.LawOnABoxOfTheFlow.GaussianOfTheSliceIsBorel
import YangMills.Construction.LawOnABoxOfTheFlow.GaussianOffTheEllipsoid
import YangMills.Construction.LawOnABoxOfTheFlow.KernelsOfALaw
import YangMills.Construction.LawOnABoxOfTheFlow.LawGivenTheOutside
import YangMills.Construction.LawOnABoxOfTheFlow.OnePointInAnOrbit
import YangMills.Construction.LawOnABoxOfTheFlow.ToolsOfAChart
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps RenormalizationStepParameters StepSettings BoxEvents WeightedResponses MeasureKernels
open BlockAverages hiding gaugeTransform unitStep
open ResponseInTheExpansion hiding gaugeTransform
set_option synthInstance.maxSize 1024
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
variable {params : StepParameters} {n : ℕ} [NeZero n]
private instance isProbabilityMeasure_innerHaar (o : TorusSite n) (R : ℕ) : IsProbabilityMeasure (innerHaar o R) := by
  unfold innerHaar
  infer_instance
private theorem measurable_kernel_section_comp {V Q' : Type*} [MeasurableSpace V] [MeasurableSpace Q'] {p : V → Prop}
    {Γ : V → Measure V} (h : ∀ E : Set (V × V), MeasurableSet E → Measurable fun A : {A : V // p A} => Γ A.1 {ζ | (A.1, ζ) ∈ E})
    {A : Q' → V} (hA : Measurable A) (hp : ∀ q, p (A q)) {E : Set (V × V)} (hE : MeasurableSet E) :
    Measurable fun q => Γ (A q) {ζ | (A q, ζ) ∈ E} :=
  (h E hE).comp (Measurable.subtype_mk hA : Measurable fun q => (⟨A q, hp q⟩ : {A : V // p A}))
private theorem restrictInner_gaugeTransform_mem_gaugeOrbitsOverEllipsoid {a : ℝ} {L k : ℕ} {o : TorusSite n} {R : ℕ}
    {c₀ : ℝ} {g : TorusSite n → UnitQuaternion} {A : TorusBond n → imaginaryQuaternions}
    {u : OuterField o R} {w : InnerField o R} (hw : w ∈ gaugeOrbitsOverEllipsoid a L k o R c₀ g A u)
    {γ : TorusSite n → UnitQuaternion} (hγ : IsSupportedGauge o R γ) :
    restrictInner o R (gaugeTransform γ (glueField u w)) ∈ gaugeOrbitsOverEllipsoid a L k o R c₀ g A u := by
  obtain ⟨γ₁, ζ, h₁, hζ, hc⟩ := hw
  have hout : restrictOuter o R (gaugeTransform γ (glueField u w)) = u := by
    funext b
    have hb : b.1 ∉ bondsTouching o R := b.2
    have e1 : b.1.1 ∉ supBall o R := fun h => hb (Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl h⟩)
    have e2 : b.1.1 + unitStep n b.1.2 ∉ supBall o R := fun h => hb (Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr h⟩)
    show γ b.1.1 * glueField u w b.1.1 b.1.2 * (γ (b.1.1 + unitStep n b.1.2))⁻¹ = u b
    rw [hγ _ e1, hγ _ e2, one_mul, inv_one, mul_one]
    have hb' : ((b.1.1, b.1.2) : TorusBond n) ∉ bondsTouching o R := hb
    simp only [glueField, dif_neg hb']
  have hglue : glueField u (restrictInner o R (gaugeTransform γ (glueField u w))) = gaugeTransform γ (glueField u w) := by
    have h := glueField_restrictOuter_restrictInner (o := o) (R := R) (gaugeTransform γ (glueField u w))
    rwa [hout] at h
  refine ⟨γ₁ * γ⁻¹, ζ, ?_, hζ, ?_⟩
  · intro z hz
    simp [h₁ z hz, hγ z hz]
  · rw [hglue, gaugeTransform_gaugeTransform]
    have : g * (γ₁ * γ⁻¹) * γ = g * γ₁ := by
      rw [mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    rw [this]
    exact hc
set_option maxHeartbeats 4000000 in
theorem chartOverFrameStatement_holds (hLaw : conditionalLawGivenOuterStatement) (hDC : chartDensityStatement)
    (hDG : conditionalDensityStatement) (hDr : sampleBelowLawStatement)
    (hB : ellipsoidBoundsStatement) (hO : chartMeetsOrbitOnceStatement) (hF : cubeHessianStatement)
    (hGo : gaussianTailOffEllipsoidStatement) (hGb : sliceGaussianMeasurableStatement)
    (hBc : measurableChartStatement) (hSt : StageStatesMeasurableStatement) :
    chartOverFrameStatement := by
  refine holdsAtAdmissibleParameters_mono ?_ (holdsAtAdmissibleParameters_and hLaw (holdsAtAdmissibleParameters_and hDC
    (holdsAtAdmissibleParameters_and hDG (holdsAtAdmissibleParameters_and hDr holdsAtAdmissibleParameters_floorMin_le))))
  rintro Tb y hTb ⟨hL, hdc, hdg, hdr, hy₀⟩ κ₀ h1 h2
  obtain ⟨CQ, R₀, hCQ, hf⟩ := hF Tb hTb
  refine ⟨CQ * 2 ^ 14, fun C₀ hC₀ => ?_⟩
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by positivity) hC₀
  obtain ⟨K₁, xb, hK1, hb⟩ := hB Tb hTb κ₀ h1 h2 C₀ hC₀pos
  obtain ⟨xo, ho⟩ := hO Tb hTb κ₀ h1 h2 C₀ hC₀pos
  obtain ⟨xg, hgo⟩ := hGo Tb hTb κ₀ h1 h2 C₀ hC₀pos
  obtain ⟨xk, hgb⟩ := hGb Tb hTb κ₀ h1 h2
  obtain ⟨xc, hbc⟩ := hBc Tb hTb κ₀ h1 h2 C₀ hC₀pos
  obtain ⟨K₂, xd, hdc'⟩ := hdc κ₀ h1 h2 C₀ hC₀pos
  obtain ⟨cg, xe, hcg, hdg'⟩ := hdg κ₀ h1 h2 K₁
  refine ⟨max (max K₁ 7) (2 * max K₂ 0), max (max (max xb xo) (max xg xk)) (max (max xc xd) (max xe (((R₀ : ℝ) + 2) ^ 27))), ?_⟩
  intro T β k n _ o x R G₀ g A M hdat hx hR hn hbs hG₀ hg hA hM hax hY
  set xs := max (max (max xb xo) (max xg xk)) (max (max xc xd) (max xe (((R₀ : ℝ) + 2) ^ 27))) with hxs
  have hfl : xs ≤ x := by rw [hx]; exact hdat.le_coupling
  have hxb : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hfl
  have hxo : xo ≤ x := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hfl
  have hxg : xg ≤ x := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hfl
  have hxk : xk ≤ x := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hfl
  have hxc : xc ≤ x := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hfl
  have hxd : xd ≤ x := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hfl
  have hxe : xe ≤ x := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hfl
  have hxr : ((R₀ : ℝ) + 2) ^ 27 ≤ x := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hfl
  have hdatum : ∀ {xs' : ℝ}, xs' ≤ x → IsBoxDatum Tb y T β κ₀ xs' k n := fun h =>
    ⟨by rw [← hx]; exact h, hdat.onFamily, hdat.measurable, hdat.side_eq, hdat.coupling_rpow_le⟩
  have hRR : R₀ + 1 ≤ R := by
    rw [hR]
    refine le_boxRadius κ₀ x h1 (R₀ + 1) ?_
    push_cast
    calc ((R₀ : ℝ) + 1 + 1) ^ 27 = ((R₀ : ℝ) + 2) ^ 27 := by ring
      _ ≤ x := hxr
  have hR1 : 1 ≤ R := by omega
  have hRpos : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) ≤ ((R₀ : ℝ) + 2) ^ 27 := one_le_pow₀ (by
      have : (0 : ℝ) ≤ R₀ := Nat.cast_nonneg _
      linarith)
    linarith
  obtain ⟨-, -, -, hlin, hqf, -, hform⟩ := hf k n o R (by omega) hn
  have hst : IsTowerAtParameters Tb y T β k :=
    ⟨hdat.onFamily.startsAtWilson, fun j hj => hdat.onFamily.coupling_eq j (by omega),
      fun j hj => hdat.onFamily.onFamily j (by omega)⟩
  have hxk' : (T.stage k).coupling = x := by
    rw [hst.coupling_eq k (by omega), hx]
  have hyj : ∀ j ≤ k, y ≤ flowCoupling (Tb.stepParameters y) β j := fun j hj => by
    have h1 := (hst.onFamily j hj).le_coupling
    have h2 := hst.coupling_eq j (by omega)
    show y ≤ (couplingFlow (Tb.stepParameters y) β j).1
    rw [← h2]
    exact h1
  haveI hPp : IsProbabilityMeasure (markedSampleLaw T β k n) :=
    (hdr T β k 0 n hst hdat.measurable hyj).1
  have hfit : (Tb.stepParameters y).Admissible := hTb.fits y hy₀
  have hstate : Measurable (stageState T k n) := hSt _ hfit T k n
  set δ := boxScale x with hδ
  set c₀ := C₀ * (R : ℝ) ^ 4 * δ ^ 2 with hc₀
  set S := supBall o (2 * (R : ℝ)) with hS
  have hδ0 : 0 ≤ δ := by
    have : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h3 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    simp only [hδ, boxScale]
    positivity
  have hq : Continuous fun v : TorusBond n → imaginaryQuaternions => hessianForm Tb.coupling Tb.side k S v v :=
    continuous_hessianForm_diag hform
  have hELc : IsClosed {p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) |
      p.2 ∈ sliceEllipsoid Tb.coupling Tb.side k o R p.1 c₀} :=
    isClosed_sliceEllipsoid_graph Tb.coupling Tb.side k o R c₀ hq
  obtain ⟨hEm, coord, hcoord, hcsp⟩ := hbc x R k n o hxc hR hn
  let X : OuterData T k o R → Set (InnerField o R) := fun q =>
    gaugeOrbitsOverEllipsoid Tb.coupling Tb.side k o R c₀ (g q) (A q) q.1
  let pt : OuterData T k o R × InnerField o R → ChartPoint o R := fun p => (A p.1, g p.1, p.1.1, p.2)
  have hpt : Measurable pt :=
    (hA.comp measurable_fst).prodMk ((hg.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  let orb₀ : Set (OuterData T k o R × InnerField o R) :=
    (Prod.fst ⁻¹' G₀) ∩ pt ⁻¹' chartPointSet Tb.coupling Tb.side k o R c₀ δ
  have hOrb₀ : MeasurableSet orb₀ := (measurable_fst hG₀).inter (hpt hEm)
  have hmem₀ : ∀ q ∈ G₀, ∀ w, (q, w) ∈ orb₀ ↔ w ∈ X q := fun q hq' w =>
    ⟨fun h => h.2.2, fun h => ⟨hq', hax q hq', h⟩⟩
  obtain ⟨hHd, Z, hZ0, hZt, key⟩ := hL T β k n o R hst hdat.measurable hbs
  let cf : OuterData T k o R × InnerField o R → TorusBond n → imaginaryQuaternions := fun p => coord (pt p)
  have hcf : Measurable cf := hcoord.comp hpt
  let ind : OuterData T k o R × InnerField o R → ENNReal := orb₀.indicator (hullStateDensity T k o R)
  have hind : Measurable ind := hHd.indicator hOrb₀
  let m : OuterData T k o R → ENNReal := fun q => ∫⁻ w, ind (q, w) ∂(innerHaar o R)
  have hm : Measurable m := hind.lintegral_prod_right'
  let good : Set (OuterData T k o R) := G₀ ∩ {q | 0 < m q}
  have hgood : MeasurableSet good := hG₀.inter (measurableSet_lt measurable_const hm)
  let gam : OuterData T k o R → Measure (TorusBond n → imaginaryQuaternions) := fun q =>
    sliceGaussian Tb.coupling Tb.side k o R x (A q)
  let ell : OuterData T k o R → Set (TorusBond n → imaginaryQuaternions) := fun q =>
    sliceEllipsoid Tb.coupling Tb.side k o R (A q) c₀
  have hellm : ∀ q, MeasurableSet (ell q) := fun q =>
    (measurable_prodMk_left (x := A q)) hELc.measurableSet
  set ε₁ : ℝ := max K₂ 0 * ((R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) with hε₁
  have ht9 : 0 ≤ (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3 := by
    have : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h3 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    positivity
  have hε₁0 : 0 ≤ ε₁ := mul_nonneg (le_max_right _ _) ht9
  have hcold : ∀ q ∈ G₀, ∀ w ∈ X q, ∀ p ∈ plaquettesIn S,
      curvature (glueField q.1 w) p.1 p.2.1 p.2.2 ≤ K₁ * (R : ℝ) ^ 2 * δ := by
    rintro q hq' w ⟨γ, ζ, hγ, hζ, hc⟩ p hp
    have := ((hb x R k n o (A q) hxb hR hn (hax q hq')).2 ζ hζ).2.2.2 _ hc
    obtain ⟨v, β', -, -, -, h4⟩ := this
    have h5 := h4 p hp
    rwa [curvature_gaugeTransform] at h5
  have hchart : ∀ q ∈ good, ∃ (c : ℝ) (wt : (TorusBond n → imaginaryQuaternions) → ℝ), 0 < c ∧ Measurable wt ∧
      (∀ ζ ∈ ell q, 0 < wt ζ ∧ |Real.log (wt ζ)| ≤ ε₁) ∧
      ∀ Φ : (TorusBond n → imaginaryQuaternions) → ENNReal, Measurable Φ →
        ∫⁻ w, Φ (cf (q, w)) * ind (q, w) ∂(innerHaar o R) =
          ENNReal.ofReal c * ∫⁻ ζ in ell q, Φ ζ * ENNReal.ofReal (wt ζ) ∂(gam q) := by
    rintro q ⟨hq', hpos⟩
    have hexw : ∃ w, ind (q, w) ≠ 0 := by
      by_contra h
      push Not at h
      have : m q = 0 := by simp [m, h]
      exact absurd hpos (by simp [this])
    obtain ⟨w₀, hw₀⟩ := hexw
    have hw₀o : (q, w₀) ∈ orb₀ := by
      by_contra h
      exact hw₀ (Set.indicator_of_notMem h _)
    have hXw₀ : w₀ ∈ X q := (hmem₀ q hq' w₀).1 hw₀o
    have hHd₀ : hullStateDensity T k o R (q, w₀) ≠ 0 := by
      have : ind (q, w₀) = hullStateDensity T k o R (q, w₀) := Set.indicator_of_mem hw₀o _
      rwa [this] at hw₀
    have hHull : IsHullState (Tb.stepParameters y) (clusterRange x) (glueField q.1 w₀) q.2.1 ∧
        0 < (T.stage k).labelWeight n (glueField q.1 w₀) q.2.1 q.2.2 := by
      classical
      unfold hullStateDensity at hHd₀
      by_cases hh : IsHullState (Tb.stepParameters y) (clusterRange (T.stage k).coupling) (glueField q.1 w₀) q.2.1
      · rw [if_pos hh] at hHd₀
        exact ⟨hxk' ▸ hh, ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 hHd₀)⟩
      · rw [if_neg hh] at hHd₀
        exact absurd (by simp) hHd₀
    obtain ⟨c, wt, hc, hwtm, hwt, hint⟩ := hdc' T β k n o x R (g q) (A q) q.1 q.2.1 q.2.2 (hdatum hxd) hx hR
      (hax q hq') (hY q hq') ⟨w₀, hXw₀, hHull⟩
    refine ⟨c, wt, hc, hwtm, fun ζ hζ => ⟨(hwt ζ hζ).1, ?_⟩, fun Φ hΦ => ?_⟩
    · refine le_trans (hwt ζ hζ).2 ?_
      have : K₂ * ((R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) ≤ ε₁ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) ht9
      calc K₂ * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3
          = K₂ * ((R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) := by ring
        _ ≤ ε₁ := this
    · have hcoordq : ∀ w ∈ X q, ∃ γ : TorusSite n → UnitQuaternion, IsSupportedGauge o R γ ∧ cf (q, w) ∈ ell q ∧
          IsInChart S (A q) (cf (q, w)) (gaugeTransform (g q * γ) (glueField q.1 w)) := fun w hw =>
        hcsp (pt (q, w)) ⟨hax q hq', hw⟩
      have hI := hint (fun w => cf (q, w)) hcoordq Φ hΦ
      rw [show gam q = sliceGaussian Tb.coupling Tb.side k o R x (A q) from rfl, ← hI]
      have hXm : MeasurableSet (X q) := by
        have : X q = (fun w => (q, w)) ⁻¹' orb₀ := by
          ext w
          exact (hmem₀ q hq' w).symm
        rw [this]
        exact measurable_prodMk_left hOrb₀
      rw [← lintegral_indicator hXm]
      refine lintegral_congr fun w => ?_
      by_cases hw : w ∈ X q
      · rw [Set.indicator_of_mem hw]
        have hwo : (q, w) ∈ orb₀ := (hmem₀ q hq' w).2 hw
        have e1 : ind (q, w) = hullStateDensity T k o R (q, w) := Set.indicator_of_mem hwo _
        obtain ⟨hh, hp, -⟩ := hdg' T β k n o x R (hdatum hxe) hx hR (glueField q.1 w₀) (glueField q.1 w) q.2.1 q.2.2
          (by rw [restrictOuter_glueField, restrictOuter_glueField]) (hY q hq') (hcold q hq' w₀ hXw₀)
          (hcold q hq' w hw) hHull.1 hHull.2
        rw [e1]
        classical
        unfold hullStateDensity
        rw [if_pos (by rw [hxk']; exact hh)]
      · rw [Set.indicator_of_notMem hw]
        have hwo : (q, w) ∉ orb₀ := fun h => hw ((hmem₀ q hq' w).1 h)
        have e1 : ind (q, w) = 0 := Set.indicator_of_notMem hwo _
        rw [e1, mul_zero]
  have hgamq : ∀ q ∈ G₀, IsProbabilityMeasure (gam q) ∧ 1 - Real.exp (-((R : ℝ) ^ 4)) ≤ (gam q).real (ell q) := by
    intro q hq'
    have hcut : 2 * hessianForm Tb.coupling Tb.side k S (A q) (A q) ≤ c₀ := by
      have h3 := (hqf (A q)).2
      have h4 := (hax q hq').curlNormSq_le
      have h5 : CQ * curlNormSq S (A q) ≤ CQ * (2 ^ 13 * (R : ℝ) ^ 4 * δ ^ 2) :=
        mul_le_mul_of_nonneg_left h4 (by linarith)
      have h6 : 0 ≤ (R : ℝ) ^ 4 * δ ^ 2 := by positivity
      have h7 : CQ * 2 ^ 14 * ((R : ℝ) ^ 4 * δ ^ 2) ≤ C₀ * ((R : ℝ) ^ 4 * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hC₀ h6
      simp only [hc₀]
      nlinarith
    obtain ⟨hp, hc⟩ := hgo x R k n o (A q) hxg hR hn (hax q hq') hcut
    refine ⟨hp, ?_⟩
    haveI := hp
    have : (gam q).real (ell q)ᶜ = 1 - (gam q).real (ell q) := by
      rw [measureReal_compl (hellm q)]
      simp
    have h8 : (gam q).real (ell q)ᶜ ≤ Real.exp (-((R : ℝ) ^ 4)) := hc
    linarith
  have hexp : Real.exp (-((R : ℝ) ^ 4)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : 0 < (R : ℝ) ^ 4 := by positivity
    linarith
  have htpos : ∀ q ∈ G₀, gam q (ell q) ≠ 0 := by
    intro q hq'
    obtain ⟨hp, h3⟩ := hgamq q hq'
    haveI := hp
    intro h0
    have : (gam q).real (ell q) = 0 := by simp [Measure.real, h0]
    linarith
  have httop : ∀ q ∈ G₀, gam q (ell q) ≠ ⊤ := by
    intro q hq'
    haveI := (hgamq q hq').1
    exact measure_ne_top _ _
  have hm0 : ∀ q ∈ good, m q ≠ 0 := fun q hq' => hq'.2.ne'
  have hmI : ∀ q ∈ good, m q ≠ ⊤ := by
    intro q hq'
    obtain ⟨c, wt, hc, hwtm, hwt, hint⟩ := hchart q hq'
    have h3 := hint 1 measurable_one
    simp only [Pi.one_apply, one_mul] at h3
    have h4 : m q = _ := h3
    rw [h4]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    have hle : ∫⁻ ζ in ell q, ENNReal.ofReal (wt ζ) ∂(gam q) ≤
        ∫⁻ ζ in ell q, ENNReal.ofReal (Real.exp ε₁) ∂(gam q) := by
      refine setLIntegral_mono' (hellm q) fun ζ hζ => ENNReal.ofReal_le_ofReal ?_
      obtain ⟨a1, a2⟩ := hwt ζ hζ
      calc wt ζ = Real.exp (Real.log (wt ζ)) := (Real.exp_log a1).symm
        _ ≤ Real.exp ε₁ := Real.exp_le_exp.2 (le_trans (le_abs_self _) a2)
    refine ne_top_of_le_ne_top ?_ hle
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (httop q hq'.1)
  obtain ⟨κ, hκM, hκ⟩ := exists_markovKernel_of_density (innerHaar o R) hind hcf hgood hm0 hmI
    (0 : TorusBond n → imaginaryQuaternions)
  haveI := hκM
  classical
  let ηf : OuterData T k o R → Measure (TorusBond n → imaginaryQuaternions) := fun q =>
    if q ∈ good then (gam q (ell q))⁻¹ • (gam q).restrict (ell q) else Measure.dirac 0
  have hsec : ∀ E : Set ((TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions)), MeasurableSet E →
      Measurable fun q : good => gam q {ζ | (A q, ζ) ∈ E} := by
    intro E hE
    exact measurable_kernel_section_comp (fun E hE => hgb x R k n o hxk hR hn E hE)
      (hA.comp measurable_subtype_coe) (fun q : good => hax q.1 q.2.1) hE
  have hηB : ∀ B : Set (TorusBond n → imaginaryQuaternions), MeasurableSet B → Measurable fun q => ηf q B := by
    intro B hB
    refine measurable_of_restrict_of_restrict_compl hgood ?_ ?_
    · have e : good.domRestrict (fun q => ηf q B) = fun q : good =>
          (gam q {ζ | (A q, ζ) ∈ {p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) |
            p.2 ∈ sliceEllipsoid Tb.coupling Tb.side k o R p.1 c₀}})⁻¹ *
            gam q {ζ | (A q, ζ) ∈ {p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) |
              p.2 ∈ sliceEllipsoid Tb.coupling Tb.side k o R p.1 c₀} ∩ (Prod.snd ⁻¹' B)} := by
        funext q
        have hq' : (q : OuterData T k o R) ∈ good := q.2
        have s2 : {ζ | ((A q, ζ) : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions)) ∈
            {p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) |
              p.2 ∈ sliceEllipsoid Tb.coupling Tb.side k o R p.1 c₀} ∩ (Prod.snd ⁻¹' B)} = B ∩ ell q := by
          ext ζ
          exact and_comm
        rw [s2]
        show ηf q B = _
        simp only [ηf, if_pos hq', Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB]
        rfl
      rw [e]
      exact (hsec _ hELc.measurableSet).inv.mul (hsec _ (hELc.measurableSet.inter (measurable_snd hB)))
    · have e : goodᶜ.domRestrict (fun q => ηf q B) = fun _ => Measure.dirac 0 B := by
        funext q
        have hq' : (q : OuterData T k o R) ∉ good := q.2
        show ηf q B = _
        simp only [ηf, if_neg hq']
      rw [e]
      exact measurable_const
  let η : Kernel (OuterData T k o R) (TorusBond n → imaginaryQuaternions) :=
    ⟨ηf, Measure.measurable_of_measurable_coe _ hηB⟩
  have hηq : ∀ q ∈ good, η q = (gam q (ell q))⁻¹ • (gam q).restrict (ell q) := fun q hq' => by
    show ηf q = _
    simp only [ηf, if_pos hq']
  haveI hηM : IsMarkovKernel η := by
    refine ⟨fun q => ?_⟩
    by_cases hq' : q ∈ good
    · rw [hηq q hq']
      refine ⟨?_⟩
      simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact ENNReal.inv_mul_cancel (htpos q hq'.1) (httop q hq'.1)
    · show IsProbabilityMeasure (ηf q)
      simp only [ηf, if_neg hq']
      infer_instance
  have hres : ∀ q ∈ good, (gam q).restrict (ell q) = gam q (ell q) • η q := fun q hq' => by
    rw [hηq q hq', smul_smul, ENNReal.mul_inv_cancel (htpos q hq'.1) (httop q hq'.1), one_smul]
  set eP : ENNReal := ENNReal.ofReal (Real.exp ε₁) with heP
  set eM : ENNReal := ENNReal.ofReal (Real.exp (-ε₁)) with heM
  have hee : eM * eP = 1 := by
    rw [heM, heP, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  have hePt : eP ≠ ⊤ := ENNReal.ofReal_ne_top
  have heM0 : eM ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hdens : ∀ q ∈ good, ∃ f : (TorusBond n → imaginaryQuaternions) → ENNReal, Measurable f ∧
      κ q = (η q).withDensity f ∧
      η q (ell q)ᶜ = 0 ∧ ∀ ζ ∈ ell q, ENNReal.ofReal (Real.exp (-(2 * ε₁))) ≤ f ζ ∧
        f ζ ≤ ENNReal.ofReal (Real.exp (2 * ε₁)) := by
    intro q hq'
    obtain ⟨c, wt, hc, hwtm, hwt, hint⟩ := hchart q hq'
    have hwm : Measurable fun ζ => ENNReal.ofReal (wt ζ) := ENNReal.measurable_ofReal.comp hwtm
    set t := gam q (ell q) with ht
    have ht0 : t ≠ 0 := htpos q hq'.1
    have htt : t ≠ ⊤ := httop q hq'.1
    set I := ∫⁻ ζ in ell q, ENNReal.ofReal (wt ζ) ∂(gam q) with hI
    have hwle : ∀ ζ ∈ ell q, ENNReal.ofReal (wt ζ) ≤ eP ∧ eM ≤ ENNReal.ofReal (wt ζ) := by
      intro ζ hζ
      obtain ⟨a1, a2⟩ := hwt ζ hζ
      have a3 := abs_le.1 a2
      refine ⟨ENNReal.ofReal_le_ofReal ?_, ENNReal.ofReal_le_ofReal ?_⟩
      · calc wt ζ = Real.exp (Real.log (wt ζ)) := (Real.exp_log a1).symm
          _ ≤ Real.exp ε₁ := Real.exp_le_exp.2 a3.2
      · calc Real.exp (-ε₁) ≤ Real.exp (Real.log (wt ζ)) := Real.exp_le_exp.2 a3.1
          _ = wt ζ := Real.exp_log a1
    have hIu : I ≤ eP * t := by
      calc I ≤ ∫⁻ ζ in ell q, eP ∂(gam q) := setLIntegral_mono' (hellm q) fun ζ hζ => (hwle ζ hζ).1
        _ = eP * t := by rw [setLIntegral_const]
    have hIl : eM * t ≤ I := by
      calc eM * t = ∫⁻ ζ in ell q, eM ∂(gam q) := by rw [setLIntegral_const]
        _ ≤ I := setLIntegral_mono' (hellm q) fun ζ hζ => (hwle ζ hζ).2
    have hI0 : I ≠ 0 := by
      intro h0
      rw [h0] at hIl
      exact (mul_ne_zero heM0 ht0) (le_antisymm hIl zero_le)
    have hIt : I ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hePt htt) hIu
    have hcE : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
    have hmq : m q = ENNReal.ofReal c * I := by
      have h3 := hint 1 measurable_one
      simp only [Pi.one_apply, one_mul] at h3
      exact h3
    have hκΦ : ∀ Φ : (TorusBond n → imaginaryQuaternions) → ENNReal, Measurable Φ →
        ∫⁻ ζ, Φ ζ ∂(κ q) = I⁻¹ * ∫⁻ ζ in ell q, Φ ζ * ENNReal.ofReal (wt ζ) ∂(gam q) := by
      intro Φ hΦ
      have h3 := hκ q hq' Φ hΦ
      rw [hint Φ hΦ] at h3
      have h4 : (∫⁻ w, ind (q, w) ∂(innerHaar o R)) = ENNReal.ofReal c * I := hmq
      rw [h4, mul_assoc] at h3
      have h5 := (ENNReal.mul_right_inj hcE ENNReal.ofReal_ne_top).1 h3
      rw [h5, ← mul_assoc, ENNReal.inv_mul_cancel hI0 hIt, one_mul]
    refine ⟨fun ζ => t / I * ENNReal.ofReal (wt ζ), hwm.const_mul _, ?_, ?_, ?_⟩
    · have hfm : Measurable fun ζ => t / I * ENNReal.ofReal (wt ζ) := hwm.const_mul _
      ext B hB
      have hIB : Measurable (B.indicator (1 : (TorusBond n → imaginaryQuaternions) → ENNReal)) :=
        measurable_one.indicator hB
      rw [← lintegral_indicator_one hB, hκΦ _ hIB, ← lintegral_indicator_one (μ := (η q).withDensity _) hB,
        lintegral_withDensity_eq_lintegral_mul _ hfm hIB, hηq q hq', lintegral_smul_measure, smul_eq_mul]
      have e1 : ∀ ζ, (((fun ζ => t / I * ENNReal.ofReal (wt ζ)) * B.indicator 1 :
          (TorusBond n → imaginaryQuaternions) → ENNReal)) ζ =
          t / I * (B.indicator 1 ζ * ENNReal.ofReal (wt ζ)) := by
        intro ζ
        simp only [Pi.mul_apply]
        ring
      simp only [e1]
      have hm2 : Measurable fun ζ =>
          B.indicator (1 : (TorusBond n → imaginaryQuaternions) → ENNReal) ζ * ENNReal.ofReal (wt ζ) := hIB.mul hwm
      rw [lintegral_const_mul _ hm2, ← mul_assoc]
      congr 1
      rw [div_eq_mul_inv, ← mul_assoc, ENNReal.inv_mul_cancel ht0 htt, one_mul]
    · rw [hηq q hq', Measure.smul_apply, Measure.restrict_apply (hellm q).compl]
      simp
    · intro ζ hζ
      have ha1 : eM ≤ t / I := by
        refine (ENNReal.le_div_iff_mul_le (Or.inl hI0) (Or.inl hIt)).2 ?_
        calc eM * I ≤ eM * (eP * t) := by gcongr
          _ = t := by rw [← mul_assoc, hee, one_mul]
      have ha2 : t / I ≤ eP := by
        refine (ENNReal.div_le_iff hI0 hIt).2 ?_
        calc t = eP * (eM * t) := by rw [← mul_assoc, mul_comm eP eM, hee, one_mul]
          _ ≤ eP * I := by gcongr
      obtain ⟨w1, w2⟩ := hwle ζ hζ
      have q1 : ENNReal.ofReal (Real.exp (-(2 * ε₁))) = eM * eM := by
        rw [heM, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        ring
      have q2 : ENNReal.ofReal (Real.exp (2 * ε₁)) = eP * eP := by
        rw [heP, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        ring
      rw [q1, q2]
      exact ⟨mul_le_mul' ha1 w2, mul_le_mul' ha2 w1⟩
  obtain ⟨wj, hwm, hwb, hwκ⟩ := exists_measurable_density_between κ η (S := good) (E := ell)
    (lo := Real.exp (-(2 * ε₁))) (hi := Real.exp (2 * ε₁)) (Real.exp_pos _) (Real.exp_le_one_iff.2 (by linarith))
    (Real.one_le_exp (by linarith)) hdens
  have hlaw : ∀ q ∈ good,
      normalize (((gam q).restrict (ell q)).withDensity fun ζ => ENNReal.ofReal (wj q ζ)) = κ q := by
    intro q hq'
    rw [hres q hq', withDensity_smul_measure, hwκ q hq']
    unfold normalize
    have ht0 := htpos q hq'.1
    have htt := httop q hq'.1
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one, smul_smul]
    rw [ENNReal.inv_mul_cancel ht0 htt, one_smul]
  let orb : Set (OuterData T k o R × InnerField o R) := {p | p.1 ∈ good ∧ p.2 ∈ X p.1}
  have horbeq : orb = orb₀ ∩ (Prod.fst ⁻¹' good) := by
    ext p
    constructor
    · rintro ⟨h3, h4⟩
      exact ⟨(hmem₀ p.1 h3.1 p.2).2 h4, h3⟩
    · rintro ⟨h3, h4⟩
      exact ⟨h4, (hmem₀ p.1 h4.1 p.2).1 h3⟩
  have hOrb : MeasurableSet orb := by
    rw [horbeq]
    exact hOrb₀.inter (measurable_fst hgood)
  let c : BoxChart T k o R := ⟨good, orb, g, A, fun q w => cf (q, w), wj, M⟩
  let e₁ : MarkedSample (Tb.stepParameters y) k n → OuterData T k o R := fun u =>
    outerData T k o R (stageState T k n u)
  let e₂ : MarkedSample (Tb.stepParameters y) k n → InnerField o R := fun u =>
    restrictInner o R (stageState T k n u).1
  have he₁ : Measurable e₁ :=
    ((measurable_restrictOuter o R).comp (measurable_fst.comp hstate)).prodMk (measurable_snd.comp hstate)
  have he₂ : Measurable e₂ := (measurable_restrictInner o R).comp (measurable_fst.comp hstate)
  have hkey : ∀ H₁ H₂ : OuterData T k o R × InnerField o R → ENNReal, Measurable H₁ → Measurable H₂ →
      (∀ q, ∫⁻ w, H₁ (q, w) * hullStateDensity T k o R (q, w) ∂(innerHaar o R) =
        ∫⁻ w, H₂ (q, w) * hullStateDensity T k o R (q, w) ∂(innerHaar o R)) →
      ∫⁻ u, H₁ (e₁ u, e₂ u) ∂(markedSampleLaw T β k n) = ∫⁻ u, H₂ (e₁ u, e₂ u) ∂(markedSampleLaw T β k n) := by
    intro H₁ H₂ h₁ h₂ h
    refine (ENNReal.mul_right_inj hZ0 hZt).1 ?_
    refine (key H₁ h₁).trans (Eq.trans ?_ (key H₂ h₂).symm)
    congr 1
    funext q
    exact h q
  have hev : MeasurableSet ((fun u => (e₁ u, e₂ u)) ⁻¹' orb) := (he₁.prodMk he₂) hOrb
  have hstar : ∀ B : Set (OuterData T k o R × (TorusBond n → imaginaryQuaternions)), MeasurableSet B →
      ∫⁻ u in (fun u => (e₁ u, e₂ u)) ⁻¹' orb, B.indicator 1 (e₁ u, cf (e₁ u, e₂ u)) ∂(markedSampleLaw T β k n) =
        ∫⁻ u in (fun u => (e₁ u, e₂ u)) ⁻¹' orb, κ (e₁ u) (Prod.mk (e₁ u) ⁻¹' B) ∂(markedSampleLaw T β k n) := by
    intro B hB
    let f₁ : OuterData T k o R × InnerField o R → ENNReal := fun p => B.indicator 1 (p.1, cf p)
    let f₂ : OuterData T k o R × InnerField o R → ENNReal := fun p => κ p.1 (Prod.mk p.1 ⁻¹' B)
    have hf₁ : Measurable f₁ := (measurable_one.indicator hB).comp (measurable_fst.prodMk hcf)
    have hf₂ : Measurable f₂ := (Kernel.measurable_kernel_prodMk_left hB).comp measurable_fst
    have conv : ∀ f : OuterData T k o R × InnerField o R → ENNReal,
        ∫⁻ u in (fun u => (e₁ u, e₂ u)) ⁻¹' orb, f (e₁ u, e₂ u) ∂(markedSampleLaw T β k n) =
          ∫⁻ u, orb.indicator f (e₁ u, e₂ u) ∂(markedSampleLaw T β k n) := by
      intro f
      rw [← lintegral_indicator hev]
      refine lintegral_congr fun u => ?_
      by_cases h : (e₁ u, e₂ u) ∈ orb
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show u ∈ (fun u => (e₁ u, e₂ u)) ⁻¹' orb from h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show u ∉ (fun u => (e₁ u, e₂ u)) ⁻¹' orb from h)]
    have c₁ := conv f₁
    have c₂ := conv f₂
    refine c₁.trans (Eq.trans ?_ c₂.symm)
    refine hkey _ _ (hf₁.indicator hOrb) (hf₂.indicator hOrb) fun q => ?_
    by_cases hq' : q ∈ good
    · let Φ : (TorusBond n → imaginaryQuaternions) → ENNReal := (Prod.mk q ⁻¹' B).indicator 1
      have hΦ : Measurable Φ := measurable_one.indicator (measurable_prodMk_left hB)
      have l1 : ∀ w, orb.indicator f₁ (q, w) * hullStateDensity T k o R (q, w) = Φ (cf (q, w)) * ind (q, w) := by
        intro w
        by_cases hw : w ∈ X q
        · have h3 : (q, w) ∈ orb := ⟨hq', hw⟩
          have h4 : (q, w) ∈ orb₀ := (hmem₀ q hq'.1 w).2 hw
          rw [Set.indicator_of_mem h3, show ind (q, w) = _ from Set.indicator_of_mem h4 _]
          rfl
        · have h3 : (q, w) ∉ orb := fun h => hw h.2
          have h4 : (q, w) ∉ orb₀ := fun h => hw ((hmem₀ q hq'.1 w).1 h)
          rw [Set.indicator_of_notMem h3, show ind (q, w) = _ from Set.indicator_of_notMem h4 _]
          simp
      have l2 : ∀ w, orb.indicator f₂ (q, w) * hullStateDensity T k o R (q, w) =
          κ q (Prod.mk q ⁻¹' B) * ind (q, w) := by
        intro w
        by_cases hw : w ∈ X q
        · have h3 : (q, w) ∈ orb := ⟨hq', hw⟩
          have h4 : (q, w) ∈ orb₀ := (hmem₀ q hq'.1 w).2 hw
          rw [Set.indicator_of_mem h3, show ind (q, w) = _ from Set.indicator_of_mem h4 _]
        · have h3 : (q, w) ∉ orb := fun h => hw h.2
          have h4 : (q, w) ∉ orb₀ := fun h => hw ((hmem₀ q hq'.1 w).1 h)
          rw [Set.indicator_of_notMem h3, show ind (q, w) = _ from Set.indicator_of_notMem h4 _]
          simp
      simp only [l1, l2]
      have hind' : Measurable fun w => ind (q, w) := hind.comp measurable_prodMk_left
      have e5 : ∫⁻ ζ, Φ ζ ∂(κ q) = κ q (Prod.mk q ⁻¹' B) := lintegral_indicator_one (measurable_prodMk_left hB)
      rw [hκ q hq' Φ hΦ, lintegral_const_mul _ hind', e5, mul_comm]
    · have l1 : ∀ (f : OuterData T k o R × InnerField o R → ENNReal) (w : InnerField o R), orb.indicator f (q, w) = 0 :=
        fun f w => Set.indicator_of_notMem (fun h => hq' h.1) _
      simp only [l1, zero_mul]
  have hmono : ∀ (e : ℕ) (d : ℝ), 0 ≤ d →
      K₁ * (R : ℝ) ^ e * d ≤ max (max K₁ 7) (2 * max K₂ 0) * (R : ℝ) ^ e * d := by
    intro e d hd
    have : K₁ ≤ max (max K₁ 7) (2 * max K₂ 0) := le_trans (le_max_left _ _) (le_max_left _ _)
    have h3 : 0 ≤ (R : ℝ) ^ e := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this h3) hd
  refine ⟨c, rfl, rfl, rfl, Set.inter_subset_left, fun p => Iff.rfl, ?_, ?_, ?_, hellm, hcf, ?_, ?_, ?_⟩
  · exact
      { measurableSet_goodOuter := hgood
        measurableSet_orbitSet := hOrb
        fst_mem_goodOuter := fun p hp => hp.1
        measurable_axialGauge := hg.comp measurable_subtype_coe
        measurable_background := hA.comp measurable_subtype_coe
        measurable_coord := hcf.comp measurable_subtype_coe
        measurable_weight := hwm.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
        measurable_meanCurl := hM.comp measurable_subtype_coe
        gauge_mem := fun p hp γ hγ => ⟨hp.1, restrictInner_gaugeTransform_mem_gaugeOrbitsOverEllipsoid hp.2 hγ⟩ }
  · refine ⟨fun p hp => ?_, fun p hp γ ζ hγ hζ hc => ?_, fun p hp => ?_⟩
    · exact hcsp (pt p) ⟨hax p.1 hp.1.1, hp.2⟩
    · obtain ⟨γ₀, hγ₀, hζ₀, hc₀'⟩ := hcsp (pt p) ⟨hax p.1 hp.1.1, hp.2⟩
      have hin : IsSupportedGauge o R ((g p.1 * γ) * (g p.1 * γ₀)⁻¹) := by
        intro z hz
        have e1 : γ z = 1 := hγ z hz
        have e2 : γ₀ z = 1 := hγ₀ z hz
        show (g p.1 * γ * (g p.1 * γ₀)⁻¹) z = 1
        simp [Pi.mul_apply, Pi.inv_apply, e1, e2]
      have hgg : gaugeTransform ((g p.1 * γ) * (g p.1 * γ₀)⁻¹) (gaugeTransform (g p.1 * γ₀) (glueField p.1.1 p.2)) =
          gaugeTransform (g p.1 * γ) (glueField p.1.1 p.2) := by
        rw [gaugeTransform_gaugeTransform, inv_mul_cancel_right]
      exact (ho x R k n o (A p.1) hxo hR hn (hax p.1 hp.1.1) (gaugeTransform (g p.1 * γ₀) (glueField p.1.1 p.2))
        ((g p.1 * γ) * (g p.1 * γ₀)⁻¹) (cf p) ζ hin hζ₀ hζ (by exact hc₀') (by rw [hgg]; exact hc)).1
    · obtain ⟨γ₀, hγ₀, hζ₀, hc₀'⟩ := hcsp (pt p) ⟨hax p.1 hp.1.1, hp.2⟩
      have hax' := hax p.1 hp.1.1
      obtain ⟨hb1, hb2, hb3, hb4⟩ := (hb x R k n o (A p.1) hxb hR hn hax').2 _ hζ₀
      obtain ⟨v, β', hv1, hv2, hv3, hv4⟩ := hb4 _ hc₀'
      have hR3 : (R : ℝ) ≤ (R : ℝ) ^ 3 := by
        calc (R : ℝ) = (R : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (R : ℝ) ^ 3 := pow_le_pow_right₀ hRpos (by norm_num)
      refine ⟨γ₀, v, β', hγ₀, fun b hbS => ?_, ?_, fun q' hq'' => ?_, ?_⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hv1 b hbS
        refine ⟨a1, a2, a3, le_trans a4 (hmono 3 δ hδ0), ?_, le_trans (hb2 b) (hmono 3 δ hδ0)⟩
        have h5 : ‖A p.1 b‖ ≤ 7 * (R : ℝ) * δ := hax'.norm_le b hbS
        have h6 : (7 : ℝ) ≤ max (max K₁ 7) (2 * max K₂ 0) := le_trans (le_max_right _ _) (le_max_left _ _)
        calc ‖A p.1 b‖ ≤ 7 * (R : ℝ) * δ := h5
          _ ≤ max (max K₁ 7) (2 * max K₂ 0) * (R : ℝ) ^ 3 * δ := by
            refine mul_le_mul_of_nonneg_right ?_ hδ0
            exact mul_le_mul h6 hR3 (by positivity) (le_trans (by norm_num) h6)
      · have := hmono 6 (δ ^ 2) (by positivity)
        exact le_trans hv2 this
      · exact le_trans (hcold p.1 hp.1.1 p.2 hp.2 q' hq'') (hmono 2 δ hδ0)
      · have := hmono 4 (δ ^ 2) (by positivity)
        exact le_trans hb3 this
  · refine ⟨fun F hF hFb => ?_, fun q hq' ζ hζ => ?_, fun q hq' => hgamq q hq'.1⟩
    · obtain ⟨Mb, hMb⟩ := hFb
      refine (setIntegral_comp_eq_setIntegral_kernel he₁ he₂ hOrb hcf κ hstar hF hMb).trans ?_
      refine setIntegral_congr_fun hev fun u hu => ?_
      have h3 : c.coordLaw x c₀ (e₁ u) = κ (e₁ u) := hlaw _ hu.1
      show ∫ ζ, F (e₁ u, ζ) ∂(κ (e₁ u)) = ∫ ζ, F (e₁ u, ζ) ∂(c.coordLaw x c₀ (e₁ u))
      rw [h3]
    · obtain ⟨a1, a2⟩ := hwb q ζ
      have hw0 : 0 < wj q ζ := lt_of_lt_of_le (Real.exp_pos _) a1
      refine ⟨hw0, ?_⟩
      have b1 : -(2 * ε₁) ≤ Real.log (wj q ζ) := by
        rw [Real.le_log_iff_exp_le hw0]
        exact a1
      have b2 : Real.log (wj q ζ) ≤ 2 * ε₁ := by
        rw [Real.log_le_iff_le_exp hw0]
        exact a2
      have b3 : |Real.log (wj q ζ)| ≤ 2 * ε₁ := abs_le.2 ⟨b1, b2⟩
      refine le_trans b3 ?_
      have b4 : 2 * max K₂ 0 ≤ max (max K₁ 7) (2 * max K₂ 0) := le_max_right _ _
      calc 2 * ε₁ = 2 * max K₂ 0 * ((R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) := by
            simp only [hε₁]
            ring
        _ ≤ max (max K₁ 7) (2 * max K₂ 0) * ((R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) :=
            mul_le_mul_of_nonneg_right b4 ht9
        _ = _ := by ring
  · intro q hq'
    have h3 : c.coordLaw x c₀ q = κ q := hlaw q hq'
    rw [h3]
    infer_instance
  · intro E hE
    have h3 : (fun q : c.goodOuter => c.coordLaw x c₀ q (Prod.mk q.1 ⁻¹' E)) =
        fun q : c.goodOuter => κ q (Prod.mk q.1 ⁻¹' E) := by
      funext q
      have h4 : c.coordLaw x c₀ q = κ q := hlaw q q.2
      rw [h4]
    rw [h3]
    exact (Kernel.measurable_kernel_prodMk_left hE).comp measurable_subtype_coe
  · let bad : Set (OuterData T k o R × InnerField o R) := orb₀ ∩ (Prod.fst ⁻¹' goodᶜ)
    have hbad : MeasurableSet bad := hOrb₀.inter (measurable_fst hgood.compl)
    have hz := hkey (bad.indicator (1 : OuterData T k o R × InnerField o R → ENNReal)) 0
      (measurable_one.indicator hbad) measurable_const (fun q => ?_)
    · have hset : {u | outerData T k o R (stageState T k n u) ∈ G₀ \ c.goodOuter ∧
          restrictInner o R (stageState T k n u).1 ∈
            gaugeOrbitsOverEllipsoid Tb.coupling Tb.side k o R (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2)
              (g (outerData T k o R (stageState T k n u))) (A (outerData T k o R (stageState T k n u)))
              (outerData T k o R (stageState T k n u)).1} = (fun u => (e₁ u, e₂ u)) ⁻¹' bad := by
        ext u
        constructor
        · rintro ⟨⟨h3, h4⟩, h5⟩
          exact ⟨(hmem₀ _ h3 _).2 h5, h4⟩
        · rintro ⟨h3, h4⟩
          exact ⟨⟨h3.1, h4⟩, (hmem₀ _ h3.1 _).1 h3⟩
      rw [hset, ← lintegral_indicator_one ((he₁.prodMk he₂) hbad)]
      have e5 : ∀ u, ((fun u => (e₁ u, e₂ u)) ⁻¹' bad).indicator
          (1 : MarkedSample (Tb.stepParameters y) k n → ENNReal) u =
          bad.indicator (1 : OuterData T k o R × InnerField o R → ENNReal) (e₁ u, e₂ u) := by
        intro u
        by_cases h : (e₁ u, e₂ u) ∈ bad
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show u ∈ (fun u => (e₁ u, e₂ u)) ⁻¹' bad from h)]
          rfl
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show u ∉ (fun u => (e₁ u, e₂ u)) ⁻¹' bad from h)]
      simp only [e5]
      rw [hz]
      simp
    · have h0 : ∫⁻ w, (0 : OuterData T k o R × InnerField o R → ENNReal) (q, w) *
          hullStateDensity T k o R (q, w) ∂(innerHaar o R) = 0 := by
        simp
      rw [h0]
      by_cases hq' : q ∈ G₀ ∧ q ∉ good
      · have hmz : m q = 0 := by
          by_contra hne
          exact hq'.2 ⟨hq'.1, pos_iff_ne_zero.2 hne⟩
        refine le_antisymm (le_trans (lintegral_mono fun w => ?_) hmz.le) zero_le
        by_cases hw : (q, w) ∈ bad
        · rw [Set.indicator_of_mem hw, show ind (q, w) = _ from Set.indicator_of_mem hw.1 _]
          simp
        · rw [Set.indicator_of_notMem hw]
          simp
      · have l1 : ∀ w, bad.indicator (1 : OuterData T k o R × InnerField o R → ENNReal) (q, w) = 0 := fun w =>
          Set.indicator_of_notMem (fun h => hq' ⟨h.1.1, h.2⟩) _
        simp only [l1, zero_mul, lintegral_zero]
end YangMills.Construction.BoxGaussian
end
