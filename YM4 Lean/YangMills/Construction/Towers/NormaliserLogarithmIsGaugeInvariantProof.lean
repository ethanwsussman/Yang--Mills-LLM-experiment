import YangMills.Construction.Towers.CovariantDifferenceRelationsOfAStepOfASideProof
import YangMills.Construction.Towers.CurvesReadInTheChartAtOneProof
import YangMills.Construction.Towers.GaugeCovarianceOfTheLiftProof
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChart
import YangMills.Construction.Towers.GaussianNumberUnderMapsThatKeepThePairing
import YangMills.Construction.Towers.MultiplierOfTheNextLevelProof
import YangMills.Construction.Towers.NormaliserLogarithmIsGaugeInvariant
import YangMills.Construction.Towers.TheFixedFamilyOfTheCriticalBranch
import YangMills.Construction.Towers.TheFormOnAFibreOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices
variable {L n k i j : ℕ}
private def FibreFacts (L n k i : ℕ) (W : Edge L n k (i + 1) → ComplexMatrix2) : Prop :=
  (fieldCurveData L n k i).IsCriticalOn (chosenLevelFibre L n k i W)
      (chosenGaugeFixedEnergy L n k i) (chosenProlong L n k i W) ∧
    Function.Surjective (constraintDifferential L n k i W) ∧
    (fieldCurveData L n k i).IsHessianFormAt (S := LinearMap.ker (constraintDifferential L n k i W))
      (fun B => B.1.1) (chosenLevelFibre L n k i W) (chosenGaugeFixedEnergy L n k i)
      (chosenProlong L n k i W) (fibreHessianForm L n k i W) ∧
    (∀ B : LinearMap.ker (constraintDifferential L n k i W), ∃ (I : Set ℝ) (γ : ℝ → Edge L n k i → ComplexMatrix2),
      (fieldCurveData L n k i).IsTwiceDiffCurve I γ ∧
        Set.MapsTo γ I (chosenLevelFibre L n k i W) ∧ γ 0 = chosenProlong L n k i W ∧
        (fieldCurveData L n k i).tangent γ = B.1.1) ∧
    (fibreHessianForm L n k i W).PosDef
private theorem extendOddly_congr {f g : Edge L n k j → ComplexMatrix2}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b = g b) : extendOddly f = extendOddly g := by apply _root_.YangMills.Construction.Tower.CovDiffStep.extendOddly_congr <;> assumption
private theorem extendOddly_of_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
private theorem curveTangent_congr {γ γ' : ℝ → Edge L n k j → ComplexMatrix2} (h : γ =ᶠ[𝓝 0] γ') :
    curveTangent γ = curveTangent γ' := by apply _root_.YangMills.SharedProofs.p19450 <;> assumption
private theorem isUnit_det_of_mem {X : ComplexMatrix2} (hX : X ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit X.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem inv_mul_of_mem {X : ComplexMatrix2} (hX : X ∈ PeriodicLattice.compactGaugeGroup) :
    X⁻¹ * X = 1 := by apply _root_.YangMills.SharedProofs.p14555 <;> assumption
private theorem norm_conj_sub_one_le {a c X : ComplexMatrix2} (ha : a ∈ PeriodicLattice.compactGaugeGroup)
    (hc : c ∈ PeriodicLattice.compactGaugeGroup) :
    ‖a * X * c⁻¹ - 1‖ ≤ ‖X - 1‖ + ‖a - 1‖ + ‖c - 1‖ := by apply _root_.YangMills.SharedProofs.p32758 <;> assumption
private theorem norm_conj_sub_one {a X : ComplexMatrix2} (ha : a ∈ PeriodicLattice.compactGaugeGroup) :
    ‖a * X * a⁻¹ - 1‖ = ‖X - 1‖ := by apply _root_.YangMills.Construction.PeriodicLattice.HolonomyUnderReordering.norm_conj_sub_one_of_mem <;> assumption
private theorem gaugeTransform_mem {u : Vertex L n k j → ComplexMatrix2} {U : Edge L n k j → ComplexMatrix2}
    (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup) (hU : U ∈ fieldSpace L n k j) :
    PeriodicLattice.gaugeTransform u U ∈ fieldSpace L n k j := by apply _root_.YangMills.SharedProofs.p8548 <;> assumption
private theorem isDiffAtZeroPath_gaugeTransform {u : Vertex L n k j → ComplexMatrix2}
    {δ : ℝ → Edge L n k j → ComplexMatrix2}
    (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup) (hδ : IsDiffAtZeroPath δ) :
    IsDiffAtZeroPath (fun t => PeriodicLattice.gaugeTransform u (δ t)) :=
  ⟨hδ.1.mono fun _ ht => gaugeTransform_mem hu ht, fun b hb =>
    ((hδ.2 b hb).const_mul (u b.source)).mul_const ((u b.target)⁻¹)⟩
private theorem curveTangent_gaugeTransform {u : Vertex L n k j → ComplexMatrix2}
    {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup)
    (hγ : ∀ b : Edge L n k j, b.IsPositivelyOriented → DifferentiableAt ℝ (fun t => γ t b) 0) :
    curveTangent (fun t => PeriodicLattice.gaugeTransform u (γ t)) =
      adjointForm u (curveTangent γ) := by
  unfold adjointForm
  conv_lhs => unfold curveTangent
  refine extendOddly_congr fun b hb => ?_
  unfold curveTangent
  rw [extendOddly_of_pos _ hb]
  have hd : HasDerivAt (fun t => PeriodicLattice.gaugeTransform u (γ t) b)
      (u b.source * deriv (fun t => γ t b) 0 * (u b.target)⁻¹) 0 :=
    ((hγ b hb).hasDerivAt.const_mul (u b.source)).mul_const ((u b.target)⁻¹)
  rw [hd.deriv]
  change Complex.I⁻¹ • (u b.source * deriv (fun t => γ t b) 0 * (u b.target)⁻¹ *
      (u b.source * γ 0 b * (u b.target)⁻¹)⁻¹) =
    u b.source * (Complex.I⁻¹ • (deriv (fun t => γ t b) 0 * (γ 0 b)⁻¹)) * (u b.source)⁻¹
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hu _)),
    Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc u b.source * deriv (fun t => γ t b) 0 * (u b.target)⁻¹ *
        (u b.target * ((γ 0 b)⁻¹ * (u b.source)⁻¹))
      = u b.source * deriv (fun t => γ t b) 0 * ((u b.target)⁻¹ * u b.target) *
          ((γ 0 b)⁻¹ * (u b.source)⁻¹) := by noncomm_ring
    _ = u b.source * (deriv (fun t => γ t b) 0 * (γ 0 b)⁻¹) * (u b.source)⁻¹ := by
      rw [inv_mul_of_mem (hu _), mul_one]
      noncomm_ring
private theorem isOpen_near_one {ι : Type*} [Finite ι] (δ : ℝ) :
    IsOpen {V : ι → ComplexMatrix2 | ∀ b, ‖V b - 1‖ < δ} := by apply _root_.YangMills.SharedProofs.p24342 <;> assumption
private theorem eventually_near_one {ι : Type*} [Finite ι] {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ V in 𝓝 (fun _ : ι => (1 : ComplexMatrix2)), ∀ b, ‖V b - 1‖ < δ :=
  (isOpen_near_one δ).mem_nhds fun b => by simpa using hδ
private theorem exists_radius_of_near {ι : Type*} [Finite ι] {D : Set (ι → ComplexMatrix2)}
    {P : (ι → ComplexMatrix2) → Prop}
    (h : EventuallyNearIdentity D P) : ∃ δ : ℝ, 0 < δ ∧ ∀ V ∈ D, (∀ b, ‖V b - 1‖ < δ) → P V := by apply _root_.YangMills.SharedProofs.p388 <;> assumption
private theorem gaussianNormaliser_gaugeTransform
    (hG : ConstrainedGaussianIsometryInvariance)
    (hGF : GaugeEquivarianceFormsAllSides)
    (hP : diffAtZeroPathsStatement)
    (hA : AnalyticMapsAlongCurves)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i + 1 ≤ k)
    [Finite (Edge L n k i)]
    (hN : (chosenCriticalBranch L n k).IsFibreNhd i (chosenFibreNhd L n k i))
    {v : Vertex L n k (i + 1) → ComplexMatrix2} {w : Vertex L n k i → ComplexMatrix2}
    (hv : v ∈ gaugeGroupAt L n k (i + 1)) (hw : w ∈ gaugeGroupAt L n k i)
    {W : Edge L n k (i + 1) → ComplexMatrix2}
    (hW : FibreFacts L n k i W) (hW' : FibreFacts L n k i (PeriodicLattice.gaugeTransform v W))
    (hlift : chosenProlong L n k i (PeriodicLattice.gaugeTransform v W) =
      PeriodicLattice.gaugeTransform w (chosenProlong L n k i W))
    {δ : ℝ} (hδ : ∀ b, ‖chosenProlong L n k i W b - 1‖ < δ)
    (hO : ∀ U ∈ fieldSpace L n k i, (∀ b, ‖U b - 1‖ < δ) →
      smoothingStep L n k i (PeriodicLattice.gaugeTransform w U) =
          PeriodicLattice.gaugeTransform v (smoothingStep L n k i U) ∧
        chosenGaugeFixedEnergy L n k i (PeriodicLattice.gaugeTransform w U) =
          chosenGaugeFixedEnergy L n k i U) :
    gaussianNormaliser L n k i (PeriodicLattice.gaugeTransform v W) = gaussianNormaliser L n k i W := by
  obtain ⟨hCr, -, hHess, hCurves, -⟩ := hW
  obtain ⟨hCr', -, hHess', -, -⟩ := hW'
  have hU : chosenProlong L n k i W ∈ chosenFibreNhd L n k i := hCr.1.1
  have hU' : PeriodicLattice.gaugeTransform w (chosenProlong L n k i W) ∈ chosenFibreNhd L n k i := by
    rw [← hlift]
    exact hCr'.1.1
  have hVc : chosenProlong L n k i W ∈ fieldSpace L n k i := hN.isOpenNhd.1.1 hU
  have hvg : ∀ y, v y ∈ PeriodicLattice.compactGaugeGroup := hv
  have hwg : ∀ x, w x ∈ PeriodicLattice.compactGaugeGroup := hw
  have hsub : ∀ {X : ComplexMatrix2}, X ∈ PeriodicLattice.compactGaugeGroup →
      X ∈ PeriodicLattice.complexGaugeGroup :=
    fun hX => (Matrix.mem_specialUnitaryGroup_iff.1 hX).2
  obtain ⟨eO, heO, hpO⟩ :=
    ((((hGF L k i hL (by omega)).1 n hn) w fun x => hsub (hwg x)).2.2.2 hw).1
  obtain ⟨eO', heO', hpO'⟩ :=
    ((((hGF L k (i + 1) hL hi).1 n hn) v fun x => hsub (hvg x)).2.2.2 hv).1
  have hPi := hP L n k i hL hn (by omega)
  obtain ⟨-, hPt⟩ := (hA L n k i (i + 1) hL hn (by omega) hi).1 _ _ hN.analytic_smoothing
  have hnear : ∀ d : ℝ → Edge L n k i → ComplexMatrix2, IsDiffAtZeroPath d →
      d 0 = chosenProlong L n k i W →
      ∀ᶠ t in 𝓝 (0 : ℝ), d t ∈ fieldSpace L n k i ∧ ∀ b, ‖d t b - 1‖ < δ := by
    intro d hd h0
    have hten := (hPi.1 d hd).2
    rw [h0] at hten
    have hs : ∀ᶠ U in 𝓝[fieldSpace L n k i] chosenProlong L n k i W, ∀ b, ‖U b - 1‖ < δ :=
      nhdsWithin_le_nhds ((isOpen_near_one δ).mem_nhds hδ)
    exact hd.1.and (hten.eventually hs)
  have hcomm : ∀ B : edgeFormSpace L n k i,
      constraintDifferential L n k i (PeriodicLattice.gaugeTransform v W) (eO B) =
        eO' (constraintDifferential L n k i W B) := by
    intro B
    obtain ⟨hlin, halong⟩ := hPt _ hU
    obtain ⟨hlin', halong'⟩ := hPt _ hU'
    obtain ⟨hd, hd0, hdt⟩ := hPi.2.2 _ hVc B.1 B.2
    have hd' := isDiffAtZeroPath_gaugeTransform hwg hd
    obtain ⟨hm, hmt⟩ := halong _ hd hd0
    obtain ⟨-, hmt'⟩ := halong' _ hd' (by simp only [hd0])
    have ht' := curveTangent_gaugeTransform hwg hd.2
    rw [hdt, ← heO] at ht'
    have heq : (fun t : ℝ => smoothingStep L n k i (PeriodicLattice.gaugeTransform w
          (PeriodicLattice.expTwist ((t : ℂ) • B.1) (chosenProlong L n k i W)))) =ᶠ[𝓝 0]
        fun t : ℝ => PeriodicLattice.gaugeTransform v (smoothingStep L n k i
          (PeriodicLattice.expTwist ((t : ℂ) • B.1) (chosenProlong L n k i W))) :=
      (hnear _ hd hd0).mono fun t ht => (hO _ ht.1 ht.2).1
    have e₁ : ((constraintDifferential L n k i (PeriodicLattice.gaugeTransform v W) (eO B) :
        edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) =
        leftDifferential (smoothingStep L n k i)
          (PeriodicLattice.gaugeTransform w (chosenProlong L n k i W))
          (eO B : Edge L n k i → ComplexMatrix2) := by
      unfold constraintDifferential
      rw [hlift]
      exact hlin' _
    have e₂ : ((constraintDifferential L n k i W B : edgeFormSpace L n k (i + 1)) :
        Edge L n k (i + 1) → ComplexMatrix2) =
        leftDifferential (smoothingStep L n k i) (chosenProlong L n k i W) B.1 := hlin B
    apply Subtype.ext
    rw [e₁, heO', e₂, ← ht', ← hmt', curveTangent_congr heq,
      curveTangent_gaugeTransform hvg hm.2, hmt, hdt]
  have hTT : ∀ (B : LinearMap.ker (constraintDifferential L n k i W))
      (B' : LinearMap.ker (constraintDifferential L n k i (PeriodicLattice.gaugeTransform v W))),
      B'.1 = eO B.1 →
        fibreHessianForm L n k i (PeriodicLattice.gaugeTransform v W) B' =
          fibreHessianForm L n k i W B := by
    intro B B' hBB
    obtain ⟨I, γ, hγ, hγN, hγ0, hγt⟩ := hCurves B
    have hγd : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ := hγ.1
    have hIo : I ∈ 𝓝 (0 : ℝ) := hγd.1.1.mem_nhds hγd.1.2.2
    have hpath : IsDiffAtZeroPath γ :=
      ⟨Filter.mem_of_superset hIo fun t ht => hγd.2.1 ht,
        fun b hb => (hγd.2.2 b hb 0 hγd.1.2.2).differentiableAt hIo⟩
    have hpath' := isDiffAtZeroPath_gaugeTransform hwg hpath
    have hin' : ∀ᶠ t in 𝓝 (0 : ℝ),
        PeriodicLattice.gaugeTransform w (γ t) ∈ chosenFibreNhd L n k i := by
      have hten := (hPi.1 _ hpath').2
      have e0 : PeriodicLattice.gaugeTransform w (γ 0) =
          PeriodicLattice.gaugeTransform w (chosenProlong L n k i W) := by rw [hγ0]
      simp only [e0] at hten
      exact hten.eventually (hPi.2.1 _ hN.isOpenNhd.1 _ hU')
    have hE : {t : ℝ | t ∈ I ∧ (γ t ∈ fieldSpace L n k i ∧ ∀ b, ‖γ t b - 1‖ < δ) ∧
        PeriodicLattice.gaugeTransform w (γ t) ∈ chosenFibreNhd L n k i} ∈ 𝓝 (0 : ℝ) :=
      (Filter.Eventually.and hIo ((hnear γ hpath hγ0).and hin'))
    obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hE
    have hJ : IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) r) := by
      refine ⟨Metric.isOpen_ball, ?_, Metric.mem_ball_self hr⟩
      rw [Real.ball_eq_Ioo]
      exact ordConnected_Ioo
    have hJI : Metric.ball (0 : ℝ) r ⊆ I := fun t ht => (hrs ht).1
    have hγ'd : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup (Metric.ball (0 : ℝ) r)
        (fun t => PeriodicLattice.gaugeTransform w (γ t)) :=
      ⟨hJ, fun t ht => gaugeTransform_mem hwg (hγd.2.1 (hJI ht)), fun b hb =>
        (((hγd.2.2 b hb).mono hJI).const_mul (w b.source)).mul_const ((w b.target)⁻¹)⟩
    have htw : ∀ b : Edge L n k i, b.IsPositivelyOriented → DifferentiableOn ℝ
        (deriv fun t => PeriodicLattice.gaugeTransform w (γ t) b) (Metric.ball (0 : ℝ) r) := by
      intro b hb
      have e : ∀ t ∈ Metric.ball (0 : ℝ) r,
          deriv (fun s => PeriodicLattice.gaugeTransform w (γ s) b) t =
            w b.source * deriv (fun s => γ s b) t * (w b.target)⁻¹ := by
        intro t ht
        have hdiff : DifferentiableAt ℝ (fun s => γ s b) t :=
          (hγd.2.2 b hb t (hJI ht)).differentiableAt (hγd.1.1.mem_nhds (hJI ht))
        exact ((hdiff.hasDerivAt.const_mul (w b.source)).mul_const ((w b.target)⁻¹)).deriv
      exact ((((hγ.2 b hb).mono hJI).const_mul (w b.source)).mul_const ((w b.target)⁻¹)).congr e
    have hmaps : MapsTo (fun t => PeriodicLattice.gaugeTransform w (γ t)) (Metric.ball (0 : ℝ) r)
        (chosenLevelFibre L n k i (PeriodicLattice.gaugeTransform v W)) := by
      intro t ht
      refine And.intro (hrs ht).2.2 ?_
      rw [(hO _ (hrs ht).2.1.1 (hrs ht).2.1.2).1,
        show smoothingStep L n k i (γ t) = W from (hγN (hJI ht)).2]
    have h0 : PeriodicLattice.gaugeTransform w (γ 0) =
        chosenProlong L n k i (PeriodicLattice.gaugeTransform v W) := by rw [hlift, hγ0]
    have htan : (fieldCurveData L n k i).tangent (fun t => PeriodicLattice.gaugeTransform w (γ t)) =
        B'.1.1 := by
      have hγt' : curveTangent γ = B.1.1 := hγt
      change curveTangent (fun t => PeriodicLattice.gaugeTransform w (γ t)) = _
      rw [curveTangent_gaugeTransform hwg hpath.2, hγt', hBB, heO]
    have e₁ := hHess' _ _ B' ⟨hγ'd, htw⟩ hmaps h0 htan
    have e₂ := hHess I γ B hγ hγN hγ0 hγt
    have heq : (fun t => chosenGaugeFixedEnergy L n k i (PeriodicLattice.gaugeTransform w (γ t))) =ᶠ[𝓝 0]
        fun t => chosenGaugeFixedEnergy L n k i (γ t) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
      exact (hO _ (hrs ht).2.1.1 (hrs ht).2.1.2).2
    exact e₁.trans (heq.deriv.deriv_eq.trans e₂.symm)
  exact hG L n k i (i + 1) L n k i (i + 1) eO eO'
    (fun B B' => by rw [heO, heO, hpO]) (fun B B' => by rw [heO', heO', hpO'])
    _ _ hcomm _ _ hTT
private theorem blockGaugeLift_of_mem (hS : BlocksPartitionFiner L n k (i + 1))
    (v : Vertex L n k (i + 1) → ComplexMatrix2) {y : Vertex L n k (i + 1)} {x : Vertex L n k i}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y) :
    blockGaugeLift v x = v y := by apply _root_.YangMills.SharedProofs.p60232 <;> assumption
private theorem toSublattice_mem_sitesInBlock (hB : ∀ y, BlockEqOffsetImage L n k (i + 1) y)
    (hS : BlocksPartitionFiner L n k (i + 1)) (y : Vertex L n k (i + 1)) :
    (y.toSublattice (PeriodicLattice.levelDepth k i) : Vertex L n k i) ∈
      PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y := by apply _root_.YangMills.SharedProofs.p22504 <;> assumption
private theorem restrict_blockGaugeLift (hB : ∀ y, BlockEqOffsetImage L n k (i + 1) y)
    (hS : BlocksPartitionFiner L n k (i + 1)) (v : Vertex L n k (i + 1) → ComplexMatrix2) :
    restrictVertexFunction (i + 1) (blockGaugeLift v) = v := by
  funext y
  exact blockGaugeLift_of_mem hS v (toSublattice_mem_sitesInBlock hB hS y)
private theorem axialFunction_blockGaugeLift (hB : ∀ y, BlockEqOffsetImage L n k (i + 1) y)
    (hS : BlocksPartitionFiner L n k (i + 1)) {v : Vertex L n k (i + 1) → ComplexMatrix2}
    (hv : ∀ y, v y ∈ PeriodicLattice.compactGaugeGroup) {U : Edge L n k i → ComplexMatrix2}
    (hc : ∀ (y : Vertex L n k (i + 1)),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
      PeriodicLattice.meanContourHolonomy (PeriodicLattice.gaugeTransform (blockGaugeLift v) U) y x =
        blockGaugeLift v (y.toSublattice (PeriodicLattice.levelDepth k i)) *
          PeriodicLattice.meanContourHolonomy U y x * (blockGaugeLift v x)⁻¹) :
    axialFunction L n k i (PeriodicLattice.gaugeTransform (blockGaugeLift v) U) =
      axialFunction L n k i U := by apply _root_.YangMills.SharedProofs.p62128 <;> assumption
private theorem finite_edge (hL : 0 < L) : Finite (Edge L n k j) :=
  haveI := SeparatedSequences.BaseParameters.site_finite hL n (PeriodicLattice.levelDepth k j)
  Finite.of_injective (fun b : Edge L n k j => (b.source, b.target)) fun _ _ h =>
    PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
theorem logNormaliserRatio_gauge_invariant (hFam : ChosenBranchIsCritical)
    (hForm : CriticalFibreHessianPosDef)
    (hG : ConstrainedGaussianIsometryInvariance)
    (hAvg : SmoothingAnalyticCovariantOnSides)
    (hBlocks : BlockStructure)
    (hGF : GaugeEquivarianceFormsAllSides)
    (hP : diffAtZeroPathsStatement)
    (hA : AnalyticMapsAlongCurves) :
    LogNormaliserRatioGaugeInvariant := by
  intro L n k hL hn i hi
  have hik : i < k := hi
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hfs : ∀ j : ℕ, Finite (Vertex L n k j) :=
    fun j => SeparatedSequences.BaseParameters.site_finite hL0 n _
  have hfb : ∀ j : ℕ, Finite (Edge L n k j) := fun _ => finite_edge hL0
  have := hfs i
  have := hfs (i + 1)
  have := hfb i
  have := hfb (i + 1)
  obtain ⟨hb, hNall⟩ := hFam L n k hL hn
  have hN := hNall i hik
  obtain ⟨hDisp, hSort, -, -⟩ :=
    (hBlocks L k (i + 1) hL (by omega) (by omega) (by omega)).1 n hn
  obtain ⟨δ₁, hδ₁, hcov⟩ := exists_radius_of_near (hAvg L hL n k i hn hik).gauge_covariant
  have hForm' : EventuallyNearIdentity (fieldSpace L n k (i + 1)) (FibreFacts L n k i) :=
    hForm L n k hL hn i hi
  obtain ⟨δ₃, hδ₃, hgood⟩ := exists_radius_of_near hForm'
  have hlift : Tendsto (chosenProlong L n k i)
      (𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1))
      (𝓝[fieldSpace L n k i] trivialField L n k i) := by
    obtain ⟨𝒲, hU, hAn⟩ := hb.analytic_prolong i hik
    have hnear : 𝒲 ∈ 𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1) :=
      (hP L n k (i + 1) hL hn hi).2.1 𝒲 hU.1 _ hU.2
    have hc := ((hA L n k (i + 1) i hL hn hi (by omega)).1 𝒲 _ hAn).1 _ hU.2
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.mem_of_superset hnear fun W hW => hAn.2.1 hW⟩
    have h := hc.tendsto.mono_left (nhdsWithin_le_of_mem hnear)
    rw [hb.prolong_trivial i hik] at h
    exact h
  have hwG : ∀ v : Vertex L n k (i + 1) → ComplexMatrix2, v ∈ gaugeGroupAt L n k (i + 1) →
      blockGaugeLift v ∈ gaugeGroupAt L n k i := fun _ h _ => h _
  have hstep : ∀ v ∈ gaugeGroupAt L n k (i + 1),
      ∀ U ∈ fieldSpace L n k i, (∀ c, ‖U c - 1‖ < δ₁) →
      (chosenCriticalBranch L n k).energy i (PeriodicLattice.gaugeTransform (blockGaugeLift v) U) =
        (chosenCriticalBranch L n k).energy i U →
      smoothingStep L n k i (PeriodicLattice.gaugeTransform (blockGaugeLift v) U) =
          PeriodicLattice.gaugeTransform v (smoothingStep L n k i U) ∧
        chosenGaugeFixedEnergy L n k i (PeriodicLattice.gaugeTransform (blockGaugeLift v) U) =
          chosenGaugeFixedEnergy L n k i U := by
    intro v hv U hU hs hF
    obtain ⟨h1, h2⟩ := hcov U hU hs (blockGaugeLift v) (hwG v hv)
    rw [restrict_blockGaugeLift hDisp hSort] at h1
    refine ⟨h1, ?_⟩
    unfold chosenGaugeFixedEnergy CriticalBranchData.gaugeFixedEnergy
    rw [hF, axialFunction_blockGaugeLift hDisp hSort hv h2]
  refine ⟨?_, ?_⟩
  · obtain ⟨la, hla, lb, hlb, hlab⟩ := eventually_prod_iff.1 (hb.prolong_gauge_equivariant i hik).1
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := eventually_prod_iff.1 (hb.energy_gauge_invariant i hik.le).1
    obtain ⟨η₁, hη₁, ha⟩ := exists_radius_of_near (D := gaugeGroupAt L n k i) (P := pa) hpa
    obtain ⟨δ₂, hδ₂, hb₂⟩ := exists_radius_of_near (D := fieldSpace L n k i) (P := pb) hpb
    obtain ⟨δ, hδ, hδa, hδb⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₁ ∧ δ ≤ δ₂ :=
      ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, min_le_left _ _, min_le_right _ _⟩
    obtain ⟨η, hη, hηa, hηb⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ η₁ ∧ η ≤ δ₃ / 4 :=
      ⟨min η₁ (δ₃ / 4), lt_min hη₁ (by positivity), min_le_left _ _, min_le_right _ _⟩
    refine eventually_prod_iff.2 ⟨fun v => v ∈ gaugeGroupAt L n k (i + 1) ∧
      (∀ y, ‖v y - 1‖ < η) ∧ la v, ?_, fun W => W ∈ fieldSpace L n k (i + 1) ∧
      (∀ c, ‖W c - 1‖ < δ₃ / 2) ∧ (∀ c, ‖chosenProlong L n k i W c - 1‖ < δ) ∧ lb W, ?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_near_one hη), hla]
        with v h1 h2 h3
      exact ⟨h1, h2, h3⟩
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_near_one (half_pos hδ₃)),
        hlift.eventually (nhdsWithin_le_nhds (eventually_near_one hδ)), hlb] with W h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    · intro v hv W hW
      obtain ⟨hvG, hvs, hvl⟩ := hv
      obtain ⟨hWc, hWs, hpW, hWl⟩ := hW
      have hvg : ∀ y, v y ∈ PeriodicLattice.compactGaugeGroup := hvG
      have hws : ∀ x, ‖blockGaugeLift v x - 1‖ < η := fun x => hvs _
      have hWvs : ∀ c, ‖PeriodicLattice.gaugeTransform v W c - 1‖ < δ₃ := by
        intro c
        have h0 := norm_conj_sub_one_le (X := W c) (hvg c.source) (hvg c.target)
        have h1 := hWs c
        have h2 := hvs c.source
        have h3 := hvs c.target
        change ‖v c.source * W c * (v c.target)⁻¹ - 1‖ < δ₃
        linarith
      have hG1 := hgood W hWc fun c => (hWs c).trans (half_lt_self hδ₃)
      have hG2 := hgood _ (gaugeTransform_mem hvg hWc) hWvs
      have hZ : gaussianNormaliser L n k i (PeriodicLattice.gaugeTransform v W) =
          gaussianNormaliser L n k i W := by
        refine gaussianNormaliser_gaugeTransform hG hGF hP hA hL hn hi hN hvG (hwG v hvG) hG1 hG2
          (hlab hvl hWl) hpW fun U hU hs => ?_
        exact hstep v hvG U hU (fun c => (hs c).trans_le hδa)
          (hab (ha _ (hwG v hvG) fun x => (hws x).trans_le hηa)
            (hb₂ U hU fun c => (hs c).trans_le hδb))
      change logNormaliserRatio L n k i (PeriodicLattice.gaugeTransform v W) =
        logNormaliserRatio L n k i W
      unfold logNormaliserRatio
      rw [hZ]
  · obtain ⟨δ₂, hδ₂, hb₂⟩ := exists_radius_of_near (hb.energy_gauge_invariant i hik.le).2
    obtain ⟨δ, hδ, hδa, hδb⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₁ ∧ δ ≤ δ₂ :=
      ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, min_le_left _ _, min_le_right _ _⟩
    change ∀ᶠ W in 𝓝[fieldSpace L n k (i + 1)] (fun _ => (1 : ComplexMatrix2)), _
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_near_one hδ₃),
      hlift.eventually (nhdsWithin_le_nhds (eventually_near_one hδ)),
      (hb.prolong_gauge_equivariant i hik).2]
      with W hWc hWs hpW hWl v hvG hconst
    have hvg : ∀ y, v y ∈ PeriodicLattice.compactGaugeGroup := hvG
    have hWvs : ∀ c, ‖PeriodicLattice.gaugeTransform v W c - 1‖ < δ₃ := by
      intro c
      change ‖v c.source * W c * (v c.target)⁻¹ - 1‖ < δ₃
      rw [hconst c.target c.source, norm_conj_sub_one (hvg _)]
      exact hWs c
    have hG1 := hgood W hWc hWs
    have hG2 := hgood _ (gaugeTransform_mem hvg hWc) hWvs
    have hZ : gaussianNormaliser L n k i (PeriodicLattice.gaugeTransform v W) =
        gaussianNormaliser L n k i W := by
      refine gaussianNormaliser_gaugeTransform hG hGF hP hA hL hn hi hN hvG (hwG v hvG) hG1 hG2
        (hWl v hvG hconst) hpW fun U hU hs => ?_
      exact hstep v hvG U hU (fun c => (hs c).trans_le hδa)
        (hb₂ U hU (fun c => (hs c).trans_le hδb) _ (hwG v hvG) fun x x' => hconst _ _)
    unfold logNormaliserRatio
    rw [hZ]
end YangMills.Construction.Tower
end
