import YangMills.Construction.Matrices.PauliMatricesAreAnOrthonormalBasisProof
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChartProof
import YangMills.Construction.OneLoop.PauliMatrixComputations
import YangMills.Construction.Towers.DifferentialsOfRealAnalyticMaps
import YangMills.Construction.Towers.PairingOfTheRealTransposeOnForms
import YangMills.Construction.Towers.PathsDifferentiableAtZeroProof
import YangMills.Construction.Towers.RealAnalyticMapsAlongPathsProof
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces YangMills.Construction.Matrices.PowerExpCharts
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.AnalyticDifferentials
open YangMills.Construction.Tower.AnalyticNearField YangMills.Construction.Tower.LeftChartFields
private def pauliCoeff (Y : ComplexMatrix2) (a : Fin 3) : ℂ :=
  ComplexMatrix2.halfTrace (Y * ComplexMatrix2.pauliFamily a)
private theorem pauliCoeff_pauliFamily (a b : Fin 3) :
    pauliCoeff (ComplexMatrix2.pauliFamily a) b = if a = b then 1 else 0 := by apply _root_.YangMills.Construction.Matrices.PauliBasis.halfTracePairing_pauli <;> assumption
private theorem eq_sum_pauliCoeff {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.traceless) :
    Y = ∑ a, pauliCoeff Y a • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.LeftChartFields.eq_sum_pauliCoeff <;> assumption
private theorem pauliFamily_mem_su (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
private theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private theorem pauliCoeff_im {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff Y a).im = 0 := by apply _root_.YangMills.Construction.Tower.LeftChartFields.pauliCoeff_im <;> assumption
private theorem traceless_ext {Y Y' : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.traceless)
    (hY' : Y' ∈ ComplexMatrix2.traceless) (h : ∀ a, pauliCoeff Y a = pauliCoeff Y' a) :
    Y = Y' := by apply _root_.YangMills.Construction.Tower.LeftChartFields.traceless_ext_pauliCoeff <;> assumption
private theorem pauliCoeff_sum (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff (∑ e, c e • ComplexMatrix2.pauliFamily e) a = c a := by apply _root_.YangMills.Construction.Tower.LeftChartFields.pauliCoeff_sum <;> assumption
private theorem continuous_pauliCoeff (a : Fin 3) :
    Continuous fun Y : ComplexMatrix2 => pauliCoeff Y a := by
  unfold pauliCoeff ComplexMatrix2.halfTrace ComplexMatrix2.fullTrace
  exact continuous_const.mul (Continuous.matrix_trace (continuous_id.mul continuous_const))
private theorem inv_eq_star_of_mem {M : ComplexMatrix2}
    (hM : M ∈ PeriodicLattice.compactGaugeGroup) : M⁻¹ = star M := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.inv_eq_star_of_mem <;> assumption
section Power
variable {σ : Type} [Fintype σ]
private theorem exists_lieProjection :
    ∃ P : ComplexMatrix2 →L[ℝ] ComplexMatrix2.LieElement,
      ∀ Y : ComplexMatrix2.LieElement, P Y.toMatrix = Y := by apply _root_.YangMills.Construction.Matrices.specialUnitaryPower.Composition.exists_clm_leftInverse_toMatrix <;> assumption
private theorem exists_smooth_extension {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hcharts : PowerCharts σ) {O : Set (σ → ComplexMatrix2)} {f : (σ → ComplexMatrix2) → E}
    {p₀ : σ → ComplexMatrix2} (hp₀ : p₀ ∈ specialUnitaryPower σ)
    {N : Set (σ → ComplexMatrix2.LieElement)} (hN : N ∈ 𝓝 0)
    (hform : ChartMapsInto O p₀ N) (hsm : ContDiffOn ℝ ∞ (f ∘ expChartI p₀) N) :
    ∃ (Ω : Set (σ → ComplexMatrix2)) (g : (σ → ComplexMatrix2) → E), IsOpen Ω ∧ p₀ ∈ Ω ∧
      ContDiffOn ℝ ∞ g Ω ∧ ∀ w ∈ Ω, w ∈ specialUnitaryPower σ → w ∈ O ∧ g w = f w := by
  obtain ⟨-, hform', hε⟩ := hcharts p₀ hp₀
  have hεpos : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, ⟨Ω₀, hΩ₀, himg⟩, hp₀img, -, hlogopen, hlogsm, hsub, hleft, -⟩ :=
    hε _ hεpos (by rw [Real.exp_log (by norm_num)])
  obtain ⟨P, hP⟩ := exists_lieProjection
  let G₁ : (σ → ComplexMatrix2) → σ → ComplexMatrix2.LieElement := fun X s => P (logChart p₀ X s)
  have hz : (0 : ComplexMatrix2.LieElement).toMatrix = 0 := rfl
  have hchart0 : expChartI p₀ 0 = p₀ := by
    rw [(hform' 0).2.1]
    funext s
    simp [hz]
  have h0small : (0 : σ → ComplexMatrix2.LieElement) ∈ smallBall σ (Real.log (19 / 10)) := by
    intro s
    simpa [hz] using hεpos
  have hG₁0 : G₁ p₀ = 0 := by
    funext s
    have hl := congrFun (hleft 0 h0small) s
    rw [hchart0] at hl
    show P (logChart p₀ p₀ s) = 0
    rw [hl]
    exact hP 0
  have hG₁ : ContDiffOn ℝ ∞ G₁ (logDomain p₀) :=
    contDiffOn_pi.2 fun s => P.contDiff.comp_contDiffOn (contDiffOn_pi.1 hlogsm s)
  have hp₀Ω₀ : p₀ ∈ Ω₀ := (himg ▸ hp₀img : p₀ ∈ Ω₀ ∩ _).1
  have hp₀log : p₀ ∈ logDomain p₀ := hsub hp₀img
  refine ⟨Ω₀ ∩ (logDomain p₀ ∩ G₁ ⁻¹' interior N), (f ∘ expChartI p₀) ∘ G₁,
    hΩ₀.inter (hG₁.continuousOn.isOpen_inter_preimage hlogopen isOpen_interior),
    ⟨hp₀Ω₀, hp₀log, ?_⟩, ?_, ?_⟩
  · show G₁ p₀ ∈ interior N
    rw [hG₁0]
    exact mem_interior_iff_mem_nhds.2 hN
  · refine hsm.comp (hG₁.mono fun w hw => hw.2.1) fun w hw => ?_
    exact interior_subset hw.2.2
  · intro w hw hwG
    have hmem : w ∈ expChartI p₀ '' smallBall σ (Real.log (19 / 10)) := by
      rw [himg]
      exact ⟨hw.1, hwG⟩
    obtain ⟨Y, hY, rfl⟩ := hmem
    have hG₁Y : G₁ (expChartI p₀ Y) = Y := by
      funext s
      show P (logChart p₀ (expChartI p₀ Y) s) = Y s
      rw [hleft Y hY]
      exact hP (Y s)
    refine ⟨hform ?_, ?_⟩
    · have h := hw.2.2
      change G₁ (expChartI p₀ Y) ∈ interior N at h
      rw [hG₁Y] at h
      exact interior_subset h
    · show f (expChartI p₀ (G₁ (expChartI p₀ Y))) = _
      rw [hG₁Y]
end Power
set_option maxHeartbeats 400000 in
private theorem differentiable_mixed {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : V → F} (hg : ContDiffAt ℝ 2 G 0) (u u' : V) :
    (∀ᶠ s : ℝ in 𝓝 0, DifferentiableAt ℝ (fun t : ℝ => G (s • u + t • u')) 0) ∧
      DifferentiableAt ℝ (fun s : ℝ => deriv (fun t : ℝ => G (s • u + t • u')) 0) 0 := by
  have hnear : ∀ᶠ y in 𝓝 (0 : V), DifferentiableAt ℝ G y :=
    (hg.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hl₀ : HasDerivAt (fun s : ℝ => s • u) u 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const u
    rw [one_smul] at h
    exact h
  have hs : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ G (s • u) := by
    have h : Tendsto (fun s : ℝ => s • u) (𝓝 0) (𝓝 0) := by
      have h' := hl₀.continuousAt.tendsto
      rwa [zero_smul] at h'
    exact h.eventually hnear
  have hline : ∀ s : ℝ, HasDerivAt (fun t : ℝ => s • u + t • u') u' 0 := by
    intro s
    have h' := ((hasDerivAt_id (0 : ℝ)).smul_const u').const_add (s • u)
    rw [one_smul] at h'
    exact h'
  have hpt : ∀ s : ℝ, (fun t : ℝ => s • u + t • u') 0 = s • u := fun s => by simp
  have hder : ∀ s : ℝ, DifferentiableAt ℝ G (s • u) →
      HasDerivAt (fun t : ℝ => G (s • u + t • u')) (fderiv ℝ G (s • u) u') 0 := by
    intro s h
    have h₁ : HasFDerivAt G (fderiv ℝ G (s • u)) ((fun t : ℝ => s • u + t • u') 0) := by
      rw [hpt]
      exact h.hasFDerivAt
    exact h₁.comp_hasDerivAt (0 : ℝ) (hline s)
  refine ⟨hs.mono fun s h => (hder s h).differentiableAt, ?_⟩
  have hinner : (fun s : ℝ => deriv (fun t : ℝ => G (s • u + t • u')) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ G (s • u) u' := by
    filter_upwards [hs] with s h
    exact (hder s h).deriv
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hinner
  have hfd : DifferentiableAt ℝ (fderiv ℝ G) 0 :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h₁ : DifferentiableAt ℝ (fderiv ℝ G) ((fun s : ℝ => s • u) 0) := by
    simpa using hfd
  exact (h₁.comp (0 : ℝ) hl₀.differentiableAt).clm_apply (differentiableAt_const u')
private theorem hasDerivAt_mul_of_vanishing {φ ψ : ℝ → ComplexMatrix2} {d : ComplexMatrix2}
    (h0 : φ 0 = 0) (hφ : HasDerivAt φ d 0) (hψ : ContinuousAt ψ 0) :
    HasDerivAt (fun t => φ t * ψ t) (d * ψ 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hφ ⊢
  have hψ' : Tendsto ψ (𝓝[≠] 0) (𝓝 (ψ 0)) := hψ.tendsto.mono_left nhdsWithin_le_nhds
  refine (hφ.mul hψ').congr fun t => ?_
  simp [slope, h0]
private def halfTraceCLM : ComplexMatrix2 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    (((1 / 2 : ℂ) • Matrix.traceLinearMap (Fin 2) ℂ ℂ : ComplexMatrix2 →ₗ[ℂ] ℂ).restrictScalars ℝ)
private theorem halfTraceCLM_apply (X : ComplexMatrix2) :
    halfTraceCLM X = ComplexMatrix2.halfTrace X := rfl
private theorem logSeries_along_curve {W : ℝ → ComplexMatrix2} {A D : ComplexMatrix2}
    (hlogs : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra)
    (hnear : ∀ᶠ t in 𝓝 (0 : ℝ), W t ∈ PeriodicLattice.compactGaugeGroup) (h0 : W 0 = A)
    (hD : HasDerivAt W D 0) :
    (∀ᶠ t in 𝓝 (0 : ℝ), ComplexMatrix2.operatorNorm (W t * A⁻¹ - 1) < 1) ∧
      DifferentiableAt ℝ (fun t => ComplexMatrix2.logSeries (W t * A⁻¹)) 0 ∧
      Complex.I⁻¹ • deriv (fun t => ComplexMatrix2.logSeries (W t * A⁻¹)) 0 =
        Complex.I⁻¹ • (D * A⁻¹) ∧
      Complex.I⁻¹ • (D * A⁻¹) ∈ ComplexMatrix2.hermitianTraceless := by
  subst h0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnear
  have hI : IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) ε) := by
    refine ⟨Metric.isOpen_ball, ?_, Metric.mem_ball_self hε⟩
    rw [Real.ball_eq_Ioo]
    exact ordConnected_Ioo
  have h := hlogs _ hI W (fun t ht => hball t ht) hD.differentiableAt
  rw [hD.deriv] at h
  exact h
private theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
private theorem holomorphicScalar_of_coords {σ : Type} [Fintype σ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (h : IsHolomorphicToCoords b (Equiv.refl _) W Φ) :
    HolomorphicScalar b W fun q => Φ q 0 := by apply _root_.YangMills.SharedProofs.p9409 <;> assumption
section Lattice
variable {L n k j j' : ℕ}
private structure EdgeFacts (L n k j : ℕ) : Prop where
  rev : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented
  left : (finiteData L n k j).LeftExpMulMemGroup
  nonempty : Nonempty (PositiveEdge L n k j)
private theorem opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
private theorem positive_or_opposite_positive (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem fieldOfPositiveValues_restrict {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem fieldOfPositiveValues_restrict_expTwist (A U : Edge L n k j → ComplexMatrix2) :
    fieldOfPositiveValues (restrictToPositiveEdges (PeriodicLattice.expTwist A U)) =
      PeriodicLattice.expTwist A U := by
  funext b
  by_cases h : b.IsPositivelyOriented
  · simp [fieldOfPositiveValues, PeriodicLattice.expTwist, h, restrictToPositiveEdges]
  · have h' := (positive_or_opposite_positive b).resolve_left h
    simp [fieldOfPositiveValues, PeriodicLattice.expTwist, h, h', restrictToPositiveEdges]
abbrev _root_.YangMills.SharedProofs.p25947 := @fieldOfPositiveValues_restrict_expTwist
private theorem restrict_expTwist_apply (A U : Edge L n k j → ComplexMatrix2)
    (b : PositiveEdge L n k j) :
    restrictToPositiveEdges (PeriodicLattice.expTwist A U) b =
      ComplexMatrix2.matExp (Complex.I • A b.1) * U b.1 := by
  simp only [restrictToPositiveEdges, PeriodicLattice.expTwist, if_pos b.2]
private theorem expTwist_zero_smul {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (B : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B) V = V := by apply _root_.YangMills.Construction.Tower.DiffAtZeroPaths.expTwist_zero_smul <;> assumption
private theorem extendOddly_isBondForm (hl : EdgeFacts L n k j) {𝔥 : Set ComplexMatrix2}
    {f : Edge L n k j → ComplexMatrix2} (hf : ∀ b, b.IsPositivelyOriented → f b ∈ 𝔥) :
    PeriodicLattice.IsBondForm 𝔥 (extendOddly f) := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [extendOddly, if_pos hb]
    exact hf b hb
  · by_cases hb : b.IsPositivelyOriented
    · simp only [extendOddly, if_pos hb, if_neg (hl.rev b hb), opposite_opposite]
    · have hr := (positive_or_opposite_positive b).resolve_left hb
      simp only [extendOddly, if_pos hr, if_neg hb, neg_neg]
private theorem edgeFormOfPositiveValues_mem (hl : EdgeFacts L n k j)
    {w : PositiveEdge L n k j → ComplexMatrix2}
    (hw : ∀ b, w b ∈ ComplexMatrix2.hermitianTraceless) :
    edgeFormOfPositiveValues w ∈ edgeFormSpace L n k j := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [edgeFormOfPositiveValues, dif_pos hb]
    exact hw _
  · by_cases hb : b.IsPositivelyOriented
    · have hr := hl.rev b hb
      have hrr : b.opposite.opposite.IsPositivelyOriented := hb
      simp only [edgeFormOfPositiveValues, dif_pos hb, dif_neg hr, dif_pos hrr]
      rfl
    · have hr := (positive_or_opposite_positive b).resolve_left hb
      simp only [edgeFormOfPositiveValues, dif_pos hr, dif_neg hb, neg_neg]
private theorem bondForm_ext {𝔥 : Set ComplexMatrix2} {B B' : Edge L n k j → ComplexMatrix2}
    (hB : PeriodicLattice.IsBondForm 𝔥 B) (hB' : PeriodicLattice.IsBondForm 𝔥 B')
    (h : ∀ b, b.IsPositivelyOriented → B b = B' b) : B = B' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact h b hb
  · have hr := (positive_or_opposite_positive b).resolve_left hb
    have h1 : B b.opposite = -B b := hB.2 b
    have h2 : B' b.opposite = -B' b := hB'.2 b
    have h3 := h _ hr
    rw [h1, h2] at h3
    exact neg_injective h3
private theorem edgeForm_ext {B B' : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) (hB' : B' ∈ edgeFormSpace L n k j)
    (h : ∀ b, b.IsPositivelyOriented → B b = B' b) : B = B' := by apply _root_.YangMills.SharedProofs.p88895 <;> assumption
private theorem pauliBasisForm_mem (hl : EdgeFacts L n k j) (b : PositiveEdge L n k j)
    (a : Fin 3) : pauliBasisForm b a ∈ edgeFormSpace L n k j := by
  refine edgeFormOfPositiveValues_mem hl fun c => ?_
  split_ifs
  · exact pauliFamily_mem_su a
  · exact ComplexMatrix2.hermitianTraceless.zero_mem
private theorem pauliBasisForm_apply (b c : PositiveEdge L n k j) (a : Fin 3) :
    pauliBasisForm b a c.1 =
      open Classical in if c = b then ComplexMatrix2.pauliFamily a else 0 := by
  simp only [pauliBasisForm, edgeFormOfPositiveValues, dif_pos c.2]
private theorem edgeFormPairing_pauliBasisForm (X : Edge L n k j → ComplexMatrix2)
    (b : PositiveEdge L n k j) (a : Fin 3) :
    edgeFormPairing X (pauliBasisForm b a) = pauliCoeff (X b.1) a := by
  classical
  unfold edgeFormPairing traceFinsumPairing
  rw [finsum_eq_single _ b]
  · simp [restrictToPositiveEdges, pauliBasisForm_apply, pauliCoeff]
  · intro c hc
    simp [restrictToPositiveEdges, pauliBasisForm_apply, hc]
abbrev _root_.YangMills.DeltaSharedProofs.p500976 := @edgeFormPairing_pauliBasisForm
variable [Fintype (PositiveEdge L n k j)]
private theorem edgeFormPairing_eq_sum (X Y : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing X Y = ∑ b : PositiveEdge L n k j, halfTraceCLM (X b.1 * Y b.1) :=
  finsum_eq_sum_of_fintype _
private theorem sum_pauliBasisForm_apply (x : PositiveEdge L n k j × Fin 3 → ℝ)
    (b : PositiveEdge L n k j) :
    (∑ i : PositiveEdge L n k j × Fin 3, x i • pauliBasisForm i.1 i.2) b.1 =
      ∑ a, x (b, a) • ComplexMatrix2.pauliFamily a := by
  classical
  rw [Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [pauliBasisForm_apply]
  · intro c _ hc
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [pauliBasisForm_apply, Ne.symm hc]
  · simp
private theorem ofReal_re_pauliCoeff {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) (a : Fin 3) :
    (((pauliCoeff Y a).re : ℝ) : ℂ) = pauliCoeff Y a :=
  Complex.ext rfl (by simp [pauliCoeff_im hY a])
private theorem eq_sum_pauliBasisForm (hl : EdgeFacts L n k j) {Y : Edge L n k j → ComplexMatrix2}
    (hY : Y ∈ edgeFormSpace L n k j) :
    Y = ∑ i : PositiveEdge L n k j × Fin 3,
      (pauliCoeff (Y i.1.1) i.2).re • pauliBasisForm i.1 i.2 := by
  refine edgeForm_ext hY (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (pauliBasisForm_mem hl i.1 i.2)) fun b hb => ?_
  have hval := sum_pauliBasisForm_apply
    (fun i : PositiveEdge L n k j × Fin 3 => (pauliCoeff (Y i.1.1) i.2).re) ⟨b, hb⟩
  refine Eq.trans ?_ hval.symm
  have hsu : Y b ∈ ComplexMatrix2.hermitianTraceless := hY.1 b hb
  conv_lhs => rw [eq_sum_pauliCoeff hsu.2]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.coe_smul, ofReal_re_pauliCoeff hsu]
private theorem colorCoords_eq (hl : EdgeFacts L n k j) {Y : Edge L n k j → ComplexMatrix2}
    (hY : Y ∈ edgeFormSpace L n k j) (i : PositiveEdge L n k j × Fin 3) :
    colorCoords Y i = (pauliCoeff (Y i.1.1) i.2).re := by
  have hex : ∃ x : PositiveEdge L n k j × Fin 3 → ℝ, formOfCoeffs x = Y :=
    ⟨fun i => (pauliCoeff (Y i.1.1) i.2).re,
      (finsum_eq_sum_of_fintype _).trans (eq_sum_pauliBasisForm hl hY).symm⟩
  have hspec : formOfCoeffs (colorCoords Y) = Y := Classical.epsilon_spec hex
  have hsum : ∑ i : PositiveEdge L n k j × Fin 3,
      colorCoords Y i • pauliBasisForm i.1 i.2 = Y :=
    (finsum_eq_sum_of_fintype _).symm.trans hspec
  have hval := sum_pauliBasisForm_apply (colorCoords Y) i.1
  rw [hsum] at hval
  have hc : pauliCoeff (Y i.1.1) i.2 = (colorCoords Y i : ℂ) := by
    rw [hval]
    simp only [← Complex.coe_smul]
    exact pauliCoeff_sum (fun a => (colorCoords Y (i.1, a) : ℂ)) i.2
  rw [hc]
  simp
private structure SmoothExtensionOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒲 : Set (Edge L n k j → ComplexMatrix2)) (h : (Edge L n k j → ComplexMatrix2) → E)
    (Ω : Set (PositiveEdge L n k j → ComplexMatrix2))
    (g : (PositiveEdge L n k j → ComplexMatrix2) → E) : Prop where
  isOpen : IsOpen Ω
  smooth : ContDiffOn ℝ ∞ g Ω
  eq : ∀ w ∈ Ω, w ∈ specialUnitaryPower (PositiveEdge L n k j) →
    fieldOfPositiveValues w ∈ 𝒲 ∧ g w = h (fieldOfPositiveValues w)
private theorem exists_smoothExtensionOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hC : PowerCharts (PositiveEdge L n k j)) {𝒲 : Set (Edge L n k j → ComplexMatrix2)}
    (hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒲)
    {h : (Edge L n k j → ComplexMatrix2) → E}
    (hser : HasChartPowerSeries (restrictToPositiveEdges '' 𝒲)
      fun w => h (fieldOfPositiveValues w))
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ 𝒲) :
    ∃ (Ω : Set (PositiveEdge L n k j → ComplexMatrix2))
      (g : (PositiveEdge L n k j → ComplexMatrix2) → E),
      restrictToPositiveEdges V ∈ Ω ∧ SmoothExtensionOn 𝒲 h Ω g := by
  obtain ⟨N, hN, hform, hsm, -⟩ := hser.1 (restrictToPositiveEdges V) ⟨V, hV, rfl⟩
  have hp₀ : restrictToPositiveEdges V ∈ specialUnitaryPower (PositiveEdge L n k j) :=
    fun b => (hopen.1 hV).1 b.1 (mem_univ _)
  obtain ⟨Ω, g, hΩ, hmem, hg, heq⟩ := exists_smooth_extension hC hp₀ hN hform hsm
  refine ⟨Ω, g, hmem, hΩ, hg, fun w hw hG => ?_⟩
  obtain ⟨⟨U, hU, rfl⟩, hgw⟩ := heq w hw hG
  refine ⟨?_, hgw⟩
  rw [fieldOfPositiveValues_restrict (hopen.1 hU)]
  exact hU
private def leftTangentMap (V : Edge L n k j → ComplexMatrix2) :
    (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] (PositiveEdge L n k j → ComplexMatrix2) where
  toFun B b := Complex.I • B b.1 * V b.1
  map_add' B B' := by
    funext b
    simp [smul_add, add_mul]
  map_smul' c B := by
    funext b
    show Complex.I • (c • B b.1) * V b.1 = c • (Complex.I • B b.1 * V b.1)
    rw [smul_comm, smul_mul_assoc]
omit [Fintype (PositiveEdge L n k j)] in
private theorem restrict_expTwist_mem (hl : EdgeFacts L n k j)
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (hB : B ∈ edgeFormSpace L n k j) (t : ℝ) :
    restrictToPositiveEdges (PeriodicLattice.expTwist ((t : ℂ) • B) V) ∈
      specialUnitaryPower (PositiveEdge L n k j) := by
  intro b
  show restrictToPositiveEdges (PeriodicLattice.expTwist ((t : ℂ) • B) V) b ∈
    PeriodicLattice.compactGaugeGroup
  rw [restrict_expTwist_apply]
  exact (hl.left.1 V hV B hB b).1 t
omit [Fintype (PositiveEdge L n k j)] in
private theorem hasDerivAt_restrict_expTwist (hl : EdgeFacts L n k j)
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (hB : B ∈ edgeFormSpace L n k j) :
    HasDerivAt
      (fun t : ℝ => restrictToPositiveEdges (PeriodicLattice.expTwist ((t : ℂ) • B) V))
      (leftTangentMap V B) 0 := by
  refine hasDerivAt_pi.2 fun b => ?_
  refine ((hl.left.1 V hV B hB b).2).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  exact restrict_expTwist_apply _ _ b
private theorem hasDerivAt_along_expTwist {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hl : EdgeFacts L n k j) {𝒲 : Set (Edge L n k j → ComplexMatrix2)}
    {h : (Edge L n k j → ComplexMatrix2) → E} {Ω : Set (PositiveEdge L n k j → ComplexMatrix2)}
    {g : (PositiveEdge L n k j → ComplexMatrix2) → E} (hext : SmoothExtensionOn 𝒲 h Ω g)
    {V B : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j)
    (hw : restrictToPositiveEdges V ∈ Ω) (hB : B ∈ edgeFormSpace L n k j) :
    (∀ᶠ t : ℝ in 𝓝 0, PeriodicLattice.expTwist ((t : ℂ) • B) V ∈ 𝒲) ∧
      HasDerivAt (fun t : ℝ => h (PeriodicLattice.expTwist ((t : ℂ) • B) V))
        (fderiv ℝ g (restrictToPositiveEdges V) (leftTangentMap V B)) 0 := by
  have hc := hasDerivAt_restrict_expTwist hl hV hB
  have hc0 : (fun t : ℝ =>
      restrictToPositiveEdges (PeriodicLattice.expTwist ((t : ℂ) • B) V)) 0 =
      restrictToPositiveEdges V := by
    show restrictToPositiveEdges (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B) V) = _
    rw [expTwist_zero_smul hV]
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,
      restrictToPositiveEdges (PeriodicLattice.expTwist ((t : ℂ) • B) V) ∈ Ω :=
    hc.continuousAt.eventually_mem (hext.isOpen.mem_nhds (by
      rw [expTwist_zero_smul hV]
      exact hw))
  have hval : ∀ᶠ t : ℝ in 𝓝 0, PeriodicLattice.expTwist ((t : ℂ) • B) V ∈ 𝒲 ∧
      g (restrictToPositiveEdges (PeriodicLattice.expTwist ((t : ℂ) • B) V)) =
        h (PeriodicLattice.expTwist ((t : ℂ) • B) V) := by
    filter_upwards [hnear] with t ht
    have h' := hext.eq _ ht (restrict_expTwist_mem hl hV hB t)
    rwa [fieldOfPositiveValues_restrict_expTwist] at h'
  refine ⟨hval.mono fun _ h' => h'.1, ?_⟩
  have hg : DifferentiableAt ℝ g (restrictToPositiveEdges V) :=
    (hext.smooth.contDiffAt (hext.isOpen.mem_nhds hw)).differentiableAt (by simp)
  have h₁ : HasFDerivAt g (fderiv ℝ g (restrictToPositiveEdges V))
      ((fun t : ℝ =>
        restrictToPositiveEdges (PeriodicLattice.expTwist ((t : ℂ) • B) V)) 0) := by
    rw [hc0]
    exact hg.hasFDerivAt
  exact (h₁.comp_hasDerivAt (0 : ℝ) hc).congr_of_eventuallyEq
    (hval.mono fun t ht => ht.2.symm)
private theorem halfTraceCLM_sum_mul (c : Fin 3 → ℂ) (Y : ComplexMatrix2) :
    halfTraceCLM ((∑ a, c a • ComplexMatrix2.pauliFamily a) * Y) = ∑ a, c a * pauliCoeff Y a := by
  simp only [halfTraceCLM_apply, pauliCoeff, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Finset.sum_mul, Matrix.trace_sum, smul_mul_assoc, Matrix.trace_smul, Finset.mul_sum,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.trace_mul_comm]
  ring
private theorem hasLeftGradientAt_of_extension (hl : EdgeFacts L n k j)
    {𝒲 : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℂ}
    {Ω : Set (PositiveEdge L n k j → ComplexMatrix2)}
    {g : (PositiveEdge L n k j → ComplexMatrix2) → ℂ} (hext : SmoothExtensionOn 𝒲 F Ω g)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j)
    (hw : restrictToPositiveEdges V ∈ Ω) :
    HasLeftGradientAt 𝒲 F V := by
  have hder : ∀ B ∈ edgeFormSpace L n k j, leftDeriv F V B =
      fderiv ℝ g (restrictToPositiveEdges V) (leftTangentMap V B) :=
    fun B hB => (hasDerivAt_along_expTwist hl hext hV hw hB).2.deriv
  let X₀ : Edge L n k j → ComplexMatrix2 := extendOddly fun b =>
    open Classical in if h : b.IsPositivelyOriented then
      ∑ a, leftDeriv F V (pauliBasisForm ⟨b, h⟩ a) • ComplexMatrix2.pauliFamily a else 0
  have hX₀ : ∀ b : PositiveEdge L n k j,
      X₀ b.1 = ∑ a, leftDeriv F V (pauliBasisForm b a) • ComplexMatrix2.pauliFamily a := by
    intro b
    simp only [X₀, extendOddly, if_pos b.2, dif_pos b.2]
  have hgrad : IsLeftGradient 𝒲 F V X₀ := by
    refine ⟨extendOddly_isBondForm hl fun b hb => ?_,
      fun hreal => extendOddly_isBondForm hl fun b hb => ?_, fun B hB _ => ?_⟩
    · simp only [dif_pos hb]
      exact ComplexMatrix2.traceless.sum_mem fun a _ =>
        ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem_traceless a)
    · simp only [dif_pos hb]
      refine ComplexMatrix2.hermitianTraceless.sum_mem fun a _ => ?_
      obtain ⟨hnear, hd⟩ :=
        hasDerivAt_along_expTwist hl hext hV hw (pauliBasisForm_mem hl ⟨b, hb⟩ a)
      have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
      have hz : HasDerivAt (Complex.imCLM ∘ fun t : ℝ =>
          F (PeriodicLattice.expTwist ((t : ℂ) • pauliBasisForm ⟨b, hb⟩ a) V)) 0 0 :=
        (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
          (hnear.mono fun t ht => hreal _ ht)
      have hzero : (leftDeriv F V (pauliBasisForm ⟨b, hb⟩ a)).im = 0 := by
        rw [hder _ (pauliBasisForm_mem hl ⟨b, hb⟩ a)]
        exact him.unique hz
      have hre : leftDeriv F V (pauliBasisForm ⟨b, hb⟩ a) =
          (((leftDeriv F V (pauliBasisForm ⟨b, hb⟩ a)).re : ℝ) : ℂ) :=
        Complex.ext rfl (by simp [hzero])
      rw [hre, Complex.coe_smul]
      exact ComplexMatrix2.hermitianTraceless.smul_mem _ (pauliFamily_mem_su a)
    · have hR : leftDeriv F V B = ∑ i : PositiveEdge L n k j × Fin 3,
          (pauliCoeff (B i.1.1) i.2).re • leftDeriv F V (pauliBasisForm i.1 i.2) := by
        rw [hder B hB]
        conv_lhs => rw [eq_sum_pauliBasisForm hl hB]
        rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, map_smul, hder _ (pauliBasisForm_mem hl i.1 i.2)]
      rw [edgeFormPairing_eq_sum, hR, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hX₀ b, halfTraceCLM_sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hsu : B b.1 ∈ ComplexMatrix2.hermitianTraceless := hB.1 b.1 b.2
      rw [Complex.real_smul, ofReal_re_pauliCoeff hsu, mul_comm]
  have hspec : IsLeftGradient 𝒲 F V (leftGradient 𝒲 F V) := Classical.epsilon_spec ⟨X₀, hgrad⟩
  refine ⟨fun B hB => (hasDerivAt_along_expTwist hl hext hV hw hB).2.differentiableAt, hspec,
    fun X hX => ?_⟩
  refine bondForm_ext hX.1 hspec.1 fun b hb =>
    traceless_ext (hX.1.1 b hb) (hspec.1.1 b hb) fun a => ?_
  have h1 := hX.2.2 _ (pauliBasisForm_mem hl ⟨b, hb⟩ a) (Set.toFinite _)
  have h2 := hspec.2.2 _ (pauliBasisForm_mem hl ⟨b, hb⟩ a) (Set.toFinite _)
  rw [edgeFormPairing_pauliBasisForm] at h1 h2
  exact h1.trans h2.symm
private theorem hasLeftSecondDerivAt_of_series (hC : PowerCharts (PositiveEdge L n k j))
    {𝒲 : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℂ}
    (hser : HasChartPowerSeries (restrictToPositiveEdges '' 𝒲)
      fun w => F (fieldOfPositiveValues w))
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ 𝒲) (hVc : V ∈ fieldSpace L n k j) :
    HasLeftSecondDerivAt F V := by
  intro B hB B' hB'
  obtain ⟨N, hN, -, hsm, -⟩ := hser.1 (restrictToPositiveEdges V) ⟨V, hV, rfl⟩
  have hp₀ : restrictToPositiveEdges V ∈ specialUnitaryPower (PositiveEdge L n k j) :=
    fun b => hVc.1 b.1 (mem_univ _)
  obtain ⟨-, hform, -⟩ := hC _ hp₀
  have hg : ContDiffAt ℝ 2
      ((fun w => F (fieldOfPositiveValues w)) ∘ expChartI (restrictToPositiveEdges V)) 0 :=
    (hsm.contDiffAt hN).of_le ENat.LEInfty.out
  let u : PositiveEdge L n k j → ComplexMatrix2.LieElement :=
    fun b => (⟨B b.1, hB.1 b.1 b.2⟩ : ComplexMatrix2.hermitianTraceless)
  let u' : PositiveEdge L n k j → ComplexMatrix2.LieElement :=
    fun b => (⟨B' b.1, hB'.1 b.1 b.2⟩ : ComplexMatrix2.hermitianTraceless)
  have hval : ∀ s t : ℝ,
      ((fun w => F (fieldOfPositiveValues w)) ∘ expChartI (restrictToPositiveEdges V))
        (s • u + t • u') =
        F (PeriodicLattice.expTwist ((s : ℂ) • B + (t : ℂ) • B') V) := by
    intro s t
    show F (fieldOfPositiveValues (expChartI (restrictToPositiveEdges V) (s • u + t • u'))) = _
    rw [(hform _).2.1, ← fieldOfPositiveValues_restrict_expTwist]
    congr 2
    funext b
    rw [restrict_expTwist_apply]
    have hm : ((s • u + t • u') b).toMatrix = s • B b.1 + t • B' b.1 := rfl
    rw [hm]
    simp only [Pi.add_apply, Pi.smul_apply, Complex.coe_smul]
    rfl
  obtain ⟨h1, h2⟩ := differentiable_mixed hg u u'
  simp only [hval] at h1 h2
  exact ⟨h1, h2⟩
variable [Fintype (PositiveEdge L n k j')]
private theorem leftDifferential_facts (hl : EdgeFacts L n k j)
    (hlogs : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra)
    {𝒲 : Set (Edge L n k j → ComplexMatrix2)}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (hmaps : MapsTo m 𝒲 (fieldSpace L n k j')) {Ω : Set (PositiveEdge L n k j → ComplexMatrix2)}
    {g : (PositiveEdge L n k j → ComplexMatrix2) → PositiveEdge L n k j' → ComplexMatrix2}
    (hext : SmoothExtensionOn 𝒲 (fun V => restrictToPositiveEdges (m V)) Ω g)
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (hw : restrictToPositiveEdges V ∈ Ω)
    (hB : B ∈ edgeFormSpace L n k j) (c : PositiveEdge L n k j') :
    (∀ᶠ t : ℝ in 𝓝 0, ComplexMatrix2.operatorNorm
      (m (PeriodicLattice.expTwist ((t : ℂ) • B) V) c.1 * (m V c.1)⁻¹ - 1) < 1) ∧
    DifferentiableAt ℝ (fun t : ℝ =>
      ComplexMatrix2.logSeries
        (m (PeriodicLattice.expTwist ((t : ℂ) • B) V) c.1 * (m V c.1)⁻¹)) 0 ∧
    leftDifferential m V B c.1 = Complex.I⁻¹ •
      (fderiv ℝ g (restrictToPositiveEdges V) (leftTangentMap V B) c * (m V c.1)⁻¹) ∧
    Complex.I⁻¹ • (fderiv ℝ g (restrictToPositiveEdges V) (leftTangentMap V B) c *
      (m V c.1)⁻¹) ∈ ComplexMatrix2.hermitianTraceless := by
  obtain ⟨hnear, hder⟩ := hasDerivAt_along_expTwist hl hext hV hw hB
  have hW : HasDerivAt (fun t : ℝ => m (PeriodicLattice.expTwist ((t : ℂ) • B) V) c.1)
      (fderiv ℝ g (restrictToPositiveEdges V) (leftTangentMap V B) c) 0 :=
    (hasDerivAt_pi.1 hder) c
  have hW0 : (fun t : ℝ => m (PeriodicLattice.expTwist ((t : ℂ) • B) V) c.1) 0 = m V c.1 := by
    show m (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B) V) c.1 = _
    rw [expTwist_zero_smul hV]
  obtain ⟨h1, h2, h3, h4⟩ := logSeries_along_curve hlogs
    (hnear.mono fun t ht => (hmaps ht).1 c.1 (mem_univ _)) hW0 hW
  refine ⟨h1, h2, ?_, h4⟩
  rw [← h3]
  simp only [leftDifferential, extendOddly, if_pos c.2, logDirectionalDeriv]
  rfl
private theorem leftDifferential_mem (hl : EdgeFacts L n k j) (hl' : EdgeFacts L n k j')
    (hlogs : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra)
    {𝒲 : Set (Edge L n k j → ComplexMatrix2)}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (hmaps : MapsTo m 𝒲 (fieldSpace L n k j')) {Ω : Set (PositiveEdge L n k j → ComplexMatrix2)}
    {g : (PositiveEdge L n k j → ComplexMatrix2) → PositiveEdge L n k j' → ComplexMatrix2}
    (hext : SmoothExtensionOn 𝒲 (fun V => restrictToPositiveEdges (m V)) Ω g)
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (hw : restrictToPositiveEdges V ∈ Ω)
    (hB : B ∈ edgeFormSpace L n k j) :
    leftDifferential m V B ∈ edgeFormSpace L n k j' := by
  exact show PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra
      (leftDifferential m V B) from by
    refine extendOddly_isBondForm hl' fun c hc => ?_
    obtain ⟨-, -, h3, h4⟩ := leftDifferential_facts hl hlogs hmaps hext hV hw hB ⟨c, hc⟩
    have e : leftDifferential m V B c =
        logDirectionalDeriv ℝ (fun X => m (PeriodicLattice.expTwist X V) c) (m V c) B := by
      simp only [leftDifferential, extendOddly, if_pos hc]
    rw [← e, h3]
    exact h4
private theorem leftDifferentialIsLinear_of_extension (hl : EdgeFacts L n k j)
    (hl' : EdgeFacts L n k j')
    (hlogs : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra)
    {𝒲 : Set (Edge L n k j → ComplexMatrix2)}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (hmaps : MapsTo m 𝒲 (fieldSpace L n k j')) {Ω : Set (PositiveEdge L n k j → ComplexMatrix2)}
    {g : (PositiveEdge L n k j → ComplexMatrix2) → PositiveEdge L n k j' → ComplexMatrix2}
    (hext : SmoothExtensionOn 𝒲 (fun V => restrictToPositiveEdges (m V)) Ω g)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (hw : restrictToPositiveEdges V ∈ Ω) :
    LeftDifferentialIsLinear m V := by
  have hmem : ∀ B ∈ edgeFormSpace L n k j, leftDifferential m V B ∈ edgeFormSpace L n k j' :=
    fun B hB => leftDifferential_mem hl hl' hlogs hmaps hext hV hw hB
  have hformula : ∀ B ∈ edgeFormSpace L n k j, ∀ c : PositiveEdge L n k j',
      leftDifferential m V B c.1 = Complex.I⁻¹ •
        (fderiv ℝ g (restrictToPositiveEdges V) (leftTangentMap V B) c * (m V c.1)⁻¹) :=
    fun B hB c => (leftDifferential_facts hl hlogs hmaps hext hV hw hB c).2.2.1
  have hadd : ∀ B ∈ edgeFormSpace L n k j, ∀ B' ∈ edgeFormSpace L n k j,
      leftDifferential m V (B + B') = leftDifferential m V B + leftDifferential m V B' := by
    intro B hB B' hB'
    refine edgeForm_ext (hmem _ ((edgeFormSpace L n k j).add_mem hB hB'))
      ((edgeFormSpace L n k j').add_mem (hmem _ hB) (hmem _ hB')) fun c hc => ?_
    show _ = leftDifferential m V B c + leftDifferential m V B' c
    rw [hformula _ ((edgeFormSpace L n k j).add_mem hB hB') ⟨c, hc⟩, hformula B hB ⟨c, hc⟩,
      hformula B' hB' ⟨c, hc⟩, map_add, map_add]
    simp [add_mul, smul_add]
  have hsmul : ∀ (r : ℝ), ∀ B ∈ edgeFormSpace L n k j,
      leftDifferential m V (r • B) = r • leftDifferential m V B := by
    intro r B hB
    refine edgeForm_ext (hmem _ ((edgeFormSpace L n k j).smul_mem r hB))
      ((edgeFormSpace L n k j').smul_mem r (hmem _ hB)) fun c hc => ?_
    show _ = r • leftDifferential m V B c
    rw [hformula _ ((edgeFormSpace L n k j).smul_mem r hB) ⟨c, hc⟩, hformula B hB ⟨c, hc⟩,
      map_smul, map_smul, Pi.smul_apply, smul_mul_assoc, smul_comm]
  let T : edgeFormSpace L n k j →ₗ[ℝ] edgeFormSpace L n k j' :=
    { toFun := fun B => ⟨leftDifferential m V B, hmem B B.2⟩
      map_add' := fun B B' => Subtype.ext (hadd B B.2 B' B'.2)
      map_smul' := fun r B => Subtype.ext (hsmul r B B.2) }
  have hex : ∃ T : edgeFormSpace L n k j →ₗ[ℝ] edgeFormSpace L n k j',
      ∀ B : edgeFormSpace L n k j,
      (T B : Edge L n k j' → ComplexMatrix2) = leftDifferential m V B := ⟨T, fun _ => rfl⟩
  exact Classical.epsilon_spec hex
private theorem continuousOn_of_entries {f : ℝ → ComplexMatrix2} {S : Set ℝ}
    (h : ∀ r s, ContinuousOn (fun t => f t r s) S) : ContinuousOn f S := by
  have e : f = fun t => ∑ r, ∑ s, f t r s • (Matrix.single r s (1 : ℂ)) := by
    funext t
    ext i l
    simp [Matrix.sum_apply, Matrix.single_apply]
    fin_cases i <;> fin_cases l <;> simp
  rw [e]
  exact continuousOn_finsetSum _ fun r _ => continuousOn_finsetSum _ fun s _ =>
    (h r s).smul continuousOn_const
private theorem along_curve_facts (hl : EdgeFacts L n k j) (hl' : EdgeFacts L n k j')
    (hlogs : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra)
    {𝒲 : Set (Edge L n k j → ComplexMatrix2)}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (hmaps : MapsTo m 𝒲 (fieldSpace L n k j')) {Ω : Set (PositiveEdge L n k j → ComplexMatrix2)}
    {g : (PositiveEdge L n k j → ComplexMatrix2) → PositiveEdge L n k j' → ComplexMatrix2}
    (hext : SmoothExtensionOn 𝒲 (fun V => restrictToPositiveEdges (m V)) Ω g) {I : Set ℝ}
    {γ : ℝ → Edge L n k j → ComplexMatrix2} (hγ : IsContinuousCurveStartingIn 𝒲 I γ)
    (hw : restrictToPositiveEdges (γ 0) ∈ Ω) :
    ∃ J ∈ 𝓝 (0 : ℝ), (∀ t ∈ J, γ t ∈ 𝒲 ∧ LeftDifferentialIsLinear m (γ t)) ∧
      ∀ B ∈ edgeFormSpace L n k j,
        (∀ t ∈ J, leftDifferential m (γ t) B ∈ edgeFormSpace L n k j') ∧
        ∀ c : PositiveEdge L n k j',
          ContinuousOn (fun t => leftDifferential m (γ t) B c.1) J := by
  obtain ⟨hI, hmapsγ, -, hcont⟩ := hγ
  have hwc : ContinuousOn (fun t => restrictToPositiveEdges (γ t)) I :=
    continuousOn_pi.2 fun b => continuousOn_of_entries fun r s => hcont b.1 b.2 r s
  have hJopen := hwc.isOpen_inter_preimage hI.1 hext.isOpen
  have hJ0 : (0 : ℝ) ∈ I ∩ (fun t => restrictToPositiveEdges (γ t)) ⁻¹' Ω := ⟨hI.2.2, hw⟩
  have hconf : ∀ t ∈ I, γ t ∈ fieldSpace L n k j := fun t ht => hmapsγ ht
  have hin : ∀ t ∈ I ∩ (fun t => restrictToPositiveEdges (γ t)) ⁻¹' Ω, γ t ∈ 𝒲 := by
    intro t ht
    have hG : restrictToPositiveEdges (γ t) ∈ specialUnitaryPower (PositiveEdge L n k j) :=
      fun b => (hconf t ht.1).1 b.1 (mem_univ _)
    have h := (hext.eq _ ht.2 hG).1
    rwa [fieldOfPositiveValues_restrict (hconf t ht.1)] at h
  have hgval : ∀ t ∈ I ∩ (fun t => restrictToPositiveEdges (γ t)) ⁻¹' Ω,
      g (restrictToPositiveEdges (γ t)) = restrictToPositiveEdges (m (γ t)) := by
    intro t ht
    have hG : restrictToPositiveEdges (γ t) ∈ specialUnitaryPower (PositiveEdge L n k j) :=
      fun b => (hconf t ht.1).1 b.1 (mem_univ _)
    have h := (hext.eq _ ht.2 hG).2
    rwa [fieldOfPositiveValues_restrict (hconf t ht.1)] at h
  refine ⟨_, hJopen.mem_nhds hJ0, fun t ht => ⟨hin t ht, ?_⟩,
    fun B hB => ⟨fun t ht => ?_, ?_⟩⟩
  · exact leftDifferentialIsLinear_of_extension hl hl' hlogs hmaps hext (hconf t ht.1) ht.2
  · exact leftDifferential_mem hl hl' hlogs hmaps hext (hconf t ht.1) ht.2 hB
  · intro c
    have hwJ := hwc.mono
      (inter_subset_left (t := (fun t => restrictToPositiveEdges (γ t)) ⁻¹' Ω))
    have hmapsJ : MapsTo (fun t => restrictToPositiveEdges (γ t))
        (I ∩ (fun t => restrictToPositiveEdges (γ t)) ⁻¹' Ω) Ω := fun t ht => ht.2
    have hfd : ContinuousOn (fderiv ℝ g) Ω :=
      hext.smooth.continuousOn_fderiv_of_isOpen hext.isOpen (by simp)
    have h1 := hfd.comp hwJ hmapsJ
    have h2 : ContinuousOn (fun t => leftTangentMap (γ t) B)
        (I ∩ (fun t => restrictToPositiveEdges (γ t)) ⁻¹' Ω) :=
      continuousOn_pi.2 fun b =>
        continuousOn_const.mul ((continuous_apply b).comp_continuousOn hwJ)
    have h3 := h1.clm_apply h2
    have h4 := (continuous_apply c).comp_continuousOn h3
    have h5 := continuous_star.comp_continuousOn ((continuous_apply c).comp_continuousOn
      (hext.smooth.continuousOn.comp hwJ hmapsJ))
    have h6 : ContinuousOn (fun t => Complex.I⁻¹ •
        (fderiv ℝ g (restrictToPositiveEdges (γ t)) (leftTangentMap (γ t) B) c *
          star (g (restrictToPositiveEdges (γ t)) c)))
        (I ∩ (fun t => restrictToPositiveEdges (γ t)) ⁻¹' Ω) :=
      (h4.mul h5).const_smul Complex.I⁻¹
    refine h6.congr fun t ht => ?_
    have hGt : m (γ t) c.1 ∈ PeriodicLattice.compactGaugeGroup :=
      (hmaps (hin t ht)).1 c.1 (mem_univ _)
    have hv : g (restrictToPositiveEdges (γ t)) c = m (γ t) c.1 := congrFun (hgval t ht) c
    rw [(leftDifferential_facts hl hlogs hmaps hext (hconf t ht.1) ht.2 hB c).2.2.1,
      inv_eq_star_of_mem hGt]
    beta_reduce
    rw [hv]
end Lattice
private theorem not_opposite_positive {L n k j : ℕ}
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
section Requirements
variable {L n k j j' : ℕ}
private theorem chart_facts_of_function (hS : PowerExpCharts.ExpChartsStatement)
    (hl : EdgeFacts L n k j) [iP : Fintype (PositiveEdge L n k j)]
    {𝒲 : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℂ}
    (hF : IsAnalyticComplexFieldFunction 𝒲 F) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒲 ∧
      HasChartPowerSeries (restrictToPositiveEdges '' 𝒲) (fun w => F (fieldOfPositiveValues w)) ∧
      EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower (PositiveEdge L n k j))
        (restrictToPositiveEdges '' 𝒲) (fun w => F (fieldOfPositiveValues w)) ∧
      EmbeddedSubmanifold.HasDifferentiablePartialsOn (specialUnitaryPower (PositiveEdge L n k j))
        (restrictToPositiveEdges '' 𝒲) (fun w => F (fieldOfPositiveValues w)) := by
  obtain ⟨hopen, f₁, hra⟩ := hF
  obtain rfl : f₁ = iP := Subsingleton.elim _ _
  have := hl.nonempty
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  have hread := ((hS (PositiveEdge L n k j) (PositiveEdge L n k j)).2.2.2.2.2.2.2 β).1
  have hconf : ∀ {U}, U ∈ 𝒲 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => fieldOfPositiveValues_restrict (hopen.1 hU)
  have hrest : IsLocallyHolomorphicRestriction (HolomorphicScalar β) id
      (restrictToPositiveEdges '' 𝒲) (fun w => F (fieldOfPositiveValues w)) := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒲} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒲
      rw [hconf hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Φ, hΦ, heq⟩ := hra.2 _ hq
    refine ⟨𝒳, fun q => Φ q 0, hp𝒳, holomorphicScalar_of_coords (hΦ β), ?_⟩
    rintro _ ⟨U', hU', rfl⟩ hx
    have hval := heq ⟨hx, (Submodule.mem_bot ℝ).2 (funext fun e => e.elim),
      fun c => (hopen.1 hU').1 c (mem_univ _)⟩
    exact congrFun hval 0
  obtain ⟨h1, h2, h3⟩ := ((hread _ hopen.2).2.1 _ hrest)
  exact ⟨hopen, h1, h2, h3⟩
private theorem chart_facts_of_map (hS : PowerExpCharts.ExpChartsStatement)
    (hl : EdgeFacts L n k j) (hl' : EdgeFacts L n k j')
    [iP : Fintype (PositiveEdge L n k j)] [iP' : Fintype (PositiveEdge L n k j')]
    {𝒲 : Set (Edge L n k j → ComplexMatrix2)}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (hm : IsAnalyticFieldMap 𝒲 m) :
    HasChartPowerSeries (restrictToPositiveEdges '' 𝒲)
        (fun w => restrictToPositiveEdges (m (fieldOfPositiveValues w))) ∧
      specialUnitaryPower.IsDifferentiableInto (restrictToPositiveEdges '' 𝒲)
        (fun w => restrictToPositiveEdges (m (fieldOfPositiveValues w))) := by
  obtain ⟨hopen, hmaps, f₁, f₂, hra⟩ := hm
  obtain rfl : f₁ = iP := Subsingleton.elim _ _
  obtain rfl : f₂ = iP' := Subsingleton.elim _ _
  have := hl.nonempty
  have := hl'.nonempty
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  have hread := ((hS (PositiveEdge L n k j) (PositiveEdge L n k j')).2.2.2.2.2.2.2 β).1
  have hconf : ∀ {U}, U ∈ 𝒲 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => fieldOfPositiveValues_restrict (hopen.1 hU)
  have hinto : MapsTo (fun w => restrictToPositiveEdges (m (fieldOfPositiveValues w)))
      (restrictToPositiveEdges '' 𝒲) (specialUnitaryPower (PositiveEdge L n k j')) := by
    rintro _ ⟨U, hU, rfl⟩
    show restrictToPositiveEdges (m (fieldOfPositiveValues (restrictToPositiveEdges U))) ∈ _
    rw [hconf hU]
    exact fun c => (hmaps hU).1 c (mem_univ _)
  have hrest : IsLocallyHolomorphicRestriction (IsHolomorphicToProduct β) asGroupFactors
      (restrictToPositiveEdges '' 𝒲)
      (fun w => restrictToPositiveEdges (m (fieldOfPositiveValues w))) := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒲} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒲
      rw [hconf hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Ψ, hΨ, heq⟩ := hra.2.2.2 _ hq
    refine ⟨𝒳, Ψ, hp𝒳, hΨ β, ?_⟩
    rintro _ ⟨V, hV, rfl⟩ hx
    refine heq ⟨hx, ?_, ?_⟩
    · exact (Submodule.mem_bot ℝ).2 (funext fun e => e.elim)
    · exact fun c => (hopen.1 hV).1 c (mem_univ _)
  exact (hread _ hopen.2).2.2.2 _ hinto hrest
private theorem analyticFnsSmooth_of_charts (hS : PowerExpCharts.ExpChartsStatement)
    (hl : EdgeFacts L n k j) (𝒲 : Set (Edge L n k j → ComplexMatrix2)) :
    AnalyticFnsSmooth 𝒲 := by
  intro F hF
  obtain ⟨-, f₁, -⟩ := id hF
  let := f₁
  have := hl.nonempty
  obtain ⟨hopen, hser, hdiff, htwice⟩ := chart_facts_of_function hS hl hF
  have hC := (hS (PositiveEdge L n k j) (PositiveEdge L n k j)).1
  refine ⟨⟨hopen, f₁, hopen.2, hser.2⟩, ⟨hopen, f₁, hdiff⟩, ⟨hopen, f₁, htwice⟩,
    fun V hV => ?_⟩
  obtain ⟨Ω, g, hw, hext⟩ := exists_smoothExtensionOn hC hopen hser hV
  exact ⟨hasLeftGradientAt_of_extension hl hext (hopen.1 hV) hw,
    hasLeftSecondDerivAt_of_series hC hser hV (hopen.1 hV)⟩
private theorem analyticMapsSmooth_of_charts (hS : PowerExpCharts.ExpChartsStatement)
    (hl : EdgeFacts L n k j) (hl' : EdgeFacts L n k j')
    (hlogs : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra)
    (𝒲 : Set (Edge L n k j → ComplexMatrix2)) : AnalyticMapsSmooth j' 𝒲 := by
  intro F hF
  obtain ⟨hopen, hmaps, f₁, f₂, -⟩ := id hF
  let := f₁
  let := f₂
  have := hl.nonempty
  have := hl'.nonempty
  obtain ⟨hser, hdiff⟩ := chart_facts_of_map hS hl hl' hF
  have hC := (hS (PositiveEdge L n k j) (PositiveEdge L n k j)).1
  refine ⟨⟨hopen, hmaps, f₁, f₂, hopen.2, hser.2⟩, ⟨hopen, hmaps, f₁, f₂, hdiff⟩,
    fun V hV => ?_⟩
  obtain ⟨Ω, g, hw, hext⟩ :=
    exists_smoothExtensionOn hC hopen (h := fun V => restrictToPositiveEdges (F V)) hser hV
  refine ⟨fun B hB c hc => ?_,
    leftDifferentialIsLinear_of_extension hl hl' hlogs hmaps hext (hopen.1 hV) hw⟩
  obtain ⟨h1, h2, -, -⟩ :=
    leftDifferential_facts hl hlogs hmaps hext (hopen.1 hV) hw hB ⟨c, hc⟩
  exact ⟨h1, h2⟩
private theorem along_curve_facts_of_map (hS : PowerExpCharts.ExpChartsStatement)
    (hl : EdgeFacts L n k j) (hl' : EdgeFacts L n k j')
    (hlogs : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra)
    [Fintype (PositiveEdge L n k j)] [Fintype (PositiveEdge L n k j')]
    {𝒲 : Set (Edge L n k j → ComplexMatrix2)}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (hm : IsAnalyticFieldMap 𝒲 m) {I : Set ℝ} {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsContinuousCurveStartingIn 𝒲 I γ) :
    ∃ J ∈ 𝓝 (0 : ℝ), (∀ t ∈ J, γ t ∈ 𝒲 ∧ LeftDifferentialIsLinear m (γ t)) ∧
      ∀ B ∈ edgeFormSpace L n k j,
        (∀ t ∈ J, leftDifferential m (γ t) B ∈ edgeFormSpace L n k j') ∧
        ∀ c : PositiveEdge L n k j',
          ContinuousOn (fun t => leftDifferential m (γ t) B c.1) J := by
  obtain ⟨hopen, hmaps, -, -, -⟩ := id hm
  have := hl.nonempty
  have hser := (chart_facts_of_map hS hl hl' hm).1
  have hC := (hS (PositiveEdge L n k j) (PositiveEdge L n k j)).1
  obtain ⟨Ω, g, hw, hext⟩ :=
    exists_smoothExtensionOn hC hopen (h := fun V => restrictToPositiveEdges (m V)) hser hγ.2.2.1
  exact along_curve_facts hl hl' hlogs hmaps hext hγ hw
private theorem differentialContinuous_of_charts (hS : PowerExpCharts.ExpChartsStatement)
    (hl : EdgeFacts L n k j) (hl' : EdgeFacts L n k j')
    (hlogs : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra)
    (𝒲 : Set (Edge L n k j → ComplexMatrix2)) : DifferentialContinuousAlongCurves j' 𝒲 := by
  intro 𝔭 I γ hm hγ
  obtain ⟨-, -, f₁, f₂, -⟩ := id hm
  let := f₁
  let := f₂
  obtain ⟨J, hJ, hJ𝒲, hforms⟩ := along_curve_facts_of_map hS hl hl' hlogs hm hγ
  refine ⟨mem_of_superset hJ fun t ht => (hJ𝒲 t ht).1, fun B hB => ⟨J, hJ, fun i => ?_⟩⟩
  refine ContinuousOn.congr (Complex.continuous_re.comp_continuousOn
    ((continuous_pauliCoeff i.2).comp_continuousOn ((hforms B hB).2 i.1))) fun t ht => ?_
  exact colorCoords_eq hl' ((hforms B hB).1 t ht) i
private theorem transposeDifferentiable_of_charts (hS : PowerExpCharts.ExpChartsStatement)
    (hT : RealTransposeEdgeFormPairing) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) (hj' : j' ≤ k)
    (hl : EdgeFacts L n k j) (hl' : EdgeFacts L n k j')
    (hlogs : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra)
    (𝒲 : Set (Edge L n k j → ComplexMatrix2)) : TransposeDifferentiableAlongCurves j' 𝒲 := by
  intro 𝔭 I γ χ χ' hm hγ hχ0 hχ
  obtain ⟨-, -, f₁, f₂, -⟩ := id hm
  let := f₁
  let := f₂
  obtain ⟨J, hJ, hJ𝒲, hforms⟩ := along_curve_facts_of_map hS hl hl' hlogs hm hγ
  have hJ0 : (0 : ℝ) ∈ J := mem_of_mem_nhds hJ
  have hpair : ∀ (t : ℝ) (g' : edgeFormSpace L n k j') (B : edgeFormSpace L n k j),
      edgeFormPairing (leftDifferentialTranspose 𝔭 (γ t) g' : Edge L n k j → ComplexMatrix2)
          (B : Edge L n k j → ComplexMatrix2) =
        edgeFormPairing (g' : Edge L n k j' → ComplexMatrix2)
          (leftDifferentialLinear 𝔭 (γ t) B : Edge L n k j' → ComplexMatrix2) :=
    fun t g' B => hT L n k j j' hL hn hj hj' _ g' B
  refine ⟨mem_of_superset hJ fun t ht => ⟨(hJ𝒲 t ht).2, fun B => hpair t (χ t) B⟩, ?_⟩
  have hpos : ∀ b : PositiveEdge L n k j, HasDerivAt
      (fun t => (leftDifferentialTranspose 𝔭 (γ t) (χ t) : Edge L n k j → ComplexMatrix2) b.1)
      ((leftDifferentialTranspose 𝔭 (γ 0) χ' : Edge L n k j → ComplexMatrix2) b.1) 0 := by
    intro b
    have he : ∀ a, pauliBasisForm b a ∈ edgeFormSpace L n k j := pauliBasisForm_mem hl b
    have hz : ∀ a, HasDerivAt
        (fun t => edgeFormPairing (χ t : Edge L n k j' → ComplexMatrix2)
          (leftDifferential 𝔭 (γ t) (pauliBasisForm b a)))
        (edgeFormPairing (χ' : Edge L n k j' → ComplexMatrix2)
          (leftDifferential 𝔭 (γ 0) (pauliBasisForm b a))) 0 := by
      intro a
      simp only [edgeFormPairing_eq_sum]
      refine HasDerivAt.fun_sum fun c _ => ?_
      have h0 : (χ 0 : Edge L n k j' → ComplexMatrix2) c.1 = 0 := by
        rw [hχ0]
        rfl
      exact halfTraceCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (hasDerivAt_mul_of_vanishing h0 (hχ c.1)
          (((hforms _ (he a)).2 c).continuousAt hJ))
    have hmain : HasDerivAt
        (fun t => ∑ a, edgeFormPairing (χ t : Edge L n k j' → ComplexMatrix2)
          (leftDifferential 𝔭 (γ t) (pauliBasisForm b a)) • ComplexMatrix2.pauliFamily a)
        (∑ a, edgeFormPairing (χ' : Edge L n k j' → ComplexMatrix2)
          (leftDifferential 𝔭 (γ 0) (pauliBasisForm b a)) • ComplexMatrix2.pauliFamily a) 0 :=
      HasDerivAt.fun_sum fun a _ => (hz a).smul_const _
    have hval : ∀ Z : edgeFormSpace L n k j, (Z : Edge L n k j → ComplexMatrix2) b.1 =
        ∑ a, edgeFormPairing (Z : Edge L n k j → ComplexMatrix2) (pauliBasisForm b a) •
          ComplexMatrix2.pauliFamily a := by
      intro Z
      simp only [edgeFormPairing_pauliBasisForm]
      exact eq_sum_pauliCoeff (Z.2.1 b.1 b.2).2
    have hT' : ∀ t ∈ J, ∀ g' : edgeFormSpace L n k j',
        (leftDifferentialTranspose 𝔭 (γ t) g' : Edge L n k j → ComplexMatrix2) b.1 =
          ∑ a, edgeFormPairing (g' : Edge L n k j' → ComplexMatrix2)
            (leftDifferential 𝔭 (γ t) (pauliBasisForm b a)) • ComplexMatrix2.pauliFamily a := by
      intro t ht g'
      rw [hval]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h1 := hpair t g' ⟨_, he a⟩
      have h2 := (hJ𝒲 t ht).2 ⟨_, he a⟩
      rw [h2] at h1
      rw [show edgeFormPairing
        (leftDifferentialTranspose 𝔭 (γ t) g' : Edge L n k j → ComplexMatrix2)
        (pauliBasisForm b a) = _ from h1]
    rw [hT' 0 hJ0 χ']
    exact hmain.congr_of_eventuallyEq (mem_of_superset hJ fun t ht => hT' t ht (χ t))
  intro b
  by_cases hb : b.IsPositivelyOriented
  · exact hpos ⟨b, hb⟩
  · have hr := (positive_or_opposite_positive b).resolve_left hb
    have hform : ∀ Z : edgeFormSpace L n k j, (Z : Edge L n k j → ComplexMatrix2) b =
        -(Z : Edge L n k j → ComplexMatrix2) b.opposite := by
      intro Z
      have h := Z.2.2 b.opposite
      rwa [opposite_opposite] at h
    rw [hform]
    exact (hpos ⟨b.opposite, hr⟩).neg.congr_of_eventuallyEq
      (Eventually.of_forall fun t => hform _)
end Requirements
theorem analyticMapsDifferentiable_of_charts (hS : PowerExpCharts.ExpChartsStatement)
    (hU : LeftChartFields.Claim)
    (hB : BondSetFields.ProductStructureHolds)
    (hT : RealTransposeEdgeFormPairing)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties) : AnalyticMapsDifferentiable := by
  intro L n k j j' hL hn hj hj' 𝒲 _
  have edgeFacts : ∀ i, i ≤ k → EdgeFacts L n k i := by
    intro i hi
    refine ⟨fun b hb => not_opposite_positive hA hL hn hi b hb,
      ((hU.2.2 L k i hL hi).1 n hn).1.1, ?_⟩
    obtain ⟨-, ⟨b, -⟩, -⟩ := ((hB L hL k i hi).1 n hn).2
    rcases positive_or_opposite_positive b with h | h
    · exact ⟨⟨b, h⟩⟩
    · exact ⟨⟨b.opposite, h⟩⟩
  have hl := edgeFacts j hj
  have hl' := edgeFacts j' hj'
  have hlogs : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra :=
    fun I hI => (hU.1 I hI).1
  exact ⟨analyticFnsSmooth_of_charts hS hl 𝒲, analyticMapsSmooth_of_charts hS hl hl' hlogs 𝒲,
    differentialContinuous_of_charts hS hl hl' hlogs 𝒲,
    transposeDifferentiable_of_charts hS hT hL hn hj hj' hl hl' hlogs 𝒲⟩
end YangMills.Construction.Tower.AnalyticDifferentials
end
