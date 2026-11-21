import YangMills.Construction.Towers.DerivativeOfTheContourLogarithmAlongCurvesProof
import YangMills.Construction.Towers.GaugeFixingFunctionAsASumOfCosinesProof
import YangMills.Construction.Towers.GaugeFixingFunctionIsRealAnalyticNearOne
import YangMills.Construction.Towers.PropertiesOfTheGaugeFixingFunctions
import YangMills.Construction.Towers.RealAnalyticFunctionsAlongTwiceDifferentiableCurves
import YangMills.Construction.Towers.TrivialConfigurationAtAStep
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower
namespace AxialFunctionFacts
private theorem tendsto_one_sub_cos_div_sq {y : ℝ → ℝ} {d : ℝ} (hy0 : Tendsto y (𝓝[≠] 0) (𝓝 0))
    (hyd : Tendsto (fun t => y t / |t|) (𝓝[≠] 0) (𝓝 d)) :
    Tendsto (fun t => (1 - Real.cos (y t)) / t ^ 2) (𝓝[≠] 0) (𝓝 (d ^ 2 / 2)) := by
  have hquad : Tendsto (fun t => (y t / |t|) ^ 2 / 2) (𝓝[≠] 0) (𝓝 (d ^ 2 / 2)) :=
    (hyd.pow 2).div_const 2
  have hdom : Tendsto (fun t => (5 / 96 : ℝ) * ((y t / |t|) ^ 2 * y t ^ 2)) (𝓝[≠] 0) (𝓝 0) := by
    have := ((hyd.pow 2).mul (hy0.pow 2)).const_mul (5 / 96 : ℝ)
    simpa using this
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |y t| ≤ 1 := by
    have : ∀ᶠ t in 𝓝[≠] (0 : ℝ), y t ∈ Metric.closedBall (0 : ℝ) 1 :=
      hy0.eventually (Metric.closedBall_mem_nhds _ one_pos)
    filter_upwards [this] with t ht
    simpa [Metric.mem_closedBall] using ht
  have herr : Tendsto (fun t => (1 - Real.cos (y t)) / t ^ 2 - (y t / |t|) ^ 2 / 2) (𝓝[≠] 0)
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hdom
    filter_upwards [hsmall, self_mem_nhdsWithin] with t ht ht0
    have hcos := Real.cos_bound ht
    have htne : t ≠ 0 := ht0
    have hpos : 0 < t ^ 2 := by positivity
    have hrw : (1 - Real.cos (y t)) / t ^ 2 - (y t / |t|) ^ 2 / 2 =
        -(Real.cos (y t) - (1 - y t ^ 2 / 2)) / t ^ 2 := by
      rw [div_pow, sq_abs]
      field_simp
      ring
    have hfour : |y t| ^ 4 = y t ^ 4 := by
      have : |y t| ^ 4 = (|y t| ^ 2) ^ 2 := by ring
      rw [this, sq_abs]
      ring
    have hmul : (5 / 96 : ℝ) * ((y t / |t|) ^ 2 * y t ^ 2) * t ^ 2 = |y t| ^ 4 * (5 / 96) := by
      rw [hfour, div_pow, sq_abs]
      field_simp
    rw [hrw, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos, hmul]
    exact hcos
  simpa using herr.add hquad
private theorem tendsto_div_sq_of_deriv_zero {F : ℝ → ℝ} (hF0 : F 0 = 0)
    (hdF : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ F t) (hF1 : deriv F 0 = 0)
    (hF2 : DifferentiableAt ℝ (deriv F) 0) :
    Tendsto (fun t => F t / t ^ 2) (𝓝[≠] 0) (𝓝 (deriv (deriv F) 0 / 2)) := by
  have hFlim : Tendsto F (𝓝[≠] 0) (𝓝 0) := by
    have := hdF.self_of_nhds.continuousAt.tendsto
    rw [hF0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) :=
      (continuous_pow 2).continuousAt.tendsto
    simpa using this.mono_left nhdsWithin_le_nhds
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hF2.hasDerivAt
  have hquot : Tendsto (fun t => deriv F t / (2 * t)) (𝓝[≠] 0) (𝓝 (deriv (deriv F) 0 / 2)) := by
    refine (hslope.div_const 2).congr fun t => ?_
    simp only [zero_add, hF1, sub_zero, smul_eq_mul]
    rw [mul_comm 2 t, div_mul_eq_div_div_swap, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  refine HasDerivAt.lhopital_zero_nhdsNE (f' := deriv F) (g' := fun t => 2 * t) ?_ ?_ ?_ hFlim hsq
    hquot
  · filter_upwards [nhdsWithin_le_nhds hdF] with t ht
    exact ht.hasDerivAt
  · refine Eventually.of_forall fun t => ?_
    simpa using hasDerivAt_pow 2 t
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero two_ne_zero ht
private theorem halfTrace_mul_self (hP : OneLoop.PauliMatrixRelations) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.halfTrace (X * X) = ((ComplexMatrix2.operatorNorm X ^ 2 : ℝ) : ℂ) := by
  obtain ⟨-, -, -, -, -, -, -, hnorm, -⟩ := hP
  have := hnorm ⟨X, hX.2⟩ hX
  exact this.symm
private theorem traceFinsumPairing_self (hP : OneLoop.PauliMatrixRelations) {ι : Type*}
    [Fintype ι] {f : ι → ComplexMatrix2} (hf : ∀ j, f j ∈ ComplexMatrix2.hermitianTraceless) :
    traceFinsumPairing f f = ((∑ j, ComplexMatrix2.operatorNorm (f j) ^ 2 : ℝ) : ℂ) := by
  rw [traceFinsumPairing, finsum_eq_sum_of_fintype, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ => halfTrace_mul_self hP (hf j)
variable {L n k i : ℕ}
private theorem isPositive_or_opposite (b : Edge L n k i) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem fieldOfPositiveValues_restrict {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k i) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem mem_nhdsWithin_of_isOpenFieldSet {𝒰 : Set (Edge L n k i → ComplexMatrix2)}
    (h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ 𝒰) : 𝒰 ∈ 𝓝[fieldSpace L n k i] V := by
  obtain ⟨hsub, O, hO, himg⟩ := h𝒰
  have hcont : Continuous
      (restrictToPositiveEdges : (Edge L n k i → ComplexMatrix2) → PositiveEdge L n k i →
        ComplexMatrix2) :=
    continuous_pi fun _ => continuous_apply _
  have hVO : restrictToPositiveEdges V ∈ O := by
    have : restrictToPositiveEdges V ∈ restrictToPositiveEdges '' 𝒰 := mem_image_of_mem _ hV
    rw [himg] at this
    exact this.1
  have hOev : ∀ᶠ W in 𝓝 V, restrictToPositiveEdges W ∈ O :=
    hcont.continuousAt.eventually_mem (hO.mem_nhds hVO)
  filter_upwards [nhdsWithin_le_nhds hOev, self_mem_nhdsWithin] with W hW₁ hW₂
  have hmem : restrictToPositiveEdges W ∈ restrictToPositiveEdges '' 𝒰 := by
    rw [himg]
    exact ⟨hW₁, fun b => hW₂.1 _ (mem_univ _)⟩
  obtain ⟨W', hW', hWeq⟩ := hmem
  have : W' = W := by
    rw [← fieldOfPositiveValues_restrict (hsub hW'), hWeq, fieldOfPositiveValues_restrict hW₂]
  exact this ▸ hW'
abbrev _root_.YangMills.SharedProofs.p46903 := @mem_nhdsWithin_of_isOpenFieldSet
private theorem tendsto_fieldCurve {I : Set ℝ} {γ : ℝ → Edge L n k i → ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ) :
    Tendsto γ (𝓝 0) (𝓝[fieldSpace L n k i] γ 0) := by
  have hI : I ∈ 𝓝 (0 : ℝ) := hγ.1.1.mem_nhds hγ.1.2.2
  have hfield : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ fieldSpace L n k i := by
    filter_upwards [hI] with t ht
    exact hγ.2.1 ht
  have hpos : ∀ b : Edge L n k i, b.IsPositivelyOriented →
      ContinuousAt (fun t => γ t b) 0 := fun b hb =>
    ((hγ.2.2 b hb 0 hγ.1.2.2).differentiableAt hI).continuousAt
  refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_pi_nhds.mpr fun b => ?_, hfield⟩
  by_cases h : b.IsPositivelyOriented
  · exact (hpos b h).tendsto
  · have h' := (isPositive_or_opposite b).resolve_left h
    have hopp : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
    have hstar : ∀ t, γ t ∈ fieldSpace L n k i →
        γ t b = (γ t b.opposite).conjTranspose := by
      intro t ht
      have hinv := ht.2 b.opposite (mem_univ _)
      rw [hopp] at hinv
      have hu := (Matrix.mem_specialUnitaryGroup_iff.mp (ht.1 b.opposite (mem_univ _))).1
      rw [hinv]
      exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hu)
    have hc : ContinuousAt (fun t => (γ t b.opposite).conjTranspose) 0 :=
      ((continuous_id.matrix_conjTranspose).continuousAt).comp (hpos _ h')
    have hlim := hc.tendsto
    rw [← hstar 0 (hfield.self_of_nhds)] at hlim
    refine hlim.congr' ?_
    filter_upwards [hfield] with t hft
    exact (hstar t hft).symm
private def expCurve (V B : Edge L n k i → ComplexMatrix2) (t : ℝ) :
    Edge L n k i → ComplexMatrix2 :=
  PeriodicLattice.expTwist ((t : ℂ) • B) V
private theorem expCurve_zero {V : Edge L n k i → ComplexMatrix2} (B : Edge L n k i → ComplexMatrix2)
    (hV : V ∈ fieldSpace L n k i) : expCurve V B 0 = V := by apply _root_.YangMills.DeltaSharedProofs.p500778 <;> assumption
private theorem expCurve_of_positive (V B : Edge L n k i → ComplexMatrix2) {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) (t : ℝ) :
    expCurve V B t b = ComplexMatrix2.matExp (t • (Complex.I • B b)) * V b := by
  have : Complex.I • ((t : ℂ) • B) b = t • (Complex.I • B b) := by
    rw [Pi.smul_apply, Complex.coe_smul, smul_comm]
  simp only [expCurve, PeriodicLattice.expTwist, if_pos hb, this]
private theorem hasDerivAt_expCurve (V B : Edge L n k i → ComplexMatrix2) {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) (t : ℝ) :
    HasDerivAt (fun s => expCurve V B s b)
      (ComplexMatrix2.matExp (t • (Complex.I • B b)) * (Complex.I • B b) * V b) t := by
  have hE : HasDerivAt (fun s : ℝ => ComplexMatrix2.matExp (s • (Complex.I • B b)))
      (ComplexMatrix2.matExp (t • (Complex.I • B b)) * (Complex.I • B b)) t :=
    hasDerivAt_exp_smul_const (Complex.I • B b) t
  have hEV := hE.mul_const (V b)
  exact hEV.congr_of_eventuallyEq (Eventually.of_forall fun s => expCurve_of_positive V B hb s)
private theorem curveTangent_expCurve {V B : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k i) (hB : B ∈ edgeFormSpace L n k i) :
    curveTangent (expCurve V B) = B := by
  have hpos : ∀ b : Edge L n k i, b.IsPositivelyOriented →
      Complex.I⁻¹ • (deriv (fun t => expCurve V B t b) 0 * (expCurve V B 0 b)⁻¹) = B b := by
    intro b hb
    have hu : IsUnit (V b).det := by
      have := (Matrix.mem_specialUnitaryGroup_iff.mp (hV.1 b (mem_univ _))).2
      rw [this]
      exact isUnit_one
    rw [(hasDerivAt_expCurve V B hb 0).deriv, expCurve_zero B hV, zero_smul]
    have hexp : ComplexMatrix2.matExp (0 : ComplexMatrix2) = 1 := by simp [ComplexMatrix2.matExp]
    rw [hexp, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hu, mul_one, smul_smul,
      inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  funext b
  by_cases h : b.IsPositivelyOriented
  · simp only [curveTangent, extendOddly, if_pos h]
    exact hpos b h
  · have h' := (isPositive_or_opposite b).resolve_left h
    simp only [curveTangent, extendOddly, if_neg h]
    rw [hpos _ h', hB.2 b, neg_neg]
private theorem expCurve_isTwiceDiff {V B : Edge L n k i → ComplexMatrix2}
    (hmem : ∀ t : ℝ, expCurve V B t ∈ fieldSpace L n k i) :
    (fieldCurveData L n k i).IsTwiceDiffCurve univ (expCurve V B) := by
  refine ⟨⟨⟨isOpen_univ, ordConnected_univ, mem_univ _⟩, fun t _ => hmem t, fun b hb t _ =>
    (hasDerivAt_expCurve V B hb t).differentiableAt.differentiableWithinAt⟩, fun b hb t _ => ?_⟩
  have hd : deriv (fun s => expCurve V B s b) =
      fun s : ℝ => ComplexMatrix2.matExp (s • (Complex.I • B b)) * (Complex.I • B b) * V b :=
    funext fun s => (hasDerivAt_expCurve V B hb s).deriv
  rw [hd]
  have hE : HasDerivAt (fun s : ℝ => ComplexMatrix2.matExp (s • (Complex.I • B b)))
      (ComplexMatrix2.matExp (t • (Complex.I • B b)) * (Complex.I • B b)) t :=
    hasDerivAt_exp_smul_const (Complex.I • B b) t
  exact ((hE.mul_const _).mul_const _).differentiableAt.differentiableWithinAt
private def CosineSumFacts (L n k i : ℕ) (W : Edge L n k i → ComplexMatrix2) : Prop :=
  W ∈ axialFunctionDomain L n k i ∧
    (∀ x, contourLog L n k i W x ∈ ComplexMatrix2.hermitianTraceless) ∧
    axialFunction L n k i W =
      ∑ᶠ x, (1 - Real.cos (ComplexMatrix2.operatorNorm (contourLog L n k i W x))) ∧
    0 ≤ axialFunction L n k i W ∧
    (axialFunction L n k i W = 0 ↔ IsAxialGaugeAt L n k i W)
private def LogDerivFacts (L n k i : ℕ) (V : Edge L n k i → ComplexMatrix2) : Prop :=
  ∀ (I : Set ℝ) (γ : ℝ → Edge L n k i → ComplexMatrix2),
    IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ → γ 0 = V →
      ∀ x : FineOnlyVertex L n k i,
        HasDerivAt
          (fun t => Complex.I⁻¹ •
            ComplexMatrix2.logSeries
              (PeriodicLattice.meanContourHolonomy (γ t) (cubeCentre x) x.1))
          (contourLogDeriv L n k i V (curveTangent γ) x) 0 ∧
        contourLogDeriv L n k i V (curveTangent γ) x ∈ ComplexMatrix2.hermitianTraceless
private theorem cubeCentre_spec (hZ : BlocksPartitionFiner L n k (i + 1))
    (x : FineOnlyVertex L n k i) :
    x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) (cubeCentre x) ∧
      (x.1 : PeriodicLattice.FourTorus L n) ≠ cubeCentre x := by apply _root_.YangMills.SharedProofs.p27590 <;> assumption
private theorem contourLog_eq_zero_of_axial (hZ : BlocksPartitionFiner L n k (i + 1))
    {V : Edge L n k i → ComplexMatrix2} (hax : IsAxialGaugeAt L n k i V)
    (x : FineOnlyVertex L n k i) :
    contourLog L n k i V x = 0 := by
  have hs := cubeCentre_spec hZ x
  have h1 : PeriodicLattice.meanContourHolonomy V (cubeCentre x) x.1 = 1 :=
    hax.2 _ (mem_univ _) x.1 hs.1 hs.2
  simp [contourLog, h1, ComplexMatrix2.logSeries]
private theorem axialFunction_along_curve (hP : OneLoop.PauliMatrixRelations)
    (hZ : BlocksPartitionFiner L n k (i + 1)) [Finite (FineOnlyVertex L n k i)]
    {V : Edge L n k i → ComplexMatrix2}
    (hnear : ∀ᶠ W in 𝓝[fieldSpace L n k i] V, CosineSumFacts L n k i W)
    (hfirst : LogDerivFacts L n k i V) (hax : IsAxialGaugeAt L n k i V)
    {I : Set ℝ} {γ : ℝ → Edge L n k i → ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ) (h0 : γ 0 = V)
    (hdiff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun s => axialFunction L n k i (γ s)) t)
    (hdiff2 : DifferentiableAt ℝ (deriv fun s => axialFunction L n k i (γ s)) 0) :
    HasDerivAt (fun s => axialFunction L n k i (γ s)) 0 0 ∧
      deriv (deriv fun s => axialFunction L n k i (γ s)) 0 =
        traceFinsumNorm (contourLogDeriv L n k i V (curveTangent γ)) ^ 2 := by
  classical
  have := Fintype.ofFinite (FineOnlyVertex L n k i)
  set F : ℝ → ℝ := fun s => axialFunction L n k i (γ s) with hFdef
  set D := contourLogDeriv L n k i V (curveTangent γ) with hDdef
  have hT : Tendsto γ (𝓝 0) (𝓝[fieldSpace L n k i] V) := h0 ▸ tendsto_fieldCurve hγ
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), CosineSumFacts L n k i (γ t) := hT.eventually hnear
  have hF0 : F 0 = 0 := by
    have hat : CosineSumFacts L n k i (γ 0) := hev.self_of_nhds
    exact hat.2.2.2.2.mpr (h0 ▸ hax)
  have hmin : IsLocalMin F 0 := by
    filter_upwards [hev] with t ht
    rw [hF0]
    exact ht.2.2.2.1
  have hF1 : deriv F 0 = 0 := hmin.deriv_eq_zero
  have hlimA := tendsto_div_sq_of_deriv_zero hF0 hdiff hF1 hdiff2
  have hterm : ∀ x : FineOnlyVertex L n k i,
      Tendsto (fun t => (1 - Real.cos (ComplexMatrix2.operatorNorm (contourLog L n k i (γ t) x))) /
        t ^ 2) (𝓝[≠] 0) (𝓝 (ComplexMatrix2.operatorNorm (D x) ^ 2 / 2)) := by
    intro x
    have hder : HasDerivAt (fun t => contourLog L n k i (γ t) x) (D x) 0 :=
      (hfirst I γ hγ h0 x).1
    have hz : contourLog L n k i (γ 0) x = 0 := by
      rw [h0]
      exact contourLog_eq_zero_of_axial hZ hax x
    have hc : Tendsto (fun t => ComplexMatrix2.operatorNorm (contourLog L n k i (γ t) x))
        (𝓝[≠] 0) (𝓝 0) := by
      have := hder.continuousAt.tendsto.norm
      rw [hz, norm_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hs := (hasDerivAt_iff_tendsto_slope_zero.mp hder).norm
    refine tendsto_one_sub_cos_div_sq hc (hs.congr fun t => ?_)
    simp only [zero_add, hz, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [div_eq_inv_mul]
  have hlimB : Tendsto (fun t => F t / t ^ 2) (𝓝[≠] 0)
      (𝓝 (∑ x, ComplexMatrix2.operatorNorm (D x) ^ 2 / 2)) := by
    refine (tendsto_finsetSum Finset.univ fun x _ => hterm x).congr' ?_
    filter_upwards [nhdsWithin_le_nhds hev] with t ht
    rw [hFdef]
    simp only
    rw [ht.2.2.1, finsum_eq_sum_of_fintype, Finset.sum_div]
  have hsu : ∀ x, D x ∈ ComplexMatrix2.hermitianTraceless := fun x => (hfirst I γ hγ h0 x).2
  have hnorm : traceFinsumNorm D ^ 2 = ∑ x, ComplexMatrix2.operatorNorm (D x) ^ 2 := by
    have hnn : 0 ≤ ∑ x, ComplexMatrix2.operatorNorm (D x) ^ 2 :=
      Finset.sum_nonneg fun x _ => by positivity
    rw [traceFinsumNorm, traceFinsumPairing_self hP hsu, Complex.ofReal_re, Real.sq_sqrt hnn]
  refine ⟨?_, ?_⟩
  · have := hdiff.self_of_nhds.hasDerivAt
    rwa [hF1] at this
  · have huniq := tendsto_nhds_unique hlimA hlimB
    rw [hnorm]
    rw [← Finset.sum_div] at huniq
    linarith
end AxialFunctionFacts
open AxialFunctionFacts in
theorem axialFunctionFacts_holds
    (hTrivial : TrivialFieldAtStep)
    (hSum : AxialFunctionCosineSum)
    (hAnalytic : AxialFunctionAnalyticNearOne)
    (hTwice : AnalyticAlongC2CurveStatement)
    (hFirst : ContourLogDerivAlongCurves.Statement)
    (hVal : SmoothingNearTrivialField)
    (hChart : LeftChartFields.Claim)
    (hP : OneLoop.PauliMatrixRelations)
    (hAvg : SmoothingNearIdentity)
    (hBlocks : BlockStructure) :
    AxialFunctionFacts.statement := by
  intro L n k i hL hn hi
  obtain ⟨ht₁, ht₂, ht₃⟩ := hTrivial L n k i hL hn hi
  obtain ⟨hfinOff, hsum⟩ := hSum L n k i hL hn hi
  have hfinPos : Finite (PositiveEdge L n k i) := ((hChart.2.2 L k i hL hi.le).1 n hn).2.1.1
  have hZ : BlocksPartitionFiner L n k (i + 1) :=
    ((hBlocks L k (i + 1) hL (by omega) (by omega) (by omega)).1 n hn).2.1
  obtain ⟨𝒰, hU, hUdom, hRA⟩ := hAnalytic L n k i hL hn hi
  have hfirst : ∀ᶠ V in 𝓝[fieldSpace L n k i] trivialField L n k i,
      LogDerivFacts L n k i V := hFirst L n k i hL hn hi
  have hsum' : ∀ᶠ V in 𝓝[fieldSpace L n k i] trivialField L n k i,
      CosineSumFacts L n k i V := hsum
  have hnear : ∀ᶠ V in 𝓝[fieldSpace L n k i] trivialField L n k i,
      ∀ᶠ W in 𝓝[fieldSpace L n k i] V, CosineSumFacts L n k i W :=
    eventually_eventually_nhdsWithin.mpr hsum'
  have hinU : ∀ᶠ V in 𝓝[fieldSpace L n k i] trivialField L n k i, V ∈ 𝒰 :=
    mem_nhdsWithin_of_isOpenFieldSet hU.1 hU.2
  have hall := hnear.and (hfirst.and (hinU.and self_mem_nhdsWithin))
  have hcurve : ∀ V, (∀ᶠ W in 𝓝[fieldSpace L n k i] V, CosineSumFacts L n k i W) →
      LogDerivFacts L n k i V → V ∈ 𝒰 → V ∈ fieldSpace L n k i → IsAxialGaugeAt L n k i V →
      ∀ (I : Set ℝ) (γ : ℝ → Edge L n k i → ComplexMatrix2),
        (fieldCurveData L n k i).IsTwiceDiffCurve I γ → γ 0 = V →
        HasDerivAt (fun s => axialFunction L n k i (γ s)) 0 0 ∧
          deriv (deriv fun s => axialFunction L n k i (γ s)) 0 =
            traceFinsumNorm (contourLogDeriv L n k i V (curveTangent γ)) ^ 2 := by
    intro V hN hF hVU hV hax I γ hγ h0
    obtain ⟨hd₁, hd₂⟩ := hTwice L n k i hL hn hi.le 𝒰 (axialFunction L n k i) hRA V hVU I γ hγ h0
    exact axialFunction_along_curve hP hZ hN hF hax hγ.1 h0 hd₁ hd₂
  have hmemCurve : ∀ V ∈ fieldSpace L n k i, ∀ B ∈ edgeFormSpace L n k i, ∀ t : ℝ,
      expCurve V B t ∈ fieldSpace L n k i := by
    intro V hV B hB t
    have hreal : ((t : ℂ) • B) = t • B := by
      funext b
      exact Complex.coe_smul t (B b)
    show PeriodicLattice.expTwist ((t : ℂ) • B) V ∈ _
    rw [hreal]
    exact (hVal L n k hL hn (by omega)).2 i hi.le (t • B)
      ((edgeFormSpace L n k i).smul_mem t hB) V hV
  refine
    { meanContourHolonomy_trivial := ht₁
      smoothingStep_trivial := ht₂
      isAxialGaugeAt_trivial := ht₃
      analytic_near_identity := ⟨𝒰, hU, hUdom, hRA⟩
      nonneg := hsum'.mono fun V h => h.2.2.2.1
      eq_zero_iff := hsum'.mono fun V h => h.2.2.2.2
      leftGradient_eq_zero := ?_
      leftSecondDeriv_eq := ?_
      deriv_deriv_along_curve := ?_
      contourLogDeriv_trivial := ?_ }
  · refine hall.mono ?_
    rintro V ⟨hN, hF, hVU, hV⟩ hax
    classical
    have := Fintype.ofFinite (PositiveEdge L n k i)
    set G : (Edge L n k i → ComplexMatrix2) → ℂ := fun W => (axialFunction L n k i W : ℂ) with hG
    have hzero : ∀ B ∈ edgeFormSpace L n k i, leftDeriv G V B = 0 := by
      intro B hB
      have hc := hcurve V hN hF hVU hV hax univ (expCurve V B)
        (expCurve_isTwiceDiff (hmemCurve V hV B hB)) (expCurve_zero B hV)
      have hcomp := hc.1.ofReal_comp
      have h2 := hcomp.deriv
      simpa [leftDeriv, directionalDeriv, expCurve, hG] using h2
    have hgrad0 : IsLeftGradient (fieldSpace L n k i) G V 0 := by
      refine ⟨⟨fun b _ => ComplexMatrix2.traceless.zero_mem, fun b => by simp⟩,
        fun _ => ⟨fun b _ => ComplexMatrix2.hermitianTraceless.zero_mem, fun b => by simp⟩,
        fun B hB _ => ?_⟩
      rw [hzero B hB]
      simp [edgeFormPairing, traceFinsumPairing, restrictToPositiveEdges, ComplexMatrix2.halfTrace,
        ComplexMatrix2.fullTrace]
    have hX := Classical.epsilon_spec (p := IsLeftGradient (fieldSpace L n k i) G V) ⟨0, hgrad0⟩
    change IsLeftGradient (fieldSpace L n k i) G V (leftGradient (fieldSpace L n k i) G V) at hX
    set X := leftGradient (fieldSpace L n k i) G V with hXdef
    have hreal : PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra X :=
      hX.2.1 fun W _ => by simp [hG]
    have hXform : X ∈ edgeFormSpace L n k i := hreal
    have hpair := hX.2.2 X hXform (Set.toFinite _)
    rw [hzero X hXform] at hpair
    have hvals : ∀ b : PositiveEdge L n k i,
        restrictToPositiveEdges X b ∈ ComplexMatrix2.hermitianTraceless :=
      fun b => hreal.1 b b.2
    rw [edgeFormPairing, traceFinsumPairing_self hP hvals] at hpair
    have hsumz : ∑ b, ComplexMatrix2.operatorNorm (restrictToPositiveEdges X b) ^ 2 = 0 := by
      exact_mod_cast hpair
    have hb0 : ∀ b : PositiveEdge L n k i, X b = 0 := by
      intro b
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => by positivity)).mp hsumz b
        (Finset.mem_univ _)
      exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h)
    funext b
    by_cases h : b.IsPositivelyOriented
    · exact hb0 ⟨b, h⟩
    · have h' := (isPositive_or_opposite b).resolve_left h
      have hr := hb0 ⟨b.opposite, h'⟩
      have hneg : X b.opposite = -X b := hreal.2 b
      have hr' : X b.opposite = 0 := hr
      rw [hr'] at hneg
      simpa using hneg.symm
  · refine hall.mono ?_
    rintro V ⟨hN, hF, hVU, hV⟩ hax B hB
    have hc := hcurve V hN hF hVU hV hax univ (expCurve V B)
      (expCurve_isTwiceDiff (hmemCurve V hV B hB)) (expCurve_zero B hV)
    rw [curveTangent_expCurve hV hB] at hc
    rw [← hc.2]
    set f : ℝ → ℝ := fun s => axialFunction L n k i (expCurve V B s) with hf
    have hinner : ∀ s : ℝ, deriv (fun t : ℝ => axialFunction L n k i
        (PeriodicLattice.expTwist (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B) V)) 0 =
          deriv f s := by
      intro s
      have heq : (fun t : ℝ => axialFunction L n k i
          (PeriodicLattice.expTwist (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B) V)) =
            fun t => f (s + t) := by
        funext t
        have : algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B = ((s + t : ℝ) : ℂ) • B := by
          rw [← add_smul]
          simp
        simp only [hf, expCurve, this]
      rw [heq, deriv_comp_const_add, add_zero]
    simp only [leftSecondDeriv, mixedDirectionalDeriv, hinner]
  · refine hall.mono ?_
    rintro V ⟨hN, hF, hVU, hV⟩ hax B hB I γ hγ h0 htan
    have hc := hcurve V hN hF hVU hV hax I γ hγ h0
    have ht : curveTangent γ = B := htan
    rw [ht] at hc
    exact hc.2
  · intro B hB
    funext x
    have hs := cubeCentre_spec hZ x
    exact ((hAvg.1 L hL).1 n k i hn hi).2.1.deriv_contour B hB (cubeCentre x) x.1 hs.1
end Tower
end YangMills.Construction
end
