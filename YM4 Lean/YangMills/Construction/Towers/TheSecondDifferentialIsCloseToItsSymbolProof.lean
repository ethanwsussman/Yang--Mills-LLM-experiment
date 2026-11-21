import YangMills.Construction.PeriodicOperators.NumbersOfALocalOperatorFunction
import YangMills.Construction.Towers.ACommonWidthAndTheTransposedStraightAverageProof
import YangMills.Construction.Towers.BlocksOfTheTwoOperatorFunctionsDescendProof
import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.FieldsAndTheirValues
import YangMills.Construction.Towers.SecondDifferentialOfTheFunctionalAndItsComplexExtension
import YangMills.Construction.Towers.StraightAverageOnTheFormsOfTheWholeLatticeProof
import YangMills.Construction.Towers.TheMassiveFunctionalIsGaugeInvariantProof
import YangMills.Construction.Towers.TheSecondDifferentialIsCloseToItsSymbol
import YangMills.Construction.Towers.TheTwoOperatorFunctionsAreRealAtRealFields
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.SecondDerivNearSymbol
open YangMills.Construction
open PeriodicOperators
open PeriodicOperators.LogDetSecondDerivs
open YangMills.Construction.LocalKernels (FieldIdx FieldComponent)
open FullSpace (fieldPeriodicData vectorIndices ghostIndices vectorOpFn ghostOpFn)
section Calculus
variable {N : ℕ}
theorem iteratedDeriv_lines_eq_secondFDeriv {G : (Fin N → ℝ) → ℝ}
    (hG : HasSecondFDerivAtZero G) {h : ℝ → ℝ → ℝ} {c : ℝ} (v v' : Fin N → ℝ)
    (hh : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᶠ t in 𝓝 (0 : ℝ), h s t = G (s • v + t • v') + c) :
    deriv (fun s => deriv (fun t => h s t) 0) 0 = fderiv ℝ (fderiv ℝ G) 0 v v' := by
  obtain ⟨hd, hd2⟩ := hG
  have hline : Tendsto (fun s : ℝ => s • v) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => s • v) := by fun_prop
    simpa using hc.tendsto 0
  have e1 : ∀ᶠ s in 𝓝 (0 : ℝ), deriv (fun t => h s t) 0 = fderiv ℝ G (s • v) v' := by
    filter_upwards [hh, hline.eventually hd] with s hs hds
    have hcongr : (fun t => h s t) =ᶠ[𝓝 0] fun t => G (s • v + t • v') + c := hs
    rw [hcongr.deriv_eq]
    have hl : HasDerivAt (fun t : ℝ => s • v + t • v') v' 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v').const_add (s • v)
    have hG' : HasFDerivAt G (fderiv ℝ G (s • v)) ((fun t : ℝ => s • v + t • v') 0) := by
      simpa using hds.hasFDerivAt
    exact ((hG'.comp_hasDerivAt (0 : ℝ) hl).add_const c).deriv
  have e2 : (fun s => deriv (fun t => h s t) 0) =ᶠ[𝓝 0] fun s => fderiv ℝ G (s • v) v' := e1
  rw [e2.deriv_eq]
  have hl : HasDerivAt (fun s : ℝ => s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hD : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) 0) ((fun s : ℝ => s • v) 0) := by
    simpa using hd2.hasFDerivAt
  have hc := hD.comp_hasDerivAt (0 : ℝ) hl
  have := hc.clm_apply (hasDerivAt_const (0 : ℝ) v')
  simpa using this.deriv
theorem hasSecondFDerivAtZero_linearCombination {g₁ g₂ : (Fin N → ℝ) → ℝ} (a : ℝ)
    (h₁ : HasSecondFDerivAtZero g₁) (h₂ : HasSecondFDerivAtZero g₂) :
    HasSecondFDerivAtZero (fun v => a * g₁ v + g₂ v) ∧
      ∀ x y, fderiv ℝ (fderiv ℝ fun v => a * g₁ v + g₂ v) 0 x y =
        a * fderiv ℝ (fderiv ℝ g₁) 0 x y + fderiv ℝ (fderiv ℝ g₂) 0 x y := by
  have ev : fderiv ℝ (fun v => a * g₁ v + g₂ v) =ᶠ[𝓝 0]
      fun v => a • fderiv ℝ g₁ v + fderiv ℝ g₂ v := by
    filter_upwards [h₁.1, h₂.1] with v d₁ d₂
    rw [fderiv_fun_add (d₁.const_mul a) d₂, fderiv_const_mul d₁]
  have hsum : DifferentiableAt ℝ (fun v => a • fderiv ℝ g₁ v + fderiv ℝ g₂ v) 0 :=
    (h₁.2.const_smul a).add h₂.2
  refine ⟨⟨?_, ev.differentiableAt_iff.2 hsum⟩, fun x y => ?_⟩
  · filter_upwards [h₁.1, h₂.1] with v d₁ d₂
    exact (d₁.const_mul a).add d₂
  · have hh : HasFDerivAt (fun v => a • fderiv ℝ g₁ v + fderiv ℝ g₂ v)
        (a • fderiv ℝ (fderiv ℝ g₁) 0 + fderiv ℝ (fderiv ℝ g₂) 0) 0 :=
      (h₁.2.hasFDerivAt.const_smul a).add h₂.2.hasFDerivAt
    rw [ev.fderiv_eq, hh.fderiv]
    simp
end Calculus
section Real
variable {F I : PeriodicData} {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
theorem isRealOnRealFields_of_eventually
    (hHol : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hnear : ∀ f : F.Carrier → ℂ, (∀ κ, (f κ).im = 0) → IsSupBelow F f ρ₀ →
      ∀ ι' ι, (T f ι' ι).im = 0) :
    IsRealOnRealFields F I T := by
  rintro f hf ⟨ρ, R, hM, r₀, hr₀, hle₀⟩ ι' ι
  have hρ : 0 < ρ := hM.radius_pos
  obtain ⟨l, e, h, hh, hval⟩ := hM.holo_entry ι' ι
  rw [hval f ⟨r₀, hr₀, hle₀⟩]
  set r : ℝ := max r₀ 0 with hr
  have hrρ : r < ρ := max_lt hr₀ hρ
  have hr0 : 0 ≤ r := le_max_right _ _
  have hle : ∀ κ, ‖f κ‖ ≤ r := fun κ => (hle₀ κ).trans (le_max_left _ _)
  set x : Coordinates.ComplexCoordinates l := fieldValues e f with hx
  have hxle : ∀ j, ‖x j‖ ≤ r := fun j => hle _
  set P : Set (Coordinates.ComplexCoordinates l) :=
    Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk 0 ρ with hP
  have hPo : IsOpen P := by
    have : P = ⋂ j, {z : Coordinates.ComplexCoordinates l |
        ‖z j - (0 : Coordinates.ComplexCoordinates l) j‖ < ρ} := by
      ext z
      simp [hP, Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk]
    rw [this]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  have hD : DifferentiableOn ℂ h P := by
    have h₁ := (hHol l 1 P (fun z _ => h z) hPo).1 hh
    exact differentiableOn_pi.1 h₁ 0
  set c : ℝ := 2 * ρ / (ρ + r) with hc
  have hρr : 0 < ρ + r := by linarith
  have hc1 : 1 < c := by
    rw [hc, one_lt_div hρr]
    linarith
  have hcr : c * r < ρ := by
    rw [hc, div_mul_eq_mul_div, div_lt_iff₀ hρr]
    nlinarith
  have hline : ∀ u : ℂ, ‖u‖ < c → u • x ∈ P := by
    intro u hu j
    have h₁ : ‖u * x j‖ ≤ c * r := by
      rw [norm_mul]
      exact mul_le_mul hu.le (hxle j) (norm_nonneg _) (by linarith)
    simpa using lt_of_le_of_lt h₁ hcr
  have hφ : DifferentiableOn ℂ (fun u : ℂ => h (u • x)) (Metric.ball 0 c) := by
    refine hD.comp (by fun_prop) fun u hu => hline u ?_
    simpa using hu
  have hA : AnalyticOnNhd ℂ (fun u : ℂ => h (u • x)) (Metric.ball 0 c) :=
    hφ.analyticOnNhd Metric.isOpen_ball
  have hψ : AnalyticOnNhd ℝ (fun t : ℝ => (h ((t : ℂ) • x)).im) (Metric.ball 0 c) := by
    intro t ht
    have ht' : (t : ℂ) ∈ Metric.ball (0 : ℂ) c := by simpa using ht
    have h₁ : AnalyticAt ℝ (fun u : ℂ => h (u • x)) (t : ℂ) := (hA _ ht').restrictScalars
    have h₂ : AnalyticAt ℝ (fun t : ℝ => (t : ℂ)) t := Complex.ofRealCLM.analyticAt t
    have h₃ : AnalyticAt ℝ (fun t : ℝ => h ((t : ℂ) • x)) t := h₁.fun_comp h₂
    exact Complex.imCLM.analyticAt _ |>.fun_comp h₃
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * r < min ρ ρ₀ := by
    have hcont : Continuous fun t : ℝ => |t| * r := by fun_prop
    have := hcont.tendsto 0
    simp only [abs_zero, zero_mul] at this
    exact this.eventually (gt_mem_nhds (lt_min hρ hρ₀))
  have hzero : (fun t : ℝ => (h ((t : ℂ) • x)).im) =ᶠ[𝓝 0] 0 := by
    filter_upwards [hsmall] with t ht
    have hb : ∀ κ, ‖((t : ℂ) • f) κ‖ ≤ |t| * r := by
      intro κ
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hle κ) (abs_nonneg t)
    have hreal : ∀ κ, (((t : ℂ) • f) κ).im = 0 := by
      intro κ
      simp [hf κ]
    have e₁ := hval ((t : ℂ) • f) ⟨_, ht.trans_le (min_le_left _ _), hb⟩
    have e₂ := hnear ((t : ℂ) • f) hreal ⟨_, ht.trans_le (min_le_right _ _), hb⟩ ι' ι
    rw [e₁] at e₂
    exact e₂
  have hall := hψ.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℝ) c).isPreconnected (Metric.mem_ball_self (by linarith)) hzero
  have h₁ := hall (show (1 : ℝ) ∈ Metric.ball (0 : ℝ) c by simpa using hc1)
  simpa using h₁
end Real
section Colours
theorem pauliCoeff_eq_of_mem {X : Matrices.ComplexMatrix2}
    (h : X ∈ Matrices.ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a X = OneLoop.pauliCoordinateEquiv ⟨X, h⟩ a := by
  simp only [pauliCoeff, dif_pos h]
theorem pauliCoeff_add {X Y : Matrices.ComplexMatrix2} (hX : X ∈ Matrices.ComplexMatrix2.traceless)
    (hY : Y ∈ Matrices.ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
theorem pauliCoeff_smul (z : ℂ) {X : Matrices.ComplexMatrix2}
    (h : X ∈ Matrices.ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (z • X) = z * pauliCoeff a X := by
  rw [pauliCoeff_eq_of_mem (Matrices.ComplexMatrix2.traceless.smul_mem z h), pauliCoeff_eq_of_mem h]
  have : (⟨z • X, Matrices.ComplexMatrix2.traceless.smul_mem z h⟩ :
      Matrices.ComplexMatrix2.traceless) = z • ⟨X, h⟩ := rfl
  rw [this, map_smul]
  rfl
theorem sum_smul_pauliFamily_mem_traceless (c : Fin 3 → ℂ) :
    (∑ b, c b • Matrices.ComplexMatrix2.pauliFamily b) ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_sum_smul (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, c b • Matrices.ComplexMatrix2.pauliFamily b) = c a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliCoeff_im_eq_zero {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.hermitianTraceless) (a : Fin 3) :
    (pauliCoeff a X).im = 0 := by apply _root_.YangMills.SharedProofs.p23717 <;> assumption
theorem mem_hermitianTraceless_of_im_eq_zero {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless)
    (h : ∀ a, (pauliCoeff a X).im = 0) : X ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.OperatorBlocksDescend.mem_hermitianTraceless_of_im <;> assumption
end Colours
section Fields
variable {L n k : ℕ}
theorem mem_complexEdgeForms_of_mem {j : ℕ} {B : Edge L n k j → Matrices.ComplexMatrix2}
    (h : B ∈ edgeFormSpace L n k j) : B ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
theorem conjTranspose_mem_traceless {X : Matrices.ComplexMatrix2}
    (h : X ∈ Matrices.ComplexMatrix2.traceless) :
    X.conjTranspose ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.MassiveFunctionals.GaugeInvariance.conjTranspose_mem_traceless <;> assumption
theorem hermitianPart_mem {X : Matrices.ComplexMatrix2} (h : X ∈ Matrices.ComplexMatrix2.traceless) :
    ((1 / 2 : ℂ) • (X + X.conjTranspose)) ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.FullSpace.StraightSmoothing.hermitianPart_mem_hermitianTraceless <;> assumption
theorem skewPart_mem {X : Matrices.ComplexMatrix2} (h : X ∈ Matrices.ComplexMatrix2.traceless) :
    ((1 / (2 * Complex.I) : ℂ) • (X - X.conjTranspose)) ∈
      Matrices.ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, Matrices.ComplexMatrix2.traceless.smul_mem _
    (Matrices.ComplexMatrix2.traceless.sub_mem h (conjTranspose_mem_traceless h))⟩
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
  have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I) : ℂ) := by
    simp [Complex.inv_I]
  rw [this, neg_smul, ← smul_neg, neg_sub]
theorem eq_hermitianPart_add_I_smul (X : Matrices.ComplexMatrix2) :
    X = (1 / 2 : ℂ) • (X + X.conjTranspose) +
      Complex.I • ((1 / (2 * Complex.I) : ℂ) • (X - X.conjTranspose)) := by
  rw [smul_smul]
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  rw [this, ← smul_add]
  have h2 : X + X.conjTranspose + (X - X.conjTranspose) = (2 : ℂ) • X := by
    rw [two_smul]; abel
  rw [h2, smul_smul]
  norm_num
theorem complexEdgeForm_decomp {j : ℕ} (B : complexEdgeForms L n k j) :
    ∃ (R S : edgeFormSpace L n k j) (R' S' : complexEdgeForms L n k j),
      (R' : Edge L n k j → Matrices.ComplexMatrix2) = R ∧
        (S' : Edge L n k j → Matrices.ComplexMatrix2) = S ∧
        B = R' + Complex.I • S' := by
  have hB := B.2
  have hR : (fun b => (1 / 2 : ℂ) • ((B : Edge L n k j → Matrices.ComplexMatrix2) b +
      ((B : Edge L n k j → Matrices.ComplexMatrix2) b).conjTranspose)) ∈ edgeFormSpace L n k j := by
    refine ⟨fun b hb => hermitianPart_mem (hB.1 b hb), fun b => ?_⟩
    simp only [hB.2 b, Matrix.conjTranspose_neg]
    rw [← neg_add, smul_neg]
  have hS : (fun b => (1 / (2 * Complex.I) : ℂ) • ((B : Edge L n k j → Matrices.ComplexMatrix2) b -
      ((B : Edge L n k j → Matrices.ComplexMatrix2) b).conjTranspose)) ∈ edgeFormSpace L n k j := by
    refine ⟨fun b hb => skewPart_mem (hB.1 b hb), fun b => ?_⟩
    simp only [hB.2 b, Matrix.conjTranspose_neg]
    rw [← smul_neg]
    congr 1
    abel
  refine ⟨⟨_, hR⟩, ⟨_, hS⟩, ⟨_, mem_complexEdgeForms_of_mem hR⟩,
    ⟨_, mem_complexEdgeForms_of_mem hS⟩, rfl, rfl, ?_⟩
  apply Subtype.ext
  funext b
  exact eq_hermitianPart_add_I_smul _
theorem periodicField_decomp (ζ : PeriodicField L n k) :
    ∃ (ζr ζi : PeriodicField L n k) (r r' : RealPeriodicField L n k),
      ζr.RealizedBy r ∧ ζi.RealizedBy r' ∧ ζ = ζr + Complex.I • ζi := by
  obtain ⟨R₁, S₁, R₁', S₁', a₁, b₁, e₁⟩ := complexEdgeForm_decomp ζ.1
  obtain ⟨R₂, S₂, R₂', S₂', a₂, b₂, e₂⟩ := complexEdgeForm_decomp ζ.2.1
  obtain ⟨R₃, S₃, R₃', S₃', a₃, b₃, e₃⟩ := complexEdgeForm_decomp ζ.2.2
  refine ⟨(R₁', R₂', R₃'), (S₁', S₂', S₃'), (R₁, R₂, R₃), (S₁, S₂, S₃), ⟨a₁, a₂, a₃⟩,
    ⟨b₁, b₂, b₃⟩, ?_⟩
  exact Prod.ext e₁ (Prod.ext e₂ e₃)
theorem pauliCoeffs_add (hL : 0 < L) (ζ ζ' : PeriodicField L n k) :
    (ζ + ζ').pauliCoeffs hL = ζ.pauliCoeffs hL + ζ'.pauliCoeffs hL := by
  funext κ
  obtain ⟨p, ι⟩ := κ
  cases p
  · exact pauliCoeff_add (ζ.1.2.1 _ (LocalKernels.projPositiveEdge L n k 0 ι.2).2)
      (ζ'.1.2.1 _ (LocalKernels.projPositiveEdge L n k 0 ι.2).2) _
  · exact pauliCoeff_add (ζ.2.1.2.1 _ (LocalKernels.projPositiveEdge L n k 0 ι.2).2)
      (ζ'.2.1.2.1 _ (LocalKernels.projPositiveEdge L n k 0 ι.2).2) _
  · exact pauliCoeff_add (ζ.2.2.2.1 _ (LocalKernels.projPositiveEdge L n k k ι.2).2)
      (ζ'.2.2.2.1 _ (LocalKernels.projPositiveEdge L n k k ι.2).2) _
theorem pauliCoeffs_smul (hL : 0 < L) (z : ℂ) (ζ : PeriodicField L n k) :
    (z • ζ).pauliCoeffs hL = z • ζ.pauliCoeffs hL := by
  funext κ
  obtain ⟨p, ι⟩ := κ
  cases p
  · exact pauliCoeff_smul z (ζ.1.2.1 _ (LocalKernels.projPositiveEdge L n k 0 ι.2).2) _
  · exact pauliCoeff_smul z (ζ.2.1.2.1 _ (LocalKernels.projPositiveEdge L n k 0 ι.2).2) _
  · exact pauliCoeff_smul z (ζ.2.2.2.1 _ (LocalKernels.projPositiveEdge L n k k ι.2).2) _
theorem pauliCoeffs_im_eq_zero (hL : 0 < L) {ζ : PeriodicField L n k} {r : RealPeriodicField L n k}
    (h : ζ.RealizedBy r) (κ : FieldIdx L k hL) : (ζ.pauliCoeffs hL κ).im = 0 := by
  obtain ⟨p, ι⟩ := κ
  obtain ⟨h₁, h₂, h₃⟩ := h
  cases p
  · change (pauliCoeff ι.1 ((ζ.1 : Edge L n k 0 → Matrices.ComplexMatrix2)
      (LocalKernels.projPositiveEdge L n k 0 ι.2).1)).im = 0
    rw [h₁]
    exact pauliCoeff_im_eq_zero (r.1.2.1 _ (LocalKernels.projPositiveEdge L n k 0 ι.2).2) _
  · change (pauliCoeff ι.1 ((ζ.2.1 : Edge L n k 0 → Matrices.ComplexMatrix2)
      (LocalKernels.projPositiveEdge L n k 0 ι.2).1)).im = 0
    rw [h₂]
    exact pauliCoeff_im_eq_zero (r.2.1.2.1 _ (LocalKernels.projPositiveEdge L n k 0 ι.2).2) _
  · change (pauliCoeff ι.1 ((ζ.2.2 : Edge L n k k → Matrices.ComplexMatrix2)
      (LocalKernels.projPositiveEdge L n k k ι.2).1)).im = 0
    rw [h₃]
    exact pauliCoeff_im_eq_zero (r.2.2.2.1 _ (LocalKernels.projPositiveEdge L n k k ι.2).2) _
open YangMills.Construction.LocalKernels.Periodisation (QuotientClassesPeriodic)
def imageCoeffs (hL : 0 < L) (ζ : PeriodicField L n k) :
    (LocalKernels.fieldIndices L k hL).ImageCarrier L n → ℂ
  | ⟨.background, c⟩ => (edgePauliCoordinates L n k 0).coeffs ζ.1.1 c.1
  | ⟨.source, c⟩ => (edgePauliCoordinates L n k 0).coeffs ζ.2.1.1 c.1
  | ⟨.coarse, c⟩ => (edgePauliCoordinates L n k k).coeffs ζ.2.2.1 c.1
theorem imageCoeffs_proj (hL : 0 < L) (ζ : PeriodicField L n k)
    (κ : FieldIdx L k hL) :
    imageCoeffs hL ζ ((LocalKernels.fieldIndices L k hL).proj L n κ) =
      ζ.pauliCoeffs hL κ := by
  obtain ⟨_ | _ | _, ι⟩ := κ <;> rfl
theorem onQuotient_mkQuot (hL : 0 < L)
    (hcl : QuotientClassesPeriodic L n (LocalKernels.fieldIndices L k hL))
    (ζ : PeriodicField L n k) (κ : FieldIdx L k hL) :
    ζ.onQuotient hL ((fieldPeriodicData L k hL).mkQuot (2 * L ^ n) κ) = ζ.pauliCoeffs hL κ := by
  obtain ⟨-, ⟨φ, -, hφ⟩, -⟩ := hcl
  have hex : ∃ f : (fieldPeriodicData L k hL).QuotMod (2 * L ^ n) → ℂ,
      ∀ κ : FieldIdx L k hL,
        f ((fieldPeriodicData L k hL).mkQuot (2 * L ^ n) κ) = ζ.pauliCoeffs hL κ :=
    ⟨fun c => imageCoeffs hL ζ (φ c), fun κ => by
      have h1 := hφ κ
      change imageCoeffs hL ζ
        (φ ((fieldPeriodicData L k hL).mkQuot (LocalKernels.Periodisation.periodSide L n) κ)) = _
      rw [h1, imageCoeffs_proj]⟩
  exact Classical.epsilon_spec hex κ
theorem onQuotient_eq_of (hL : 0 < L)
    (hcl : QuotientClassesPeriodic L n (LocalKernels.fieldIndices L k hL))
    (ζ : PeriodicField L n k) {f : (fieldPeriodicData L k hL).QuotMod (2 * L ^ n) → ℂ}
    (h : ∀ κ, f ((fieldPeriodicData L k hL).mkQuot (2 * L ^ n) κ) = ζ.pauliCoeffs hL κ) :
    ζ.onQuotient hL = f := by
  funext c
  obtain ⟨κ, rfl⟩ := Quot.exists_rep c
  exact (onQuotient_mkQuot hL hcl ζ κ).trans (h κ).symm
theorem onQuotient_add (hL : 0 < L)
    (hcl : QuotientClassesPeriodic L n (LocalKernels.fieldIndices L k hL))
    (ζ ζ' : PeriodicField L n k) :
    (ζ + ζ').onQuotient hL = ζ.onQuotient hL + ζ'.onQuotient hL :=
  onQuotient_eq_of hL hcl _ fun κ => by
    rw [pauliCoeffs_add, Pi.add_apply, Pi.add_apply, onQuotient_mkQuot hL hcl,
      onQuotient_mkQuot hL hcl]
theorem onQuotient_smul (hL : 0 < L)
    (hcl : QuotientClassesPeriodic L n (LocalKernels.fieldIndices L k hL))
    (z : ℂ) (ζ : PeriodicField L n k) :
    (z • ζ).onQuotient hL = z • ζ.onQuotient hL :=
  onQuotient_eq_of hL hcl _ fun κ => by
    rw [pauliCoeffs_smul, Pi.smul_apply, Pi.smul_apply, onQuotient_mkQuot hL hcl]
theorem onQuotient_im_eq_zero (hL : 0 < L)
    (hcl : QuotientClassesPeriodic L n (LocalKernels.fieldIndices L k hL))
    {ζ : PeriodicField L n k} {r : RealPeriodicField L n k} (h : ζ.RealizedBy r)
    (c : (fieldPeriodicData L k hL).QuotMod (2 * L ^ n)) : (ζ.onQuotient hL c).im = 0 := by
  obtain ⟨κ, rfl⟩ := Quot.exists_rep c
  have e := onQuotient_mkQuot hL hcl ζ κ
  change (ζ.onQuotient hL ((fieldPeriodicData L k hL).mkQuot (2 * L ^ n) κ)).im = 0
  rw [e]
  exact pauliCoeffs_im_eq_zero hL h κ
theorem onQuotient_eq_descendField (hL : 0 < L)
    (hcl : QuotientClassesPeriodic L n (LocalKernels.fieldIndices L k hL))
    {ζ : PeriodicField L n k} {g : FieldIdx L k hL → ℂ} (h : ζ.pauliCoeffs hL = g) :
    ζ.onQuotient hL = descendField (fieldPeriodicData L k hL) (2 * L ^ n) g := by
  funext c
  have hex : ∃ z, ∀ κ, (fieldPeriodicData L k hL).mkQuot (2 * L ^ n) κ = c → g κ = z :=
    ⟨ζ.onQuotient hL c, fun κ hκ => by
      rw [← hκ, onQuotient_mkQuot hL hcl, h]⟩
  have hs := Classical.epsilon_spec hex
  obtain ⟨κ, rfl⟩ := Quot.exists_rep c
  have e₁ := hs κ rfl
  have e₂ := onQuotient_mkQuot hL hcl ζ κ
  rw [h] at e₂
  exact e₂.trans e₁
theorem pauliCoeffs_bounded (hL : 0 < L)
    (hcl : QuotientClassesPeriodic L n (LocalKernels.fieldIndices L k hL))
    (ζ : PeriodicField L n k) : ∃ M : ℝ, 0 ≤ M ∧ ∀ κ, ‖ζ.pauliCoeffs hL κ‖ ≤ M := by
  have hfin : Finite ((fieldPeriodicData L k hL).QuotMod (2 * L ^ n)) := by
    obtain ⟨hI, ⟨φ, hφ, -⟩, -⟩ := hcl
    exact Finite.of_injective φ hφ.1
  let _ := Fintype.ofFinite ((fieldPeriodicData L k hL).QuotMod (2 * L ^ n))
  refine ⟨∑ c, ‖ζ.onQuotient hL c‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun κ => ?_⟩
  rw [← onQuotient_mkQuot hL hcl]
  exact Finset.single_le_sum (f := fun c => ‖ζ.onQuotient hL c‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ _)
theorem exists_complexEdgeForm {j : ℕ}
    (hOr : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (c : Fin 3 × PositiveEdge L n k j → ℂ) :
    ∃ B : complexEdgeForms L n k j, ∀ (a : Fin 3) (d : PositiveEdge L n k j),
      pauliCoeff a ((B : Edge L n k j → Matrices.ComplexMatrix2) d.1) = c (a, d) := by
  classical
  let val : Edge L n k j → Matrices.ComplexMatrix2 := fun b =>
    if h : b.IsPositivelyOriented then ∑ a, c (a, ⟨b, h⟩) • Matrices.ComplexMatrix2.pauliFamily a
    else 0
  have hval : ∀ d : PositiveEdge L n k j,
      extendOddly val d.1 = ∑ a, c (a, d) • Matrices.ComplexMatrix2.pauliFamily a := by
    intro d
    simp only [extendOddly, val, if_pos d.2, dif_pos d.2]
  refine ⟨⟨extendOddly val, fun b hb => ?_, fun b => ?_⟩, fun a d => ?_⟩
  · have := hval ⟨b, hb⟩
    simp only at this
    rw [this]
    exact sum_smul_pauliFamily_mem_traceless _
  · simp only [extendOddly]
    rcases hOr b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have e : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
      rw [if_neg h₂, if_pos h₁, e]
    · rw [if_pos h₁, if_neg h₂, neg_neg]
  · change pauliCoeff a (extendOddly val d.1) = _
    rw [hval, pauliCoeff_sum_smul (fun a => c (a, d)) a]
theorem exists_periodicField (hL : 0 < L)
    (hcl : QuotientClassesPeriodic L n (LocalKernels.fieldIndices L k hL))
    (h₀ : Function.Surjective (LocalKernels.projPositiveEdge L n k 0))
    (hk : Function.Surjective (LocalKernels.projPositiveEdge L n k k))
    (hOr₀ : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hOrk : ∀ b : Edge L n k k, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : FieldIdx L k hL → ℂ)
    (hf : ∀ (m : Fin 4 → ℤ) (ι : FieldIdx L k hL),
      f ((fieldPeriodicData L k hL).translate ((2 * L ^ n) • m) ι) = f ι) :
    ∃ ζ : PeriodicField L n k, ζ.pauliCoeffs hL = f := by
  obtain ⟨-, -, hbij⟩ := hcl
  obtain ⟨g, -, hg⟩ := hbij.surjOn hf
  have hgf : ∀ κ : FieldIdx L k hL,
      f κ = g ((LocalKernels.fieldIndices L k hL).proj L n κ) := fun κ =>
    (congrFun hg κ).symm
  obtain ⟨B₁, e₁⟩ := exists_complexEdgeForm hOr₀ fun ad : Fin 3 × PositiveEdge L n k 0 =>
    f ⟨FieldComponent.background, (ad.1, Function.surjInv h₀ ad.2)⟩
  obtain ⟨B₂, e₂⟩ := exists_complexEdgeForm hOr₀ fun ad : Fin 3 × PositiveEdge L n k 0 =>
    f ⟨FieldComponent.source, (ad.1, Function.surjInv h₀ ad.2)⟩
  obtain ⟨B₃, e₃⟩ := exists_complexEdgeForm hOrk fun ad : Fin 3 × PositiveEdge L n k k =>
    f ⟨FieldComponent.coarse, (ad.1, Function.surjInv hk ad.2)⟩
  refine ⟨(B₁, B₂, B₃), ?_⟩
  funext κ
  obtain ⟨p, ι⟩ := κ
  cases p
  · refine (e₁ ι.1 _).trans ?_
    refine (hgf _).trans (Eq.trans ?_ (hgf _).symm)
    refine congrArg g (Sigma.ext rfl (heq_of_eq (Subtype.ext ?_)))
    exact Prod.ext rfl (Function.surjInv_eq h₀ _)
  · refine (e₂ ι.1 _).trans ?_
    refine (hgf _).trans (Eq.trans ?_ (hgf _).symm)
    refine congrArg g (Sigma.ext rfl (heq_of_eq (Subtype.ext ?_)))
    exact Prod.ext rfl (Function.surjInv_eq h₀ _)
  · refine (e₃ ι.1 _).trans ?_
    refine (hgf _).trans (Eq.trans ?_ (hgf _).symm)
    refine congrArg g (Sigma.ext rfl (heq_of_eq (Subtype.ext ?_)))
    exact Prod.ext rfl (Function.surjInv_eq hk _)
end Fields
section Waves
theorem blochWave_translate {F : PeriodicData} (hF : IsPeriodic F) {s : ℕ} (hs : s ≠ 0)
    {κ : Fin 4 → ℂ} (c : Fin 4 → ℤ)
    (hκ : ∀ μ, κ μ = (c μ : ℂ) * ((2 * Real.pi / s : ℝ) : ℂ)) (ε : F.UnitQuot → ℂ)
    (m : Fin 4 → ℤ) (ι : F.Carrier) :
    blochWave F κ ε (F.translate (s • m) ι) = blochWave F κ ε ι := by
  have hcl : F.mkQuot 1 (F.translate (s • m) ι) = F.mkQuot 1 ι :=
    (Quot.sound ⟨s • m, by simp⟩).symm
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hdot : bilinDot κ (toComplexVec (F.pos (F.translate (s • m) ι))) =
      bilinDot κ (toComplexVec (F.pos ι)) +
        ((∑ μ, c μ * m μ : ℤ) : ℂ) * (2 * Real.pi) := by
    rw [hF.pos_translate]
    simp only [bilinDot, toComplexVec, Pi.add_apply, Complex.ofReal_add, mul_add,
      Finset.sum_add_distrib]
    congr 1
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hκ μ]
    simp only [castVec, Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
    push_cast
    field_simp
  unfold blochWave
  rw [hcl, hdot, mul_add, Complex.exp_add]
  have hone : Complex.exp (Complex.I * (((∑ μ, c μ * m μ : ℤ) : ℂ) * (2 * Real.pi))) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (∑ μ, c μ * m μ)
    rw [← this]
    congr 1
    ring
  rw [hone, mul_one]
end Waves
section Main
variable {L n k : ℕ}
open YangMills.Construction.LocalKernels.Periodisation (QuotientClassesPeriodic)
open FullSpace.OperatorFunctions (FunctionalEqLogDetNearZero logDetCombination)
def realQuotCoords (hL : 0 < L) {N : ℕ}
    (e : Fin N ≃ (fieldPeriodicData L k hL).QuotMod (2 * L ^ n)) (ξ : PeriodicField L n k) :
    Fin N → ℝ :=
  fun j => (ξ.onQuotient hL (e j)).re
theorem ofReal_smul_complexMatrix2 (s : ℝ) (X : Matrices.ComplexMatrix2) : (s : ℂ) • X = s • X := by apply _root_.YangMills.Construction.Tower.AsDifferentials.ofReal_smul_matrix <;> assumption
theorem realizedBy_linearCombination {ξ ξ' : PeriodicField L n k} {r r' : RealPeriodicField L n k}
    (h : ξ.RealizedBy r) (h' : ξ'.RealizedBy r') (s t : ℝ) :
    ((s : ℂ) • ξ + (t : ℂ) • ξ').RealizedBy (s • r + t • r') := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  obtain ⟨h₁', h₂', h₃'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · funext b
    change (s : ℂ) • (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) b +
        (t : ℂ) • (ξ'.1 : Edge L n k 0 → Matrices.ComplexMatrix2) b =
      s • (r.1 : Edge L n k 0 → Matrices.ComplexMatrix2) b +
        t • (r'.1 : Edge L n k 0 → Matrices.ComplexMatrix2) b
    rw [h₁, h₁', ofReal_smul_complexMatrix2, ofReal_smul_complexMatrix2]
  · funext b
    change (s : ℂ) • (ξ.2.1 : Edge L n k 0 → Matrices.ComplexMatrix2) b +
        (t : ℂ) • (ξ'.2.1 : Edge L n k 0 → Matrices.ComplexMatrix2) b =
      s • (r.2.1 : Edge L n k 0 → Matrices.ComplexMatrix2) b +
        t • (r'.2.1 : Edge L n k 0 → Matrices.ComplexMatrix2) b
    rw [h₂, h₂', ofReal_smul_complexMatrix2, ofReal_smul_complexMatrix2]
  · funext b
    change (s : ℂ) • (ξ.2.2 : Edge L n k k → Matrices.ComplexMatrix2) b +
        (t : ℂ) • (ξ'.2.2 : Edge L n k k → Matrices.ComplexMatrix2) b =
      s • (r.2.2 : Edge L n k k → Matrices.ComplexMatrix2) b +
        t • (r'.2.2 : Edge L n k k → Matrices.ComplexMatrix2) b
    rw [h₃, h₃', ofReal_smul_complexMatrix2, ofReal_smul_complexMatrix2]
theorem secondDeriv_eq_on_real (hL : 0 < L)
    (hcl : QuotientClassesPeriodic L n (LocalKernels.fieldIndices L k hL))
    (hnear : FunctionalEqLogDetNearZero L n k hL) {N : ℕ}
    (e : Fin N ≃ (fieldPeriodicData L k hL).QuotMod (2 * L ^ n))
    (hv : HasSecondFDerivAtZero (realLogAbsDetDiffInCoords (fieldPeriodicData L k hL)
      (vectorIndices L k) (vectorOpFn L k hL) e))
    (hg : HasSecondFDerivAtZero (realLogAbsDetDiffInCoords (fieldPeriodicData L k hL)
      (ghostIndices L k) (ghostOpFn L k hL) e))
    {ξ ξ' : PeriodicField L n k} {r r' : RealPeriodicField L n k}
    (h : ξ.RealizedBy r) (h' : ξ'.RealizedBy r') :
    fieldFunctionalSecondDeriv L n k r r' =
      -(1 / 2) * fderiv ℝ (fderiv ℝ (realLogAbsDetDiffInCoords (fieldPeriodicData L k hL)
          (vectorIndices L k) (vectorOpFn L k hL) e)) 0
          (realQuotCoords hL e ξ) (realQuotCoords hL e ξ') +
        fderiv ℝ (fderiv ℝ (realLogAbsDetDiffInCoords (fieldPeriodicData L k hL)
          (ghostIndices L k) (ghostOpFn L k hL) e)) 0
          (realQuotCoords hL e ξ) (realQuotCoords hL e ξ') := by
  obtain ⟨hG, hB⟩ := hasSecondFDerivAtZero_linearCombination (-(1 / 2)) hv hg
  rw [← hB]
  obtain ⟨ε, hε, hn⟩ := hnear
  obtain ⟨M, hM0, hM⟩ := pauliCoeffs_bounded hL hcl ξ
  obtain ⟨M', hM'0, hM'⟩ := pauliCoeffs_bounded hL hcl ξ'
  have hsmall : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), |p.1| * M + |p.2| * M' < ε := by
    have hc : Continuous fun p : ℝ × ℝ => |p.1| * M + |p.2| * M' := by fun_prop
    have h₀ := hc.tendsto ((0 : ℝ), (0 : ℝ))
    simp only [abs_zero, zero_mul, add_zero] at h₀
    exact h₀.eventually (gt_mem_nhds hε)
  refine iteratedDeriv_lines_eq_secondFDeriv hG
    (h := fun s t => fieldFunctional (s • r + t • r'))
    (c := -(1 / 2) * Real.log ‖LinearMap.det (quotOperator (fieldPeriodicData L k hL)
        (vectorIndices L k) (vectorOpFn L k hL) (2 * L ^ n) 0)‖ +
      Real.log ‖LinearMap.det (quotOperator (fieldPeriodicData L k hL) (ghostIndices L k)
        (ghostOpFn L k hL) (2 * L ^ n) 0)‖) _ _ ?_
  filter_upwards [hsmall.curry_nhds] with s hs
  filter_upwards [hs] with t ht
  have hreal := realizedBy_linearCombination h h' s t
  have hbelow : IsSupBelow (fieldPeriodicData L k hL)
      (((s : ℂ) • ξ + (t : ℂ) • ξ').pauliCoeffs hL) ε := by
    refine ⟨_, ht, fun κ => ?_⟩
    rw [pauliCoeffs_add, pauliCoeffs_smul, pauliCoeffs_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM κ) (abs_nonneg s)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM' κ) (abs_nonneg t)
  obtain ⟨-, heq⟩ := hn _ _ hreal hbelow
  have hon : ((s : ℂ) • ξ + (t : ℂ) • ξ').onQuotient hL = fun c =>
      ((ofRealCoords e (s • realQuotCoords hL e ξ + t • realQuotCoords hL e ξ') c :
        ℝ) : ℂ) := by
    rw [onQuotient_add hL hcl, onQuotient_smul hL hcl, onQuotient_smul hL hcl]
    funext c
    have e₁ : ξ.onQuotient hL c = ((realQuotCoords hL e ξ (e.symm c) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [realQuotCoords]
      · simp [onQuotient_im_eq_zero hL hcl h c]
    have e₂ : ξ'.onQuotient hL c = ((realQuotCoords hL e ξ' (e.symm c) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [realQuotCoords]
      · simp [onQuotient_im_eq_zero hL hcl h' c]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e₁, e₂, ofRealCoords]
    push_cast
    rfl
  change fieldFunctional (s • r + t • r') = _
  rw [heq]
  unfold logDetCombination
  rw [hon]
  simp only [realLogAbsDetDiffInCoords, realLogAbsDetDiff]
  ring
theorem complexSecondDeriv_eq (hL : 0 < L)
    (hcl : QuotientClassesPeriodic L n (LocalKernels.fieldIndices L k hL))
    (hnear : FunctionalEqLogDetNearZero L n k hL) {N : ℕ}
    (e : Fin N ≃ (fieldPeriodicData L k hL).QuotMod (2 * L ^ n))
    (hv : HasSecondFDerivAtZero (realLogAbsDetDiffInCoords (fieldPeriodicData L k hL)
      (vectorIndices L k) (vectorOpFn L k hL) e))
    (hg : HasSecondFDerivAtZero (realLogAbsDetDiffInCoords (fieldPeriodicData L k hL)
      (ghostIndices L k) (ghostOpFn L k hL) e))
    {β : PeriodicField L n k →ₗ[ℂ] PeriodicField L n k →ₗ[ℂ] ℂ}
    (hβ : IsComplexSecondDeriv L n k β) (ζ ζ' : PeriodicField L n k) :
    β ζ ζ' =
      -(1 / 2) * realLogAbsDetSecondDeriv (fieldPeriodicData L k hL) (vectorIndices L k)
          (vectorOpFn L k hL) e (ζ.onQuotient hL) (ζ'.onQuotient hL) +
        realLogAbsDetSecondDeriv (fieldPeriodicData L k hL) (ghostIndices L k)
          (ghostOpFn L k hL) e (ζ.onQuotient hL) (ζ'.onQuotient hL) := by
  obtain ⟨a, b, r₁, r₂, h₁, h₂, rfl⟩ := periodicField_decomp ζ
  obtain ⟨a', b', r₁', r₂', h₁', h₂', rfl⟩ := periodicField_decomp ζ'
  have coord : ∀ {x y : PeriodicField L n k} {p q : RealPeriodicField L n k}, x.RealizedBy p →
      y.RealizedBy q →
      (fun j => (toCoords e ((x + Complex.I • y).onQuotient hL) j).re) =
          realQuotCoords hL e x ∧
        (fun j => (toCoords e ((x + Complex.I • y).onQuotient hL) j).im) =
          realQuotCoords hL e y := by
    intro x y p q hx hy
    have hc : ∀ j, toCoords e ((x + Complex.I • y).onQuotient hL) j =
        x.onQuotient hL (e j) + Complex.I * y.onQuotient hL (e j) := by
      intro j
      rw [toCoords, onQuotient_add hL hcl, onQuotient_smul hL hcl]
      rfl
    constructor
    · funext j
      rw [hc]
      simp [realQuotCoords, onQuotient_im_eq_zero hL hcl hy (e j)]
    · funext j
      rw [hc]
      simp [realQuotCoords, onQuotient_im_eq_zero hL hcl hx (e j)]
  have expand : β (a + Complex.I • b) (a' + Complex.I • b') =
      β a a' + Complex.I * β a b' + Complex.I * β b a' + Complex.I * Complex.I * β b b' := by
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  simp only [realLogAbsDetSecondDeriv, complexifiedSecondDeriv, (coord h₁ h₂).1,
    (coord h₁ h₂).2, (coord h₁' h₂').1, (coord h₁' h₂').2]
  rw [expand, hβ a a' r₁ r₁' h₁ h₁', hβ a b' r₁ r₂' h₁ h₂', hβ b a' r₂ r₁' h₂ h₁',
    hβ b b' r₂ r₂' h₂ h₂', secondDeriv_eq_on_real hL hcl hnear e hv hg h₁ h₁',
    secondDeriv_eq_on_real hL hcl hnear e hv hg h₁ h₂',
    secondDeriv_eq_on_real hL hcl hnear e hv hg h₂ h₁',
    secondDeriv_eq_on_real hL hcl hnear e hv hg h₂ h₂', Complex.I_mul_I]
  push_cast
  ring
theorem norm_neg_half_add_le {x y : ℂ} {C₁ C₂ c₁ c₂ s A B : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hs : 0 ≤ s) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h₁ : ‖x‖ ≤ C₁ * Real.exp (-c₁ * s) * A * B) (h₂ : ‖y‖ ≤ C₂ * Real.exp (-c₂ * s) * A * B) :
    ‖-(1 / 2) * x + y‖ ≤ (C₁ + C₂) * Real.exp (-(min c₁ c₂) * s) * A * B := by
  have e₁ : Real.exp (-c₁ * s) ≤ Real.exp (-(min c₁ c₂) * s) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left c₁ c₂])
  have e₂ : Real.exp (-c₂ * s) ≤ Real.exp (-(min c₁ c₂) * s) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right c₁ c₂])
  have b₁ : ‖x‖ ≤ C₁ * Real.exp (-(min c₁ c₂) * s) * (A * B) := by
    calc ‖x‖ ≤ C₁ * Real.exp (-c₁ * s) * A * B := h₁
      _ = C₁ * Real.exp (-c₁ * s) * (A * B) := by ring
      _ ≤ _ := by gcongr
  have b₂ : ‖y‖ ≤ C₂ * Real.exp (-(min c₁ c₂) * s) * (A * B) := by
    calc ‖y‖ ≤ C₂ * Real.exp (-c₂ * s) * A * B := h₂
      _ = C₂ * Real.exp (-c₂ * s) * (A * B) := by ring
      _ ≤ _ := by gcongr
  have hx : ‖-(1 / 2) * x‖ = (1 / 2) * ‖x‖ := by
    rw [norm_mul]
    norm_num
  have hP : 0 ≤ C₁ * Real.exp (-(min c₁ c₂) * s) * (A * B) := by positivity
  calc ‖-(1 / 2) * x + y‖ ≤ ‖-(1 / 2) * x‖ + ‖y‖ := norm_add_le _ _
    _ = (1 / 2) * ‖x‖ + ‖y‖ := by rw [hx]
    _ ≤ C₁ * Real.exp (-(min c₁ c₂) * s) * (A * B) +
        C₂ * Real.exp (-(min c₁ c₂) * s) * (A * B) := by linarith
    _ = _ := by ring
end Main
section Bound
theorem isPeriodic_disjSum {I I' : PeriodicData} (h : IsPeriodic I)
    (h' : IsPeriodic I') : IsPeriodic (I.disjSum I') where
  translate_zero ι := by
    cases ι with
    | inl i => exact congrArg Sum.inl (h.translate_zero i)
    | inr i => exact congrArg Sum.inr (h'.translate_zero i)
  translate_add m n ι := by
    cases ι with
    | inl i => exact congrArg Sum.inl (h.translate_add m n i)
    | inr i => exact congrArg Sum.inr (h'.translate_add m n i)
  free n ι e := by
    cases ι with
    | inl i => exact h.free n i (Sum.inl.inj e)
    | inr i => exact h'.free n i (Sum.inr.inj e)
  finite_quot := by
    have := h.finite_quot
    have := h'.finite_quot
    let f : I.UnitQuot ⊕ I'.UnitQuot → (I.disjSum I').UnitQuot := Sum.elim
      (Quot.lift (fun i => (I.disjSum I').mkQuot 1 (Sum.inl i)) (by
        rintro i _ ⟨n, rfl⟩
        exact Quot.sound ⟨n, rfl⟩))
      (Quot.lift (fun i => (I.disjSum I').mkQuot 1 (Sum.inr i)) (by
        rintro i _ ⟨n, rfl⟩
        exact Quot.sound ⟨n, rfl⟩))
    refine Finite.of_surjective f fun c => ?_
    induction c using Quot.ind with
    | mk ι =>
      cases ι with
      | inl i => exact ⟨Sum.inl (I.mkQuot 1 i), rfl⟩
      | inr i => exact ⟨Sum.inr (I'.mkQuot 1 i), rfl⟩
  pos_translate n ι := by
    cases ι with
    | inl i => exact h.pos_translate n i
    | inr i => exact h'.pos_translate n i
  finite_components := by
    have := h.finite_components
    have := h'.finite_components
    exact inferInstanceAs (Finite (I.Component ⊕ I'.Component))
  componentOf_translate n ι := by
    cases ι with
    | inl i => exact congrArg Sum.inl (h.componentOf_translate n i)
    | inr i => exact congrArg Sum.inr (h'.componentOf_translate n i)
  weight_pos p := by
    cases p with
    | inl q => exact h.weight_pos q
    | inr q => exact h'.weight_pos q
theorem isUnit_symbolHom {I : PeriodicData} {T : I.Carrier → I.Carrier → ℂ}
    (h : SymbolInvertibleOnReals I T) (κ : InfiniteLattice.AmbientSpace) :
    IsUnit (symbolHom I I T (toComplexVec κ) : Module.End ℂ (I.UnitQuot → ℂ)) := by apply _root_.YangMills.Construction.Tower.FullSpace.JointWidthProof.isUnit_symbolHom <;> assumption
variable {L k : ℕ}
theorem isCompactValued_of_pauliCoeffs (hL : 0 < L) (ζ : FullSpace.FullField L k)
    (h : ∀ κ, (ζ.pauliCoeffs hL κ).im = 0) : ζ.IsCompactValued := by
  refine ⟨⟨fun b hb => mem_hermitianTraceless_of_im_eq_zero (ζ.1.2.1 b hb) fun a => ?_, ζ.1.2.2⟩,
    ⟨fun b hb => mem_hermitianTraceless_of_im_eq_zero (ζ.2.1.2.1 b hb) fun a => ?_, ζ.2.1.2.2⟩,
    ⟨fun b hb => mem_hermitianTraceless_of_im_eq_zero (ζ.2.2.2.1 b hb) fun a => ?_, ζ.2.2.2.2⟩⟩
  · exact h ⟨FieldComponent.background, (a, ⟨b, hb⟩)⟩
  · exact h ⟨FieldComponent.source, (a, ⟨b, hb⟩)⟩
  · exact h ⟨FieldComponent.coarse, (a, ⟨b, hb⟩)⟩
theorem cast_torusSide (L n : ℕ) : ((2 * L ^ n : ℕ) : ℝ) = PeriodicLattice.torusSide L n := by
  simp [PeriodicLattice.torusSide]
theorem xor_positive_opposite
    (hOr : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hS : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : 0 < n) (hj : j ≤ k)
    (b : Edge L n k j) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
  ((hOr ⟨L, hS, 1, ⟨n, hn⟩⟩ (PeriodicLattice.levelDepth k j) (by
    simp only [PeriodicLattice.levelDepth]
    have : (0 : ℤ) < n := by exact_mod_cast hn
    have : (j : ℤ) ≤ k := by exact_mod_cast hj
    simp only [PNat.mk_coe]
    omega)).1 b).2.2.2.2.2
end Bound
theorem secondDerivCloseToSymbol_holds (hLog : PeriodicOperators.LogDetSecondDerivs.Claim)
    (hTwo : FullSpace.OperatorFunctions.OperatorFunctionsTheorem)
    (hNum : PeriodicOperators.ParameterIndependence.Claim)
    (hExt : Tower.HessianAndComplexExtensionHolds)
    (hReal : FullSpace.OperatorFunctionsRealOnCompactFields)
    (hVal : FullSpace.FieldValues.FieldsAndValuesClaim)
    (hCells : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hPer : LocalKernels.IndexSetPeriodicity.Statement)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hOr : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hHol : Coordinates.ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement) :
    SecondDerivCloseToSymbol := by
  intro L hL hS k hk
  obtain ⟨⟨-, -, -, hlv, hlg⟩, hlogs, hsv, hsg⟩ := hTwo L hL hS k hk
  have hF : IsPeriodic (fieldPeriodicData L k hL) :=
    ((hPer L hS k).2 (LocalKernels.fieldIndices L k hL)).1
  have hV : IsPeriodic (vectorIndices L k) :=
    isPeriodic_disjSum (hIdx L hS k 0 (Nat.zero_le k)).2.1 (hIdx L hS k k le_rfl).2.1
  have hG : IsPeriodic (ghostIndices L k) :=
    isPeriodic_disjSum (hIdx L hS k 0 (Nat.zero_le k)).1 (hIdx L hS k k le_rfl).1
  obtain ⟨ρ₀, hρ₀, hreal⟩ := hReal L hL hS k hk
  have hfield : ∀ f : (fieldPeriodicData L k hL).Carrier → ℂ, (∀ κ, (f κ).im = 0) →
      IsSupBelow (fieldPeriodicData L k hL) f ρ₀ →
      (∀ ι' ι, (vectorOpFn L k hL f ι' ι).im = 0) ∧
        ∀ ι' ι, (ghostOpFn L k hL f ι' ι).im = 0 := by
    intro f hf hb
    obtain ⟨ζ, rfl⟩ := (hVal L hL k).2.1 f
    obtain ⟨-, -, -, e₄, e₅, -⟩ := (hVal L hL k).1 ζ
    rw [e₄, e₅]
    exact hreal ζ hb (isCompactValued_of_pauliCoeffs hL ζ hf)
  have hrv : IsRealOnRealFields (fieldPeriodicData L k hL) (vectorIndices L k) (vectorOpFn L k hL) :=
    isRealOnRealFields_of_eventually hHol hρ₀ fun f hf hb => (hfield f hf hb).1
  have hrg : IsRealOnRealFields (fieldPeriodicData L k hL) (ghostIndices L k) (ghostOpFn L k hL) :=
    isRealOnRealFields_of_eventually hHol hρ₀ fun f hf hb => (hfield f hf hb).2
  obtain ⟨_, -, -, -, -, hbv⟩ := hLog _ _ hF hV _ hlv (isUnit_symbolHom hsv)
  obtain ⟨_, -, -, -, -, hbg⟩ := hLog _ _ hF hG _ hlg (isUnit_symbolHom hsg)
  obtain ⟨s₁, Cv, cv, hCv, hcv, hbv⟩ := hbv hrv
  obtain ⟨s₂, Cg, cg, hCg, hcg, hbg⟩ := hbg hrg
  obtain ⟨ρv, Rv, hMv⟩ := hlv
  obtain ⟨ρg, Rg, hMg⟩ := hlg
  have hMv' := (hNum _ _ _ hF hV hV _ ρv Rv ρv Rv hMv hMv).1.1 ρv (max Rv Rg) hMv.radius_pos le_rfl
    (le_max_left _ _)
  have hMg' := (hNum _ _ _ hF hG hG _ ρg Rg ρg Rg hMg hMg).1.1 ρg (max Rv Rg) hMg.radius_pos le_rfl
    (le_max_right _ _)
  have hL1 : 1 < L := by
    have := hS.2
    omega
  refine ⟨Cv + Cg, min cv cg, add_pos hCv hCg, lt_min hcv hcg, ?_⟩
  have htend : Tendsto (fun n : ℕ => PeriodicLattice.torusSide L n) atTop atTop := by
    have h₁ : Tendsto (fun n : ℕ => (L : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hL1)
    exact h₁.const_mul_atTop two_pos
  obtain ⟨n₀, hn₀, hbig₀⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧
      max (max (s₁ : ℝ) (s₂ : ℝ)) (4 * max Rv Rg) < PeriodicLattice.torusSide L n₀ := by
    have := (htend.eventually_gt_atTop (max (max (s₁ : ℝ) (s₂ : ℝ)) (4 * max Rv Rg))).and
      (eventually_gt_atTop 0)
    obtain ⟨n₀, h₁, h₂⟩ := this.exists
    exact ⟨n₀, h₂, h₁⟩
  refine ⟨PeriodicLattice.torusSide L n₀, ⟨n₀, hn₀, rfl⟩, ?_⟩
  rintro _ - hge n hn rfl
  have hbig := lt_of_lt_of_le hbig₀ hge
  rw [← cast_torusSide] at hbig
  have hs₁ : s₁ ≤ 2 * L ^ n := by
    have : (s₁ : ℝ) < ((2 * L ^ n : ℕ) : ℝ) :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hbig
    exact_mod_cast this.le
  have hs₂ : s₂ ≤ 2 * L ^ n := by
    have : (s₂ : ℝ) < ((2 * L ^ n : ℕ) : ℝ) :=
      lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hbig
    exact_mod_cast this.le
  have hR : 4 * max Rv Rg < ((2 * L ^ n : ℕ) : ℝ) := lt_of_le_of_lt (le_max_right _ _) hbig
  have hs0 : 2 * L ^ n ≠ 0 := by
    have := pow_pos hL n
    omega
  have hcell := hCells L hS k n hn
  have hcl := hcell.2 (LocalKernels.fieldIndices L k hL)
  have hfin : Finite ((fieldPeriodicData L k hL).QuotMod (2 * L ^ n)) := by
    obtain ⟨hI, ⟨φ, hφ, -⟩, -⟩ := hcl
    exact Finite.of_injective φ hφ.1
  obtain ⟨N, ⟨e'⟩⟩ := Finite.exists_equiv_fin ((fieldPeriodicData L k hL).QuotMod (2 * L ^ n))
  have e : Fin N ≃ (fieldPeriodicData L k hL).QuotMod (2 * L ^ n) := e'.symm
  obtain ⟨-, hdv, -, hcv'⟩ := hbv (2 * L ^ n) hs₁ N e
  obtain ⟨-, hdg, -, hcg'⟩ := hbg (2 * L ^ n) hs₂ N e
  have hnear := (hlogs (max Rv Rg) ⟨ρv, hMv'⟩ ⟨ρg, hMg'⟩ n hn hR)
  have hb₀ : Finite (PositiveEdge L n k 0) := by
    have : Finite (Vertex L n k 0) :=
      (ClusterExpansion.RegionPolymers.sublattice_finite hL n
        (PeriodicLattice.levelDepth k 0)).to_subtype
    exact Finite.of_injective (fun b : PositiveEdge L n k 0 => (b.1.source, b.1.target)) fun _ _ h =>
      Subtype.ext (PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  have hbk : Finite (PositiveEdge L n k k) := by
    have : Finite (Vertex L n k k) :=
      (ClusterExpansion.RegionPolymers.sublattice_finite hL n
        (PeriodicLattice.levelDepth k k)).to_subtype
    exact Finite.of_injective (fun b : PositiveEdge L n k k => (b.1.source, b.1.target)) fun _ _ h =>
      Subtype.ext (PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let _ : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
  let _ : Fintype (PositiveEdge L n k k) := Fintype.ofFinite _
  have hβ := (hExt L n k hS hn hk).isComplexSecondDeriv
  have hc₀ := hcell.1 0 (Nat.zero_le k)
  have hck := hcell.1 k le_rfl
  have hwave : ∀ (κ : Fin 4 → ℂ) (c : Fin 4 → ℤ),
      (∀ μ, κ μ = (c μ : ℂ) * ((2 * Real.pi / ((2 * L ^ n : ℕ) : ℝ) : ℝ) : ℂ)) →
      ∀ ε : (fieldPeriodicData L k hL).UnitQuot → ℂ,
      (TorusResponseField.blochWaveField L n k hL κ ε).onQuotient hL =
        descendField (fieldPeriodicData L k hL) (2 * L ^ n)
          (blochWave (fieldPeriodicData L k hL) κ ε) := by
    intro κ c hκ ε
    have hex := exists_periodicField hL hcl (hc₀.1 .edge).1 (hck.1 .edge).1
      (xor_positive_opposite hOr hS hn (Nat.zero_le k)) (xor_positive_opposite hOr hS hn le_rfl)
      (blochWave (fieldPeriodicData L k hL) κ ε) (blochWave_translate hF hs0 c hκ ε)
    exact onQuotient_eq_descendField hL hcl (Classical.epsilon_spec hex)
  intro p hp εPlus εMinus
  have hp₂ := hp
  obtain ⟨c, hc⟩ : ∃ c : Fin 4 → ℤ, ∀ μ, p μ =
      (c μ : ℝ) * (2 * Real.pi / ((2 * L ^ n : ℕ) : ℝ)) := hp₂
  have hw₁ := hwave (toComplexVec p) c (fun μ => by
    simp only [toComplexVec]
    rw [hc μ]
    push_cast
    rfl) εPlus
  have hw₂ := hwave (-toComplexVec p) (-c) (fun μ => by
    simp only [toComplexVec, Pi.neg_apply]
    rw [hc μ]
    push_cast
    ring) εMinus
  rw [complexSecondDeriv_eq hL hcl hnear e hdv hdg hβ, hw₁, hw₂]
  have a₁ := hcv' p hp εPlus εMinus
  have a₂ := hcg' p hp εPlus εMinus
  have hA : 0 ≤ wNorm ((fieldPeriodicData L k hL).quotWeight 1) εPlus := Real.sqrt_nonneg _
  have hB : 0 ≤ wNorm ((fieldPeriodicData L k hL).quotWeight 1) εMinus := Real.sqrt_nonneg _
  have key := norm_neg_half_add_le hCv hCg (Nat.cast_nonneg (2 * L ^ n)) hA hB a₁ a₂
  convert key using 2
  simp only [FullSpace.secondVariationSymbol, FullSpace.vectorJet, FullSpace.ghostJet]
  ring
end YangMills.Construction.Tower.SecondDerivNearSymbol
end
