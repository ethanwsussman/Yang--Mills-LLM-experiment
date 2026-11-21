import YangMills.Construction.Towers.TracesOfTheParametrixOverTheHalfLineProof
import YangMills.Construction.Towers.AsymptoticsOfTheMassiveCoefficientProof
import YangMills.Construction.Towers.ChargedSymbolAtTheOrigin
import YangMills.Construction.Towers.ChargedSymbolOfTheConstantField
import YangMills.Construction.Towers.FormulaForTheMassiveCoefficient
import YangMills.Construction.Towers.NeutralLogarithmToTheSecondOrder
import YangMills.Construction.Towers.SectorsOfTheDensityOfTheConstantField
import YangMills.Construction.Towers.SymbolsOfTheParametrix
import Mathlib
set_option autoImplicit false
open Filter Asymptotics MeasureTheory Topology
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (torusAverage toComplexVec)
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
namespace MassiveStiffnessProof
open YangMills.Construction.Tower.MagneticWeyl YangMills.Construction.Tower.MagneticWeyl.FluxSecondOrder YangMills.Construction.Tower.Massive
theorem eq_zero_of_isBigO_cube {g : ℝ → ℂ} (h : g =O[𝓝 0] fun x : ℝ => |x| ^ 3) : g 0 = 0 := by
  obtain ⟨C, hC⟩ := h.bound
  have h0 := hC.self_of_nhds
  simpa using h0
theorem linear_quadratic_coeffs_eq_zero {a b : ℂ}
    (h : (fun x : ℝ => (x : ℂ) * a + (x : ℂ) ^ 2 * b) =O[𝓝 0] fun x : ℝ => |x| ^ 3) :
    a = 0 ∧ b = 0 := by
  obtain ⟨C, hC⟩ := h.bound
  have hC' : ∀ᶠ x : ℝ in 𝓝[≠] 0, x ≠ 0 ∧
      ‖(x : ℂ) * a + (x : ℂ) ^ 2 * b‖ ≤ C * ‖|x| ^ 3‖ :=
    (eventually_mem_nhdsWithin).mono (fun x hx => hx) |>.and (hC.filter_mono nhdsWithin_le_nhds)
  have ha : a = 0 := by
    have h1 : Tendsto (fun x : ℝ => a + (x : ℂ) * b) (𝓝[≠] 0) (𝓝 a) := by
      have hc : Continuous fun x : ℝ => a + (x : ℂ) * b := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun x : ℝ => a + (x : ℂ) * b) (𝓝[≠] 0) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun x : ℝ => C * x ^ 2) ?_ ?_
      · filter_upwards [hC'] with x hx
        obtain ⟨hx0, hx⟩ := hx
        have hp : 0 < |x| := abs_pos.mpr hx0
        have he : (x : ℂ) * a + (x : ℂ) ^ 2 * b = (x : ℂ) * (a + (x : ℂ) * b) := by ring
        rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs,
          abs_abs] at hx
        have h3 : |x| * ‖a + (x : ℂ) * b‖ ≤ |x| * (C * x ^ 2) := by
          calc |x| * ‖a + (x : ℂ) * b‖ ≤ C * |x| ^ 3 := hx
            _ = |x| * (C * x ^ 2) := by rw [← sq_abs x]; ring
        exact le_of_mul_le_mul_left h3 hp
      · have hc : Continuous fun x : ℝ => C * x ^ 2 := by fun_prop
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique h1 h2
  subst ha
  refine ⟨rfl, ?_⟩
  have h2 : Tendsto (fun _ : ℝ => b) (𝓝[≠] 0) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x : ℝ => C * |x|) ?_ ?_
    · filter_upwards [hC'] with x hx
      obtain ⟨hx0, hx⟩ := hx
      have hp : 0 < |x| ^ 2 := by positivity
      rw [mul_zero, zero_add, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_pow,
        Real.norm_eq_abs, abs_abs] at hx
      have h3 : |x| ^ 2 * ‖b‖ ≤ |x| ^ 2 * (C * |x|) := by
        calc |x| ^ 2 * ‖b‖ ≤ C * |x| ^ 3 := hx
          _ = |x| ^ 2 * (C * |x|) := by ring
      exact le_of_mul_le_mul_left h3 hp
    · have hc : Continuous fun x : ℝ => C * |x| := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique tendsto_const_nhds h2
theorem isBigO_cube_comp_two_mul {g : ℝ → ℂ} (h : g =O[𝓝 0] fun x : ℝ => |x| ^ 3) :
    (fun x : ℝ => g (2 * x)) =O[𝓝 0] fun x : ℝ => |x| ^ 3 := by
  have ht : Tendsto (fun x : ℝ => 2 * x) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun x : ℝ => 2 * x := by fun_prop
    simpa using hc.tendsto 0
  refine (h.comp_tendsto ht).trans (IsBigO.of_bound 8 (Eventually.of_forall fun x => ?_))
  simp only [Function.comp_def, abs_mul, abs_two, norm_pow, norm_mul, Real.norm_eq_abs, abs_abs]
  rw [mul_pow]
  norm_num
theorem coeffs_of_sector_expansions {R M P Q : ℝ → ℂ} {c A₁ A₄ c₁ c₂ b Y β : ℂ}
    (hS : ∀ᶠ x in 𝓝 (0 : ℝ), R x = c + 2 * P (2 * x) - 1 / 2 * M x - Q (2 * x))
    (hP : (fun x : ℝ => P x - (A₁ + (x : ℂ) ^ 2 * b)) =O[𝓝 0] fun x : ℝ => |x| ^ 3)
    (hQ : (fun x : ℝ => Q x - (A₄ + (x : ℂ) * c₁ + (x : ℂ) ^ 2 * c₂)) =O[𝓝 0]
      fun x : ℝ => |x| ^ 3)
    (hM : (fun x : ℝ => M x - (A₄ - (x : ℂ) ^ 2 / 2 * Y)) =O[𝓝 0] fun x : ℝ => |x| ^ 3)
    (hR : (fun x : ℝ => R x - R 0 - 1 / 2 * β * (x : ℂ) ^ 2) =O[𝓝 0] fun x : ℝ => |x| ^ 3) :
    c₁ = 0 ∧ 8 * b + 1 / 4 * Y - 4 * c₂ - 1 / 2 * β = 0 := by
  have hP0 : P 0 = A₁ := by
    have := eq_zero_of_isBigO_cube hP
    simpa [sub_eq_zero] using this
  have hQ0 : Q 0 = A₄ := by
    have := eq_zero_of_isBigO_cube hQ
    simpa [sub_eq_zero] using this
  have hM0 : M 0 = A₄ := by
    have := eq_zero_of_isBigO_cube hM
    simpa [sub_eq_zero] using this
  have hR0 : R 0 = c + 2 * A₁ - 1 / 2 * A₄ - A₄ := by
    have := hS.self_of_nhds
    simpa [hP0, hQ0, hM0] using this
  have hsum := ((hR.sub ((isBigO_cube_comp_two_mul hP).const_mul_left 2)).add
    (hM.const_mul_left (1 / 2))).add (isBigO_cube_comp_two_mul hQ)
  have hT : (fun x : ℝ => (x : ℂ) * (-2 * c₁) +
      (x : ℂ) ^ 2 * (8 * b + 1 / 4 * Y - 4 * c₂ - 1 / 2 * β)) =O[𝓝 0] fun x : ℝ => |x| ^ 3 := by
    refine hsum.congr' ?_ EventuallyEq.rfl
    filter_upwards [hS] with x hx
    rw [hx, hR0]
    push_cast
    ring
  obtain ⟨h1, h2⟩ := linear_quadratic_coeffs_eq_zero hT
  exact ⟨by simpa using h1, h2⟩
theorem integrableOn_Icc_pi {g : AmbientSpace → ℂ} (hg : Continuous g) :
    IntegrableOn g (Set.Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi) volume :=
  hg.continuousOn.integrableOn_compact isCompact_Icc
theorem torusAverage_two_mul_sub {g k : AmbientSpace → ℂ} (hg : Continuous g) (hk : Continuous k) :
    (torusAverage fun q => 2 * g q - k q) = 2 * torusAverage g - torusAverage k := by
  unfold torusAverage
  rw [integral_sub ((integrableOn_Icc_pi hg).const_mul 2) (integrableOn_Icc_pi hk), integral_const_mul]
  ring
def realSymbol (q : AmbientSpace) : ℝ := ∑ μ, (2 - 2 * Real.cos (q μ))
theorem latticeSymbol_toComplexVec (q : AmbientSpace) : latticeSymbol (toComplexVec q) = (realSymbol q : ℂ) := by
  simp [latticeSymbol, realSymbol, axisSymbol, toComplexVec]
theorem continuous_resolventAtReal {z : ℝ} (hz : 0 < z) : Continuous (resolventAtReal z) := by apply _root_.YangMills.Construction.Tower.MagneticWeyl.HalfLineTrace.continuous_shiftedInverse <;> assumption
theorem partialIn_partialIn_latticeSymbol (μ : Fin 4) (κ : Fin 4 → ℂ) :
    Massive.partialIn μ (Massive.partialIn μ latticeSymbol) κ =
      2 * Complex.cos (κ μ) := by apply _root_.YangMills.Construction.Tower.Massive.CoefficientAsymptoticsProof.partialIn_partialIn_latticeSymbol <;> assumption
theorem continuous_symbolSecondDerivFirst : Continuous symbolSecondDerivFirst := by
  have h : symbolSecondDerivFirst = fun q => 2 * Complex.cos (q 0 : ℂ) := by
    funext q
    simp [symbolSecondDerivFirst, partialIn_partialIn_latticeSymbol, toComplexVec]
  rw [h]
  fun_prop
theorem continuous_symbolSecondDerivSecond : Continuous symbolSecondDerivSecond := by
  have h : symbolSecondDerivSecond = fun q => 2 * Complex.cos (q 1 : ℂ) := by
    funext q
    simp [symbolSecondDerivSecond, partialIn_partialIn_latticeSymbol, toComplexVec]
  rw [h]
  fun_prop
theorem continuous_quadraticIntegrand {N' : ℕ} [NeZero N'] {z : ℝ} (hz : 0 < z)
    {τ₁ τ₂ : AmbientSpace → Matrix (Fin N') (Fin N') ℂ} (h₁ : Continuous τ₁) (h₂ : Continuous τ₂) :
    Continuous fun q =>
      -(1 / 2) * resolventAtReal z q ^ 2 * Matrices.RectangularMatrix.diagSum (τ₁ q ^ 2) +
        resolventAtReal z q * Matrices.RectangularMatrix.diagSum (τ₂ q) +
        (N' : ℂ) / 24 * resolventAtReal z q ^ 2 * symbolSecondDerivFirst q *
          symbolSecondDerivSecond q := by
  have hΥ := continuous_resolventAtReal hz
  have ht₁ : Continuous fun q => Matrices.RectangularMatrix.diagSum (τ₁ q ^ 2) := (h₁.pow 2).matrix_trace
  have ht₂ : Continuous fun q => Matrices.RectangularMatrix.diagSum (τ₂ q) := h₂.matrix_trace
  have hd₁ := continuous_symbolSecondDerivFirst
  have hd₂ := continuous_symbolSecondDerivSecond
  fun_prop
theorem pointwiseAdjoint_scalarMultiplier (q : AmbientSpace) :
    pointwiseAdjoint scalarMultiplier q = scalarMultiplier q := by
  simp [pointwiseAdjoint, scalarMultiplier, latticeSymbol_toComplexVec, Matrix.conjTranspose_smul]
theorem opNormValue_zero {N' : ℕ} [NeZero N'] :
    Matrices.RectangularMatrix.opNormValue (0 : Matrix (Fin N') (Fin N') ℂ) = 0 := by
  simp [Matrices.RectangularMatrix.opNormValue, OneLoopNotation.opNormOf]
theorem isWeylSymbol_zero {N' : ℕ} [NeZero N'] :
    IsWeylSymbol fun _ : AmbientSpace => (0 : Matrix (Fin N') (Fin N') ℂ) := by
  refine ⟨fun _ => 0, fun q => ?_, fun j _ => ?_⟩
  · simp [hasSum_zero]
  · simp only [opNormValue_zero, zero_mul]
    exact summable_zero
theorem weightedCoeffNorm_zero {N' : ℕ} [NeZero N'] :
    weightedCoeffNorm 3 (fun _ : AmbientSpace => (0 : Matrix (Fin N') (Fin N') ℂ)) = 0 := by
  have h : ∀ n, fourierCoeff (fun _ : AmbientSpace => (0 : Matrix (Fin N') (Fin N') ℂ)) n = 0 := by
    intro n
    ext i k
    simp [MagneticWeyl.fourierCoeff, torusAverage]
  simp [weightedCoeffNorm, h, opNormValue_zero]
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2 in
theorem hypotheses_scalar (hPsi : ApproxInverseSymbolBounds) {L : ℕ} {z φ : ℝ}
    (hA : IsBoundedBelowBy (addScalar (weylQuant L φ scalarMultiplier) z) (z / 2)) :
    Hypotheses (n := 1) L z 1 0 (fun _ => 0) (fun _ => 0) (fun _ => scalarMultiplier)
      (fun _ _ => 0) φ where
  isFiniteFourierSymbol := (hPsi 1).1
  isHermitian := pointwiseAdjoint_scalarMultiplier
  fourierCoeff_eq_zero := (hPsi 1).2.1
  eq_add q := by simp [scalarMultiplier]
  error_isWeylSymbol := isWeylSymbol_zero
  error_norm_le := by
    rw [weightedCoeffNorm_zero]
    simp
  boundedBelow := hA
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2 in
theorem hypotheses_charged {D C : ℝ} {τ₁ τ₂ : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ}
    {τ τr : ℝ → AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ} (h : ChargedSymbolExpansion D C τ₁ τ₂ τ τr)
    {L : ℕ} {z φ : ℝ} (hφ : |φ| ≤ Real.pi)
    (hA : IsBoundedBelowBy (addScalar (weylQuant L φ (τ φ)) z) (z / 2)) :
    Hypotheses L z D C τ₁ τ₂ τ τr φ where
  isFiniteFourierSymbol := h.isFiniteFourierSymbol φ hφ
  isHermitian := h.isHermitian φ hφ
  fourierCoeff_eq_zero := h.fourierCoeff_eq_zero φ hφ
  eq_add := h.eq_add φ hφ
  error_isWeylSymbol := h.error_isWeylSymbol φ hφ
  error_norm_le := h.error_norm_le φ hφ
  boundedBelow := hA
theorem eventually_abs_le_of_pos {ρ : ℝ} (hρ : 0 < ρ) : ∀ᶠ x : ℝ in 𝓝 0, |x| ≤ ρ := by
  have h : Tendsto (fun x : ℝ => |x|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ))
  exact h.eventually (Iic_mem_nhds hρ)
end MassiveStiffnessProof
open MassiveStiffnessProof YangMills.Construction.Tower.MagneticWeyl
  YangMills.Construction.Tower.MagneticWeyl.FluxSecondOrder YangMills.Construction.Tower.Massive
  YangMills.Construction.Tower.AbelianFieldDensity in
theorem massiveStiffnessFormula_holds
    (h₁ : ChargedSymbolExpansionExists)
    (h₂ : ChargedSymbolTraceSqAtZero)
    (h₃ : densitySectorDecomposition)
    (h₄ : NeutralLogSecondOrder)
    (h₅ : MagneticWeyl.FluxSecondOrder.Claim)
    (h₆ : AbelianFieldDensity.QuadraticResponseToConstantField)
    (h₇ : MagneticWeyl.ApproxInverseSymbolBounds) :
    ConstantSymbols.MassiveStiffnessFormula := by
  obtain ⟨D, C, τ₁, τ₂, τ, τr, hexp⟩ := h₁
  refine ⟨τ₁, τ₂, hexp.linear_isFiniteFourierSymbol, hexp.quadratic_isFiniteFourierSymbol,
    hexp.linear_isHermitian, hexp.quadratic_isHermitian, h₂ D C τ₁ τ₂ τ τr hexp, ?_⟩
  intro L hstand hL z hz
  obtain ⟨r₀, hr₀, C₀, hresp⟩ := h₆ z hz
  obtain ⟨hform, hresp⟩ := hresp L hL hstand
  refine ⟨hform, ?_⟩
  obtain ⟨c, hsec⟩ := h₃ L hstand z hz
  obtain ⟨C₁, hneu⟩ := h₄ L hstand z hz
  obtain ⟨m, hm, hm1, hmz⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ m ≤ z / 48 :=
    ⟨min 1 (z / 48), lt_min one_pos (by positivity), min_le_left _ _, min_le_right _ _⟩
  have hpi := Real.pi_gt_three
  have hrange : ∀ f : ℝ, |f| ≤ m → |f| ≤ Real.pi / 2 ∧ 24 * |Real.sin f| ≤ z / 2 := by
    intro f hf
    refine ⟨by linarith, ?_⟩
    have := Real.abs_sin_le_abs (x := f)
    linarith
  have hhalf : ∀ φ : ℝ, |φ| ≤ 2 * m → |φ / 2| ≤ m := by
    intro φ hφ
    rw [abs_div, abs_two]
    linarith
  have htwo : ∀ φ : ℝ, 2 * (φ / 2) = φ := fun φ => by ring
  have hscalar : ∀ φ : ℝ, |φ| ≤ 2 * m →
      UnitLatticeL2.IsBoundedBelowBy
        (OperatorCalculus.addScalar (weylQuant L φ scalarMultiplier) z) (z / 2) := by
    intro φ hφ
    have hf := hrange _ (hhalf φ hφ)
    have h := (hsec (φ / 2) hf.1 hf.2).2.1
    rwa [htwo] at h
  have hcharged : ∀ φ : ℝ, |φ| ≤ 2 * m →
      UnitLatticeL2.IsBoundedBelowBy
        (OperatorCalculus.addScalar (weylQuant L φ (τ φ)) z) (z / 2) := by
    intro φ hφ
    have hf := hrange _ (hhalf φ hφ)
    have h := ((hsec (φ / 2) hf.1 hf.2).2.2 (τ (2 * (φ / 2)))
      (hexp.massiveOp_eq L hstand (φ / 2) hf.1)).1
    rwa [htwo] at h
  have hr : 0 < 2 * m := by positivity
  obtain ⟨-, -, -, -, e₁⟩ := h₅ L 1 z hz 1 0 (2 * m) (fun _ => 0) (fun _ => 0)
    (fun _ => scalarMultiplier) (fun _ _ => 0) hr
    (fun φ hφ => hypotheses_scalar h₇ (hscalar φ hφ))
  obtain ⟨-, -, hc₁, hc₂, e₄⟩ := h₅ L 4 z hz D C (2 * m) τ₁ τ₂ τ τr hr
    (fun φ hφ => hypotheses_charged hexp (by linarith) (hcharged φ hφ))
  have hF : linearTerm z (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) = 0 := by
    simp [linearTerm, Matrices.RectangularMatrix.diagSum, torusAverage]
  simp only [hF, mul_zero, add_zero] at e₁
  have hzero : scaledLinearAngle L 0 = fun _ => 0 := by
    funext b
    simp [scaledLinearAngle]
  have hM : (fun f : ℝ => logTrace L z 0 (neutralSectorSymbol f) -
      (constantTerm 4 z - (f : ℂ) ^ 2 / 2 * torusAverage fun q =>
        resolvent z (toComplexVec q) *
          (axisSymbol 0 (toComplexVec q) + axisSymbol 1 (toComplexVec q)))) =O[𝓝 0]
      fun f : ℝ => |f| ^ 3 := by
    refine IsBigO.of_bound |C₁| ?_
    filter_upwards [eventually_abs_le_of_pos one_pos] with f hf
    refine (hneu f hf).trans ?_
    have h4 : f ^ 4 ≤ |f| ^ 3 := by
      have h0 : 0 ≤ |f| := abs_nonneg f
      calc f ^ 4 = |f| ^ 3 * |f| := by rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ f ^ 4)]; simp [abs_pow]; ring
        _ ≤ |f| ^ 3 * 1 := by gcongr
        _ = |f| ^ 3 := mul_one _
    rw [Real.norm_of_nonneg (by positivity)]
    calc C₁ * f ^ 4 ≤ |C₁| * f ^ 4 := by gcongr; exact le_abs_self _
      _ ≤ |C₁| * |f| ^ 3 := by gcongr
  have hR : (fun f : ℝ => densityAt z (scaledLinearAngle L f) (0 : FullSpace.Vertex L 0 0) -
      densityAt z (scaledLinearAngle L 0) (0 : FullSpace.Vertex L 0 0) -
      1 / 2 * (massiveStiffness hL z : ℂ) * (f : ℂ) ^ 2) =O[𝓝 0] fun f : ℝ => |f| ^ 3 := by
    refine IsBigO.of_bound C₀ ?_
    filter_upwards [eventually_abs_le_of_pos hr₀] with f hf
    have h := (hresp f hf).2
    rw [Real.norm_of_nonneg (by positivity), hzero]
    convert h using 3
    push_cast
    ring
  obtain ⟨-, h2⟩ := coeffs_of_sector_expansions
    (R := fun f : ℝ => densityAt z (scaledLinearAngle L f) (0 : FullSpace.Vertex L 0 0))
    (M := fun f : ℝ => logTrace L z 0 (neutralSectorSymbol f))
    (P := fun φ : ℝ => logTrace L z φ scalarMultiplier)
    (Q := fun φ : ℝ => logTrace L z φ (τ φ))
    (c := c) (β := (massiveStiffness hL z : ℂ))
    (by
      filter_upwards [eventually_abs_le_of_pos hm] with f hf
      have hf' := hrange f hf
      exact ((hsec f hf'.1 hf'.2).2.2 (τ (2 * f))
        (hexp.massiveOp_eq L hstand f hf'.1)).2)
    e₁ e₄ hM hR
  have hcube := torusAverage_two_mul_sub
    (continuous_quadraticIntegrand hz (τ₁ := fun _ => (0 : Matrix (Fin 1) (Fin 1) ℂ))
      (τ₂ := fun _ => 0) continuous_const continuous_const)
    (continuous_quadraticIntegrand hz hc₁ hc₂)
  have ht₀ : Matrices.RectangularMatrix.diagSum (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    simp [Matrices.RectangularMatrix.diagSum]
  have ht₁ : Matrices.RectangularMatrix.diagSum ((0 : Matrix (Fin 1) (Fin 1) ℂ) ^ 2) = 0 := by
    simp [Matrices.RectangularMatrix.diagSum]
  have hform' : (torusAverage fun q =>
      1 / 2 * resolvent z (toComplexVec q) ^ 2 * ((τ₁ q) ^ 2).trace -
        1 / 12 * resolvent z (toComplexVec q) ^ 2 *
            Massive.partialIn 0 (Massive.partialIn 0 latticeSymbol) (toComplexVec q) *
            Massive.partialIn 1 (Massive.partialIn 1 latticeSymbol) (toComplexVec q) -
          resolvent z (toComplexVec q) * (τ₂ q).trace) =
      2 * quadraticTerm z (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) (fun _ => 0) -
        quadraticTerm z τ₁ τ₂ := by
    refine Eq.trans ?_ hcube
    congr 1
    funext q
    change 1 / 2 * resolventAtReal z q ^ 2 * Matrices.RectangularMatrix.diagSum (τ₁ q ^ 2) -
        1 / 12 * resolventAtReal z q ^ 2 * symbolSecondDerivFirst q * symbolSecondDerivSecond q -
          resolventAtReal z q * Matrices.RectangularMatrix.diagSum (τ₂ q) = _
    rw [ht₀, ht₁]
    push_cast
    ring
  rw [hform']
  linear_combination (-2) * h2
end YangMills.Construction.Tower.ConstantFieldSymbols
end
