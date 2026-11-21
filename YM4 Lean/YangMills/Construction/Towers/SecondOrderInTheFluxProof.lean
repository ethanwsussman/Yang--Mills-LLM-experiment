import YangMills.Construction.Towers.AdjointOfAQuantization
import YangMills.Construction.Towers.DensityOfAResolventFromAParametrix
import YangMills.Construction.Towers.RemainderOfTheParametrix
import YangMills.Construction.Towers.SecondOrderInTheFlux
import YangMills.Construction.Towers.TheCoefficientsOfTheExpansionInTheFlux
import YangMills.Construction.Towers.TheDensityIsABoundedLinearFunctional
import YangMills.Construction.Towers.TracesOfTheParametrixOverTheHalfLine
import Mathlib
set_option autoImplicit false
open Filter Asymptotics Set YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.OneLoopNotation
open YangMills.Construction.PeriodicOperators (torusAverage toComplexVec)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.MagneticWeyl
namespace FluxSecondOrder
open FluxExpansion
theorem hasDerivAt_latticeSymbol_update (k : Fin 4 → ℂ) (μ : Fin 4) (t : ℂ) :
    HasDerivAt (fun t : ℂ => Massive.latticeSymbol (Function.update k μ t))
      (2 * Complex.sin t) t := by
  have h : HasDerivAt (fun t : ℂ => ∑ ν : Fin 4,
      Massive.axisSymbol ν (Function.update k μ t))
      (∑ ν : Fin 4, if ν = μ then 2 * Complex.sin t else 0) t := by
    refine HasDerivAt.fun_sum fun ν _ => ?_
    by_cases hν : ν = μ
    · subst hν
      simp only [Massive.axisSymbol, Function.update_self, if_true]
      have := ((Complex.hasDerivAt_cos t).const_mul (2 : ℂ)).const_sub (2 : ℂ)
      convert this using 1
      ring
    · simp only [Massive.axisSymbol, Function.update_of_ne hν, if_neg hν]
      exact hasDerivAt_const _ _
  simpa [Massive.latticeSymbol] using h
theorem partialIn_latticeSymbol (μ : Fin 4) :
    Massive.partialIn μ Massive.latticeSymbol =
      fun k => 2 * Complex.sin (k μ) := by
  funext k
  exact (hasDerivAt_latticeSymbol_update k μ (k μ)).deriv
theorem partialIn_partialIn_latticeSymbol (μ : Fin 4) (q : AmbientSpace) :
    Massive.partialIn μ
        (Massive.partialIn μ Massive.latticeSymbol) (toComplexVec q) =
      baseSymbolSecondDeriv μ q := by
  rw [partialIn_latticeSymbol]
  have h : (fun t : ℂ => 2 * Complex.sin (Function.update (toComplexVec q) μ t μ)) =
      fun t => 2 * Complex.sin t := by
    funext t
    simp
  simp only [Massive.partialIn, h]
  exact ((Complex.hasDerivAt_sin _).const_mul (2 : ℂ)).deriv
theorem trace_scalarOp_sub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {τ : BddOp H → ℂ} {m : ℕ} (h : AbelianFieldDensity.IsBoundedLinearTrace τ m) (c : ℂ)
    (T : BddOp H) : τ (scalarOp c - T) = c * (m : ℂ) - τ T := by
  obtain ⟨hl, -, hid⟩ := h
  have h0 : τ 0 = 0 := by
    have := hl (ContinuousLinearMap.id ℂ H) (ContinuousLinearMap.id ℂ H) (-1)
    simp only [neg_smul, one_smul, add_neg_cancel, hid] at this
    rw [this]
    ring
  have hc : τ (scalarOp c) = c * (m : ℂ) := by
    have := hl 0 (ContinuousLinearMap.id ℂ H) c
    rw [zero_add, h0, zero_add, hid] at this
    exact this
  have := hl (scalarOp c) T (-1)
  rw [sub_eq_add_neg, ← neg_one_smul ℂ T, this, hc]
  ring
theorem integral_inv_half_add_sq_le {z y : ℝ} (hz : 0 < z) (hy : 0 ≤ y) :
    ∫ w in (0 : ℝ)..y, ((z / 2 + w) ^ 2)⁻¹ ≤ 2 / z := by
  have hd : ∀ w ∈ uIcc (0 : ℝ) y, HasDerivAt (fun w : ℝ => -(z / 2 + w)⁻¹) (((z / 2 + w) ^ 2)⁻¹) w := by
    intro w hw
    rw [uIcc_of_le hy] at hw
    have hne : z / 2 + w ≠ 0 := by have := hw.1; positivity
    have := ((hasDerivAt_id' w).const_add (z / 2)).fun_inv hne
    exact this.neg.congr_deriv (by field_simp)
  have hc : ContinuousOn (fun w : ℝ => ((z / 2 + w) ^ 2)⁻¹) (uIcc 0 y) := by
    rw [uIcc_of_le hy]
    refine ContinuousOn.inv₀ (by fun_prop) fun w hw => ?_
    have := hw.1
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  have h1 : 0 < (z / 2 + y)⁻¹ := by positivity
  have h2 : (z / 2 + 0)⁻¹ = 2 / z := by rw [add_zero, inv_div]
  simp only [h2]
  linarith
end FluxSecondOrder
open FluxSecondOrder FluxExpansion in
theorem FluxSecondOrder.bound_at_flux
    (hDens : ResolventDensityViaParametrix)
    (hLim : OperatorCalculus.Calculus.Statement)
    (hTrace : AbelianFieldDensity.TraceIsBoundedLinear)
    (hAdj : WeylQuantAdjoint)
    (L n : ℕ) [NeZero n] (z : ℝ) (hz : 0 < z) (D C K : ℝ) (hK : 0 ≤ K)
    (σ₁ σ₂ : AmbientSpace → Matrix (Fin n) (Fin n) ℂ) (σ σr : ℝ → AmbientSpace → Matrix (Fin n) (Fin n) ℂ)
    (φ : ℝ) (hφ : |φ| ≤ 1) (hc : Hypotheses L z D C σ₁ σ₂ σ σr φ)
    (hRem : ∀ s : ℝ, z ≤ s → IsWeylSymbol (approxInverse s φ σ₁ σ₂) ∧
      ∃ e : AmbientSpace → Matrix (Fin n) (Fin n) ℂ, IsWeylSymbol e ∧
        moyalProduct φ (approxInverse s φ σ₁ σ₂)
            (fun q => (baseSymbolMatrix n q + (φ : ℂ) • σ₁ q + (φ : ℂ) ^ 2 • σ₂ q + σr φ q) +
              (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) =
          (fun q => 1 + e q) ∧
        weightedCoeffNorm 0 e ≤ K * (|φ| ^ 3 + weightedCoeffNorm 3 (σr φ)) / s)
    (g₀ g₁ g₂ : ℝ → ℂ) (c₀ c₁ c₂ : ℂ)
    (hg₀ : ContinuousOn g₀ (Ici 0)) (hg₁ : ContinuousOn g₁ (Ici 0)) (hg₂ : ContinuousOn g₂ (Ici 0))
    (hsum : ∀ w : ℝ, 0 ≤ w →
      (torusAverage fun q => Matrices.RectangularMatrix.diagSum (approxInverse (z + w) φ σ₁ σ₂ q)) =
        g₀ w + (φ : ℂ) * g₁ w + (φ : ℂ) ^ 2 * g₂ w)
    (hl₀ : Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, ((n : ℂ) * (((1 + w)⁻¹ : ℝ) : ℂ) - g₀ w)) atTop
      (nhds c₀))
    (hl₁ : Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, -g₁ w) atTop (nhds c₁))
    (hl₂ : Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, -g₂ w) atTop (nhds c₂)) :
    ‖logTrace L z φ (σ φ) - (c₀ + (φ : ℂ) * c₁ + (φ : ℂ) ^ 2 * c₂)‖ ≤
      (n : ℝ) * (K * (1 + |C|)) * (2 / z) * |φ| ^ 3 := by
  have hN : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hsym : IsWeylSymbol (σ φ) := hc.isFiniteFourierSymbol.1
  set A := weylQuant L φ (σ φ) with hA
  have hherm : pointwiseAdjoint (σ φ) = σ φ := funext hc.isHermitian
  have hAself : IsSelfAdjointOp A := by
    have := (hAdj L φ n n (σ φ) hsym).2
    rw [hherm] at this
    exact this
  obtain ⟨hSum, -, -, -, -, -, hLog⟩ := hLim (VectorL2 L n) (VectorL2 L n)
  set S := addScalar A z with hS
  have hSself : IsSelfAdjointOp S := (hSum A hAself z 0).1
  obtain ⟨hinv, hnc, -, hint, -, huniq, hlog⟩ := hLog S (z / 2) hSself (by positivity) hc.boundedBelow
  obtain ⟨hlin, hpass⟩ := (hTrace L 0).2.2 n hN
  obtain ⟨-, hconv, hτc, -, hτl, hτeq⟩ := hpass (resolventDiff S) hnc (by
    obtain ⟨l, hl⟩ := hint
    exact ⟨l, by simpa only [abs_norm] using hl⟩)
  have hX : AbelianFieldDensity.opIntegralIoi (resolventDiff S) =
      opLog S := huniq.unique hconv hlog
  have hlim : Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y,
      AbelianFieldDensity.vecTraceAt (resolventDiff S w) 0) atTop
      (nhds (logTrace L z φ (σ φ))) := by
    have : logTrace L z φ (σ φ) =
        AbelianFieldDensity.complexIntegralIoi
          fun w => AbelianFieldDensity.vecTraceAt (resolventDiff S w) 0 := by
      rw [← hτeq, hX]
      rfl
    rw [this]
    exact hτl
  set R : ℝ → BddOp (VectorL2 L n) := fun w => inverseOp (addScalar S w)
    with hR
  have hτT : ∀ w, AbelianFieldDensity.vecTraceAt (resolventDiff S w) 0 =
      (n : ℂ) * (((1 + w)⁻¹ : ℝ) : ℂ) - AbelianFieldDensity.vecTraceAt (R w) 0 := by
    intro w
    have := trace_scalarOp_sub hlin (((1 + w)⁻¹ : ℝ) : ℂ) (R w)
    rw [mul_comm] at this
    exact this
  set E : ℝ → ℂ := fun w => AbelianFieldDensity.vecTraceAt (R w) 0 -
    (g₀ w + (φ : ℂ) * g₁ w + (φ : ℂ) ^ 2 * g₂ w) with hE
  have hEb : ∀ w : ℝ, 0 ≤ w →
      ‖E w‖ ≤ ((n : ℝ) * (K * (1 + |C|)) * |φ| ^ 3) * ((z / 2 + w) ^ 2)⁻¹ := by
    intro w hw
    have hs : z ≤ z + w := by linarith
    obtain ⟨hρ, e, he, hstar, hbd⟩ := hRem (z + w) hs
    have hstar' : moyalProduct φ (approxInverse (z + w) φ σ₁ σ₂)
        (fun q => σ φ q + ((z + w : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) =
        (fun q => 1 + e q) := by
      rw [← hstar]
      congr 1
      funext q
      rw [hc.eq_add q]
      rfl
    have h := hDens L n φ z w hz hw (σ φ) _ e hsym hρ he hc.isHermitian hc.boundedBelow hstar'
    rw [hsum w hw] at h
    have hnorm : weightedCoeffNorm 3 (σr φ) ≤ |C| * |φ| ^ 3 :=
      hc.error_norm_le.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    have hzw : 0 < z / 2 + w := by positivity
    have he' : weightedCoeffNorm 0 e ≤ K * (1 + |C|) * |φ| ^ 3 * (z / 2 + w)⁻¹ := by
      refine hbd.trans ?_
      rw [div_eq_mul_inv]
      have h1 : K * (|φ| ^ 3 + weightedCoeffNorm 3 (σr φ)) ≤ K * (1 + |C|) * |φ| ^ 3 := by
        have : |φ| ^ 3 + weightedCoeffNorm 3 (σr φ) ≤ (1 + |C|) * |φ| ^ 3 := by linarith
        calc K * (|φ| ^ 3 + weightedCoeffNorm 3 (σr φ)) ≤ K * ((1 + |C|) * |φ| ^ 3) :=
              mul_le_mul_of_nonneg_left this hK
          _ = K * (1 + |C|) * |φ| ^ 3 := by ring
      have h2 : (z + w)⁻¹ ≤ (z / 2 + w)⁻¹ := inv_anti₀ hzw (by linarith)
      have h3 : 0 ≤ K * (1 + |C|) * |φ| ^ 3 := by positivity
      calc K * (|φ| ^ 3 + weightedCoeffNorm 3 (σr φ)) * (z + w)⁻¹
          ≤ K * (1 + |C|) * |φ| ^ 3 * (z + w)⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ K * (1 + |C|) * |φ| ^ 3 * (z / 2 + w)⁻¹ := mul_le_mul_of_nonneg_left h2 h3
    calc ‖E w‖ ≤ (n : ℝ) * weightedCoeffNorm 0 e * (z / 2 + w)⁻¹ := h
      _ ≤ (n : ℝ) * (K * (1 + |C|) * |φ| ^ 3 * (z / 2 + w)⁻¹) * (z / 2 + w)⁻¹ := by
          gcongr
      _ = _ := by
          rw [pow_two, mul_inv]
          ring
  have hc1 : ContinuousOn (fun w : ℝ => (n : ℂ) * (((1 + w)⁻¹ : ℝ) : ℂ)) (Ici 0) := by
    refine continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ?_)
    refine ContinuousOn.inv₀ (by fun_prop) fun w hw => ?_
    have : (0 : ℝ) ≤ w := hw
    positivity
  have hcT : ContinuousOn (fun w => AbelianFieldDensity.vecTraceAt (resolventDiff S w) 0)
      (Ici 0) := hτc
  have hcR : ContinuousOn (fun w => AbelianFieldDensity.vecTraceAt (R w) 0) (Ici 0) := by
    have : (fun w => AbelianFieldDensity.vecTraceAt (R w) 0) = fun w =>
        (n : ℂ) * (((1 + w)⁻¹ : ℝ) : ℂ) -
          AbelianFieldDensity.vecTraceAt (resolventDiff S w) 0 := by
      funext w
      rw [hτT w]
      ring
    rw [this]
    exact hc1.sub hcT
  have hii : ∀ {f : ℝ → ℂ}, ContinuousOn f (Ici 0) → ∀ y : ℝ, 0 ≤ y →
      IntervalIntegrable f MeasureTheory.volume 0 y := by
    intro f hf y hy
    refine ContinuousOn.intervalIntegrable (hf.mono ?_)
    rw [uIcc_of_le hy]
    exact Icc_subset_Ici_self
  have hsplit : ∀ y : ℝ, 0 ≤ y → (∫ w in (0 : ℝ)..y, E w) =
      (∫ w in (0 : ℝ)..y, ((n : ℂ) * (((1 + w)⁻¹ : ℝ) : ℂ) - g₀ w)) +
        (φ : ℂ) * (∫ w in (0 : ℝ)..y, -g₁ w) + (φ : ℂ) ^ 2 * (∫ w in (0 : ℝ)..y, -g₂ w) -
        ∫ w in (0 : ℝ)..y, AbelianFieldDensity.vecTraceAt (resolventDiff S w) 0 := by
    intro y hy
    have i0 : IntervalIntegrable (fun w : ℝ => (n : ℂ) * (((1 + w)⁻¹ : ℝ) : ℂ) - g₀ w)
        MeasureTheory.volume 0 y := hii (hc1.sub hg₀) y hy
    have i1 : IntervalIntegrable (fun w : ℝ => (φ : ℂ) * -g₁ w) MeasureTheory.volume 0 y :=
      (hii hg₁.neg y hy).const_mul _
    have i2 : IntervalIntegrable (fun w : ℝ => (φ : ℂ) ^ 2 * -g₂ w) MeasureTheory.volume 0 y :=
      (hii hg₂.neg y hy).const_mul _
    have iT : IntervalIntegrable
        (fun w : ℝ => AbelianFieldDensity.vecTraceAt (resolventDiff S w) 0)
        MeasureTheory.volume 0 y := hii hcT y hy
    have i01 : IntervalIntegrable
        (fun w : ℝ => ((n : ℂ) * (((1 + w)⁻¹ : ℝ) : ℂ) - g₀ w) + (φ : ℂ) * -g₁ w)
        MeasureTheory.volume 0 y := i0.add i1
    have i012 : IntervalIntegrable
        (fun w : ℝ => ((n : ℂ) * (((1 + w)⁻¹ : ℝ) : ℂ) - g₀ w) + (φ : ℂ) * -g₁ w +
          (φ : ℂ) ^ 2 * -g₂ w) MeasureTheory.volume 0 y := i01.add i2
    have hcongr : (∫ w in (0 : ℝ)..y, E w) = ∫ w in (0 : ℝ)..y,
        (((n : ℂ) * (((1 + w)⁻¹ : ℝ) : ℂ) - g₀ w) + (φ : ℂ) * -g₁ w + (φ : ℂ) ^ 2 * -g₂ w -
          AbelianFieldDensity.vecTraceAt (resolventDiff S w) 0) := by
      refine intervalIntegral.integral_congr fun w _ => ?_
      simp only [hE, hτT w]
      ring
    rw [hcongr, intervalIntegral.integral_sub i012 iT, intervalIntegral.integral_add i01 i2,
      intervalIntegral.integral_add i0 i1, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hEl : Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, E w) atTop
      (nhds (c₀ + (φ : ℂ) * c₁ + (φ : ℂ) ^ 2 * c₂ - logTrace L z φ (σ φ))) := by
    have h := ((hl₀.add (hl₁.const_mul (φ : ℂ))).add (hl₂.const_mul ((φ : ℂ) ^ 2))).sub hlim
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    exact (hsplit y hy).symm
  have hM : 0 ≤ (n : ℝ) * (K * (1 + |C|)) * |φ| ^ 3 := by positivity
  have hbound : ∀ᶠ y : ℝ in atTop, ‖∫ w in (0 : ℝ)..y, E w‖ ≤
      (n : ℝ) * (K * (1 + |C|)) * (2 / z) * |φ| ^ 3 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    have hcI : ContinuousOn (fun w : ℝ => ((n : ℝ) * (K * (1 + |C|)) * |φ| ^ 3) *
        ((z / 2 + w) ^ 2)⁻¹) (uIcc 0 y) := by
      rw [uIcc_of_le hy]
      refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun w hw => ?_)
      have := hw.1
      positivity
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) hy
      (Eventually.of_forall fun w hw => hEb w hw.1.le) hcI.intervalIntegrable
    refine h1.trans ?_
    rw [intervalIntegral.integral_const_mul]
    calc _ ≤ ((n : ℝ) * (K * (1 + |C|)) * |φ| ^ 3) * (2 / z) :=
          mul_le_mul_of_nonneg_left (integral_inv_half_add_sq_le hz hy) hM
      _ = _ := by ring
  have hfin := le_of_tendsto hEl.norm hbound
  rw [norm_sub_rev]
  exact hfin
open FluxSecondOrder FluxExpansion in
theorem FluxSecondOrder.claim_holds
    (hRem : ApproxInverseRemainder)
    (hDens : ResolventDensityViaParametrix)
    (hTr : HalfLineTraceLimits)
    (hCoef : FluxCoefficientsAreTrigPolys)
    (hLim : OperatorCalculus.Calculus.Statement)
    (hTrace : AbelianFieldDensity.TraceIsBoundedLinear)
    (hAdj : WeylQuantAdjoint) :
    FluxSecondOrder.Claim := by
  intro L n _ z hz D C r σ₁ σ₂ σ σr hr hc
  obtain ⟨t₁, t₂, c₁, c₂⟩ := hCoef n D C r σ₁ σ₂ σ σr hr fun φ hφ =>
    ⟨(hc φ hφ).isFiniteFourierSymbol, (hc φ hφ).fourierCoeff_eq_zero, (hc φ hφ).eq_add,
      (hc φ hφ).error_isWeylSymbol, (hc φ hφ).error_norm_le⟩
  refine ⟨t₁, t₂, c₁, c₂, ?_⟩
  obtain ⟨K, hK0, hK⟩ := hRem n z hz σ₁ σ₂ t₁.1 t₂.1
  obtain ⟨hg₀, hg₁, hg₂, hsum, hl₀, hl₁, hl₂⟩ := hTr n z hz σ₁ σ₂ c₁ c₂
  have hfirst : ∀ q, symbolSecondDerivFirst q = baseSymbolSecondDeriv 0 q :=
    partialIn_partialIn_latticeSymbol 0
  have hsecond : ∀ q, symbolSecondDerivSecond q = baseSymbolSecondDeriv 1 q :=
    partialIn_partialIn_latticeSymbol 1
  have hcoef₂ : quadraticTerm z σ₁ σ₂ = torusAverage fun q =>
      -(1 / 2) * shiftedInverse z q ^ 2 * Matrices.RectangularMatrix.diagSum (σ₁ q ^ 2) +
        shiftedInverse z q * Matrices.RectangularMatrix.diagSum (σ₂ q) +
        (n : ℂ) / 24 * shiftedInverse z q ^ 2 * baseSymbolSecondDeriv 0 q * baseSymbolSecondDeriv 1 q := by
    simp only [quadraticTerm, hfirst, hsecond]
    rfl
  have hpos : 0 < min r 1 := lt_min hr one_pos
  refine IsBigO.of_bound ((n : ℝ) * (K * (1 + |C|)) * (2 / z)) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with φ hφ
  have hφ' : |φ| < min r 1 := by simpa [Real.norm_eq_abs] using hφ
  have hφr : |φ| ≤ r := (hφ'.trans_le (min_le_left _ _)).le
  have hφ1 : |φ| ≤ 1 := (hφ'.trans_le (min_le_right _ _)).le
  have h := FluxSecondOrder.bound_at_flux hDens hLim hTrace hAdj L n z hz D C K hK0 σ₁ σ₂ σ σr φ hφ1
    (hc φ hφr) (fun s hs => hK s φ hs hφ1 (σr φ) (hc φ hφr).error_isWeylSymbol)
    _ _ _ (constantTerm n z) (linearTerm z σ₁) (quadraticTerm z σ₁ σ₂)
    hg₀ hg₁ hg₂ (fun w hw => hsum w φ hw) hl₀ hl₁ (hcoef₂ ▸ hl₂)
  simpa [Real.norm_eq_abs, abs_abs, abs_pow] using h
end YangMills.Construction.Tower.MagneticWeyl
end
