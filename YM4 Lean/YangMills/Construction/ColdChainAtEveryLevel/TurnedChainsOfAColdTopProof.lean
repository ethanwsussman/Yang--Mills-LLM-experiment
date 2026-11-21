import YangMills.Construction.ColdChainAtEveryLevel.ComparisonOfAgreeingPairsProof
import YangMills.Construction.ColdChainAtEveryLevel.LocalBoundsOverATurnedTop
import YangMills.Construction.ColdChainAtEveryLevel.TurnedChainsOfAColdTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
open Filter Topology
namespace YangMills.Construction
namespace ColdTopTwistedChains
open BlockAverages GaugeMap Analytic CoordinateSeminorms
  YangMills.Construction.BlockAverages.ChartCoordinates
  YangMills.Construction.BlockAverages.ComplexChartCoordinates SpanVariations ComplexFamilies
open TwistedTops
variable {F : BlockFrame}
structure PairData (a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) {k : ℕ}
    (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (Wf : (Fin k → ℂ) → ComplexChainChart F) : Prop where
  side_odd : Odd F.blockSide
  del_pos : 0 < del
  Ca₄_pos : 0 < Ca₄
  Ct_pos : 0 < Ct
  cT_pos : 0 < cT
  CT_pos : 0 < CT
  Ca_pos : 0 < Ca
  C_pos : 0 < C
  C₀_pos : 0 < C₀
  s_pos : 0 < s
  r_pos : 0 < r
  r'_pos : 0 < r'
  r'_le_r : r' ≤ r
  r_le_c : r ≤ c
  r_lt_c₁ : r < c₁
  smallness : 8 * Ca₄ * C * (2 * r + r') ≤ 1
  estimate : ReferenceFormWeightedEstimate a θ del Ca₄ S V
  taylor : ActionTaylorBounds a θ del Ct cT CT s S V
  twisted : TwistedTotalBounds a θ del Ca c C s S V b X
  regular : ∀ U : ChainChart F, supWeightedNorm S del (referenceFieldChain S V) U ≤ c₁ →
    ChartIsRegular S (referenceFieldChain S V) U
  family : IsComplexCriticalFamily a θ del C₀ r r' s S V b X Wf
variable {a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top} {k : ℕ}
  {b : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {Wf : (Fin k → ℂ) → ComplexChainChart F}
theorem neg_one_smul_imag (x : imaginaryQuaternions) : (-1 : ℝ) • x = -x := neg_one_smul ℝ x
theorem sum_norm_ofRealVec (ζ : Fin k → ℝ) : ∑ l, ‖ofRealVec ζ l‖ = ∑ l, |ζ l| := by
  simp [SpanVariations.ofRealVec, Complex.norm_real]
theorem supWeightedNorm_zeroChart (hL : 0 < F.blockSide) (R : F.FieldChain) :
    supWeightedNorm S del R (zeroChart F) = 0 := by
  have h := supWeightedNorm_smul S hL del R (zeroChart F) 0
  have e : chartMove (zeroChart F) (zeroChart F) 0 = zeroChart F := by
    apply chainChart_ext
    · funext p i
      simp [chartMove, zeroChart]
    · funext j p i
      simp [chartMove, zeroChart]
  rw [e] at h
  simpa using h
def realPartChart (Wf : (Fin k → ℂ) → ComplexChainChart F) (ζ : Fin k → ℝ) : ChainChart F := (Wf (ofRealVec ζ)).re
theorem supWeightedNorm_realPartChart_le (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf)
    {ζ : Fin k → ℝ} (hζ : ∑ l, |ζ l| < r') :
    supWeightedNorm S del (referenceFieldChain S V) (realPartChart Wf ζ) ≤ r ∧
      supWeightedNorm S del (referenceFieldChain S V) (realPartChart Wf ζ) ≤ C₀ * (s + ∑ l, |ζ l|) := by
  have hζ' : ∑ l, ‖ofRealVec ζ l‖ < r' := by rwa [sum_norm_ofRealVec]
  have h1 : supWeightedNorm S del (referenceFieldChain S V) (realPartChart Wf ζ) ≤
      complexSupWeightedNorm S del (referenceFieldChain S V) (Wf (ofRealVec ζ)) :=
    le_add_of_nonneg_right (supWeightedNorm_nonneg _ _ _ _)
  refine ⟨h1.trans (h.family.small _ hζ'), h1.trans ?_⟩
  have := h.family.norm_le _ hζ'
  rwa [sum_norm_ofRealVec] at this
theorem complexFirstVariation_realPartChart (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf)
    {ζ : Fin k → ℝ} (hζ : ∑ l, |ζ l| < r') (A : ChainChart F) :
    complexFirstVariation a S (referenceFieldChain S V) (realChart (realPartChart Wf ζ))
        (complexTwistedTop b X (ofRealVec ζ) V) A =
      complexFirstVariation a S (referenceFieldChain S V) (Wf (ofRealVec ζ)) (complexTwistedTop b X (ofRealVec ζ) V) A := by
  refine complexFirstVariation_congr_point h.side_odd _ _ A ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ ?_
  have := h.family.real ζ hζ
  exact ⟨fun x hx => (this.1 x hx).symm, fun j hj x hx => (this.2 j hj x hx).symm⟩
theorem sum_abs_le_of_pair (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf) {ζ : Fin k → ℝ}
    (hζ : ∑ l, |ζ l| < r') : ∑ l, |ζ l| ≤ c := hζ.le.trans (h.r'_le_r.trans h.r_le_c)
theorem realPartChart_isCriticalAlong (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf)
    {ζ : Fin k → ℝ} (hζ : ∑ l, |ζ l| < r') (A : ChainChart F)
    (hA : InGaugeSlice S V (referenceFieldChain S V 0) A.fine) :
    IsStationaryAlong a S (referenceFieldChain S V) (rotatedField (bondSpread b X ζ) V) (realPartChart Wf ζ) A := by
  obtain ⟨h1, -⟩ := supWeightedNorm_realPartChart_le h hζ
  have hr := hasDerivAt_chartAction_of_complexFirstVariation h.side_odd h.del_pos.le h.twisted h.regular ζ
    (sum_abs_le_of_pair h hζ) (realPartChart Wf ζ) A (h1.trans h.r_le_c) (lt_of_le_of_lt h1 h.r_lt_c₁)
  have e : complexFirstVariation a S (referenceFieldChain S V) (realChart (realPartChart Wf ζ))
      (complexTwistedTop b X (fun l => (ζ l : ℂ)) V) A = 0 := by
    have := complexFirstVariation_realPartChart h hζ A
    have hc := h.family.critical (ofRealVec ζ) (by rwa [sum_norm_ofRealVec]) A hA
    rw [hc] at this
    exact this
  have := hr.1
  rw [e] at this
  unfold IsStationaryAlong
  simpa using this
theorem referenceSecondDeriv_chartMove (hT : ActionTaylorBounds a θ del Ct cT CT s S V) (U U' A : ChainChart F)
    (t : ℝ) :
    referenceSecondDeriv a S (referenceFieldChain S V) V (chartMove U U' t) A =
      referenceSecondDeriv a S (referenceFieldChain S V) V U A +
        t * referenceSecondDeriv a S (referenceFieldChain S V) V U' A := by
  have e : chartMove U U' t = chartSum U (chartSmul t U') := by
    apply chainChart_ext
    · funext p i
      simp [chartMove, chartSum, chartSmul, chartZero]
    · funext j p i
      simp [chartMove, chartSum, chartSmul, chartZero]
  rw [e, hT.hessian_add_left, hT.hessian_smul_left]
theorem referenceSecondDeriv_zeroChart (hT : ActionTaylorBounds a θ del Ct cT CT s S V) (B : ChainChart F) :
    referenceSecondDeriv a S (referenceFieldChain S V) V (zeroChart F) B = 0 := by
  have h := hT.hessian_smul_left 0 (zeroChart F) B
  have e : chartSmul 0 (zeroChart F) = zeroChart F := by
    apply chainChart_ext
    · funext p i
      simp [chartSmul, chartMove, chartZero, zeroChart]
    · funext j p i
      simp [chartSmul, chartMove, chartZero, zeroChart]
  rw [e] at h
  simpa using h
theorem linear_eq_of_chartAgreeOn (R : F.FieldChain) (f : ChainChart F → ℝ)
    (hadd : ∀ A A', f (chartMove A A' 1) = f A + f A') (w : F.SiteWeights) (K : ℝ)
    (hb : ∀ A, |f A| ≤ K * _root_.YangMills.Construction.BlockAverages.weightedNorm S R A w) {A A' : ChainChart F} (h : ChartEqOnBonds S A A') : f A = f A' := by
  have e : chartMove A' (chartMove A A' (-1)) 1 = A := by
    apply chainChart_ext
    · funext p i
      simp only [chartMove, one_smul, neg_one_smul_imag]
      abel
    · funext j p i
      simp only [chartMove, one_smul, neg_one_smul_imag]
      abel
  have hz : ChartEqOnBonds S (chartMove A A' (-1)) (zeroChart F) := by
    refine ⟨fun x hx => ?_, fun j hj x hx => ?_⟩
    · simp [chartMove, zeroChart, h.1 x hx, neg_one_smul_imag]
    · simp [chartMove, zeroChart, h.2 j hj x hx, neg_one_smul_imag]
  have h0 : f (chartMove A A' (-1)) = 0 := by
    have := hb (chartMove A A' (-1))
    rw [_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_eq_zero_of_chartEq S R _ w hz, mul_zero] at this
    exact abs_eq_zero.1 (le_antisymm this (abs_nonneg _))
  have := hadd A' (chartMove A A' (-1))
  rw [e, h0, add_zero] at this
  exact this
theorem complexFirstVariation_zero (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf)
    (A : ChainChart F) :
    complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F)) (complexTwistedTop b X 0 V) A =
      (chartFirstVariation a S (referenceFieldChain S V) V (chartZero F) A : ℂ) := by
  have hc : 0 ≤ c := h.r_pos.le.trans h.r_le_c
  have hno := supWeightedNorm_zeroChart (S := S) (del := del) h.side_odd.pos (referenceFieldChain S V)
  have hsup : complexSupWeightedNorm S del (referenceFieldChain S V) (realChart (zeroChart F)) ≤ c := by
    rw [complexSupWeightedNorm_realChart h.side_odd.pos, hno]
    exact hc
  have hd := differentiableAt_complexChartMove_line h.twisted (ζ := 0) hsup (by simpa using hc) A
  rw [complexTwistedTop_zero] at hd ⊢
  have hr := complexFirstVariation_real a (referenceFieldChain S V) (zeroChart F) A V hd
    (eventually_chartIsRegular_chartMove h.side_odd.pos h.del_pos.le h.regular A
      (by rw [hno]; exact h.r_pos.trans h.r_lt_c₁))
  have hfv : chartFirstVariation a S (referenceFieldChain S V) V (chartZero F) A =
      (complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F)) (complexifyField V) A).re :=
    hr.1.deriv
  rw [hfv]
  exact Complex.ext (by simp) (by simpa using hr.2)
theorem inGaugeSlice_chartMove {U U' : ChainChart F} (t : ℝ)
    (hU : InGaugeSlice S V (referenceFieldChain S V 0) U.fine)
    (hU' : InGaugeSlice S V (referenceFieldChain S V 0) U'.fine) :
    InGaugeSlice S V (referenceFieldChain S V 0) (chartMove U U' t).fine := by
  have hv : ofChart U + t • ofChart U' ∈ gaugeSliceSubmodule S V (referenceFieldChain S V 0) :=
    Submodule.add_mem _ (mem_gaugeSliceSubmodule.2 hU) (Submodule.smul_mem _ _ (mem_gaugeSliceSubmodule.2 hU'))
  have e : chartMove U U' t = toChart (ofChart U + t • ofChart U') := chartMove_toChart (ofChart U) (ofChart U') t
  rw [e]
  exact mem_gaugeSliceSubmodule.1 hv
theorem complexReferenceSecondDeriv_realChart_sub (hT : ActionTaylorBounds a θ del Ct cT CT s S V)
    (U₁ U₂ A : ChainChart F) :
    complexReferenceSecondDeriv a S (referenceFieldChain S V) V (complexChartSub (realChart U₁) (realChart U₂)) A =
      ((referenceSecondDeriv a S (referenceFieldChain S V) V U₁ A -
        referenceSecondDeriv a S (referenceFieldChain S V) V U₂ A : ℝ) : ℂ) := by
  have h2 : referenceSecondDeriv a S (referenceFieldChain S V) V
      (chartMove (⟨fun _ _ => 0, fun _ _ _ => 0⟩ : ChainChart F) ⟨fun _ _ => 0, fun _ _ _ => 0⟩ (-1)) A = 0 := by
    rw [referenceSecondDeriv_chartMove hT]
    have := referenceSecondDeriv_zeroChart hT A
    have e : (⟨fun _ _ => 0, fun _ _ _ => 0⟩ : ChainChart F) = zeroChart F := rfl
    rw [e, this]
    simp
  unfold complexReferenceSecondDeriv complexChartSub realChart
  simp only
  rw [h2, referenceSecondDeriv_chartMove hT]
  push_cast
  ring
theorem complexWeightedNorm_realChart_sub (R : F.FieldChain) (U₁ U₂ : ChainChart F) (w : F.SiteWeights) :
    complexWeightedNorm S R (complexChartSub (realChart U₁) (realChart U₂)) w =
      _root_.YangMills.Construction.BlockAverages.weightedNorm S R (chartMove U₁ U₂ (-1)) w := by
  unfold complexWeightedNorm complexChartSub realChart
  simp only
  have h0 : _root_.YangMills.Construction.BlockAverages.weightedNorm S R (chartMove (⟨fun _ _ => 0, fun _ _ _ => 0⟩ : ChainChart F)
      ⟨fun _ _ => 0, fun _ _ _ => 0⟩ (-1)) w = 0 := by
    refine _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_eq_zero_of_chartEq S R _ w ⟨fun x _ => ?_, fun j _ x _ => ?_⟩ <;> simp [chartMove, zeroChart]
  rw [h0, add_zero]
theorem sum_abs_nonneg' (ζ : Fin k → ℝ) : 0 ≤ ∑ l, |ζ l| := Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem remainder_bound_arith {Ca₄ C C₀ CT Cl Y σ s N nL nZ r r' : ℝ} (hCa₄ : 0 < Ca₄) (hC : 0 < C) (hC₀ : 0 < C₀)
    (hCT : 0 < CT) (hCl : 0 < Cl) (hs : 0 < s) (hσ : 0 ≤ σ) (hY : 0 ≤ Y) (hYs : Y ≤ C₀ * (s + σ))
    (hYr : Y ≤ r) (hσr : σ ≤ r') (hsm : 8 * Ca₄ * C * (2 * r + r') ≤ 1) (hr : 0 ≤ r)
    (hnL0 : 0 ≤ nL) (hnZ0 : 0 ≤ nZ) (hN : N ≤ nL + nZ)
    (hnL : nL ≤ Ca₄ * Cl * (s + σ))
    (hZ : nZ ≤ Ca₄ * (C * (Y + σ) * N + C * (s + σ) ^ 2 + CT * s ^ 2)) :
    nZ ≤ (2 * Ca₄ * C * (C₀ + 1) * (Ca₄ * Cl) + 2 * Ca₄ * (C + CT)) * (s + σ) ^ 2 := by
  set t := Ca₄ * C * (Y + σ) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht2 : t ≤ 1 / 2 := by
    have h1 : Y + σ ≤ 2 * r + r' := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ Ca₄ * C)
    have h3 : 0 ≤ Ca₄ * C * (2 * r + r') := by
      have : 0 ≤ 2 * r + r' := by linarith
      positivity
    nlinarith
  have ht3 : t ≤ Ca₄ * C * (C₀ + 1) * (s + σ) := by
    have h1 : Y + σ ≤ (C₀ + 1) * (s + σ) := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ Ca₄ * C)
    calc t = Ca₄ * C * (Y + σ) := ht
      _ ≤ Ca₄ * C * ((C₀ + 1) * (s + σ)) := this
      _ = Ca₄ * C * (C₀ + 1) * (s + σ) := by ring
  have h1 : Ca₄ * (C * (Y + σ) * N) ≤ t * (nL + nZ) := by
    have : Ca₄ * (C * (Y + σ) * N) = t * N := by rw [ht]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hN ht0
  have h2 : s ^ 2 ≤ (s + σ) ^ 2 := by nlinarith
  have h3 : Ca₄ * (C * (s + σ) ^ 2 + CT * s ^ 2) ≤ Ca₄ * (C + CT) * (s + σ) ^ 2 := by
    have : C * (s + σ) ^ 2 + CT * s ^ 2 ≤ (C + CT) * (s + σ) ^ 2 := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left this hCa₄.le
    linarith
  have h4 : nZ ≤ t * (nL + nZ) + Ca₄ * (C + CT) * (s + σ) ^ 2 := by
    have : Ca₄ * (C * (Y + σ) * N + C * (s + σ) ^ 2 + CT * s ^ 2) =
        Ca₄ * (C * (Y + σ) * N) + Ca₄ * (C * (s + σ) ^ 2 + CT * s ^ 2) := by ring
    linarith
  have h5 : t * nZ ≤ (1 / 2) * nZ := mul_le_mul_of_nonneg_right ht2 hnZ0
  have h7 : t * nL ≤ Ca₄ * C * (C₀ + 1) * (s + σ) * (Ca₄ * Cl * (s + σ)) :=
    mul_le_mul ht3 hnL hnL0 (by positivity)
  have e : (2 * Ca₄ * C * (C₀ + 1) * (Ca₄ * Cl) + 2 * Ca₄ * (C + CT)) * (s + σ) ^ 2 =
      2 * (Ca₄ * C * (C₀ + 1) * (s + σ) * (Ca₄ * Cl * (s + σ))) + 2 * (Ca₄ * (C + CT) * (s + σ) ^ 2) := by
    ring
  rw [e]
  linarith
theorem exists_linear_split (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf) {ζ : Fin k → ℝ}
    (hζ : ∑ l, |ζ l| < r') :
    ∃ Ulin Urest : ChainChart F,
      ChartEqOnBonds S (realPartChart Wf ζ) (chartSum Ulin Urest) ∧
      ∀ (p : F.Site 0) (y0 : F.Cell) (θ' : ℝ), θ' = θ ∨ θ' = 0 →
        _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) Ulin (decayWeights F del θ' p y0) ≤
          Ca₄ * (Ct + Ca) * (s + ∑ l, |ζ l|) ∧
        _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) Urest (decayWeights F del θ' p y0) ≤
          (2 * Ca₄ * C * (C₀ + 1) * (Ca₄ * (Ct + Ca)) + 2 * Ca₄ * (C + CT)) * (s + ∑ l, |ζ l|) ^ 2 := by
  have hCa₄ := h.Ca₄_pos
  have hCt := h.Ct_pos
  have hCT := h.CT_pos
  have hCa := h.Ca_pos
  have hC := h.C_pos
  have hC₀ := h.C₀_pos
  have hs := h.s_pos
  have hσ0 := sum_abs_nonneg' ζ
  obtain ⟨hUr, hUs⟩ := supWeightedNorm_realPartChart_le h hζ
  obtain ⟨ℓ₀, a0, s0, b0⟩ := h.taylor.linear_source
  obtain ⟨ℓ₁, a1, s1, b1⟩ := h.twisted.twistSource ζ (sum_abs_le_of_pair h hζ)
  have read0 : ∀ A A' : ChainChart F, ChartEqOnBonds S A A' → ℓ₀ A = ℓ₀ A' := fun A A' hh =>
    linear_eq_of_chartAgreeOn (S := S) (referenceFieldChain S V) ℓ₀ (fun A A' => a0 A A') _ (Ct * s)
      (fun A => (b0 A 0 0 0 (Or.inr rfl)).1) hh
  have read1 : ∀ A A' : ChainChart F, ChartEqOnBonds S A A' → ℓ₁ A = ℓ₁ A' := fun A A' hh =>
    linear_eq_of_chartAgreeOn (S := S) (referenceFieldChain S V) ℓ₁ a1 _ (Ca * ∑ l, |ζ l|)
      (fun A => (b1 A 0 0 0 (Or.inr rfl)).1) hh
  obtain ⟨Ulin, hsl, hform⟩ := h.family.solve (fun A => -(ℓ₀ A + ℓ₁ A))
    (fun A A' => by
      have e0 : ℓ₀ (chartMove A A' 1) = ℓ₀ A + ℓ₀ A' := a0 A A'
      simp only [e0, a1]
      ring)
    (fun t A => by
      have e0 : ℓ₀ (chartMove (zeroChart F) A t) = t * ℓ₀ A := s0 t A
      simp only [e0, s1]
      ring)
    (fun A A' hh => by simp only [read0 A A' hh, read1 A A' hh])
  have hslU : InGaugeSlice S V (referenceFieldChain S V 0) (realPartChart Wf ζ).fine :=
    (h.family.mem_slice (ofRealVec ζ) (by rwa [sum_norm_ofRealVec])).1
  have hsZ := inGaugeSlice_chartMove (-1) hslU hsl
  have hadded : chartSum Ulin (chartMove (realPartChart Wf ζ) Ulin (-1)) = realPartChart Wf ζ := by
    apply chainChart_ext
    · funext p i
      simp only [chartSum, chartMove, one_smul, neg_one_smul_imag]
      abel
    · funext j p i
      simp only [chartSum, chartMove, one_smul, neg_one_smul_imag]
      abel
  refine ⟨Ulin, chartMove (realPartChart Wf ζ) Ulin (-1), ?_, fun p y0 θ' hθ' => ?_⟩
  · rw [hadded]
    exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  have hθ3 : θ' = θ ∨ θ' = 0 ∨ θ' = -θ := hθ'.elim Or.inl fun e => Or.inr (Or.inl e)
  have hφ : ∀ y y', |(-del * (cellSupDist y y0 : ℝ)) - (-del * (cellSupDist y' y0 : ℝ))| ≤ del * cellSupDist y y' :=
    fun y y' => abs_neg_mul_cellSupDist_sub_le del h.del_pos.le y0 y y'
  have hnL : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) Ulin (decayWeights F del θ' p y0) ≤
      Ca₄ * (Ct * s + Ca * ∑ l, |ζ l|) :=
    h.estimate (fun y => -del * (cellSupDist y y0 : ℝ)) p θ' hθ3 hφ Ulin
      (fun A => referenceSecondDeriv a S (referenceFieldChain S V) V Ulin A) (Ct * s + Ca * ∑ l, |ζ l|)
      (by positivity) hsl (fun _ _ => rfl) (fun A hA => by
        rw [hform A hA, abs_neg]
        have e1 := (b0 A p y0 θ' hθ').1
        have e2 := (b1 A p y0 θ' hθ').1
        have e3 := norm_add_le (ℓ₀ A) (ℓ₁ A)
        simp only [Real.norm_eq_abs] at e3
        rw [add_mul]
        exact e3.trans (add_le_add e1 e2))
  have hnL' : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) Ulin (decayWeights F del θ' p y0) ≤
      Ca₄ * (Ct + Ca) * (s + ∑ l, |ζ l|) := by
    refine hnL.trans ?_
    have : Ct * s + Ca * ∑ l, |ζ l| ≤ (Ct + Ca) * (s + ∑ l, |ζ l|) := by nlinarith
    calc Ca₄ * (Ct * s + Ca * ∑ l, |ζ l|) ≤ Ca₄ * ((Ct + Ca) * (s + ∑ l, |ζ l|)) :=
          mul_le_mul_of_nonneg_left this hCa₄.le
      _ = Ca₄ * (Ct + Ca) * (s + ∑ l, |ζ l|) := by ring
  refine ⟨hnL', ?_⟩
  set N := _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (realPartChart Wf ζ) (decayWeights F del θ' p y0) with hNd
  set Y := supWeightedNorm S del (referenceFieldChain S V) (realPartChart Wf ζ) with hYd
  have hY0 : 0 ≤ Y := supWeightedNorm_nonneg _ _ _ _
  have hN0 : 0 ≤ N := _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _
  have key : ∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
      |referenceSecondDeriv a S (referenceFieldChain S V) V (chartMove (realPartChart Wf ζ) Ulin (-1)) A| ≤
        (C * (Y + ∑ l, |ζ l|) * N + C * (s + ∑ l, |ζ l|) ^ 2 + CT * s ^ 2) *
          _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F del θ' p y0)) := by
    intro A hA
    have hζc : ∑ l, ‖ofRealVec ζ l‖ ≤ c := by
      rw [sum_norm_ofRealVec]
      exact sum_abs_le_of_pair h hζ
    have hW₁ : complexSupWeightedNorm S del (referenceFieldChain S V) (realChart (realPartChart Wf ζ)) ≤ c := by
      rw [complexSupWeightedNorm_realChart h.side_odd.pos]
      exact hUr.trans h.r_le_c
    have hno := supWeightedNorm_zeroChart (S := S) (del := del) h.side_odd.pos (referenceFieldChain S V)
    have hW₀ : complexSupWeightedNorm S del (referenceFieldChain S V) (realChart (zeroChart F)) ≤ c := by
      rw [complexSupWeightedNorm_realChart h.side_odd.pos, hno]
      exact h.r_pos.le.trans h.r_le_c
    have lip := h.twisted.lipschitz (realChart (realPartChart Wf ζ)) (realChart (zeroChart F)) (ofRealVec ζ)
      hW₁ hW₀ hζc (fun y => -del * (cellSupDist y y0 : ℝ)) θ' p hθ3 hφ A
    have hsame : ChartEqOnBonds S (chartMove (realPartChart Wf ζ) (zeroChart F) (-1)) (realPartChart Wf ζ) :=
      ⟨fun x _ => by simp [chartMove, zeroChart], fun j _ x _ => by simp [chartMove, zeroChart]⟩
    rw [complexSupWeightedNorm_realChart h.side_odd.pos, complexSupWeightedNorm_realChart h.side_odd.pos, hno,
      sum_norm_ofRealVec, complexReferenceSecondDeriv_realChart_sub h.taylor,
      referenceSecondDeriv_zeroChart h.taylor, complexWeightedNorm_realChart_sub,
      _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_congr S _ _ _ _ hsame, add_zero, sub_zero] at lip
    have hG1 : complexFirstVariation a S (referenceFieldChain S V) (realChart (realPartChart Wf ζ))
        (complexTwistedTop b X (ofRealVec ζ) V) A = 0 :=
      (complexFirstVariation_realPartChart h hζ A).trans
        (h.family.critical _ (by rwa [sum_norm_ofRealVec]) A hA)
    have t0 := complexFirstVariation_zero h A
    have ts : ‖complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F))
          (complexTwistedTop b X (ofRealVec ζ) V) A -
        complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F))
          (complexTwistedTop b X 0 V) A - (ℓ₁ A : ℂ)‖ ≤
        C * (s + ∑ l, |ζ l|) ^ 2 * _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A
          (invertedWeights (decayWeights F del θ' p y0)) := (b1 A p y0 θ' hθ').2
    have f0 := (b0 A p y0 θ' hθ').2
    rw [referenceSecondDeriv_chartMove h.taylor, hform A hA]
    set G₀ := complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F))
      (complexTwistedTop b X (ofRealVec ζ) V) A
    set fU := referenceSecondDeriv a S (referenceFieldChain S V) V (realPartChart Wf ζ) A
    set fv := chartFirstVariation a S (referenceFieldChain S V) V (chartZero F) A
    rw [hG1] at lip
    rw [t0] at ts
    have e : (((fU + -1 * -(ℓ₀ A + ℓ₁ A) : ℝ)) : ℂ) =
        -(0 - G₀ - (fU : ℂ)) - (G₀ - (fv : ℂ) - (ℓ₁ A : ℂ)) - (((fv - ℓ₀ A : ℝ)) : ℂ) := by
      push_cast
      ring
    have e2 : |fU + -1 * -(ℓ₀ A + ℓ₁ A)| = ‖(((fU + -1 * -(ℓ₀ A + ℓ₁ A) : ℝ)) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [e2, e]
    have n1 := norm_sub_le (-(0 - G₀ - (fU : ℂ)) - (G₀ - (fv : ℂ) - (ℓ₁ A : ℂ))) (((fv - ℓ₀ A : ℝ)) : ℂ)
    have n2 := norm_sub_le (-(0 - G₀ - (fU : ℂ))) (G₀ - (fv : ℂ) - (ℓ₁ A : ℂ))
    rw [norm_neg] at n2
    have n3 : ‖(((fv - ℓ₀ A : ℝ)) : ℂ)‖ = |fv - ℓ₀ A| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [n3] at n1
    have e3 : (C * (Y + ∑ l, |ζ l|) * N + C * (s + ∑ l, |ζ l|) ^ 2 + CT * s ^ 2) *
          _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F del θ' p y0)) =
        C * (Y + ∑ l, |ζ l|) * N *
            weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F del θ' p y0)) +
          C * (s + ∑ l, |ζ l|) ^ 2 *
            weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F del θ' p y0)) +
          CT * s ^ 2 *
            _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F del θ' p y0)) := by ring
    rw [e3]
    have lip' : ‖0 - G₀ - (fU : ℂ)‖ ≤ C * (Y + ∑ l, |ζ l|) * N *
        _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F del θ' p y0)) := lip
    linarith
  have hZ := h.estimate (fun y => -del * (cellSupDist y y0 : ℝ)) p θ' hθ3 hφ
    (chartMove (realPartChart Wf ζ) Ulin (-1))
    (fun A => referenceSecondDeriv a S (referenceFieldChain S V) V (chartMove (realPartChart Wf ζ) Ulin (-1)) A)
    (C * (Y + ∑ l, |ζ l|) * N + C * (s + ∑ l, |ζ l|) ^ 2 + CT * s ^ 2) (by positivity) hsZ (fun _ _ => rfl) key
  have hNle : N ≤ _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) Ulin (decayWeights F del θ' p y0) +
      _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove (realPartChart Wf ζ) Ulin (-1))
        (decayWeights F del θ' p y0) := by
    have h1 := _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_chartMove_le S (referenceFieldChain S V) Ulin
      (chartMove (realPartChart Wf ζ) Ulin (-1)) 1
      (decayWeights F del θ' p y0) (fun j x => (decayWeights_pos h.side_odd.pos del θ' p y0 j x).le)
    simp only [abs_one, one_mul] at h1
    have e : chartMove Ulin (chartMove (realPartChart Wf ζ) Ulin (-1)) 1 = realPartChart Wf ζ := hadded
    rw [e] at h1
    exact h1
  exact remainder_bound_arith hCa₄ hC hC₀ hCT (by positivity) hs hσ0 hY0 hUs hUr (hζ.le) h.smallness h.r_pos.le
    (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _) (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _) hNle hnL' hZ
theorem referenceSecondDeriv_self_eq_deriv (A : ChainChart F) :
    referenceSecondDeriv a S (referenceFieldChain S V) V A A =
      deriv (deriv fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove (chartZero F) A τ) V) 0 := by
  unfold referenceSecondDeriv
  have e : ∀ τ : ℝ, deriv (fun σ : ℝ => chartAction a S (referenceFieldChain S V)
      (chartMove (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ A τ) A σ) V) 0 =
      deriv (fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove (chartZero F) A τ) V) τ := by
    intro τ
    have e1 : (fun σ : ℝ => chartAction a S (referenceFieldChain S V)
        (chartMove (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ A τ) A σ) V) =
        fun σ : ℝ => (fun τ : ℝ => chartAction a S (referenceFieldChain S V)
          (chartMove (chartZero F) A τ) V) (τ + σ) := by
      funext σ
      have e2 : chartMove (chartMove (⟨fun _ _ => 0, fun _ _ _ => 0⟩ : ChainChart F) A τ) A σ =
          chartMove (chartZero F) A (τ + σ) := by
        apply chainChart_ext
        · funext p i
          simp [chartMove, chartZero, add_smul]
        · funext j p i
          simp [chartMove, chartZero, add_smul]
      simp only [e2]
    rw [e1]
    have h9 := deriv_comp_const_add (fun τ : ℝ => chartAction a S (referenceFieldChain S V)
      (chartMove (chartZero F) A τ) V) τ (0 : ℝ)
    rw [add_zero] at h9
    exact h9
  simp only [e]
theorem complexChartMove_realChart_chartMove (U A : ChainChart F) (τ₀ : ℝ) (τ : ℂ) :
    complexChartMove (realChart (chartMove U A τ₀)) A τ = complexChartMove (realChart U) A ((τ₀ : ℂ) + τ) := by
  unfold complexChartMove realChart
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, zero_add]
  congr 1
  apply chainChart_ext
  · funext p i
    simp [chartMove, add_smul, add_assoc]
  · funext j p i
    simp [chartMove, add_smul, add_assoc]
theorem chartMove_chartMove (U A : ChainChart F) (τ₀ τ : ℝ) :
    chartMove (chartMove U A τ₀) A τ = chartMove U A (τ₀ + τ) := by
  apply chainChart_ext
  · funext p i
    simp [chartMove, add_smul, add_assoc]
  · funext j p i
    simp [chartMove, add_smul, add_assoc]
theorem quarter_quadraticForm_le_secondDeriv (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf)
    {Ca2 : ℝ} (ha : 0 < a) (hrlt : r < c)
    (hN : ∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
      weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ≤
        Ca2 * Real.sqrt (quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F)))
    (hCa2 : 0 ≤ Ca2) (hsm : (CT * s + C * (2 * r + r')) * Ca2 ^ 2 ≤ 3 / 4) {ζ : Fin k → ℝ}
    (hζ : ∑ l, |ζ l| < r') (A : ChainChart F) (hA : InGaugeSlice S V (referenceFieldChain S V 0) A.fine) :
    (1 / 4) * quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F) ≤
      deriv (deriv fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove (realPartChart Wf ζ) A τ)
        (rotatedField (bondSpread b X ζ) V)) 0 := by
  have hL := h.side_odd
  have hC := h.C_pos
  have hdel := h.del_pos
  have hcsum := sum_abs_le_of_pair h hζ
  obtain ⟨hUr, -⟩ := supWeightedNorm_realPartChart_le h hζ
  set U := realPartChart Wf ζ with hU
  set Y := supWeightedNorm S del (referenceFieldChain S V) U with hYd
  have hY0 : 0 ≤ Y := supWeightedNorm_nonneg _ _ _ _
  set YA := supWeightedNorm S del (referenceFieldChain S V) A with hYAd
  set T := complexTwistedTop b X (fun l => ((ζ l : ℝ) : ℂ)) V with hT
  set top := rotatedField (bondSpread b X ζ) V with htop
  set hh : ℂ → ℂ := fun τ => complexTotalOverTop a S (referenceFieldChain S V) (complexChartMove (realChart U) A τ) T
    with hhd
  have hζc : ∑ l, ‖((ζ l : ℝ) : ℂ)‖ ≤ c := by
    simpa [Complex.norm_real] using hcsum
  have hW : complexSupWeightedNorm S del (referenceFieldChain S V) (realChart U) ≤ c := by
    rw [complexSupWeightedNorm_realChart hL.pos]
    exact hUr.trans h.r_le_c
  have hhA : AnalyticAt ℂ hh 0 := analyticAt_complexTotalOverTop_line h.twisted hW hζc A
  have hd1A : AnalyticAt ℂ (deriv hh) 0 := hhA.deriv
  set d2 := deriv (deriv hh) 0 with hd2d
  have hd2 : HasDerivAt (deriv hh) d2 (((0 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_zero]
    exact hd1A.differentiableAt.hasDerivAt
  have hψ : HasDerivAt (fun τ : ℝ => deriv hh (τ : ℂ)) d2 0 := hd2.comp_ofReal
  have hsmallτ : ∀ᶠ τ : ℝ in 𝓝 0, Y + |τ| * YA < c ∧ Y + |τ| * YA < c₁ := by
    have hcont : Continuous fun τ : ℝ => Y + |τ| * YA := by fun_prop
    have h1 := hcont.continuousAt (x := (0 : ℝ))
    have e0 : Y + |(0 : ℝ)| * YA = Y := by simp
    exact (h1.eventually_lt continuousAt_const (by rw [e0]; exact lt_of_le_of_lt hUr hrlt)).and
      (h1.eventually_lt continuousAt_const (by rw [e0]; exact lt_of_le_of_lt hUr h.r_lt_c₁))
  have hfirst : ∀ τ₀ : ℝ, Y + |τ₀| * YA < c → Y + |τ₀| * YA < c₁ →
      complexFirstVariation a S (referenceFieldChain S V) (realChart (chartMove U A τ₀)) T A = deriv hh (τ₀ : ℂ) ∧
      HasDerivAt (fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ) top)
        (deriv hh (τ₀ : ℂ)).re τ₀ := by
    intro τ₀ h1 h2
    have hn : supWeightedNorm S del (referenceFieldChain S V) (chartMove U A τ₀) ≤ Y + |τ₀| * YA :=
      supWeightedNorm_chartMove_le S hL.pos del hdel.le _ U A τ₀
    have e1 : complexFirstVariation a S (referenceFieldChain S V) (realChart (chartMove U A τ₀)) T A =
        deriv hh (τ₀ : ℂ) := by
      unfold complexFirstVariation
      have e : (fun τ : ℂ => complexTotalOverTop a S (referenceFieldChain S V)
          (complexChartMove (realChart (chartMove U A τ₀)) A τ) T) =
          fun τ : ℂ => hh ((τ₀ : ℂ) + τ) := by
        funext τ
        simp only [hhd, complexChartMove_realChart_chartMove]
      rw [e]
      have h9 := deriv_comp_const_add hh (τ₀ : ℂ) (0 : ℂ)
      rw [add_zero] at h9
      exact h9
    refine ⟨e1, ?_⟩
    have hr := hasDerivAt_chartAction_of_complexFirstVariation hL hdel.le h.twisted h.regular ζ hcsum
      (chartMove U A τ₀) A (hn.trans h1.le) (lt_of_le_of_lt hn h2)
    have hr1 := hr.1
    rw [show complexFirstVariation a S (referenceFieldChain S V) (realChart (chartMove U A τ₀))
      (complexTwistedTop b X (fun l => ((ζ l : ℝ) : ℂ)) V) A = deriv hh (τ₀ : ℂ) from e1] at hr1
    have e2 : (fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove (chartMove U A τ₀) A τ)
        (rotatedField (bondSpread b X ζ) V)) =
        fun τ : ℝ => (fun τ' : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ') top) (τ₀ + τ) := by
      funext τ
      simp only [chartMove_chartMove, htop]
    rw [e2] at hr1
    have h3 : HasDerivAt (fun τ : ℝ => (fun τ' : ℝ => chartAction a S (referenceFieldChain S V)
        (chartMove U A τ') top) (τ₀ + τ)) (deriv hh (τ₀ : ℂ)).re (-τ₀ + τ₀) := by
      simpa using hr1
    have h4 := h3.comp_const_add (-τ₀) τ₀
    simpa using h4
  have hderiv : deriv (fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ) top) =ᶠ[𝓝 0]
      fun τ : ℝ => (deriv hh (τ : ℂ)).re := by
    filter_upwards [hsmallτ] with τ hτ
    exact (hfirst τ hτ.1 hτ.2).2.deriv
  have hre : HasDerivAt (fun τ : ℝ => (deriv hh (τ : ℂ)).re) d2.re 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hψ
  have hfinal : deriv (deriv fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ) top) 0 =
      d2.re := by
    rw [hderiv.deriv_eq]
    exact hre.deriv
  rw [hfinal]
  set n := _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) with hn
  have hn0 : 0 ≤ n := _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _
  set Bf := referenceSecondDeriv a S (referenceFieldChain S V) V A A with hBf
  have hq : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A
      (invertedWeights (classWeight F (fun _ => 0) 0 0)) = n := by
    rw [classWeight_zero]
    have : invertedWeights (oneSiteWeights F) = oneSiteWeights F := by
      funext j x
      simp [invertedWeights, oneSiteWeights]
    rw [this]
  have hlipτ : ∀ τ : ℝ, Y + |τ| * YA < c → Y + |τ| * YA < c₁ →
      ‖deriv hh (τ : ℂ) - deriv hh ((0 : ℝ) : ℂ) - ((τ * Bf : ℝ) : ℂ)‖ ≤
        C * (Y + |τ| * YA + Y + ∑ l, |ζ l|) * (|τ| * n) * n := by
    intro τ h1 h2
    have hn' : supWeightedNorm S del (referenceFieldChain S V) (chartMove U A τ) ≤ Y + |τ| * YA :=
      supWeightedNorm_chartMove_le S hL.pos del hdel.le _ U A τ
    have lip := h.twisted.lipschitz (realChart (chartMove U A τ)) (realChart U) (fun l => ((ζ l : ℝ) : ℂ))
      (by rw [complexSupWeightedNorm_realChart hL.pos]; exact hn'.trans h1.le) hW hζc (fun _ => 0) 0 0
      (Or.inr (Or.inl rfl))
      (fun y y' => by
        simp only [sub_self, abs_zero]
        positivity) A
    have e0 := (hfirst 0 (by simpa using lt_of_le_of_lt hUr hrlt) (by simpa using lt_of_le_of_lt hUr h.r_lt_c₁)).1
    have e00 : chartMove U A 0 = U := by
      apply chainChart_ext
      · funext p i
        simp [chartMove]
      · funext j p i
        simp [chartMove]
    rw [e00] at e0
    have hsameτ : chartMove (chartMove U A τ) U (-1) = chartMove (zeroChart F) A τ := by
      apply chainChart_ext
      · funext p i
        simp only [chartMove, zeroChart, neg_one_smul_imag]
        abel
      · funext j p i
        simp only [chartMove, zeroChart, neg_one_smul_imag]
        abel
    rw [complexReferenceSecondDeriv_realChart_sub h.taylor, referenceSecondDeriv_chartMove h.taylor,
      complexWeightedNorm_realChart_sub, hsameτ, classWeight_zero,
      _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_smul S _ A τ (oneSiteWeights F) (fun _ _ => zero_le_one),
      complexSupWeightedNorm_realChart hL.pos, complexSupWeightedNorm_realChart hL.pos] at lip
    rw [(hfirst τ h1 h2).1, e0] at lip
    have hq' := hq
    rw [classWeight_zero] at hq'
    rw [hq'] at lip
    have e1 : ((referenceSecondDeriv a S (referenceFieldChain S V) V U A +
        τ * referenceSecondDeriv a S (referenceFieldChain S V) V A A -
        referenceSecondDeriv a S (referenceFieldChain S V) V U A : ℝ) : ℂ) = ((τ * Bf : ℝ) : ℂ) := by
      congr 1
      rw [hBf]
      ring
    rw [e1] at lip
    refine lip.trans ?_
    have hsum : ∑ l, ‖((ζ l : ℝ) : ℂ)‖ = ∑ l, |ζ l| := by simp [Complex.norm_real]
    rw [hsum]
    have hbd : supWeightedNorm S del (referenceFieldChain S V) (chartMove U A τ) + Y + ∑ l, |ζ l| ≤
        Y + |τ| * YA + Y + ∑ l, |ζ l| := by linarith
    have : 0 ≤ |τ| * n := by positivity
    gcongr
  have hslope : ‖d2 - ((Bf : ℝ) : ℂ)‖ ≤ C * (2 * Y + ∑ l, |ζ l|) * n * n := by
    have ht := (hasDerivAt_iff_tendsto_slope_zero.1 hψ)
    have h1 : Tendsto (fun t : ℝ => ‖t⁻¹ • (deriv hh (((0 + t : ℝ)) : ℂ) - deriv hh ((0 : ℝ) : ℂ)) -
        ((Bf : ℝ) : ℂ)‖) (𝓝[≠] 0) (𝓝 ‖d2 - ((Bf : ℝ) : ℂ)‖) :=
      (ht.sub_const _).norm
    have hu : Tendsto (fun t : ℝ => C * (Y + |t| * YA + Y + ∑ l, |ζ l|) * n * n) (𝓝[≠] 0)
        (𝓝 (C * (2 * Y + ∑ l, |ζ l|) * n * n)) := by
      have hc : Continuous fun t : ℝ => C * (Y + |t| * YA + Y + ∑ l, |ζ l|) * n * n := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      convert this using 2
      simp only [abs_zero, zero_mul, add_zero]
      ring
    refine le_of_tendsto_of_tendsto h1 hu ?_
    filter_upwards [nhdsWithin_le_nhds hsmallτ, self_mem_nhdsWithin] with t ht1 ht2
    have hne : t ≠ 0 := ht2
    have habs : 0 < |t| := abs_pos.2 hne
    have h2 := hlipτ t ht1.1 ht1.2
    have e : t⁻¹ • (deriv hh (((0 + t : ℝ)) : ℂ) - deriv hh ((0 : ℝ) : ℂ)) - ((Bf : ℝ) : ℂ) =
        ((t⁻¹ : ℝ) : ℂ) * (deriv hh (t : ℂ) - deriv hh ((0 : ℝ) : ℂ) - ((t * Bf : ℝ) : ℂ)) := by
      have hne' : (t : ℂ) ≠ 0 := by exact_mod_cast hne
      rw [zero_add, Complex.real_smul]
      push_cast
      field_simp
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv]
    rw [inv_mul_le_iff₀ habs]
    refine h2.trans (le_of_eq ?_)
    ring
  have hsec := h.taylor.second_deriv_le (chartZero F) A (by
    have := supWeightedNorm_zeroChart (S := S) (del := del) hL.pos (referenceFieldChain S V)
    have e : supWeightedNorm S del (referenceFieldChain S V) (chartZero F) = 0 := this
    rw [e]
    exact h.cT_pos.le)
  have hz : supWeightedNorm S del (referenceFieldChain S V) (chartZero F) = 0 :=
    supWeightedNorm_zeroChart (S := S) (del := del) hL.pos (referenceFieldChain S V)
  rw [hz, add_zero, ← referenceSecondDeriv_self_eq_deriv] at hsec
  have hN2 : 0 ≤ quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F) :=
    quadraticFormNormSq_nonneg a ha.le S _ A _
  have hn2 : n ^ 2 ≤ Ca2 ^ 2 * quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F) := by
    have h1 := hN A hA
    have h2 := pow_le_pow_left₀ hn0 h1 2
    rw [mul_pow, Real.sq_sqrt hN2] at h2
    exact h2
  have hB1 := (abs_le.1 hsec).1
  have hd1 : Bf - C * (2 * Y + ∑ l, |ζ l|) * n * n ≤ d2.re := by
    have h1 := Complex.abs_re_le_norm (d2 - ((Bf : ℝ) : ℂ))
    have h2 := h1.trans hslope
    simp only [Complex.sub_re, Complex.ofReal_re] at h2
    have := (abs_le.1 h2).1
    linarith
  have hYb : 2 * Y + ∑ l, |ζ l| ≤ 2 * r + r' := by linarith
  have hCT := h.CT_pos
  have hs := h.s_pos
  have hcomb : (CT * s + C * (2 * Y + ∑ l, |ζ l|)) * n ^ 2 ≤
      (3 / 4) * quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F) := by
    have h1 : CT * s + C * (2 * Y + ∑ l, |ζ l|) ≤ CT * s + C * (2 * r + r') := by
      have := mul_le_mul_of_nonneg_left hYb hC.le
      linarith
    have h0 : 0 ≤ CT * s + C * (2 * Y + ∑ l, |ζ l|) := by positivity
    calc (CT * s + C * (2 * Y + ∑ l, |ζ l|)) * n ^ 2
        ≤ (CT * s + C * (2 * Y + ∑ l, |ζ l|)) *
            (Ca2 ^ 2 * quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F)) :=
          mul_le_mul_of_nonneg_left hn2 h0
      _ ≤ (CT * s + C * (2 * r + r')) *
            (Ca2 ^ 2 * quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (CT * s + C * (2 * r + r')) * Ca2 ^ 2 *
            quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F) := by ring
      _ ≤ (3 / 4) * quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F) :=
          mul_le_mul_of_nonneg_right hsm hN2
  have e : CT * (s + 0) * n ^ 2 + C * (2 * Y + ∑ l, |ζ l|) * n * n =
      (CT * s + C * (2 * Y + ∑ l, |ζ l|)) * n ^ 2 := by ring
  nlinarith
def imagCoordLinear (e : Fin 3) : imaginaryQuaternions →ₗ[ℝ] ℝ where
  toFun := imagCoord e
  map_add' x y := by
    fin_cases e <;> simp [imagCoord]
  map_smul' t x := by
    fin_cases e <;> simp [imagCoord]
def fineCoordinateFunctional (S : Finset F.Cell) (x : ↥(innerBonds S 0)) (e : Fin 3) : ChartValues S →ₗ[ℝ] ℝ :=
  (imagCoordLinear e).comp ((LinearMap.proj x).comp (LinearMap.fst ℝ _ _))
def coarseCoordinate (S : Finset F.Cell) (j : Fin F.depth) (x : ↥(innerBonds S (j.val + 1))) (e : Fin 3) :
    ChartValues S →ₗ[ℝ] ℝ :=
  (imagCoordLinear e).comp ((LinearMap.proj x).comp
    ((LinearMap.proj (φ := fun j : Fin F.depth => ↥(innerBonds S (j.val + 1)) → imaginaryQuaternions) j).comp
      (LinearMap.snd ℝ _ _)))
theorem sum_lt_of_forall_lt_div (hk : 1 ≤ k) {x : Fin k → ℝ} {r' : ℝ} (h : ∀ l, x l < r' / k) :
    ∑ l, x l < r' := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have h1 := Finset.sum_lt_sum_of_nonempty hne (fun l _ => h l)
  have h2 : ∑ _l : Fin k, r' / k = r' := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  linarith
theorem chartValues_zeroChart : chartValues S (zeroChart F) = 0 := rfl
theorem rotatedChain_complex_eq_real (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf)
    (ℓ : ChartValues S →ₗ[ℝ] ℝ) {ζ : Fin k → ℝ} (hζ : ∑ l, |ζ l| < r') :
    (ℓ (chartValues S (Wf fun l => (ζ l : ℂ)).re) : ℂ) +
        Complex.I * (ℓ (chartValues S (Wf fun l => (ζ l : ℂ)).im) : ℂ) =
      (ℓ (chartValues S (realPartChart Wf ζ)) : ℂ) := by
  have e : chartValues S (Wf fun l => (ζ l : ℂ)).im = 0 :=
    (chartValues_congr (h.family.real ζ hζ)).trans chartValues_zeroChart
  rw [e, map_zero]
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  rfl
theorem isRestrictionOfHolomorphic_chart (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf)
    (hk : 1 ≤ k) (ℓ : ChartValues S →ₗ[ℝ] ℝ) (f : (Fin k → ℝ) → ℝ)
    (hf : ∀ ζ, f ζ = ℓ (chartValues S (realPartChart Wf ζ))) :
    IsRestrictionOfHolomorphic (r' / k) f := by
  refine ⟨fun ζ => (ℓ (chartValues S (Wf ζ).re) : ℂ) + Complex.I * (ℓ (chartValues S (Wf ζ).im) : ℂ), ?_, ?_⟩
  · intro ζ hζ
    exact (h.family.analytic ζ (sum_lt_of_forall_lt_div hk hζ) ℓ).differentiableAt.differentiableWithinAt
  · intro ζ hζ
    rw [hf]
    exact rotatedChain_complex_eq_real h ℓ (sum_lt_of_forall_lt_div hk hζ)
theorem analyticAt_linearFunctional (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf)
    (ℓ : ChartValues S →ₗ[ℝ] ℝ) :
    AnalyticAt ℝ (fun ζ : Fin k → ℝ => ℓ (chartValues S (realPartChart Wf ζ))) 0 := by
  set ιL : (Fin k → ℝ) →L[ℝ] (Fin k → ℂ) :=
    ContinuousLinearMap.pi fun l => Complex.ofRealCLM.comp (ContinuousLinearMap.proj l) with hιL
  have h0 : ∑ l, ‖(0 : Fin k → ℂ) l‖ < r' := by simpa using h.r'_pos
  have hg := h.family.analytic 0 h0 ℓ
  have hg' : AnalyticAt ℂ (fun ζ' => (ℓ (chartValues S (Wf ζ').re) : ℂ) +
      Complex.I * (ℓ (chartValues S (Wf ζ').im) : ℂ)) (ιL 0) := by
    rw [map_zero]
    exact hg
  have h1 : AnalyticAt ℝ (fun x => ((ℓ (chartValues S (Wf (ιL x)).re) : ℂ) +
      Complex.I * (ℓ (chartValues S (Wf (ιL x)).im) : ℂ)).re) 0 :=
    (Complex.reCLM.analyticAt _).comp ((hg'.restrictScalars).comp (ιL.analyticAt 0))
  refine h1.congr ?_
  have hcont : Continuous fun x : Fin k → ℝ => ∑ l, |x l| := by fun_prop
  have hev : ∀ᶠ x : Fin k → ℝ in 𝓝 0, ∑ l, |x l| < r' :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simpa using h.r'_pos)
  filter_upwards [hev] with x hx
  have e := rotatedChain_complex_eq_real h ℓ hx
  have e2 : ιL x = fun l => ((x l : ℝ) : ℂ) := rfl
  simp only [e2]
  rw [e]
  simp
theorem analyticAt_of_imagCoord {f : (Fin k → ℝ) → imaginaryQuaternions}
    (hf : ∀ e, AnalyticAt ℝ (fun ζ => imagCoord e (f ζ)) 0) : AnalyticAt ℝ f 0 := by apply _root_.YangMills.Construction.BlockAverages.AgreeingPairs.analyticAt_of_imagCoord <;> assumption
def realChartValues (S : Finset F.Cell) (Wf : (Fin k → ℂ) → ComplexChainChart F) (ζ : Fin k → ℝ) : ChartValues S :=
  chartValues S (realPartChart Wf ζ)
theorem analyticAt_realChartValues (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf) :
    AnalyticAt ℝ (realChartValues S Wf) 0 := by
  refine AnalyticAt.prod ?_ ?_
  · rw [analyticAt_pi_iff]
    intro x
    exact analyticAt_of_imagCoord fun e => analyticAt_linearFunctional h (fineCoordinateFunctional S x e)
  · rw [analyticAt_pi_iff]
    intro j
    rw [analyticAt_pi_iff]
    intro x
    exact analyticAt_of_imagCoord fun e => analyticAt_linearFunctional h (coarseCoordinate S j x e)
theorem chartValues_chartMixedDeriv (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf) {m : ℕ}
    (e : Fin m ↪ Fin k) :
    chartValues S (chartMixedDeriv (realPartChart Wf) e) =
      iteratedFDeriv ℝ m (realChartValues S Wf) 0 (fun l => Pi.single (e l) 1) := by
  have hc : ContDiffAt ℝ (m : WithTop ℕ∞) (realChartValues S Wf) 0 := (analyticAt_realChartValues h).contDiffAt
  refine Prod.ext ?_ ?_
  · funext x
    have hp := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(innerBonds S 0) => imaginaryQuaternions) x).comp
      (ContinuousLinearMap.fst ℝ (↥(innerBonds S 0) → imaginaryQuaternions)
        ((j : Fin F.depth) → ↥(innerBonds S (j.val + 1)) → imaginaryQuaternions))).iteratedFDeriv_comp_left hc
          (i := m) le_rfl
    have := congrArg (fun M => M (fun l => (Pi.single (e l) 1 : Fin k → ℝ))) hp
    exact this
  · funext j x
    have hp := ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : ↥(innerBonds S (j.val + 1)) => imaginaryQuaternions) x).comp
      ((ContinuousLinearMap.proj (R := ℝ)
        (φ := fun j : Fin F.depth => ↥(innerBonds S (j.val + 1)) → imaginaryQuaternions) j).comp
      (ContinuousLinearMap.snd ℝ (↥(innerBonds S 0) → imaginaryQuaternions)
        ((j : Fin F.depth) → ↥(innerBonds S (j.val + 1)) → imaginaryQuaternions)))).iteratedFDeriv_comp_left hc
          (i := m) le_rfl
    have := congrArg (fun M => M (fun l => (Pi.single (e l) 1 : Fin k → ℝ))) hp
    exact this
theorem chartMixedDeriv_of_pairData (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf) {m : ℕ}
    (e : Fin m ↪ Fin k) (ℓ : ChartValues S →ₗ[ℝ] ℝ) :
    ℓ (chartValues S (chartMixedDeriv (realPartChart Wf) e)) =
      iteratedFDeriv ℝ m (fun ζ => ℓ (chartValues S (realPartChart Wf ζ))) 0 (fun l => Pi.single (e l) 1) := by
  have hc : ContDiffAt ℝ (m : WithTop ℕ∞) (realChartValues S Wf) 0 := (analyticAt_realChartValues h).contDiffAt
  have hp := (LinearMap.toContinuousLinearMap ℓ).iteratedFDeriv_comp_left hc (i := m) le_rfl
  have := congrArg (fun M => M (fun l => (Pi.single (e l) 1 : Fin k → ℝ))) hp
  rw [chartValues_chartMixedDeriv h e]
  exact this.symm
theorem linearFunctional_chartMove (ℓ : ChartValues S →ₗ[ℝ] ℝ) (U U' : ChainChart F) (t : ℝ) :
    ℓ (chartValues S (chartMove U U' t)) = ℓ (chartValues S U) + t * ℓ (chartValues S U') := by apply _root_.YangMills.Construction.BlockAverages.AgreeingPairs.linear_chartValues_chartMove <;> assumption
theorem localNorm_le_exp_mul_inverted (hdel : 0 < del) (R : F.FieldChain) (A : ChainChart F) (y₀ : F.Cell) :
    localNorm S R A (constOneWeights F) y₀ ≤ Real.exp (3 * del) *
      _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (invertedWeights (classWeight F (fun y => del * (cellSupDist y y₀ : ℝ)) 0 0)) := by
  refine (localNorm_le_of_weights_le S R A
    (invertedWeights (classWeight F (fun y => del * (cellSupDist y y₀ : ℝ)) 0 0))
    (constOneWeights F) y₀ (Real.exp (3 * del)) (Real.exp_pos _).le fun j x hx => ⟨zero_le_one, ?_⟩).trans ?_
  · show (1 : ℝ) ≤ Real.exp (3 * del) * (classWeight F (fun y => del * (cellSupDist y y₀ : ℝ)) 0 0 j x)⁻¹
    have e : classWeight F (fun y => del * (cellSupDist y y₀ : ℝ)) 0 0 j x =
        Real.exp (del * (cellSupDist (enclosingCell x) y₀ : ℝ)) := by
      simp [classWeight]
    rw [e, ← Real.exp_neg, ← Real.exp_add]
    apply Real.one_le_exp
    have h1 : (cellSupDist (enclosingCell x) y₀ : ℝ) ≤ 3 := by
      rw [cellSupDist_comm]
      exact_mod_cast hx
    nlinarith
  · exact mul_le_mul_of_nonneg_left (localNorm_le_weightedNorm S R A _ y₀) (Real.exp_pos _).le
theorem localNorm_le_exp_mul_weighted (hdel : 0 < del) (R : F.FieldChain) (A : ChainChart F) (y₀ z : F.Cell) :
    localNorm S R A (constOneWeights F) z ≤ Real.exp (3 * del - del * (cellSupDist z y₀ : ℝ)) *
      _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (classWeight F (fun y => del * (cellSupDist y y₀ : ℝ)) 0 0) := by
  refine (localNorm_le_of_weights_le S R A (classWeight F (fun y => del * (cellSupDist y y₀ : ℝ)) 0 0)
    (constOneWeights F) z (Real.exp (3 * del - del * (cellSupDist z y₀ : ℝ))) (Real.exp_pos _).le
    fun j x hx => ⟨zero_le_one, ?_⟩).trans ?_
  · show (1 : ℝ) ≤ Real.exp (3 * del - del * (cellSupDist z y₀ : ℝ)) *
      classWeight F (fun y => del * (cellSupDist y y₀ : ℝ)) 0 0 j x
    have e : classWeight F (fun y => del * (cellSupDist y y₀ : ℝ)) 0 0 j x =
        Real.exp (del * (cellSupDist (enclosingCell x) y₀ : ℝ)) := by
      simp [classWeight]
    rw [e, ← Real.exp_add]
    apply Real.one_le_exp
    have h1 := abs_mul_cellSupDist_sub_le del hdel.le y₀ z (enclosingCell x)
    have h2 : (cellSupDist z (enclosingCell x) : ℝ) ≤ 3 := by exact_mod_cast hx
    have h3 := (abs_le.1 h1).2
    nlinarith
  · exact mul_le_mul_of_nonneg_left (localNorm_le_weightedNorm S R A _ z) (Real.exp_pos _).le
def mixedDecayConstant (del C C₀ r' : ℝ) (m : ℕ) : ℝ :=
  C₀ * (C * r' * Real.exp (3 * del)) * Real.exp (3 * del) * (((m : ℝ) + 1) / r') ^ m
theorem localNorm_chartMixedDeriv_le (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf)
    (hMix : CauchyMixedDerivativeDifferenceProperty) {m : ℕ} (e : Fin m ↪ Fin k) (z : F.Cell) (hm : 1 ≤ m) :
    localNorm S (referenceFieldChain S V) (chartMixedDeriv (realPartChart Wf) e) (oneSiteWeights F) z ≤
      mixedDecayConstant del C C₀ r' m * Real.exp (-del * bondListDistance z (b ∘ e)) := by
  have hdel := h.del_pos
  have hC := h.C_pos
  have hr' := h.r'_pos
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := exists_linear_chartValues_le_localNorm (S := S) (referenceFieldChain S V)
    (constOneWeights F) (fun _ _ => zero_le_one) z (chartMixedDeriv (realPartChart Wf) e)
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun l : Fin m => cellSupDist z ((b ∘ e) l).1)
  set i := e l₀ with hi
  set y₀ := (b i).1 with hy₀
  have hD : bondListDistance z (b ∘ e) = cellSupDist z y₀ := hl₀
  set φ : F.Cell → ℝ := fun y => del * (cellSupDist y y₀ : ℝ) with hφ
  set g : (Fin k → ℂ) → ℂ := fun ζ => (ℓ (chartValues S (Wf ζ).re) : ℂ) +
    Complex.I * (ℓ (chartValues S (Wf ζ).im) : ℂ) with hg
  set M := Real.exp (3 * del - del * (cellSupDist z y₀ : ℝ)) * (C₀ * (C * r' * Real.exp (3 * del))) with hM
  have hb : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r' → ‖g ζ - g (Function.update ζ i 0)‖ ≤ M := by
    intro ζ hζ
    set ζ' := Function.update ζ i 0 with hζ'
    have hζ'r : ∑ l, ‖ζ' l‖ < r' := by
      refine lt_of_le_of_lt (Finset.sum_le_sum fun l _ => ?_) hζ
      by_cases hl : l = i
      · subst hl
        simp [hζ']
      · simp [hζ', hl]
    have hi_le : ‖ζ i‖ ≤ r' := by
      refine (Finset.single_le_sum (f := fun l => ‖ζ l‖) (fun l _ => norm_nonneg _) (Finset.mem_univ i)).trans hζ.le
    have hβ0 : 0 ≤ C * r' * Real.exp (3 * del) := by positivity
    have hstable := h.family.stable φ 0 0 (Or.inr (Or.inl rfl))
      (fun y y' => abs_mul_cellSupDist_sub_le del hdel.le y₀ y y') ζ
      (Wf ζ) (Wf ζ') (C * r' * Real.exp (3 * del)) hζ hβ0 (h.family.mem_slice ζ hζ).1 (h.family.mem_slice ζ hζ).2
      (h.family.mem_slice ζ' hζ'r).1 (h.family.mem_slice ζ' hζ'r).2 (h.family.small ζ hζ) (h.family.small ζ' hζ'r) (by
        intro A hA
        have h1 := h.family.critical ζ hζ A hA
        have h2 := h.family.critical ζ' hζ'r A hA
        have h3 := h.twisted.localTwist (Wf ζ') ζ ζ' i ((h.family.small ζ' hζ'r).trans h.r_le_c)
          (hζ.le.trans (h.r'_le_r.trans h.r_le_c)) (hζ'r.le.trans (h.r'_le_r.trans h.r_le_c)) (fun l' hl' => by
            simp [hζ', hl']) A
        rw [h2, sub_zero] at h3
        rw [h1, zero_sub, norm_neg]
        have e1 : ζ i - ζ' i = ζ i := by simp [hζ']
        rw [e1] at h3
        refine h3.trans ?_
        have h4 := localNorm_le_exp_mul_inverted (S := S) hdel (referenceFieldChain S V) A y₀
        have h5 : C * ‖ζ i‖ ≤ C * r' := mul_le_mul_of_nonneg_left hi_le hC.le
        have n0 : 0 ≤ localNorm S (referenceFieldChain S V) A (constOneWeights F) y₀ := localNorm_nonneg _ _ _ _ _
        calc C * ‖ζ i‖ * localNorm S (referenceFieldChain S V) A (constOneWeights F) y₀
            ≤ C * r' * (Real.exp (3 * del) * _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A
              (invertedWeights (classWeight F φ 0 0))) :=
              mul_le_mul h5 h4 n0 (by positivity)
          _ = C * r' * Real.exp (3 * del) * _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A
              (invertedWeights (classWeight F φ 0 0)) := by ring)
    set D := complexChartSub (Wf ζ) (Wf ζ') with hDd
    have e1 : g ζ - g ζ' = ((ℓ (chartValues S D.re) : ℝ) : ℂ) + Complex.I * ((ℓ (chartValues S D.im) : ℝ) : ℂ) := by
      have r1 : ℓ (chartValues S D.re) = ℓ (chartValues S (Wf ζ).re) + (-1) * ℓ (chartValues S (Wf ζ').re) :=
        linearFunctional_chartMove ℓ _ _ _
      have r2 : ℓ (chartValues S D.im) = ℓ (chartValues S (Wf ζ).im) + (-1) * ℓ (chartValues S (Wf ζ').im) :=
        linearFunctional_chartMove ℓ _ _ _
      rw [r1, r2]
      simp only [hg]
      push_cast
      ring
    rw [e1]
    have n1 : ‖((ℓ (chartValues S D.re) : ℝ) : ℂ) + Complex.I * ((ℓ (chartValues S D.im) : ℝ) : ℂ)‖ ≤
        |ℓ (chartValues S D.re)| + |ℓ (chartValues S D.im)| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
    refine n1.trans ?_
    have w1 := (hℓ2 D.re).trans (localNorm_le_exp_mul_weighted (S := S) hdel (referenceFieldChain S V) D.re y₀ z)
    have w2 := (hℓ2 D.im).trans (localNorm_le_exp_mul_weighted (S := S) hdel (referenceFieldChain S V) D.im y₀ z)
    have hs' : complexWeightedNorm S (referenceFieldChain S V) D (classWeight F φ 0 0) ≤
        C₀ * (C * r' * Real.exp (3 * del)) :=
      hstable
    have e3 : |ℓ (chartValues S D.re)| + |ℓ (chartValues S D.im)| ≤
        Real.exp (3 * del - del * (cellSupDist z y₀ : ℝ)) *
          complexWeightedNorm S (referenceFieldChain S V) D (classWeight F φ 0 0) := by
      unfold complexWeightedNorm
      rw [mul_add]
      exact add_le_add w1 w2
    exact e3.trans (mul_le_mul_of_nonneg_left hs' (Real.exp_pos _).le)
  have hcont : Continuous fun x : Fin k → ℝ => ∑ l, |x l| := by fun_prop
  have hev : ∀ᶠ x : Fin k → ℝ in 𝓝 0, ∑ l, |x l| < r' :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simpa using h.r'_pos)
  have hmix := hMix k m (fun l => e l) l₀ g (fun ζ => ℓ (chartValues S (realPartChart Wf ζ))) r' M hr'
    (fun ζ hζ => h.family.analytic ζ hζ ℓ)
    (by
      filter_upwards [hev] with x hx
      exact rotatedChain_complex_eq_real h ℓ hx)
    hb
  rw [← chartMixedDeriv_of_pairData h e ℓ, hℓ1] at hmix
  have hnear : localNorm S (referenceFieldChain S V) (chartMixedDeriv (realPartChart Wf) e) (oneSiteWeights F) z ≤
      M * (((m : ℝ) + 1) / r') ^ m := (le_abs_self _).trans hmix
  refine hnear.trans (le_of_eq ?_)
  rw [hD, hM]
  unfold mixedDecayConstant
  have e4 : Real.exp (3 * del - del * (cellSupDist z y₀ : ℝ)) =
      Real.exp (3 * del) * Real.exp (-del * (cellSupDist z y₀ : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e4]
  ring
theorem hasTopLocalBounds_mono {C₂ CL s' : ℝ} {V' : F.GaugeField F.top} {U : ChainChart F}
    (hb : HasTopLocalBounds θ C₂ s' S V V' U) (hL : 0 < F.blockSide) (hC₂ : 0 ≤ C₂) (hC : C₂ ≤ CL) (hs' : 0 ≤ s') :
    HasTopLocalBounds θ CL s' S V V' U := by
  have hLr : (0 : ℝ) < (F.blockSide : ℝ) := by exact_mod_cast hL
  have hm : C₂ * s' ≤ CL * s' := mul_le_mul_of_nonneg_right hC hs'
  have h0 : 0 ≤ C₂ * s' := mul_nonneg hC₂ hs'
  have h4 : (C₂ * s') ^ 4 ≤ (CL * s') ^ 4 := pow_le_pow_left₀ h0 hm 4
  have h2 : (C₂ * s') ^ 2 ≤ (CL * s') ^ 2 := pow_le_pow_left₀ h0 hm 2
  constructor
  · intro j p x hj h1 h3
    have hx : 0 ≤ x := by linarith
    have q : 0 ≤ (x / (F.blockSide : ℝ) ^ (F.top - j)) ^ (4 * θ) :=
      Real.rpow_nonneg (div_nonneg hx (pow_nonneg hLr.le _)) _
    exact (hb.quartic_le j p x hj h1 h3).trans (mul_le_mul_of_nonneg_right h4 q)
  · intro p x h1 h3
    have hx : 0 ≤ x := by linarith
    have q : 0 ≤ (x / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) :=
      Real.rpow_nonneg (div_nonneg hx (pow_nonneg hLr.le _)) _
    obtain ⟨e1, e2⟩ := hb.curvature_misfit_le p x h1 h3
    exact ⟨e1.trans (mul_le_mul_of_nonneg_right h2 q), e2.trans (mul_le_mul_of_nonneg_right h2 q)⟩
  · intro j z hj
    obtain ⟨e1, e2⟩ := hb.cell_misfit_le j z hj
    have q1 : 0 ≤ (4 / (F.blockSide : ℝ) ^ 2) ^ (F.top - 1 - j) := pow_nonneg (by positivity) _
    have q2 : 0 ≤ (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) := pow_nonneg (by positivity) _
    exact ⟨e1.trans (pow_le_pow_left₀ (mul_nonneg h0 q1) (mul_le_mul_of_nonneg_right hm q1) 4),
      e2.trans (pow_le_pow_left₀ (mul_nonneg h0 q2) (mul_le_mul_of_nonneg_right hm q2) 2)⟩
theorem rotatedField_bondSpread_zero (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (V : F.GaugeField F.top) : rotatedField (bondSpread b X 0) V = V := by apply _root_.YangMills.Construction.BlockAverages.AgreeingPairs.rotatedField_zero <;> assumption
theorem norm_bondSpread_le {X : Fin k → imaginaryQuaternions} (hX : AreUnitVectors X)
    (b : Fin k → F.Site F.top × Fin 4) (ζ : Fin k → ℝ) (y : F.Site F.top) (i : Fin 4) :
    ‖bondSpread b X ζ y i‖ ≤ ∑ l, |ζ l| := by
  unfold bondSpread
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  split_ifs
  · rw [norm_smul, hX l, mul_one, Real.norm_eq_abs]
  · simp
theorem isCold_mono {j : ℕ} {X' : F.GaugeField j} {s₁ s₂ : ℝ} (h : IsCold S j s₁ X') (hs : s₁ ≤ s₂) :
    IsCold S j s₂ X' :=
  fun p hp => lt_of_lt_of_le (h p hp) hs
set_option maxHeartbeats 400000 in
theorem chartAgreeOn_of_isCriticalAlong (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf)
    {ζ : Fin k → ℝ} (hζ : ∑ l, |ζ l| < r') {U' : ChainChart F}
    (hsl : InGaugeSlice S V (referenceFieldChain S V 0) U'.fine)
    (hU' : supWeightedNorm S del (referenceFieldChain S V) U' ≤ r)
    (hcr : ∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
      IsStationaryAlong a S (referenceFieldChain S V) (rotatedField (bondSpread b X ζ) V) U' A) :
    ChartEqOnBonds S (realPartChart Wf ζ) U' := by
  have hζ' : ∑ l, ‖ofRealVec ζ l‖ < r' := by rwa [sum_norm_ofRealVec]
  have hsl0 : InGaugeSlice S V (referenceFieldChain S V 0)
      (⟨fun _ _ => 0, fun _ _ _ => 0⟩ : ChainChart F).fine :=
    fun s' _ => gaugeMap_zero S V (referenceFieldChain S V 0) s'
  have hstable := h.family.stable (fun _ => 0) 0 0 (Or.inr (Or.inl rfl)) (fun y y' => by
      simp only [sub_self, abs_zero]
      exact mul_nonneg h.del_pos.le (Nat.cast_nonneg _)) (ofRealVec ζ) (Wf (ofRealVec ζ)) (realChart U') 0 hζ' le_rfl
    (h.family.mem_slice _ hζ').1 (h.family.mem_slice _ hζ').2 hsl hsl0 (h.family.small _ hζ')
    (by rw [complexSupWeightedNorm_realChart h.side_odd.pos]; exact hU') (fun A hA => by
      have hr := hasDerivAt_chartAction_of_complexFirstVariation h.side_odd h.del_pos.le h.twisted h.regular ζ
        (sum_abs_le_of_pair h hζ) U' A (hU'.trans h.r_le_c) (lt_of_le_of_lt hU' h.r_lt_c₁)
      have hcA : HasDerivAt (fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U' A τ)
          (rotatedField (bondSpread b X ζ) V)) 0 0 := hcr A hA
      have e0 := hr.1.unique hcA
      have e1 : complexFirstVariation a S (referenceFieldChain S V) (realChart U')
          (complexTwistedTop b X (fun l => (ζ l : ℂ)) V) A = 0 :=
        Complex.ext e0 hr.2
      have e2 := h.family.critical (ofRealVec ζ) hζ' A hA
      have e3 : complexFirstVariation a S (referenceFieldChain S V) (realChart U')
          (complexTwistedTop b X (ofRealVec ζ) V) A = 0 := e1
      rw [e2, e3]
      simp)
  rw [mul_zero] at hstable
  have h1 : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove (Wf (ofRealVec ζ)).re U' (-1))
      (classWeight F (fun _ => 0) 0 0) = 0 := by
    have h2 : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove (Wf (ofRealVec ζ)).re U' (-1))
        (classWeight F (fun _ => 0) 0 0) ≤ 0 := by
      have h5 : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove (Wf (ofRealVec ζ)).re U' (-1))
          (classWeight F (fun _ => 0) 0 0) + _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V)
          (chartMove (Wf (ofRealVec ζ)).im (⟨fun _ _ => 0, fun _ _ _ => 0⟩ : ChainChart F) (-1))
          (classWeight F (fun _ => 0) 0 0) ≤ 0 := hstable
      have h6 := _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg S (referenceFieldChain S V)
          (chartMove (Wf (ofRealVec ζ)).im (⟨fun _ _ => 0, fun _ _ _ => 0⟩ : ChainChart F) (-1))
          (classWeight F (fun _ => 0) 0 0)
      linarith
    exact le_antisymm h2 (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _)
  rw [classWeight_zero] at h1
  have h3 := chartEq_zero_of_weightedNorm_eq_zero S h.side_odd _ _ _ (fun _ _ => one_pos) h1
  refine ⟨fun x hx => ?_, fun j hj x hx => ?_⟩
  · have h4 := h3.1 x hx
    simp only [chartMove, neg_one_smul_imag, zeroChart] at h4
    exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact h4)
  · have h4 := h3.2 j hj x hx
    simp only [chartMove, neg_one_smul_imag, zeroChart] at h4
    exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact h4)
theorem sum_abs_le_mul {ζ : Fin k → ℝ} {σ : ℝ} (hσ : ∀ l, |ζ l| ≤ σ) : ∑ l, |ζ l| ≤ k * σ := by
  have := Finset.sum_le_sum (s := Finset.univ) fun l _ => hσ l
  simpa using this
theorem isTwistedCriticalChain_realPartChart {Ca' CL K₂ C₂ s₂ Ca2 : ℝ}
    (h : PairData a θ del Ca₄ Ct cT CT Ca c C C₀ c₁ r r' s S V b X Wf)
    (hMix : CauchyMixedDerivativeDifferenceProperty) (ha : 0 < a) (hrlt : r < c) (hk : 1 ≤ k)
    (hX : AreUnitVectors X) (hCa' : Ca₄ * (Ct + Ca) ≤ Ca')
    (hK : 2 * Ca₄ * C * (C₀ + 1) * (Ca₄ * (Ct + Ca)) + 2 * Ca₄ * (C + CT) ≤ K₂) (hKCL : K₂ ≤ CL)
    (hC₂ : 0 ≤ C₂) (hC₂L : C₂ ≤ CL) (hs₂ : s + r' ≤ s₂) (hCold : IsCold S F.top s V)
    (hAny : ∀ (W : F.GaugeField F.top) (U : ChainChart F), supWeightedNorm S del (referenceFieldChain S V) U ≤ r →
      (∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
        IsStationaryAlong a S (referenceFieldChain S V) W U A) →
      ∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) W U A)
    (hN : ∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
      weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ≤
        Ca2 * Real.sqrt (quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F)))
    (hCa2 : 0 ≤ Ca2) (hsm : (CT * s + C * (2 * r + r')) * Ca2 ^ 2 ≤ 3 / 4)
    (hLB : ∀ (s' : ℝ) (v : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s' → s' ≤ s₂ → IsCold S F.top s' V →
      (∀ y i, ‖v y i‖ ≤ s') → ∀ U : ChainChart F, supWeightedNorm S del (referenceFieldChain S V) U ≤ r →
      (∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) (rotatedField v V) U A) →
      (∃ Ulin Urest : ChainChart F, ChartEqOnBonds S U (chartSum Ulin Urest) ∧
        ∀ (p : F.Site 0) (y0 : F.Cell) (θ' : ℝ), θ' = θ ∨ θ' = 0 →
          _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) Ulin (decayWeights F del θ' p y0) ≤ Ca' * s' ∧
          _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) Urest (decayWeights F del θ' p y0) ≤ K₂ * s' ^ 2) →
      HasTopLocalBounds θ C₂ s' S V (rotatedField v V) U)
    {U₀ : ChainChart F} (hzero : ChartEqOnBonds S (realPartChart Wf 0) U₀) :
    IsTwistedCriticalChain a θ del Ca' r r' CL s (mixedDecayConstant del C C₀ r') S V b X U₀ (realPartChart Wf) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hCa₄ := h.Ca₄_pos
  have hsum : ∀ ζ : Fin k → ℝ, (∀ l, |ζ l| < r' / k) → ∑ l, |ζ l| < r' := fun ζ hζ =>
    sum_lt_of_forall_lt_div hk hζ
  have hfull : ∀ ζ : Fin k → ℝ, ∑ l, |ζ l| < r' → ∀ A : ChainChart F,
      IsStationaryAlong a S (referenceFieldChain S V) (rotatedField (bondSpread b X ζ) V) (realPartChart Wf ζ) A :=
    fun ζ hζ => hAny _ _ (supWeightedNorm_realPartChart_le h hζ).1 fun A hA => realPartChart_isCriticalAlong h hζ A hA
  exact {
    eq_zero := hzero
    holo_fine := fun x hx e => isRestrictionOfHolomorphic_chart h hk (fineCoordinateFunctional S ⟨x, hx⟩ e) _ fun _ => rfl
    holo_coarse := fun j hj x hx e => by
      have hj' : j < F.depth := by
        have hn : F.top = F.depth + 1 := rfl
        omega
      exact isRestrictionOfHolomorphic_chart h hk (coarseCoordinate S ⟨j, hj'⟩ ⟨x, hx⟩ e) _ fun _ => rfl
    analytic_fine := fun x hx => analyticAt_of_imagCoord fun e => analyticAt_linearFunctional h (fineCoordinateFunctional S ⟨x, hx⟩ e)
    analytic_coarse := fun j hj x hx => by
      have hj' : j < F.depth := by
        have hn : F.top = F.depth + 1 := rfl
        omega
      exact analyticAt_of_imagCoord fun e => analyticAt_linearFunctional h (coarseCoordinate S ⟨j, hj'⟩ ⟨x, hx⟩ e)
    mem_gaugeSlice := fun ζ hζ =>
      (h.family.mem_slice (ofRealVec ζ) (by rw [sum_norm_ofRealVec]; exact hsum ζ hζ)).1
    norm_le := fun ζ hζ => (supWeightedNorm_realPartChart_le h (hsum ζ hζ)).1
    isCritical := fun ζ σ hσ hσr => by
      have hσ0 : 0 ≤ σ := by
        have hl : 0 ≤ |ζ ⟨0, hk⟩| := abs_nonneg _
        exact hl.trans (hσ _)
      have hkσ : k * σ < r' := by
        rw [lt_div_iff₀ hkpos] at hσr
        linarith
      have hle := sum_abs_le_mul hσ
      have hζ : ∑ l, |ζ l| < r' := lt_of_le_of_lt hle hkσ
      have hs := h.s_pos
      set s' := s + k * σ with hs'
      have hs'0 : 0 < s' := by positivity
      have hss : s + ∑ l, |ζ l| ≤ s' := by linarith
      have h0 := sum_abs_nonneg' ζ
      obtain ⟨Ulin, Urest, hsame, hsz⟩ := exists_linear_split h hζ
      have hsplit : ∃ Ulin Urest : ChainChart F,
          ChartEqOnBonds S (realPartChart Wf ζ) (chartSum Ulin Urest) ∧
          ∀ (p : F.Site 0) (y0 : F.Cell) (θ' : ℝ), θ' = θ ∨ θ' = 0 →
            _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) Ulin (decayWeights F del θ' p y0) ≤ Ca' * s' ∧
            _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) Urest (decayWeights F del θ' p y0) ≤ K₂ * s' ^ 2 := by
        refine ⟨Ulin, Urest, hsame, fun p y0 θ' hθ' => ⟨?_, ?_⟩⟩
        · refine (hsz p y0 θ' hθ').1.trans ?_
          have hc0 : 0 ≤ Ca₄ * (Ct + Ca) := by
            have := h.Ct_pos
            have := h.Ca_pos
            positivity
          exact mul_le_mul hCa' hss (by positivity) (hc0.trans hCa')
        · refine (hsz p y0 θ' hθ').2.trans ?_
          have hc0 : 0 ≤ 2 * Ca₄ * C * (C₀ + 1) * (Ca₄ * (Ct + Ca)) + 2 * Ca₄ * (C + CT) := by
            have := h.Ct_pos
            have := h.Ca_pos
            have := h.C_pos
            have := h.C₀_pos
            have := h.CT_pos
            positivity
          exact mul_le_mul hK (pow_le_pow_left₀ (by positivity) hss 2) (by positivity) (hc0.trans hK)
      have hlb := hasTopLocalBounds_mono (hLB s' (bondSpread b X ζ) hs'0 (by linarith) (isCold_mono hCold (by
          have : 0 ≤ (k : ℝ) * σ := by positivity
          linarith))
        (fun y i => (norm_bondSpread_le hX b ζ y i).trans (by linarith)) (realPartChart Wf ζ)
        (supWeightedNorm_realPartChart_le h hζ).1
        (hfull ζ hζ) hsplit) h.side_odd.pos hC₂ hC₂L hs'0.le
      obtain ⟨Ul, Ur, h1, h2⟩ := hsplit
      exact {
        critical := hfull ζ hζ
        split := ⟨Ul, Ur, h1, fun p y0 θ' hθ' => ⟨(h2 p y0 θ' hθ').1, (h2 p y0 θ' hθ').2.trans
          (mul_le_mul_of_nonneg_right hKCL (by positivity))⟩⟩
        quartic := hlb.quartic_le
        curvature_and_misfits := hlb.curvature_misfit_le
        misfits_on_cells := hlb.cell_misfit_le }
    hessian_ge := fun ζ hζ A hA => quarter_quadraticForm_le_secondDeriv h ha hrlt hN hCa2 hsm (hsum ζ hζ) A hA
    mixedDeriv_decay := fun m e z hm => localNorm_chartMixedDeriv_le h hMix e z hm }
theorem complexCriticalFamily_of_le {ρ : ℝ} (hf : IsComplexCriticalFamily a θ del C₀ r ρ s S V b X Wf)
    (hr : r' ≤ ρ) : IsComplexCriticalFamily a θ del C₀ r r' s S V b X Wf where
  mem_slice ζ hζ := hf.mem_slice ζ (hζ.trans_le hr)
  norm_le ζ hζ := hf.norm_le ζ (hζ.trans_le hr)
  small ζ hζ := hf.small ζ (hζ.trans_le hr)
  critical ζ hζ := hf.critical ζ (hζ.trans_le hr)
  analytic ζ hζ := hf.analytic ζ (hζ.trans_le hr)
  real ζ hζ := hf.real ζ (hζ.trans_le hr)
  solve := hf.solve
  stable φ θ' p h1 h2 ζ W W' β hζ := hf.stable φ θ' p h1 h2 ζ W W' β (hζ.trans_le hr)
theorem hessian_floor_arith {CT s C₀ r r' Ca2 : ℝ} (hCT : 0 < CT) (hC₀ : 0 < C₀) (hs : 0 < s) (hr : 0 < r)
    (hr' : r' ≤ r) (hs8 : s ≤ 3 / (8 * CT * (Ca2 ^ 2 + 1))) (hr8 : r ≤ 1 / (8 * C₀ * (Ca2 ^ 2 + 1))) :
    (CT * s + C₀ * (2 * r + r')) * Ca2 ^ 2 ≤ 3 / 4 := by
  set q := Ca2 ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have h0 : 0 < 8 * CT * (q + 1) := by positivity
  have h1 : s * (8 * CT * (q + 1)) ≤ 3 := (le_div_iff₀ h0).1 hs8
  have h0' : 0 < 8 * C₀ * (q + 1) := by positivity
  have h2 : r * (8 * C₀ * (q + 1)) ≤ 1 := (le_div_iff₀ h0').1 hr8
  have a1 : CT * s * q ≤ CT * s * (q + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have a2 : C₀ * r * q ≤ C₀ * r * (q + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have a3 : C₀ * (2 * r + r') * q ≤ 3 * (C₀ * r * q) := by
    have : C₀ * (2 * r + r') ≤ 3 * (C₀ * r) := by
      have := mul_le_mul_of_nonneg_left hr' hC₀.le
      linarith
    have h3 := mul_le_mul_of_nonneg_right this hq0
    calc C₀ * (2 * r + r') * q ≤ 3 * (C₀ * r) * q := h3
      _ = 3 * (C₀ * r * q) := by ring
  have e3 : (CT * s + C₀ * (2 * r + r')) * q = CT * s * q + C₀ * (2 * r + r') * q := by ring
  rw [e3]
  linarith
theorem smallness_arith {Ca₄ C₀ r r' : ℝ} (hCa₄ : 0 < Ca₄) (hC₀ : 0 < C₀) (hr : 0 < r) (hr' : r' ≤ r)
    (hr24 : r ≤ 1 / (24 * Ca₄ * C₀)) : 8 * Ca₄ * C₀ * (2 * r + r') ≤ 1 := by
  have h0 : 0 < 24 * Ca₄ * C₀ := by positivity
  have h2 : r * (24 * Ca₄ * C₀) ≤ 1 := (le_div_iff₀ h0).1 hr24
  have h3 : 8 * Ca₄ * C₀ * (2 * r + r') ≤ 8 * Ca₄ * C₀ * (3 * r) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith
end ColdTopTwistedChains
open ColdTopTwistedChains BlockAverages GaugeMap Analytic CoordinateSeminorms TwistedTops in
set_option maxHeartbeats 1000000 in
theorem ColdTopTwistedChains.coldTopTwistedChainsStatement_holds (hC0 : complexCriticalFamiliesStatement)
    (hT : actionTaylorBoundStatement) (hN : sliceNormFormBoundStatement)
    (hAny : sliceCriticalImpliesCriticalStatement) (hLB : twistedTopLocalBoundsStatement)
    (hMix : CauchyMixedDerivativeDifferenceProperty) (hR : smallChartIsRegularStatement) :
    coldTopTwistedChainsStatement := by
  intro a θ del Ca₄ ha hθ hθ8 hdel hdel8 hCa₄ hEl
  obtain ⟨Ca, hCa, L₂, hC0'⟩ := hC0 a θ del Ca₄ ha hθ hθ8 hdel hdel8 hCa₄ hEl
  obtain ⟨L₁, hE'⟩ := hEl
  obtain ⟨Ct, L₃, hCt, hT'⟩ := hT a θ del ha hθ.le hθ8 hdel hdel8
  obtain ⟨c₂, Ca2, L₄, hc₂, hCa2, hN'⟩ := hN a ha
  obtain ⟨L₅, hAny'⟩ := hAny a del ha hdel hdel8
  have hCa' : 0 < Ca₄ * (Ct + Ca) := by positivity
  obtain ⟨L₆, hLB'⟩ := hLB a θ del (Ca₄ * (Ct + Ca)) ha hθ hθ8 hdel hdel8 hCa'
  obtain ⟨L₇, hR'⟩ := hR
  refine ⟨Ca₄ * (Ct + Ca), hCa', max (max (max L₁ L₂) (max L₃ L₄)) (max (max L₅ L₆) L₇), fun L hL hLge => ?_⟩
  have hA : max (max L₁ L₂) (max L₃ L₄) ≤ L := le_trans (le_max_left _ _) hLge
  have hB : max (max L₅ L₆) L₇ ≤ L := le_trans (le_max_right _ _) hLge
  have hL1 : L₁ ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hA)
  have hL2 : L₂ ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hA)
  have hL3 : L₃ ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hA)
  have hL4 : L₄ ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hA)
  have hL5 : L₅ ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hB)
  have hL6 : L₆ ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hB)
  have hL7 : L₇ ≤ L := le_trans (le_max_right _ _) hB
  obtain ⟨cE, hcE, hEL⟩ := hE' L hL hL1
  obtain ⟨c₀, C₀, hc₀, hC₀, hFam⟩ := hC0' L hL hL2
  obtain ⟨cT, CT, hcT, hCT, hTL⟩ := hT' L hL hL3
  obtain ⟨c₄, hc₄, hAnyL⟩ := hAny' L hL hL5
  obtain ⟨c₁, hc₁, hRL⟩ := hR' L hL hL7 del hdel hdel8
  have hD : 0 < Ca2 ^ 2 + 1 := by positivity
  refine ⟨min (min (c₀ / 2) (c₁ / 2)) (min c₄ (min (1 / (24 * Ca₄ * C₀)) (1 / (8 * C₀ * (Ca2 ^ 2 + 1))))),
    lt_min (lt_min (by positivity) (by positivity)) (lt_min hc₄ (lt_min (by positivity) (by positivity))),
    fun r hr hrc => ?_⟩
  have hrc₀ : r ≤ c₀ / 2 := hrc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrc₁ : r ≤ c₁ / 2 := hrc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrc₄ : r ≤ c₄ := hrc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr24 : r ≤ 1 / (24 * Ca₄ * C₀) :=
    hrc.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr8 : r ≤ 1 / (8 * C₀ * (Ca2 ^ 2 + 1)) :=
    hrc.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨r₀, s₀, hr₀, hr₀r, hs₀, hFamL⟩ := hFam r hr (by linarith)
  set K₂ : ℝ := 2 * Ca₄ * C₀ * (C₀ + 1) * (Ca₄ * (Ct + Ca)) + 2 * Ca₄ * (C₀ + CT) with hK₂
  have hK₂0 : 0 < K₂ := by positivity
  obtain ⟨s₂, C₂, hs₂, hC₂, hLBL⟩ := hLB' L hL hL6 r K₂ hr hK₂0
  set r' : ℝ := min r₀ (s₂ / 2) with hr'd
  have hr'0 : 0 < r' := lt_min hr₀ (by positivity)
  have hr'r₀ : r' ≤ r₀ := min_le_left _ _
  have hr's : r' ≤ s₂ / 2 := min_le_right _ _
  have hr'r : r' ≤ r := hr'r₀.trans hr₀r
  refine ⟨r', min (min s₀ (s₂ / 2)) (min (min cE cT) (min (min c₂ c₄) (min c₁ (3 / (8 * CT * (Ca2 ^ 2 + 1)))))),
    K₂ + C₂, mixedDecayConstant del C₀ C₀ r', hr'0, hr'r,
    lt_min (lt_min hs₀ (by positivity)) (lt_min (lt_min hcE hcT) (lt_min (lt_min hc₂ hc₄)
      (lt_min hc₁ (by positivity)))), by positivity,
    fun m => by unfold mixedDecayConstant; positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsle hcold
  have hLF : Odd F.blockSide := hFL ▸ hL
  have hL4F : L₄ ≤ F.blockSide := hFL ▸ hL4
  have hs₀' : s ≤ s₀ := hsle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs₂' : s ≤ s₂ / 2 := hsle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hR1 := (min_le_right (min s₀ (s₂ / 2))
    (min (min cE cT) (min (min c₂ c₄) (min c₁ (3 / (8 * CT * (Ca2 ^ 2 + 1)))))))
  have hsE : s ≤ cE := hsle.trans (hR1.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hsT : s ≤ cT := hsle.trans (hR1.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hs2 : s ≤ c₂ := hsle.trans (hR1.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))))
  have hs4 : s ≤ c₄ := hsle.trans (hR1.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))))
  have hs1 : s ≤ c₁ := hsle.trans (hR1.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hs8 : s ≤ 3 / (8 * CT * (Ca2 ^ 2 + 1)) :=
    hsle.trans (hR1.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hEp := hEL F m S hFL hamb hm hreg s V hs hsE hcold
  have hTp := hTL F m S hFL hamb hm hreg s V hs hsT hcold
  have hregP : ∀ U : ChainChart F, supWeightedNorm S del (referenceFieldChain S V) U ≤ c₁ →
      ChartIsRegular S (referenceFieldChain S V) U := fun U hU =>
    (hRL F m S hFL hamb hm hreg s V hs hs1 hcold U hU).1
  have hAnyP : ∀ (W : F.GaugeField F.top) (U : ChainChart F),
      supWeightedNorm S del (referenceFieldChain S V) U ≤ r →
      (∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
        IsStationaryAlong a S (referenceFieldChain S V) W U A) →
      ∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) W U A := fun W U hU hc =>
    hAnyL F m S hFL hamb hm hreg s V W hs hs4 hcold U (hU.trans hrc₄) hc
  have hNp : ∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
      weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ≤
        Ca2 * Real.sqrt (quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F)) := by
    intro A hA
    have := hN' F m S hLF hL4F hamb hm hreg s V hs hs2 hcold (fun _ => 0) 0 0 0 (by norm_num) (by norm_num)
      (by simp) A hA
    rwa [classWeight_zero] at this
  have hsm : (CT * s + C₀ * (2 * r + r')) * Ca2 ^ 2 ≤ 3 / 4 :=
    hessian_floor_arith hCT hC₀ hs hr (by linarith) hs8 hr8
  have hsmall : 8 * Ca₄ * C₀ * (2 * r + r') ≤ 1 := smallness_arith hCa₄ hC₀ hr (by linarith) hr24
  have hctx : ∀ (k : ℕ) (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
      ∃ Wf, PairData a θ del Ca₄ Ct cT CT Ca c₀ C₀ C₀ c₁ r r' s S V b X Wf := by
    intro k b X hX
    obtain ⟨hBp, Wf, hfam⟩ := hFamL F m S hFL hamb hm hreg s V hs hs₀' hcold k b X hX
    exact ⟨Wf, {
      side_odd := hLF, del_pos := hdel, Ca₄_pos := hCa₄, Ct_pos := hCt, cT_pos := hcT, CT_pos := hCT,
      Ca_pos := hCa, C_pos := hC₀, C₀_pos := hC₀, s_pos := hs, r_pos := hr, r'_pos := hr'0, r'_le_r := hr'r,
      r_le_c := by linarith, r_lt_c₁ := by linarith, smallness := hsmall, estimate := hEp, taylor := hTp,
      twisted := hBp, regular := hregP, family := complexCriticalFamily_of_le hfam hr'r₀ }⟩
  have hrlt : r < c₀ := by linarith
  obtain ⟨W₀, h₀⟩ := hctx 0 Fin.elim0 Fin.elim0 (fun l => l.elim0)
  have hz0 : ∑ l : Fin 0, |(0 : Fin 0 → ℝ) l| < r' := by simpa using hr'0
  have hsl₀ : InGaugeSlice S V (referenceFieldChain S V 0) (realPartChart W₀ 0).fine :=
    (h₀.family.mem_slice _ (by rw [sum_norm_ofRealVec]; exact hz0)).1
  have hr₀sup := (supWeightedNorm_realPartChart_le h₀ hz0).1
  have hcrit₀ : ∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
      IsStationaryAlong a S (referenceFieldChain S V) V (realPartChart W₀ 0) A := by
    intro A hA
    have := realPartChart_isCriticalAlong h₀ hz0 A hA
    rwa [rotatedField_bondSpread_zero] at this
  have hK₂L : K₂ ≤ K₂ + C₂ := by linarith
  have hC₂L : C₂ ≤ K₂ + C₂ := by linarith
  refine ⟨realPartChart W₀ 0, ?_, fun k c X hk hX => ?_⟩
  · obtain ⟨Ulin, Urest, hsame, hsz⟩ := exists_linear_split h₀ hz0
    exact {
      mem_slice := hsl₀
      small := hr₀sup
      critical := hAnyP V _ hr₀sup hcrit₀
      unique := fun U' h1 h2 h3 =>
        chartAgreeOn_of_isCriticalAlong h₀ hz0 h1 h2 (by rw [rotatedField_bondSpread_zero]; exact h3)
      split := ⟨Ulin, Urest, hsame, fun p y0 θ' hθ' => by
        have e := hsz p y0 θ' hθ'
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at e
        refine ⟨e.1, e.2.trans (mul_le_mul_of_nonneg_right hK₂L (by positivity))⟩⟩
      floor := fun A hA => by
        have := quarter_quadraticForm_le_secondDeriv h₀ ha hrlt hNp hCa2.le hsm hz0 A hA
        rwa [rotatedField_bondSpread_zero] at this }
  · obtain ⟨Wf, hc⟩ := hctx k c X hX
    have hz : ∑ l : Fin k, |(0 : Fin k → ℝ) l| < r' := by simpa using hr'0
    have hzero := chartAgreeOn_of_isCriticalAlong hc hz hsl₀ hr₀sup
      (by rw [rotatedField_bondSpread_zero]; exact hcrit₀)
    exact ⟨realPartChart Wf, isTwistedCriticalChain_realPartChart hc hMix ha hrlt hk hX le_rfl le_rfl hK₂L hC₂.le
      hC₂L (by linarith) hcold hAnyP hNp hCa2.le hsm
      (fun s' v h1 h2 h3 h4 U h5 h6 h7 => hLBL F m S hFL hamb hm hreg s' V v h1 h2 h3 h4 U h5 h6 h7) hzero⟩
end YangMills.Construction
end
