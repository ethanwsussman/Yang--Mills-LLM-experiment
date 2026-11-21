import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAComplexChain
import YangMills.Construction.ColdChainAtEveryLevel.HolomorphicZeroOfACoerciveFamily
import YangMills.Construction.ColdChainAtEveryLevel.SeminormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
open Filter Topology
namespace YangMills.Construction.SpanVariations
open BlockAverages Analytic CoordinateSeminorms BlockAverages.ComplexChartCoordinates
variable {F : BlockFrame}
def realCombination {m : ℕ} (v : Fin m → ChartVector F) (x : Fin m → ℝ) : ChartVector F := ∑ i, x i • v i
theorem neg_one_smul_chartVector (u : ChartVector F) : (-1 : ℝ) • u = -u := by
  refine Prod.ext ?_ ?_
  · funext p i
    exact neg_one_smul ℝ (u.1 p i)
  · funext j p i
    exact neg_one_smul ℝ (u.2 j p i)
theorem realCombination_add {m : ℕ} (v : Fin m → ChartVector F) (x y : Fin m → ℝ) :
    realCombination v (x + y) = realCombination v x + realCombination v y := by
  simp [realCombination, add_smul, Finset.sum_add_distrib]
theorem realCombination_smul {m : ℕ} (v : Fin m → ChartVector F) (c : ℝ) (x : Fin m → ℝ) :
    realCombination v (c • x) = c • realCombination v x := by
  simp [realCombination, Finset.smul_sum, smul_smul]
theorem realCombination_sub {m : ℕ} (v : Fin m → ChartVector F) (x y : Fin m → ℝ) :
    realCombination v (x - y) = realCombination v x - realCombination v y := by
  have e : x - y = x + (-1 : ℝ) • y := by
    simp [sub_eq_add_neg]
  rw [e, realCombination_add, realCombination_smul, neg_one_smul_chartVector, sub_eq_add_neg]
theorem realCombination_zero {m : ℕ} (v : Fin m → ChartVector F) : realCombination v 0 = 0 := by
  simp [realCombination]
theorem chartMove_toChart (x y : ChartVector F) (c : ℝ) :
    chartMove (toChart x) (toChart y) c = toChart (x + c • y) := by
  apply chainChart_ext
  · funext p i
    simp [chartMove, toChart]
  · funext j p i
    simp [chartMove, toChart]
theorem chartShiftMulti_toChart {m : ℕ} (v : Fin m → ChartVector F) (x : Fin m → ℝ) :
    chartShiftMulti (zeroChart F) (fun i => toChart (v i)) x = toChart (realCombination v x) := by
  apply chainChart_ext
  · funext p i
    simp [chartShiftMulti, zeroChart, toChart, realCombination, Prod.fst_sum, Finset.sum_apply]
  · funext j p i
    simp [chartShiftMulti, zeroChart, toChart, realCombination, Prod.snd_sum, Finset.sum_apply]
theorem complexSpan_eq {m : ℕ} (v : Fin m → ChartVector F) (t : Fin m → ℂ) :
    complexSpan (fun i => toChart (v i)) t =
      ⟨toChart (realCombination v (realParts t)), toChart (realCombination v (imagParts t))⟩ := by
  unfold complexSpan
  rw [chartShiftMulti_toChart, chartShiftMulti_toChart]
  rfl
def ofRealVec {m : ℕ} (α : Fin m → ℝ) : Fin m → ℂ := fun i => (α i : ℂ)
theorem complexChartMove_complexSpan {m : ℕ} (v : Fin m → ChartVector F) (t : Fin m → ℂ) (α : Fin m → ℝ) (τ : ℂ) :
    complexChartMove (complexSpan (fun i => toChart (v i)) t) (toChart (realCombination v α)) τ =
      complexSpan (fun i => toChart (v i)) (t + τ • ofRealVec α) := by
  rw [complexSpan_eq, complexSpan_eq]
  unfold complexChartMove
  simp only [chartMove_toChart, ← realCombination_smul, ← realCombination_add]
  have e1 : realParts t + τ.re • α = realParts (t + τ • ofRealVec α) := by
    funext i
    simp [realParts, ofRealVec]
  have e2 : imagParts t + τ.im • α = imagParts (t + τ • ofRealVec α) := by
    funext i
    simp [imagParts, ofRealVec]
  rw [e1, e2]
theorem complexChartSub_complexSpan {m : ℕ} (v : Fin m → ChartVector F) (t t' : Fin m → ℂ) :
    complexChartSub (complexSpan (fun i => toChart (v i)) t) (complexSpan (fun i => toChart (v i)) t') =
      complexSpan (fun i => toChart (v i)) (t - t') := by
  rw [complexSpan_eq, complexSpan_eq, complexSpan_eq]
  unfold complexChartSub
  simp only [chartMove_toChart]
  have e1 : realCombination v (realParts t) + (-1 : ℝ) • realCombination v (realParts t') =
      realCombination v (realParts (t - t')) := by
    have : realParts (t - t') = realParts t - realParts t' := by
      funext i
      simp [realParts]
    rw [this, realCombination_sub, neg_one_smul_chartVector, sub_eq_add_neg]
  have e2 : realCombination v (imagParts t) + (-1 : ℝ) • realCombination v (imagParts t') =
      realCombination v (imagParts (t - t')) := by
    have : imagParts (t - t') = imagParts t - imagParts t' := by
      funext i
      simp [imagParts]
    rw [this, realCombination_sub, neg_one_smul_chartVector, sub_eq_add_neg]
  rw [e1, e2]
theorem complexSpan_zero {m : ℕ} (v : Fin m → ChartVector F) :
    complexSpan (fun i => toChart (v i)) 0 = realChart (zeroChart F) := by
  rw [complexSpan_eq]
  have e1 : realParts (0 : Fin m → ℂ) = 0 := by
    funext i
    simp [realParts]
  have e2 : imagParts (0 : Fin m → ℂ) = 0 := by
    funext i
    simp [imagParts]
  rw [e1, e2, realCombination_zero]
  rfl
theorem complexSpan_of_imagParts_eq_zero {m : ℕ} (v : Fin m → ChartVector F) (t : Fin m → ℂ)
    (h : imagParts t = 0) :
    complexSpan (fun i => toChart (v i)) t = realChart (toChart (realCombination v (realParts t))) := by
  rw [complexSpan_eq, h, realCombination_zero]
  rfl
def spanTotal (a : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) {m k : ℕ} (v : Fin m → ChartVector F)
    (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (q : (Fin m → ℂ) × (Fin k → ℂ)) : ℂ :=
  complexTotalOverTop a S (referenceFieldChain S V) (complexSpan (fun i => toChart (v i)) q.1)
    (complexTwistedTop b X q.2 V)
def spanGradient (a : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) {m k : ℕ} (v : Fin m → ChartVector F)
    (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (q : (Fin m → ℂ) × (Fin k → ℂ)) : Fin m → ℂ :=
  fun j => fderiv ℂ (spanTotal a S V v b X) q (Pi.single j 1, 0)
variable {S : Finset F.Cell} {V : F.GaugeField F.top} {m k : ℕ} {v : Fin m → ChartVector F}
  {b : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {a : ℝ}
theorem complexFirstVariation_complexSpan {t : Fin m → ℂ} {ζ : Fin k → ℂ}
    (hd : DifferentiableAt ℂ (spanTotal a S V v b X) (t, ζ)) (α : Fin m → ℝ) :
    complexFirstVariation a S (referenceFieldChain S V) (complexSpan (fun i => toChart (v i)) t)
        (complexTwistedTop b X ζ V) (toChart (realCombination v α)) =
      fderiv ℂ (spanTotal a S V v b X) (t, ζ) (ofRealVec α, 0) := by
  have hl : HasDerivAt (fun τ : ℂ => (((t + τ • ofRealVec α, ζ)) : (Fin m → ℂ) × (Fin k → ℂ)))
      (ofRealVec α, 0) 0 := by
    refine HasDerivAt.prodMk ?_ (hasDerivAt_const _ _)
    have := ((hasDerivAt_id (0 : ℂ)).smul_const (ofRealVec α)).const_add t
    simpa using this
  have e0 : (((t + (0 : ℂ) • ofRealVec α, ζ)) : (Fin m → ℂ) × (Fin k → ℂ)) = (t, ζ) := by simp
  have hf : HasFDerivAt (spanTotal a S V v b X) (fderiv ℂ (spanTotal a S V v b X) (t, ζ))
      (t + (0 : ℂ) • ofRealVec α, ζ) := by
    rw [e0]
    exact hd.hasFDerivAt
  have hc := hf.comp_hasDerivAt (0 : ℂ) hl
  unfold complexFirstVariation
  have e : (fun τ : ℂ => complexTotalOverTop a S (referenceFieldChain S V)
      (complexChartMove (complexSpan (fun i => toChart (v i)) t) (toChart (realCombination v α)) τ)
        (complexTwistedTop b X ζ V)) =
      spanTotal a S V v b X ∘ fun τ : ℂ => (((t + τ • ofRealVec α, ζ)) : (Fin m → ℂ) × (Fin k → ℂ)) := by
    funext τ
    simp only [Function.comp, spanTotal, complexChartMove_complexSpan]
  rw [e]
  exact hc.deriv
theorem directionPairing_spanGradient (q : (Fin m → ℂ) × (Fin k → ℂ)) (α : Fin m → ℝ) :
    directionPairing (spanGradient a S V v b X q) α =
      fderiv ℂ (spanTotal a S V v b X) q (ofRealVec α, 0) := by
  have e : (((ofRealVec α, 0)) : (Fin m → ℂ) × (Fin k → ℂ)) =
      ∑ j, (α j : ℂ) • (((Pi.single j 1, 0)) : (Fin m → ℂ) × (Fin k → ℂ)) := by
    refine Prod.ext ?_ ?_
    · funext i
      simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply, ofRealVec]
    · simp [Prod.snd_sum]
  rw [e, map_sum]
  simp only [directionPairing, spanGradient, map_smul, smul_eq_mul]
theorem analyticAt_spanGradient {q : (Fin m → ℂ) × (Fin k → ℂ)}
    (hf : AnalyticAt ℂ (spanTotal a S V v b X) q) :
    AnalyticAt ℂ (spanGradient a S V v b X) q := by
  refine AnalyticAt.pi fun j => ?_
  exact ((ContinuousLinearMap.apply ℂ ℂ ((Pi.single j 1, 0) : (Fin m → ℂ) × (Fin k → ℂ))).analyticAt _).comp
    hf.fderiv
theorem complexFirstVariation_complexSpan_eq_pairing {t : Fin m → ℂ} {ζ : Fin k → ℂ}
    (hd : DifferentiableAt ℂ (spanTotal a S V v b X) (t, ζ)) (α : Fin m → ℝ) :
    complexFirstVariation a S (referenceFieldChain S V) (complexSpan (fun i => toChart (v i)) t)
        (complexTwistedTop b X ζ V) (toChart (realCombination v α)) =
      directionPairing (spanGradient a S V v b X (t, ζ)) α := by
  rw [complexFirstVariation_complexSpan hd, directionPairing_spanGradient]
theorem complexTwistedTop_zero : complexTwistedTop b X 0 V = complexifyField V := by
  funext y i
  simp [complexTwistedTop, complexifyField]
theorem complexChartMove_zero (W : ComplexChainChart F) (A : ChainChart F) : complexChartMove W A 0 = W := by
  have h : ∀ U : ChainChart F, chartMove U A 0 = U := by
    intro U
    apply chainChart_ext
    · funext p i
      simp [chartMove]
    · funext j p i
      simp [chartMove]
  cases W
  simp [complexChartMove, h]
theorem complexFirstVariation_congr_direction (hodd : Odd F.blockSide) (R : F.FieldChain)
    (W : ComplexChainChart F) (T : F.ComplexField F.top)
    {A A' : ChainChart F} (h : ChartEqOnBonds S A A') :
    complexFirstVariation a S R W T A = complexFirstVariation a S R W T A' := by
  unfold complexFirstVariation
  have e : (fun τ : ℂ => complexTotalOverTop a S R (complexChartMove W A τ) T) =
      fun τ : ℂ => complexTotalOverTop a S R (complexChartMove W A' τ) T := by
    funext τ
    refine complexTotalOverTop_congr hodd a R T ?_ ?_
    · refine ⟨fun x hx => ?_, fun j hj x hx => ?_⟩
      · simp only [complexChartMove, chartMove]
        rw [h.1 x hx]
      · simp only [complexChartMove, chartMove]
        rw [h.2 j hj x hx]
    · refine ⟨fun x hx => ?_, fun j hj x hx => ?_⟩
      · simp only [complexChartMove, chartMove]
        rw [h.1 x hx]
      · simp only [complexChartMove, chartMove]
        rw [h.2 j hj x hx]
  rw [e]
theorem complexFirstVariation_congr_point (hodd : Odd F.blockSide) (R : F.FieldChain)
    (T : F.ComplexField F.top) (A : ChainChart F)
    {W W' : ComplexChainChart F} (h1 : ChartEqOnBonds S W.re W'.re) (h2 : ChartEqOnBonds S W.im W'.im) :
    complexFirstVariation a S R W T A = complexFirstVariation a S R W' T A := by
  unfold complexFirstVariation
  have e : (fun τ : ℂ => complexTotalOverTop a S R (complexChartMove W A τ) T) =
      fun τ : ℂ => complexTotalOverTop a S R (complexChartMove W' A τ) T := by
    funext τ
    refine complexTotalOverTop_congr hodd a R T ?_ ?_
    · refine ⟨fun x hx => ?_, fun j hj x hx => ?_⟩
      · simp only [complexChartMove, chartMove]
        rw [h1.1 x hx]
      · simp only [complexChartMove, chartMove]
        rw [h1.2 j hj x hx]
    · refine ⟨fun x hx => ?_, fun j hj x hx => ?_⟩
      · simp only [complexChartMove, chartMove]
        rw [h2.1 x hx]
      · simp only [complexChartMove, chartMove]
        rw [h2.2 j hj x hx]
  rw [e]
theorem differentiableAt_complexChartMove_line {θ del Ca c C s : ℝ}
    (hB : TwistedTotalBounds a θ del Ca c C s S V b X)
    {W : ComplexChainChart F} {ζ : Fin k → ℂ}
    (hW : complexSupWeightedNorm S del (referenceFieldChain S V) W ≤ c)
    (hζ : ∑ l, ‖ζ l‖ ≤ c) (A : ChainChart F) :
    DifferentiableAt ℂ
      (fun τ : ℂ => complexTotalOverTop a S (referenceFieldChain S V) (complexChartMove W A τ)
        (complexTwistedTop b X ζ V)) 0 := by
  set A' : Fin 3 → ChainChart F := ![W.re, W.im, A] with hA'
  have hsp : ∀ τ : ℂ, complexSpan A' ![1, Complex.I, τ] = complexChartMove W A τ := by
    intro τ
    unfold complexSpan complexChartMove
    congr 1
    · apply chainChart_ext
      · funext p i
        simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_three, hA']
      · funext j p i
        simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_three, hA']
    · apply chainChart_ext
      · funext p i
        simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_three, hA']
      · funext j p i
        simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_three, hA']
  have h0 := hB.analytic 3 A' ![1, Complex.I, 0] ζ (by rw [hsp, complexChartMove_zero]; exact hW) hζ
  have hline : DifferentiableAt ℂ
      (fun τ : ℂ => (((![1, Complex.I, τ], ζ)) : (Fin 3 → ℂ) × (Fin k → ℂ))) 0 := by
    refine DifferentiableAt.prodMk ?_ (differentiableAt_const _)
    rw [differentiableAt_pi]
    intro i
    fin_cases i
    · simp
    · simp
    · simp
  have hcomp := DifferentiableAt.comp (g := fun q : (Fin 3 → ℂ) × (Fin k → ℂ) =>
    complexTotalOverTop a S (referenceFieldChain S V) (complexSpan A' q.1) (complexTwistedTop b X q.2 V))
    (0 : ℂ) h0.differentiableAt hline
  have e : (fun τ : ℂ => complexTotalOverTop a S (referenceFieldChain S V) (complexChartMove W A τ)
      (complexTwistedTop b X ζ V)) =
      (fun q : (Fin 3 → ℂ) × (Fin k → ℂ) =>
        complexTotalOverTop a S (referenceFieldChain S V) (complexSpan A' q.1) (complexTwistedTop b X q.2 V)) ∘
      fun τ : ℂ => (((![1, Complex.I, τ], ζ)) : (Fin 3 → ℂ) × (Fin k → ℂ)) := by
    funext τ
    simp only [Function.comp, hsp]
  rw [e]
  exact hcomp
end YangMills.Construction.SpanVariations
end
