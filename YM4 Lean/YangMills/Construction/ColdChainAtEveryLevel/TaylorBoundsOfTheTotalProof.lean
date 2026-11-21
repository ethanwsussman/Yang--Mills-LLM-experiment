import YangMills.Construction.ColdChainAtEveryLevel.CriticalPointOnTheSliceProof
import YangMills.Construction.ColdChainAtEveryLevel.DerivativesAlongLines
import YangMills.Construction.ColdChainAtEveryLevel.DerivativesOfTheChainTotal
import YangMills.Construction.ColdChainAtEveryLevel.FirstVariationAtTheReference
import YangMills.Construction.ColdChainAtEveryLevel.FormNearItsMainPart
import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinatesAreSeminorms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace TaylorExpansion
open YangMills.Construction.LineDerivatives YangMills.Construction.BlockAverages.ChartNorms Filter Topology
variable {F : BlockFrame}
abbrev ChartVec (F : BlockFrame) : Type :=
  (F.Site 0 → Fin 4 → imaginaryQuaternions) × ((j : ℕ) → F.Site (j + 1) → Fin 4 → imaginaryQuaternions)
def ofVec (x : ChartVec F) : ChainChart F := ⟨x.1, x.2⟩
def toVec (U : ChainChart F) : ChartVec F := (U.fine, U.coarse)
theorem chartShiftMulti_eq_ofVec {k : ℕ} (U : ChainChart F) (A : Fin k → ChainChart F) (t : Fin k → ℝ) :
    chartShiftMulti U A t = ofVec (toVec U + ∑ i, t i • toVec (A i)) := by
  unfold chartShiftMulti ofVec toVec
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd]
  congr 1
  · funext x i
    simp [Finset.sum_apply]
  · funext j y i
    simp [Finset.sum_apply]
def actionOnVec (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top) (x : ChartVec F) : ℝ :=
  chartAction a S R (ofVec x) V
theorem alongDirections_actionOnVec {a : ℝ} {S : Finset F.Cell} {R : F.FieldChain} {V : F.GaugeField F.top} {k : ℕ}
    (U : ChainChart F) (A : Fin k → ChainChart F) :
    alongDirections (actionOnVec a S R V) (toVec U) (fun i => toVec (A i)) =
      fun t => chartAction a S R (chartShiftMulti U A t) V := by
  funext t
  rw [chartShiftMulti_eq_ofVec]
  rfl
theorem mixedDeriv_actionOnVec {a : ℝ} {S : Finset F.Cell} {R : F.FieldChain} {V : F.GaugeField F.top} {k : ℕ}
    (U : ChainChart F) (A : Fin k → ChainChart F) :
    mixedDeriv (actionOnVec a S R V) (toVec U) (fun i => toVec (A i)) =
      iteratedFDeriv ℝ k (fun t => chartAction a S R (chartShiftMulti U A t) V) 0 (fun i => Pi.single i 1) := by
  unfold mixedDeriv
  rw [alongDirections_actionOnVec]
theorem expPowerWeights_zero (p : F.Site 0) : classWeight F (fun _ => 0) 0 p = oneSiteWeights F := by apply _root_.YangMills.Construction.CoordinateSeminorms.classWeight_zero <;> assumption
theorem reciprocalWeights_oneSiteWeights : invertedWeights (oneSiteWeights F) = oneSiteWeights F := by
  funext j x
  simp [invertedWeights, oneSiteWeights]
theorem isExpPowerPair_zero (θ δ : ℝ) (hδ : 0 ≤ δ) : IsExpPowerPair F θ δ (fun _ => 0) 0 := by apply _root_.YangMills.Construction.BlockAverages.SliceCriticalPoint.isExpPowerPair_zero <;> assumption
theorem sum_localNorm_mul_le (S : Finset F.Cell) (R : F.FieldChain) (U A : ChainChart F) (w w' : F.SiteWeights) :
    ∑ z ∈ S, localNorm S R U w z * localNorm S R A w' z ≤ weightedNorm S R U w * weightedNorm S R A w' :=
  Real.sum_mul_le_sqrt_mul_sqrt S _ _
structure DerivBall (a θ δ c : ℝ) (C₂ C₃ : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) : Prop where
  analytic : ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c →
    AnalyticAlongDirections (actionOnVec a S (referenceFieldChain S V) V) (toVec U)
  second : ∀ (φ : F.Cell → ℝ) (θ' : ℝ) (p : F.Site 0), IsExpPowerPair F θ δ φ θ' →
    ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c → ∀ X A : ChainChart F,
      |mixedDeriv (actionOnVec a S (referenceFieldChain S V) V) (toVec U) ![toVec X, toVec A]| ≤
        C₂ * weightedNorm S (referenceFieldChain S V) X (classWeight F φ θ' p) *
          weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p))
  third : ∀ (φ : F.Cell → ℝ) (θ' : ℝ) (p : F.Site 0), IsExpPowerPair F θ δ φ θ' →
    ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c → ∀ Y X A : ChainChart F,
      |mixedDeriv (actionOnVec a S (referenceFieldChain S V) V) (toVec U) ![toVec Y, toVec X, toVec A]| ≤
        C₃ * supWeightedNorm S δ (referenceFieldChain S V) Y *
          weightedNorm S (referenceFieldChain S V) X (classWeight F φ θ' p) *
          weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p))
theorem localNorm_nonneg (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) (z : F.Cell) :
    0 ≤ localNorm S R U w z := Real.sqrt_nonneg _
theorem derivBall_of_bounds {a θ δ c : ℝ} {Ck : ℕ → ℝ} (hδ : 0 < δ) (hCk : ∀ k, 0 < Ck k)
    {S : Finset F.Cell} {V : F.GaugeField F.top}
    (h : ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c →
      (∀ (k : ℕ) (A : Fin k → ChainChart F),
        AnalyticAt ℝ (fun t : Fin k → ℝ =>
          chartAction a S (referenceFieldChain S V) (chartShiftMulti U A t) V) 0) ∧
      (∀ (k : ℕ), 2 ≤ k → ∀ (A : Fin k → ChainChart F) (φ : F.Cell → ℝ) (θ' : ℝ) (p : F.Site 0)
        (i₁ i₂ : Fin k), i₁ ≠ i₂ → (θ' = θ ∨ θ' = 0 ∨ θ' = -θ) →
        (∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y') →
        |iteratedFDeriv ℝ k (fun t : Fin k → ℝ =>
            chartAction a S (referenceFieldChain S V) (chartShiftMulti U A t) V) 0
          (fun i => Pi.single i 1)| ≤
          Ck k * ∑ z ∈ S, ∏ i, localNorm S (referenceFieldChain S V) (A i)
            (if i = i₁ then classWeight F φ θ' p
              else if i = i₂ then invertedWeights (classWeight F φ θ' p) else constOneWeights F) z)) :
    DerivBall (F := F) a θ δ c (Ck 2) (Ck 3 * Real.exp (3 * δ)) S V := by
  refine ⟨fun U hU => ?_, ?_, ?_⟩
  · intro k A
    have hA : A = fun i => toVec (ofVec (A i)) := rfl
    rw [hA, alongDirections_actionOnVec U (fun i => ofVec (A i))]
    exact (h U hU).1 k _
  · intro φ θ' p hcl U hU X A
    have e : (![toVec X, toVec A] : Fin 2 → ChartVec F) = fun i => toVec ((![X, A] : Fin 2 → ChainChart F) i) := by
      funext i
      fin_cases i <;> rfl
    rw [e, mixedDeriv_actionOnVec]
    refine ((h U hU).2 2 le_rfl ![X, A] φ θ' p 0 1 (by simp) hcl.1 hcl.2).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hCk 2).le
    simp only [Fin.prod_univ_two]
    simpa using sum_localNorm_mul_le S (referenceFieldChain S V) X A (classWeight F φ θ' p)
      (invertedWeights (classWeight F φ θ' p))
  · intro φ θ' p hcl U hU Y X A
    have e : (![toVec Y, toVec X, toVec A] : Fin 3 → ChartVec F) =
        fun i => toVec ((![Y, X, A] : Fin 3 → ChainChart F) i) := by
      funext i
      fin_cases i <;> rfl
    rw [e, mixedDeriv_actionOnVec]
    refine ((h U hU).2 3 (by norm_num) ![Y, X, A] φ θ' p 1 2 (by simp) hcl.1 hcl.2).trans ?_
    set N := supWeightedNorm S δ (referenceFieldChain S V) Y with hN
    have hN0 : 0 ≤ N := supWeightedNorm_nonneg _ _ _ _
    have hsum : ∑ z ∈ S, ∏ i, localNorm S (referenceFieldChain S V) ((![Y, X, A] : Fin 3 → ChainChart F) i)
        (if i = 1 then classWeight F φ θ' p
          else if i = 2 then invertedWeights (classWeight F φ θ' p) else constOneWeights F) z ≤
        Real.exp (3 * δ) * N * (weightedNorm S (referenceFieldChain S V) X (classWeight F φ θ' p) *
          weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p))) := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left
        (sum_localNorm_mul_le S (referenceFieldChain S V) X A (classWeight F φ θ' p)
          (invertedWeights (classWeight F φ θ' p))) (by positivity))
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun z hz => ?_
      simp only [Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
      have hb : localNorm S (referenceFieldChain S V) Y (constOneWeights F) z ≤ Real.exp (3 * δ) * N :=
        localNorm_constOne_le_supWeightedNorm S _ Y hδ hz
      have e1 : ((0 : Fin 3) = 1) = False := by simp
      have e2 : ((0 : Fin 3) = 2) = False := by simp
      have e3 : ((2 : Fin 3) = 1) = False := by simp
      simp only [e1, e2, e3, if_false, if_true]
      calc _ ≤ (Real.exp (3 * δ) * N) * (localNorm S (referenceFieldChain S V) X (classWeight F φ θ' p) z *
              localNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p)) z) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right hb (mul_nonneg (localNorm_nonneg _ _ _ _ _) (localNorm_nonneg _ _ _ _ _))
        _ = _ := rfl
    calc _ ≤ Ck 3 * (Real.exp (3 * δ) * N * (weightedNorm S (referenceFieldChain S V) X (classWeight F φ θ' p) *
          weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p)))) :=
          mul_le_mul_of_nonneg_left hsum (hCk 3).le
      _ = _ := by ring
section Bounds
variable {a θ δ c C₂ C₃ : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
theorem supWeightedNorm_zeroChart (hL : 0 < F.blockSide) (hδ : 0 ≤ δ) (R' : F.FieldChain) :
    supWeightedNorm S δ R' (zeroChart F) = 0 := by
  refine le_antisymm (supWeightedNorm_le _ _ _ _ _ fun y₀ => ?_) (supWeightedNorm_nonneg _ _ _ _)
  have hz : ∀ B, localNormSq S B R' (zeroChart F) (decayWeights F δ 0 0 y₀) = 0 := by
    intro B
    simp [localNormSq, zeroChart, linearizedCurl, adjointAction]
  simp [weightedNorm, localNorm, hz]
theorem chartFirstVariation_eq_mixedDeriv {U : ChainChart F}
    (hU : AnalyticAlongDirections (actionOnVec a S (referenceFieldChain S V) V) (toVec U)) (A : ChainChart F) :
    chartFirstVariation a S (referenceFieldChain S V) V U A =
      mixedDeriv (actionOnVec a S (referenceFieldChain S V) V) (toVec U) ![toVec A] :=
  deriv_along hU (toVec A)
theorem eventually_analytic_near (hL : 0 < F.blockSide) (hδ : 0 ≤ δ) (hc : 0 < c) {C₂' C₃' : ℝ}
    (hb : DerivBall (F := F) a θ δ (2 * c) C₂' C₃' S V) {U : ChainChart F}
    (hU : supWeightedNorm S δ (referenceFieldChain S V) U ≤ c) (X : ChainChart F) :
    ∀ᶠ τ : ℝ in 𝓝 0, AnalyticAlongDirections (actionOnVec a S (referenceFieldChain S V) V) (toVec U + τ • toVec X) := by
  set N := supWeightedNorm S δ (referenceFieldChain S V) X with hN
  have hN0 : 0 ≤ N := supWeightedNorm_nonneg _ _ _ _
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show 0 < c / (N + 1) by positivity)] with τ hτ
  refine hb.analytic (chartMove U X τ) ?_
  have h1 := supWeightedNorm_chartMove_le S hL δ hδ (referenceFieldChain S V) U X τ
  have h2 : |τ| < c / (N + 1) := by simpa [Real.dist_eq] using hτ
  have h3 : |τ| * N ≤ c := by
    have h4 : |τ| * (N + 1) ≤ c := by
      have := (lt_div_iff₀ (by positivity : 0 < N + 1)).1 h2
      exact this.le
    nlinarith [abs_nonneg τ]
  linarith
theorem referenceHessian_eq_mixedDeriv (hL : 0 < F.blockSide) (hδ : 0 ≤ δ) (hc : 0 < c) {C₂' C₃' : ℝ}
    (hb : DerivBall (F := F) a θ δ (2 * c) C₂' C₃' S V) (X A : ChainChart F) :
    referenceSecondDeriv a S (referenceFieldChain S V) V X A =
      mixedDeriv (actionOnVec a S (referenceFieldChain S V) V) 0 ![toVec X, toVec A] := by
  have h0 : supWeightedNorm S δ (referenceFieldChain S V) (zeroChart F) ≤ c := by
    rw [supWeightedNorm_zeroChart hL hδ]
    exact hc.le
  have h1 : AnalyticAlongDirections (actionOnVec a S (referenceFieldChain S V) V) 0 :=
    hb.analytic (zeroChart F) (by linarith)
  exact deriv_deriv_along_two (toVec X) (toVec A) h1 (eventually_analytic_near hL hδ hc hb h0 X)
theorem supWeightedNorm_chartMove_zero_le (hL : 0 < F.blockSide) (hδ : 0 ≤ δ) (W : ChainChart F) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    supWeightedNorm S δ (referenceFieldChain S V) (chartMove (zeroChart F) W r) ≤
      supWeightedNorm S δ (referenceFieldChain S V) W := by
  have h1 := supWeightedNorm_chartMove_le S hL δ hδ (referenceFieldChain S V) (zeroChart F) W r
  rw [supWeightedNorm_zeroChart hL hδ, zero_add, abs_of_nonneg hr.1] at h1
  have h2 : 0 ≤ supWeightedNorm S δ (referenceFieldChain S V) W := supWeightedNorm_nonneg _ _ _ _
  nlinarith [hr.2]
theorem abs_mixedDeriv_sub_reference_le (hL : 0 < F.blockSide) (hδ : 0 ≤ δ)
    (hb : DerivBall (F := F) a θ δ c C₂ C₃ S V)
    (hC₃ : 0 ≤ C₃) (φ : F.Cell → ℝ) (θ' : ℝ) (p : F.Site 0) (hcl : IsExpPowerPair F θ δ φ θ')
    {W : ChainChart F} (hW : supWeightedNorm S δ (referenceFieldChain S V) W ≤ c) (X A : ChainChart F) :
    |mixedDeriv (actionOnVec a S (referenceFieldChain S V) V) (toVec W) ![toVec X, toVec A] -
        mixedDeriv (actionOnVec a S (referenceFieldChain S V) V) 0 ![toVec X, toVec A]| ≤
      C₃ * supWeightedNorm S δ (referenceFieldChain S V) W *
        weightedNorm S (referenceFieldChain S V) X (classWeight F φ θ' p) *
        weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p)) := by
  have h := abs_mixedDeriv_sub_sub_le (J := actionOnVec a S (referenceFieldChain S V) V) (W := 0) (X := toVec W)
    (fun r hr => hb.analytic (chartMove (zeroChart F) W r) ((supWeightedNorm_chartMove_zero_le hL hδ W hr).trans hW))
    ![toVec X, toVec A] 0 (C₃ * supWeightedNorm S δ (referenceFieldChain S V) W *
        weightedNorm S (referenceFieldChain S V) X (classWeight F φ θ' p) *
        weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p)))
    (fun r hr => by
      rw [sub_zero]
      exact hb.third φ θ' p hcl (chartMove (zeroChart F) W r)
        ((supWeightedNorm_chartMove_zero_le hL hδ W hr).trans hW) W X A)
  rw [zero_add, sub_zero] at h
  exact h
theorem toVec_add_chartSub (U U' : ChainChart F) : toVec U' + toVec (chartSub U U') = toVec U := by
  have e : toVec (chartSub U U') = toVec U + (-1 : ℝ) • toVec U' := rfl
  rw [e]
  module
theorem toVec_chartSum (A A' : ChainChart F) : toVec (chartSum A A') = toVec A + toVec A' := by
  have e : toVec (chartSum A A') = toVec A + (1 : ℝ) • toVec A' := rfl
  rw [e, one_smul]
theorem toVec_chartSmul (t : ℝ) (A : ChainChart F) : toVec (chartSmul t A) = t • toVec A := by
  have e : toVec (chartSmul t A) = 0 + t • toVec A := rfl
  rw [e, zero_add]
theorem actionTaylorBounds_of_derivBall {Ca CF C₁ s : ℝ} (hL : 0 < F.blockSide) (hδ : 0 < δ) (hc : 0 < c)
    (hb : DerivBall (F := F) a θ δ (4 * c) C₂ C₃ S V) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hCF : 0 ≤ CF) (hC₁ : 0 ≤ C₁)
    (hs : 0 < s)
    (hform : ∀ A : ChainChart F, |referenceSecondDeriv a S (referenceFieldChain S V) V A A -
        quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F)| ≤
      CF * s * weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ^ 2)
    (hsrc : ∃ ℓ : ChainChart F → ℝ,
      (∀ A A', ℓ (chartSum A A') = ℓ A + ℓ A') ∧
      (∀ (t : ℝ) A, ℓ (chartMove (zeroChart F) A t) = t * ℓ A) ∧
      ∀ (A : ChainChart F) (p : F.Site 0) (y₀ : F.Cell) (θ' : ℝ), θ' = θ ∨ θ' = 0 →
        |ℓ A| ≤ Ca * s * weightedNorm S (referenceFieldChain S V) A
          (invertedWeights (decayWeights F δ θ' p y₀)) ∧
        |deriv (fun τ : ℝ => chartAction a S (referenceFieldChain S V)
            (chartMove (zeroChart F) A τ) V) 0 - ℓ A| ≤
          C₁ * s ^ 2 * weightedNorm S (referenceFieldChain S V) A
            (invertedWeights (decayWeights F δ θ' p y₀))) :
    ActionTaylorBounds a θ δ Ca c (CF + C₁ + C₂ + 2 * C₃) s S V := by
  have hδ0 : 0 ≤ δ := hδ.le
  have hb2 : DerivBall (F := F) a θ δ (2 * (2 * c)) C₂ C₃ S V := by
    have e : 2 * (2 * c) = 4 * c := by ring
    rw [e]
    exact hb
  have hgc : ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ 4 * c →
      AnalyticAlongDirections (actionOnVec a S (referenceFieldChain S V) V) (toVec U) := hb.analytic
  have hg0 : AnalyticAlongDirections (actionOnVec a S (referenceFieldChain S V) V) 0 :=
    hb.analytic (zeroChart F) (by rw [supWeightedNorm_zeroChart hL hδ0]; positivity)
  have nn : ∀ (A : ChainChart F) (w : F.SiteWeights), 0 ≤ weightedNorm S (referenceFieldChain S V) A w :=
    fun A w => weightedNorm_nonneg _ _ _ _
  have hform_eq : ∀ X A, referenceSecondDeriv a S (referenceFieldChain S V) V X A =
      mixedDeriv (actionOnVec a S (referenceFieldChain S V) V) 0 ![toVec X, toVec A] :=
    referenceHessian_eq_mixedDeriv hL hδ0 (by positivity) hb2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U A hU
    exact (hasDerivAt_along (hgc U (by linarith)) (toVec A)).differentiableAt
  · intro U A A' hU
    have hg := hgc U (by linarith)
    rw [chartFirstVariation_eq_mixedDeriv hg, chartFirstVariation_eq_mixedDeriv hg,
      chartFirstVariation_eq_mixedDeriv hg, toVec_chartSum]
    exact mixedDeriv_one_add hg _ _
  · intro t U A hU
    have hg := hgc U (by linarith)
    rw [chartFirstVariation_eq_mixedDeriv hg, chartFirstVariation_eq_mixedDeriv hg, toVec_chartSmul]
    exact mixedDeriv_one_smul hg _ _
  · intro U U' A
    rw [hform_eq, hform_eq, hform_eq, toVec_chartSum]
    exact mixedDeriv_two_add_left hg0 _ _ _
  · intro t U A
    rw [hform_eq, hform_eq, toVec_chartSmul]
    exact mixedDeriv_two_smul_left hg0 _ _ _
  · intro U A A'
    rw [hform_eq, hform_eq, hform_eq, toVec_chartSum]
    exact mixedDeriv_two_add_right hg0 _ _ _
  · intro t U A
    rw [hform_eq, hform_eq, toVec_chartSmul]
    exact mixedDeriv_two_smul_right hg0 _ _ _
  · intro φ θ' p hcl U A
    rw [hform_eq]
    refine (hb.second φ θ' p hcl (zeroChart F) (by rw [supWeightedNorm_zeroChart hL hδ0]; positivity) U A).trans ?_
    have h1 := mul_nonneg (nn U (classWeight F φ θ' p)) (nn A (invertedWeights (classWeight F φ θ' p)))
    have : C₂ ≤ CF + C₁ + C₂ + 2 * C₃ := by linarith
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right this h1
  · obtain ⟨ℓ, h1, h2, h3⟩ := hsrc
    refine ⟨ℓ, h1, h2, fun A p y₀ θ' hθ' => ⟨(h3 A p y₀ θ' hθ').1, (h3 A p y₀ θ' hθ').2.trans ?_⟩⟩
    have h4 : C₁ ≤ CF + C₁ + C₂ + 2 * C₃ := by linarith
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 (by positivity)) (nn _ _)
  · intro U U' hU hU' φ θ' p hcl A
    set X := chartSub U U' with hX
    set nU := supWeightedNorm S δ (referenceFieldChain S V) U with hnU
    set nU' := supWeightedNorm S δ (referenceFieldChain S V) U' with hnU'
    have hnU0 : 0 ≤ nU := supWeightedNorm_nonneg _ _ _ _
    have hnU'0 : 0 ≤ nU' := supWeightedNorm_nonneg _ _ _ _
    have hXn : supWeightedNorm S δ (referenceFieldChain S V) X ≤ nU + nU' := by
      have h := supWeightedNorm_chartMove_le S hL δ hδ0 (referenceFieldChain S V) U U' (-1)
      rw [abs_neg, abs_one, one_mul] at h
      exact h
    have hWr : ∀ r ∈ Set.Icc (0 : ℝ) 1,
        supWeightedNorm S δ (referenceFieldChain S V) (chartMove U' X r) ≤ nU + 2 * nU' := by
      intro r hr
      have h1 := supWeightedNorm_chartMove_le S hL δ hδ0 (referenceFieldChain S V) U' X r
      rw [abs_of_nonneg hr.1] at h1
      have h2 : r * supWeightedNorm S δ (referenceFieldChain S V) X ≤ nU + nU' := by
        nlinarith [hr.2, hr.1]
      linarith
    set nX := weightedNorm S (referenceFieldChain S V) X (classWeight F φ θ' p) with hnX
    set nA := weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p)) with hnA
    have hnX0 : 0 ≤ nX := nn _ _
    have hnA0 : 0 ≤ nA := nn _ _
    have hseg := abs_mixedDeriv_sub_sub_le (J := actionOnVec a S (referenceFieldChain S V) V) (W := toVec U')
      (X := toVec X)
      (fun r hr => hb.analytic (chartMove U' X r) (by have := hWr r hr; linarith))
      ![toVec A] (mixedDeriv (actionOnVec a S (referenceFieldChain S V) V) 0 ![toVec X, toVec A])
      (C₃ * (2 * (nU + nU')) * nX * nA)
      (fun r hr => by
        have h1 := abs_mixedDeriv_sub_reference_le hL hδ0 hb hC₃ φ θ' p hcl (W := chartMove U' X r)
          (by have := hWr r hr; linarith) X A
        refine h1.trans ?_
        have h2 := hWr r hr
        have h3 : C₃ * supWeightedNorm S δ (referenceFieldChain S V) (chartMove U' X r) ≤ C₃ * (2 * (nU + nU')) :=
          mul_le_mul_of_nonneg_left (by linarith) hC₃
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hnX0) hnA0)
    rw [toVec_add_chartSub U U'] at hseg
    rw [chartFirstVariation_eq_mixedDeriv (hgc U (by linarith)),
      chartFirstVariation_eq_mixedDeriv (hgc U' (by linarith)), hform_eq]
    refine hseg.trans ?_
    have h4 : C₃ * 2 ≤ CF + C₁ + C₂ + 2 * C₃ := by linarith
    have h5 : 0 ≤ (nU + nU') * nX * nA := by positivity
    calc C₃ * (2 * (nU + nU')) * nX * nA = (C₃ * 2) * ((nU + nU') * nX * nA) := by ring
      _ ≤ (CF + C₁ + C₂ + 2 * C₃) * ((nU + nU') * nX * nA) := mul_le_mul_of_nonneg_right h4 h5
      _ = _ := by ring
  · intro U A hU
    have e : deriv (deriv fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ) V) 0 =
        mixedDeriv (actionOnVec a S (referenceFieldChain S V) V) (toVec U) ![toVec A, toVec A] :=
      deriv_deriv_along (toVec A) (hgc U (by linarith)) (eventually_analytic_near hL hδ0 (by positivity) hb2
        (by linarith) A)
    have h1 := abs_mixedDeriv_sub_reference_le hL hδ0 hb hC₃ (fun _ => 0) 0 0 (isExpPowerPair_zero θ δ hδ0)
      (W := U) (by linarith) A A
    rw [expPowerWeights_zero, reciprocalWeights_oneSiteWeights] at h1
    have h2 := hform A
    rw [hform_eq] at h2
    rw [e]
    set n := weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) with hn
    set nU := supWeightedNorm S δ (referenceFieldChain S V) U with hnU
    have hnU0 : 0 ≤ nU := supWeightedNorm_nonneg _ _ _ _
    have h3 := abs_sub_le (mixedDeriv (actionOnVec a S (referenceFieldChain S V) V) (toVec U) ![toVec A, toVec A])
      (mixedDeriv (actionOnVec a S (referenceFieldChain S V) V) 0 ![toVec A, toVec A])
      (quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F))
    refine h3.trans ((add_le_add h1 h2).trans ?_)
    have e1 : C₃ * nU * n * n = C₃ * nU * n ^ 2 := by ring
    rw [e1]
    have hn2 : 0 ≤ n ^ 2 := by positivity
    have h6 : C₃ * nU ≤ (CF + C₁ + C₂ + 2 * C₃) * nU :=
      mul_le_mul_of_nonneg_right (by linarith) hnU0
    have h7 : CF * s ≤ (CF + C₁ + C₂ + 2 * C₃) * s :=
      mul_le_mul_of_nonneg_right (by linarith) hs.le
    calc C₃ * nU * n ^ 2 + CF * s * n ^ 2 = (C₃ * nU + CF * s) * n ^ 2 := by ring
      _ ≤ ((CF + C₁ + C₂ + 2 * C₃) * nU + (CF + C₁ + C₂ + 2 * C₃) * s) * n ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) hn2
      _ = _ := by ring
end Bounds
end TaylorExpansion
open TaylorExpansion ChartNorms in
theorem actionTaylorBound_of_statements (hD : chartActionDerivativeBoundsStatement)
    (hF : hessianNearPrincipalStatement) (hV : referenceFirstVariationStatement) :
    actionTaylorBoundStatement := by
  intro a θ δ ha hθ hθ8 hδ hδ8
  obtain ⟨L₀, hD⟩ := hD
  obtain ⟨LF, hF⟩ := hF a θ δ ha hθ hθ8 hδ hδ8
  obtain ⟨Ca, LV, hCa, hV⟩ := hV a θ δ ha hθ hθ8 hδ hδ8
  refine ⟨Ca, max L₀ (max LF LV), hCa, fun L hodd hL => ?_⟩
  have hL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hLF : LF ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLV : LV ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  obtain ⟨cD, CD, Ck, hcD, hCD, hCk, hD⟩ := hD L a θ δ hodd hL₀ ha hθ hθ8 hδ hδ8
  obtain ⟨cF, CF, hcF, hCF, hF⟩ := hF L hodd hLF
  obtain ⟨cV, CV, hcV, hCV, hV⟩ := hV L hodd hLV
  set c := min (cD / 4) (min cF cV) with hc
  have hc0 : 0 < c := lt_min (by positivity) (lt_min hcF hcV)
  have hc1 : c ≤ cD / 4 := min_le_left _ _
  have hc2 : c ≤ cF := (min_le_right _ _).trans (min_le_left _ _)
  have hc3 : c ≤ cV := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, CF + CV + Ck 2 + 2 * (Ck 3 * Real.exp (3 * δ)), hc0, ?_, ?_⟩
  · have := hCk 2
    have := hCk 3
    positivity
  intro F m S hFL hamb hm hreg s V hs hsc hcold
  have hLpos : 0 < F.blockSide := by
    rw [hFL]
    exact hodd.pos
  have hball : DerivBall (F := F) a θ δ (4 * c) (Ck 2) (Ck 3 * Real.exp (3 * δ)) S V := by
    refine derivBall_of_bounds hδ hCk fun U hU => ?_
    have h := hD F m S hFL hamb hm hreg s V hs (by linarith) hcold U (by linarith)
    exact ⟨h.1, h.2.1⟩
  refine actionTaylorBounds_of_derivBall hLpos hδ hc0 hball (hCk 2).le (by have := hCk 3; positivity) hCF.le
    hCV.le hs ?_ (hV F m S hFL hamb hm hreg s V hs (hsc.trans hc3) hcold)
  intro A
  have h1 := hF F m S hFL hamb hm hreg s V hs (hsc.trans hc2) hcold (fun _ => 0) 0 0 (Or.inr (Or.inl rfl))
    (fun y y' => by
      simp only [sub_self, abs_zero]
      positivity) A A
  rw [expPowerWeights_zero, reciprocalWeights_oneSiteWeights] at h1
  have e : principalHessian a S (referenceFieldChain S V) A A =
      quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F) := by
    unfold principalHessian quadraticFormNormSq
    simp only [oneSiteWeights, one_mul, real_inner_self_eq_norm_sq]
    rfl
  rw [e] at h1
  refine h1.trans (le_of_eq ?_)
  ring
end YangMills.Construction.BlockAverages
end
