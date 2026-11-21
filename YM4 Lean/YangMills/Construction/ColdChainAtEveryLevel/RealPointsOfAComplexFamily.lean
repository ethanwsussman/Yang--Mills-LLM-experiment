import YangMills.Construction.ColdChainAtEveryLevel.FirstVariationsOnASpan
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
open Filter Topology
namespace YangMills.Construction.ComplexFamilies
open BlockAverages CoordinateSeminorms BlockAverages.ChartCoordinates BlockAverages.ComplexChartCoordinates SpanVariations
variable {F : BlockFrame}
theorem abs_mul_cellSupDist_sub_le (δ : ℝ) (hδ : 0 ≤ δ) (y₀ y y' : F.Cell) :
    |δ * (cellSupDist y y₀ : ℝ) - δ * (cellSupDist y' y₀ : ℝ)| ≤ δ * cellSupDist y y' := by
  have t1 : (cellSupDist y y₀ : ℝ) ≤ cellSupDist y y' + cellSupDist y' y₀ := by
    exact_mod_cast cellSupDist_triangle y y' y₀
  have t2 : (cellSupDist y' y₀ : ℝ) ≤ cellSupDist y y' + cellSupDist y y₀ := by
    have := cellSupDist_triangle y' y y₀
    rw [cellSupDist_comm y' y] at this
    exact_mod_cast this
  have e : δ * (cellSupDist y y₀ : ℝ) - δ * (cellSupDist y' y₀ : ℝ) =
      δ * ((cellSupDist y y₀ : ℝ) - cellSupDist y' y₀) := by ring
  rw [e, abs_mul, abs_of_nonneg hδ]
  refine mul_le_mul_of_nonneg_left ?_ hδ
  rw [abs_le]
  constructor <;> linarith
theorem abs_neg_mul_cellSupDist_sub_le (δ : ℝ) (hδ : 0 ≤ δ) (y₀ y y' : F.Cell) :
    |(-δ * (cellSupDist y y₀ : ℝ)) - (-δ * (cellSupDist y' y₀ : ℝ))| ≤ δ * cellSupDist y y' := by
  have h := abs_mul_cellSupDist_sub_le δ hδ y₀ y y'
  have e : (-δ * (cellSupDist y y₀ : ℝ)) - (-δ * (cellSupDist y' y₀ : ℝ)) =
      -(δ * (cellSupDist y y₀ : ℝ) - δ * (cellSupDist y' y₀ : ℝ)) := by ring
  rw [e, abs_neg]
  exact h
theorem localNorm_nonneg (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights)
    (z : F.Cell) : 0 ≤ localNorm S R U w z := Real.sqrt_nonneg _
theorem localNorm_congr (S : Finset F.Cell) (R : F.FieldChain) {U U' : ChainChart F} (w : F.SiteWeights)
    (z : F.Cell) (h : ChartEqOnBonds S U U') : localNorm S R U w z = localNorm S R U' w z := by
  unfold localNorm
  rw [localNormSq_congr S _ R U U' w h]
theorem localNorm_le_of_weights_le (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w w' : F.SiteWeights) (z : F.Cell) (κ : ℝ) (hκ : 0 ≤ κ)
    (h : ∀ (j : ℕ) (x : F.Site j), cellSupDist z (enclosingCell x) ≤ 3 → 0 ≤ w' j x ∧ w' j x ≤ κ * w j x) :
    localNorm S R U w' z ≤ κ * localNorm S R U w z := by
  have term : ∀ (e j : ℕ) (x : F.Site j) (c : ℝ), 0 ≤ c → cellSupDist z (enclosingCell x) ≤ 3 →
      (w' j x * c) ^ e ≤ κ ^ e * (w j x * c) ^ e := by
    intro e j x c hc hx
    obtain ⟨h1, h2⟩ := h j x hx
    have h3 : w' j x * c ≤ κ * (w j x * c) := by
      have := mul_le_mul_of_nonneg_right h2 hc
      linarith
    calc (w' j x * c) ^ e ≤ (κ * (w j x * c)) ^ e := pow_le_pow_left₀ (mul_nonneg h1 hc) h3 e
      _ = κ ^ e * (w j x * c) ^ e := mul_pow _ _ _
  have hbox : ∀ {j : ℕ} {x : F.Site j}, enclosingCell x ∈ cellBall S z 3 →
      cellSupDist z (enclosingCell x) ≤ 3 := by
    intro j x hx
    unfold cellBall at hx
    exact (Finset.mem_filter.1 hx).2
  have h1 : ∑ b ∈ bondsOver S (cellBall S z 3) 0, (w' 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤
      κ ^ 4 * ∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b hb => term 4 0 b.1 _ (norm_nonneg _) (hbox (mem_bondsOver.1 hb).2)
  have h2 : ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, (w' 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 ≤
      κ ^ 2 * ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b hb => term 2 0 b.1 _ (norm_nonneg _) (hbox (mem_plaquettesOver.1 hb).2)
  have h3 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (w' (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤
      κ ^ 2 * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b hb => term 2 (j + 1) b.1 _ (norm_nonneg _) (hbox (mem_bondsOver.1 hb).2)
  have h4 : Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w' 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) ≤
      κ ^ 2 * Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) := by
    refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
    rw [show κ ^ 4 = (κ ^ 2) ^ 2 by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have h5 : localNormSq S (cellBall S z 3) R U w' ≤ κ ^ 2 * localNormSq S (cellBall S z 3) R U w := by
    unfold localNormSq
    rw [mul_add, mul_add]
    linarith
  unfold localNorm
  refine (Real.sqrt_le_sqrt h5).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hκ]
theorem eventually_chartIsRegular_chartMove {S : Finset F.Cell} {δ : ℝ} (hL : 0 < F.blockSide) (hδ : 0 ≤ δ)
    {R : F.FieldChain} {c₁ : ℝ}
    (hreg : ∀ U : ChainChart F, supWeightedNorm S δ R U ≤ c₁ → ChartIsRegular S R U)
    {U : ChainChart F} (A : ChainChart F) (hU : supWeightedNorm S δ R U < c₁) :
    ∀ᶠ τ : ℝ in 𝓝 0, ChartIsRegular S R (chartMove U A τ) := by
  have hcont : Continuous fun τ : ℝ => supWeightedNorm S δ R U + |τ| * supWeightedNorm S δ R A := by
    fun_prop
  have h1 : ∀ᶠ τ : ℝ in 𝓝 0, supWeightedNorm S δ R U + |τ| * supWeightedNorm S δ R A < c₁ :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hU)
  filter_upwards [h1] with τ hτ
  exact hreg _ ((supWeightedNorm_chartMove_le S hL δ hδ R U A τ).trans hτ.le)
theorem exists_linear_le_seminorm {E : Type} [AddCommGroup E] [Module ℝ E] (p : E → ℝ)
    (hadd : ∀ x y, p (x + y) ≤ p x + p y) (hsmul : ∀ (c : ℝ) x, p (c • x) = |c| * p x) (x₀ : E) :
    ∃ ℓ : E →ₗ[ℝ] ℝ, ℓ x₀ = p x₀ ∧ ∀ y, |ℓ y| ≤ p y := by
  have hneg : ∀ y, p (-y) = p y := by
    intro y
    have := hsmul (-1) y
    simpa using this
  have h0 : p 0 = 0 := by
    have := hsmul 0 0
    simpa using this
  have hnn : ∀ y, 0 ≤ p y := by
    intro y
    have := hadd y (-y)
    rw [add_neg_cancel, h0, hneg] at this
    linarith
  by_cases hx : x₀ = 0
  · subst hx
    exact ⟨0, by simp [h0], fun y => by simpa using hnn y⟩
  · obtain ⟨g, hg1, hg2⟩ := exists_extension_of_le_sublinear
      (LinearPMap.mkSpanSingleton (K := ℝ) (L := ℝ) (σ := RingHom.id ℝ) x₀ (p x₀) hx) p
      (fun c hc x => by rw [hsmul, abs_of_pos hc]) hadd (fun ⟨x, hxm⟩ => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxm
        have e1 : (LinearPMap.mkSpanSingleton (K := ℝ) (L := ℝ) (σ := RingHom.id ℝ) x₀ (p x₀) hx)
            ⟨c • x₀, hxm⟩ = c • p x₀ :=
          LinearPMap.mkSpanSingleton'_apply _ _ _ _ _
        rw [e1]
        show c • p x₀ ≤ p (c • x₀)
        rw [hsmul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_right (le_abs_self c) (hnn _))
    refine ⟨g, ?_, fun y => abs_le.2 ⟨?_, hg2 y⟩⟩
    · have hmem : x₀ ∈ (LinearPMap.mkSpanSingleton (K := ℝ) (L := ℝ) (σ := RingHom.id ℝ) x₀ (p x₀) hx).domain := by
        show x₀ ∈ Submodule.span ℝ {x₀}
        exact Submodule.mem_span_singleton_self x₀
      have h1 := hg1 ⟨x₀, hmem⟩
      have h2 : (LinearPMap.mkSpanSingleton (K := ℝ) (L := ℝ) (σ := RingHom.id ℝ) x₀ (p x₀) hx) ⟨x₀, hmem⟩ = p x₀ :=
        LinearPMap.mkSpanSingleton_apply ℝ ℝ hx (p x₀)
      rw [h2] at h1
      exact h1
    · have := hg2 (-y)
      rw [map_neg, hneg] at this
      linarith
variable {S : Finset F.Cell}
theorem exists_linear_chartValues_le_localNorm (R : F.FieldChain) (w : F.SiteWeights) (hw : ∀ j x, 0 ≤ w j x)
    (z : F.Cell) (A₀ : ChainChart F) :
    ∃ ℓ : ChartValues S →ₗ[ℝ] ℝ, ℓ (chartValues S A₀) = localNorm S R A₀ w z ∧
      ∀ B : ChainChart F, |ℓ (chartValues S B)| ≤ localNorm S R B w z := by
  set p : ChartValues S → ℝ := fun e => localNorm S R (chartOfValues S (zeroChart F) e) w z with hp
  have hread : ∀ B : ChainChart F, p (chartValues S B) = localNorm S R B w z := fun B =>
    localNorm_congr S R w z (chartOfValues_agreeOn _ B)
  have hbond : ∀ (e : ChartValues S) (b : F.Site 0 × Fin 4) (hb : b ∈ innerBonds S 0),
      (chartOfValues S (zeroChart F) e).fine b.1 b.2 = e.1 ⟨b, hb⟩ := by
    intro e b hb
    simp only [chartOfValues]
    rw [dif_pos (show (b.1, b.2) ∈ innerBonds S 0 from hb)]
  have hbond2 : ∀ (e : ChartValues S) (j : ℕ) (hj : j + 1 < F.top) (b : F.Site (j + 1) × Fin 4)
      (hb : b ∈ innerBonds S (j + 1)), ∃ hj' : j < F.depth,
      (chartOfValues S (zeroChart F) e).coarse j b.1 b.2 = e.2 ⟨j, hj'⟩ ⟨b, hb⟩ := by
    intro e j hj b hb
    have hj' : j < F.depth := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    refine ⟨hj', ?_⟩
    simp only [chartOfValues]
    rw [dif_pos hj', dif_pos (show (b.1, b.2) ∈ innerBonds S (j + 1) from hb)]
  have hadd : ∀ x y : ChartValues S, p (x + y) ≤ p x + p y := by
    intro x y
    have hs : ChartEqOnBonds S (chartOfValues S (zeroChart F) (x + y))
        (chartMove (chartOfValues S (zeroChart F) x) (chartOfValues S (zeroChart F) y) 1) := by
      refine ⟨fun b hb => ?_, fun j hj b hb => ?_⟩
      · simp only [chartMove, one_smul]
        rw [hbond _ b hb, hbond _ b hb, hbond _ b hb]
        rfl
      · simp only [chartMove, one_smul]
        obtain ⟨h1, e1⟩ := hbond2 (x + y) j hj b hb
        obtain ⟨h2, e2⟩ := hbond2 x j hj b hb
        obtain ⟨h3, e3⟩ := hbond2 y j hj b hb
        rw [e1, e2, e3]
        rfl
    have := localNorm_chartMove_le S R (chartOfValues S (zeroChart F) x)
      (chartOfValues S (zeroChart F) y) 1 w hw z
    simp only [abs_one, one_mul] at this
    simp only [hp]
    rw [localNorm_congr S R w z hs]
    exact this
  have hle : ∀ (c : ℝ) (x : ChartValues S), p (c • x) ≤ |c| * p x := by
    intro c x
    have hs : ChartEqOnBonds S (chartOfValues S (zeroChart F) (c • x))
        (chartMove (zeroChart F) (chartOfValues S (zeroChart F) x) c) := by
      refine ⟨fun b hb => ?_, fun j hj b hb => ?_⟩
      · simp only [chartMove]
        rw [hbond _ b hb, hbond _ b hb]
        simp [zeroChart]
      · simp only [chartMove]
        obtain ⟨h1, e1⟩ := hbond2 (c • x) j hj b hb
        obtain ⟨h2, e2⟩ := hbond2 x j hj b hb
        rw [e1, e2]
        simp [zeroChart]
    have := localNorm_chartMove_le S R (zeroChart F) (chartOfValues S (zeroChart F) x) c w hw z
    have h0 : localNorm S R (zeroChart F) w z = 0 := by
      unfold localNorm localNormSq
      simp [zeroChart, linearizedCurl, adjointAction]
    rw [h0, zero_add] at this
    simp only [hp]
    rw [localNorm_congr S R w z hs]
    exact this
  have hsmul : ∀ (c : ℝ) (x : ChartValues S), p (c • x) = |c| * p x := by
    intro c x
    refine le_antisymm (hle c x) ?_
    by_cases hc : c = 0
    · subst hc
      simp only [abs_zero, zero_mul]
      exact Real.sqrt_nonneg _
    · have h1 := hle c⁻¹ (c • x)
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul, abs_inv] at h1
      have hpos : 0 < |c| := abs_pos.2 hc
      rw [inv_mul_eq_div, le_div_iff₀ hpos] at h1
      linarith
  obtain ⟨ℓ, h1, h2⟩ := exists_linear_le_seminorm p hadd hsmul (chartValues S A₀)
  refine ⟨ℓ, h1.trans (hread A₀), fun B => (h2 _).trans (le_of_eq (hread B))⟩
variable {V : F.GaugeField F.top} {k : ℕ} {b : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
  {a θ δ Ca c C s : ℝ}
theorem analyticAt_complexTotalOverTop_line (hB : TwistedTotalBounds a θ δ Ca c C s S V b X)
    {W : ComplexChainChart F} {ζ : Fin k → ℂ} (hW : complexSupWeightedNorm S δ (referenceFieldChain S V) W ≤ c)
    (hζ : ∑ l, ‖ζ l‖ ≤ c) (A : ChainChart F) :
    AnalyticAt ℂ
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
  have hline : AnalyticAt ℂ (fun τ : ℂ => (((![1, Complex.I, τ], ζ)) : (Fin 3 → ℂ) × (Fin k → ℂ))) 0 := by
    refine AnalyticAt.prod ?_ analyticAt_const
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_id
  have hcomp := AnalyticAt.comp (g := fun q : (Fin 3 → ℂ) × (Fin k → ℂ) =>
    complexTotalOverTop a S (referenceFieldChain S V) (complexSpan A' q.1) (complexTwistedTop b X q.2 V))
    (x := (0 : ℂ)) h0 hline
  have e : (fun τ : ℂ => complexTotalOverTop a S (referenceFieldChain S V) (complexChartMove W A τ)
        (complexTwistedTop b X ζ V)) =
      (fun q : (Fin 3 → ℂ) × (Fin k → ℂ) =>
        complexTotalOverTop a S (referenceFieldChain S V) (complexSpan A' q.1) (complexTwistedTop b X q.2 V)) ∘
      fun τ : ℂ => (((![1, Complex.I, τ], ζ)) : (Fin 3 → ℂ) × (Fin k → ℂ)) := by
    funext τ
    simp only [Function.comp, hsp]
  rw [e]
  exact hcomp
theorem complexSupWeightedNorm_realChart (hL : 0 < F.blockSide) (R : F.FieldChain) (U : ChainChart F) :
    complexSupWeightedNorm S δ R (realChart U) = supWeightedNorm S δ R U := by
  have h := supWeightedNorm_smul S hL δ R (zeroChart F) 0
  have e : chartMove (zeroChart F) (zeroChart F) 0 = zeroChart F := by
    apply chainChart_ext
    · funext p i
      simp [chartMove, zeroChart]
    · funext j p i
      simp [chartMove, zeroChart]
  rw [e] at h
  have h2 : supWeightedNorm S δ R (zeroChart F) = 0 := by simpa using h
  show supWeightedNorm S δ R U + supWeightedNorm S δ R (zeroChart F) = supWeightedNorm S δ R U
  rw [h2, add_zero]
theorem hasDerivAt_chartAction_of_complexFirstVariation {c₁ : ℝ} (hL : Odd F.blockSide) (hδ : 0 ≤ δ)
    (hB : TwistedTotalBounds a θ δ Ca c C s S V b X)
    (hreg : ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c₁ →
      ChartIsRegular S (referenceFieldChain S V) U)
    (ζ : Fin k → ℝ) (hζ : ∑ l, |ζ l| ≤ c) (U A : ChainChart F)
    (hU : supWeightedNorm S δ (referenceFieldChain S V) U ≤ c)
    (hU₁ : supWeightedNorm S δ (referenceFieldChain S V) U < c₁) :
    HasDerivAt (fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ)
          (rotatedField (bondSpread b X ζ) V))
        (complexFirstVariation a S (referenceFieldChain S V) (realChart U)
          (complexTwistedTop b X (fun l => (ζ l : ℂ)) V) A).re 0 ∧
      (complexFirstVariation a S (referenceFieldChain S V) (realChart U)
          (complexTwistedTop b X (fun l => (ζ l : ℂ)) V) A).im = 0 := by
  have hsum : ∑ l, ‖((ζ l : ℝ) : ℂ)‖ ≤ c := by
    simpa [Complex.norm_real] using hζ
  have hd := differentiableAt_complexChartMove_line hB (W := realChart U) (ζ := fun l => (ζ l : ℂ))
    (by rw [complexSupWeightedNorm_realChart hL.pos]; exact hU) hsum A
  rw [complexTwistedTop_ofReal] at hd ⊢
  exact complexFirstVariation_real a _ U A _ hd (eventually_chartIsRegular_chartMove hL.pos hδ hreg A hU₁)
end YangMills.Construction.ComplexFamilies
end
