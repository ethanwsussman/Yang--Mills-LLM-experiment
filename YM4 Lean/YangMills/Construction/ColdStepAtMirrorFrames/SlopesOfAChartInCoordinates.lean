import YangMills.Construction.ColdStepAtMirrorFrames.SlopeAlongASegmentProof
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeOfAFrameBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeMovesByItsKernelsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages Calculus QuaternionExp
namespace ColdStepAtMirrorFrames.ChartSlopes
section
section MeanValue
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
theorem abs_sub_le_mul_of_hasDerivAt {f f' : ℝ → ℝ} {M τ : ℝ} (hτ : 0 ≤ τ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) τ, HasDerivAt f (f' t) t)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) τ, |f' t| ≤ M) : |f τ - f 0| ≤ M * τ := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f') (C := M)
    (s := Set.Icc (0 : ℝ) τ) (x := 0) (y := τ) (fun t ht => (hf t ht).hasDerivWithinAt)
    (fun t ht => by simpa using hM t ht) (convex_Icc _ _) ⟨le_rfl, hτ⟩ ⟨hτ, le_rfl⟩
  simpa [abs_of_nonneg hτ] using h
theorem hasDerivAt_along_line {g : E → ℝ} {p n : E} {t : ℝ} (hg : DifferentiableAt ℝ g (p + t • n)) :
    HasDerivAt (fun s : ℝ => g (p + s • n)) (fderiv ℝ g (p + t • n) n) t := by
  have h1 : HasDerivAt (fun s : ℝ => p + s • n) n t := by
    simpa using ((hasDerivAt_id t).smul_const n).const_add p
  exact hg.hasFDerivAt.comp_hasDerivAt t h1
theorem analyticAt_fderiv_apply {A : E → ℝ} {z : E} (hA : AnalyticAt ℝ A z) (v : E) :
    AnalyticAt ℝ (fun σ => fderiv ℝ A σ v) z := by
  have h1 := hA.fderiv
  have h2 : AnalyticAt ℝ (fun M : E →L[ℝ] ℝ => M v) (fderiv ℝ A z) :=
    (ContinuousLinearMap.apply ℝ ℝ v).analyticAt _
  exact h2.comp h1
theorem hasDerivAt_fderiv_along_line {g : E → ℝ} {p n d : E} {t : ℝ} (hg : AnalyticAt ℝ g (p + t • n)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ g (p + s • n) d)
      (iteratedFDeriv ℝ 2 g (p + t • n) ![n, d]) t := by
  have h0 : DifferentiableAt ℝ (fderiv ℝ g) (p + t • n) := hg.fderiv.differentiableAt
  have h1 : HasDerivAt (fun s : ℝ => p + s • n) n t := by
    simpa using ((hasDerivAt_id t).smul_const n).const_add p
  have h2 := h0.hasFDerivAt.comp_hasDerivAt t h1
  have h3 : HasDerivAt (fun s : ℝ => fderiv ℝ g (p + s • n) d) ((fderiv ℝ (fderiv ℝ g) (p + t • n) n) d) t := by
    have h4 := (ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp_hasDerivAt t h2
    exact h4
  rw [iteratedFDeriv_two_apply]
  simpa using h3
theorem abs_mixed_difference_le {g : E → ℝ} {d n : E} {M : ℝ}
    (hg : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℝ g (θ • d + t • n))
    (hM : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedFDeriv ℝ 2 g (θ • d + t • n) ![n, d]| ≤ M) :
    |g (d + n) - g n - g d + g 0| ≤ M := by
  have hφ : ∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun θ : ℝ => g (n + θ • d) - g ((0 : E) + θ • d))
      (fderiv ℝ g (n + θ • d) d - fderiv ℝ g ((0 : E) + θ • d) d) θ := by
    intro θ hθ
    have e1 : n + θ • d = θ • d + (1 : ℝ) • n := by rw [one_smul, add_comm]
    have e2 : (0 : E) + θ • d = θ • d + (0 : ℝ) • n := by simp
    refine HasDerivAt.sub (hasDerivAt_along_line ?_) (hasDerivAt_along_line ?_)
    · rw [e1]
      exact (hg θ hθ 1 ⟨zero_le_one, le_rfl⟩).differentiableAt
    · rw [e2]
      exact (hg θ hθ 0 ⟨le_rfl, zero_le_one⟩).differentiableAt
  have hb : ∀ θ ∈ Set.Icc (0 : ℝ) 1, |fderiv ℝ g (n + θ • d) d - fderiv ℝ g ((0 : E) + θ • d) d| ≤ M := by
    intro θ hθ
    have h := abs_sub_le_mul_of_hasDerivAt (f := fun s : ℝ => fderiv ℝ g (θ • d + s • n) d)
      (f' := fun s => iteratedFDeriv ℝ 2 g (θ • d + s • n) ![n, d]) (M := M) (τ := 1) zero_le_one
      (fun t ht => hasDerivAt_fderiv_along_line (hg θ hθ t ht)) (fun t ht => hM θ hθ t ht)
    simpa [add_comm] using h
  have h := abs_sub_le_mul_of_hasDerivAt (f := fun θ : ℝ => g (n + θ • d) - g ((0 : E) + θ • d))
    (f' := fun θ => fderiv ℝ g (n + θ • d) d - fderiv ℝ g ((0 : E) + θ • d) d) (M := M) (τ := 1) zero_le_one hφ hb
  have e : g (d + n) - g n - g d + g 0 = (g (n + (1 : ℝ) • d) - g ((0 : E) + (1 : ℝ) • d)) -
      (g (n + (0 : ℝ) • d) - g ((0 : E) + (0 : ℝ) • d)) := by
    simp only [one_smul, zero_smul, add_zero, zero_add, add_comm]
    ring
  rw [e]
  simpa using h
theorem abs_deriv_zero_le_of_second_deriv {f f' f'' : ℝ → ℝ} {M K τ : ℝ} (hτ : 0 < τ)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) τ, HasDerivAt f (f' s) s)
    (hf' : ∀ s ∈ Set.Icc (0 : ℝ) τ, HasDerivAt f' (f'' s) s)
    (h0 : |f 0| ≤ M) (h1 : |f τ| ≤ M) (hK : ∀ s ∈ Set.Icc (0 : ℝ) τ, |f'' s| ≤ K) :
    |f' 0| ≤ 2 * M / τ + K * τ := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨le_rfl, hτ.le⟩)
  have hs : ∀ s ∈ Set.Icc (0 : ℝ) τ, |f' s - f' 0| ≤ K * τ := by
    intro s hs
    have h := abs_sub_le_mul_of_hasDerivAt (f := f') (f' := f'') (M := K) (τ := s) hs.1
      (fun t ht => hf' t ⟨ht.1, ht.2.trans hs.2⟩) (fun t ht => hK t ⟨ht.1, ht.2.trans hs.2⟩)
    exact h.trans (mul_le_mul_of_nonneg_left hs.2 hK0)
  have hk := abs_sub_le_mul_of_hasDerivAt (f := fun s => f s - s * f' 0) (f' := fun s => f' s - f' 0) (M := K * τ)
    (τ := τ) hτ.le (fun s hs => by
      have := (hf s hs).fun_sub ((hasDerivAt_id' s).mul_const (f' 0))
      simpa only [one_mul] using this) hs
  simp only [zero_mul, sub_zero] at hk
  have e : τ * |f' 0| ≤ 2 * M + K * τ * τ := by
    have e1 : τ * f' 0 = (f τ - f 0) - ((f τ - τ * f' 0) - f 0) := by ring
    have e2 : τ * |f' 0| = |τ * f' 0| := by rw [abs_mul, abs_of_pos hτ]
    rw [e2, e1]
    have e3 := abs_sub (f τ - f 0) ((f τ - τ * f' 0) - f 0)
    have e4 := abs_sub (f τ) (f 0)
    linarith
  have e2 : |f' 0| ≤ (2 * M + K * τ * τ) / τ := by
    rw [le_div_iff₀ hτ]
    linarith
  have e3 : (2 * M + K * τ * τ) / τ = 2 * M / τ + K * τ := by
    field_simp
  linarith
theorem abs_fderiv_sub_le_of_two_lines {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
    {g : E → ℝ} {g' : E' → ℝ} {z y : E} {z' y' : E'} {M K τ : ℝ} (hτ : 0 < τ)
    (hg : ∀ s ∈ Set.Icc (0 : ℝ) τ, AnalyticAt ℝ g (z + s • y))
    (hg' : ∀ s ∈ Set.Icc (0 : ℝ) τ, AnalyticAt ℝ g' (z' + s • y'))
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) τ, |g (z + s • y) - g' (z' + s • y')| ≤ M)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) τ, |iteratedFDeriv ℝ 2 g (z + s • y) ![y, y]| ≤ K)
    (hK' : ∀ s ∈ Set.Icc (0 : ℝ) τ, |iteratedFDeriv ℝ 2 g' (z' + s • y') ![y', y']| ≤ K) :
    |fderiv ℝ g z y - fderiv ℝ g' z' y'| ≤ 2 * M / τ + 2 * K * τ := by
  have h := abs_deriv_zero_le_of_second_deriv (f := fun s : ℝ => g (z + s • y) - g' (z' + s • y'))
    (f' := fun s => fderiv ℝ g (z + s • y) y - fderiv ℝ g' (z' + s • y') y')
    (f'' := fun s => iteratedFDeriv ℝ 2 g (z + s • y) ![y, y] - iteratedFDeriv ℝ 2 g' (z' + s • y') ![y', y'])
    (M := M) (K := 2 * K) (τ := τ) hτ
    (fun s hs => (hasDerivAt_along_line (hg s hs).differentiableAt).sub (hasDerivAt_along_line (hg' s hs).differentiableAt))
    (fun s hs => (hasDerivAt_fderiv_along_line (hg s hs)).sub (hasDerivAt_fderiv_along_line (hg' s hs)))
    (by simpa using hM 0 ⟨le_rfl, hτ.le⟩) (hM τ ⟨hτ.le, le_rfl⟩)
    (fun s hs => by
      have := abs_sub (iteratedFDeriv ℝ 2 g (z + s • y) ![y, y]) (iteratedFDeriv ℝ 2 g' (z' + s • y') ![y', y'])
      have h1 := hK s hs
      have h2 := hK' s hs
      linarith)
  simpa using h
end MeanValue
theorem weightedNorm_nonneg {N : ℕ} {wt : Fin N → ℝ} (hw : ∀ n, 0 ≤ wt n) (x : Fin N → ℝ) : 0 ≤ _root_.YangMills.Construction.Calculus.weightedNorm wt x :=
  Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (hw n)
theorem abs_multilinear_le_of_basis {N j : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin N → ℝ) ℝ) (K : ℝ)
    (wt : Fin N → ℝ) (hw : ∀ n, 0 ≤ wt n) (hK : 0 ≤ K)
    (hT : ∀ r : Fin j → Fin N, |T (fun i => Pi.single (r i) 1)| ≤ K * ∏ i, wt (r i))
    (ξ : Fin j → Fin N → ℝ) : |T ξ| ≤ K * ∏ i, _root_.YangMills.Construction.Calculus.weightedNorm wt (ξ i) := by apply _root_.YangMills.Construction.Calculus.abs_multilinear_le_prod_weightedNorm <;> assumption
end
section
variable {F : BlockFrame}
theorem abs_imaginaryCoord_le (α : Fin 3) (w : imaginaryQuaternions) : |imaginaryCoord α w| ≤ ‖w‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.abs_imaginaryCoord_le <;> assumption
theorem chartCoordinates_add (dw₁ dw₂ : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (dv₁ dv₂ : F.Site F.top → Fin 4 → imaginaryQuaternions) (θ : ℝ) :
    chartCoordinates (fun x i => dw₁ x i + θ • dw₂ x i) (fun y i => dv₁ y i + θ • dv₂ y i) =
      chartCoordinates dw₁ dv₁ + θ • chartCoordinates dw₂ dv₂ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.chartCoordinates_add_smul <;> assumption
theorem chartCoordinates_zero : chartCoordinates (F := F) (fun _ _ => 0) (fun _ _ => 0) = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.chartCoordinates_zero <;> assumption
def chartOffset (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) : Fin (chartDimension F) → ℝ :=
  chartCoordinates dw (fun _ _ => 0)
theorem chartOffset_add (dw₁ dw₂ : F.Site F.depth → Fin 4 → imaginaryQuaternions) (θ : ℝ) :
    chartOffset (fun x i => dw₁ x i + θ • dw₂ x i) = chartOffset dw₁ + θ • chartOffset dw₂ := by
  have := chartCoordinates_add dw₁ dw₂ (fun _ _ => (0 : imaginaryQuaternions)) (fun _ _ => (0 : imaginaryQuaternions)) θ
  have e : (fun (_ : F.Site F.top) (_ : Fin 4) => (0 : imaginaryQuaternions) + θ • (0 : imaginaryQuaternions)) =
      fun _ _ => 0 := by
    funext y i
    simp
  rw [e] at this
  exact this
theorem chartOffset_zero : chartOffset (F := F) (fun _ _ => 0) = 0 := chartCoordinates_zero
theorem chartOffset_smul (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (θ : ℝ) :
    chartOffset (fun x i => θ • dw x i) = θ • chartOffset dw := by
  have := chartOffset_add (fun _ _ => 0) dw θ
  simp only [zero_add, chartOffset_zero] at this
  exact this
theorem chartOffset_sum {ι : Type} (s : Finset ι) (f : ι → F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    chartOffset (fun x i => ∑ q ∈ s, f q x i) = ∑ q ∈ s, chartOffset (f q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using chartOffset_zero
  | insert q s hq ih =>
    simp only [Finset.sum_insert hq]
    rw [← ih]
    have := chartOffset_add (f q) (fun x i => ∑ q ∈ s, f q x i) 1
    simpa using this
open Classical in
def bondBump (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) (x : F.Site F.depth) (i : Fin 4) :
    imaginaryQuaternions := if (x, i) = b then e else 0
def bondBumpCoords (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) : Fin (chartDimension F) → ℝ :=
  chartOffset (bondBump b e)
theorem bondBump_smul (b : F.Site F.depth × Fin 4) (c : ℝ) (e : imaginaryQuaternions) :
    bondBump b (c • e) = fun x i => c • bondBump b e x i := by
  funext x i
  unfold bondBump
  split_ifs <;> simp
theorem bondBumpCoords_smul (b : F.Site F.depth × Fin 4) (c : ℝ) (e : imaginaryQuaternions) :
    bondBumpCoords b (c • e) = c • bondBumpCoords b e := by
  unfold bondBumpCoords
  rw [bondBump_smul, chartOffset_smul]
def energyNear (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) :
    (Fin (chartDimension F) → ℝ) → ℝ :=
  chartRestriction a w V (chartDirections F)
def shiftChart (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => w x i + dw x i
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem leftTranslate_zero (V : F.GaugeField F.top) : leftTranslate (fun _ _ => 0) V = V := by apply _root_.YangMills.SharedProofs.p46723 <;> assumption
theorem energyNear_chartOffset (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (a : ℝ) (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) :
    energyNear a w V (chartOffset dw) = chartedEnergy a (shiftChart w dw) V := by
  have := (hCE F a w dw V (fun _ _ => 0) hL hs).1
  rw [leftTranslate_zero] at this
  exact this
theorem energyNear_add_chartOffset (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (a : ℝ) (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (σ : Fin (chartDimension F) → ℝ) :
    energyNear a w V (chartOffset dw + σ) = energyNear a (shiftChart w dw) V σ :=
  (hCE F a w dw V (fun _ _ => 0) hL hs).2 σ
theorem analyticAt_of_translate {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A B : E → ℝ) (p : E)
    (h : ∀ σ, A (p + σ) = B σ) (hB : AnalyticAt ℝ B 0) : AnalyticAt ℝ A p := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.InterpolatedSlopeLemmas.analyticAt_of_shift <;> assumption
theorem energyNear_analyticAt (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (a : ℝ) (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (hB : AnalyticAt ℝ (energyNear a (shiftChart w dw) V) 0) : AnalyticAt ℝ (energyNear a w V) (chartOffset dw) :=
  analyticAt_of_translate _ _ _ (energyNear_add_chartOffset hCE hL hs a w dw V) hB
theorem update_eq_add_bondBump (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (b : F.Site F.depth × Fin 4)
    (e : imaginaryQuaternions) (u : ℝ) :
    Function.update w b.1 (Function.update (w b.1) b.2 (w b.1 b.2 + u • e)) = fun x i => w x i + u • bondBump b e x i := by
  classical
  funext x i
  obtain ⟨b1, b2⟩ := b
  by_cases hx : x = b1
  · subst hx
    by_cases hi : i = b2
    · subst hi
      simp [bondBump]
    · simp [bondBump, Function.update_of_ne hi, hi]
  · have : (x, i) ≠ (b1, b2) := fun h => hx (congrArg Prod.fst h)
    simp [bondBump, Function.update_of_ne hx, this]
theorem chartedSlope_eq_fderiv (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (a : ℝ) (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (b : F.Site F.depth × Fin 4)
    (e : imaginaryQuaternions) (hd : DifferentiableAt ℝ (energyNear a w V) (chartOffset dw)) :
    chartedSlope a (shiftChart w dw) V b e = fderiv ℝ (energyNear a w V) (chartOffset dw) (bondBumpCoords b e) := by
  unfold chartedSlope
  have hline : (fun u : ℝ => chartedEnergy a (Function.update (shiftChart w dw) b.1
      (Function.update (shiftChart w dw b.1) b.2 (shiftChart w dw b.1 b.2 + u • e))) V) =
      fun u : ℝ => energyNear a w V (chartOffset dw + u • bondBumpCoords b e) := by
    funext u
    rw [update_eq_add_bondBump]
    unfold bondBumpCoords
    rw [← chartOffset_add, energyNear_chartOffset hCE hL hs]
    congr 1
    funext x i
    simp only [shiftChart, add_assoc]
  rw [hline]
  have h1 : HasDerivAt (fun u : ℝ => chartOffset dw + u • bondBumpCoords b e) (bondBumpCoords b e) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (bondBumpCoords b e)).const_add (chartOffset dw)
  have h2 : HasFDerivAt (energyNear a w V) (fderiv ℝ (energyNear a w V) (chartOffset dw))
      ((fun u : ℝ => chartOffset dw + u • bondBumpCoords b e) 0) := by
    simpa using hd.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℝ) h1).deriv
theorem iteratedFDeriv_comp_add_left_zero {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : E → H) (n : ℕ) (p : E) : iteratedFDeriv ℝ n (fun z => f (p + z)) 0 = iteratedFDeriv ℝ n f p := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.iteratedFDeriv_comp_add_left_zero <;> assumption
theorem iteratedFDeriv_fderiv_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E → ℝ) (v p : E) (hA : AnalyticAt ℝ A p) (l : ℕ) (m : Fin l → E) :
    iteratedFDeriv ℝ l (fun σ => fderiv ℝ A σ v) p m = (iteratedFDeriv ℝ l (fderiv ℝ A) p m) v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.InterpolatedSlopeLemmas.iteratedFDeriv_fderiv_apply <;> assumption
theorem iteratedFDeriv_fderiv_apply_snoc {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : E → ℝ) (w p : E)
    (l : ℕ) (m : Fin l → E) :
    (iteratedFDeriv ℝ l (fderiv ℝ A) p m) w = iteratedFDeriv ℝ (l + 1) A p (Fin.snoc m w) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.InterpolatedSlopeLemmas.iteratedFDeriv_fderiv_apply_eq_succ <;> assumption
theorem norm_chartDirections (n : Fin (chartDimension F)) : ‖directionVector (chartDirections F n)‖ = 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.norm_directionVector_chartDirections <;> assumption
theorem iteratedFDeriv_chartRestriction_single (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) {N l : ℕ} (q : Fin N → ChartDirection F)
    (ρ : Fin l → Fin N) (hB : AnalyticAt ℝ (chartRestriction a w V q) 0) :
    iteratedFDeriv ℝ l (chartRestriction a w V q) 0 (fun j => Pi.single (ρ j) 1) = chartMixedDeriv a w V (q ∘ ρ) := by apply _root_.YangMills.SharedProofs.p3455 <;> assumption
theorem snoc_single_eq {N l : ℕ} (r : Fin l → Fin N) (n : Fin N) :
    (Fin.snoc (fun i => Pi.single (r i) (1 : ℝ)) (Pi.single n 1) : Fin (l + 1) → Fin N → ℝ) =
      fun j => Pi.single ((Fin.snoc r n : Fin (l + 1) → Fin N) j) 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.InterpolatedSlopeLemmas.snoc_single_eq <;> assumption
theorem bondBumpCoords_eq_sum (b : F.Site F.depth × Fin 4) (hb : b ∈ chordBonds (finiteCells F))
    (e : imaginaryQuaternions) :
    bondBumpCoords b e = ∑ α, imaginaryCoord α e •
      (Pi.single (chartCoordinateEquiv F (.inl (⟨b, hb⟩, α))) (1 : ℝ) : Fin (chartDimension F) → ℝ) := by
  classical
  funext n
  obtain ⟨ι, rfl⟩ := (chartCoordinateEquiv F).surjective n
  simp only [bondBumpCoords, chartOffset, chartCoordinates, Equiv.symm_apply_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply, (chartCoordinateEquiv F).injective.eq_iff]
  rcases ι with ⟨b', β⟩ | ⟨t, β⟩
  · by_cases hbb : b' = ⟨b, hb⟩
    · subst hbb
      simp only [coordinateOfIndex, bondBump]
      simp [Prod.mk.injEq]
    · have hne : (b'.1.1, b'.1.2) ≠ b := fun h => hbb (Subtype.ext h)
      simp only [coordinateOfIndex, bondBump, if_neg hne, map_zero]
      symm
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [if_neg, mul_zero]
      intro h
      have := Sum.inl.inj h
      exact hbb (congrArg Prod.fst this)
  · simp [coordinateOfIndex]
theorem abs_iteratedFDeriv_slope_basis_le (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    (a : ℝ) (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (b : F.Site F.depth × Fin 4)
    (hb : b ∈ chordBonds (finiteCells F))
    (e : imaginaryQuaternions) (δ₁ β : ℝ) (hβ0 : 0 ≤ β) (l : ℕ) (hβ : (l : ℝ) * β ≤ δ₁) (Ckl : ℝ)
    (hCk0 : 0 ≤ Ckl)
    (hB : AnalyticAt ℝ (energyNear a (shiftChart w dw) V) 0)
    (hker : ∀ q' : Fin (l + 1) → ChartDirection F, (∀ j, ‖directionVector (q' j)‖ = 1) →
      |chartMixedDeriv a (shiftChart w dw) V q'| ≤ Ckl * Real.exp (-(δ₁ * directionDiameter q')))
    (r : Fin l → Fin (chartDimension F)) :
    |iteratedFDeriv ℝ l (fun σ => fderiv ℝ (energyNear a w V) σ (bondBumpCoords b e))
        (chartOffset dw) (fun i => Pi.single (r i) 1)| ≤
      (3 * Ckl * ‖e‖) * ∏ i, Real.exp (-(β * cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1))) := by
  classical
  have hA := energyNear_analyticAt hCE hL hs a w dw V hB
  obtain ⟨p, hp⟩ : ∃ p, p = chartOffset (F := F) dw := ⟨_, rfl⟩
  rw [← hp] at hA ⊢
  rw [iteratedFDeriv_fderiv_apply _ _ _ hA, bondBumpCoords_eq_sum b hb e, map_sum]
  simp only [map_smul, smul_eq_mul]
  have hshift : (fun z => energyNear a w V (p + z)) = energyNear a (shiftChart w dw) V := by
    funext z
    rw [hp, energyNear_add_chartOffset hCE hL hs]
  have hterm : ∀ α : Fin 3, |(iteratedFDeriv ℝ l (fderiv ℝ (energyNear a w V)) p fun i => Pi.single (r i) 1)
      (Pi.single (chartCoordinateEquiv F (.inl (⟨b, hb⟩, α))) (1 : ℝ))| ≤
      Ckl * ∏ i, Real.exp (-(β * cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1))) := by
    intro α
    rw [iteratedFDeriv_fderiv_apply_snoc, ← iteratedFDeriv_comp_add_left_zero, hshift, snoc_single_eq]
    unfold energyNear
    rw [iteratedFDeriv_chartRestriction_single _ _ _ _ _ hB]
    obtain ⟨q', hq'⟩ : ∃ q', q' = chartDirections F ∘
        (Fin.snoc r (chartCoordinateEquiv F (.inl (⟨b, hb⟩, α))) : Fin (l + 1) → Fin (chartDimension F)) := ⟨_, rfl⟩
    rw [← hq']
    have hu : ∀ j, ‖directionVector (q' j)‖ = 1 := fun j => by
      rw [hq']
      exact norm_chartDirections _
    refine (hker q' hu).trans ?_
    have hlast : directionCell (q' (Fin.last l)) = enclosingCell b.1 := by
      rw [hq']
      simp [chartDirections, directionOfIndex, directionCell]
    have hcast : ∀ i, q' (Fin.castSucc i) = chartDirections F (r i) := fun i => by
      rw [hq']
      simp
    have hd : ∀ i, cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1) ≤ directionDiameter q' := by
      intro i
      rw [← hcast, ← hlast]
      unfold directionDiameter
      refine le_trans ?_ (Finset.le_sup
        (f := fun l₁ => Finset.univ.sup fun l₂ => cellSupDist (directionCell (q' l₁)) (directionCell (q' l₂)))
        (Finset.mem_univ (Fin.castSucc i)))
      exact Finset.le_sup (f := fun l₂ => cellSupDist (directionCell (q' (Fin.castSucc i))) (directionCell (q' l₂)))
        (Finset.mem_univ (Fin.last l))
    refine mul_le_mul_of_nonneg_left ?_ hCk0
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    rw [Finset.sum_neg_distrib, neg_le_neg_iff, ← Finset.mul_sum]
    have h2 : ∑ i, (cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1) : ℝ) ≤
        l * directionDiameter q' := by
      calc ∑ i, (cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1) : ℝ)
          ≤ ∑ _i : Fin l, (directionDiameter q' : ℝ) := Finset.sum_le_sum fun i _ => by exact_mod_cast hd i
        _ = l * directionDiameter q' := by simp
    have h3 : (0 : ℝ) ≤ directionDiameter q' := by positivity
    calc β * ∑ i, (cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1) : ℝ) ≤
          β * (l * directionDiameter q') :=
          mul_le_mul_of_nonneg_left h2 hβ0
      _ = ((l : ℝ) * β) * directionDiameter q' := by ring
      _ ≤ δ₁ * directionDiameter q' := mul_le_mul_of_nonneg_right hβ h3
  have hcoef : ∀ α : Fin 3, |imaginaryCoord α e| ≤ ‖e‖ := fun α => abs_imaginaryCoord_le α e
  have hP0 : 0 ≤ ∏ i, Real.exp (-(β * cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1))) :=
    Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  have hCkP : 0 ≤ Ckl * ∏ i, Real.exp (-(β * cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1))) :=
    mul_nonneg hCk0 hP0
  calc |∑ α, imaginaryCoord α e * (iteratedFDeriv ℝ l (fderiv ℝ (energyNear a w V)) p fun i => Pi.single (r i) 1)
        (Pi.single (chartCoordinateEquiv F (.inl (⟨b, hb⟩, α))) (1 : ℝ))|
      ≤ ∑ _α : Fin 3, ‖e‖ * (Ckl *
          ∏ i, Real.exp (-(β * cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1)))) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
        rw [abs_mul]
        exact mul_le_mul (hcoef α) (hterm α) (abs_nonneg _) (norm_nonneg _)
    _ = (3 * Ckl * ‖e‖) *
          ∏ i, Real.exp (-(β * cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1))) := by
        simp
        ring
def cellWeight (β : ℝ) (Z : F.Cell) (n : Fin (chartDimension F)) : ℝ :=
  Real.exp (-(β * cellSupDist (directionCell (chartDirections F n)) Z))
theorem cellWeight_nonneg (β : ℝ) (Z : F.Cell) (n : Fin (chartDimension F)) : 0 ≤ cellWeight β Z n :=
  (Real.exp_pos _).le
theorem abs_fderiv_slope_le (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (a : ℝ) (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (b : F.Site F.depth × Fin 4)
    (hb : b ∈ chordBonds (finiteCells F)) (e : imaginaryQuaternions) (δ₁ : ℝ) (hδ₁ : 0 ≤ δ₁) (Ck : ℝ) (hCk0 : 0 ≤ Ck)
    (hB : AnalyticAt ℝ (energyNear a (shiftChart w dw) V) 0)
    (hker : ∀ q' : Fin 2 → ChartDirection F, (∀ j, ‖directionVector (q' j)‖ = 1) →
      |chartMixedDeriv a (shiftChart w dw) V q'| ≤ Ck * Real.exp (-(δ₁ * directionDiameter q')))
    (y : Fin (chartDimension F) → ℝ) :
    |fderiv ℝ (fun σ => fderiv ℝ (energyNear a w V) σ (bondBumpCoords b e)) (chartOffset dw) y| ≤
      (3 * Ck * ‖e‖) * _root_.YangMills.Construction.Calculus.weightedNorm (cellWeight δ₁ (enclosingCell b.1)) y := by
  have h := abs_multilinear_le_of_basis
    (iteratedFDeriv ℝ 1 (fun σ => fderiv ℝ (energyNear a w V) σ (bondBumpCoords b e)) (chartOffset dw))
    (3 * Ck * ‖e‖) (cellWeight δ₁ (enclosingCell b.1)) (cellWeight_nonneg _ _) (by positivity) (fun r => by
      have := abs_iteratedFDeriv_slope_basis_le hCE hL hs a w dw V b hb e δ₁ δ₁ hδ₁ 1 (by simp) Ck hCk0 hB hker r
      simpa [cellWeight] using this) (fun _ => y)
  simpa [iteratedFDeriv_one_apply] using h
theorem abs_iteratedFDeriv_two_slope_le (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    (a : ℝ) (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (b : F.Site F.depth × Fin 4)
    (hb : b ∈ chordBonds (finiteCells F)) (e : imaginaryQuaternions) (δ₁ : ℝ) (hδ₁ : 0 ≤ δ₁) (Ck : ℝ) (hCk0 : 0 ≤ Ck)
    (hB : AnalyticAt ℝ (energyNear a (shiftChart w dw) V) 0)
    (hker : ∀ q' : Fin 3 → ChartDirection F, (∀ j, ‖directionVector (q' j)‖ = 1) →
      |chartMixedDeriv a (shiftChart w dw) V q'| ≤ Ck * Real.exp (-(δ₁ * directionDiameter q')))
    (y y' : Fin (chartDimension F) → ℝ) :
    |iteratedFDeriv ℝ 2 (fun σ => fderiv ℝ (energyNear a w V) σ (bondBumpCoords b e)) (chartOffset dw) ![y, y']| ≤
      (3 * Ck * ‖e‖) * (_root_.YangMills.Construction.Calculus.weightedNorm (cellWeight (δ₁ / 2) (enclosingCell b.1)) y *
        _root_.YangMills.Construction.Calculus.weightedNorm (cellWeight (δ₁ / 2) (enclosingCell b.1)) y') := by
  have h := abs_multilinear_le_of_basis
    (iteratedFDeriv ℝ 2 (fun σ => fderiv ℝ (energyNear a w V) σ (bondBumpCoords b e)) (chartOffset dw))
    (3 * Ck * ‖e‖) (cellWeight (δ₁ / 2) (enclosingCell b.1)) (cellWeight_nonneg _ _) (by positivity) (fun r => by
      have := abs_iteratedFDeriv_slope_basis_le hCE hL hs a w dw V b hb e δ₁ (δ₁ / 2) (by positivity) 2
        (by norm_num; linarith) Ck hCk0 hB hker r
      simpa [cellWeight] using this) ![y, y']
  simpa [Fin.prod_univ_two] using h
theorem weightedNorm_chartOffset_le (ψ : F.Cell → ℝ) (hψ : ∀ z, 0 ≤ ψ z)
    (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    _root_.YangMills.Construction.Calculus.weightedNorm (fun n => ψ (directionCell (chartDirections F n))) (chartOffset dw) ≤
      3 * ∑ b : ↥(chordBonds (finiteCells F)), ‖dw b.1.1 b.1.2‖ * ψ (enclosingCell b.1.1) := by
  classical
  unfold _root_.YangMills.Construction.Calculus.weightedNorm
  have e1 : ∑ n, |chartOffset dw n| * ψ (directionCell (chartDirections F n)) =
      ∑ ι : ChartCoordinateIndex F, |coordinateOfIndex dw (fun _ _ => 0) ι| * ψ (directionCell (directionOfIndex ι)) :=
    (chartCoordinateEquiv F).symm.sum_comp
      (fun ι => |coordinateOfIndex dw (fun _ _ => 0) ι| * ψ (directionCell (directionOfIndex ι)))
  rw [e1, Fintype.sum_sum_type]
  have e2 : ∑ x : ↥(innerBonds (finiteCells F) F.top) × Fin 3,
      |coordinateOfIndex dw (fun _ _ => 0) (Sum.inr x)| *
        ψ (directionCell (directionOfIndex (Sum.inr x : ChartCoordinateIndex F))) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [coordinateOfIndex]
  rw [e2, add_zero, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  simp only [Fin.sum_univ_three, coordinateOfIndex, directionOfIndex, directionCell]
  have h1 := abs_imaginaryCoord_le 0 (dw b.1.1 b.1.2)
  have h2 := abs_imaginaryCoord_le 1 (dw b.1.1 b.1.2)
  have h3 := abs_imaginaryCoord_le 2 (dw b.1.1 b.1.2)
  have h4 := hψ (enclosingCell b.1.1)
  nlinarith
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_chartedField_sub_le (hexp : ExpUnitLipschitzInjective)
    (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) {m : ℝ} (hm0 : 0 ≤ m) (hm : ∀ x i, ‖dw x i‖ ≤ m) (x : F.Site F.depth) (i : Fin 4) :
    ‖((chartedField (shiftChart w dw) V x i : UnitQuaternion) : ℍ[ℝ]) -
      ((chartedField w V x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ m := by
  have hw : ‖((expUnit (shiftChart w dw x i) : UnitQuaternion) : ℍ[ℝ]) -
      ((expUnit (w x i) : UnitQuaternion) : ℍ[ℝ])‖ ≤ m := by
    refine (hexp.1 _ _).trans ?_
    have : shiftChart w dw x i - w x i = dw x i := by simp [shiftChart]
    rw [this]
    exact hm x i
  unfold chartedField
  split_ifs with h1 h2
  · have e1 : ((expUnit (shiftChart w dw x i) * V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ]) -
        ((expUnit (w x i) * V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ]) =
        (((expUnit (shiftChart w dw x i) : UnitQuaternion) : ℍ[ℝ]) - ((expUnit (w x i) : UnitQuaternion) : ℍ[ℝ])) *
          ((V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ]) := by
      rw [sub_mul]
      rfl
    rw [e1, norm_mul, norm_coe_unitQuaternion, mul_one]
    exact hw
  · simpa using hm0
  · exact hw
theorem isSmallCurvature_shiftChart (hexp : ExpUnitLipschitzInjective) (hhol : PathHolonomyLipschitz)
    {w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top} {s m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ x i, ‖dw x i‖ ≤ m)
    (hw : IsSmallCurvature s (chartedField w V)) : IsSmallCurvature (s + 4 * m) (chartedField (shiftChart w dw) V) := by
  intro p hp
  have h0 := hw p hp
  have h1 := hhol F F.depth _ _ m (norm_chartedField_sub_le hexp w dw V hm0 hm) p.1
    [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)]
  unfold plaquetteDefect plaquetteHolonomy at h0 ⊢
  have h3 := norm_sub_le_norm_sub_add_norm_sub
    (((pathHolonomy (chartedField (shiftChart w dw) V) p.1
      [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion)) : ℍ[ℝ])
    (((pathHolonomy (chartedField w V) p.1
      [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion)) : ℍ[ℝ]) 1
  simp only [List.length_cons, List.length_nil] at h1
  push_cast at h1
  linarith
end
section
variable {F F' : BlockFrame}
structure SlopeControl (a δ₁ C2 C3 m : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) :
    Prop where
  analytic : ∀ dw : F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ x i, ‖dw x i‖ ≤ m) →
    AnalyticAt ℝ (energyNear a (shiftChart w dw) V) 0
  secondKernel : ∀ dw : F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ x i, ‖dw x i‖ ≤ m) →
    ∀ q' : Fin 2 → ChartDirection F, (∀ j, ‖directionVector (q' j)‖ = 1) →
      |chartMixedDeriv a (shiftChart w dw) V q'| ≤ C2 * Real.exp (-(δ₁ * directionDiameter q'))
  thirdKernel : ∀ dw : F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ x i, ‖dw x i‖ ≤ m) →
    ∀ q' : Fin 3 → ChartDirection F, (∀ j, ‖directionVector (q' j)‖ = 1) →
      |chartMixedDeriv a (shiftChart w dw) V q'| ≤ C3 * Real.exp (-(δ₁ * directionDiameter q'))
theorem weightedNorm_smul {N : ℕ} (wt : Fin N → ℝ) (c : ℝ) (x : Fin N → ℝ) :
    _root_.YangMills.Construction.Calculus.weightedNorm wt (c • x) = |c| * _root_.YangMills.Construction.Calculus.weightedNorm wt x := by apply _root_.YangMills.Construction.Calculus.weightedNorm_smul <;> assumption
theorem weightedNorm_add_le {N : ℕ} {wt : Fin N → ℝ} (hw : ∀ n, 0 ≤ wt n) (x y : Fin N → ℝ) :
    _root_.YangMills.Construction.Calculus.weightedNorm wt (x + y) ≤ _root_.YangMills.Construction.Calculus.weightedNorm wt x + _root_.YangMills.Construction.Calculus.weightedNorm wt y := by apply _root_.YangMills.Construction.Calculus.weightedNorm_add_le <;> assumption
theorem weightedNorm_sum_le {N : ℕ} {wt : Fin N → ℝ} (hw : ∀ n, 0 ≤ wt n) {ι : Type} (s : Finset ι)
    (f : ι → Fin N → ℝ) : _root_.YangMills.Construction.Calculus.weightedNorm wt (∑ q ∈ s, f q) ≤ ∑ q ∈ s, _root_.YangMills.Construction.Calculus.weightedNorm wt (f q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [_root_.YangMills.Construction.Calculus.weightedNorm]
  | insert q s hq ih =>
    simp only [Finset.sum_insert hq]
    exact (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.weightedNorm_add_le hw _ _).trans (add_le_add le_rfl ih)
theorem weightedNorm_bondBumpCoords_le (β : ℝ) (Z : F.Cell) (b : F.Site F.depth × Fin 4)
    (hb : b ∈ chordBonds (finiteCells F)) (e : imaginaryQuaternions) :
    _root_.YangMills.Construction.Calculus.weightedNorm (cellWeight β Z) (bondBumpCoords b e) ≤
      3 * ‖e‖ * Real.exp (-(β * cellSupDist (enclosingCell b.1) Z)) := by
  classical
  have h := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.weightedNorm_chartOffset_le (F := F) (fun z => Real.exp (-(β * cellSupDist z Z)))
    (fun _ => (Real.exp_pos _).le) (bondBump b e)
  have e1 : ∑ c : ↥(chordBonds (finiteCells F)),
      ‖bondBump b e c.1.1 c.1.2‖ * Real.exp (-(β * cellSupDist (enclosingCell c.1.1) Z)) =
      ‖e‖ * Real.exp (-(β * cellSupDist (enclosingCell b.1) Z)) := by
    rw [Finset.sum_eq_single (⟨b, hb⟩ : ↥(chordBonds (finiteCells F)))]
    · simp [bondBump]
    · intro c _ hc
      have hne : (c.1.1, c.1.2) ≠ b := fun h => hc (Subtype.ext h)
      simp [bondBump, hne]
    · simp
  rw [e1] at h
  have e2 : cellWeight β Z = fun n => (fun z => Real.exp (-(β * cellSupDist z Z))) (directionCell (chartDirections F n)) :=
    rfl
  rw [e2, mul_assoc]
  exact h
theorem exp_neg_mul_natCast_le_one {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) : Real.exp (-(β * n)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have : (0 : ℝ) ≤ β * n := by positivity
  linarith
def bondBumps {ι : Type} [Fintype ι] (j : ι → ↥(chordBonds (finiteCells F))) (c : ι → imaginaryQuaternions) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => ∑ q, bondBump (j q).1 (c q) x i
theorem chartOffset_bondBumps {ι : Type} [Fintype ι] (j : ι → ↥(chordBonds (finiteCells F)))
    (c : ι → imaginaryQuaternions) :
    chartOffset (bondBumps j c) = ∑ q, bondBumpCoords (j q).1 (c q) := by
  unfold bondBumps bondBumpCoords
  exact chartOffset_sum Finset.univ fun q => bondBump (j q).1 (c q)
theorem bondBumps_apply_self {ι : Type} [Fintype ι] {j : ι → ↥(chordBonds (finiteCells F))}
    (hj : Function.Injective j) (c : ι → imaginaryQuaternions) (q : ι) :
    bondBumps j c (j q).1.1 (j q).1.2 = c q := by
  classical
  unfold bondBumps
  rw [Finset.sum_eq_single q]
  · simp [bondBump]
  · intro q' _ hq
    have : ((j q).1.1, (j q).1.2) ≠ (j q').1 := fun h => hq (hj (Subtype.ext (by simpa using h.symm)))
    simp [bondBump, this]
  · simp
theorem bondBumps_apply_of_ne {ι : Type} [Fintype ι] {j : ι → ↥(chordBonds (finiteCells F))}
    (c : ι → imaginaryQuaternions)
    {x : F.Site F.depth} {i : Fin 4} (h : ∀ q, (x, i) ≠ (j q).1) : bondBumps j c x i = 0 := by
  classical
  unfold bondBumps
  refine Finset.sum_eq_zero fun q _ => ?_
  simp [bondBump, h q]
theorem norm_bondBumps_le {ι : Type} [Fintype ι] {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j)
    {c : ι → imaginaryQuaternions} {m : ℝ} (hm0 : 0 ≤ m) (hc : ∀ q, ‖c q‖ ≤ m) (x : F.Site F.depth) (i : Fin 4) :
    ‖bondBumps j c x i‖ ≤ m := by
  by_cases h : ∃ q, (x, i) = (j q).1
  · obtain ⟨q, hq⟩ := h
    have e1 : x = (j q).1.1 := congrArg Prod.fst hq
    have e2 : i = (j q).1.2 := congrArg Prod.snd hq
    rw [e1, e2, bondBumps_apply_self hj]
    exact hc q
  · rw [bondBumps_apply_of_ne c (fun q hq => h ⟨q, hq⟩), norm_zero]
    exact hm0
theorem norm_bondBump_le (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) (x : F.Site F.depth) (i : Fin 4) :
    ‖bondBump b e x i‖ ≤ ‖e‖ := by
  unfold bondBump
  split_ifs
  · exact le_rfl
  · simp
section Core
variable (hCE : ChartedEnergyInCoordinates)
include hCE
abbrev slopeFunction (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) :
    (Fin (chartDimension F) → ℝ) → ℝ :=
  fun σ => fderiv ℝ (energyNear a w V) σ (bondBumpCoords b e)
theorem slopeFunction_analyticAt {a δ₁ C2 C3 m : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top}
    (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hS : SlopeControl a δ₁ C2 C3 m w V)
    {dw : F.Site F.depth → Fin 4 → imaginaryQuaternions} (hdw : ∀ x i, ‖dw x i‖ ≤ m) (b : F.Site F.depth × Fin 4)
    (e : imaginaryQuaternions) :
    AnalyticAt ℝ (slopeFunction a w V b e) (chartOffset dw) :=
  analyticAt_fderiv_apply (energyNear_analyticAt hCE hL hs a w dw V (hS.analytic dw hdw)) _
theorem chartedSlope_eq_slopeFunction {a δ₁ C2 C3 m : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top}
    (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hS : SlopeControl a δ₁ C2 C3 m w V)
    {dw : F.Site F.depth → Fin 4 → imaginaryQuaternions} (hdw : ∀ x i, ‖dw x i‖ ≤ m) (b : F.Site F.depth × Fin 4)
    (e : imaginaryQuaternions) :
    chartedSlope a (shiftChart w dw) V b e = slopeFunction a w V b e (chartOffset dw) :=
  chartedSlope_eq_fderiv hCE hL hs a w dw V b e
    (energyNear_analyticAt hCE hL hs a w dw V (hS.analytic dw hdw)).differentiableAt
theorem abs_second_deriv_slopeFunction_le {a δ₁ C2 C3 m : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top}
    (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hS : SlopeControl a δ₁ C2 C3 m w V) (hδ₁ : 0 ≤ δ₁)
    (hC3 : 0 ≤ C3)
    {dw : F.Site F.depth → Fin 4 → imaginaryQuaternions} (hdw : ∀ x i, ‖dw x i‖ ≤ m) {b b₂ : F.Site F.depth × Fin 4}
    (hb : b ∈ chordBonds (finiteCells F)) (hb₂ : b₂ ∈ chordBonds (finiteCells F)) (e e₂ : imaginaryQuaternions)
    (he₂ : ‖e₂‖ = 1) :
    |iteratedFDeriv ℝ 2 (slopeFunction a w V b e) (chartOffset dw) ![bondBumpCoords b₂ e₂, bondBumpCoords b₂ e₂]| ≤
      27 * C3 * ‖e‖ := by
  have h := abs_iteratedFDeriv_two_slope_le hCE hL hs a w dw V b hb e δ₁ hδ₁ C3 hC3 (hS.analytic dw hdw)
    (hS.thirdKernel dw hdw) (bondBumpCoords b₂ e₂) (bondBumpCoords b₂ e₂)
  have h1 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.weightedNorm_bondBumpCoords_le (δ₁ / 2) (enclosingCell b.1) b₂ hb₂ e₂
  have h2 : Real.exp (-(δ₁ / 2 * cellSupDist (enclosingCell b₂.1) (enclosingCell b.1))) ≤ 1 :=
    exp_neg_mul_natCast_le_one (by positivity) _
  have h3 : _root_.YangMills.Construction.Calculus.weightedNorm (cellWeight (δ₁ / 2) (enclosingCell b.1)) (bondBumpCoords b₂ e₂) ≤ 3 := by
    rw [he₂, mul_one] at h1
    nlinarith
  have h4 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.weightedNorm_nonneg (cellWeight_nonneg (δ₁ / 2) (enclosingCell b.1)) (bondBumpCoords b₂ e₂)
  have h5 : 0 ≤ 3 * C3 * ‖e‖ := by positivity
  refine h.trans ?_
  have h6 : _root_.YangMills.Construction.Calculus.weightedNorm (cellWeight (δ₁ / 2) (enclosingCell b.1)) (bondBumpCoords b₂ e₂) *
      _root_.YangMills.Construction.Calculus.weightedNorm (cellWeight (δ₁ / 2) (enclosingCell b.1)) (bondBumpCoords b₂ e₂) ≤ 9 := by nlinarith
  nlinarith
theorem abs_fderiv_slopeFunction_le {a δ₁ C2 C3 m : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top}
    (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hS : SlopeControl a δ₁ C2 C3 m w V) (hδ₁ : 0 ≤ δ₁)
    (hC2 : 0 ≤ C2)
    {dw : F.Site F.depth → Fin 4 → imaginaryQuaternions} (hdw : ∀ x i, ‖dw x i‖ ≤ m) {b b₂ : F.Site F.depth × Fin 4}
    (hb : b ∈ chordBonds (finiteCells F)) (hb₂ : b₂ ∈ chordBonds (finiteCells F)) (e e₂ : imaginaryQuaternions)
    (he₂ : ‖e₂‖ = 1) :
    |fderiv ℝ (slopeFunction a w V b e) (chartOffset dw) (bondBumpCoords b₂ e₂)| ≤
      9 * C2 * ‖e‖ * Real.exp (-(δ₁ * cellSupDist (enclosingCell b₂.1) (enclosingCell b.1))) := by
  have h := abs_fderiv_slope_le hCE hL hs a w dw V b hb e δ₁ hδ₁ C2 hC2 (hS.analytic dw hdw) (hS.secondKernel dw hdw)
    (bondBumpCoords b₂ e₂)
  have h1 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.weightedNorm_bondBumpCoords_le δ₁ (enclosingCell b.1) b₂ hb₂ e₂
  rw [he₂, mul_one] at h1
  have h5 : 0 ≤ 3 * C2 * ‖e‖ := by positivity
  calc _ ≤ _ := h
    _ ≤ (3 * C2 * ‖e‖) * (3 * Real.exp (-(δ₁ * cellSupDist (enclosingCell b₂.1) (enclosingCell b.1)))) :=
        mul_le_mul_of_nonneg_left h1 h5
    _ = _ := by ring
end Core
end
section
variable {F F' : BlockFrame}
theorem abs_fderiv_slopeFunction_sub_le (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    (hL' : Odd F'.blockSide) (hs' : ∀ i, 2 ≤ F'.extent i) {a δ₁ C2 C3 m M τ : ℝ}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions} {V' : F'.GaugeField F'.top}
    (hS : SlopeControl a δ₁ C2 C3 m w V) (hS' : SlopeControl a δ₁ C2 C3 m w' V') (hδ₁ : 0 ≤ δ₁) (hC2 : 0 ≤ C2)
    (hC3 : 0 ≤ C3)
    (hτ : 0 < τ) {b b₂ : F.Site F.depth × Fin 4} {b' b₂' : F'.Site F'.depth × Fin 4}
    (hb : b ∈ chordBonds (finiteCells F)) (hb₂ : b₂ ∈ chordBonds (finiteCells F))
    (hb' : b' ∈ chordBonds (finiteCells F')) (hb₂' : b₂' ∈ chordBonds (finiteCells F'))
    (hdist : cellSupDist (enclosingCell b₂'.1) (enclosingCell b'.1) = cellSupDist (enclosingCell b₂.1) (enclosingCell b.1))
    (e e₂ : imaginaryQuaternions) {dw : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {dw' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    (hdw : ∀ s ∈ Set.Icc (0 : ℝ) τ, ∀ x i, ‖dw x i + s • bondBump b₂ e₂ x i‖ ≤ m)
    (hdw' : ∀ s ∈ Set.Icc (0 : ℝ) τ, ∀ x i, ‖dw' x i + s • bondBump b₂' e₂ x i‖ ≤ m)
    (he₂ : ‖e₂‖ = 1)
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) τ,
      |chartedSlope a (shiftChart w fun x i => dw x i + s • bondBump b₂ e₂ x i) V b e -
        chartedSlope a (shiftChart w' fun x i => dw' x i + s • bondBump b₂' e₂ x i) V' b' e| ≤ M) :
    |fderiv ℝ (slopeFunction a w V b e) (chartOffset dw) (bondBumpCoords b₂ e₂) -
        fderiv ℝ (slopeFunction a w' V' b' e) (chartOffset dw') (bondBumpCoords b₂' e₂)| ≤
      min (2 * M / τ + 2 * (27 * C3 * ‖e‖) * τ)
        (18 * C2 * ‖e‖ * Real.exp (-(δ₁ * cellSupDist (enclosingCell b₂.1) (enclosingCell b.1)))) := by
  have e1 : ∀ s : ℝ, chartOffset dw + s • bondBumpCoords b₂ e₂ =
      chartOffset fun x i => dw x i + s • bondBump b₂ e₂ x i := fun s =>
    (chartOffset_add _ _ s).symm
  have e1' : ∀ s : ℝ, chartOffset dw' + s • bondBumpCoords b₂' e₂ =
      chartOffset fun x i => dw' x i + s • bondBump b₂' e₂ x i := fun s =>
    (chartOffset_add _ _ s).symm
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) τ := ⟨le_rfl, hτ.le⟩
  have hz : ∀ x i, ‖dw x i‖ ≤ m := fun x i => by simpa using hdw 0 h0 x i
  have hz' : ∀ x i, ‖dw' x i‖ ≤ m := fun x i => by simpa using hdw' 0 h0 x i
  refine le_min ?_ ?_
  · refine abs_fderiv_sub_le_of_two_lines hτ (fun s hs₁ => ?_) (fun s hs₁ => ?_) (fun s hs₁ => ?_)
      (fun s hs₁ => ?_) (fun s hs₁ => ?_)
    · rw [e1]
      exact slopeFunction_analyticAt hCE hL hs hS (hdw s hs₁) b e
    · rw [e1']
      exact slopeFunction_analyticAt hCE hL' hs' hS' (hdw' s hs₁) b' e
    · rw [e1, e1', ← chartedSlope_eq_slopeFunction hCE hL hs hS (hdw s hs₁),
        ← chartedSlope_eq_slopeFunction hCE hL' hs' hS' (hdw' s hs₁)]
      exact hM s hs₁
    · rw [e1]
      exact abs_second_deriv_slopeFunction_le hCE hL hs hS hδ₁ hC3 (hdw s hs₁) hb hb₂ e e₂ he₂
    · rw [e1']
      exact abs_second_deriv_slopeFunction_le hCE hL' hs' hS' hδ₁ hC3 (hdw' s hs₁) hb' hb₂' e e₂ he₂
  · have h1 := abs_fderiv_slopeFunction_le hCE hL hs hS hδ₁ hC2 hz hb hb₂ e e₂ he₂
    have h2 := abs_fderiv_slopeFunction_le hCE hL' hs' hS' hδ₁ hC2 hz' hb' hb₂' e e₂ he₂
    rw [hdist] at h2
    have h3 := abs_sub (fderiv ℝ (slopeFunction a w V b e) (chartOffset dw) (bondBumpCoords b₂ e₂))
      (fderiv ℝ (slopeFunction a w' V' b' e) (chartOffset dw') (bondBumpCoords b₂' e₂))
    linarith
theorem abs_fderiv_slopeFunction_sub_le_smul (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    (hL' : Odd F'.blockSide) (hs' : ∀ i, 2 ≤ F'.extent i) {a δ₁ C2 C3 m M τ : ℝ}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions} {V' : F'.GaugeField F'.top}
    (hS : SlopeControl a δ₁ C2 C3 m w V) (hS' : SlopeControl a δ₁ C2 C3 m w' V') (hδ₁ : 0 ≤ δ₁) (hC2 : 0 ≤ C2)
    (hC3 : 0 ≤ C3)
    (hτ : 0 < τ) {b b₂ : F.Site F.depth × Fin 4} {b' b₂' : F'.Site F'.depth × Fin 4}
    (hb : b ∈ chordBonds (finiteCells F)) (hb₂ : b₂ ∈ chordBonds (finiteCells F))
    (hb' : b' ∈ chordBonds (finiteCells F')) (hb₂' : b₂' ∈ chordBonds (finiteCells F'))
    (hdist : cellSupDist (enclosingCell b₂'.1) (enclosingCell b'.1) = cellSupDist (enclosingCell b₂.1) (enclosingCell b.1))
    (e c : imaginaryQuaternions) {dw : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {dw' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    (hdw : ∀ e₂ : imaginaryQuaternions, ‖e₂‖ = 1 → ∀ s ∈ Set.Icc (0 : ℝ) τ, ∀ x i,
      ‖dw x i + s • bondBump b₂ e₂ x i‖ ≤ m)
    (hdw' : ∀ e₂ : imaginaryQuaternions, ‖e₂‖ = 1 → ∀ s ∈ Set.Icc (0 : ℝ) τ, ∀ x i,
      ‖dw' x i + s • bondBump b₂' e₂ x i‖ ≤ m)
    (hM : ∀ e₂ : imaginaryQuaternions, ‖e₂‖ = 1 → ∀ s ∈ Set.Icc (0 : ℝ) τ,
      |chartedSlope a (shiftChart w fun x i => dw x i + s • bondBump b₂ e₂ x i) V b e -
        chartedSlope a (shiftChart w' fun x i => dw' x i + s • bondBump b₂' e₂ x i) V' b' e| ≤ M) :
    |fderiv ℝ (slopeFunction a w V b e) (chartOffset dw) (bondBumpCoords b₂ c) -
        fderiv ℝ (slopeFunction a w' V' b' e) (chartOffset dw') (bondBumpCoords b₂' c)| ≤
      ‖c‖ * min (2 * M / τ + 2 * (27 * C3 * ‖e‖) * τ)
        (18 * C2 * ‖e‖ * Real.exp (-(δ₁ * cellSupDist (enclosingCell b₂.1) (enclosingCell b.1)))) := by
  by_cases hc : c = 0
  · have e0 : (0 : imaginaryQuaternions) = (0 : ℝ) • (0 : imaginaryQuaternions) := by simp
    subst hc
    rw [e0, bondBumpCoords_smul, bondBumpCoords_smul]
    simp
  · have hn : ‖c‖ ≠ 0 := by simpa using hc
    obtain ⟨u, hu⟩ : ∃ u : imaginaryQuaternions, u = ‖c‖⁻¹ • c := ⟨_, rfl⟩
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hcu : c = ‖c‖ • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have h := abs_fderiv_slopeFunction_sub_le hCE hL hs hL' hs' hS hS' hδ₁ hC2 hC3 hτ hb hb₂ hb' hb₂' hdist e u
      (hdw u hu1) (hdw' u hu1) hu1 (hM u hu1)
    have e2 : fderiv ℝ (slopeFunction a w V b e) (chartOffset dw) (bondBumpCoords b₂ c) -
        fderiv ℝ (slopeFunction a w' V' b' e) (chartOffset dw') (bondBumpCoords b₂' c) =
        ‖c‖ * (fderiv ℝ (slopeFunction a w V b e) (chartOffset dw) (bondBumpCoords b₂ u) -
          fderiv ℝ (slopeFunction a w' V' b' e) (chartOffset dw') (bondBumpCoords b₂' u)) := by
      conv_lhs => rw [hcu, bondBumpCoords_smul, bondBumpCoords_smul]
      simp only [map_smul, smul_eq_mul]
      ring
    rw [e2, abs_mul, abs_of_nonneg (norm_nonneg c)]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg c)
theorem abs_slope_difference_sub_le (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    (hL' : Odd F'.blockSide) (hs' : ∀ i, 2 ≤ F'.extent i) {a δ₁ C2 C3 m M τ D P : ℝ}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions} {V' : F'.GaugeField F'.top}
    (hS : SlopeControl a δ₁ C2 C3 m w V) (hS' : SlopeControl a δ₁ C2 C3 m w' V') (hδ₁ : 0 ≤ δ₁) (hC2 : 0 ≤ C2)
    (hC3 : 0 ≤ C3)
    (hτ : 0 < τ) {ι : Type} [Fintype ι]
    {j : ι → ↥(chordBonds (finiteCells F))} {j' : ι → ↥(chordBonds (finiteCells F'))}
    (hj : Function.Injective j) (hj' : Function.Injective j') (c : ι → imaginaryQuaternions)
    (del : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (hD : ∀ x i, ‖del x i‖ ≤ D) (hP0 : 0 ≤ P) (hP : ∀ q, ‖c q‖ ≤ P) (hm : D + P + τ ≤ m) (hD0 : 0 ≤ D)
    {b : F.Site F.depth × Fin 4} {b' : F'.Site F'.depth × Fin 4}
    (hb : b ∈ chordBonds (finiteCells F)) (hb' : b' ∈ chordBonds (finiteCells F'))
    (hdist : ∀ q, cellSupDist (enclosingCell (j' q).1.1) (enclosingCell b'.1) =
      cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1))
    (e : imaginaryQuaternions)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ q, ∀ e₂ : imaginaryQuaternions, ‖e₂‖ = 1 → ∀ s ∈ Set.Icc (0 : ℝ) τ,
      |chartedSlope a (shiftChart w fun x i => (del x i + t • bondBumps j c x i) + s • bondBump (j q).1 e₂ x i) V b e -
        chartedSlope a (shiftChart w' fun x i => ((0 : imaginaryQuaternions) + t • bondBumps j' c x i) +
          s • bondBump (j' q).1 e₂ x i) V' b' e| ≤ M)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |(chartedSlope a (shiftChart w fun x i => u • bondBumps j c x i) V b e -
        chartedSlope a (shiftChart w' fun x i => u • bondBumps j' c x i) V' b' e) -
      (chartedSlope a (shiftChart w fun _ _ => 0) V b e - chartedSlope a (shiftChart w' fun _ _ => 0) V' b' e)| ≤
      (3 * C3 * ‖e‖) * (_root_.YangMills.Construction.Calculus.weightedNorm (cellWeight (δ₁ / 2) (enclosingCell b.1)) (chartOffset (bondBumps j c)) *
          _root_.YangMills.Construction.Calculus.weightedNorm (cellWeight (δ₁ / 2) (enclosingCell b.1)) (chartOffset del)) +
        ∑ q, ‖c q‖ * min (2 * M / τ + 2 * (27 * C3 * ‖e‖) * τ)
          (18 * C2 * ‖e‖ * Real.exp (-(δ₁ * cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1)))) := by
  have hτ0 := hτ.le
  have hu0 := hu.1
  have hu1 := hu.2
  obtain ⟨g, hg⟩ : ∃ g, g = slopeFunction a w V b e := ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g', g' = slopeFunction a w' V' b' e := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = chartOffset (bondBumps j c) := ⟨_, rfl⟩
  obtain ⟨n', hn'⟩ : ∃ n', n' = chartOffset (bondBumps j' c) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = chartOffset del := ⟨_, rfl⟩
  have hB : ∀ x i, ‖bondBumps j c x i‖ ≤ P := norm_bondBumps_le hj hP0 hP
  have hB' : ∀ x i, ‖bondBumps j' c x i‖ ≤ P := norm_bondBumps_le hj' hP0 hP
  have hsm : ∀ (θ t : ℝ), |θ| ≤ 1 → |t| ≤ 1 → ∀ x i, ‖θ • del x i + t • bondBumps j c x i‖ ≤ D + P := by
    intro θ t hθ ht x i
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul hθ (hD x i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul ht (hB x i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hsm' : ∀ t : ℝ, |t| ≤ 1 → ∀ x i, ‖t • bondBumps j' c x i‖ ≤ P := by
    intro t ht x i
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul ht (hB' x i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hτm : 0 ≤ τ := hτ0
  have hDPm : D + P ≤ m := by linarith
  have hPm : P ≤ m := by linarith
  have hDm : D ≤ m := by linarith
  have hmix : |g (d + u • n) - g (u • n) - g d + g 0| ≤
      (3 * C3 * ‖e‖) * (_root_.YangMills.Construction.Calculus.weightedNorm (cellWeight (δ₁ / 2) (enclosingCell b.1)) (chartOffset (bondBumps j c)) *
          _root_.YangMills.Construction.Calculus.weightedNorm (cellWeight (δ₁ / 2) (enclosingCell b.1)) (chartOffset del)) := by
    have epoint : ∀ θ t : ℝ, θ • d + t • (u • n) =
        chartOffset fun x i => θ • del x i + (t * u) • bondBumps j c x i := by
      intro θ t
      have h1 := chartOffset_add (fun x i => θ • del x i) (bondBumps j c) (t * u)
      rw [h1, chartOffset_smul, hd, hn, mul_smul]
    refine abs_mixed_difference_le (fun θ hθ t ht => ?_) (fun θ hθ t ht => ?_)
    · rw [epoint, hg]
      refine slopeFunction_analyticAt hCE hL hs hS (fun x i => ?_) b e
      refine (hsm θ (t * u) ?_ ?_ x i).trans hDPm
      · rw [abs_of_nonneg hθ.1]
        exact hθ.2
      · rw [abs_of_nonneg (mul_nonneg ht.1 hu0)]
        exact mul_le_one₀ ht.2 hu0 hu1
    · rw [epoint, hg]
      have hsmall : ∀ x i, ‖θ • del x i + (t * u) • bondBumps j c x i‖ ≤ m := fun x i => by
        refine (hsm θ (t * u) ?_ ?_ x i).trans hDPm
        · rw [abs_of_nonneg hθ.1]
          exact hθ.2
        · rw [abs_of_nonneg (mul_nonneg ht.1 hu0)]
          exact mul_le_one₀ ht.2 hu0 hu1
      have h := abs_iteratedFDeriv_two_slope_le hCE hL hs a w _ V b hb e δ₁ hδ₁ C3 hC3 (hS.analytic _ hsmall)
        (hS.thirdKernel _ hsmall) (u • n) d
      refine h.trans ?_
      rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.weightedNorm_smul, abs_of_nonneg hu0, hn, hd]
      have h4 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.weightedNorm_nonneg (cellWeight_nonneg (δ₁ / 2) (enclosingCell b.1)) (chartOffset (bondBumps j c))
      have h5 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.weightedNorm_nonneg (cellWeight_nonneg (δ₁ / 2) (enclosingCell b.1)) (chartOffset del)
      have h6 : 0 ≤ 3 * C3 * ‖e‖ := by positivity
      refine mul_le_mul_of_nonneg_left ?_ h6
      refine mul_le_mul_of_nonneg_right ?_ h5
      exact mul_le_of_le_one_left h4 hu1
  obtain ⟨Bd, hBd⟩ : ∃ Bd, Bd = ∑ q, ‖c q‖ * min (2 * M / τ + 2 * (27 * C3 * ‖e‖) * τ)
      (18 * C2 * ‖e‖ * Real.exp (-(δ₁ * cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1)))) := ⟨_, rfl⟩
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |fderiv ℝ g (d + t • n) n - fderiv ℝ g' ((0 : Fin (chartDimension F') → ℝ) + t • n') n'| ≤ Bd := by
    intro t ht
    have ept : d + t • n = chartOffset fun x i => del x i + t • bondBumps j c x i := by
      rw [hd, hn]
      exact (chartOffset_add _ _ t).symm
    have ept' : (0 : Fin (chartDimension F') → ℝ) + t • n' =
        chartOffset fun x i => (0 : imaginaryQuaternions) + t • bondBumps j' c x i := by
      rw [hn', ← chartOffset_zero]
      exact (chartOffset_add _ _ t).symm
    have en : n = ∑ q, bondBumpCoords (j q).1 (c q) := hn.trans (chartOffset_bondBumps j c)
    have en' : n' = ∑ q, bondBumpCoords (j' q).1 (c q) := hn'.trans (chartOffset_bondBumps j' c)
    obtain ⟨z, hz⟩ : ∃ z, z = d + t • n := ⟨_, rfl⟩
    obtain ⟨z', hz'⟩ : ∃ z', z' = (0 : Fin (chartDimension F') → ℝ) + t • n' := ⟨_, rfl⟩
    rw [← hz, ← hz']
    have es : fderiv ℝ g z n - fderiv ℝ g' z' n' =
        ∑ q, (fderiv ℝ g z (bondBumpCoords (j q).1 (c q)) - fderiv ℝ g' z' (bondBumpCoords (j' q).1 (c q))) := by
      rw [en, en', map_sum, map_sum, Finset.sum_sub_distrib]
    rw [es, hBd]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [hz, hz', ept, ept', hg, hg']
    have hbase : ∀ x i, ‖del x i + t • bondBumps j c x i‖ ≤ D + P := fun x i => by
      have := hsm 1 t (by simp) (by rw [abs_of_nonneg ht.1]; exact ht.2) x i
      simpa using this
    have hbase' : ∀ x i, ‖(0 : imaginaryQuaternions) + t • bondBumps j' c x i‖ ≤ P := fun x i => by
      have := hsm' t (by rw [abs_of_nonneg ht.1]; exact ht.2) x i
      simpa using this
    have hstep : ∀ (b₂ : F.Site F.depth × Fin 4) (e₂ : imaginaryQuaternions), ‖e₂‖ = 1 →
        ∀ s ∈ Set.Icc (0 : ℝ) τ, ∀ x i, ‖s • bondBump b₂ e₂ x i‖ ≤ τ := by
      intro b₂ e₂ he₂ s hs₁ x i
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs₁.1]
      have h1 := norm_bondBump_le b₂ e₂ x i
      rw [he₂] at h1
      exact (mul_le_mul hs₁.2 h1 (norm_nonneg _) hτ0).trans_eq (mul_one _)
    have hstep' : ∀ (b₂ : F'.Site F'.depth × Fin 4) (e₂ : imaginaryQuaternions), ‖e₂‖ = 1 →
        ∀ s ∈ Set.Icc (0 : ℝ) τ, ∀ x i, ‖s • bondBump b₂ e₂ x i‖ ≤ τ := by
      intro b₂ e₂ he₂ s hs₁ x i
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs₁.1]
      have h1 := norm_bondBump_le b₂ e₂ x i
      rw [he₂] at h1
      exact (mul_le_mul hs₁.2 h1 (norm_nonneg _) hτ0).trans_eq (mul_one _)
    exact abs_fderiv_slopeFunction_sub_le_smul hCE hL hs hL' hs' hS hS' hδ₁ hC2 hC3 hτ hb (j q).2 hb' (j' q).2
      (hdist q) e (c q)
      (fun e₂ he₂ s hs₁ x i => (norm_add_le _ _).trans (by
        have h1 := hbase x i
        have h2 := hstep (j q).1 e₂ he₂ s hs₁ x i
        linarith))
      (fun e₂ he₂ s hs₁ x i => (norm_add_le _ _).trans (by
        have h1 := hbase' x i
        have h2 := hstep' (j' q).1 e₂ he₂ s hs₁ x i
        linarith))
      (fun e₂ he₂ s hs₁ => hM t ht q e₂ he₂ s hs₁)
  have hBd0 : 0 ≤ Bd := (abs_nonneg _).trans (hseg 0 ⟨le_rfl, zero_le_one⟩)
  have hJ := abs_sub_le_mul_of_hasDerivAt
    (f := fun t : ℝ => g (d + t • n) - g' ((0 : Fin (chartDimension F') → ℝ) + t • n'))
    (f' := fun t => fderiv ℝ g (d + t • n) n - fderiv ℝ g' ((0 : Fin (chartDimension F') → ℝ) + t • n') n')
    (M := Bd) (τ := u) hu0
    (fun t ht => by
      have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hu1⟩
      have ha : |t| ≤ 1 := by rw [abs_of_nonneg ht1.1]; exact ht1.2
      have ept : d + t • n = chartOffset fun x i => del x i + t • bondBumps j c x i := by
        rw [hd, hn]
        exact (chartOffset_add _ _ t).symm
      have ept' : (0 : Fin (chartDimension F') → ℝ) + t • n' =
          chartOffset fun x i => (0 : imaginaryQuaternions) + t • bondBumps j' c x i := by
        rw [hn', ← chartOffset_zero]
        exact (chartOffset_add _ _ t).symm
      have h1 : DifferentiableAt ℝ g (d + t • n) := by
        rw [ept, hg]
        refine (slopeFunction_analyticAt hCE hL hs hS (fun x i => ?_) b e).differentiableAt
        have := hsm 1 t (by simp) ha x i
        simp only [one_smul] at this
        exact this.trans hDPm
      have h2 : DifferentiableAt ℝ g' ((0 : Fin (chartDimension F') → ℝ) + t • n') := by
        rw [ept', hg']
        refine (slopeFunction_analyticAt hCE hL' hs' hS' (fun x i => ?_) b' e).differentiableAt
        have := hsm' t ha x i
        simp only [zero_add]
        exact this.trans hPm
      exact (hasDerivAt_along_line h1).fun_sub (hasDerivAt_along_line h2))
    (fun t ht => hseg t ⟨ht.1, ht.2.trans hu1⟩)
  simp only [zero_smul, add_zero, zero_add] at hJ
  have hJ2 : Bd * u ≤ Bd := mul_le_of_le_one_right hBd0 hu1
  have hu' : |u| ≤ 1 := by rw [abs_of_nonneg hu0]; exact hu1
  have e1 : chartedSlope a (shiftChart w fun x i => u • bondBumps j c x i) V b e = g (u • n) := by
    rw [chartedSlope_eq_slopeFunction hCE hL hs hS (fun x i => ?_) b e, hg, hn, chartOffset_smul]
    have := hsm 0 u (by simp) hu' x i
    simp only [zero_smul, zero_add] at this
    exact this.trans hDPm
  have e2 : chartedSlope a (shiftChart w' fun x i => u • bondBumps j' c x i) V' b' e = g' (u • n') := by
    rw [chartedSlope_eq_slopeFunction hCE hL' hs' hS' (fun x i => ?_) b' e, hg', hn', chartOffset_smul]
    exact (hsm' u hu' x i).trans hPm
  have hm0 : 0 ≤ m := by linarith
  have e3 : chartedSlope a (shiftChart w fun _ _ => 0) V b e = g 0 := by
    rw [chartedSlope_eq_slopeFunction hCE hL hs hS (fun x i => by simpa using hm0) b e, hg, chartOffset_zero]
  have e4 : chartedSlope a (shiftChart w' fun _ _ => 0) V' b' e = g' 0 := by
    rw [chartedSlope_eq_slopeFunction hCE hL' hs' hS' (fun x i => by simpa using hm0) b' e, hg', chartOffset_zero]
  rw [e1, e2, e3, e4, ← hBd]
  have h1 := abs_le.mp hmix
  have h2 := abs_le.mp hJ
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
end
end ColdStepAtMirrorFrames.ChartSlopes
end YangMills.Construction
end
