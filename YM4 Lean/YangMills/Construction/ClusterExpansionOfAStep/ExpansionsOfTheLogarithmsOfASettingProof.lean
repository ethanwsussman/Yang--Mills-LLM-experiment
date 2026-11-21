import YangMills.Construction.ClusterExpansionOfAStep.DensitiesInCoordinatesForm
import YangMills.Construction.ClusterExpansionOfAStep.DerivativesOfTheMeanOfABond
import YangMills.Construction.ClusterExpansionOfAStep.ExpansionsOfTheLogarithmsOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.GroupGapIsSmoothForm
import YangMills.Construction.ClusterExpansionOfAStep.LogOfTheHaarDensityIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames BondMeans TorusFields TorusLumps TorusContours
  TopLevelSites TorusCounting StepSettings StepCosts LineCalculus RenormalizationStepParameters HaarDensity
namespace ClusterExpansionOfAStep
namespace LogJacobianBounds
def gapOfNorm (A : ℝ) (z : ℍ[ℝ]) : ℝ := logPartitionGap (A * ‖z‖)
theorem isCompact_unitShell : IsCompact {z : ℍ[ℝ] | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1} := by
  refine (isCompact_closedBall (0 : ℍ[ℝ]) 1).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  · intro z hz
    simpa using hz.2
theorem exists_gapOfNorm_deriv_bounds (hgap : HaarGapDerivBound) (hweyl : WeylIntegrationFormula)
    (hsm : HaarGapSmoothStatement) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : ℝ, 2 ≤ A → ∀ z : ℍ[ℝ], 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
      ContDiffAt ℝ 3 (gapOfNorm A) z ∧ (∀ a, |fderiv ℝ (gapOfNorm A) z a| ≤ K * ‖a‖) ∧
        ∀ a b, |fderiv ℝ (fderiv ℝ (gapOfNorm A)) z a b| ≤ K * ‖a‖ * ‖b‖ := by
  obtain ⟨C₁, h₁⟩ := hgap 1 le_rfl
  obtain ⟨C₂, h₂⟩ := hgap 2 (by norm_num)
  have hC₁ : 0 ≤ C₁ := (abs_nonneg _).trans (h₁ 1 le_rfl)
  have hC₂ : 0 ≤ C₂ := (abs_nonneg _).trans (h₂ 1 le_rfl)
  have hsame : logPartitionGap = haarGap := funext hweyl.2.2
  obtain ⟨N, hN0, hN⟩ := exists_bound_fderiv_of_isCompact (f := fun z : ℍ[ℝ] => ‖z‖) isCompact_unitShell fun z hz =>
    contDiffAt_norm ℝ (by
      intro h0
      have := hz.1
      rw [h0, norm_zero] at this
      norm_num at this)
  refine ⟨2 * C₁ * N + 4 * C₂ * N ^ 2, by positivity, fun A hA z hz1 hz2 => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz1
    norm_num at hz1
  have hNz := hN z ⟨hz1, hz2⟩
  set g : ℍ[ℝ] → ℝ := fun y => A * ‖y‖ with hg
  set s : ℝ := A * ‖z‖ with hs
  have hs1 : 1 ≤ s := by nlinarith
  have hAs : A ≤ 2 * s := by nlinarith
  have hA0 : 0 ≤ A := by linarith
  have hns : ContDiffAt ℝ 3 (fun y : ℍ[ℝ] => ‖y‖) z := contDiffAt_norm ℝ hz0
  have hgs : ContDiffAt ℝ 3 g z := contDiffAt_const.mul hns
  have hsg : ContDiffAt ℝ 3 haarGap (g z) := hsm.contDiffAt
  have hQ : gapOfNorm A = haarGap ∘ g := by
    funext y
    simp only [gapOfNorm, Function.comp, hg, hsame]
  have hd1 : ∀ y : ℍ[ℝ], y ≠ 0 → fderiv ℝ g y = A • fderiv ℝ (fun y : ℍ[ℝ] => ‖y‖) y := by
    intro y hy
    exact fderiv_const_mul ((contDiffAt_norm ℝ hy (n := 3)).differentiableAt (by norm_num)) A
  have hd2 : fderiv ℝ (fderiv ℝ g) z = A • fderiv ℝ (fderiv ℝ fun y : ℍ[ℝ] => ‖y‖) z := by
    have he : fderiv ℝ g =ᶠ[𝓝 z] fun y => A • fderiv ℝ (fun y : ℍ[ℝ] => ‖y‖) y := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
      exact hd1 y hy
    rw [he.fderiv_eq]
    exact fderiv_const_smul
      ((hns.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)) A
  have hD1 : ‖fderiv ℝ haarGap s‖ * A ≤ 2 * C₁ := by
    have h := h₁ s hs1
    have e : ‖fderiv ℝ haarGap s‖ = |iteratedDeriv 1 haarGap s| := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    rw [e]
    rw [abs_mul, pow_one, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s)] at h
    have h3 := abs_nonneg (iteratedDeriv 1 haarGap s)
    nlinarith
  have hD2 : ‖fderiv ℝ (fderiv ℝ haarGap) s‖ * A ^ 2 ≤ 4 * C₂ := by
    have h := h₂ s hs1
    have e : ‖fderiv ℝ (fderiv ℝ haarGap) s‖ = |iteratedDeriv 2 haarGap s| := by
      rw [← norm_iteratedFDeriv_two_eq, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    rw [e]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2)] at h
    have h3 := abs_nonneg (iteratedDeriv 2 haarGap s)
    have h4 : A ^ 2 ≤ 4 * s ^ 2 := by nlinarith
    nlinarith
  have hDN : ∀ a, ‖fderiv ℝ (fun y : ℍ[ℝ] => ‖y‖) z a‖ ≤ N * ‖a‖ := fun a =>
    (fderiv ℝ (fun y : ℍ[ℝ] => ‖y‖) z).le_of_opNorm_le hNz.1 a
  have hDg : ∀ a, |fderiv ℝ g z a| ≤ A * (N * ‖a‖) := by
    intro a
    rw [hd1 z hz0, ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hA0]
    exact mul_le_mul_of_nonneg_left (hDN a) hA0
  have hDDg : ∀ a b, |fderiv ℝ (fderiv ℝ g) z a b| ≤ A * (N * ‖a‖ * ‖b‖) := by
    intro a b
    rw [hd2]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [abs_mul, abs_of_nonneg hA0]
    refine mul_le_mul_of_nonneg_left ?_ hA0
    have h := (fderiv ℝ (fderiv ℝ fun y : ℍ[ℝ] => ‖y‖) z).le_opNorm₂ a b
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    gcongr
    exact hNz.2
  have hee : gapOfNorm A =ᶠ[𝓝 z] haarGap ∘ g := by rw [hQ]
  refine ⟨by rw [hQ]; exact hsg.comp z hgs, fun a => ?_, fun a b => ?_⟩
  · rw [fderiv_of_eventuallyEq_comp hee (hsg.differentiableAt (by norm_num)) (hgs.differentiableAt (by norm_num))]
    simp only [ContinuousLinearMap.comp_apply]
    have h := (fderiv ℝ haarGap s).le_opNorm (fderiv ℝ g z a)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    have h5 : ‖fderiv ℝ haarGap s‖ * |fderiv ℝ g z a| ≤ ‖fderiv ℝ haarGap s‖ * (A * (N * ‖a‖)) :=
      mul_le_mul_of_nonneg_left (hDg a) (norm_nonneg _)
    have h6 : ‖fderiv ℝ haarGap s‖ * (A * (N * ‖a‖)) ≤ 2 * C₁ * (N * ‖a‖) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hD1 (by positivity)
    have h7 : 0 ≤ 4 * C₂ * N ^ 2 * ‖a‖ := by positivity
    calc _ ≤ _ := h.trans (h5.trans h6)
      _ ≤ _ := by nlinarith
  · have hf := second_fderiv_of_eventuallyEq_comp hee (hsg.of_le (by norm_num)) (hgs.of_le (by norm_num)) a b
    rw [hf]
    have h1 := (fderiv ℝ (fderiv ℝ haarGap) s).le_opNorm₂ (fderiv ℝ g z a) (fderiv ℝ g z b)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h1
    have h2 := (fderiv ℝ haarGap s).le_opNorm (fderiv ℝ (fderiv ℝ g) z a b)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h2
    have h3 : |fderiv ℝ g z a| * |fderiv ℝ g z b| ≤ (A * (N * ‖a‖)) * (A * (N * ‖b‖)) :=
      mul_le_mul (hDg a) (hDg b) (abs_nonneg _) (by positivity)
    have h4 : ‖fderiv ℝ (fderiv ℝ haarGap) s‖ * |fderiv ℝ g z a| * |fderiv ℝ g z b| ≤
        4 * C₂ * N ^ 2 * ‖a‖ * ‖b‖ := by
      calc _ = ‖fderiv ℝ (fderiv ℝ haarGap) s‖ * (|fderiv ℝ g z a| * |fderiv ℝ g z b|) := by ring
        _ ≤ ‖fderiv ℝ (fderiv ℝ haarGap) s‖ * ((A * (N * ‖a‖)) * (A * (N * ‖b‖))) :=
            mul_le_mul_of_nonneg_left h3 (ContinuousLinearMap.opNorm_nonneg _)
        _ = (‖fderiv ℝ (fderiv ℝ haarGap) s‖ * A ^ 2) * (N ^ 2 * ‖a‖ * ‖b‖) := by ring
        _ ≤ (4 * C₂) * (N ^ 2 * ‖a‖ * ‖b‖) := mul_le_mul_of_nonneg_right hD2 (by positivity)
        _ = _ := by ring
    have h5 : ‖fderiv ℝ haarGap s‖ * |fderiv ℝ (fderiv ℝ g) z a b| ≤ 2 * C₁ * N * ‖a‖ * ‖b‖ := by
      calc _ ≤ ‖fderiv ℝ haarGap s‖ * (A * (N * ‖a‖ * ‖b‖)) :=
            mul_le_mul_of_nonneg_left (hDDg a b) (norm_nonneg _)
        _ = (‖fderiv ℝ haarGap s‖ * A) * (N * ‖a‖ * ‖b‖) := by ring
        _ ≤ (2 * C₁) * (N * ‖a‖ * ‖b‖) := mul_le_mul_of_nonneg_right hD1 (by positivity)
        _ = _ := by ring
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (h1.trans h4) (h2.trans h5)
      _ = _ := by ring
section Composition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem gap_comp_isTame {Q : ℍ[ℝ] → ℝ} {m : E → ℍ[ℝ]} {p : E} {A₀ B₀ K : ℝ} (hK : 0 ≤ K) (hm : IsTame m p A₀ B₀)
    (hQ : ContDiffAt ℝ 3 Q (m p)) (h1 : ∀ a, |fderiv ℝ Q (m p) a| ≤ K * ‖a‖)
    (h2 : ∀ a b, |fderiv ℝ (fderiv ℝ Q) (m p) a b| ≤ K * ‖a‖ * ‖b‖) :
    ContDiffAt ℝ 3 (Q ∘ m) p ∧ (∀ u, |fderiv ℝ (Q ∘ m) p u| ≤ K * A₀ * ‖u‖) ∧
      (∀ u v, |fderiv ℝ (fderiv ℝ (Q ∘ m)) p u v| ≤ K * (A₀ ^ 2 + B₀) * ‖u‖ * ‖v‖) ∧
      (∀ u v, fderiv ℝ m p u = 0 → fderiv ℝ (fderiv ℝ m) p u v = 0 → fderiv ℝ (fderiv ℝ m) p v u = 0 →
        fderiv ℝ (Q ∘ m) p u = 0 ∧ fderiv ℝ (fderiv ℝ (Q ∘ m)) p u v = 0 ∧
          fderiv ℝ (fderiv ℝ (Q ∘ m)) p v u = 0) := by
  have hms : ContDiffAt ℝ 3 m p := hm.smooth.contDiffAt
  have hA₀ : 0 ≤ A₀ := (norm_nonneg _).trans hm.firstDeriv_le
  have hn1 : ‖fderiv ℝ m p‖ ≤ A₀ := by
    rw [← norm_iteratedFDeriv_one]
    exact hm.firstDeriv_le
  have hD : ∀ u, ‖fderiv ℝ m p u‖ ≤ A₀ * ‖u‖ := fun u => (fderiv ℝ m p).le_of_opNorm_le hn1 u
  have hDD : ∀ u v, ‖fderiv ℝ (fderiv ℝ m) p u v‖ ≤ B₀ * ‖u‖ * ‖v‖ := by
    intro u v
    have h := (iteratedFDeriv ℝ 2 m p).le_opNorm ![u, v]
    rw [iteratedFDeriv_two_apply] at h
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    refine h.trans ?_
    rw [mul_assoc B₀]
    exact mul_le_mul_of_nonneg_right hm.secondDeriv_le (by positivity)
  have he : Q ∘ m =ᶠ[𝓝 p] Q ∘ m := EventuallyEq.rfl
  have f1 := fderiv_of_eventuallyEq_comp he (hQ.differentiableAt (by norm_num)) (hms.differentiableAt (by norm_num))
  have f2 := second_fderiv_of_eventuallyEq_comp he (hQ.of_le (by norm_num)) (hms.of_le (by norm_num))
  refine ⟨hQ.comp p hms, fun u => ?_, fun u v => ?_, fun u v hu huv hvu => ⟨?_, ?_, ?_⟩⟩
  · rw [f1, ContinuousLinearMap.comp_apply]
    calc _ ≤ K * ‖fderiv ℝ m p u‖ := h1 _
      _ ≤ K * (A₀ * ‖u‖) := mul_le_mul_of_nonneg_left (hD u) hK
      _ = _ := by ring
  · rw [f2 u v]
    have e1 := h2 (fderiv ℝ m p u) (fderiv ℝ m p v)
    have e2 := h1 (fderiv ℝ (fderiv ℝ m) p u v)
    have e3 : K * ‖fderiv ℝ m p u‖ * ‖fderiv ℝ m p v‖ ≤ K * A₀ ^ 2 * ‖u‖ * ‖v‖ := by
      calc _ = K * (‖fderiv ℝ m p u‖ * ‖fderiv ℝ m p v‖) := by ring
        _ ≤ K * ((A₀ * ‖u‖) * (A₀ * ‖v‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hD u) (hD v) (norm_nonneg _) (by positivity)) hK
        _ = _ := by ring
    have e4 : K * ‖fderiv ℝ (fderiv ℝ m) p u v‖ ≤ K * B₀ * ‖u‖ * ‖v‖ := by
      calc _ ≤ K * (B₀ * ‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left (hDD u v) hK
        _ = _ := by ring
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (e1.trans e3) (e2.trans e4)
      _ = _ := by ring
  · rw [f1, ContinuousLinearMap.comp_apply, hu, map_zero]
  · rw [f2 u v, hu, huv]
    simp
  · rw [f2 v u, hu, hvu]
    simp
theorem fderiv_eq_zero_of_comp_proj {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ 3 f) (P : E →L[ℝ] E) (he : ∀ y, f (P y) = f y) {u : E} (hu : P u = 0) (p v : E) :
    fderiv ℝ f p u = 0 ∧ fderiv ℝ (fderiv ℝ f) p u v = 0 ∧ fderiv ℝ (fderiv ℝ f) p v u = 0 := by
  have hc : f = f ∘ P := funext fun y => (he y).symm
  have hee : f =ᶠ[𝓝 p] f ∘ P := by
    rw [← hc]
  have f1 := fderiv_of_eventuallyEq_comp hee (hf.differentiable (by norm_num) (P p)) P.differentiableAt
  have f2 := second_fderiv_of_eventuallyEq_comp hee (hf.of_le (by norm_num)).contDiffAt
    (P.contDiff (n := 2)).contDiffAt
  have hP : fderiv ℝ (P : E → E) = fun _ => P := funext fun y => P.fderiv
  have hPP : fderiv ℝ (fderiv ℝ (P : E → E)) p = 0 := by
    rw [hP]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [f1, ContinuousLinearMap.comp_apply, P.fderiv, hu, map_zero]
  · rw [f2, hPP, P.fderiv, hu]
    simp
  · rw [f2, hPP, P.fderiv, hu]
    simp
end Composition
section Step
variable {R : StepSetup} {n : ℕ}
open Classical in
def restrictCoords {N : ℕ} {free : Finset (TorusBond N)} (A : free → Prop) : FreeCoords free →L[ℝ] FreeCoords free :=
  ContinuousLinearMap.pi fun b => if A b then ContinuousLinearMap.proj b else 0
open Classical in
theorem restrictCoords_apply {N : ℕ} {free : Finset (TorusBond N)} (A : free → Prop) (η : FreeCoords free)
    (b : free) : restrictCoords A η b = if A b then η b else 0 := by
  unfold restrictCoords
  rw [ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl
def IsNearBond (R : StepSetup) (c : TorusBond n) (b : TorusBond (n * R.params.side)) : Prop :=
  bondBlock (R := R) b = c.1 ∨ bondBlock (R := R) b = c.1 + TorusFields.unitStep n c.2
theorem toTorusSite_torusSiteInFrame [NeZero n] (L : ℕ) [NeZero L] (c : TorusSite n) :
    (toTorusSite n (torusSiteInFrame (stepBlockFrame L n) 1 c) : TorusSite n) = c := by
  unfold torusSiteInFrame
  rw [TopLevelSites.toTorusSite_siteOfCoords (fun i => stepBlockFrame_period_one i)]
  funext k
  simp [siteOfInt]
theorem bondMean_restrictCoords [NeZero n] (hread : ContourMeanReadsTwoBlocks) (hodd : Odd R.params.side)
    (hn : 16 ≤ n) (s : ChartSetting R n) {J₀ : ℕ} {h₁ : Finset (Finset ((stepBlockFrame R.params.side n).Site 0))}
    (hb : IsBaseChoice (F := stepBlockFrame R.params.side n) J₀ h₁ s.bases)
    (h : Finset (Finset ((stepBlockFrame R.params.side n).Site 0))) (c : TorusBond n) (η : FreeCoords s.free) :
    bondMean s h c (restrictCoords (fun b : s.free => IsNearBond R c b.1) η) = bondMean s h c η := by
  classical
  have hL : 1 ≤ (stepBlockFrame R.params.side n).blockSide := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  have mem : ∀ z : (stepBlockFrame R.params.side n).Cell, s.bases z ∈ sitesBelow 0 z := fun z => by
    obtain ⟨w, hw, e⟩ := exists_centredCube_of_isBaseChoice hL hb z
    rw [e]
    exact (mem_sitesBelow_iff z _).mpr ⟨w, hw, rfl⟩
  have hblock : ∀ (y : (stepBlockFrame R.params.side n).Cell) (x : (stepBlockFrame R.params.side n).Site 0),
      x ∈ sitesBelow 0 y →
      parentBlock R.params.side (toTorusSite (n * R.params.side) x : TorusSite (n * R.params.side)) =
        toTorusSite n y := by
    intro y x hx
    obtain ⟨w, hw, e⟩ := (mem_sitesBelow_iff y x).mp hx
    rw [e]
    exact parentBlock_siteAtOffset y hw
  have hy : (toTorusSite n (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1) : TorusSite n) = c.1 :=
    toTorusSite_torusSiteInFrame _ _
  have hy' : (toTorusSite n (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1 +
      BlockAverages.unitStep 1 c.2) : TorusSite n) = c.1 + TorusFields.unitStep n c.2 := by
    rw [TopLevelSites.toTorusSite_add (fun i => stepBlockFrame_period_one i), hy,
      TopLevelSites.toTorusSite_unitStep (fun i => stepBlockFrame_period_one i)]
  unfold bondMean
  refine hread R.params.side n R.params.baseDepth hodd hn h h s.bases s.bases _ _
    (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1) c.2 rfl rfl rfl (mem _) rfl (mem _) ?_
  intro x k hx _
  show s.field _ (toTorusSite (n * R.params.side) x) k = s.field η (toTorusSite (n * R.params.side) x) k
  unfold ChartSetting.field
  by_cases hf : (toTorusSite (n * R.params.side) x, k) ∈ s.free
  · rw [dif_pos hf, dif_pos hf, restrictCoords_apply, if_pos]
    rcases hx with hx | hx
    · exact Or.inl ((hblock _ x hx).trans hy)
    · exact Or.inr ((hblock _ x hx).trans hy')
  · rw [dif_neg hf, dif_neg hf]
theorem continuous_fieldCurvature (s : ChartSetting R n)
    (hc : ∀ x i, Continuous fun η : FreeCoords s.free => ((s.field η x i : UnitQuaternion) : ℍ[ℝ]))
    (z : TorusSite (n * R.params.side)) (μ ν : Fin 4) :
    Continuous fun η : FreeCoords s.free => TorusFields.curvature (s.field η) z μ ν := by
  unfold TorusFields.curvature holonomy
  have e : (fun η : FreeCoords s.free => ((s.field η z μ * s.field η (z + TorusFields.unitStep _ μ) ν *
      (s.field η (z + TorusFields.unitStep _ ν) μ)⁻¹ * (s.field η z ν)⁻¹ : UnitQuaternion) : ℍ[ℝ])) = fun η =>
      ((s.field η z μ : UnitQuaternion) : ℍ[ℝ]) *
        ((s.field η (z + TorusFields.unitStep _ μ) ν : UnitQuaternion) : ℍ[ℝ]) *
        star ((s.field η (z + TorusFields.unitStep _ ν) μ : UnitQuaternion) : ℍ[ℝ]) *
        star ((s.field η z ν : UnitQuaternion) : ℍ[ℝ]) := by
    funext η
    simp only [Submonoid.coe_mul, coe_inv_unitQuaternion]
  have h1 : Continuous fun η : FreeCoords s.free =>
      ((s.field η z μ : UnitQuaternion) : ℍ[ℝ]) *
        ((s.field η (z + TorusFields.unitStep _ μ) ν : UnitQuaternion) : ℍ[ℝ]) *
        star ((s.field η (z + TorusFields.unitStep _ ν) μ : UnitQuaternion) : ℍ[ℝ]) *
        star ((s.field η z ν : UnitQuaternion) : ℍ[ℝ]) :=
    (((hc _ _).mul (hc _ _)).mul (hc _ _).star).mul (hc _ _).star
  rw [← e] at h1
  exact (h1.sub continuous_const).norm
theorem stepHotLumps_eventually_eq [NeZero n] (s : ChartSetting R n) (hs : s.IsAdmissible)
    (hσ : 0 < R.params.threshold) (hr : 1 ≤ R.range)
    (hc : ∀ x i, Continuous fun η : FreeCoords s.free => ((s.field η x i : UnitQuaternion) : ℍ[ℝ]))
    (p : FreeCoords s.free) (hp : s.InBalls p) :
    ∀ᶠ η in 𝓝 p, stepHotLumps R.params (s.field η) = stepHotLumps R.params (s.field p) := by
  classical
  have hper : ∀ i, (stepBlockFrame R.params.side n).period 0 i = n * R.params.side :=
    fun i => stepBlockFrame_period_zero i
  have key : ∀ q ∈ cutPlaquettes (levelSites (stepBlockFrame R.params.side n) 0), ∀ᶠ η in 𝓝 p,
      (R.params.threshold ≤ plaquetteDefect (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η)) q ↔
        R.params.threshold ≤ plaquetteDefect (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field p)) q) := by
    rintro ⟨x, μ, ν⟩ hq
    have hlt : μ < ν := (Finset.mem_filter.mp hq).2.1
    have er : ∀ η, plaquetteDefect (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η)) (x, μ, ν) =
        TorusFields.curvature (s.field η) (toTorusSite (n * R.params.side) x) μ ν :=
      fun η => plaquetteDefect_readAtLevel_eq hper _ _ _ _
    simp only [er]
    set z : TorusSite (n * R.params.side) := toTorusSite (n * R.params.side) x with hz
    by_cases hfree : (z, μ) ∈ s.free ∨ (z + TorusFields.unitStep _ μ, ν) ∈ s.free ∨
        (z + TorusFields.unitStep _ ν, μ) ∈ s.free ∨ (z, ν) ∈ s.free
    · have hd : ∃ b ∈ s.free, supDist z b.1 ≤ 3 * R.range := by
        have h1 : supDist z z ≤ 3 * R.range := by
          rw [supDist_self]
          omega
        have h2 : ∀ i, supDist z (z + TorusFields.unitStep _ i) ≤ 3 * R.range := fun i => by
          have := supDist_add_unitStep_le z i
          omega
        rcases hfree with h | h | h | h
        · exact ⟨_, h, h1⟩
        · exact ⟨_, h, h2 μ⟩
        · exact ⟨_, h, h2 ν⟩
        · exact ⟨_, h, h1⟩
      obtain ⟨b, hb, hbd⟩ := hd
      have hcold := hs.curvature_lt p hp b hb z μ ν hlt hbd
      have hlt' : TorusFields.curvature (s.field p) z μ ν < R.params.threshold := by linarith
      have ev1 : ∀ᶠ η in 𝓝 p, TorusFields.curvature (s.field η) z μ ν < R.params.threshold :=
        (continuous_fieldCurvature s hc z μ ν).continuousAt.eventually_lt continuousAt_const hlt'
      filter_upwards [ev1] with η hη
      exact iff_of_false (not_le.mpr hη) (not_le.mpr hlt')
    · push Not at hfree
      obtain ⟨f1, f2, f3, f4⟩ := hfree
      refine Eventually.of_forall fun η => ?_
      have e : ∀ η : FreeCoords s.free, ∀ y i, (y, i) ∉ s.free → s.field η y i = s.fine y i :=
        fun η y i h => dif_neg h
      have : TorusFields.curvature (s.field η) z μ ν = TorusFields.curvature (s.field p) z μ ν := by
        unfold TorusFields.curvature holonomy
        rw [e η _ _ f1, e η _ _ f2, e η _ _ f3, e η _ _ f4, e p _ _ f1, e p _ _ f2, e p _ _ f3, e p _ _ f4]
      rw [this]
  filter_upwards [(eventually_all_finset _).mpr key] with η hη
  unfold stepHotLumps hotLumps
  congr 1
  exact Finset.filter_congr hη
theorem restrictCoords_single {N : ℕ} {free : Finset (TorusBond N)} {A : free → Prop} {b : free} (hb : ¬ A b)
    (X : EuclideanSpace ℝ (Fin 3)) :
    restrictCoords A (Pi.single b X : FreeCoords free) = 0 := by
  classical
  funext b'
  rw [restrictCoords_apply]
  split_ifs with h
  · have : b' ≠ b := fun e => hb (e ▸ h)
    simp [Pi.single_eq_of_ne this]
  · rfl
theorem supDist_parentBlock_le_of_isNearBond {c : TorusBond n} {b : TorusBond (n * R.params.side)} [NeZero n]
    (h : IsNearBond R c b) : supDist (parentBlock R.params.side b.1) c.1 ≤ 1 := by
  rcases h with h | h
  · have e : parentBlock R.params.side b.1 = c.1 := h
    rw [e, supDist_self]
    omega
  · have e : parentBlock R.params.side b.1 = c.1 + TorusFields.unitStep n c.2 := h
    rw [e, _root_.YangMills.Construction.TorusFields.supDist_comm]
    exact supDist_add_unitStep_le _ _
theorem gapOfNorm_bondMean_bounds [NeZero n] (hread : ContourMeanReadsTwoBlocks) (hodd : Odd R.params.side)
    (hn : 16 ≤ n) (s : ChartSetting R n) (hs : s.IsAdmissible) {Kq Ke A : ℝ} (hKq : 0 ≤ Kq) (hKe : 0 ≤ Ke)
    (hexp : ∀ z : ℍ[ℝ], ‖z‖ ≤ 2 → ‖iteratedFDeriv ℝ 1 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) z‖ ≤ Ke ∧
      ‖iteratedFDeriv ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) z‖ ≤ Ke)
    (houter : ∀ A : ℝ, 2 ≤ A → ∀ z : ℍ[ℝ], 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
      ContDiffAt ℝ 3 (gapOfNorm A) z ∧ (∀ a, |fderiv ℝ (gapOfNorm A) z a| ≤ Kq * ‖a‖) ∧
        ∀ a b, |fderiv ℝ (fderiv ℝ (gapOfNorm A)) z a b| ≤ Kq * ‖a‖ * ‖b‖)
    (hA : 2 ≤ A) (p : FreeCoords s.free) (hp : s.InBalls p)
    (hsize : ∀ b : s.free, ‖((s.frame b.1 + toImaginary (p b) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 2)
    (h₀ : Finset (Finset ((stepBlockFrame R.params.side n).Site 0)))
    (hh : h₀ = stepHotLumps R.params (s.field p)) (c : TorusBond n) :
    ContDiffAt ℝ 3 (fun η => gapOfNorm A (bondMean s h₀ c η)) p ∧
    (∀ u, |fderiv ℝ (fun η => gapOfNorm A (bondMean s h₀ c η)) p u| ≤
      Kq * (Ke * (9 * R.params.side : ℕ)) * ‖u‖) ∧
    (∀ u v, |fderiv ℝ (fderiv ℝ fun η => gapOfNorm A (bondMean s h₀ c η)) p u v| ≤
      Kq * ((Ke * (9 * R.params.side : ℕ)) ^ 2 + (Ke * (9 * R.params.side : ℕ) +
        (Ke * (9 * R.params.side : ℕ)) ^ 2)) * ‖u‖ * ‖v‖) ∧
    ∀ b : s.free, ¬ IsNearBond R c b.1 → ∀ (X : EuclideanSpace ℝ (Fin 3)) (v : FreeCoords s.free),
      fderiv ℝ (fun η => gapOfNorm A (bondMean s h₀ c η)) p (Pi.single b X) = 0 ∧
      fderiv ℝ (fderiv ℝ fun η => gapOfNorm A (bondMean s h₀ c η)) p (Pi.single b X) v = 0 ∧
      fderiv ℝ (fderiv ℝ fun η => gapOfNorm A (bondMean s h₀ c η)) p v (Pi.single b X) = 0 := by
  have hn2 : 2 ≤ n := by omega
  have hm := isTame_bondMean s hKe hexp p hsize hn2 hs.isBaseChoice h₀ c
  have hkeep : ∀ η, bondMean s h₀ c (restrictCoords (fun b : s.free => IsNearBond R c b.1) η) =
      bondMean s h₀ c η :=
    fun η => bondMean_restrictCoords hread hodd hn s hs.isBaseChoice h₀ c η
  by_cases hex : ∃ b : s.free, IsNearBond R c b.1
  · obtain ⟨b₀, hb₀⟩ := hex
    have hlow : 1 / 2 ≤ ‖bondMean s h₀ c p‖ := by
      have h1 := hs.half_le_meanNorm p hp b₀.1 b₀.2 c
        ((supDist_parentBlock_le_of_isNearBond hb₀).trans (by norm_num))
      rw [hh]
      exact h1
    obtain ⟨q1, q2, q3⟩ := houter A hA _ hlow hm.norm_le_one
    obtain ⟨r1, r2, r3, r4⟩ := gap_comp_isTame hKq hm q1 q2 q3
    refine ⟨r1, r2, r3, fun b hb X v => ?_⟩
    obtain ⟨v1, v2, v3⟩ := fderiv_eq_zero_of_comp_proj hm.smooth _ hkeep
      (restrictCoords_single (A := fun b : s.free => IsNearBond R c b.1) hb X) p v
    exact r4 _ _ v1 v2 v3
  · have hz : ∀ η : FreeCoords s.free, restrictCoords (fun b : s.free => IsNearBond R c b.1) η = 0 := by
      intro η
      funext b
      rw [restrictCoords_apply, if_neg fun h => hex ⟨b, h⟩]
      rfl
    have hG : (fun η => gapOfNorm A (bondMean s h₀ c η)) = fun _ => gapOfNorm A (bondMean s h₀ c 0) := by
      funext η
      rw [← hkeep η, hz]
    have hnn : 0 ≤ Ke * ((9 * R.params.side : ℕ) : ℝ) := by positivity
    rw [hG]
    refine ⟨contDiffAt_const, fun u => ?_, fun u v => ?_, fun b _ X v => ?_⟩
    · simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, abs_zero]
      positivity
    · simp only [fderiv_fun_const]
      simp
      positivity
    · simp
def logHaar (w : EuclideanSpace ℝ (Fin 3)) : ℝ := Real.log (haarLogDensity w)
theorem exists_logHaar_bounds (hlog : logHaarDensityContDiffOnBall) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 3 / 2 → ContDiffAt ℝ 3 logHaar z ∧ ‖fderiv ℝ logHaar z‖ ≤ K ∧
      ‖fderiv ℝ (fderiv ℝ logHaar) z‖ ≤ K := by
  have hπ := Real.pi_gt_three
  have hs : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 3 / 2 → ContDiffAt ℝ 3 logHaar z := fun z hz =>
    hlog z (by linarith)
  obtain ⟨K, hK, h⟩ := exists_bound_fderiv_of_isCompact (f := logHaar)
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 2)) fun z hz => hs z (by simpa using hz)
  exact ⟨K, hK, fun z hz => ⟨hs z hz, h z (by simpa using hz)⟩⟩
theorem logHaar_coord_bounds {N : ℕ} {free : Finset (TorusBond N)} {K : ℝ} (b : free)
    (v₀ : EuclideanSpace ℝ (Fin 3)) (p : FreeCoords free) (hs : ContDiffAt ℝ 3 logHaar (v₀ + p b))
    (h1 : ‖fderiv ℝ logHaar (v₀ + p b)‖ ≤ K) (h2 : ‖fderiv ℝ (fderiv ℝ logHaar) (v₀ + p b)‖ ≤ K) :
    ContDiffAt ℝ 3 (fun η : FreeCoords free => logHaar (v₀ + η b)) p ∧
      (∀ u : FreeCoords free, |fderiv ℝ (fun η : FreeCoords free => logHaar (v₀ + η b)) p u| ≤ K * ‖u b‖) ∧
      ∀ u v : FreeCoords free,
        |fderiv ℝ (fderiv ℝ fun η : FreeCoords free => logHaar (v₀ + η b)) p u v| ≤ K * ‖u b‖ * ‖v b‖ := by
  set P : FreeCoords free →L[ℝ] EuclideanSpace ℝ (Fin 3) := ContinuousLinearMap.proj b with hP
  set l : FreeCoords free → EuclideanSpace ℝ (Fin 3) := fun η => v₀ + P η with hl
  have hd : ∀ y, fderiv ℝ l y = P := fun y => (P.hasFDerivAt.const_add v₀).fderiv
  have hdd : fderiv ℝ (fderiv ℝ l) p = 0 := by
    rw [funext hd]
    simp
  have hlc : ContDiffAt ℝ 3 l p := (contDiff_const.add P.contDiff).contDiffAt
  have hH : (fun η : FreeCoords free => logHaar (v₀ + η b)) = logHaar ∘ l := rfl
  have hee : logHaar ∘ l =ᶠ[𝓝 p] logHaar ∘ l := EventuallyEq.rfl
  have hs' : ContDiffAt ℝ 3 logHaar (l p) := hs
  rw [hH]
  refine ⟨hs'.comp p hlc, fun u => ?_, fun u v => ?_⟩
  · rw [fderiv_of_eventuallyEq_comp hee (hs'.differentiableAt (by norm_num)) (hlc.differentiableAt (by norm_num)),
      hd, ContinuousLinearMap.comp_apply]
    have h := (fderiv ℝ logHaar (l p)).le_of_opNorm_le h1 (P u)
    rwa [Real.norm_eq_abs] at h
  · rw [second_fderiv_of_eventuallyEq_comp hee (hs'.of_le (by norm_num)) (hlc.of_le (by norm_num)), hd, hdd]
    simp only [ContinuousLinearMap.zero_apply, map_zero, add_zero]
    have h := (fderiv ℝ (fderiv ℝ logHaar) (l p)).le_opNorm₂ (P u) (P v)
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    have h3 : ‖fderiv ℝ (fderiv ℝ logHaar) (l p)‖ ≤ K := h2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (norm_nonneg _)) (norm_nonneg _)
end Step
section Sums
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem contDiffAt_sum_and_fderiv {ι : Type*} (S : Finset ι) (f : ι → E → ℝ) {p : E}
    (h : ∀ i ∈ S, ContDiffAt ℝ 3 (f i) p) :
    ContDiffAt ℝ 3 (fun y => ∑ i ∈ S, f i y) p ∧
      fderiv ℝ (fun y => ∑ i ∈ S, f i y) p = ∑ i ∈ S, fderiv ℝ (f i) p ∧
      fderiv ℝ (fderiv ℝ fun y => ∑ i ∈ S, f i y) p = ∑ i ∈ S, fderiv ℝ (fderiv ℝ (f i)) p := by
  have hd : ∀ i ∈ S, ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ (f i) y := fun i hi =>
    eventually_differentiableAt_of_contDiffAt_two ((h i hi).of_le (by norm_num))
  have he : fderiv ℝ (fun y => ∑ i ∈ S, f i y) =ᶠ[𝓝 p] fun y => ∑ i ∈ S, fderiv ℝ (f i) y := by
    filter_upwards [(eventually_all_finset S).mpr hd] with y hy
    exact fderiv_fun_sum hy
  have hdd : ∀ i ∈ S, DifferentiableAt ℝ (fderiv ℝ (f i)) p := fun i hi =>
    ((h i hi).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  refine ⟨ContDiffAt.sum h, he.eq_of_nhds, ?_⟩
  rw [he.fderiv_eq]
  exact fderiv_fun_sum hdd
theorem update_add_smul_eq {ι : Type*} [DecidableEq ι] {β : Type*} [AddCommGroup β] [Module ℝ β] (η : ι → β)
    (b : ι) (X : β) (τ : ℝ) : Function.update η b (η b + τ • X) = η + τ • (Pi.single b X : ι → β) := by
  funext b'
  by_cases h : b' = b
  · subst h
    simp
  · simp [h]
end Sums
section Final
variable {R : StepSetup} {n : ℕ}
open Classical in
theorem card_isNearBond_le [NeZero n] (b : TorusBond (n * R.params.side)) :
    (Finset.univ.filter fun c : TorusBond n => IsNearBond R c b).card ≤ 8 := by
  set B := bondBlock (R := R) b with hB
  have hsub : (Finset.univ.filter fun c : TorusBond n => IsNearBond R c b) ⊆
      (Finset.univ : Finset (Fin 4 × Bool)).image
        fun q => ((if q.2 then B else B - TorusFields.unitStep n q.1), q.1) := by
    rintro ⟨y, i⟩ hc
    have hn : IsNearBond R (y, i) b := (Finset.mem_filter.mp hc).2
    refine Finset.mem_image.mpr ?_
    rcases hn with h | h
    · refine ⟨(i, true), Finset.mem_univ _, ?_⟩
      simp only [if_true]
      exact Prod.ext h rfl
    · refine ⟨(i, false), Finset.mem_univ _, ?_⟩
      have h' : B = y + TorusFields.unitStep n i := h
      simp only [Bool.false_eq_true, if_false]
      exact Prod.ext (by rw [h']; simp) rfl
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = 8 := by simp
theorem bondBlockDist_le_one_of_isNearBond [NeZero n] {c : TorusBond n} {b b' : TorusBond (n * R.params.side)}
    (h : IsNearBond R c b) (h' : IsNearBond R c b') : bondBlockDist (R := R) (n := n) b b' ≤ 1 := by
  unfold bondBlockDist
  rcases h with h | h <;> rcases h' with h' | h' <;> rw [h, h']
  · rw [supDist_self]
    omega
  · exact supDist_add_unitStep_le _ _
  · rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    exact supDist_add_unitStep_le _ _
  · rw [supDist_self]
    omega
open Classical in
theorem card_bondBlockDist_le_one [NeZero n] (s : ChartSetting R n) (b : s.free) :
    (((Finset.univ.filter fun b' : s.free => bondBlockDist (R := R) (n := n) b.1 b'.1 ≤ 1).card : ℕ) : ℝ) ≤
      4 * (3 ^ 4 * (2 * (R.params.side : ℝ) + 1) ^ 4) := by
  set B := bondBlock (R := R) b.1 with hB
  have hb1 : (sitesInBlocks R.params.side (thickening 1 {B})).card ≤ 3 ^ 4 * (2 * R.params.side + 1) ^ 4 := by
    have hsub : sitesInBlocks R.params.side (thickening 1 {B}) ⊆
        (thickening 1 {B}).biUnion fun Y => sitesInBlocks R.params.side {Y} := by
      intro x hx
      refine Finset.mem_biUnion.mpr ⟨parentBlock R.params.side x, ?_, ?_⟩
      · simpa [sitesInBlocks] using hx
      · simp [sitesInBlocks]
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ Y ∈ thickening 1 {B}, (sitesInBlocks R.params.side {Y}).card := Finset.card_biUnion_le
      _ ≤ ∑ _Y ∈ thickening 1 {B}, (2 * R.params.side + 1) ^ 4 :=
          Finset.sum_le_sum fun Y _ => card_sitesInBlocks_singleton_le Y
      _ = (thickening 1 {B}).card * (2 * R.params.side + 1) ^ 4 := by simp
      _ ≤ 3 ^ 4 * (2 * R.params.side + 1) ^ 4 := Nat.mul_le_mul_right _ (card_thickening_singleton_le 1 B)
  have hinj : (Finset.univ.filter fun b' : s.free => bondBlockDist (R := R) (n := n) b.1 b'.1 ≤ 1).card ≤
      ((sitesInBlocks R.params.side (thickening 1 {B})) ×ˢ (Finset.univ : Finset (Fin 4))).card := by
    refine Finset.card_le_card_of_injOn (fun b' => b'.1) ?_ ?_
    · intro b' hb'
      have hd : bondBlockDist (R := R) (n := n) b.1 b'.1 ≤ 1 := (Finset.mem_filter.mp hb').2
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
      have h1 : parentBlock R.params.side b'.1.1 ∈ thickening 1 {B} := by
        refine (mem_thickening _ _ _).2 ⟨B, by simp, ?_⟩
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
        exact hd
      simpa [sitesInBlocks] using h1
    · intro a _ a' _ h
      exact Subtype.ext h
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hinj
  have h3 := hinj.trans (Nat.mul_le_mul_right _ hb1)
  have h4 : (((Finset.univ.filter fun b' : s.free => bondBlockDist (R := R) (n := n) b.1 b'.1 ≤ 1).card : ℕ) : ℝ) ≤
      ((3 ^ 4 * (2 * R.params.side + 1) ^ 4 * 4 : ℕ) : ℝ) := by exact_mod_cast h3
  refine h4.trans (le_of_eq ?_)
  push_cast
  ring
theorem logJacobian_sum_eventuallyEq [NeZero n] (s : ChartSetting R n) (p : FreeCoords s.free)
    (h₀ : Finset (Finset ((stepBlockFrame R.params.side n).Site 0)))
    (hev : ∀ᶠ η in 𝓝 p, stepHotLumps R.params (s.field η) = h₀) :
    (fun η : FreeCoords s.free => ∑ Y : TorusSite n, s.logJacobian (s.field η) η Y) =ᶠ[𝓝 p] fun η =>
      ∑ i : TorusBond n ⊕ s.free, Sum.elim (fun c η => gapOfNorm (R.params.coupling * R.coupling) (bondMean s h₀ c η))
        (fun (b : s.free) (η : FreeCoords s.free) => logHaar (toCoords (s.frame b.1) + η b)) i η := by
  filter_upwards [hev] with η hη
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  unfold ChartSetting.logJacobian
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun i _ => ?_
    unfold meanNorm gapOfNorm bondMean
    rw [hη]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single (bondBlock (R := R) b.1)]
    · exact if_pos rfl
    · intro Y _ hY
      exact if_neg (Ne.symm hY)
    · intro h
      exact absurd (Finset.mem_univ _) h
open Classical in
theorem logJacobian_bounds_at [NeZero n] (hread : ContourMeanReadsTwoBlocks) (hodd : Odd R.params.side)
    (hn : 16 ≤ n) (s : ChartSetting R n) (hs : s.IsAdmissible) {Kq Ke Kh : ℝ} (hKq : 0 ≤ Kq) (hKe : 0 ≤ Ke)
    (hKh : 0 ≤ Kh)
    (hexp : ∀ z : ℍ[ℝ], ‖z‖ ≤ 2 → ‖iteratedFDeriv ℝ 1 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) z‖ ≤ Ke ∧
      ‖iteratedFDeriv ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) z‖ ≤ Ke)
    (houter : ∀ A : ℝ, 2 ≤ A → ∀ z : ℍ[ℝ], 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
      ContDiffAt ℝ 3 (gapOfNorm A) z ∧ (∀ a, |fderiv ℝ (gapOfNorm A) z a| ≤ Kq * ‖a‖) ∧
        ∀ a b, |fderiv ℝ (fderiv ℝ (gapOfNorm A)) z a b| ≤ Kq * ‖a‖ * ‖b‖)
    (hhaar : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 3 / 2 → ContDiffAt ℝ 3 logHaar z ∧
      ‖fderiv ℝ logHaar z‖ ≤ Kh ∧ ‖fderiv ℝ (fderiv ℝ logHaar) z‖ ≤ Kh)
    (hA : 2 ≤ R.params.coupling * R.coupling) (p : FreeCoords s.free) (hp : s.InBalls p)
    (hsize : ∀ b : s.free, ‖((s.frame b.1 + toImaginary (p b) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 2)
    (hsmall : ∀ b : s.free, ‖toCoords (s.frame b.1) + p b‖ ≤ 3 / 2)
    (hev : ∀ᶠ η in 𝓝 p, stepHotLumps R.params (s.field η) = stepHotLumps R.params (s.field p)) {B₁ B₂ : ℝ}
    (hB₁ : B₁ = Kq * (Ke * (9 * R.params.side : ℕ)))
    (hB₂ : B₂ = Kq * ((Ke * (9 * R.params.side : ℕ)) ^ 2 + (Ke * (9 * R.params.side : ℕ) +
      (Ke * (9 * R.params.side : ℕ)) ^ 2))) :
    ContDiffAt ℝ 3 (fun η : FreeCoords s.free => ∑ Y : TorusSite n, s.logJacobian (s.field η) η Y) p ∧
    (∀ (b : s.free) (X : EuclideanSpace ℝ (Fin 3)), ‖X‖ = 1 →
      |fderiv ℝ (fun η : FreeCoords s.free => ∑ Y : TorusSite n, s.logJacobian (s.field η) η Y) p
        (Pi.single b X)| ≤ 8 * B₁ + Kh) ∧
    ∀ (b b' : s.free) (X X' : EuclideanSpace ℝ (Fin 3)), ‖X‖ = 1 → ‖X'‖ = 1 →
      |fderiv ℝ (fderiv ℝ fun η : FreeCoords s.free => ∑ Y : TorusSite n, s.logJacobian (s.field η) η Y) p
        (Pi.single b X) (Pi.single b' X')| ≤
        (if bondBlockDist (R := R) (n := n) b.1 b'.1 ≤ 1 then 8 * B₂ else 0) + (if b = b' then Kh else 0) := by
  set h₀ := stepHotLumps R.params (s.field p) with hh₀
  have hB₁0 : 0 ≤ B₁ := by
    rw [hB₁]
    positivity
  have hB₂0 : 0 ≤ B₂ := by
    rw [hB₂]
    positivity
  have hmean := fun c : TorusBond n =>
    gapOfNorm_bondMean_bounds hread hodd hn s hs hKq hKe hexp houter hA p hp hsize h₀ rfl c
  have hlogs := fun b : s.free => logHaar_coord_bounds (K := Kh) b (toCoords (s.frame b.1)) p
    (hhaar _ (hsmall b)).1 (hhaar _ (hsmall b)).2.1 (hhaar _ (hsmall b)).2.2
  set piece : TorusBond n ⊕ s.free → FreeCoords s.free → ℝ :=
    Sum.elim (fun c η => gapOfNorm (R.params.coupling * R.coupling) (bondMean s h₀ c η))
      (fun (b : s.free) (η : FreeCoords s.free) => logHaar (toCoords (s.frame b.1) + η b)) with hpiece
  have hsm : ∀ i ∈ (Finset.univ : Finset (TorusBond n ⊕ s.free)), ContDiffAt ℝ 3 (piece i) p := by
    rintro (c | b) _
    · exact (hmean c).1
    · exact (hlogs b).1
  obtain ⟨d0, d1, d2⟩ := contDiffAt_sum_and_fderiv Finset.univ piece hsm
  have hg := logJacobian_sum_eventuallyEq s p h₀ hev
  have hcount : ∀ b : TorusBond (n * R.params.side), ∀ B : ℝ, 0 ≤ B →
      ∑ c : TorusBond n, (if IsNearBond R c b then B else 0) ≤ 8 * B := by
    intro b B hB
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h8 : (((Finset.univ.filter fun c : TorusBond n => IsNearBond R c b).card : ℕ) : ℝ) ≤ 8 := by
      exact_mod_cast card_isNearBond_le b
    exact mul_le_mul_of_nonneg_right h8 hB
  refine ⟨d0.congr_of_eventuallyEq hg, fun b X hX => ?_, fun b b' X X' hX hX' => ?_⟩
  · have hu : ‖(Pi.single b X : FreeCoords s.free)‖ = 1 := by
      rw [Pi.norm_single]
      exact hX
    rw [hg.fderiv_eq, d1, Fintype.sum_sum_type]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans
        (le_trans (Finset.sum_le_sum fun c _ => ?_) (hcount b.1 B₁ hB₁0))
      by_cases hn' : IsNearBond R c b.1
      · rw [if_pos hn']
        have h1 := (hmean c).2.1 (Pi.single b X)
        rw [hu, mul_one, ← hB₁] at h1
        exact h1
      · rw [if_neg hn']
        have h1 := ((hmean c).2.2.2 b hn' X 0).1
        simp only [hpiece, Sum.elim_inl]
        rw [h1, abs_zero]
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hz : ∀ b'' : s.free, |fderiv ℝ (piece (Sum.inr b'')) p (Pi.single b X)| ≤
          if b'' = b then Kh else 0 := by
        intro b''
        have h1 := (hlogs b'').2.1 (Pi.single b X)
        have et : piece (Sum.inr b'') = fun η => logHaar (toCoords (s.frame b''.1) + η b'') := rfl
        rw [et]
        by_cases e : b'' = b
        · subst e
          rw [if_pos rfl]
          simpa [hX] using h1
        · rw [if_neg e]
          simpa [Pi.single_eq_of_ne e] using h1
      refine (Finset.sum_le_sum fun b'' _ => hz b'').trans ?_
      simp
  · have hu : ‖(Pi.single b X : FreeCoords s.free)‖ = 1 := by
      rw [Pi.norm_single]
      exact hX
    have hv : ‖(Pi.single b' X' : FreeCoords s.free)‖ = 1 := by
      rw [Pi.norm_single]
      exact hX'
    rw [hg.fderiv.fderiv_eq, d2, Fintype.sum_sum_type]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · have hpiece1 : ∀ c : TorusBond n,
          |fderiv ℝ (fderiv ℝ (piece (Sum.inl c))) p (Pi.single b X) (Pi.single b' X')| ≤
          if IsNearBond R c b.1 ∧ IsNearBond R c b'.1 then B₂ else 0 := by
        intro c
        by_cases hn1 : IsNearBond R c b.1
        · by_cases hn2 : IsNearBond R c b'.1
          · rw [if_pos ⟨hn1, hn2⟩]
            have h1 := (hmean c).2.2.1 (Pi.single b X) (Pi.single b' X')
            rw [hu, hv, mul_one, mul_one, ← hB₂] at h1
            exact h1
          · rw [if_neg fun h => hn2 h.2]
            have h1 := ((hmean c).2.2.2 b' hn2 X' (Pi.single b X)).2.2
            simp only [hpiece, Sum.elim_inl]
            rw [h1, abs_zero]
        · rw [if_neg fun h => hn1 h.1]
          have h1 := ((hmean c).2.2.2 b hn1 X (Pi.single b' X')).2.1
          simp only [hpiece, Sum.elim_inl]
          rw [h1, abs_zero]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun c _ => hpiece1 c).trans ?_)
      by_cases hd : bondBlockDist (R := R) (n := n) b.1 b'.1 ≤ 1
      · rw [if_pos hd]
        refine le_trans (Finset.sum_le_sum fun c _ => ?_) (hcount b.1 B₂ hB₂0)
        by_cases hn1 : IsNearBond R c b.1
        · rw [if_pos hn1]
          split_ifs
          · exact le_rfl
          · exact hB₂0
        · rw [if_neg hn1, if_neg fun h => hn1 h.1]
      · rw [if_neg hd]
        refine le_of_eq (Finset.sum_eq_zero fun c _ => ?_)
        rw [if_neg fun h => hd (bondBlockDist_le_one_of_isNearBond h.1 h.2)]
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hz : ∀ b'' : s.free,
          |fderiv ℝ (fderiv ℝ (piece (Sum.inr b''))) p (Pi.single b X) (Pi.single b' X')| ≤
          if b'' = b ∧ b = b' then Kh else 0 := by
        intro b''
        have h1 := (hlogs b'').2.2 (Pi.single b X) (Pi.single b' X')
        have et : piece (Sum.inr b'') = fun η => logHaar (toCoords (s.frame b''.1) + η b'') := rfl
        rw [et]
        by_cases e : b'' = b
        · by_cases e' : b = b'
          · subst e
            subst e'
            rw [if_pos ⟨rfl, rfl⟩]
            simpa [hX, hX'] using h1
          · rw [if_neg fun h => e' h.2]
            have e2 : b'' ≠ b' := fun h => e' (e.symm.trans h)
            simpa [Pi.single_eq_of_ne e2] using h1
        · rw [if_neg fun h => e h.1]
          simpa [Pi.single_eq_of_ne e] using h1
      refine (Finset.sum_le_sum fun b'' _ => hz b'').trans ?_
      by_cases e : b = b'
      · simp [e]
      · simp [e]
end Final
theorem mixedSecondDeriv_eq_fderiv {N : ℕ} {free : Finset (TorusBond N)} {u : FreeCoords free → ℝ}
    {η : FreeCoords free} (h : ContDiffAt ℝ 2 u η) (b b' : free) (X X' : EuclideanSpace ℝ (Fin 3)) :
    mixedSecondDeriv u η b b' X X' = fderiv ℝ (fderiv ℝ u) η (Pi.single b X) (Pi.single b' X') := by apply _root_.YangMills.Construction.StepSettings.mixedSecondDeriv_eq_secondDeriv <;> assumption
theorem norm_toCoords (w : imaginaryQuaternions) : ‖toCoords w‖ = ‖(w : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianBound.norm_toCoords <;> assumption
theorem norm_frame_le {R : StepSetup} {n : ℕ} (hρ : 0 ≤ R.anchorRadius) (s : ChartSetting R n)
    (b : TorusBond (n * R.params.side)) : ‖(s.frame b : ℍ[ℝ])‖ ≤ R.anchorRadius := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianBound.norm_frame_le <;> assumption
end LogJacobianBounds
open LogJacobianBounds in
theorem logJacobianIsPotentialPiece_holds (hread : ContourMeanReadsTwoBlocks)
    (hgap : HaarGapDerivBound) (hweyl : WeylIntegrationFormula)
    (hsm : HaarGapSmoothStatement) (hlog : logHaarDensityContDiffOnBall) :
    LogJacobianIsPotentialPiece := by
  classical
  intro T hT
  obtain ⟨Kq, hKq, houter⟩ := exists_gapOfNorm_deriv_bounds hgap hweyl hsm
  obtain ⟨Ke, hKe, hexp⟩ := exists_bound_quaternionExp
  obtain ⟨Kh, hKh, hhaar⟩ := exists_logHaar_bounds hlog
  set B₁ : ℝ := Kq * (Ke * (9 * T.side : ℕ)) with hB₁
  set B₂ : ℝ := Kq * ((Ke * (9 * T.side : ℕ)) ^ 2 + (Ke * (9 * T.side : ℕ) + (Ke * (9 * T.side : ℕ)) ^ 2))
    with hB₂
  have hB₁0 : 0 ≤ B₁ := by positivity
  set Cnt : ℝ := 4 * (3 ^ 4 * (2 * (T.side : ℝ) + 1) ^ 4) with hCnt
  have hrt0 : 0 ≤ T.rt := hT.rt_pos.le
  have hE0 : 0 ≤ 8 * B₂ * Real.exp (2 * T.rt) := by positivity
  set C : ℝ := 8 * B₁ + Kh + (Cnt * (8 * B₂ * Real.exp (2 * T.rt)) + Kh) + 1 with hC
  refine ⟨C, 2, by positivity, fun y hy R hR n _ hn s hs => ?_⟩
  have hx : 2 ≤ R.coupling := hy.trans hR.le_coupling
  have ha1 := hT.a_ge
  have haL : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hLL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hrt : R.params.rt = T.rt := by rw [hR.params_eq]; rfl
  have hσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hσ0 : 0 < R.params.threshold := by
    rw [hσ]
    exact hT.σ_pos
  have hodd : Odd R.params.side := by
    rw [hLL]
    exact hT.L_odd
  have hn16 : 16 ≤ n := by
    have := hT.n₀_ge
    omega
  have hA : 2 ≤ R.params.coupling * R.coupling := by
    rw [haL]
    nlinarith
  have hr : 1 ≤ R.range := le_clusterRange_of_pow_le (m := 1) (by
    norm_num
    linarith)
  have hρAle : R.anchorRadius ≤ 1 := by
    rw [hR.anchorRadius_eq]
    exact hT.chain.2.2.2.2.1
  have hρA0 : 0 ≤ R.anchorRadius := by
    rw [hR.anchorRadius_eq]
    exact hT.chain.2.2.2.1.le
  have hρ : R.ballRadius ≤ 1 / 2 := by
    have e : R.ballRadius = T.ballRadius := by
      unfold StepSettings.StepSetup.ballRadius RenormalizationStepParameters.ParameterAssignment.ballRadius
      rw [hR.params_eq]
      rfl
    have h1 := hT.ρ_le
    have h2 := hT.chain.2.2.2.2.1
    have h3 := hT.chain.2.2.2.2.2.2.2.1 0
    have h4 := hT.σ_pos
    have h5 : 0 ≤ 2 * T.N 0 * T.threshold := by positivity
    rw [e]
    linarith
  have hpoint : ∀ (p : FreeCoords s.free), s.InBalls p → ∀ b : s.free,
      ‖(toImaginary (p b) : ℍ[ℝ])‖ ≤ 1 / 2 :=
    fun p hp b => (hp b).trans hρ
  have hsize : ∀ (p : FreeCoords s.free), s.InBalls p → ∀ b : s.free,
      ‖((s.frame b.1 + toImaginary (p b) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 2 := by
    intro p hp b
    have h1 := norm_add_le ((s.frame b.1 : imaginaryQuaternions) : ℍ[ℝ])
      ((toImaginary (p b) : imaginaryQuaternions) : ℍ[ℝ])
    have h2 := norm_frame_le hρA0 s b.1
    have h3 := hpoint p hp b
    have e : ((s.frame b.1 + toImaginary (p b) : imaginaryQuaternions) : ℍ[ℝ]) =
        ((s.frame b.1 : imaginaryQuaternions) : ℍ[ℝ]) + ((toImaginary (p b) : imaginaryQuaternions) : ℍ[ℝ]) := rfl
    rw [e]
    linarith
  have hsmall : ∀ (p : FreeCoords s.free), s.InBalls p → ∀ b : s.free,
      ‖toCoords (s.frame b.1) + p b‖ ≤ 3 / 2 := by
    intro p hp b
    have h1 := norm_add_le (toCoords (s.frame b.1)) (p b)
    rw [norm_toCoords] at h1
    have h2 := norm_frame_le hρA0 s b.1
    have h3 := hpoint p hp b
    rw [BondMeans.norm_toImaginary] at h3
    linarith
  have hB₁' : B₁ = Kq * (Ke * (9 * R.params.side : ℕ)) := by rw [hLL]
  have hB₂' : B₂ = Kq * ((Ke * (9 * R.params.side : ℕ)) ^ 2 +
      (Ke * (9 * R.params.side : ℕ) + (Ke * (9 * R.params.side : ℕ)) ^ 2)) := by rw [hLL]
  have pt := fun (p : FreeCoords s.free) (hp : s.InBalls p) =>
    logJacobian_bounds_at hread hodd hn16 s hs hKq hKe hKh hexp houter hhaar hA p hp (hsize p hp) (hsmall p hp)
      (stepHotLumps_eventually_eq s hs hσ0 hr
        (fun x i => (isTame_field s hKe hexp p (hsize p hp) x i).smooth.continuous) p hp)
      hB₁' hB₂'
  refine ⟨fun η hη => (pt η hη).1, ⟨fun b b' =>
    (if bondBlockDist (R := R) (n := n) b.1 b'.1 ≤ 1 then 8 * B₂ else 0) + (if b = b' then Kh else 0), ?_, ?_⟩, ?_⟩
  · intro η hη b b' X X' hX hX'
    rw [mixedSecondDeriv_eq_fderiv ((pt η hη).1.of_le (by norm_num))]
    exact (pt η hη).2.2 b b' X X' hX hX'
  · intro b
    have hexp1 : ∀ b' : s.free, ((if bondBlockDist (R := R) (n := n) b.1 b'.1 ≤ 1 then 8 * B₂ else 0) +
        (if b = b' then Kh else 0)) *
          Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) ≤
        (if bondBlockDist (R := R) (n := n) b.1 b'.1 ≤ 1 then 8 * B₂ * Real.exp (2 * T.rt) else 0) +
          (if b = b' then Kh else 0) := by
      intro b'
      rw [add_mul, hrt]
      refine add_le_add ?_ ?_
      · by_cases hd : bondBlockDist (R := R) (n := n) b.1 b'.1 ≤ 1
        · rw [if_pos hd, if_pos hd]
          have h1 : ((bondBlockDist (R := R) (n := n) b.1 b'.1 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hd
          have h2 : Real.exp (2 * T.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) ≤ Real.exp (2 * T.rt) := by
            apply Real.exp_le_exp.mpr
            nlinarith
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
        · rw [if_neg hd, if_neg hd, zero_mul]
      · by_cases e : b = b'
        · subst e
          have hz : bondBlockDist (R := R) (n := n) b.1 b.1 = 0 := by
            unfold bondBlockDist
            exact supDist_self _
          rw [if_pos rfl, hz]
          simp
        · rw [if_neg e, zero_mul]
    refine (Finset.sum_le_sum fun b' _ => hexp1 b').trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h1 := card_bondBlockDist_le_one s b
    have hLc : (R.params.side : ℝ) = T.side := by rw [hLL]
    rw [hLc] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 hE0
    have h3 : ∑ b' : s.free, (if b = b' then Kh else 0) = Kh := by simp
    rw [h3]
    rw [hC]
    have h4 : 0 ≤ 8 * B₁ + Kh := by positivity
    linarith
  · intro η hη b X hX
    have e : (fun τ : ℝ => ∑ Y : TorusSite n, s.logJacobian (s.field (Function.update η b (η b + τ • X)))
        (Function.update η b (η b + τ • X)) Y) = fun τ => ∑ Y : TorusSite n,
        s.logJacobian (s.field (η + τ • (Pi.single b X : FreeCoords s.free)))
          (η + τ • (Pi.single b X : FreeCoords s.free)) Y := by
      funext τ
      rw [_root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianBounds.update_add_smul_eq η b X τ]
    rw [e, deriv_along_line (f := fun η : FreeCoords s.free => ∑ Y : TorusSite n, s.logJacobian (s.field η) η Y)
      ((pt η hη).1.differentiableAt (by norm_num))]
    refine ((pt η hη).2.1 b X hX).trans ?_
    rw [hC]
    have h4 : 0 ≤ Cnt * (8 * B₂ * Real.exp (2 * T.rt)) + Kh := by positivity
    linarith
end ClusterExpansionOfAStep
end YangMills.Construction
end
