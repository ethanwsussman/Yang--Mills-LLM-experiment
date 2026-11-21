import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdChainAtEveryLevel.SizesAtAGoodCellProof
import YangMills.Construction.ColdChainAtEveryLevel.TotalUnderATurnedTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionAcrossFramesProof
import YangMills.Construction.ColdChainAtEveryLevel.HolonomiesOnTheHullOfABond
import YangMills.Construction.RunningCouplingSlope.ActionsNearTheFlatField
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages
section SecondDerivative
def secondDerivZero (h : ℝ → ℝ) : ℝ := deriv (deriv h) 0
theorem secondDerivZero_congr {h₁ h₂ : ℝ → ℝ} (e : h₁ =ᶠ[𝓝 0] h₂) : secondDerivZero h₁ = secondDerivZero h₂ := by
  unfold secondDerivZero
  exact (e.deriv).deriv_eq
theorem secondDerivZero_add {h₁ h₂ : ℝ → ℝ} (a₁ : AnalyticAt ℝ h₁ 0) (a₂ : AnalyticAt ℝ h₂ 0) :
    secondDerivZero (fun τ => h₁ τ + h₂ τ) = secondDerivZero h₁ + secondDerivZero h₂ := by apply _root_.YangMills.DeltaSharedProofs.p500418 <;> assumption
theorem secondDerivZero_const_mul {h : ℝ → ℝ} (c : ℝ) (a : AnalyticAt ℝ h 0) :
    secondDerivZero (fun τ => c * h τ) = c * secondDerivZero h := by apply _root_.YangMills.DeltaSharedProofs.p501758 <;> assumption
theorem secondDerivZero_sum {ι : Type} (s : Finset ι) (h : ι → ℝ → ℝ) (a : ∀ i ∈ s, AnalyticAt ℝ (h i) 0) :
    secondDerivZero (fun τ => ∑ i ∈ s, h i τ) = ∑ i ∈ s, secondDerivZero (h i) := by apply _root_.YangMills.DeltaSharedProofs.p500899 <;> assumption
theorem tendsto_div_sq_secondDerivZero {ψ : ℝ → ℝ} (h : AnalyticAt ℝ ψ 0) (h0 : ψ 0 = 0) (h1 : deriv ψ 0 = 0) :
    Tendsto (fun τ => ψ τ / τ ^ 2) (𝓝[≠] 0) (𝓝 (secondDerivZero ψ / 2)) := by
  have hd : HasDerivAt (deriv ψ) (secondDerivZero ψ) 0 := h.deriv.differentiableAt.hasDerivAt
  have hs : Tendsto (fun τ => deriv ψ τ / τ) (𝓝[≠] 0) (𝓝 (secondDerivZero ψ)) := by
    have := hasDerivAt_iff_tendsto_slope.1 hd
    refine this.congr fun τ => ?_
    simp [slope, h1, div_eq_inv_mul]
  have hdiv : Tendsto (fun τ => deriv ψ τ / (2 * τ)) (𝓝[≠] 0) (𝓝 (secondDerivZero ψ / 2)) := by
    refine (hs.div_const 2).congr fun τ => ?_
    rw [div_div, mul_comm]
  refine HasDerivAt.lhopital_zero_nhdsNE (f' := deriv ψ) (g' := fun τ => 2 * τ) ?_ ?_ ?_ ?_ ?_ hdiv
  · filter_upwards [nhdsWithin_le_nhds h.eventually_analyticAt] with τ b
    exact b.differentiableAt.hasDerivAt
  · refine Eventually.of_forall fun τ => ?_
    simpa using hasDerivAt_pow 2 τ
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact mul_ne_zero two_ne_zero hτ
  · have := h.continuousAt.tendsto
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have : Tendsto (fun τ : ℝ => τ ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) := (continuous_pow 2).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
theorem deriv_zero_of_nonneg_of_eq_zero {ψ : ℝ → ℝ} (hn : ∀ᶠ τ in 𝓝 0, 0 ≤ ψ τ) (h0 : ψ 0 = 0) : deriv ψ 0 = 0 := by
  have : IsLocalMin ψ 0 := by
    filter_upwards [hn] with τ hτ
    rw [h0]
    exact hτ
  exact this.deriv_eq_zero
theorem secondDerivZero_nonneg {ψ : ℝ → ℝ} (h : AnalyticAt ℝ ψ 0) (hn : ∀ᶠ τ in 𝓝 0, 0 ≤ ψ τ) (h0 : ψ 0 = 0) :
    0 ≤ secondDerivZero ψ := by
  have ht := tendsto_div_sq_secondDerivZero h h0 (deriv_zero_of_nonneg_of_eq_zero hn h0)
  have : 0 ≤ secondDerivZero ψ / 2 := by
    refine ge_of_tendsto ht ?_
    filter_upwards [nhdsWithin_le_nhds hn] with τ hτ
    positivity
  linarith
theorem secondDerivZero_comp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {g : E → ℝ} {p : E}
    {γ : ℝ → E} (hg : AnalyticAt ℝ g p) (hc : fderiv ℝ g p = 0) (hγ : AnalyticAt ℝ γ 0) (h0 : γ 0 = p) :
    secondDerivZero (fun τ => g (γ τ)) = fderiv ℝ (fderiv ℝ g) p (deriv γ 0) (deriv γ 0) := by
  unfold secondDerivZero
  have hcont : ContinuousAt γ 0 := hγ.continuousAt
  have hgg : ∀ᶠ τ in 𝓝 (0 : ℝ), AnalyticAt ℝ g (γ τ) := by
    have := hg.eventually_analyticAt
    rw [← h0] at this
    exact hcont.eventually this
  have e : deriv (fun τ => g (γ τ)) =ᶠ[𝓝 0] fun τ => fderiv ℝ g (γ τ) (deriv γ τ) := by
    filter_upwards [hgg, hγ.eventually_analyticAt] with τ b₁ b₂
    exact (b₁.differentiableAt.hasFDerivAt.comp_hasDerivAt τ b₂.differentiableAt.hasDerivAt).deriv
  rw [e.deriv_eq]
  have d1 : HasDerivAt (fun τ => fderiv ℝ g (γ τ)) (fderiv ℝ (fderiv ℝ g) p (deriv γ 0)) 0 := by
    have a : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) p) (γ 0) := by
      rw [h0]
      exact hg.fderiv.differentiableAt.hasFDerivAt
    exact a.comp_hasDerivAt 0 hγ.differentiableAt.hasDerivAt
  have d2 : HasDerivAt (deriv γ) (deriv (deriv γ) 0) 0 := hγ.deriv.differentiableAt.hasDerivAt
  have := (d1.clm_apply d2).deriv
  rw [this, h0, hc]
  simp
end SecondDerivative
section Defect
def reDefect (q : ℍ[ℝ]) : ℝ := ‖q‖ - q.re
theorem quat_re_le_norm (q : ℍ[ℝ]) : q.re ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.quaternion_re_le_norm <;> assumption
theorem reDefect_nonneg (q : ℍ[ℝ]) : 0 ≤ reDefect q := sub_nonneg.2 (quat_re_le_norm q)
theorem reDefect_mul_norm_add_re (q : ℍ[ℝ]) : reDefect q * (‖q‖ + q.re) = ‖q.im‖ ^ 2 := by
  have h : q.re ^ 2 + ‖q.im‖ ^ 2 = ‖q‖ ^ 2 := GaugeFixing.re_sq_add_norm_im_sq q
  unfold reDefect
  nlinarith
theorem tendsto_reDefect_div_sq {Z : ℝ → ℍ[ℝ]} {d : ℍ[ℝ]} (hZ : HasDerivAt Z d 0) (h1 : Z 0 = 1) :
    Tendsto (fun τ => reDefect (Z τ) / τ ^ 2) (𝓝[≠] 0) (𝓝 (‖d.im‖ ^ 2 / 2)) := by
  have hc : ContinuousAt Z 0 := hZ.continuousAt
  have hD : Tendsto (fun τ => ‖Z τ‖ + (Z τ).re) (𝓝 0) (𝓝 2) := by
    have a : Tendsto Z (𝓝 0) (𝓝 1) := by simpa [ContinuousAt, h1] using hc
    have b : Tendsto (fun τ => ‖Z τ‖) (𝓝 0) (𝓝 1) := by simpa using a.norm
    have c : Tendsto (fun τ => (Z τ).re) (𝓝 0) (𝓝 1) := by
      have c' : Tendsto (fun τ => (Z τ).re) (𝓝 0) (𝓝 (1 : ℍ[ℝ]).re) :=
        (Quaternion.continuous_re.tendsto (1 : ℍ[ℝ])).comp a
      simpa using c'
    have := b.add c
    norm_num at this
    exact this
  have hs : Tendsto (slope Z 0) (𝓝[≠] 0) (𝓝 d) := hasDerivAt_iff_tendsto_slope.1 hZ
  have hi : Tendsto (fun τ => (slope Z 0 τ).im) (𝓝[≠] 0) (𝓝 d.im) :=
    (Quaternion.continuous_im.tendsto d).comp hs
  have hq : Tendsto (fun τ => ‖(slope Z 0 τ).im‖ ^ 2 / (‖Z τ‖ + (Z τ).re)) (𝓝[≠] 0) (𝓝 (‖d.im‖ ^ 2 / 2)) :=
    (hi.norm.pow 2).div (hD.mono_left nhdsWithin_le_nhds) (by norm_num)
  refine hq.congr' ?_
  have hpos : ∀ᶠ τ in 𝓝[≠] (0 : ℝ), 0 < ‖Z τ‖ + (Z τ).re :=
    (hD.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds (by norm_num))
  filter_upwards [hpos, self_mem_nhdsWithin] with τ hp hτ
  have hτ' : τ ≠ 0 := hτ
  have e : (slope Z 0 τ).im = τ⁻¹ • (Z τ).im := by
    simp only [slope, vsub_eq_sub, sub_zero, h1]
    ext <;> simp
  rw [e, norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, inv_pow, sq_abs, ← reDefect_mul_norm_add_re]
  field_simp
theorem secondDerivZero_reDefect {Z : ℝ → ℍ[ℝ]} {d : ℍ[ℝ]} (hZ : HasDerivAt Z d 0) (h1 : Z 0 = 1)
    (a : AnalyticAt ℝ (fun τ => reDefect (Z τ)) 0) :
    secondDerivZero (fun τ => reDefect (Z τ)) = ‖d.im‖ ^ 2 := by
  have h0 : reDefect (Z 0) = 0 := by simp [reDefect, h1]
  have hn : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 ≤ reDefect (Z τ) := Eventually.of_forall fun τ => reDefect_nonneg _
  have t1 := tendsto_div_sq_secondDerivZero a h0 (deriv_zero_of_nonneg_of_eq_zero hn h0)
  have t2 := tendsto_reDefect_div_sq hZ h1
  have := tendsto_nhds_unique t1 t2
  linarith
end Defect
section Families
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : BlockFrame}
def IsAnalyticFieldFamily {k : ℕ} (φ : E → F.GaugeField k) (e : E) : Prop :=
  ∀ x i, AnalyticAt ℝ (fun y => ((φ y x i : UnitQuaternion) : ℍ[ℝ])) e
theorem IsAnalyticFieldFamily.analyticAt_link {k : ℕ} {φ : E → F.GaugeField k} {e : E} (h : IsAnalyticFieldFamily φ e)
    (x : F.Site k) (st : PathStep) :
    AnalyticAt ℝ (fun y => ((linkValue (φ y) x st : UnitQuaternion) : ℍ[ℝ])) e := by
  unfold linkValue
  cases hs : st.2
  · simp only [Bool.false_eq_true, if_false, coe_inv_unitQuaternion]
    exact analyticAt_quat_star (h (x - unitStep k st.1) st.1)
  · simpa using h x st.1
theorem IsAnalyticFieldFamily.analyticAt_path {k : ℕ} {φ : E → F.GaugeField k} {e : E} (h : IsAnalyticFieldFamily φ e)
    (l : List PathStep) :
    ∀ x, AnalyticAt ℝ (fun y => ((pathHolonomy (φ y) x l : UnitQuaternion) : ℍ[ℝ])) e := by
  induction l with
  | nil => intro x; simpa [pathHolonomy] using analyticAt_const
  | cons st r ih =>
    intro x
    exact (h.analyticAt_link x st).mul (ih _)
theorem IsAnalyticFieldFamily.analyticAt_contourAverage {j : ℕ} {φ : E → F.GaugeField j} {e : E}
    (h : IsAnalyticFieldFamily φ e) (c : F.Site (j + 1) × Fin 4) :
    AnalyticAt ℝ (fun y => contourAverage (φ y) c) e := by
  unfold contourAverage
  have hs : AnalyticAt ℝ (fun y => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy (φ y) (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])) e :=
    Finset.analyticAt_fun_sum _ fun _ _ => Finset.analyticAt_fun_sum _ fun _ _ => h.analyticAt_path _ _
  exact (analyticAt_const : AnalyticAt ℝ (fun _ : E => (1 / (24 * (F.blockSide : ℝ) ^ 4))) e).smul hs
theorem IsAnalyticFieldFamily.analyticAt_blockFit {j : ℕ} {φ : E → F.GaugeField j} {φ' : E → F.GaugeField (j + 1)}
    {e : E} (h : IsAnalyticFieldFamily φ e) (h' : IsAnalyticFieldFamily φ' e) (c : F.Site (j + 1) × Fin 4)
    (h0 : contourAverage (φ e) c ≠ 0) : AnalyticAt ℝ (fun y => blockFit (φ y) (φ' y) c) e := by
  unfold blockFit
  exact (analyticAt_quat_norm (h.analyticAt_contourAverage c) h0).sub
    (analyticAt_quat_re ((h.analyticAt_contourAverage c).mul (analyticAt_quat_star (h' c.1 c.2))))
theorem continuous_pathHolonomy {X : Type} [TopologicalSpace X] {k : ℕ} {φ : X → F.GaugeField k} (h : Continuous φ)
    (l : List PathStep) :
    ∀ x, Continuous fun y => ((pathHolonomy (φ y) x l : UnitQuaternion) : ℍ[ℝ]) := by
  have hb : ∀ (x : F.Site k) (i : Fin 4), Continuous fun y => ((φ y x i : UnitQuaternion) : ℍ[ℝ]) := fun x i =>
    continuous_subtype_val.comp ((continuous_apply i).comp ((continuous_apply x).comp h))
  have hst : ∀ (x : F.Site k) (st : PathStep),
      Continuous fun y => ((linkValue (φ y) x st : UnitQuaternion) : ℍ[ℝ]) := by
    intro x st
    unfold linkValue
    cases hs : st.2
    · simp only [Bool.false_eq_true, if_false, coe_inv_unitQuaternion]
      exact quatStarCLM.continuous.comp (hb (x - unitStep k st.1) st.1)
    · simpa using hb x st.1
  induction l with
  | nil => intro x; simpa [pathHolonomy] using continuous_const
  | cons st r ih =>
    intro x
    exact (hst x st).mul (ih _)
theorem continuous_blockFit {X : Type} [TopologicalSpace X] {j : ℕ} {φ : X → F.GaugeField j}
    {φ' : X → F.GaugeField (j + 1)} (h : Continuous φ) (h' : Continuous φ') (c : F.Site (j + 1) × Fin 4) :
    Continuous fun y => blockFit (φ y) (φ' y) c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.continuous_blockFit <;> assumption
end Families
section Curves
variable {F : BlockFrame} {k : ℕ}
theorem star_coe_imaginary (b : imaginaryQuaternions) : star (b : ℍ[ℝ]) = -(b : ℍ[ℝ]) := by apply _root_.YangMills.Construction.GaugeMotions.star_coe_imaginary <;> assumption
structure IsCurveThroughTrivial (c : ℝ → F.GaugeField k) (β : F.Site k → Fin 4 → imaginaryQuaternions) : Prop where
  at_zero : c 0 = trivialBlockField F k
  hasDerivAt : ∀ x i, HasDerivAt (fun τ => ((c τ x i : UnitQuaternion) : ℍ[ℝ])) (β x i : ℍ[ℝ]) 0
def linkForm (β : F.Site k → Fin 4 → imaginaryQuaternions) (x : F.Site k) (st : PathStep) : imaginaryQuaternions :=
  if st.2 then β x st.1 else - β (x - unitStep k st.1) st.1
def formAlongPath (β : F.Site k → Fin 4 → imaginaryQuaternions) : F.Site k → List PathStep → imaginaryQuaternions
  | _, [] => 0
  | x, st :: r => linkForm β x st + formAlongPath β (x + stepDisplacement k st) r
theorem linkValue_trivial (x : F.Site k) (st : PathStep) : linkValue (trivialBlockField F k) x st = 1 := by
  unfold linkValue trivialBlockField
  cases st.2 <;> simp
theorem pathHolonomy_trivial (l : List PathStep) :
    ∀ x : F.Site k, pathHolonomy (trivialBlockField F k) x l = 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathHolonomy_one <;> assumption
theorem IsCurveThroughTrivial.hasDerivAt_link {c : ℝ → F.GaugeField k} {β : F.Site k → Fin 4 → imaginaryQuaternions}
    (h : IsCurveThroughTrivial c β) (x : F.Site k) (st : PathStep) :
    HasDerivAt (fun τ => ((linkValue (c τ) x st : UnitQuaternion) : ℍ[ℝ])) (linkForm β x st : ℍ[ℝ]) 0 := by
  unfold linkValue linkForm
  cases hs : st.2
  · have h1 := quatStarCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h.hasDerivAt (x - unitStep k st.1) st.1)
    have e : quatStarCLM ((β (x - unitStep k st.1) st.1 : imaginaryQuaternions) : ℍ[ℝ]) =
        ((- β (x - unitStep k st.1) st.1 : imaginaryQuaternions) : ℍ[ℝ]) := by
      simp [star_coe_imaginary]
    rw [e] at h1
    simp only [Bool.false_eq_true, if_false, coe_inv_unitQuaternion]
    exact h1
  · simpa using h.hasDerivAt x st.1
theorem IsCurveThroughTrivial.hasDerivAt_path {c : ℝ → F.GaugeField k} {β : F.Site k → Fin 4 → imaginaryQuaternions}
    (h : IsCurveThroughTrivial c β) (l : List PathStep) :
    ∀ x, HasDerivAt (fun τ => ((pathHolonomy (c τ) x l : UnitQuaternion) : ℍ[ℝ])) (formAlongPath β x l : ℍ[ℝ]) 0 := by
  induction l with
  | nil => intro x; simpa [pathHolonomy, formAlongPath] using hasDerivAt_const (0 : ℝ) (1 : ℍ[ℝ])
  | cons st r ih =>
    intro x
    have := (h.hasDerivAt_link x st).fun_mul (ih (x + stepDisplacement k st))
    simp only [h.at_zero, linkValue_trivial, pathHolonomy_trivial] at this
    simpa [formAlongPath, pathHolonomy] using this
open LatticePaths
theorem siteOfCoords_add_stepDisplacement (z : (Fin 4 → ℤ)) (st : PathStep) :
    siteOfCoords (F := F) k z + stepDisplacement k st = siteOfCoords k (z + FlatPairing.stepDisplacement st) := by apply _root_.YangMills.DeltaSharedProofs.p4150 <;> assumption
theorem linkValue_of_pure {W : F.GaugeField k} {g : (Fin 4 → ℤ) → UnitQuaternion}
    (h : ∀ z i, W (siteOfCoords k z) i = g z * (g (z + Pi.single i 1))⁻¹) (z : (Fin 4 → ℤ)) (st : PathStep) :
    linkValue W (siteOfCoords k z) st = g z * (g (z + FlatPairing.stepDisplacement st))⁻¹ := by
  unfold linkValue FlatPairing.stepDisplacement
  cases hs : st.2
  · simp only [Bool.false_eq_true, if_false]
    have e : siteOfCoords (F := F) k z - unitStep k st.1 =
        siteOfCoords k (z - LatticeFractionalIntegration.basisVector st.1) := by
      rw [siteOfCoords_sub, unitStep_eq]
    rw [e, h, mul_inv_rev, inv_inv]
    have e2 : z - LatticeFractionalIntegration.basisVector st.1 + Pi.single st.1 1 = z := by
      simp [LatticeFractionalIntegration.basisVector]
    rw [e2, sub_eq_add_neg]
  · simpa [LatticeFractionalIntegration.basisVector] using h z st.1
theorem pathHolonomy_of_pure {W : F.GaugeField k} {g : (Fin 4 → ℤ) → UnitQuaternion}
    (h : ∀ z i, W (siteOfCoords k z) i = g z * (g (z + Pi.single i 1))⁻¹) (l : List PathStep) :
    ∀ z, pathHolonomy W (siteOfCoords k z) l = g z * (g (endpoint z l))⁻¹ := by
  induction l with
  | nil => intro z; simp [pathHolonomy, endpoint]
  | cons st r ih =>
    intro z
    simp only [pathHolonomy, endpoint]
    rw [siteOfCoords_add_stepDisplacement, ih, linkValue_of_pure h]
    group
theorem linkForm_of_exact {β : F.Site k → Fin 4 → imaginaryQuaternions} {l : (Fin 4 → ℤ) → imaginaryQuaternions}
    (h : ∀ z i, β (siteOfCoords k z) i = l z - l (z + Pi.single i 1)) (z : (Fin 4 → ℤ)) (st : PathStep) :
    linkForm β (siteOfCoords k z) st = l z - l (z + FlatPairing.stepDisplacement st) := by
  unfold linkForm FlatPairing.stepDisplacement
  cases hs : st.2
  · simp only [Bool.false_eq_true, if_false]
    have e : siteOfCoords (F := F) k z - unitStep k st.1 =
        siteOfCoords k (z - LatticeFractionalIntegration.basisVector st.1) := by
      rw [siteOfCoords_sub, unitStep_eq]
    rw [e, h]
    have e2 : z - LatticeFractionalIntegration.basisVector st.1 + Pi.single st.1 1 = z := by
      simp [LatticeFractionalIntegration.basisVector]
    rw [e2, neg_sub, sub_eq_add_neg z]
  · simpa [LatticeFractionalIntegration.basisVector] using h z st.1
theorem formAlongPath_of_exact {β : F.Site k → Fin 4 → imaginaryQuaternions} {l : (Fin 4 → ℤ) → imaginaryQuaternions}
    (h : ∀ z i, β (siteOfCoords k z) i = l z - l (z + Pi.single i 1)) (p : List PathStep) :
    ∀ z, formAlongPath β (siteOfCoords k z) p = l z - l (endpoint z p) := by
  induction p with
  | nil => intro z; simp [formAlongPath, endpoint]
  | cons st r ih =>
    intro z
    simp only [formAlongPath, endpoint]
    rw [siteOfCoords_add_stepDisplacement, ih, linkForm_of_exact h]
    abel
theorem endpoint_bondContour (z : (Fin 4 → ℤ)) (L : ℕ) (o : (Fin 4 → ℤ)) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    endpoint z (bondContour L o π i) = z + (L : ℤ) • LatticeFractionalIntegration.basisVector i := by
  unfold bondContour
  rw [endpoint_append, endpoint_append, endpoint_replicate]
  have e : FlatPairing.stepDisplacement (i, true) = LatticeFractionalIntegration.basisVector i := by
    simp [FlatPairing.stepDisplacement]
  rw [e, endpoint_add, endpoint_reversePath]
theorem average_const (hL : Odd F.blockSide) (q : ℍ[ℝ]) :
    (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ _h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), q = q := by apply _root_.YangMills.Construction.BondHull.smul_sum_perm_const <;> assumption
def blockCoords (L : ℕ) (y : (Fin 4 → ℤ)) : (Fin 4 → ℤ) := fun m => (L : ℤ) * y m
theorem blockCoords_add_single (L : ℕ) (y : (Fin 4 → ℤ)) (i : Fin 4) :
    blockCoords L (y + Pi.single i 1) = blockCoords L y + (L : ℤ) • LatticeFractionalIntegration.basisVector i := by
  funext m
  simp [blockCoords, LatticeFractionalIntegration.basisVector, mul_add]
theorem contourAverage_trivial (hL : Odd F.blockSide) {j : ℕ} (c : F.Site (j + 1) × Fin 4) :
    contourAverage (trivialBlockField F j) c = 1 := by apply _root_.YangMills.Construction.BlockAverages.LowCostPatch.contourAverage_trivialField <;> assumption
theorem contourAverage_of_pure {j : ℕ} (hj : j < F.top) (hL : Odd F.blockSide) {W : F.GaugeField j}
    {g : (Fin 4 → ℤ) → UnitQuaternion}
    (h : ∀ z i, W (siteOfCoords j z) i = g z * (g (z + Pi.single i 1))⁻¹) (y : (Fin 4 → ℤ)) (i : Fin 4) :
    contourAverage W (siteOfCoords (j + 1) y, i) =
      ((g (blockCoords F.blockSide y) * (g (blockCoords F.blockSide (y + Pi.single i 1)))⁻¹ : UnitQuaternion) :
        ℍ[ℝ]) := by
  unfold contourAverage
  have e : refineSite (siteOfCoords (F := F) (j + 1) y) = siteOfCoords j (blockCoords F.blockSide y) :=
    BlockLines.refineSite_siteOfCoords hj y
  simp only [e, pathHolonomy_of_pure h, endpoint_bondContour, blockCoords_add_single]
  exact average_const hL _
theorem IsCurveThroughTrivial.hasDerivAt_contourAverage_of_exact {j : ℕ} (hj : j < F.top) (hL : Odd F.blockSide)
    {c : ℝ → F.GaugeField j} {β : F.Site j → Fin 4 → imaginaryQuaternions} (hc : IsCurveThroughTrivial c β)
    {l : (Fin 4 → ℤ) → imaginaryQuaternions}
    (h : ∀ z i, β (siteOfCoords j z) i = l z - l (z + Pi.single i 1)) (y : (Fin 4 → ℤ)) (i : Fin 4) :
    HasDerivAt (fun τ => contourAverage (c τ) (siteOfCoords (j + 1) y, i))
      ((l (blockCoords F.blockSide y) - l (blockCoords F.blockSide (y + Pi.single i 1)) : imaginaryQuaternions) :
        ℍ[ℝ]) 0 := by
  unfold contourAverage
  have e : refineSite (siteOfCoords (F := F) (j + 1) y) = siteOfCoords j (blockCoords F.blockSide y) :=
    BlockLines.refineSite_siteOfCoords hj y
  simp only [e]
  set D : ℍ[ℝ] := ((l (blockCoords F.blockSide y) - l (blockCoords F.blockSide (y + Pi.single i 1)) :
    imaginaryQuaternions) : ℍ[ℝ]) with hD
  have hs : HasDerivAt (fun τ => ∑ o ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy (c τ) (siteOfCoords j (blockCoords F.blockSide y)) (bondContour F.blockSide o π i) :
        UnitQuaternion) : ℍ[ℝ]))
      (∑ _o ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), D) 0 := by
    refine HasDerivAt.fun_sum fun o _ => HasDerivAt.fun_sum fun π _ => ?_
    have := hc.hasDerivAt_path (bondContour F.blockSide o π i) (siteOfCoords j (blockCoords F.blockSide y))
    rw [formAlongPath_of_exact h, endpoint_bondContour, ← blockCoords_add_single] at this
    exact this
  have := hs.const_smul (1 / (24 * (F.blockSide : ℝ) ^ 4))
  rwa [average_const hL] at this
theorem blockFit_eq_reDefect {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    blockFit X X' c = reDefect (contourAverage X c * (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
  unfold blockFit reDefect
  rw [norm_mul, norm_coe_unitQuaternion, mul_one]
theorem one_sub_re_eq_reDefect (g : UnitQuaternion) : 1 - (g : ℍ[ℝ]).re = reDefect (g : ℍ[ℝ]) := by
  unfold reDefect
  rw [norm_coe_unitQuaternion]
theorem hasDerivAt_normalize_one_add_smul (b : imaginaryQuaternions) :
    HasDerivAt (fun τ : ℝ => ((normalize (1 + τ • (b : ℍ[ℝ])) : UnitQuaternion) : ℍ[ℝ])) (b : ℍ[ℝ]) 0 := by
  have hb : (b : ℍ[ℝ]).re = 0 := b.2
  set q : ℝ → ℍ[ℝ] := fun τ => 1 + τ • (b : ℍ[ℝ]) with hq
  have hq1 : HasDerivAt q (b : ℍ[ℝ]) 0 := by
    have h2 : HasDerivAt (fun τ : ℝ => τ • (b : ℍ[ℝ])) ((1 : ℝ) • (b : ℍ[ℝ])) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const (b : ℍ[ℝ])
    rw [one_smul] at h2
    exact h2.const_add (1 : ℍ[ℝ])
  have hqa : AnalyticAt ℝ q 0 := analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hq0 : q 0 = 1 := by simp [hq]
  have hm : AnalyticAt ℝ (fun τ => ‖q τ‖) 0 := analyticAt_quat_norm hqa (by rw [hq0]; exact one_ne_zero)
  have hm0 : ‖q 0‖ = 1 := by rw [hq0]; simp
  have hsq : ∀ τ, ‖q τ‖ ^ 2 = 1 + τ ^ 2 * ‖(b : ℍ[ℝ])‖ ^ 2 := by
    intro τ
    have h := GaugeFixing.re_sq_add_norm_im_sq (q τ)
    have h' := GaugeFixing.re_sq_add_norm_im_sq (b : ℍ[ℝ])
    have e1 : (q τ).re = 1 := by simp [hq, hb]
    have e2 : (q τ).im = τ • (b : ℍ[ℝ]).im := by
      ext <;> simp [hq]
    rw [e1, e2, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h
    rw [hb] at h'
    nlinarith
  have d1 : HasDerivAt (fun τ => ‖q τ‖) (deriv (fun τ => ‖q τ‖) 0) 0 := hm.differentiableAt.hasDerivAt
  have d2 : HasDerivAt (fun τ => ‖q τ‖ ^ 2) (2 * deriv (fun τ => ‖q τ‖) 0) 0 := by
    have := d1.fun_pow 2
    simpa [hm0] using this
  have d3 : HasDerivAt (fun τ => ‖q τ‖ ^ 2) 0 0 := by
    have e : (fun τ => ‖q τ‖ ^ 2) = fun τ : ℝ => 1 + τ ^ 2 * ‖(b : ℍ[ℝ])‖ ^ 2 := funext hsq
    rw [e]
    have := ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (‖(b : ℍ[ℝ])‖ ^ 2)).const_add (1 : ℝ)
    simpa using this
  have d0 : deriv (fun τ => ‖q τ‖) 0 = 0 := by
    have := d2.unique d3
    linarith
  rw [d0] at d1
  have hi : HasDerivAt (fun τ => ‖q τ‖⁻¹) 0 0 := by
    have := d1.fun_inv (by rw [hm0]; exact one_ne_zero)
    simpa using this
  have hp := hi.fun_smul hq1
  have hfin : HasDerivAt (fun τ => ‖q τ‖⁻¹ • q τ) (b : ℍ[ℝ]) 0 := by
    simpa [hm0, hq0] using hp
  refine hfin.congr_of_eventuallyEq ?_
  have hc : ContinuousAt q 0 := hq1.continuousAt
  filter_upwards [hc.eventually_ne (by rw [hq0]; exact one_ne_zero : q 0 ≠ 0)] with τ hτ
  exact coe_normalize hτ
theorem isCurveThroughTrivial_fieldAlongLine (B : F.Site k → Fin 4 → imaginaryQuaternions) :
    IsCurveThroughTrivial (fieldAlongLine (F := F) B) B where
  at_zero := by
    funext x i
    have : normalize (1 : ℍ[ℝ]) = 1 := normalize_coe (1 : UnitQuaternion)
    simp [fieldAlongLine, fieldOfQuaternions, trivialBlockField, this]
  hasDerivAt := fun x i => hasDerivAt_normalize_one_add_smul (B x i)
end Curves
section LatticeMoves
open GaugeFixing
variable {α : Type}
theorem apply_single_eq_of_line_moves (u : (Fin 4 → ℤ) → α) (M : ℤ) (i : Fin 4) (b : Fin 4 → ℤ)
    (hstep : ∀ s : ℤ, -M ≤ s → s < M → u (b + Pi.single i s) = u (b + Pi.single i (s + 1)))
    (s : ℤ) (hs : |s| ≤ M) : u (b + Pi.single i s) = u b := by
  have hpos : ∀ n : ℕ, (n : ℤ) ≤ M → u (b + Pi.single i (n : ℤ)) = u b := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      push_cast at hn ⊢
      rw [← hstep n (by omega) (by omega)]
      exact ih (by omega)
  have hneg : ∀ n : ℕ, (n : ℤ) ≤ M → u (b + Pi.single i (-(n : ℤ))) = u b := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      push_cast at hn ⊢
      have e : -(n : ℤ) = -((n : ℤ) + 1) + 1 := by ring
      rw [hstep (-((n : ℤ) + 1)) (by omega) (by omega), ← e]
      exact ih (by omega)
  have h := abs_le.1 hs
  rcases le_or_gt 0 s with h0 | h0
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    exact hpos n h.2
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -s)
    have e : s = -(n : ℤ) := by omega
    rw [e]
    exact hneg n (by omega)
def leadingCoords (o : Fin 4 → ℤ) (k : ℕ) : Fin 4 → ℤ := fun l => if (l : ℕ) < k then o l else 0
theorem apply_eq_apply_zero_of_axis_moves (u : (Fin 4 → ℤ) → α) (o : Fin 4 → ℤ)
    (hline : ∀ (i : Fin 4) (b : Fin 4 → ℤ), (∀ l, i ≤ l → b l = 0) → (∀ l, b l = 0 ∨ b l = o l) →
      u (b + Pi.single i (o i)) = u b) : u o = u 0 := by
  have hk : ∀ k : ℕ, k ≤ 4 → u (leadingCoords o k) = u 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      have e0 : leadingCoords o 0 = 0 := by
        funext l
        simp [leadingCoords]
      rw [e0]
    | succ k ih =>
      intro hk
      have hk' : k < 4 := by omega
      have e : leadingCoords o (k + 1) = leadingCoords o k + Pi.single ⟨k, hk'⟩ (o ⟨k, hk'⟩) := by
        funext l
        by_cases h1 : (l : ℕ) < k
        · have h2 : l ≠ ⟨k, hk'⟩ := fun e => by rw [e] at h1; simp at h1
          simp [leadingCoords, h1, Nat.lt_succ_of_lt h1, h2]
        · by_cases h2 : (l : ℕ) = k
          · have h3 : l = ⟨k, hk'⟩ := Fin.ext h2
            subst h3
            simp [leadingCoords]
          · have h3 : l ≠ ⟨k, hk'⟩ := fun e => h2 (by rw [e])
            have h4 : ¬ (l : ℕ) < k + 1 := by omega
            simp [leadingCoords, h1, h4, h3]
      rw [e, hline ⟨k, hk'⟩ (leadingCoords o k) ?_ ?_, ih (by omega)]
      · intro l hl
        have : ¬ (l : ℕ) < k := by
          have : k ≤ (l : ℕ) := hl
          omega
        simp [leadingCoords, this]
      · intro l
        by_cases h1 : (l : ℕ) < k <;> simp [leadingCoords, h1]
  have e : leadingCoords o 4 = o := by
    funext l
    simp [leadingCoords, l.2]
  rw [← hk 4 le_rfl, e]
theorem apply_eq_apply_zero_of_tree_moves (L : ℕ) (u : (Fin 4 → ℤ) → α)
    (h : ∀ o i, o ∈ centredCube L → o + Pi.single i 1 ∈ centredCube L → (∀ l, i < l → o l = 0) →
      u o = u (o + Pi.single i 1)) :
    ∀ o ∈ centredCube L, u o = u 0 := by
  intro o ho
  refine apply_eq_apply_zero_of_axis_moves u o fun i b hb hbo => ?_
  have hbi : b i = 0 := hb i le_rfl
  have hbc : ∀ l, -halfSide L ≤ b l ∧ b l ≤ halfSide L := by
    intro l
    have h1 := mem_centredCube.1 ho l
    have h2 := mem_centredCube.1 ho i
    rcases hbo l with e | e
    · rw [e]
      have : 0 ≤ halfSide L := by
        have := h1.1
        have := h1.2
        omega
      omega
    · rw [e]
      exact h1
  refine apply_single_eq_of_line_moves u (halfSide L) i b (fun s h1 h2 => ?_) (o i) ?_
  · have e : b + Pi.single i (s + 1) = b + Pi.single i s + Pi.single i 1 := by
      funext l
      by_cases hl : l = i
      · subst hl; simp [add_assoc]
      · simp [hl]
    rw [e]
    have coord_val : ∀ (t : ℤ) (l : Fin 4), (b + Pi.single i t : Fin 4 → ℤ) l = if l = i then t else b l := by
      intro t l
      by_cases hl : l = i
      · subst hl; simp [hbi]
      · simp [hl]
    refine h _ i ?_ ?_ ?_
    · refine mem_centredCube.2 fun l => ?_
      rw [coord_val]
      split_ifs with hl
      · omega
      · exact hbc l
    · refine mem_centredCube.2 fun l => ?_
      rw [← e, coord_val]
      split_ifs with hl
      · omega
      · exact hbc l
    · intro l hl
      rw [coord_val, if_neg hl.ne', hb l hl.le]
  · have := mem_centredCube.1 ho i
    exact abs_le.2 this
theorem apply_eq_apply_zero_of_unit_moves (v : (Fin 4 → ℤ) → α) (h : ∀ y i, v y = v (y + Pi.single i 1)) :
    ∀ y, v y = v 0 := by
  intro y
  refine apply_eq_apply_zero_of_axis_moves v y fun i b _ _ => ?_
  refine apply_single_eq_of_line_moves v |y i| i b (fun s _ _ => ?_) (y i) le_rfl
  have e : b + Pi.single i (s + 1) = b + Pi.single i s + Pi.single i 1 := by
    funext l
    by_cases hl : l = i
    · subst hl; simp [add_assoc]
    · simp [hl]
  rw [e]
  exact h _ i
variable {F : BlockFrame}
theorem isAxialTreeBond_cellCentre_add (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (y : F.Cell)
    (o : Fin 4 → ℤ) (i : Fin 4) (ho : o ∈ centredCube F.blockSide) (ho' : o + Pi.single i 1 ∈ centredCube F.blockSide)
    (hz : ∀ l, i < l → o l = 0) :
    IsAxialTreeBond (cellCentre F.depth y + siteOfCoords F.depth o, i) := by
  constructor
  · unfold IsCrossingBond
    simp only [cellCentre_add_siteOfCoords_add_unitStep, enclosingCell_cellCentre_add hs hL y _ ho',
      enclosingCell_cellCentre_add hs hL y _ ho]
    simp
  · intro l hl
    simp only [cellOffset_cellCentre_add hs hL y o ho]
    exact hz l hl
theorem cellCentre_siteOfCoords (hj : F.depth < F.top) (y : Fin 4 → ℤ) :
    cellCentre F.depth (siteOfCoords F.top y) = siteOfCoords F.depth (blockCoords F.blockSide y) := by
  rw [← refineSite_eq_cellCentre]
  exact BlockLines.refineSite_siteOfCoords hj y
theorem apply_eq_apply_zero_of_tree_and_block_moves (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide)
    (u : (Fin 4 → ℤ) → α)
    (tree : ∀ z i, IsAxialTreeBond (siteOfCoords F.depth z, i) → u z = u (z + Pi.single i 1))
    (top : ∀ y i, u (blockCoords F.blockSide y) = u (blockCoords F.blockSide (y + Pi.single i 1))) :
    ∀ z, u z = u 0 := by
  have hLpos : (0 : ℤ) < F.blockSide := by
    have : 0 < F.blockSide := hL.pos
    exact_mod_cast this
  have hL2 : (F.blockSide : ℤ) = 2 * halfSide F.blockSide + 1 := blockSide_eq_two_mul_halfSide_add_one hL
  have hcent : ∀ y, u (blockCoords F.blockSide y) = u 0 := by
    intro y
    have h1 := apply_eq_apply_zero_of_unit_moves (fun y => u (blockCoords F.blockSide y)) top y
    have e0 : blockCoords F.blockSide (0 : Fin 4 → ℤ) = 0 := by
      funext m
      simp [blockCoords]
    simp only [e0] at h1
    exact h1
  have hblock : ∀ y, ∀ o ∈ centredCube F.blockSide, u (blockCoords F.blockSide y + o) = u (blockCoords F.blockSide y) := by
    intro y
    have := apply_eq_apply_zero_of_tree_moves F.blockSide (fun o => u (blockCoords F.blockSide y + o)) ?_
    · simpa using this
    · intro o i ho ho' hz
      have e : siteOfCoords F.depth (blockCoords F.blockSide y + o) =
          cellCentre F.depth (siteOfCoords F.top y) + siteOfCoords F.depth o := by
        rw [cellCentre_siteOfCoords (by simp [BlockFrame.top]), GaugeFixing.siteOfCoords_add]
      have ht := tree (blockCoords F.blockSide y + o) i (by
        rw [e]
        exact isAxialTreeBond_cellCentre_add hs hL _ o i ho ho' hz)
      simpa [add_assoc] using ht
  intro z
  set y : Fin 4 → ℤ := fun m => (z m + halfSide F.blockSide) / (F.blockSide : ℤ) with hy
  set o : Fin 4 → ℤ := fun m => (z m + halfSide F.blockSide) % (F.blockSide : ℤ) - halfSide F.blockSide with hoo
  have hz : z = blockCoords F.blockSide y + o := by
    funext m
    have := Int.mul_ediv_add_emod (z m + halfSide F.blockSide) (F.blockSide : ℤ)
    simp only [blockCoords, hy, hoo, Pi.add_apply]
    linarith
  have ho : o ∈ centredCube F.blockSide := by
    refine mem_centredCube.2 fun m => ?_
    have h1 := Int.emod_nonneg (z m + halfSide F.blockSide) hLpos.ne'
    have h2 := Int.emod_lt_of_pos (z m + halfSide F.blockSide) hLpos
    simp only [hoo]
    constructor <;> omega
  rw [hz, hblock y o ho, hcent y]
end LatticeMoves
end YangMills.Construction.RunningCouplingSlope
end
