import YangMills.Construction.ClusterExpansionOfAStep.ConvexMeasureOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.GradientsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.PowersAgainstAnExponential
import YangMills.Construction.ClusterExpansionOfAStep.ShiftsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.TwoLawsOnACommonPart
import YangMills.Construction.ClusterExpansionOfAStep.TwoSettingsOnABox
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
open MeasureTheory
namespace ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames BallLaws SettingShifts StepSettings TorusFields TorusLumps
  BlockOffsets TorusBalls RenormalizationStepParameters
namespace LocalMeans
set_option linter.unusedSectionVars false
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
theorem inBalls_of_norm_lt (s : ChartSetting R n) {η : FreeCoords s.free} (h : ∀ b, ‖η b‖ < R.ballRadius) :
    s.InBalls η :=
  fun b => by
    rw [coordNorm_eq_norm]
    exact (h b).le
theorem update_add_eq_add_bondVariation {free : Finset (TorusBond n)} (η : FreeCoords free) (b : free)
    (v : EuclideanSpace ℝ (Fin 3)) :
    Function.update η b (η b + v) = η + bondVariation b v := by
  funext x
  by_cases h : x = b
  · subst h
    simp [bondVariation]
  · simp [bondVariation, Function.update_of_ne h, Pi.single_eq_of_ne h]
theorem directionalDeriv_eq_fderiv {free : Finset (TorusBond n)} {u Ψ : FreeCoords free → ℝ} {η : FreeCoords free}
    (h : Ψ =ᶠ[nhds η] u) (hd : DifferentiableAt ℝ Ψ η) (b : free) (X : EuclideanSpace ℝ (Fin 3)) :
    directionalDeriv u η b X = fderiv ℝ Ψ η (bondVariation b X) := by
  have hline : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => η + τ • (bondVariation b X : FreeCoords free))
      (bondVariation b X) τ := fun τ => by
    simpa using ((hasDerivAt_id τ).smul_const (bondVariation b X : FreeCoords free)).const_add η
  have hp : ∀ τ : ℝ, Function.update η b (η b + τ • X) = η + τ • (bondVariation b X : FreeCoords free) := by
    intro τ
    rw [update_add_eq_add_bondVariation]
    congr 1
    funext x
    by_cases hx : x = b
    · subst hx
      simp [bondVariation]
    · simp [bondVariation, Pi.single_eq_of_ne hx]
  have hc : ContinuousAt (fun τ : ℝ => η + τ • (bondVariation b X : FreeCoords free)) 0 := (hline 0).continuousAt
  have h0 : Filter.Tendsto (fun τ : ℝ => η + τ • (bondVariation b X : FreeCoords free)) (nhds 0) (nhds η) := by
    have := hc.tendsto
    simpa using this
  have ev : (fun τ : ℝ => u (Function.update η b (η b + τ • X))) =ᶠ[nhds 0]
      fun τ : ℝ => Ψ (η + τ • (bondVariation b X : FreeCoords free)) := by
    filter_upwards [h0.eventually h] with τ hτ
    rw [hp, hτ]
  unfold directionalDeriv
  rw [ev.deriv_eq]
  have h3 : HasFDerivAt Ψ (fderiv ℝ Ψ η) (η + (0 : ℝ) • (bondVariation b X : FreeCoords free)) := by
    simpa using hd.hasFDerivAt
  exact (h3.comp_hasDerivAt (0 : ℝ) (hline 0)).deriv
theorem isPseudoMetricOnBonds_bondDist (s : ChartSetting R n) : IsPseudoMetricOnBonds s.bondDist := by
  refine ⟨fun b => ?_, fun b b' => ?_, fun b b' b'' => ?_⟩
  · simp [ChartSetting.bondDist, bondBlockDist, _root_.YangMills.Construction.TorusFields.supDist_self]
  · simp [ChartSetting.bondDist, bondBlockDist, _root_.YangMills.Construction.TorusFields.supDist_comm]
  · simp only [ChartSetting.bondDist, bondBlockDist]
    exact_mod_cast _root_.YangMills.Construction.TorusFields.supDist_triangle _ _ _
theorem fderiv_linearComb_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ} {η : E}
    (hf : DifferentiableAt ℝ f η) (hg : DifferentiableAt ℝ g η) (c₀ c₁ : ℝ) (a : E) :
    fderiv ℝ (fun ζ => c₀ * f ζ + c₁ * g ζ) η a = c₀ * fderiv ℝ f η a + c₁ * fderiv ℝ g η a := by
  have := ((hf.hasFDerivAt.const_mul c₀).add (hg.hasFDerivAt.const_mul c₁)).fderiv
  erw [this]
  simp
theorem restrictTo_eq_restrictToSet (s : ChartSetting R n) (X : Finset s.free) (η : FreeCoords s.free) :
    s.restrictTo X η = restrictToSet X η := by
  funext b
  simp only [ChartSetting.restrictTo, restrictToSet]
theorem chartRestricted_eq (s : ChartSetting R n) (lam v : ℝ) (X : Finset s.free) (u : FreeCoords s.free → ℝ)
    (η : FreeCoords s.free) :
    s.restrictedPotential lam v X u η = v * u η + (1 - v) * (u (restrictToSet X η) +
      R.coupling * lam / 2 * ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2) := by
  simp only [ChartSetting.restrictedPotential, restrictTo_eq_restrictToSet]
structure ComparablePotentials (s : ChartSetting R n) (s' : ChartSetting R n') (Y : TorusSite n) (Y' : TorusSite n')
    (m : ℕ) (lam C₁ Bd A : ℝ)
    (u : FreeCoords s.free → ℝ) (u' : FreeCoords s'.free → ℝ)
    (Ψ : BondField s.free → ℝ) (Ψ' : BondField s'.free → ℝ)
    (K : s.free → s.free → ℝ) (K' : s'.free → s'.free → ℝ) : Prop where
  eventuallyEq : ∀ η, s.InBalls η → Ψ =ᶠ[nhds η] u
  eventuallyEq' : ∀ η, s'.InBalls η → Ψ' =ᶠ[nhds η] u'
  convex : IsUniformlyConvexDecaying R.ballRadius (R.coupling * lam / 8) R.params.rt s.bondDist Ψ K
  convex' : IsUniformlyConvexDecaying R.ballRadius (R.coupling * lam / 8) R.params.rt s'.bondDist Ψ' K'
  standingConstraints : ∀ b, ∑ b' ∈ Finset.univ.erase b, K b b' * Real.exp (R.params.rt * s.bondDist b b') ≤
    A * (R.coupling * lam / 8)
  expansions' : ∀ b, ∑ b' ∈ Finset.univ.erase b, K' b b' * Real.exp (R.params.rt * s'.bondDist b b') ≤
    A * (R.coupling * lam / 8)
  gradNorm_le : ∀ η : BondField s.free, (∀ b, ‖η b‖ < R.ballRadius) → ∀ b, bondGradNorm Ψ b η ≤ C₁
  gradNorm_le' : ∀ η : BondField s'.free, (∀ b, ‖η b‖ < R.ballRadius) → ∀ b, bondGradNorm Ψ' b η ≤ C₁
  fderiv_close : ∀ (η : FreeCoords s.free) (η' : FreeCoords s'.free), s.InBalls η → s'.InBalls η' →
    CoordsAgreeNear s s' Y Y' m η η' → ∀ (q : NearBondIndex) (h : nearBond R.params.side Y q ∈ s.free)
      (h' : nearBond R.params.side Y' q ∈ s'.free), IsNearIndex R.params.side (m / 2) q → ∀ e : BondVector,
      |fderiv ℝ Ψ η (bondVariation ⟨_, h⟩ e) - fderiv ℝ Ψ' η' (bondVariation ⟨_, h'⟩ e)| ≤ Bd * ‖e‖
theorem inBalls_restrictToSet (s : ChartSetting R n) (X : Finset s.free) {η : FreeCoords s.free}
    (hρ : 0 < R.ballRadius) (h : s.InBalls η) : s.InBalls (restrictToSet X η) := by
  intro b
  simp only [restrictToSet]
  split_ifs
  · exact h b
  · rw [coordNorm_eq_norm]
    simpa using hρ.le
theorem coordsAgreeNear_restrictToSet {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m : ℕ} {η : FreeCoords s.free} {η' : FreeCoords s'.free} {X : Finset s.free}
    {X' : Finset s'.free}
    (hfree : ∀ q, IsNearIndex R.params.side m q → (nearBond R.params.side Y q ∈ s.free ↔ nearBond R.params.side Y' q ∈ s'.free))
    (hX : SameNearIndices s s' Y Y' m X X') (hn : CoordsAgreeNear s s' Y Y' m η η') :
    CoordsAgreeNear s s' Y Y' m (restrictToSet X η) (restrictToSet X' η') := by
  intro q hq
  have base := hn q hq
  simp only [ChartSetting.coordsByIndex] at base ⊢
  by_cases hf : nearBond R.params.side Y q ∈ s.free
  · have hf' := (hfree q hq).mp hf
    rw [dif_pos hf, dif_pos hf'] at base ⊢
    have hm := hX q hf hf' hq
    simp only [restrictToSet]
    by_cases hin : (⟨_, hf⟩ : s.free) ∈ X
    · rw [if_pos hin, if_pos (hm.mp hin)]
      exact base
    · rw [if_neg hin, if_neg (fun e => hin (hm.mpr e))]
  · have hf' : nearBond R.params.side Y' q ∉ s'.free := fun e => hf ((hfree q hq).mpr e)
    rw [dif_neg hf, dif_neg hf']
theorem fderiv_restrictedPotential_bondVariation {ι : Type} [Fintype ι] [DecidableEq ι] {Ψ : BondField ι → ℝ}
    (h : ContDiff ℝ 3 Ψ) (c : ℝ) (X : Finset ι) (η : BondField ι) (b : ι) (e : BondVector) :
    fderiv ℝ (restrictedPotential c X Ψ) η (bondVariation b e) =
      if b ∈ X then fderiv ℝ Ψ (restrictToSet X η) (bondVariation b e) else c * inner ℝ (η b) e := by
  rw [fderiv_restrictedPotential h, restrictCLM_bondVariation, restrictCLM_apply]
  have hs : ∑ x ∈ Finset.univ \ X, inner ℝ (η x) ((bondVariation b e : BondField ι) x) =
      if b ∈ Finset.univ \ X then inner ℝ (η b) e else 0 := by
    by_cases hb : b ∈ Finset.univ \ X
    · rw [if_pos hb, Finset.sum_eq_single b]
      · simp [bondVariation]
      · intro x _ hx
        simp [bondVariation, Pi.single_eq_of_ne hx]
      · exact fun hn => absurd hb hn
    · rw [if_neg hb]
      refine Finset.sum_eq_zero fun x hx => ?_
      have : x ≠ b := fun hh => hb (hh ▸ hx)
      simp [bondVariation, Pi.single_eq_of_ne this]
  rw [hs]
  by_cases hb : b ∈ X
  · simp [hb]
  · simp [hb]
theorem eventuallyEq_restricted_comb (s : ChartSetting R n) {Ψ u : FreeCoords s.free → ℝ} (hρ : 0 < R.ballRadius)
    (hΨ : ∀ η, s.InBalls η → Ψ =ᶠ[nhds η] u) (lam v : ℝ) (X : Finset s.free) :
    ∀ η, s.InBalls η →
      (fun ζ => (1 - v) * restrictedPotential (R.coupling * lam) X Ψ ζ + v * Ψ ζ) =ᶠ[nhds η]
        s.restrictedPotential lam v X u := by
  intro η hη
  have e1 := hΨ η hη
  have e2 := hΨ _ (inBalls_restrictToSet s X hρ hη)
  have hc : Filter.Tendsto (fun ζ : FreeCoords s.free => restrictToSet X ζ) (nhds η)
      (nhds (restrictToSet X η)) := by
    have e : (fun ζ : FreeCoords s.free => restrictToSet X ζ) = restrictCLM X := by
      funext ζ
      rw [restrictCLM_apply]
    rw [e, ← restrictCLM_apply]
    exact (restrictCLM X).continuous.tendsto η
  filter_upwards [e1, hc.eventually e2] with ζ a b
  rw [chartRestricted_eq]
  unfold restrictedPotential
  rw [a, b]
  ring
theorem restricted_rows_le {ι : Type} [Fintype ι] [DecidableEq ι] {K : ι → ι → ℝ} {W : ι → ι → ℝ} {c v B : ℝ}
    (h : ∀ b, ∑ b' ∈ Finset.univ.erase b, K b b' * W b b' ≤ B) (b : ι) :
    ∑ b' ∈ Finset.univ.erase b, ((1 - v) * (K b b' + if b = b' then c else 0) + v * K b b') * W b b' ≤ B := by
  refine le_trans (le_of_eq ?_) (h b)
  refine Finset.sum_congr rfl fun b' hb' => ?_
  have : b ≠ b' := fun e => (Finset.mem_erase.mp hb').1 e.symm
  simp only [this, if_false]
  ring
theorem bondGradNorm_restricted_comb_le {ι : Type} [Fintype ι] [DecidableEq ι] {Ψ : BondField ι → ℝ}
    {ρ c C₁ v : ℝ} {X : Finset ι}
    (hρ : 0 < ρ) (h : ContDiff ℝ 3 Ψ) (hcut : ContDiff ℝ 3 (restrictedPotential c X Ψ)) (hc : 0 ≤ c)
    (hC₁ : 0 ≤ C₁) (hcC : c * ρ ≤ C₁) (h0 : 0 ≤ v) (h1 : v ≤ 1)
    (hf : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm Ψ b η ≤ C₁) {η : BondField ι}
    (hη : ∀ b, ‖η b‖ < ρ) (b : ι) :
    bondGradNorm (fun ζ => (1 - v) * restrictedPotential c X Ψ ζ + v * Ψ ζ) b η ≤ C₁ := by
  have hv : 0 ≤ 1 - v := by linarith
  refine bondGradNorm_le_of_forall hC₁ fun e => ?_
  rw [fderiv_linearComb_apply (hcut.differentiable (by norm_num) η) (h.differentiable (by norm_num) η),
    fderiv_restrictedPotential_bondVariation h]
  have a2 : |fderiv ℝ Ψ η (bondVariation b e)| ≤ C₁ * ‖e‖ :=
    (abs_fderiv_bondVariation_le Ψ η b e).trans (by gcongr; exact hf η hη b)
  have a1 : |if b ∈ X then fderiv ℝ Ψ (restrictToSet X η) (bondVariation b e) else c * inner ℝ (η b) e| ≤
      C₁ * ‖e‖ := by
    split_ifs with hb
    · have hm : ∀ x, ‖restrictToSet X η x‖ < ρ := by
        intro x
        rw [← restrictCLM_apply]
        exact restrictCLM_mem hρ hη x
      exact (abs_fderiv_bondVariation_le Ψ _ b e).trans (by gcongr; exact hf _ hm b)
    · rw [abs_mul, abs_of_nonneg hc]
      have h2 : |inner ℝ (η b) e| ≤ ρ * ‖e‖ := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        gcongr
        exact (hη b).le
      calc c * |inner ℝ (η b) e| ≤ c * (ρ * ‖e‖) := by gcongr
        _ = c * ρ * ‖e‖ := by ring
        _ ≤ C₁ * ‖e‖ := by gcongr
  calc _ ≤ (1 - v) * |if b ∈ X then fderiv ℝ Ψ (restrictToSet X η) (bondVariation b e) else c * inner ℝ (η b) e| +
        v * |fderiv ℝ Ψ η (bondVariation b e)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hv, abs_of_nonneg h0]
    _ ≤ (1 - v) * (C₁ * ‖e‖) + v * (C₁ * ‖e‖) := by gcongr
    _ = C₁ * ‖e‖ := by ring
theorem ComparablePotentials.restrict {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m : ℕ} {lam C₁ Bd A v : ℝ}
    {u : FreeCoords s.free → ℝ} {u' : FreeCoords s'.free → ℝ} {Ψ : BondField s.free → ℝ}
    {Ψ' : BondField s'.free → ℝ} {K : s.free → s.free → ℝ} {K' : s'.free → s'.free → ℝ}
    {X : Finset s.free} {X' : Finset s'.free} (hρ : 0 < R.ballRadius) (hx : 0 < R.coupling * lam) (hC₁ : 0 ≤ C₁)
    (hcC : R.coupling * lam * R.ballRadius ≤ C₁) (hBd : 0 ≤ Bd)
    (hfree : ∀ q, IsNearIndex R.params.side m q → (nearBond R.params.side Y q ∈ s.free ↔ nearBond R.params.side Y' q ∈ s'.free))
    (g : ComparablePotentials s s' Y Y' m lam C₁ Bd A u u' Ψ Ψ' K K') (h0 : 0 ≤ v) (h1 : v ≤ 1)
    (hX : SameNearIndices s s' Y Y' m X X') :
    ComparablePotentials s s' Y Y' m lam C₁ Bd A (s.restrictedPotential lam v X u) (s'.restrictedPotential lam v X' u')
      (fun ζ => (1 - v) * restrictedPotential (R.coupling * lam) X Ψ ζ + v * Ψ ζ)
      (fun ζ => (1 - v) * restrictedPotential (R.coupling * lam) X' Ψ' ζ + v * Ψ' ζ)
      (fun b b' => (1 - v) * (K b b' + if b = b' then R.coupling * lam else 0) + v * K b b')
      (fun b b' => (1 - v) * (K' b b' + if b = b' then R.coupling * lam else 0) + v * K' b b') := by
  have hm : 0 < R.coupling * lam / 8 := by positivity
  have hc2 : 2 * (R.coupling * lam / 8) ≤ R.coupling * lam := by linarith
  have D := isPseudoMetricOnBonds_bondDist s
  have D' := isPseudoMetricOnBonds_bondDist s'
  have c1 := isUniformlyConvexDecaying_restrictedPotential hρ hm D g.convex hc2 X
  have c2 := isUniformlyConvexDecaying_restrictedPotential hρ hm D' g.convex' hc2 X'
  have hv : 0 ≤ 1 - v := by linarith
  refine ⟨eventuallyEq_restricted_comb s hρ g.eventuallyEq lam v X,
    eventuallyEq_restricted_comb s' hρ g.eventuallyEq' lam v X',
    isUniformlyConvexDecaying_convexComb h0 h1 c1 g.convex,
    isUniformlyConvexDecaying_convexComb h0 h1 c2 g.convex', restricted_rows_le g.standingConstraints, restricted_rows_le g.expansions',
    fun η hη b => bondGradNorm_restricted_comb_le hρ g.convex.smooth c1.smooth hx.le hC₁ hcC h0 h1 g.gradNorm_le hη b,
    fun η hη b => bondGradNorm_restricted_comb_le hρ g.convex'.smooth c2.smooth hx.le hC₁ hcC h0 h1 g.gradNorm_le' hη b,
    ?_⟩
  intro η η' hη hη' hn q h h' hq e
  have hqm : IsNearIndex R.params.side m q := ⟨fun l => by
    have := hq.1 l
    omega, hq.2⟩
  have dΨ := g.convex.smooth.differentiable (by norm_num : (3 : WithTop ℕ∞) ≠ 0) η
  have dΨ' := g.convex'.smooth.differentiable (by norm_num : (3 : WithTop ℕ∞) ≠ 0) η'
  have dc := c1.smooth.differentiable (by norm_num : (3 : WithTop ℕ∞) ≠ 0) η
  have dc' := c2.smooth.differentiable (by norm_num : (3 : WithTop ℕ∞) ≠ 0) η'
  rw [fderiv_linearComb_apply dc dΨ, fderiv_linearComb_apply dc' dΨ',
    fderiv_restrictedPotential_bondVariation g.convex.smooth, fderiv_restrictedPotential_bondVariation g.convex'.smooth]
  have a2 := g.fderiv_close η η' hη hη' hn q h h' hq e
  have hval : η ⟨_, h⟩ = η' ⟨_, h'⟩ := by
    have := hn q hqm
    simpa only [ChartSetting.coordsByIndex, dif_pos h, dif_pos h'] using this
  have hmem := hX q h h' hqm
  have a1 : |(if (⟨_, h⟩ : s.free) ∈ X then fderiv ℝ Ψ (restrictToSet X η) (bondVariation ⟨_, h⟩ e)
        else R.coupling * lam * inner ℝ (η ⟨_, h⟩) e) -
      (if (⟨_, h'⟩ : s'.free) ∈ X' then fderiv ℝ Ψ' (restrictToSet X' η') (bondVariation ⟨_, h'⟩ e)
        else R.coupling * lam * inner ℝ (η' ⟨_, h'⟩) e)| ≤ Bd * ‖e‖ := by
    by_cases hin : (⟨_, h⟩ : s.free) ∈ X
    · rw [if_pos hin, if_pos (hmem.mp hin)]
      exact g.fderiv_close _ _ (inBalls_restrictToSet s X hρ hη) (inBalls_restrictToSet s' X' hρ hη')
        (coordsAgreeNear_restrictToSet hfree hX hn) q h h' hq e
    · rw [if_neg hin, if_neg (fun e' => hin (hmem.mpr e')), hval, sub_self, abs_zero]
      positivity
  set P := (if (⟨_, h⟩ : s.free) ∈ X then fderiv ℝ Ψ (restrictToSet X η) (bondVariation ⟨_, h⟩ e)
        else R.coupling * lam * inner ℝ (η ⟨_, h⟩) e)
  set P' := (if (⟨_, h'⟩ : s'.free) ∈ X' then fderiv ℝ Ψ' (restrictToSet X' η') (bondVariation ⟨_, h'⟩ e)
        else R.coupling * lam * inner ℝ (η' ⟨_, h'⟩) e)
  have e1 : (1 - v) * P + v * fderiv ℝ Ψ η (bondVariation ⟨_, h⟩ e) -
      ((1 - v) * P' + v * fderiv ℝ Ψ' η' (bondVariation ⟨_, h'⟩ e)) =
      (1 - v) * (P - P') + v * (fderiv ℝ Ψ η (bondVariation ⟨_, h⟩ e) - fderiv ℝ Ψ' η' (bondVariation ⟨_, h'⟩ e)) := by
    ring
  rw [e1]
  calc _ ≤ (1 - v) * |P - P'| +
        v * |fderiv ℝ Ψ η (bondVariation ⟨_, h⟩ e) - fderiv ℝ Ψ' η' (bondVariation ⟨_, h'⟩ e)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hv, abs_of_nonneg h0]
    _ ≤ (1 - v) * (Bd * ‖e‖) + v * (Bd * ‖e‖) := by gcongr
    _ = Bd * ‖e‖ := by ring
theorem ComparablePotentials.convexComb {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m : ℕ} {lam C₁ Bd A c : ℝ}
    {u w : FreeCoords s.free → ℝ} {u' w' : FreeCoords s'.free → ℝ} {Ψ Φ : BondField s.free → ℝ}
    {Ψ' Φ' : BondField s'.free → ℝ} {K Kw : s.free → s.free → ℝ} {K' Kw' : s'.free → s'.free → ℝ}
    (g : ComparablePotentials s s' Y Y' m lam C₁ Bd A u u' Ψ Ψ' K K')
    (g₂ : ComparablePotentials s s' Y Y' m lam C₁ Bd A w w' Φ Φ' Kw Kw')
    (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ComparablePotentials s s' Y Y' m lam C₁ Bd A (fun η => c * u η + (1 - c) * w η)
      (fun η => c * u' η + (1 - c) * w' η)
      (fun ζ => (1 - c) * Φ ζ + c * Ψ ζ) (fun ζ => (1 - c) * Φ' ζ + c * Ψ' ζ)
      (fun b b' => (1 - c) * Kw b b' + c * K b b') (fun b b' => (1 - c) * Kw' b b' + c * K' b b') := by
  have hv : 0 ≤ 1 - c := by linarith
  have rowmix : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {P Q W : ι → ι → ℝ} {B : ℝ},
      (∀ b, ∑ b' ∈ Finset.univ.erase b, P b b' * W b b' ≤ B) →
      (∀ b, ∑ b' ∈ Finset.univ.erase b, Q b b' * W b b' ≤ B) →
      ∀ b, ∑ b' ∈ Finset.univ.erase b, ((1 - c) * Q b b' + c * P b b') * W b b' ≤ B := by
    intro ι _ _ P Q W B hP hQ b
    have e : ∑ b' ∈ Finset.univ.erase b, ((1 - c) * Q b b' + c * P b b') * W b b' =
        (1 - c) * ∑ b' ∈ Finset.univ.erase b, Q b b' * W b b' +
          c * ∑ b' ∈ Finset.univ.erase b, P b b' * W b b' := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    have a := mul_le_mul_of_nonneg_left (hQ b) hv
    have b' := mul_le_mul_of_nonneg_left (hP b) h0
    linarith
  have firstmix : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {f g₁ : BondField ι → ℝ} {η : BondField ι},
      ContDiff ℝ 3 f → ContDiff ℝ 3 g₁ → ∀ b : ι, bondGradNorm f b η ≤ C₁ → bondGradNorm g₁ b η ≤ C₁ → 0 ≤ C₁ →
      bondGradNorm (fun ζ => (1 - c) * f ζ + c * g₁ ζ) b η ≤ C₁ := by
    intro ι _ _ f g₁ η hf hg b a₁ a₂ hC
    refine bondGradNorm_le_of_forall hC fun e => ?_
    rw [fderiv_linearComb_apply (hf.differentiable (by norm_num) η) (hg.differentiable (by norm_num) η)]
    have b₁ := (abs_fderiv_bondVariation_le f η b e).trans (mul_le_mul_of_nonneg_right a₁ (norm_nonneg e))
    have b₂ := (abs_fderiv_bondVariation_le g₁ η b e).trans (mul_le_mul_of_nonneg_right a₂ (norm_nonneg e))
    calc _ ≤ (1 - c) * |fderiv ℝ f η (bondVariation b e)| + c * |fderiv ℝ g₁ η (bondVariation b e)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hv, abs_of_nonneg h0]
      _ ≤ (1 - c) * (C₁ * ‖e‖) + c * (C₁ * ‖e‖) := by gcongr
      _ = C₁ * ‖e‖ := by ring
  have eqmix : ∀ {ι : Type} {f g₁ F G : (ι → BondVector) → ℝ} {η : ι → BondVector}
      [TopologicalSpace (ι → BondVector)],
      f =ᶠ[nhds η] F → g₁ =ᶠ[nhds η] G →
      (fun ζ => (1 - c) * g₁ ζ + c * f ζ) =ᶠ[nhds η] fun ζ => c * F ζ + (1 - c) * G ζ := by
    intro ι f g₁ F G η _ a b
    filter_upwards [a, b] with ζ p q
    rw [p, q]
    ring
  refine ⟨fun η hη => eqmix (g.eventuallyEq η hη) (g₂.eventuallyEq η hη),
    fun η hη => eqmix (g.eventuallyEq' η hη) (g₂.eventuallyEq' η hη),
    isUniformlyConvexDecaying_convexComb h0 h1 g₂.convex g.convex,
    isUniformlyConvexDecaying_convexComb h0 h1 g₂.convex' g.convex', rowmix g.standingConstraints g₂.standingConstraints,
    rowmix g.expansions' g₂.expansions', ?_, ?_, ?_⟩
  · intro η hη b
    have hC : 0 ≤ C₁ := (norm_nonneg _).trans (g.gradNorm_le η hη b)
    exact firstmix g₂.convex.smooth g.convex.smooth b (g₂.gradNorm_le η hη b) (g.gradNorm_le η hη b) hC
  · intro η hη b
    have hC : 0 ≤ C₁ := (norm_nonneg _).trans (g.gradNorm_le' η hη b)
    exact firstmix g₂.convex'.smooth g.convex'.smooth b (g₂.gradNorm_le' η hη b) (g.gradNorm_le' η hη b) hC
  · intro η η' hη hη' hn q h h' hq e
    rw [fderiv_linearComb_apply (g₂.convex.smooth.differentiable (by norm_num) η)
        (g.convex.smooth.differentiable (by norm_num) η),
      fderiv_linearComb_apply (g₂.convex'.smooth.differentiable (by norm_num) η')
        (g.convex'.smooth.differentiable (by norm_num) η')]
    have a₁ := g.fderiv_close η η' hη hη' hn q h h' hq e
    have a₂ := g₂.fderiv_close η η' hη hη' hn q h h' hq e
    have e1 : (1 - c) * fderiv ℝ Φ η (bondVariation ⟨_, h⟩ e) + c * fderiv ℝ Ψ η (bondVariation ⟨_, h⟩ e) -
        ((1 - c) * fderiv ℝ Φ' η' (bondVariation ⟨_, h'⟩ e) + c * fderiv ℝ Ψ' η' (bondVariation ⟨_, h'⟩ e)) =
        (1 - c) * (fderiv ℝ Φ η (bondVariation ⟨_, h⟩ e) - fderiv ℝ Φ' η' (bondVariation ⟨_, h'⟩ e)) +
          c * (fderiv ℝ Ψ η (bondVariation ⟨_, h⟩ e) - fderiv ℝ Ψ' η' (bondVariation ⟨_, h'⟩ e)) := by ring
    rw [e1]
    calc _ ≤ (1 - c) * |fderiv ℝ Φ η (bondVariation ⟨_, h⟩ e) - fderiv ℝ Φ' η' (bondVariation ⟨_, h'⟩ e)| +
          c * |fderiv ℝ Ψ η (bondVariation ⟨_, h⟩ e) - fderiv ℝ Ψ' η' (bondVariation ⟨_, h'⟩ e)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hv, abs_of_nonneg h0]
      _ ≤ (1 - c) * (Bd * ‖e‖) + c * (Bd * ‖e‖) := by gcongr
      _ = Bd * ‖e‖ := by ring
theorem abs_le_of_unit_bound {T : BondVector → ℝ} {B : ℝ} (hB : 0 ≤ B) (hl : ∀ (t : ℝ) e, T (t • e) = t * T e)
    (hu : ∀ X : BondVector, ‖X‖ = 1 → |T X| ≤ B) (e : BondVector) : |T e| ≤ B * ‖e‖ := by
  by_cases h : e = 0
  · subst h
    have := hl 0 0
    simp only [zero_smul, zero_mul] at this
    simp [this]
  · have hn : 0 < ‖e‖ := norm_pos_iff.mpr h
    have hX : ‖(‖e‖)⁻¹ • e‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have e1 : ‖e‖ • ((‖e‖)⁻¹ • e) = e := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    calc |T e| = |T (‖e‖ • ((‖e‖)⁻¹ • e))| := by rw [e1]
      _ = ‖e‖ * |T ((‖e‖)⁻¹ • e)| := by rw [hl, abs_mul, abs_of_pos hn]
      _ ≤ ‖e‖ * B := by
          have := hu _ hX
          gcongr
      _ = B * ‖e‖ := by ring
theorem bondVariation_smul {ι : Type} [DecidableEq ι] (b : ι) (t : ℝ) (e : BondVector) :
    (bondVariation b (t • e) : BondField ι) = t • bondVariation b e := by
  funext x
  by_cases h : x = b
  · subst h
    simp [bondVariation]
  · simp [bondVariation, Pi.single_eq_of_ne h]
theorem ComparablePotentials.of_partPotential {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m : ℕ} {lam C C₁ Bd A : ℝ}
    {u : FreeCoords s.free → ℝ} {u' : FreeCoords s'.free → ℝ} {Ψ : BondField s.free → ℝ}
    {Ψ' : BondField s'.free → ℝ} {K : s.free → s.free → ℝ} {K' : s'.free → s'.free → ℝ}
    (hC₁ : C * R.coupling ≤ C₁) (hC₁0 : 0 ≤ C₁) (hBd : 0 ≤ Bd) (hu : s.HasFullDecay u lam C)
    (hu' : s'.HasFullDecay u' lam C)
    (e : ∀ η, s.InBalls η → Ψ =ᶠ[nhds η] u) (e' : ∀ η, s'.InBalls η → Ψ' =ᶠ[nhds η] u')
    (c : IsUniformlyConvexDecaying R.ballRadius (R.coupling * lam / 8) R.params.rt s.bondDist Ψ K)
    (c' : IsUniformlyConvexDecaying R.ballRadius (R.coupling * lam / 8) R.params.rt s'.bondDist Ψ' K')
    (r : ∀ b, ∑ b' ∈ Finset.univ.erase b, K b b' * Real.exp (R.params.rt * s.bondDist b b') ≤
      A * (R.coupling * lam / 8))
    (r' : ∀ b, ∑ b' ∈ Finset.univ.erase b, K' b b' * Real.exp (R.params.rt * s'.bondDist b b') ≤
      A * (R.coupling * lam / 8))
    (hg : ∀ (η : FreeCoords s.free) (η' : FreeCoords s'.free), s.InBalls η → s'.InBalls η' →
      CoordsAgreeNear s s' Y Y' m η η' → ∀ (q : NearBondIndex) (h : nearBond R.params.side Y q ∈ s.free)
        (h' : nearBond R.params.side Y' q ∈ s'.free) (X : BondVector), IsNearIndex R.params.side (m / 2) q → ‖X‖ = 1 →
        |directionalDeriv u η ⟨_, h⟩ X - directionalDeriv u' η' ⟨_, h'⟩ X| ≤ Bd) :
    ComparablePotentials s s' Y Y' m lam C₁ Bd A u u' Ψ Ψ' K K' := by
  have lin : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : BondField ι → ℝ) (η : BondField ι) (b : ι) (t : ℝ)
      (w : BondVector), fderiv ℝ f η (bondVariation b (t • w)) = t * fderiv ℝ f η (bondVariation b w) := by
    intro ι _ _ f η b t w
    rw [bondVariation_smul, map_smul, smul_eq_mul]
  have firstBound : ∀ {N : ℕ} [NeZero N] (v : ChartSetting R N) (w : FreeCoords v.free → ℝ)
      (P : BondField v.free → ℝ),
      v.HasFullDecay w lam C → (∀ η, v.InBalls η → P =ᶠ[nhds η] w) → ContDiff ℝ 3 P →
      ∀ η : BondField v.free, (∀ b, ‖η b‖ < R.ballRadius) → ∀ b, bondGradNorm P b η ≤ C₁ := by
    intro N _ v w P hw he hc η hη b
    refine bondGradNorm_le_of_forall hC₁0 fun x =>
      abs_le_of_unit_bound hC₁0 (T := fun x => fderiv ℝ P η (bondVariation b x))
        (fun t x => lin P η b t x) (fun X hX => ?_) x
    have hin := inBalls_of_norm_lt v hη
    have h1 : directionalDeriv w η b X = fderiv ℝ P η (bondVariation b X) :=
      directionalDeriv_eq_fderiv (he η hin) (hc.differentiable (by norm_num) η) b X
    rw [← h1]
    exact (hw.firstDeriv_le η hin b X hX).trans hC₁
  refine ⟨e, e', c, c', r, r', firstBound s u Ψ hu e c.smooth, firstBound s' u' Ψ' hu' e' c'.smooth, ?_⟩
  intro η η' hη hη' hn q h h' hq x
  refine abs_le_of_unit_bound hBd
    (T := fun x => fderiv ℝ Ψ η (bondVariation ⟨_, h⟩ x) - fderiv ℝ Ψ' η' (bondVariation ⟨_, h'⟩ x))
    (fun t x => by
      rw [lin, lin]
      ring) (fun X hX => ?_) x
  rw [← directionalDeriv_eq_fderiv (e η hη) (c.smooth.differentiable (by norm_num) η),
    ← directionalDeriv_eq_fderiv (e' η' hη') (c'.smooth.differentiable (by norm_num) η')]
  exact hg η η' hη hη' hn q h h' X hq hX
theorem exists_comparablePotentials {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m : ℕ} {lam C₁ Bd A : ℝ}
    (hρ : 0 < R.ballRadius) (hx : 0 < R.coupling * lam) (hC₁ : 0 ≤ C₁)
    (hcC : R.coupling * lam * R.ballRadius ≤ C₁) (hBd : 0 ≤ Bd)
    (hfree : ∀ q, IsNearIndex R.params.side m q → (nearBond R.params.side Y q ∈ s.free ↔ nearBond R.params.side Y' q ∈ s'.free))
    (base : ∀ ν : ℝ, 0 ≤ ν → ν ≤ 1 → ∃ Ψ Ψ' K K',
      ComparablePotentials s s' Y Y' m lam C₁ Bd A (s.partPotential ν) (s'.partPotential ν) Ψ Ψ' K K')
    {u : FreeCoords s.free → ℝ} {u' : FreeCoords s'.free → ℝ} (h : AlikePotentials s s' lam Y Y' m u u') :
    ∃ Ψ Ψ' K K', ComparablePotentials s s' Y Y' m lam C₁ Bd A u u' Ψ Ψ' K K' := by
  induction h with
  | part_potential ν a b => exact base ν a b
  | restrict v X X' u u' a b hX _ ih =>
    obtain ⟨Ψ, Ψ', K, K', g⟩ := ih
    exact ⟨_, _, _, _, ComparablePotentials.restrict hρ hx hC₁ hcC hBd hfree g a b hX⟩
  | convex c u w u' w' a b _ _ ih ih₂ =>
    obtain ⟨Ψ, Ψ', K, K', g⟩ := ih
    obtain ⟨Φ, Φ', Kw, Kw', g₂⟩ := ih₂
    exact ⟨_, _, _, _, ComparablePotentials.convexComb g g₂ a b⟩
section Indices
def boxOffsets (k : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(k : ℤ)) k
open Classical in
def nearFreeIndices (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ) : Finset NearBondIndex :=
  ((boxOffsets k) ×ˢ ((centredCube R.params.side) ×ˢ (Finset.univ : Finset (Fin 4)))).filter
    fun q => nearBond R.params.side Y q ∈ s.free
theorem mem_nearFreeIndices {s : ChartSetting R n} {Y : TorusSite n} {k : ℕ} {q : NearBondIndex} :
    q ∈ nearFreeIndices s Y k ↔ IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q ∈ s.free := by
  obtain ⟨h, o, i⟩ := q
  simp only [nearFreeIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, boxOffsets,
    Fintype.mem_piFinset, Finset.mem_Icc, IsNearIndex, OffsetInBox, abs_le]
theorem card_nearFreeIndices_le (hodd : Odd R.params.side) (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ) :
    ((nearFreeIndices s Y k).card : ℝ) ≤ ((k : ℝ) * 2 + 1) ^ 4 * (R.params.side : ℝ) ^ 4 * 4 := by
  have h1 : (nearFreeIndices s Y k).card ≤ (2 * k + 1) ^ 4 * (R.params.side ^ 4 * 4) := by
    refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
    have ht : ((k : ℤ) + 1 - -(k : ℤ)).toNat = 2 * k + 1 := by omega
    have hb : (boxOffsets k).card = (2 * k + 1) ^ 4 := by
      simp only [boxOffsets, Fintype.card_piFinset, Int.card_Icc, ht]
      simp
    rw [Finset.card_product, Finset.card_product, card_centredCube hodd, hb]
    simp
  have h2 : ((nearFreeIndices s Y k).card : ℝ) ≤ (((2 * k + 1) ^ 4 * (R.params.side ^ 4 * 4) : ℕ) : ℝ) := by
    exact_mod_cast h1
  refine h2.trans (le_of_eq ?_)
  push_cast
  ring
theorem bondBlock_nearBond (hodd : Odd R.params.side) {Y : TorusSite n} {q : NearBondIndex}
    (hq : q.2.1 ∈ centredCube R.params.side) :
    bondBlock (R := R) (nearBond R.params.side Y q) = Y + siteOfInt q.1 :=
  parentBlock_fineSite hodd Y q.1 q.2.1 hq
theorem exists_nearIndex_of_supDist_le (hodd : Odd R.params.side) {s : ChartSetting R n} {Y : TorusSite n} {k : ℕ}
    (b : s.free) (hk : _root_.YangMills.Construction.TorusFields.supDist Y (bondBlock (R := R) b.1) ≤ k) :
    ∃ q ∈ nearFreeIndices s Y k, nearBond R.params.side Y q = b.1 := by
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist Y (bondBlock (R := R) b.1)
  obtain ⟨o, ho, hx⟩ := exists_fineSite_of_parentBlock hodd (Y + siteOfInt e) b.1.1 he
  have hbond : nearBond R.params.side Y (e, o, b.1.2) = b.1 := by
    have := fineSite_add_siteOfInt R.params.side Y e 0 o
    simp only [add_zero] at this
    simp only [nearBond]
    rw [← this, ← hx]
  refine ⟨(e, o, b.1.2), mem_nearFreeIndices.mpr ⟨⟨fun l => ?_, ho⟩, ?_⟩, hbond⟩
  · have := hb l
    show |e l| ≤ (k : ℤ)
    rw [Int.abs_eq_natAbs]
    omega
  · rw [hbond]
    exact b.2
theorem valMinAbs_intCast_of_small {N : ℕ} [NeZero N] {e : ℤ} (h : 2 * |e| < N) :
    ((e : ZMod N)).valMinAbs = e := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
theorem supDist_add_siteOfInt_add_siteOfInt {N : ℕ} [NeZero N] (Z : TorusSite N) {a b : Fin 4 → ℤ} {k : ℕ}
    (hk : 4 * k < N) (ha : OffsetInBox k a) (hb : OffsetInBox k b) :
    _root_.YangMills.Construction.TorusFields.supDist (Z + siteOfInt a) (Z + siteOfInt b) = Finset.univ.sup fun i => (a i - b i).natAbs := by
  unfold TorusFields.supDist
  refine Finset.sup_congr rfl fun i _ => ?_
  have e : (Z + siteOfInt a : TorusSite N) i - (Z + siteOfInt b : TorusSite N) i = (((a i - b i : ℤ)) : ZMod N) := by
    simp [siteOfInt]
  rw [e, valMinAbs_intCast_of_small]
  have h1 := abs_le.mp (ha i)
  have h2 := abs_le.mp (hb i)
  have h3 : |a i - b i| ≤ 2 * (k : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  omega
theorem sum_exp_bondDist_le (hodd : Odd R.params.side) (s : ChartSetting R n) {c A₁ : ℝ}
    (hA₁ : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (D : ℕ),
      ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => D ≤ _root_.YangMills.Construction.TorusFields.supDist Y y), Real.exp (-(c * _root_.YangMills.Construction.TorusFields.supDist Y y)) ≤
        A₁ * Real.exp (-(c * D / 2))) (b₀ : s.free) :
    ∑ b : s.free, Real.exp (-(c * s.bondDist b₀ b)) ≤ 4 * (R.params.side : ℝ) ^ 4 * A₁ := by
  classical
  set Z₀ := bondBlock (R := R) b₀.1 with hZ₀
  set g : TorusSite n → ℝ := fun Z => Real.exp (-(c * _root_.YangMills.Construction.TorusFields.supDist Z Z₀)) with hg
  have hg0 : ∀ Z, 0 ≤ g Z := fun Z => (Real.exp_pos _).le
  have hne : NeZero (n * R.params.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have e1 : ∑ b : s.free, Real.exp (-(c * s.bondDist b₀ b)) = ∑ b ∈ s.free, g (parentBlock R.params.side b.1) := by
    rw [← Finset.sum_coe_sort s.free]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hg, ChartSetting.bondDist, bondBlockDist]
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    rfl
  have e2 : ∑ b ∈ s.free, g (parentBlock R.params.side b.1) ≤
      ∑ b : TorusBond (n * R.params.side), g (parentBlock R.params.side b.1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => hg0 _
  have e3 : ∑ b : TorusBond (n * R.params.side), g (parentBlock R.params.side b.1) =
      4 * ∑ x : TorusSite (n * R.params.side), g (parentBlock R.params.side x) := by
    rw [Fintype.sum_prod_type]
    simp [Finset.mul_sum]
  have e4 : ∑ x : TorusSite (n * R.params.side), g (parentBlock R.params.side x) =
      (R.params.side : ℝ) ^ 4 * ∑ Z : TorusSite n, g Z := by
    rw [← Finset.sum_fiberwise Finset.univ (parentBlock R.params.side), Finset.mul_sum]
    refine Finset.sum_congr rfl fun Z _ => ?_
    have hfil : (Finset.univ.filter fun x : TorusSite (n * R.params.side) => parentBlock R.params.side x = Z) =
        sitesInBlocks R.params.side {Z} := by
      ext x
      simp [sitesInBlocks]
    rw [hfil]
    have h1 : ∑ x ∈ sitesInBlocks R.params.side {Z}, g (parentBlock R.params.side x) =
        ∑ x ∈ sitesInBlocks R.params.side {Z}, g Z := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have : parentBlock R.params.side x = Z := by simpa [sitesInBlocks] using hx
      rw [this]
    rw [h1, sum_sitesInBlocks hodd Z fun _ => g Z]
    simp [card_centredCube hodd]
  have e5 : ∑ Z : TorusSite n, g Z ≤ A₁ := by
    have := hA₁ n Z₀ 0
    simpa [hg] using this
  rw [e1]
  refine e2.trans ?_
  rw [e3, e4]
  have hL : (0 : ℝ) ≤ (R.params.side : ℝ) ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left e5 hL]
theorem sum_restrictedGradBound_le {ι ι₀ : Type} [Fintype ι] [DecidableEq ι] [Fintype ι₀] {d : ι → ι → ℝ}
    (hd : IsPseudoMetricOnBonds d)
    {K : ι → ι → ℝ} (hK : ∀ b b', 0 ≤ K b b') {j : ι₀ → ι} (Z : Finset ι₀) {ρ c C₁ κ Am Wb D : ℝ} (hκ : 0 ≤ κ)
    (hρ : 0 ≤ ρ) (hcC : 0 ≤ C₁ + c * ρ)
    (hrows : ∀ b, ∑ b' ∈ Finset.univ.erase b, K b b' * Real.exp (κ * d b b') ≤ Am)
    (hoff : ∀ a ∈ Z, ∀ b, b ∉ Finset.univ.image j → D ≤ d (j a) b)
    (hW : ∀ a, ∑ b, Real.exp (-(κ / 4 * d (j a) b)) ≤ Wb) :
    ∑ a ∈ Z, ∑ b, restrictedGradBound ρ c C₁ (Finset.univ.image j) K b * Real.exp (-(κ * d (j a) b)) ≤
      Z.card * (((Finset.univ.image j).card : ℝ) * (ρ * Am * Real.exp (-(κ * D))) +
        (C₁ + c * ρ) * (Wb * Real.exp (-(3 / 4 * κ * D)))) := by
  set X := Finset.univ.image j with hX
  have hAm : ∀ a ∈ Z, ∀ b ∈ X, (∑ b' ∈ Finset.univ \ X, K b b') * Real.exp (-(κ * d (j a) b)) ≤
      Am * Real.exp (-(κ * D)) := by
    intro a ha b hb
    rw [Finset.sum_mul]
    have h1 : ∀ b' ∈ Finset.univ \ X, K b b' * Real.exp (-(κ * d (j a) b)) ≤
        K b b' * Real.exp (κ * d b b') * Real.exp (-(κ * D)) := by
      intro b' hb'
      have h2 := hoff a ha b' (Finset.mem_sdiff.mp hb').2
      have h3 := hd.triangle (j a) b b'
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hK _ _)
      have : κ * D ≤ κ * (d (j a) b + d b b') := mul_le_mul_of_nonneg_left (h2.trans h3) hκ
      nlinarith
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine le_trans ?_ (hrows b)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => mul_nonneg (hK _ _) (Real.exp_pos _).le
    intro b' hb'
    refine Finset.mem_erase.mpr ⟨fun e => ?_, Finset.mem_univ _⟩
    exact (Finset.mem_sdiff.mp hb').2 (e ▸ hb)
  have per : ∀ a ∈ Z, ∑ b, restrictedGradBound ρ c C₁ X K b * Real.exp (-(κ * d (j a) b)) ≤
      (X.card : ℝ) * (ρ * Am * Real.exp (-(κ * D))) + (C₁ + c * ρ) * (Wb * Real.exp (-(3 / 4 * κ * D))) := by
    intro a ha
    rw [← Finset.sum_sdiff (Finset.subset_univ X), add_comm]
    refine add_le_add ?_ ?_
    · have : ∀ b ∈ X, restrictedGradBound ρ c C₁ X K b * Real.exp (-(κ * d (j a) b)) ≤
          ρ * Am * Real.exp (-(κ * D)) := by
        intro b hb
        simp only [restrictedGradBound, if_pos hb]
        have := mul_le_mul_of_nonneg_left (hAm a ha b hb) hρ
        calc _ = ρ * ((∑ b' ∈ Finset.univ \ X, K b b') * Real.exp (-(κ * d (j a) b))) := by ring
          _ ≤ ρ * (Am * Real.exp (-(κ * D))) := this
          _ = _ := by ring
      refine (Finset.sum_le_card_nsmul _ _ _ this).trans (le_of_eq ?_)
      rw [nsmul_eq_mul]
    · have : ∀ b ∈ Finset.univ \ X, restrictedGradBound ρ c C₁ X K b * Real.exp (-(κ * d (j a) b)) ≤
          (C₁ + c * ρ) * (Real.exp (-(3 / 4 * κ * D)) * Real.exp (-(κ / 4 * d (j a) b))) := by
        intro b hb
        have hbX := (Finset.mem_sdiff.mp hb).2
        simp only [restrictedGradBound, if_neg hbX]
        refine mul_le_mul_of_nonneg_left ?_ hcC
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h2 := hoff a ha b hbX
        have : κ * D ≤ κ * d (j a) b := mul_le_mul_of_nonneg_left h2 hκ
        nlinarith
      refine (Finset.sum_le_sum this).trans ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hcC
      have h5 : ∑ b ∈ Finset.univ \ X, Real.exp (-(κ / 4 * d (j a) b)) ≤ Wb :=
        le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le)
          (hW a)
      have hp := (Real.exp_pos (-(3 / 4 * κ * D))).le
      nlinarith [mul_le_mul_of_nonneg_left h5 hp]
  refine (Finset.sum_le_card_nsmul _ _ _ per).trans (le_of_eq ?_)
  rw [nsmul_eq_mul]
theorem offBlock_terms_le {z w P ρ A lam x G₀ Wb ε e₁ e₂ : ℝ} (hz : 0 ≤ z) (hzP : z ≤ P) (hw : 0 ≤ w)
    (hwP : w ≤ P) (hP : 1 ≤ P)
    (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hlam : 0 ≤ lam) (hx : 0 ≤ x) (hG : 0 ≤ G₀) (hWb : 0 ≤ Wb) (hε : 0 ≤ ε)
    (h1 : 0 ≤ e₁) (h1ε : e₁ ≤ ε) (h2 : 0 ≤ e₂) (h2ε : e₂ ≤ ε) :
    z * (w * (ρ * (A * (x * lam / 8)) * e₁) + (G₀ * x + x * lam * ρ) * (Wb * e₂)) ≤
      (ρ * A * lam / 8 + (G₀ + lam * ρ) * Wb) * x * P ^ 2 * ε := by
  have a : z * (w * (ρ * (A * (x * lam / 8)) * e₁) + (G₀ * x + x * lam * ρ) * (Wb * e₂)) ≤
      P * (P * (ρ * (A * (x * lam / 8)) * ε) + (G₀ * x + x * lam * ρ) * (Wb * ε)) := by gcongr
  refine a.trans ?_
  have h3 : 0 ≤ (G₀ + lam * ρ) * Wb * x * ε := by positivity
  have h4 : P ≤ P ^ 2 := by nlinarith
  have e : P * (P * (ρ * (A * (x * lam / 8)) * ε) + (G₀ * x + x * lam * ρ) * (Wb * ε)) =
      P ^ 2 * (ρ * A * lam / 8 * x * ε) + P * ((G₀ + lam * ρ) * Wb * x * ε) := by ring
  rw [e]
  have e2 : (ρ * A * lam / 8 + (G₀ + lam * ρ) * Wb) * x * P ^ 2 * ε =
      P ^ 2 * (ρ * A * lam / 8 * x * ε) + P ^ 2 * ((G₀ + lam * ρ) * Wb * x * ε) := by ring
  rw [e2]
  have := mul_le_mul_of_nonneg_right h4 h3
  linarith
end Indices
section Main
theorem weightedMean_eq_ballExpectation {s : ChartSetting R n} {u : FreeCoords s.free → ℝ}
    {Ψ : BondField s.free → ℝ}
    (e : ∀ η, s.InBalls η → Ψ =ᶠ[nhds η] u) (G : FreeCoords s.free → ℝ) :
    weightedMean (s.lawDensity u) G = ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ G := by
  have hd : ∀ η, s.lawDensity u η = ballDensity (cutoffFactor R.ballRadius R.barrierFn) Ψ η := by
    intro η
    unfold ChartSetting.lawDensity ballDensity ChartSetting.cutoffProduct radialWeightProd
    simp only [coordNorm_eq_norm]
    by_cases h : ∀ b, ‖η b‖ < R.ballRadius
    · rw [(e η (inBalls_of_norm_lt s h)).eq_of_nhds]
    · have hz : ∏ b : s.free, cutoffFactor R.ballRadius R.barrierFn ‖η b‖ = 0 := by
        simp only [not_forall, not_lt] at h
        obtain ⟨b, hb⟩ := h
        refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
        unfold cutoffFactor
        rw [if_neg (not_lt.mpr hb)]
      rw [hz]
      simp
  unfold weightedMean ballExpectation
  simp only [hd]
theorem extendByZero_bondVariation {ι ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] [DecidableEq ι] {j : ι₀ → ι}
    (hj : Function.Injective j) (a : ι₀) (e : BondVector) :
    _root_.YangMills.Construction.ClusterExpansionOfAStep.extendByZero j (bondVariation a e) = bondVariation (j a) e := by
  funext b
  by_cases hb : ∃ a', j a' = b
  · obtain ⟨a', rfl⟩ := hb
    rw [extendByZero_apply_image hj]
    by_cases h : a' = a
    · subst h
      simp [bondVariation]
    · have h' : j a' ≠ j a := fun e => h (hj e)
      simp [bondVariation, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
  · have hb' : ∀ a', j a' ≠ b := fun a' e => hb ⟨a', e⟩
    rw [extendByZero_apply_of_not_mem_range _ hb']
    have : b ≠ j a := fun e => hb' a e.symm
    simp [bondVariation, Pi.single_eq_of_ne this]
theorem norm_extendByZero_lt {ι ι₀ : Type} [Fintype ι₀] [DecidableEq ι] {j : ι₀ → ι} {ρ : ℝ}
    (hj : Function.Injective j)
    (hρ : 0 < ρ) {ξ : BondField ι₀} (hξ : ∀ a, ‖ξ a‖ < ρ) : ∀ b, ‖_root_.YangMills.Construction.ClusterExpansionOfAStep.extendByZero j ξ b‖ < ρ := by
  intro b
  by_cases hb : ∃ a, j a = b
  · obtain ⟨a, rfl⟩ := hb
    rw [extendByZero_apply_image hj]
    exact hξ a
  · rw [extendByZero_apply_of_not_mem_range _ fun a e => hb ⟨a, e⟩]
    simpa using hρ
def indexedCoords (S : Finset NearBondIndex) (ξ : BondField ↥S) (q : NearBondIndex) : EuclideanSpace ℝ (Fin 3) :=
  if h : q ∈ S then ξ ⟨q, h⟩ else 0
theorem measurable_indexedCoords (S : Finset NearBondIndex) : Measurable (indexedCoords S) := by
  refine measurable_pi_lambda _ fun q => ?_
  unfold indexedCoords
  by_cases h : q ∈ S
  · simp only [h, dif_pos]
    exact measurable_pi_apply _
  · simp only [h, dif_neg, not_false_eq_true]
    exact measurable_const
open Classical in
def innerPart (L k : ℕ) (S : Finset NearBondIndex) : Finset ↥S := Finset.univ.filter fun a => IsNearIndex L k a.1
theorem abs_sub_weightedMean_le (hcore : SharedMarginalMeanBound) (hodd : Odd R.params.side) {s : ChartSetting R n}
    {s' : ChartSetting R n'}
    {Y : TorusSite n} {Y' : TorusSite n'} {m : ℕ} {lam C₁ Bd A o Wb : ℝ} {u : FreeCoords s.free → ℝ}
    {u' : FreeCoords s'.free → ℝ} {Ψ : BondField s.free → ℝ} {Ψ' : BondField s'.free → ℝ}
    {K : s.free → s.free → ℝ} {K' : s'.free → s'.free → ℝ} (hρ : 0 < R.ballRadius) (hx : 0 < R.coupling * lam)
    (hrt : 0 ≤ R.params.rt)
    (hp : IsCutoff R.ballRadius R.barrierFn) (hag : SettingsAgreeNear s s' Y Y' m) (hBd : 0 ≤ Bd)
    (hC₁ : 0 ≤ C₁ + R.coupling * lam * R.ballRadius) (hA : 0 ≤ A)
    (g : ComparablePotentials s s' Y Y' m lam C₁ Bd A u u' Ψ Ψ' K K')
    (hW : ∀ b, ∑ b', Real.exp (-(R.params.rt / 4 * s.bondDist b b')) ≤ Wb)
    (hW' : ∀ b, ∑ b', Real.exp (-(R.params.rt / 4 * s'.bondDist b b')) ≤ Wb)
    {F : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ} (hF : Measurable F)
    (hFr : DependsWithin R.params.side (m / 4) F)
    (hFo : ∀ z z', CoordsInBalls R z → CoordsInBalls R z' → |F z - F z'| ≤ o) (ho : 0 ≤ o) :
    |weightedMean (s.lawDensity u) (fun η => F (s.coordsByIndex Y η)) -
        weightedMean (s'.lawDensity u') (fun η => F (s'.coordsByIndex Y' η))| ≤
      4 * R.ballRadius * (1 + A) * o *
        (((innerPart R.params.side (m / 4) (nearFreeIndices s Y (m / 2))).card : ℝ) *
            (((nearFreeIndices s Y (m / 2)).card : ℝ) *
            (R.ballRadius * (A * (R.coupling * lam / 8)) * Real.exp (-(R.params.rt * ((m / 2 + 1 - m / 4 : ℕ) : ℝ)))) +
            (C₁ + R.coupling * lam * R.ballRadius) *
              (Wb * Real.exp (-(3 / 4 * R.params.rt * ((m / 2 + 1 - m / 4 : ℕ) : ℝ))))) +
          ((innerPart R.params.side (m / 4) (nearFreeIndices s Y (m / 2))).card : ℝ) *
            (((nearFreeIndices s Y (m / 2)).card : ℝ) *
            (R.ballRadius * (A * (R.coupling * lam / 8)) * Real.exp (-(R.params.rt * ((m / 2 + 1 - m / 4 : ℕ) : ℝ)))) +
            (C₁ + R.coupling * lam * R.ballRadius) *
              (Wb * Real.exp (-(3 / 4 * R.params.rt * ((m / 2 + 1 - m / 4 : ℕ) : ℝ))))) +
          ((innerPart R.params.side (m / 4) (nearFreeIndices s Y (m / 2))).card : ℝ) *
            (((nearFreeIndices s Y (m / 2)).card : ℝ) * Bd)) := by
  set S := nearFreeIndices s Y (m / 2) with hS
  have side := hag.lt_extent
  have side' := hag.lt_extent'
  have near2 : ∀ {q}, IsNearIndex R.params.side (m / 2) q → IsNearIndex R.params.side m q := fun {q} hq => ⟨fun l => by
    have := hq.1 l
    omega, hq.2⟩
  have memS : ∀ a : ↥S, IsNearIndex R.params.side (m / 2) a.1 ∧ nearBond R.params.side Y a.1 ∈ s.free := fun a =>
    mem_nearFreeIndices.mp a.2
  have memS' : ∀ a : ↥S, nearBond R.params.side Y' a.1 ∈ s'.free := fun a =>
    (hag.free_iff _ (near2 (memS a).1)).mp (memS a).2
  set j : ↥S → s.free := fun a => ⟨nearBond R.params.side Y a.1, (memS a).2⟩ with hj
  set j' : ↥S → s'.free := fun a => ⟨nearBond R.params.side Y' a.1, memS' a⟩ with hj'
  have inj : Function.Injective j := by
    intro a b e
    exact Subtype.ext (eq_of_nearBond_eq hodd (k := m) (by omega) (near2 (memS a).1) (near2 (memS b).1)
      (congrArg Subtype.val e))
  have inj' : Function.Injective j' := by
    intro a b e
    exact Subtype.ext (eq_of_nearBond_eq hodd (k := m) (by omega) (near2 (memS a).1) (near2 (memS b).1)
      (congrArg Subtype.val e))
  have D := isPseudoMetricOnBonds_bondDist s
  have D' := isPseudoMetricOnBonds_bondDist s'
  have hd' : ∀ a b, s.bondDist (j a) (j b) = s'.bondDist (j' a) (j' b) := by
    intro a b
    simp only [ChartSetting.bondDist, bondBlockDist, hj, hj']
    rw [bondBlock_nearBond hodd (memS a).1.2, bondBlock_nearBond hodd (memS b).1.2,
      bondBlock_nearBond hodd (memS a).1.2, bondBlock_nearBond hodd (memS b).1.2,
      _root_.YangMills.Construction.ClusterExpansionOfAStep.LocalMeans.supDist_add_siteOfInt_add_siteOfInt Y (k := m / 2) (by omega) (memS a).1.1 (memS b).1.1,
      _root_.YangMills.Construction.ClusterExpansionOfAStep.LocalMeans.supDist_add_siteOfInt_add_siteOfInt Y' (k := m / 2) (by omega) (memS a).1.1 (memS b).1.1]
  set F₀ : BondField ↥S → ℝ := fun ξ => F (indexedCoords S ξ) with hF₀
  have hm8 : 0 < R.coupling * lam / 8 := by positivity
  have read1 : ∀ η : FreeCoords s.free, F (s.coordsByIndex Y η) = F₀ fun a => η (j a) := by
    intro η
    refine hFr _ _ fun q hq => ?_
    have hq2 : IsNearIndex R.params.side (m / 2) q := ⟨fun l => by
      have := hq.1 l
      omega, hq.2⟩
    simp only [ChartSetting.coordsByIndex, indexedCoords]
    by_cases hf : nearBond R.params.side Y q ∈ s.free
    · have hqS : q ∈ S := mem_nearFreeIndices.mpr ⟨hq2, hf⟩
      rw [dif_pos hf, dif_pos hqS]
    · have hqS : q ∉ S := fun h => hf (mem_nearFreeIndices.mp h).2
      rw [dif_neg hf, dif_neg hqS]
  have read2 : ∀ η : FreeCoords s'.free, F (s'.coordsByIndex Y' η) = F₀ fun a => η (j' a) := by
    intro η
    refine hFr _ _ fun q hq => ?_
    have hq2 : IsNearIndex R.params.side (m / 2) q := ⟨fun l => by
      have := hq.1 l
      omega, hq.2⟩
    simp only [ChartSetting.coordsByIndex, indexedCoords]
    by_cases hf : nearBond R.params.side Y' q ∈ s'.free
    · have hf2 := (hag.free_iff q (near2 hq2)).mpr hf
      have hqS : q ∈ S := mem_nearFreeIndices.mpr ⟨hq2, hf2⟩
      rw [dif_pos hf, dif_pos hqS]
    · have hqS : q ∉ S := fun h => hf ((hag.free_iff q (near2 hq2)).mp (mem_nearFreeIndices.mp h).2)
      rw [dif_neg hf, dif_neg hqS]
  have hballs : ∀ ξ : BondField ↥S, (∀ a, ‖ξ a‖ < R.ballRadius) → CoordsInBalls R (indexedCoords S ξ) := by
    intro ξ hξ q
    rw [coordNorm_eq_norm]
    unfold indexedCoords
    split_ifs with h
    · exact (hξ _).le
    · simpa using hρ.le
  have nearExt : ∀ ξ : BondField ↥S,
      CoordsAgreeNear s s' Y Y' m (_root_.YangMills.Construction.ClusterExpansionOfAStep.extendByZero j ξ) (_root_.YangMills.Construction.ClusterExpansionOfAStep.extendByZero j' ξ) := by
    intro ξ q hq
    simp only [ChartSetting.coordsByIndex]
    by_cases hf : nearBond R.params.side Y q ∈ s.free
    · have hf' := (hag.free_iff q hq).mp hf
      rw [dif_pos hf, dif_pos hf']
      by_cases hq2 : IsNearIndex R.params.side (m / 2) q
      · have hqS : q ∈ S := mem_nearFreeIndices.mpr ⟨hq2, hf⟩
        have e1 : (⟨nearBond R.params.side Y q, hf⟩ : s.free) = j ⟨q, hqS⟩ := rfl
        have e2 : (⟨nearBond R.params.side Y' q, hf'⟩ : s'.free) = j' ⟨q, hqS⟩ := rfl
        rw [e1, e2, extendByZero_apply_image inj, extendByZero_apply_image inj']
      · rw [extendByZero_apply_of_not_mem_range, extendByZero_apply_of_not_mem_range]
        · intro a e
          exact hq2 ((eq_of_nearBond_eq hodd (k := m) (by omega) (near2 (memS a).1) hq
            (congrArg Subtype.val e)) ▸ (memS a).1)
        · intro a e
          exact hq2 ((eq_of_nearBond_eq hodd (k := m) (by omega) (near2 (memS a).1) hq
            (congrArg Subtype.val e)) ▸ (memS a).1)
    · have hf' : nearBond R.params.side Y' q ∉ s'.free := fun e => hf ((hag.free_iff q hq).mpr e)
      rw [dif_neg hf, dif_neg hf']
  have core := hcore (↥s.free) (↥s'.free) (↥S) R.ballRadius (R.coupling * lam / 8) R.params.rt A o (R.coupling * lam)
    C₁ s.bondDist s'.bondDist (fun a b => s.bondDist (j a) (j b)) Ψ Ψ' K K' R.barrierFn j j' hρ hm8 hrt hp D D'
    inj inj' (fun _ _ => rfl) hd' g.convex g.convex' g.standingConstraints g.expansions' (by linarith) g.gradNorm_le g.gradNorm_le'
    (innerPart R.params.side (m / 4) S) F₀ (fun _ => Bd) (hF.comp (measurable_indexedCoords S))
    (fun ξ ξ' h => hFr _ _ fun q hq => by
      unfold indexedCoords
      by_cases hqS : q ∈ S
      · rw [dif_pos hqS, dif_pos hqS]
        refine h ⟨q, hqS⟩ ?_
        simp only [innerPart, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hq
      · rw [dif_neg hqS, dif_neg hqS])
    (fun ξ ξ' h h' => hFo _ _ (hballs ξ h) (hballs ξ' h'))
    (fun ξ hξ a => by
      refine bondGradNorm_le_of_forall hBd fun e => ?_
      have c1 := g.convex.smooth
      have c2 := g.convex'.smooth
      have d1 : DifferentiableAt ℝ (fun ζ => Ψ (_root_.YangMills.Construction.ClusterExpansionOfAStep.extendByZero j ζ)) ξ :=
        (c1.comp (_root_.YangMills.Construction.ClusterExpansionOfAStep.extendByZero j).contDiff).differentiable (by norm_num) ξ
      have d2 : DifferentiableAt ℝ (fun ζ => Ψ' (_root_.YangMills.Construction.ClusterExpansionOfAStep.extendByZero j' ζ)) ξ :=
        (c2.comp (_root_.YangMills.Construction.ClusterExpansionOfAStep.extendByZero j').contDiff).differentiable (by norm_num) ξ
      have f1 : fderiv ℝ (fun ζ => Ψ' (_root_.YangMills.Construction.ClusterExpansionOfAStep.extendByZero j' ζ) - Ψ (_root_.YangMills.Construction.ClusterExpansionOfAStep.extendByZero j ζ)) ξ (bondVariation a e) =
          fderiv ℝ (fun ζ => Ψ' (_root_.YangMills.Construction.ClusterExpansionOfAStep.extendByZero j' ζ)) ξ (bondVariation a e) -
            fderiv ℝ (fun ζ => Ψ (_root_.YangMills.Construction.ClusterExpansionOfAStep.extendByZero j ζ)) ξ (bondVariation a e) := by
        have := (d2.hasFDerivAt.sub d1.hasFDerivAt).fderiv
        erw [this]
        rfl
      rw [f1, fderiv_comp_clm c1, fderiv_comp_clm c2, extendByZero_bondVariation inj,
        extendByZero_bondVariation inj', abs_sub_comm]
      exact g.fderiv_close _ _ (inBalls_of_norm_lt s (norm_extendByZero_lt inj hρ hξ))
        (inBalls_of_norm_lt s' (norm_extendByZero_lt inj' hρ hξ))
        (nearExt ξ) a.1 (memS a).2 (memS' a) (memS a).1 e)
  rw [funext read1, funext read2, weightedMean_eq_ballExpectation g.eventuallyEq,
    weightedMean_eq_ballExpectation g.eventuallyEq']
  refine core.trans ?_
  have hoff : ∀ {N : ℕ} [NeZero N] (v : ChartSetting R N) (Z : TorusSite N) (jv : ↥S → v.free),
      (∀ a, (jv a).1 = nearBond R.params.side Z a.1) →
      (∀ b : v.free, _root_.YangMills.Construction.TorusFields.supDist Z (bondBlock (R := R) b.1) ≤ m / 2 → b ∈ Finset.univ.image jv) →
      ∀ a ∈ innerPart R.params.side (m / 4) S, ∀ b, b ∉ Finset.univ.image jv →
        (((m / 2 + 1 - m / 4 : ℕ) : ℝ)) ≤ v.bondDist (jv a) b := by
    intro N _ v Z jv hjv hall a ha b hb
    have haq : IsNearIndex R.params.side (m / 4) a.1 := by
      simpa only [innerPart, Finset.mem_filter, Finset.mem_univ, true_and] using ha
    have h1 : m / 2 + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist Z (bondBlock (R := R) b.1) := by
      by_contra hlt
      exact hb (hall b (by omega))
    have h2 : _root_.YangMills.Construction.TorusFields.supDist Z (bondBlock (R := R) (jv a).1) ≤ m / 4 := by
      rw [hjv, bondBlock_nearBond hodd (memS a).1.2]
      refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le Z a.1.1 (m / 4) fun l => ?_
      have := haq.1 l
      rw [Int.abs_eq_natAbs] at this
      omega
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle Z (bondBlock (R := R) (jv a).1) (bondBlock (R := R) b.1)
    have h4 : m / 2 + 1 - m / 4 ≤ _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) (jv a).1) (bondBlock (R := R) b.1) := by omega
    simp only [ChartSetting.bondDist, bondBlockDist]
    exact_mod_cast h4
  have hall1 : ∀ b : s.free, _root_.YangMills.Construction.TorusFields.supDist Y (bondBlock (R := R) b.1) ≤ m / 2 → b ∈ Finset.univ.image j := by
    intro b hb
    obtain ⟨q, hq, e⟩ := exists_nearIndex_of_supDist_le hodd b hb
    exact Finset.mem_image.mpr ⟨⟨q, hq⟩, Finset.mem_univ _, Subtype.ext e⟩
  have hall2 : ∀ b : s'.free, _root_.YangMills.Construction.TorusFields.supDist Y' (bondBlock (R := R) b.1) ≤ m / 2 → b ∈ Finset.univ.image j' := by
    intro b hb
    obtain ⟨q, hq, e⟩ := exists_nearIndex_of_supDist_le hodd b hb
    have hq' := mem_nearFreeIndices.mp hq
    have hqS : q ∈ S := mem_nearFreeIndices.mpr ⟨hq'.1, (hag.free_iff q (near2 hq'.1)).mpr hq'.2⟩
    exact Finset.mem_image.mpr ⟨⟨q, hqS⟩, Finset.mem_univ _, Subtype.ext e⟩
  have K0 := kernel_nonneg hρ g.convex
  have K0' := kernel_nonneg hρ g.convex'
  have s1 := sum_restrictedGradBound_le D K0 (j := j) (innerPart R.params.side (m / 4) S) (ρ := R.ballRadius)
    (c := R.coupling * lam) (C₁ := C₁) (κ := R.params.rt)
    (Wb := Wb) hrt hρ.le hC₁ g.standingConstraints (hoff s Y j (fun _ => rfl) hall1) (fun a => hW (j a))
  have s2 := sum_restrictedGradBound_le D' K0' (j := j') (innerPart R.params.side (m / 4) S) (ρ := R.ballRadius)
    (c := R.coupling * lam) (C₁ := C₁)
    (κ := R.params.rt) (Wb := Wb) hrt hρ.le hC₁ g.expansions' (hoff s' Y' j' (fun _ => rfl) hall2) (fun a => hW' (j' a))
  have hcard : ((Finset.univ.image j).card : ℝ) ≤ (S.card : ℝ) := by
    have : (Finset.univ.image j).card ≤ (Finset.univ : Finset ↥S).card := Finset.card_image_le
    simpa using (Nat.cast_le (α := ℝ).mpr this)
  have hcard' : ((Finset.univ.image j').card : ℝ) ≤ (S.card : ℝ) := by
    have : (Finset.univ.image j').card ≤ (Finset.univ : Finset ↥S).card := Finset.card_image_le
    simpa using (Nat.cast_le (α := ℝ).mpr this)
  have hAm : 0 ≤ R.ballRadius * (A * (R.coupling * lam / 8)) *
      Real.exp (-(R.params.rt * ((m / 2 + 1 - m / 4 : ℕ) : ℝ))) := by positivity
  have hz : (0 : ℝ) ≤ ((innerPart R.params.side (m / 4) S).card : ℝ) := Nat.cast_nonneg _
  have mono : ∀ c₁ E₂ : ℝ, c₁ ≤ (S.card : ℝ) → ((innerPart R.params.side (m / 4) S).card : ℝ) *
      (c₁ * (R.ballRadius * (A * (R.coupling * lam / 8)) *
        Real.exp (-(R.params.rt * ((m / 2 + 1 - m / 4 : ℕ) : ℝ)))) + E₂) ≤
      ((innerPart R.params.side (m / 4) S).card : ℝ) *
        ((S.card : ℝ) * (R.ballRadius * (A * (R.coupling * lam / 8)) *
          Real.exp (-(R.params.rt * ((m / 2 + 1 - m / 4 : ℕ) : ℝ)))) + E₂) := by
    intro c₁ E₂ h
    refine mul_le_mul_of_nonneg_left ?_ hz
    linarith [mul_le_mul_of_nonneg_right h hAm]
  have b1 := s1.trans (mono _ _ hcard)
  have b2 := s2.trans (mono _ _ hcard')
  have b3 : ∑ a ∈ innerPart R.params.side (m / 4) S, ∑ a' : ↥S, Bd * Real.exp (-(R.params.rt * s.bondDist (j a) (j a'))) ≤
      ((innerPart R.params.side (m / 4) S).card : ℝ) * ((S.card : ℝ) * Bd) := by
    have inner : ∀ a ∈ innerPart R.params.side (m / 4) S,
        ∑ a' : ↥S, Bd * Real.exp (-(R.params.rt * s.bondDist (j a) (j a'))) ≤ (S.card : ℝ) * Bd := by
      intro a _
      have h1 : ∀ a' ∈ (Finset.univ : Finset ↥S), Bd * Real.exp (-(R.params.rt * s.bondDist (j a) (j a'))) ≤ Bd := by
        intro a' _
        have h2 : Real.exp (-(R.params.rt * s.bondDist (j a) (j a'))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hrt (pseudoMetric_nonneg D _ _)))
        exact mul_le_of_le_one_right hBd h2
      refine (Finset.sum_le_card_nsmul _ _ _ h1).trans (le_of_eq ?_)
      simp
    refine (Finset.sum_le_card_nsmul _ _ _ inner).trans (le_of_eq ?_)
    rw [nsmul_eq_mul]
  have hpre : 0 ≤ 4 * R.ballRadius * (1 + A) * o := by positivity
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add b1 b2) b3) hpre
theorem final_bound_le {pre G₁ x W4 mm e16 e8 o : ℝ} (ho : 0 ≤ o) (he : 0 ≤ e8)
    (hN : (pre * G₁ * W4 ^ 2) * x ^ 1 * mm ^ 8 * e16 ≤ 1) :
    pre * o * (G₁ * x * (mm ^ 4 * W4) ^ 2 * (e16 * e8)) ≤ o * e8 := by
  have h : 0 ≤ o * e8 := mul_nonneg ho he
  have e : pre * o * (G₁ * x * (mm ^ 4 * W4) ^ 2 * (e16 * e8)) =
      (o * e8) * ((pre * G₁ * W4 ^ 2) * x ^ 1 * mm ^ 8 * e16) := by ring
  rw [e]
  exact mul_le_of_le_one_right h hN
theorem three_terms_le {B₁ B₃ G x P ε : ℝ} (h₁ : B₁ ≤ G * x * P ^ 2 * ε) (h₃ : B₃ ≤ x * P ^ 2 * ε) :
    B₁ + B₁ + B₃ ≤ (2 * G + 1) * x * P ^ 2 * ε := by
  have e : (2 * G + 1) * x * P ^ 2 * ε = G * x * P ^ 2 * ε + G * x * P ^ 2 * ε + x * P ^ 2 * ε := by ring
  rw [e]
  linarith
theorem total_bound_le {rt ρ A lam x G₀ Wb G W4 z w Bd o D mR : ℝ} (hrt : 0 ≤ rt) (hρ : 0 ≤ ρ) (hA : 0 ≤ A)
    (hlam : 0 ≤ lam)
    (hx : 1 ≤ x) (hG₀ : 0 ≤ G₀) (hWb : 0 ≤ Wb) (hW41 : 1 ≤ W4) (ho : 0 ≤ o)
    (hG : G = ρ * A * lam / 8 + (G₀ + lam * ρ) * Wb) (hm0 : 0 ≤ mR) (hmD : mR ≤ 4 * D) (hz0 : 0 ≤ z)
    (hzw : z ≤ w)
    (hwP : w ≤ (mR + 1) ^ 4 * W4) (hBd : Bd = Real.exp (-(4 * rt * mR)))
    (hN : (4 * ρ * (1 + A) * (2 * G + 1) * W4 ^ 2) * x ^ 1 * (mR + 1) ^ 8 * Real.exp (-(rt / 16 * mR)) ≤ 1) :
    4 * ρ * (1 + A) * o *
      (z * (w * (ρ * (A * (x * lam / 8)) * Real.exp (-(rt * D))) +
          (G₀ * x + x * lam * ρ) * (Wb * Real.exp (-(3 / 4 * rt * D)))) +
        z * (w * (ρ * (A * (x * lam / 8)) * Real.exp (-(rt * D))) +
          (G₀ * x + x * lam * ρ) * (Wb * Real.exp (-(3 / 4 * rt * D)))) +
        z * (w * Bd)) ≤ o * Real.exp (-(rt * mR / 2 ^ 3)) := by
  have hw0 : 0 ≤ w := hz0.trans hzw
  have hx0 : 0 ≤ x := by linarith
  set e16 : ℝ := Real.exp (-(rt / 16 * mR)) with he16
  set e8 : ℝ := Real.exp (-(rt * mR / 2 ^ 3)) with he8
  have hε : e16 * e8 = Real.exp (-(3 / 16 * rt * mR)) := by
    rw [he16, he8, ← Real.exp_add]
    congr 1
    ring
  have hrtm : rt * mR ≤ rt * (4 * D) := mul_le_mul_of_nonneg_left hmD hrt
  have hrtm0 : 0 ≤ rt * mR := mul_nonneg hrt hm0
  have hε0 : 0 ≤ e16 * e8 := by positivity
  have he₁ : Real.exp (-(rt * D)) ≤ e16 * e8 := by
    rw [hε]
    apply Real.exp_le_exp.mpr
    linarith
  have he₂ : Real.exp (-(3 / 4 * rt * D)) ≤ e16 * e8 := by
    rw [hε]
    apply Real.exp_le_exp.mpr
    linarith
  have hBε : Bd ≤ e16 * e8 := by
    rw [hε, hBd]
    apply Real.exp_le_exp.mpr
    linarith
  have hBd0 : 0 ≤ Bd := by rw [hBd]; positivity
  set P : ℝ := (mR + 1) ^ 4 * W4 with hP
  have hP1 : 1 ≤ P := by
    have h1 : (1 : ℝ) ≤ (mR + 1) ^ 4 := one_le_pow₀ (by linarith)
    rw [hP]
    nlinarith
  have B₁ := offBlock_terms_le (z := z) (w := w) (P := P) (ρ := ρ) (A := A) (lam := lam) (x := x) (G₀ := G₀)
    (Wb := Wb) (ε := e16 * e8) (e₁ := Real.exp (-(rt * D))) (e₂ := Real.exp (-(3 / 4 * rt * D))) hz0
    (hzw.trans hwP) hw0 hwP hP1
    hρ hA hlam hx0 hG₀ hWb hε0 (Real.exp_pos _).le he₁ (Real.exp_pos _).le he₂
  have B₃ : z * (w * Bd) ≤ x * P ^ 2 * (e16 * e8) := by
    have a1 : z * (w * Bd) ≤ P * (P * (e16 * e8)) := by
      have hzP := hzw.trans hwP
      gcongr
    have a2 : P * (P * (e16 * e8)) = 1 * P ^ 2 * (e16 * e8) := by ring
    rw [a2] at a1
    refine a1.trans ?_
    gcongr
  rw [← hG] at B₁
  have hsum := three_terms_le B₁ B₃
  have hpre : 0 ≤ 4 * ρ * (1 + A) * o := by positivity
  refine (mul_le_mul_of_nonneg_left hsum hpre).trans ?_
  exact final_bound_le (pre := 4 * ρ * (1 + A)) (G₁ := 2 * G + 1) (x := x) (W4 := W4) (mm := mR + 1)
    (e16 := e16) (e8 := e8) (o := o) ho (Real.exp_pos _).le hN
theorem localMeansClose (hconv : SettingsUniformlyConvex) (hgrad : SettingGradientsClose)
    (hcore : SharedMarginalMeanBound) (htie : ChartPotentialConvex)
    (hnum : PolynomialBelowExponential) : LocalMeansClose := by
  obtain ⟨r₁, p₁, H1⟩ := hconv
  obtain ⟨r₂, p₂, H2⟩ := hgrad
  refine ⟨fun c => min (r₁ c) (r₂ c), fun c => lt_min (p₁ c) (p₂ c), fun T hT hrt => ?_⟩
  obtain ⟨C, y₁, hC, H1⟩ := H1 T hT (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, H2⟩ := H2 T hT (hrt.trans (min_le_right _ _))
  have hrt0 := hT.rt_pos
  have hσ := hT.σ_pos
  have hlam : 0 < T.lam := hT.chain.2.2.1
  have hLone : (1 : ℝ) ≤ T.side := by
    have : 1 ≤ T.side := Nat.pos_of_ne_zero (NeZero.ne T.side)
    exact_mod_cast this
  have hLpos : (0 : ℝ) < T.side := by linarith
  obtain ⟨A₁, hA₁0, hA₁⟩ := exists_sum_exp_supDist_le (T.rt / 4) (by positivity)
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = T.threshold / 64 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρd]; positivity
  obtain ⟨A, hAd⟩ : ∃ A, A = 8 * (4 * (2 * (T.side : ℝ)) ^ 4) * C / T.lam + (2 * T.rt)⁻¹ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAd]; positivity
  obtain ⟨Wb, hWbd⟩ : ∃ Wb, Wb = 4 * (T.side : ℝ) ^ 4 * A₁ := ⟨_, rfl⟩
  have hWb0 : 0 ≤ Wb := by rw [hWbd]; positivity
  obtain ⟨G₀, hG₀d⟩ : ∃ G₀, G₀ = C + T.lam * ρ + 1 := ⟨_, rfl⟩
  have hG₀0 : 0 ≤ G₀ := by rw [hG₀d]; positivity
  obtain ⟨G, hGd⟩ : ∃ G, G = ρ * A * T.lam / 8 + (G₀ + T.lam * ρ) * Wb := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hGd]; positivity
  obtain ⟨W4, hW4d⟩ : ∃ W4, W4 = 4 * (T.side : ℝ) ^ 4 := ⟨_, rfl⟩
  have hW41 : 1 ≤ W4 := by
    rw [hW4d]
    have : (1 : ℝ) ≤ (T.side : ℝ) ^ 4 := one_le_pow₀ hLone
    linarith
  obtain ⟨y₃, hy₃, N⟩ := hnum (4 * ρ * (1 + A) * (2 * G + 1) * W4 ^ 2) (T.rt / 16) (4 * T.side) 1 8
    (by positivity) (by positivity)
  refine ⟨max T.floorMin (max y₁ (max y₂ y₃)), fun y hy R hOT n n' _ _ hn hn' s s' Y Y' m hs hs' hag hr u u'
    hal F o hF hFr hFo => ?_⟩
  obtain ⟨hR, hρA, hp, hyx, hstep⟩ := id hOT
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hy2 : y₂ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  have hy3 : y₃ ≤ R.coupling :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))).trans hyx
  have hx1 : 1 ≤ R.coupling := hy₃.trans hy3
  have hx0 : 0 < R.coupling := by linarith
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have hRrt : R.params.rt = T.rt := by rw [hR]; rfl
  have hRσ : R.params.threshold = T.threshold := by rw [hR]; rfl
  have hodd : Odd R.params.side := by rw [hL]; exact hT.L_odd
  have hRρ : R.ballRadius = ρ := by
    show R.params.threshold / 64 = _
    rw [hRσ, hρd]
  have hρR : 0 < R.ballRadius := by rw [hRρ]; exact hρ0
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    rw [hRρ, hp, hρd]
    exact hT.cut
  have hx : 0 < R.coupling * T.lam := by positivity
  have hOff : R.params.offDiagonalBound T.lam C = A := by
    rw [hAd]
    simp only [StepParameters.offDiagonalBound, StepParameters.blockBondBound, hL, hRrt]
  have hWs : ∀ {N : ℕ} [NeZero N] (v : ChartSetting R N) (b : v.free),
      ∑ b', Real.exp (-(R.params.rt / 4 * v.bondDist b b')) ≤ Wb := by
    intro N _ v b
    have h3 := sum_exp_bondDist_le hodd v (c := R.params.rt / 4) (A₁ := A₁) (by rw [hRrt]; exact hA₁) b
    have hLp : (R.params.side : ℝ) = T.side := by rw [hL]
    rw [hWbd, ← hLp]
    exact h3
  have ho : 0 ≤ o := by
    have hz : CoordsInBalls R (0 : NearBondIndex → EuclideanSpace ℝ (Fin 3)) := fun q => by
      rw [coordNorm_eq_norm]
      simpa using hρR.le
    simpa using hFo 0 0 hz hz
  obtain ⟨Bd, hBdd⟩ : ∃ Bd, Bd = Real.exp (-(4 * T.rt * m)) := ⟨_, rfl⟩
  have hBd0 : 0 ≤ Bd := by rw [hBdd]; exact (Real.exp_pos _).le
  have hG₀x : C * R.coupling ≤ G₀ * R.coupling := by
    have : C ≤ G₀ := by
      rw [hG₀d]
      have : 0 ≤ T.lam * ρ := by positivity
      linarith
    gcongr
  have hcC : R.coupling * T.lam * R.ballRadius ≤ G₀ * R.coupling := by
    rw [hRρ]
    have : T.lam * ρ ≤ G₀ := by
      rw [hG₀d]
      linarith
    calc R.coupling * T.lam * ρ = (T.lam * ρ) * R.coupling := by ring
      _ ≤ G₀ * R.coupling := by gcongr
  have hC₁0 : 0 ≤ G₀ * R.coupling := by positivity
  have hkr : (R.range : ℝ) / (2 ^ 8 * T.side) ≤ m := by
    refine le_trans ?_ hr
    have hrn : (0 : ℝ) ≤ R.range := Nat.cast_nonneg _
    have h4 : (4 : ℝ) * T.side ≤ 2 ^ 8 * T.side := by nlinarith
    exact div_le_div_of_nonneg_left hrn (by positivity) h4
  have base : ∀ ν : ℝ, 0 ≤ ν → ν ≤ 1 → ∃ Ψ Ψ' K K', ComparablePotentials s s' Y Y' m T.lam (G₀ * R.coupling) Bd A
      (s.partPotential ν) (s'.partPotential ν) Ψ Ψ' K K' := by
    intro ν h0 h1
    have cs := (H1 y hy1 R hOT n hn s hs).2.1 ν h0 h1
    have cs' := (H1 y hy1 R hOT n' hn' s' hs').2.1 ν h0 h1
    have hσR : 0 < R.params.threshold := by rw [hRσ]; exact hσ
    have hrtR : 0 < R.params.rt := by rw [hRrt]; exact hrt0
    obtain ⟨Ψ, K, e, c, -, r⟩ := htie R T.lam C hσR hrtR hx0 hlam n s _ cs
    obtain ⟨Ψ', K', e', c', -, r'⟩ := htie R T.lam C hσR hrtR hx0 hlam n' s' _ cs'
    rw [hOff] at r r'
    refine ⟨Ψ, Ψ', K, K', ComparablePotentials.of_partPotential hG₀x hC₁0 hBd0 cs cs' e e' c c' r r' ?_⟩
    intro η η' hη hη' hn₂ q h h' X hq hX
    rw [hBdd]
    exact ((H2 y hy2 R hOT n n' hn hn' s s' Y Y' m m η η' hs hs' hag le_rfl hkr hn₂ hη hη' q h h' X hq
      hX).2 hr ν h0 h1)
  obtain ⟨Ψ, Ψ', K, K', g⟩ := exists_comparablePotentials hρR hx hC₁0 hcC hBd0 hag.free_iff base hal
  have hFr' : DependsWithin R.params.side (m / 4) F := by rw [hL]; exact hFr
  have pb := abs_sub_weightedMean_le hcore hodd hρR hx (by rw [hRrt]; exact hrt0.le) hcut hag hBd0
    (by positivity) hA0 g (hWs s) (hWs s') hF hFr' hFo ho
  refine pb.trans ?_
  have hzw : (((innerPart R.params.side (m / 4) (nearFreeIndices s Y (m / 2))).card : ℕ) : ℝ) ≤
      (((nearFreeIndices s Y (m / 2)).card : ℕ) : ℝ) := by
    refine Nat.cast_le.mpr ((Finset.card_le_univ _).trans (le_of_eq (Fintype.card_coe _)))
  have hwP : (((nearFreeIndices s Y (m / 2)).card : ℕ) : ℝ) ≤ ((m : ℝ) + 1) ^ 4 * W4 := by
    have h1 := card_nearFreeIndices_le hodd s Y (m / 2)
    refine h1.trans ?_
    have hLp : (R.params.side : ℝ) = T.side := by rw [hL]
    rw [hW4d, hLp]
    have h2 : (((m / 2 : ℕ) : ℝ)) * 2 + 1 ≤ (m : ℝ) + 1 := by
      have h0 : m / 2 * 2 ≤ m := Nat.div_mul_le_self m 2
      have h3 := Nat.cast_le (α := ℝ).mpr h0
      rw [Nat.cast_mul] at h3
      have h4 : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [h4] at h3
      linarith
    have h5 : ((((m / 2 : ℕ) : ℝ)) * 2 + 1) ^ 4 ≤ ((m : ℝ) + 1) ^ 4 := by gcongr
    have h6 : (0 : ℝ) ≤ (T.side : ℝ) ^ 4 := by positivity
    calc ((((m / 2 : ℕ) : ℝ)) * 2 + 1) ^ 4 * (T.side : ℝ) ^ 4 * 4 ≤
          ((m : ℝ) + 1) ^ 4 * (T.side : ℝ) ^ 4 * 4 := by gcongr
      _ = _ := by ring
  have hmD : (m : ℝ) ≤ 4 * (((m / 2 + 1 - m / 4 : ℕ)) : ℝ) := by
    have h0 : m ≤ 4 * (m / 2 + 1 - m / 4) := by omega
    have h2 := Nat.cast_le (α := ℝ).mpr h0
    rw [Nat.cast_mul] at h2
    have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
    rwa [h4] at h2
  have hNm := N R.coupling hy3 m hr
  rw [hRρ, hRrt]
  exact total_bound_le hrt0.le hρ0.le hA0 hlam.le hx1 hG₀0 hWb0 hW41 ho hGd (Nat.cast_nonneg m) hmD
    (Nat.cast_nonneg _) hzw hwP hBdd hNm
end Main
end LocalMeans
theorem localMeansClose_of_parts (hconv : SettingsUniformlyConvex) (hgrad : SettingGradientsClose)
    (hcore : SharedMarginalMeanBound) (htie : ChartPotentialConvex)
    (hnum : PolynomialBelowExponential) : LocalMeansClose := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LocalMeans.localMeansClose <;> assumption
end ClusterExpansionOfAStep
end
end YangMills.Construction
