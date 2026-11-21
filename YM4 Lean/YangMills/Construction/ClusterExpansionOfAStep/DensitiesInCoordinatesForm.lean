import YangMills.Construction.ClusterExpansionOfAStep.ChartOfFreeBonds
import YangMills.Construction.ClusterExpansionOfAStep.EntriesOfTheDensities
import YangMills.Construction.ClusterExpansionOfAStep.LogarithmOfAMove
import YangMills.Construction.ClusterExpansionOfAStep.NearPotentialAgainstTheCostProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps BondCoordinates ExponentialSums
  StepCosts FieldMoves
namespace Calculus
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
theorem secondDeriv_clm_comp (L : F →L[ℝ] G) {g : E → F} {x : E} (hg : ContDiffAt ℝ 2 g x) (u v : E) :
    fderiv ℝ (fderiv ℝ (L ∘ g)) x u v = L (fderiv ℝ (fderiv ℝ g) x u v) := by apply _root_.YangMills.Construction.QuaternionLogarithm.second_fderiv_clm_comp_apply <;> assumption
theorem secondDeriv_comp_clm {f : F → G} (L : E →L[ℝ] F) {x : E} (hf : ContDiffAt ℝ 2 f (L x)) (u v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ L)) x u v = fderiv ℝ (fderiv ℝ f) (L x) (L u) (L v) := by
  have hL : fderiv ℝ (L : E → F) = fun _ => L := funext fun p => L.fderiv
  rw [secondDeriv_comp hf L.contDiff.contDiffAt, hL]
  simp
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem contDiffAt_pi_apply_zero {ξ : ι → E → G} {k : WithTop ℕ∞} (hξ : ∀ b, ContDiffAt ℝ k (ξ b) 0) :
    ContDiffAt ℝ k (fun (v : ι → E) b => ξ b (v b)) 0 := by
  refine contDiffAt_pi.mpr fun b => ?_
  have h1 : ContDiffAt ℝ k (ξ b) ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => E) b) 0) := by
    simpa using hξ b
  exact h1.comp (0 : ι → E) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => E) b).contDiff.contDiffAt
theorem fderiv_pi_apply_zero {ξ : ι → E → G} (hξ : ∀ b, ContDiffAt ℝ 2 (ξ b) 0) (u : ι → E) (b : ι) :
    fderiv ℝ (fun (v : ι → E) b => ξ b (v b)) 0 u b = fderiv ℝ (ξ b) 0 (u b) := by
  set Φ : (ι → E) → ι → G := fun v b => ξ b (v b) with hΦ
  have hC : ContDiffAt ℝ 2 Φ 0 := contDiffAt_pi_apply_zero hξ
  set πb := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => G) b with hπ
  set pb := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => E) b with hp
  have e : πb ∘ Φ = ξ b ∘ pb := rfl
  have h1 : fderiv ℝ (πb ∘ Φ) 0 u = πb (fderiv ℝ Φ 0 u) := by
    rw [fderiv_comp (0 : ι → E) πb.differentiableAt (hC.differentiableAt (by norm_num))]
    simp
  have hx : ContDiffAt ℝ 2 (ξ b) (pb 0) := by simpa using hξ b
  have h2 : fderiv ℝ (ξ b ∘ pb) 0 u = fderiv ℝ (ξ b) 0 (u b) := by
    rw [fderiv_comp (0 : ι → E) (hx.differentiableAt (by norm_num)) pb.differentiableAt]
    simp [hp]
  rw [e, h2] at h1
  exact h1.symm
theorem secondDeriv_pi_apply_zero {ξ : ι → E → G} (hξ : ∀ b, ContDiffAt ℝ 2 (ξ b) 0) (u v : ι → E) (b : ι) :
    fderiv ℝ (fderiv ℝ (fun (v : ι → E) b => ξ b (v b))) 0 u v b =
      fderiv ℝ (fderiv ℝ (ξ b)) 0 (u b) (v b) := by
  set Φ : (ι → E) → ι → G := fun v b => ξ b (v b) with hΦ
  have hC : ContDiffAt ℝ 2 Φ 0 := contDiffAt_pi_apply_zero hξ
  set πb := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => G) b with hπ
  set pb := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => E) b with hp
  have e : πb ∘ Φ = ξ b ∘ pb := rfl
  have hx : ContDiffAt ℝ 2 (ξ b) (pb 0) := by simpa using hξ b
  have h1 := secondDeriv_clm_comp πb hC u v
  have h2 := secondDeriv_comp_clm pb hx u v
  rw [e, h2] at h1
  exact show πb (fderiv ℝ (fderiv ℝ Φ) 0 u v) = fderiv ℝ (fderiv ℝ (ξ b)) 0 (u b) (v b) from by
    rw [← h1]
    simp [hp]
theorem fderiv_comp_add_left_eq (g : E → F) (p : E) :
    fderiv ℝ (fun v => g (p + v)) = fun v => fderiv ℝ g (p + v) := by
  funext v
  exact fderiv_comp_add_left p
theorem contDiffAt_of_comp_add_left {g : E → F} {p : E} {k : WithTop ℕ∞}
    (h : ContDiffAt ℝ k (fun v => g (p + v)) 0) : ContDiffAt ℝ k g p := by
  have h1 : ContDiffAt ℝ k (fun y : E => y - p) p := contDiffAt_id.sub contDiffAt_const
  have h2 : ContDiffAt ℝ k (fun v => g (p + v)) ((fun y : E => y - p) p) := by simpa using h
  have h3 : ContDiffAt ℝ k (fun y : E => (fun v => g (p + v)) (y - p)) p :=
    ContDiffAt.comp (f := fun y : E => y - p) p h2 h1
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp
end Calculus
namespace StepSettings
open Calculus
section Coordinates
variable {m : ℕ} {free : Finset (TorusBond m)}
theorem update_add_smul_eq (η : FreeCoords free) (b : free) (X : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    Function.update η b (η b + t • X) = η + t • (Pi.single b X : FreeCoords free) := by
  funext c
  by_cases hc : c = b
  · subst hc
    simp
  · simp [Function.update_of_ne hc, Pi.single_apply, hc]
theorem deriv_update_line_eq {u : FreeCoords free → ℝ} {η : FreeCoords free} (hu : DifferentiableAt ℝ u η)
    (b : free) (X : EuclideanSpace ℝ (Fin 3)) :
    deriv (fun t : ℝ => u (Function.update η b (η b + t • X))) 0 =
      fderiv ℝ u η (Pi.single b X : FreeCoords free) := by
  simp only [update_add_smul_eq]
  exact (hasDerivAt_comp_line η _ 0 (by simpa using hu)).deriv.trans (by simp)
theorem mixedSecondDeriv_eq_secondDeriv {u : FreeCoords free → ℝ} {η : FreeCoords free}
    (hu : ContDiffAt ℝ 2 u η) (b b' : free) (X X' : EuclideanSpace ℝ (Fin 3)) :
    mixedSecondDeriv u η b b' X X' = fderiv ℝ (fderiv ℝ u) η (Pi.single b X : FreeCoords free)
      (Pi.single b' X' : FreeCoords free) := by
  set e₁ : FreeCoords free := Pi.single b X with he₁
  set e₂ : FreeCoords free := Pi.single b' X' with he₂
  have hcont : Filter.Tendsto (fun t : ℝ => η + t • e₁) (nhds 0) (nhds η) := by
    have : Continuous fun t : ℝ => η + t • e₁ := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ t in nhds (0 : ℝ), ContDiffAt ℝ 2 u (η + t • e₁) :=
    hcont.eventually (hu.eventually (by norm_num))
  have hinner : (fun t : ℝ => deriv (fun t' : ℝ => u (Function.update (Function.update η b (η b + t • X)) b'
      ((Function.update η b (η b + t • X)) b' + t' • X'))) 0) =ᶠ[nhds 0]
      fun t => fderiv ℝ u (η + t • e₁) e₂ := by
    filter_upwards [hev] with t ht
    simp only [update_add_smul_eq]
    have := deriv_update_line_eq (ht.differentiableAt (by norm_num)) b' X'
    simp only [update_add_smul_eq] at this
    exact this
  unfold mixedSecondDeriv
  rw [hinner.deriv_eq]
  have hd2 : DifferentiableAt ℝ (fderiv ℝ u) (η + (0 : ℝ) • e₁) := by
    simpa using (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 := hasDerivAt_comp_line (G := fderiv ℝ u) η e₁ 0 hd2
  have h2 := (ContinuousLinearMap.apply ℝ ℝ e₂).hasFDerivAt.comp_hasDerivAt 0 h1
  have h3 : HasDerivAt (fun t : ℝ => fderiv ℝ u (η + t • e₁) e₂)
      (fderiv ℝ (fderiv ℝ u) (η + (0 : ℝ) • e₁) e₁ e₂) 0 := h2
  simpa using h3.deriv
end Coordinates
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n}
def ChartSetting.pointAt (s : ChartSetting R n) (η : FreeCoords s.free) (b : s.free) : imaginaryQuaternions :=
  s.frame b.1 + toImaginary (η b)
def ChartSetting.startGauge (s : ChartSetting R n) (b : s.free) : UnitQuaternion := gaugeAt s.fine b.1.1
def ChartSetting.logMoves (s : ChartSetting R n) (η : FreeCoords s.free) (v : FreeCoords s.free) :
    s.free → imaginaryQuaternions :=
  fun b => bondLogMove (s.pointAt η b) (s.startGauge b) (v b)
theorem chartLink_add_toImaginary (s : ChartSetting R n) (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (w : imaginaryQuaternions) (u : EuclideanSpace ℝ (Fin 3)) :
    chartLink s x i (w + toImaginary u) = bondMove w (gaugeAt s.fine x) u * chartLink s x i w := by
  unfold chartLink bondMove
  split_ifs <;> group
theorem ChartSetting.field_add_eventually (s : ChartSetting R n) (η : FreeCoords s.free) :
    ∀ᶠ v in nhds (0 : FreeCoords s.free), s.field (η + v) = s.expOnFree (s.logMoves η v) (s.field η) := by
  have hb : ∀ b : s.free, ∀ᶠ v in nhds (0 : FreeCoords s.free),
      expUnit (bondLogMove (s.pointAt η b) (s.startGauge b) (v b)) =
        bondMove (s.pointAt η b) (s.startGauge b) (v b) := fun b => by
    have ht : Filter.Tendsto (fun v : FreeCoords s.free => v b) (nhds 0) (nhds 0) := by
      have := (continuous_apply b).tendsto (0 : FreeCoords s.free)
      simpa using this
    exact ht.eventually (expUnit_bondLogMove _ _)
  filter_upwards [Filter.eventually_all.mpr hb] with v hv
  funext x i
  by_cases h : (x, i) ∈ s.free
  · have f1 : s.field (η + v) x i =
        chartLink s x i (s.frame (x, i) + toImaginary ((η + v) ⟨(x, i), h⟩)) := dif_pos h
    have f2 : s.field η x i = chartLink s x i (s.frame (x, i) + toImaginary (η ⟨(x, i), h⟩)) := dif_pos h
    have f3 : s.expOnFree (s.logMoves η v) (s.field η) x i =
        expUnit (s.logMoves η v ⟨(x, i), h⟩) * s.field η x i := dif_pos h
    have e : s.frame (x, i) + toImaginary ((η + v) ⟨(x, i), h⟩) =
        s.pointAt η ⟨(x, i), h⟩ + toImaginary (v ⟨(x, i), h⟩) := by
      simp only [ChartSetting.pointAt, Pi.add_apply]
      rw [← toImaginaryCLM_apply, map_add, toImaginaryCLM_apply, toImaginaryCLM_apply, add_assoc]
    rw [f1, f3, f2, e, chartLink_add_toImaginary]
    have := hv ⟨(x, i), h⟩
    simp only [ChartSetting.logMoves]
    rw [this]
    rfl
  · have f1 : s.field (η + v) x i = s.fine x i := s.field_apply_of_not_mem _ x i h
    have f2 : s.field η x i = s.fine x i := s.field_apply_of_not_mem _ x i h
    have f3 : s.expOnFree (s.logMoves η v) (s.field η) x i = s.field η x i := dif_neg h
    rw [f1, f3, f2]
theorem norm_minimizingCoordinates_le {F : BlockFrame} {a ρ : ℝ} (hρ : 0 ≤ ρ) (S : Finset F.Cell)
    (V : F.GaugeField F.top) (x : F.Site F.depth) (i : Fin 4) : ‖minimizingCoordinates a S V ρ x i‖ ≤ ρ := by
  classical
  unfold minimizingCoordinates
  split_ifs with hh
  · obtain ⟨h0, h1, -⟩ := hh.choose_spec
    by_cases hb : (x, i) ∈ chordBonds S
    · exact h1 _ hb
    · have := h0 _ hb
      simp only at this
      rw [this]
      simpa using hρ
  · simpa using hρ
theorem ChartSetting.norm_frame_le (s : ChartSetting R n) (hρ : 0 ≤ R.anchorRadius)
    (b : TorusBond (n * R.params.side)) : ‖s.frame b‖ ≤ R.anchorRadius := by
  unfold ChartSetting.frame frameCoord bondFrameCoord
  split_ifs
  · exact norm_minimizingCoordinates_le hρ _ _ _ _
  · exact norm_minimizingCoordinates_le hρ _ _ _ _
theorem ChartSetting.Hypotheses.isNear_field (h : s.Hypotheses) {η : FreeCoords s.free} (hη : s.InBalls η) :
    s.IsNear (R.params.threshold / 4) (s.field η) :=
  ⟨h.isAdmissible.hotLumps_eq η hη, fun x i hx => s.field_apply_of_not_mem η x i hx,
    h.isAdmissible.curvature_lt η hη⟩
theorem ChartSetting.Hypotheses.norm_pointAt_le (_h : s.Hypotheses) (hρ0 : 0 ≤ R.anchorRadius)
    (hρ1 : R.anchorRadius ≤ 1) (hσ : R.params.threshold ≤ 1) {η : FreeCoords s.free} (hη : s.InBalls η)
    (b : s.free) : ‖s.pointAt η b‖ ≤ 3 := by
  have h1 := s.norm_frame_le hρ0 b.1
  have h2 : ‖toImaginary (η b)‖ ≤ R.ballRadius := hη b
  have h3 : R.ballRadius ≤ 1 := by
    unfold StepSetup.ballRadius
    linarith
  exact (norm_add_le _ _).trans (by linarith)
theorem ChartSetting.Hypotheses.totalDensity_coords (h : s.Hypotheses) {N₃ : ℝ} (hA : s.ActionSmooth N₃)
    {η : FreeCoords s.free} (hη : s.InBalls η) :
    ContDiffAt ℝ 3 (s.chartFn s.densityAt (s.field η)) 0 ∧ ContDiffAt ℝ 3 s.totalDensity η ∧
      (∀ u, fderiv ℝ s.totalDensity η u =
        fderiv ℝ (s.chartFn s.densityAt (s.field η)) 0 (fderiv ℝ (s.logMoves η) 0 u)) ∧
      ∀ u v, fderiv ℝ (fderiv ℝ s.totalDensity) η u v =
        fderiv ℝ (fderiv ℝ (s.chartFn s.densityAt (s.field η))) 0 (fderiv ℝ (s.logMoves η) 0 u)
            (fderiv ℝ (s.logMoves η) 0 v) +
          fderiv ℝ (s.chartFn s.densityAt (s.field η)) 0 (fderiv ℝ (fderiv ℝ (s.logMoves η)) 0 u v) := by
  have hg := h.isNear_field hη
  have hσ := h.threshold_pos
  have hf : ContDiffAt ℝ 3 (s.chartFn s.densityAt (s.field η)) 0 :=
    ChartSetting.contDiffAt_chartFn fun k c X hc => (hg.densityAt_smooth h hA (by linarith) hc X).1
  have hΞ : ContDiffAt ℝ 3 (s.logMoves η) 0 :=
    contDiffAt_pi_apply_zero (ξ := fun b : s.free => bondLogMove (s.pointAt η b) (s.startGauge b))
      fun b => contDiffAt_bondLogMove _ _
  have hΞ0 : s.logMoves η 0 = 0 := by
    funext b
    exact bondLogMove_zero _ _
  have hf' : ContDiffAt ℝ 3 (s.chartFn s.densityAt (s.field η)) (s.logMoves η 0) := by rwa [hΞ0]
  have hH : ContDiffAt ℝ 3 (s.chartFn s.densityAt (s.field η) ∘ s.logMoves η) 0 := hf'.comp 0 hΞ
  have ev : (fun v => s.totalDensity (η + v)) =ᶠ[nhds 0]
      s.chartFn s.densityAt (s.field η) ∘ s.logMoves η := by
    filter_upwards [s.field_add_eventually η] with v hv
    simp only [Function.comp, ChartSetting.chartFn, ChartSetting.totalDensity_eq_densityAt, hv]
  have hG : ContDiffAt ℝ 3 (fun v => s.totalDensity (η + v)) 0 := hH.congr_of_eventuallyEq ev
  have hf2 : ContDiffAt ℝ 2 (s.chartFn s.densityAt (s.field η)) (s.logMoves η 0) := hf'.of_le (by norm_num)
  have hΞ2 : ContDiffAt ℝ 2 (s.logMoves η) 0 := hΞ.of_le (by norm_num)
  refine ⟨hf, contDiffAt_of_comp_add_left hG, fun u => ?_, fun u v => ?_⟩
  · have e1 : fderiv ℝ s.totalDensity η = fderiv ℝ (fun v => s.totalDensity (η + v)) 0 := by
      rw [fderiv_comp_add_left_eq]
      simp
    rw [e1, ev.fderiv_eq, fderiv_comp 0 (hf2.differentiableAt (by norm_num))
      (hΞ2.differentiableAt (by norm_num)), hΞ0]
    rfl
  · have e1 : fderiv ℝ (fderiv ℝ s.totalDensity) η =
        fderiv ℝ (fderiv ℝ (fun v => s.totalDensity (η + v))) 0 := by
      rw [fderiv_comp_add_left_eq, fderiv_comp_add_left_eq]
      simp
    rw [e1, (Filter.EventuallyEq.fderiv ev).fderiv_eq, secondDeriv_comp hf2 hΞ2, hΞ0]
theorem ChartSetting.fderiv_logMoves_single (s : ChartSetting R n) (η : FreeCoords s.free) (b : s.free)
    (X : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (s.logMoves η) 0 (Pi.single b X : FreeCoords s.free) =
      Pi.single b (fderiv ℝ (bondLogMove (s.pointAt η b) (s.startGauge b)) 0 X) := by
  funext b₁
  have hξ : ∀ b : s.free, ContDiffAt ℝ 2 (bondLogMove (s.pointAt η b) (s.startGauge b)) 0 := fun b =>
    (contDiffAt_bondLogMove _ _).of_le (by norm_num)
  have h1 := fderiv_pi_apply_zero hξ (Pi.single b X : FreeCoords s.free) b₁
  refine h1.trans ?_
  by_cases hb : b₁ = b
  · subst hb
    simp
  · simp [Pi.single_apply, hb]
theorem ChartSetting.secondDeriv_logMoves_single (s : ChartSetting R n) (η : FreeCoords s.free) (b b' : s.free)
    (X X' : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fderiv ℝ (s.logMoves η)) 0 (Pi.single b X : FreeCoords s.free)
        (Pi.single b' X' : FreeCoords s.free) =
      if b = b' then Pi.single b (fderiv ℝ (fderiv ℝ (bondLogMove (s.pointAt η b) (s.startGauge b))) 0 X X')
      else 0 := by
  funext b₁
  have hξ : ∀ b : s.free, ContDiffAt ℝ 2 (bondLogMove (s.pointAt η b) (s.startGauge b)) 0 := fun b =>
    (contDiffAt_bondLogMove _ _).of_le (by norm_num)
  have h1 := secondDeriv_pi_apply_zero hξ (Pi.single b X : FreeCoords s.free)
    (Pi.single b' X' : FreeCoords s.free) b₁
  refine h1.trans ?_
  by_cases hbb : b = b'
  · subst hbb
    rw [if_pos rfl]
    by_cases hb : b₁ = b
    · subst hb
      simp
    · simp [Pi.single_apply, hb]
  · rw [if_neg hbb]
    by_cases hb : b₁ = b
    · subst hb
      have : b₁ ≠ b' := hbb
      simp [Pi.single_apply, this]
    · simp [Pi.single_apply, hb]
variable {τ : ℝ} {W : TorusField (n * R.params.side)}
theorem ChartSetting.Hypotheses.abs_secondDeriv_chartFn_le (h : s.Hypotheses) {N₃ : ℝ} (hA : s.ActionSmooth N₃)
    (hN₃ : 0 ≤ N₃) (hτ : 0 < τ)
    (hstep : ∀ a : imaginaryQuaternions, ‖a‖ ≤ 2 * τ →
      ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ R.params.threshold / 64)
    (hx : 0 ≤ R.coupling) (hCd : 0 ≤ R.params.derivBound) (hg : s.IsNear (R.params.threshold / 4) W)
    (hf : ContDiffAt ℝ 3 (s.chartFn s.densityAt W) 0) (b b' : s.free) (P P' : imaginaryQuaternions)
    (hP : ‖P‖ = 1) (hP' : ‖P'‖ = 1) (hc : b ≠ b' ∨ P = P') :
    |fderiv ℝ (fderiv ℝ (s.chartFn s.densityAt W)) 0 (Pi.single b P) (Pi.single b' P')| ≤
      (R.mainConstant + R.tailConstant τ N₃ * Real.exp (-R.params.decayRate * R.range / 64)) *
        Real.exp (-(R.params.decayRate / 32) * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) := by
  have hu : AreUnitVectors ![P, P'] := by
    intro l
    fin_cases l
    · exact hP
    · exact hP'
  have hcomm : CommutingPair (fun l => ((![b, b'] l : s.free) : TorusBond (n * R.params.side))) ![P, P'] := by
    rcases hc with hc | hc
    · left
      exact fun e => hc (Subtype.ext e)
    · right
      exact hc
  have key := h.abs_mixedDeriv_le_exp hA hN₃ hτ hstep hx hCd hg
    (c := fun l => ((![b, b'] l : s.free) : TorusBond (n * R.params.side)))
    (X := ![P, P']) (fun l => (![b, b'] l).2) hu hcomm
  rw [ChartSetting.iteratedFDeriv_two_alongPair hf ![b, b'] ![P, P']] at key
  exact key
theorem ChartSetting.Hypotheses.abs_fderiv_chartFn_le (h : s.Hypotheses) {N₃ : ℝ} (hA : s.ActionSmooth N₃)
    (hN₃ : 0 ≤ N₃) (hτ : 0 < τ)
    (hstep : ∀ a : imaginaryQuaternions, ‖a‖ ≤ 2 * τ →
      ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ R.params.threshold / 64)
    (hx : 0 ≤ R.coupling) (hCd : 0 ≤ R.params.derivBound) (hg : s.IsNear (R.params.threshold / 4) W)
    (hf : ContDiffAt ℝ 3 (s.chartFn s.densityAt W) 0) (b : s.free) (P : imaginaryQuaternions) (hP : ‖P‖ = 1) :
    |fderiv ℝ (s.chartFn s.densityAt W) 0 (Pi.single b P)| ≤
      R.params.E * expLatticeSum R.params.weightRate +
        R.firstTailConstant τ N₃ * Real.exp (-R.params.decayRate * R.range / 8) := by
  have hu : AreUnitVectors ![P, P] := by
    intro l
    fin_cases l <;> exact hP
  have key := h.abs_firstDeriv_le hA hN₃ hτ hstep hx hCd hg
    (c := fun l => ((![b, b] l : s.free) : TorusBond (n * R.params.side)))
    (X := ![P, P]) (fun l => (![b, b] l).2) hu (Or.inr rfl) rfl
  rw [ChartSetting.iteratedFDeriv_one_alongPair hf ![b, b] ![P, P]] at key
  exact key
theorem block_exp_arith {rt c d bd L : ℝ} (hrt : 0 < rt) (hc : c = rt / 2 ^ 18) (hd : 0 ≤ d) (hbd : 0 ≤ bd)
    (hL : 2 ^ 19 ≤ L) (hb : L * bd ≤ d + L) : 2 * rt * bd ≤ c * d + 2 * rt := by
  have h1 : (bd - 1) * 2 ^ 19 ≤ d := by
    by_cases h : 1 ≤ bd
    · have : (bd - 1) * 2 ^ 19 ≤ (bd - 1) * L := mul_le_mul_of_nonneg_left hL (by linarith)
      nlinarith
    · have : bd - 1 < 0 := by linarith
      nlinarith
  rw [hc]
  nlinarith
theorem ChartSetting.Hypotheses.isPotentialPiece_totalDensity (h : s.Hypotheses) {N₃ : ℝ}
    (hA : s.ActionSmooth N₃) (hN₃ : 0 ≤ N₃) (hτ : 0 < τ)
    (hstep : ∀ a : imaginaryQuaternions, ‖a‖ ≤ 2 * τ →
      ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ R.params.threshold / 64)
    (hx : 0 ≤ R.coupling) (hCd : 0 ≤ R.params.derivBound) {C : ℝ} (hC : 0 < C)
    (hξ : ∀ (w : imaginaryQuaternions) (t : UnitQuaternion), ‖w‖ ≤ 3 →
      (∀ u, ‖fderiv ℝ (bondLogMove w t) 0 u‖ ≤ C * ‖u‖) ∧
      ∀ u v, ‖fderiv ℝ (fderiv ℝ (bondLogMove w t)) 0 u v‖ ≤ C * ‖u‖ * ‖v‖)
    (hw : ∀ η, s.InBalls η → ∀ b, ‖s.pointAt η b‖ ≤ 3) (hL : 2 ^ 19 ≤ R.params.side) :
    s.IsPotentialPiece s.totalDensity
      (2 * (R.mainConstant + R.tailConstant τ N₃ * Real.exp (-R.params.decayRate * R.range / 64)) * C ^ 2 *
          (Real.exp (2 * R.params.rt) * (4 * expLatticeSum (R.params.decayRate / 64))) +
        (R.params.E * expLatticeSum R.params.weightRate +
          R.firstTailConstant τ N₃ * Real.exp (-R.params.decayRate * R.range / 8)) * C) := by
  set A := R.mainConstant + R.tailConstant τ N₃ * Real.exp (-R.params.decayRate * R.range / 64) with hAdef
  set K₁ := R.params.E * expLatticeSum R.params.weightRate +
    R.firstTailConstant τ N₃ * Real.exp (-R.params.decayRate * R.range / 8) with hK₁
  have hδ := decayRate_pos h
  have hrt := h.admissible.rt_pos
  have hA0 : 0 ≤ A := add_nonneg (mainConstant_nonneg h)
    (mul_nonneg (tailConstant_nonneg h hτ hN₃ hx hCd) (Real.exp_pos _).le)
  have hK0 : 0 ≤ K₁ := by
    have hD := differenceConstant_nonneg h
    have hLr : 0 < expLatticeSum R.params.weightRate := expLatticeSum_pos (weightRate_pos h)
    have hE := h.admissible.E_pos
    have : 0 ≤ R.firstTailConstant τ N₃ := by
      unfold StepSetup.firstTailConstant
      positivity
    positivity
  have hLc : 0 < expLatticeSum (R.params.decayRate / 64) := expLatticeSum_pos (by linarith)
  have entry : ∀ η, s.InBalls η → ∀ (b b' : s.free) X X', ‖X‖ = 1 → ‖X'‖ = 1 →
      |mixedSecondDeriv s.totalDensity η b b' X X'| ≤
        2 * (A * Real.exp (-(R.params.decayRate / 32) * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1)) * C ^ 2 +
          if b = b' then K₁ * C else 0 := by
    intro η hη b b' X X' hX hX'
    obtain ⟨hf, hsm, -, h2⟩ := h.totalDensity_coords hA hη
    have hg := h.isNear_field hη
    rw [mixedSecondDeriv_eq_secondDeriv (hsm.of_le (by norm_num)), h2, s.fderiv_logMoves_single,
      s.fderiv_logMoves_single, s.secondDeriv_logMoves_single]
    have ha := (hξ _ (s.startGauge b) (hw η hη b)).1 X
    have ha' := (hξ _ (s.startGauge b') (hw η hη b')).1 X'
    rw [hX, mul_one] at ha
    rw [hX', mul_one] at ha'
    have hM0 : 0 ≤ A * Real.exp (-(R.params.decayRate / 32) * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) := by positivity
    have t1 := ChartSetting.abs_secondDeriv_single_le hf b b' (fun P P' hP hP' hc =>
      h.abs_secondDeriv_chartFn_le hA hN₃ hτ hstep hx hCd hg hf b b' P P' hP hP' hc) hM0
      (fderiv ℝ (bondLogMove (s.pointAt η b) (s.startGauge b)) 0 X)
      (fderiv ℝ (bondLogMove (s.pointAt η b') (s.startGauge b')) 0 X')
    have t1' : |fderiv ℝ (fderiv ℝ (s.chartFn s.densityAt (s.field η))) 0
        (Pi.single b (fderiv ℝ (bondLogMove (s.pointAt η b) (s.startGauge b)) 0 X))
        (Pi.single b' (fderiv ℝ (bondLogMove (s.pointAt η b') (s.startGauge b')) 0 X'))| ≤
        2 * (A * Real.exp (-(R.params.decayRate / 32) * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1)) * C ^ 2 := by
      refine t1.trans ?_
      have n2 := norm_nonneg (fderiv ℝ (bondLogMove (s.pointAt η b') (s.startGauge b')) 0 X')
      calc _ = 2 * (A * Real.exp (-(R.params.decayRate / 32) * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1)) *
            (‖fderiv ℝ (bondLogMove (s.pointAt η b) (s.startGauge b)) 0 X‖ *
              ‖fderiv ℝ (bondLogMove (s.pointAt η b') (s.startGauge b')) 0 X'‖) := by ring
        _ ≤ 2 * (A * Real.exp (-(R.params.decayRate / 32) * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1)) * (C * C) :=
            mul_le_mul_of_nonneg_left (mul_le_mul ha ha' n2 hC.le) (by positivity)
        _ = _ := by ring
    refine (abs_add_le _ _).trans (add_le_add t1' ?_)
    by_cases hbb : b = b'
    · subst hbb
      simp only [if_true]
      have t2 := ChartSetting.abs_firstDeriv_single_le (f := s.chartFn s.densityAt (s.field η)) b
        (fun P hP => h.abs_fderiv_chartFn_le hA hN₃ hτ hstep hx hCd hg hf b P hP)
        (fderiv ℝ (fderiv ℝ (bondLogMove (s.pointAt η b) (s.startGauge b))) 0 X X')
      have t3 := (hξ _ (s.startGauge b) (hw η hη b)).2 X X'
      rw [hX, hX', mul_one, mul_one] at t3
      exact t2.trans (mul_le_mul_of_nonneg_left t3 hK0)
    · simp [if_neg hbb]
  obtain ⟨hsm0⟩ : Nonempty (∀ η, s.InBalls η → ContDiffAt ℝ 3 s.totalDensity η) :=
    ⟨fun η hη => (h.totalDensity_coords hA hη).2.1⟩
  refine ⟨hsm0, ⟨fun b b' => 2 * (A * Real.exp (-(R.params.decayRate / 32) * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1)) * C ^ 2 +
    if b = b' then K₁ * C else 0, entry, fun b => ?_⟩, ?_⟩
  · have hc2 : R.params.decayRate / 64 = R.params.rt / 2 ^ 18 := by
      unfold StepParameters.decayRate
      ring
    have term : ∀ b' : s.free, Real.exp (-(R.params.decayRate / 32) * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) *
        Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) ≤
        Real.exp (2 * R.params.rt) * Real.exp (-(R.params.decayRate / 64) * _root_.YangMills.Construction.TorusFields.supDist b'.1.1 b.1.1) := by
      intro b'
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hb0 := _root_.YangMills.Construction.ExponentialSums.supDist_parentBlock_le R.params.side b.1.1 b'.1.1
      have hb1 : (R.params.side : ℝ) * (bondBlockDist (R := R) (n := n) b.1 b'.1 : ℝ) ≤
          (_root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1 : ℝ) + R.params.side := by exact_mod_cast hb0
      have hLr : (2 : ℝ) ^ 19 ≤ R.params.side := by exact_mod_cast hL
      have := block_exp_arith hrt hc2 (by positivity) (by positivity) hLr hb1
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm b'.1.1 b.1.1]
      nlinarith
    have sum1 : ∑ b' : s.free, Real.exp (-(R.params.decayRate / 32) * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) *
        Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) ≤
        Real.exp (2 * R.params.rt) * (4 * expLatticeSum (R.params.decayRate / 64)) := by
      refine (Finset.sum_le_sum fun b' _ => term b').trans ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have h3 := sum_bonds_exp_le (c := R.params.decayRate / 64) (by linarith) b.1.1 s.free
      rw [← Finset.sum_coe_sort s.free
        (fun β => Real.exp (-(R.params.decayRate / 64) * _root_.YangMills.Construction.TorusFields.supDist β.1 b.1.1))] at h3
      exact h3
    have sum2 : ∑ b' : s.free, (if b = b' then K₁ * C else 0) *
        Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) = K₁ * C := by
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq Finset.univ b]
      simp [bondBlockDist, _root_.YangMills.Construction.TorusFields.supDist_self]
    simp only [add_mul]
    rw [Finset.sum_add_distrib, sum2]
    refine add_le_add ?_ le_rfl
    have e : ∀ b' : s.free, 2 * (A * Real.exp (-(R.params.decayRate / 32) * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1)) * C ^ 2 *
        Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) =
        2 * A * C ^ 2 * (Real.exp (-(R.params.decayRate / 32) * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) *
          Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1)) := fun b' => by ring
    simp only [e]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left sum1 (by positivity)
  · intro η hη b X hX
    obtain ⟨hf, hsm, h1, -⟩ := h.totalDensity_coords hA hη
    have hg := h.isNear_field hη
    rw [deriv_update_line_eq (hsm.differentiableAt (by norm_num)), h1, s.fderiv_logMoves_single]
    have ha := (hξ _ (s.startGauge b) (hw η hη b)).1 X
    rw [hX, mul_one] at ha
    have t2 := ChartSetting.abs_firstDeriv_single_le (f := s.chartFn s.densityAt (s.field η)) b
      (fun P hP => h.abs_fderiv_chartFn_le hA hN₃ hτ hstep hx hCd hg hf b P hP)
      (fderiv ℝ (bondLogMove (s.pointAt η b) (s.startGauge b)) 0 X)
    have t3 : |fderiv ℝ (s.chartFn s.densityAt (s.field η)) 0
        (Pi.single b (fderiv ℝ (bondLogMove (s.pointAt η b) (s.startGauge b)) 0 X))| ≤ K₁ * C :=
      t2.trans (mul_le_mul_of_nonneg_left ha hK0)
    have t4 : 0 ≤ 2 * A * C ^ 2 * (Real.exp (2 * R.params.rt) * (4 * expLatticeSum (R.params.decayRate / 64))) := by
      positivity
    linarith
theorem potential_size_arith {A₀ e₁ Cx Z T₁ F₁ P₁ P₂ x g₁ g₂ C₀ P C E₃ : ℝ} (hA₀ : 0 ≤ A₀) (he₁ : 0 ≤ e₁)
    (hCx : 0 < Cx) (hZ : 0 ≤ Z) (hT : T₁ ≤ P₁ * x ^ 3) (hF : F₁ ≤ P₂ * x ^ 3) (hg₁ : 0 < g₁) (hg₂ : 0 < g₂)
    (hg : g₂ ≤ g₁) (hF0 : 0 ≤ F₁) (hC₀ : C₀ = 2 * A₀ * Cx ^ 2 * Z + e₁ * Cx)
    (hP : P = 2 * P₁ * Cx ^ 2 * Z + P₂ * Cx) (hPx : P ≤ x) (hx : 1 ≤ x) (hC₀C : C₀ ≤ C) (hC4 : 4 ≤ C)
    (hE₃ : 0 ≤ E₃) :
    2 * (A₀ + T₁ * g₁) * Cx ^ 2 * Z + (e₁ + F₁ * g₂) * Cx ≤ C * (1 + E₃) + x ^ C * g₁ := by
  have hx3 : 0 < x ^ 3 := by positivity
  have a1 : 2 * (T₁ * g₁) * Cx ^ 2 * Z ≤ 2 * (P₁ * x ^ 3 * g₁) * Cx ^ 2 * Z := by
    have : T₁ * g₁ ≤ P₁ * x ^ 3 * g₁ := mul_le_mul_of_nonneg_right hT hg₁.le
    have hk : 0 ≤ 2 * Cx ^ 2 * Z := by positivity
    nlinarith
  have a2 : F₁ * g₂ * Cx ≤ P₂ * x ^ 3 * g₁ * Cx := by
    have b1 : F₁ * g₂ ≤ F₁ * g₁ := mul_le_mul_of_nonneg_left hg hF0
    have b2 : F₁ * g₁ ≤ P₂ * x ^ 3 * g₁ := mul_le_mul_of_nonneg_right hF hg₁.le
    exact mul_le_mul_of_nonneg_right (b1.trans b2) hCx.le
  have a3 : P * x ^ 3 * g₁ ≤ x ^ 4 * g₁ := by
    have : P * x ^ 3 ≤ x * x ^ 3 := mul_le_mul_of_nonneg_right hPx hx3.le
    have e : x * x ^ 3 = x ^ 4 := by ring
    rw [e] at this
    exact mul_le_mul_of_nonneg_right this hg₁.le
  have a4 : x ^ 4 * g₁ ≤ x ^ C * g₁ := by
    have : x ^ (4 : ℝ) ≤ x ^ C := Real.rpow_le_rpow_of_exponent_le hx hC4
    have e : x ^ (4 : ℝ) = x ^ 4 := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [e] at this
    exact mul_le_mul_of_nonneg_right this hg₁.le
  have a5 : C₀ ≤ C * (1 + E₃) := by
    have : 0 ≤ C * E₃ := by positivity
    nlinarith
  have e1 : 2 * (A₀ + T₁ * g₁) * Cx ^ 2 * Z + (e₁ + F₁ * g₂) * Cx =
      C₀ + 2 * (T₁ * g₁) * Cx ^ 2 * Z + F₁ * g₂ * Cx := by
    rw [hC₀]
    ring
  have e2 : 2 * (P₁ * x ^ 3 * g₁) * Cx ^ 2 * Z + P₂ * x ^ 3 * g₁ * Cx = P * x ^ 3 * g₁ := by
    rw [hP]
    ring
  rw [e1]
  linarith
theorem cube_poly_le {a b c x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : 1 ≤ x) :
    (a * x) ^ 3 + x * b + c ≤ (a ^ 3 + b + c) * x ^ 3 := by
  have h1 : x ≤ x ^ 3 := by nlinarith [sq_nonneg x, mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hx)]
  have e : (a * x) ^ 3 = a ^ 3 * x ^ 3 := by ring
  rw [e]
  nlinarith
theorem square_poly_le {a b c x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : 1 ≤ x) :
    (a * x) ^ 2 + x * b + c ≤ (a ^ 2 + b + c) * x ^ 3 := by
  have h1 : x ≤ x ^ 2 := by nlinarith
  have h0 : x ^ 2 ≤ x ^ 3 := by nlinarith [sq_nonneg x]
  have e : (a * x) ^ 2 = a ^ 2 * x ^ 2 := by ring
  have h3 : a ^ 2 * x ^ 2 ≤ a ^ 2 * x ^ 3 := mul_le_mul_of_nonneg_left h0 (by positivity)
  have h4 : x * b ≤ x ^ 3 * b := mul_le_mul_of_nonneg_right (h1.trans h0) hb
  have h5 : c ≤ x ^ 3 * c := by nlinarith
  rw [e]
  nlinarith
theorem le_clusterRange {x : ℝ} {B : ℕ} (hx : (B : ℝ) ^ 100 ≤ x) : B ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.NearPotentialBound.le_clusterRange_of_pow_le <;> assumption
theorem exists_expUnit_near_one {ε : ℝ} (hε : 0 < ε) : ∃ τ : ℝ, 0 < τ ∧ ∀ a : imaginaryQuaternions,
    ‖a‖ ≤ 2 * τ → ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε := by
  have hc : Continuous fun a : imaginaryQuaternions => ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ :=
    ((continuous_subtype_val.comp continuous_expUnit).sub continuous_const).norm
  have h0 : ‖((expUnit 0 : UnitQuaternion) : ℍ[ℝ]) - 1‖ = 0 := by
    rw [expUnit_zero]
    simp
  have := hc.tendsto (0 : imaginaryQuaternions)
  rw [h0] at this
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp (this.eventually (gt_mem_nhds hε))
  refine ⟨δ / 4, by positivity, fun a ha => ?_⟩
  have : dist a 0 < δ := by
    rw [dist_zero_right]
    linarith
  exact (hb this).le
end StepSettings
end YangMills.Construction
end
