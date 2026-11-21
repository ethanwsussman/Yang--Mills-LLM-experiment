import YangMills.Construction.ClusterExpansionOfAStep.ActionAlongMovesProof
import YangMills.Construction.ClusterExpansionOfAStep.PartsOfTheCostAlongMoves
import YangMills.Construction.ColdChainAtEveryLevel.PinnedQuarticGaugeProof
import YangMills.Construction.ColdStepAtMirrorFrames.AdjointOfTheGroup
import YangMills.Construction.FormsOnATorus.AxialLadderOnACube
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.LawOnABoxOfTheFlow.FormOfACube
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps TorusChain StepCosts LevelAction FreeBondMoves LineCalculus QuaternionLogarithm BlockAverages
  ResponseInTheExpansion
section AlongLines
private theorem tendsto_div_sq_of_deriv_zero {g g' : ℝ → ℝ} {c : ℝ} (hg : ∀ᶠ τ in 𝓝 (0 : ℝ), HasDerivAt g (g' τ) τ)
    (hc : HasDerivAt g' c 0) (hg0 : g 0 = 0) (hg'0 : g' 0 = 0) :
    Tendsto (fun τ : ℝ => g τ / τ ^ 2) (𝓝[≠] 0) (𝓝 (c / 2)) := by
  have hcont : ContinuousAt g 0 := hg.self_of_nhds.continuousAt
  have hslope : Tendsto (fun τ : ℝ => g' τ / (2 * τ)) (𝓝[≠] 0) (𝓝 (c / 2)) := by
    have h2 := hc.tendsto_slope_zero
    have h3 : (fun t : ℝ => t⁻¹ • (g' (0 + t) - g' 0)) = fun t => g' t / t := by
      funext t
      simp [hg'0, div_eq_inv_mul]
    rw [h3] at h2
    have h4 := h2.div_const 2
    refine h4.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    field_simp
  refine HasDerivAt.lhopital_zero_nhdsNE (f := g) (g := fun τ => τ ^ 2) (f' := g') (g' := fun τ => 2 * τ)
    (hg.filter_mono nhdsWithin_le_nhds) ?_ ?_ ?_ ?_ hslope
  · refine Eventually.of_forall fun τ => ?_
    simpa using hasDerivAt_pow 2 τ
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    positivity
  · have : Tendsto g (𝓝 0) (𝓝 0) := by simpa [ContinuousAt, hg0] using hcont
    exact this.mono_left nhdsWithin_le_nhds
  · have : Tendsto (fun τ : ℝ => τ ^ 2) (𝓝 0) (𝓝 0) := by
      have h := (continuous_pow 2 : Continuous fun τ : ℝ => τ ^ 2).tendsto 0
      simpa using h
    exact this.mono_left nhdsWithin_le_nhds
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem tendsto_line_div_sq {u : E → ℝ} (h : ContDiffAt ℝ 2 u 0) (h0 : u 0 = 0) (a : E) (hd : fderiv ℝ u 0 a = 0) :
    Tendsto (fun τ : ℝ => u (τ • a) / τ ^ 2) (𝓝[≠] 0) (𝓝 (fderiv ℝ (fderiv ℝ u) 0 a a / 2)) := by
  have h1 : ∀ᶠ τ in 𝓝 (0 : ℝ), HasDerivAt (fun τ' : ℝ => u ((0 : E) + τ' • a)) (fderiv ℝ u ((0 : E) + τ • a) a) τ := by
    filter_upwards [eventually_along_affineLine (d := a) (eventually_differentiableAt_of_contDiffAt_two h)] with τ hτ
    exact hasDerivAt_comp_affineLine hτ
  have h2 := tendsto_div_sq_of_deriv_zero h1 (hasDerivAt_fderiv_apply_along_line h) (by simpa using h0) (by simpa using hd)
  simpa using h2
private theorem fderiv_line_eq_zero_of_nonneg {u : E → ℝ} (h : ContDiffAt ℝ 2 u 0) (h0 : u 0 = 0) (a : E)
    (hpos : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 ≤ u (τ • a)) : fderiv ℝ u 0 a = 0 := by
  have hd : DifferentiableAt ℝ u ((0 : E) + (0 : ℝ) • a) := by
    simpa using h.differentiableAt (by norm_num)
  have h1 := hasDerivAt_comp_affineLine (d := a) hd
  have hmin : IsLocalMin (fun τ' : ℝ => u ((0 : E) + τ' • a)) 0 := by
    have : ∀ᶠ τ in 𝓝 (0 : ℝ), u ((0 : E) + (0 : ℝ) • a) ≤ u ((0 : E) + τ • a) := by
      filter_upwards [hpos] with τ hτ
      simpa [h0] using hτ
    exact this
  have h2 := hmin.hasDerivAt_eq_zero h1
  simpa using h2
end AlongLines
section FlatHessian
variable {n : ℕ} [NeZero n]
private abbrev BondMoves (n : ℕ) [NeZero n] : Type := ↥(Finset.univ : Finset (TorusBond n)) → ImaginaryCoord
private def formCoords (u : TorusBond n → imaginaryQuaternions) : BondMoves n :=
  fun b => imPartCLM ((u b.1 : imaginaryQuaternions) : ℍ[ℝ])
private theorem toImaginary_imPartCLM (X : imaginaryQuaternions) :
    ColdStepAtMirrorFrames.toImaginary (imPartCLM (X : ℍ[ℝ])) = X := by
  apply Subtype.ext
  show imaginaryCLM (imPartCLM (X : ℍ[ℝ])) = (X : ℍ[ℝ])
  have hr : (X : ℍ[ℝ]).re = 0 := X.2
  ext <;> simp [imaginaryCLM_apply, imPartCLM, hr]
private theorem bilin_eq_sum_single {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : (ι → ImaginaryCoord) →L[ℝ] (ι → ImaginaryCoord) →L[ℝ] ℝ)
    (x y : ι → ImaginaryCoord) : H x y = ∑ b, ∑ b', H (Pi.single b (x b)) (Pi.single b' (y b')) := by apply _root_.YangMills.Construction.CostDerivatives.bilinear_eq_sum_single <;> assumption
private def onMoves (G : TorusField n → ℝ) : BondMoves n → ℝ := alongMoves Finset.univ G (trivialField n)
private def flatHessian (G : TorusField n → ℝ) : BondMoves n →L[ℝ] BondMoves n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (onMoves G)) 0
private theorem onMoves_smul_formCoords (G : TorusField n → ℝ) (u : TorusBond n → imaginaryQuaternions) (τ : ℝ) :
    onMoves G (τ • formCoords u) = G (exponentialField (τ • u)) := by
  unfold onMoves alongMoves
  congr 1
  funext x i
  simp only [leftMovesAt, Finset.mem_univ, dif_pos, trivialField, mul_one, exponentialField]
  congr 1
  show ColdStepAtMirrorFrames.toImaginary (τ • imPartCLM ((u (x, i) : imaginaryQuaternions) : ℍ[ℝ])) = τ • u (x, i)
  rw [toImaginary_smul, toImaginary_imPartCLM]
private theorem onMoves_zero (G : TorusField n → ℝ) : onMoves G 0 = G (trivialField n) := by
  unfold onMoves alongMoves
  congr 1
  funext x i
  simp [leftMovesAt, trivialField, toImaginary_zero, expUnit_zero]
private theorem contDiffAt_onMoves {G : TorusField n → ℝ} (h : ContDiffThreeAt G (trivialField n)) :
    ContDiffAt ℝ 2 (onMoves G) 0 :=
  (contDiffAt_alongMoves Finset.univ h).of_le (by norm_num)
private theorem flatHessian_symm {G : TorusField n → ℝ} (h : ContDiffThreeAt G (trivialField n)) (a a' : BondMoves n) :
    flatHessian G a a' = flatHessian G a' a :=
  ((contDiffAt_onMoves h).isSymmSndFDerivAt (by simp)) a a'
private theorem flatHessian_single {G : TorusField n → ℝ} (h : ContDiffThreeAt G (trivialField n)) (b b' : TorusBond n)
    (X Y : imaginaryQuaternions) :
    flatHessian G (Pi.single ⟨b, Finset.mem_univ b⟩ (imPartCLM (X : ℍ[ℝ])))
      (Pi.single ⟨b', Finset.mem_univ b'⟩ (imPartCLM (Y : ℍ[ℝ]))) = mixedDeriv G (trivialField n) ![b, b'] ![X, Y] := by
  have := second_fderiv_alongMoves h ⟨b, Finset.mem_univ b⟩ ⟨b', Finset.mem_univ b'⟩ (imPartCLM (X : ℍ[ℝ]))
    (imPartCLM (Y : ℍ[ℝ]))
  simpa [flatHessian, onMoves, toImaginary_imPartCLM] using this
private theorem sum_mixedDeriv_eq_flatHessian {G : TorusField n → ℝ} (h : ContDiffThreeAt G (trivialField n))
    (u v : TorusBond n → imaginaryQuaternions) :
    ∑ b : TorusBond n, ∑ b' : TorusBond n, mixedDeriv G (trivialField n) ![b, b'] ![u b, v b'] =
      flatHessian G (formCoords u) (formCoords v) := by
  classical
  rw [bilin_eq_sum_single (flatHessian G) (formCoords u) (formCoords v)]
  have e : ∀ (b b' : ↥(Finset.univ : Finset (TorusBond n))),
      flatHessian G (Pi.single b (formCoords u b)) (Pi.single b' (formCoords v b')) =
        mixedDeriv G (trivialField n) ![b.1, b'.1] ![u b.1, v b'.1] := fun b b' => flatHessian_single h b.1 b'.1 _ _
  simp only [e]
  rw [Finset.univ.sum_coe_sort (fun b => ∑ b' : ↥(Finset.univ : Finset (TorusBond n)),
    mixedDeriv G (trivialField n) ![b, b'.1] ![u b, v b'.1])]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact (Finset.univ.sum_coe_sort (fun b' => mixedDeriv G (trivialField n) ![b, b'] ![u b, v b'])).symm
private theorem tendsto_flatHessian {G : TorusField n → ℝ} (h : ContDiffThreeAt G (trivialField n))
    (h0 : G (trivialField n) = 0) (u : TorusBond n → imaginaryQuaternions)
    (hpos : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 ≤ G (exponentialField (τ • u))) :
    Tendsto (fun τ : ℝ => G (exponentialField (τ • u)) / τ ^ 2) (𝓝[≠] 0)
      (𝓝 (flatHessian G (formCoords u) (formCoords u) / 2)) := by
  have hz : onMoves G 0 = 0 := by rw [onMoves_zero, h0]
  have hs := fderiv_line_eq_zero_of_nonneg (contDiffAt_onMoves h) hz (formCoords u)
    (by simpa only [onMoves_smul_formCoords] using hpos)
  simpa only [onMoves_smul_formCoords, flatHessian] using
    tendsto_line_div_sq (contDiffAt_onMoves h) hz (formCoords u) hs
end FlatHessian
section Plaquettes
variable {n : ℕ} [NeZero n]
private theorem hasDerivAt_expUnit_line (X : imaginaryQuaternions) :
    HasDerivAt (fun τ : ℝ => ((expUnit (τ • X) : UnitQuaternion) : ℍ[ℝ])) (X : ℍ[ℝ]) 0 := by apply _root_.YangMills.Construction.GaugedCriticality.hasDerivAt_expUnit_smul <;> assumption
private theorem hasDerivAt_expUnit_line_inv (X : imaginaryQuaternions) :
    HasDerivAt (fun τ : ℝ => (((expUnit (τ • X))⁻¹ : UnitQuaternion) : ℍ[ℝ])) (-(X : ℍ[ℝ])) 0 := by apply _root_.YangMills.Construction.PinnedGauge.hasDerivAt_expUnit_inv <;> assumption
private theorem hasDerivAt_holonomy_line (w : TorusBond n → imaginaryQuaternions) (x : TorusSite n) (μ ν : Fin 4) :
    HasDerivAt (fun τ : ℝ => ((holonomy (exponentialField (τ • w)) x μ ν : UnitQuaternion) : ℍ[ℝ]))
      ((lieFormCurl w (x, μ, ν) : imaginaryQuaternions) : ℍ[ℝ]) 0 := by
  have h1 := hasDerivAt_expUnit_line (w (x, μ))
  have h2 := hasDerivAt_expUnit_line (w (x + TorusFields.unitStep n μ, ν))
  have h3 := hasDerivAt_expUnit_line_inv (w (x + TorusFields.unitStep n ν, μ))
  have h4 := hasDerivAt_expUnit_line_inv (w (x, ν))
  have h := ((h1.mul h2).mul h3).mul h4
  have e0 : ∀ X : imaginaryQuaternions, expUnit ((0 : ℝ) • X) = 1 := fun X => by rw [zero_smul, expUnit_zero]
  refine HasDerivAt.congr_deriv (f' := _) h ?_
  simp only [Pi.mul_apply, e0, inv_one, OneMemClass.coe_one, mul_one, one_mul]
  simp only [lieFormCurl, Submodule.coe_add, Submodule.coe_sub]
  abel
private theorem exponentialField_zero_smul (w : TorusBond n → imaginaryQuaternions) :
    exponentialField ((0 : ℝ) • w) = trivialField n := by
  funext x i
  simp [exponentialField, trivialField, expUnit_zero]
private theorem holonomy_zero_smul (w : TorusBond n → imaginaryQuaternions) (x : TorusSite n) (μ ν : Fin 4) :
    holonomy (exponentialField ((0 : ℝ) • w)) x μ ν = 1 := by
  rw [exponentialField_zero_smul]
  simp [holonomy, trivialField]
private theorem tendsto_curvature_sq_div (w : TorusBond n → imaginaryQuaternions) (x : TorusSite n) (μ ν : Fin 4) :
    Tendsto (fun τ : ℝ => curvature (exponentialField (τ • w)) x μ ν ^ 2 / τ ^ 2) (𝓝[≠] 0)
      (𝓝 (‖lieFormCurl w (x, μ, ν)‖ ^ 2)) := by
  have h := (hasDerivAt_holonomy_line w x μ ν).tendsto_slope_zero
  have h2 := (h.norm).pow 2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ' : τ ≠ 0 := hτ
  simp only [zero_add, holonomy_zero_smul, OneMemClass.coe_one, norm_smul, norm_inv, Real.norm_eq_abs, mul_pow,
    inv_pow, sq_abs, curvature]
  field_simp
private theorem tendsto_curvature_line (w : TorusBond n → imaginaryQuaternions) (x : TorusSite n) (μ ν : Fin 4) :
    Tendsto (fun τ : ℝ => curvature (exponentialField (τ • w)) x μ ν) (𝓝 0) (𝓝 0) := by
  have h := (hasDerivAt_holonomy_line w x μ ν).continuousAt.tendsto
  have h2 := (h.sub_const (1 : ℍ[ℝ])).norm
  simp only [holonomy_zero_smul, OneMemClass.coe_one, sub_self, norm_zero] at h2
  exact h2
private theorem flatHessian_nonneg {G : TorusField n → ℝ} (h : ContDiffThreeAt G (trivialField n))
    (h0 : G (trivialField n) = 0) (u : TorusBond n → imaginaryQuaternions)
    (hpos : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 ≤ G (exponentialField (τ • u))) :
    0 ≤ flatHessian G (formCoords u) (formCoords u) := by
  have h1 := tendsto_flatHessian h h0 u hpos
  have h2 : 0 ≤ flatHessian G (formCoords u) (formCoords u) / 2 := by
    refine ge_of_tendsto h1 ?_
    filter_upwards [hpos.filter_mono nhdsWithin_le_nhds] with τ hτ
    positivity
  linarith
private theorem flatHessian_nonpos {G : TorusField n → ℝ} (h : ContDiffThreeAt G (trivialField n))
    (h0 : G (trivialField n) = 0) (u : TorusBond n → imaginaryQuaternions)
    (hpos : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 ≤ G (exponentialField (τ • u)))
    (hs : ∀ ε : ℝ, 0 < ε → ∀ᶠ τ in 𝓝[≠] (0 : ℝ), G (exponentialField (τ • u)) ≤ ε * τ ^ 2) :
    flatHessian G (formCoords u) (formCoords u) ≤ 0 := by
  have h1 := tendsto_flatHessian h h0 u hpos
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h2 : flatHessian G (formCoords u) (formCoords u) / 2 ≤ ε / 2 := by
    refine le_of_tendsto h1 ?_
    filter_upwards [hs (ε / 2) (by positivity), self_mem_nhdsWithin] with τ hτ hτ0
    have hτ' : τ ≠ 0 := hτ0
    have : 0 < τ ^ 2 := by positivity
    rw [div_le_iff₀ this]
    exact hτ
  linarith
private theorem flatHessian_ge_curl {G : TorusField n → ℝ} (h : ContDiffThreeAt G (trivialField n))
    (h0 : G (trivialField n) = 0) {c l : ℝ} (hc : 0 ≤ c) (hl : 0 < l)
    (P : Finset (TorusPlaquette n)) (hG : ∀ W, c * ∑ p ∈ P, min (curvature W p.1 p.2.1 p.2.2 ^ 2) l ≤ G W)
    (u : TorusBond n → imaginaryQuaternions) :
    2 * c * ∑ p ∈ P, ‖lieFormCurl u p‖ ^ 2 ≤ flatHessian G (formCoords u) (formCoords u) := by
  have hpos : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 ≤ G (exponentialField (τ • u)) := by
    refine Eventually.of_forall fun τ => le_trans ?_ (hG _)
    refine mul_nonneg hc (Finset.sum_nonneg fun p _ => le_min (sq_nonneg _) hl.le)
  have h1 := tendsto_flatHessian h h0 u hpos
  have h2 : Tendsto (fun τ : ℝ => c * ∑ p ∈ P, curvature (exponentialField (τ • u)) p.1 p.2.1 p.2.2 ^ 2 / τ ^ 2)
      (𝓝[≠] 0) (𝓝 (c * ∑ p ∈ P, ‖lieFormCurl u p‖ ^ 2)) :=
    (tendsto_finsetSum _ fun p _ => tendsto_curvature_sq_div u p.1 p.2.1 p.2.2).const_mul c
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ p ∈ P, curvature (exponentialField (τ • u)) p.1 p.2.1 p.2.2 ^ 2 < l := by
    refine (Finset.eventually_all P).mpr fun p _ => ?_
    have h3 := (tendsto_curvature_line u p.1 p.2.1 p.2.2).pow 2
    have h4 : (0 : ℝ) ^ 2 < l := by simpa using hl
    exact h3.eventually (gt_mem_nhds h4)
  have h5 : c * ∑ p ∈ P, ‖lieFormCurl u p‖ ^ 2 ≤ flatHessian G (formCoords u) (formCoords u) / 2 := by
    refine le_of_tendsto_of_tendsto h2 h1 ?_
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with τ hτ hτ0
    have hτ' : τ ≠ 0 := hτ0
    have h6 : 0 < τ ^ 2 := by positivity
    have h7 := hG (exponentialField (τ • u))
    have h8 : ∑ p ∈ P, min (curvature (exponentialField (τ • u)) p.1 p.2.1 p.2.2 ^ 2) l =
        ∑ p ∈ P, curvature (exponentialField (τ • u)) p.1 p.2.1 p.2.2 ^ 2 :=
      Finset.sum_congr rfl fun p hp => min_eq_left (hτ p hp).le
    rw [h8] at h7
    rw [← Finset.sum_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right h7 h6.le
  linarith
private theorem flatHessian_wilson {G : TorusField n → ℝ} (h : ContDiffThreeAt G (trivialField n))
    (P : Finset (TorusPlaquette n))
    (hG : ∀ W, G W = ∑ p ∈ P, plaquetteEnergy W p.1 p.2.1 p.2.2) (u : TorusBond n → imaginaryQuaternions) :
    flatHessian G (formCoords u) (formCoords u) = ∑ p ∈ P, ‖lieFormCurl u p‖ ^ 2 := by
  have h0 : G (trivialField n) = 0 := by
    rw [hG]
    simp [plaquetteEnergy, holonomy_trivialField]
  have hpos : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 ≤ G (exponentialField (τ • u)) := by
    refine Eventually.of_forall fun τ => ?_
    rw [hG]
    exact Finset.sum_nonneg fun p _ => plaquetteEnergy_nonneg _ _ _ _
  have h1 := tendsto_flatHessian h h0 u hpos
  have h2 : Tendsto (fun τ : ℝ => ∑ p ∈ P, curvature (exponentialField (τ • u)) p.1 p.2.1 p.2.2 ^ 2 / τ ^ 2 / 2)
      (𝓝[≠] 0) (𝓝 (∑ p ∈ P, ‖lieFormCurl u p‖ ^ 2 / 2)) :=
    tendsto_finsetSum _ fun p _ => (tendsto_curvature_sq_div u p.1 p.2.1 p.2.2).div_const 2
  have h3 : Tendsto (fun τ : ℝ => G (exponentialField (τ • u)) / τ ^ 2) (𝓝[≠] 0)
      (𝓝 (∑ p ∈ P, ‖lieFormCurl u p‖ ^ 2 / 2)) := by
    refine h2.congr' (Eventually.of_forall fun τ => ?_)
    show _ = G (exponentialField (τ • u)) / τ ^ 2
    rw [hG, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [plaquetteEnergy_eq_curvature_sq]
    ring
  have h4 := tendsto_nhds_unique h1 h3
  rw [← Finset.sum_div] at h4
  linarith
private theorem bilin_eq_zero_of_null {E : Type*} [AddCommGroup E] [Module ℝ E] (H : E → E → ℝ)
    (hadd : ∀ a b c, H (a + b) c = H a c + H b c) (hadd' : ∀ a b c, H a (b + c) = H a b + H a c)
    (hsm : ∀ (t : ℝ) a b, H (t • a) b = t * H a b) (hsm' : ∀ (t : ℝ) a b, H a (t • b) = t * H a b)
    (hsym : ∀ a b, H a b = H b a) (hnn : ∀ a, 0 ≤ H a a) {a : E} (ha : H a a = 0) (b : E) : H a b = 0 := by
  set c := H a b with hc
  set q := H b b with hq
  have hq0 : 0 ≤ q := hnn b
  have key : ∀ t : ℝ, 0 ≤ 2 * t * c + t ^ 2 * q := by
    intro t
    have := hnn (a + t • b)
    simp only [hadd, hadd', hsm, hsm'] at this
    rw [hsym b a, ha, ← hc, ← hq] at this
    nlinarith
  by_contra hne
  have hc2 : 0 < c ^ 2 := by positivity
  have h1 := key (-c / (q + 1))
  have h2 : 2 * (-c / (q + 1)) * c + (-c / (q + 1)) ^ 2 * q = -(c ^ 2 * (q + 2)) / (q + 1) ^ 2 := by
    field_simp
    ring
  rw [h2] at h1
  have h3 : -(c ^ 2 * (q + 2)) / (q + 1) ^ 2 < 0 := by
    apply div_neg_of_neg_of_pos
    · nlinarith
    · positivity
  linarith
end Plaquettes
section CentredCoordinates
variable {n : ℕ} [NeZero n]
private def centredCoords (o x : TorusSite n) : Fin 4 → ℤ := fun l => (x l - o l).valMinAbs
private theorem valMinAbs_intCast {a : ℤ} (h : 2 * |a| < n) : ((a : ZMod n)).valMinAbs = a := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
private theorem mem_supBall_iff {o x : TorusSite n} {R : ℕ} :
    x ∈ supBall o (2 * R) ↔ ∀ l, |centredCoords o x l| ≤ 2 * (R : ℤ) := by
  have h1 : x ∈ supBall o (2 * R) ↔ _root_.YangMills.Construction.TorusFields.supDist x o ≤ 2 * R := by
    simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
    exact_mod_cast Iff.rfl
  rw [h1, _root_.YangMills.Construction.TorusFields.supDist_le_iff]
  refine forall_congr' fun l => ?_
  simp only [centredCoords, Int.abs_eq_natAbs]
  omega
abbrev _root_.YangMills.DeltaSharedProofs.p501575 := @mem_supBall_iff
end CentredCoordinates
section ShareCeiling
variable {n : ℕ} [NeZero n]
private structure FlatShareBounds (sh : TorusSite n → TorusField n → ℝ) (S : Finset (TorusSite n)) (D δ N0 σ : ℝ) :
    Prop where
  contDiff : ∀ y, ContDiffThreeAt (sh y) (trivialField n)
  mixed_decay : ∀ (y : TorusSite n) (b b' : TorusBond n) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
    |mixedDeriv (sh y) (trivialField n) ![b, b'] ![X, X']| ≤ D * Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist y b.1) ∧
    |mixedDeriv (sh y) (trivialField n) ![b, b'] ![X, X']| ≤ D * Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist y b'.1)
  bounds : ∀ (y : TorusSite n) (s : ℝ) (W : TorusField n), 0 < s → s ≤ σ → IsColdOn s S W →
    0 ≤ sh y W ∧ sh y W ≤ N0 * s ^ 2
  vanish_off : ∀ y, y ∉ S → ∀ W, sh y W = 0
private theorem isColdOn_trivialField (S : Finset (TorusSite n)) {s : ℝ} (hs : 0 < s) : IsColdOn s S (trivialField n) := by
  intro p _
  simp [curvature, holonomy, trivialField, hs]
private theorem eventually_isColdOn_line (S : Finset (TorusSite n)) (u : TorusBond n → imaginaryQuaternions) {s : ℝ}
    (hs : 0 < s) : ∀ᶠ τ in 𝓝 (0 : ℝ), IsColdOn s S (exponentialField (τ • u)) := by
  refine (Finset.eventually_all (plaquettesIn S)).mpr fun p _ => ?_
  exact (tendsto_curvature_line u p.1 p.2.1 p.2.2).eventually (gt_mem_nhds hs)
variable {sh : TorusSite n → TorusField n → ℝ} {S : Finset (TorusSite n)} {D δ N0 σ : ℝ}
private theorem FlatShareBounds.trivial_eq_zero (h : FlatShareBounds sh S D δ N0 σ) (hσ : 0 < σ) (y : TorusSite n) :
    sh y (trivialField n) = 0 := by
  have h1 := (h.bounds y σ (trivialField n) hσ le_rfl (isColdOn_trivialField S hσ)).1
  refine le_antisymm ?_ h1
  have h2 : Tendsto (fun s : ℝ => N0 * s ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => N0 * s ^ 2) (𝓝 0) (𝓝 (N0 * 0 ^ 2)) :=
      ((continuous_pow 2).const_smul N0).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto h2 ?_
  filter_upwards [Ioc_mem_nhdsGT hσ] with s hs
  exact (h.bounds y s (trivialField n) hs.1 hs.2 (isColdOn_trivialField S hs.1)).2
private theorem FlatShareBounds.eventually_nonneg (h : FlatShareBounds sh S D δ N0 σ) (hσ : 0 < σ) (y : TorusSite n)
    (u : TorusBond n → imaginaryQuaternions) : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 ≤ sh y (exponentialField (τ • u)) := by
  filter_upwards [eventually_isColdOn_line S u hσ] with τ hτ
  exact (h.bounds y σ _ hσ le_rfl hτ).1
private theorem formCoords_add (u v : TorusBond n → imaginaryQuaternions) :
    formCoords (u + v) = formCoords u + formCoords v := by
  funext b
  simp [formCoords, map_add]
private theorem formCoords_smul (c : ℝ) (u : TorusBond n → imaginaryQuaternions) :
    formCoords (c • u) = c • formCoords u := by
  funext b
  simp [formCoords, map_smul]
private theorem FlatShareBounds.flatHessian_nonpos_of_curl_free (h : FlatShareBounds sh S D δ N0 σ) (hσ : 0 < σ)
    (hN : 0 ≤ N0) (y : TorusSite n) {u : TorusBond n → imaginaryQuaternions}
    (hu : ∀ p ∈ plaquettesIn S, lieFormCurl u p = 0) :
    flatHessian (sh y) (formCoords u) (formCoords u) ≤ 0 := by
  refine flatHessian_nonpos (h.contDiff y) (h.trivial_eq_zero hσ y) u (h.eventually_nonneg hσ y u) fun ε hε => ?_
  set κ : ℝ := Real.sqrt (ε / (N0 + 1)) with hκ
  have hN1 : 0 < N0 + 1 := by linarith
  have hκ2 : κ ^ 2 = ε / (N0 + 1) := Real.sq_sqrt (by positivity)
  have h1 : ∀ᶠ τ in 𝓝[≠] (0 : ℝ), ∀ p ∈ plaquettesIn S,
      curvature (exponentialField (τ • u)) p.1 p.2.1 p.2.2 ^ 2 / τ ^ 2 < κ ^ 2 := by
    refine (Finset.eventually_all (plaquettesIn S)).mpr fun p hp => ?_
    have h2 := tendsto_curvature_sq_div u p.1 p.2.1 p.2.2
    have e : lieFormCurl u (p.1, p.2.1, p.2.2) = 0 := hu p hp
    rw [e] at h2
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h2
    exact h2.eventually (gt_mem_nhds (by positivity))
  have h3 : ∀ᶠ τ in 𝓝[≠] (0 : ℝ), κ * |τ| ≤ σ := by
    have h4 : Tendsto (fun τ : ℝ => κ * |τ|) (𝓝 0) (𝓝 (κ * |0|)) :=
      ((continuous_abs).const_smul κ).tendsto 0
    simp only [abs_zero, mul_zero] at h4
    exact (h4.mono_left nhdsWithin_le_nhds).eventually (ge_mem_nhds hσ)
  filter_upwards [h1, h3, self_mem_nhdsWithin] with τ hτ1 hτ2 hτ0
  have hτ' : τ ≠ 0 := hτ0
  have hcold : IsColdOn (κ * |τ|) S (exponentialField (τ • u)) := by
    intro p hp
    have h5 := hτ1 p hp
    have h6 : 0 < τ ^ 2 := by positivity
    rw [div_lt_iff₀ h6] at h5
    have h7 : curvature (exponentialField (τ • u)) p.1 p.2.1 p.2.2 ^ 2 < (κ * |τ|) ^ 2 := by
      rw [mul_pow, sq_abs]
      exact h5
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h7
  have h8 := (h.bounds y _ _ (by positivity) hτ2 hcold).2
  refine h8.trans ?_
  rw [mul_pow, sq_abs, hκ2]
  have h9 : 0 ≤ τ ^ 2 := by positivity
  have h10 : N0 * (ε / (N0 + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hN1]
    nlinarith
  calc N0 * (ε / (N0 + 1) * τ ^ 2) = N0 * (ε / (N0 + 1)) * τ ^ 2 := by ring
    _ ≤ ε * τ ^ 2 := mul_le_mul_of_nonneg_right h10 h9
private theorem abs_mixedDeriv_le_of_units {G : TorusField n → ℝ} (h : ContDiffThreeAt G (trivialField n))
    (b b' : TorusBond n) {M : ℝ}
    (hM : ∀ X X' : imaginaryQuaternions, ‖X‖ = 1 → ‖X'‖ = 1 →
      |mixedDeriv G (trivialField n) ![b, b'] ![X, X']| ≤ M) (X X' : imaginaryQuaternions) :
    |mixedDeriv G (trivialField n) ![b, b'] ![X, X']| ≤ M * ‖X‖ * ‖X'‖ := by
  have hs : ∀ (c : ℝ) (Y : imaginaryQuaternions),
      imPartCLM ((c • Y : imaginaryQuaternions) : ℍ[ℝ]) = c • imPartCLM (Y : ℍ[ℝ]) := fun c Y => by
    simp [map_smul]
  have hz : imPartCLM ((0 : imaginaryQuaternions) : ℍ[ℝ]) = 0 := by simp
  by_cases hX : X = 0
  · rw [← flatHessian_single h, hX, hz]
    simp
  by_cases hX' : X' = 0
  · rw [← flatHessian_single h, hX', hz]
    simp
  have h1 : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
  have h2 : ‖X'‖ ≠ 0 := norm_ne_zero_iff.mpr hX'
  have h3 := hM (‖X‖⁻¹ • X) (‖X'‖⁻¹ • X') (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h1])
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h2])
  rw [← flatHessian_single h, hs, hs, Pi.single_smul, Pi.single_smul] at h3
  simp only [map_smul, _root_.smul_apply, smul_eq_mul] at h3
  rw [← flatHessian_single h]
  have e : flatHessian G (Pi.single ⟨b, Finset.mem_univ b⟩ (imPartCLM (X : ℍ[ℝ])))
      (Pi.single ⟨b', Finset.mem_univ b'⟩ (imPartCLM (X' : ℍ[ℝ]))) =
      ‖X‖ * ‖X'‖ * (‖X'‖⁻¹ * (‖X‖⁻¹ * flatHessian G (Pi.single ⟨b, Finset.mem_univ b⟩ (imPartCLM (X : ℍ[ℝ])))
      (Pi.single ⟨b', Finset.mem_univ b'⟩ (imPartCLM (X' : ℍ[ℝ]))))) := by
    field_simp
  rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖X‖ * ‖X'‖)]
  calc ‖X‖ * ‖X'‖ * |‖X'‖⁻¹ * (‖X‖⁻¹ * flatHessian G (Pi.single ⟨b, Finset.mem_univ b⟩ (imPartCLM (X : ℍ[ℝ])))
      (Pi.single ⟨b', Finset.mem_univ b'⟩ (imPartCLM (X' : ℍ[ℝ]))))|
      ≤ ‖X‖ * ‖X'‖ * M := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = M * ‖X‖ * ‖X'‖ := by ring
private def bondWeight (δ : ℝ) (y : TorusSite n) (b : TorusBond n) : ℝ := Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist b.1 y)
private def nearCurlSquares (S : Finset (TorusSite n)) (v : TorusBond n → imaginaryQuaternions) (y : TorusSite n)
    (d : ℕ) : ℝ :=
  ∑ p ∈ plaquettesIn S, if _root_.YangMills.Construction.TorusFields.supDist p.1 y ≤ d then ‖lieFormCurl v p‖ ^ 2 else 0
private def expSumBound (β : ℝ) : ℝ := (2 / (1 - Real.exp (-β / 4))) ^ 4
private theorem sum_sites_exp_le {β : ℝ} (hβ : 0 < β) (y : TorusSite n) :
    ∑ x : TorusSite n, Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist x y) ≤ expSumBound β := sum_exp_neg_mul_supDist_le hβ y
private theorem sum_bonds_exp_le {β : ℝ} (hβ : 0 < β) (y : TorusSite n) :
    ∑ b : TorusBond n, Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist b.1 y) ≤ 4 * expSumBound β := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 := sum_sites_exp_le hβ y
  rw [← Finset.mul_sum]
  push_cast
  linarith
private theorem expSumBound_nonneg {β : ℝ} (hβ : 0 < β) : 0 ≤ expSumBound β := by
  have h : Real.exp (-β / 4) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  unfold expSumBound
  have : 0 < 1 - Real.exp (-β / 4) := by linarith
  positivity
end ShareCeiling
section ShareCeiling
variable {n : ℕ} [NeZero n]
variable {sh : TorusSite n → TorusField n → ℝ} {S : Finset (TorusSite n)} {D δ N0 σ : ℝ}
private theorem flatHessian_eq_of_curl_eq (h : FlatShareBounds sh S D δ N0 σ) (hσ : 0 < σ) (hN : 0 ≤ N0) (y : TorusSite n)
    {v A : TorusBond n → imaginaryQuaternions} (hA : ∀ p ∈ plaquettesIn S, lieFormCurl (v - A) p = 0) :
    flatHessian (sh y) (formCoords v) (formCoords v) = flatHessian (sh y) (formCoords A) (formCoords A) := by
  set H : (TorusBond n → imaginaryQuaternions) → (TorusBond n → imaginaryQuaternions) → ℝ :=
    fun u u' => flatHessian (sh y) (formCoords u) (formCoords u') with hH
  have hnn : ∀ u, 0 ≤ H u u := fun u =>
    flatHessian_nonneg (h.contDiff y) (h.trivial_eq_zero hσ y) u (h.eventually_nonneg hσ y u)
  have hw : H (v - A) (v - A) = 0 := le_antisymm (h.flatHessian_nonpos_of_curl_free hσ hN y hA) (hnn _)
  have hsym : ∀ a b, H a b = H b a := fun a b => flatHessian_symm (h.contDiff y) _ _
  have hadd : ∀ a b c, H (a + b) c = H a c + H b c := fun a b c => by
    simp only [hH, formCoords_add, map_add, _root_.add_apply]
  have hadd' : ∀ a b c, H a (b + c) = H a b + H a c := fun a b c => by
    simp only [hH, formCoords_add, map_add]
  have hsm : ∀ (t : ℝ) a b, H (t • a) b = t * H a b := fun t a b => by
    simp only [hH, formCoords_smul, map_smul, _root_.smul_apply, smul_eq_mul]
  have hsm' : ∀ (t : ℝ) a b, H a (t • b) = t * H a b := fun t a b => by
    simp only [hH, formCoords_smul, map_smul, smul_eq_mul]
  have hc := bilin_eq_zero_of_null H hadd hadd' hsm hsm' hsym hnn hw
  have e : v = (v - A) + A := by abel
  show H v v = H A A
  rw [e, hadd, hadd', hadd', hw, hc A, hsym A (v - A), hc A]
  simp
private theorem abs_mixedDeriv_le_weights (h : FlatShareBounds sh S D δ N0 σ) (hD : 0 ≤ D) (hδ : 0 < δ)
    (y : TorusSite n) (b b' : TorusBond n) (X X' : imaginaryQuaternions) :
    |mixedDeriv (sh y) (trivialField n) ![b, b'] ![X, X']| ≤
      D * (bondWeight δ y b * bondWeight δ y b') * ‖X‖ * ‖X'‖ := by
  refine abs_mixedDeriv_le_of_units (h.contDiff y) b b' (fun U U' hU hU' => ?_) X X'
  obtain ⟨h1, h2⟩ := h.mixed_decay y b b' U U' hU hU'
  have e : bondWeight δ y b * bondWeight δ y b' =
      Real.exp (-δ * (((_root_.YangMills.Construction.TorusFields.supDist b.1 y : ℝ) + _root_.YangMills.Construction.TorusFields.supDist b'.1 y) / 2)) := by
    unfold bondWeight
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e]
  rcases le_total (_root_.YangMills.Construction.TorusFields.supDist b.1 y) (_root_.YangMills.Construction.TorusFields.supDist b'.1 y) with hle | hle
  · refine h2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD)
    have : ((_root_.YangMills.Construction.TorusFields.supDist b.1 y : ℕ) : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist b'.1 y := by exact_mod_cast hle
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm y b'.1]
    nlinarith
  · refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD)
    have : ((_root_.YangMills.Construction.TorusFields.supDist b'.1 y : ℕ) : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist b.1 y := by exact_mod_cast hle
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm y b.1]
    nlinarith
private theorem flatHessian_le_weighted (h : FlatShareBounds sh S D δ N0 σ) (hD : 0 ≤ D) (hδ : 0 < δ) (y : TorusSite n)
    (A : TorusBond n → imaginaryQuaternions) :
    flatHessian (sh y) (formCoords A) (formCoords A) ≤
      D * (4 * expSumBound (δ / 2)) * ∑ b : TorusBond n, bondWeight δ y b * ‖A b‖ ^ 2 := by
  rw [← sum_mixedDeriv_eq_flatHessian (h.contDiff y) A A]
  have h1 : ∑ b : TorusBond n, ∑ b' : TorusBond n, mixedDeriv (sh y) (trivialField n) ![b, b'] ![A b, A b'] ≤
      D * (∑ b : TorusBond n, bondWeight δ y b * ‖A b‖) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b' _ => ?_
    refine (le_abs_self _).trans ((abs_mixedDeriv_le_weights h hD hδ y b b' _ _).trans (le_of_eq ?_))
    ring
  refine h1.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hD
  set r : TorusBond n → ℝ := fun b => Real.exp (-(δ / 4) * _root_.YangMills.Construction.TorusFields.supDist b.1 y) with hr
  have hq : ∀ b, bondWeight δ y b = r b ^ 2 := fun b => by
    simp only [bondWeight, hr]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ r (fun b => r b * ‖A b‖)
  have h3 : ∑ b : TorusBond n, r b * (r b * ‖A b‖) = ∑ b : TorusBond n, bondWeight δ y b * ‖A b‖ :=
    Finset.sum_congr rfl fun b _ => by rw [hq]; ring
  have h4 : ∑ b : TorusBond n, (r b * ‖A b‖) ^ 2 = ∑ b : TorusBond n, bondWeight δ y b * ‖A b‖ ^ 2 :=
    Finset.sum_congr rfl fun b _ => by rw [hq]; ring
  have h5 : ∑ b : TorusBond n, r b ^ 2 ≤ 4 * expSumBound (δ / 2) := by
    have := sum_bonds_exp_le (n := n) (β := δ / 2) (by positivity) y
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hq]
    rfl
  rw [h3, h4] at h2
  refine h2.trans (mul_le_mul_of_nonneg_right h5 ?_)
  exact Finset.sum_nonneg fun b _ => mul_nonneg (Real.exp_pos _).le (by positivity)
private theorem flatHessian_share_le (hL : AxialGauge.axialGaugeCurlBoundStatement) {R : ℕ} (hR : 1 ≤ R)
    (hn : 16 * R < n) {o y : TorusSite n} (hy : y ∈ supBall o (2 * R))
    (h : FlatShareBounds sh (supBall o (2 * R)) D δ N0 σ) (hσ : 0 < σ) (hN : 0 ≤ N0) (hD : 0 ≤ D) (hδ : 0 < δ)
    (v : TorusBond n → imaginaryQuaternions) :
    flatHessian (sh y) (formCoords v) (formCoords v) ≤ D * (4 * expSumBound (δ / 2)) *
      ∑ b : TorusBond n, bondWeight δ y b *
        (9 * (_root_.YangMills.Construction.TorusFields.supDist b.1 y : ℝ) ^ 2 * nearCurlSquares (supBall o (2 * R)) v y (_root_.YangMills.Construction.TorusFields.supDist b.1 y)) := by
  classical
  obtain ⟨A, hoff, hcurl, hbd⟩ := hL n R hR hn o y hy v
  rw [flatHessian_eq_of_curl_eq h hσ hN y hcurl]
  refine (flatHessian_le_weighted h hD hδ y A).trans ?_
  have hK : 0 ≤ D * (4 * expSumBound (δ / 2)) :=
    mul_nonneg hD (by have := expSumBound_nonneg (β := δ / 2) (by positivity); positivity)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) hK
  have hq : 0 ≤ bondWeight δ y b := (Real.exp_pos _).le
  refine mul_le_mul_of_nonneg_left ?_ hq
  have hnear : 0 ≤ nearCurlSquares (supBall o (2 * R)) v y (_root_.YangMills.Construction.TorusFields.supDist b.1 y) :=
    Finset.sum_nonneg fun p _ => by split_ifs <;> positivity
  by_cases hb : b.1 ∈ supBall o (2 * R) ∧ b.1 + TorusFields.unitStep n b.2 ∈ supBall o (2 * R)
  · obtain ⟨x, i⟩ := b
    have h1 := hbd x i (Real.sqrt (nearCurlSquares (supBall o (2 * R)) v y (_root_.YangMills.Construction.TorusFields.supDist x y))) (Real.sqrt_nonneg _)
      hb.1 hb.2
      (fun p hp hle => by
        refine Real.le_sqrt_of_sq_le ?_
        have h2 : (if _root_.YangMills.Construction.TorusFields.supDist p.1 y ≤ _root_.YangMills.Construction.TorusFields.supDist x y then ‖lieFormCurl v p‖ ^ 2 else 0) ≤
            nearCurlSquares (supBall o (2 * R)) v y (_root_.YangMills.Construction.TorusFields.supDist x y) :=
          Finset.single_le_sum (f := fun p => if _root_.YangMills.Construction.TorusFields.supDist p.1 y ≤ _root_.YangMills.Construction.TorusFields.supDist x y then ‖lieFormCurl v p‖ ^ 2 else 0)
            (fun p _ => by split_ifs <;> positivity) hp
        rwa [if_pos hle] at h2)
    have h3 : ‖A (x, i)‖ ^ 2 ≤
        (3 * ((_root_.YangMills.Construction.TorusFields.supDist x y : ℝ) * Real.sqrt (nearCurlSquares (supBall o (2 * R)) v y (_root_.YangMills.Construction.TorusFields.supDist x y)))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    refine h3.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hnear]
    norm_num
    ring
  · rw [show A b = 0 from hoff b.1 b.2 hb]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
private theorem sum_weights_le (hδ : 0 < δ) (z : TorusSite n) :
    ∑ y : TorusSite n, ∑ b : TorusBond n,
      (if supDist z y ≤ supDist b.1 y then bondWeight δ y b * (9 * (supDist b.1 y : ℝ) ^ 2) else 0) ≤
      288 / δ ^ 2 * (4 * expSumBound (δ / 8) * expSumBound (δ / 8)) := by
  have hβ : 0 < δ / 8 := by positivity
  have hF := expSumBound_nonneg hβ
  have hC : 0 ≤ 288 / δ ^ 2 := by positivity
  have hterm : ∀ (y : TorusSite n) (b : TorusBond n),
      (if supDist z y ≤ supDist b.1 y then bondWeight δ y b * (9 * (supDist b.1 y : ℝ) ^ 2) else 0) ≤
        288 / δ ^ 2 * (Real.exp (-(δ / 8) * _root_.YangMills.Construction.TorusFields.supDist y z) * Real.exp (-(δ / 8) * _root_.YangMills.Construction.TorusFields.supDist b.1 y)) := by
    intro y b
    split_ifs with hle
    · set d : ℝ := ((_root_.YangMills.Construction.TorusFields.supDist b.1 y : ℕ) : ℝ) with hd
      have hr : ((_root_.YangMills.Construction.TorusFields.supDist y z : ℕ) : ℝ) ≤ d := by
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm y z, hd]
        exact_mod_cast hle
      have h1 : (δ * d / 4) ^ 2 / 2 ≤ Real.exp (δ * d / 4) := by
        have := Real.quadratic_le_exp_of_nonneg (x := δ * d / 4) (by positivity)
        have h2 : 0 ≤ δ * d / 4 := by positivity
        linarith
      have h2 : 9 * d ^ 2 ≤ 288 / δ ^ 2 * Real.exp (δ * d / 4) := by
        have h3 : 0 < δ ^ 2 := by positivity
        rw [div_mul_eq_mul_div, le_div_iff₀ h3]
        nlinarith
      have h4 : bondWeight δ y b = Real.exp (-(δ / 2) * d) := rfl
      rw [h4]
      calc Real.exp (-(δ / 2) * d) * (9 * d ^ 2)
          ≤ Real.exp (-(δ / 2) * d) * (288 / δ ^ 2 * Real.exp (δ * d / 4)) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = 288 / δ ^ 2 * Real.exp (-(δ / 4) * d) := by
            rw [mul_left_comm, ← Real.exp_add]
            congr 2
            ring
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ hC
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            nlinarith
    · positivity
  calc _ ≤ ∑ y : TorusSite n, ∑ b : TorusBond n,
        288 / δ ^ 2 * (Real.exp (-(δ / 8) * _root_.YangMills.Construction.TorusFields.supDist y z) * Real.exp (-(δ / 8) * _root_.YangMills.Construction.TorusFields.supDist b.1 y)) :=
        Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun b _ => hterm y b
    _ = 288 / δ ^ 2 * ∑ y : TorusSite n, Real.exp (-(δ / 8) * _root_.YangMills.Construction.TorusFields.supDist y z) *
        ∑ b : TorusBond n, Real.exp (-(δ / 8) * _root_.YangMills.Construction.TorusFields.supDist b.1 y) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 288 / δ ^ 2 * ∑ y : TorusSite n, Real.exp (-(δ / 8) * _root_.YangMills.Construction.TorusFields.supDist y z) * (4 * expSumBound (δ / 8)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) hC
        exact mul_le_mul_of_nonneg_left (sum_bonds_exp_le hβ y) (Real.exp_pos _).le
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        rw [← Finset.sum_mul]
        have := sum_sites_exp_le (n := n) hβ z
        have h5 : 0 ≤ 4 * expSumBound (δ / 8) := by positivity
        calc _ ≤ expSumBound (δ / 8) * (4 * expSumBound (δ / 8)) := mul_le_mul_of_nonneg_right this h5
          _ = _ := by ring
private def hessianCeiling (D δ : ℝ) : ℝ :=
  D * (4 * expSumBound (δ / 2)) * (288 / δ ^ 2 * (4 * expSumBound (δ / 8) * expSumBound (δ / 8)))
private theorem sum_flatHessian_le (hL : AxialGauge.axialGaugeCurlBoundStatement) {R : ℕ} (hR : 1 ≤ R)
    (hn : 16 * R < n) {o : TorusSite n}
    (h : FlatShareBounds sh (supBall o (2 * R)) D δ N0 σ) (hσ : 0 < σ) (hN : 0 ≤ N0) (hD : 0 ≤ D) (hδ : 0 < δ)
    (v : TorusBond n → imaginaryQuaternions) :
    ∑ y : TorusSite n, flatHessian (sh y) (formCoords v) (formCoords v) ≤
      hessianCeiling D δ * ∑ p ∈ plaquettesIn (supBall o (2 * R)), ‖lieFormCurl v p‖ ^ 2 := by
  classical
  set S := supBall o (2 * R) with hS
  have hK : 0 ≤ D * (4 * expSumBound (δ / 2)) :=
    mul_nonneg hD (by have := expSumBound_nonneg (β := δ / 2) (by positivity); positivity)
  have h1 : ∀ y : TorusSite n, flatHessian (sh y) (formCoords v) (formCoords v) ≤ D * (4 * expSumBound (δ / 2)) *
      ∑ b : TorusBond n, bondWeight δ y b * (9 * (_root_.YangMills.Construction.TorusFields.supDist b.1 y : ℝ) ^ 2 * nearCurlSquares S v y (_root_.YangMills.Construction.TorusFields.supDist b.1 y)) := by
    intro y
    by_cases hy : y ∈ S
    · exact flatHessian_share_le hL hR hn hy h hσ hN hD hδ v
    · have hz : flatHessian (sh y) (formCoords v) (formCoords v) ≤ 0 := by
        refine flatHessian_nonpos (h.contDiff y) (h.trivial_eq_zero hσ y) v (h.eventually_nonneg hσ y v)
          fun ε hε => ?_
        refine Eventually.of_forall fun τ => ?_
        rw [h.vanish_off y hy]
        positivity
      refine hz.trans (mul_nonneg hK (Finset.sum_nonneg fun b _ => ?_))
      have : 0 ≤ nearCurlSquares S v y (_root_.YangMills.Construction.TorusFields.supDist b.1 y) :=
        Finset.sum_nonneg fun p _ => by split_ifs <;> positivity
      have hq : 0 ≤ bondWeight δ y b := (Real.exp_pos _).le
      positivity
  refine (Finset.sum_le_sum fun y _ => h1 y).trans ?_
  rw [← Finset.mul_sum]
  have e : hessianCeiling D δ * ∑ p ∈ plaquettesIn S, ‖lieFormCurl v p‖ ^ 2 = D * (4 * expSumBound (δ / 2)) *
      ((288 / δ ^ 2 * (4 * expSumBound (δ / 8) * expSumBound (δ / 8))) *
        ∑ p ∈ plaquettesIn S, ‖lieFormCurl v p‖ ^ 2) := by
    unfold hessianCeiling
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hK
  have h2 : ∑ y : TorusSite n, ∑ b : TorusBond n,
      bondWeight δ y b * (9 * (_root_.YangMills.Construction.TorusFields.supDist b.1 y : ℝ) ^ 2 * nearCurlSquares S v y (_root_.YangMills.Construction.TorusFields.supDist b.1 y)) =
      ∑ p ∈ plaquettesIn S, ‖lieFormCurl v p‖ ^ 2 * ∑ y : TorusSite n, ∑ b : TorusBond n,
        (if _root_.YangMills.Construction.TorusFields.supDist p.1 y ≤ _root_.YangMills.Construction.TorusFields.supDist b.1 y then bondWeight δ y b * (9 * (_root_.YangMills.Construction.TorusFields.supDist b.1 y : ℝ) ^ 2) else 0) := by
    simp only [nearCurlSquares, Finset.mul_sum]
    calc _ = ∑ y : TorusSite n, ∑ p ∈ plaquettesIn S, ∑ b : TorusBond n,
          bondWeight δ y b * (9 * (supDist b.1 y : ℝ) ^ 2 *
          (if _root_.YangMills.Construction.TorusFields.supDist p.1 y ≤ _root_.YangMills.Construction.TorusFields.supDist b.1 y then ‖lieFormCurl v p‖ ^ 2 else 0)) :=
          Finset.sum_congr rfl fun y _ => Finset.sum_comm
      _ = ∑ p ∈ plaquettesIn S, ∑ y : TorusSite n, ∑ b : TorusBond n,
          bondWeight δ y b * (9 * (supDist b.1 y : ℝ) ^ 2 *
          (if _root_.YangMills.Construction.TorusFields.supDist p.1 y ≤ _root_.YangMills.Construction.TorusFields.supDist b.1 y then ‖lieFormCurl v p‖ ^ 2 else 0)) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun b _ => ?_
          split_ifs
          · ring
          · simp
  rw [h2, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (sum_weights_le hδ p.1) (by positivity)
end ShareCeiling
section LevelShares
variable {n : ℕ} [NeZero n]
private theorem cellShare_eq_zero_of_not_mem {F : BlockFrame} (hL : Odd F.blockSide) {a : ℝ} {S : Finset F.Cell}
    {Y : F.Cell} (X : F.FieldChain) (hY : Y ∉ S) : cellShare a S Y X = 0 := by
  classical
  have hne : ∀ {j : ℕ} {x : F.Site j}, x ∈ sitesOfCells S j → enclosingCell x ≠ Y := fun hx e =>
    hY (e ▸ BlockLines.enclosingCell_mem hL hx)
  unfold cellShare
  have h1 : ∑ p ∈ innerPlaquettes S 0,
      (∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0) *
      (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    have hc := (Finset.mem_filter.mp hp).2.2
    rw [Finset.sum_eq_zero fun x hx => if_neg (hne (hc hx)), zero_mul]
  have h2 : ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1),
      ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
        (if enclosingCell (c.1 + BlockAverages.unitStep (j + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) *
        blockFit (X j) (X (j + 1)) c = 0 := by
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun c hc => ?_
    obtain ⟨h3, h4⟩ := Finset.mem_filter.mp hc
    rw [if_neg (hne (Finset.mem_product.mp h3).1), if_neg (hne h4)]
    simp
  rw [h1, h2]
  simp
private theorem levelShare_eq_zero_of_not_mem (a : ℝ) {L : ℕ} (hL : Odd L) (t : ℕ) {X : Finset (TorusSite n)}
    {y : TorusSite n} (W : TorusField n) (hy : y ∉ X) : levelShare a L (t + 1) X y W = 0 := by
  have hp : ∀ i, (torusFrame L t n).period (torusFrame L t n).top i = n := fun i => TorusFrame.period_torusFrame i
  show minimalCellShare a (cellsOfSites (torusFrame L t n) X) (torusSiteInFrame (torusFrame L t n) (t + 1) y)
    (readAtLevel (torusFrame L t n) (t + 1) _) = 0
  unfold minimalCellShare
  split_ifs
  · refine cellShare_eq_zero_of_not_mem (F := torusFrame L t n) hL _ ?_
    intro hin
    have := (mem_cellsOfSites_iff hp _ _).mp hin
    have e := toTorusSite_torusSiteInFrame (F := torusFrame L t n) hp y
    exact hy (e ▸ this)
  · rfl
private theorem flatShareBounds_succ {a δ lam ρ σA cg : ℝ} {L : ℕ} {N : ℕ → ℝ} (hL : Odd L)
    (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (t : ℕ) (hn : 64 ≤ n) {X : Finset (TorusSite n)}
    (hreg : IsRegularRegion X 1024) :
    FlatShareBounds (fun y => levelShare a L (t + 1) X y) X (N 2) δ (N 0) σA := by
  obtain ⟨hδ, hδ8, hlam, hρ, hρ1, hσ, hcg, hN, hch⟩ := hc
  have : NeZero L := ⟨hL.pos.ne'⟩
  have hp : ∀ i, (torusFrame L t n).period (torusFrame L t n).top i = n := fun i => TorusFrame.period_torusFrame i
  have hamb : IsAdmissibleAmbient (torusFrame L t n) := Or.inr fun _ => hn
  have hreg' : IsOrthantRegular (cellsOfSites (torusFrame L t n) X) 1024 := isOrthantRegular_of_isRegularRegion hp hreg
  have key : ∀ (s : ℝ) (W : TorusField n), 0 < s → s ≤ σA → IsColdOn s X W →
      HasRegularCellShares a δ s N (cellsOfSites (torusFrame L t n) X)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top W) :=
    fun s W hs0 hs hcold => (hch (torusFrame L t n) 1024 (cellsOfSites (torusFrame L t n) X) rfl hamb le_rfl hreg' s _
      hs0 hs (isCold_of_isColdOn (F := torusFrame L t n) hp hcold)).2.2.1
  obtain ⟨-, hSn, -, -, -, -, hShare, -, -⟩ := key σA (trivialField n) hσ le_rfl (isColdOn_trivialField X hσ)
  refine ⟨fun y => contDiffThreeAt_of_isBondAnalyticAt hp (hSn _), ?_, ?_, ?_⟩
  · intro y b b' U U' hU hU'
    have hX : AreUnitVectors ![U, U'] := fun l => by
      fin_cases l
      · exact hU
      · exact hU'
    have gen : ∀ l₀ : Fin 2, |mixedDeriv (levelShare a L (t + 1) X y) (trivialField n) ![b, b'] ![U, U']| ≤
        N 2 * Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist y ((![b, b'] : Fin 2 → TorusBond n) l₀).1) := by
      intro l₀
      have e : mixedDeriv (levelShare a L (t + 1) X y) (trivialField n) ![b, b'] ![U, U'] =
          mixedBondDerivative (minimalCellShare a (cellsOfSites (torusFrame L t n) X)
              (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y))
            (readAtLevel (torusFrame L t n) (torusFrame L t n).top (trivialField n))
            (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top
                ((![b, b'] : Fin 2 → TorusBond n) l).1,
              ((![b, b'] : Fin 2 → TorusBond n) l).2)) ![U, U'] :=
        mixedDeriv_readAtLevel hp (minimalCellShare a (cellsOfSites (torusFrame L t n) X)
            (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y))
          (trivialField n) ![b, b'] ![U, U']
      rw [e]
      refine (hShare _ 2 _ _ (by norm_num) hX).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hN 2).le
      have h2 : cellSupDist (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
          (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top ((![b, b'] : Fin 2 → TorusBond n) l₀).1) ≤
          bondListDistance (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
            (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top
                ((![b, b'] : Fin 2 → TorusBond n) l).1,
              ((![b, b'] : Fin 2 → TorusBond n) l).2)) :=
        Finset.le_sup (f := fun l : Fin 2 => cellSupDist (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
          (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top ((![b, b'] : Fin 2 → TorusBond n) l).1))
          (Finset.mem_univ l₀)
      rw [cellSupDist_torusSiteInFrame hp] at h2
      have h3 : ((_root_.YangMills.Construction.TorusFields.supDist y ((![b, b'] : Fin 2 → TorusBond n) l₀).1 : ℕ) : ℝ) ≤
          (bondListDistance (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
            (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top
                ((![b, b'] : Fin 2 → TorusBond n) l).1,
              ((![b, b'] : Fin 2 → TorusBond n) l).2)) : ℝ) := by exact_mod_cast h2
      nlinarith
    exact ⟨gen 0, gen 1⟩
  · intro y s W hs0 hs hcold
    obtain ⟨-, -, -, -, -, -, -, hS, -⟩ := key s W hs0 hs hcold
    exact hS _
  · intro y hy W
    exact levelShare_eq_zero_of_not_mem a hL t W hy
private theorem readAtLevel_gaugeTransform {F : BlockFrame} [∀ i, NeZero (F.period F.top i)]
    (hp : ∀ i, F.period F.top i = n) (g : TorusSite n → UnitQuaternion) (W : TorusField n) :
    readAtLevel F F.top (TorusFields.gaugeTransform g W) =
      BlockAverages.gaugeTransform (fun y => g (toTorusSite n y)) (readAtLevel F F.top W) := by apply _root_.YangMills.Construction.LevelAction.readAtLevel_gaugeTransform <;> assumption
private theorem actionAtLevel_gaugeTransform (hS : SharesSumToAction) {a δ lam ρ σA cg : ℝ} {L : ℕ} {N : ℕ → ℝ}
    (ha : 0 ≤ a) (hL : Odd L) (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (t : ℕ) (hn : 64 ≤ n)
    {X : Finset (TorusSite n)} {W : TorusField n} (hreg : IsRegularRegion X 1024) (hcold : IsColdOn σA X W)
    (g : TorusSite n → UnitQuaternion) :
    actionAtLevel a L (t + 1) X (TorusFields.gaugeTransform g W) = actionAtLevel a L (t + 1) X W := by
  obtain ⟨hδ, hδ8, hlam, hρ, hρ1, hσ, hcg, hN, hch⟩ := hc
  have : NeZero L := ⟨hL.pos.ne'⟩
  have hp : ∀ i, (torusFrame L t n).period (torusFrame L t n).top i = n := fun i => TorusFrame.period_torusFrame i
  have hreg' : IsOrthantRegular (cellsOfSites (torusFrame L t n) X) 1024 := isOrthantRegular_of_isRegularRegion hp hreg
  have hcold' := isCold_of_isColdOn (F := torusFrame L t n) hp hcold
  obtain ⟨-, -, H3, -⟩ := hch (torusFrame L t n) 1024 _ rfl (Or.inr fun _ => hn) le_rfl hreg' σA _ hσ le_rfl hcold'
  obtain ⟨-, -, -, hG, -⟩ := H3
  rw [← hS a L t n X (TorusFields.gaugeTransform g W) ha hL.pos (by omega), ← hS a L t n X W ha hL.pos (by omega)]
  refine Finset.sum_congr rfl fun y _ => ?_
  show minimalCellShare a (cellsOfSites (torusFrame L t n) X)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top (TorusFields.gaugeTransform g W)) =
    minimalCellShare a (cellsOfSites (torusFrame L t n) X)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
  rw [readAtLevel_gaugeTransform hp]
  exact hG _ _
private theorem flatHessian_sum {sh : TorusSite n → TorusField n → ℝ} {S : Finset (TorusSite n)} {D δ N0 σ : ℝ}
    (h : FlatShareBounds sh S D δ N0 σ) (hσ : 0 < σ) {G : TorusField n → ℝ} (h3 : ContDiffThreeAt G (trivialField n))
    (hsum : ∀ W, G W = ∑ y, sh y W) (u : TorusBond n → imaginaryQuaternions) :
    flatHessian G (formCoords u) (formCoords u) = ∑ y, flatHessian (sh y) (formCoords u) (formCoords u) := by
  have h0 : G (trivialField n) = 0 := by
    rw [hsum]
    exact Finset.sum_eq_zero fun y _ => h.trivial_eq_zero hσ y
  have hpos : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 ≤ G (exponentialField (τ • u)) := by
    have : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ y ∈ (Finset.univ : Finset (TorusSite n)), 0 ≤ sh y (exponentialField (τ • u)) :=
      (Finset.eventually_all _).mpr fun y _ => h.eventually_nonneg hσ y u
    filter_upwards [this] with τ hτ
    rw [hsum]
    exact Finset.sum_nonneg hτ
  have h1 := tendsto_flatHessian h3 h0 u hpos
  have h2 : Tendsto (fun τ : ℝ => ∑ y, sh y (exponentialField (τ • u)) / τ ^ 2) (𝓝[≠] 0)
      (𝓝 (∑ y, flatHessian (sh y) (formCoords u) (formCoords u) / 2)) :=
    tendsto_finsetSum _ fun y _ =>
      tendsto_flatHessian (h.contDiff y) (h.trivial_eq_zero hσ y) u (h.eventually_nonneg hσ y u)
  have h4 : Tendsto (fun τ : ℝ => G (exponentialField (τ • u)) / τ ^ 2) (𝓝[≠] 0)
      (𝓝 (∑ y, flatHessian (sh y) (formCoords u) (formCoords u) / 2)) := by
    refine h2.congr' (Eventually.of_forall fun τ => ?_)
    show _ = G (exponentialField (τ • u)) / τ ^ 2
    rw [hsum, Finset.sum_div]
  have h5 := tendsto_nhds_unique h1 h4
  rw [← Finset.sum_div] at h5
  linarith
private theorem abs_valMinAbs_cases {a : ℤ} (h1 : |a| ≤ n) :
    |((a : ZMod n)).valMinAbs| = |a| ∨ |((a : ZMod n)).valMinAbs| = n - |a| := by
  have hs : ∀ y : ℤ, ((a : ZMod n)) = y → y * 2 ∈ Set.Ioc (-(n : ℤ)) n → ((a : ZMod n)).valMinAbs = y :=
    fun y e hy => (ZMod.valMinAbs_spec _ _).mpr ⟨e, hy⟩
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have e1 : ((a + n : ℤ) : ZMod n) = a := by simp
  have e2 : ((a - n : ℤ) : ZMod n) = a := by simp
  simp only [Int.abs_eq_natAbs] at h1 ⊢
  by_cases c1 : a * 2 ∈ Set.Ioc (-(n : ℤ)) n
  · left
    rw [hs a rfl c1]
  · right
    rw [Set.mem_Ioc] at c1
    by_cases c2 : 0 ≤ a
    · rw [hs (a - n) e2.symm (by rw [Set.mem_Ioc]; omega)]
      omega
    · rw [hs (a + n) e1.symm (by rw [Set.mem_Ioc]; omega)]
      omega
private theorem supBall_isRegularRegion {R : ℕ} (hR : 1024 ≤ R) (hn : 16 * R < n) (o : TorusSite n) :
    IsRegularRegion (supBall o (2 * R)) 1024 := by
  intro z
  refine ⟨fun l => if 0 ≤ centredCoords o z l then -1 else 1, fun l => ?_, ?_⟩
  · by_cases h : 0 ≤ centredCoords o z l
    · right
      simp [h]
    · left
      simp [h]
  intro q hq hqz h hsign hh
  refine mem_supBall_iff.mpr fun l => ?_
  have hql := mem_supBall_iff.mp hq l
  have hz : ((centredCoords o z l).natAbs : ℕ) ≤ n / 2 := ZMod.natAbs_valMinAbs_le _
  have hl := hh l
  have hs := hsign l
  have hd := (_root_.YangMills.Construction.TorusFields.supDist_le_iff q z _).mp hqz l
  have e : (q + siteOfInt h : TorusSite n) l - o l = ((centredCoords o q l + h l : ℤ) : ZMod n) := by
    simp [centredCoords, siteOfInt, ZMod.coe_valMinAbs]
    ring
  have e2 : q l - z l = ((centredCoords o q l - centredCoords o z l : ℤ) : ZMod n) := by
    simp [centredCoords, ZMod.coe_valMinAbs]
  have hc : centredCoords o (q + siteOfInt h) l = centredCoords o q l + h l := by
    show ((q + siteOfInt h : TorusSite n) l - o l).valMinAbs = _
    rw [e, valMinAbs_intCast]
    simp only [Int.abs_eq_natAbs] at hql hl ⊢
    omega
  rw [hc]
  rw [e2] at hd
  simp only [Int.abs_eq_natAbs] at hql hl ⊢
  have h2 := abs_valMinAbs_cases (n := n) (a := centredCoords o q l - centredCoords o z l) (by
    simp only [Int.abs_eq_natAbs]
    omega)
  simp only [Int.abs_eq_natAbs] at h2
  by_cases hz0 : 0 ≤ centredCoords o z l
  · simp only [hz0, if_true] at hs
    omega
  · simp only [hz0, if_false] at hs
    omega
end LevelShares
section Colours
open ColdStepAtMirrorFrames ColdStepAtMirrorFrames.Adjoint
variable {n : ℕ} [NeZero n]
private def adjointForm (g : UnitQuaternion) (u : TorusBond n → imaginaryQuaternions) :
    TorusBond n → imaginaryQuaternions := fun b => _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (u b)
private theorem gaugeTransform_exponentialField (g : UnitQuaternion) (u : TorusBond n → imaginaryQuaternions) (τ : ℝ) :
    TorusFields.gaugeTransform (fun _ => g) (exponentialField (τ • u)) = exponentialField (τ • adjointForm g u) := by
  funext x i
  simp only [TorusFields.gaugeTransform, exponentialField, Pi.smul_apply, adjointForm, ← _root_.YangMills.Construction.ColdStepAtMirrorFrames.Adjoint.adjointAction_smul,
    expUnit_adjointAction]
private def hessianPairing (G : TorusField n → ℝ) (u v : TorusBond n → imaginaryQuaternions) : ℝ :=
  flatHessian G (formCoords u) (formCoords v)
private theorem hessianPairing_add_left (G : TorusField n → ℝ) (a b c : TorusBond n → imaginaryQuaternions) :
    hessianPairing G (a + b) c = hessianPairing G a c + hessianPairing G b c := by
  simp only [hessianPairing, formCoords_add, map_add, _root_.add_apply]
private theorem hessianPairing_add_right (G : TorusField n → ℝ) (a b c : TorusBond n → imaginaryQuaternions) :
    hessianPairing G a (b + c) = hessianPairing G a b + hessianPairing G a c := by
  simp only [hessianPairing, formCoords_add, map_add]
private theorem hessianPairing_smul_left (G : TorusField n → ℝ) (t : ℝ) (a b : TorusBond n → imaginaryQuaternions) :
    hessianPairing G (t • a) b = t * hessianPairing G a b := by
  simp only [hessianPairing, formCoords_smul, map_smul, _root_.smul_apply, smul_eq_mul]
private theorem hessianPairing_smul_right (G : TorusField n → ℝ) (t : ℝ) (a b : TorusBond n → imaginaryQuaternions) :
    hessianPairing G a (t • b) = t * hessianPairing G a b := by
  simp only [hessianPairing, formCoords_smul, map_smul, smul_eq_mul]
private theorem hessianPairing_symm {G : TorusField n → ℝ} (h : ContDiffThreeAt G (trivialField n))
    (a b : TorusBond n → imaginaryQuaternions) : hessianPairing G a b = hessianPairing G b a :=
  flatHessian_symm h _ _
variable {G : TorusField n → ℝ}
private theorem hessianPairing_adjoint_self (h3 : ContDiffThreeAt G (trivialField n)) (h0 : G (trivialField n) = 0)
    (hpos : ∀ W, 0 ≤ G W)
    (hg : ∀ (g : UnitQuaternion) (u : TorusBond n → imaginaryQuaternions), ∀ᶠ τ in 𝓝 (0 : ℝ),
      G (TorusFields.gaugeTransform (fun _ => g) (exponentialField (τ • u))) = G (exponentialField (τ • u)))
    (g : UnitQuaternion) (u : TorusBond n → imaginaryQuaternions) :
    hessianPairing G (adjointForm g u) (adjointForm g u) = hessianPairing G u u := by
  have h1 := tendsto_flatHessian h3 h0 u (Eventually.of_forall fun _ => hpos _)
  have h2 := tendsto_flatHessian h3 h0 (adjointForm g u) (Eventually.of_forall fun _ => hpos _)
  have h4 : Tendsto (fun τ : ℝ => G (exponentialField (τ • adjointForm g u)) / τ ^ 2) (𝓝[≠] 0)
      (𝓝 (flatHessian G (formCoords u) (formCoords u) / 2)) := by
    refine h1.congr' ?_
    filter_upwards [(hg g u).filter_mono nhdsWithin_le_nhds] with τ hτ
    rw [← gaugeTransform_exponentialField, hτ]
  have h5 := tendsto_nhds_unique h2 h4
  unfold hessianPairing
  linarith
private theorem hessianPairing_adjoint (h3 : ContDiffThreeAt G (trivialField n)) (h0 : G (trivialField n) = 0)
    (hpos : ∀ W, 0 ≤ G W)
    (hg : ∀ (g : UnitQuaternion) (u : TorusBond n → imaginaryQuaternions), ∀ᶠ τ in 𝓝 (0 : ℝ),
      G (TorusFields.gaugeTransform (fun _ => g) (exponentialField (τ • u))) = G (exponentialField (τ • u)))
    (g : UnitQuaternion) (u v : TorusBond n → imaginaryQuaternions) :
    hessianPairing G (adjointForm g u) (adjointForm g v) = hessianPairing G u v := by
  have e : adjointForm g (u + v) = adjointForm g u + adjointForm g v := by
    funext b
    exact _root_.YangMills.Construction.ColdStepAtMirrorFrames.Adjoint.adjointAction_add g _ _
  have h1 := hessianPairing_adjoint_self h3 h0 hpos hg g (u + v)
  have h2 := hessianPairing_adjoint_self h3 h0 hpos hg g u
  have h4 := hessianPairing_adjoint_self h3 h0 hpos hg g v
  rw [e] at h1
  simp only [hessianPairing_add_left, hessianPairing_add_right] at h1
  rw [hessianPairing_symm h3 (adjointForm g v) (adjointForm g u), hessianPairing_symm h3 v u] at h1
  linarith
open Classical in
private def singleBondForm (b : TorusBond n) (X : imaginaryQuaternions) : TorusBond n → imaginaryQuaternions :=
  Pi.single b X
private theorem singleBondForm_add (b : TorusBond n) (X Y : imaginaryQuaternions) :
    singleBondForm b (X + Y) = singleBondForm b X + singleBondForm b Y := by
  classical
  exact Pi.single_add (f := fun _ => imaginaryQuaternions) b X Y
private theorem singleBondForm_smul (b : TorusBond n) (c : ℝ) (X : imaginaryQuaternions) :
    singleBondForm b (c • X) = c • singleBondForm b X := by
  classical
  exact Pi.single_smul (f := fun _ => imaginaryQuaternions) b c X
private theorem adjointForm_singleBondForm (g : UnitQuaternion) (b : TorusBond n) (X : imaginaryQuaternions) :
    adjointForm g (singleBondForm b X) = singleBondForm b (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X) := by
  classical
  funext c
  by_cases hc : c = b
  · subst hc
    simp [adjointForm, singleBondForm]
  · simp [adjointForm, singleBondForm, hc, _root_.YangMills.Construction.ColdStepAtMirrorFrames.Adjoint.adjointAction_zero]
private theorem formCoords_singleBondForm (b : TorusBond n) (X : imaginaryQuaternions) :
    formCoords (singleBondForm b X) = Pi.single ⟨b, Finset.mem_univ b⟩ (imPartCLM (X : ℍ[ℝ])) := by
  classical
  funext c
  by_cases hc : c = ⟨b, Finset.mem_univ b⟩
  · subst hc
    simp [formCoords, singleBondForm]
  · have h1 : c.1 ≠ b := fun e => hc (Subtype.ext e)
    simp [formCoords, singleBondForm, hc, h1]
private theorem hessianPairing_singleBondForm (h3 : ContDiffThreeAt G (trivialField n)) (b b' : TorusBond n)
    (X Y : imaginaryQuaternions) :
    hessianPairing G (singleBondForm b X) (singleBondForm b' Y) = mixedDeriv G (trivialField n) ![b, b'] ![X, Y] := by
  unfold hessianPairing
  rw [formCoords_singleBondForm, formCoords_singleBondForm]
  exact flatHessian_single h3 b b' X Y
private def quat (a b c d : ℝ) : ℍ[ℝ] := ⟨a, b, c, d⟩
@[simp] private theorem quat_re (a b c d : ℝ) : (quat a b c d).re = a := rfl
@[simp] private theorem quat_imI (a b c d : ℝ) : (quat a b c d).imI = b := rfl
@[simp] private theorem quat_imJ (a b c d : ℝ) : (quat a b c d).imJ = c := rfl
@[simp] private theorem quat_imK (a b c d : ℝ) : (quat a b c d).imK = d := rfl
private def imagI : imaginaryQuaternions := ⟨quat 0 1 0 0, rfl⟩
private def imagJ : imaginaryQuaternions := ⟨quat 0 0 1 0, rfl⟩
private def imagK : imaginaryQuaternions := ⟨quat 0 0 0 1, rfl⟩
@[simp] private theorem coe_imagI : ((imagI : imaginaryQuaternions) : ℍ[ℝ]) = quat 0 1 0 0 := rfl
@[simp] private theorem coe_imagJ : ((imagJ : imaginaryQuaternions) : ℍ[ℝ]) = quat 0 0 1 0 := rfl
@[simp] private theorem coe_imagK : ((imagK : imaginaryQuaternions) : ℍ[ℝ]) = quat 0 0 0 1 := rfl
private theorem imaginary_expand (X : imaginaryQuaternions) :
    X = (X : ℍ[ℝ]).imI • imagI + (X : ℍ[ℝ]).imJ • imagJ + (X : ℍ[ℝ]).imK • imagK := by
  have hr : (X : ℍ[ℝ]).re = 0 := X.2
  apply Subtype.ext
  ext <;> simp [hr]
private def unitI : UnitQuaternion := ⟨quat 0 1 0 0, by rw [Unitary.mem_iff]; constructor <;> ext <;> simp⟩
private def unitJ : UnitQuaternion := ⟨quat 0 0 1 0, by rw [Unitary.mem_iff]; constructor <;> ext <;> simp⟩
private def unitCycle : UnitQuaternion := ⟨quat (1 / 2) (1 / 2) (1 / 2) (1 / 2), by
  rw [Unitary.mem_iff]; constructor <;> ext <;> simp <;> norm_num⟩
@[simp] private theorem coe_unitI : ((unitI : UnitQuaternion) : ℍ[ℝ]) = quat 0 1 0 0 := rfl
@[simp] private theorem coe_unitJ : ((unitJ : UnitQuaternion) : ℍ[ℝ]) = quat 0 0 1 0 := rfl
@[simp] private theorem coe_unitCycle : ((unitCycle : UnitQuaternion) : ℍ[ℝ]) = quat (1 / 2) (1 / 2) (1 / 2) (1 / 2) :=
  rfl
private theorem coe_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X : imaginaryQuaternions) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (X : ℍ[ℝ]) * star (g : ℍ[ℝ]) := rfl
private theorem adjointAction_unitI_imagI : ColdStepAtMirrorFrames.adjointAction unitI imagI = imagI := by
  apply Subtype.ext
  rw [coe_adjointAction]
  ext <;> simp
private theorem adjointAction_unitI_imagJ : ColdStepAtMirrorFrames.adjointAction unitI imagJ = -imagJ := by
  apply Subtype.ext
  rw [coe_adjointAction]
  ext <;> simp
private theorem adjointAction_unitI_imagK : ColdStepAtMirrorFrames.adjointAction unitI imagK = -imagK := by
  apply Subtype.ext
  rw [coe_adjointAction]
  ext <;> simp
private theorem adjointAction_unitJ_imagJ : ColdStepAtMirrorFrames.adjointAction unitJ imagJ = imagJ := by
  apply Subtype.ext
  rw [coe_adjointAction]
  ext <;> simp
private theorem adjointAction_unitJ_imagK : ColdStepAtMirrorFrames.adjointAction unitJ imagK = -imagK := by
  apply Subtype.ext
  rw [coe_adjointAction]
  ext <;> simp
private theorem adjointAction_unitCycle_imagI : ColdStepAtMirrorFrames.adjointAction unitCycle imagI = imagJ := by
  apply Subtype.ext
  rw [coe_adjointAction]
  ext <;> simp <;> norm_num
private theorem adjointAction_unitCycle_imagJ : ColdStepAtMirrorFrames.adjointAction unitCycle imagJ = imagK := by
  apply Subtype.ext
  rw [coe_adjointAction]
  ext <;> simp <;> norm_num
private theorem singleBondForm_neg (b : TorusBond n) (X : imaginaryQuaternions) :
    singleBondForm b (-X) = (-1 : ℝ) • singleBondForm b X := by
  have e : (-1 : ℝ) • X = -X := neg_one_smul ℝ X
  rw [← singleBondForm_smul, e]
private theorem hessianPairing_singleBondForm_eq_sum (h3 : ContDiffThreeAt G (trivialField n))
    (hinv : ∀ (g : UnitQuaternion) (u v : TorusBond n → imaginaryQuaternions),
      hessianPairing G (adjointForm g u) (adjointForm g v) = hessianPairing G u v)
    (b b' : TorusBond n) (X Y : imaginaryQuaternions) :
    hessianPairing G (singleBondForm b X) (singleBondForm b' Y) = ∑ e : Fin 3,
      hessianPairing G (singleBondForm b imagI) (singleBondForm b' imagI) * imaginaryComponent e X *
        imaginaryComponent e Y := by
  have inv : ∀ (g : UnitQuaternion) (P Q : imaginaryQuaternions),
      hessianPairing G (singleBondForm b (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g P)) (singleBondForm b' (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g Q)) =
        hessianPairing G (singleBondForm b P) (singleBondForm b' Q) :=
    fun g P Q => by rw [← adjointForm_singleBondForm, ← adjointForm_singleBondForm, hinv]
  have off : ∀ (g : UnitQuaternion) (P Q : imaginaryQuaternions),
      (ColdStepAtMirrorFrames.adjointAction g P = P ∧ ColdStepAtMirrorFrames.adjointAction g Q = -Q) →
        hessianPairing G (singleBondForm b P) (singleBondForm b' Q) = 0 := by
    intro g P Q ⟨h1, h2⟩
    have h4 := inv g P Q
    rw [h1, h2, singleBondForm_neg, hessianPairing_smul_right] at h4
    linarith
  have off' : ∀ (g : UnitQuaternion) (P Q : imaginaryQuaternions),
      (ColdStepAtMirrorFrames.adjointAction g P = -P ∧ ColdStepAtMirrorFrames.adjointAction g Q = Q) →
        hessianPairing G (singleBondForm b P) (singleBondForm b' Q) = 0 := by
    intro g P Q ⟨h1, h2⟩
    have h4 := inv g P Q
    rw [h1, h2, singleBondForm_neg, hessianPairing_smul_left] at h4
    linarith
  have e12 := off unitI imagI imagJ ⟨adjointAction_unitI_imagI, adjointAction_unitI_imagJ⟩
  have e13 := off unitI imagI imagK ⟨adjointAction_unitI_imagI, adjointAction_unitI_imagK⟩
  have e21 := off' unitI imagJ imagI ⟨adjointAction_unitI_imagJ, adjointAction_unitI_imagI⟩
  have e31 := off' unitI imagK imagI ⟨adjointAction_unitI_imagK, adjointAction_unitI_imagI⟩
  have e23 := off unitJ imagJ imagK ⟨adjointAction_unitJ_imagJ, adjointAction_unitJ_imagK⟩
  have e32 := off' unitJ imagK imagJ ⟨adjointAction_unitJ_imagK, adjointAction_unitJ_imagJ⟩
  have d2 : hessianPairing G (singleBondForm b imagJ) (singleBondForm b' imagJ) =
      hessianPairing G (singleBondForm b imagI) (singleBondForm b' imagI) := by
    have := inv unitCycle imagI imagI
    rwa [adjointAction_unitCycle_imagI] at this
  have d3 : hessianPairing G (singleBondForm b imagK) (singleBondForm b' imagK) =
      hessianPairing G (singleBondForm b imagI) (singleBondForm b' imagI) := by
    have := inv unitCycle imagJ imagJ
    rw [adjointAction_unitCycle_imagJ] at this
    rw [this, d2]
  conv_lhs => rw [imaginary_expand X, imaginary_expand Y]
  simp only [singleBondForm_add, singleBondForm_smul, hessianPairing_add_left, hessianPairing_add_right,
    hessianPairing_smul_left, hessianPairing_smul_right, e12, e13, e21, e31, e23, e32, d2, d3]
  simp only [Fin.sum_univ_three, imaginaryComponent, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  simp
  ring
end Colours
section Floors
private theorem sum_min_curvature_le_read {F : BlockFrame} {j N : ℕ} [NeZero N] (hp : ∀ i, F.period j i = N)
    (X : Finset (TorusSite N)) (W : TorusField N) {l : ℝ} (hl : 0 ≤ l) (Y : Finset (F.Site j))
    (hY : ∀ x ∈ X, torusSiteInFrame F j x ∈ Y) :
    ∑ p ∈ plaquettesIn X, min (curvature W p.1 p.2.1 p.2.2 ^ 2) l ≤
      ∑ p ∈ LumpContours.cutPlaquettes Y, min (plaquetteDefect (readAtLevel F j W) p ^ 2) l := by
  classical
  set m : TorusPlaquette N → F.Site j × Fin 4 × Fin 4 := fun p => (torusSiteInFrame F j p.1, p.2) with hm
  have hinj : Function.Injective m := by
    intro p q hpq
    have h1 : torusSiteInFrame F j p.1 = torusSiteInFrame F j q.1 :=
      congrArg (fun z : F.Site j × Fin 4 × Fin 4 => z.1) hpq
    have h2 : p.2 = q.2 := congrArg (fun z : F.Site j × Fin 4 × Fin 4 => z.2) hpq
    refine Prod.ext ?_ h2
    rw [← TopLevelSites.toTorusSite_torusSiteInFrame hp p.1, ← TopLevelSites.toTorusSite_torusSiteInFrame hp q.1, h1]
  have hunit : ∀ i : Fin 4, BlockAverages.unitStep j i = torusSiteInFrame F j (TorusFields.unitStep N i) := fun i => by
    apply TopLevelSites.toTorusSite_injective hp
    rw [TopLevelSites.toTorusSite_unitStep hp, TopLevelSites.toTorusSite_torusSiteInFrame hp]
  have hval : ∀ p : TorusPlaquette N,
      min (plaquetteDefect (readAtLevel F j W) (m p) ^ 2) l = min (curvature W p.1 p.2.1 p.2.2 ^ 2) l := by
    rintro ⟨x, μ, ν⟩
    show min (plaquetteDefect (readAtLevel F j W) (torusSiteInFrame F j x, μ, ν) ^ 2) l = _
    rw [TopLevelSites.plaquetteDefect_readAtLevel_eq hp, TopLevelSites.toTorusSite_torusSiteInFrame hp]
  calc ∑ p ∈ plaquettesIn X, min (curvature W p.1 p.2.1 p.2.2 ^ 2) l
      = ∑ p ∈ plaquettesIn X, min (plaquetteDefect (readAtLevel F j W) (m p) ^ 2) l :=
        Finset.sum_congr rfl fun p _ => (hval p).symm
    _ = ∑ q ∈ (plaquettesIn X).image m, min (plaquetteDefect (readAtLevel F j W) q ^ 2) l :=
        (Finset.sum_image (f := fun q => min (plaquetteDefect (readAtLevel F j W) q ^ 2) l)
          fun a _ b _ h => hinj h).symm
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => le_min (sq_nonneg _) hl
        intro q hq
        obtain ⟨⟨x, μ, ν⟩, hp', rfl⟩ := Finset.mem_image.mp hq
        have hmem := mem_plaquettesIn_iff_forall_vertex.mp hp'
        have c1 : x ∈ X := hmem.2 _ (by simp [plaquetteVertices])
        have c2 : x + TorusFields.unitStep N μ ∈ X := hmem.2 _ (by simp [plaquetteVertices])
        have c3 : x + TorusFields.unitStep N ν ∈ X := hmem.2 _ (by simp [plaquetteVertices])
        have c4 : x + TorusFields.unitStep N μ + TorusFields.unitStep N ν ∈ X := hmem.2 _ (by simp [plaquetteVertices])
        simp only [LumpContours.cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, hm]
        refine ⟨hY _ c1, hmem.1, ?_⟩
        intro z hz
        simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton, hunit,
          ← TopLevelSites.torusSiteInFrame_add hp] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact hY _ c1
        · exact hY _ c2
        · exact hY _ c3
        · exact hY _ c4
variable {n : ℕ} [NeZero n]
private theorem coercive_floor_actionAtLevel (hC : LumpContours.ActionAtLevelIsCutAction) {cK a : ℝ} {L : ℕ} [NeZero L]
    (hco : RenormalizationStepParameters.CoercivityBound cK a L) (hcK : 0 ≤ cK) (ha : 0 ≤ a) (hL : Odd L) (t : ℕ) (hn : 64 ≤ n)
    (S : Finset (TorusSite n)) (W : TorusField n) :
    cK * ∑ p ∈ plaquettesIn S, min (curvature W p.1 p.2.1 p.2.2 ^ 2) ((L : ℝ) ^ (-4 : ℤ)) ≤
      actionAtLevel a L (t + 1) S W := by
  have hp : ∀ i, (torusFrame L t n).period (torusFrame L t n).top i = n := fun i => TorusFrame.period_torusFrame i
  have h1 := (hco (torusFrame L t n) rfl (Or.inr fun _ => hn) (torusFrame L t n).top le_rfl).2
    (cellsOfSites (torusFrame L t n) S) (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
  have h2 := (hC a ha L hL n (torusFrame L t n) rfl (fun _ => rfl)).1 S W
  rw [h2] at h1
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hcK) h1
  refine sum_min_curvature_le_read hp S W (by positivity) _ fun x hx => ?_
  refine (mem_cellsOfSites_iff hp _ _).mpr ?_
  rwa [toTorusSite_torusSiteInFrame hp]
private theorem two_mul_coercivity_le_one (hM : ActionSmoothAlongMoves) (hC : LumpContours.ActionAtLevelIsCutAction)
    {cK a δ lam ρ σA cg : ℝ} {L : ℕ} [NeZero L] {N : ℕ → ℝ} (hco : RenormalizationStepParameters.CoercivityBound cK a L) (hcK : 0 ≤ cK)
    (ha : 0 < a) (hL : Odd L) (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) : 2 * cK ≤ 1 := by
  classical
  set F : BlockFrame := torusFrame L 0 64 with hF
  have hLpos : 0 < L := hL.pos
  set m : ℕ := 64 * L with hm
  have : NeZero m := ⟨by simp [hm, hLpos.ne']⟩
  have hm64 : 64 ≤ m := by nlinarith
  have hp : ∀ i, F.period F.depth i = m := fun i => by
    rw [TopLevelSites.period_depth]
    rfl
  have hG : ∀ W : TorusField m, cK * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
      min (curvature W p.1 p.2.1 p.2.2 ^ 2) ((L : ℝ) ^ (-4 : ℤ)) ≤ actionAtLevel a L 0 Finset.univ W := by
    intro W
    have h1 := (hco F rfl (Or.inr fun _ => le_rfl) F.depth (Nat.le_succ _)).2
      (FrameTransfer.sitesOfTorus F F.depth (Finset.univ : Finset (TorusSite m))) (readAtLevel F F.depth W)
    have h2 := (hC a ha.le L hL 64 F rfl (fun _ => rfl)).2 (Finset.univ : Finset (TorusSite (64 * L))) W
    rw [h2] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hcK) h1
    refine sum_min_curvature_le_read hp Finset.univ W (by positivity) _ fun x _ => ?_
    exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
  obtain ⟨-, -, -, -, -, hσ, -, -, -⟩ := id hc
  obtain ⟨C, -, hA⟩ := hM a δ L lam ρ σA cg N ha hL hc
  have hreg : IsRegularRegion (Finset.univ : Finset (TorusSite m)) 1024 := fun z =>
    ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => Finset.mem_univ _⟩
  have h3 := (hA 0 m hm64 Finset.univ (trivialField m) hreg (isColdOn_trivialField _ hσ)).1
  have h0 : actionAtLevel a L 0 (Finset.univ : Finset (TorusSite m)) (trivialField m) = 0 :=
    wilsonAction_trivialField _
  set u : TorusBond m → imaginaryQuaternions := singleBondForm ((0 : TorusSite m), (0 : Fin 4)) imagI with hu
  have hf := flatHessian_ge_curl h3 h0 hcK (by positivity) _ hG u
  rw [flatHessian_wilson h3 _ (fun W => rfl) u] at hf
  set P : TorusPlaquette m := ((0 : TorusSite m), (0 : Fin 4), (1 : Fin 4)) with hP
  have hPmem : P ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)) :=
    mem_plaquettesIn_iff_forall_vertex.mpr ⟨by simp [hP], fun _ _ => Finset.mem_univ _⟩
  have hfact : Fact (1 < m) := ⟨by omega⟩
  have hne : TorusFields.unitStep m (1 : Fin 4) ≠ (0 : TorusSite m) := by
    intro e
    have := congrFun e 1
    simp [TorusFields.unitStep] at this
  have hcurl : lieFormCurl u P = imagI := by
    have a1 : u ((0 : TorusSite m), (0 : Fin 4)) = imagI := by simp [hu, singleBondForm]
    have a2 : u ((0 : TorusSite m) + TorusFields.unitStep m 0, (1 : Fin 4)) = 0 := by simp [hu, singleBondForm]
    have a3 : u ((0 : TorusSite m) + TorusFields.unitStep m 1, (0 : Fin 4)) = 0 := by simp [hu, singleBondForm, hne]
    have a4 : u ((0 : TorusSite m), (1 : Fin 4)) = 0 := by simp [hu, singleBondForm]
    simp only [lieFormCurl, hP, a1, a2, a3, a4]
    simp
  have hpos : 0 < ‖lieFormCurl u P‖ ^ 2 := by
    rw [hcurl]
    have : imagI ≠ 0 := by
      intro e
      have := congrArg (fun X : imaginaryQuaternions => (X : ℍ[ℝ]).imI) e
      simp at this
    positivity
  have hsum : 0 < ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), ‖lieFormCurl u p‖ ^ 2 :=
    lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun p => ‖lieFormCurl u p‖ ^ 2) (fun _ _ => by positivity) hPmem)
  nlinarith
end Floors
section Conclusion
variable {n : ℕ} [NeZero n]
private theorem lieFormCurl_latticeGrad (φ : TorusSite n → imaginaryQuaternions) (p : TorusPlaquette n) :
    lieFormCurl (latticeGrad φ) p = 0 := by
  simp only [lieFormCurl, latticeGrad]
  rw [add_right_comm p.1 (TorusFields.unitStep n p.2.2) (TorusFields.unitStep n p.2.1)]
  abel
private theorem hessian_properties {G : TorusField n → ℝ} {S : Finset (TorusSite n)} {cK CQ : ℝ}
    (h3 : ContDiffThreeAt G (trivialField n)) (h0 : G (trivialField n) = 0) (hpos : ∀ W, 0 ≤ G W)
    (hg : ∀ (g : UnitQuaternion) (u : TorusBond n → imaginaryQuaternions), ∀ᶠ τ in 𝓝 (0 : ℝ),
      G (TorusFields.gaugeTransform (fun _ => g) (exponentialField (τ • u))) = G (exponentialField (τ • u)))
    (hfloor : ∀ v, 2 * cK * curlNormSq S v ≤ hessianPairing G v v)
    (hceil : ∀ v, hessianPairing G v v ≤ CQ * curlNormSq S v) (hcK : 0 ≤ cK) :
    (∀ u v : TorusBond n → imaginaryQuaternions,
      ∑ b : TorusBond n, ∑ b' : TorusBond n, mixedDeriv G (trivialField n) ![b, b'] ![u b, v b'] =
        hessianPairing G u v) ∧
    (∀ u v, hessianPairing G u v = hessianPairing G v u) ∧
    (∀ (c : ℝ) (u u' v : TorusBond n → imaginaryQuaternions),
      hessianPairing G (c • u + u') v = c * hessianPairing G u v + hessianPairing G u' v) ∧
    (∀ (φ : TorusSite n → imaginaryQuaternions) (v : TorusBond n → imaginaryQuaternions),
      hessianPairing G (latticeGrad φ) v = 0) ∧
    ∀ u v : TorusBond n → imaginaryQuaternions, hessianPairing G u v = ∑ e : Fin 3, ∑ b : TorusBond n,
      ∑ b' : TorusBond n, mixedDeriv G (trivialField n) ![b, b'] ![imaginaryUnitI, imaginaryUnitI] *
        imaginaryComponent e (u b) * imaginaryComponent e (v b') := by
  have hsum : ∀ u v : TorusBond n → imaginaryQuaternions,
      ∑ b : TorusBond n, ∑ b' : TorusBond n, mixedDeriv G (trivialField n) ![b, b'] ![u b, v b'] =
        hessianPairing G u v := fun u v => sum_mixedDeriv_eq_flatHessian h3 u v
  refine ⟨hsum, hessianPairing_symm h3, ?_, ?_, ?_⟩
  · intro c u u' v
    rw [hessianPairing_add_left, hessianPairing_smul_left]
  · intro φ v
    have hnn : ∀ a, 0 ≤ hessianPairing G a a := fun a => by
      have h1 := hfloor a
      have h2 : 0 ≤ curlNormSq S a := Finset.sum_nonneg fun p _ => by positivity
      have h4 : 0 ≤ 2 * cK * curlNormSq S a := by positivity
      linarith
    have hz : hessianPairing G (latticeGrad φ) (latticeGrad φ) = 0 := by
      refine le_antisymm ?_ (hnn _)
      have h1 := hceil (latticeGrad φ)
      have h2 : curlNormSq S (latticeGrad φ) = 0 :=
        Finset.sum_eq_zero fun p _ => by rw [lieFormCurl_latticeGrad]; simp
      rwa [h2, mul_zero] at h1
    exact bilin_eq_zero_of_null (hessianPairing G) (hessianPairing_add_left G)
      (fun a b c => hessianPairing_add_right G a b c) (hessianPairing_smul_left G) (hessianPairing_smul_right G)
      (hessianPairing_symm h3) hnn hz v
  · intro u v
    rw [← hsum]
    have hinv := hessianPairing_adjoint h3 h0 hpos hg
    have e1 : ∀ b b' : TorusBond n, mixedDeriv G (trivialField n) ![b, b'] ![u b, v b'] = ∑ e : Fin 3,
        mixedDeriv G (trivialField n) ![b, b'] ![imaginaryUnitI, imaginaryUnitI] * imaginaryComponent e (u b) *
          imaginaryComponent e (v b') := by
      intro b b'
      rw [← hessianPairing_singleBondForm h3, hessianPairing_singleBondForm_eq_sum h3 hinv,
        hessianPairing_singleBondForm h3]
      rfl
    simp only [e1]
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm]
    exact Finset.sum_comm
end Conclusion
theorem cubeHessianStatement_holds (hL : AxialGauge.axialGaugeCurlBoundStatement) (hM : ActionSmoothAlongMoves)
    (hS : SharesSumToAction) (hC : LumpContours.ActionAtLevelIsCutAction) : cubeHessianStatement := by
  intro Tb hT
  have ha0 : 0 < Tb.coupling := by linarith [hT.a_ge]
  have hc := hT.chain
  obtain ⟨hδ, hδ8, hlam, hρ, hρ1, hσ, hcg, hN, hch⟩ := id hc
  obtain ⟨CM, hCM, hAM⟩ := hM Tb.coupling Tb.δ₁ Tb.side Tb.lam Tb.ρA Tb.σA Tb.cg Tb.N ha0 hT.L_odd hc
  have hcK0 := hT.cK_pos.le
  have hhalf := two_mul_coercivity_le_one hM hC hT.coercive hcK0 ha0 hT.L_odd hc
  have hCc : 0 ≤ hessianCeiling (Tb.N 2) Tb.δ₁ := by
    have h1 := expSumBound_nonneg (β := Tb.δ₁ / 2) (by positivity)
    have h2 := expSumBound_nonneg (β := Tb.δ₁ / 8) (by positivity)
    have h3 := hN 2
    unfold hessianCeiling
    positivity
  refine ⟨1 + hessianCeiling (Tb.N 2) Tb.δ₁, 1024, by linarith, ?_⟩
  intro k n _ o R hR hn
  have h64 : 64 ≤ n := by omega
  have hreg := supBall_isRegularRegion hR hn o
  set S := supBall o (2 * R) with hSdef
  have hcold := isColdOn_trivialField S hσ
  have h3 : ContDiffThreeAt (actionAtLevel Tb.coupling Tb.side k S) (trivialField n) :=
    (hAM k n h64 S (trivialField n) hreg hcold).1
  have hcurlnn : ∀ v : TorusBond n → imaginaryQuaternions, 0 ≤ curlNormSq S v :=
    fun v => Finset.sum_nonneg fun p _ => by positivity
  have key : actionAtLevel Tb.coupling Tb.side k S (trivialField n) = 0 ∧
      (∀ W, 0 ≤ actionAtLevel Tb.coupling Tb.side k S W) ∧
      (∀ (g : UnitQuaternion) (u : TorusBond n → imaginaryQuaternions), ∀ᶠ τ in 𝓝 (0 : ℝ),
        actionAtLevel Tb.coupling Tb.side k S (TorusFields.gaugeTransform (fun _ => g) (exponentialField (τ • u))) =
          actionAtLevel Tb.coupling Tb.side k S (exponentialField (τ • u))) ∧
      (∀ v, 2 * Tb.coercivity * curlNormSq S v ≤ hessianPairing (actionAtLevel Tb.coupling Tb.side k S) v v) ∧
      (∀ v, hessianPairing (actionAtLevel Tb.coupling Tb.side k S) v v ≤
        (1 + hessianCeiling (Tb.N 2) Tb.δ₁) * curlNormSq S v) := by
    cases k with
    | zero =>
      have hW : ∀ v, hessianPairing (actionAtLevel Tb.coupling Tb.side 0 S) v v = curlNormSq S v := fun v =>
        flatHessian_wilson h3 (plaquettesIn S) (fun W => rfl) v
      refine ⟨wilsonAction_trivialField S, fun W => Finset.sum_nonneg fun p _ => plaquetteEnergy_nonneg _ _ _ _,
        fun g u => Eventually.of_forall fun τ => wilsonAction_gaugeTransform S _ _, fun v => ?_, fun v => ?_⟩
      · rw [hW]
        have := hcurlnn v
        nlinarith
      · rw [hW]
        have := hcurlnn v
        nlinarith
    | succ t =>
      have hsd := flatShareBounds_succ (n := n) hT.L_odd hc t h64 hreg
      have hsum : ∀ W, actionAtLevel Tb.coupling Tb.side (t + 1) S W =
          ∑ y, levelShare Tb.coupling Tb.side (t + 1) S y W := fun W =>
        (hS Tb.coupling Tb.side t n S W ha0.le hT.L_odd.pos (by omega)).symm
      have h0 : actionAtLevel Tb.coupling Tb.side (t + 1) S (trivialField n) = 0 := by
        rw [hsum]
        exact Finset.sum_eq_zero fun y _ => hsd.trivial_eq_zero hσ y
      have hfl := coercive_floor_actionAtLevel (n := n) hC hT.coercive hcK0 ha0.le hT.L_odd t h64 S
      have hL4 : (0 : ℝ) < (Tb.side : ℝ) ^ (-4 : ℤ) := by
        have : 0 < Tb.side := hT.L_odd.pos
        positivity
      refine ⟨h0, fun W => ?_, fun g u => ?_, fun v => ?_, fun v => ?_⟩
      · refine le_trans ?_ (hfl W)
        exact mul_nonneg hcK0 (Finset.sum_nonneg fun p _ => le_min (sq_nonneg _) hL4.le)
      · filter_upwards [eventually_isColdOn_line S u hσ] with τ hτ
        exact actionAtLevel_gaugeTransform hS ha0.le hT.L_odd hc t h64 hreg hτ _
      · exact flatHessian_ge_curl h3 h0 hcK0 hL4 (plaquettesIn S) hfl v
      · have h1 : hessianPairing (actionAtLevel Tb.coupling Tb.side (t + 1) S) v v = _ :=
          flatHessian_sum hsd hσ h3 hsum v
        rw [h1]
        have h2 := sum_flatHessian_le hL (by omega) hn hsd hσ (by have := hN 0; positivity) (hN 2).le hδ v
        have := hcurlnn v
        have e : curlNormSq S v = ∑ p ∈ plaquettesIn S, ‖lieFormCurl v p‖ ^ 2 := rfl
        rw [e] at this ⊢
        nlinarith
  obtain ⟨h0, hpos, hg, hfl, hce⟩ := key
  obtain ⟨f1, f2, f3, f4, f5⟩ := hessian_properties h3 h0 hpos hg hfl hce hcK0
  have hcut : ∀ u v : TorusBond n → imaginaryQuaternions,
      hessianForm Tb.coupling Tb.side k S u v = hessianPairing (actionAtLevel Tb.coupling Tb.side k S) u v := f1
  refine ⟨h0, fun j c X => (h3 j c X).of_le (by norm_num), fun u v => ?_, fun c u u' v => ?_, fun v => ⟨?_, ?_⟩,
    fun φ v => ?_, fun u v => ?_⟩
  · rw [hcut, hcut]
    exact f2 u v
  · simp only [hcut]
    exact f3 c u u' v
  · rw [hcut]
    exact hfl v
  · rw [hcut]
    exact hce v
  · rw [hcut]
    exact f4 φ v
  · rw [hcut]
    exact f5 u v
end YangMills.Construction.BoxGaussian
end
