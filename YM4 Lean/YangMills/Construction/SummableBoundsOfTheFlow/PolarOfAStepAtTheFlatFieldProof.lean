import YangMills.Construction.ClusterExpansionOfAStep.AdmissionEqualInBoxes
import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.FlatResponsesAreScalarProof
import YangMills.Construction.ColdStepAtMirrorFrames.TreeResponseOfTheLeastCoordinatesProof
import YangMills.Construction.LawByMomentsOfTheFlow.MaxwellFormOfTheBareLevelProof
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheMaxwellFormProof
import YangMills.Construction.SummableBoundsOfTheFlow.PolarOfAStepAtTheFlatField
import YangMills.Construction.SummableBoundsOfTheFlow.TheSharesAtDrawnParametersProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open BlockAverages LatticePaths FrameTransfer ColdStepAtMirrorFrames TorusFields TorusLumps WeightedResponses
  FrameTorusAction TwoLevelMixtures
namespace StepPolarity
section Calculus
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
private theorem iteratedFDeriv_two_comp_clm {Φ : E → ℝ} (h : ContDiffAt ℝ 2 Φ 0) (ι : G →L[ℝ] E) (m : Fin 2 → G) :
    iteratedFDeriv ℝ 2 (fun s => Φ (ι s)) 0 m = fderiv ℝ (fderiv ℝ Φ) 0 (ι (m 0)) (ι (m 1)) := by apply _root_.YangMills.SharedProofs.p5330 <;> assumption
private theorem taylor_two_remainder {Φ : E → ℝ} (h : ContDiffAt ℝ 2 Φ 0) (h0 : Φ 0 = 0) (h1 : fderiv ℝ Φ 0 = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 (0 : E), |2 * Φ y - fderiv ℝ (fderiv ℝ Φ) 0 y y| ≤ ε * ‖y‖ ^ 2 := by
  set H := fderiv ℝ (fderiv ℝ Φ) 0 with hH
  have hd : HasFDerivAt (fderiv ℝ Φ) H 0 :=
    ((h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hlo := hd.isLittleO.def (half_pos hε)
  have hev : ∀ᶠ σ in 𝓝 (0 : E), DifferentiableAt ℝ Φ σ :=
    (h.eventually (by simp)).mono fun σ hσ => hσ.differentiableAt (by norm_num)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hlo.and hev)
  refine Metric.eventually_nhds_iff_ball.2 ⟨δ, hδ, fun y hy => ?_⟩
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, s • y ∈ Metric.ball (0 : E) δ := by
    intro s hs
    rw [mem_ball_zero_iff] at hy ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [hs.2, norm_nonneg y]
  set k : ℝ → ℝ := fun s => Φ (s • y) - s ^ 2 / 2 * H y y with hk
  set k' : ℝ → ℝ := fun s => fderiv ℝ Φ (s • y) y - s * H y y with hk'
  have hkd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt k (k' s) (Set.Icc 0 1) s := by
    intro s hs
    have h1' : HasFDerivAt Φ (fderiv ℝ Φ (s • y)) ((fun r : ℝ => r • y) s) := (hball _ (hseg s hs)).2.hasFDerivAt
    have h2 : HasDerivAt (fun r : ℝ => r • y) y s := by
      simpa using (hasDerivAt_id s).smul_const y
    have h3 : HasDerivAt (fun r : ℝ => Φ (r • y)) (fderiv ℝ Φ (s • y) y) s := h1'.comp_hasDerivAt s h2
    have h4 : HasDerivAt (fun r : ℝ => r ^ 2 / 2 * H y y) (s * H y y) s := by
      have h5 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
      have h6 : HasDerivAt (fun r : ℝ => r ^ 2 / 2 * H y y) (2 * s / 2 * H y y) s :=
        (h5.div_const 2).mul_const (H y y)
      have e6 : 2 * s / 2 * H y y = s * H y y := by ring
      rwa [e6] at h6
    exact (h3.sub h4).hasDerivWithinAt
  have hb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖k' s‖ ≤ ε / 2 * ‖y‖ ^ 2 := by
    intro s hs
    have h2 := (hball _ (hseg s hs)).1
    simp only [sub_zero, h1, map_smul] at h2
    have e : k' s = (fderiv ℝ Φ (s • y) - s • H y) y := by
      simp [hk']
    rw [e]
    refine ((fderiv ℝ Φ (s • y) - s • H y).le_opNorm y).trans ?_
    have h3 : ‖s • y‖ ≤ ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      nlinarith [hs.2, norm_nonneg y]
    have h4 : ‖fderiv ℝ Φ (s • y) - s • H y‖ ≤ ε / 2 * ‖y‖ := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left h3 (half_pos hε).le)
      simpa using h2
    calc ‖fderiv ℝ Φ (s • y) - s • H y‖ * ‖y‖ ≤ ε / 2 * ‖y‖ * ‖y‖ :=
          mul_le_mul_of_nonneg_right h4 (norm_nonneg y)
      _ = ε / 2 * ‖y‖ ^ 2 := by ring
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hkd hb (convex_Icc 0 1)
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  have e0 : k 0 = 0 := by simp [hk, h0]
  have e1 : k 1 = Φ y - H y y / 2 := by
    simp only [hk, one_smul]
    ring
  rw [e0, e1] at hmv
  simp only [sub_zero, norm_one, mul_one, Real.norm_eq_abs] at hmv
  have e2 : 2 * Φ y - H y y = 2 * (Φ y - H y y / 2) := by ring
  rw [e2, abs_mul]
  simp only [abs_two]
  linarith
private theorem tendsto_two_mul_div_sq {Φ : E → ℝ} (h : ContDiffAt ℝ 2 Φ 0) (h0 : Φ 0 = 0) (h1 : fderiv ℝ Φ 0 = 0)
    {v : ℝ → E} {d : E} (hv0 : v 0 = 0) (hv : HasDerivAt v d 0) :
    Tendsto (fun τ : ℝ => 2 * Φ (v τ) / τ ^ 2) (𝓝[>] 0) (𝓝 (fderiv ℝ (fderiv ℝ Φ) 0 d d)) := by
  set H := fderiv ℝ (fderiv ℝ Φ) 0 with hH
  have hw : Tendsto (fun τ : ℝ => τ⁻¹ • v τ) (𝓝[>] 0) (𝓝 d) := by
    have h2 := hasDerivAt_iff_tendsto_slope_zero.1 hv
    have h3 : Tendsto (fun t : ℝ => t⁻¹ • (v (0 + t) - v 0)) (𝓝[>] 0) (𝓝 d) :=
      h2.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
    refine h3.congr fun τ => ?_
    simp [hv0]
  have hvz : Tendsto v (𝓝[>] 0) (𝓝 0) := by
    have := hv.continuousAt.tendsto
    rw [hv0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hHw : Tendsto (fun τ : ℝ => H (τ⁻¹ • v τ) (τ⁻¹ • v τ)) (𝓝[>] 0) (𝓝 (H d d)) := by
    have hc : Continuous fun p : E × E => H p.1 p.2 := by fun_prop
    exact (hc.tendsto (d, d)).comp (hw.prodMk_nhds hw)
  have hrest : Tendsto (fun τ : ℝ => 2 * Φ (v τ) / τ ^ 2 - H (τ⁻¹ • v τ) (τ⁻¹ • v τ)) (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set M := ‖d‖ + 1 with hM
    have hMp : 0 < M := by positivity
    have hbd : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ‖τ⁻¹ • v τ‖ < M :=
      (hw.norm).eventually (gt_mem_nhds (by rw [hM]; linarith))
    have hε' : 0 < ε / (2 * M ^ 2) := by positivity
    have ht := hvz.eventually (taylor_two_remainder h h0 h1 hε')
    filter_upwards [hbd, ht, self_mem_nhdsWithin] with τ h1' h2' h3'
    have hτ : (0 : ℝ) < τ := h3'
    have e : 2 * Φ (v τ) / τ ^ 2 - H (τ⁻¹ • v τ) (τ⁻¹ • v τ) = (2 * Φ (v τ) - H (v τ) (v τ)) / τ ^ 2 := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      field_simp
    have en : ‖v τ‖ ^ 2 / τ ^ 2 = ‖τ⁻¹ • v τ‖ ^ 2 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hτ]
      field_simp
    rw [Real.dist_eq, sub_zero, e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < τ ^ 2)]
    calc |2 * Φ (v τ) - H (v τ) (v τ)| / τ ^ 2 ≤ ε / (2 * M ^ 2) * ‖v τ‖ ^ 2 / τ ^ 2 := by
          gcongr
      _ = ε / (2 * M ^ 2) * ‖τ⁻¹ • v τ‖ ^ 2 := by rw [mul_div_assoc, en]
      _ ≤ ε / (2 * M ^ 2) * M ^ 2 := by
          gcongr
      _ < ε := by
          have : ε / (2 * M ^ 2) * M ^ 2 = ε / 2 := by field_simp
          rw [this]
          linarith
  have := hrest.add hHw
  simp only [zero_add, sub_add_cancel] at this
  exact this
private theorem eq_zero_of_quadratic_nonneg {P R : ℝ} (hq : ∀ ε : ℝ, 0 ≤ 2 * ε * P + ε ^ 2 * R) : P = 0 := by apply _root_.YangMills.SharedProofs.p10126 <;> assumption
private theorem sum_basis_bilinear {B : Type*} [Fintype B] [DecidableEq B]
    (D : (B → ℝ) →L[ℝ] (B → ℝ) →L[ℝ] ℝ) (A A' : B → ℝ) :
    ∑ b, ∑ b', A b * D (Pi.single b 1) (Pi.single b' 1) * A' b' = D A A' := by apply _root_.YangMills.SharedProofs.p21054 <;> assumption
end Calculus
section OneColour
private theorem expUnit_zero_eq : expUnit 0 = 1 := Subtype.ext (by simp [expUnit])
private theorem expUnit_generator_add (s t : ℝ) :
    expUnit ((s + t) • unitGenerator) = expUnit (s • unitGenerator) * expUnit (t • unitGenerator) := by apply _root_.YangMills.SharedProofs.p21518 <;> assumption
private theorem inv_expUnit_generator (s : ℝ) :
    (expUnit (s • unitGenerator))⁻¹ = expUnit ((-s) • unitGenerator) := by apply _root_.YangMills.SharedProofs.p1618 <;> assumption
private theorem norm_unitGenerator : ‖(unitGenerator : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SingleColourFields.norm_unitGenerator <;> assumption
private theorem re_expUnit_generator (s : ℝ) :
    ((expUnit (s • unitGenerator) : UnitQuaternion) : ℍ[ℝ]).re = Real.cos s := by apply _root_.YangMills.SharedProofs.p36152 <;> assumption
variable {n : ℕ}
private def abelianTorusField (σ : TorusBond n → ℝ) : TorusField n :=
  fun x i => expUnit (σ (x, i) • unitGenerator)
private theorem holonomy_abelianTorusField (σ : TorusBond n → ℝ) (x : TorusSite n) (μ ν : Fin 4) :
    holonomy (abelianTorusField σ) x μ ν = expUnit (curl σ (x, μ, ν) • unitGenerator) := by
  simp only [holonomy, abelianTorusField, curl]
  rw [inv_expUnit_generator, inv_expUnit_generator, ← expUnit_generator_add, ← expUnit_generator_add,
    ← expUnit_generator_add]
  congr 2
private theorem plaquetteEnergy_abelianTorusField (σ : TorusBond n → ℝ) (x : TorusSite n) (μ ν : Fin 4) :
    plaquetteEnergy (abelianTorusField σ) x μ ν = 1 - Real.cos (curl σ (x, μ, ν)) := by
  rw [plaquetteEnergy, holonomy_abelianTorusField, re_expUnit_generator]
end OneColour
section MaxwellForm
variable {n : ℕ} [NeZero n]
private theorem abelianTorusField_zero : abelianTorusField (0 : TorusBond n → ℝ) = trivialField n := by
  funext x i
  simp [abelianTorusField, trivialField, expUnit_zero_eq]
private theorem maxwellKernel_eq_fderiv (a : ℝ) (L u : ℕ)
    (hC : ContDiffAt ℝ 2 (fun σ : TorusBond n → ℝ => actionAtLevel a L u Finset.univ (abelianTorusField σ)) 0)
    (b b' : TorusBond n) :
    maxwellKernel a L u b b' = fderiv ℝ (fderiv ℝ fun σ : TorusBond n → ℝ =>
      actionAtLevel a L u Finset.univ (abelianTorusField σ)) 0 (Pi.single b 1) (Pi.single b' 1) := by
  let ι : (Fin 2 → ℝ) →L[ℝ] (TorusBond n → ℝ) :=
    (ContinuousLinearMap.proj 0).smulRight (Pi.single b 1) +
      (ContinuousLinearMap.proj 1).smulRight (Pi.single b' 1)
  have e1 : ∀ (d : TorusBond n) (x : TorusSite n) (i : Fin 4) (s : ℝ),
      (if d = (x, i) then s • unitGenerator else (0 : imaginaryQuaternions)) =
      (s * (Pi.single d (1 : ℝ) : TorusBond n → ℝ) (x, i)) • unitGenerator := by
    intro d x i s
    by_cases h : d = (x, i)
    · rw [if_pos h, h]
      simp
    · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h)]
      simp
  have hfun : (fun σ : Fin 2 → ℝ => actionAtLevel a L u Finset.univ
      (perturb ![b, b'] ![unitGenerator, unitGenerator] σ (trivialField n))) =
      fun σ => (fun σ : TorusBond n → ℝ => actionAtLevel a L u Finset.univ (abelianTorusField σ)) (ι σ) := by
    funext σ
    show actionAtLevel a L u Finset.univ _ = actionAtLevel a L u Finset.univ _
    congr 1
    funext x i
    have hs : (∑ l : Fin 2, if (![b, b'] : Fin 2 → TorusBond n) l = (x, i) then
        σ l • (![unitGenerator, unitGenerator] : Fin 2 → imaginaryQuaternions) l
        else 0) = (ι σ (x, i)) • unitGenerator := by
      rw [Fin.sum_univ_two]
      show (if b = (x, i) then σ 0 • unitGenerator else (0 : imaginaryQuaternions)) +
        (if b' = (x, i) then σ 1 • unitGenerator else (0 : imaginaryQuaternions)) = _
      rw [e1, e1, ← add_smul]
      simp [ι]
    show expUnit _ * 1 = expUnit _
    rw [mul_one, hs]
  unfold maxwellKernel mixedDeriv
  rw [hfun, iteratedFDeriv_two_comp_clm hC ι]
  simp [ι]
end MaxwellForm
section FirstParts
variable {n : ℕ}
private theorem contDiffAt_readAtLevel_of_analytic [NeZero n] {Eo : Type} [NormedAddCommGroup Eo]
    [NormedSpace ℝ Eo] [CompleteSpace Eo] {F : BlockFrame} (hm : ∀ k, F.period F.top k = n)
    (Gf : F.GaugeField F.top → Eo) (h : IsBondAnalyticAt Gf (flatField F F.top)) :
    ContDiffAt ℝ 2 (fun σ : TorusBond n → ℝ => Gf (readAtLevel F F.top (abelianTorusField σ))) 0 := by
  classical
  let e : Fin (Fintype.card (TorusBond n)) ≃ TorusBond n := (Fintype.equivFin (TorusBond n)).symm
  let c : Fin (Fintype.card (TorusBond n)) → F.Site F.top × Fin 4 :=
    fun l => (torusToFrame F F.top (e l).1, (e l).2)
  let Xs : Fin (Fintype.card (TorusBond n)) → imaginaryQuaternions := fun _ => unitGenerator
  have hturn : ∀ σ' : Fin (Fintype.card (TorusBond n)) → ℝ,
      rotatedField (BlockAverages.bondSpread c Xs σ') (flatField F F.top) =
        readAtLevel F F.top (abelianTorusField fun b => σ' (e.symm b)) := by
    intro σ'
    funext y i
    have hs : BlockAverages.bondSpread c Xs σ' y i = σ' (e.symm (frameToTorus n y, i)) • unitGenerator := by
      unfold BlockAverages.bondSpread
      rw [Finset.sum_eq_single (e.symm (frameToTorus n y, i))]
      · rw [if_pos]
        show (torusToFrame F F.top (e (e.symm (frameToTorus n y, i))).1,
          (e (e.symm (frameToTorus n y, i))).2) = (y, i)
        rw [Equiv.apply_symm_apply]
        exact Prod.ext (torusToFrame_frameToTorus hm y) rfl
      · intro l _ hl
        rw [if_neg]
        intro hc
        apply hl
        have h1 : torusToFrame F F.top (e l).1 = y := congrArg Prod.fst hc
        have h2 : (e l).2 = i := congrArg Prod.snd hc
        rw [Equiv.eq_symm_apply]
        refine Prod.ext ?_ h2
        rw [← h1, frameToTorus_torusToFrame hm]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    show expUnit (BlockAverages.bondSpread c Xs σ' y i) * 1 =
      expUnit (σ' (e.symm (frameToTorus n y, i)) • unitGenerator)
    rw [hs, mul_one]
  have hA := h _ c Xs
  let P : (TorusBond n → ℝ) →L[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (e l)
  have hA' : ContDiffAt ℝ 2
      (fun σ' => Gf (rotatedField (BlockAverages.bondSpread c Xs σ') (flatField F F.top))) (P 0) := by
    rw [map_zero]
    exact hA.contDiffAt
  have hc := hA'.comp (0 : TorusBond n → ℝ) P.contDiff.contDiffAt
  refine hc.congr_of_eventuallyEq (Eventually.of_forall fun σ => ?_)
  show Gf (readAtLevel F F.top (abelianTorusField σ)) =
    Gf (rotatedField (BlockAverages.bondSpread c Xs (P σ)) (flatField F F.top))
  rw [hturn]
  have e2 : (fun b => P σ (e.symm b)) = σ := by
    funext b
    show σ (e (e.symm b)) = σ b
    rw [Equiv.apply_symm_apply]
  rw [e2]
end FirstParts
section Levels
variable {a : ℝ} {L : ℕ} {cn : ColdChainParameters}
private abbrev abelianAction (a : ℝ) (L u m : ℕ) [NeZero m] : (TorusBond m → ℝ) → ℝ :=
  fun σ => actionAtLevel a L u Finset.univ (abelianTorusField σ)
private theorem cellsOfSites_univ (L t m : ℕ) [NeZero m] :
    cellsOfSites (torusFrame L t m) (Finset.univ : Finset (TorusSite m)) = finiteCells (torusFrame L t m) := by apply _root_.YangMills.SharedProofs.p810 <;> assumption
private theorem abelianAction_succ (a : ℝ) (L t m : ℕ) [NeZero m] (σ : TorusBond m → ℝ) :
    abelianAction a L (t + 1) m σ = minimalAction a (finiteCells (torusFrame L t m)) (torusFrame L t m).top
      (readAtLevel (torusFrame L t m) (torusFrame L t m).top (abelianTorusField σ)) := by
  show minimalAction a (cellsOfSites (torusFrame L t m) Finset.univ) (t + 1) _ = _
  rw [cellsOfSites_univ]
  rfl
private theorem abelianAction_props (hLeast : minimalChainExistenceStatement) (hFlat : flatTopVanishingStatement)
    (ha : 0 ≤ a) (hL : Odd L) (hc : cn.Admissible a L) (u : ℕ) {m : ℕ} [NeZero m] (hm : 64 ≤ m) :
    ContDiffAt ℝ 2 (abelianAction a L u m) 0 ∧ abelianAction a L u m 0 = 0 ∧ ∀ σ, 0 ≤ abelianAction a L u m σ := by
  cases u with
  | zero =>
    have hact : ∀ σ : TorusBond m → ℝ, abelianAction a L 0 m σ =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), (1 - Real.cos (curl σ p)) := fun σ =>
      Finset.sum_congr rfl fun p _ => plaquetteEnergy_abelianTorusField σ p.1 p.2.1 p.2.2
    refine ⟨?_, ?_, fun σ => ?_⟩
    · have hcd : ContDiff ℝ 2 fun σ : TorusBond m → ℝ =>
          ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), (1 - Real.cos (curl σ p)) := by
        refine ContDiff.sum fun p _ => contDiff_const.sub (Real.contDiff_cos.comp ?_)
        unfold curl
        exact (((contDiff_apply ℝ ℝ _).add (contDiff_apply ℝ ℝ _)).sub (contDiff_apply ℝ ℝ _)).sub
          (contDiff_apply ℝ ℝ _)
      have e : abelianAction a L 0 m = _ := funext hact
      rw [e]
      exact hcd.contDiffAt
    · rw [hact]
      simp [curl]
    · rw [hact]
      exact Finset.sum_nonneg fun p _ => sub_nonneg.2 (Real.cos_le_one _)
  | succ t =>
    have hm' : ∀ k, (torusFrame L t m).period (torusFrame L t m).top k = m := TorusFrame.period_torusFrame
    have hodd : Odd (torusFrame L t m).blockSide := hL
    have hσ : 0 < cn.σA := hc.positivity.2.2.2.1
    have hcold : IsSmallCurvature cn.σA (uniformField (torusFrame L t m) (torusFrame L t m).top) :=
      isSmallCurvature_of_near_one _ (m := 0) (by linarith) (fun x i => by simp [uniformField])
    have hcl := hc.estimates (torusFrame L t m) cn.σA _ ⟨rfl, ⟨m, hm, fun _ => rfl⟩⟩ hσ le_rfl hcold
    refine ⟨?_, ?_, fun σ => ?_⟩
    · have e : abelianAction a L (t + 1) m = fun σ => minimalAction a (finiteCells (torusFrame L t m))
          (torusFrame L t m).top
          (readAtLevel (torusFrame L t m) (torusFrame L t m).top (abelianTorusField σ)) :=
        funext (abelianAction_succ a L t m)
      rw [e]
      exact contDiffAt_readAtLevel_of_analytic hm' _ hcl.cellShares.1
    · rw [abelianAction_succ, abelianTorusField_zero]
      exact (hFlat _ a _ ha hodd).2.1 _
    · rw [abelianAction_succ]
      exact (hLeast _ a _ ha).2.1 _ _
private theorem maxwellForm_eq_fderiv {u m : ℕ} [NeZero m] (hC : ContDiffAt ℝ 2 (abelianAction a L u m) 0)
    (A A' : TorusBond m → ℝ) :
    maxwellForm a L u A A' = fderiv ℝ (fderiv ℝ (abelianAction a L u m)) 0 A A' := by
  rw [← sum_basis_bilinear]
  unfold maxwellForm
  simp only [maxwellKernel_eq_fderiv a L u hC]
private theorem fderiv_abelianAction_zero {u m : ℕ} [NeZero m] (h0 : abelianAction a L u m 0 = 0)
    (hnn : ∀ σ, 0 ≤ abelianAction a L u m σ) :
    fderiv ℝ (abelianAction a L u m) 0 = 0 :=
  IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun σ => by rw [h0]; exact hnn σ)
end Levels
section Reads
private def torusForm {F : BlockFrame} {j : ℕ} (m : ℕ) (σ : TorusBond m → ℝ) : LevelForm F j :=
  fun x i => σ (toTorusSite m x, i)
private theorem restrictToTorus_torusForm {F : BlockFrame} {j m : ℕ} (hp : ∀ i, F.period j i = m)
    (σ : TorusBond m → ℝ) :
    restrictToTorus m (abelianField unitGenerator (torusForm (F := F) (j := j) m σ)) = abelianTorusField σ := by
  funext x i
  show expUnit (σ (toTorusSite m (siteOfTorusSite (F := F) j x), i) • unitGenerator) =
    expUnit (σ (x, i) • unitGenerator)
  rw [toTorusSite_siteOfTorusSite hp]
private theorem period_depth (L u n : ℕ) (i : Fin 4) : (torusFrame L u n).period u i = n * L := by apply _root_.YangMills.Construction.CongruentAdmission.torusFrame_period_depth <;> assumption
private theorem period_top_level (L u n : ℕ) (i : Fin 4) : (torusFrame L u n).period (u + 1) i = n := by apply _root_.YangMills.Construction.CongruentAdmission.torusFrame_period_succ <;> assumption
private theorem period_stepBlockFrame_zero (L n : ℕ) (i : Fin 4) : (stepBlockFrame L n).period 0 i = n * L := by apply _root_.YangMills.Construction.BlockOffsets.period_zero <;> assumption
private theorem period_stepBlockFrame_one (L n : ℕ) (i : Fin 4) : (stepBlockFrame L n).period 1 i = n := by apply _root_.YangMills.Construction.BlockOffsets.period_one <;> assumption
variable {a : ℝ} {L u n : ℕ} [NeZero n] [NeZero L]
private theorem minimalAction_torusForm (hL : Odd L) (σ : TorusBond (n * L) → ℝ) :
    minimalAction a (finiteCells (torusFrame L u n)) u
        (abelianField unitGenerator (torusForm (F := torusFrame L u n) (j := u) (n * L) σ)) =
      abelianAction a L u (n * L) σ := by
  refine (minimalAction_eq_actionAtLevel (F := torusFrame L u n) (j := u) (L := L) (n := n) (m := n * L) rfl hL
    (fun _ => rfl) (Nat.pos_of_ne_zero (NeZero.ne n)) rfl (period_depth L u n) rfl _).trans ?_
  rw [restrictToTorus_torusForm (period_depth L u n)]
private def fitTotal (L u n : ℕ) [NeZero n] (σ : TorusBond (n * L) → ℝ) (β : TorusBond n → ℝ) : ℝ :=
  ∑ c : TorusBond n, blockFit (abelianField unitGenerator (torusForm (F := torusFrame L u n) (j := u) (n * L) σ))
    (abelianField unitGenerator (torusForm (F := torusFrame L u n) (j := u + 1) n β))
    (torusToFrame (torusFrame L u n) (u + 1) c.1, c.2)
private theorem sum_innerBonds_top (hL : Odd L) (f : (torusFrame L u n).Site (u + 1) × Fin 4 → ℝ) :
    ∑ b ∈ innerBonds (finiteCells (torusFrame L u n)) (u + 1), f b =
      ∑ c : TorusBond n, f (torusToFrame (torusFrame L u n) (u + 1) c.1, c.2) := by
  have hs : ∀ i, 0 < (torusFrame L u n).extent i := fun _ => Nat.pos_of_ne_zero (NeZero.ne n)
  have hodd : Odd (torusFrame L u n).blockSide := hL
  have hb := sum_innerBonds_finiteCells (F := torusFrame L u n) hodd hs (k := u + 1) (Nat.le_refl _) f
  rw [hb, Fintype.sum_prod_type]
  refine Finset.sum_nbij' (frameToTorus n) (torusToFrame _ (u + 1)) (fun _ _ => Finset.mem_univ _)
    (fun z _ => mem_sitesOfCells_finiteCells (F := torusFrame L u n) hodd hs (k := u + 1) (Nat.le_refl _) _)
    ?_ ?_ ?_
  · intro y _
    exact torusToFrame_frameToTorus (period_top_level L u n) y
  · intro z _
    exact frameToTorus_torusToFrame (period_top_level L u n) z
  · intro y _
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [torusToFrame_frameToTorus (period_top_level L u n)]
private theorem blockEnergy_torusForm (hL : Odd L) (σ : TorusBond (n * L) → ℝ) (β : TorusBond n → ℝ) :
    blockEnergy a (finiteCells (torusFrame L u n)) u
        (abelianField unitGenerator (torusForm (F := torusFrame L u n) (j := u) (n * L) σ))
        (abelianField unitGenerator (torusForm (F := torusFrame L u n) (j := u + 1) n β)) =
      abelianAction a L u (n * L) σ + a * fitTotal L u n σ β := by
  unfold blockEnergy fitTotal
  rw [minimalAction_torusForm hL, sum_innerBonds_top hL]
private theorem abelianAction_succ_top (β : TorusBond n → ℝ) :
    abelianAction a L (u + 1) n β = minimalAction a (finiteCells (torusFrame L u n)) (u + 1)
      (abelianField unitGenerator (torusForm (F := torusFrame L u n) (j := u + 1) n β)) :=
  abelianAction_succ a L u n β
private theorem abelianAction_succ_le (hLeast : minimalChainExistenceStatement) (ha : 0 ≤ a) (hL : Odd L)
    (σ : TorusBond (n * L) → ℝ) (β : TorusBond n → ℝ) :
    abelianAction a L (u + 1) n β ≤ abelianAction a L u (n * L) σ + a * fitTotal L u n σ β := by
  obtain ⟨W, hW, hmin⟩ := (hLeast (torusFrame L u n) a (finiteCells _) ha).2.2.1 u
    (abelianField unitGenerator (torusForm (F := torusFrame L u n) (j := u + 1) n β))
  rw [abelianAction_succ_top, ← hW, ← blockEnergy_torusForm hL]
  exact hmin _
end Reads
section Limits
private theorem tendsto_cos_curve {A : ℝ → ℝ} {A' : ℝ} (hA : HasDerivAt A A' 0) (h0 : A 0 = 0) :
    Tendsto (fun τ => Real.cos (A τ)) (𝓝[>] 0) (𝓝 1) := by
  have h := (Real.continuous_cos.tendsto (A 0)).comp hA.continuousAt.tendsto
  rw [h0, Real.cos_zero] at h
  exact h.mono_left nhdsWithin_le_nhds
private theorem tendsto_sin_curve_div {A : ℝ → ℝ} {A' : ℝ} (hA : HasDerivAt A A' 0) (h0 : A 0 = 0) :
    Tendsto (fun τ => Real.sin (A τ) / τ) (𝓝[>] 0) (𝓝 A') := by
  have h2 : HasDerivAt (fun τ => Real.sin (A τ)) A' 0 := by simpa [h0] using hA.sin
  have h := hasDerivAt_iff_tendsto_slope_zero.1 h2
  have h3 : Tendsto (fun t : ℝ => t⁻¹ • (Real.sin (A (0 + t)) - Real.sin (A 0))) (𝓝[>] 0) (𝓝 A') :=
    h.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  refine h3.congr fun τ => ?_
  simp [h0, div_eq_inv_mul]
variable {F : BlockFrame} {m : ℕ} [NeZero m]
private theorem hasDerivAt_pathSum {j : ℕ} {s : ℝ → TorusBond m → ℝ} {d : TorusBond m → ℝ} (hs : HasDerivAt s d 0)
    (x : F.Site j) (l : List PathStep) :
    HasDerivAt (fun τ => pathSum (torusForm (F := F) (j := j) m (s τ)) x l)
      (pathSum (torusForm (F := F) (j := j) m d) x l) 0 := by
  have hb : ∀ b, HasDerivAt (fun τ => s τ b) (d b) 0 := hasDerivAt_pi.1 hs
  induction l generalizing x with
  | nil => simpa [pathSum] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  | cons st r ih =>
    simp only [pathSum]
    refine HasDerivAt.add ?_ (ih _)
    by_cases h : st.2 = true
    · simp only [h, if_true]
      exact hb _
    · simp only [h, Bool.false_eq_true, if_false]
      exact (hb _).neg
private theorem pathSum_zero {j : ℕ} (x : F.Site j) (l : List PathStep) :
    pathSum (torusForm (F := F) (j := j) m (0 : TorusBond m → ℝ)) x l = 0 := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih => simp [pathSum, ih, torusForm]
private theorem tendsto_averages_curve (hL : Odd F.blockSide) {j : ℕ} {s : ℝ → TorusBond m → ℝ}
    {d : TorusBond m → ℝ} (hs0 : s 0 = 0)
    (hs : HasDerivAt s d 0) (b : ℝ) (c : F.Site (j + 1) × Fin 4) :
    Tendsto (fun τ : ℝ => cosineAverage (torusForm (F := F) (j := j) m (s τ)) (τ * b) c) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun τ : ℝ => sineAverage (torusForm (F := F) (j := j) m (s τ)) (τ * b) c / τ) (𝓝[>] 0)
        (𝓝 (ColdStepAtMirrorFrames.contourAverage (torusForm (F := F) (j := j) m d) c.1 c.2 - b)) := by
  have hL0 : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hL.pos.ne'
  have hcard : (1 / (24 * (F.blockSide : ℝ) ^ 4)) *
      ∑ _h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ) = 1 := by
    simp only [Finset.sum_const, card_perm_fin_four, card_centredCube hL, nsmul_eq_mul]
    push_cast
    field_simp
  have hA : ∀ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)),
      HasDerivAt (fun τ : ℝ => pathSum (torusForm (F := F) (j := j) m (s τ)) (refineSite c.1)
          (bondContour F.blockSide h π c.2) - τ * b)
        (pathSum (torusForm (F := F) (j := j) m d) (refineSite c.1) (bondContour F.blockSide h π c.2) - b) 0 := by
    intro h π
    have h2 : HasDerivAt (fun τ : ℝ => τ * b) b 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const b
    exact (hasDerivAt_pathSum hs _ _).sub h2
  have hA0 : ∀ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)),
      pathSum (torusForm (F := F) (j := j) m (s 0)) (refineSite c.1) (bondContour F.blockSide h π c.2) - 0 * b = 0 := by
    intro h π
    rw [hs0, pathSum_zero]
    simp
  constructor
  · have h1 : Tendsto (fun τ : ℝ => (1 / (24 * (F.blockSide : ℝ) ^ 4)) *
        ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        Real.cos (pathSum (torusForm (F := F) (j := j) m (s τ)) (refineSite c.1)
          (bondContour F.blockSide h π c.2) - τ * b)) (𝓝[>] 0)
        (𝓝 ((1 / (24 * (F.blockSide : ℝ) ^ 4)) *
          ∑ _h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ))) :=
      Tendsto.const_mul _ (tendsto_finset_sum _ fun h _ => tendsto_finset_sum _ fun π _ =>
        tendsto_cos_curve (hA h π) (hA0 h π))
    rw [hcard] at h1
    exact h1
  · have h1 : Tendsto (fun τ : ℝ => (1 / (24 * (F.blockSide : ℝ) ^ 4)) *
        ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        (Real.sin (pathSum (torusForm (F := F) (j := j) m (s τ)) (refineSite c.1)
          (bondContour F.blockSide h π c.2) - τ * b) / τ)) (𝓝[>] 0)
        (𝓝 ((1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
          (pathSum (torusForm (F := F) (j := j) m d) (refineSite c.1) (bondContour F.blockSide h π c.2) - b))) :=
      Tendsto.const_mul _ (tendsto_finset_sum _ fun h _ => tendsto_finset_sum _ fun π _ =>
        tendsto_sin_curve_div (hA h π) (hA0 h π))
    have e : (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        (pathSum (torusForm (F := F) (j := j) m d) (refineSite c.1) (bondContour F.blockSide h π c.2) - b) =
        ColdStepAtMirrorFrames.contourAverage (torusForm (F := F) (j := j) m d) c.1 c.2 - b := by
      unfold ColdStepAtMirrorFrames.contourAverage
      simp only [Finset.sum_sub_distrib, mul_sub]
      congr 1
      simp only [Finset.sum_const, card_perm_fin_four, card_centredCube hL, nsmul_eq_mul]
      push_cast
      field_simp
    rw [e] at h1
    refine h1.congr fun τ => ?_
    unfold sineAverage
    simp only [mul_div_assoc, Finset.sum_div]
private theorem unitGenerator_norm : ‖unitGenerator‖ = 1 := norm_unitGenerator
private theorem contourAverage_abelianField_mul_inv {j : ℕ} (θ : LevelForm F j) (θ' : LevelForm F (j + 1))
    (c : F.Site (j + 1) × Fin 4) :
    BlockAverages.contourAverage (abelianField unitGenerator θ) c *
        (((abelianField unitGenerator θ' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (cosineAverage θ (θ' c.1 c.2) c : ℍ[ℝ]) + sineAverage θ (θ' c.1 c.2) c • (unitGenerator : ℍ[ℝ]) := by
  have hg' : (abelianField unitGenerator θ' c.1 c.2)⁻¹ = expUnit ((- θ' c.1 c.2) • unitGenerator) :=
    inv_expUnit_smul unitGenerator_norm _
  rw [hg']
  unfold BlockAverages.contourAverage
  rw [smul_mul_assoc, Finset.sum_mul]
  have e1 : ∀ h ∈ centredCube F.blockSide, (∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy (abelianField unitGenerator θ) (refineSite c.1) (bondContour F.blockSide h π c.2) :
        UnitQuaternion) : ℍ[ℝ])) *
        ((expUnit ((- θ' c.1 c.2) • unitGenerator) : UnitQuaternion) : ℍ[ℝ]) =
      ∑ π : Equiv.Perm (Fin 4),
        (((Real.cos (pathSum θ (refineSite c.1) (bondContour F.blockSide h π c.2) - θ' c.1 c.2) : ℝ) : ℍ[ℝ]) +
          Real.sin (pathSum θ (refineSite c.1) (bondContour F.blockSide h π c.2) - θ' c.1 c.2) •
            (unitGenerator : ℍ[ℝ])) := by
    intro h _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [pathHolonomy_abelianField unitGenerator_norm]
    show (((expUnit _ * expUnit _ : UnitQuaternion)) : ℍ[ℝ]) = _
    rw [expUnit_smul_mul unitGenerator_norm, coe_expUnit_smul unitGenerator_norm]
    rfl
  rw [Finset.sum_congr rfl e1]
  simp only [Finset.sum_add_distrib, ← Finset.sum_smul, smul_add]
  unfold cosineAverage sineAverage
  congr 1
  · simp_rw [← quaternion_coe_sum]
    exact smul_quaternion_coe _ _
  · rw [smul_smul]
private theorem sineAverage_sq_le_blockFit (hL : Odd F.blockSide) {j : ℕ} (θ : LevelForm F j)
    (θ' : LevelForm F (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    sineAverage θ (θ' c.1 c.2) c ^ 2 / 2 ≤ blockFit (abelianField unitGenerator θ) (abelianField unitGenerator θ') c := by
  have h := componentAlong_sq_div_two_le_blockFit unitGenerator_norm hL (abelianField unitGenerator θ)
    (abelianField unitGenerator θ') c
  rw [contourAverage_abelianField_mul_inv, componentAlong_add, componentAlong_smul,
    componentAlong_self unitGenerator_norm] at h
  have e : ∀ r : ℝ, componentAlong unitGenerator (r : ℍ[ℝ]) = 0 := fun r => by
    simp [componentAlong_eq_imParts]
  rw [e] at h
  simpa using h
private theorem tendsto_blockFit_curve (hL : Odd F.blockSide) {j n : ℕ} {s : ℝ → TorusBond m → ℝ}
    {d : TorusBond m → ℝ} (hs0 : s 0 = 0)
    (hs : HasDerivAt s d 0) (B : TorusBond n → ℝ) (c : F.Site (j + 1) × Fin 4) :
    Tendsto (fun τ : ℝ => 2 * blockFit (abelianField unitGenerator (torusForm (F := F) (j := j) m (s τ)))
        (abelianField unitGenerator (torusForm (F := F) (j := j + 1) n (τ • B))) c / τ ^ 2) (𝓝[>] 0)
      (𝓝 ((ColdStepAtMirrorFrames.contourAverage (torusForm (F := F) (j := j) m d) c.1 c.2 -
        torusForm (F := F) (j := j + 1) n B c.1 c.2) ^ 2)) := by
  set b := torusForm (F := F) (j := j + 1) n B c.1 c.2 with hb
  obtain ⟨h1, h2⟩ := tendsto_averages_curve hL hs0 hs b c
  have e : ∀ τ : ℝ, torusForm (F := F) (j := j + 1) n (τ • B) c.1 c.2 = τ * b := fun τ => rfl
  have hlow := h2.pow 2
  have hup : Tendsto (fun τ : ℝ => (sineAverage (torusForm (F := F) (j := j) m (s τ)) (τ * b) c / τ) ^ 2 /
      cosineAverage (torusForm (F := F) (j := j) m (s τ)) (τ * b) c) (𝓝[>] 0)
      (𝓝 ((ColdStepAtMirrorFrames.contourAverage (torusForm (F := F) (j := j) m d) c.1 c.2 - b) ^ 2)) := by
    have h3 := (h2.pow 2).div h1 one_ne_zero
    rw [div_one] at h3
    exact h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have h := sineAverage_sq_le_blockFit hL (torusForm (F := F) (j := j) m (s τ))
      (torusForm (F := F) (j := j + 1) n (τ • B)) c
    rw [e τ] at h
    rw [div_pow, div_le_div_iff_of_pos_right (by positivity)]
    linarith
  · filter_upwards [self_mem_nhdsWithin, h1.eventually (lt_mem_nhds one_pos)] with τ hτ hA
    have hτ0 : (0 : ℝ) < τ := hτ
    have hA0 : 0 < cosineAverage (torusForm (F := F) (j := j) m (s τ)) (τ * b) c := hA
    have h := blockFit_abelianField_le unitGenerator_norm (torusForm (F := F) (j := j) m (s τ))
      (torusForm (F := F) (j := j + 1) n (τ • B)) c (by rw [e τ]; exact hA0)
    rw [e τ] at h
    have e2 : (sineAverage (torusForm (F := F) (j := j) m (s τ)) (τ * b) c / τ) ^ 2 /
        cosineAverage (torusForm (F := F) (j := j) m (s τ)) (τ * b) c =
        2 * (sineAverage (torusForm (F := F) (j := j) m (s τ)) (τ * b) c ^ 2 /
          (2 * cosineAverage (torusForm (F := F) (j := j) m (s τ)) (τ * b) c)) / τ ^ 2 := by
      field_simp
    rw [e2, div_le_div_iff_of_pos_right (by positivity)]
    linarith
end Limits
section Contours
private def torusPathSum {m : ℕ} (σ : TorusBond m → ℝ) : TorusSite m → List PathStep → ℝ
  | _, [] => 0
  | x, st :: r => (if st.2 then σ (x, st.1) else - σ (x - TorusFields.unitStep m st.1, st.1)) +
      torusPathSum σ (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) r
variable {F : BlockFrame} {j m : ℕ}
private theorem toTorusSite_zero_site : toTorusSite m (0 : F.Site j) = 0 := by
  funext k
  simp [toTorusSite, siteCoords]
private theorem toTorusSite_neg_site (hp : ∀ i, F.period j i = m) (x : F.Site j) :
    toTorusSite m (-x) = - toTorusSite m x := by
  have h := FrameTorusAction.toTorusSite_add hp x (-x)
  rw [add_neg_cancel, toTorusSite_zero_site] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm
private theorem pathSum_torusForm (hp : ∀ i, F.period j i = m) (σ : TorusBond m → ℝ) (x : F.Site j)
    (l : List PathStep) :
    pathSum (torusForm (F := F) (j := j) m σ) x l = torusPathSum σ (toTorusSite m x) l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have hstep : toTorusSite m (x + stepDisplacement j st) =
        toTorusSite m x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1) := by
      rw [FrameTorusAction.toTorusSite_add hp]
      congr 1
      unfold stepDisplacement
      by_cases h : st.2 = true
      · simp only [h, if_true]
        exact toTorusSite_unitStep hp _
      · simp only [h, Bool.false_eq_true, if_false]
        rw [toTorusSite_neg_site hp, toTorusSite_unitStep hp]
    have hsub : toTorusSite m (x - BlockAverages.unitStep j st.1) =
        toTorusSite m x - TorusFields.unitStep m st.1 := by
      rw [sub_eq_add_neg, FrameTorusAction.toTorusSite_add hp, toTorusSite_neg_site hp, toTorusSite_unitStep hp,
        sub_eq_add_neg]
    show (if st.2 then σ (toTorusSite m x, st.1) else
        - σ (toTorusSite m (x - BlockAverages.unitStep j st.1), st.1)) +
      pathSum _ (x + stepDisplacement j st) r = _
    rw [ih, hstep, hsub]
    rfl
private theorem toTorusSite_siteOfCoords_eq (hp : ∀ i, F.period j i = m) (z : Fin 4 → ℤ) :
    toTorusSite m (siteOfCoords (F := F) j z) = fun k => (z k : ZMod m) := by
  funext k
  exact intCast_cast_intCast (hp k) (z k)
private theorem siteCoords_torusToFrame {n : ℕ} [NeZero n] (hp : ∀ i, F.period j i = n) (x : TorusSite n)
    (k : Fin 4) : siteCoords (torusToFrame F j x) k = ((x k).cast : ℤ) := by apply _root_.YangMills.Construction.TopLevelSites.siteCoords_torusSiteInFrame <;> assumption
variable {L u n : ℕ} [NeZero n] [NeZero L]
private theorem contourAverage_eq_contourMean (σ : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    ColdStepAtMirrorFrames.contourAverage (F := torusFrame L u n) (j := u) (torusForm (n * L) σ)
        (torusToFrame (torusFrame L u n) (u + 1) c.1) c.2 =
      contourMean L σ c := by
  have hb : toTorusSite (n * L) (refineSite (torusToFrame (torusFrame L u n) (u + 1) c.1) :
        (torusFrame L u n).Site u) =
      toTorusSite (n * L) (refineSite (StepCosts.torusSiteInFrame (stepBlockFrame L n) 1 c.1) :
        (stepBlockFrame L n).Site 0) := by
    show toTorusSite (n * L) (siteOfCoords (F := torusFrame L u n) u fun i =>
        (L : ℤ) * siteCoords (torusToFrame (torusFrame L u n) (u + 1) c.1) i) =
      toTorusSite (n * L) (siteOfCoords (F := stepBlockFrame L n) 0 fun i =>
        (L : ℤ) * siteCoords (torusToFrame (stepBlockFrame L n) 1 c.1) i)
    rw [toTorusSite_siteOfCoords_eq (period_depth L u n), toTorusSite_siteOfCoords_eq (period_stepBlockFrame_zero L n)]
    funext k
    rw [siteCoords_torusToFrame (period_top_level L u n), siteCoords_torusToFrame (period_stepBlockFrame_one L n)]
  unfold contourMean ColdStepAtMirrorFrames.contourAverage
  show (1 / (24 * (L : ℝ) ^ 4)) * ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
      pathSum (torusForm (F := torusFrame L u n) (j := u) (n * L) σ)
        (refineSite (torusToFrame (torusFrame L u n) (u + 1) c.1)) (bondContour L h π c.2) =
    (1 / (24 * (L : ℝ) ^ 4)) * ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
      pathSum (torusForm (F := stepBlockFrame L n) (j := 0) (n * L) σ)
        (refineSite (StepCosts.torusSiteInFrame (stepBlockFrame L n) 1 c.1)) (bondContour L h π c.2)
  congr 1
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => ?_
  rw [pathSum_torusForm (period_depth L u n), pathSum_torusForm (period_stepBlockFrame_zero L n), hb]
private theorem pathSum_add_smul {j' : ℕ} {F' : BlockFrame} {m' : ℕ} (A B : TorusBond m' → ℝ) (ε : ℝ)
    (x : F'.Site j') (l : List PathStep) :
    pathSum (torusForm (F := F') (j := j') m' (A + ε • B)) x l =
      pathSum (torusForm (F := F') (j := j') m' A) x l + ε * pathSum (torusForm (F := F') (j := j') m' B) x l := by
  induction l generalizing x with
  | nil => simp [pathSum]
  | cons st r ih =>
    simp only [pathSum, ih]
    by_cases h : st.2 = true
    · simp only [h, if_true, torusForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [h, Bool.false_eq_true, if_false, torusForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
private theorem contourMean_add_smul (A B : TorusBond (n * L) → ℝ) (ε : ℝ) (c : TorusBond n) :
    contourMean L (A + ε • B) c = contourMean L A c + ε * contourMean L B c := by
  show ColdStepAtMirrorFrames.contourAverage (F := stepBlockFrame L n) (j := 0) (torusForm (n * L) (A + ε • B)) _ _ =
    ColdStepAtMirrorFrames.contourAverage (F := stepBlockFrame L n) (j := 0) (torusForm (n * L) A) _ _ +
      ε * ColdStepAtMirrorFrames.contourAverage (F := stepBlockFrame L n) (j := 0) (torusForm (n * L) B) _ _
  unfold ColdStepAtMirrorFrames.contourAverage
  simp only [pathSum_add_smul, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
end Contours
end StepPolarity
namespace ColdStepAtMirrorFrames
section Flat
variable {F : BlockFrame}
private theorem conj_expUnit (g : UnitQuaternion) (w w' : imaginaryQuaternions)
    (h : (g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = (w' : ℍ[ℝ])) :
    g * expUnit w * g⁻¹ = expUnit w' := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponse.mul_expUnit_mul_inv <;> assumption
private theorem eq_smul_of_conj_fixed (X D : imaginaryQuaternions) (hX : ‖X‖ = 1) (hu : (X : ℍ[ℝ]) ∈ unitary ℍ[ℝ])
    (hfix : (X : ℍ[ℝ]) * (D : ℍ[ℝ]) * star (X : ℍ[ℝ]) = (D : ℍ[ℝ])) :
    D = (-((D : ℍ[ℝ]) * (X : ℍ[ℝ])).re) • X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponse.eq_smul_of_conj_fixed <;> assumption
private theorem adjointMap_minimizingCoordinates {a : ℝ} {L : ℕ} {c : ColdChainParameters}
    (hT : MinimalActionGaugeCovariance) (hL : Odd L)
    (hc : c.Admissible a L) (hF : IsBlockTorus L F) (V : F.GaugeField F.top) (hV : IsSmallCurvature c.σA V)
    (γ : F.Cell → UnitQuaternion) (hg : gaugeTransform γ V = V) (x : F.Site F.depth) (i : Fin 4) :
    adjointMap (γ (enclosingCell x)) (minimizingCoordinates a (finiteCells F) V c.ρA x i) =
      minimizingCoordinates a (finiteCells F) V c.ρA x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponse.adjointMap_minimizingCoordinates_of_gauge_fixed <;> assumption
private def topBondLine (X : imaginaryQuaternions) (b : F.Site F.top × Fin 4) (τ : ℝ) : F.GaugeField F.top :=
  abelianField X fun y i => τ * topBondIndicator b y i
private theorem leftTranslate_bondSpread_eq (b : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (t : Fin 1 → ℝ) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread ![b] ![X] t) (uniformField F F.top) = topBondLine X b (t 0) := by apply _root_.YangMills.DeltaSharedProofs.p502581 <;> assumption
private theorem topBondLine_zero (b : F.Site F.top × Fin 4) (X : imaginaryQuaternions) :
    topBondLine X b 0 = uniformField F F.top := by
  funext y i
  simp [topBondLine, abelianField, uniformField, expUnit_zero_eq_one]
private theorem torusCoordinate_of_not_mem {a ρ : ℝ} (bd : F.Site F.depth × Fin 4)
    (hb : bd ∉ chordBonds (finiteCells F)) (V : F.GaugeField F.top) : torusCoordinate a ρ bd V = 0 := by apply _root_.YangMills.SharedProofs.p33224 <;> assumption
section Numbers
variable {a : ℝ} {L : ℕ} {c : ColdChainParameters}
private theorem hasDerivAt_torusCoordinate (hc : c.Admissible a L) (hFL : F.blockSide = L) (hF : IsLargeCubicTorus F)
    (bd : F.Site F.depth × Fin 4) (b : F.Site F.top × Fin 4) (X : imaginaryQuaternions) :
    HasDerivAt (fun τ => torusCoordinate a c.ρA bd (topBondLine X b τ))
      (bondDeriv (torusCoordinate a c.ρA bd) (uniformField F F.top) ![b] ![X]) 0 := by apply _root_.YangMills.DeltaSharedProofs.p501622 <;> assumption
end Numbers
end Flat
end ColdStepAtMirrorFrames
namespace StepPolarity
section Curve
variable {a : ℝ} {L u n : ℕ} [NeZero n] [NeZero L] {cn : ColdChainParameters}
private theorem topBondIndicator_torusToFrame (c : TorusBond n) (y : (torusFrame L u n).Site (torusFrame L u n).top)
    (i : Fin 4) :
    topBondIndicator (F := torusFrame L u n) (torusToFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2) y i =
      bondIndicator c (frameToTorus n y, i) := by
  have hT : ∀ k, (torusFrame L u n).period (torusFrame L u n).top k = n := TorusFrame.period_torusFrame
  have key : (y, i) = (torusToFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2) ↔
      (frameToTorus n y, i) = c := by
    constructor
    · intro h
      have h1 : y = torusToFrame (torusFrame L u n) (torusFrame L u n).top c.1 := congrArg Prod.fst h
      have h2 : i = c.2 := congrArg Prod.snd h
      refine Prod.ext ?_ h2
      show frameToTorus n y = c.1
      rw [h1, frameToTorus_torusToFrame hT]
    · intro h
      have h1 : frameToTorus n y = c.1 := congrArg Prod.fst h
      have h2 : i = c.2 := congrArg Prod.snd h
      refine Prod.ext ?_ h2
      show y = torusToFrame (torusFrame L u n) (torusFrame L u n).top c.1
      rw [← h1, torusToFrame_frameToTorus hT]
  unfold topBondIndicator bondIndicator
  by_cases h : (frameToTorus n y, i) = c
  · rw [if_pos (key.2 h), if_pos h]
  · rw [if_neg (fun e => h (key.1 e)), if_neg h]
private theorem topBondLine_eq_abelianField (c : TorusBond n) (τ : ℝ) :
    topBondLine unitGenerator (F := torusFrame L u n)
        (torusToFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2) τ =
      abelianField unitGenerator (torusForm (F := torusFrame L u n) (j := u + 1) n (τ • bondIndicator c)) := by
  funext y i
  show expUnit ((τ * topBondIndicator (F := torusFrame L u n) _ y i) • unitGenerator) =
    expUnit ((τ • bondIndicator c) (toTorusSite n y, i) • unitGenerator)
  rw [topBondIndicator_torusToFrame]
  rfl
open Classical in
private def minimizingExponent (a ρ : ℝ) (L u n : ℕ) (c : TorusBond n) (τ : ℝ) (b : TorusBond (n * L)) : ℝ :=
  componentAlong unitGenerator (torusCoordinate (F := torusFrame L u n) a ρ
      (torusToFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2)
      (topBondLine unitGenerator (F := torusFrame L u n)
        (torusToFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2) τ) : ℍ[ℝ]) +
    if IsCrossingBond (F := torusFrame L u n) (torusToFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) ∧
        enclosingCell (torusToFrame (torusFrame L u n) (torusFrame L u n).depth b.1) =
          torusToFrame (torusFrame L u n) (torusFrame L u n).top c.1 ∧ b.2 = c.2 then τ else 0
private theorem minimizingExponent_zero (hFS : FlatCoordinatesScalar) (hL : Odd L) (hc : cn.Admissible a L)
    (hn : 64 ≤ n) (c : TorusBond n) : minimizingExponent a cn.ρA L u n c 0 = 0 := by
  funext b
  unfold minimizingExponent
  rw [topBondLine_zero, (hFS a L cn hL hc (torusFrame L u n)
    (torusToFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2)
    (torusToFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2) unitGenerator ⟨rfl, n, hn, fun _ => rfl⟩
    unitGenerator_norm).1]
  simp [componentAlong_zero]
private def componentAlongCLM : imaginaryQuaternions →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  { toFun := fun v => componentAlong unitGenerator (v : ℍ[ℝ])
    map_add' := fun v w => by simp [componentAlong_add]
    map_smul' := fun r v => by simp [componentAlong_smul] }
private theorem hasDerivAt_minimizingExponent (hc : cn.Admissible a L) (hn : 64 ≤ n) (c : TorusBond n) :
    HasDerivAt (minimizingExponent a cn.ρA L u n c) (fun b => responseKernel a cn.ρA L u b c) 0 := by
  classical
  refine hasDerivAt_pi.2 fun b => ?_
  have h1 := hasDerivAt_torusCoordinate (F := torusFrame L u n) hc rfl ⟨n, hn, fun _ => rfl⟩
    (torusToFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2)
    (torusToFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2) unitGenerator
  have h2 := componentAlongCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  set r' : ℝ := componentAlong unitGenerator ((bondDeriv (torusCoordinate (F := torusFrame L u n) a cn.ρA
    (torusToFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2))
    (uniformField (torusFrame L u n) (torusFrame L u n).top)
    ![(torusToFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2)] ![unitGenerator] :
      imaginaryQuaternions) : ℍ[ℝ]) with hr'
  set r : ℝ → ℝ := fun τ => componentAlong unitGenerator (torusCoordinate (F := torusFrame L u n) a cn.ρA
      (torusToFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2)
      (topBondLine unitGenerator (F := torusFrame L u n)
        (torusToFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2) τ) : ℍ[ℝ]) with hr
  have h3 : HasDerivAt r r' 0 := h2
  by_cases hP : IsCrossingBond (F := torusFrame L u n)
      (torusToFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) ∧
      enclosingCell (torusToFrame (torusFrame L u n) (torusFrame L u n).depth b.1) =
        torusToFrame (torusFrame L u n) (torusFrame L u n).top c.1 ∧ b.2 = c.2
  · have e1 : (fun τ => minimizingExponent a cn.ρA L u n c τ b) = fun τ => r τ + τ := by
      funext τ
      exact congrArg (r τ + ·) (if_pos hP)
    have e2 : responseKernel a cn.ρA L u b c = r' + 1 := congrArg (r' + ·) (if_pos hP)
    rw [e1, e2]
    exact h3.add (hasDerivAt_id' 0)
  · have e1 : (fun τ => minimizingExponent a cn.ρA L u n c τ b) = fun τ => r τ + 0 := by
      funext τ
      exact congrArg (r τ + ·) (if_neg hP)
    have e2 : responseKernel a cn.ρA L u b c = r' + 0 := congrArg (r' + ·) (if_neg hP)
    rw [e1, e2]
    exact h3.add (hasDerivAt_const _ _)
private theorem abelianAction_succ_eq_along (hLeast : minimalChainExistenceStatement)
    (hGauge : MinimalActionGaugeCovariance)
    (ha : 0 ≤ a) (hL : Odd L) (hc : cn.Admissible a L) (hn : 64 ≤ n) (c : TorusBond n) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), abelianAction a L (u + 1) n (τ • bondIndicator c) =
      abelianAction a L u (n * L) (minimizingExponent a cn.ρA L u n c τ) +
        a * fitTotal L u n (minimizingExponent a cn.ρA L u n c τ) (τ • bondIndicator c) := by
  classical
  obtain ⟨⟨-, -, hs0, -⟩, body⟩ := hc.classical
  have hσ16 : 16 * cn.s₀ ≤ cn.σA := hc.inequalities.2.2.1
  have hF : IsBlockTorus L (torusFrame L u n) := ⟨rfl, n, hn, fun _ => rfl⟩
  have hX : ‖unitGenerator‖ = 1 := unitGenerator_norm
  have hball : Set.Ioo (0 : ℝ) (cn.s₀ / 8) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hball] with τ hτ
  obtain ⟨hτ0, hτ1⟩ := hτ
  set cF : (torusFrame L u n).Site (torusFrame L u n).top × Fin 4 :=
    (torusToFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2) with hcF
  set V := topBondLine unitGenerator (F := torusFrame L u n) cF τ with hV
  have hnear : ∀ x i, ‖((V x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ τ := by
    intro x i
    refine (TorusFrame.norm_expUnit_sub_one_le _).trans ?_
    show ‖(((τ * topBondIndicator (F := torusFrame L u n) cF x i) • unitGenerator : imaginaryQuaternions) :
      ℍ[ℝ])‖ ≤ τ
    have h : ‖(unitGenerator : ℍ[ℝ])‖ = 1 := norm_unitGenerator
    rw [Submodule.coe_smul, norm_smul, h, mul_one, Real.norm_eq_abs]
    unfold topBondIndicator
    split_ifs <;> simp [abs_of_pos hτ0, hτ0.le]
  have hcold0 : IsSmallCurvature cn.s₀ V := isSmallCurvature_of_near_one V (m := τ) (by linarith) hnear
  have hcoldσ : IsSmallCurvature cn.σA V := isSmallCurvature_of_near_one V (m := τ) (by linarith) hnear
  have hw := (body (torusFrame L u n) cn.s₀ V hF hs0 le_rfl hcold0).1
  set w := minimizingCoordinates a (finiteCells (torusFrame L u n)) V cn.ρA with hwdef
  have hun : Quaternion.normSq (unitGenerator : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, norm_unitGenerator]
    norm_num
  have hu : (unitGenerator : ℍ[ℝ]) ∈ unitary ℍ[ℝ] := by
    rw [Unitary.mem_iff]
    constructor
    · rw [Quaternion.star_mul_self, hun]
      simp
    · rw [Quaternion.self_mul_star, hun]
      simp
  set g : UnitQuaternion := ⟨(unitGenerator : ℍ[ℝ]), hu⟩ with hgdef
  have hginv : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (unitGenerator : ℍ[ℝ]) := rfl
  have hXX : (unitGenerator : ℍ[ℝ]) * star (unitGenerator : ℍ[ℝ]) = 1 := by
    rw [Quaternion.self_mul_star, hun]
    simp
  have hgf : gaugeTransform (fun _ => g) V = V := by
    funext x i
    show g * expUnit ((τ * topBondIndicator (F := torusFrame L u n) cF x i) • unitGenerator) * g⁻¹ =
      expUnit ((τ * topBondIndicator (F := torusFrame L u n) cF x i) • unitGenerator)
    apply conj_expUnit
    simp only [Submodule.coe_smul, mul_smul_comm, smul_mul_assoc, hginv]
    change (τ * topBondIndicator (F := torusFrame L u n) cF x i) •
      ((unitGenerator : ℍ[ℝ]) * (unitGenerator : ℍ[ℝ]) * star (unitGenerator : ℍ[ℝ])) = _
    rw [mul_assoc, hXX, mul_one]
  have halong : ∀ x i, w x i = (componentAlong unitGenerator (w x i : ℍ[ℝ])) • unitGenerator := by
    intro x i
    have h := adjointMap_minimizingCoordinates hGauge hL hc hF V hcoldσ (fun _ => g) hgf x i
    have h2 := congrArg (fun v : imaginaryQuaternions => (v : ℍ[ℝ])) h
    exact eq_smul_of_conj_fixed unitGenerator _ hX hu h2
  have hchart : chartedField w V =
      abelianField unitGenerator
        (torusForm (F := torusFrame L u n) (j := u) (n * L) (minimizingExponent a cn.ρA L u n c τ)) := by
    funext x i
    have hx : torusToFrame (torusFrame L u n) (torusFrame L u n).depth (toTorusSite (n * L) x) = x :=
      torusToFrame_frameToTorus (period_depth L u n) x
    have hval : minimizingExponent a cn.ρA L u n c τ (toTorusSite (n * L) x, i) =
        componentAlong unitGenerator (w x i : ℍ[ℝ]) +
        if IsCrossingBond (F := torusFrame L u n) (x, i) ∧ enclosingCell x = cF.1 ∧ i = cF.2 then τ else 0 := by
      unfold minimizingExponent
      simp only [hx]
      rfl
    show chartedField w V x i =
      expUnit (minimizingExponent a cn.ρA L u n c τ (toTorusSite (n * L) x, i) • unitGenerator)
    rw [hval]
    have hexp : expUnit (w x i) = expUnit ((componentAlong unitGenerator (w x i : ℍ[ℝ])) • unitGenerator) :=
      congrArg expUnit (halong x i)
    unfold chartedField
    by_cases hcr : IsCrossingBond (F := torusFrame L u n) (x, i)
    · rw [if_pos hcr]
      have hv : V (enclosingCell x) i =
          expUnit ((τ * topBondIndicator (F := torusFrame L u n) cF (enclosingCell x) i) • unitGenerator) := rfl
      rw [hv, hexp, expUnit_smul_mul hX]
      congr 2
      by_cases hq : enclosingCell x = cF.1 ∧ i = cF.2
      · rw [if_pos ⟨hcr, hq⟩]
        unfold topBondIndicator
        rw [if_pos (Prod.ext hq.1 hq.2)]
        ring
      · rw [if_neg (fun h => hq h.2)]
        unfold topBondIndicator
        rw [if_neg (fun h => hq ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩)]
        ring
    · have hz : (if IsCrossingBond (F := torusFrame L u n) (x, i) ∧ enclosingCell x = cF.1 ∧ i = cF.2 then τ
          else 0) = 0 :=
        if_neg (fun h => hcr h.1)
      rw [if_neg hcr, hz, add_zero]
      by_cases ht : IsAxialTreeBond (F := torusFrame L u n) (x, i)
      · rw [if_pos ht]
        have h0 : w x i = 0 := hw.1 (x, i) (fun hm => (Finset.mem_filter.1 hm).2 ht)
        rw [h0]
        simp [componentAlong_zero, expUnit_zero_eq_one]
      · rw [if_neg ht, hexp]
  have hTL := topBondLine_eq_abelianField (L := L) (u := u) c τ
  obtain ⟨W, hW, hmin⟩ := (hLeast (torusFrame L u n) a (finiteCells _) ha).2.2.1 u V
  have h1 : blockEnergy a (finiteCells (torusFrame L u n)) u
      (abelianField unitGenerator
        (torusForm (F := torusFrame L u n) (j := u) (n * L) (minimizingExponent a cn.ρA L u n c τ))) V ≤
      blockEnergy a (finiteCells (torusFrame L u n)) u W V := by
    have := hw.2.2 W
    rw [hchart] at this
    exact this
  have hle : blockEnergy a (finiteCells (torusFrame L u n)) u
      (abelianField unitGenerator
        (torusForm (F := torusFrame L u n) (j := u) (n * L) (minimizingExponent a cn.ρA L u n c τ))) V =
      minimalAction a (finiteCells (torusFrame L u n)) (u + 1) V :=
    le_antisymm (h1.trans_eq hW) (hW.symm.le.trans (hmin _))
  calc abelianAction a L (u + 1) n (τ • bondIndicator c)
      = minimalAction a (finiteCells (torusFrame L u n)) (u + 1)
          (abelianField unitGenerator
            (torusForm (F := torusFrame L u n) (j := u + 1) n (τ • bondIndicator c))) := abelianAction_succ_top _
    _ = minimalAction a (finiteCells (torusFrame L u n)) (u + 1) V := by rw [← hTL]
    _ = blockEnergy a (finiteCells (torusFrame L u n)) u
          (abelianField unitGenerator
            (torusForm (F := torusFrame L u n) (j := u) (n * L) (minimizingExponent a cn.ρA L u n c τ))) V :=
        hle.symm
    _ = blockEnergy a (finiteCells (torusFrame L u n)) u
          (abelianField unitGenerator
            (torusForm (F := torusFrame L u n) (j := u) (n * L) (minimizingExponent a cn.ρA L u n c τ)))
          (abelianField unitGenerator
            (torusForm (F := torusFrame L u n) (j := u + 1) n (τ • bondIndicator c))) := by rw [← hTL]
    _ = _ := blockEnergy_torusForm hL _ _
end Curve
section Square
variable {a : ℝ} {L : ℕ} {cn : ColdChainParameters}
private theorem tendsto_abelianAction_div_sq (hLeast : minimalChainExistenceStatement)
    (hFlat : flatTopVanishingStatement)
    (ha : 0 ≤ a) (hL : Odd L) (hc : cn.Admissible a L) (u : ℕ) {m : ℕ} [NeZero m] (hm : 64 ≤ m)
    (B : TorusBond m → ℝ) :
    Tendsto (fun τ : ℝ => 2 * abelianAction a L u m (τ • B) / τ ^ 2) (𝓝[>] 0) (𝓝 (maxwellForm a L u B B)) := by
  obtain ⟨hC, h0, hnn⟩ := abelianAction_props hLeast hFlat ha hL hc u hm
  have hv : HasDerivAt (fun τ : ℝ => τ • B) B 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const B
  have h := tendsto_two_mul_div_sq hC h0 (fderiv_abelianAction_zero h0 hnn) (v := fun τ : ℝ => τ • B) (by simp) hv
  rwa [← maxwellForm_eq_fderiv hC] at h
variable {u n : ℕ} [NeZero n] [NeZero L]
private theorem tendsto_blockEnergy_div_sq (hLeast : minimalChainExistenceStatement)
    (hFlat : flatTopVanishingStatement)
    (ha : 0 ≤ a) (hL : Odd L) (hc : cn.Admissible a L) (hm : 64 ≤ n * L) {s : ℝ → TorusBond (n * L) → ℝ}
    {d : TorusBond (n * L) → ℝ} (hs0 : s 0 = 0) (hs : HasDerivAt s d 0) (B : TorusBond n → ℝ) :
    Tendsto (fun τ : ℝ => 2 * (abelianAction a L u (n * L) (s τ) + a * fitTotal L u n (s τ) (τ • B)) / τ ^ 2)
      (𝓝[>] 0) (𝓝 (maxwellForm a L u d d + a * ∑ c : TorusBond n, (contourMean L d c - B c) ^ 2)) := by
  obtain ⟨hC, h0, hnn⟩ := abelianAction_props hLeast hFlat ha hL hc u hm
  have h1 := tendsto_two_mul_div_sq hC h0 (fderiv_abelianAction_zero h0 hnn) hs0 hs
  rw [← maxwellForm_eq_fderiv hC] at h1
  have hodd : Odd (torusFrame L u n).blockSide := hL
  have h2 : Tendsto (fun τ : ℝ => ∑ c : TorusBond n, 2 * blockFit
      (abelianField unitGenerator (torusForm (F := torusFrame L u n) (j := u) (n * L) (s τ)))
      (abelianField unitGenerator (torusForm (F := torusFrame L u n) (j := u + 1) n (τ • B)))
      (torusToFrame (torusFrame L u n) (u + 1) c.1, c.2) / τ ^ 2) (𝓝[>] 0)
      (𝓝 (∑ c : TorusBond n, (contourMean L d c - B c) ^ 2)) := by
    refine tendsto_finset_sum _ fun c _ => ?_
    have h3 := tendsto_blockFit_curve (F := torusFrame L u n) (j := u) hodd hs0 hs B
      (torusToFrame (torusFrame L u n) (u + 1) c.1, c.2)
    have e1 := contourAverage_eq_contourMean (L := L) (u := u) d c
    have e2 : torusForm (F := torusFrame L u n) (j := u + 1) n B (torusToFrame (torusFrame L u n) (u + 1) c.1) c.2 =
        B c := by
      show B (frameToTorus n (torusToFrame (torusFrame L u n) (u + 1) c.1), c.2) = B c
      rw [frameToTorus_torusToFrame (period_top_level L u n)]
    simp only [e1, e2] at h3
    exact h3
  refine (h1.add (h2.const_mul a)).congr fun τ => ?_
  unfold fitTotal
  simp only [← Finset.sum_div, ← Finset.mul_sum]
  ring
private theorem maxwellForm_step (hLeast : minimalChainExistenceStatement) (hFlat : flatTopVanishingStatement)
    (hGauge : MinimalActionGaugeCovariance) (hFS : FlatCoordinatesScalar)
    (ha : 0 ≤ a) (hL : Odd L) (hc : cn.Admissible a L) (hn : 64 ≤ n) :
    (∀ (X : TorusBond (n * L) → ℝ) (B : TorusBond n → ℝ), maxwellForm a L (u + 1) B B ≤
      maxwellForm a L u X X + a * ∑ c : TorusBond n, (contourMean L X c - B c) ^ 2) ∧
    ∀ c : TorusBond n, maxwellForm a L (u + 1) (bondIndicator c) (bondIndicator c) =
      maxwellForm a L u (fun b => responseKernel a cn.ρA L u b c) (fun b => responseKernel a cn.ρA L u b c) +
        a * ∑ c' : TorusBond n,
          (contourMean L (fun b => responseKernel a cn.ρA L u b c) c' - bondIndicator c c') ^ 2 := by
  have hLpos : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hm : 64 ≤ n * L := hn.trans (Nat.le_mul_of_pos_right n hLpos)
  constructor
  · intro X B
    have hv : HasDerivAt (fun τ : ℝ => τ • X) X 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const X
    have h1 := tendsto_abelianAction_div_sq hLeast hFlat ha hL hc (u + 1) hn B
    have h2 := tendsto_blockEnergy_div_sq (u := u) hLeast hFlat ha hL hc hm (s := fun τ : ℝ => τ • X) (by simp) hv B
    refine le_of_tendsto_of_tendsto h1 h2 ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have := abelianAction_succ_le (u := u) hLeast ha hL (τ • X) (τ • B)
    gcongr
  · intro c
    have h1 := tendsto_abelianAction_div_sq hLeast hFlat ha hL hc (u + 1) hn (bondIndicator c)
    have h2 := tendsto_blockEnergy_div_sq (u := u) hLeast hFlat ha hL hc hm
      (minimizingExponent_zero (u := u) hFS hL hc hn c)
      (hasDerivAt_minimizingExponent (u := u) hc hn c) (bondIndicator c)
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [abelianAction_succ_eq_along (u := u) hLeast hGauge ha hL hc hn c] with τ hτ
    rw [hτ]
end Square
private theorem eventuallyOrdered_of_forall {P : ColdStepAtMirrorFrames.StepParameters → Prop}
    (h : ∀ T : ColdStepAtMirrorFrames.StepParameters, T.IsOrdered → P T) : EventuallyOrdered P := by
  intro a _
  refine ⟨0, fun L _ _ c _ => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun nss _ =>
    ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ E _ => ⟨0, fun n₀ _ => ⟨0, fun CE _ => ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  intro hD _
  exact h _ hD
theorem polarIdentityStatement_holds (hLeast : minimalChainExistenceStatement)
    (hFlat : flatTopVanishingStatement) (hGauge : MinimalActionGaugeCovariance)
    (hFS : FlatCoordinatesScalar) : polarIdentityStatement := by
  refine eventuallyOrdered_of_forall fun T hD => ?_
  intro _
  have ha : 0 ≤ T.a := by linarith [hD.one_le_a]
  have hL := hD.odd_L
  have hc := hD.chain_admissible
  refine ⟨fun u m _ b b' hm => ?_, fun u n _ c φ B hn => ?_⟩
  · obtain ⟨hC, -, -⟩ := abelianAction_props hLeast hFlat ha hL hc u hm
    rw [maxwellKernel_eq_fderiv T.a T.L u hC, maxwellKernel_eq_fderiv T.a T.L u hC]
    exact (hC.isSymmSndFDerivAt (by simp)).eq _ _
  · have hLpos : 1 ≤ T.L := Nat.one_le_iff_ne_zero.2 (NeZero.ne T.L)
    have hm : 64 ≤ n * T.L := hn.trans (Nat.le_mul_of_pos_right n hLpos)
    obtain ⟨hC, -, -⟩ := abelianAction_props hLeast hFlat ha hL hc u hm
    obtain ⟨hC', -, -⟩ := abelianAction_props hLeast hFlat ha hL hc (u + 1) hn
    obtain ⟨hup, heq⟩ := maxwellForm_step (u := u) hLeast hFlat hGauge hFS ha hL hc hn
    have hsym := (hC.isSymmSndFDerivAt (by simp)).eq
    have hsym' := (hC'.isSymmSndFDerivAt (by simp)).eq
    set W : TorusBond (n * T.L) → ℝ := fun b => responseKernel T.a T.ρA T.L u b c with hW
    set e : TorusBond n → ℝ := bondIndicator c with he
    have h0 := heq c
    simp only [maxwellForm_eq_fderiv hC, maxwellForm_eq_fderiv hC'] at h0 ⊢
    set H := fderiv ℝ (fderiv ℝ (abelianAction T.a T.L u (n * T.L))) 0 with hH
    set H' := fderiv ℝ (fderiv ℝ (abelianAction T.a T.L (u + 1) n)) 0 with hH'
    set m : TorusBond n → ℝ := fun c' => contourMean T.L W c' - e c' with hmdef
    set m' : TorusBond n → ℝ := fun c' => contourMean T.L φ c' - B c' with hm'def
    have key : ∀ ε : ℝ, 0 ≤ 2 * ε * (H W φ + T.a * ∑ c', m c' * m' c' - H' e B) +
        ε ^ 2 * (H φ φ + T.a * ∑ c', m' c' ^ 2 - H' B B) := by
      intro ε
      have h := hup (W + ε • φ) (e + ε • B)
      simp only [maxwellForm_eq_fderiv hC, maxwellForm_eq_fderiv hC'] at h
      have e1 : ∀ c', contourMean T.L (W + ε • φ) c' - (e + ε • B) c' = m c' + ε * m' c' := by
        intro c'
        rw [contourMean_add_smul]
        simp only [hmdef, hm'def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      simp only [e1] at h
      have e2 : ∑ c', (m c' + ε * m' c') ^ 2 =
          ∑ c', m c' ^ 2 + 2 * ε * ∑ c', m c' * m' c' + ε ^ 2 * ∑ c', m' c' ^ 2 := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c' _ => ?_
        ring
      rw [e2] at h
      have e3 : H (W + ε • φ) (W + ε • φ) = H W W + ε * H W φ + ε * H φ W + ε ^ 2 * H φ φ := by
        simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      have e4 : H' (e + ε • B) (e + ε • B) = H' e e + ε * H' e B + ε * H' B e + ε ^ 2 * H' B B := by
        simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      rw [e3, e4, hsym φ W, hsym' B e] at h
      have h0' : H' e e = H W W + T.a * ∑ c', m c' ^ 2 := h0
      rw [h0'] at h
      nlinarith
    have hz := eq_zero_of_quadratic_nonneg key
    linarith
end StepPolarity
end YangMills.Construction
end
