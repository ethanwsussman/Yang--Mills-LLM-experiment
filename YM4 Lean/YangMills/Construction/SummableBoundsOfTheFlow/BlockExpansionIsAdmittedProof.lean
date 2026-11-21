import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsBetweenCompare
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionIsAdmitted
import YangMills.Construction.SummableBoundsOfTheFlow.DistancesOfOffsets
import YangMills.Construction.SummableBoundsOfTheFlow.JointSmoothnessFromMoves
import YangMills.Construction.SummableBoundsOfTheFlow.SitesOfACellAreFew
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceGoesUpALevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Interpolation TorusComparison Estimates ConvexObservables
  CellCounting SummableBounds FamilyNorms
namespace TorusComparison
namespace BlockExpansionAdmissibility
section Law
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private structure CutoffLaw (ρ : ℝ) (p : ℝ → ℝ) (x c : ℝ) (Φ : BondField ι → ℝ) (μ : Measure (BondField ι)) : Prop where
  isProbability : IsProbabilityMeasure μ
  expectation_eq : ∀ f : BondField ι → ℝ, ballExpectation (cutoffFactor ρ p) Φ f = ∫ η, f η ∂μ
  integrable_iff : ∀ f : BondField ι → ℝ,
    Integrable f μ ↔ Integrable fun η => f η * ballDensity (cutoffFactor ρ p) Φ η
  ae_ball : ∀ᵐ η ∂μ, ∀ b, ‖η b‖ < ρ
  moment_le : ∀ b, ∫ η, ‖η b‖ ^ 2 ∂μ ≤ c / x
omit [DecidableEq ι] in
private theorem isOpen_ball_set (ρ : ℝ) : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
abbrev _root_.YangMills.DeltaSharedProofs.p3020 := @isOpen_ball_set
abbrev _root_.YangMills.SharedProofs.p3058 := @isOpen_ball_set
private theorem cutoffLaw_exists (hLaw : normalizedBallLawIsProbabilityStatement) {ρ x lam κ C C' : ℝ} {p : ℝ → ℝ}
    {Cq : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {d : ι → ι → ℝ} {Φ : BondField ι → ℝ} (hρ : 0 < ρ) (hcut : IsCutoff ρ p)
    (hconv : HasUniformlyConvexLaw ρ lam x κ C d Φ) (hm : LawMomentBounds ρ x κ C' p Cq Cr d Φ) :
    ∃ μ, CutoffLaw ρ p x (Cq 1) Φ μ := by
  obtain ⟨Ψ', K', hΨ', hconvex, -, -⟩ := hconv
  obtain ⟨h1, h2, h3, h4, -, -, -, -, -, hnz, -⟩ := hLaw ι ρ p Ψ' hρ hcut hconvex.smooth.continuous
  have hdens : ballDensity (cutoffFactor ρ p) Φ = ballDensity (cutoffFactor ρ p) Ψ' := by
    funext η
    by_cases hη' : ∀ b, ‖η b‖ < ρ
    · unfold ballDensity
      rw [hΨ' η hη']
    · have h0 : ballDensity (cutoffFactor ρ p) Ψ' η = 0 := by
        by_contra hne
        exact hη' ((hnz η).1 hne)
      have h1 : radialWeightProd (cutoffFactor ρ p) η = 0 := by
        unfold ballDensity at h0
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · exact absurd h (Real.exp_pos _).ne'
      rw [h0]
      unfold ballDensity
      rw [h1, zero_mul]
  have hmean : ∀ f : BondField ι → ℝ,
      ballExpectation (cutoffFactor ρ p) Φ f = ballExpectation (cutoffFactor ρ p) Ψ' f := by
    intro f
    unfold ballExpectation
    rw [hdens]
  refine ⟨normalizedBallLaw (cutoffFactor ρ p) Ψ', h1, fun f => by rw [hmean, h2], fun f => by rw [hdens]; exact h3 f, h4,
    fun b => ?_⟩
  have := hm.moments 1 b
  rw [hmean, ← h2] at this
  simpa [div_eq_mul_inv] using this
variable {ρ x c : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ} {μ : Measure (BondField ι)}
omit [DecidableEq ι] in
private theorem CutoffLaw.aestronglyMeasurable (h : CutoffLaw ρ p x c Φ μ) {H : BondField ι → ℝ}
    (hH : ContinuousOn H {η | ∀ b, ‖η b‖ < ρ}) : AEStronglyMeasurable H μ := by
  have hμ : μ.restrict {η | ∀ b, ‖η b‖ < ρ} = μ := Measure.restrict_eq_self_of_ae_mem h.ae_ball
  rw [← hμ]
  exact hH.aestronglyMeasurable (isOpen_ball_set ρ).measurableSet
private theorem CutoffLaw.integrable_of_bound (h : CutoffLaw ρ p x c Φ μ) {H : BondField ι → ℝ}
    (hH : ContinuousOn H {η | ∀ b, ‖η b‖ < ρ}) {M : ℝ} (hM : ∀ η, (∀ b, ‖η b‖ < ρ) → |H η| ≤ M) : Integrable H μ := by
  have := h.isProbability
  exact Integrable.of_bound (h.aestronglyMeasurable hH) M (h.ae_ball.mono fun η hη => by simpa using hM η hη)
private theorem CutoffLaw.momentBound_two (h : CutoffLaw ρ p x c Φ μ) {H G : BondField ι → ℝ} {B : ℝ}
    (hH : ContinuousOn H {η | ∀ b, ‖η b‖ < ρ}) {M : ℝ} (hM : ∀ η, (∀ b, ‖η b‖ < ρ) → |H η| ≤ M)
    (hG : Integrable G μ) (hHG : ∀ η, (∀ b, ‖η b‖ < ρ) → |H η| ^ 2 ≤ G η) (hB : ∫ η, G η ∂μ ≤ B ^ 2) :
    MomentBound (cutoffFactor ρ p) Φ H 2 B := by
  have hc2 : ContinuousOn (fun η => |H η| ^ 2) {η | ∀ b, ‖η b‖ < ρ} := (continuous_abs.comp_continuousOn hH).pow 2
  have hb2 : ∀ η, (∀ b, ‖η b‖ < ρ) → |(fun η => |H η| ^ 2) η| ≤ M ^ 2 := fun η hη => by
    have := hM η hη
    have h0 := abs_nonneg (H η)
    simp only [abs_pow, abs_abs]
    exact pow_le_pow_left₀ h0 this 2
  have hi := h.integrable_of_bound hc2 hb2
  refine ⟨(h.integrable_iff _).1 hi, ?_⟩
  rw [h.expectation_eq]
  exact (integral_mono_ae hi hG (h.ae_ball.mono fun η hη => hHG η hη)).trans hB
end Law
section Extension
variable {F : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem extendByZero_apply_mem {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j)
    {Λ : Finset ι} {i : ι} (hi : i ∈ Λ) (ζ : BondField ι) : _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ (j i) = ζ i := by
  unfold _root_.YangMills.Construction.Interpolation.extendByZero
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hne
    rw [if_neg fun h => hne (hj h)]
  · intro h
    exact absurd hi h
abbrev _root_.YangMills.SharedProofs.p25945 := @extendByZero_apply_mem
private theorem extendByZero_apply_not_mem {j : ι → ↥(chordBonds (finiteCells F))} {Λ : Finset ι} (ζ : BondField ι)
    {b : ↥(chordBonds (finiteCells F))} (hb : ∀ i ∈ Λ, j i ≠ b) : _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b = 0 :=
  Finset.sum_eq_zero fun i hi => if_neg (hb i hi)
private theorem extendByZero_cases {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (Λ : Finset ι)
    (ζ : BondField ι) (b : ↥(chordBonds (finiteCells F))) :
    _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b = 0 ∨ ∃ i, _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b = ζ i := by
  by_cases h : ∃ i ∈ Λ, j i = b
  · obtain ⟨i, hi, rfl⟩ := h
    exact Or.inr ⟨i, extendByZero_apply_mem hj hi ζ⟩
  · push Not at h
    exact Or.inl (extendByZero_apply_not_mem ζ h)
private theorem norm_extendByZero_lt {ρ : ℝ} (hρ : 0 < ρ) {j : ι → ↥(chordBonds (finiteCells F))}
    (hj : Function.Injective j) (Λ : Finset ι) {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < ρ)
    (b : ↥(chordBonds (finiteCells F))) : ‖_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b‖ < ρ := by
  rcases extendByZero_cases hj Λ ζ b with h | ⟨i, h⟩
  · rw [h]
    simpa using hρ
  · rw [h]
    exact hζ i
abbrev _root_.YangMills.SharedProofs.p22320 := @norm_extendByZero_lt
private theorem extendByZero_id_univ (η : StepVariable (finiteCells F)) : _root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ η = η := by apply _root_.YangMills.Construction.InterpolatedBirths.extendByZero_id <;> assumption
private def extendByZeroCLM (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι) :
    BondField ι →L[ℝ] StepVariable (finiteCells F) :=
  ContinuousLinearMap.pi fun b => ∑ i ∈ Λ, if j i = b then
    (ContinuousLinearMap.proj i : BondField ι →L[ℝ] BondVector) else 0
private theorem extendByZeroCLM_apply (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι) (ζ : BondField ι) :
    extendByZeroCLM j Λ ζ = _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ := by
  funext b
  simp only [extendByZeroCLM, ContinuousLinearMap.coe_pi', sum_apply, _root_.YangMills.Construction.Interpolation.extendByZero]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp
private theorem abs_fderiv_single_le {κ' : Type} [Fintype κ'] [DecidableEq κ'] (A : BondField κ' → ℝ)
    (η : BondField κ') (b : κ') (e : BondVector) : |fderiv ℝ A η (Pi.single b e)| ≤ bondGradNorm A b η * ‖e‖ :=
  ((fderiv ℝ A η).comp (ContinuousLinearMap.single ℝ (fun _ : κ' => BondVector) b)).le_opNorm e
private theorem bondGradNorm_comp_extendByZero_le {A : StepVariable (finiteCells F) → ℝ}
    {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (Λ : Finset ι) {ζ : BondField ι}
    (hd : DifferentiableAt ℝ A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) (i : ι) :
    bondGradNorm (fun ζ => A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) i ζ ≤
      if i ∈ Λ then bondGradNorm A (j i) (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) else 0 := by
  have hf : (fun ζ => A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) = A ∘ extendByZeroCLM j Λ := by
    funext ζ
    simp [extendByZeroCLM_apply]
  have hd' : DifferentiableAt ℝ A (extendByZeroCLM j Λ ζ) := by rwa [extendByZeroCLM_apply]
  have hfd : fderiv ℝ (A ∘ extendByZeroCLM j Λ) ζ =
      (fderiv ℝ A (extendByZeroCLM j Λ ζ)).comp (extendByZeroCLM j Λ) :=
    (hd'.hasFDerivAt.comp ζ (extendByZeroCLM j Λ).hasFDerivAt).fderiv
  unfold bondGradNorm
  rw [hf, hfd, extendByZeroCLM_apply]
  split_ifs with hi
  · refine le_of_eq (congrArg norm ?_)
    refine ContinuousLinearMap.ext fun e => ?_
    show fderiv ℝ A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) (extendByZeroCLM j Λ (Pi.single i e)) =
      fderiv ℝ A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) (Pi.single (j i) e)
    congr 1
    rw [extendByZeroCLM_apply]
    funext b
    by_cases hb : b = j i
    · subst hb
      rw [extendByZero_apply_mem hj hi]
      simp
    · rw [Pi.single_eq_of_ne hb]
      unfold _root_.YangMills.Construction.Interpolation.extendByZero
      refine Finset.sum_eq_zero fun i' _ => ?_
      split_ifs with h
      · have : i' ≠ i := fun e => hb (by rw [← h, e])
        rw [Pi.single_apply, if_neg this]
      · rfl
  · have : ((fderiv ℝ A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)).comp (extendByZeroCLM j Λ)).comp
        (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) i) = 0 := by
      refine ContinuousLinearMap.ext fun e => ?_
      show fderiv ℝ A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) (extendByZeroCLM j Λ (Pi.single i e)) = 0
      have h0 : extendByZeroCLM j Λ (Pi.single i e) = 0 := by
        rw [extendByZeroCLM_apply]
        funext b
        unfold _root_.YangMills.Construction.Interpolation.extendByZero
        refine Finset.sum_eq_zero fun i' hi' => ?_
        split_ifs with h
        · have : i' ≠ i := fun e => hi (e ▸ hi')
          rw [Pi.single_apply, if_neg this]
        · rfl
      rw [h0, map_zero]
    rw [this, norm_zero]
abbrev _root_.YangMills.SharedProofs.p25557 := @bondGradNorm_comp_extendByZero_le
end Extension
section DecayingGradient
variable {F : BlockFrame}
private structure IsDecayingGradient (ρ κ g M : ℝ) (Y : F.Cell) (A : StepVariable (finiteCells F) → ℝ) : Prop where
  smooth : ContDiffOn ℝ 1 A {η | ∀ b, ‖η b‖ < ρ}
  bounded : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → |A η| ≤ M
  slope : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → ∀ b : ↥(chordBonds (finiteCells F)),
    bondGradNorm A b η ≤ g * Real.exp (-(2 ^ 5 * κ * bondDistToCell Y b))
private theorem decayingGradient_differentiableAt {ρ κ g M : ℝ} {Y : F.Cell} {A : StepVariable (finiteCells F) → ℝ}
    (hA : IsDecayingGradient ρ κ g M Y A) {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < ρ) :
    DifferentiableAt ℝ A η :=
  (hA.smooth.contDiffAt ((isOpen_ball_set ρ).mem_nhds hη)).differentiableAt one_ne_zero
private theorem decayingGradient_sub_freeze_le {ρ κ g M : ℝ} {Y : F.Cell} {A : StepVariable (finiteCells F) → ℝ}
    (hA : IsDecayingGradient ρ κ g M Y A) (Λ : Finset ↥(chordBonds (finiteCells F)))
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < ρ) :
    |A η - A (_root_.YangMills.Construction.Interpolation.extendByZero id Λ η)| ≤ ∑ b, if b ∈ Λ then 0 else
      g * Real.exp (-(2 ^ 5 * κ * bondDistToCell Y b)) * ‖η b‖ := by
  classical
  set P := _root_.YangMills.Construction.Interpolation.extendByZero id Λ η with hP
  set u := η - P with hu
  have hPin : ∀ b ∈ Λ, P b = η b := fun b hb => extendByZero_apply_mem Function.injective_id hb η
  have hPout : ∀ b, b ∉ Λ → P b = 0 := fun b hb => extendByZero_apply_not_mem η fun i hi h => hb (h ▸ hi)
  have hcomp : ∀ v : ℝ, v ∈ Set.Icc (0 : ℝ) 1 → ∀ b, ‖(P + v • u) b‖ ≤ ‖η b‖ := by
    intro v hv b
    by_cases hb : b ∈ Λ
    · simp [hu, hPin b hb]
    · simp only [hu, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, hPout b hb, sub_zero, zero_add, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hv.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hv.2
  have hball : ∀ v : ℝ, v ∈ Set.Icc (0 : ℝ) 1 → ∀ b, ‖(P + v • u) b‖ < ρ := fun v hv b =>
    (hcomp v hv b).trans_lt (hη b)
  have hder : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => A (P + v • u)) (fderiv ℝ A (P + v • u) ((1 : ℝ) • u)) v := by
    intro v hv
    have h1 : HasDerivAt (fun v : ℝ => P + v • u) ((1 : ℝ) • u) v := ((hasDerivAt_id v).smul_const u).const_add P
    exact (decayingGradient_differentiableAt hA (hball v hv)).hasFDerivAt.comp_hasDerivAt v h1
  have hbound : ∀ v ∈ Set.Ico (0 : ℝ) 1, ‖fderiv ℝ A (P + v • u) ((1 : ℝ) • u)‖ ≤ ∑ b, if b ∈ Λ then 0 else
      g * Real.exp (-(2 ^ 5 * κ * bondDistToCell Y b)) * ‖η b‖ := by
    intro v hv
    have hv' : v ∈ Set.Icc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
    rw [one_smul, Real.norm_eq_abs]
    have esum : fderiv ℝ A (P + v • u) u = ∑ b, fderiv ℝ A (P + v • u) (Pi.single b (u b)) := by
      rw [← map_sum, Finset.univ_sum_single]
    rw [esum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    refine (abs_fderiv_single_le A _ b (u b)).trans ?_
    have hs := hA.slope (P + v • u) (hball v hv') b
    by_cases hb : b ∈ Λ
    · have : u b = 0 := by simp [hu, hPin b hb]
      simp [this, hb]
    · have : u b = η b := by simp [hu, hPout b hb]
      rw [if_neg hb, this]
      exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (fun v hv => (hder v hv).hasDerivWithinAt) hbound
  simp only [one_smul, zero_smul, add_zero, hu, add_sub_cancel, Real.norm_eq_abs] at this
  exact this
end DecayingGradient
section Gradients
variable {F : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {ρ x c : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ}
  {μ : Measure (BondField ι)}
omit [DecidableEq ι] in
private theorem CutoffLaw.mono (h : CutoffLaw ρ p x c Φ μ) {c' : ℝ} (hc : c ≤ c') (hx : 0 < x) :
    CutoffLaw ρ p x c' Φ μ :=
  ⟨h.isProbability, h.expectation_eq, h.integrable_iff, h.ae_ball,
    fun b => (h.moment_le b).trans (div_le_div_of_nonneg_right hc hx.le)⟩
private theorem CutoffLaw.integrable_norm_sq (h : CutoffLaw ρ p x c Φ μ) (i : ι) :
    Integrable (fun η : BondField ι => ‖η i‖ ^ 2) μ := by
  refine h.integrable_of_bound (M := ρ ^ 2) ((continuous_norm.comp (continuous_apply i)).pow 2).continuousOn
    fun η hη => ?_
  rw [abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hη i).le 2
omit [DecidableEq ι] in
private theorem CutoffLaw.abs_integral_le (h : CutoffLaw ρ p x c Φ μ) {H : BondField ι → ℝ} {B : ℝ}
    (hB : ∀ η, (∀ b, ‖η b‖ < ρ) → |H η| ≤ B) : |∫ η, H η ∂μ| ≤ B := by
  have hprob := h.isProbability
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := H) (C := B)
    (h.ae_ball.mono fun η hη => by simpa using hB η hη)
  simpa using this
private theorem bondGradNorm_continuousOn {κ' : Type} [Fintype κ'] [DecidableEq κ'] {H : BondField κ' → ℝ} {ρ : ℝ}
    (hH : ContDiffOn ℝ 1 H {η | ∀ b, ‖η b‖ < ρ}) (b : κ') :
    ContinuousOn (bondGradNorm H b) {η | ∀ b, ‖η b‖ < ρ} := by
  have h1 := hH.continuousOn_fderiv_of_isOpen (isOpen_ball_set ρ) le_rfl
  exact (h1.clm_comp continuousOn_const).norm
private theorem hasGradientBound_of_decaying (h : CutoffLaw ρ p x c Φ μ) (hρ : 0 < ρ) (hx : 1 ≤ x) {κ g M : ℝ}
    (hκ : 0 ≤ κ) (hg : 0 ≤ g) {Y : F.Cell} {A : StepVariable (finiteCells F) → ℝ}
    (hA : IsDecayingGradient ρ κ g M Y A) {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j)
    (Λ : Finset ι) {dZ : ι → ℝ} (hd : ∀ i, dZ i = bondDistToCell Y (j i)) {hh : ℝ} (hgh : g ≤ hh) :
    HasGradientBound ρ (cutoffFactor ρ p) Φ x κ hh dZ (fun ζ => A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) := by
  set H : BondField ι → ℝ := fun ζ => A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) with hHdef
  have hball : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → ∀ b, ‖_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b‖ < ρ :=
    fun ζ hζ => norm_extendByZero_lt hρ hj Λ hζ
  have hHc : ContDiffOn ℝ 1 H {η | ∀ b, ‖η b‖ < ρ} := by
    have e : H = A ∘ extendByZeroCLM j Λ := by
      funext ζ
      simp [hHdef, extendByZeroCLM_apply]
    rw [e]
    refine hA.smooth.comp (extendByZeroCLM j Λ).contDiff.contDiffOn fun ζ hζ => ?_
    show ∀ b, ‖extendByZeroCLM j Λ ζ b‖ < ρ
    rw [extendByZeroCLM_apply]
    exact hball ζ hζ
  have hHb : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → |H ζ| ≤ M := fun ζ hζ => hA.bounded _ (hball ζ hζ)
  have hdist : ∀ i, 0 ≤ dZ i := fun i => by
    rw [hd]
    exact Nat.cast_nonneg _
  have hpn : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → ∀ i,
      bondGradNorm H i ζ ≤ g * Real.exp (-(2 * κ * dZ i)) := by
    intro ζ hζ i
    have hdiff := decayingGradient_differentiableAt hA (hball ζ hζ)
    refine (bondGradNorm_comp_extendByZero_le hj Λ hdiff i).trans ?_
    split_ifs with hi
    · refine (hA.slope _ (hball ζ hζ) (j i)).trans (mul_le_mul_of_nonneg_left ?_ hg)
      rw [Real.exp_le_exp, hd i]
      have h1 : 0 ≤ κ * bondDistToCell Y (j i) := mul_nonneg hκ (Nat.cast_nonneg _)
      nlinarith
    · positivity
  have hpn0 : ∀ ζ i, 0 ≤ bondGradNorm H i ζ := fun ζ i => norm_nonneg _
  have hbig' : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → ∀ i, |bondGradNorm H i ζ| ≤ g := by
    intro ζ hζ i
    rw [abs_of_nonneg (hpn0 ζ i)]
    refine (hpn ζ hζ i).trans (mul_le_of_le_one_right hg ?_)
    rw [Real.exp_le_one_iff]
    have := mul_nonneg hκ (hdist i)
    linarith
  refine ⟨fun ζ hζ => ?_, fun k hk => ⟨?_, fun i => ?_⟩, fun i => ?_⟩
  · exact (hHc.contDiffAt ((isOpen_ball_set ρ).mem_nhds hζ)).differentiableAt one_ne_zero
  · refine (h.integrable_iff _).1 (h.integrable_of_bound (M := M ^ k) ?_ ?_)
    · exact (continuous_abs.comp_continuousOn hHc.continuousOn).pow k
    · intro ζ hζ
      simp only [abs_pow, abs_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hHb ζ hζ) k
  · refine (h.integrable_iff _).1 (h.integrable_of_bound (M := g ^ k) ?_ ?_)
    · exact (continuous_abs.comp_continuousOn (bondGradNorm_continuousOn hHc i)).pow k
    · intro ζ hζ
      simp only [abs_pow, abs_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbig' ζ hζ i) k
  · set E : ℝ := Real.exp (-(2 * κ * dZ i)) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hprob := h.isProbability
    refine h.momentBound_two (G := fun _ => (g * E) ^ 2) (bondGradNorm_continuousOn hHc i) (hbig' · · i)
      (integrable_const _) ?_ ?_
    · intro ζ hζ
      rw [sq_abs]
      exact pow_le_pow_left₀ (hpn0 ζ i) (hpn ζ hζ i) 2
    · have hs : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
      have h1 : g ≤ Real.sqrt x * hh := by nlinarith
      have h2 : g * E ≤ Real.sqrt x * hh * E := mul_le_mul_of_nonneg_right h1 hE0.le
      have e : ∫ _ : BondField ι, (g * E) ^ 2 ∂μ = (g * E) ^ 2 := by simp
      rw [e]
      exact pow_le_pow_left₀ (by positivity) h2 2
end Gradients
section Laws
variable {F F' : BlockFrame} {T : StepParameters} {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {t : ℕ} {x : ℝ}
private theorem integrable_mul_radialWeightProd (hLaw : normalizedBallLawIsProbabilityStatement) {ι : Type} [Fintype ι]
    [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hcut : IsCutoff ρ p) {H : BondField ι → ℝ}
    (hH : ContinuousOn H {η | ∀ b, ‖η b‖ < ρ}) {M : ℝ} (hM : ∀ η, (∀ b, ‖η b‖ < ρ) → |H η| ≤ M) :
    Integrable fun η => H η * radialWeightProd (cutoffFactor ρ p) η := by
  obtain ⟨h1, -, h3, h4, -⟩ := hLaw ι ρ p (fun _ => 0) hρ hcut continuous_const
  have hμ : (normalizedBallLaw (cutoffFactor ρ p) fun _ : BondField ι => (0 : ℝ)).restrict {η | ∀ b, ‖η b‖ < ρ} =
      normalizedBallLaw (cutoffFactor ρ p) fun _ : BondField ι => (0 : ℝ) := Measure.restrict_eq_self_of_ae_mem h4
  have ha : AEStronglyMeasurable H (normalizedBallLaw (cutoffFactor ρ p) fun _ : BondField ι => (0 : ℝ)) := by
    rw [← hμ]
    exact hH.aestronglyMeasurable (isOpen_ball_set ρ).measurableSet
  have hi := (h3 H).1 (Integrable.of_bound ha M (h4.mono fun η hη => by simpa using hM η hη))
  simpa [ballDensity] using hi
abbrev _root_.YangMills.SharedProofs.p23182 := @integrable_mul_radialWeightProd
private theorem cutoffLaw_freezing (hLaw : normalizedBallLawIsProbabilityStatement) (hρ : 0 < T.ballRadius)
    (hcut : IsCutoff T.ballRadius T.p) (FB : InterpolatedFrameBoundsAt T Cq Cz Cr t x) {V : F.GaugeField F.top}
    (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    {Ψ : StepVariable (finiteCells F) → ℝ}
    (hlaw : IsIntermediateLaw T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x)
      (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V Ψ)
    (Λ : Finset ↥(chordBonds (finiteCells F))) {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    ∃ μ, CutoffLaw T.ballRadius T.p x (Cq 1) (freezingHomotopy T.chainParams.lam x Λ Ψ v) μ := by
  let d : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ :=
    fun i i' => cellSupDist (enclosingCell i.1.1) (enclosingCell i'.1.1)
  let M : Fin 2 → LawOnBondVariables ↥(chordBonds (finiteCells F)) :=
    ![⟨F, V, id, Finset.univ, Ψ⟩, ⟨F, V, id, Λ, Ψ⟩]
  have hw : IsConvexWeights ![v, 1 - v] := by
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simpa using h0
      · simpa using h1
    · simp
  have hM : ∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t
      T.n₀ (frameRadius x) d := by
    intro l
    fin_cases l
    · exact ⟨hF, hV, hlaw, Function.injective_id, fun _ _ => rfl⟩
    · exact ⟨hF, hV, hlaw, Function.injective_id, fun _ _ => rfl⟩
  obtain ⟨hc, hm, -⟩ := FB.laws _ d 2 ![v, 1 - v] M hw hM
  have e : convexCombinationExponent T.chainParams.lam x ![v, 1 - v] M =
      freezingHomotopy T.chainParams.lam x Λ Ψ v := by
    funext η
    have h1 : frozenExponent T.chainParams.lam x id Finset.univ Ψ η = Ψ η := by
      unfold frozenExponent
      rw [extendByZero_id_univ]
      simp
    show ∑ l, ![v, 1 - v] l * (M l).exponent T.chainParams.lam x η =
      v * Ψ η + (1 - v) * frozenExponent T.chainParams.lam x id Λ Ψ η
    rw [Fin.sum_univ_two]
    show v * frozenExponent T.chainParams.lam x id Finset.univ Ψ η +
      (1 - v) * frozenExponent T.chainParams.lam x id Λ Ψ η = _
    rw [h1]
  rw [e] at hc hm
  exact cutoffLaw_exists hLaw hρ hcut hc hm
private theorem cutoffLaw_pairing (hLaw : normalizedBallLawIsProbabilityStatement) (hρ : 0 < T.ballRadius)
    (hcut : IsCutoff T.ballRadius T.p) (FB : InterpolatedFrameBoundsAt T Cq Cz Cr t x) {V : F.GaugeField F.top}
    {V' : F'.GaugeField F'.top} (hF : IsCubicTopTorus T.L t T.n₀ F) (hF' : IsCubicTopTorus T.L t T.n₀ F')
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hV' : IsSmallCurvature (5 / 4 * T.σ) V')
    {Ψ : StepVariable (finiteCells F) → ℝ} {Ψ' : StepVariable (finiteCells F') → ℝ}
    (hlaw : IsIntermediateLaw T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x)
      (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V Ψ)
    (hlaw' : IsIntermediateLaw T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x)
      (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V' Ψ')
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {j : ι → ↥(chordBonds (finiteCells F))} {j' : ι → ↥(chordBonds (finiteCells F'))} (hj : Function.Injective j)
    (hj' : Function.Injective j')
    (hdist : ∀ i i', cellSupDist (enclosingCell (j i).1.1) (enclosingCell (j i').1.1) =
      cellSupDist (enclosingCell (j' i).1.1) (enclosingCell (j' i').1.1))
    {th : ℝ} (h0 : 0 ≤ th) (h1 : th ≤ 1) :
    ∃ μ, CutoffLaw T.ballRadius T.p x (Cq 1) (pairingHomotopy j j' Ψ Ψ' th) μ := by
  let d : ι → ι → ℝ := fun i i' => cellSupDist (enclosingCell (j i).1.1) (enclosingCell (j i').1.1)
  let M : Fin 2 → LawOnBondVariables ι := ![⟨F, V, j, Finset.univ, Ψ⟩, ⟨F', V', j', Finset.univ, Ψ'⟩]
  have hw : IsConvexWeights ![th, 1 - th] := by
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simpa using h0
      · simpa using h1
    · simp
  have hM : ∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t
      T.n₀ (frameRadius x) d := by
    intro l
    fin_cases l
    · exact ⟨hF, hV, hlaw, hj, fun _ _ => rfl⟩
    · exact ⟨hF', hV', hlaw', hj', fun i i' => by
        show (cellSupDist (enclosingCell (j i).1.1) (enclosingCell (j i').1.1) : ℝ) = _
        rw [hdist i i']
        rfl⟩
  obtain ⟨hc, hm, -⟩ := FB.laws _ d 2 ![th, 1 - th] M hw hM
  have e : convexCombinationExponent T.chainParams.lam x ![th, 1 - th] M = pairingHomotopy j j' Ψ Ψ' th := by
    funext η
    simp [convexCombinationExponent, Fin.sum_univ_two, M, LawOnBondVariables.exponent, pairingHomotopy,
      frozenExponent, toTorus]
  rw [e] at hc hm
  exact cutoffLaw_exists hLaw hρ hcut hc hm
private theorem shortPairing_distances (hOff : cellOffsetStatement) {q : ℕ} {Y : F.Cell} {Y' : F'.Cell} {ι : Type}
    {j : ι → ↥(chordBonds (finiteCells F))} {j' : ι → ↥(chordBonds (finiteCells F'))} (hL : Odd F.blockSide)
    (hL' : F'.blockSide = F.blockSide) (hs : ∀ i, 2 * q + 2 < F.extent i) (hs' : ∀ i, 2 * q + 2 < F'.extent i)
    (hp : IsShortPairing Y Y' q j j') :
    (∀ i i', cellSupDist (enclosingCell (j i).1.1) (enclosingCell (j i').1.1) =
      cellSupDist (enclosingCell (j' i).1.1) (enclosingCell (j' i').1.1)) ∧
    ∀ i, bondDistToCell Y (j i) = bondDistToCell Y' (j' i) := by
  have hLo' : Odd F'.blockSide := by rw [hL']; exact hL
  have h2 : ∀ i, 2 ≤ F.extent i := fun i => by have := hs i; omega
  have h2' : ∀ i, 2 ≤ F'.extent i := fun i => by have := hs' i; omega
  obtain ⟨a1, -, -, a4⟩ := hOff F hL h2
  obtain ⟨b1, -, -, b4⟩ := hOff F' hLo' h2'
  have key : ∀ i, ∃ h : Fin 4 → ℤ, (∀ l, 2 * |h l| ≤ q) ∧ enclosingCell (j i).1.1 = Y + siteOfCoords F.top h ∧
      enclosingCell (j' i).1.1 = Y' + siteOfCoords F'.top h := by
    intro i
    obtain ⟨h, o, k, hh, ho, e1, e2⟩ := hp.short_offsets i
    refine ⟨h, hh, ?_, ?_⟩
    · rw [e1]
      exact a1 Y h o k ho
    · rw [e2]
      exact b1 Y' h o k (by rw [hL']; exact ho)
  refine ⟨fun i i' => ?_, fun i => ?_⟩
  · obtain ⟨h, hh, e1, e2⟩ := key i
    obtain ⟨g, hg, g1, g2⟩ := key i'
    rw [e1, e2, g1, g2, (a4 q hs Y h g hh hg).2, (b4 q hs' Y' h g hh hg).2]
  · obtain ⟨h, hh, e1, e2⟩ := key i
    have z : ∀ {G : BlockFrame} (Z : G.Cell), Z + siteOfCoords G.top (0 : Fin 4 → ℤ) = Z := by
      intro G Z
      funext l
      simp [siteOfCoords]
    have hz : ∀ l : Fin 4, 2 * |(0 : Fin 4 → ℤ) l| ≤ (q : ℤ) := fun l => by simp
    unfold bondDistToCell
    rw [e1, e2]
    have c1 := (a4 q hs Y h 0 hh hz).2
    have c2 := (b4 q hs' Y' h 0 hh hz).2
    rw [z] at c1 c2
    rw [c1, c2]
abbrev _root_.YangMills.SharedProofs.p91775 := @shortPairing_distances
end Laws
section OneTorus
variable {F : BlockFrame} {T : StepParameters}
private theorem sum_exp_comp_injective_le {κ : ℝ} {ι : Type} [Fintype ι] [DecidableEq ι] {Y : F.Cell}
    {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) :
    ∑ i, Real.exp (-(κ * bondDistToCell Y (j i))) ≤
      ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(κ * bondDistToCell Y b)) := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := j) (f := fun b => Real.exp (-(κ * bondDistToCell Y b)))
    fun a _ b _ h => hj h]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le
abbrev _root_.YangMills.SharedProofs.p95346 := @sum_exp_comp_injective_le
private theorem exp_rate_le {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 1 ≤ r) (Y : F.Cell) (b : ↥(chordBonds (finiteCells F))) :
    Real.exp (-(r * κ * bondDistToCell Y b)) ≤ Real.exp (-(κ * bondDistToCell Y b)) := by
  rw [Real.exp_le_exp]
  have h1 : 0 ≤ κ * bondDistToCell Y b := mul_nonneg hκ (Nat.cast_nonneg _)
  nlinarith
private theorem sum_exp_outside_le {κ W : ℝ} (hκ : 0 < κ) (Y : F.Cell) (q : ℕ)
    (hW : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(κ * bondDistToCell Y b)) ≤ W) :
    (∑ b : ↥(chordBonds (finiteCells F)), if b ∈ bondsNearCell Y q then (0 : ℝ) else
      Real.exp (-(2 ^ 5 * κ * bondDistToCell Y b))) ≤ Real.exp (-(4 * κ * q)) * W := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hW (Real.exp_pos _).le)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  split_ifs with hb
  · positivity
  · rw [← Real.exp_add, Real.exp_le_exp]
    have hb' : (q : ℝ) < 2 * bondDistToCell Y b := by
      have : ¬ 2 * cellSupDist (enclosingCell b.1.1) Y ≤ q := fun h => hb (by simp [bondsNearCell, h])
      have h2 : q < 2 * cellSupDist (enclosingCell b.1.1) Y := not_le.1 this
      unfold bondDistToCell
      exact_mod_cast h2
    nlinarith [mul_pos hκ (by linarith [Nat.cast_nonneg (α := ℝ) q] : (0 : ℝ) < 2 * bondDistToCell Y b + 1),
      mul_nonneg hκ.le (Nat.cast_nonneg (α := ℝ) q), mul_le_mul_of_nonneg_left hb'.le hκ.le,
      mul_nonneg hκ.le (Nat.cast_nonneg (α := ℝ) (cellSupDist (enclosingCell b.1.1) Y))]
private theorem comparisonBoundsOnTorus_of (hLaw : normalizedBallLawIsProbabilityStatement) (hρ : 0 < T.ballRadius)
    (hcut : IsCutoff T.ballRadius T.p) (hκ : 0 < T.κ) {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {t : ℕ} {x : ℝ}
    (FB : InterpolatedFrameBoundsAt T Cq Cz Cr t x) (hx : 1 ≤ x) {V : F.GaugeField F.top}
    (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    {Ψ : StepVariable (finiteCells F) → ℝ}
    (hlaw : IsIntermediateLaw T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x)
      (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V Ψ)
    {g M W α : ℝ} (hg : 0 ≤ g) {Y : F.Cell} {A : StepVariable (finiteCells F) → ℝ}
    (hA : IsDecayingGradient T.ballRadius T.κ g M Y A)
    (hW : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(T.κ * bondDistToCell Y b)) ≤ W)
    (hgα : g ≤ α) (hfr : W * T.ballRadius * g ≤ α) (q : ℕ) :
    ComparisonHypothesesOnTorus T.ballRadius T.chainParams.lam x T.κ α T.p q Y Ψ A := by
  have hfc : ∀ Λ : Finset ↥(chordBonds (finiteCells F)),
      ContinuousOn (fun η => A (freezeOutside Λ η)) {η | ∀ b, ‖η b‖ < T.ballRadius} := by
    intro Λ
    have e : (fun η => A (freezeOutside Λ η)) = A ∘ extendByZeroCLM id Λ := by
      funext η
      simp [extendByZeroCLM_apply, freezeOutside]
    rw [e]
    refine hA.smooth.continuousOn.comp (extendByZeroCLM id Λ).continuous.continuousOn fun η hη => ?_
    show ∀ b, ‖extendByZeroCLM id Λ η b‖ < T.ballRadius
    rw [extendByZeroCLM_apply]
    exact norm_extendByZero_lt hρ Function.injective_id Λ hη
  have law : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ∃ μ, CutoffLaw T.ballRadius T.p x (Cq 1)
      (freezingHomotopy T.chainParams.lam x (bondsNearCell Y q) Ψ v) μ :=
    fun v h0 h1 => cutoffLaw_freezing hLaw hρ hcut FB hF hV hlaw (bondsNearCell Y q) h0 h1
  refine ⟨integrable_mul_radialWeightProd hLaw hρ hcut hA.smooth.continuousOn hA.bounded,
    integrable_mul_radialWeightProd hLaw hρ hcut (hfc _)
      (fun η hη => hA.bounded _ (norm_extendByZero_lt hρ Function.injective_id _ hη)),
    fun v h0 h1 => ?_, fun v h0 h1 => ?_, fun v h0 h1 => ?_⟩
  · obtain ⟨μ, hμ⟩ := law v h0 h1
    have := hasGradientBound_of_decaying hμ hρ hx hκ.le hg hA (j := id) Function.injective_id Finset.univ
      (dZ := bondDistToCell Y) (fun _ => rfl) hgα
    simpa only [extendByZero_id_univ] using this
  · obtain ⟨μ, hμ⟩ := law v h0 h1
    exact hasGradientBound_of_decaying hμ hρ hx hκ.le hg hA (j := id) Function.injective_id (bondsNearCell Y q)
      (dZ := bondDistToCell Y) (fun _ => rfl) hgα
  · obtain ⟨μ, hμ⟩ := law v h0 h1
    rw [hμ.expectation_eq]
    have hpt : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        |A η - A (freezeOutside (bondsNearCell Y q) η)| ≤ α * Real.exp (-(4 * T.κ * q)) := by
      intro η hη
      refine (decayingGradient_sub_freeze_le hA (bondsNearCell Y q) hη).trans ?_
      have h1 : (∑ b, if b ∈ bondsNearCell Y q then (0 : ℝ) else
          g * Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b)) * ‖η b‖) ≤
          T.ballRadius * g * ∑ b : ↥(chordBonds (finiteCells F)), if b ∈ bondsNearCell Y q then (0 : ℝ) else
            Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun b _ => ?_
        split_ifs with hb
        · simp
        · have := mul_le_mul_of_nonneg_left (hη b).le
            (mul_nonneg hg (Real.exp_pos (-(2 ^ 5 * T.κ * bondDistToCell Y b))).le)
          linarith
      refine h1.trans ?_
      have h2 := mul_le_mul_of_nonneg_left (sum_exp_outside_le hκ Y q hW) (mul_nonneg hρ.le hg)
      refine h2.trans ?_
      have he := (Real.exp_pos (-(4 * T.κ * q))).le
      have h3 := mul_le_mul_of_nonneg_right hfr he
      nlinarith
    exact hμ.abs_integral_le hpt
private theorem abs_ballExpectation_le (hLaw : normalizedBallLawIsProbabilityStatement) (hρ : 0 < T.ballRadius)
    (hcut : IsCutoff T.ballRadius T.p) {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {t : ℕ} {x : ℝ}
    (FB : InterpolatedFrameBoundsAt T Cq Cz Cr t x) {V : F.GaugeField F.top} (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) {Ψ : StepVariable (finiteCells F) → ℝ}
    (hlaw : IsIntermediateLaw T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x)
      (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V Ψ)
    {κ g M : ℝ} {Y : F.Cell} {A : StepVariable (finiteCells F) → ℝ} (hA : IsDecayingGradient T.ballRadius κ g M Y A) :
    |ballExpectation (cutoffFactor T.ballRadius T.p) Ψ A| ≤ M := by
  obtain ⟨μ, hμ⟩ := cutoffLaw_freezing hLaw hρ hcut FB hF hV hlaw ∅ zero_le_one le_rfl
  have e : freezingHomotopy T.chainParams.lam x ∅ Ψ 1 = Ψ := by
    funext η
    simp [freezingHomotopy]
  rw [e] at hμ
  rw [hμ.expectation_eq]
  exact hμ.abs_integral_le hA.bounded
end OneTorus
section SeriesExpansions
variable {F : BlockFrame}
private theorem bondDeriv_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ}
    (G : F.GaugeField j → E) (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G W c X = G W := by
  have h1 : ∀ τ : Fin 0 → ℝ, leftTranslate (bondSpread c X τ) W = W := by
    intro τ
    funext y i
    have h2 : expUnit (0 : imaginaryQuaternions) = 1 := Subtype.ext (by simp [expUnit, NormedSpace.exp_zero])
    simp [leftTranslate, ColdStepAtMirrorFrames.bondSpread, h2]
  simp only [bondDeriv, iteratedFDeriv_zero_apply, h1]
abbrev _root_.YangMills.SharedProofs.p3568 := @bondDeriv_zero
private theorem leftTranslate_bondSpread_zero {j : ℕ} (c : Fin 0 → F.Site j × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) (τ : Fin 0 → ℝ) (W : F.GaugeField j) :
    leftTranslate (bondSpread c X τ) W = W := by
  have h2 : expUnit (0 : imaginaryQuaternions) = 1 := Subtype.ext (by simp [expUnit, NormedSpace.exp_zero])
  funext y i
  simp [leftTranslate, ColdStepAtMirrorFrames.bondSpread, h2]
private theorem uniformField_isSmallCurvature {j : ℕ} {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (uniformField F j) := by apply _root_.YangMills.SharedProofs.p8038 <;> assumption
private theorem hasBoundedDerivatives_of {L t n₀ : ℕ} {σ δ ε ε₃ : ℝ} {f : LocalFamily}
    (hf : IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ f) :
    HasBoundedDerivatives L t n₀ σ δ 3 (fun j => if j = 3 then ε₃ else ε) f :=
  ⟨fun F hF y W hW j c X => by exact_mod_cast hf.smooth F hF y W hW j c X, hf.gauge_invariant,
    fun F hF y W j c X hW h1 h3 hX => hf.decay F hF y W j c X hW h1 h3 hX⟩
abbrev _root_.YangMills.SharedProofs.p1 := @hasBoundedDerivatives_of
private theorem abs_subtractTrivial_le {L t n₀ : ℕ} {σ δ ε ε₃ : ℝ} {h : LocalFamily} (hσ : 0 < σ)
    (hf : IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ h) (hF : IsCubicTorusAbove L t n₀ F)
    (hper : ∀ i, 2 < F.period F.depth i) (y : F.Site F.depth) {W : F.GaugeField F.depth}
    (hW : IsSmallCurvature σ W) : |subtractTrivial h F y W| ≤ ε := by
  have hag : AgreeOnBox W (uniformField F F.depth) y y 0 := by
    refine ⟨fun i => by simpa using hper i, fun i => by simpa using hper i, fun b hb => ?_⟩
    exfalso
    obtain ⟨h1, h2⟩ := hb
    have a1 := h1 b.2
    have a2 := h2 b.2
    simp only [Pi.add_apply, Pi.single_eq_same, Nat.cast_zero, abs_nonpos_iff] at a1 a2
    omega
  have key := hf.locality F F hF hF y y W (uniformField F F.depth) 0 0 Fin.elim0 Fin.elim0 hW
    (uniformField_isSmallCurvature hσ) hag (by norm_num) (fun l => l.elim0) (fun l => l.elim0)
  rw [bondDeriv_zero, bondDeriv_zero] at key
  have e0 : subtractTrivial h F y (uniformField F F.depth) = 0 := by
    simp [subtractTrivial]
  have e1 : torusDecayFactor L δ ((0 : ℕ) : ℝ) = 1 := by simp [torusDecayFactor]
  rw [e0, sub_zero, e1, div_one] at key
  exact key
private theorem jointMixedDeriv_single {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {η : StepVariable (finiteCells F)} {V : F.GaugeField F.top} (b : ↥(chordBonds (finiteCells F)))
    (u : EuclideanSpace ℝ (Fin 3)) (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions)
    (hd : DifferentiableAt ℝ (fun ζ => G ζ V) η) :
    jointMixedDeriv (l := 1) (j := 0) G η V ![b] ![u] c X = fderiv ℝ (fun ζ => G ζ V) η (Pi.single b u) := by
  classical
  let Lm : (Fin 1 → ℝ) →L[ℝ] StepVariable (finiteCells F) :=
    (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => EuclideanSpace ℝ (Fin 3)) b).comp
      ((ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ).smulRight u)
  have e : jointDisplacement G η V ![b] ![u] c X = fun τ : Fin 1 → ℝ => (fun ζ => G ζ V) (η + Lm τ) := by
    funext τ
    simp only [jointDisplacement, displacedPoint, leftTranslate_bondSpread_zero]
    congr 1
    simp [Lm]
    funext β
    by_cases hb : β = b
    · subst hb
      simp
    · simp [Pi.single_eq_of_ne hb]
  have h0 : HasFDerivAt (fun τ : Fin 1 → ℝ => η + Lm τ) Lm 0 := Lm.hasFDerivAt.const_add η
  have h1 : HasFDerivAt (fun ζ => G ζ V) (fderiv ℝ (fun ζ => G ζ V) η) (η + Lm 0) := by
    rw [map_zero, add_zero]
    exact hd.hasFDerivAt
  have h2 := h1.comp (0 : Fin 1 → ℝ) h0
  unfold jointMixedDeriv
  rw [e]
  show iteratedFDeriv ℝ 1 _ 0 _ = _
  rw [iteratedFDeriv_one_apply]
  have h3 : fderiv ℝ (fun τ : Fin 1 → ℝ => (fun ζ => G ζ V) (η + Lm τ)) 0 =
      (fderiv ℝ (fun ζ => G ζ V) η).comp Lm := h2.fderiv
  rw [h3]
  show fderiv ℝ (fun ζ => G ζ V) η (Lm (Pi.single 0 1)) = _
  congr 1
  simp [Lm]
private theorem cellSupDist_le_diameter (u v : F.Cell) (P : Finset F.Cell) (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by
  unfold cellSetDiameter
  exact (Finset.le_sup (f := fun v' => cellSupDist u v') hv).trans
    (Finset.le_sup (f := fun u' => P.sup fun v' => cellSupDist u' v') hu)
variable {T : StepParameters} {C : ℝ} {Ck : ℕ → ℝ} {t : ℕ} {x s ε ε₃ : ℝ} {h : LocalFamily} {V : F.GaugeField F.top}
private theorem isTransportBounded_of (hTr : TransportBoundsAt T C Ck) (hx : T.coupling ≤ x) (hε : 0 ≤ ε)
    (hε₃ : 0 ≤ ε₃) (hf : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε ε₃ h)
    (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ T.ballRadius) :
    IsTransportBounded s T.a T.chainParams.ρA T.κ T.decayRate C Ck T.L (frameRadius x) 3
      (fun j => if j = 3 then ε₃ else ε) h V η :=
  hTr x t 3 _ h F V s η hx le_rfl (by norm_num) (fun j => by
    show 0 ≤ if j = 3 then ε₃ else ε
    split_ifs <;> assumption) (hasBoundedDerivatives_of hf) hF hV hs0 hs1 hη
private theorem interpolatedExpansion_contDiffAt (hJS : JointlyContDiffOnBallsOfDisplacements)
    (hTr : TransportBoundsAt T C Ck) (hx : T.coupling ≤ x) (hε : 0 ≤ ε) (hε₃ : 0 ≤ ε₃)
    (hf : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε ε₃ h) (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (y : F.Site F.depth)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ T.ballRadius) :
    ContDiffAt ℝ 3 (fun ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V) η := by
  have hj := hJS F T.ballRadius V (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y)
    (fun ζ hζ l j b u c X hu hX => by
      exact_mod_cast (isTransportBounded_of hTr hx hε hε₃ hf hF hV hs0 hs1 hζ).smooth y l j b u c X hu hX)
  have h0 := hj 0 Fin.elim0 Fin.elim0 η hη
  have hl : ContDiffAt ℝ 3 (fun ζ : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), ζ)) η :=
    contDiffAt_const.prodMk contDiffAt_id
  have h2 := ContDiffAt.comp (f := fun ζ : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), ζ)) η h0 hl
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [Function.comp, leftTranslate_bondSpread_zero]
private theorem abs_fderiv_interpolatedExpansion_le (hJS : JointlyContDiffOnBallsOfDisplacements)
    (hTr : TransportBoundsAt T C Ck) (hx : T.coupling ≤ x) (hε : 0 ≤ ε) (hε₃ : 0 ≤ ε₃)
    (hf : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε ε₃ h) (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (y : F.Site F.depth)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ T.ballRadius) (b : ↥(chordBonds (finiteCells F)))
    (u : EuclideanSpace ℝ (Fin 3)) (hu : ‖u‖ = 1) (hC : 0 ≤ C) (hκ : 0 ≤ T.κ) :
    |fderiv ℝ (fun ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V) η (Pi.single b u)| ≤
      C * ε * Real.exp (-(2 ^ 7 * T.κ * cellSupDist (enclosingCell b.1.1) (enclosingCell y))) := by
  have hd : DifferentiableAt ℝ (fun ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V) η :=
    (interpolatedExpansion_contDiffAt hJS hTr hx hε hε₃ hf hF hV hs0 hs1 y hη).differentiableAt (by norm_num)
  have tr := isTransportBounded_of hTr hx hε hε₃ hf hF hV hs0 hs1 hη
  have g := tr.jointDeriv_le y 1 0 ![b] ![u] Fin.elim0 Fin.elim0 (by omega) (by omega)
    (fun i => by fin_cases i; exact hu) (fun l => l.elim0)
  rw [jointMixedDeriv_single b u _ _ hd] at g
  have e1 : runningMax (fun j => if j = 3 then ε₃ else ε) (1 + 0) = ε := by
    simp [runningMax, hε]
  rw [e1] at g
  refine g.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC hε))
  rw [Real.exp_le_exp, neg_le_neg_iff]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h3 : cellSupDist (enclosingCell b.1.1) (enclosingCell y) ≤
      cellSetDiameter (insert (enclosingCell y) (chordBondCells ![b] ∪
        topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) :=
    cellSupDist_le_diameter _ _ _ (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩))) (Finset.mem_insert_self _ _)
  exact_mod_cast h3
private theorem sum_interpolatedExpansion_decaying (hJS : JointlyContDiffOnBallsOfDisplacements)
    (hTr : TransportBoundsAt T C Ck) (hx : T.coupling ≤ x) (hε : 0 ≤ ε) (hε₃ : 0 ≤ ε₃)
    (hf : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε ε₃ h) (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hC : 0 ≤ C) (hκ : 0 ≤ T.κ) {N : ℝ}
    (hσ : 0 < T.σ)
    (hcold : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
      IsSmallCurvature T.σ (interpolatedField s T.a T.chainParams.ρA (frameRadius x) V η))
    (hper : ∀ i, 2 < F.period F.depth i) (hlow : IsCubicTorusAbove T.L t T.n₀ F) {Y : F.Cell}
    (S : Finset (F.Site F.depth)) (hS : ∀ y ∈ S, enclosingCell y = Y) (hN : (S.card : ℝ) ≤ N) :
    IsDecayingGradient T.ballRadius T.κ (N * (C * ε)) (N * ε) Y
      (fun η => ∑ y ∈ S, interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y η V) := by
  have hcd : ∀ y, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
      ContDiffAt ℝ 3 (fun ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V) η :=
    fun y η hη => interpolatedExpansion_contDiffAt hJS hTr hx hε hε₃ hf hF hV hs0 hs1 y fun b => (hη b).le
  have hN0 : 0 ≤ N := (Nat.cast_nonneg _).trans hN
  refine ⟨?_, fun η hη => ?_, fun η hη b => ?_⟩
  · refine ContDiffOn.sum fun y _ η hη => ?_
    exact ((hcd y η hη).of_le (by norm_num)).contDiffWithinAt
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∀ y ∈ S, |interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y η V| ≤ ε :=
      fun y _ => abs_subtractTrivial_le hσ hf hlow hper y (hcold η hη)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hN hε
  · have hfd : HasFDerivAt (fun ζ => ∑ y ∈ S, interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V)
        (∑ y ∈ S, fderiv ℝ (fun ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V) η) η :=
      HasFDerivAt.fun_sum fun y _ => ((hcd y η hη).differentiableAt (by norm_num)).hasFDerivAt
    have hE0 := (Real.exp_pos (-(2 ^ 5 * T.κ * bondDistToCell Y b))).le
    unfold bondGradNorm
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun u hu => ?_
    show ‖fderiv ℝ (fun ζ => ∑ y ∈ S, interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V) η
      (Pi.single b u)‖ ≤ _
    rw [hfd.fderiv, _root_.sum_apply, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∀ y ∈ S, |fderiv ℝ (fun ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V) η
        (Pi.single b u)| ≤ C * ε * Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b)) := by
      intro y hy
      refine (abs_fderiv_interpolatedExpansion_le hJS hTr hx hε hε₃ hf hF hV hs0 hs1 y (fun b => (hη b).le) b u hu hC
        hκ).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC hε)
      rw [Real.exp_le_exp, hS y hy]
      have h2 : 0 ≤ T.κ * bondDistToCell Y b := mul_nonneg hκ (Nat.cast_nonneg _)
      unfold bondDistToCell at h2 ⊢
      nlinarith
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have := mul_le_mul_of_nonneg_right hN (mul_nonneg (mul_nonneg hC hε) hE0)
    nlinarith
end SeriesExpansions
section Scaled
variable {F : BlockFrame}
private theorem iteratedFDeriv_const_mul_zero {k : ℕ} {c : ℝ} (hc : c ≠ 0) (g : (Fin k → ℝ) → ℝ)
    (v : Fin k → (Fin k → ℝ)) :
    iteratedFDeriv ℝ k (fun τ => c * g τ) 0 v = c * iteratedFDeriv ℝ k g 0 v := by
  have h := (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc)).iteratedFDeriv_comp_left
    (f := g) (x := (0 : Fin k → ℝ)) (i := k)
  have h2 : (⇑(ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc)) ∘ g) = fun τ => c * g τ := by
    funext τ
    simp [ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]
  rw [h2] at h
  rw [h]
  simp [ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]
abbrev _root_.YangMills.SharedProofs.p20802 := @iteratedFDeriv_const_mul_zero
private theorem bondDeriv_const_mul {j k : ℕ} {c : ℝ} (hc : c ≠ 0) (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (b : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun W' => c * G W') W b X = c * bondDeriv G W b X :=
  iteratedFDeriv_const_mul_zero hc _ _
private def scaledFamily (c : ℝ) (h : LocalFamily) : LocalFamily := fun F y W => c * h F y W
private theorem subtractTrivial_scaledFamily (c : ℝ) (h : LocalFamily) (F : BlockFrame) (y : F.Site F.depth)
    (W : F.GaugeField F.depth) : subtractTrivial (scaledFamily c h) F y W = c * subtractTrivial h F y W := by
  simp only [subtractTrivial, scaledFamily]; ring
private theorem interpolatedExpansion_scaledFamily (s a ρA : ℝ) (m : ℕ) (c : ℝ) (h : LocalFamily) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    interpolatedExpansion s a ρA m (scaledFamily c h) y η V = c * interpolatedExpansion s a ρA m h y η V :=
  subtractTrivial_scaledFamily c h F y _
private theorem interpolatedBlockExpansion_scaledFamily (s a ρA : ℝ) (m : ℕ) (c : ℝ) (h : LocalFamily) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    interpolatedBlockExpansion s a ρA m (scaledFamily c h) Y η V = c * interpolatedBlockExpansion s a ρA m h Y η V := by
  simp only [interpolatedBlockExpansion, interpolatedExpansion_scaledFamily, Finset.mul_sum]
private theorem scaledFamily_isNormBounded {L t n₀ : ℕ} {σ δ ε ε₃ c : ℝ} {h : LocalFamily} (hc : 0 < c)
    (hh : IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ h) :
    IsNormBoundedLocalFamily L t n₀ σ δ (c * ε) (c * ε₃) (scaledFamily c h) := by
  have hc0 : c ≠ 0 := hc.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro F hF y W hW k b X
    exact contDiffAt_const.mul (hh.smooth F hF y W hW k b X)
  · intro F hF y W γ hW
    simp only [scaledFamily, hh.gauge_invariant F hF y W γ hW]
  · intro F hF y g W hW
    simp only [scaledFamily, hh.translation_invariant F hF y g W hW]
  · intro F hF y W k b X hW h1 h3 hX
    have e : bondDeriv (scaledFamily c h F y) W b X = c * bondDeriv (h F y) W b X :=
      bondDeriv_const_mul hc0 (h F y) W b X
    rw [e, abs_mul, abs_of_pos hc]
    have := hh.decay F hF y W k b X hW h1 h3 hX
    have h2 := mul_le_mul_of_nonneg_left this hc.le
    refine h2.trans (le_of_eq ?_)
    split_ifs <;> ring
  · intro F F' hF hF' y y' W W' r k e X hW hW' hA hk he hX
    have e1 : bondDeriv (subtractTrivial (scaledFamily c h) F y) W (bondsAt y e) X =
        c * bondDeriv (subtractTrivial h F y) W (bondsAt y e) X := by
      rw [← bondDeriv_const_mul hc0]
      congr 1
      funext W''
      exact subtractTrivial_scaledFamily c h F y W''
    have e2 : bondDeriv (subtractTrivial (scaledFamily c h) F' y') W' (bondsAt y' e) X =
        c * bondDeriv (subtractTrivial h F' y') W' (bondsAt y' e) X := by
      rw [← bondDeriv_const_mul hc0]
      congr 1
      funext W''
      exact subtractTrivial_scaledFamily c h F' y' W''
    rw [e1, e2, ← mul_sub, abs_mul, abs_of_pos hc]
    have := hh.locality F F' hF hF' y y' W W' r k e X hW hW' hA hk he hX
    have h2 := mul_le_mul_of_nonneg_left this hc.le
    refine h2.trans (le_of_eq ?_)
    ring
private theorem pushforwardField_eq_toTorus {ι : Type} [Fintype ι] [DecidableEq ι]
    (j : ι → ↥(chordBonds (finiteCells F))) (ζ : BondField ι) : pushforwardField j ζ = toTorus j ζ := by
  funext b
  simp only [pushforwardField, toTorus, _root_.YangMills.Construction.Interpolation.extendByZero]
private theorem abs_interpolatedBlockExpansion_sub_le {T : StepParameters} (hRo : InterpolatedExpansionsCompareAt T)
    (hE : 0 < T.E) (hη₃ : 0 < T.η₃) {t : ℕ} {x s ε : ℝ} {h : LocalFamily} {F' : BlockFrame} {V : F.GaugeField F.top}
    {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {q : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {j : ι → ↥(chordBonds (finiteCells F))} {j' : ι → ↥(chordBonds (finiteCells F'))} (hx : T.coupling ≤ x)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 < ε)
    (hh : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h) (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hF' : IsCubicTopTorus T.L t T.n₀ F') (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    (hV' : IsSmallCurvature (5 / 4 * T.σ) V') (hAg : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q)
    (hnp : IsShortPairing Y Y' q j j') (hq : T.blockIndex ≤ q) {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < T.ballRadius) :
    |interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) h Y (toTorus j ζ) V -
      interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) h Y' (toTorus j' ζ) V'| ≤
      T.Ct * (ε / T.η₃) * Real.exp (-(4 * T.κ * q)) *
        (x * ∑ i, Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y (j i))) * ‖ζ i‖ ^ 2 + 1) := by
  set c : ℝ := T.E / ε with hcdef
  have hc : 0 < c := div_pos hE hε
  have hcε : c * ε = T.E := by rw [hcdef]; field_simp
  have hc3 : c * (ε / T.η₃) = T.energyRatio := by
    show c * (ε / T.η₃) = T.E / T.η₃
    rw [← hcε]
    ring
  have hfam : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio (scaledFamily c h) := by
    have := scaledFamily_isNormBounded hc hh
    rwa [hcε, hc3] at this
  have hset : InterpolatedComparisonSetting T t x s (scaledFamily c h) V V' Y Y' q j j' 0 := by
    refine ⟨hx, ⟨hs0, hs1⟩, hfam, hF, hF', hV, hV', hAg, hq, hnp.isBoxPairing.injective_left,
      hnp.isBoxPairing.injective_right, fun i => ?_, fun i => by simp⟩
    obtain ⟨g, o, k, hg, ho, e1, e2⟩ := hnp.short_offsets i
    refine ⟨g, o, k, ho, fun l => ?_, e1, e2⟩
    have a := hg l
    have b := abs_nonneg (g l)
    linarith
  obtain ⟨-, hP⟩ := hRo t x s (scaledFamily c h) F F' V V' Y Y' q ι j j' 0 hset
  have key := (hP ζ hζ).1
  have z : ∀ {G : BlockFrame} (Z : G.Cell), Z + siteOfCoords G.top (0 : Fin 4 → ℤ) = Z := by
    intro G Z
    funext l
    simp [siteOfCoords]
  rw [z, z, pushforwardField_eq_toTorus, pushforwardField_eq_toTorus] at key
  beta_reduce at key
  rw [interpolatedBlockExpansion_scaledFamily, interpolatedBlockExpansion_scaledFamily, ← mul_sub, abs_mul, abs_of_pos hc,
    abs_sub_comm, ← hc3] at key
  have e : T.Ct * (c * (ε / T.η₃)) * Real.exp (-(4 * T.κ * q)) *
      (x * weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F) Y ζ + 1) =
      c * (T.Ct * (ε / T.η₃) * Real.exp (-(4 * T.κ * q)) *
        (x * weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F) Y ζ + 1)) := by ring
  rw [e] at key
  exact le_of_mul_le_mul_left key hc
end Scaled
section Assembly
variable {U : StepParameters}
private theorem card_sites_le (hSites : SitesPerCellLePow) {F : BlockFrame} (hodd : Odd F.blockSide)
    (hs2 : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) (S : Finset (F.Site F.depth))
    (hS : ∀ y ∈ S, y ∈ sitesOfCells (finiteCells F) F.depth ∧ enclosingCell y = Y) :
    (S.card : ℝ) ≤ (F.blockSide : ℝ) ^ 4 := by
  classical
  have h1 := hSites F (finiteCells F) hodd hs2 Y
  have h2 : S.card ≤ F.blockSide ^ 4 := by
    refine le_trans ?_ h1
    refine (Finset.card_le_card ?_).trans (Finset.card_image_le (f := Subtype.val))
    intro y hy
    obtain ⟨a, b⟩ := hS y hy
    exact Finset.mem_image.2 ⟨⟨y, a⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, b⟩, rfl⟩
  exact_mod_cast h2
private theorem interpolatedBlockExpansion_decaying (hJS : JointlyContDiffOnBallsOfDisplacements)
    (hSites : SitesPerCellLePow) {C : ℝ} {Ck : ℕ → ℝ} {t : ℕ} {x s ε ε₃ : ℝ} {h : LocalFamily} {F : BlockFrame}
    {V : F.GaugeField F.top} (hTr : TransportBoundsAt U C Ck) (hx : U.coupling ≤ x) (hε : 0 ≤ ε) (hε₃ : 0 ≤ ε₃)
    (hf : IsNormBoundedLocalFamily U.L t U.n₀ U.σ U.decayRate ε ε₃ h) (hF : IsCubicTopTorus U.L t U.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * U.σ) V) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hC : 0 ≤ C) (hκ : 0 ≤ U.κ)
    (hσ : 0 < U.σ) (hodd : Odd U.L) (hs2 : ∀ i, 2 < F.extent i)
    (hcold : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < U.ballRadius) →
      IsSmallCurvature U.σ (interpolatedField s U.a U.chainParams.ρA (frameRadius x) V η)) (Y : F.Cell) :
    IsDecayingGradient U.ballRadius U.κ ((U.L : ℝ) ^ 4 * (C * ε)) ((U.L : ℝ) ^ 4 * ε) Y
      (fun η => interpolatedBlockExpansion s U.a U.chainParams.ρA (frameRadius x) h Y η V) := by
  have hFL : F.blockSide = U.L := hF.1
  have hLo : Odd F.blockSide := by rw [hFL]; exact hodd
  have hLpos : 0 < F.blockSide := hLo.pos
  have hper : ∀ i, 2 < F.period F.depth i := fun i => by
    have h1 : 0 < F.blockSide ^ (F.top - F.depth) := pow_pos hLpos _
    show 2 < F.extent i * F.blockSide ^ (F.top - F.depth)
    have := hs2 i
    nlinarith
  obtain ⟨h1, h2, n, hside, hnn⟩ := id hF
  have hlow : IsCubicTorusAbove U.L t U.n₀ F :=
    ⟨h1, h2, n, hside, hnn.trans (Nat.le_mul_of_pos_right _ (by rw [← hFL]; exact hLpos))⟩
  unfold interpolatedBlockExpansion
  refine sum_interpolatedExpansion_decaying hJS hTr hx hε hε₃ hf hF hV hs0 hs1 hC hκ hσ hcold hper hlow _
    (fun y hy => (Finset.mem_filter.1 hy).2) ?_
  rw [← hFL]
  exact card_sites_le hSites hLo (fun i => (hs2 i).le) Y _ fun y hy => Finset.mem_filter.1 hy
set_option maxHeartbeats 1000000 in
private theorem admissibleAt_of_bounds (hLaw : normalizedBallLawIsProbabilityStatement) (hOff : cellOffsetStatement)
    (hJS : JointlyContDiffOnBallsOfDisplacements) (hSites : SitesPerCellLePow) (hρ : 0 < U.ballRadius)
    (hσ : 0 < U.σ) (hcut : IsCutoff U.ballRadius U.p) (hκ : 0 < U.κ) (hη₃ : 0 < U.η₃) (hη1 : U.η₃ ≤ 1)
    (hE : 1 ≤ U.E) (hodd : Odd U.L) (hn : 1 ≤ U.n₀) (hy : 1 ≤ U.coupling) {Cq Cz : ℕ → ℝ}
    {Cr : ℕ → ℕ → ℕ → ℝ} {C : ℝ} {Ck : ℕ → ℝ} (hC : 0 < C)
    (hFB : ∀ (t : ℕ) (x : ℝ), U.coupling ≤ x → InterpolatedFrameBoundsAt U Cq Cz Cr t x)
    (hTr : TransportBoundsAt U C Ck) (hRo : InterpolatedExpansionsCompareAt U) {W K : ℝ} (hW0 : 0 ≤ W)
    (hWs : ∀ F : BlockFrame, F.blockSide = U.L → (∀ i, 2 ≤ F.extent i) → ∀ Y : F.Cell,
      ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(U.κ * bondDistToCell Y b)) ≤ W)
    (hK : (U.L : ℝ) ^ 4 * C * (1 + W * U.ballRadius) + 2 * (U.L : ℝ) ^ 4 + |U.Ct| * (W * |Cq 1| + 1) ≤ K) :
    InterpolatedBlockExpansionAdmissibleAt { U with Cs := K } := by
  intro t x s ε φ h F F' V V' Y Y' q ι _ _ j j' hx0 hs0 hs1 hε hφ0 hh0 hTF0 hTF0' hV0 hV0' hAg hnp
  have hx : U.coupling ≤ x := hx0
  have hφ : IsNormBoundedLocalFamily U.L t U.n₀ U.σ U.decayRate U.E U.energyRatio φ := hφ0
  have hh : IsNormBoundedLocalFamily U.L t U.n₀ U.σ U.decayRate ε (ε / U.η₃) h := hh0
  have hTF : IsCubicTopTorus U.L t U.n₀ F := hTF0
  have hTF' : IsCubicTopTorus U.L t U.n₀ F' := hTF0'
  have hV : IsSmallCurvature (5 / 4 * U.σ) V := hV0
  have hV' : IsSmallCurvature (5 / 4 * U.σ) V' := hV0'
  clear hx0 hφ0 hh0 hTF0 hTF0' hV0 hV0'
  have hx1 : 1 ≤ x := hy.trans hx
  have hxp : 0 < x := by linarith
  have hFL : F.blockSide = U.L := hTF.1
  have hFL' : F'.blockSide = U.L := hTF'.1
  obtain ⟨-, -, n, hside, hnn⟩ := id hTF
  obtain ⟨-, -, n', hside', hnn'⟩ := id hTF'
  have sd : ∀ i, 2 * q + 2 < F.extent i := fun i => by
    rcases hAg.1 i with h0 | h0
    · have := hside i
      omega
    · exact h0
  have sd' : ∀ i, 2 * q + 2 < F'.extent i := fun i => by
    rcases hAg.2.1 i with h0 | h0
    · have := hside' i
      omega
    · exact h0
  have hs2 : ∀ i, 2 < F.extent i := fun i => by have := sd i; omega
  have hs2' : ∀ i, 2 < F'.extent i := fun i => by have := sd' i; omega
  have hLo : Odd F.blockSide := by rw [hFL]; exact hodd
  obtain ⟨hd1, hd2⟩ := shortPairing_distances hOff hLo (hFL'.trans hFL.symm) sd sd' hnp
  have hj := hnp.isBoxPairing.injective_left
  have hj' := hnp.isBoxPairing.injective_right
  have FB := hFB t x hx
  have hW1 := hWs F hFL (fun i => (hs2 i).le) Y
  have hW2 := hWs F' hFL' (fun i => (hs2' i).le) Y'
  have hc : 0 ≤ |Cq 1| := abs_nonneg _
  have hL4 : 0 ≤ (U.L : ℝ) ^ 4 := by positivity
  have hε₃ : 0 ≤ ε / U.η₃ := (div_pos hε hη₃).le
  have mono : ∀ {G : BlockFrame} {Wg : G.GaugeField G.depth}, IsSmallCurvature (3 / 4 * U.σ) Wg →
      IsSmallCurvature U.σ Wg :=
    fun hc' p hp => (hc' p hp).trans (by linarith)
  have hcold : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < U.ballRadius) →
      IsSmallCurvature U.σ (interpolatedField s U.a U.chainParams.ρA (frameRadius x) V η) := fun η hη =>
    mono ((FB.one_torus F V s hTF hV hs0 hs1).small.small_curvature_nearby η fun b => (hη b).le)
  have hcold' : ∀ η : StepVariable (finiteCells F'), (∀ b, ‖η b‖ < U.ballRadius) →
      IsSmallCurvature U.σ (interpolatedField s U.a U.chainParams.ρA (frameRadius x) V' η) := fun η hη =>
    mono ((FB.one_torus F' V' s hTF' hV' hs0 hs1).small.small_curvature_nearby η fun b => (hη b).le)
  have sl := interpolatedBlockExpansion_decaying hJS hSites hTr hx hε.le hε₃ hh hTF hV hs0 hs1 hC.le hκ.le hσ hodd hs2
    hcold Y
  have sl' := interpolatedBlockExpansion_decaying hJS hSites hTr hx hε.le hε₃ hh hTF' hV' hs0 hs1 hC.le hκ.le hσ hodd hs2'
    hcold' Y'
  have hlaw : IsIntermediateLaw U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x)
      (IsNormBoundedLocalFamily U.L t U.n₀ U.σ U.decayRate U.E U.energyRatio) V
      (familyLawExponent s U.a U.chainParams.ρA x (frameRadius x) φ V) :=
    IsIntermediateLaw.ofFamily s φ hs0 hs1 hφ
  have hlaw' : IsIntermediateLaw U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x)
      (IsNormBoundedLocalFamily U.L t U.n₀ U.σ U.decayRate U.E U.energyRatio) V'
      (familyLawExponent s U.a U.chainParams.ρA x (frameRadius x) φ V') :=
    IsIntermediateLaw.ofFamily s φ hs0 hs1 hφ
  change ComparisonHypotheses U.ballRadius U.chainParams.lam x U.κ (K * ε / U.η₃) U.p U.blockIndex q Y Y' j j'
    _ _ _ _ ∧ _ ∧ _
  set e : ℝ := ε / U.η₃ with he
  have he0 : 0 ≤ e := hε₃
  have hεe : ε ≤ e := by
    rw [he, le_div_iff₀ hη₃]
    nlinarith
  obtain ⟨α, hα⟩ : ∃ α, α = K * ε / U.η₃ := ⟨_, rfl⟩
  have hαe : α = K * e := by rw [hα, he]; ring
  rw [← hα]
  have hρ0 := hρ.le
  have t1 : 0 ≤ (U.L : ℝ) ^ 4 * C * e := by positivity
  have t2 : 0 ≤ (U.L : ℝ) ^ 4 * C * (W * U.ballRadius) * e := by positivity
  have t3 : 0 ≤ 2 * (U.L : ℝ) ^ 4 * e := by positivity
  have t4 : 0 ≤ |U.Ct| * (W * |Cq 1| + 1) * e := by positivity
  have hsum : (U.L : ℝ) ^ 4 * C * e + (U.L : ℝ) ^ 4 * C * (W * U.ballRadius) * e + 2 * (U.L : ℝ) ^ 4 * e +
      |U.Ct| * (W * |Cq 1| + 1) * e ≤ α := by
    rw [hαe]
    have c4 := mul_le_mul_of_nonneg_right hK he0
    refine le_trans (le_of_eq ?_) c4
    ring
  have hg0 : 0 ≤ (U.L : ℝ) ^ 4 * (C * ε) := by positivity
  have hgα : (U.L : ℝ) ^ 4 * (C * ε) ≤ α := by
    have : (U.L : ℝ) ^ 4 * (C * ε) ≤ (U.L : ℝ) ^ 4 * C * e := by
      have := mul_le_mul_of_nonneg_left hεe (mul_nonneg hL4 hC.le)
      nlinarith
    linarith
  have hfr : W * U.ballRadius * ((U.L : ℝ) ^ 4 * (C * ε)) ≤ α := by
    have : W * U.ballRadius * ((U.L : ℝ) ^ 4 * (C * ε)) ≤ (U.L : ℝ) ^ 4 * C * (W * U.ballRadius) * e := by
      have := mul_le_mul_of_nonneg_left hεe (by positivity : 0 ≤ (U.L : ℝ) ^ 4 * C * (W * U.ballRadius))
      nlinarith
    linarith
  have hme : 2 * ((U.L : ℝ) ^ 4 * ε) ≤ α := by
    have : 2 * ((U.L : ℝ) ^ 4 * ε) ≤ 2 * (U.L : ℝ) ^ 4 * e := by
      have := mul_le_mul_of_nonneg_left hεe (by positivity : 0 ≤ 2 * (U.L : ℝ) ^ 4)
      nlinarith
    linarith
  have hW6 : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * U.κ * bondDistToCell Y b)) ≤ W :=
    (Finset.sum_le_sum fun b _ => exp_rate_le hκ.le (by norm_num) Y b).trans hW1
  have law : ∀ th : ℝ, 0 ≤ th → th ≤ 1 → ∃ μ, CutoffLaw U.ballRadius U.p x |Cq 1|
      (pairingHomotopy j j' (familyLawExponent s U.a U.chainParams.ρA x (frameRadius x) φ V)
        (familyLawExponent s U.a U.chainParams.ρA x (frameRadius x) φ V') th) μ := by
    intro th h0 h1
    obtain ⟨μ, hμ⟩ := cutoffLaw_pairing hLaw hρ hcut FB hTF hTF' hV hV' hlaw hlaw' hj hj' hd1 h0 h1
    exact ⟨μ, hμ.mono (le_abs_self _) hxp⟩
  refine ⟨⟨comparisonBoundsOnTorus_of hLaw hρ hcut hκ FB hx1 hTF hV hlaw hg0 sl hW1 hgα hfr q,
    comparisonBoundsOnTorus_of hLaw hρ hcut hκ FB hx1 hTF' hV' hlaw' hg0 sl' hW2 hgα hfr q, ?_,
    fun th h0 h1 => ?_, fun hq th h0 h1 => ?_⟩, sl.smooth, sl'.smooth⟩
  · have b1 := abs_ballExpectation_le hLaw hρ hcut FB hTF hV hlaw sl
    have b2 := abs_ballExpectation_le hLaw hρ hcut FB hTF' hV' hlaw' sl'
    refine (abs_sub _ _).trans ?_
    linarith
  · obtain ⟨μ, hμ⟩ := law th h0 h1
    exact ⟨hasGradientBound_of_decaying hμ hρ hx1 hκ.le hg0 sl hj Finset.univ (fun _ => rfl) hgα,
      hasGradientBound_of_decaying hμ hρ hx1 hκ.le hg0 sl' hj' Finset.univ (fun i => hd2 i) hgα⟩
  · obtain ⟨μ, hμ⟩ := law th h0 h1
    have hprob := hμ.isProbability
    set e₄ : ℝ := Real.exp (-(4 * U.κ * q)) with he₄
    have he₄0 : 0 < e₄ := Real.exp_pos _
    let S₂ : BondField ι → ℝ := fun ζ => ∑ i, Real.exp (-(2 ^ 5 * U.κ * bondDistToCell Y (j i))) * ‖ζ i‖ ^ 2
    have hS₂i : ∀ i ∈ (Finset.univ : Finset ι), Integrable
        (fun ζ : BondField ι => Real.exp (-(2 ^ 5 * U.κ * bondDistToCell Y (j i))) * ‖ζ i‖ ^ 2) μ :=
      fun i _ => (hμ.integrable_norm_sq i).const_mul _
    have hS₂1 : Integrable S₂ μ := integrable_finsetSum _ hS₂i
    have hS₂2 : ∫ ζ, S₂ ζ ∂μ ≤ W * |Cq 1| / x := by
      simp only [S₂]
      rw [integral_finsetSum _ hS₂i]
      have hsum5 : ∑ i, Real.exp (-(2 ^ 5 * U.κ * bondDistToCell Y (j i))) ≤ W :=
        (sum_exp_comp_injective_le hj).trans
          ((Finset.sum_le_sum fun b _ => exp_rate_le hκ.le (by norm_num) Y b).trans hW1)
      calc ∑ i, ∫ ζ, Real.exp (-(2 ^ 5 * U.κ * bondDistToCell Y (j i))) * ‖ζ i‖ ^ 2 ∂μ
          ≤ ∑ i, Real.exp (-(2 ^ 5 * U.κ * bondDistToCell Y (j i))) * (|Cq 1| / x) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [integral_const_mul]
            exact mul_le_mul_of_nonneg_left (hμ.moment_le i) (Real.exp_pos _).le
        _ = (∑ i, Real.exp (-(2 ^ 5 * U.κ * bondDistToCell Y (j i)))) * (|Cq 1| / x) := by rw [Finset.sum_mul]
        _ ≤ W * (|Cq 1| / x) := mul_le_mul_of_nonneg_right hsum5 (div_nonneg hc hxp.le)
        _ = W * |Cq 1| / x := by ring
    have hS₂0 : ∀ ζ, 0 ≤ S₂ ζ := fun ζ => Finset.sum_nonneg fun i _ => by positivity
    let G : BondField ι → ℝ := fun ζ => |U.Ct| * e * e₄ * (x * S₂ ζ + 1)
    have hG : Integrable G μ := ((hS₂1.const_mul x).add (integrable_const _)).const_mul _
    rw [hμ.expectation_eq]
    have hle : ∫ ζ, G ζ ∂μ ≤ α * e₄ := by
      have e1 : ∫ ζ, G ζ ∂μ = |U.Ct| * e * e₄ * (x * ∫ ζ, S₂ ζ ∂μ + 1) := by
        simp only [G]
        rw [integral_const_mul, integral_add (hS₂1.const_mul x) (integrable_const _), integral_const_mul]
        simp
      rw [e1]
      have c1 : x * ∫ ζ, S₂ ζ ∂μ ≤ W * |Cq 1| := by
        have := mul_le_mul_of_nonneg_left hS₂2 hxp.le
        refine this.trans (le_of_eq ?_)
        field_simp
      have c2 : |U.Ct| * e * e₄ * (x * ∫ ζ, S₂ ζ ∂μ + 1) ≤ |U.Ct| * e * e₄ * (W * |Cq 1| + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      refine c2.trans ?_
      have c3 : |U.Ct| * (W * |Cq 1| + 1) * e ≤ α := by linarith
      have c4 := mul_le_mul_of_nonneg_right c3 he₄0.le
      refine le_trans (le_of_eq ?_) c4
      ring
    refine le_trans ?_ hle
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hG (hμ.ae_ball.mono fun ζ hζ => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_interpolatedBlockExpansion_sub_le hRo (by linarith) hη₃ hx hs0 hs1 hε hh hTF hTF' hV hV' hAg hnp hq
      hζ).trans ?_
    have hx2 : 0 ≤ x * S₂ ζ + 1 := by
      have := mul_nonneg hxp.le (hS₂0 ζ)
      linarith
    show U.Ct * (ε / U.η₃) * e₄ * (x * S₂ ζ + 1) ≤ |U.Ct| * e * e₄ * (x * S₂ ζ + 1)
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ he₄0.le) hx2
    exact mul_le_mul_of_nonneg_right (le_abs_self _) he0
end Assembly
end BlockExpansionAdmissibility
open BlockExpansionAdmissibility in
theorem interpolatedBlockExpansionAdmissible (hFr : interpolatedFramesStatement) (hTr : transportBoundsStatement)
    (hRo : InterpolatedExpansionsCompare) (hLaw : normalizedBallLawIsProbabilityStatement)
    (hOff : cellOffsetStatement) (hSum : _root_.YangMills.Construction.CellCounting.ExpDecaySumBounded)
    (hFew : cellBondsCardStatement) (hSites : SitesPerCellLePow)
    (hJS : JointlyContDiffOnBallsOfDisplacements) (hJ : EventuallyInParametersCombines)
    (hD : joinAtLoweredSmallnessConstantStatement) : interpolatedBlockExpansionAdmissibleStatement := by
  classical
  obtain ⟨Cq, Cz, Cr, hF⟩ := hFr
  obtain ⟨C, Ck, hC, -, hTr⟩ := hTr
  let Wf : StepParameters → ℝ := fun T => if h : 0 < T.κ then Classical.choose (hSum (4 * T.L ^ 4) T.κ h) else 0
  let Kf : StepParameters → ℝ := fun T => (T.L : ℝ) ^ 4 * C (rateParameters T) * (1 + |Wf T| * T.ballRadius) +
    2 * (T.L : ℝ) ^ 4 + |T.Ct| * (|Wf T| * |Cq T 1| + 1)
  refine hD _ _ InterpolatedBlockExpansionAdmissibleAt (fun T' _ => Kf T') hF (hJ.1 _ _ hTr hRo) ?_
  intro T c _ hodd hn hy hE hη hη1 hκ hσ _ hcut hG hP hR
  have hκz : 0 < ({ T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 } : StepParameters).κ := hκ
  have hW : Wf { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 } =
      Classical.choose (hSum (4 * T.L ^ 4) T.κ hκ) := dif_pos hκz
  have hspec := Classical.choose_spec (hSum (4 * T.L ^ 4) T.κ hκ)
  rw [← hW] at hspec
  have hρ : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  exact admissibleAt_of_bounds (U := { T with Cs := c }) hLaw hOff hJS hSites hρ hσ hcut hκ hη hη1 hE hodd hn hy
    (hC _) hP hR.1 hR.2
    (W := |Wf { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 }|) (K := T.Cs) (abs_nonneg _)
    (fun F hFL hs Y => by
      show ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤ _
      refine le_trans (hspec.2 F ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1) (fun z => ?_) Y)
        (le_abs_self _)
      have hFL' : F.blockSide = T.L := hFL
      have := hFew F (by rw [hFL']; exact hodd) hs z
      rwa [hFL'] at this) hG
end TorusComparison
end YangMills.Construction
end
