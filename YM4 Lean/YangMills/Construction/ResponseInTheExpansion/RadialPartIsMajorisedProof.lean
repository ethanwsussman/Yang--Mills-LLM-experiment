import YangMills.Construction.ResponseInTheExpansion.MajorisedObservablesAreAdmittedProof
import YangMills.Construction.ResponseInTheExpansion.RadialPartIsMajorised
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusComparison YangMills.Construction.Interpolation YangMills.Construction.CellCounting YangMills.Construction.WeightedResponses
namespace YangMills.Construction.ResponseInTheExpansion
variable {F : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι]
private def coordProjection (b : ι) : BondField ι →L[ℝ] BondField ι :=
  (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b).comp (ContinuousLinearMap.proj b)
private theorem coordProjection_apply (b : ι) (ζ : BondField ι) :
    coordProjection b ζ = bondVariation b (ζ b) := rfl
private theorem hasFDerivAt_weightedPartial {G : BondField ι → ℝ} {η : BondField ι}
    (hG : ContDiffAt ℝ 2 G η) (b : ι) :
    HasFDerivAt (fun ζ => bondPartialDeriv G b ζ (ζ b))
      ((fderiv ℝ G η).comp (coordProjection b) + (fderiv ℝ (fderiv ℝ G) η).flip (coordProjection b η)) η := by
  have hC1 : ContDiffAt ℝ 1 (fderiv ℝ G) η := hG.fderiv_right (by norm_num)
  have hD : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) η) η := (hC1.differentiableAt (by norm_num)).hasFDerivAt
  exact hD.clm_apply (coordProjection b).hasFDerivAt
private theorem secondDerivAlong_eq_fderiv {G : BondField ι → ℝ} {η : BondField ι}
    (hG : ContDiffAt ℝ 2 G η) (u v : BondField ι) :
    secondDerivAlong G η u v = fderiv ℝ (fderiv ℝ G) η v u := by
  have hC1 : ContDiffAt ℝ 1 (fderiv ℝ G) η := hG.fderiv_right (by norm_num)
  have hD : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) η) η := (hC1.differentiableAt (by norm_num)).hasFDerivAt
  have hU := hD.clm_apply (hasFDerivAt_const u η)
  unfold secondDerivAlong
  rw [hU.fderiv]
  simp
abbrev _root_.YangMills.SharedProofs.p55293 := @secondDerivAlong_eq_fderiv
private theorem contDiffAt_weightedPartial {G : BondField ι → ℝ} {η : BondField ι}
    (hG : ContDiffAt ℝ 2 G η) (b : ι) :
    ContDiffAt ℝ 1 (fun ζ => bondPartialDeriv G b ζ (ζ b)) η := by
  have hC1 : ContDiffAt ℝ 1 (fderiv ℝ G) η := hG.fderiv_right (by norm_num)
  exact hC1.clm_apply (coordProjection b).contDiff.contDiffAt
private theorem coordProjection_bondVariation_of_ne {b b' : ι} (h : b' ≠ b) (e : BondVector) :
    coordProjection b (bondVariation b' e) = 0 := by
  rw [coordProjection_apply]
  have hz : bondVariation b' e b = 0 := by
    simp [bondVariation, Pi.single_apply, Ne.symm h]
  rw [hz]
  simp [bondVariation]
private theorem coordProjection_bondVariation_self (b : ι) (e : BondVector) :
    coordProjection b (bondVariation b e) = bondVariation b e := by
  rw [coordProjection_apply]
  simp [bondVariation]
private theorem bondGradNorm_le_of_bound {f : BondField ι → ℝ} {η : BondField ι} {b : ι} {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ e : BondVector, |fderiv ℝ f η (bondVariation b e)| ≤ B * ‖e‖) :
    bondGradNorm f b η ≤ B := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.bondGradNorm_le_of_forall <;> assumption
private theorem one_le_cutoffMajorant (p : ℝ → ℝ) (Y : F.Cell) (η : StepVariable (finiteCells F)) :
    1 ≤ cutoffMajorant p Y η := by apply _root_.YangMills.SharedProofs.p29597 <;> assumption
private theorem radialPart_gradient_bound {ρ κ A W : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) (hA : 0 ≤ A) {Y : F.Cell}
    {S : Finset ↥(chordBonds (finiteCells F))} {G : StepVariable (finiteCells F) → ℝ}
    (hW : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(16 * κ * bondDistToCell Y b)) ≤ W)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < ρ) (hG : ContDiffAt ℝ 2 G η)
    (hfirst : ∀ b ∈ S, ∀ e : BondVector,
      |bondPartialDeriv G b η e| ≤ A * Real.exp (-(16 * κ * bondDistToCell Y b)) * ‖e‖)
    (hsecond : ∀ b ∈ S, ∀ (b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
      |secondDerivAlong G η (bondVariation b e) (bondVariation b' e')| ≤
      A * Real.exp (-(16 * κ * bondDistToCell Y b)) * Real.exp (-(16 * κ * bondDistToCell Y b')) * ‖e‖ * ‖e'‖)
    (b' : ↥(chordBonds (finiteCells F))) :
    DifferentiableAt ℝ (radialPart S G) η ∧
    bondGradNorm (radialPart S G) b' η ≤ A * (1 + ρ * W) * Real.exp (-(16 * κ * bondDistToCell Y b')) := by
  have hsum : HasFDerivAt (radialPart S G)
      (∑ b ∈ S, ((fderiv ℝ G η).comp (coordProjection b) +
        (fderiv ℝ (fderiv ℝ G) η).flip (coordProjection b η))) η := by
    have hs := HasFDerivAt.fun_sum (u := S) fun b _ => hasFDerivAt_weightedPartial hG b
    exact hs
  have hW0 : 0 ≤ W := (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le).trans hW
  refine ⟨hsum.differentiableAt, bondGradNorm_le_of_bound (by positivity) fun e => ?_⟩
  rw [hsum.fderiv, ContinuousLinearMap.sum_apply]
  set d' := Real.exp (-(16 * κ * bondDistToCell Y b')) with hd'
  have hterm : ∀ b ∈ S, |((fderiv ℝ G η).comp (coordProjection b) +
      (fderiv ℝ (fderiv ℝ G) η).flip (coordProjection b η)) (bondVariation b' e)| ≤
      (if b = b' then A * d' * ‖e‖ else 0) +
        ρ * (A * Real.exp (-(16 * κ * bondDistToCell Y b)) * d' * ‖e‖) := fun b hb => by
    have hsplit : ((fderiv ℝ G η).comp (coordProjection b) +
        (fderiv ℝ (fderiv ℝ G) η).flip (coordProjection b η)) (bondVariation b' e) =
        fderiv ℝ G η (coordProjection b (bondVariation b' e)) +
          secondDerivAlong G η (bondVariation b (η b)) (bondVariation b' e) := by
      rw [secondDerivAlong_eq_fderiv hG]
      rfl
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · by_cases hbb : b = b'
      · subst hbb
        rw [if_pos rfl, coordProjection_bondVariation_self]
        exact hfirst b hb e
      · rw [if_neg hbb, coordProjection_bondVariation_of_ne (Ne.symm hbb)]
        simp
    · refine (hsecond b hb b' (η b) e).trans ?_
      have hn : ‖η b‖ ≤ ρ := (hη b).le
      have hp : 0 ≤ A * Real.exp (-(16 * κ * bondDistToCell Y b)) * d' * ‖e‖ := by positivity
      calc A * Real.exp (-(16 * κ * bondDistToCell Y b)) * d' * ‖η b‖ * ‖e‖ =
            ‖η b‖ * (A * Real.exp (-(16 * κ * bondDistToCell Y b)) * d' * ‖e‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hn hp
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_add_distrib]
  have hdiag : ∑ b ∈ S, (if b = b' then A * d' * ‖e‖ else 0) ≤ A * d' * ‖e‖ := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  have hoff : ∑ b ∈ S, ρ * (A * Real.exp (-(16 * κ * bondDistToCell Y b)) * d' * ‖e‖) ≤
      ρ * W * (A * d' * ‖e‖) := by
    have hfac : ∑ b ∈ S, ρ * (A * Real.exp (-(16 * κ * bondDistToCell Y b)) * d' * ‖e‖) =
        ρ * (∑ b ∈ S, Real.exp (-(16 * κ * bondDistToCell Y b))) * (A * d' * ‖e‖) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hfac]
    have hS : ∑ b ∈ S, Real.exp (-(16 * κ * bondDistToCell Y b)) ≤ W :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le).trans hW
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hρ.le) (by positivity)
  calc _ ≤ A * d' * ‖e‖ + ρ * W * (A * d' * ‖e‖) := add_le_add hdiag hoff
    _ = _ := by ring
private theorem freezeOutside_bound {ρ P B : ℝ} (hρ : 0 < ρ) (hP : 0 ≤ P)
    {R : StepVariable (finiteCells F) → ℝ}
    (Λ : Finset ↥(chordBonds (finiteCells F))) (w : ↥(chordBonds (finiteCells F)) → ℝ)
    (hd : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → DifferentiableAt ℝ R η)
    (hg : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm R b η ≤ P * w b)
    (hw : ρ * ∑ b ∈ Finset.univ \ Λ, P * w b ≤ B)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < ρ) : |R η - R (freezeOutside Λ η)| ≤ B := by
  classical
  set η₀ := freezeOutside Λ η with hη₀
  have hin : ∀ b, b ∈ Λ → η₀ b = η b := fun b hb => by
    simp only [hη₀, freezeOutside, _root_.YangMills.Construction.Interpolation.extendByZero]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hne
      simp [hne]
    · exact fun h => absurd hb h
  have hout : ∀ b, b ∉ Λ → η₀ b = 0 := fun b hb => by
    simp only [hη₀, freezeOutside, _root_.YangMills.Construction.Interpolation.extendByZero]
    refine Finset.sum_eq_zero fun b' hb' => ?_
    have hne : b' ≠ b := fun e => hb (e ▸ hb')
    simp [hne]
  set γ : ℝ → StepVariable (finiteCells F) := fun s => η₀ + s • (η - η₀) with hγ
  have hγball : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ b, ‖γ s b‖ < ρ := fun s hs b => by
    by_cases hb : b ∈ Λ
    · simp only [hγ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, hin b hb, sub_self, smul_zero, add_zero]
      exact hη b
    · simp only [hγ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, hout b hb, sub_zero, zero_add]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      have hle : s * ‖η b‖ ≤ 1 * ‖η b‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      linarith [hη b]
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (R ∘ γ) (fderiv ℝ R (γ s) (η - η₀)) (Set.Icc 0 1) s := fun s hs => by
    have hline : HasDerivAt γ (η - η₀) s := by
      have hsm : HasDerivAt (fun s : ℝ => s • (η - η₀)) ((1 : ℝ) • (η - η₀)) s :=
        (hasDerivAt_id s).smul_const _
      simpa [hγ] using hsm.const_add η₀
    exact ((hd _ (hγball s hs)).hasFDerivAt.comp_hasDerivAt s hline).hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ R (γ s) (η - η₀)‖ ≤ B := fun s hs => by
    have hsplit : η - η₀ = ∑ b, bondVariation b ((η - η₀) b) := by
      simp only [bondVariation]
      exact (Finset.univ_sum_single _).symm
    rw [hsplit, map_sum]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ b ∈ (Finset.univ : Finset ↥(chordBonds (finiteCells F))),
        ‖fderiv ℝ R (γ s) (bondVariation b ((η - η₀) b))‖ ≤ if b ∈ Λ then 0 else ρ * (P * w b) :=
      fun b _ => by
      split_ifs with hb
      · have hz : (η - η₀) b = 0 := by simp [hin b hb]
        rw [hz]
        simp [bondVariation]
      · have hop : ‖fderiv ℝ R (γ s) (bondVariation b ((η - η₀) b))‖ ≤
            bondGradNorm R b (γ s) * ‖(η - η₀) b‖ :=
          ((fderiv ℝ R (γ s)).comp
            (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b)).le_opNorm _
        have hlen : ‖(η - η₀) b‖ ≤ ρ := by
          simp only [Pi.sub_apply, hout b hb, sub_zero]
          exact (hη b).le
        have hgr := hg _ (hγball s hs) b
        have hnn : 0 ≤ bondGradNorm R b (γ s) := norm_nonneg _
        calc _ ≤ bondGradNorm R b (γ s) * ‖(η - η₀) b‖ := hop
          _ ≤ (P * w b) * ρ := mul_le_mul hgr hlen (norm_nonneg _) (hnn.trans hgr)
          _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    refine le_trans (le_of_eq ?_) hw
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _) (fun b hb => ?_) fun b hb => ?_
    · have hmem : b ∈ Λ := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hb
        exact hb
      rw [if_pos hmem]
    · have hmem : b ∉ Λ := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hb
        exact hb
      rw [if_neg hmem]
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc 0 1)
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  have hend : (R ∘ γ) 1 = R η := by simp [hγ]
  have hstart : (R ∘ γ) 0 = R η₀ := by simp [hγ]
  rw [hend, hstart, Real.norm_eq_abs] at hmv
  simpa using hmv
theorem radialPartDominated (hS : _root_.YangMills.Construction.CellCounting.ExpDecaySumBounded) : radialPartDominatedStatement := by
  intro N ρ κ hρ hκ
  obtain ⟨W, hW0, hW⟩ := hS N (8 * κ) (by positivity)
  refine ⟨(1 + ρ * W) ^ 2, by positivity, ?_⟩
  intro F Y p q S G A hN hA hG hfirst hsecond
  have hd0 : ∀ b : ↥(chordBonds (finiteCells F)), 0 ≤ bondDistToCell Y b := fun b => by
    unfold bondDistToCell
    positivity
  have hW8 : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(8 * κ * bondDistToCell Y b)) ≤ W := by
    have hc := hW F _ (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) (fun z => by convert hN z) Y
    exact hc
  have hW16 : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(16 * κ * bondDistToCell Y b)) ≤ W := by
    refine (Finset.sum_le_sum fun b _ => Real.exp_le_exp.2 ?_).trans hW8
    nlinarith [hd0 b]
  have hgr := fun (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < ρ)
      (b' : ↥(chordBonds (finiteCells F))) =>
    radialPart_gradient_bound hρ hκ hA hW16 hη (hG η hη) (hfirst η hη) (hsecond η hη) b'
  have hC1 : A * (1 + ρ * W) ≤ (1 + ρ * W) ^ 2 * A := by
    have h0 : 0 ≤ ρ * W := by positivity
    nlinarith [mul_nonneg hA h0, mul_nonneg (mul_nonneg hA h0) h0]
  have hCA : 0 ≤ (1 + ρ * W) ^ 2 * A := by positivity
  have hsm : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → ContDiffAt ℝ 1 (radialPart S G) η :=
    fun η hη => ContDiffAt.sum fun b _ => contDiffAt_weightedPartial (hG η hη) b
  refine ⟨fun η hη => (hsm η hη).contDiffWithinAt, fun η hη => ?_, fun η hη b => ?_, fun η hη => ?_⟩
  · have hval : |radialPart S G η| ≤ A * (ρ * W) := by
      unfold radialPart
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hb : ∀ b ∈ S, |bondPartialDeriv G b η (η b)| ≤
          A * ρ * Real.exp (-(16 * κ * bondDistToCell Y b)) := fun b hb => by
        refine (hfirst η hη b hb (η b)).trans ?_
        have hn := (hη b).le
        have he := (Real.exp_pos (-(16 * κ * bondDistToCell Y b))).le
        calc A * Real.exp (-(16 * κ * bondDistToCell Y b)) * ‖η b‖ ≤
              A * Real.exp (-(16 * κ * bondDistToCell Y b)) * ρ :=
              mul_le_mul_of_nonneg_left hn (by positivity)
          _ = _ := by ring
      refine (Finset.sum_le_sum hb).trans ?_
      rw [← Finset.mul_sum]
      have hs : ∑ b ∈ S, Real.exp (-(16 * κ * bondDistToCell Y b)) ≤ W :=
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le).trans hW16
      calc A * ρ * ∑ b ∈ S, Real.exp (-(16 * κ * bondDistToCell Y b)) ≤ A * ρ * W :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = _ := by ring
    have hmaj := one_le_cutoffMajorant p Y η
    calc _ ≤ (1 + ρ * W) ^ 2 * A * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hmaj hCA
  · have hgb := (hgr η hη b).2
    have hmaj := one_le_cutoffMajorant p Y η
    have he : Real.exp (-(16 * κ * bondDistToCell Y b)) ≤ Real.exp (-(2 * κ * bondDistToCell Y b)) :=
      Real.exp_le_exp.2 (by nlinarith [hd0 b])
    calc _ ≤ A * (1 + ρ * W) * Real.exp (-(16 * κ * bondDistToCell Y b)) := hgb
      _ ≤ (1 + ρ * W) ^ 2 * A * Real.exp (-(2 * κ * bondDistToCell Y b)) :=
        mul_le_mul hC1 he (Real.exp_pos _).le hCA
      _ ≤ (1 + ρ * W) ^ 2 * A * Real.exp (-(2 * κ * bondDistToCell Y b)) * cutoffMajorant p Y η :=
        le_mul_of_one_le_right (by positivity) hmaj
  · have hP : 0 ≤ A * (1 + ρ * W) := by positivity
    refine freezeOutside_bound hρ hP (bondsNearCell Y q) (fun b => Real.exp (-(16 * κ * bondDistToCell Y b)))
      (fun η hη => (hsm η hη).differentiableAt (by norm_num)) (fun η hη b => (hgr η hη b).2) ?_ hη
    set e₄ := Real.exp (-(4 * κ * q)) with he₄
    have he₄0 : 0 ≤ e₄ := (Real.exp_pos _).le
    have hoff : ∀ b ∈ Finset.univ \ bondsNearCell Y q,
        A * (1 + ρ * W) * Real.exp (-(16 * κ * bondDistToCell Y b)) ≤
        A * (1 + ρ * W) * e₄ * Real.exp (-(8 * κ * bondDistToCell Y b)) := fun b hb => by
      have hnb : b ∉ bondsNearCell Y q := (Finset.mem_sdiff.1 hb).2
      have hq : (q : ℝ) ≤ 2 * bondDistToCell Y b := by
        have hlt : q < 2 * cellSupDist (enclosingCell b.1.1) Y := by
          by_contra hcon
          exact hnb (Finset.mem_filter.2 ⟨Finset.mem_univ _, not_lt.1 hcon⟩)
        unfold bondDistToCell
        exact_mod_cast hlt.le
      rw [mul_assoc (A * (1 + ρ * W)) e₄, he₄, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hP
      nlinarith
    have hsum : ∑ b ∈ Finset.univ \ bondsNearCell Y q,
        A * (1 + ρ * W) * Real.exp (-(16 * κ * bondDistToCell Y b)) ≤ A * (1 + ρ * W) * e₄ * W := by
      refine (Finset.sum_le_sum hoff).trans ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => (Real.exp_pos _).le).trans hW8
    calc _ ≤ ρ * (A * (1 + ρ * W) * e₄ * W) := mul_le_mul_of_nonneg_left hsum hρ.le
      _ = (ρ * W) * (A * (1 + ρ * W)) * e₄ := by ring
      _ ≤ (1 + ρ * W) ^ 2 * A * e₄ := by
        refine mul_le_mul_of_nonneg_right ?_ he₄0
        have h0 : 0 ≤ ρ * W := by positivity
        nlinarith [mul_nonneg hA h0, mul_nonneg (mul_nonneg hA h0) h0]
end YangMills.Construction.ResponseInTheExpansion
end
