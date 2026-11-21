import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.TermsBetweenCompareOnTwoTori
import YangMills.Construction.ResponseInTheExpansion.GapLessCostIsASlopeProof
import YangMills.Construction.ResponseInTheExpansion.RadialPartIsMajorisedProof
import YangMills.Construction.ResponseInTheExpansion.RadialPartsAreAdmitted
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
open BlockAverages ColdStepAtMirrorFrames Interpolation TorusComparison CellCounting WeightedResponses Estimates
namespace ResponseInTheExpansion
variable {F : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem radialParts_expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := Subtype.ext (by simp [expUnit])
private theorem leftTranslate_bondSpread_empty {j : ℕ} (V : F.GaugeField j) (τ : Fin 0 → ℝ) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread (Fin.elim0 : Fin 0 → F.Site j × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) τ) V = V := by
  funext y i
  simp [leftTranslate, ColdStepAtMirrorFrames.bondSpread, radialParts_expUnit_zero]
private theorem bondDeriv_empty {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ} (G : F.GaugeField j → E) (W : F.GaugeField j) :
    bondDeriv G W (Fin.elim0 : Fin 0 → F.Site j × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) = G W := by
  unfold bondDeriv
  rw [iteratedFDeriv_zero_apply, leftTranslate_bondSpread_empty]
private theorem contDiffAt_of_empty_move {k : WithTop ℕ∞} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F))
    (h : ContDiffAt ℝ k (fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) q.1) V)) (0, η)) :
    ContDiffAt ℝ k (fun ζ => G ζ V) η := by apply _root_.YangMills.SharedProofs.p43393 <;> assumption
private theorem isOpen_polyball (ρ : ℝ) : IsOpen {ζ : BondField ι | ∀ i, ‖ζ i‖ < ρ} := by apply _root_.YangMills.SharedProofs.p5886 <;> assumption
private theorem abs_bondPartialDeriv_le_mul_norm {f : BondField ι → ℝ} {η : BondField ι} {b : ι} {B : ℝ}
    (h : ∀ e : BondVector, ‖e‖ = 1 → |bondPartialDeriv f b η e| ≤ B) (e : BondVector) : |bondPartialDeriv f b η e| ≤ B * ‖e‖ := by
  by_cases he : e = 0
  · subst he
    simp [bondPartialDeriv, bondVariation]
  · have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
    have h1 := h (‖e‖⁻¹ • e) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn])
    have hat : bondVariation b e = ‖e‖ • bondVariation b (‖e‖⁻¹ • e) := by
      unfold bondVariation
      rw [← Pi.single_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have : bondPartialDeriv f b η e = ‖e‖ * bondPartialDeriv f b η (‖e‖⁻¹ • e) := by
      unfold bondPartialDeriv
      rw [hat, map_smul, smul_eq_mul]
    rw [this, abs_mul, abs_of_nonneg (norm_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
private theorem secondDerivAlong_eq_fderiv {G : BondField ι → ℝ} {η : BondField ι} (hG : ContDiffAt ℝ 2 G η) (u v : BondField ι) :
    secondDerivAlong G η u v = fderiv ℝ (fderiv ℝ G) η v u := by apply _root_.YangMills.SharedProofs.p55293 <;> assumption
private theorem abs_secondDerivAlong_le_mul_norm {G : BondField ι → ℝ} {η : BondField ι} (hG : ContDiffAt ℝ 2 G η) {b b' : ι} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ e e' : BondVector, ‖e‖ = 1 → ‖e'‖ = 1 → |secondDerivAlong G η (bondVariation b e) (bondVariation b' e')| ≤ B) (e e' : BondVector) :
    |secondDerivAlong G η (bondVariation b e) (bondVariation b' e')| ≤ B * ‖e‖ * ‖e'‖ := by
  simp only [secondDerivAlong_eq_fderiv hG] at h ⊢
  by_cases he : e = 0
  · subst he
    simp [bondVariation]
  by_cases he' : e' = 0
  · subst he'
    simp [bondVariation]
  have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
  have hn' : ‖e'‖ ≠ 0 := norm_ne_zero_iff.2 he'
  have h1 := h (‖e‖⁻¹ • e) (‖e'‖⁻¹ • e') (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn])
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn'])
  have hat : ∀ (c : ι) (v : BondVector), ‖v‖ ≠ 0 → bondVariation c v = ‖v‖ • bondVariation c (‖v‖⁻¹ • v) := fun c v hv => by
    unfold bondVariation
    rw [← Pi.single_smul, smul_smul, mul_inv_cancel₀ hv, one_smul]
  have : fderiv ℝ (fderiv ℝ G) η (bondVariation b' e') (bondVariation b e) =
      ‖e‖ * ‖e'‖ * fderiv ℝ (fderiv ℝ G) η (bondVariation b' (‖e'‖⁻¹ • e')) (bondVariation b (‖e‖⁻¹ • e)) := by
    conv_lhs => rw [hat b e hn, hat b' e' hn']
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [this, abs_mul, abs_mul, abs_of_nonneg (norm_nonneg e), abs_of_nonneg (norm_nonneg e')]
  calc ‖e‖ * ‖e'‖ * _ ≤ ‖e‖ * ‖e'‖ * B := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring
private theorem derivs_of_finset_sum {Z : Type} (s : Finset Z) (g : Z → BondField ι → ℝ) {G : BondField ι → ℝ}
    {η : BondField ι} (hev : G =ᶠ[nhds η] fun ζ => ∑ y ∈ s, g y ζ) (hg : ∀ y ∈ s, ContDiffAt ℝ 2 (g y) η) :
    ContDiffAt ℝ 2 G η ∧ (∀ b e, bondPartialDeriv G b η e = ∑ y ∈ s, bondPartialDeriv (g y) b η e) ∧
      ∀ u v, secondDerivAlong G η u v = ∑ y ∈ s, secondDerivAlong (g y) η u v := by
  classical
  have hsum : ContDiffAt ℝ 2 (fun ζ => ∑ y ∈ s, g y ζ) η := ContDiffAt.sum hg
  have hG := hsum.congr_of_eventuallyEq hev
  have hnear : ∀ᶠ ζ in nhds η, ∀ y ∈ s, ContDiffAt ℝ 2 (g y) ζ :=
    (Filter.eventually_all_finset s).2 fun y hy => (hg y hy).eventually (by norm_num)
  have hfd : ∀ᶠ ζ in nhds η, fderiv ℝ G ζ = ∑ y ∈ s, fderiv ℝ (g y) ζ := by
    filter_upwards [hev.eventually_nhds, hnear] with ζ h1 h2
    have h1' : G =ᶠ[nhds ζ] fun ζ => ∑ y ∈ s, g y ζ := h1
    rw [h1'.fderiv_eq]
    have := HasFDerivAt.fun_sum (u := s) fun y hy => ((h2 y hy).differentiableAt (by norm_num)).hasFDerivAt
    exact this.fderiv
  refine ⟨hG, fun b e => ?_, fun u v => ?_⟩
  · unfold bondPartialDeriv
    rw [hfd.self_of_nhds, ContinuousLinearMap.sum_apply]
  · unfold secondDerivAlong
    have hev2 : (fun ζ => fderiv ℝ G ζ u) =ᶠ[nhds η] fun ζ => ∑ y ∈ s, fderiv ℝ (g y) ζ u := by
      filter_upwards [hfd] with ζ h
      rw [h, ContinuousLinearMap.sum_apply]
    rw [hev2.fderiv_eq]
    have hd : ∀ y ∈ s, DifferentiableAt ℝ (fun ζ => fderiv ℝ (g y) ζ u) η := fun y hy => by
      have h1 : ContDiffAt ℝ 1 (fderiv ℝ (g y)) η := (hg y hy).fderiv_right (by norm_num)
      exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const u)
    have := HasFDerivAt.fun_sum (u := s) fun y hy => (hd y hy).hasFDerivAt
    rw [this.fderiv, ContinuousLinearMap.sum_apply]
private def pushforwardCLM (j : ι → ↥(chordBonds (finiteCells F))) :
    BondField ι →L[ℝ] StepVariable (finiteCells F) :=
  ∑ i : ι, (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) (j i)).comp
    (ContinuousLinearMap.proj i)
private theorem pushforwardCLM_apply (j : ι → ↥(chordBonds (finiteCells F))) (ζ : BondField ι) :
    pushforwardCLM j ζ = pushforwardField j ζ := by
  funext b
  simp [pushforwardCLM, pushforwardField, Pi.single_apply, Finset.sum_apply, eq_comm]
private theorem pushforwardField_apply_self {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (i : ι) (ζ : BondField ι) :
    pushforwardField j ζ (j i) = ζ i := by
  unfold pushforwardField
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hne
    rw [if_neg (fun h => hne (hj h))]
  · exact fun h => absurd (Finset.mem_univ _) h
private theorem pushforwardField_apply_of_ne {j : ι → ↥(chordBonds (finiteCells F))} {b : ↥(chordBonds (finiteCells F))}
    (hb : ∀ i, j i ≠ b) (ζ : BondField ι) : pushforwardField j ζ b = 0 := by
  unfold pushforwardField
  exact Finset.sum_eq_zero fun i _ => if_neg (hb i)
private theorem pushforwardField_bondVariation (j : ι → ↥(chordBonds (finiteCells F))) (i : ι) (e : BondVector) :
    pushforwardField j (bondVariation i e) = bondVariation (j i) e := by
  funext b
  unfold pushforwardField bondVariation
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_apply, eq_comm]
  · intro i' _ hne
    simp [Pi.single_apply, hne]
  · exact fun h => absurd (Finset.mem_univ _) h
private theorem pushforwardField_norm_lt {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) {ρ : ℝ} (hρ : 0 < ρ)
    {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < ρ) (b : ↥(chordBonds (finiteCells F))) : ‖pushforwardField j ζ b‖ < ρ := by
  by_cases h : ∃ i, j i = b
  · obtain ⟨i, rfl⟩ := h
    rw [pushforwardField_apply_self hj]
    exact hζ i
  · rw [pushforwardField_apply_of_ne (fun i e => h ⟨i, e⟩)]
    simpa using hρ
private theorem abs_sub_bondPartialDeriv_le {ρ c ε x κ B : ℝ} {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (hρ : 0 < ρ)
    {z : F.Cell} {G G' : StepVariable (finiteCells F) → ℝ} (hP : PairedPartsCompare ρ c ε x κ j j z G G')
    (hB : 0 ≤ B)
    (hX : ∀ ξ ∈ openPolyball ι ρ, c * ε * (x * Real.sqrt (weightedSqNormNear κ (fun k => bondBlock F (j k)) (blockDist F) z ξ) + 1) ≤ B)
    {ζ : BondField ι} (hζ : ζ ∈ openPolyball ι ρ) (hd : DifferentiableAt ℝ G (pushforwardField j ζ))
    (hd' : DifferentiableAt ℝ G' (pushforwardField j ζ)) (b : ↥(chordBonds (finiteCells F))) :
    |bondPartialDeriv G' b (pushforwardField j ζ) (pushforwardField j ζ b) - bondPartialDeriv G b (pushforwardField j ζ) (pushforwardField j ζ b)| ≤
      ρ * B * Real.exp (-(2 * κ * blockDist F (bondBlock F b) z)) := by
  by_cases h : ∃ i, j i = b
  · obtain ⟨i, rfl⟩ := h
    rw [pushforwardField_apply_self hj]
    have hdA : HasFDerivAt (fun ζ' => G (pushforwardField j ζ')) ((fderiv ℝ G (pushforwardField j ζ)).comp (pushforwardCLM j)) ζ := by
      have h1 : HasFDerivAt G (fderiv ℝ G (pushforwardCLM j ζ)) (pushforwardCLM j ζ) := by
        rw [pushforwardCLM_apply]
        exact hd.hasFDerivAt
      have h2 := h1.comp ζ (pushforwardCLM j).hasFDerivAt
      rw [pushforwardCLM_apply] at h2
      have e : (fun ζ' => G (pushforwardField j ζ')) = G ∘ pushforwardCLM j := by
        funext ζ'
        simp [pushforwardCLM_apply]
      rw [e]
      exact h2
    have hdB : HasFDerivAt (fun ζ' => G' (pushforwardField j ζ')) ((fderiv ℝ G' (pushforwardField j ζ)).comp (pushforwardCLM j)) ζ := by
      have h1 : HasFDerivAt G' (fderiv ℝ G' (pushforwardCLM j ζ)) (pushforwardCLM j ζ) := by
        rw [pushforwardCLM_apply]
        exact hd'.hasFDerivAt
      have h2 := h1.comp ζ (pushforwardCLM j).hasFDerivAt
      rw [pushforwardCLM_apply] at h2
      have e : (fun ζ' => G' (pushforwardField j ζ')) = G' ∘ pushforwardCLM j := by
        funext ζ'
        simp [pushforwardCLM_apply]
      rw [e]
      exact h2
    have hD := hdB.sub hdA
    have hval : bondPartialDeriv G' (j i) (pushforwardField j ζ) (ζ i) - bondPartialDeriv G (j i) (pushforwardField j ζ) (ζ i) =
        fderiv ℝ (fun ζ' => G' (pushforwardField j ζ') - G (pushforwardField j ζ')) ζ (bondVariation i (ζ i)) := by
      have : fderiv ℝ (fun ζ' => G' (pushforwardField j ζ') - G (pushforwardField j ζ')) ζ = _ := hD.fderiv
      rw [this]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, pushforwardCLM_apply, pushforwardField_bondVariation, bondPartialDeriv]
    rw [hval]
    have hle : |fderiv ℝ (fun ζ' => G' (pushforwardField j ζ') - G (pushforwardField j ζ')) ζ (bondVariation i (ζ i))| ≤
        bondGradNorm (fun ζ' => G' (pushforwardField j ζ') - G (pushforwardField j ζ')) i ζ * ‖ζ i‖ :=
      ((fderiv ℝ (fun ζ' => G' (pushforwardField j ζ') - G (pushforwardField j ζ')) ζ).comp
        (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) i)).le_opNorm _
    have h1 := (hP ζ hζ).2 i
    have hn : ‖ζ i‖ ≤ ρ := (hζ i).le
    have h2 := hX ζ hζ
    have he := (Real.exp_pos (-(2 * κ * blockDist F (bondBlock F (j i)) z))).le
    calc _ ≤ _ := hle
      _ ≤ (B * Real.exp (-(2 * κ * blockDist F (bondBlock F (j i)) z))) * ρ :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_right h2 he)) hn (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [pushforwardField_apply_of_ne (fun i e => h ⟨i, e⟩)]
    have : bondVariation b (0 : BondVector) = 0 := by simp [bondVariation]
    simp only [bondPartialDeriv, this, map_zero, sub_self, abs_zero]
    positivity
private theorem IsCutoffDominated.mono {ρ κ M M' : ℝ} {p : ℝ → ℝ} {q : ℕ} {Y : F.Cell} {A : StepVariable (finiteCells F) → ℝ}
    (h : IsCutoffDominated ρ κ M p q Y A) (hM : M ≤ M') : IsCutoffDominated ρ κ M' p q Y A := by
  have hg : ∀ η : StepVariable (finiteCells F), 0 ≤ cutoffMajorant p Y η := fun η => by
    unfold cutoffMajorant ColdHalfLaw.sumOverBlock
    have : 0 ≤ ∑ b : ↥(chordBonds (finiteCells F)), (open Classical in if enclosingCell b.1.1 = Y then
        |deriv p ‖η b‖| + |deriv (deriv p) ‖η b‖| else 0) :=
      Finset.sum_nonneg fun b _ => by split_ifs <;> positivity
    linarith
  refine ⟨h.smooth, fun η hη => (h.abs_le η hη).trans (mul_le_mul_of_nonneg_right hM (hg η)), fun η hη b =>
    (h.gradient_le η hη b).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le) (hg η)),
    fun η hη => (h.freeze_le η hη).trans (mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le)⟩
private theorem norm_freezeOutside_lt {ρ : ℝ} (hρ : 0 < ρ) (Λ : Finset ↥(chordBonds (finiteCells F))) {η : StepVariable (finiteCells F)}
    (hη : ∀ b, ‖η b‖ < ρ) (b : ↥(chordBonds (finiteCells F))) : ‖freezeOutside Λ η b‖ < ρ := by
  classical
  unfold freezeOutside _root_.YangMills.Construction.Interpolation.extendByZero
  by_cases hb : b ∈ Λ
  · rw [Finset.sum_eq_single b]
    · simpa using hη b
    · intro b' _ hne
      simp [hne]
    · exact fun h => absurd hb h
  · rw [Finset.sum_eq_zero]
    · simpa using hρ
    · intro b' hb'
      have : b' ≠ b := fun e => hb (e ▸ hb')
      simp [this]
private theorem IsCutoffDominated.congr {ρ κ M : ℝ} {p : ℝ → ℝ} {q : ℕ} {Y : F.Cell} {A B : StepVariable (finiteCells F) → ℝ}
    (hρ : 0 < ρ) (h : IsCutoffDominated ρ κ M p q Y B) (hAB : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → A η = B η) :
    IsCutoffDominated ρ κ M p q Y A := by
  refine ⟨h.smooth.congr fun η hη => hAB η hη, fun η hη => ?_, fun η hη b => ?_, fun η hη => ?_⟩
  · rw [hAB η hη]
    exact h.abs_le η hη
  · have hev : A =ᶠ[nhds η] B := by
      filter_upwards [(isOpen_polyball ρ).mem_nhds hη] with ζ hζ
      exact hAB ζ hζ
    have : bondGradNorm A b η = bondGradNorm B b η := by
      unfold bondGradNorm
      rw [hev.fderiv_eq]
    rw [this]
    exact h.gradient_le η hη b
  · rw [hAB η hη, hAB _ (norm_freezeOutside_lt hρ _ hη)]
    exact h.freeze_le η hη
private theorem areUnitVectors_empty : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun i => i.elim0
private theorem cellSupDist_le_bondSpanWithCell {k : ℕ} (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x) (Y z : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) : (cellSupDist z Y : ℝ) ≤ (bondSpanWithCell Y z c : ℝ) := by
  have h1 : cellSupDist Y z ≤ bondSpanWithCell Y z c := by
    unfold bondSpanWithCell bondSpan
    refine le_max_of_le_left ?_
    exact Finset.le_sup (f := fun l : Fin (k + 1) =>
      siteSupDist Y ((Fin.cons ((z, 0) : F.Site F.top × Fin 4) c : Fin (k + 1) → F.Site F.top × Fin 4) l).1)
      (Finset.mem_univ (0 : Fin (k + 1)))
  rw [hsym z Y]
  exact_mod_cast h1
private theorem cellSupDist_le_chordBondSpan (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x) (Y : F.Cell)
    (b b' : ↥(chordBonds (finiteCells F))) : (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤ (chordBondSpan Y ![b, b'] : ℝ) ∧
      (cellSupDist (enclosingCell b'.1.1) Y : ℝ) ≤ (chordBondSpan Y ![b, b'] : ℝ) := by
  have h : ∀ l : Fin 2, cellSupDist Y (enclosingCell (![b, b'] l).1.1) ≤ chordBondSpan Y ![b, b'] := fun l => by
    unfold chordBondSpan bondSpan
    refine le_max_of_le_left ?_
    exact Finset.le_sup (f := fun l : Fin 2 => siteSupDist Y (enclosingCell (![b, b'] l).1.1, (0 : Fin 4)).1) (Finset.mem_univ l)
  constructor
  · rw [hsym _ Y]
    exact_mod_cast h 0
  · rw [hsym _ Y]
    exact_mod_cast h 1
private theorem blockExpansion_bounds {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {f : LocalFamily} {W : F.GaugeField F.top} {Y : F.Cell} {Ns : ℕ} (hκ : 0 < T.κ)
    (hE : 0 ≤ T.E)
    (hRB : CentredExpansionBounds false T.a T.chainParams.ρA T.ballRadius T.κ T.decayRate T.E T.energyRatio T.Ct T.L (frameRadius x) f W)
    (hf4 : ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F)),
      interpolatedExpansion 1 T.a T.chainParams.ρA (frameRadius x) f y η W = centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y η W)
    (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (hNs : (open Classical in ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card) ≤ Ns)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < T.ballRadius) :
    ContDiffAt ℝ 2 (fun ζ => interpolatedBlockExpansion 1 T.a T.chainParams.ρA (frameRadius x) f Y ζ W) η ∧
    (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
      |bondPartialDeriv (fun ζ => interpolatedBlockExpansion 1 T.a T.chainParams.ρA (frameRadius x) f Y ζ W) b η e| ≤
        Ns * (|T.Ct| * T.E) * Real.exp (-(16 * T.κ * bondDistToCell Y b)) * ‖e‖) ∧
    (∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
      |secondDerivAlong (fun ζ => interpolatedBlockExpansion 1 T.a T.chainParams.ρA (frameRadius x) f Y ζ W) η (bondVariation b e) (bondVariation b' e')| ≤
        Ns * (|T.Ct| * T.E) * Real.exp (-(16 * T.κ * bondDistToCell Y b)) * Real.exp (-(16 * T.κ * bondDistToCell Y b')) * ‖e‖ * ‖e'‖) ∧
    (coldHalfLawAt T x f).familyTerm Y η W =
      radialPart Finset.univ (fun ζ => interpolatedBlockExpansion 1 T.a T.chainParams.ρA (frameRadius x) f Y ζ W) η := by
  classical
  set Ys := (sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y with hYs
  set g : F.Site F.depth → StepVariable (finiteCells F) → ℝ := fun y ζ => interpolatedExpansion 1 T.a T.chainParams.ρA (frameRadius x) f y ζ W with hgd
  have hgfun : ∀ y, g y = fun ζ => centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y ζ W := fun y => funext fun ζ => hf4 y ζ
  have hcl : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
  have hg : ∀ y ∈ Ys, ContDiffAt ℝ 2 (g y) η := fun y _ => by
    rw [hgfun]
    have := contDiffAt_of_empty_move (fun ζ V' => centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y ζ V') W η
      (hRB.smooth y η 0 Fin.elim0 Fin.elim0 hcl)
    exact this.of_le (by norm_num)
  have hsum := derivs_of_finset_sum Ys g (G := fun ζ => interpolatedBlockExpansion 1 T.a T.chainParams.ρA (frameRadius x) f Y ζ W) (η := η)
    (Filter.Eventually.of_forall fun ζ => rfl) hg
  obtain ⟨h2, hpart, hsec⟩ := hsum
  have hcE : 0 ≤ |T.Ct| * T.E := by positivity
  have hNc : (Ys.card : ℝ) ≤ Ns := by
    have : Ys.card ≤ Ns := by
      convert hNs
    exact_mod_cast this
  have hone : ∀ (y : F.Site F.depth), y ∈ Ys → ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector), ‖e‖ = 1 →
      |bondPartialDeriv (g y) b η e| ≤ |T.Ct| * T.E * Real.exp (-(16 * T.κ * bondDistToCell Y b)) := fun y hy b e he => by
    have hcell : enclosingCell y = Y := (Finset.mem_filter.1 hy).2
    have h1 := hRB.deriv_top_partial y η b e 0 Fin.elim0 Fin.elim0 hη (by norm_num) areUnitVectors_empty he
    rw [bondDeriv_empty, hcell, if_neg (by norm_num)] at h1
    rw [hgfun]
    refine h1.trans ?_
    have hs := cellSupDist_le_bondSpanWithCell hsym Y (enclosingCell b.1.1) (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
    have hle : Real.exp (-(2 ^ 5 * T.κ * (bondSpanWithCell Y (enclosingCell b.1.1) (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : ℝ))) ≤
        Real.exp (-(16 * T.κ * bondDistToCell Y b)) := by
      refine Real.exp_le_exp.2 ?_
      unfold bondDistToCell
      have : (0 : ℝ) ≤ cellSupDist (enclosingCell b.1.1) Y := by positivity
      nlinarith
    calc T.Ct * T.E * _ ≤ |T.Ct| * T.E * _ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hE) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hle hcE
  have htwo : ∀ (y : F.Site F.depth), y ∈ Ys → ∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector), ‖e‖ = 1 → ‖e'‖ = 1 →
      |secondDerivAlong (g y) η (bondVariation b e) (bondVariation b' e')| ≤
        |T.Ct| * T.E * (Real.exp (-(16 * T.κ * bondDistToCell Y b)) * Real.exp (-(16 * T.κ * bondDistToCell Y b'))) :=
    fun y hy b b' e e' he he' => by
    have hcell : enclosingCell y = Y := (Finset.mem_filter.1 hy).2
    have h1 := hRB.second_deriv y η b b' e e' hη he he'
    rw [hcell] at h1
    rw [hgfun]
    refine h1.trans ?_
    obtain ⟨hs, hs'⟩ := cellSupDist_le_chordBondSpan hsym Y b b'
    have hle : Real.exp (-(2 ^ 5 * T.κ * (chordBondSpan Y ![b, b'] : ℝ))) ≤
        Real.exp (-(16 * T.κ * bondDistToCell Y b)) * Real.exp (-(16 * T.κ * bondDistToCell Y b')) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      unfold bondDistToCell
      nlinarith
    calc T.Ct * T.E * _ ≤ |T.Ct| * T.E * _ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hE) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hle hcE
  refine ⟨h2, fun b e => ?_, fun b b' e e' => ?_, ?_⟩
  · have hu : ∀ e : BondVector, ‖e‖ = 1 →
        |bondPartialDeriv (fun ζ => interpolatedBlockExpansion 1 T.a T.chainParams.ρA (frameRadius x) f Y ζ W) b η e| ≤
          Ns * (|T.Ct| * T.E) * Real.exp (-(16 * T.κ * bondDistToCell Y b)) := fun e he => by
      rw [hpart]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun y hy => hone y hy b e he).trans ?_)
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNc hcE) (Real.exp_pos _).le
    exact abs_bondPartialDeriv_le_mul_norm hu e
  · have hB : 0 ≤ Ns * (|T.Ct| * T.E) * Real.exp (-(16 * T.κ * bondDistToCell Y b)) * Real.exp (-(16 * T.κ * bondDistToCell Y b')) := by
      positivity
    refine abs_secondDerivAlong_le_mul_norm h2 hB (fun e e' he he' => ?_) e e'
    rw [hsec]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun y hy => htwo y hy b b' e e' he he').trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    calc _ ≤ (Ns : ℝ) * (|T.Ct| * T.E * (Real.exp (-(16 * T.κ * bondDistToCell Y b)) * Real.exp (-(16 * T.κ * bondDistToCell Y b')))) :=
          mul_le_mul_of_nonneg_right hNc (by positivity)
      _ = _ := by ring
  · unfold ColdHalfLaw.familyTerm radialPart
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => (hpart b (η b)).symm
private theorem interpolatedExponent_bounds {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {W : F.GaugeField F.top} {Y : F.Cell} {X Wc : ℝ}
    (hκ : 0 < T.κ) (hx : 0 ≤ x) (hX : 0 ≤ X) (hWc0 : 0 ≤ Wc)
    (hPB : InterpolatedPartsSmooth 1 T.a T.chainParams.ρA T.ballRadius x (frameRadius x) W)
    (hEB : InterpolatedExponentBounds 1 T.a T.chainParams.ρA T.ballRadius x T.κ T.Cs (frameRadius x) W)
    (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (hsq : ∀ (z : F.Cell) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ < T.ballRadius) →
      x * Real.sqrt (localSqNorm T.κ z η) + 1 ≤ X)
    (hWc : ∑ z ∈ finiteCells F, Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ))) ≤ Wc)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < T.ballRadius) :
    (∀ z, DifferentiableAt ℝ (interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) z W) η) ∧
    ContDiffAt ℝ 2 (interpolatedExponent 1 T.a T.chainParams.ρA x (frameRadius x) W) η ∧
    (∀ (z : F.Cell) (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
      |bondPartialDeriv (interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) z W) b η e| ≤
        |T.Cs| * X * Real.exp (-(2 ^ 6 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) * ‖e‖) ∧
    (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
      bondPartialDeriv (interpolatedExponent 1 T.a T.chainParams.ρA x (frameRadius x) W) b η e =
        ∑ z ∈ finiteCells F, bondPartialDeriv (interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) z W) b η e) ∧
    (∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector), enclosingCell b.1.1 = Y →
      |secondDerivAlong (interpolatedExponent 1 T.a T.chainParams.ρA x (frameRadius x) W) η (bondVariation b e) (bondVariation b' e')| ≤
        |T.Cs| * x * Wc * Real.exp (-(16 * T.κ * bondDistToCell Y b')) * ‖e‖ * ‖e'‖) := by
  classical
  set m := frameRadius x with hm
  set ψ : F.Cell → StepVariable (finiteCells F) → ℝ := fun z => interpolatedBlockExponent 1 T.a T.chainParams.ρA x m z W with hψ
  have hcl : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
  have hg3 : ∀ z, ContDiffAt ℝ 2 (ψ z) η := fun z => by
    have := contDiffAt_of_empty_move (fun ζ V' => interpolatedBlockExponent 1 T.a T.chainParams.ρA x m z V' ζ) W η
      (hPB.smooth z η 0 Fin.elim0 Fin.elim0 hcl)
    exact this.of_le (by norm_num)
  have hev : interpolatedExponent 1 T.a T.chainParams.ρA x m W =ᶠ[nhds η] fun ζ => ∑ z ∈ finiteCells F, ψ z ζ := by
    filter_upwards [(isOpen_polyball T.ballRadius).mem_nhds hη] with ζ hζ
    exact hPB.sum_eq ζ hζ
  obtain ⟨h2, hpart, hsec⟩ := derivs_of_finset_sum (finiteCells F) ψ hev fun z _ => hg3 z
  have hCs : 0 ≤ |T.Cs| := abs_nonneg _
  have hone : ∀ (z : F.Cell) (b : ↥(chordBonds (finiteCells F))) (e : BondVector), ‖e‖ = 1 →
      |bondPartialDeriv (ψ z) b η e| ≤ |T.Cs| * X * Real.exp (-(2 ^ 6 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) := fun z b e he => by
    have h1 := hEB.deriv_top_partial z η b e 0 Fin.elim0 Fin.elim0 hη (by norm_num) areUnitVectors_empty he
    rw [bondDeriv_empty] at h1
    refine h1.trans ?_
    have hs := cellSupDist_le_bondSpanWithCell hsym z (enclosingCell b.1.1) (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
    have hle : Real.exp (-(2 ^ 6 * T.κ * (bondSpanWithCell z (enclosingCell b.1.1) (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : ℝ))) ≤
        Real.exp (-(2 ^ 6 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) := by
      refine Real.exp_le_exp.2 ?_
      have : 0 < (2 : ℝ) ^ 6 * T.κ := by positivity
      nlinarith
    have hs0 := hsq z η hη
    have hs1 : 0 ≤ x * Real.sqrt (localSqNorm T.κ z η) + 1 := by positivity
    calc T.Cs * _ * _ ≤ |T.Cs| * X * Real.exp (-(2 ^ 6 * T.κ * (bondSpanWithCell z (enclosingCell b.1.1) (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul (le_abs_self _) hs0 hs1 hCs
      _ ≤ _ := mul_le_mul_of_nonneg_left hle (by positivity)
  have hsec1 : ∀ (z : F.Cell) (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector), enclosingCell b.1.1 = Y → ‖e‖ = 1 → ‖e'‖ = 1 →
      |secondDerivAlong (ψ z) η (bondVariation b e) (bondVariation b' e')| ≤
        |T.Cs| * x * Real.exp (-(16 * T.κ * bondDistToCell Y b')) * Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ))) :=
    fun z b b' e e' hb he he' => by
    have h1 := hEB.second_deriv z η b b' e e' hη he he'
    refine h1.trans ?_
    have hu : cellSupDist z Y ≤ max (cellSupDist z (enclosingCell b.1.1)) (max (cellSupDist z (enclosingCell b'.1.1)) (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1))) := by
      rw [hb]
      exact le_max_left _ _
    have hv : cellSupDist (enclosingCell b'.1.1) Y ≤ max (cellSupDist z (enclosingCell b.1.1)) (max (cellSupDist z (enclosingCell b'.1.1)) (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1))) := by
      rw [hb, hsym (enclosingCell b'.1.1) Y]
      exact le_max_of_le_right (le_max_right _ _)
    have hu' : (cellSupDist z Y : ℝ) ≤ ((max (cellSupDist z (enclosingCell b.1.1)) (max (cellSupDist z (enclosingCell b'.1.1)) (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1))) : ℕ) : ℝ) := by
      exact_mod_cast hu
    have hv' : (cellSupDist (enclosingCell b'.1.1) Y : ℝ) ≤ ((max (cellSupDist z (enclosingCell b.1.1)) (max (cellSupDist z (enclosingCell b'.1.1)) (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1))) : ℕ) : ℝ) := by
      exact_mod_cast hv
    have hle : Real.exp (-(2 ^ 6 * T.κ * ((max (cellSupDist z (enclosingCell b.1.1)) (max (cellSupDist z (enclosingCell b'.1.1)) (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1))) : ℕ) : ℝ))) ≤
        Real.exp (-(16 * T.κ * bondDistToCell Y b')) * Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ))) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      unfold bondDistToCell
      nlinarith
    calc T.Cs * x * _ ≤ |T.Cs| * x * _ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hx) (Real.exp_pos _).le
      _ ≤ |T.Cs| * x * (Real.exp (-(16 * T.κ * bondDistToCell Y b')) * Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ)))) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = _ := by ring
  refine ⟨fun z => (hg3 z).differentiableAt (by norm_num), h2.congr_of_eventuallyEq (Filter.EventuallyEq.refl _ _), fun z b e => ?_, hpart, fun b b' e e' hb => ?_⟩
  · have hB : ∀ e : BondVector, ‖e‖ = 1 → |bondPartialDeriv (ψ z) b η e| ≤ |T.Cs| * X * Real.exp (-(2 ^ 6 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) :=
      fun e he => hone z b e he
    exact abs_bondPartialDeriv_le_mul_norm hB e
  · have hB : 0 ≤ |T.Cs| * x * Wc * Real.exp (-(16 * T.κ * bondDistToCell Y b')) := by positivity
    refine abs_secondDerivAlong_le_mul_norm h2 hB (fun e e' he he' => ?_) e e'
    rw [hsec]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun z _ => hsec1 z b b' e e' hb he he').trans ?_)
    rw [← Finset.mul_sum]
    calc _ ≤ |T.Cs| * x * Real.exp (-(16 * T.κ * bondDistToCell Y b')) * Wc :=
          mul_le_mul_of_nonneg_left hWc (by positivity)
      _ = _ := by ring
private theorem exists_offset_of_cell {z Y : F.Cell} (hper : ∀ i, NeZero (F.period F.top i)) :
    ∃ o : Fin 4 → ℤ, z = Y + siteOfCoords F.top o ∧ ∀ i, |o i| ≤ (cellSupDist z Y : ℤ) := by
  refine ⟨fun i => (z i - Y i).valMinAbs, ?_, fun i => ?_⟩
  · funext i
    have := hper i
    simp [siteOfCoords, ZMod.coe_valMinAbs]
  · have h1 : ((z i - Y i).valMinAbs).natAbs ≤ cellSupDist z Y :=
      Finset.le_sup (f := fun i => ((z i - Y i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h2 : |(z i - Y i).valMinAbs| = (((z i - Y i).valMinAbs).natAbs : ℤ) := Int.abs_eq_natAbs _
    show |(z i - Y i).valMinAbs| ≤ _
    rw [h2]
    exact_mod_cast h1
private theorem sqrt_le_one_add_self {u : ℝ} (hu : 0 ≤ u) : Real.sqrt u ≤ 1 + u := by
  have h := Real.sq_sqrt hu
  nlinarith [sq_nonneg (Real.sqrt u - 1)]
set_option maxHeartbeats 2000000 in
theorem radialPartsComparable (hJ : EventuallyInParametersCombines) (hPS : interpolatedPartsSmoothStatement)
    (hEnds : interpolationAtEndpoints) (hFB : interpolatedFramesStatement)
    (hRw : CentredExpansionsBounded) (hTC : InterpolatedTermsCloseOnTwoTori)
    (hMaj : DominatedObservablesComparable) (hRad : radialPartDominatedStatement)
    (hS : _root_.YangMills.Construction.CellCounting.ExpDecaySumBounded) (hFew : cellBondsCardStatement)
    (hSites : SitesPerCellLePow) (hG : CubicTorusCellGeometry) : radialPartsComparableStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cq, Cz, Cr, hP⟩ := hFB
  obtain ⟨hg1, -⟩ := hG
  have h2 : EventuallyInParameters fun T => 64 ≤ T.n₀ ∧ 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨64, fun _ h => ⟨0, fun _ _ => ⟨1, fun _ hy => ⟨h, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine weaken _ _ ?_ (join _ _ hP (join _ _ h2 (join _ _ hPS (join _ _ hRw (join _ _ hTC hMaj)))))
  rintro T hDr ⟨hPT, ⟨hn2, hy1⟩, hPST, hRwT, hTCT, CM, hCM, hMT⟩
  intro t x f hfl hrow
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  have hκ : 0 < T.κ := hDr.κ_pos
  have hx1 : 1 ≤ x := hy1.trans hfl
  have hx : 0 ≤ x := by linarith
  have hE : 0 ≤ T.E := le_trans zero_le_one hDr.one_le_E
  set N : ℕ := 4 * T.L ^ 4 with hNdef
  obtain ⟨CR, hCR, hRadT⟩ := hRad N T.ballRadius T.κ hρ hκ
  obtain ⟨W3, hW30, hW3⟩ := hS N (2 ^ 5 * T.κ) (by positivity)
  obtain ⟨Wb, hWb0, hWb⟩ := hS N (2 * T.κ) (by positivity)
  obtain ⟨Wc, hWc0, hWc⟩ := hS 1 (2 * T.κ) (by positivity)
  set X : ℝ := x * (1 + T.ballRadius ^ 2 * W3) + 1 with hXdef
  have hX : 0 ≤ X := by positivity
  have setup : ∀ F : BlockFrame, IsCubicTopTorus T.L t T.n₀ F →
      (∀ x y : F.Cell, cellSupDist x y = cellSupDist y x) ∧
      (∀ z : F.Cell, (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤ N) ∧
      (∀ Y : F.Cell, ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card ≤ T.L ^ 4) ∧
      (∀ i, NeZero (F.period F.top i)) ∧ ∀ i, 2 ≤ F.extent i := fun F htop => by
    obtain ⟨hLF, htt, n, hside, hn⟩ := id htop
    have hoddF : Odd F.blockSide := by rw [hLF]; exact hDr.odd_L
    have hnpos : 64 ≤ n := hn2.trans hn
    have hcub : IsLargeCubicTorus F := ⟨n, hnpos, hside⟩
    obtain ⟨-, -, hsym, -, -⟩ := hg1 F hoddF hcub
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    refine ⟨hsym, fun z => ?_, fun Y => ?_, fun i => ⟨by rw [hper, hside]; omega⟩, fun i => by rw [hside]; omega⟩
    · have := hFew F hoddF (fun i => by rw [hside]; omega) z
      rw [hLF] at this
      convert this
    · have := hSites F (finiteCells F) hoddF (fun i => by rw [hside]; omega) Y
      rw [hLF] at this
      refine le_trans (le_of_eq ?_) this
      have e : ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y) =
          (Finset.univ.filter fun y : ↥(sitesOfCells (finiteCells F) F.depth) => enclosingCell y.1 = Y).map (Function.Embedding.subtype _) := by
        ext y
        constructor
        · intro h
          exact Finset.mem_map.2 ⟨⟨y, (Finset.mem_filter.1 h).1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 h).2⟩, rfl⟩
        · intro h
          obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 h
          exact Finset.mem_filter.2 ⟨y'.2, (Finset.mem_filter.1 hy').2⟩
      rw [e, Finset.card_map]
  have hsqC : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ (z : F.Cell) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ < T.ballRadius) →
      x * Real.sqrt (localSqNorm T.κ z η) + 1 ≤ X := fun F htop z η hη => by
    obtain ⟨-, hN, -, -, -⟩ := setup F htop
    have hs : localSqNorm T.κ z η ≤ T.ballRadius ^ 2 * W3 := by
      unfold localSqNorm
      have h1 : ∀ b ∈ (Finset.univ : Finset ↥(chordBonds (finiteCells F))),
          Real.exp (-(2 ^ 6 * T.κ * cellSupDist (enclosingCell b.1.1) z)) * ‖η b‖ ^ 2 ≤
            T.ballRadius ^ 2 * Real.exp (-(2 ^ 5 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) := fun b _ => by
        have h2 : ‖η b‖ ^ 2 ≤ T.ballRadius ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hη b).le 2
        have h3 : Real.exp (-(2 ^ 6 * T.κ * cellSupDist (enclosingCell b.1.1) z)) ≤ Real.exp (-(2 ^ 5 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) := by
          refine Real.exp_le_exp.2 ?_
          have : (0 : ℝ) ≤ cellSupDist (enclosingCell b.1.1) z := by positivity
          nlinarith
        calc _ ≤ Real.exp (-(2 ^ 5 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) * T.ballRadius ^ 2 :=
              mul_le_mul h3 h2 (by positivity) (Real.exp_pos _).le
          _ = _ := by ring
      refine (Finset.sum_le_sum h1).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hW3 F _ (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) (fun z' => by convert hN z') z) (by positivity)
    have hs0 : 0 ≤ localSqNorm T.κ z η := by
      unfold localSqNorm
      exact Finset.sum_nonneg fun b _ => by positivity
    have := sqrt_le_one_add_self hs0
    have h3 : Real.sqrt (localSqNorm T.κ z η) ≤ 1 + T.ballRadius ^ 2 * W3 := by linarith
    have := mul_le_mul_of_nonneg_left h3 hx
    simp only [hXdef]
    linarith
  have hsqV : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (j : ι → ↥(chordBonds (finiteCells F))), Function.Injective j → ∀ (z : F.Cell) (ξ : BondField ι), ξ ∈ openPolyball ι T.ballRadius →
      x * Real.sqrt (weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F) z ξ) + 1 ≤ X := fun F htop ι _ _ j hj z ξ hξ => by
    obtain ⟨-, hN, -, -, -⟩ := setup F htop
    have hfib : ∀ z' : F.Cell, (Finset.univ.filter fun i : ι => enclosingCell (j i).1.1 = z').card ≤ N := fun z' => by
      refine le_trans ?_ (hN z')
      exact Finset.card_le_card_of_injOn j (fun i hi => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
        exact hi) (fun a _ b _ h => hj h)
    have hs : weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F) z ξ ≤ T.ballRadius ^ 2 * W3 := by
      unfold weightedSqNormNear
      have h1 : ∀ k ∈ (Finset.univ : Finset ι), Real.exp (-(2 ^ 5 * T.κ * blockDist F (bondBlock F (j k)) z)) * ‖ξ k‖ ^ 2 ≤
          T.ballRadius ^ 2 * Real.exp (-(2 ^ 5 * T.κ * (cellSupDist (enclosingCell (j k).1.1) z : ℝ))) := fun k _ => by
        have h2 : ‖ξ k‖ ^ 2 ≤ T.ballRadius ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hξ k).le 2
        calc _ ≤ Real.exp (-(2 ^ 5 * T.κ * blockDist F (bondBlock F (j k)) z)) * T.ballRadius ^ 2 :=
              mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
          _ = _ := by
            unfold blockDist bondBlock
            ring
      refine (Finset.sum_le_sum h1).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hW3 F ι (fun k => enclosingCell (j k).1.1) (fun z' => by convert hfib z') z) (by positivity)
    have hs0 : 0 ≤ weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F) z ξ := by
      unfold weightedSqNormNear
      exact Finset.sum_nonneg fun b _ => by positivity
    have := sqrt_le_one_add_self hs0
    have h3 : Real.sqrt (weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F) z ξ) ≤ 1 + T.ballRadius ^ 2 * W3 := by linarith
    have := mul_le_mul_of_nonneg_left h3 hx
    simp only [hXdef]
    linarith
  set Ar : ℝ := ((T.L ^ 4 : ℕ) : ℝ) * (|T.Ct| * T.E) with hAr
  have hAr0 : 0 ≤ Ar := by positivity
  set Mr : ℝ := CR * Ar + T.ballRadius * (|T.Ct * T.energyRatio| * X) * Wb with hMr
  have hMr0 : 0 ≤ Mr := by positivity
  set Ae : ℝ := |T.Cs| * (X + x) * Wc with hAe
  have hAe0 : 0 ≤ Ae := by positivity
  set Me : ℝ := CR * Ae + N * (T.ballRadius * ((|T.Ct| + 2 * |T.Cs|) * X) * Wc) with hMe
  have hMe0 : 0 ≤ Me := by positivity
  have hCompare : ∀ (F : BlockFrame) (V V' : F.GaugeField F.top) (Y : F.Cell) (q : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
      (j : ι → ↥(chordBonds (finiteCells F))) (o : Fin 4 → ℤ), IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
      IsSmallCurvature (5 / 4 * T.σ) V' → AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → IsShortPairing Y Y q j j →
      T.blockIndex ≤ q → (∀ i, 8 * |o i| ≤ (q : ℤ)) → InterpolatedComparisonSetting T t x 1 f V V' Y Y q j j o :=
    fun F V V' Y q ι _ _ j o htop hV hV' hag hpair hq ho => by
    refine ⟨hfl, ⟨zero_le_one, le_rfl⟩, ⟨hrow.smooth, hrow.gauge_invariant, hrow.translation_invariant, hrow.decay, hrow.locality⟩, htop, htop, hV, hV', hag, hq,
      hpair.isBoxPairing.injective_left, hpair.isBoxPairing.injective_right, fun i => ?_, ho⟩
    obtain ⟨h, u, k, hh, hu, e, e'⟩ := hpair.short_offsets i
    refine ⟨h, u, k, hu, fun l => ?_, e, e'⟩
    have := hh l
    have h0 := abs_nonneg (h l)
    omega
  refine ⟨⟨CM * Mr, by positivity, ?_⟩, ⟨CM * Me, by positivity, ?_⟩⟩
  · intro F V V' Y q ι _ _ j htop hV hV' hag hpair
    obtain ⟨hsym, hN, hNs, hper, hsd⟩ := setup F htop
    have hends : ∀ W : F.GaugeField F.top, ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F)),
        interpolatedExpansion 1 T.a T.chainParams.ρA (frameRadius x) f y η W = centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y η W :=
      fun W y η => by
      have := (hEnds F false T.a T.chainParams.ρA T.chainParams.lam x 0 (frameRadius x) W).2.2.2.1 f y η
      simpa [segmentEnd] using this
    have facts := fun (W : F.GaugeField F.top) (hW : IsSmallCurvature (5 / 4 * T.σ) W) (η : StepVariable (finiteCells F))
      (hη : ∀ b, ‖η b‖ < T.ballRadius) => blockExpansion_bounds (T := T) (x := x) (f := f) (Y := Y) (Ns := T.L ^ 4) hκ hE
        (hRwT t x f F W false hfl hrow htop hW) (hends W) hsym (hNs Y) hη
    have maj : ∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) W →
        IsCutoffDominated T.ballRadius T.κ Mr T.p q Y (fun η => (coldHalfLawAt T x f).familyTerm Y η W) := fun W hW => by
      have h1 := hRadT F Y T.p q Finset.univ (fun ζ => interpolatedBlockExpansion 1 T.a T.chainParams.ρA (frameRadius x) f Y ζ W) Ar
        (fun z => by convert hN z) hAr0 (fun η hη => (facts W hW η hη).1)
        (fun η hη b _ e => (facts W hW η hη).2.1 b e) (fun η hη b _ b' e e' => (facts W hW η hη).2.2.1 b b' e e')
      have hle : CR * Ar ≤ Mr := by
        simp only [hMr]
        have : 0 ≤ T.ballRadius * (|T.Ct * T.energyRatio| * X) * Wb := by positivity
        linarith
      exact (h1.mono hle).congr hρ fun η hη => (facts W hW η hη).2.2.2
    refine hMT t x f F V V' Y q ι j ((coldHalfLawAt T x f).familyTerm Y) Mr hfl hrow htop hV hV' hpair hMr0 (maj V hV) (maj V' hV') fun hq ζ hζ => ?_
    set ε := Real.exp (-(4 * T.κ * q)) with hε
    have hε0 : 0 ≤ ε := (Real.exp_pos _).le
    have hinj := hpair.isBoxPairing.injective_left
    have hon : ∀ b, ‖toTorus j ζ b‖ < T.ballRadius := pushforwardField_norm_lt hinj hρ hζ
    have f1 := facts V hV _ hon
    have f2 := facts V' hV' _ hon
    rw [f1.2.2.2, f2.2.2.2]
    have hY0 : Y + siteOfCoords F.top 0 = Y := by
      funext i
      simp [siteOfCoords]
    have hcs := hCompare F V V' Y q ι j 0 htop hV hV' hag hpair hq (fun i => by simp)
    have hcomp := (hTCT t x 1 f F F V V' Y Y q ι j j 0 hcs).2
    rw [hY0] at hcomp
    set B := |T.Ct * T.energyRatio| * ε * X with hB
    have hB0 : 0 ≤ B := by positivity
    have hXc : ∀ ξ ∈ openPolyball ι T.ballRadius, T.Ct * T.energyRatio * ε *
        (x * Real.sqrt (weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F) Y ξ) + 1) ≤ B := fun ξ hξ => by
      have h1 := hsqV F htop ι j hinj Y ξ hξ
      have h2 : 0 ≤ x * Real.sqrt (weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F) Y ξ) + 1 := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hε0) h1 h2 (by positivity)
    have hterm := fun b => abs_sub_bondPartialDeriv_le hinj hρ hcomp hB0 hXc hζ (f1.1.differentiableAt (by norm_num))
      (f2.1.differentiableAt (by norm_num)) b
    unfold radialPart
    rw [← Finset.sum_sub_distrib]
    have hsum : ∑ b : ↥(chordBonds (finiteCells F)), T.ballRadius * B * Real.exp (-(2 * T.κ * blockDist F (bondBlock F b) Y)) ≤ T.ballRadius * B * Wb := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hWb F _ (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) (fun z' => by convert hN z') Y) (by positivity)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun b _ => ?_).trans (hsum.trans ?_))
    · rw [abs_sub_comm]
      exact hterm b
    · have h0 : 0 ≤ CR * Ar := by positivity
      have : T.ballRadius * B * Wb = (T.ballRadius * (|T.Ct * T.energyRatio| * X) * Wb) * ε := by
        simp only [hB]
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by simp only [hMr]; linarith) hε0
  · intro F V V' Y q ι _ _ j htop hV hV' hag hpair
    obtain ⟨hsym, hN, hNs, hper, hsd⟩ := setup F htop
    have hCc : ∑ z ∈ finiteCells F, Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ))) ≤ Wc := by
      have := hWc F ↥(finiteCells F) Subtype.val (fun z => Finset.card_le_one.2 fun a ha b hb => by
        have ha' := (Finset.mem_filter.1 ha).2
        have hb' := (Finset.mem_filter.1 hb).2
        exact Subtype.ext (ha'.trans hb'.symm)) Y
      rwa [Finset.sum_coe_sort (finiteCells F) (fun z => Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ))))] at this
    have hd0 : ∀ b : ↥(chordBonds (finiteCells F)), enclosingCell b.1.1 = Y → bondDistToCell Y b = 0 := fun b hb => by
      have hz : cellSupDist Y Y = 0 := Nat.le_zero.1 (Finset.sup_le fun i _ => by simp)
      unfold bondDistToCell
      rw [hb, hz]
      simp
    set Sb := Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y with hSb
    have hcb : ∀ b ∈ Sb, enclosingCell b.1.1 = Y := fun b hb => (Finset.mem_filter.1 hb).2
    have facts := fun (W : F.GaugeField F.top) (hW : IsSmallCurvature (5 / 4 * T.σ) W) (η : StepVariable (finiteCells F))
      (hη : ∀ b, ‖η b‖ < T.ballRadius) => interpolatedExponent_bounds (T := T) (x := x) (W := W) (Y := Y) hκ hx hX hWc0
        (hPST t x F W 1 hfl htop hW zero_le_one le_rfl) ((hPT t x hfl).one_torus F W 1 htop hW zero_le_one le_rfl).exponent hsym
        (hsqC F htop) hCc hη
    have hexp64 : ∀ (z : F.Cell) (b : ↥(chordBonds (finiteCells F))), b ∈ Sb →
        Real.exp (-(2 ^ 6 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ))) := fun z b hb => by
      rw [hcb b hb, hsym Y z]
      refine Real.exp_le_exp.2 ?_
      have : (0 : ℝ) ≤ cellSupDist z Y := by positivity
      nlinarith
    have maj : ∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) W →
        IsCutoffDominated T.ballRadius T.κ Me T.p q Y (fun η => (coldHalfLawAt T x f).exponentRadialPart Y η W) := fun W hW => by
      have h1 := hRadT F Y T.p q Sb (interpolatedExponent 1 T.a T.chainParams.ρA x (frameRadius x) W) Ae
        (fun z => by convert hN z) hAe0 (fun η hη => (facts W hW η hη).2.1) (fun η hη b hb e => ?_) (fun η hη b hb b' e e' => ?_)
      · have hle : CR * Ae ≤ Me := by
          simp only [hMe]
          have : 0 ≤ (N : ℝ) * (T.ballRadius * ((|T.Ct| + 2 * |T.Cs|) * X) * Wc) := by positivity
          linarith
        exact h1.mono hle
      · obtain ⟨-, -, hp, hpart, -⟩ := facts W hW η hη
        rw [hd0 b (hcb b hb), hpart]
        simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have h3 : ∀ z ∈ finiteCells F, |bondPartialDeriv (interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) z W) b η e| ≤
            |T.Cs| * X * ‖e‖ * Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ))) := fun z _ => by
          refine (hp z b e).trans ?_
          calc _ = |T.Cs| * X * ‖e‖ * Real.exp (-(2 ^ 6 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (hexp64 z b hb) (by positivity)
        refine (Finset.sum_le_sum h3).trans ?_
        rw [← Finset.mul_sum]
        calc _ ≤ |T.Cs| * X * ‖e‖ * Wc := mul_le_mul_of_nonneg_left hCc (by positivity)
          _ ≤ |T.Cs| * (X + x) * ‖e‖ * Wc := by
            refine mul_le_mul_of_nonneg_right ?_ hWc0
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
          _ = _ := by simp only [hAe]; ring
      · obtain ⟨-, -, -, -, hs⟩ := facts W hW η hη
        rw [hd0 b (hcb b hb)]
        simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
        refine (hs b b' e e' (hcb b hb)).trans ?_
        have he0 := (Real.exp_pos (-(16 * T.κ * bondDistToCell Y b'))).le
        have h4 : |T.Cs| * x * Wc ≤ Ae := by
          simp only [hAe]
          refine mul_le_mul_of_nonneg_right ?_ hWc0
          exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right h4 he0
    refine hMT t x f F V V' Y q ι j ((coldHalfLawAt T x f).exponentRadialPart Y) Me hfl hrow htop hV hV' hpair hMe0 (maj V hV) (maj V' hV') fun hq ζ hζ => ?_
    set ε := Real.exp (-(4 * T.κ * q)) with hε
    have hε0 : 0 ≤ ε := (Real.exp_pos _).le
    have hinj := hpair.isBoxPairing.injective_left
    have hon : ∀ b, ‖toTorus j ζ b‖ < T.ballRadius := pushforwardField_norm_lt hinj hρ hζ
    obtain ⟨d1, -, p1, s1, -⟩ := facts V hV _ hon
    obtain ⟨d2, -, p2, s2, -⟩ := facts V' hV' _ hon
    set U : ℝ := T.ballRadius * ((|T.Ct| + 2 * |T.Cs|) * X) * ε with hU
    have hU0 : 0 ≤ U := by positivity
    have hterm : ∀ b ∈ Sb, ∀ z : F.Cell,
        |bondPartialDeriv (interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) z V) b (toTorus j ζ) (toTorus j ζ b) -
          bondPartialDeriv (interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) z V') b (toTorus j ζ) (toTorus j ζ b)| ≤
        U * Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ))) := fun b hb z => by
      have he0 := (Real.exp_pos (-(2 * T.κ * (cellSupDist z Y : ℝ)))).le
      by_cases hn : 8 * cellSupDist z Y ≤ q
      · obtain ⟨o, hz, ho⟩ := exists_offset_of_cell (z := z) (Y := Y) hper
        have hoq : ∀ i, 8 * |o i| ≤ (q : ℤ) := fun i => by
          have h1 := ho i
          have h2 : (8 * cellSupDist z Y : ℤ) ≤ q := by exact_mod_cast hn
          omega
        have hcs := hCompare F V V' Y q ι j o htop hV hV' hag hpair hq hoq
        have hcomp := (hTCT t x 1 f F F V V' Y Y q ι j j o hcs).1
        rw [← hz] at hcomp
        set B := |T.Ct| * ε * X with hB
        have hB0 : 0 ≤ B := by positivity
        have hXc : ∀ ξ ∈ openPolyball ι T.ballRadius, T.Ct * ε *
            (x * Real.sqrt (weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F) z ξ) + 1) ≤ B := fun ξ hξ => by
          have h1 := hsqV F htop ι j hinj z ξ hξ
          have h2 : 0 ≤ x * Real.sqrt (weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F) z ξ) + 1 := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hε0) h1 h2 (by positivity)
        have h := abs_sub_bondPartialDeriv_le hinj hρ hcomp hB0 hXc hζ (d1 z) (d2 z) b
        rw [abs_sub_comm]
        refine h.trans ?_
        have hdist : blockDist F (bondBlock F b) z = (cellSupDist z Y : ℝ) := by
          unfold blockDist bondBlock
          rw [hcb b hb, hsym Y z]
        rw [hdist]
        refine mul_le_mul_of_nonneg_right ?_ he0
        simp only [hU, hB]
        have : |T.Ct| * ε * X ≤ (|T.Ct| + 2 * |T.Cs|) * X * ε := by
          have h5 : 0 ≤ 2 * |T.Cs| * X * ε := by positivity
          nlinarith
        calc T.ballRadius * (|T.Ct| * ε * X) ≤ T.ballRadius * ((|T.Ct| + 2 * |T.Cs|) * X * ε) := mul_le_mul_of_nonneg_left this hρ.le
          _ = _ := by ring
      · have hq' : (q : ℝ) ≤ 8 * (cellSupDist z Y : ℝ) := by
          have : q < 8 * cellSupDist z Y := not_le.1 hn
          exact_mod_cast this.le
        have hdecay : Real.exp (-(2 ^ 6 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ ε * Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ))) := by
          rw [hcb b hb, hsym Y z, hε, ← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          have h0 : (0 : ℝ) ≤ cellSupDist z Y := by positivity
          nlinarith
        have hnorm : ‖toTorus j ζ b‖ ≤ T.ballRadius := (hon b).le
        have one : ∀ {a B' : ℝ}, a ≤ |T.Cs| * X * Real.exp (-(2 ^ 6 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) * ‖toTorus j ζ b‖ →
            a ≤ |T.Cs| * X * T.ballRadius * (ε * Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ)))) := fun {a B'} h => by
          refine h.trans ?_
          calc _ ≤ |T.Cs| * X * (ε * Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ)))) * T.ballRadius :=
                mul_le_mul (mul_le_mul_of_nonneg_left hdecay (by positivity)) hnorm (norm_nonneg _) (by positivity)
            _ = _ := by ring
        have a1 := one (B' := 0) (p1 z b (toTorus j ζ b))
        have a2 := one (B' := 0) (p2 z b (toTorus j ζ b))
        refine (abs_sub _ _).trans ?_
        calc _ ≤ 2 * (|T.Cs| * X * T.ballRadius * (ε * Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ))))) := by linarith
          _ ≤ _ := by
            have h5 : 0 ≤ |T.Ct| * X * T.ballRadius * ε * Real.exp (-(2 * T.κ * (cellSupDist z Y : ℝ))) := by positivity
            simp only [hU]
            nlinarith
    show |radialPart Sb (interpolatedExponent 1 T.a T.chainParams.ρA x (frameRadius x) V) (toTorus j ζ) -
      radialPart Sb (interpolatedExponent 1 T.a T.chainParams.ρA x (frameRadius x) V') (toTorus j ζ)| ≤ _
    unfold radialPart
    rw [← Finset.sum_sub_distrib]
    have hb1 : ∀ b ∈ Sb, |bondPartialDeriv (interpolatedExponent 1 T.a T.chainParams.ρA x (frameRadius x) V) b (toTorus j ζ) (toTorus j ζ b) -
        bondPartialDeriv (interpolatedExponent 1 T.a T.chainParams.ρA x (frameRadius x) V') b (toTorus j ζ) (toTorus j ζ b)| ≤ U * Wc := fun b hb => by
      rw [s1, s2, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun z _ => hterm b hb z).trans ?_)
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hCc hU0
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hb1).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (Sb.card : ℝ) ≤ N := by
      have : Sb.card ≤ N := by
        convert hN Y
      exact_mod_cast this
    have h0 : 0 ≤ CR * Ae := by positivity
    calc _ ≤ (N : ℝ) * (U * Wc) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (N * (T.ballRadius * ((|T.Ct| + 2 * |T.Cs|) * X) * Wc)) * ε := by simp only [hU]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by simp only [hMe]; linarith) hε0
end ResponseInTheExpansion
end
end YangMills.Construction
