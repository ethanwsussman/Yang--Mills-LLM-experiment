import YangMills.Construction.ColdStepAtMirrorFrames.BoxesOfTwoToriMatch
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentsStayGoodProof
import YangMills.Construction.ColdStepAtMirrorFrames.FreezingOfAConvexMeasure
import YangMills.Construction.ColdStepAtMirrorFrames.FreezingOfTheMeansProof
import YangMills.Construction.ColdStepAtMirrorFrames.FreezingOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.FloorOfTheScaledExponentsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open YangMills.Construction.BlockAverages Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace StepFreezing
open LocalCalculus
section
variable {ι P : Type} [Fintype ι] [DecidableEq ι] {ρ r x : ℝ} {pos : ι → P} {D : P → P → ℝ} {z : P}
theorem secondDerivAlong_linear_combination (hρ : 0 < ρ) {f g : BondField ι → ℝ}
    (hf : ContDiffOn ℝ 2 f (openPolyball ι ρ)) (hg : ContDiffOn ℝ 2 g (openPolyball ι ρ)) (a c : ℝ)
    {η : BondField ι} (hη : η ∈ openPolyball ι ρ) (u v : BondField ι) :
    secondDerivAlong (fun ζ => a * f ζ + c * g ζ) η u v =
      a * secondDerivAlong f η u v + c * secondDerivAlong g η u v := by
  unfold secondDerivAlong
  have hO := isOpen_openPolyball (ι := ι) hρ
  have e : (fun ζ => fderiv ℝ (fun ξ => a * f ξ + c * g ξ) ζ u) =ᶠ[𝓝 η]
      fun ζ => a * fderiv ℝ f ζ u + c * fderiv ℝ g ζ u := by
    filter_upwards [hO.mem_nhds hη] with ζ hζ
    have h1 : HasFDerivAt f (fderiv ℝ f ζ) ζ :=
      ((hf.contDiffAt (hO.mem_nhds hζ)).differentiableAt (by norm_num)).hasFDerivAt
    have h2 : HasFDerivAt g (fderiv ℝ g ζ) ζ :=
      ((hg.contDiffAt (hO.mem_nhds hζ)).differentiableAt (by norm_num)).hasFDerivAt
    have h3 : HasFDerivAt (fun ξ => a * f ξ + c * g ξ) (a • fderiv ℝ f ζ + c • fderiv ℝ g ζ) ζ :=
      (h1.const_mul a).add (h2.const_mul c)
    rw [h3.fderiv]
    simp
  rw [e.fderiv_eq]
  have dd : ∀ {θ : BondField ι → ℝ}, ContDiffOn ℝ 2 θ (openPolyball ι ρ) →
      HasFDerivAt (fun ζ => fderiv ℝ θ ζ u) (fderiv ℝ (fun ζ => fderiv ℝ θ ζ u) η) η := by
    intro θ hθ
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ θ) (openPolyball ι ρ) := hθ.fderiv_of_isOpen hO (by norm_num)
    have h2 : ContDiffOn ℝ 1 (fun ζ => fderiv ℝ θ ζ u) (openPolyball ι ρ) := h1.clm_apply contDiffOn_const
    exact ((h2.contDiffAt (hO.mem_nhds hη)).differentiableAt (by norm_num)).hasFDerivAt
  have h4 : HasFDerivAt (fun ζ => a * fderiv ℝ f ζ u + c * fderiv ℝ g ζ u)
      (a • fderiv ℝ (fun ζ => fderiv ℝ f ζ u) η + c • fderiv ℝ (fun ζ => fderiv ℝ g ζ u) η) η :=
    ((dd hf).const_mul a).add ((dd hg).const_mul c)
  rw [h4.fderiv]
  simp
theorem weightedSqNormNear_nonneg_at (z : P) (η : BondField ι) : 0 ≤ weightedSqNormNear r pos D z η :=
  Finset.sum_nonneg fun b _ => mul_nonneg (Real.exp_pos _).le (by positivity)
theorem secondDerivAlong_smul_right (θ : BondField ι → ℝ) (η u v : BondField ι) (a : ℝ) :
    secondDerivAlong θ η u (a • v) = a * secondDerivAlong θ η u v := by
  unfold secondDerivAlong
  simp
theorem secondDerivAlong_smul_left (hρ : 0 < ρ) {θ : BondField ι → ℝ}
    (hθ : ContDiffOn ℝ 2 θ (openPolyball ι ρ))
    {η : BondField ι} (hη : η ∈ openPolyball ι ρ) (u v : BondField ι) (a : ℝ) :
    secondDerivAlong θ η (a • u) v = a * secondDerivAlong θ η u v := by
  unfold secondDerivAlong
  have hO := isOpen_openPolyball (ι := ι) hρ
  have e : (fun ζ => fderiv ℝ θ ζ (a • u)) = fun ζ => a * fderiv ℝ θ ζ u := by
    funext ζ
    simp
  rw [e]
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ θ) (openPolyball ι ρ) := hθ.fderiv_of_isOpen hO (by norm_num)
  have h2 : ContDiffOn ℝ 1 (fun ζ => fderiv ℝ θ ζ u) (openPolyball ι ρ) := h1.clm_apply contDiffOn_const
  have h3 : HasFDerivAt (fun ζ => fderiv ℝ θ ζ u) (fderiv ℝ (fun ζ => fderiv ℝ θ ζ u) η) η :=
    ((h2.contDiffAt (hO.mem_nhds hη)).differentiableAt (by norm_num)).hasFDerivAt
  have h4 : HasFDerivAt (fun ζ => a * fderiv ℝ θ ζ u) (a • fderiv ℝ (fun ζ => fderiv ℝ θ ζ u) η) η :=
    h3.const_mul a
  rw [h4.fderiv]
  simp
theorem bondVariation_smul (b : ι) (a : ℝ) (e : BondVector) :
    bondVariation b (a • e) = a • bondVariation b e := by apply _root_.YangMills.SharedProofs.p169 <;> assumption
theorem bondVariation_zero (b : ι) : bondVariation b (0 : BondVector) = 0 := by
  unfold bondVariation
  simp
theorem bondGradNorm_le_of_unit {f : BondField ι → ℝ} {b : ι} {η : BondField ι} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ e, ‖e‖ = 1 → |fderiv ℝ f η (bondVariation b e)| ≤ B) : bondGradNorm f b η ≤ B := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalTerms.bondGradNorm_le_of_unit <;> assumption
theorem abs_secondDerivAlong_le_of_unit (hρ : 0 < ρ) {θ : BondField ι → ℝ}
    (hθ : ContDiffOn ℝ 2 θ (openPolyball ι ρ))
    {η : BondField ι} (hη : η ∈ openPolyball ι ρ) {b b' : ι} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ e e', ‖e‖ = 1 → ‖e'‖ = 1 → |secondDerivAlong θ η (bondVariation b e) (bondVariation b' e')| ≤ B)
    (e e' : BondVector) :
    |secondDerivAlong θ η (bondVariation b e) (bondVariation b' e')| ≤ B * ‖e‖ * ‖e'‖ := by
  by_cases he : e = 0
  · subst he
    have : secondDerivAlong θ η (bondVariation b 0) (bondVariation b' e') = 0 := by
      rw [bondVariation_zero]
      unfold secondDerivAlong
      simp
    simp [this]
  by_cases he' : e' = 0
  · subst he'
    have : secondDerivAlong θ η (bondVariation b e) (bondVariation b' 0) = 0 := by
      rw [bondVariation_zero]
      unfold secondDerivAlong
      simp
    simp [this]
  have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hn' : 0 < ‖e'‖ := norm_pos_iff.mpr he'
  have hu : ‖(‖e‖⁻¹ • e)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hu' : ‖(‖e'‖⁻¹ • e')‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn'.ne']
  have e1 : e = ‖e‖ • (‖e‖⁻¹ • e) := by
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have e2 : e' = ‖e'‖ • (‖e'‖⁻¹ • e') := by
    rw [smul_smul, mul_inv_cancel₀ hn'.ne', one_smul]
  have h1 := h _ _ hu hu'
  calc |secondDerivAlong θ η (bondVariation b e) (bondVariation b' e')|
      = |secondDerivAlong θ η (bondVariation b (‖e‖ • (‖e‖⁻¹ • e)))
          (bondVariation b' (‖e'‖ • (‖e'‖⁻¹ • e')))| := by
        rw [← e1, ← e2]
    _ = ‖e‖ * ‖e'‖ * |secondDerivAlong θ η (bondVariation b (‖e‖⁻¹ • e)) (bondVariation b' (‖e'‖⁻¹ • e'))| := by
        have A1 : bondVariation b (‖e‖ • (‖e‖⁻¹ • e)) = ‖e‖ • bondVariation b (‖e‖⁻¹ • e) :=
          bondVariation_smul b _ _
        have A2 : bondVariation b' (‖e'‖ • (‖e'‖⁻¹ • e')) = ‖e'‖ • bondVariation b' (‖e'‖⁻¹ • e') :=
          bondVariation_smul b' _ _
        rw [A1, A2, secondDerivAlong_smul_left hρ hθ hη, secondDerivAlong_smul_right, abs_mul, abs_mul,
          abs_of_pos hn, abs_of_pos hn']
        ring
    _ ≤ ‖e‖ * ‖e'‖ * B := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = B * ‖e‖ * ‖e'‖ := by ring
theorem isLocalTermAt_mono {c c' : ℝ} {θ : BondField ι → ℝ} (hc : c ≤ c') (hx : 0 ≤ x)
    (hT : IsLocalTermAt ρ r c x pos D z θ) : IsLocalTermAt ρ r c' x pos D z θ := by
  refine ⟨hT.smooth, fun η hη b => (hT.slope η hη b).trans ?_, fun η hη b b' e e' =>
    (hT.second η hη b b' e e').trans ?_⟩
  · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_right hc
    have := Real.sqrt_nonneg (weightedSqNormNear r pos D z η)
    positivity
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hc hx
theorem isLocalTermAt_linear_combination (hρ : 0 < ρ) {c₁ c₂ : ℝ} {θ₁ θ₂ : BondField ι → ℝ}
    (h₁ : IsLocalTermAt ρ r c₁ x pos D z θ₁) (h₂ : IsLocalTermAt ρ r c₂ x pos D z θ₂) (a b : ℝ) :
    IsLocalTermAt ρ r (|a| * c₁ + |b| * c₂) x pos D z (fun ζ => a * θ₁ ζ + b * θ₂ ζ) := by
  refine ⟨(contDiffOn_const.mul h₁.smooth).add (contDiffOn_const.mul h₂.smooth), fun η hη k => ?_,
    fun η hη k k' e e' => ?_⟩
  · refine (bondGradNorm_linear_combination_le hρ (contDiffOn_one_of_two h₁.smooth)
      (contDiffOn_one_of_two h₂.smooth) a b hη k).trans ?_
    have t1 := mul_le_mul_of_nonneg_left (h₁.slope η hη k) (abs_nonneg a)
    have t2 := mul_le_mul_of_nonneg_left (h₂.slope η hη k) (abs_nonneg b)
    refine (add_le_add t1 t2).trans (le_of_eq ?_)
    ring
  · rw [secondDerivAlong_linear_combination hρ h₁.smooth h₂.smooth a b hη]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have t1 := mul_le_mul_of_nonneg_left (h₁.second η hη k k' e e') (abs_nonneg a)
    have t2 := mul_le_mul_of_nonneg_left (h₂.second η hη k k' e e') (abs_nonneg b)
    refine (add_le_add t1 t2).trans (le_of_eq ?_)
    ring
theorem isLocalTermAt_zero (hρ : 0 < ρ) (hx : 0 ≤ x) :
    IsLocalTermAt ρ r 0 x pos D z (fun _ => (0 : ℝ)) := by
  refine ⟨contDiffOn_const, fun η _ b => ?_, fun η _ b b' e e' => ?_⟩
  · simp [bondGradNorm]
  · simp [secondDerivAlong]
theorem isLocalTermAt_sum (hρ : 0 < ρ) (hx : 0 ≤ x) {α : Type} (s : Finset α) {c : ℝ} (hc : 0 ≤ c)
    (θ : α → BondField ι → ℝ) (h : ∀ a ∈ s, IsLocalTermAt ρ r c x pos D z (θ a)) :
    IsLocalTermAt ρ r (s.card * c) x pos D z (fun ζ => ∑ a ∈ s, θ a ζ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isLocalTermAt_zero (r := r) (pos := pos) (D := D) (z := z) hρ hx
  | insert a s ha ih =>
    have h1 := isLocalTermAt_linear_combination hρ (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb)) 1 1
    simp only [abs_one, one_mul] at h1
    simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    refine isLocalTermAt_mono (le_of_eq ?_) hx h1
    push_cast
    ring
theorem secondDerivAlong_halfSqNormOn (μ : ℝ) (Λ : Finset ι) (η u v : BondField ι) :
    secondDerivAlong (halfSqNormOn μ Λ) η u v = ∑ b ∈ Λ, μ * inner ℝ (v b) (u b) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.PotentialStability.secondDerivAlong_halfSqNormOn <;> assumption
theorem isLocalTermAt_halfSqNormOn (hρ : 0 < ρ) {lam : ℝ} (hlam : 0 ≤ lam) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hD : IsPseudoMetricOnBonds D) (B : Finset ι) (hB : ∀ b ∈ B, pos b = z) :
    IsLocalTermAt ρ r lam x pos D z (halfSqNormOn (x * lam) B) := by
  have hμ : 0 ≤ x * lam := by positivity
  have hsm : ContDiffOn ℝ 2 (halfSqNormOn (ι := ι) (x * lam) B) (openPolyball ι ρ) :=
    ((contDiff_halfSqNormOn (x * lam) B).of_le (by norm_num)).contDiffOn
  refine ⟨hsm, fun η hη b => ?_, fun η hη b b' e e' => ?_⟩
  · refine (bondGradNorm_halfSqNormOn_le hμ B η b).trans ?_
    split_ifs with hb
    · have hD0 : D (pos b) z = 0 := by
        rw [hB b hb, hD.self]
      rw [hD0]
      simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
      have h1 : ‖η b‖ ≤ Real.sqrt (weightedSqNormNear r pos D z η) := by
        apply Real.le_sqrt_of_sq_le
        unfold weightedSqNormNear
        have h2 := Finset.single_le_sum
          (f := fun b => Real.exp (-(2 ^ 5 * r * D (pos b) z)) * ‖η b‖ ^ 2)
          (fun b _ => mul_nonneg (Real.exp_pos _).le (by positivity)) (Finset.mem_univ b)
        simpa [hD0] using h2
      have := mul_le_mul_of_nonneg_left h1 hμ
      nlinarith
    · have : 0 ≤ lam * (x * Real.sqrt (weightedSqNormNear r pos D z η) + 1) := by positivity
      exact mul_nonneg this (Real.exp_pos _).le
  · rw [secondDerivAlong_halfSqNormOn]
    by_cases hbb : b = b'
    · subst hbb
      by_cases hb : b ∈ B
      · rw [Finset.sum_eq_single b]
        · have hD0 : D (pos b) z = 0 := by
            rw [hB b hb, hD.self]
          simp only [bondVariation, Pi.single_eq_same, hD0, max_self, mul_zero, neg_zero, Real.exp_zero,
            mul_one]
          rw [abs_mul, abs_of_nonneg hμ]
          have h1 := abs_real_inner_le_norm e' e
          have h2 : lam * x * ‖e‖ * ‖e'‖ = x * lam * (‖e'‖ * ‖e‖) := by ring
          rw [h2]
          exact mul_le_mul_of_nonneg_left h1 hμ
        · intro c _ hc
          simp [bondVariation, hc]
        · exact fun h => absurd hb h
      · rw [Finset.sum_eq_zero]
        · simp only [abs_zero]
          positivity
        · intro c hc
          have : c ≠ b := fun h => hb (h ▸ hc)
          simp [bondVariation, this]
    · rw [Finset.sum_eq_zero]
      · simp only [abs_zero]
        positivity
      · intro c _
        by_cases h1 : c = b
        · subst h1
          have : c ≠ b' := hbb
          simp [bondVariation, this]
        · simp [bondVariation, h1]
end
section
variable {F : BlockFrame}
theorem isPseudoMetricOnBonds_cellDistance (F : BlockFrame) : IsPseudoMetricOnBonds (blockDist F) := by
  refine ⟨fun b => ?_, fun b b' => ?_, fun b b' b'' => ?_⟩
  · simp [blockDist, PatchLocality.cellSupDist_self]
  · simp only [blockDist]
    rw [PatchLocality.cellSupDist_comm]
  · simp only [blockDist]
    exact_mod_cast PatchLocality.cellSupDist_triangle b b' b''
theorem leftTranslate_bondSpread_zero {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (W : F.GaugeField j) : leftTranslate (bondSpread c X 0) W = W := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
theorem bondDeriv_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ} (G : F.GaugeField j → E)
    (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p3568 <;> assumption
theorem contDiffOn_of_contDiffAt_translate {ρ : ℝ} (G : F.GaugeField F.top → StepVariable (finiteCells F) → ℝ)
    (V : F.GaugeField F.top)
    (h : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 (fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) =>
        G (leftTranslate (bondSpread (fun l : Fin 0 => l.elim0) (fun l : Fin 0 => l.elim0) q.1) V) q.2) (0, η)) :
    ContDiffOn ℝ 2 (G V) (openPolyball ↥(chordBonds (finiteCells F)) ρ) := by
  intro η hη
  have h1 := h η (fun b => (hη b).le)
  have h2 : ContDiffAt ℝ 3 (fun ζ : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), ζ)) η :=
    contDiffAt_const.prodMk contDiffAt_id
  have h3 := ContDiffAt.comp η (g := fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) =>
        G (leftTranslate (bondSpread (fun l : Fin 0 => l.elim0) (fun l : Fin 0 => l.elim0) q.1) V) q.2) h1 h2
  have e : ((fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) =>
        G (leftTranslate (bondSpread (fun l : Fin 0 => l.elim0) (fun l : Fin 0 => l.elim0) q.1) V) q.2) ∘
      fun ζ : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), ζ)) = G V := by
    funext ζ
    simp only [Function.comp, leftTranslate_bondSpread_zero]
  rw [e] at h3
  exact (h3.of_le (by norm_num)).contDiffWithinAt
theorem cellSupDist_le_bondSpanWithCell {k : ℕ} (Y z : F.Cell) (c : Fin k → F.Site F.top × Fin 4) :
    cellSupDist Y z ≤ bondSpanWithCell Y z c := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalTerms.cellSupDist_le_bondSpanWithCell <;> assumption
theorem cellSupDist_le_chordBondSpan {k : ℕ} (Y : F.Cell) (b : Fin k → ↥(chordBonds (finiteCells F)))
    (l : Fin k) : cellSupDist Y (enclosingCell (b l).1.1) ≤ chordBondSpan Y b := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalTerms.cellSupDist_le_chordBondSpan <;> assumption
theorem localSqNorm_le_weightedSqNormNear {κ : ℝ} (hκ : 0 ≤ κ) (Y : F.Cell) (η : StepVariable (finiteCells F)) :
    localSqNorm κ Y η ≤ weightedSqNormNear κ (bondBlock F) (blockDist F) Y η := by
  refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
  apply Real.exp_le_exp.mpr
  have h0 : (0 : ℝ) ≤ cellSupDist (enclosingCell b.1.1) Y := by positivity
  have h1 : (2 ^ 5 * κ) * (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤
      (2 ^ 6 * κ) * (cellSupDist (enclosingCell b.1.1) Y : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) h0
  simp only [blockDist, bondBlock]
  linarith
theorem isLocalTermAt_cellExponent {star : Bool} {a ρA ρ x κ C : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hC : 0 ≤ C) (hx : 0 ≤ x) (hB : CellExponentBounds star a ρA ρ x κ C m V)
    (Y : F.Cell) :
    IsLocalTermAt ρ κ C x (bondBlock F) (blockDist F) Y (cellExponent star a ρA x m Y V) := by
  have hsm : ContDiffOn ℝ 2 (cellExponent star a ρA x m Y V)
      (openPolyball ↥(chordBonds (finiteCells F)) ρ) :=
    contDiffOn_of_contDiffAt_translate (fun V' => cellExponent star a ρA x m Y V') V
      (fun η h => hB.smooth Y η 0 _ _ h)
  refine ⟨hsm, fun η hη b => ?_, fun η hη b b' e e' => ?_⟩
  · have hs0 := Real.sqrt_nonneg (weightedSqNormNear κ (bondBlock F) (blockDist F) Y η)
    apply bondGradNorm_le_of_unit (by positivity)
    intro e he
    have h1 := hB.deriv_top_partial Y η b e 0 (fun l => l.elim0) (fun l => l.elim0) hη (by norm_num)
      (fun l => l.elim0) he
    rw [bondDeriv_zero] at h1
    have h2 : |fderiv ℝ (cellExponent star a ρA x m Y V) η (bondVariation b e)| ≤ _ := h1
    refine h2.trans ?_
    apply mul_le_mul _ ?_ (Real.exp_pos _).le (by positivity)
    · apply mul_le_mul_of_nonneg_left _ hC
      have h3 := Real.sqrt_le_sqrt (localSqNorm_le_weightedSqNormNear hκ.le Y η)
      have := mul_le_mul_of_nonneg_left h3 hx
      linarith
    · apply Real.exp_le_exp.mpr
      have h3 : (cellSupDist Y (enclosingCell b.1.1) : ℝ) ≤
          (bondSpanWithCell Y (enclosingCell b.1.1) (fun l : Fin 0 => l.elim0) : ℝ) := by
        exact_mod_cast cellSupDist_le_bondSpanWithCell Y (enclosingCell b.1.1) (fun l : Fin 0 => l.elim0)
      have h4 : blockDist F (bondBlock F b) Y = (cellSupDist Y (enclosingCell b.1.1) : ℝ) := by
        simp only [blockDist, bondBlock]
        rw [PatchLocality.cellSupDist_comm]
      rw [h4]
      have h5 : (0 : ℝ) ≤ cellSupDist Y (enclosingCell b.1.1) := by positivity
      nlinarith
  · refine abs_secondDerivAlong_le_of_unit hρ hsm hη (by positivity) (fun e e' he he' => ?_) e e'
    refine (hB.second_deriv Y η b b' e e' hη he he').trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have h3 := cellSupDist_le_chordBondSpan Y ![b, b'] 0
    have h4 := cellSupDist_le_chordBondSpan Y ![b, b'] 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h3 h4
    have h5 : blockDist F (bondBlock F b) Y ≤ (chordBondSpan Y ![b, b'] : ℝ) := by
      simp only [blockDist, bondBlock]
      rw [PatchLocality.cellSupDist_comm]
      exact_mod_cast h3
    have h6 : blockDist F (bondBlock F b') Y ≤ (chordBondSpan Y ![b, b'] : ℝ) := by
      simp only [blockDist, bondBlock]
      rw [PatchLocality.cellSupDist_comm]
      exact_mod_cast h4
    have h7 := max_le h5 h6
    nlinarith
theorem isLocalTermAt_centredExpansion {star : Bool} {a ρA ρ κ δ E E₃ C x : ℝ} {L m : ℕ} {f : LocalFamily}
    {V : F.GaugeField F.top}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hx : 1 ≤ x)
    (hB : CentredExpansionBounds star a ρA ρ κ δ E E₃ C L m f V) (y : F.Site F.depth) :
    IsLocalTermAt ρ κ (C * E) x (bondBlock F) (blockDist F) (enclosingCell y)
      (fun ζ => centredExpansion star a ρA m f y ζ V) := by
  have hsm : ContDiffOn ℝ 2 (fun ζ => centredExpansion star a ρA m f y ζ V)
      (openPolyball ↥(chordBonds (finiteCells F)) ρ) :=
    contDiffOn_of_contDiffAt_translate (fun V' ζ => centredExpansion star a ρA m f y ζ V') V
      (fun η h => hB.smooth y η 0 _ _ h)
  refine ⟨hsm, fun η hη b => ?_, fun η hη b b' e e' => ?_⟩
  · have hs0 := Real.sqrt_nonneg (weightedSqNormNear κ (bondBlock F) (blockDist F) (enclosingCell y) η)
    apply bondGradNorm_le_of_unit (by positivity)
    intro e he
    have h1 := hB.deriv_top_partial y η b e 0 (fun l => l.elim0) (fun l => l.elim0) hη (by norm_num)
      (fun l => l.elim0) he
    rw [bondDeriv_zero] at h1
    have h2 : |fderiv ℝ (fun ζ => centredExpansion star a ρA m f y ζ V) η (bondVariation b e)| ≤ _ := h1
    refine h2.trans ?_
    simp only [show (0 : ℕ) ≠ 2 by norm_num, if_false]
    have h3 : (cellSupDist (enclosingCell y) (enclosingCell b.1.1) : ℝ) ≤
        (bondSpanWithCell (enclosingCell y) (enclosingCell b.1.1) (fun l : Fin 0 => l.elim0) : ℝ) := by
      exact_mod_cast cellSupDist_le_bondSpanWithCell (enclosingCell y) (enclosingCell b.1.1)
        (fun l : Fin 0 => l.elim0)
    have h4 : blockDist F (bondBlock F b) (enclosingCell y) =
        (cellSupDist (enclosingCell y) (enclosingCell b.1.1) : ℝ) := by
      simp only [blockDist, bondBlock]
      rw [PatchLocality.cellSupDist_comm]
    have h5 : Real.exp (-(2 ^ 5 * κ *
          (bondSpanWithCell (enclosingCell y) (enclosingCell b.1.1) (fun l : Fin 0 => l.elim0) : ℝ))) ≤
        Real.exp (-(2 ^ 5 * κ * blockDist F (bondBlock F b) (enclosingCell y))) := by
      apply Real.exp_le_exp.mpr
      rw [h4]
      have : (2 ^ 5 * κ) * (cellSupDist (enclosingCell y) (enclosingCell b.1.1) : ℝ) ≤
          (2 ^ 5 * κ) * (bondSpanWithCell (enclosingCell y) (enclosingCell b.1.1) (fun l : Fin 0 => l.elim0) : ℝ) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith
    have h6 : (1 : ℝ) ≤ x * Real.sqrt (weightedSqNormNear κ (bondBlock F) (blockDist F) (enclosingCell y) η) + 1 := by
      have : 0 ≤ x * Real.sqrt (weightedSqNormNear κ (bondBlock F) (blockDist F) (enclosingCell y) η) := by
        positivity
      linarith
    calc C * E * Real.exp (-(2 ^ 5 * κ *
          (bondSpanWithCell (enclosingCell y) (enclosingCell b.1.1) (fun l : Fin 0 => l.elim0) : ℝ)))
        ≤ C * E * Real.exp (-(2 ^ 5 * κ * blockDist F (bondBlock F b) (enclosingCell y))) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have : 0 ≤ C * E := by positivity
          nlinarith
  · refine abs_secondDerivAlong_le_of_unit hρ hsm hη (by positivity) (fun e e' he he' => ?_) e e'
    refine (hB.second_deriv y η b b' e e' hη he he').trans ?_
    have h3 := cellSupDist_le_chordBondSpan (enclosingCell y) ![b, b'] 0
    have h4 := cellSupDist_le_chordBondSpan (enclosingCell y) ![b, b'] 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h3 h4
    have h5 : blockDist F (bondBlock F b) (enclosingCell y) ≤ (chordBondSpan (enclosingCell y) ![b, b'] : ℝ) := by
      simp only [blockDist, bondBlock]
      rw [PatchLocality.cellSupDist_comm]
      exact_mod_cast h3
    have h6 : blockDist F (bondBlock F b') (enclosingCell y) ≤ (chordBondSpan (enclosingCell y) ![b, b'] : ℝ) := by
      simp only [blockDist, bondBlock]
      rw [PatchLocality.cellSupDist_comm]
      exact_mod_cast h4
    have h7 := max_le h5 h6
    have h9 : Real.exp (-(2 ^ 5 * κ * (chordBondSpan (enclosingCell y) ![b, b'] : ℝ))) ≤
        Real.exp (-(2 ^ 5 * κ * max (blockDist F (bondBlock F b) (enclosingCell y))
          (blockDist F (bondBlock F b') (enclosingCell y)))) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left h7 (by positivity : (0 : ℝ) ≤ 2 ^ 5 * κ)
      linarith
    have hCE : 0 ≤ C * E := by positivity
    calc C * E * Real.exp (-(2 ^ 5 * κ * (chordBondSpan (enclosingCell y) ![b, b'] : ℝ)))
        ≤ C * E * Real.exp (-(2 ^ 5 * κ * max (blockDist F (bondBlock F b) (enclosingCell y))
            (blockDist F (bondBlock F b') (enclosingCell y)))) :=
          mul_le_mul_of_nonneg_left h9 hCE
      _ ≤ C * E * x * Real.exp (-(2 ^ 5 * κ * max (blockDist F (bondBlock F b) (enclosingCell y))
            (blockDist F (bondBlock F b') (enclosingCell y)))) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          nlinarith
theorem card_centredCube {L : ℕ} (hL : Odd L) : (centredCube L).card = L ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem card_sites_in_cell_le (hs : SiteDecomposition) (hodd : Odd F.blockSide) (hside : ∀ i, 2 ≤ F.extent i)
    (z : F.Cell) [DecidablePred fun y : F.Site F.depth => enclosingCell y = z] :
    ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = z).card ≤ F.blockSide ^ 4 := by
  obtain ⟨_, h2, _, _⟩ := hs F hodd hside
  rw [← card_centredCube hodd]
  apply Finset.card_le_card_of_injOn cellOffset
  · intro y _
    exact (h2 y).2
  · intro y hy y' hy' he
    have hz := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    have hz' := (Finset.mem_filter.mp (Finset.mem_coe.mp hy')).2
    have e1 := (h2 y).1
    have e2 := (h2 y').1
    rw [← e1, ← e2, he, hz, hz']
theorem isLocalTermAt_cellCentredExpansion {star : Bool} {a ρA ρ κ δ E E₃ C x : ℝ} {L m : ℕ} {f : LocalFamily}
    {V : F.GaugeField F.top}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hx : 1 ≤ x)
    (hB : CentredExpansionBounds star a ρA ρ κ δ E E₃ C L m f V) (hs : SiteDecomposition)
    (hodd : Odd F.blockSide) (hside : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) :
    IsLocalTermAt ρ κ (C * E * (F.blockSide : ℝ) ^ 4) x (bondBlock F) (blockDist F) Y
      (fun ζ => cellCentredExpansion star a ρA m f Y ζ V) := by
  classical
  have hx0 : 0 ≤ x := by linarith
  have hc : 0 ≤ C * E := by positivity
  unfold cellCentredExpansion
  have h1 := isLocalTermAt_sum (r := κ) (pos := bondBlock F) (D := blockDist F) (z := Y) hρ hx0
    ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y) hc
    (fun y ζ => centredExpansion star a ρA m f y ζ V) (fun y hy => by
      have h2 := isLocalTermAt_centredExpansion hρ hκ hC hE hx hB y
      rw [(Finset.mem_filter.mp hy).2] at h2
      exact h2)
  refine isLocalTermAt_mono ?_ hx0 h1
  have h2 := card_sites_in_cell_le hs hodd hside Y
  have h3 : ((((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card : ℕ) : ℝ) ≤
      (F.blockSide : ℝ) ^ 4 := by
    exact_mod_cast h2
  calc ((((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card : ℕ) : ℝ) * (C * E)
      ≤ (F.blockSide : ℝ) ^ 4 * (C * E) := mul_le_mul_of_nonneg_right h3 hc
    _ = _ := by ring
theorem cellQuadratic_eq_halfSqNormOn (lam x : ℝ) (Y : F.Cell) :
    cellQuadratic (F := F) lam x Y =
      halfSqNormOn (x * lam) (open Classical in Finset.univ.filter fun b => bondBlock F b = Y) := by
  classical
  funext η
  unfold cellQuadratic halfSqNormOn
  rw [Finset.sum_filter]
  rfl
theorem isLocalTermAt_cellQuadratic {ρ κ lam x : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) (hlam : 0 ≤ lam) (hx : 0 ≤ x)
    (Y : F.Cell) :
    IsLocalTermAt ρ κ lam x (bondBlock F) (blockDist F) Y (cellQuadratic lam x Y) := by
  classical
  rw [cellQuadratic_eq_halfSqNormOn]
  exact isLocalTermAt_halfSqNormOn hρ hlam hx hκ.le (isPseudoMetricOnBonds_cellDistance F) _
    fun b hb => (Finset.mem_filter.mp hb).2
theorem finite_cell (hs : ∀ i, 0 < F.extent i) : Finite F.Cell := by apply _root_.YangMills.Construction.TopLevelSites.finite_cell <;> assumption
theorem finiteCells_eq_univ (hf : Finite F.Cell) :
    finiteCells F = @Finset.univ _ (Fintype.ofFinite F.Cell) := by
  unfold finiteCells
  rw [dif_pos hf]
theorem mem_finiteCells (hf : Finite F.Cell) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.SharedProofs.p8277 <;> assumption
theorem mem_bondsNearCell_iff {Y : F.Cell} {r : ℕ} (b : ↥(chordBonds (finiteCells F))) :
    b ∈ bondsNearCell F Y r ↔ blockDist F (bondBlock F b) Y ≤ (r : ℝ) / 2 := by
  classical
  simp only [bondsNearCell, Finset.mem_filter, Finset.mem_univ, true_and, blockDist, bondBlock]
  constructor
  · intro h
    have : (2 : ℝ) * (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤ r := by exact_mod_cast h
    linarith
  · intro h
    have : (2 : ℝ) * (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤ r := by linarith
    exact_mod_cast this
theorem le_cellDistance_of_not_mem_cellsNearCell (hf : Finite F.Cell) {Y z : F.Cell} {r : ℕ}
    (h : z ∉ cellsNearCell F Y r) : (r : ℝ) / 8 ≤ blockDist F z Y := by
  classical
  simp only [cellsNearCell, Finset.mem_filter, _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepFreezing.mem_finiteCells hf z, true_and, not_lt] at h
  simp only [blockDist]
  have : (r : ℝ) ≤ 8 * (cellSupDist z Y : ℝ) := by exact_mod_cast h
  linarith
theorem abs_ballExpectation_sub_le_of_local (hfz : BallExpectationFreezingBound)
    (hbox : NearBlocksCorrespondByOffset)
    {F F' : BlockFrame} {ρ κ S lam x c ε : ℝ} {p : ℝ → ℝ} {r : ℕ} (hL : F.blockSide = F'.blockSide)
    (ht : F.depth = F'.depth)
    (hodd : Odd F.blockSide) (hs : ∀ i, 2 * r + 2 < F.extent i) (hs' : ∀ i, 2 * r + 2 < F'.extent i)
    (hρ : 0 < ρ) (hκ : 0 < κ) (hlam : 0 < lam) (hx : 1 ≤ x) (hc : 1 ≤ c) (hε : 0 ≤ ε) (hp : IsCutoff ρ p)
    {Ψ H : StepVariable (finiteCells F) → ℝ} {θ : F.Cell → StepVariable (finiteCells F) → ℝ} {Y : F.Cell}
    {Ψ' H' : StepVariable (finiteCells F') → ℝ} {θ' : F'.Cell → StepVariable (finiteCells F') → ℝ}
    {Y' : F'.Cell}
    (hΨ : IsAdmissiblePotential ρ (x * lam / 4) κ
      (fun b b' => blockDist F (bondBlock F b) (bondBlock F b')) Ψ)
    (hΨ' : IsAdmissiblePotential ρ (x * lam / 4) κ
      (fun b b' => blockDist F' (bondBlock F' b) (bondBlock F' b')) Ψ')
    (hW : ∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(κ / 4 * blockDist F (bondBlock F b) z)) ≤ S ∧
      ∑ z' ∈ finiteCells F, Real.exp (-(κ / 4 * blockDist F z' z)) ≤ S)
    (hW' : ∀ z : F'.Cell, ∑ b : ↥(chordBonds (finiteCells F')),
        Real.exp (-(κ / 4 * blockDist F' (bondBlock F' b) z)) ≤ S ∧
      ∑ z' ∈ finiteCells F', Real.exp (-(κ / 4 * blockDist F' z' z)) ≤ S)
    (hθ : ∀ z, IsLocalTermAt ρ κ c x (bondBlock F) (blockDist F) z (θ z))
    (hsum : ∀ η ∈ openPolyball ↥(chordBonds (finiteCells F)) ρ, Ψ η = ∑ z ∈ finiteCells F, θ z η)
    (hθ' : ∀ z, IsLocalTermAt ρ κ c x (bondBlock F') (blockDist F') z (θ' z))
    (hsum' : ∀ η ∈ openPolyball ↥(chordBonds (finiteCells F')) ρ, Ψ' η = ∑ z ∈ finiteCells F', θ' z η)
    (hH : IsLocalTermAt ρ κ c x (bondBlock F) (blockDist F) Y H)
    (hH' : IsLocalTermAt ρ κ c x (bondBlock F') (blockDist F') Y' H')
    (hcmp : ∀ (e : ↥(bondsNearCell F Y r) ≃ ↥(bondsNearCell F' Y' r))
      (φ : {z // z ∈ cellsNearCell F Y r} ≃ {z // z ∈ cellsNearCell F' Y' r}),
      BondsMatchByOffset Y Y' r e → CellsMatchByOffset Y Y' r φ →
      (∀ k z, bondBlock F k.1 = z.1 ↔ bondBlock F' (e k).1 = (φ z).1) →
      (∀ z : {z // z ∈ cellsNearCell F Y r}, z.1 = Y → (φ z).1 = Y') →
      (∀ (z : {z // z ∈ cellsNearCell F Y r}), ∀ ξ ∈ openPolyball ↥(bondsNearCell F Y r) ρ, ∀ k,
        bondGradNorm (fun ζ => θ' (φ z).1 (pushforwardField (fun k => (e k).1) ζ) -
          θ z.1 (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ζ)) k ξ ≤
          c * ε * (x * Real.sqrt (weightedSqNormNear κ (fun k : ↥(bondsNearCell F Y r) => bondBlock F k.1)
            (blockDist F) z.1 ξ) + 1) *
            Real.exp (-(2 * κ * blockDist F (bondBlock F k.1) z.1))) ∧
      (∀ ξ ∈ openPolyball ↥(bondsNearCell F Y r) ρ, |H' (pushforwardField (fun k => (e k).1) ξ) -
        H (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ξ)| ≤
        c * ε * (x * weightedSqNormNear κ (fun k : ↥(bondsNearCell F Y r) => bondBlock F k.1)
          (blockDist F) Y ξ + 1))) :
    |ballExpectation (cutoffFactor ρ p) Ψ H - ballExpectation (cutoffFactor ρ p) Ψ' H'| ≤
      c ^ 2 * (2 * freezingConstant lam S * Real.exp (-(κ * r / 16)) +
        blockComparisonConstant lam S * (ε + Real.exp (-(κ * r / 32)))) := by
  have hf : Finite F.Cell := finite_cell fun i => by have := hs i; omega
  have hf' : Finite F'.Cell := finite_cell fun i => by have := hs' i; omega
  letI iF : Fintype F.Cell := Fintype.ofFinite _
  letI iF' : Fintype F'.Cell := Fintype.ofFinite _
  obtain ⟨e, φ, hbm, hcm, hd1, hd2, hd3, hd4⟩ := hbox F F' Y Y' r hL ht hodd hs hs'
  obtain ⟨hc1, hc2⟩ := hcmp e φ hbm hcm hd3 hd4
  have hwe := finiteCells_eq_univ hf
  have hwe' := finiteCells_eq_univ hf'
  refine hfz ↥(chordBonds (finiteCells F)) ↥(chordBonds (finiteCells F')) F.Cell F'.Cell ρ κ S lam x c ε
    (r : ℝ) p (bondBlock F) (blockDist F) Ψ H θ Y (bondBlock F') (blockDist F') Ψ' H' θ' Y'
    (bondsNearCell F Y r) (bondsNearCell F' Y' r) e (cellsNearCell F Y r) (cellsNearCell F' Y' r) φ
    hρ hκ hlam hx hc hε
    (by positivity) hp (isPseudoMetricOnBonds_cellDistance F) (isPseudoMetricOnBonds_cellDistance F')
    hΨ hΨ' (fun z => (hW z).1)
    (fun z => by
      have := (hW z).2
      rwa [hwe] at this)
    (fun z => (hW' z).1)
    (fun z => by
      have := (hW' z).2
      rwa [hwe'] at this)
    hθ (fun η hη => by
      rw [hsum η hη, hwe])
    hθ' (fun η hη => by
      rw [hsum' η hη, hwe'])
    hH hH' (fun b => mem_bondsNearCell_iff b) (fun b => mem_bondsNearCell_iff b)
    (fun k k' => by
      simp only [blockDist]
      exact_mod_cast hd1 k k')
    (fun k => by
      simp only [blockDist]
      exact_mod_cast hd2 k)
    (fun z hz => le_cellDistance_of_not_mem_cellsNearCell hf hz)
    (fun z hz => le_cellDistance_of_not_mem_cellsNearCell hf' hz) hc1 hc2
def interpolatedTerm (star : Bool) (a ρA x lam v : ℝ) (m : ℕ) (V : F.GaugeField F.top) (z : F.Cell)
    (η : StepVariable (finiteCells F)) : ℝ :=
  v * cellExponent star a ρA x m z V η + (1 - v) * cellQuadratic lam x z η
def headDifference (star : Bool) (a ρA x lam : ℝ) (m : ℕ) (V : F.GaugeField F.top) (z : F.Cell)
    (η : StepVariable (finiteCells F)) : ℝ :=
  1 * cellExponent star a ρA x m z V η + (-1) * cellQuadratic lam x z η
def expansionPerturbedTerm (star : Bool) (a ρA x ν : ℝ) (m : ℕ) (f : LocalFamily) (V : F.GaugeField F.top)
    (z : F.Cell) (η : StepVariable (finiteCells F)) : ℝ :=
  1 * cellExponent star a ρA x m z V η + (-ν) * cellCentredExpansion star a ρA m f z η V
theorem stepExponent_eq_sub_expansions (star : Bool) (a ρA x ν : ℝ) (m : ℕ) (f : LocalFamily)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    stepExponent star a ρA x m f ν V η =
      stepExponent star a ρA x m (fun _ _ _ => 0) 0 V η -
        ν * ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion star a ρA m f y η V := by
  simp only [stepExponent, zero_mul, sub_zero]
theorem sum_centredExpansion_eq_sum_cells (hf : Finite F.Cell) (star : Bool) (a ρA : ℝ) (m : ℕ) (f : LocalFamily)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion star a ρA m f y η V =
      ∑ z ∈ finiteCells F, cellCentredExpansion star a ρA m f z η V := by
  classical
  unfold cellCentredExpansion
  exact (Finset.sum_fiberwise_of_maps_to (fun y _ => _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepFreezing.mem_finiteCells hf (enclosingCell y)) _).symm
theorem halfSqNormOn_univ_eq_sum_cells (hf : Finite F.Cell) (lam x : ℝ) (η : StepVariable (finiteCells F)) :
    halfSqNormOn (x * lam) Finset.univ η = ∑ z ∈ finiteCells F, cellQuadratic lam x z η := by
  classical
  unfold cellQuadratic halfSqNormOn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq]
  simp [_root_.YangMills.Construction.ColdStepAtMirrorFrames.StepFreezing.mem_finiteCells hf]
theorem exists_admissible_of_convexClassMember {star : Bool} {ρ m κ : ℝ} {P : StepVariable (finiteCells F) → ℝ}
    (h : IsConvexClassMember ρ m κ (chordBondDist F) P) :
    ∃ Ψ, IsAdmissiblePotential ρ m κ (fun b b' => blockDist F (bondBlock F b) (bondBlock F b')) Ψ ∧
      ∀ η ∈ openPolyball ↥(chordBonds (finiteCells F)) ρ, Ψ η = P η := by
  obtain ⟨Ψ, K, hEq, hK, hsl⟩ := h
  exact ⟨Ψ, ⟨K, hK, hsl⟩, fun η hη => hEq η hη⟩
theorem exists_interpolated_potential (hgood : AdmissiblePotentialStability) {star : Bool}
    {a ρA ρ lam x κ C v : ℝ} {m : ℕ}
    {f : LocalFamily} {V : F.GaugeField F.top} (hρ : 0 < ρ) (hκ : 0 < κ) (hx : 1 ≤ x) (hlam : 0 < lam)
    (hf : Finite F.Cell) (hB : CellExponentBounds star a ρA ρ x κ C m V)
    (hC : StepExponentIsConvex star a ρA ρ lam x κ m f 0 V) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ∃ Ψ, IsAdmissiblePotential ρ (x * lam / 4) κ
        (fun b b' => blockDist F (bondBlock F b) (bondBlock F b')) Ψ ∧
      (∀ η ∈ openPolyball ↥(chordBonds (finiteCells F)) ρ,
        Ψ η = v * stepExponent star a ρA x m f 0 V η + (1 - v) * totalQuadratic lam x η) ∧
      ∀ η ∈ openPolyball ↥(chordBonds (finiteCells F)) ρ,
        Ψ η = ∑ z ∈ finiteCells F, interpolatedTerm star a ρA x lam v m V z η := by
  obtain ⟨Ψ₀, g₀, hEq⟩ := exists_admissible_of_convexClassMember (star := star) hC
  have hx0 : 0 < x := by linarith
  have hm0 : 0 < x * lam / 4 := by positivity
  have h2m : 2 * (x * lam / 4) ≤ x * lam := by linarith [mul_pos hx0 hlam]
  have hd : IsPseudoMetricOnBonds (fun b b' : ↥(chordBonds (finiteCells F)) =>
      blockDist F (bondBlock F b) (bondBlock F b')) :=
    ⟨fun b => (isPseudoMetricOnBonds_cellDistance F).self _,
      fun b b' => (isPseudoMetricOnBonds_cellDistance F).symm _ _,
      fun b b' b'' => (isPseudoMetricOnBonds_cellDistance F).triangle _ _ _⟩
  obtain ⟨hsg, hsq, -, -⟩ :=
    hgood ↥(chordBonds (finiteCells F)) ρ (x * lam / 4) κ (x * lam) _ hρ hm0 hκ.le hd h2m
  refine ⟨segmentInterpolant (halfSqNormOn (x * lam) Finset.univ) Ψ₀ v, hsg _ _ v hsq g₀ hv0 hv1, ?_, ?_⟩
  · intro η hη
    simp only [segmentInterpolant]
    rw [hEq η hη]
    rfl
  · intro η hη
    simp only [segmentInterpolant]
    rw [hEq η hη, stepExponent_eq_sub_expansions, halfSqNormOn_univ_eq_sum_cells hf]
    simp only [zero_mul, sub_zero, interpolatedTerm, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hB.sum_eq η hη]
theorem exists_expansionPerturbed_potential {star : Bool} {a ρA ρ lam x κ C ν : ℝ} {m : ℕ}
    {f : LocalFamily} {V : F.GaugeField F.top} (hf : Finite F.Cell)
    (hB : CellExponentBounds star a ρA ρ x κ C m V)
    (hC : StepExponentIsConvex star a ρA ρ lam x κ m f ν V) :
    ∃ Ψ, IsAdmissiblePotential ρ (x * lam / 4) κ
        (fun b b' => blockDist F (bondBlock F b) (bondBlock F b')) Ψ ∧
      (∀ η ∈ openPolyball ↥(chordBonds (finiteCells F)) ρ, Ψ η = stepExponent star a ρA x m f ν V η) ∧
      ∀ η ∈ openPolyball ↥(chordBonds (finiteCells F)) ρ,
        Ψ η = ∑ z ∈ finiteCells F, expansionPerturbedTerm star a ρA x ν m f V z η := by
  obtain ⟨Ψ, g, hEq⟩ := exists_admissible_of_convexClassMember (star := star) hC
  refine ⟨Ψ, g, hEq, fun η hη => ?_⟩
  rw [hEq η hη, stepExponent_eq_sub_expansions, sum_centredExpansion_eq_sum_cells hf, hB.sum_eq η hη]
  simp only [expansionPerturbedTerm, Finset.sum_add_distrib, ← Finset.mul_sum, one_mul]
  ring
theorem contDiffOn_comp_pushforwardField {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {ρ : ℝ} (hρ : 0 < ρ) (j : κ → ι) (hj : Function.Injective j) {θ : BondField ι → ℝ}
    (hθ : ContDiffOn ℝ 1 θ (openPolyball ι ρ)) :
    ContDiffOn ℝ 1 (fun ζ => θ (pushforwardField j ζ)) (openPolyball κ ρ) := by
  have e : (fun ζ => θ (pushforwardField j ζ)) = fun ζ => θ (pushforwardFieldCLM j ζ) := by
    funext ζ
    rw [pushforwardFieldCLM_apply]
  rw [e]
  exact hθ.comp (pushforwardFieldCLM j).contDiff.contDiffOn (fun ξ hξ => by
    rw [pushforwardFieldCLM_apply]
    exact pushforwardField_mem_openPolyball hρ j hj hξ)
theorem mem_bondsNearCell_of_cell {Y z : F.Cell} {r : ℕ} (hz : z ∈ cellsNearCell F Y r)
    (b : ↥(chordBonds (finiteCells F))) (hb : bondBlock F b = z) : b ∈ bondsNearCell F Y r := by
  classical
  have h1 := (Finset.mem_filter.mp hz).2
  simp only [bondsNearCell, Finset.mem_filter, Finset.mem_univ, true_and]
  have h2 : enclosingCell b.1.1 = z := hb
  rw [h2]
  omega
theorem sum_eq_sum_bondsNearCell {Y : F.Cell} {r : ℕ} (G : ↥(chordBonds (finiteCells F)) → ℝ)
    (hG : ∀ b, b ∉ bondsNearCell F Y r → G b = 0) :
    ∑ b, G b = ∑ k : ↥(bondsNearCell F Y r), G k.1 := by
  rw [Finset.sum_coe_sort (bondsNearCell F Y r) G]
  exact (Finset.sum_subset (Finset.subset_univ _) fun b _ hb => hG b hb).symm
theorem cellQuadratic_pushforward_eq {F F' : BlockFrame} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} (lam x : ℝ)
    (e : ↥(bondsNearCell F Y r) ≃ ↥(bondsNearCell F' Y' r))
    (φ : {z // z ∈ cellsNearCell F Y r} ≃ {z // z ∈ cellsNearCell F' Y' r})
    (hd3 : ∀ k z, bondBlock F k.1 = z.1 ↔ bondBlock F' (e k).1 = (φ z).1)
    (z : {z // z ∈ cellsNearCell F Y r}) (ξ : BondField ↥(bondsNearCell F Y r)) :
    cellQuadratic lam x (φ z).1 (pushforwardField (fun k => (e k).1) ξ) =
      cellQuadratic lam x z.1 (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ξ) := by
  have hj : Function.Injective (fun k : ↥(bondsNearCell F Y r) => k.1) := Subtype.val_injective
  have hj' : Function.Injective (fun k : ↥(bondsNearCell F Y r) => (e k).1) :=
    fun a b h => e.injective (Subtype.ext h)
  unfold cellQuadratic
  rw [sum_eq_sum_bondsNearCell (Y := Y) (r := r) _ (fun b hb => by
        have : enclosingCell b.1.1 ≠ z.1 := fun h => hb (mem_bondsNearCell_of_cell z.2 b h)
        simp [this]),
    sum_eq_sum_bondsNearCell (Y := Y') (r := r) _ (fun b hb => by
        have : enclosingCell b.1.1 ≠ (φ z).1 := fun h => hb (mem_bondsNearCell_of_cell (φ z).2 b h)
        simp [this]),
    ← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ξ k.1 = ξ k :=
    pushforwardField_apply_image _ hj ξ k
  have h2 : pushforwardField (fun k => (e k).1) ξ (e k).1 = ξ k := pushforwardField_apply_image _ hj' ξ k
  rw [h1, h2]
  have h3 := hd3 k z
  by_cases h4 : enclosingCell k.1.1.1 = z.1
  · have h5 : enclosingCell (e k).1.1.1 = (φ z).1 := h3.mp h4
    simp [h4, h5]
  · have h5 : ¬ enclosingCell (e k).1.1.1 = (φ z).1 := fun h => h4 (h3.mpr h)
    simp [h4, h5]
theorem interpolated_terms_close {F F' : BlockFrame} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} {star : Bool}
    {a ρA ρ lam x κ C c ε v : ℝ} {m : ℕ} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    {e : ↥(bondsNearCell F Y r) ≃ ↥(bondsNearCell F' Y' r)}
    {φ : {z // z ∈ cellsNearCell F Y r} ≃ {z // z ∈ cellsNearCell F' Y' r}} (hρ : 0 < ρ) (hx : 0 ≤ x)
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hCc : C ≤ c) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hsm : ∀ z, ContDiffOn ℝ 1 (cellExponent star a ρA x m z V)
      (openPolyball ↥(chordBonds (finiteCells F)) ρ))
    (hsm' : ∀ z, ContDiffOn ℝ 1 (cellExponent star a ρA x m z V')
      (openPolyball ↥(chordBonds (finiteCells F')) ρ))
    (hTC : TermsCloseOnNearBonds ρ C ε x κ Y Y' r e φ (fun z => cellExponent star a ρA x m z V)
      (fun z => cellExponent star a ρA x m z V'))
    (hd3 : ∀ k z, bondBlock F k.1 = z.1 ↔ bondBlock F' (e k).1 = (φ z).1)
    (hd4 : ∀ z : {z // z ∈ cellsNearCell F Y r}, z.1 = Y → (φ z).1 = Y') (hY : Y ∈ cellsNearCell F Y r) :
    (∀ (z : {z // z ∈ cellsNearCell F Y r}), ∀ ξ ∈ openPolyball ↥(bondsNearCell F Y r) ρ, ∀ k,
      bondGradNorm (fun ζ => interpolatedTerm star a ρA x lam v m V' (φ z).1 (pushforwardField (fun k => (e k).1) ζ) -
        interpolatedTerm star a ρA x lam v m V z.1
          (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ζ)) k ξ ≤
        c * ε * (x * Real.sqrt (weightedSqNormNear κ (fun k : ↥(bondsNearCell F Y r) => bondBlock F k.1)
          (blockDist F) z.1 ξ) + 1) *
          Real.exp (-(2 * κ * blockDist F (bondBlock F k.1) z.1))) ∧
    (∀ ξ ∈ openPolyball ↥(bondsNearCell F Y r) ρ,
      |headDifference star a ρA x lam m V' Y' (pushforwardField (fun k => (e k).1) ξ) -
        headDifference star a ρA x lam m V Y (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ξ)| ≤
        c * ε * (x * weightedSqNormNear κ (fun k : ↥(bondsNearCell F Y r) => bondBlock F k.1)
          (blockDist F) Y ξ + 1)) := by
  have hj : Function.Injective (fun k : ↥(bondsNearCell F Y r) => k.1) := Subtype.val_injective
  have hj' : Function.Injective (fun k : ↥(bondsNearCell F Y r) => (e k).1) :=
    fun a b h => e.injective (Subtype.ext h)
  refine ⟨fun z ξ hξ k => ?_, fun ξ hξ => ?_⟩
  · set A : BondField ↥(bondsNearCell F Y r) → ℝ := fun ζ =>
      cellExponent star a ρA x m (φ z).1 V' (pushforwardField (fun k => (e k).1) ζ) -
        cellExponent star a ρA x m z.1 V (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ζ) with hA
    have hAs : ContDiffOn ℝ 1 A (openPolyball ↥(bondsNearCell F Y r) ρ) :=
      (contDiffOn_comp_pushforwardField hρ _ hj' (hsm' (φ z).1)).sub
        (contDiffOn_comp_pushforwardField hρ _ hj (hsm z.1))
    have e1 : (fun ζ => interpolatedTerm star a ρA x lam v m V' (φ z).1 (pushforwardField (fun k => (e k).1) ζ) -
        interpolatedTerm star a ρA x lam v m V z.1
          (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ζ)) =
        fun ζ => v * A ζ + 0 * A ζ := by
      funext ζ
      simp only [interpolatedTerm, hA]
      rw [cellQuadratic_pushforward_eq lam x e φ hd3 z ζ]
      ring
    rw [e1]
    have h1 := bondGradNorm_linear_combination_le hρ hAs hAs v 0 hξ k
    have h2 := (hTC z ξ hξ).2 k
    rw [abs_zero, zero_mul, add_zero, abs_of_nonneg hv0] at h1
    have h3 : v * bondGradNorm A k ξ ≤ bondGradNorm A k ξ := by
      have := bondGradNorm_nonneg A k ξ
      nlinarith
    refine h1.trans (h3.trans (h2.trans ?_))
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_right _ (by
      have := Real.sqrt_nonneg (weightedSqNormNear κ (fun k : ↥(bondsNearCell F Y r) => bondBlock F k.1)
        (blockDist F) z.1 ξ)
      positivity)
    exact mul_le_mul_of_nonneg_right hCc hε
  · set z₀ : {z // z ∈ cellsNearCell F Y r} := ⟨Y, hY⟩ with hz₀
    have h1 := (hTC z₀ ξ hξ).1
    have h2 : (φ z₀).1 = Y' := hd4 z₀ rfl
    have h3 := cellQuadratic_pushforward_eq lam x e φ hd3 z₀ ξ
    rw [h2] at h1 h3
    have e2 : headDifference star a ρA x lam m V' Y' (pushforwardField (fun k => (e k).1) ξ) -
        headDifference star a ρA x lam m V Y (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ξ) =
        cellExponent star a ρA x m Y' V' (pushforwardField (fun k => (e k).1) ξ) -
          cellExponent star a ρA x m Y V (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ξ) := by
      simp only [headDifference]
      rw [h3]
      ring
    rw [e2]
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_right _ (by
      have := weightedSqNormNear_nonneg_at (r := κ) (pos := fun k : ↥(bondsNearCell F Y r) => bondBlock F k.1)
        (D := blockDist F) Y ξ
      positivity)
    exact mul_le_mul_of_nonneg_right hCc hε
theorem expansionPerturbed_terms_close {F F' : BlockFrame} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} {star : Bool}
    {a ρA ρ x κ C₁ C₂ c ε ν : ℝ} {m : ℕ} {f : LocalFamily} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    {e : ↥(bondsNearCell F Y r) ≃ ↥(bondsNearCell F' Y' r)}
    {φ : {z // z ∈ cellsNearCell F Y r} ≃ {z // z ∈ cellsNearCell F' Y' r}} (hρ : 0 < ρ) (hx : 0 ≤ x)
    (hε : 0 ≤ ε) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCc : C₁ + C₂ ≤ c) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hsm : ∀ z, ContDiffOn ℝ 1 (cellExponent star a ρA x m z V)
      (openPolyball ↥(chordBonds (finiteCells F)) ρ))
    (hsm' : ∀ z, ContDiffOn ℝ 1 (cellExponent star a ρA x m z V')
      (openPolyball ↥(chordBonds (finiteCells F')) ρ))
    (hrm : ∀ z, ContDiffOn ℝ 1 (fun ζ => cellCentredExpansion star a ρA m f z ζ V)
      (openPolyball ↥(chordBonds (finiteCells F)) ρ))
    (hrm' : ∀ z, ContDiffOn ℝ 1 (fun ζ => cellCentredExpansion star a ρA m f z ζ V')
      (openPolyball ↥(chordBonds (finiteCells F')) ρ))
    (hTC : TermsCloseOnNearBonds ρ C₁ ε x κ Y Y' r e φ (fun z => cellExponent star a ρA x m z V)
      (fun z => cellExponent star a ρA x m z V'))
    (hTR : TermsCloseOnNearBonds ρ C₂ ε x κ Y Y' r e φ (fun z η => cellCentredExpansion star a ρA m f z η V)
      (fun z η => cellCentredExpansion star a ρA m f z η V'))
    (hd4 : ∀ z : {z // z ∈ cellsNearCell F Y r}, z.1 = Y → (φ z).1 = Y') (hY : Y ∈ cellsNearCell F Y r) :
    (∀ (z : {z // z ∈ cellsNearCell F Y r}), ∀ ξ ∈ openPolyball ↥(bondsNearCell F Y r) ρ, ∀ k,
      bondGradNorm (fun ζ => expansionPerturbedTerm star a ρA x ν m f V' (φ z).1 (pushforwardField (fun k => (e k).1) ζ) -
        expansionPerturbedTerm star a ρA x ν m f V z.1
          (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ζ)) k ξ ≤
        c * ε * (x * Real.sqrt (weightedSqNormNear κ (fun k : ↥(bondsNearCell F Y r) => bondBlock F k.1)
          (blockDist F) z.1 ξ) + 1) *
          Real.exp (-(2 * κ * blockDist F (bondBlock F k.1) z.1))) ∧
    (∀ ξ ∈ openPolyball ↥(bondsNearCell F Y r) ρ,
      |cellCentredExpansion star a ρA m f Y' (pushforwardField (fun k => (e k).1) ξ) V' -
        cellCentredExpansion star a ρA m f Y (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ξ) V| ≤
        c * ε * (x * weightedSqNormNear κ (fun k : ↥(bondsNearCell F Y r) => bondBlock F k.1)
          (blockDist F) Y ξ + 1)) := by
  have hj : Function.Injective (fun k : ↥(bondsNearCell F Y r) => k.1) := Subtype.val_injective
  have hj' : Function.Injective (fun k : ↥(bondsNearCell F Y r) => (e k).1) :=
    fun a b h => e.injective (Subtype.ext h)
  refine ⟨fun z ξ hξ k => ?_, fun ξ hξ => ?_⟩
  · set A : BondField ↥(bondsNearCell F Y r) → ℝ := fun ζ =>
      cellExponent star a ρA x m (φ z).1 V' (pushforwardField (fun k => (e k).1) ζ) -
        cellExponent star a ρA x m z.1 V (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ζ) with hA
    set B : BondField ↥(bondsNearCell F Y r) → ℝ := fun ζ =>
      cellCentredExpansion star a ρA m f (φ z).1 (pushforwardField (fun k => (e k).1) ζ) V' -
        cellCentredExpansion star a ρA m f z.1 (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ζ) V with hBd
    have hAs : ContDiffOn ℝ 1 A (openPolyball ↥(bondsNearCell F Y r) ρ) :=
      (contDiffOn_comp_pushforwardField hρ _ hj' (hsm' (φ z).1)).sub
        (contDiffOn_comp_pushforwardField hρ _ hj (hsm z.1))
    have hBs : ContDiffOn ℝ 1 B (openPolyball ↥(bondsNearCell F Y r) ρ) :=
      (contDiffOn_comp_pushforwardField hρ _ hj' (hrm' (φ z).1)).sub
        (contDiffOn_comp_pushforwardField hρ _ hj (hrm z.1))
    have e1 : (fun ζ => expansionPerturbedTerm star a ρA x ν m f V' (φ z).1 (pushforwardField (fun k => (e k).1) ζ) -
        expansionPerturbedTerm star a ρA x ν m f V z.1
          (pushforwardField (fun k : ↥(bondsNearCell F Y r) => k.1) ζ)) =
        fun ζ => 1 * A ζ + (-ν) * B ζ := by
      funext ζ
      simp only [expansionPerturbedTerm, hA, hBd]
      ring
    rw [e1]
    have h1 := bondGradNorm_linear_combination_le hρ hAs hBs 1 (-ν) hξ k
    have h2 := (hTC z ξ hξ).2 k
    have h3 := (hTR z ξ hξ).2 k
    rw [abs_one, abs_neg, abs_of_nonneg hν0, one_mul] at h1
    set u := x * Real.sqrt (weightedSqNormNear κ (fun k : ↥(bondsNearCell F Y r) => bondBlock F k.1)
      (blockDist F) z.1 ξ) + 1 with hu
    have hu0 : 0 ≤ u := by
      have := Real.sqrt_nonneg (weightedSqNormNear κ (fun k : ↥(bondsNearCell F Y r) => bondBlock F k.1)
        (blockDist F) z.1 ξ)
      positivity
    set w := Real.exp (-(2 * κ * blockDist F (bondBlock F k.1) z.1)) with hw
    have hw0 : 0 < w := Real.exp_pos _
    have h4 : ν * bondGradNorm B k ξ ≤ C₂ * ε * u * w := by
      have := bondGradNorm_nonneg B k ξ
      have h5 : ν * bondGradNorm B k ξ ≤ 1 * bondGradNorm B k ξ :=
        mul_le_mul_of_nonneg_right hν1 this
      linarith
    have h6 : 0 ≤ ε * u * w := by positivity
    calc bondGradNorm (fun ζ => 1 * A ζ + (-ν) * B ζ) k ξ
        ≤ C₁ * ε * u * w + C₂ * ε * u * w := h1.trans (add_le_add h2 h4)
      _ = (C₁ + C₂) * (ε * u * w) := by ring
      _ ≤ c * (ε * u * w) := mul_le_mul_of_nonneg_right hCc h6
      _ = c * ε * u * w := by ring
  · set z₀ : {z // z ∈ cellsNearCell F Y r} := ⟨Y, hY⟩ with hz₀
    have h1 := (hTR z₀ ξ hξ).1
    have h2 : (φ z₀).1 = Y' := hd4 z₀ rfl
    rw [h2] at h1
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_right _ (by
      have := weightedSqNormNear_nonneg_at (r := κ) (pos := fun k : ↥(bondsNearCell F Y r) => bondBlock F k.1)
        (D := blockDist F) Y ξ
      positivity)
    apply mul_le_mul_of_nonneg_right _ hε
    linarith
theorem freezing_constants_nonneg {lam S : ℝ} (hlam : 0 < lam) (hS : 0 ≤ S) :
    0 ≤ freezingConstant lam S ∧ 0 ≤ blockComparisonConstant lam S := by
  unfold freezingConstant blockComparisonConstant
  constructor <;> positivity
theorem freezing_sum_le {lam S c κ : ℝ} (hlam : 0 < lam) (hS : 0 ≤ S) (hκ : 0 < κ) (r : ℕ) :
    c ^ 2 * (2 * freezingConstant lam S * Real.exp (-(κ * r / 16)) +
      blockComparisonConstant lam S * (Real.exp (-(4 * κ * r)) + Real.exp (-(κ * r / 32)))) ≤
      freezingThreshold lam S c * Real.exp (-(κ * r / 2 ^ 7)) := by
  obtain ⟨h1, h2⟩ := freezing_constants_nonneg hlam hS
  have hr : 0 ≤ κ * r := by positivity
  set E := Real.exp (-(κ * r / 2 ^ 7)) with hE
  have e1 : Real.exp (-(κ * r / 16)) ≤ E := by
    apply Real.exp_le_exp.mpr
    linarith
  have e2 : Real.exp (-(4 * κ * r)) ≤ E := by
    apply Real.exp_le_exp.mpr
    linarith
  have e3 : Real.exp (-(κ * r / 32)) ≤ E := by
    apply Real.exp_le_exp.mpr
    linarith
  unfold freezingThreshold
  have h3 : 2 * freezingConstant lam S * Real.exp (-(κ * r / 16)) +
      blockComparisonConstant lam S * (Real.exp (-(4 * κ * r)) + Real.exp (-(κ * r / 32))) ≤
      (2 * freezingConstant lam S + 2 * blockComparisonConstant lam S) * E := by
    have t1 := mul_le_mul_of_nonneg_left e1 (by positivity : 0 ≤ 2 * freezingConstant lam S)
    have t2 := mul_le_mul_of_nonneg_left (add_le_add e2 e3) h2
    nlinarith
  calc c ^ 2 * (2 * freezingConstant lam S * Real.exp (-(κ * r / 16)) +
        blockComparisonConstant lam S * (Real.exp (-(4 * κ * r)) + Real.exp (-(κ * r / 32))))
      ≤ c ^ 2 * ((2 * freezingConstant lam S + 2 * blockComparisonConstant lam S) * E) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring
theorem abs_sub_le_of_small_radius {a a' B κ nss : ℝ} {rr : ℝ} {Cst : ℝ} (hκ : 0 < κ) (hr : rr ≤ nss)
    (ha : |a| ≤ B) (ha' : |a'| ≤ B) (hB : 0 ≤ B)
    (hC : 2 * B * Real.exp (κ * nss / 2 ^ 7) ≤ Cst) :
    |a - a'| ≤ Cst * Real.exp (-(κ * rr / 2 ^ 7)) := by
  have h1 : |a - a'| ≤ 2 * B := by
    have := abs_sub a a'
    linarith
  refine h1.trans ?_
  have h2 : 1 ≤ Real.exp (κ * nss / 2 ^ 7) * Real.exp (-(κ * rr / 2 ^ 7)) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp
    have : κ * rr ≤ κ * nss := mul_le_mul_of_nonneg_left hr hκ.le
    linarith
  calc 2 * B ≤ 2 * B * (Real.exp (κ * nss / 2 ^ 7) * Real.exp (-(κ * rr / 2 ^ 7))) := by
        have : 0 ≤ 2 * B := by positivity
        nlinarith
    _ = 2 * B * Real.exp (κ * nss / 2 ^ 7) * Real.exp (-(κ * rr / 2 ^ 7)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
def interpolatedConstant (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : ℝ := T.Ct + T.chainParams.lam + 1
def expansionPerturbedConstant (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : ℝ := (T.Ct + 1) * (1 + T.energyRatio * (T.L : ℝ) ^ 4)
structure TorusData (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (S x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (star : Bool) : Prop where
  finite : Finite F.Cell
  odd_blockSide : Odd F.blockSide
  two_le_extent : ∀ i, 2 ≤ F.extent i
  blockSide_eq : F.blockSide = T.L
  weight_sums_le : ∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(T.κ / 4 * blockDist F (bondBlock F b) z)) ≤ S ∧
    ∑ z' ∈ finiteCells F, Real.exp (-(T.κ / 4 * blockDist F z' z)) ≤ S
  exponent_bounds : CellExponentBounds star T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V
  expansion_bounds : CentredExpansionBounds star T.a T.chainParams.ρA T.ballRadius T.κ T.decayRate T.E T.energyRatio T.Ct T.L
    (frameRadius x) f V
  convex : ∀ ν : ℝ, 0 ≤ ν → ν ≤ 1 →
    StepExponentIsConvex star T.a T.chainParams.ρA T.ballRadius T.chainParams.lam x T.κ (frameRadius x) f ν V
  expansion_abs_le : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ < T.ballRadius) →
    |cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y η V| ≤ T.E
structure PositivityData (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (S x : ℝ) : Prop where
  radius_pos : 0 < T.ballRadius
  κ_pos : 0 < T.κ
  one_le_x : 1 ≤ x
  lam_pos : 0 < T.chainParams.lam
  Ct_nonneg : 0 ≤ T.Ct
  one_le_E : 1 ≤ T.E
  E_le_energyRatio : T.E ≤ T.energyRatio
  one_le_blockSide_pow : 1 ≤ (T.L : ℝ) ^ 4
  S_nonneg : 0 ≤ S
  cutoff : IsCutoff T.ballRadius T.p
variable {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {S x : ℝ} {f : LocalFamily} {F F' : BlockFrame} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top} {star : Bool}
theorem isLocalTermAt_interpolatedTerm (g : PositivityData T S x) (hs : TorusData T S x f F V star) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (z : F.Cell) :
    IsLocalTermAt T.ballRadius T.κ (interpolatedConstant T) x (bondBlock F) (blockDist F) z
      (interpolatedTerm star T.a T.chainParams.ρA x T.chainParams.lam v (frameRadius x) V z) := by
  have hx0 : 0 ≤ x := by linarith [g.one_le_x]
  have h1 := isLocalTermAt_cellExponent g.radius_pos g.κ_pos g.Ct_nonneg hx0 hs.exponent_bounds z
  have h2 := isLocalTermAt_cellQuadratic (F := F) g.radius_pos g.κ_pos g.lam_pos.le hx0 z
  have h3 := isLocalTermAt_linear_combination g.radius_pos h1 h2 v (1 - v)
  refine isLocalTermAt_mono ?_ hx0 h3
  rw [abs_of_nonneg hv0, abs_of_nonneg (by linarith : 0 ≤ 1 - v)]
  unfold interpolatedConstant
  have := g.Ct_nonneg
  have := g.lam_pos
  nlinarith
theorem isLocalTermAt_headDifference (g : PositivityData T S x) (hs : TorusData T S x f F V star) (z : F.Cell) :
    IsLocalTermAt T.ballRadius T.κ (interpolatedConstant T) x (bondBlock F) (blockDist F) z
      (headDifference star T.a T.chainParams.ρA x T.chainParams.lam (frameRadius x) V z) := by
  have hx0 : 0 ≤ x := by linarith [g.one_le_x]
  have h1 := isLocalTermAt_cellExponent g.radius_pos g.κ_pos g.Ct_nonneg hx0 hs.exponent_bounds z
  have h2 := isLocalTermAt_cellQuadratic (F := F) g.radius_pos g.κ_pos g.lam_pos.le hx0 z
  have h3 := isLocalTermAt_linear_combination g.radius_pos h1 h2 1 (-1)
  refine isLocalTermAt_mono ?_ hx0 h3
  simp only [abs_one, abs_neg, one_mul]
  unfold interpolatedConstant
  linarith
theorem isLocalTermAt_cellCentredExpansion_of (g : PositivityData T S x) (hb : SiteDecomposition)
    (hs : TorusData T S x f F V star) (z : F.Cell) :
    IsLocalTermAt T.ballRadius T.κ (T.Ct * T.E * (T.L : ℝ) ^ 4) x (bondBlock F) (blockDist F) z
      (fun ζ => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f z ζ V) := by
  have h := isLocalTermAt_cellCentredExpansion g.radius_pos g.κ_pos g.Ct_nonneg (by linarith [g.one_le_E]) g.one_le_x
    hs.expansion_bounds hb hs.odd_blockSide hs.two_le_extent z
  rwa [hs.blockSide_eq] at h
theorem expansionPerturbedConstant_bounds (g : PositivityData T S x) :
    T.Ct * T.E * (T.L : ℝ) ^ 4 ≤ expansionPerturbedConstant T ∧
      T.Ct + T.Ct * T.E * (T.L : ℝ) ^ 4 ≤ expansionPerturbedConstant T ∧
      T.Ct + T.Ct * T.energyRatio ≤ expansionPerturbedConstant T ∧ 1 ≤ expansionPerturbedConstant T := by
  have hC := g.Ct_nonneg
  have hE := g.one_le_E
  have hE₃ := g.E_le_energyRatio
  have hL := g.one_le_blockSide_pow
  set q := (T.L : ℝ) ^ 4
  have h0 : 0 ≤ T.energyRatio := by linarith
  have a1 : T.Ct * T.E * q ≤ T.Ct * T.energyRatio * q := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left hE₃ hC
  have a2 : T.Ct * T.energyRatio ≤ T.Ct * T.energyRatio * q := by
    have : 0 ≤ T.Ct * T.energyRatio := by positivity
    nlinarith
  have a3 : 0 ≤ T.energyRatio * q := by positivity
  have a4 : 0 ≤ T.Ct * T.energyRatio * q := by positivity
  have e : expansionPerturbedConstant T = T.Ct + T.Ct * T.energyRatio * q + 1 + T.energyRatio * q := by
    unfold expansionPerturbedConstant
    ring
  rw [e]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩
theorem isLocalTermAt_expansionPerturbedTerm (g : PositivityData T S x) (hb : SiteDecomposition)
    (hs : TorusData T S x f F V star) {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (z : F.Cell) :
    IsLocalTermAt T.ballRadius T.κ (expansionPerturbedConstant T) x (bondBlock F) (blockDist F) z
      (expansionPerturbedTerm star T.a T.chainParams.ρA x ν (frameRadius x) f V z) := by
  have hx0 : 0 ≤ x := by linarith [g.one_le_x]
  have h1 := isLocalTermAt_cellExponent g.radius_pos g.κ_pos g.Ct_nonneg hx0 hs.exponent_bounds z
  have h2 := isLocalTermAt_cellCentredExpansion_of g hb hs z
  have h3 := isLocalTermAt_linear_combination g.radius_pos h1 h2 1 (-ν)
  refine isLocalTermAt_mono ?_ hx0 h3
  rw [abs_one, abs_neg, abs_of_nonneg hν0, one_mul]
  obtain ⟨_, c2, _, _⟩ := expansionPerturbedConstant_bounds g
  have : 0 ≤ T.Ct * T.E * (T.L : ℝ) ^ 4 := by
    have := g.Ct_nonneg
    have := g.one_le_E
    positivity
  nlinarith
theorem cutoffMean_eq_ballExpectation (ρ : ℝ) (p : ℝ → ℝ) (Ψ H : StepVariable (finiteCells F) → ℝ) :
    cutoffMean ρ p Ψ H = ballExpectation (cutoffFactor ρ p) Ψ H := rfl
theorem mem_cellsNearCell_self {Y : F.Cell} {r : ℕ} (hf : Finite F.Cell) (hr : 1 ≤ r) :
    Y ∈ cellsNearCell F Y r := by
  classical
  simp only [cellsNearCell, Finset.mem_filter, _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepFreezing.mem_finiteCells hf Y, true_and, PatchLocality.cellSupDist_self]
  omega
theorem continuous_of_isAdmissiblePotential {ρ m r : ℝ}
    {d : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ}
    {Ψ : StepVariable (finiteCells F) → ℝ} (g : IsAdmissiblePotential ρ m r d Ψ) : Continuous Ψ := by
  obtain ⟨K, hK, _⟩ := g
  exact hK.smooth.continuous
theorem interpolated_freezing_large_radius (hfz : BallExpectationFreezingBound)
    (hbox : NearBlocksCorrespondByOffset)
    (hgood : AdmissiblePotentialStability) (hmc : CutoffExpectationIsPositiveForm)
    (g : PositivityData T S x) (hs : TorusData T S x f F V star) (hs' : TorusData T S x f F' V' star)
    {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} (ht : F.depth = F'.depth)
    (h1 : ∀ i, 2 * r + 2 < F.extent i) (h2 : ∀ i, 2 * r + 2 < F'.extent i) (hr : 1 ≤ r)
    (hX : ∀ (e : ↥(bondsNearCell F Y r) ≃ ↥(bondsNearCell F' Y' r))
      (φ : {z // z ∈ cellsNearCell F Y r} ≃ {z // z ∈ cellsNearCell F' Y' r}),
      BondsMatchByOffset Y Y' r e → CellsMatchByOffset Y Y' r φ →
      TermsCloseOnNearBonds T.ballRadius T.Ct (Real.exp (-(4 * T.κ * r))) x T.κ Y Y' r e φ
        (fun z => cellExponent star T.a T.chainParams.ρA x (frameRadius x) z V)
        (fun z => cellExponent star T.a T.chainParams.ρA x (frameRadius x) z V'))
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    |cutoffMean T.ballRadius T.p (fun η => v * stepExponent star T.a T.chainParams.ρA x (frameRadius x) f 0 V η +
          (1 - v) * totalQuadratic T.chainParams.lam x η)
        (fun η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y V η -
          cellQuadratic T.chainParams.lam x Y η) -
      cutoffMean T.ballRadius T.p (fun η => v * stepExponent star T.a T.chainParams.ρA x (frameRadius x) f 0 V' η +
          (1 - v) * totalQuadratic T.chainParams.lam x η)
        (fun η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y' V' η -
          cellQuadratic T.chainParams.lam x Y' η)| ≤
      freezingThreshold T.chainParams.lam S (interpolatedConstant T) * Real.exp (-(T.κ * r / 2 ^ 7)) := by
  have hx0 : 0 ≤ x := by linarith [g.one_le_x]
  obtain ⟨Ψ, gΨ, eΨ, sΨ⟩ := exists_interpolated_potential hgood g.radius_pos g.κ_pos g.one_le_x g.lam_pos
    hs.finite hs.exponent_bounds (hs.convex 0 le_rfl zero_le_one) hv0 hv1
  obtain ⟨Ψ', gΨ', eΨ', sΨ'⟩ := exists_interpolated_potential hgood g.radius_pos g.κ_pos g.one_le_x g.lam_pos
    hs'.finite hs'.exponent_bounds (hs'.convex 0 le_rfl zero_le_one) hv0 hv1
  have F₁ := hmc _ T.ballRadius T.p Ψ g.radius_pos g.cutoff (continuous_of_isAdmissiblePotential gΨ)
  have F₂ := hmc _ T.ballRadius T.p Ψ' g.radius_pos g.cutoff (continuous_of_isAdmissiblePotential gΨ')
  have m1 := F₁.congr_potential _
    (headDifference star T.a T.chainParams.ρA x T.chainParams.lam (frameRadius x) V Y) eΨ
  have m2 := F₂.congr_potential _
    (headDifference star T.a T.chainParams.ρA x T.chainParams.lam (frameRadius x) V' Y') eΨ'
  have eH : (fun η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y V η -
      cellQuadratic T.chainParams.lam x Y η) =
      headDifference star T.a T.chainParams.ρA x T.chainParams.lam (frameRadius x) V Y := by
    funext η
    simp only [headDifference]
    ring
  have eH' : (fun η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y' V' η -
      cellQuadratic T.chainParams.lam x Y' η) =
      headDifference star T.a T.chainParams.ρA x T.chainParams.lam (frameRadius x) V' Y' := by
    funext η
    simp only [headDifference]
    ring
  rw [eH, eH', cutoffMean_eq_ballExpectation, cutoffMean_eq_ballExpectation, ← m1, ← m2]
  have hc1 : 1 ≤ interpolatedConstant T := by
    unfold interpolatedConstant
    linarith [g.Ct_nonneg, g.lam_pos]
  have hsm : ∀ z, ContDiffOn ℝ 1 (cellExponent star T.a T.chainParams.ρA x (frameRadius x) z V)
      (openPolyball ↥(chordBonds (finiteCells F)) T.ballRadius) := fun z =>
    contDiffOn_one_of_two
      (isLocalTermAt_cellExponent g.radius_pos g.κ_pos g.Ct_nonneg hx0 hs.exponent_bounds z).smooth
  have hsm' : ∀ z, ContDiffOn ℝ 1 (cellExponent star T.a T.chainParams.ρA x (frameRadius x) z V')
      (openPolyball ↥(chordBonds (finiteCells F')) T.ballRadius) := fun z =>
    contDiffOn_one_of_two
      (isLocalTermAt_cellExponent g.radius_pos g.κ_pos g.Ct_nonneg hx0 hs'.exponent_bounds z).smooth
  have main := abs_ballExpectation_sub_le_of_local (S := S) (lam := T.chainParams.lam)
    (ε := Real.exp (-(4 * T.κ * r))) hfz hbox
    (hs.blockSide_eq.trans hs'.blockSide_eq.symm) ht hs.odd_blockSide h1 h2 g.radius_pos g.κ_pos g.lam_pos
    g.one_le_x hc1 (Real.exp_pos _).le g.cutoff
    gΨ gΨ' hs.weight_sums_le hs'.weight_sums_le (fun z => isLocalTermAt_interpolatedTerm g hs hv0 hv1 z) sΨ
    (fun z => isLocalTermAt_interpolatedTerm g hs' hv0 hv1 z) sΨ'
    (isLocalTermAt_headDifference g hs Y) (isLocalTermAt_headDifference g hs' Y')
    (fun e φ hbm hcm hd3 hd4 => interpolated_terms_close g.radius_pos hx0 (Real.exp_pos _).le g.Ct_nonneg
      (by unfold interpolatedConstant; linarith [g.lam_pos]) hv0 hv1 hsm hsm' (hX e φ hbm hcm) hd3 hd4
      (mem_cellsNearCell_self hs.finite hr))
  exact main.trans (freezing_sum_le g.lam_pos g.S_nonneg g.κ_pos r)
theorem expansionPerturbed_freezing_large_radius (hfz : BallExpectationFreezingBound)
    (hbox : NearBlocksCorrespondByOffset)
    (hmc : CutoffExpectationIsPositiveForm) (hb : SiteDecomposition)
    (g : PositivityData T S x) (hs : TorusData T S x f F V star) (hs' : TorusData T S x f F' V' star)
    {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} (ht : F.depth = F'.depth)
    (h1 : ∀ i, 2 * r + 2 < F.extent i) (h2 : ∀ i, 2 * r + 2 < F'.extent i) (hr : 1 ≤ r)
    (hX : ∀ (e : ↥(bondsNearCell F Y r) ≃ ↥(bondsNearCell F' Y' r))
      (φ : {z // z ∈ cellsNearCell F Y r} ≃ {z // z ∈ cellsNearCell F' Y' r}),
      BondsMatchByOffset Y Y' r e → CellsMatchByOffset Y Y' r φ →
      TermsCloseOnNearBonds T.ballRadius T.Ct (Real.exp (-(4 * T.κ * r))) x T.κ Y Y' r e φ
        (fun z => cellExponent star T.a T.chainParams.ρA x (frameRadius x) z V)
        (fun z => cellExponent star T.a T.chainParams.ρA x (frameRadius x) z V') ∧
      TermsCloseOnNearBonds T.ballRadius (T.Ct * T.energyRatio) (Real.exp (-(4 * T.κ * r))) x T.κ Y Y' r e φ
        (fun z η => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f z η V)
        (fun z η => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f z η V'))
    {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) :
    |cutoffMean T.ballRadius T.p (stepExponent star T.a T.chainParams.ρA x (frameRadius x) f ν V)
        (fun η => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y η V) -
      cutoffMean T.ballRadius T.p (stepExponent star T.a T.chainParams.ρA x (frameRadius x) f ν V')
        (fun η => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y' η V')| ≤
      freezingThreshold T.chainParams.lam S (expansionPerturbedConstant T) * Real.exp (-(T.κ * r / 2 ^ 7)) := by
  have hx0 : 0 ≤ x := by linarith [g.one_le_x]
  obtain ⟨Ψ, gΨ, eΨ, sΨ⟩ := exists_expansionPerturbed_potential hs.finite hs.exponent_bounds (hs.convex ν hν0 hν1)
  obtain ⟨Ψ', gΨ', eΨ', sΨ'⟩ :=
    exists_expansionPerturbed_potential hs'.finite hs'.exponent_bounds (hs'.convex ν hν0 hν1)
  have F₁ := hmc _ T.ballRadius T.p Ψ g.radius_pos g.cutoff (continuous_of_isAdmissiblePotential gΨ)
  have F₂ := hmc _ T.ballRadius T.p Ψ' g.radius_pos g.cutoff (continuous_of_isAdmissiblePotential gΨ')
  have m1 := F₁.congr_potential _
    (fun η => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y η V) eΨ
  have m2 := F₂.congr_potential _
    (fun η => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y' η V') eΨ'
  rw [cutoffMean_eq_ballExpectation, cutoffMean_eq_ballExpectation, ← m1, ← m2]
  obtain ⟨c1, _, c3, c4⟩ := expansionPerturbedConstant_bounds g
  have hE₃ : 0 ≤ T.energyRatio := by linarith [g.one_le_E, g.E_le_energyRatio]
  have hsm : ∀ z, ContDiffOn ℝ 1 (cellExponent star T.a T.chainParams.ρA x (frameRadius x) z V)
      (openPolyball ↥(chordBonds (finiteCells F)) T.ballRadius) := fun z =>
    contDiffOn_one_of_two
      (isLocalTermAt_cellExponent g.radius_pos g.κ_pos g.Ct_nonneg hx0 hs.exponent_bounds z).smooth
  have hsm' : ∀ z, ContDiffOn ℝ 1 (cellExponent star T.a T.chainParams.ρA x (frameRadius x) z V')
      (openPolyball ↥(chordBonds (finiteCells F')) T.ballRadius) := fun z =>
    contDiffOn_one_of_two
      (isLocalTermAt_cellExponent g.radius_pos g.κ_pos g.Ct_nonneg hx0 hs'.exponent_bounds z).smooth
  have hrm : ∀ z, ContDiffOn ℝ 1 (fun ζ => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f z ζ V)
      (openPolyball ↥(chordBonds (finiteCells F)) T.ballRadius) := fun z =>
    contDiffOn_one_of_two (isLocalTermAt_cellCentredExpansion_of g hb hs z).smooth
  have hrm' : ∀ z, ContDiffOn ℝ 1 (fun ζ => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f z ζ V')
      (openPolyball ↥(chordBonds (finiteCells F')) T.ballRadius) := fun z =>
    contDiffOn_one_of_two (isLocalTermAt_cellCentredExpansion_of g hb hs' z).smooth
  have main := abs_ballExpectation_sub_le_of_local (S := S) (lam := T.chainParams.lam)
    (ε := Real.exp (-(4 * T.κ * r))) hfz hbox
    (hs.blockSide_eq.trans hs'.blockSide_eq.symm) ht hs.odd_blockSide h1 h2 g.radius_pos g.κ_pos g.lam_pos
    g.one_le_x c4 (Real.exp_pos _).le g.cutoff
    gΨ gΨ' hs.weight_sums_le hs'.weight_sums_le (fun z => isLocalTermAt_expansionPerturbedTerm g hb hs hν0 hν1 z) sΨ
    (fun z => isLocalTermAt_expansionPerturbedTerm g hb hs' hν0 hν1 z) sΨ'
    (isLocalTermAt_mono c1 hx0 (isLocalTermAt_cellCentredExpansion_of g hb hs Y))
    (isLocalTermAt_mono c1 hx0 (isLocalTermAt_cellCentredExpansion_of g hb hs' Y'))
    (fun e φ hbm hcm hd3 hd4 => expansionPerturbed_terms_close (C₁ := T.Ct) (C₂ := T.Ct * T.energyRatio)
      g.radius_pos hx0 (Real.exp_pos _).le
      g.Ct_nonneg (mul_nonneg g.Ct_nonneg hE₃) c3 hν0 hν1 hsm hsm' hrm hrm' (hX e φ hbm hcm).1
      (hX e φ hbm hcm).2 hd4
      (mem_cellsNearCell_self hs.finite hr))
  exact main.trans (freezing_sum_le g.lam_pos g.S_nonneg g.κ_pos r)
theorem abs_ballExpectation_headDifference_le (hsz : AdmissibleMomentBoundsHold)
    (hmc : CutoffExpectationIsPositiveForm)
    (g : PositivityData T S x) (hs : TorusData T S x f F V star) {Ψ : StepVariable (finiteCells F) → ℝ}
    (gΨ : IsAdmissiblePotential T.ballRadius (x * T.chainParams.lam / 4) T.κ
      (fun b b' => blockDist F (bondBlock F b) (bondBlock F b')) Ψ) (Y : F.Cell) :
    |ballExpectation (cutoffFactor T.ballRadius T.p) Ψ
        (headDifference star T.a T.chainParams.ρA x T.chainParams.lam (frameRadius x) V Y)| ≤
      interpolatedConstant T * (32 * S ^ 2 / T.chainParams.lam + 1) := by
  have hf := hs.finite
  letI iF : Fintype F.Cell := Fintype.ofFinite _
  have hx0 : 0 < x := by linarith [g.one_le_x]
  have hlam := g.lam_pos
  have hm0 : 0 < x * T.chainParams.lam / 4 := by positivity
  have Sz := hsz ↥(chordBonds (finiteCells F)) F.Cell T.ballRadius (x * T.chainParams.lam / 4) T.κ S T.p
    (bondBlock F) (blockDist F) Ψ g.radius_pos hm0 g.κ_pos g.cutoff (isPseudoMetricOnBonds_cellDistance F) gΨ
    (fun z => (hs.weight_sums_le z).1)
  have F₁ := hmc _ T.ballRadius T.p Ψ g.radius_pos g.cutoff (continuous_of_isAdmissiblePotential gΨ)
  have hc0 : 0 ≤ interpolatedConstant T := by
    unfold interpolatedConstant
    linarith [g.Ct_nonneg]
  have hH := isLocalTermAt_headDifference g hs Y
  obtain ⟨M, hM0, hM⟩ := exists_bondGradNorm_bound_of_localTerm g.radius_pos g.κ_pos.le hc0 hx0.le
    (isPseudoMetricOnBonds_cellDistance F) hH
  have nH := isBoundedContinuousOn_of_bondGradNorm_le g.radius_pos (contDiffOn_one_of_two hH.smooth) hM0 hM
  have hq := isBoundedContinuousOn_weightedSqNormNear (r := T.κ) (pos := bondBlock F) (D := blockDist F)
    (ι := ↥(chordBonds (finiteCells F))) g.radius_pos Y
  have nM : IsBoundedContinuousOn ↥(chordBonds (finiteCells F)) T.ballRadius
      (fun η => interpolatedConstant T * (x * weightedSqNormNear T.κ (bondBlock F) (blockDist F) Y η + 1)) :=
    (IsBoundedContinuousOn.const _).mul
      (((IsBoundedContinuousOn.const _).mul hq).add (IsBoundedContinuousOn.const _))
  have hpt : ∀ η ∈ openPolyball ↥(chordBonds (finiteCells F)) T.ballRadius,
      |headDifference star T.a T.chainParams.ρA x T.chainParams.lam (frameRadius x) V Y η| ≤
        interpolatedConstant T * (x * weightedSqNormNear T.κ (bondBlock F) (blockDist F) Y η + 1) := by
    intro η hη
    have hsq := weightedSqNormNear_nonneg (r := T.κ) (pos := bondBlock F) (D := blockDist F) Y η
    have h1 := hs.exponent_bounds.deriv_top Y η 0 (fun l => l.elim0) (fun l => l.elim0) hη (by norm_num)
      (fun l => l.elim0)
    rw [bondDeriv_zero] at h1
    have h2 : |cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y V η| ≤
        T.Ct * (x * weightedSqNormNear T.κ (bondBlock F) (blockDist F) Y η + 1) := by
      refine h1.trans ?_
      have hk := localSqNorm_le_weightedSqNormNear g.κ_pos.le Y η
      have e1 : Real.exp (-(2 ^ 6 * T.κ * (bondSpan Y (fun l : Fin 0 => l.elim0) : ℝ))) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have : 0 ≤ 2 ^ 6 * T.κ * (bondSpan Y (fun l : Fin 0 => l.elim0) : ℝ) := by
          have := g.κ_pos
          positivity
        linarith
      have hCt := g.Ct_nonneg
      have h0 : 0 ≤ localSqNorm T.κ Y η := Finset.sum_nonneg fun b _ =>
        mul_nonneg (Real.exp_pos _).le (by positivity)
      calc T.Ct * (x * localSqNorm T.κ Y η + 1) *
            Real.exp (-(2 ^ 6 * T.κ * (bondSpan Y (fun l : Fin 0 => l.elim0) : ℝ)))
          ≤ T.Ct * (x * localSqNorm T.κ Y η + 1) * 1 :=
            mul_le_mul_of_nonneg_left e1 (by positivity)
        _ ≤ _ := by
            rw [mul_one]
            apply mul_le_mul_of_nonneg_left _ hCt
            have := mul_le_mul_of_nonneg_left hk hx0.le
            linarith
    have h3 : |cellQuadratic T.chainParams.lam x Y η| ≤
        T.chainParams.lam * (x * weightedSqNormNear T.κ (bondBlock F) (blockDist F) Y η) := by
      have h4 : 0 ≤ cellQuadratic T.chainParams.lam x Y η := Finset.sum_nonneg fun b _ => by
        split_ifs
        · positivity
        · exact le_rfl
      rw [abs_of_nonneg h4]
      have h5 : T.chainParams.lam * (x * weightedSqNormNear T.κ (bondBlock F) (blockDist F) Y η) =
          ∑ b, x * T.chainParams.lam * (Real.exp (-(2 ^ 5 * T.κ *
            blockDist F (bondBlock F b) Y)) * ‖η b‖ ^ 2) := by
        unfold weightedSqNormNear
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      rw [h5]
      unfold cellQuadratic
      refine Finset.sum_le_sum fun b _ => ?_
      by_cases hb : enclosingCell b.1.1 = Y
      · have hd : blockDist F (bondBlock F b) Y = 0 := by
          simp only [bondBlock, hb]
          exact (isPseudoMetricOnBonds_cellDistance F).self Y
        simp only [hb, if_true, hd, mul_zero, neg_zero, Real.exp_zero, one_mul]
        have : 0 ≤ x * T.chainParams.lam * ‖η b‖ ^ 2 := by positivity
        linarith
      · simp only [hb, if_false]
        positivity
    unfold headDifference
    rw [show interpolatedConstant T * (x * weightedSqNormNear T.κ (bondBlock F) (blockDist F) Y η + 1) =
      (T.Ct + T.chainParams.lam + 1) * (x * weightedSqNormNear T.κ (bondBlock F) (blockDist F) Y η + 1) from rfl]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_one, abs_neg, abs_one, one_mul, one_mul]
    have h6 : 0 ≤ x * weightedSqNormNear T.κ (bondBlock F) (blockDist F) Y η := by positivity
    nlinarith [g.lam_pos, g.Ct_nonneg]
  refine (abs_ballExpectation_le F₁ nH nM hpt).trans ?_
  rw [F₁.map_smul, F₁.map_add _ _ ((IsBoundedContinuousOn.const _).mul hq) (IsBoundedContinuousOn.const _),
    F₁.map_smul, F₁.map_one]
  apply mul_le_mul_of_nonneg_left _ hc0
  have h7 := mul_le_mul_of_nonneg_left (Sz.near_moment_le Y) hx0.le
  have e2 : x * (8 * S ^ 2 / (x * T.chainParams.lam / 4)) = 32 * S ^ 2 / T.chainParams.lam := by
    field_simp
    ring
  rw [e2] at h7
  linarith
end
end StepFreezing
open StepFreezing LocalCalculus in
theorem stepFreezingStatement_proof (hfz : BallExpectationFreezingBound)
    (hbox : NearBlocksCorrespondByOffset) (hb : SiteDecomposition)
    (hgood : AdmissiblePotentialStability) (hsz : AdmissibleMomentBoundsHold)
    (hmc : CutoffExpectationIsPositiveForm) : stepFreezingStatement := by
  intro T S hT hnss hn0 hCt hy hlam hW hCs hCE hBd hRd hCv hX hTr t x f F F' V V' Y Y' r star hxy hrow
    htop htop' hcold hcold' hag
  have hx : 1 ≤ x := hy.trans hxy
  have hκ := hT.κ_pos
  have hσ := hT.σ_pos
  have hρ : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  have hE := hT.one_le_E
  have hη₀ := hT.η₃_pos
  have hE₃ : T.E ≤ T.energyRatio := by
    unfold StepParameters.energyRatio
    rw [le_div_iff₀ hη₀]
    nlinarith [hT.η₃_le_one]
  have hLo := hT.odd_L
  have hL1 : 1 ≤ (T.L : ℝ) ^ 4 := by
    have : 1 ≤ T.L := hLo.pos
    have h1 : (1 : ℝ) ≤ T.L := by exact_mod_cast this
    exact one_le_pow₀ h1
  obtain ⟨hLF, htF, n, hn, hnn⟩ := id htop
  obtain ⟨hLF', htF', n', hn', hnn'⟩ := id htop'
  have hn2 : 2 ≤ n := hn0.trans hnn
  have hn2' : 2 ≤ n' := hn0.trans hnn'
  have hWF := hW F n hLF hn2 hn
  have hWF' := hW F' n' hLF' hn2' hn'
  have hS : 0 ≤ S := (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le).trans (hWF Y).1
  have g : PositivityData T S x := ⟨hρ, hκ, hx, hlam, hCt, hE, hE₃, hL1, hS, hT.cutoff⟩
  have sizeOf : ∀ {G : BlockFrame} (W : G.GaugeField G.top), IsCubicTopTorus T.L t T.n₀ G →
      IsSmallCurvature (5 / 4 * T.σ) W → ∀ (Z : G.Cell) (η : StepVariable (finiteCells G)),
      (∀ b, ‖η b‖ < T.ballRadius) →
        |cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Z η W| ≤ T.E := by
    intro G W hG hWc Z η hη
    have h1 := ((hTr t x f G W hxy hrow hG hWc star).1).abs_le Z η hη
    refine h1.trans ?_
    have hw : 1 ≤ torusDecayFactor T.L T.decayRate (T.blockIndex : ℝ) := by
      unfold torusDecayFactor
      have a1 : (1 : ℝ) ≤ max 1 (((T.blockIndex : ℝ) / (T.L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) :=
        le_max_left _ _
      have a2 : (1 : ℝ) ≤ Real.exp (T.decayRate * T.blockIndex) := by
        apply Real.one_le_exp
        unfold StepParameters.decayRate
        positivity
      nlinarith
    have h2 : (2⁻¹ : ℝ) ^ 8 * T.E ≤ T.E := by
      have : (2⁻¹ : ℝ) ^ 8 ≤ 1 := by norm_num
      nlinarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have sideOf : ∀ {G : BlockFrame} (W : G.GaugeField G.top) (m : ℕ), G.blockSide = T.L →
      (∀ i, G.extent i = m) → 2 ≤ m →
      IsCubicTopTorus T.L t T.n₀ G → IsSmallCurvature (5 / 4 * T.σ) W →
      (∀ z : G.Cell, ∑ b : ↥(chordBonds (finiteCells G)),
        Real.exp (-(T.κ / 4 * blockDist G (bondBlock G b) z)) ≤ S ∧
        ∑ z' ∈ finiteCells G, Real.exp (-(T.κ / 4 * blockDist G z' z)) ≤ S) →
      TorusData T S x f G W star := by
    intro G W m hGL hGm hm2 hG hWc hWG
    refine ⟨finite_cell fun i => ?_, by rw [hGL]; exact hLo, fun i => ?_, hGL, hWG,
      (hBd t x G W star hxy hG hWc).1, hRd t x f G W star hxy hrow hG hWc,
      fun ν h0 h1 => hCv t x f G W star ν hxy hrow hG hWc h0 h1, fun Z η hη => sizeOf W hG hWc Z η hη⟩
    · rw [hGm]
      omega
    · rw [hGm]
      exact hm2
  have hs := sideOf V n hLF hn hn2 htop hcold hWF
  have hs' := sideOf V' n' hLF' hn' hn2' htop' hcold' hWF'
  have htt : F.depth = F'.depth := htF.trans htF'.symm
  obtain ⟨fN, cN⟩ := freezing_constants_nonneg hlam hS
  have fl1 : ∀ c : ℝ, 0 ≤ freezingThreshold T.chainParams.lam S c := fun c => by
    unfold freezingThreshold
    positivity
  intro v hv0 hv1
  have hS1 : freezingThreshold T.chainParams.lam S (interpolatedConstant T) ≤ T.Cs := by
    refine le_trans ?_ hCs
    unfold exponentConstantThreshold
    have : 0 ≤ 2 * (T.Ct + T.chainParams.lam + 1) * (32 * S ^ 2 / T.chainParams.lam + 1) *
        Real.exp (T.κ * T.blockIndex / 2 ^ 7) := by positivity
    have e : freezingThreshold T.chainParams.lam S (T.Ct + T.chainParams.lam + 1) =
        freezingThreshold T.chainParams.lam S (interpolatedConstant T) := rfl
    linarith
  have hS2 : freezingThreshold T.chainParams.lam S (expansionPerturbedConstant T) ≤ T.CE := by
    refine le_trans ?_ hCE
    unfold expansionConstantThreshold
    have : 0 ≤ 2 * T.E * Real.exp (T.κ * T.blockIndex / 2 ^ 7) := by positivity
    have e : freezingThreshold T.chainParams.lam S ((T.Ct + 1) * (1 + T.energyRatio * (T.L : ℝ) ^ 4)) =
        freezingThreshold T.chainParams.lam S (expansionPerturbedConstant T) := rfl
    linarith
  have hcS : 2 * (interpolatedConstant T * (32 * S ^ 2 / T.chainParams.lam + 1)) *
      Real.exp (T.κ * T.blockIndex / 2 ^ 7) ≤ T.Cs := by
    refine le_trans ?_ hCs
    unfold exponentConstantThreshold
    have e : 2 * (interpolatedConstant T * (32 * S ^ 2 / T.chainParams.lam + 1)) *
        Real.exp (T.κ * T.blockIndex / 2 ^ 7) =
        2 * (T.Ct + T.chainParams.lam + 1) * (32 * S ^ 2 / T.chainParams.lam + 1) *
          Real.exp (T.κ * T.blockIndex / 2 ^ 7) := by
      unfold interpolatedConstant
      ring
    have := fl1 (T.Ct + T.chainParams.lam + 1)
    linarith
  have hcF : 2 * T.E * Real.exp (T.κ * T.blockIndex / 2 ^ 7) ≤ T.CE := by
    refine le_trans ?_ hCE
    unfold expansionConstantThreshold
    have := fl1 ((T.Ct + 1) * (1 + T.energyRatio * (T.L : ℝ) ^ 4))
    linarith
  by_cases hr : T.blockIndex ≤ r
  · have hr1 : 1 ≤ r := hnss.trans hr
    have h1 : ∀ i, 2 * r + 2 < F.extent i := fun i => by
      rcases hag.1 i with h | h
      · have := hn i
        omega
      · exact h
    have h2 : ∀ i, 2 * r + 2 < F'.extent i := fun i => by
      rcases hag.2.1 i with h | h
      · have := hn' i
        omega
      · exact h
    have hXe := fun e φ hbm hcm => hX t x f F F' V V' Y Y' r e φ hxy hrow htop htop' hcold hcold' hag hr
      hbm hcm star
    refine ⟨?_, ?_⟩
    · refine (interpolated_freezing_large_radius hfz hbox hgood hmc g hs hs' htt h1 h2 hr1
        (fun e φ hbm hcm => (hXe e φ hbm hcm).1) hv0 hv1).trans ?_
      have e : T.κ * r / 2 ^ 7 = T.κ * (r : ℝ) / 2 ^ 7 := rfl
      exact mul_le_mul_of_nonneg_right hS1 (Real.exp_pos _).le
    · refine (expansionPerturbed_freezing_large_radius hfz hbox hmc hb g hs hs' htt h1 h2 hr1 hXe hv0 hv1).trans ?_
      exact mul_le_mul_of_nonneg_right hS2 (Real.exp_pos _).le
  · push Not at hr
    have hrr : (r : ℝ) ≤ T.blockIndex := by exact_mod_cast hr.le
    refine ⟨?_, ?_⟩
    · obtain ⟨Ψ, gΨ, eΨ, -⟩ := exists_interpolated_potential hgood hρ hκ hx hlam hs.finite hs.exponent_bounds
        (hs.convex 0 le_rfl zero_le_one) hv0 hv1
      obtain ⟨Ψ', gΨ', eΨ', -⟩ := exists_interpolated_potential hgood hρ hκ hx hlam hs'.finite
        hs'.exponent_bounds (hs'.convex 0 le_rfl zero_le_one) hv0 hv1
      have F₁ := hmc _ T.ballRadius T.p Ψ hρ hT.cutoff (continuous_of_isAdmissiblePotential gΨ)
      have F₂ := hmc _ T.ballRadius T.p Ψ' hρ hT.cutoff (continuous_of_isAdmissiblePotential gΨ')
      have m1 := F₁.congr_potential _
        (headDifference star T.a T.chainParams.ρA x T.chainParams.lam (frameRadius x) V Y) eΨ
      have m2 := F₂.congr_potential _
        (headDifference star T.a T.chainParams.ρA x T.chainParams.lam (frameRadius x) V' Y') eΨ'
      have eH : (fun η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y V η -
          cellQuadratic T.chainParams.lam x Y η) =
          headDifference star T.a T.chainParams.ρA x T.chainParams.lam (frameRadius x) V Y := by
        funext η
        simp only [headDifference]
        ring
      have eH' : (fun η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y' V' η -
          cellQuadratic T.chainParams.lam x Y' η) =
          headDifference star T.a T.chainParams.ρA x T.chainParams.lam (frameRadius x) V' Y' := by
        funext η
        simp only [headDifference]
        ring
      rw [eH, eH', cutoffMean_eq_ballExpectation, cutoffMean_eq_ballExpectation, ← m1, ← m2]
      have hB0 : 0 ≤ interpolatedConstant T * (32 * S ^ 2 / T.chainParams.lam + 1) := by
        unfold interpolatedConstant
        positivity
      exact abs_sub_le_of_small_radius hκ hrr (abs_ballExpectation_headDifference_le hsz hmc g hs gΨ Y)
        (abs_ballExpectation_headDifference_le hsz hmc g hs' gΨ' Y') hB0 hcS
    · obtain ⟨Ψ, gΨ, eΨ, -⟩ := exists_expansionPerturbed_potential hs.finite hs.exponent_bounds (hs.convex v hv0 hv1)
      obtain ⟨Ψ', gΨ', eΨ', -⟩ :=
        exists_expansionPerturbed_potential hs'.finite hs'.exponent_bounds (hs'.convex v hv0 hv1)
      have F₁ := hmc _ T.ballRadius T.p Ψ hρ hT.cutoff (continuous_of_isAdmissiblePotential gΨ)
      have F₂ := hmc _ T.ballRadius T.p Ψ' hρ hT.cutoff (continuous_of_isAdmissiblePotential gΨ')
      have m1 := F₁.congr_potential _
        (fun η => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y η V) eΨ
      have m2 := F₂.congr_potential _
        (fun η => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y' η V') eΨ'
      rw [cutoffMean_eq_ballExpectation, cutoffMean_eq_ballExpectation, ← m1, ← m2]
      have hx0 : 0 ≤ x := by linarith
      have hd : ∀ {G : BlockFrame} (W : G.GaugeField G.top) (Z : G.Cell), TorusData T S x f G W star →
          IsBoundedContinuousOn ↥(chordBonds (finiteCells G)) T.ballRadius
            (fun ζ => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Z ζ W) := by
        intro G W Z hG
        have hfin := hG.finite
        letI iG : Fintype G.Cell := Fintype.ofFinite _
        have hT1 := isLocalTermAt_cellCentredExpansion_of g hb hG Z
        have hc0 : 0 ≤ T.Ct * T.E * (T.L : ℝ) ^ 4 := by positivity
        obtain ⟨M, hM0, hM⟩ :=
          exists_bondGradNorm_bound_of_localTerm hρ hκ.le hc0 hx0 (isPseudoMetricOnBonds_cellDistance G) hT1
        exact isBoundedContinuousOn_of_bondGradNorm_le hρ (contDiffOn_one_of_two hT1.smooth) hM0 hM
      exact abs_sub_le_of_small_radius hκ hrr
        (F₁.abs_le (hd V Y hs) fun η hη => hs.expansion_abs_le Y η hη)
        (F₂.abs_le (hd V' Y' hs') fun η hη => hs'.expansion_abs_le Y' η hη) (by linarith) hcF
end YangMills.Construction.ColdStepAtMirrorFrames
end
