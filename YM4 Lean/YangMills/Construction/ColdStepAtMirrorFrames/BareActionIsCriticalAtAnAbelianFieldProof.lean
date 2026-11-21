import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import YangMills.Construction.ColdStepAtMirrorFrames.JetOfAFunctionOfAField
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
import YangMills.Construction.ColdStepAtMirrorFrames.ComponentsOfAFieldAlongAnElement
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionIsGaugeInvariant
set_option autoImplicit false

noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def IsAbelianWithFlux {j : ℕ} (X : imaginaryQuaternions) (g : ℝ) (μ ν : Fin 4) (W : F.GaugeField j) : Prop :=
  (∃ β : F.Site j → Fin 4 → ℝ, ∀ x i, W x i = expUnit (β x i • X)) ∧
    ∀ (x : F.Site j) (α α' : Fin 4), α < α' →
      plaquetteHolonomy W (x, α, α') = expUnit ((if α = μ ∧ α' = ν then g else 0) • X)
def BareActionCriticalAtAbelianField : Prop :=
  ∀ (F : BlockFrame) (X : imaginaryQuaternions) (g : ℝ) (μ ν : Fin 4), Odd F.blockSide →
    (∀ i, 0 < F.extent i) → ‖X‖ = 1 → μ < ν →
    ∀ W : F.GaugeField 0, IsAbelianWithFlux X g μ ν W →
      ContDiffThreeAlongBonds (wilsonAction (finiteCells F)) W ∧
      HasFDerivAt (formComposition (innerBonds (finiteCells F) 0) (wilsonAction (finiteCells F)) W)
        (0 : (↥(innerBonds (finiteCells F) 0) → imaginaryQuaternions) →L[ℝ] ℝ) 0
end ColdStepAtMirrorFrames
end YangMills.Construction
end

noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
private theorem coe_smul_imag (s : ℝ) (X : imaginaryQuaternions) :
    ((s • X : imaginaryQuaternions) : Quaternion ℝ) = s • (X : Quaternion ℝ) := rfl
private theorem expUnit_add_smul (X : imaginaryQuaternions) (s t : ℝ) :
    expUnit ((s + t) • X) = expUnit (s • X) * expUnit (t • X) := by
  let +nondep : NormedAlgebra ℚ (Quaternion ℝ) := .restrictScalars ℚ ℝ _
  apply Subtype.ext
  show NormedSpace.exp (((s + t) • X : imaginaryQuaternions) : Quaternion ℝ) =
    NormedSpace.exp ((s • X : imaginaryQuaternions) : Quaternion ℝ) *
      NormedSpace.exp ((t • X : imaginaryQuaternions) : Quaternion ℝ)
  rw [coe_smul_imag, coe_smul_imag, coe_smul_imag, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left s).smul_right t)
abbrev _root_.YangMills.SharedProofs.p2328 := @expUnit_add_smul
private theorem expUnit_zero_smul (X : imaginaryQuaternions) : expUnit ((0 : ℝ) • X) = 1 := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.expUnit_zero_smul <;> assumption
private theorem expUnit_smul_inv (X : imaginaryQuaternions) (s : ℝ) :
    (expUnit (s • X))⁻¹ = expUnit ((-s) • X) := by
  have h : expUnit (s • X) * expUnit ((-s) • X) = 1 := by
    rw [← expUnit_add_smul, add_neg_cancel, expUnit_zero_smul]
  exact inv_eq_of_mul_eq_one_right h
abbrev _root_.YangMills.SharedProofs.p4359 := @expUnit_smul_inv
private theorem exp_smul_of_norm_one (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (s : ℝ) :
    NormedSpace.exp (s • (X : Quaternion ℝ)) =
      ((Real.cos s : ℝ) : Quaternion ℝ) + Real.sin s • (X : Quaternion ℝ) := by
  have hX' : ‖(X : Quaternion ℝ)‖ = 1 := hX
  have hre : (s • (X : Quaternion ℝ)).re = 0 := by
    have : (X : Quaternion ℝ).re = 0 := X.2
    simp [this]
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  have hn : ‖s • (X : Quaternion ℝ)‖ = |s| := by rw [norm_smul, hX']; simp
  rw [Quaternion.exp_of_re_eq_zero _ hre, hn, Real.cos_abs]
  congr 1
  rw [smul_smul]
  congr 1
  rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; field_simp
  · rw [h, Real.sin_neg]; field_simp
private theorem re_expUnit_smul (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (s : ℝ) :
    ((expUnit (s • X) : UnitQuaternion) : Quaternion ℝ).re = Real.cos s := by
  show (NormedSpace.exp (s • (X : Quaternion ℝ))).re = _
  rw [exp_smul_of_norm_one X hX]
  have : (X : Quaternion ℝ).re = 0 := X.2
  simp [this]
private theorem coe_inv_unitQuaternion (g : UnitQuaternion) :
    ((g⁻¹ : UnitQuaternion) : Quaternion ℝ) = star (g : Quaternion ℝ) := by
  rw [← Unitary.star_eq_inv, Unitary.coe_star]
private theorem contDiff_exp_quaternion :
    ContDiff ℝ ⊤ (NormedSpace.exp : Quaternion ℝ → Quaternion ℝ) := by
  have : AnalyticOnNhd ℝ (NormedSpace.exp : Quaternion ℝ → Quaternion ℝ) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  exact this.contDiff
abbrev _root_.YangMills.SharedProofs.p23558 := @contDiff_exp_quaternion
private def realPartL : Quaternion ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => q.re, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }
private def conjugateL : Quaternion ℝ →L[ℝ] Quaternion ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := star, map_add' := star_add, map_smul' := fun c q => by ext <;> simp }
section Smooth
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
private theorem contDiff_leftTranslate_link {j : ℕ} {v : P → F.Site j → Fin 4 → imaginaryQuaternions}
    (hv : ∀ x i, ContDiff ℝ ⊤ fun τ => ((v τ x i : imaginaryQuaternions) : Quaternion ℝ))
    (W : F.GaugeField j) (x : F.Site j) (i : Fin 4) :
    ContDiff ℝ ⊤ fun τ => ((leftTranslate (v τ) W x i : UnitQuaternion) : Quaternion ℝ) :=
  (contDiff_exp_quaternion.comp (hv x i)).mul contDiff_const
private theorem contDiff_pathHolonomy_leftTranslate {j : ℕ}
    {v : P → F.Site j → Fin 4 → imaginaryQuaternions}
    (hv : ∀ x i, ContDiff ℝ ⊤ fun τ => ((v τ x i : imaginaryQuaternions) : Quaternion ℝ))
    (W : F.GaugeField j) :
    ∀ (p : List PathStep) (x : F.Site j),
      ContDiff ℝ ⊤ fun τ => ((pathHolonomy (leftTranslate (v τ) W) x p : UnitQuaternion) : Quaternion ℝ)
  | [], _ => contDiff_const
  | st :: r, x => by
    have h2 := contDiff_pathHolonomy_leftTranslate hv W r (x + stepDisplacement j st)
    have h1 : ContDiff ℝ ⊤ fun τ =>
        ((linkValue (leftTranslate (v τ) W) x st : UnitQuaternion) : Quaternion ℝ) := by
      unfold linkValue
      by_cases hb : st.2 = true
      · simp only [hb, if_true]
        exact contDiff_leftTranslate_link hv W x st.1
      · simp only [hb, Bool.false_eq_true, if_false, coe_inv_unitQuaternion]
        exact conjugateL.contDiff.comp (contDiff_leftTranslate_link hv W _ st.1)
    exact h1.mul h2
private theorem contDiff_wilsonAction_leftTranslate {v : P → F.Site 0 → Fin 4 → imaginaryQuaternions}
    (hv : ∀ x i, ContDiff ℝ ⊤ fun τ => ((v τ x i : imaginaryQuaternions) : Quaternion ℝ))
    (S : Finset F.Cell) (W : F.GaugeField 0) :
    ContDiff ℝ ⊤ fun τ => wilsonAction S (leftTranslate (v τ) W) := by
  unfold wilsonAction
  apply ContDiff.sum
  intro p _
  show ContDiff ℝ ⊤ fun τ => 1 - realPartL ((pathHolonomy (leftTranslate (v τ) W) p.1
    [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : Quaternion ℝ)
  exact contDiff_const.sub (realPartL.contDiff.comp (contDiff_pathHolonomy_leftTranslate hv W _ p.1))
end Smooth
private def plaquetteAngle {j : ℕ} (b : F.Site j → Fin 4 → ℝ) (p : F.Site j × Fin 4 × Fin 4) : ℝ :=
  b p.1 p.2.1 + b (p.1 + unitStep j p.2.1) p.2.2 -
    b (p.1 + unitStep j p.2.1 + unitStep j p.2.2 - unitStep j p.2.1) p.2.1 -
    b (p.1 + unitStep j p.2.1 + unitStep j p.2.2 + - unitStep j p.2.1 - unitStep j p.2.2) p.2.2
private theorem plaquetteHolonomy_of_angles {j : ℕ} (X : imaginaryQuaternions)
    (b : F.Site j → Fin 4 → ℝ) (Y : F.GaugeField j)
    (hY : ∀ x i, Y x i = expUnit (b x i • X)) (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteHolonomy Y p = expUnit (plaquetteAngle b p • X) := by
  obtain ⟨x, α, α'⟩ := p
  unfold plaquetteHolonomy plaquetteAngle
  simp only [pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false, hY,
    expUnit_smul_inv, mul_one]
  rw [← expUnit_add_smul, ← expUnit_add_smul, ← expUnit_add_smul]
  congr 2
  ring
theorem bareActionCriticalAtAbelianField (hgauge : MinimalActionGaugeInvariant) :
    BareActionCriticalAtAbelianField := by
  classical
  intro F X g μ ν hodd hs hX hμν W hW
  have hLpos : 0 < F.blockSide := hodd.pos
  set S : Finset F.Cell := finiteCells F with hS
  set B : Finset (F.Site 0 × Fin 4) := innerBonds S 0 with hBdef
  have hT : ∀ x : F.Site 0, x ∈ sitesOfCells S 0 :=
    fun x => _root_.YangMills.Construction.ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs (Nat.zero_le _) x
  have hB : ∀ b : F.Site 0 × Fin 4, b ∈ B := by
    intro b
    rw [hBdef]
    unfold innerBonds
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hT _, Finset.mem_univ _⟩, hT _⟩
  have hP : ∀ p : F.Site 0 × Fin 4 × Fin 4, p ∈ innerPlaquettes S 0 ↔ p.2.1 < p.2.2 := by
    intro p
    unfold innerPlaquettes
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    constructor
    · exact fun h => h.2.1
    · intro h
      exact ⟨⟨hT _, Finset.mem_univ _, Finset.mem_univ _⟩, h, fun x _ => hT x⟩
  have hsm : ContDiffThreeAlongBonds (wilsonAction S) W := by
    intro k c X'
    have hv : ∀ x i, ContDiff ℝ ⊤ fun τ : Fin k → ℝ =>
        ((bondSpread c X' τ x i : imaginaryQuaternions) : Quaternion ℝ) := by
      intro x i
      have he : (fun τ : Fin k → ℝ => ((bondSpread c X' τ x i : imaginaryQuaternions) : Quaternion ℝ)) =
          fun τ => ∑ l, (if c l = (x, i) then τ l • (X' l : Quaternion ℝ) else 0) := by
        funext τ
        unfold bondSpread
        rw [AddSubmonoidClass.coe_finset_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs <;> simp
      rw [he]
      apply ContDiff.sum
      intro l _
      split_ifs
      · exact (contDiff_apply ℝ ℝ l).smul contDiff_const
      · exact contDiff_const
    exact ((contDiff_wilsonAction_leftTranslate hv S W).of_le le_top).contDiffAt
  refine ⟨hsm, ?_⟩
  set H := formComposition B (wilsonAction S) W with hHdef
  have hHeq : ∀ A, H A = wilsonAction S (leftTranslate (extendByZero A) W) := fun A => rfl
  have hHs : ContDiff ℝ ⊤ H := by
    have hv : ∀ x i, ContDiff ℝ ⊤ fun A : ↥B → imaginaryQuaternions =>
        ((extendByZero A x i : imaginaryQuaternions) : Quaternion ℝ) := by
      intro x i
      have he : (fun A : ↥B → imaginaryQuaternions =>
          ((extendByZero A x i : imaginaryQuaternions) : Quaternion ℝ)) =
          fun A => ((A ⟨(x, i), hB _⟩ : imaginaryQuaternions) : Quaternion ℝ) := by
        funext A
        unfold extendByZero
        rw [dif_pos (hB (x, i))]
      rw [he]
      exact imaginaryQuaternions.subtypeL.contDiff.comp (contDiff_apply ℝ imaginaryQuaternions _)
    exact contDiff_wilsonAction_leftTranslate hv S W
  have hfd : HasFDerivAt H (fderiv ℝ H 0) 0 :=
    ((hHs.differentiable (by simp)) 0).hasFDerivAt
  suffices hz : fderiv ℝ H 0 = 0 by rw [← hz]; exact hfd
  set ℓ := fderiv ℝ H 0 with hℓ
  have hline : ∀ A : ↥B → imaginaryQuaternions, HasDerivAt (fun τ : ℝ => H (τ • A)) (ℓ A) 0 := by
    intro A
    have h1 : HasDerivAt (fun τ : ℝ => τ • A) A 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const A
    have hfd' : HasFDerivAt H ℓ ((0 : ℝ) • A) := by simpa using hfd
    exact hfd'.comp_hasDerivAt (0 : ℝ) h1
  have hXre : (X : Quaternion ℝ).re = 0 := X.2
  have hXn : ‖(X : Quaternion ℝ)‖ = 1 := hX
  have hN1 : Quaternion.normSq (X : Quaternion ℝ) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hXn]; norm_num
  have hN : (X : Quaternion ℝ).imI ^ 2 + (X : Quaternion ℝ).imJ ^ 2 + (X : Quaternion ℝ).imK ^ 2 = 1 := by
    have h1 := hN1
    rw [Quaternion.normSq_def'] at h1
    rw [hXre] at h1
    nlinarith
  have hstarX : star (X : Quaternion ℝ) * (X : Quaternion ℝ) = 1 := by
    rw [Quaternion.star_mul_self, hN1]; simp
  have hXstar : (X : Quaternion ℝ) * star (X : Quaternion ℝ) = 1 := by
    rw [Quaternion.self_mul_star, hN1]; simp
  let uX : UnitQuaternion := ⟨(X : Quaternion ℝ), Unitary.mem_iff.2 ⟨hstarX, hXstar⟩⟩
  have hcre : ∀ q : imaginaryQuaternions,
      ((X : Quaternion ℝ) * (q : Quaternion ℝ) * star (X : Quaternion ℝ)).re = 0 := by
    intro q
    have hq : (q : Quaternion ℝ).re = 0 := q.2
    simp [hXre, hq]
    ring
  let c : imaginaryQuaternions → imaginaryQuaternions :=
    fun q => ⟨(X : Quaternion ℝ) * (q : Quaternion ℝ) * star (X : Quaternion ℝ), hcre q⟩
  let a : imaginaryQuaternions → ℝ := fun q => - ((q : Quaternion ℝ) * (X : Quaternion ℝ)).re
  have hform : ∀ q : imaginaryQuaternions, ((c q : imaginaryQuaternions) : Quaternion ℝ) =
      (2 * a q) • (X : Quaternion ℝ) - (q : Quaternion ℝ) := by
    intro q
    have hq : (q : Quaternion ℝ).re = 0 := q.2
    show (X : Quaternion ℝ) * (q : Quaternion ℝ) * star (X : Quaternion ℝ) = _
    simp only [a]
    ext
    · simp [hXre, hq]; ring
    · simp [hXre, hq]; linear_combination (- (q : Quaternion ℝ).imI) * hN
    · simp [hXre, hq]; linear_combination (- (q : Quaternion ℝ).imJ) * hN
    · simp [hXre, hq]; linear_combination (- (q : Quaternion ℝ).imK) * hN
  have hnc : ∀ q : imaginaryQuaternions, ‖c q‖ = ‖q‖ := by
    intro q
    show ‖(X : Quaternion ℝ) * (q : Quaternion ℝ) * star (X : Quaternion ℝ)‖ = ‖(q : Quaternion ℝ)‖
    rw [norm_mul, norm_mul, Quaternion.norm_star, hXn]
    simp
  have hexpc : ∀ q : imaginaryQuaternions, expUnit (c q) = uX * expUnit q * uX⁻¹ := by
    intro q
    apply Subtype.ext
    have hq : (q : Quaternion ℝ).re = 0 := q.2
    have hcq : ((c q : imaginaryQuaternions) : Quaternion ℝ).re = 0 := (c q).2
    show NormedSpace.exp ((c q : imaginaryQuaternions) : Quaternion ℝ) =
      (X : Quaternion ℝ) * NormedSpace.exp (q : Quaternion ℝ) * ((uX⁻¹ : UnitQuaternion) : Quaternion ℝ)
    rw [coe_inv_unitQuaternion, Quaternion.exp_of_re_eq_zero _ hq, Quaternion.exp_of_re_eq_zero _ hcq]
    have hn' : ‖((c q : imaginaryQuaternions) : Quaternion ℝ)‖ = ‖(q : Quaternion ℝ)‖ := hnc q
    rw [hn']
    show _ = (X : Quaternion ℝ) * _ * star (X : Quaternion ℝ)
    have hcoe : ((c q : imaginaryQuaternions) : Quaternion ℝ) =
        (X : Quaternion ℝ) * (q : Quaternion ℝ) * star (X : Quaternion ℝ) := rfl
    rw [hcoe, mul_add, add_mul]
    congr 1
    · rw [Quaternion.mul_coe_eq_smul, smul_mul_assoc, hXstar]
      rw [← Quaternion.coe_mul_eq_smul, mul_one]
    · rw [mul_smul_comm, smul_mul_assoc]
  have hcW : ∀ x i, uX * W x i * uX⁻¹ = W x i := by
    obtain ⟨⟨β, hβ⟩, _⟩ := hW
    intro x i
    rw [hβ, ← hexpc]
    congr 1
    apply Subtype.ext
    rw [hform]
    have h1 : a (β x i • X) = β x i := by
      show - (((β x i • X : imaginaryQuaternions) : Quaternion ℝ) * (X : Quaternion ℝ)).re = _
      rw [coe_smul_imag, smul_mul_assoc]
      have h2 : ((X : Quaternion ℝ) * (X : Quaternion ℝ)).re = -1 := by
        simp [hXre]
        nlinarith
      simp [h2]
    rw [h1, coe_smul_imag]
    rw [mul_smul]
    module
  have hturn : ∀ A : ↥B → imaginaryQuaternions, H (fun b => c (A b)) = H A := by
    intro A
    rw [hHeq, hHeq]
    have hfield : leftTranslate (extendByZero fun b => c (A b)) W =
        gaugeTransform (fun _ => uX) (leftTranslate (extendByZero A) W) := by
      funext x i
      unfold gaugeTransform leftTranslate extendByZero
      rw [dif_pos (hB (x, i)), dif_pos (hB (x, i)), hexpc]
      calc uX * expUnit (A ⟨(x, i), hB _⟩) * uX⁻¹ * W x i
          = uX * expUnit (A ⟨(x, i), hB _⟩) * uX⁻¹ * (uX * W x i * uX⁻¹) := by rw [hcW]
        _ = uX * (expUnit (A ⟨(x, i), hB _⟩) * W x i) * uX⁻¹ := by group
    rw [hfield]
    exact hgauge F 0 S 0 (Nat.zero_le _) hLpos _ _
  have hperp : ∀ A : ↥B → imaginaryQuaternions, (∀ b, c (A b) = - A b) → ℓ A = 0 := by
    intro A hA
    have hsame : (fun τ : ℝ => H (τ • A)) = fun τ => H (τ • (-A)) := by
      funext τ
      rw [← hturn (τ • A)]
      congr 1
      funext b
      apply Subtype.ext
      have h1 : ((c ((τ • A) b) : imaginaryQuaternions) : Quaternion ℝ) =
          τ • ((c (A b) : imaginaryQuaternions) : Quaternion ℝ) := by
        show (X : Quaternion ℝ) * ((τ • (A b) : imaginaryQuaternions) : Quaternion ℝ) *
          star (X : Quaternion ℝ) = τ • _
        rw [coe_smul_imag, mul_smul_comm, smul_mul_assoc]
      rw [h1, hA b]
      simp
    have h1 := hline A
    rw [hsame] at h1
    have h2 := h1.unique (hline (-A))
    rw [map_neg] at h2
    linarith
  obtain ⟨⟨β, hβ⟩, hpl⟩ := hW
  have hab : ∀ e : ↥B → ℝ, ℓ (fun b => e b • X) = 0 := by
    intro e
    let e' : F.Site 0 → Fin 4 → ℝ := fun x i => e ⟨(x, i), hB _⟩
    let θ : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun p => if p.2.1 = μ ∧ p.2.2 = ν then g else 0
    have hfield : ∀ τ : ℝ, ∀ x i, leftTranslate (extendByZero (τ • fun b => e b • X)) W x i =
        expUnit ((τ * e' x i + β x i) • X) := by
      intro τ x i
      unfold leftTranslate extendByZero
      rw [dif_pos (hB (x, i)), hβ, expUnit_add_smul X (τ * e' x i) (β x i)]
      congr 2
      show τ • e ⟨(x, i), hB _⟩ • X = _
      rw [smul_smul]
    have hsum : ∀ τ : ℝ, H (τ • fun b => e b • X) =
        ∑ p ∈ innerPlaquettes S 0, (1 - Real.cos (θ p + τ * plaquetteAngle e' p)) := by
      intro τ
      rw [hHeq]
      unfold wilsonAction
      refine Finset.sum_congr rfl fun p hp => ?_
      have h1 := plaquetteHolonomy_of_angles X (fun x i => τ * e' x i + β x i) _ (hfield τ) p
      have h2 := plaquetteHolonomy_of_angles X β W hβ p
      obtain ⟨x, α, α'⟩ := p
      have hlt : α < α' := (hP _).1 hp
      rw [hpl x α α' hlt] at h2
      have h3 : plaquetteAngle (fun x i => τ * e' x i + β x i) (x, α, α') =
          τ * plaquetteAngle e' (x, α, α') + plaquetteAngle β (x, α, α') := by
        unfold plaquetteAngle
        dsimp only
        ring
      rw [h1, h3, expUnit_add_smul X, ← h2, ← expUnit_add_smul, re_expUnit_smul X hX]
      congr 2
      simp only [θ]
      ring
    have hder : HasDerivAt (fun τ : ℝ => H (τ • fun b => e b • X))
        (∑ p ∈ innerPlaquettes S 0, Real.sin (θ p) * plaquetteAngle e' p) 0 := by
      have he : (fun τ : ℝ => H (τ • fun b => e b • X)) = fun τ =>
          ∑ p ∈ innerPlaquettes S 0, (1 - Real.cos (θ p + τ * plaquetteAngle e' p)) := funext hsum
      rw [he]
      apply HasDerivAt.fun_sum
      intro p _
      have h1 : HasDerivAt (fun τ : ℝ => θ p + τ * plaquetteAngle e' p) (plaquetteAngle e' p) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (plaquetteAngle e' p)).const_add (θ p)
      have h2 := (Real.hasDerivAt_cos (θ p + 0 * plaquetteAngle e' p)).comp (0 : ℝ) h1
      have h3 := h2.const_sub 1
      simpa using h3
    have hzero : ∑ p ∈ innerPlaquettes S 0, Real.sin (θ p) * plaquetteAngle e' p = 0 := by
      have hstep : ∑ p ∈ innerPlaquettes S 0, Real.sin (θ p) * plaquetteAngle e' p =
          ∑ p ∈ (sitesOfCells S 0).image (fun x => ((x, μ, ν) : F.Site 0 × Fin 4 × Fin 4)),
            Real.sin g * plaquetteAngle e' p := by
        symm
        apply Finset.sum_subset_zero_on_sdiff
        · intro p hp
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hp
          exact (hP _).2 hμν
        · intro p hp
          have hp1 := Finset.mem_sdiff.1 hp
          have hnot : ¬ (p.2.1 = μ ∧ p.2.2 = ν) := by
            rintro ⟨h1, h2⟩
            apply hp1.2
            refine Finset.mem_image.2 ⟨p.1, hT _, ?_⟩
            rw [← h1, ← h2]
          simp [θ, hnot]
        · intro p hp
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hp
          simp [θ]
      rw [hstep, Finset.sum_image (by intro x _ y _ h; exact (Prod.ext_iff.1 h).1), ← Finset.mul_sum]
      have hshift : ∀ (u : F.Site 0) (i : Fin 4),
          ∑ x ∈ sitesOfCells S 0, e' (x + u) i = ∑ x ∈ sitesOfCells S 0, e' x i := by
        intro u i
        apply Finset.sum_nbij' (fun x => x + u) (fun x => x - u)
        · intro x _; exact hT _
        · intro x _; exact hT _
        · intro x _; simp
        · intro x _; simp
        · intro x _; rfl
      have hd : ∑ x ∈ sitesOfCells S 0, plaquetteAngle e' (x, μ, ν) = 0 := by
        unfold plaquetteAngle
        dsimp only
        have e1 : ∀ x : F.Site 0, x + unitStep 0 μ + unitStep 0 ν - unitStep 0 μ = x + unitStep 0 ν := by
          intro x; abel
        have e2 : ∀ x : F.Site 0,
            x + unitStep 0 μ + unitStep 0 ν + - unitStep 0 μ - unitStep 0 ν = x := by
          intro x; abel
        simp only [e1, e2, Finset.sum_sub_distrib, Finset.sum_add_distrib, hshift]
        ring
      rw [hd, mul_zero]
    rw [hzero] at hder
    exact (hline _).unique hder
  ext A
  show ℓ A = 0
  let e : ↥B → ℝ := fun b => a (A b)
  have hsplit : A = (fun b => e b • X) + (fun b => A b - e b • X) := by
    funext b
    simp
  rw [hsplit, map_add, hab e, zero_add]
  apply hperp
  intro b
  apply Subtype.ext
  rw [hform]
  have h0 : a (A b - e b • X) = 0 := by
    show - ((((A b - e b • X : imaginaryQuaternions)) : Quaternion ℝ) * (X : Quaternion ℝ)).re = 0
    have h2 : ((X : Quaternion ℝ) * (X : Quaternion ℝ)).re = -1 := by
      simp [hXre]
      nlinarith
    have h3 : (((A b - e b • X : imaginaryQuaternions)) : Quaternion ℝ) =
        (A b : Quaternion ℝ) - e b • (X : Quaternion ℝ) := rfl
    rw [h3, sub_mul, smul_mul_assoc]
    simp only [e, a]
    simp [h2]
  rw [h0]
  simp
end YangMills.Construction.ColdStepAtMirrorFrames
end
