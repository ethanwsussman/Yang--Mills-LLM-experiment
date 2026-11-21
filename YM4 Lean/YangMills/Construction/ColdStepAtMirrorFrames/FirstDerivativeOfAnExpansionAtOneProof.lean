import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import YangMills.Construction.ColdStepAtMirrorFrames.FirstDerivativeOfAnExpansionAtOne
import YangMills.Construction.ColdStepAtMirrorFrames.JetOfAFunctionOfAField
import YangMills.Construction.SummableBoundsOfTheFlow.LinesOfTwoTopsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open BlockAverages Filter Topology
variable {F : BlockFrame}
private theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : Quaternion ℝ)‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
private theorem re_expUnit (w : imaginaryQuaternions) :
    ((expUnit w : UnitQuaternion) : Quaternion ℝ).re = Real.cos ‖w‖ := by
  have hre : (w : Quaternion ℝ).re = 0 := w.2
  show (NormedSpace.exp (w : Quaternion ℝ)).re = _
  rw [Quaternion.exp_of_re_eq_zero _ hre]
  first
    | (simp [hre]; done)
    | (simp [hre]; rfl)
abbrev _root_.YangMills.SharedProofs.p42298 := @re_expUnit
private theorem norm_expUnit_sub_one_le (w : imaginaryQuaternions) :
    ‖((expUnit w : UnitQuaternion) : Quaternion ℝ) - 1‖ ≤ ‖w‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le <;> assumption
abbrev _root_.YangMills.SharedProofs.p28543 := @norm_expUnit_sub_one_le
private theorem plaquetteDefect_close {j : ℕ} {Y Y' : F.GaugeField j} {d : ℝ}
    (h : ∀ x i, ‖((Y x i : UnitQuaternion) : Quaternion ℝ) - (Y' x i : UnitQuaternion)‖ ≤ d)
    (hd : 0 ≤ d) (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteDefect Y p ≤ plaquetteDefect Y' p + 4 * d := by apply _root_.YangMills.Construction.DerivativeInterpolation.HolonomyPerturbation.plaquetteDefect_le_add <;> assumption
private def conjBy (Z q : imaginaryQuaternions) : imaginaryQuaternions :=
  ⟨(Z : Quaternion ℝ) * (q : Quaternion ℝ) * star (Z : Quaternion ℝ), by
    have hq : (q : Quaternion ℝ).re = 0 := q.2
    have hZ : (Z : Quaternion ℝ).re = 0 := Z.2
    show ((Z : Quaternion ℝ) * (q : Quaternion ℝ) * star (Z : Quaternion ℝ)).re = 0
    simp [hq, hZ]
    ring⟩
private theorem star_mul_self_and_mul_star_of_norm_one (Z : imaginaryQuaternions) (hZ : ‖Z‖ = 1) :
    star (Z : Quaternion ℝ) * (Z : Quaternion ℝ) = 1 ∧
      (Z : Quaternion ℝ) * star (Z : Quaternion ℝ) = 1 := by
  have hZ' : ‖(Z : Quaternion ℝ)‖ = 1 := hZ
  have hN1 : Quaternion.normSq (Z : Quaternion ℝ) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hZ']; norm_num
  exact ⟨by rw [Quaternion.star_mul_self, hN1]; simp, by rw [Quaternion.self_mul_star, hN1]; simp⟩
private theorem expUnit_conjBy (Z : imaginaryQuaternions) (hZ : ‖Z‖ = 1) (q : imaginaryQuaternions) :
    ((expUnit (conjBy Z q) : UnitQuaternion) : Quaternion ℝ) =
      (Z : Quaternion ℝ) * ((expUnit q : UnitQuaternion) : Quaternion ℝ) * star (Z : Quaternion ℝ) := by
  obtain ⟨_, hZs⟩ := star_mul_self_and_mul_star_of_norm_one Z hZ
  have hZ' : ‖(Z : Quaternion ℝ)‖ = 1 := hZ
  have hq : (q : Quaternion ℝ).re = 0 := q.2
  have hc : ((conjBy Z q : imaginaryQuaternions) : Quaternion ℝ).re = 0 := (conjBy Z q).2
  have hn : ‖((conjBy Z q : imaginaryQuaternions) : Quaternion ℝ)‖ = ‖(q : Quaternion ℝ)‖ := by
    show ‖(Z : Quaternion ℝ) * (q : Quaternion ℝ) * star (Z : Quaternion ℝ)‖ = _
    rw [norm_mul, norm_mul, Quaternion.norm_star, hZ']
    simp
  show NormedSpace.exp ((conjBy Z q : imaginaryQuaternions) : Quaternion ℝ) =
    (Z : Quaternion ℝ) * NormedSpace.exp (q : Quaternion ℝ) * _
  rw [Quaternion.exp_of_re_eq_zero _ hq, Quaternion.exp_of_re_eq_zero _ hc, hn]
  have hcoe : ((conjBy Z q : imaginaryQuaternions) : Quaternion ℝ) =
      (Z : Quaternion ℝ) * (q : Quaternion ℝ) * star (Z : Quaternion ℝ) := rfl
  rw [hcoe, mul_add, add_mul]
  congr 1
  · rw [Quaternion.mul_coe_eq_smul, smul_mul_assoc, hZs, ← Quaternion.coe_mul_eq_smul, mul_one]
  · rw [mul_smul_comm, smul_mul_assoc]
private theorem conjBy_smul (Z : imaginaryQuaternions) (τ : ℝ) (q : imaginaryQuaternions) :
    conjBy Z (τ • q) = τ • conjBy Z q := by
  apply Subtype.ext
  show (Z : Quaternion ℝ) * (τ • (q : Quaternion ℝ)) * star (Z : Quaternion ℝ) = τ • _
  rw [mul_smul_comm, smul_mul_assoc]
  rfl
theorem firstDerivAtTrivialVanishes_of_formCompositionJet (hjet : FormCompositionJet) :
    FirstDerivAtTrivialVanishes := by
  classical
  intro L t n₀ σ δ E E₃ f F hrow hσ hlow y c X
  set G := f F y with hG
  set W := uniformField F F.depth with hW
  have hflat : IsSmallCurvature σ W := by
    intro p _
    have : plaquetteHolonomy W p = 1 := by
      simp [plaquetteHolonomy, pathHolonomy, linkValue, hW, uniformField]
    unfold plaquetteDefect
    rw [this]
    simpa using hσ
  have hs := hrow.smooth F hlow y W hflat
  set b := c 0 with hb
  set B : Finset (F.Site F.depth × Fin 4) := {b} with hB
  have hbm : b ∈ B := Finset.mem_singleton_self b
  set u : ↥B := ⟨b, hbm⟩ with hu
  obtain ⟨hcd, hent, _⟩ := hjet ℝ F F.depth B G W hs
  set H := formComposition B G W with hH
  have hfd : HasFDerivAt H (fderiv ℝ H 0) 0 := (hcd.differentiableAt (by norm_num)).hasFDerivAt
  set ℓ := fderiv ℝ H 0 with hℓ
  have hline : ∀ A : ↥B → imaginaryQuaternions, HasDerivAt (fun τ : ℝ => H (τ • A)) (ℓ A) 0 := by
    intro A
    have h1 : HasDerivAt (fun τ : ℝ => τ • A) A 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const A
    have hfd' : HasFDerivAt H ℓ ((0 : ℝ) • A) := by simpa using hfd
    exact hfd'.comp_hasDerivAt (0 : ℝ) h1
  have hfield : ∀ (τ : ℝ) (Y : imaginaryQuaternions), ∀ x i,
      ‖((leftTranslate (extendByZero (τ • singleBondForm u Y)) W x i : UnitQuaternion) : Quaternion ℝ) -
        ((W x i : UnitQuaternion) : Quaternion ℝ)‖ ≤ |τ| * ‖Y‖ := by
    intro τ Y x i
    have hW1 : W x i = 1 := rfl
    show ‖((expUnit (extendByZero (τ • singleBondForm u Y) x i) * W x i : UnitQuaternion) :
      Quaternion ℝ) - _‖ ≤ _
    rw [hW1, mul_one]
    have h2 : ‖extendByZero (τ • singleBondForm u Y) x i‖ ≤ |τ| * ‖Y‖ := by
      unfold extendByZero
      split_ifs with hm
      · rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
        unfold singleBondForm
        by_cases hbb : (⟨(x, i), hm⟩ : ↥B) = u
        · rw [hbb]
          simp
        · rw [Pi.single_eq_of_ne hbb]
          simp
          positivity
      · simp
        positivity
    have h3 : ((1 : UnitQuaternion) : Quaternion ℝ) = 1 := rfl
    rw [h3]
    exact (norm_expUnit_sub_one_le _).trans h2
  have hsmallτ : ∀ Y : imaginaryQuaternions, ∀ᶠ τ : ℝ in 𝓝 0,
      IsSmallCurvature σ (leftTranslate (extendByZero (τ • singleBondForm u Y)) W) := by
    intro Y
    have hc : Tendsto (fun τ : ℝ => 4 * (|τ| * ‖Y‖)) (𝓝 0) (𝓝 (4 * (|0| * ‖Y‖))) :=
      ((continuous_abs.tendsto 0).mul_const _).const_mul _
    simp only [abs_zero, zero_mul, mul_zero] at hc
    filter_upwards [hc.eventually (gt_mem_nhds hσ)] with τ hτ
    intro p hp
    have h1 := plaquetteDefect_close (hfield τ Y) (by positivity) p
    have h2 : plaquetteDefect W p < σ := hflat p hp
    have h3 : plaquetteDefect W p = 0 := by
      have : plaquetteHolonomy W p = 1 := by
        simp [plaquetteHolonomy, pathHolonomy, linkValue, hW, uniformField]
      unfold plaquetteDefect
      rw [this]
      simp
    rw [h3] at h1
    linarith
  have hconj : ∀ (Z : imaginaryQuaternions), ‖Z‖ = 1 → ∀ Y : imaginaryQuaternions,
      ℓ (singleBondForm u (conjBy Z Y)) = ℓ (singleBondForm u Y) := by
    intro Z hZ Y
    obtain ⟨hZ1, hZ2⟩ := star_mul_self_and_mul_star_of_norm_one Z hZ
    let g : UnitQuaternion := ⟨(Z : Quaternion ℝ), Unitary.mem_iff.2 ⟨hZ1, hZ2⟩⟩
    have hsame : ∀ᶠ τ : ℝ in 𝓝 0,
        H (τ • singleBondForm u (conjBy Z Y)) = H (τ • singleBondForm u Y) := by
      filter_upwards [hsmallτ Y] with τ hτ
      show G (leftTranslate (extendByZero (τ • singleBondForm u (conjBy Z Y))) W) =
        G (leftTranslate (extendByZero (τ • singleBondForm u Y)) W)
      have hf : leftTranslate (extendByZero (τ • singleBondForm u (conjBy Z Y))) W =
          gaugeTransform (fun _ => g) (leftTranslate (extendByZero (τ • singleBondForm u Y)) W) := by
        funext x i
        apply Subtype.ext
        show ((expUnit (extendByZero (τ • singleBondForm u (conjBy Z Y)) x i) * 1 : UnitQuaternion) :
            Quaternion ℝ) =
          (Z : Quaternion ℝ) *
            ((expUnit (extendByZero (τ • singleBondForm u Y) x i) * 1 : UnitQuaternion) : Quaternion ℝ) *
              star (Z : Quaternion ℝ)
        rw [mul_one, mul_one]
        have hval : extendByZero (τ • singleBondForm u (conjBy Z Y)) x i =
            conjBy Z (extendByZero (τ • singleBondForm u Y) x i) := by
          unfold extendByZero
          split_ifs with hm
          · rw [Pi.smul_apply, Pi.smul_apply]
            unfold singleBondForm
            by_cases hbb : (⟨(x, i), hm⟩ : ↥B) = u
            · rw [hbb, Pi.single_eq_same, Pi.single_eq_same, conjBy_smul]
            · rw [Pi.single_eq_of_ne hbb, Pi.single_eq_of_ne hbb, smul_zero]
              apply Subtype.ext
              show (0 : Quaternion ℝ) = (Z : Quaternion ℝ) * 0 * _
              simp
          · apply Subtype.ext
            show (0 : Quaternion ℝ) = (Z : Quaternion ℝ) * 0 * _
            simp
        rw [hval, expUnit_conjBy Z hZ]
      rw [hf]
      exact hrow.gauge_invariant F hlow y _ _ hτ
    exact ((hline _).congr_of_eventuallyEq (hsame.mono fun τ h => h.symm)).unique (hline _)
  have hneg : ∀ (Z Y : imaginaryQuaternions), ‖Z‖ = 1 → conjBy Z Y = - Y →
      ℓ (singleBondForm u Y) = 0 := by
    intro Z Y hZ hY
    have h1 := hconj Z hZ Y
    rw [hY] at h1
    have h2 : singleBondForm u (-Y) = - singleBondForm u Y := by
      unfold singleBondForm
      rw [Pi.single_neg]
    rw [h2, map_neg] at h1
    linarith
  obtain ⟨I, hI0, hI1, hI2, hI3⟩ : ∃ q : Quaternion ℝ, q.re = 0 ∧ q.imI = 1 ∧ q.imJ = 0 ∧ q.imK = 0 :=
    ⟨⟨0, 1, 0, 0⟩, rfl, rfl, rfl, rfl⟩
  obtain ⟨J, hJ0, hJ1, hJ2, hJ3⟩ : ∃ q : Quaternion ℝ, q.re = 0 ∧ q.imI = 0 ∧ q.imJ = 1 ∧ q.imK = 0 :=
    ⟨⟨0, 0, 1, 0⟩, rfl, rfl, rfl, rfl⟩
  obtain ⟨K, hK0, hK1, hK2, hK3⟩ : ∃ q : Quaternion ℝ, q.re = 0 ∧ q.imI = 0 ∧ q.imJ = 0 ∧ q.imK = 1 :=
    ⟨⟨0, 0, 0, 1⟩, rfl, rfl, rfl, rfl⟩
  have hnorm : ∀ q : Quaternion ℝ, Quaternion.normSq q = 1 → ‖q‖ = 1 := by
    intro q hq
    have h5 := Quaternion.normSq_eq_norm_mul_self q
    rw [hq] at h5
    nlinarith [norm_nonneg q]
  have hIu : ‖(⟨I, hI0⟩ : imaginaryQuaternions)‖ = 1 :=
    hnorm I (by rw [Quaternion.normSq_def', hI0, hI1, hI2, hI3]; norm_num)
  have hJu : ‖(⟨J, hJ0⟩ : imaginaryQuaternions)‖ = 1 :=
    hnorm J (by rw [Quaternion.normSq_def', hJ0, hJ1, hJ2, hJ3]; norm_num)
  have lI : ℓ (singleBondForm u ⟨I, hI0⟩) = 0 := by
    apply hneg ⟨J, hJ0⟩ _ hJu
    apply Subtype.ext
    show J * I * star J = - I
    ext <;> simp [hI0, hI1, hI2, hI3, hJ0, hJ1, hJ2, hJ3]
  have lJ : ℓ (singleBondForm u ⟨J, hJ0⟩) = 0 := by
    apply hneg ⟨I, hI0⟩ _ hIu
    apply Subtype.ext
    show I * J * star I = - J
    ext <;> simp [hI0, hI1, hI2, hI3, hJ0, hJ1, hJ2, hJ3]
  have lK : ℓ (singleBondForm u ⟨K, hK0⟩) = 0 := by
    apply hneg ⟨I, hI0⟩ _ hIu
    apply Subtype.ext
    show I * K * star I = - K
    ext <;> simp [hI0, hI1, hI2, hI3, hK0, hK1, hK2, hK3]
  have hY : ∀ Y : imaginaryQuaternions, ℓ (singleBondForm u Y) = 0 := by
    intro Y
    have hd : Y = (Y : Quaternion ℝ).imI • (⟨I, hI0⟩ : imaginaryQuaternions) +
        (Y : Quaternion ℝ).imJ • (⟨J, hJ0⟩ : imaginaryQuaternions) +
        (Y : Quaternion ℝ).imK • (⟨K, hK0⟩ : imaginaryQuaternions) := by
      apply Subtype.ext
      have hy : (Y : Quaternion ℝ).re = 0 := Y.2
      show (Y : Quaternion ℝ) =
        (Y : Quaternion ℝ).imI • I + (Y : Quaternion ℝ).imJ • J + (Y : Quaternion ℝ).imK • K
      ext <;> simp [hy, hI0, hI1, hI2, hI3, hJ0, hJ1, hJ2, hJ3, hK0, hK1, hK2, hK3]
    have hform : ∀ (r s v : ℝ) (A A' A'' : imaginaryQuaternions),
        singleBondForm u (r • A + s • A' + v • A'') =
          r • singleBondForm u A + s • singleBondForm u A' + v • singleBondForm u A'' := by
      intro r s v A A' A''
      unfold singleBondForm
      rw [Pi.single_add, Pi.single_add, Pi.single_smul, Pi.single_smul, Pi.single_smul]
    rw [hd, hform, map_add, map_add, map_smul, map_smul, map_smul, lI, lJ, lK]
    simp
  have e1 := hent 1 (fun _ => u) X (by norm_num)
  have hc1 : (fun l : Fin 1 => ((fun _ => u : Fin 1 → ↥B) l).1) = c := by
    funext l
    have : l = 0 := Subsingleton.elim _ _
    rw [this]
  rw [hc1] at e1
  rw [← e1, iteratedFDeriv_one_apply]
  show fderiv ℝ H 0 _ = 0
  have : singleBondForm u (X 0) = singleBondForm u (X 0) := rfl
  simpa using hY (X 0)
end YangMills.Construction.ColdStepAtMirrorFrames
end
