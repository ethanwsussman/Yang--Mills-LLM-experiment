import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ColdStepAtMirrorFrames.SmallUnitsAndTheirLogarithms
import YangMills.Construction.LawByMomentsOfTheFlow.AxialGaugeAlongPaths
import YangMills.Construction.ResponseInTheExpansion.AxialGaugeOnABox
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open ColdStepAtMirrorFrames.BlockOffsets ColdStepAtMirrorFrames.SmallUnits
namespace MomentLaw
namespace AxialGaugePaths
section UnitGroup
private theorem norm_coe_unit (g : BlockAverages.UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
private theorem norm_prod_four_sub_one_sub_sum_le (g₁ g₂ g₃ g₄ : BlockAverages.UnitQuaternion) :
    ‖((g₁ * g₂ * g₃ * g₄ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 - (((g₁ : ℍ[ℝ]) - 1) + ((g₂ : ℍ[ℝ]) - 1) + ((g₃ : ℍ[ℝ]) - 1) + ((g₄ : ℍ[ℝ]) - 1))‖ ≤
      (distFromOne g₁ + distFromOne g₂ + distFromOne g₃ + distFromOne g₄) ^ 2 := by
  have e : ((g₁ * g₂ * g₃ * g₄ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 - (((g₁ : ℍ[ℝ]) - 1) + ((g₂ : ℍ[ℝ]) - 1) + ((g₃ : ℍ[ℝ]) - 1) + ((g₄ : ℍ[ℝ]) - 1)) =
      ((g₁ : ℍ[ℝ]) - 1) * ((g₂ : ℍ[ℝ]) - 1) + (((g₁ * g₂ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1) * ((g₃ : ℍ[ℝ]) - 1) +
        (((g₁ * g₂ * g₃ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1) * ((g₄ : ℍ[ℝ]) - 1) := by
    have c1 : ((g₁ * g₂ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = (g₁ : ℍ[ℝ]) * g₂ := rfl
    have c2 : ((g₁ * g₂ * g₃ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = (g₁ : ℍ[ℝ]) * g₂ * g₃ := rfl
    have c3 : ((g₁ * g₂ * g₃ * g₄ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = (g₁ : ℍ[ℝ]) * g₂ * g₃ * g₄ := rfl
    rw [c1, c2, c3]
    noncomm_ring
  rw [e]
  have h1 : ‖((g₁ : ℍ[ℝ]) - 1) * ((g₂ : ℍ[ℝ]) - 1)‖ ≤ distFromOne g₁ * distFromOne g₂ := by
    rw [norm_mul]; rfl
  have h2 : ‖(((g₁ * g₂ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1) * ((g₃ : ℍ[ℝ]) - 1)‖ ≤ (distFromOne g₁ + distFromOne g₂) * distFromOne g₃ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (distFromOne_mul g₁ g₂) (distFromOne_nonneg _)
  have h3 : ‖(((g₁ * g₂ * g₃ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1) * ((g₄ : ℍ[ℝ]) - 1)‖ ≤ (distFromOne g₁ + distFromOne g₂ + distFromOne g₃) * distFromOne g₄ := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (distFromOne_nonneg _)
    have a := distFromOne_mul (g₁ * g₂) g₃
    have b := distFromOne_mul g₁ g₂
    exact a.trans (by linarith)
  have p1 := distFromOne_nonneg g₁
  have p2 := distFromOne_nonneg g₂
  have p3 := distFromOne_nonneg g₃
  have p4 := distFromOne_nonneg g₄
  refine (norm_add_le _ _).trans ?_
  have := norm_add_le (((g₁ : ℍ[ℝ]) - 1) * ((g₂ : ℍ[ℝ]) - 1)) ((((g₁ * g₂ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1) * ((g₃ : ℍ[ℝ]) - 1))
  nlinarith [mul_nonneg p1 p2, mul_nonneg p1 p3, mul_nonneg p1 p4, mul_nonneg p2 p3, mul_nonneg p2 p4, mul_nonneg p3 p4,
    sq_nonneg (distFromOne g₁), sq_nonneg (distFromOne g₂), sq_nonneg (distFromOne g₃), sq_nonneg (distFromOne g₄)]
private theorem norm_expUnit_inv_sub_one_add_le (y : BlockAverages.imaginaryQuaternions) (hy : ‖y‖ ≤ 1) :
    ‖(((BlockAverages.expUnit y)⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 + (y : ℍ[ℝ])‖ ≤ 2 * ‖y‖ ^ 2 := by
  set E : BlockAverages.UnitQuaternion := BlockAverages.expUnit y with hE
  have h1 : ((E⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * (E : ℍ[ℝ]) = 1 := by
    have : ((E⁻¹ * E : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = 1 := by rw [inv_mul_cancel]; rfl
    exact this
  have e : ((E⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 + (y : ℍ[ℝ]) =
      -(((E⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * ((E : ℍ[ℝ]) - 1 - (y : ℍ[ℝ]))) - (((E⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1) * (y : ℍ[ℝ]) := by
    have : ((E⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * ((E : ℍ[ℝ]) - 1 - (y : ℍ[ℝ])) =
        1 - ((E⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - ((E⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * (y : ℍ[ℝ]) := by
      rw [mul_sub, mul_sub, h1, mul_one]
    rw [this]
    noncomm_ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg, norm_mul, norm_mul, norm_coe_unit E⁻¹, one_mul]
  have a := norm_expUnit_sub_one_sub_le y hy
  have b : ‖((E⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖y‖ := by
    have := distFromOne_expUnit_le y
    rw [← distFromOne_inv] at this
    exact this
  have c : ‖(y : ℍ[ℝ])‖ = ‖y‖ := rfl
  rw [c]
  nlinarith [norm_nonneg y, mul_le_mul_of_nonneg_right b (norm_nonneg y)]
private theorem norm_prod_four_expUnit_sub_one_sub_le (y₁ y₂ y₃ y₄ : BlockAverages.imaginaryQuaternions) (h : ‖y₁‖ + ‖y₂‖ + ‖y₃‖ + ‖y₄‖ ≤ 1) :
    ‖((BlockAverages.expUnit y₁ * BlockAverages.expUnit y₂ * (BlockAverages.expUnit y₃)⁻¹ * (BlockAverages.expUnit y₄)⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 - ((y₁ + y₂ - y₃ - y₄ : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      3 * (‖y₁‖ + ‖y₂‖ + ‖y₃‖ + ‖y₄‖) ^ 2 := by
  have p1 := norm_nonneg y₁
  have p2 := norm_nonneg y₂
  have p3 := norm_nonneg y₃
  have p4 := norm_nonneg y₄
  have a := norm_prod_four_sub_one_sub_sum_le (BlockAverages.expUnit y₁) (BlockAverages.expUnit y₂) (BlockAverages.expUnit y₃)⁻¹ (BlockAverages.expUnit y₄)⁻¹
  have g1 := distFromOne_expUnit_le y₁
  have g2 := distFromOne_expUnit_le y₂
  have g3 : distFromOne (BlockAverages.expUnit y₃)⁻¹ ≤ ‖y₃‖ := by rw [distFromOne_inv]; exact distFromOne_expUnit_le y₃
  have g4 : distFromOne (BlockAverages.expUnit y₄)⁻¹ ≤ ‖y₄‖ := by rw [distFromOne_inv]; exact distFromOne_expUnit_le y₄
  have b1 := norm_expUnit_sub_one_sub_le y₁ (by linarith)
  have b2 := norm_expUnit_sub_one_sub_le y₂ (by linarith)
  have b3 := norm_expUnit_inv_sub_one_add_le y₃ (by linarith)
  have b4 := norm_expUnit_inv_sub_one_add_le y₄ (by linarith)
  set S := ‖y₁‖ + ‖y₂‖ + ‖y₃‖ + ‖y₄‖ with hS
  have hsum : (distFromOne (BlockAverages.expUnit y₁) + distFromOne (BlockAverages.expUnit y₂) + distFromOne (BlockAverages.expUnit y₃)⁻¹ + distFromOne (BlockAverages.expUnit y₄)⁻¹) ^ 2 ≤ S ^ 2 := by
    have n1 := distFromOne_nonneg (BlockAverages.expUnit y₁)
    have n2 := distFromOne_nonneg (BlockAverages.expUnit y₂)
    have n3 := distFromOne_nonneg (BlockAverages.expUnit y₃)⁻¹
    have n4 := distFromOne_nonneg (BlockAverages.expUnit y₄)⁻¹
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  set r₁ : ℍ[ℝ] := ((BlockAverages.expUnit y₁ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 with hr₁
  set r₂ : ℍ[ℝ] := ((BlockAverages.expUnit y₂ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 with hr₂
  set r₃ : ℍ[ℝ] := (((BlockAverages.expUnit y₃)⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 with hr₃
  set r₄ : ℍ[ℝ] := (((BlockAverages.expUnit y₄)⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 with hr₄
  set P : ℍ[ℝ] := ((BlockAverages.expUnit y₁ * BlockAverages.expUnit y₂ * (BlockAverages.expUnit y₃)⁻¹ * (BlockAverages.expUnit y₄)⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) with hP
  have e : P - 1 - ((y₁ + y₂ - y₃ - y₄ : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) =
      (P - 1 - (r₁ + r₂ + r₃ + r₄)) + (r₁ - (y₁ : ℍ[ℝ])) + (r₂ - (y₂ : ℍ[ℝ])) + (r₃ + (y₃ : ℍ[ℝ])) + (r₄ + (y₄ : ℍ[ℝ])) := by
    push_cast
    abel
  rw [e]
  have hs : ‖y₁‖ ^ 2 + ‖y₂‖ ^ 2 + 2 * ‖y₃‖ ^ 2 + 2 * ‖y₄‖ ^ 2 ≤ 2 * S ^ 2 := by
    rw [hS]
    nlinarith [mul_nonneg p1 p2, mul_nonneg p1 p3, mul_nonneg p1 p4, mul_nonneg p2 p3, mul_nonneg p2 p4, mul_nonneg p3 p4]
  calc _ ≤ ‖P - 1 - (r₁ + r₂ + r₃ + r₄)‖ + ‖r₁ - (y₁ : ℍ[ℝ])‖ + ‖r₂ - (y₂ : ℍ[ℝ])‖ + ‖r₃ + (y₃ : ℍ[ℝ])‖ + ‖r₄ + (y₄ : ℍ[ℝ])‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 3 * S ^ 2 := by linarith
private theorem norm_conj_sub_le (g q : BlockAverages.UnitQuaternion) :
    ‖((g * q * g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - (q : ℍ[ℝ])‖ ≤ 2 * distFromOne g * distFromOne q := by
  have h1 : ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by
    have : ((g⁻¹ * g : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = 1 := by rw [inv_mul_cancel]; rfl
    exact this
  have h2 : (g : ℍ[ℝ]) * ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = 1 := by
    have : ((g * g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = 1 := by rw [mul_inv_cancel]; rfl
    exact this
  have e : ((g * q * g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - (q : ℍ[ℝ]) =
      ((g : ℍ[ℝ]) - 1) * ((q : ℍ[ℝ]) - 1) * ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) + ((q : ℍ[ℝ]) - 1) * (((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1) := by
    have c : ((g * q * g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = (g : ℍ[ℝ]) * q * ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) := rfl
    rw [c]
    have : ((g : ℍ[ℝ]) - 1) * ((q : ℍ[ℝ]) - 1) * ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) =
        (g : ℍ[ℝ]) * q * ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 - (q : ℍ[ℝ]) * ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) + ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) := by
      have : ((g : ℍ[ℝ]) - 1) * ((q : ℍ[ℝ]) - 1) * ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) =
          (g : ℍ[ℝ]) * q * ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - (g : ℍ[ℝ]) * ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - (q : ℍ[ℝ]) * ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) + ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) := by
        noncomm_ring
      rw [this, h2]
    rw [this]
    noncomm_ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_coe_unit g⁻¹, mul_one]
  have hgi : ‖((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ = distFromOne g := distFromOne_inv g
  rw [hgi]
  have : ‖(g : ℍ[ℝ]) - 1‖ = distFromOne g := rfl
  rw [this]
  have : ‖(q : ℍ[ℝ]) - 1‖ = distFromOne q := rfl
  rw [this]
  linarith
private theorem norm_minimalLog_le_pi (u : BlockAverages.UnitQuaternion) : ‖LumpContours.minimalLog u‖ ≤ Real.pi := by
  set w := LumpContours.minimalLog u with hw
  have hexp : BlockAverages.expUnit w = u := TopLevelSites.expUnit_minimalLog u
  have hleast : ∀ w' : BlockAverages.imaginaryQuaternions, BlockAverages.expUnit w' = u → ‖(w : ℍ[ℝ])‖ ≤ ‖(w' : ℍ[ℝ])‖ := by
    intro w' h'
    rw [hw]
    unfold LumpContours.minimalLog
    rw [dif_pos (TopLevelSites.exists_minimal_log u)]
    exact (TopLevelSites.exists_minimal_log u).choose_spec.2 w' h'
  by_contra hgt
  rw [not_le] at hgt
  have hpi := Real.pi_pos
  set s : ℝ := ‖(w : ℍ[ℝ])‖ with hs
  have hgt' : Real.pi < s := hgt
  have hs0 : 0 < s := hpi.trans hgt'
  set w' : BlockAverages.imaginaryQuaternions := ((s - 2 * Real.pi) / s) • w with hw'
  have hn' : ‖(w' : ℍ[ℝ])‖ = |s - 2 * Real.pi| := by
    have : (w' : ℍ[ℝ]) = ((s - 2 * Real.pi) / s) • (w : ℍ[ℝ]) := rfl
    rw [this, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hs0, div_mul_eq_mul_div, ← hs]
    field_simp
  have hlt : ‖(w' : ℍ[ℝ])‖ < s := by
    rw [hn', abs_lt]
    constructor <;> linarith
  have hE : BlockAverages.expUnit w' = u := by
    rw [← hexp]
    apply Subtype.ext
    show NormedSpace.exp (w' : ℍ[ℝ]) = NormedSpace.exp (w : ℍ[ℝ])
    rw [TopLevelSites.exp_imaginary, TopLevelSites.exp_imaginary, hn', ← hs]
    have hw'c : (w' : ℍ[ℝ]) = ((s - 2 * Real.pi) / s) • (w : ℍ[ℝ]) := rfl
    rw [hw'c, smul_smul]
    have hc : Real.cos |s - 2 * Real.pi| = Real.cos s := by
      rw [Real.cos_abs, Real.cos_sub_two_pi]
    have hcoef : Real.sin |s - 2 * Real.pi| / |s - 2 * Real.pi| * ((s - 2 * Real.pi) / s) = Real.sin s / s := by
      rcases eq_or_ne s (2 * Real.pi) with h0 | h0
      · rw [h0]
        simp
      · have hne : s - 2 * Real.pi ≠ 0 := sub_ne_zero.2 h0
        have e1 : Real.sin |s - 2 * Real.pi| / |s - 2 * Real.pi| = Real.sin (s - 2 * Real.pi) / (s - 2 * Real.pi) := by
          rcases abs_cases (s - 2 * Real.pi) with ⟨h1, -⟩ | ⟨h1, -⟩
          · rw [h1]
          · rw [h1, Real.sin_neg]
            field_simp
        rw [e1, Real.sin_sub_two_pi]
        field_simp
    rw [hc, hcoef]
  exact absurd (hleast w' hE) (not_le.2 hlt)
end UnitGroup
section LatticePaths
variable {ℓ : TorusLumps.StepParameters} {N : ℕ} [NeZero N]
private theorem axialGaugeAt_eq_pathHolonomy (W : TorusFields.TorusField N) (o z : TorusFields.TorusSite N) :
    ResponseInTheExpansion.axialGaugeAt ℓ W o z = BlockAverages.pathHolonomy (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top W)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top o) (BlockAverages.axisPath (MomentLaw.minimalOffset o z) 1) := by
  have hn : ∀ i, (TorusLumps.stepBlockFrame ℓ.side N).extent i = N := fun _ => rfl
  have hpt := TopLevelSites.period_top_of_extent (F := TorusLumps.stepBlockFrame ℓ.side N) hn
  have e : ColdStepAtMirrorFrames.minimalOffset (F := TorusLumps.stepBlockFrame ℓ.side N) (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top o)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top z) = MomentLaw.minimalOffset o z := by
    funext i
    unfold ColdStepAtMirrorFrames.minimalOffset MomentLaw.minimalOffset
    have h : ∀ {P : ℕ} (hP : P = N) (a b : ZMod N),
        (((((a.cast : ℤ)) : ZMod P)) - ((((b.cast : ℤ)) : ZMod P))).valMinAbs = (a - b).valMinAbs := by
      intro P hP a b
      subst hP
      simp
    exact h (hpt i) (z i) (o i)
  have e0 : ResponseInTheExpansion.axialGaugeAt ℓ W o z = BlockAverages.pathHolonomy (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top W)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top o)
      (BlockAverages.axisPath (ColdStepAtMirrorFrames.minimalOffset (F := TorusLumps.stepBlockFrame ℓ.side N) (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top o)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top z)) 1) := rfl
  rw [e0, e]
private theorem siteOfCoords_add_unitStep (F : BlockAverages.BlockFrame) (u : Fin 4 → ℤ) (i : Fin 4) (Y : F.Cell) :
    Y + BlockAverages.siteOfCoords F.top u + BlockAverages.unitStep F.top i = Y + BlockAverages.siteOfCoords F.top (u + Pi.single i 1) := by
  rw [add_assoc]
  congr 1
  funext l
  simp [BlockAverages.siteOfCoords, BlockAverages.unitStep]
private theorem siteOfCoords_sub_unitStep (F : BlockAverages.BlockFrame) (u : Fin 4 → ℤ) (i : Fin 4) (Y : F.Cell) :
    Y + BlockAverages.siteOfCoords F.top u - BlockAverages.unitStep F.top i = Y + BlockAverages.siteOfCoords F.top (u - Pi.single i 1) := by
  rw [add_sub_assoc]
  congr 1
  funext l
  simp [BlockAverages.siteOfCoords, BlockAverages.unitStep]
private theorem distFromOne_pathHolonomy_le (W : TorusFields.TorusField N) (o : TorusFields.TorusSite N) :
    ∀ (l : List BlockAverages.PathStep) (u : Fin 4 → ℤ),
      distFromOne (BlockAverages.pathHolonomy (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top W)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top o + BlockAverages.siteOfCoords (TorusLumps.stepBlockFrame ℓ.side N).top u) l) ≤
        (((BlockOffsets.pathBonds u l).map fun b => (o + TorusFields.siteOfInt b.1, b.2)).map fun c => distFromOne (W c.1 c.2)).sum := by
  have hn : ∀ i, (TorusLumps.stepBlockFrame ℓ.side N).extent i = N := fun _ => rfl
  intro l
  induction l with
  | nil =>
    intro u
    simp [BlockAverages.pathHolonomy, distFromOne_one, BlockOffsets.pathBonds]
  | cons st r ih =>
    intro u
    obtain ⟨i, d⟩ := st
    cases d with
    | true =>
      simp only [BlockAverages.pathHolonomy, BlockAverages.linkValue, BlockAverages.stepDisplacement, if_true, BlockOffsets.pathBonds, List.map_cons, List.sum_cons]
      refine (distFromOne_mul _ _).trans ?_
      rw [siteOfCoords_add_unitStep, TopLevelSites.readAtLevel_torusSiteInFrame_add hn]
      have := ih (u + Pi.single i 1)
      gcongr
    | false =>
      simp only [BlockAverages.pathHolonomy, BlockAverages.linkValue, BlockAverages.stepDisplacement, Bool.false_eq_true, if_false, BlockOffsets.pathBonds, List.map_cons, List.sum_cons]
      refine (distFromOne_mul _ _).trans ?_
      rw [siteOfCoords_sub_unitStep, distFromOne_inv, TopLevelSites.readAtLevel_torusSiteInFrame_add hn, ← sub_eq_add_neg, siteOfCoords_sub_unitStep]
      have := ih (u - Pi.single i 1)
      gcongr
private theorem norm_pathHolonomy_sub_le (W W' : TorusFields.TorusField N) (o : TorusFields.TorusSite N) :
    ∀ (l : List BlockAverages.PathStep) (u : Fin 4 → ℤ),
      ‖((BlockAverages.pathHolonomy (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top W)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top o + BlockAverages.siteOfCoords (TorusLumps.stepBlockFrame ℓ.side N).top u) l : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
        (BlockAverages.pathHolonomy (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top W')
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top o + BlockAverages.siteOfCoords (TorusLumps.stepBlockFrame ℓ.side N).top u) l : BlockAverages.UnitQuaternion)‖ ≤
        (((BlockOffsets.pathBonds u l).map fun b => (o + TorusFields.siteOfInt b.1, b.2)).map
          fun c => ‖((W c.1 c.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - (W' c.1 c.2 : BlockAverages.UnitQuaternion)‖).sum := by
  have hn : ∀ i, (TorusLumps.stepBlockFrame ℓ.side N).extent i = N := fun _ => rfl
  intro l
  induction l with
  | nil =>
    intro u
    simp [BlockAverages.pathHolonomy, BlockOffsets.pathBonds]
  | cons st r ih =>
    intro u
    obtain ⟨i, d⟩ := st
    cases d with
    | true =>
      simp only [BlockAverages.pathHolonomy, BlockAverages.linkValue, BlockAverages.stepDisplacement, if_true, BlockOffsets.pathBonds, List.map_cons, List.sum_cons]
      refine (TopLevelSites.norm_mul_sub_mul_le _ _ _ _).trans ?_
      rw [siteOfCoords_add_unitStep, TopLevelSites.readAtLevel_torusSiteInFrame_add hn, TopLevelSites.readAtLevel_torusSiteInFrame_add hn]
      have := ih (u + Pi.single i 1)
      gcongr
    | false =>
      simp only [BlockAverages.pathHolonomy, BlockAverages.linkValue, BlockAverages.stepDisplacement, Bool.false_eq_true, if_false, BlockOffsets.pathBonds, List.map_cons, List.sum_cons]
      refine (TopLevelSites.norm_mul_sub_mul_le _ _ _ _).trans ?_
      rw [TopLevelSites.norm_inv_sub_inv, siteOfCoords_sub_unitStep, TopLevelSites.readAtLevel_torusSiteInFrame_add hn, TopLevelSites.readAtLevel_torusSiteInFrame_add hn, ← sub_eq_add_neg, siteOfCoords_sub_unitStep]
      have := ih (u - Pi.single i 1)
      gcongr
private theorem length_pathBonds : ∀ (l : List BlockAverages.PathStep) (u : Fin 4 → ℤ), (BlockOffsets.pathBonds u l).length = l.length := by
  intro l
  induction l with
  | nil => intro u; rfl
  | cons st r ih =>
    intro u
    simp [BlockOffsets.pathBonds, ih]
private theorem length_axisPath (h : Fin 4 → ℤ) :
    (BlockAverages.axisPath h 1).length = (h 0).natAbs + (h 1).natAbs + (h 2).natAbs + (h 3).natAbs := by
  have e : BlockAverages.axisPath h 1 = List.replicate (h 0).natAbs (0, decide (0 ≤ h 0)) ++
      (List.replicate (h 1).natAbs (1, decide (0 ≤ h 1)) ++
        (List.replicate (h 2).natAbs (2, decide (0 ≤ h 2)) ++
          (List.replicate (h 3).natAbs (3, decide (0 ≤ h 3)) ++ []))) := by
    simp [BlockAverages.axisPath, List.finRange_succ, List.flatMap_cons]
    rfl
  rw [e]
  simp
  omega
private theorem natAbs_minimalOffset_le (o z : TorusFields.TorusSite N) (i : Fin 4) : (MomentLaw.minimalOffset o z i).natAbs ≤ TorusFields.supDist z o :=
  Finset.le_sup (f := fun i => ((z i - o i).valMinAbs).natAbs) (Finset.mem_univ i)
end LatticePaths
end AxialGaugePaths
open AxialGaugePaths in
theorem axialGaugePathBounds_holds (hAx : WeightedResponses.axialGaugeNearOneStatement) : MomentLaw.axialGaugePathBoundsStatement := by
  refine ⟨?_, ?_, ?_, norm_minimalLog_le_pi⟩
  · intro ℓ N _ o z
    have hn : ∀ i, (TorusLumps.stepBlockFrame ℓ.side N).extent i = N := fun _ => rfl
    have zero : StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top o + BlockAverages.siteOfCoords (TorusLumps.stepBlockFrame ℓ.side N).top 0 =
        StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top o := by
      have : BlockAverages.siteOfCoords (F := TorusLumps.stepBlockFrame ℓ.side N) (TorusLumps.stepBlockFrame ℓ.side N).top 0 = 0 := by
        funext i
        simp [BlockAverages.siteOfCoords]
      rw [this, add_zero]
    refine ⟨fun W => ?_, fun W W' => ?_, fun c hc => ?_, ?_⟩
    · rw [axialGaugeAt_eq_pathHolonomy]
      have := distFromOne_pathHolonomy_le (ℓ := ℓ) W o (BlockAverages.axisPath (MomentLaw.minimalOffset o z) 1) 0
      rw [zero] at this
      exact this
    · rw [axialGaugeAt_eq_pathHolonomy, axialGaugeAt_eq_pathHolonomy]
      have := norm_pathHolonomy_sub_le (ℓ := ℓ) W W' o (BlockAverages.axisPath (MomentLaw.minimalOffset o z) 1) 0
      rw [zero] at this
      exact this
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
      have hg := BlockOffsets.isAxialBond_of_mem_axisPath (H := (TorusFields.supDist z o : ℤ)) (o := MomentLaw.minimalOffset o z) (fun l => by
        have := natAbs_minimalOffset_le o z l
        constructor <;> omega) b hb
      have h1 := TorusFields.supDist_add_siteOfInt_le o b.1 (TorusFields.supDist z o) (fun i => by
        have := hg.1 i
        omega)
      rw [TorusFields.supDist_comm]
      exact h1
    · unfold MomentLaw.latticePath
      rw [List.length_map, length_pathBonds, length_axisPath]
      have a0 := natAbs_minimalOffset_le o z 0
      have a1 := natAbs_minimalOffset_le o z 1
      have a2 := natAbs_minimalOffset_le o z 2
      have a3 := natAbs_minimalOffset_le o z 3
      omega
  · intro ℓ N _ o W r s hbig hs hcold b hb1 hb2
    set F := TorusLumps.stepBlockFrame ℓ.side N with hF
    have hn : ∀ i, F.extent i = N := fun _ => rfl
    have hpt := TopLevelSites.period_top_of_extent (F := F) hn
    set Y : F.Cell := StepCosts.torusSiteInFrame F F.top o with hY
    have hbox : ∀ h : Fin 4 → ℤ, BlockAverages.WithinRadius r h → TorusFields.supDist (o + TorusFields.siteOfInt h) o ≤ r := by
      intro h hh
      rw [TorusFields.supDist_comm]
      refine TorusFields.supDist_add_siteOfInt_le o h r fun i => ?_
      have := abs_le.1 (hh i)
      omega
    have hon : ∀ h : Fin 4 → ℤ, TorusLumps.toTorusSite N (Y + BlockAverages.siteOfCoords F.top h : F.Cell) = o + TorusFields.siteOfInt h := fun h => by
      rw [TopLevelSites.toTorusSite_add hpt, TopLevelSites.toTorusSite_torusSiteInFrame hpt, TopLevelSites.toTorusSite_siteOfCoords hpt]
    have key := hAx F (TorusFields.readAtLevel F F.top W) Y s r (fun _ => hbig) hs (fun c i l hil h1 h2 h3 h4 => by
      rw [TopLevelSites.plaquetteDefect_readAtLevel_eq hpt, hon]
      have e : ∀ (h : Fin 4 → ℤ) (i : Fin 4), o + TorusFields.siteOfInt (h + Pi.single i 1) = o + TorusFields.siteOfInt h + TorusFields.unitStep N i := by
        intro h i
        funext k
        by_cases hk : k = i
        · subst hk
          simp [TorusFields.siteOfInt, TorusFields.unitStep, add_assoc]
        · simp [TorusFields.siteOfInt, TorusFields.unitStep, hk, Pi.single_eq_of_ne hk]
      refine hcold _ _ _ hil (hbox _ h1) ?_ ?_ ?_
      · rw [← e]; exact hbox _ h2
      · rw [← e]; exact hbox _ h3
      · rw [← e, ← e]; exact hbox _ h4)
    obtain ⟨h, hz, hle⟩ := TorusFields.exists_offset_of_supDist o b.1
    obtain ⟨h', hz', hle'⟩ := TorusFields.exists_offset_of_supDist o (b.1 + TorusFields.unitStep N b.2)
    rw [TorusFields.supDist_comm] at hb1 hb2
    have hh1 : BlockAverages.WithinRadius r h := fun i => by
      have := hle i
      rw [abs_le]
      omega
    have hh2 : BlockAverages.WithinRadius r (h + Pi.single b.2 1) := by
      intro i
      by_cases hi : i = b.2
      · subst hi
        have e1 := congrFun hz' b.2
        have e2 := congrFun hz b.2
        have e3 : ((h' b.2 : ℤ) : ZMod N) = ((h b.2 + 1 : ℤ) : ZMod N) := by
          have a1 : (b.1 + TorusFields.unitStep N b.2) b.2 = b.1 b.2 + 1 := by simp [TorusFields.unitStep]
          have a2 : (o + TorusFields.siteOfInt h' : TorusFields.TorusSite N) b.2 = o b.2 + ((h' b.2 : ℤ) : ZMod N) := rfl
          have a3 : (o + TorusFields.siteOfInt h : TorusFields.TorusSite N) b.2 = o b.2 + ((h b.2 : ℤ) : ZMod N) := rfl
          rw [a1, a2, e2, a3] at e1
          push_cast
          have := add_left_cancel (a := o b.2) (b := ((h' b.2 : ℤ) : ZMod N)) (c := ((h b.2 : ℤ) : ZMod N) + 1) (by
            rw [← e1]; ring)
          exact this
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at e3
        have b1 := hle b.2
        have b2 := hle' b.2
        have hd : h b.2 + 1 - h' b.2 = 0 := by
          refine Int.eq_zero_of_abs_lt_dvd e3 ?_
          rw [abs_lt]
          constructor <;> omega
        have : (h + Pi.single b.2 1 : Fin 4 → ℤ) b.2 = h' b.2 := by
          simp
          omega
        rw [this, abs_le]
        omega
      · simpa [Pi.single_eq_of_ne hi] using hh1 i
    have hk := key (h, b.2) ⟨hh1, hh2⟩
    have hg : ∀ z' : F.Cell, ColdStepAtMirrorFrames.axialGaugeHolonomy (TorusFields.readAtLevel F F.top W) Y z' = ResponseInTheExpansion.axialGaugeAt ℓ W o (TorusLumps.toTorusSite N z') := fun z' => by
      have e0 : ResponseInTheExpansion.axialGaugeAt ℓ W o (TorusLumps.toTorusSite N z') = ColdStepAtMirrorFrames.axialGaugeHolonomy (F := F) (TorusFields.readAtLevel F F.top W) (StepCosts.torusSiteInFrame F F.top o)
          (StepCosts.torusSiteInFrame F F.top (TorusLumps.toTorusSite N z')) := rfl
      rw [e0, TopLevelSites.torusSiteInFrame_toTorusSite hpt]
    have hgr : BlockAverages.gaugeTransform (ColdStepAtMirrorFrames.axialGaugeHolonomy (TorusFields.readAtLevel F F.top W) Y) (TorusFields.readAtLevel F F.top W) (Y + BlockAverages.siteOfCoords F.top h) b.2 =
        ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ W o) W b := by
      have e2 : TorusLumps.toTorusSite N (Y + BlockAverages.siteOfCoords F.top h + BlockAverages.unitStep F.top b.2 : F.Cell) = TorusLumps.toTorusSite N (Y + BlockAverages.siteOfCoords F.top h : F.Cell) + TorusFields.unitStep N b.2 := by
        rw [TopLevelSites.toTorusSite_add hpt, TopLevelSites.toTorusSite_unitStep hpt]
      unfold BlockAverages.gaugeTransform ResponseInTheExpansion.gaugeTransform
      rw [hg, hg, e2, hon, ← hz, TopLevelSites.readAtLevel_torusSiteInFrame_add hn, ← hz]
    have h3 : ‖((BlockAverages.gaugeTransform (ColdStepAtMirrorFrames.axialGaugeHolonomy (TorusFields.readAtLevel F F.top W) Y) (TorusFields.readAtLevel F F.top W) (Y + BlockAverages.siteOfCoords F.top (h, b.2).1) (h, b.2).2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 3 * r * s := hk
    show ‖((ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ W o) W b : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ _
    rw [← hgr]
    exact h3
  · intro N _ W g B x μ ν h1 h2 h3 h4 hB ha
    set a : TorusFields.TorusBond N → BlockAverages.imaginaryQuaternions := fun b => LumpContours.minimalLog (ResponseInTheExpansion.gaugeTransform g W b) with hadef
    have hq : TorusFields.holonomy W x μ ν = BlockAverages.expUnit (B (x, μ)) * BlockAverages.expUnit (B (x + TorusFields.unitStep N μ, ν)) * (BlockAverages.expUnit (B (x + TorusFields.unitStep N ν, μ)))⁻¹ *
        (BlockAverages.expUnit (B (x, ν)))⁻¹ := by
      unfold TorusFields.holonomy
      rw [h1, h2, h3, h4]
    have f1 : ‖((TorusFields.holonomy W x μ ν : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 - ((ResponseInTheExpansion.lieFormCurl B (x, μ, ν) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 3 * MomentLaw.plaquetteLogSize B x μ ν ^ 2 := by
      rw [hq]
      exact norm_prod_four_expUnit_sub_one_sub_le _ _ _ _ hB
    have hgq : g x * TorusFields.holonomy W x μ ν * (g x)⁻¹ = BlockAverages.expUnit (a (x, μ)) * BlockAverages.expUnit (a (x + TorusFields.unitStep N μ, ν)) *
        (BlockAverages.expUnit (a (x + TorusFields.unitStep N ν, μ)))⁻¹ * (BlockAverages.expUnit (a (x, ν)))⁻¹ := by
      simp only [hadef, TopLevelSites.expUnit_minimalLog]
      have e : x + TorusFields.unitStep N ν + TorusFields.unitStep N μ = x + TorusFields.unitStep N μ + TorusFields.unitStep N ν := by abel
      unfold ResponseInTheExpansion.gaugeTransform TorusFields.holonomy
      simp only
      rw [e]
      group
    have f2 : ‖((g x * TorusFields.holonomy W x μ ν * (g x)⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 - ((ResponseInTheExpansion.lieFormCurl a (x, μ, ν) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        3 * MomentLaw.plaquetteLogSize a x μ ν ^ 2 := by
      rw [hgq]
      exact norm_prod_four_expUnit_sub_one_sub_le _ _ _ _ ha
    refine ⟨f1, ?_⟩
    have f3 := norm_conj_sub_le (g x) (TorusFields.holonomy W x μ ν)
    set Q : ℍ[ℝ] := ((TorusFields.holonomy W x μ ν : BlockAverages.UnitQuaternion) : ℍ[ℝ]) with hQ
    set Q' : ℍ[ℝ] := ((g x * TorusFields.holonomy W x μ ν * (g x)⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) with hQ'
    have e : ((ResponseInTheExpansion.lieFormCurl a (x, μ, ν) - ResponseInTheExpansion.lieFormCurl B (x, μ, ν) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) =
        -(Q' - 1 - ((ResponseInTheExpansion.lieFormCurl a (x, μ, ν) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])) + (Q' - Q) + (Q - 1 - ((ResponseInTheExpansion.lieFormCurl B (x, μ, ν) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])) := by
      push_cast
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (-(Q' - 1 - ((ResponseInTheExpansion.lieFormCurl a (x, μ, ν) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]))) (Q' - Q)
    rw [norm_neg] at this
    have hc : distFromOne (TorusFields.holonomy W x μ ν) = TorusFields.curvature W x μ ν := rfl
    rw [hc] at f3
    linarith
end MomentLaw
end YangMills.Construction
end
