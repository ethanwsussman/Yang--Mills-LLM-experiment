import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClassProof
import YangMills.Construction.FormsOnATorus.FormsAlongPathsOfATorus
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.LawOnABoxOfTheFlow.BoundsOnTheEllipsoid
import YangMills.Construction.LawOnABoxOfTheFlow.CirculationOnTheGoodEvent
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.BoxEvents
section UnitQuaternions
private theorem inner_coe_unit (q : ℍ[ℝ]) (v : BlockAverages.UnitQuaternion) :
    inner ℝ q ((v : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = (q * ((v⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])).re := by
  rw [Quaternion.inner_def]
  rfl
private theorem norm_sub_coe_unit_sq (q : ℍ[ℝ]) (v : BlockAverages.UnitQuaternion) :
    ‖q - ((v : BlockAverages.UnitQuaternion) : ℍ[ℝ])‖ ^ 2 =
      ‖q‖ ^ 2 - 2 * (q * ((v⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])).re + 1 := by
  have h := norm_sub_sq_real q ((v : BlockAverages.UnitQuaternion) : ℍ[ℝ])
  rw [PathForms.norm_unitQuaternion, inner_coe_unit] at h
  rw [h]
  ring
private theorem re_coe_unit (v : BlockAverages.UnitQuaternion) :
    ((v : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re = 1 - ‖((v : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 / 2 := by apply _root_.YangMills.Construction.ReferenceBounds.re_coe_unitQuaternion_eq <;> assumption
private theorem re_le_norm_self (q : ℍ[ℝ]) : q.re ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.quaternion_re_le_norm <;> assumption
private theorem norm_sub_unit_le_of_defect {q : ℍ[ℝ]} {v : BlockAverages.UnitQuaternion} {δ : ℝ} (hδ : 0 ≤ δ)
    (hq : ‖q‖ ≤ 1) (hf : 2 * TorusPaths.alignmentDefect v q ≤ δ ^ 2) :
    ‖q - ((v : BlockAverages.UnitQuaternion) : ℍ[ℝ])‖ ≤ δ + (1 - ‖q‖) := by
  have h := norm_sub_coe_unit_sq q v
  unfold TorusPaths.alignmentDefect at hf
  have h1 : 0 ≤ 1 - ‖q‖ := by linarith
  have h2 : ‖q - ((v : BlockAverages.UnitQuaternion) : ℍ[ℝ])‖ ^ 2 ≤ (δ + (1 - ‖q‖)) ^ 2 := by
    rw [h]
    nlinarith [mul_nonneg hδ h1]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (add_nonneg hδ h1) two_ne_zero).mp h2
private theorem re_finset_sum {ι : Type} (s : Finset ι) (G : ι → ℍ[ℝ]) :
    (∑ e ∈ s, G e).re = ∑ e ∈ s, (G e).re := by apply _root_.YangMills.Construction.BlockAverages.CoordinateStep.re_finset_sum <;> assumption
private theorem re_conj_units (g : BlockAverages.UnitQuaternion) (X : ℍ[ℝ]) :
    (((g : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * X * ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])).re = X.re := by apply _root_.YangMills.Construction.GaugedCriticality.re_conj_unit <;> assumption
private theorem alignmentDefect_conj (g₁ g₂ v : BlockAverages.UnitQuaternion) (q : ℍ[ℝ]) :
    TorusPaths.alignmentDefect (g₁ * v * g₂⁻¹)
        (((g₁ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * q * ((g₂⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])) =
      TorusPaths.alignmentDefect v q := by
  unfold TorusPaths.alignmentDefect
  have h1 : ‖((g₁ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * q * ((g₂⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])‖ = ‖q‖ := by
    rw [norm_mul, norm_mul, PathForms.norm_unitQuaternion, PathForms.norm_unitQuaternion, one_mul, mul_one]
  have h2 : ((g₁ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * q * ((g₂⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) *
      (((g₁ * v * g₂⁻¹)⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) =
      ((g₁ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * (q * ((v⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])) *
        ((g₁⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) := by
    have e : (g₁ * v * g₂⁻¹)⁻¹ = g₂ * v⁻¹ * g₁⁻¹ := by group
    have e2 : ((g₂⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * ((g₂ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = 1 := by
      rw [← Submonoid.coe_mul, inv_mul_cancel]
      rfl
    rw [e]
    simp only [Submonoid.coe_mul]
    calc _ = ((g₁ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * q *
          (((g₂⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * ((g₂ : BlockAverages.UnitQuaternion) : ℍ[ℝ])) *
          ((v⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * ((g₁⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) := by
          noncomm_ring
      _ = _ := by rw [e2]; noncomm_ring
  rw [h1, h2, re_conj_units]
end UnitQuaternions
section Paths
variable {m : ℕ}
private theorem pathHolonomy_gaugeTransform (g : TorusFields.TorusSite m → BlockAverages.UnitQuaternion)
    (W : TorusFields.TorusField m) (x : TorusFields.TorusSite m) (l : List BlockAverages.PathStep) :
    PathForms.pathHolonomy (TorusFields.gaugeTransform g W) x l =
      g x * PathForms.pathHolonomy W x l * (g (PathForms.pathEnd x l))⁻¹ := by
  induction l generalizing x with
  | nil => simp [PathForms.pathHolonomy, PathForms.pathEnd]
  | cons st r ih =>
    simp only [PathForms.pathHolonomy, PathForms.pathEnd]
    rw [ih]
    rcases st with ⟨i, c⟩
    cases c
    · simp [PathForms.stepHolonomy, PathForms.stepShift, TorusFields.gaugeTransform, mul_assoc, sub_eq_add_neg]
    · simp [PathForms.stepHolonomy, PathForms.stepShift, TorusFields.gaugeTransform, mul_assoc]
end Paths
section Contours
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem plainContourAverage_eq_sum (Y : TorusFields.TorusSite n) (i : Fin 4) (W : TorusFields.TorusField (n * L)) :
    TorusContours.plainContourAverage L Y i W = TorusContours.contourWeight L • ∑ e ∈ TorusContours.contourIndex L,
      ((PathForms.pathHolonomy W (TorusBlocks.blockCentreSite L Y) (BlockAverages.bondContour L e.1 e.2 i) :
        BlockAverages.UnitQuaternion) : ℍ[ℝ]) := by
  unfold TorusContours.plainContourAverage TorusPaths.wordAverage TorusContours.contourWord
  simp only [PathForms.pathHolonomy_eq_wordHolonomy]
private theorem pathEnd_bondContour (Y : TorusFields.TorusSite n) (i : Fin 4) (ξ : Fin 4 → ℤ)
    (π : Equiv.Perm (Fin 4)) :
    PathForms.pathEnd (TorusBlocks.blockCentreSite L Y) (BlockAverages.bondContour L ξ π i) =
      TorusBlocks.blockCentreSite L (Y + TorusFields.unitStep n i) := by
  unfold BlockAverages.bondContour
  rw [PathForms.blockCentreSite_add_unitStep, PathForms.pathEnd_append, PathForms.pathEnd_append,
    PathForms.pathEnd_axisPath, PathForms.pathEnd_replicate]
  have e : TorusBlocks.blockCentreSite L Y + TorusFields.siteOfInt ξ + L • TorusFields.unitStep (n * L) i =
      PathForms.pathEnd (TorusBlocks.blockCentreSite L Y + L • TorusFields.unitStep (n * L) i)
        (BlockAverages.axisPath ξ π) := by
    rw [PathForms.pathEnd_axisPath]
    abel
  rw [e, PathForms.pathEnd_reversePath]
private theorem plainContourAverage_gaugeTransform (g : TorusFields.TorusSite (n * L) → BlockAverages.UnitQuaternion)
    (W : TorusFields.TorusField (n * L)) (Y : TorusFields.TorusSite n) (i : Fin 4) :
    TorusContours.plainContourAverage L Y i (TorusFields.gaugeTransform g W) =
      ((g (TorusBlocks.blockCentreSite L Y) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) *
        TorusContours.plainContourAverage L Y i W *
        (((g (TorusBlocks.blockCentreSite L (Y + TorusFields.unitStep n i)))⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) := by
  rw [plainContourAverage_eq_sum, plainContourAverage_eq_sum, mul_smul_comm, smul_mul_assoc, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [pathHolonomy_gaugeTransform, pathEnd_bondContour]
  simp only [Submonoid.coe_mul]
private theorem plainContourAverage_expansion (hL : Odd L) (W : TorusFields.TorusField (n * L))
    (Y : TorusFields.TorusSite n) (i : Fin 4) {a : ℝ} (h0 : 0 ≤ a)
    (ha : ∀ e ∈ TorusContours.contourIndex L,
      ∀ b ∈ PathForms.pathBonds (TorusBlocks.blockCentreSite L Y) (BlockAverages.bondContour L e.1 e.2 i),
        ‖PathForms.linkDeviation W b‖ ≤ a) :
    ‖TorusContours.plainContourAverage L Y i W - 1 - PathForms.contourMean L (PathForms.linkDeviation W) (Y, i)‖ ≤
        (5 * L * a) ^ 2 ∧
      ‖TorusContours.plainContourAverage L Y i W‖ ≤ 1 ∧
      1 - ‖TorusContours.plainContourAverage L Y i W‖ ≤ (5 * L * a) ^ 2 / 2 := by
  have hw := TorusContours.contourWeight_mul_card (L := L) hL
  have hw0 := TorusContours.contourWeight_nonneg L
  set w := TorusContours.contourWeight L with hwdef
  set I := TorusContours.contourIndex L with hI
  have hlen : ∀ e ∈ I, ((BlockAverages.bondContour L e.1 e.2 i).length : ℝ) ≤ 5 * L := fun e he => by
    have := TorusContours.length_bondContour_le hL (Finset.mem_product.mp he).1 e.2 i
    exact_mod_cast this
  have hone : ∀ e ∈ I, ‖((PathForms.pathHolonomy W (TorusBlocks.blockCentreSite L Y)
      (BlockAverages.bondContour L e.1 e.2 i) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 5 * L * a :=
    fun e he => (PathForms.norm_pathHolonomy_sub_one_le W _ _ (ha e he)).trans
      (mul_le_mul_of_nonneg_right (hlen e he) h0)
  have hlin : ∀ e ∈ I, ‖((PathForms.pathHolonomy W (TorusBlocks.blockCentreSite L Y)
      (BlockAverages.bondContour L e.1 e.2 i) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 -
      PathForms.formPathSum (PathForms.linkDeviation W) (TorusBlocks.blockCentreSite L Y)
        (BlockAverages.bondContour L e.1 e.2 i)‖ ≤ (5 * L * a) ^ 2 := fun e he =>
    (PathForms.norm_pathHolonomy_sub_one_sub_formPathSum_le W _ _ h0 (ha e he)).trans
      (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (hlen e he) h0) 2)
  have hsum : ∀ (G : (Fin 4 → ℤ) × Equiv.Perm (Fin 4) → ℍ[ℝ]) (c : ℝ), (∀ e ∈ I, ‖G e‖ ≤ c) →
      ‖w • ∑ e ∈ I, G e‖ ≤ c := fun G c hG => by
    rw [norm_smul, Real.norm_of_nonneg hw0]
    have h2 : ‖∑ e ∈ I, G e‖ ≤ I.card • c := (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ hG)
    rw [nsmul_eq_mul] at h2
    calc w * ‖∑ e ∈ I, G e‖ ≤ w * (I.card * c) := mul_le_mul_of_nonneg_left h2 hw0
      _ = c := by rw [← mul_assoc, hw, one_mul]
  have h1eq : (1 : ℍ[ℝ]) = w • ∑ e ∈ I, (1 : ℍ[ℝ]) := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hw, one_smul]
  rw [plainContourAverage_eq_sum]
  refine ⟨?_, ?_, ?_⟩
  · unfold PathForms.contourMean
    have e : w • ∑ e ∈ I, ((PathForms.pathHolonomy W (TorusBlocks.blockCentreSite L Y)
          (BlockAverages.bondContour L e.1 e.2 i) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 -
        w • ∑ e ∈ I, PathForms.formPathSum (PathForms.linkDeviation W) (TorusBlocks.blockCentreSite L Y)
          (BlockAverages.bondContour L e.1 e.2 i) =
        w • ∑ e ∈ I, (((PathForms.pathHolonomy W (TorusBlocks.blockCentreSite L Y)
          (BlockAverages.bondContour L e.1 e.2 i) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 -
          PathForms.formPathSum (PathForms.linkDeviation W) (TorusBlocks.blockCentreSite L Y)
            (BlockAverages.bondContour L e.1 e.2 i)) := by
      conv_lhs => rw [h1eq]
      rw [← smul_sub, ← smul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact e ▸ hsum _ _ hlin
  · exact hsum _ 1 fun e _ => (PathForms.norm_unitQuaternion _).le
  · have hre : (1 : ℝ) - (5 * L * a) ^ 2 / 2 ≤
        (w • ∑ e ∈ I, ((PathForms.pathHolonomy W (TorusBlocks.blockCentreSite L Y)
          (BlockAverages.bondContour L e.1 e.2 i) : BlockAverages.UnitQuaternion) : ℍ[ℝ])).re := by
      have hre' : (w • ∑ e ∈ I, ((PathForms.pathHolonomy W (TorusBlocks.blockCentreSite L Y)
            (BlockAverages.bondContour L e.1 e.2 i) : BlockAverages.UnitQuaternion) : ℍ[ℝ])).re =
          w * ∑ e ∈ I, ((PathForms.pathHolonomy W (TorusBlocks.blockCentreSite L Y)
            (BlockAverages.bondContour L e.1 e.2 i) : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re := by
        rw [Quaternion.re_smul, smul_eq_mul]
        rw [re_finset_sum]
      rw [hre']
      have h3 : ∀ e ∈ I, (1 : ℝ) - (5 * L * a) ^ 2 / 2 ≤
          ((PathForms.pathHolonomy W (TorusBlocks.blockCentreSite L Y)
            (BlockAverages.bondContour L e.1 e.2 i) : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re := fun e he => by
        rw [re_coe_unit]
        have := pow_le_pow_left₀ (norm_nonneg _) (hone e he) 2
        linarith
      have h4 := Finset.card_nsmul_le_sum I _ _ h3
      rw [nsmul_eq_mul] at h4
      calc (1 : ℝ) - (5 * L * a) ^ 2 / 2 = w * (I.card * (1 - (5 * L * a) ^ 2 / 2)) := by
            rw [← mul_assoc, hw, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 hw0
    have := re_le_norm_self (w • ∑ e ∈ I, ((PathForms.pathHolonomy W (TorusBlocks.blockCentreSite L Y)
      (BlockAverages.bondContour L e.1 e.2 i) : BlockAverages.UnitQuaternion) : ℍ[ℝ]))
    linarith
private theorem linkDeviation_sub_contourMean_le (hL : Odd L) (W : TorusFields.TorusField (n * L))
    (V : TorusFields.TorusField n) (g : TorusFields.TorusSite (n * L) → BlockAverages.UnitQuaternion)
    (Y : TorusFields.TorusSite n) (i : Fin 4) {a δ : ℝ} (h0 : 0 ≤ a) (hδ : 0 ≤ δ)
    (ha : ∀ e ∈ TorusContours.contourIndex L,
      ∀ b ∈ PathForms.pathBonds (TorusBlocks.blockCentreSite L Y) (BlockAverages.bondContour L e.1 e.2 i),
        ‖PathForms.linkDeviation (TorusFields.gaugeTransform g W) b‖ ≤ a)
    (hfit : 2 * TorusPaths.alignmentDefect (V Y i) (TorusContours.plainContourAverage L Y i W) ≤ δ ^ 2) :
    ‖PathForms.linkDeviation (TorusFields.gaugeTransform (fun y => g (TorusBlocks.blockCentreSite L y)) V) (Y, i) -
        PathForms.contourMean L (PathForms.linkDeviation (TorusFields.gaugeTransform g W)) (Y, i)‖ ≤
      δ + 2 * (5 * L * a) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := plainContourAverage_expansion hL (TorusFields.gaugeTransform g W) Y i h0 ha
  set q := TorusContours.plainContourAverage L Y i (TorusFields.gaugeTransform g W) with hq
  set v : BlockAverages.UnitQuaternion :=
    TorusFields.gaugeTransform (fun y => g (TorusBlocks.blockCentreSite L y)) V Y i with hv
  have hfit' : 2 * TorusPaths.alignmentDefect v q ≤ δ ^ 2 := by
    have : TorusPaths.alignmentDefect v q =
        TorusPaths.alignmentDefect (V Y i) (TorusContours.plainContourAverage L Y i W) := by
      rw [hq, plainContourAverage_gaugeTransform, hv]
      exact alignmentDefect_conj _ _ _ _
    rw [this]
    exact hfit
  have h4 := norm_sub_unit_le_of_defect hδ h2 hfit'
  have e : PathForms.linkDeviation (TorusFields.gaugeTransform (fun y => g (TorusBlocks.blockCentreSite L y)) V) (Y, i) -
      PathForms.contourMean L (PathForms.linkDeviation (TorusFields.gaugeTransform g W)) (Y, i) =
      (q - 1 - PathForms.contourMean L (PathForms.linkDeviation (TorusFields.gaugeTransform g W)) (Y, i)) -
        (q - ((v : BlockAverages.UnitQuaternion) : ℍ[ℝ])) := by
    show ((v : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 - _ = _
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  nlinarith [sq_nonneg (5 * (L : ℝ) * a)]
end Contours
section Frames
private theorem usedContours_eq_allContours {F : BlockAverages.BlockFrame} {J₀ : ℕ}
    {h : Finset (Finset (F.Site F.depth))} {b : F.Cell → F.Site F.depth}
    {c : F.Cell × Fin 4} (h1 : LumpContours.nearbyLumps h c.1 = ∅)
    (h2 : LumpContours.nearbyLumps h (c.1 + BlockAverages.unitStep F.top c.2) = ∅) :
    LumpContours.usedContours J₀ h b c = LumpContours.allContours F := _root_.YangMills.Construction.ClusterExpansionOfAStep.ContourStability.usedContours_eq_allContours
      (F := F) (J₀ := J₀) (h := h) (b := b) (c := c) h1 h2
private theorem valMinAbs_intCast_of_two_mul_abs_lt {p : ℕ} [NeZero p] {z : ℤ} (h : 2 * |z| < p) :
    ((z : ZMod p)).valMinAbs = z := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem exists_half_of_odd (hL : Odd L) :
    ∃ q : ℤ, ((L : ℤ) - 1) / 2 = q ∧ (L : ℤ) = 2 * q + 1 ∧ 0 ≤ q := by
  obtain ⟨q, hq⟩ := hL
  refine ⟨q, ?_, ?_, by positivity⟩
  · subst hq
    push_cast
    omega
  · subst hq
    push_cast
    ring
private theorem minimalOffset_add_siteOfCoords (hL : Odd L)
    (x : (TorusLumps.stepBlockFrame L n).Site (TorusLumps.stepBlockFrame L n).depth) {ξ : Fin 4 → ℤ}
    (hξ : ξ ∈ BlockAverages.centredCube L) :
    LumpContours.minimalOffset x (x + BlockAverages.siteOfCoords (TorusLumps.stepBlockFrame L n).depth ξ) = ξ := by
  funext i
  obtain ⟨q, hq, hLq, hq0⟩ := exists_half_of_odd hL
  have h := TorusContours.mem_centredCube_iff.mp hξ i
  rw [hq] at h
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hper : (((TorusLumps.stepBlockFrame L n).period (TorusLumps.stepBlockFrame L n).depth i : ℕ) : ℤ) = n * L := by
    have : (TorusLumps.stepBlockFrame L n).period (TorusLumps.stepBlockFrame L n).depth i = n * L :=
      TorusContours.stepBlockFrame_period_zero i
    rw [this]
    push_cast
    ring
  have hbig : 2 * |ξ i| <
      (((TorusLumps.stepBlockFrame L n).period (TorusLumps.stepBlockFrame L n).depth i : ℕ) : ℤ) := by
    rw [hper]
    have h1 : |ξ i| ≤ q := abs_le.mpr h
    nlinarith
  simp only [LumpContours.minimalOffset, add_sub_cancel_left]
  exact valMinAbs_intCast_of_two_mul_abs_lt hbig
private theorem contourPath_of_centres (hL : Odd L)
    {b : (TorusLumps.stepBlockFrame L n).Cell →
      (TorusLumps.stepBlockFrame L n).Site (TorusLumps.stepBlockFrame L n).depth}
    {c : (TorusLumps.stepBlockFrame L n).Cell × Fin 4}
    (hb1 : b c.1 = BlockAverages.cellCentre (TorusLumps.stepBlockFrame L n).depth c.1)
    (hb2 : b (c.1 + BlockAverages.unitStep (TorusLumps.stepBlockFrame L n).top c.2) =
      BlockAverages.cellCentre (TorusLumps.stepBlockFrame L n).depth
        (c.1 + BlockAverages.unitStep (TorusLumps.stepBlockFrame L n).top c.2))
    {ξ : Fin 4 → ℤ} (hξ : ξ ∈ BlockAverages.centredCube L) (π : Equiv.Perm (Fin 4)) :
    LumpContours.contourPath b c ξ π = BlockAverages.bondContour L ξ π c.2 := by
  unfold LumpContours.contourPath BlockAverages.bondContour
  rw [hb1, hb2, minimalOffset_add_siteOfCoords hL _ hξ, minimalOffset_add_siteOfCoords hL _ hξ]
  rfl
private theorem contourMean_eq_plainContourAverage (hL : Odd L) {J₀ : ℕ}
    {h : Finset (Finset ((TorusLumps.stepBlockFrame L n).Site (TorusLumps.stepBlockFrame L n).depth))}
    {b : (TorusLumps.stepBlockFrame L n).Cell →
      (TorusLumps.stepBlockFrame L n).Site (TorusLumps.stepBlockFrame L n).depth}
    (W : TorusFields.TorusField (n * L)) (Y : TorusFields.TorusSite n) (i : Fin 4)
    (h1 : LumpContours.nearbyLumps h
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).top Y) = ∅)
    (h2 : LumpContours.nearbyLumps h
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).top Y +
        BlockAverages.unitStep (TorusLumps.stepBlockFrame L n).top i) = ∅)
    (hb1 : b (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).top Y) =
      BlockAverages.cellCentre (TorusLumps.stepBlockFrame L n).depth
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).top Y))
    (hb2 : b (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).top Y +
        BlockAverages.unitStep (TorusLumps.stepBlockFrame L n).top i) =
      BlockAverages.cellCentre (TorusLumps.stepBlockFrame L n).depth
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).top Y +
          BlockAverages.unitStep (TorusLumps.stepBlockFrame L n).top i)) :
    LumpContours.contourMean J₀ h b
        (TorusFields.readAtLevel (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).depth W)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).top Y, i) =
      TorusContours.plainContourAverage L Y i W := by
  haveI : NeZero (n * (TorusLumps.stepBlockFrame L n).blockSide) := inferInstanceAs (NeZero (n * L))
  have hread := TorusContours.contourAverage_readAtLevel (F := TorusLumps.stepBlockFrame L n) (n := n)
    (fun _ => rfl) W Y i
  have hcard : ((LumpContours.allContours (TorusLumps.stepBlockFrame L n)).card : ℝ) = 24 * (L : ℝ) ^ 4 := by
    have e : LumpContours.allContours (TorusLumps.stepBlockFrame L n) = TorusContours.contourIndex L := rfl
    rw [e, TorusContours.card_contourIndex hL]
    push_cast
    ring
  refine Eq.trans ?_ hread
  unfold LumpContours.contourMean BlockAverages.contourAverage
  rw [usedContours_eq_allContours (F := TorusLumps.stepBlockFrame L n) (J₀ := J₀) (h := h) (b := b)
    (c := (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).top Y, i))
    h1 h2, hcard]
  congr 1
  unfold LumpContours.allContours
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun ξ hξ => Finset.sum_congr rfl fun π _ => ?_
  rw [contourPath_of_centres hL
    (c := (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).top Y, i))
    hb1 hb2 hξ]
  show ((BlockAverages.pathHolonomy _
      (b (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).top Y)) _ :
      BlockAverages.UnitQuaternion) : ℍ[ℝ]) = _
  have e : BlockAverages.cellCentre (TorusLumps.stepBlockFrame L n).depth
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).top Y) =
      BlockAverages.refineSite
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).top Y) :=
    TorusContours.cellCentre_eq _
  rw [hb1, e]
  rfl
private theorem bondFit_eq_alignmentDefect {ℓ : TorusLumps.StepParameters} (hL : Odd ℓ.side)
    (W : TorusFields.TorusField (n * ℓ.side)) (V : TorusFields.TorusField n)
    (b : StepCosts.BaseChoice ℓ.side n) (Y : TorusFields.TorusSite n) (i : Fin 4)
    (h1 : LumpContours.nearbyLumps (StepCosts.stepHotLumps ℓ W)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) (TorusLumps.stepBlockFrame ℓ.side n).top Y) = ∅)
    (h2 : LumpContours.nearbyLumps (StepCosts.stepHotLumps ℓ W)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) (TorusLumps.stepBlockFrame ℓ.side n).top Y +
        BlockAverages.unitStep (TorusLumps.stepBlockFrame ℓ.side n).top i) = ∅)
    (hb1 : b (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n)
        (TorusLumps.stepBlockFrame ℓ.side n).top Y) =
      BlockAverages.cellCentre (TorusLumps.stepBlockFrame ℓ.side n).depth
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) (TorusLumps.stepBlockFrame ℓ.side n).top Y))
    (hb2 : b (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n)
        (TorusLumps.stepBlockFrame ℓ.side n).top Y + BlockAverages.unitStep (TorusLumps.stepBlockFrame ℓ.side n).top i) =
      BlockAverages.cellCentre (TorusLumps.stepBlockFrame ℓ.side n).depth
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) (TorusLumps.stepBlockFrame ℓ.side n).top Y +
          BlockAverages.unitStep (TorusLumps.stepBlockFrame ℓ.side n).top i)) :
    StepCosts.bondFit ℓ W V b (Y, i) =
      TorusPaths.alignmentDefect (V Y i) (TorusContours.plainContourAverage ℓ.side Y i W) := by
  have hm := contourMean_eq_plainContourAverage hL (J₀ := ℓ.baseDepth) (h := StepCosts.stepHotLumps ℓ W)
    W Y i h1 h2 hb1 hb2
  have hV : TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 V
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 Y) i = V Y i :=
    TopLevelSites.readAtLevel_torusSiteInFrame (fun i => TorusContours.stepBlockFrame_period_one i) V Y i
  unfold StepCosts.bondFit LumpContours.contourFit TorusPaths.alignmentDefect
  simp only
  rw [show LumpContours.contourMean ℓ.baseDepth (StepCosts.stepHotLumps ℓ W) b
      (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0 W)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 Y, i) =
    TorusContours.plainContourAverage ℓ.side Y i W from hm, hV]
end Frames
section Lumps
variable {n : ℕ} [NeZero n]
private theorem mem_lumpOf_self {F : BlockAverages.BlockFrame} [∀ j i, NeZero (F.period j i)] {L : ℕ} [NeZero L]
    (hL : Odd L) (g : LumpContours.LumpGrid L) {j : ℕ} (x : F.Site j) : x ∈ LumpContours.lumpOf g x := by
  obtain ⟨q, hq, hLq, hq0⟩ := exists_half_of_odd hL
  have hLpos : (0 : ℤ) < L := by omega
  unfold LumpContours.lumpOf LumpContours.boxSites
  refine Finset.mem_image.mpr ⟨BlockAverages.siteCoords x, ?_, TorusContours.siteOfCoords_siteCoords x⟩
  refine Fintype.mem_piFinset.mpr fun i => ?_
  have hoff : |LumpContours.offsetFromCentre L (BlockAverages.siteCoords x i)| ≤ ((L : ℤ) - 1) / 2 := by
    unfold LumpContours.offsetFromCentre
    rw [hq]
    have a1 := Int.emod_nonneg (BlockAverages.siteCoords x i + q) (ne_of_gt hLpos)
    have a2 := Int.emod_lt_of_pos (BlockAverages.siteCoords x i + q) hLpos
    rw [abs_le]
    constructor <;> omega
  obtain ⟨b1, b2, b3, b4⟩ := g.mem_interval _ hoff
  exact Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩
private theorem supDist_le_two_of_mem_vertices {m : ℕ} [NeZero m] (x : TorusFields.TorusSite m) (μ ν : Fin 4)
    {z : TorusFields.TorusSite m} (hz : z ∈ TorusFields.plaquetteVertices x μ ν) : TorusFields.supDist x z ≤ 2 := by
  simp only [TorusFields.plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · rw [TorusFields.supDist_self]; omega
  · exact (TorusFields.supDist_add_unitStep_le x μ).trans (by omega)
  · exact (TorusFields.supDist_add_unitStep_le x ν).trans (by omega)
  · have h1 := TorusFields.supDist_add_unitStep_le x μ
    have h2 := TorusFields.supDist_add_unitStep_le (x + TorusFields.unitStep m μ) ν
    exact (TorusFields.supDist_triangle x (x + TorusFields.unitStep m μ) _).trans (by omega)
private theorem exists_hot_vertex_of_mem_nearbyLumps {F : BlockAverages.BlockFrame} [∀ j i, NeZero (F.period j i)]
    {L : ℕ} [NeZero L] (hL : Odd L) (g : LumpContours.LumpGrid L)
    (s : ℝ) (X : Finset (F.Site F.depth)) (W : F.GaugeField F.depth) (y : F.Cell) {l : Finset (F.Site F.depth)}
    (hl : l ∈ LumpContours.nearbyLumps (LumpContours.hotLumps g s X W) y) :
    ∃ (p : F.Site F.depth × Fin 4 × Fin 4) (x : F.Site F.depth) (h' z : Fin 4 → ℤ), p.2.1 < p.2.2 ∧
      s ≤ BlockAverages.plaquetteDefect W p ∧ x ∈ BlockAverages.plaquetteCorners p ∧
      h' ∈ BlockAverages.centredCube (2 * 2 + 1) ∧ z ∈ BlockAverages.centredCube F.blockSide ∧
      x = TorusLumps.siteAtOffset (y + BlockAverages.siteOfCoords F.top h') z := by
  obtain ⟨hlh, hsub⟩ := Finset.mem_filter.mp hl
  obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hlh
  obtain ⟨hpc, hpσ⟩ := Finset.mem_filter.mp hp
  obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp hlp
  subst hxl
  have hxm : x ∈ LumpContours.lumpOf g x := mem_lumpOf_self hL g x
  generalize hT : LumpContours.cutBelow F.depth (LumpContours.cellBall y 2) = T at hsub
  have hxu : x ∈ T := hsub hxm
  rw [← hT, LumpContours.cutBelow, Finset.mem_biUnion] at hxu
  obtain ⟨y', hy', hxu'⟩ := hxu
  rw [LumpContours.cellBall, Finset.mem_image] at hy'
  obtain ⟨h', hh', hy'e⟩ := hy'
  obtain ⟨z, hz, hxz⟩ := (TorusContours.mem_sitesBelow_iff _ _).mp hxu'
  refine ⟨p, x, h', z, (Finset.mem_filter.mp hpc).2.1, hpσ, hx, hh', hz, ?_⟩
  rw [hy'e]
  exact hxz
private theorem nearbyLumps_eq_empty_of_cold {ℓ : TorusLumps.StepParameters} {δ : ℝ} {r : ℕ} (hσ : δ < ℓ.threshold)
    (hL : Odd ℓ.side) (hL16 : 16 ≤ ℓ.side)
    (W : TorusFields.TorusField (n * ℓ.side)) (o' : TorusFields.TorusSite (n * ℓ.side)) (Y : TorusFields.TorusSite n)
    (hcold : ∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o' (r : ℝ)),
      TorusFields.curvature W p.1 p.2.1 p.2.2 ≤ δ)
    (hr : TorusFields.supDist (TorusBlocks.blockCentreSite ℓ.side Y) o' + 3 * ℓ.side ≤ r) :
    LumpContours.nearbyLumps (StepCosts.stepHotLumps ℓ W)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) (TorusLumps.stepBlockFrame ℓ.side n).top Y) =
      ∅ := by
  have hp0 : ∀ i, (TorusLumps.stepBlockFrame ℓ.side n).period (TorusLumps.stepBlockFrame ℓ.side n).depth i =
      n * ℓ.side := fun i => TorusContours.stepBlockFrame_period_zero i
  have hp1 : ∀ i, (TorusLumps.stepBlockFrame ℓ.side n).period (TorusLumps.stepBlockFrame ℓ.side n).top i = n :=
    fun i => TorusContours.stepBlockFrame_period_one i
  refine Finset.eq_empty_of_forall_notMem fun l hl => ?_
  obtain ⟨p, x, h', z, hlt, hpσ, hx, hh', hz, hxz⟩ :=
    exists_hot_vertex_of_mem_nearbyLumps (F := TorusLumps.stepBlockFrame ℓ.side n) hL ℓ.grid ℓ.threshold _ _ _ hl
  set y' : (TorusLumps.stepBlockFrame ℓ.side n).Cell :=
    StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) (TorusLumps.stepBlockFrame ℓ.side n).top Y +
      BlockAverages.siteOfCoords (TorusLumps.stepBlockFrame ℓ.side n).top h' with hy'e
  obtain ⟨q, hq, hLq, hq0⟩ := exists_half_of_odd hL
  have hY' : (TorusLumps.toTorusSite n y' : TorusFields.TorusSite n) = Y + TorusFields.siteOfInt h' := by
    rw [hy'e, TopLevelSites.toTorusSite_add hp1, TopLevelSites.toTorusSite_torusSiteInFrame hp1,
      TopLevelSites.toTorusSite_siteOfCoords hp1]
  have hc : ∀ k, BlockAverages.siteCoords y' k =
      (((TorusLumps.toTorusSite n y' : TorusFields.TorusSite n) k).cast : ℤ) := fun k => by
    have := TopLevelSites.siteCoords_torusSiteInFrame hp1 (TorusLumps.toTorusSite n y') k
    rwa [TopLevelSites.torusSiteInFrame_toTorusSite hp1] at this
  have hxT : (TorusLumps.toTorusSite (n * ℓ.side) x : TorusFields.TorusSite (n * ℓ.side)) =
      TorusBlocks.blockCentreSite ℓ.side (Y + TorusFields.siteOfInt h') + TorusFields.siteOfInt z := by
    rw [hxz, TorusContours.siteAtOffset_eq, TopLevelSites.toTorusSite_siteOfCoords hp0]
    funext k
    show (((ℓ.side : ℤ) * BlockAverages.siteCoords y' k + z k : ℤ) : ZMod (n * ℓ.side)) = _
    rw [hc k, hY', TorusBlocks.blockCentreSite_apply_add]
    rfl
  have hd : TorusFields.supDist (TorusBlocks.blockCentreSite ℓ.side Y) (TorusLumps.toTorusSite (n * ℓ.side) x) ≤
      3 * ℓ.side - 4 := by
    rw [hxT, PathForms.blockCentreSite_add_siteOfInt, add_assoc, ← TorusFields.siteOfInt_add]
    refine TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
    have a1 := TorusContours.mem_centredCube_iff.mp hh' i
    have a2 := TorusContours.mem_centredCube_iff.mp hz i
    have e5 : (((2 * 2 + 1 : ℕ) : ℤ) - 1) / 2 = 2 := by norm_num
    rw [e5] at a1
    have e6 : ((TorusLumps.stepBlockFrame ℓ.side n).blockSide : ℤ) = ℓ.side := rfl
    rw [e6, hq] at a2
    have a3 : ((ℓ.side : ℤ) * h' i).natAbs ≤ 2 * ℓ.side := by
      rw [Int.natAbs_mul, Int.natAbs_natCast, mul_comm]
      exact Nat.mul_le_mul_right _ (by omega)
    have a4 := Int.natAbs_add_le ((ℓ.side : ℤ) * h' i) (z i)
    simp only [Pi.add_apply]
    omega
  have hxc : TorusFields.supDist (TorusLumps.toTorusSite (n * ℓ.side) p.1 : TorusFields.TorusSite (n * ℓ.side))
      (TorusLumps.toTorusSite (n * ℓ.side) x) ≤ 2 := by
    refine supDist_le_two_of_mem_vertices _ p.2.1 p.2.2 ?_
    simp only [BlockAverages.plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [TorusFields.plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false]
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr (Or.inl ?_)
      rw [TopLevelSites.toTorusSite_add hp0, TopLevelSites.toTorusSite_unitStep hp0]
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [TopLevelSites.toTorusSite_add hp0, TopLevelSites.toTorusSite_unitStep hp0]
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [TopLevelSites.toTorusSite_add hp0, TopLevelSites.toTorusSite_add hp0, TopLevelSites.toTorusSite_unitStep hp0,
        TopLevelSites.toTorusSite_unitStep hp0]
  have hP : ((TorusLumps.toTorusSite (n * ℓ.side) p.1, p.2.1, p.2.2) : TorusFields.TorusPlaquette (n * ℓ.side)) ∈
      TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o' (r : ℝ)) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, fun c hc' => PathForms.mem_supBall_of_supDist_le ?_⟩
    have b1 := supDist_le_two_of_mem_vertices _ _ _ hc'
    have b2 := TorusFields.supDist_triangle c (TorusLumps.toTorusSite (n * ℓ.side) p.1) o'
    have b3 := TorusFields.supDist_triangle (TorusLumps.toTorusSite (n * ℓ.side) p.1)
      (TorusLumps.toTorusSite (n * ℓ.side) x) o'
    have b4 := TorusFields.supDist_triangle (TorusLumps.toTorusSite (n * ℓ.side) x)
      (TorusBlocks.blockCentreSite ℓ.side Y) o'
    rw [TorusFields.supDist_comm c (TorusLumps.toTorusSite (n * ℓ.side) p.1)] at b2
    rw [TorusFields.supDist_comm (TorusLumps.toTorusSite (n * ℓ.side) x) (TorusBlocks.blockCentreSite ℓ.side Y)] at b4
    simp only at b1 ⊢
    omega
  have h1 := hcold _ hP
  have h2 : BlockAverages.plaquetteDefect
      (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) (TorusLumps.stepBlockFrame ℓ.side n).depth W) p =
      TorusFields.curvature W (TorusLumps.toTorusSite (n * ℓ.side) p.1) p.2.1 p.2.2 :=
    TopLevelSites.plaquetteDefect_readAtLevel_eq hp0 W p.1 p.2.1 p.2.2
  have h3 : ℓ.threshold ≤ BlockAverages.plaquetteDefect
      (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) (TorusLumps.stepBlockFrame ℓ.side n).depth W) p :=
    hpσ
  simp only at h1
  linarith
end Lumps
section Levels
private theorem norm_stepForm {m : ℕ} (f : TorusFields.TorusBond m → ℍ[ℝ]) (x : TorusFields.TorusSite m)
    (st : BlockAverages.PathStep) : ‖PathForms.stepForm f x st‖ = ‖f (PathForms.stepBond x st)‖ := by
  rcases st with ⟨i, c⟩
  cases c <;> simp [PathForms.stepForm, PathForms.stepBond]
private theorem norm_formPathSum_le {m : ℕ} (f : TorusFields.TorusBond m → ℍ[ℝ]) (x : TorusFields.TorusSite m)
    (l : List BlockAverages.PathStep) {a : ℝ}
    (ha : ∀ b ∈ PathForms.pathBonds x l, ‖f b‖ ≤ a) : ‖PathForms.formPathSum f x l‖ ≤ l.length * a := by
  induction l generalizing x with
  | nil => simp [PathForms.formPathSum]
  | cons st r ih =>
    simp only [PathForms.formPathSum, List.length_cons]
    have h1 := ha _ (List.mem_cons_self ..)
    have h2 := ih (x + PathForms.stepShift m st) fun b hb => ha b (List.mem_cons_of_mem _ hb)
    refine (norm_add_le _ _).trans ?_
    rw [norm_stepForm]
    push_cast
    linarith
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem norm_contourMean_le (hL : Odd L) (f : TorusFields.TorusBond (n * L) → ℍ[ℝ])
    (Y : TorusFields.TorusSite n) (i : Fin 4) {a : ℝ} (h0 : 0 ≤ a)
    (ha : ∀ e ∈ TorusContours.contourIndex L,
      ∀ b ∈ PathForms.pathBonds (TorusBlocks.blockCentreSite L Y) (BlockAverages.bondContour L e.1 e.2 i), ‖f b‖ ≤ a) :
    ‖PathForms.contourMean L f (Y, i)‖ ≤ 5 * L * a := by
  have hw := TorusContours.contourWeight_mul_card (L := L) hL
  have hw0 := TorusContours.contourWeight_nonneg L
  unfold PathForms.contourMean
  rw [norm_smul, Real.norm_of_nonneg hw0]
  have h1 : ∀ e ∈ TorusContours.contourIndex L, ‖PathForms.formPathSum f (TorusBlocks.blockCentreSite L Y)
      (BlockAverages.bondContour L e.1 e.2 i)‖ ≤ 5 * L * a := fun e he => by
    have h2 := norm_formPathSum_le f _ _ (ha e he)
    have h3 := TorusContours.length_bondContour_le hL (Finset.mem_product.mp he).1 e.2 i
    have h4 : ((BlockAverages.bondContour L e.1 e.2 i).length : ℝ) ≤ 5 * L := by exact_mod_cast h3
    exact h2.trans (mul_le_mul_of_nonneg_right h4 h0)
  have h2 := (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ h1)
  rw [nsmul_eq_mul] at h2
  calc _ ≤ TorusContours.contourWeight L * ((TorusContours.contourIndex L).card * (5 * L * a)) :=
        mul_le_mul_of_nonneg_left h2 hw0
    _ = 5 * L * a := by rw [← mul_assoc, hw, one_mul]
private theorem two_mul_supDist_blockCentreSite_add_one_le (hL : Odd L) (Y : TorusFields.TorusSite n)
    (x : TorusFields.TorusSite (n * L)) :
    2 * TorusFields.supDist (TorusBlocks.blockCentreSite L Y) x + 1 ≤
      L * (2 * TorusFields.supDist Y (TorusLumps.parentBlock L x) + 1) := by
  obtain ⟨o, ho, hx⟩ := TorusBlocks.exists_eq_blockCentreSite_add hL x
  obtain ⟨e, he, hb⟩ := TorusFields.exists_offset_of_supDist (TorusLumps.parentBlock L x) Y
  have key : TorusBlocks.blockCentreSite L Y = x + TorusFields.siteOfInt (fun i => (L : ℤ) * e i - o i) := by
    conv_lhs => rw [he, PathForms.blockCentreSite_add_siteOfInt]
    conv_rhs => rw [hx]
    funext k
    simp only [TorusFields.siteOfInt, Pi.add_apply]
    push_cast
    ring
  obtain ⟨q, hq⟩ := hL
  have hz : ((L : ℤ) - 1) / 2 = q := by
    subst hq
    push_cast
    omega
  have hm : TorusFields.supDist x (x + TorusFields.siteOfInt (fun i => (L : ℤ) * e i - o i)) ≤
      L * TorusFields.supDist Y (TorusLumps.parentBlock L x) + q := by
    refine TorusFields.supDist_add_siteOfInt_le x _ _ fun i => ?_
    have h1 := hb i
    rw [TorusFields.supDist_comm] at h1
    have h2 := ho i
    rw [hz] at h2
    have h3 : ((L : ℤ) * e i).natAbs ≤ L * TorusFields.supDist Y (TorusLumps.parentBlock L x) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.mul_le_mul_left _ h1
    have h4 := Int.natAbs_sub_le ((L : ℤ) * e i) (o i)
    have hLq : (L : ℤ) = 2 * q + 1 := by subst hq; push_cast; ring
    have h5 : (o i).natAbs ≤ q := by omega
    omega
  rw [key, TorusFields.supDist_comm]
  have e2 : L * (2 * TorusFields.supDist Y (TorusLumps.parentBlock L x) + 1) =
      2 * (L * TorusFields.supDist Y (TorusLumps.parentBlock L x)) + L := by ring
  rw [e2]
  omega
private theorem bond_near_ends_of_mem_contour (hL : Odd L) (Y : TorusFields.TorusSite n) (i : Fin 4)
    {e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)}
    (he : e ∈ TorusContours.contourIndex L) {b : TorusFields.TorusBond (n * L)}
    (hb : b ∈ PathForms.pathBonds (TorusBlocks.blockCentreSite L Y) (BlockAverages.bondContour L e.1 e.2 i)) :
    (TorusFields.supDist (TorusBlocks.blockCentreSite L Y) b.1 ≤ 3 * L ∧
        TorusFields.supDist (TorusBlocks.blockCentreSite L Y) (b.1 + TorusFields.unitStep (n * L) b.2) ≤ 3 * L) ∨
      (TorusFields.supDist (TorusBlocks.blockCentreSite L (Y + TorusFields.unitStep n i)) b.1 ≤ 3 * L ∧
        TorusFields.supDist (TorusBlocks.blockCentreSite L (Y + TorusFields.unitStep n i))
          (b.1 + TorusFields.unitStep (n * L) b.2) ≤ 3 * L) := by
  have hξ := (Finset.mem_product.mp he).1
  obtain ⟨q, hq⟩ := id hL
  have hleg : (BlockAverages.axisPath e.1 e.2).length ≤ 2 * L := by
    have hz : ((L : ℤ) - 1) / 2 = q := by
      subst hq
      push_cast
      omega
    have hbd : ∀ k, (e.1 k).natAbs ≤ q := fun k => by
      have := TorusContours.mem_centredCube_iff.mp hξ k
      rw [hz] at this
      omega
    have := TorusContours.length_axisPath_le e.1 e.2 hbd
    omega
  unfold BlockAverages.bondContour at hb
  rw [PathForms.pathBonds_append] at hb
  rcases List.mem_append.mp hb with hb | hb
  · left
    have := PathForms.supDist_le_length_of_mem_pathBonds _ _ hb
    simp only [List.length_append, List.length_replicate] at this
    omega
  · right
    have e1 : PathForms.pathEnd (TorusBlocks.blockCentreSite L Y)
        (BlockAverages.axisPath e.1 e.2 ++ List.replicate L (i, true)) =
        PathForms.pathEnd (TorusBlocks.blockCentreSite L (Y + TorusFields.unitStep n i))
          (BlockAverages.axisPath e.1 e.2) := by
      rw [PathForms.pathEnd_append, PathForms.pathEnd_axisPath, PathForms.pathEnd_replicate,
        PathForms.pathEnd_axisPath, PathForms.blockCentreSite_add_unitStep]
      abel
    rw [e1] at hb
    have := PathForms.supDist_le_length_of_mem_pathBonds _ _ (PathForms.mem_pathBonds_of_mem_reversePath _ _ hb)
    omega
end Levels
section Induction
private def liftedGauge (L : ℕ) :
    (d n : ℕ) → (TorusFields.TorusSite (WeightedResponses.fineSide L d n) → BlockAverages.UnitQuaternion) →
      TorusFields.TorusSite n → BlockAverages.UnitQuaternion
  | 0, _, g => g
  | d + 1, n, g => fun y => liftedGauge L d (n * L) g (TorusBlocks.blockCentreSite L y)
private theorem curvature_le_of_isGoodSample {ℓ : TorusLumps.StepParameters} {k s top : ℕ} {δ φ : ℝ} :
    ∀ (d n : ℕ) [NeZero n] (u : WeightedResponses.MarkedSample ℓ (k + d) n)
      (o : TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side d n)),
      BoxEvents.IsGoodSample ℓ k s top δ φ d n u o →
      ∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall (ResponseInTheExpansion.siteAbove ℓ.side d n o)
          ((BoxEvents.descendingRadius ℓ.side top (s - d) : ℕ) : ℝ)),
        TorusFields.curvature (WeightedResponses.topField ℓ (k + d) n u) p.1 p.2.1 p.2.2 ≤ δ
  | 0, _, _, _, _, h => h
  | _ + 1, _, _, _, _, h => h.1
variable {ℓ : TorusLumps.StepParameters} {k s top : ℕ} {δ φ E₀ η : ℝ}
private theorem coarse_link_deviation_step {n' : ℕ} [NeZero n'] (hL : Odd ℓ.side) (hL16 : 16 ≤ ℓ.side)
    (hσ : δ < ℓ.threshold) (hδ : 0 ≤ δ)
    (W : TorusFields.TorusField (n' * ℓ.side)) (V : TorusFields.TorusField n') (b : StepCosts.BaseChoice ℓ.side n')
    (g : TorusFields.TorusSite (n' * ℓ.side) → BlockAverages.UnitQuaternion)
    (oo : TorusFields.TorusSite (n' * ℓ.side))
    (ρ : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (hφ : 2 * φ ≤ δ ^ 2)
    (hsmall : 2 * (5 * ℓ.side * a) ^ 2 ≤ δ)
    (hbases : b ∈ TorusLumps.baseChoices ℓ (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n') 0 W))
    (hcold : ∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall oo ((ℓ.side * ρ + 4 * ℓ.side : ℕ) : ℝ)),
      TorusFields.curvature W p.1 p.2.1 p.2.2 ≤ δ)
    (hfit : ∀ c ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall (TorusLumps.parentBlock ℓ.side oo) (ρ : ℝ)),
      StepCosts.bondFit ℓ W V b c ≤ φ)
    (hsize : ∀ c ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall oo ((ℓ.side * ρ + 4 * ℓ.side : ℕ) : ℝ)),
      ‖PathForms.linkDeviation (TorusFields.gaugeTransform g W) c‖ ≤ a)
    {c : TorusFields.TorusBond n'}
    (hc : c ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall (TorusLumps.parentBlock ℓ.side oo) (ρ : ℝ))) :
    ‖PathForms.linkDeviation (TorusFields.gaugeTransform (fun y => g (TorusBlocks.blockCentreSite ℓ.side y)) V) c -
        PathForms.contourMean ℓ.side (PathForms.linkDeviation (TorusFields.gaugeTransform g W)) c‖ ≤ 2 * δ ∧
      ‖PathForms.contourMean ℓ.side (PathForms.linkDeviation (TorusFields.gaugeTransform g W)) c‖ ≤
        5 * ℓ.side * a := by
  obtain ⟨Y, i⟩ := c
  obtain ⟨-, hY1, hY2⟩ := Finset.mem_filter.mp hc
  have tY : TorusFields.supDist Y (TorusLumps.parentBlock ℓ.side oo) ≤ ρ := by
    have := (Finset.mem_filter.mp hY1).2
    exact_mod_cast this
  have tY2 : TorusFields.supDist (Y + TorusFields.unitStep n' i) (TorusLumps.parentBlock ℓ.side oo) ≤ ρ := by
    have := (Finset.mem_filter.mp hY2).2
    exact_mod_cast this
  have hf1 := two_mul_supDist_blockCentreSite_add_one_le hL Y oo
  have hf2 := two_mul_supDist_blockCentreSite_add_one_le hL (Y + TorusFields.unitStep n' i) oo
  have m1 : ℓ.side * (2 * TorusFields.supDist Y (TorusLumps.parentBlock ℓ.side oo) + 1) ≤
      2 * (ℓ.side * ρ) + ℓ.side := by
    calc _ ≤ ℓ.side * (2 * ρ + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have m2 : ℓ.side * (2 * TorusFields.supDist (Y + TorusFields.unitStep n' i) (TorusLumps.parentBlock ℓ.side oo) + 1) ≤
      2 * (ℓ.side * ρ) + ℓ.side := by
    calc _ ≤ ℓ.side * (2 * ρ + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have hnear : ∀ e ∈ TorusContours.contourIndex ℓ.side,
      ∀ c ∈ PathForms.pathBonds (TorusBlocks.blockCentreSite ℓ.side Y) (BlockAverages.bondContour ℓ.side e.1 e.2 i),
        c ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall oo ((ℓ.side * ρ + 4 * ℓ.side : ℕ) : ℝ)) :=
      fun e he c hcc => by
    have key : ∀ z : TorusFields.TorusSite (n' * ℓ.side),
        (TorusFields.supDist (TorusBlocks.blockCentreSite ℓ.side Y) z ≤ 3 * ℓ.side ∨
          TorusFields.supDist (TorusBlocks.blockCentreSite ℓ.side (Y + TorusFields.unitStep n' i)) z ≤ 3 * ℓ.side) →
        TorusFields.supDist z oo ≤ ℓ.side * ρ + 4 * ℓ.side := fun z hz => by
      rcases hz with hz | hz
      · have := TorusFields.supDist_triangle z (TorusBlocks.blockCentreSite ℓ.side Y) oo
        rw [TorusFields.supDist_comm z (TorusBlocks.blockCentreSite ℓ.side Y)] at this
        omega
      · have := TorusFields.supDist_triangle z (TorusBlocks.blockCentreSite ℓ.side (Y + TorusFields.unitStep n' i)) oo
        rw [TorusFields.supDist_comm z (TorusBlocks.blockCentreSite ℓ.side (Y + TorusFields.unitStep n' i))] at this
        omega
    rcases bond_near_ends_of_mem_contour hL Y i he hcc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact PathForms.mem_bondsWithin_of_mem (PathForms.mem_supBall_of_supDist_le (key _ (Or.inl h1)))
        (PathForms.mem_supBall_of_supDist_le (key _ (Or.inl h2)))
    · exact PathForms.mem_bondsWithin_of_mem (PathForms.mem_supBall_of_supDist_le (key _ (Or.inr h1)))
        (PathForms.mem_supBall_of_supDist_le (key _ (Or.inr h2)))
  have ha : ∀ e ∈ TorusContours.contourIndex ℓ.side,
      ∀ c ∈ PathForms.pathBonds (TorusBlocks.blockCentreSite ℓ.side Y) (BlockAverages.bondContour ℓ.side e.1 e.2 i),
        ‖PathForms.linkDeviation (TorusFields.gaugeTransform g W) c‖ ≤ a :=
    fun e he c hcc => hsize c (hnear e he c hcc)
  refine ⟨?_, norm_contourMean_le hL _ Y i ha0 ha⟩
  have hp1 : ∀ i, (TorusLumps.stepBlockFrame ℓ.side n').period (TorusLumps.stepBlockFrame ℓ.side n').top i = n' :=
    fun i => TorusContours.stepBlockFrame_period_one i
  have hend : StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n') (TorusLumps.stepBlockFrame ℓ.side n').top Y +
      BlockAverages.unitStep (TorusLumps.stepBlockFrame ℓ.side n').top i =
      StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n') (TorusLumps.stepBlockFrame ℓ.side n').top
        (Y + TorusFields.unitStep n' i) := by
    refine TopLevelSites.toTorusSite_injective hp1 ?_
    rw [TopLevelSites.toTorusSite_add hp1, TopLevelSites.toTorusSite_torusSiteInFrame hp1,
      TopLevelSites.toTorusSite_torusSiteInFrame hp1, TopLevelSites.toTorusSite_unitStep hp1]
  have l1 := nearbyLumps_eq_empty_of_cold (r := ℓ.side * ρ + 4 * ℓ.side) hσ hL hL16 W oo Y hcold (by omega)
  have l2 := nearbyLumps_eq_empty_of_cold (r := ℓ.side * ρ + 4 * ℓ.side) hσ hL hL16 W oo
    (Y + TorusFields.unitStep n' i) hcold (by omega)
  rw [← hend] at l2
  have hIs : LumpContours.IsBaseChoice ℓ.baseDepth (StepCosts.stepHotLumps ℓ W) b := by
    classical
    rw [TorusLumps.baseChoices, Finset.mem_filter] at hbases
    exact hbases.2
  have hb1 := (hIs _).1 (Or.inl l1)
  have hb2 := (hIs _).1 (Or.inl l2)
  have hfp := bondFit_eq_alignmentDefect hL W V b Y i l1 l2 hb1 hb2
  have hfc := hfit (Y, i) hc
  rw [hfp] at hfc
  have hs := linkDeviation_sub_contourMean_le hL W V g Y i ha0 hδ ha (by nlinarith)
  linarith
private theorem levelwise_bounds (hL : Odd ℓ.side) (hL16 : 16 ≤ ℓ.side) (hσ : δ < ℓ.threshold) (hδ : 0 ≤ δ)
    (hE₀ : δ ≤ E₀) (hφ : 2 * φ ≤ δ ^ 2)
    (hη : 0 ≤ η) (hsmall : ∀ d, d ≤ s → 2 * (5 * ℓ.side * ((6 * ℓ.side) ^ d * E₀)) ^ 2 ≤ δ) :
    ∀ (d n : ℕ) [NeZero n] (u : WeightedResponses.MarkedSample ℓ (k + d) n)
      (o : TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side d n))
      (g : TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side d n) → BlockAverages.UnitQuaternion)
      (B : TorusFields.TorusBond (WeightedResponses.fineSide ℓ.side d n) → ℍ[ℝ]),
      d ≤ s → BoxEvents.IsGoodSample ℓ k s top δ φ d n u o → BoxEvents.HasBaseChoices ℓ k d n u →
      (∀ b ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall o ((BoxEvents.descendingRadius ℓ.side top s : ℕ) : ℝ)),
        ‖PathForms.linkDeviation (TorusFields.gaugeTransform g
          (WeightedResponses.topField ℓ k _ (ResponseInTheExpansion.sampleBelow ℓ k d n u))) b‖ ≤ E₀) →
      (∀ b ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall o ((BoxEvents.descendingRadius ℓ.side top s : ℕ) : ℝ)),
        ‖(B - PathForms.linkDeviation (TorusFields.gaugeTransform g
          (WeightedResponses.topField ℓ k _ (ResponseInTheExpansion.sampleBelow ℓ k d n u)))) b‖ ≤ η) →
      (∀ b ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall (ResponseInTheExpansion.siteAbove ℓ.side d n o)
          ((BoxEvents.descendingRadius ℓ.side top (s - d) : ℕ) : ℝ)),
        ‖PathForms.linkDeviation (TorusFields.gaugeTransform (liftedGauge ℓ.side d n g)
          (WeightedResponses.topField ℓ (k + d) n u)) b‖ ≤ (6 * ℓ.side) ^ d * E₀) ∧
      ∀ (y : TorusFields.TorusSite n) (μ ν : Fin 4) (t : ℕ),
        TorusFields.supDist y (ResponseInTheExpansion.siteAbove ℓ.side d n o) + 2 * t ≤
          BoxEvents.descendingRadius ℓ.side top (s - d) →
        ‖PathForms.coarseBlockMean ℓ.side d n y μ ν t B -
            PathForms.squareCurlSum (PathForms.linkDeviation (TorusFields.gaugeTransform (liftedGauge ℓ.side d n g)
              (WeightedResponses.topField ℓ (k + d) n u))) t y μ ν‖ ≤
          t * ((ℓ.side : ℝ) ^ d * (4 * η) + 8 * δ * ((ℓ.side : ℝ) ^ d - 1)) := by
  intro d
  induction d with
  | zero =>
    intro n _ u o g B _ _ _ hE hB
    refine ⟨?_, ?_⟩
    · intro b hb
      rw [pow_zero, one_mul]
      exact hE b hb
    · intro y μ ν t ht
      rw [PathForms.coarseBlockMean_zero]
      have h1 := PathForms.norm_squareCurlSum_le (o := o) (y := y) (r := BoxEvents.descendingRadius ℓ.side top s)
        (t := t) μ ν hB ht
      have e := PathForms.squareCurlSum_sub (m := WeightedResponses.fineSide ℓ.side 0 n) B
        (PathForms.linkDeviation (TorusFields.gaugeTransform g (WeightedResponses.topField ℓ k
          (WeightedResponses.fineSide ℓ.side 0 n) (ResponseInTheExpansion.sampleBelow ℓ k 0 n u)))) t y μ ν
      refine (le_of_eq (congrArg norm e.symm)).trans (h1.trans (le_of_eq ?_))
      simp only [pow_zero]
      ring
  | succ d ih =>
    intro n _ u o g B hd hgood hbases hE hB
    have hd' : d ≤ s := by omega
    obtain ⟨hg1, hg2, hg3⟩ := hgood
    obtain ⟨hb1, hb2⟩ := hbases
    obtain ⟨I1, I2⟩ := ih (n * ℓ.side) u.1 o g B hd' hg3 hb2 hE hB
    have hρ' : BoxEvents.descendingRadius ℓ.side top (s - d) =
        ℓ.side * BoxEvents.descendingRadius ℓ.side top (s - (d + 1)) + 4 * ℓ.side := by
      have e : s - d = (s - (d + 1)) + 1 := by omega
      rw [e]
      rfl
    have hcold := curvature_le_of_isGoodSample d (n * ℓ.side) u.1 o hg3
    rw [hρ'] at I1 I2 hcold
    have hLpos : (0 : ℝ) < ℓ.side := by
      have : 16 ≤ (ℓ.side : ℝ) := by exact_mod_cast hL16
      linarith
    have hL1 : (16 : ℝ) ≤ ℓ.side := by exact_mod_cast hL16
    have h6 : (1 : ℝ) ≤ (6 * ℓ.side) ^ d := one_le_pow₀ (by linarith)
    have hE0 : 0 ≤ E₀ := hδ.trans hE₀
    have hδa : δ ≤ (6 * (ℓ.side : ℝ)) ^ d * E₀ := by nlinarith
    have ha0 : 0 ≤ (6 * (ℓ.side : ℝ)) ^ d * E₀ := hδ.trans hδa
    have hst : ∀ c ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall (ResponseInTheExpansion.siteAbove ℓ.side (d + 1) n o)
        ((BoxEvents.descendingRadius ℓ.side top (s - (d + 1)) : ℕ) : ℝ)), _ :=
      fun c hc => coarse_link_deviation_step (n' := n) (c := c) hL hL16 hσ hδ
        (WeightedResponses.topField ℓ (k + d) (n * ℓ.side) u.1) u.2.2.1 u.2.1
        (liftedGauge ℓ.side d (n * ℓ.side) g) (ResponseInTheExpansion.siteAbove ℓ.side d (n * ℓ.side) o)
        (BoxEvents.descendingRadius ℓ.side top (s - (d + 1))) ha0 hφ
        (hsmall d hd') hb1 hcold hg2 I1 hc
    refine ⟨?_, ?_⟩
    · intro c hc
      obtain ⟨s1, s2⟩ := hst c hc
      have h1 := norm_sub_norm_le
        (PathForms.linkDeviation (TorusFields.gaugeTransform (liftedGauge ℓ.side (d + 1) n g)
          (WeightedResponses.topField ℓ (k + (d + 1)) n u)) c)
        (PathForms.contourMean ℓ.side (PathForms.linkDeviation (TorusFields.gaugeTransform
          (liftedGauge ℓ.side d (n * ℓ.side) g) (WeightedResponses.topField ℓ (k + d) (n * ℓ.side) u.1))) c)
      have h2 : ‖PathForms.linkDeviation (TorusFields.gaugeTransform (liftedGauge ℓ.side (d + 1) n g)
            (WeightedResponses.topField ℓ (k + (d + 1)) n u)) c -
          PathForms.contourMean ℓ.side (PathForms.linkDeviation (TorusFields.gaugeTransform
            (liftedGauge ℓ.side d (n * ℓ.side) g) (WeightedResponses.topField ℓ (k + d) (n * ℓ.side) u.1))) c‖ ≤
          2 * δ := s1
      rw [pow_succ]
      nlinarith
    · intro y μ ν t ht
      have hz : ∀ ξ ∈ BlockAverages.centredCube ℓ.side,
          TorusFields.supDist (TorusBlocks.blockCentreSite ℓ.side y + TorusFields.siteOfInt ξ)
            (ResponseInTheExpansion.siteAbove ℓ.side d (n * ℓ.side) o) + 2 * (t * ℓ.side) ≤
          ℓ.side * BoxEvents.descendingRadius ℓ.side top (s - (d + 1)) + 4 * ℓ.side := fun ξ hξ => by
        have h1 := TorusBlocks.supDist_le_mul_supDist_parentBlock_add_one hL
          (TorusBlocks.blockCentreSite ℓ.side y + TorusFields.siteOfInt ξ)
          (ResponseInTheExpansion.siteAbove ℓ.side d (n * ℓ.side) o)
        rw [PathForms.parentBlock_blockCentreSite_add_of_mem hL y hξ] at h1
        have h2 : ℓ.side * (TorusFields.supDist y (TorusLumps.parentBlock ℓ.side
              (ResponseInTheExpansion.siteAbove ℓ.side d (n * ℓ.side) o)) + 1) + 2 * (t * ℓ.side) =
            ℓ.side * (TorusFields.supDist y (TorusLumps.parentBlock ℓ.side
              (ResponseInTheExpansion.siteAbove ℓ.side d (n * ℓ.side) o)) + 2 * t) + ℓ.side := by ring
        have h3 : ℓ.side * (TorusFields.supDist y (TorusLumps.parentBlock ℓ.side
              (ResponseInTheExpansion.siteAbove ℓ.side d (n * ℓ.side) o)) + 2 * t) ≤
            ℓ.side * BoxEvents.descendingRadius ℓ.side top (s - (d + 1)) := Nat.mul_le_mul_left _ ht
        omega
      have h1 := PathForms.norm_coarseBlockMean_succ_sub_le hL d y μ ν t B
        (PathForms.linkDeviation (TorusFields.gaugeTransform (liftedGauge ℓ.side d (n * ℓ.side) g)
          (WeightedResponses.topField ℓ (k + d) (n * ℓ.side) u.1)))
        (fun ξ hξ => I2 _ μ ν (t * ℓ.side) (hz ξ hξ))
      have h2 := PathForms.norm_squareCurlSum_le (o := ResponseInTheExpansion.siteAbove ℓ.side (d + 1) n o) (y := y)
        (r := BoxEvents.descendingRadius ℓ.side top (s - (d + 1))) (t := t)
        (f := PathForms.linkDeviation (TorusFields.gaugeTransform (liftedGauge ℓ.side (d + 1) n g)
            (WeightedResponses.topField ℓ (k + (d + 1)) n u)) -
          PathForms.contourMean ℓ.side (PathForms.linkDeviation (TorusFields.gaugeTransform
            (liftedGauge ℓ.side d (n * ℓ.side) g) (WeightedResponses.topField ℓ (k + d) (n * ℓ.side) u.1))))
        μ ν (fun c hc => (hst c hc).1) ht
      rw [PathForms.squareCurlSum_sub] at h2
      have e : PathForms.coarseBlockMean ℓ.side (d + 1) n y μ ν t B -
          PathForms.squareCurlSum (PathForms.linkDeviation (TorusFields.gaugeTransform
            (liftedGauge ℓ.side (d + 1) n g) (WeightedResponses.topField ℓ (k + (d + 1)) n u))) t y μ ν =
          (PathForms.coarseBlockMean ℓ.side (d + 1) n y μ ν t B - PathForms.squareCurlSum (PathForms.contourMean ℓ.side
            (PathForms.linkDeviation (TorusFields.gaugeTransform (liftedGauge ℓ.side d (n * ℓ.side) g)
              (WeightedResponses.topField ℓ (k + d) (n * ℓ.side) u.1)))) t y μ ν) -
          (PathForms.squareCurlSum (PathForms.linkDeviation (TorusFields.gaugeTransform
              (liftedGauge ℓ.side (d + 1) n g) (WeightedResponses.topField ℓ (k + (d + 1)) n u))) t y μ ν -
            PathForms.squareCurlSum (PathForms.contourMean ℓ.side
              (PathForms.linkDeviation (TorusFields.gaugeTransform (liftedGauge ℓ.side d (n * ℓ.side) g)
                (WeightedResponses.topField ℓ (k + d) (n * ℓ.side) u.1)))) t y μ ν) := by abel
      rw [e]
      refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans ?_)
      push_cast
      rw [pow_succ]
      have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      have hkey : 8 * δ * ((ℓ.side : ℝ) ^ d * ℓ.side - 1) - ℓ.side * (8 * δ * ((ℓ.side : ℝ) ^ d - 1)) - 8 * δ ≥ 0 := by
        have : 8 * δ * ((ℓ.side : ℝ) ^ d * ℓ.side - 1) - ℓ.side * (8 * δ * ((ℓ.side : ℝ) ^ d - 1)) - 8 * δ =
            8 * δ * (ℓ.side - 2) := by ring
        rw [this]
        exact mul_nonneg (by positivity) (by linarith)
      nlinarith [mul_nonneg ht0 hkey]
end Induction
section Floors
open Filter Topology
private theorem exists_coupling_floor (L : ℕ) (K σ κ₀ : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hσ : 0 < σ)
    (h1 : 1 / 27 ≤ κ₀) (h2 : κ₀ ≤ 1 / 21) :
    ∃ xs : ℝ, ∀ x, xs ≤ x → 1 < x ∧ 0 < BoxGaussian.boxScale x ∧ BoxGaussian.boxScale x < σ ∧
      BoxGaussian.boxScale x ≤ 1 ∧
      50 * (L : ℝ) ^ 5 * K ^ 2 * (BoxGaussian.boxRadius κ₀ x : ℝ) ^ 8 * BoxGaussian.boxScale x ≤ 1 ∧
      (13 : ℝ) ^ 3 * (L : ℝ) ^ 3 ≤ BoxGaussian.boxRadius κ₀ x ∧
      16 * (BoxGaussian.boxRadius κ₀ x : ℝ) < x ^ (1 / 10 : ℝ) := by
  set C : ℝ := 50 * (L : ℝ) ^ 5 * K ^ 2 * 2 ^ 9 with hC
  have hC0 : 0 < C := by positivity
  set c₂ : ℝ := min σ 1 / 4 with hc₂
  have hc₂0 : 0 < c₂ := by
    have : 0 < min σ 1 := lt_min hσ one_pos
    positivity
  have eA : ∀ᶠ x : ℝ in atTop, Real.log x ≤ C⁻¹ * x ^ (5 / 42 : ℝ) := by
    have := (isLittleO_log_rpow_atTop (r := 5 / 42) (by norm_num)).bound (inv_pos.mpr hC0)
    filter_upwards [this, eventually_gt_atTop 1] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)] at hx
    exact (le_abs_self _).trans hx
  have eB : ∀ᶠ x : ℝ in atTop, Real.log x ≤ c₂ * x ^ (1 / 2 : ℝ) := by
    have := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound hc₂0
    filter_upwards [this, eventually_gt_atTop 1] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)] at hx
    exact (le_abs_self _).trans hx
  have eC : ∀ᶠ x : ℝ in atTop, (13 : ℝ) ^ 3 * (L : ℝ) ^ 3 ≤ x ^ (1 / 27 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 27)).eventually_ge_atTop _
  have eD : ∀ᶠ x : ℝ in atTop, (33 : ℝ) ≤ x ^ (11 / 210 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 11 / 210)).eventually_ge_atTop _
  obtain ⟨xs, hxs⟩ := eventually_atTop.mp (eA.and (eB.and (eC.and (eD.and (eventually_gt_atTop 1)))))
  refine ⟨xs, fun x hx => ?_⟩
  obtain ⟨hA, hB, hC', hD, hx1⟩ := hxs x hx
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hhalf : x ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hx0]
    simp
  have hδ0 : 0 < BoxGaussian.boxScale x := by
    unfold BoxGaussian.boxScale
    positivity
  have hδ1 : BoxGaussian.boxScale x ≤ 2 * c₂ := by
    unfold BoxGaussian.boxScale
    calc 2 * x ^ (-(1 / 2 : ℝ)) * Real.log x ≤ 2 * x ^ (-(1 / 2 : ℝ)) * (c₂ * x ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = 2 * c₂ * (x ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 : ℝ)) := by ring
      _ = 2 * c₂ := by rw [hhalf, mul_one]
  have hmin1 : min σ 1 ≤ σ := min_le_left _ _
  have hmin2 : min σ 1 ≤ 1 := min_le_right _ _
  have hκ0 : 1 ≤ x ^ κ₀ := Real.one_le_rpow hx1.le (by linarith)
  have hRlo : x ^ κ₀ ≤ BoxGaussian.boxRadius κ₀ x := Nat.le_ceil _
  have hRhi : (BoxGaussian.boxRadius κ₀ x : ℝ) ≤ 2 * x ^ (1 / 21 : ℝ) := by
    have a1 : (BoxGaussian.boxRadius κ₀ x : ℝ) < x ^ κ₀ + 1 := Nat.ceil_lt_add_one (by linarith)
    have a2 : x ^ κ₀ ≤ x ^ (1 / 21 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le h2
    linarith
  refine ⟨hx1, hδ0, by linarith, by linarith, ?_, ?_, ?_⟩
  · have hR8 : (BoxGaussian.boxRadius κ₀ x : ℝ) ^ 8 ≤ 2 ^ 8 * x ^ (8 / 21 : ℝ) := by
      have : (BoxGaussian.boxRadius κ₀ x : ℝ) ^ 8 ≤ (2 * x ^ (1 / 21 : ℝ)) ^ 8 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hRhi 8
      refine this.trans (le_of_eq ?_)
      rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / 21 : ℝ)), ← Real.rpow_mul hx0.le]
      norm_num
    have hlogx : BoxGaussian.boxScale x ≤ 2 * x ^ (-(1 / 2 : ℝ)) * (C⁻¹ * x ^ (5 / 42 : ℝ)) := by
      unfold BoxGaussian.boxScale
      exact mul_le_mul_of_nonneg_left hA (by positivity)
    have hexp : x ^ (8 / 21 : ℝ) * (x ^ (-(1 / 2 : ℝ)) * x ^ (5 / 42 : ℝ)) = 1 := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      norm_num
    calc 50 * (L : ℝ) ^ 5 * K ^ 2 * (BoxGaussian.boxRadius κ₀ x : ℝ) ^ 8 * BoxGaussian.boxScale x
        ≤ 50 * (L : ℝ) ^ 5 * K ^ 2 * (2 ^ 8 * x ^ (8 / 21 : ℝ)) *
            (2 * x ^ (-(1 / 2 : ℝ)) * (C⁻¹ * x ^ (5 / 42 : ℝ))) := by
          gcongr
      _ = C * C⁻¹ * (x ^ (8 / 21 : ℝ) * (x ^ (-(1 / 2 : ℝ)) * x ^ (5 / 42 : ℝ))) := by
          rw [hC]
          ring
      _ = 1 := by rw [hexp, mul_one, mul_inv_cancel₀ hC0.ne']
  · have a1 : x ^ (1 / 27 : ℝ) ≤ x ^ κ₀ := Real.rpow_le_rpow_of_exponent_le hx1.le h1
    linarith
  · have e : x ^ (1 / 10 : ℝ) = x ^ (11 / 210 : ℝ) * x ^ (1 / 21 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [e]
    nlinarith
private theorem coarseningSteps_cube_le {L R : ℕ} (hL : 2 ≤ L) (hR : 1 ≤ R) :
    ((L : ℝ) ^ BoxGaussian.coarseningSteps L R) ^ 3 ≤ (L : ℝ) ^ 3 * (R : ℝ) ^ 2 := by
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  unfold BoxGaussian.coarseningSteps
  set s := sInf {s : ℕ | (R : ℝ) ^ (2 / 3 : ℝ) ≤ (L : ℝ) ^ s} with hs
  cases hs0 : s with
  | zero =>
    simp only [pow_zero, one_pow]
    have a1 : (1 : ℝ) ≤ (L : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    have a2 : (1 : ℝ) ≤ (R : ℝ) ^ 2 := one_le_pow₀ hRr
    nlinarith
  | succ s' =>
    have hlt : s' < sInf {s : ℕ | (R : ℝ) ^ (2 / 3 : ℝ) ≤ (L : ℝ) ^ s} := by omega
    have hnot := Nat.notMem_of_lt_sInf hlt
    have h1 : (L : ℝ) ^ s' < (R : ℝ) ^ (2 / 3 : ℝ) := not_le.mp hnot
    have h2 : (L : ℝ) ^ (s' + 1) ≤ L * (R : ℝ) ^ (2 / 3 : ℝ) := by
      rw [pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_left h1.le (by linarith)
    have h3 : ((R : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (R : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast ((R : ℝ) ^ (2 / 3 : ℝ)), ← Real.rpow_mul (by linarith)]
      norm_num
    calc _ ≤ ((L : ℝ) * (R : ℝ) ^ (2 / 3 : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
      _ = _ := by rw [mul_pow, h3]
private theorem descendingRadius_add_five_le {L : ℕ} (hL : 5 ≤ L) (top i : ℕ) :
    BoxEvents.descendingRadius L top i + 5 ≤ L ^ i * (top + 5) := by
  induction i with
  | zero => simp [BoxEvents.descendingRadius]
  | succ i ih =>
    have e : BoxEvents.descendingRadius L top (i + 1) = L * BoxEvents.descendingRadius L top i + 4 * L := rfl
    rw [e, pow_succ]
    have h2 : L * (BoxEvents.descendingRadius L top i + 5) ≤ L * (L ^ i * (top + 5)) := Nat.mul_le_mul_left _ ih
    have h3 : L ^ i * L * (top + 5) = L * (L ^ i * (top + 5)) := by ring
    rw [h3]
    nlinarith
end Floors
section Plaquettes
variable {m : ℕ}
private theorem curvature_gaugeTransform (g : TorusFields.TorusSite m → BlockAverages.UnitQuaternion)
    (W : TorusFields.TorusField m) (x : TorusFields.TorusSite m) (μ ν : Fin 4) :
    TorusFields.curvature (TorusFields.gaugeTransform g W) x μ ν = TorusFields.curvature W x μ ν := by apply _root_.YangMills.Construction.TorusFields.curvature_gaugeTransform <;> assumption
private def plaquetteLoop (μ ν : Fin 4) : List BlockAverages.PathStep :=
  [(μ, true), (ν, true), (μ, false), (ν, false)]
private theorem pathHolonomy_plaquetteLoop (W : TorusFields.TorusField m) (x : TorusFields.TorusSite m) (μ ν : Fin 4) :
    PathForms.pathHolonomy W x (plaquetteLoop μ ν) = TorusFields.holonomy W x μ ν := by
  have a1 : x + TorusFields.unitStep m μ + TorusFields.unitStep m ν + -TorusFields.unitStep m μ =
      x + TorusFields.unitStep m ν := by abel
  have a2 : x + TorusFields.unitStep m ν + -TorusFields.unitStep m ν = x := by abel
  have a3 : x + TorusFields.unitStep m μ + TorusFields.unitStep m ν - TorusFields.unitStep m μ =
      x + TorusFields.unitStep m ν := by abel
  have a4 : x + TorusFields.unitStep m ν - TorusFields.unitStep m ν = x := by abel
  simp only [plaquetteLoop, PathForms.pathHolonomy, PathForms.stepHolonomy, PathForms.stepShift, if_true,
    Bool.false_eq_true, if_false, a1, a2, a3, a4, mul_one, TorusFields.holonomy, mul_assoc]
private theorem formPathSum_plaquetteLoop (f : TorusFields.TorusBond m → ℍ[ℝ]) (x : TorusFields.TorusSite m)
    (μ ν : Fin 4) :
    PathForms.formPathSum f x (plaquetteLoop μ ν) = PathForms.formCurl f (x, μ, ν) := by
  have a1 : x + TorusFields.unitStep m μ + TorusFields.unitStep m ν + -TorusFields.unitStep m μ =
      x + TorusFields.unitStep m ν := by abel
  have a3 : x + TorusFields.unitStep m μ + TorusFields.unitStep m ν - TorusFields.unitStep m μ =
      x + TorusFields.unitStep m ν := by abel
  have a4 : x + TorusFields.unitStep m ν - TorusFields.unitStep m ν = x := by abel
  simp only [plaquetteLoop, PathForms.formPathSum, PathForms.stepForm, PathForms.stepShift, if_true,
    Bool.false_eq_true, if_false, a1, a3, a4, add_zero, PathForms.formCurl]
  abel
private theorem norm_formCurl_linkDeviation_le (W : TorusFields.TorusField m) (x : TorusFields.TorusSite m)
    (μ ν : Fin 4) {a : ℝ} (h0 : 0 ≤ a)
    (ha : ∀ b ∈ PathForms.pathBonds x (plaquetteLoop μ ν), ‖PathForms.linkDeviation W b‖ ≤ a) :
    ‖PathForms.formCurl (PathForms.linkDeviation W) (x, μ, ν)‖ ≤ TorusFields.curvature W x μ ν + (4 * a) ^ 2 := by
  have h := PathForms.norm_pathHolonomy_sub_one_sub_formPathSum_le W x (plaquetteLoop μ ν) h0 ha
  rw [pathHolonomy_plaquetteLoop, formPathSum_plaquetteLoop] at h
  have h4 : ((plaquetteLoop μ ν).length : ℝ) = 4 := by norm_num [plaquetteLoop]
  rw [h4] at h
  have := norm_sub_norm_le (PathForms.formCurl (PathForms.linkDeviation W) (x, μ, ν))
    (((TorusFields.holonomy W x μ ν : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1)
  rw [norm_sub_rev (PathForms.formCurl (PathForms.linkDeviation W) (x, μ, ν))] at this
  unfold TorusFields.curvature
  linarith
private theorem coe_lieFormCurl (F : TorusFields.TorusBond m → BlockAverages.imaginaryQuaternions)
    (p : TorusFields.TorusPlaquette m) :
    ((ResponseInTheExpansion.lieFormCurl F p : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) =
      PathForms.formCurl (fun b => ((F b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])) p := by
  simp [ResponseInTheExpansion.lieFormCurl, PathForms.formCurl]
private theorem coe_sum_blockWeight_smul_lieFormCurl {L s n : ℕ} [NeZero L] [NeZero n]
    (P : TorusFields.TorusPlaquette n) (hP : P.2.1 < P.2.2)
    (F : TorusFields.TorusBond (WeightedResponses.fineSide L s n) → BlockAverages.imaginaryQuaternions) :
    ((∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite (WeightedResponses.fineSide L s n))),
        BoxEvents.blockWeight L s P p • ResponseInTheExpansion.lieFormCurl F p : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) =
      PathForms.coarseBlockMean L s n P.1 P.2.1 P.2.2 1
        (fun b => ((F b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])) := by
  classical
  set G : TorusFields.TorusPlaquette (WeightedResponses.fineSide L s n) → ℍ[ℝ] :=
    PathForms.formCurl (fun b => ((F b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])) with hG
  have hq : ∀ (y : TorusFields.TorusSite (WeightedResponses.fineSide L s n)) (i j : ℕ),
      ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite (WeightedResponses.fineSide L s n))),
        (if p = (y + i • TorusFields.unitStep _ P.2.1 + j • TorusFields.unitStep _ P.2.2, P.2.1, P.2.2)
          then (1 : ℝ) else 0) • G p =
      G (y + i • TorusFields.unitStep _ P.2.1 + j • TorusFields.unitStep _ P.2.2, P.2.1, P.2.2) := fun y i j => by
    rw [Finset.sum_eq_single (y + i • TorusFields.unitStep _ P.2.1 + j • TorusFields.unitStep _ P.2.2, P.2.1, P.2.2)]
    · simp
    · intro p _ hp
      rw [if_neg hp, zero_smul]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP, fun _ _ => Finset.mem_univ _⟩) h
  rw [AddSubmonoidClass.coe_finset_sum]
  have h1 : ∀ p ∈ TorusFields.plaquettesIn
      (Finset.univ : Finset (TorusFields.TorusSite (WeightedResponses.fineSide L s n))),
      ((BoxEvents.blockWeight L s P p • ResponseInTheExpansion.lieFormCurl F p : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) =
        (1 / (L : ℝ) ^ (4 * s)) • ∑ y ∈ Finset.univ.filter
          (fun y : TorusFields.TorusSite (WeightedResponses.fineSide L s n) => ResponseInTheExpansion.siteAbove L s n y = P.1),
          ∑ i ∈ Finset.range (L ^ s), ∑ j ∈ Finset.range (L ^ s),
          (if p = (y + i • TorusFields.unitStep _ P.2.1 + j • TorusFields.unitStep _ P.2.2, P.2.1, P.2.2)
            then (1 : ℝ) else 0) • G p := fun p _ => by
    rw [Submodule.coe_smul, coe_lieFormCurl]
    unfold BoxEvents.blockWeight
    rw [mul_smul]
    simp only [Finset.sum_smul]
    rfl
  rw [Finset.sum_congr rfl h1, ← Finset.smul_sum, Finset.sum_comm]
  unfold PathForms.coarseBlockMean
  rw [one_div, one_mul]
  congr 1
  refine Finset.sum_congr (by ext y; simp) fun y _ => ?_
  unfold PathForms.squareCurlSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => hq y i j
end Plaquettes
set_option maxHeartbeats 1000000 in
private theorem circulation_bound_at {ℓ : TorusLumps.StepParameters} {k s n R : ℕ} [NeZero n] {δ φ K : ℝ}
    (hodd : Odd ℓ.side) (hL40 : 2 ^ 40 ≤ ℓ.side) (hK : 1 ≤ K) (hR : 1 ≤ R) (hδ0 : 0 < δ) (hδσ : δ < ℓ.threshold)
    (hφ : 2 * φ ≤ δ ^ 2)
    (hnum : 50 * (ℓ.side : ℝ) ^ 5 * K ^ 2 * (R : ℝ) ^ 8 * δ ≤ 1)
    (hΛ3 : ((ℓ.side : ℝ) ^ s) ^ 3 ≤ (ℓ.side : ℝ) ^ 3 * (R : ℝ) ^ 2) (h13 : 13 * ℓ.side ^ s ≤ R)
    (o : TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side s n))
    (A ζ v β' : TorusFields.TorusBond (WeightedResponses.fineSide ℓ.side s n) → BlockAverages.imaginaryQuaternions)
    (g : TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side s n) → BlockAverages.UnitQuaternion)
    (u : WeightedResponses.MarkedSample ℓ (k + s) n)
    (hv : ∀ b ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall o (2 * (R : ℝ))),
      TorusFields.gaugeTransform g (WeightedResponses.topField ℓ k _ (ResponseInTheExpansion.sampleBelow ℓ k s n u)) b.1 b.2 =
          BlockAverages.expUnit (v b) ∧ v b = A b + ζ b + β' b ∧
        ‖β' b‖ ≤ 2 * (‖A b‖ ^ 2 + ‖ζ b‖ ^ 2) ∧ ‖v b‖ ≤ K * (R : ℝ) ^ 3 * δ)
    (hA : ∀ b ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall o (2 * (R : ℝ))), ‖A b‖ ≤ 7 * R * δ)
    (hζ : ∀ b, ‖ζ b‖ ≤ K * (R : ℝ) ^ 3 * δ)
    (hgood : BoxEvents.IsGoodSample ℓ k s (BoxEvents.apexRadius ℓ.side s R) δ φ s n u o)
    (hbases : BoxEvents.HasBaseChoices ℓ k s n u)
    (P : TorusFields.TorusPlaquette n) (hP : P ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n)))
    (hnear : (ℓ.side : ℝ) ^ s * TorusFields.supDist P.1 (ResponseInTheExpansion.siteAbove ℓ.side s n o) ≤
      (R : ℝ) / 8 + 2 * (ℓ.side : ℝ) ^ s) :
    ‖∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side s n))),
        BoxEvents.blockWeight ℓ.side s P p • ResponseInTheExpansion.lieFormCurl (A + ζ) p‖ ≤
      12 * (ℓ.side : ℝ) ^ s * δ := by
  have hLr : (2 : ℝ) ^ 40 ≤ ℓ.side := by exact_mod_cast hL40
  have hL36 : (36 : ℝ) ≤ ℓ.side := by linarith
  have hL1 : (1 : ℝ) ≤ ℓ.side := by linarith
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hΛ1 : (1 : ℝ) ≤ (ℓ.side : ℝ) ^ s := one_le_pow₀ hL1
  set Λ : ℝ := (ℓ.side : ℝ) ^ s with hΛ
  set E₀ : ℝ := K * (R : ℝ) ^ 3 * δ with hE₀def
  set top := BoxEvents.apexRadius ℓ.side s R with htop
  have hR3 : (1 : ℝ) ≤ (R : ℝ) ^ 3 := one_le_pow₀ hRr
  have hδE : δ ≤ E₀ := by
    have : 1 ≤ K * (R : ℝ) ^ 3 := by nlinarith
    rw [hE₀def]
    nlinarith
  have hK2 : K ≤ K ^ 2 := by nlinarith
  have hR38 : (R : ℝ) ^ 3 ≤ (R : ℝ) ^ 8 := pow_le_pow_right₀ hRr (by norm_num)
  have hR68 : (R : ℝ) ^ 6 ≤ (R : ℝ) ^ 8 := pow_le_pow_right₀ hRr (by norm_num)
  set τ : ℝ := K ^ 2 * (R : ℝ) ^ 8 * δ with hτ
  have hτ0 : 0 < τ := by positivity
  have hL5 : (36 : ℝ) ≤ (ℓ.side : ℝ) ^ 5 := by
    have : (ℓ.side : ℝ) ^ 1 ≤ (ℓ.side : ℝ) ^ 5 := pow_le_pow_right₀ hL1 (by norm_num)
    linarith
  have hτ1 : 1800 * τ ≤ 1 := by nlinarith
  have hE₀τ : E₀ ≤ τ := by
    rw [hE₀def, hτ]
    have : K * (R : ℝ) ^ 3 ≤ K ^ 2 * (R : ℝ) ^ 8 := mul_le_mul hK2 hR38 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right this hδ0.le
  have hE₀1 : E₀ ≤ 1 := by linarith
  have hE₀sq : E₀ ^ 2 ≤ τ * δ := by
    have : E₀ ^ 2 = K ^ 2 * (R : ℝ) ^ 6 * δ * δ := by
      rw [hE₀def]
      ring
    rw [this, hτ]
    have h2 : K ^ 2 * (R : ℝ) ^ 6 ≤ K ^ 2 * (R : ℝ) ^ 8 := mul_le_mul_of_nonneg_left hR68 (by positivity)
    have h3 := mul_le_mul_of_nonneg_right h2 hδ0.le
    exact mul_le_mul_of_nonneg_right h3 hδ0.le
  have hRδ : (R : ℝ) * δ ≤ E₀ := by
    rw [hE₀def]
    have : (R : ℝ) ≤ K * (R : ℝ) ^ 3 := by
      have a1 : (R : ℝ) ^ 1 ≤ (R : ℝ) ^ 3 := pow_le_pow_right₀ hRr (by norm_num)
      nlinarith
    exact mul_le_mul_of_nonneg_right this hδ0.le
  have hsq : ((6 * (ℓ.side : ℝ)) ^ s) ^ 2 ≤ Λ ^ 3 := by
    have e : ((6 * (ℓ.side : ℝ)) ^ s) ^ 2 = (36 : ℝ) ^ s * Λ ^ 2 := by
      rw [hΛ, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm s 2, pow_mul (6 : ℝ)]
      norm_num
    rw [e]
    have h36 : (36 : ℝ) ^ s ≤ Λ := pow_le_pow_left₀ (by norm_num) hL36 s
    have : Λ ^ 3 = Λ * Λ ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h36 (by positivity)
  have hsmall : ∀ d, d ≤ s → 2 * (5 * (ℓ.side : ℝ) * ((6 * (ℓ.side : ℝ)) ^ d * E₀)) ^ 2 ≤ δ := fun d hd => by
    have a1 : (6 * (ℓ.side : ℝ)) ^ d ≤ (6 * (ℓ.side : ℝ)) ^ s := pow_le_pow_right₀ (by linarith) hd
    have a2 : ((6 * (ℓ.side : ℝ)) ^ d) ^ 2 ≤ (ℓ.side : ℝ) ^ 3 * (R : ℝ) ^ 2 :=
      ((pow_le_pow_left₀ (by positivity) a1 2).trans hsq).trans hΛ3
    have e : 2 * (5 * (ℓ.side : ℝ) * ((6 * (ℓ.side : ℝ)) ^ d * E₀)) ^ 2 =
        50 * (ℓ.side : ℝ) ^ 2 * ((6 * (ℓ.side : ℝ)) ^ d) ^ 2 * E₀ ^ 2 := by ring
    rw [e]
    calc _ ≤ 50 * (ℓ.side : ℝ) ^ 2 * ((ℓ.side : ℝ) ^ 3 * (R : ℝ) ^ 2) * E₀ ^ 2 := by gcongr
      _ = 50 * (ℓ.side : ℝ) ^ 5 * K ^ 2 * (R : ℝ) ^ 8 * δ * δ := by
        rw [hE₀def]
        ring
      _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hnum hδ0.le
      _ = δ := one_mul _
  have hρ : BoxEvents.descendingRadius ℓ.side top s ≤ 2 * R := by
    have r1 := descendingRadius_add_five_le (L := ℓ.side) (by omega) top s
    have e : ℓ.side ^ s * (top + 5) = ℓ.side ^ s * (R / (8 * ℓ.side ^ s)) + 13 * ℓ.side ^ s := by
      rw [htop]
      unfold BoxEvents.apexRadius
      ring
    have hd : ℓ.side ^ s * (R / (8 * ℓ.side ^ s)) ≤ R := by
      have h1 := Nat.div_mul_le_self R (8 * ℓ.side ^ s)
      have h2 : ℓ.side ^ s * (R / (8 * ℓ.side ^ s)) ≤ R / (8 * ℓ.side ^ s) * (8 * ℓ.side ^ s) := by
        nlinarith [Nat.zero_le (ℓ.side ^ s * (R / (8 * ℓ.side ^ s)))]
      omega
    omega
  have hsub : ∀ b ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall o
      ((BoxEvents.descendingRadius ℓ.side top s : ℕ) : ℝ)),
      b ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall o (2 * (R : ℝ))) := by
    have hρr : ((BoxEvents.descendingRadius ℓ.side top s : ℕ) : ℝ) ≤ 2 * R := by exact_mod_cast hρ
    have hin : ∀ z, z ∈ ResponseInTheExpansion.supBall o ((BoxEvents.descendingRadius ℓ.side top s : ℕ) : ℝ) →
        z ∈ ResponseInTheExpansion.supBall o (2 * (R : ℝ)) := fun z hz => by
      have := (Finset.mem_filter.mp hz).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this.trans hρr⟩
    intro b hb
    have := (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin _ this.1, hin _ this.2⟩
  have hcoe : ∀ w : BlockAverages.imaginaryQuaternions, ‖(w : ℍ[ℝ])‖ = ‖w‖ := fun w => rfl
  have hE : ∀ b ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall o
      ((BoxEvents.descendingRadius ℓ.side top s : ℕ) : ℝ)),
      ‖PathForms.linkDeviation (TorusFields.gaugeTransform g
        (WeightedResponses.topField ℓ k _ (ResponseInTheExpansion.sampleBelow ℓ k s n u))) b‖ ≤ E₀ := fun b hb => by
    obtain ⟨v1, -, -, v4⟩ := hv b (hsub b hb)
    unfold PathForms.linkDeviation
    rw [v1]
    exact (PlaquetteSecondDifference.norm_coe_expUnit_sub_one_le (v b)).trans v4
  have hB : ∀ b ∈ BoxGaussian.bondsWithin (ResponseInTheExpansion.supBall o
      ((BoxEvents.descendingRadius ℓ.side top s : ℕ) : ℝ)),
      ‖((fun b => (((A + ζ) b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])) -
        PathForms.linkDeviation (TorusFields.gaugeTransform g
          (WeightedResponses.topField ℓ k _ (ResponseInTheExpansion.sampleBelow ℓ k s n u)))) b‖ ≤
        101 * E₀ ^ 2 := fun b hb => by
    obtain ⟨v1, v2, v3, v4⟩ := hv b (hsub b hb)
    have hA' := hA b (hsub b hb)
    have hz' := hζ b
    have hv1 : ‖(v b : ℍ[ℝ])‖ ≤ 1 := by
      rw [hcoe]
      exact v4.trans hE₀1
    have h1 := PlaquetteSecondDifference.norm_expUnit_sub_one_sub_le hv1
    rw [hcoe] at h1
    have e : ((fun b => (((A + ζ) b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])) -
        PathForms.linkDeviation (TorusFields.gaugeTransform g
          (WeightedResponses.topField ℓ k _ (ResponseInTheExpansion.sampleBelow ℓ k s n u)))) b =
        -((((BlockAverages.expUnit (v b) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 - (v b : ℍ[ℝ])) +
          (β' b : ℍ[ℝ])) := by
      simp only [Pi.sub_apply, PathForms.linkDeviation, v1, v2, Pi.add_apply, Submodule.coe_add]
      abel
    rw [e, norm_neg]
    have h2 : ‖(β' b : ℍ[ℝ])‖ ≤ 2 * (‖A b‖ ^ 2 + ‖ζ b‖ ^ 2) := v3
    have h3 : ‖A b‖ ^ 2 ≤ 49 * E₀ ^ 2 := by
      have : ‖A b‖ ≤ 7 * E₀ := by nlinarith
      calc _ ≤ (7 * E₀) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
        _ = _ := by ring
    have h4 : ‖ζ b‖ ^ 2 ≤ E₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz' 2
    have h5 : ‖v b‖ ^ 2 ≤ E₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) v4 2
    refine (norm_add_le _ _).trans ?_
    linarith
  have hη : 0 ≤ 101 * E₀ ^ 2 := by positivity
  have hL16 : 16 ≤ ℓ.side := by omega
  obtain ⟨J1, J2⟩ := levelwise_bounds (ℓ := ℓ) (k := k) (s := s) (top := top) (δ := δ) (φ := φ) (E₀ := E₀)
    (η := 101 * E₀ ^ 2) hodd hL16 hδσ hδ0.le hδE hφ hη hsmall s n u o g
    (fun b => (((A + ζ) b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])) le_rfl hgood hbases hE hB
  have e0 : BoxEvents.descendingRadius ℓ.side top (s - s) = top := by
    rw [Nat.sub_self]
    rfl
  rw [e0] at J1 J2
  have hc := curvature_le_of_isGoodSample s n u o hgood
  rw [e0] at hc
  have hlt : P.2.1 < P.2.2 := (Finset.mem_filter.mp hP).2.1
  have htop1 : TorusFields.supDist P.1 (ResponseInTheExpansion.siteAbove ℓ.side s n o) + 4 ≤ top := by
    have key : (TorusFields.supDist P.1 (ResponseInTheExpansion.siteAbove ℓ.side s n o) - 2) * (8 * ℓ.side ^ s) ≤ R := by
      rcases Nat.lt_or_ge (TorusFields.supDist P.1 (ResponseInTheExpansion.siteAbove ℓ.side s n o)) 2 with h | h
      · rw [Nat.sub_eq_zero_of_le h.le, zero_mul]
        exact Nat.zero_le _
      · have hc' : (((TorusFields.supDist P.1 (ResponseInTheExpansion.siteAbove ℓ.side s n o) - 2) *
            (8 * ℓ.side ^ s) : ℕ) : ℝ) ≤ R := by
          rw [Nat.cast_mul, Nat.cast_sub h, Nat.cast_mul, Nat.cast_pow, ← hΛ]
          push_cast
          have : ((TorusFields.supDist P.1 (ResponseInTheExpansion.siteAbove ℓ.side s n o) : ℝ) - 2) * (8 * Λ) =
              8 * (Λ * (TorusFields.supDist P.1 (ResponseInTheExpansion.siteAbove ℓ.side s n o) : ℝ)) - 16 * Λ := by ring
          rw [this]
          linarith
        exact_mod_cast hc'
    have h2 : TorusFields.supDist P.1 (ResponseInTheExpansion.siteAbove ℓ.side s n o) - 2 ≤ R / (8 * ℓ.side ^ s) :=
      (Nat.le_div_iff_mul_le (by positivity)).mpr key
    rw [htop]
    unfold BoxEvents.apexRadius
    omega
  have ha0 : 0 ≤ (6 * (ℓ.side : ℝ)) ^ s * E₀ := by positivity
  have hbonds : ∀ b ∈ PathForms.pathBonds P.1 (plaquetteLoop P.2.1 P.2.2),
      ‖PathForms.linkDeviation (TorusFields.gaugeTransform (liftedGauge ℓ.side s n g)
        (WeightedResponses.topField ℓ (k + s) n u)) b‖ ≤ (6 * (ℓ.side : ℝ)) ^ s * E₀ := fun b hb => by
    have hn := PathForms.supDist_le_length_of_mem_pathBonds _ _ hb
    have hlen : (plaquetteLoop P.2.1 P.2.2).length = 4 := rfl
    rw [hlen] at hn
    refine J1 b (PathForms.mem_bondsWithin_of_mem (PathForms.mem_supBall_of_supDist_le ?_)
      (PathForms.mem_supBall_of_supDist_le ?_))
    · have := TorusFields.supDist_triangle b.1 P.1 (ResponseInTheExpansion.siteAbove ℓ.side s n o)
      rw [TorusFields.supDist_comm b.1 P.1] at this
      omega
    · have := TorusFields.supDist_triangle (b.1 + TorusFields.unitStep n b.2) P.1
        (ResponseInTheExpansion.siteAbove ℓ.side s n o)
      rw [TorusFields.supDist_comm (b.1 + TorusFields.unitStep n b.2) P.1] at this
      omega
  have hPb : ((P.1, P.2.1, P.2.2) : TorusFields.TorusPlaquette n) ∈
      TorusFields.plaquettesIn (ResponseInTheExpansion.supBall (ResponseInTheExpansion.siteAbove ℓ.side s n o) ((top : ℕ) : ℝ)) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, fun c hc' => PathForms.mem_supBall_of_supDist_le ?_⟩
    have b1 := supDist_le_two_of_mem_vertices _ _ _ hc'
    have := TorusFields.supDist_triangle c P.1 (ResponseInTheExpansion.siteAbove ℓ.side s n o)
    rw [TorusFields.supDist_comm c P.1] at this
    simp only at b1
    omega
  have hcv := hc _ hPb
  have hcurl := norm_formCurl_linkDeviation_le _ P.1 P.2.1 P.2.2 ha0 hbonds
  rw [curvature_gaugeTransform] at hcurl
  have hfin := J2 P.1 P.2.1 P.2.2 1 (by omega)
  have hsq1 : ∀ f : TorusFields.TorusBond n → ℍ[ℝ],
      PathForms.squareCurlSum f 1 P.1 P.2.1 P.2.2 = PathForms.formCurl f (P.1, P.2.1, P.2.2) := fun f => by
    simp [PathForms.squareCurlSum]
  rw [hsq1] at hfin
  have hbw := coe_sum_blockWeight_smul_lieFormCurl (L := ℓ.side) (s := s) (n := n) P hlt (A + ζ)
  have hnorm : ‖∑ p ∈ TorusFields.plaquettesIn
      (Finset.univ : Finset (TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side s n))),
      BoxEvents.blockWeight ℓ.side s P p • ResponseInTheExpansion.lieFormCurl (A + ζ) p‖ =
      ‖PathForms.coarseBlockMean ℓ.side s n P.1 P.2.1 P.2.2 1
        (fun b => (((A + ζ) b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]))‖ := by
    rw [← hbw]
    rfl
  rw [hnorm]
  have hsl := hsmall s le_rfl
  have h4a : (4 * ((6 * (ℓ.side : ℝ)) ^ s * E₀)) ^ 2 ≤ δ := by
    have : (4 * ((6 * (ℓ.side : ℝ)) ^ s * E₀)) ^ 2 ≤ 2 * (5 * (ℓ.side : ℝ) * ((6 * (ℓ.side : ℝ)) ^ s * E₀)) ^ 2 := by
      have a1 : (1 : ℝ) ≤ (ℓ.side : ℝ) ^ 2 := one_le_pow₀ hL1
      have a2 : 0 ≤ ((6 * (ℓ.side : ℝ)) ^ s * E₀) ^ 2 := by positivity
      have a3 : (16 : ℝ) ≤ 50 * (ℓ.side : ℝ) ^ 2 := by linarith
      have a4 := mul_le_mul_of_nonneg_right a3 a2
      calc _ = 16 * ((6 * (ℓ.side : ℝ)) ^ s * E₀) ^ 2 := by ring
        _ ≤ _ := a4
        _ = _ := by ring
    linarith
  have h404 : 4 * (101 * E₀ ^ 2) ≤ δ := by
    have a1 := mul_le_mul_of_nonneg_right hτ1 hδ0.le
    have a2 : 0 ≤ τ * δ := by positivity
    linarith
  have hΛδ : Λ * (4 * (101 * E₀ ^ 2)) ≤ Λ * δ := mul_le_mul_of_nonneg_left h404 (by linarith)
  have htri := norm_sub_norm_le (PathForms.coarseBlockMean ℓ.side s n P.1 P.2.1 P.2.2 1
      (fun b => (((A + ζ) b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])))
    (PathForms.formCurl (PathForms.linkDeviation (TorusFields.gaugeTransform (liftedGauge ℓ.side s n g)
      (WeightedResponses.topField ℓ (k + s) n u))) (P.1, P.2.1, P.2.2))
  have hfin' : ‖PathForms.coarseBlockMean ℓ.side s n P.1 P.2.1 P.2.2 1
        (fun b => (((A + ζ) b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])) -
      PathForms.formCurl (PathForms.linkDeviation (TorusFields.gaugeTransform (liftedGauge ℓ.side s n g)
        (WeightedResponses.topField ℓ (k + s) n u))) (P.1, P.2.1, P.2.2)‖ ≤
      Λ * (4 * (101 * E₀ ^ 2)) + 8 * δ * (Λ - 1) := by
    refine hfin.trans (le_of_eq ?_)
    push_cast
    rw [one_mul]
  have hΛδ1 : δ ≤ Λ * δ := le_mul_of_one_le_left hδ0.le hΛ1
  have e12 : 12 * Λ * δ = 12 * (Λ * δ) := by ring
  rw [e12]
  linarith
theorem circulationBoundStatement_proof (hBd : BoxGaussian.ellipsoidBoundsStatement) :
    BoxEvents.circulationBoundStatement := by
  intro a _
  refine ⟨2 ^ 40, fun _ => 1, fun _ => one_pos, ?_⟩
  intro Lt hLodd hL₀ Tb _ hTL hdrawn _
  subst hTL
  refine ⟨0, fun y _ _ _ => ?_⟩
  intro κ₀ h1 h2 C₀ hC₀
  obtain ⟨K, xs₁, hK, hb⟩ := hBd Tb hdrawn κ₀ h1 h2 C₀ hC₀
  obtain ⟨xs₂, hfl⟩ := exists_coupling_floor Tb.side K Tb.threshold κ₀ (by omega) hK hdrawn.σ_pos h1 h2
  refine ⟨max xs₁ xs₂, ?_⟩
  intro T β k s n _ o x R A ζ g u hD hx hR hs hAx hζ hCh hcold hgood hbases P hP hnear
  have hxfl : max xs₁ xs₂ ≤ x := by
    rw [hx]
    exact hD.le_coupling
  obtain ⟨hx1, hδ0, hδσ, hδ1, hnum, hR13, hR16⟩ := hfl x (le_trans (le_max_right _ _) hxfl)
  rw [← hR] at hnum hR13 hR16
  have hLn : 2 ^ 40 ≤ Tb.side := hL₀
  have hLr : (2 : ℝ) ^ 40 ≤ Tb.side := by exact_mod_cast hLn
  have hL1 : (1 : ℝ) ≤ Tb.side := by linarith [show (1 : ℝ) ≤ 2 ^ 40 by norm_num]
  have hRr : (1 : ℝ) ≤ R := by
    have a1 : (1 : ℝ) ≤ (Tb.side : ℝ) ^ 3 := one_le_pow₀ hL1
    nlinarith
  have hRn : 1 ≤ R := by exact_mod_cast hRr
  have hn16 : 16 * R < WeightedResponses.fineSide Tb.side s n := by
    have hw := hD.coupling_rpow_le
    rw [← hx] at hw
    have : (16 * (R : ℝ)) < (WeightedResponses.fineSide Tb.side s n : ℝ) := lt_of_lt_of_le hR16 hw
    exact_mod_cast this
  obtain ⟨-, hz⟩ := hb x R k (WeightedResponses.fineSide Tb.side s n) o A (le_trans (le_max_left _ _) hxfl) hR hn16 hAx
  obtain ⟨-, hζs, -, hWc⟩ := hz ζ hζ
  obtain ⟨v, β', hv, -, -, -⟩ := hWc _ hCh
  have hx0 : 0 < x := by linarith
  have hφ : 2 * (Real.log x ^ 2 / x) ≤ BoxGaussian.boxScale x ^ 2 := by
    have h3 : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
      rw [← Real.rpow_natCast (x ^ (-(1 / 2 : ℝ))), ← Real.rpow_mul hx0.le]
      norm_num
      exact Real.rpow_neg_one x
    have e : BoxGaussian.boxScale x ^ 2 = 4 * (Real.log x ^ 2 / x) := by
      unfold BoxGaussian.boxScale
      rw [mul_pow, mul_pow, h3]
      ring
    rw [e]
    have : 0 ≤ Real.log x ^ 2 / x := by positivity
    linarith
  have hΛ3 : ((Tb.side : ℝ) ^ s) ^ 3 ≤ (Tb.side : ℝ) ^ 3 * (R : ℝ) ^ 2 := by
    have := coarseningSteps_cube_le (L := Tb.side) (R := R) (by omega) hRn
    rwa [show BoxGaussian.coarseningSteps Tb.side R = s from hs.symm] at this
  have h13 : 13 * Tb.side ^ s ≤ R := by
    have a1 : (13 * (Tb.side : ℝ) ^ s) ^ 3 ≤ (R : ℝ) ^ 3 := by
      calc (13 * (Tb.side : ℝ) ^ s) ^ 3 = 13 ^ 3 * ((Tb.side : ℝ) ^ s) ^ 3 := by ring
        _ ≤ 13 ^ 3 * ((Tb.side : ℝ) ^ 3 * (R : ℝ) ^ 2) := by gcongr
        _ = (13 ^ 3 * (Tb.side : ℝ) ^ 3) * (R : ℝ) ^ 2 := by ring
        _ ≤ R * (R : ℝ) ^ 2 := by gcongr
        _ = (R : ℝ) ^ 3 := by ring
    have a2 : 13 * (Tb.side : ℝ) ^ s ≤ R :=
      (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp a1
    exact_mod_cast a2
  exact circulation_bound_at (ℓ := Tb.stepParameters y) (k := k) (s := s) (n := n) (R := R)
    (δ := BoxGaussian.boxScale x) (φ := Real.log x ^ 2 / x) (K := K) hLodd hLn hK hRn hδ0 hδσ hφ hnum hΛ3 h13
    o A ζ v β' g u hv (fun b hb => hAx.norm_le b hb) hζs hgood hbases P hP hnear
end YangMills.Construction.BoxEvents
end
