import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExponentsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexityFromAFloorAndRowsProof
import YangMills.Construction.ColdStepAtMirrorFrames.FreezingOfTheMeans
import YangMills.Construction.ColdStepAtMirrorFrames.MeansFrozenInValueProofForm
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfLocalTermsInValue
import YangMills.Construction.ColdStepAtMirrorFrames.SegmentOfConvexExponents
import YangMills.Construction.ColdStepAtMirrorFrames.TermsInFixedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.TermsOfTheStepOnTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.ScaledExponentIsTheExponentOfTheStepProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
noncomputable section
open YangMills.Construction.BlockAverages MeasureTheory
open scoped RealInnerProductSpace
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace LocalTerms
section Local
variable {ι 𝒞 : Type} [Fintype ι] [DecidableEq ι] {ρ x κ a a' : ℝ} {pl : ι → 𝒞} {D : 𝒞 → 𝒞 → ℝ} {Z : 𝒞}
structure IsLocalTerm (ρ x κ a : ℝ) (pl : ι → 𝒞) (D : 𝒞 → 𝒞 → ℝ) (g : BondField ι → ℝ) (Z : 𝒞) : Prop where
  smooth : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 g η
  slope : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm g b η ≤
    a * (x * Real.sqrt (weightedSqNormAt κ pl D Z η) + 1) * Real.exp (-(2 ^ 5 * κ * D Z (pl b)))
  second : ∀ η ∈ openPolyball ι ρ, ∀ (b b' : ι) (u u' : BondVector), ‖u‖ = 1 → ‖u'‖ = 1 →
    |secondDerivAlong g η (bondVariation b u) (bondVariation b' u')| ≤
      a * x * Real.exp (-(2 ^ 5 * κ * max (D Z (pl b)) (D Z (pl b'))))
theorem norm_le_of_mem_openPolyball {η : BondField ι} (h : η ∈ openPolyball ι ρ) : ∀ b, ‖η b‖ ≤ ρ :=
  fun b => (h b).le
theorem abs_fderiv_bondVariation_le (g : BondField ι → ℝ) (b : ι) (η : BondField ι) (w : BondVector) :
    |fderiv ℝ g η (bondVariation b w)| ≤ bondGradNorm g b η * ‖w‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.abs_fderiv_bondVariation_le <;> assumption
theorem bondGradNorm_le {g : BondField ι → ℝ} {b : ι} {η : BondField ι} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ w, |fderiv ℝ g η (bondVariation b w)| ≤ B * ‖w‖) : bondGradNorm g b η ≤ B := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.bondGradNorm_le_of_forall <;> assumption
theorem bondVariation_smul (b : ι) (c : ℝ) (u : BondVector) :
    bondVariation b (c • u) = c • bondVariation b u := by apply _root_.YangMills.SharedProofs.p169 <;> assumption
theorem bondGradNorm_le_of_unit {g : BondField ι → ℝ} {b : ι} {η : BondField ι} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ e : BondVector, ‖e‖ = 1 → |fderiv ℝ g η (bondVariation b e)| ≤ B) : bondGradNorm g b η ≤ B := by
  apply bondGradNorm_le hB
  intro w
  by_cases hw : w = 0
  · subst hw
    have : bondVariation b (0 : BondVector) = 0 := by simp [bondVariation]
    simp [this]
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have e1 : w = ‖w‖ • (‖w‖⁻¹ • w) := by
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  have h3 := h (‖w‖⁻¹ • w) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn])
  conv_lhs => rw [e1, bondVariation_smul, map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (norm_nonneg w)]
  calc _ ≤ ‖w‖ * B := by gcongr
    _ = _ := by ring
theorem differentiableAt_fderiv_apply {g : BondField ι → ℝ} {η : BondField ι} (hg : ContDiffAt ℝ 3 g η)
    (u : BondField ι) : DifferentiableAt ℝ (fun ζ => fderiv ℝ g ζ u) η := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.differentiableAt_fderiv_apply <;> assumption
theorem secondDerivAlong_linear_comb {g h : BondField ι → ℝ} {η : BondField ι} (hg : ContDiffAt ℝ 3 g η)
    (hh : ContDiffAt ℝ 3 h η) (c d : ℝ) (u v : BondField ι) :
    secondDerivAlong (fun ζ => c * g ζ + d * h ζ) η u v =
      c * secondDerivAlong g η u v + d * secondDerivAlong h η u v := by
  unfold secondDerivAlong
  have e1 : (fun ζ => fderiv ℝ (fun ζ => c * g ζ + d * h ζ) ζ u) =ᶠ[nhds η]
      fun ζ => c * fderiv ℝ g ζ u + d * fderiv ℝ h ζ u := by
    filter_upwards [hg.eventually (by simp), hh.eventually (by simp)] with ζ h1 h2
    have d1 : DifferentiableAt ℝ g ζ := h1.differentiableAt (by simp)
    have d2 : DifferentiableAt ℝ h ζ := h2.differentiableAt (by simp)
    have : HasFDerivAt (fun ζ => c * g ζ + d * h ζ) (c • fderiv ℝ g ζ + d • fderiv ℝ h ζ) ζ :=
      (d1.hasFDerivAt.const_mul c).add (d2.hasFDerivAt.const_mul d)
    rw [this.fderiv]
    simp
  rw [e1.fderiv_eq]
  have : HasFDerivAt (fun ζ => c * fderiv ℝ g ζ u + d * fderiv ℝ h ζ u)
      (c • fderiv ℝ (fun ζ => fderiv ℝ g ζ u) η + d • fderiv ℝ (fun ζ => fderiv ℝ h ζ u) η) η :=
    ((differentiableAt_fderiv_apply hg u).hasFDerivAt.const_mul c).add
      ((differentiableAt_fderiv_apply hh u).hasFDerivAt.const_mul d)
  rw [this.fderiv]
  simp
theorem IsLocalTerm.mono {g : BondField ι → ℝ} (hg : IsLocalTerm ρ x κ a pl D g Z) (hx : 0 ≤ x) (h : a ≤ a') :
    IsLocalTerm ρ x κ a' pl D g Z := by
  refine ⟨hg.smooth, fun η hη b => (hg.slope η hη b).trans ?_, fun η hη b b' u u' hu hu' =>
    (hg.second η hη b b' u u' hu hu').trans ?_⟩
  · have := Real.sqrt_nonneg (weightedSqNormAt κ pl D Z η)
    gcongr
  · gcongr
theorem IsLocalTerm.congr {g h : BondField ι → ℝ} (hg : IsLocalTerm ρ x κ a pl D g Z) (e : g = h) :
    IsLocalTerm ρ x κ a pl D h Z := e ▸ hg
theorem IsLocalTerm.linear_comb {g h : BondField ι → ℝ} (hρ : 0 < ρ) (hx : 0 ≤ x)
    (hg : IsLocalTerm ρ x κ a pl D g Z) (hh : IsLocalTerm ρ x κ a' pl D h Z) (c d : ℝ) :
    IsLocalTerm ρ x κ (|c| * a + |d| * a') pl D (fun η => c * g η + d * h η) Z := by
  refine ⟨fun η hη => (contDiffAt_const.mul (hg.smooth η hη)).add (contDiffAt_const.mul (hh.smooth η hη)),
    fun η hη b => ?_, fun η hη b b' u u' hu hu' => ?_⟩
  · have hgd : DifferentiableAt ℝ g η :=
      (hg.smooth η (norm_le_of_mem_openPolyball hη)).differentiableAt (by simp)
    have hhd : DifferentiableAt ℝ h η :=
      (hh.smooth η (norm_le_of_mem_openPolyball hη)).differentiableAt (by simp)
    have hf : HasFDerivAt (fun ζ => c * g ζ + d * h ζ) (c • fderiv ℝ g η + d • fderiv ℝ h η) η :=
      (hgd.hasFDerivAt.const_mul c).add (hhd.hasFDerivAt.const_mul d)
    set E := (x * Real.sqrt (weightedSqNormAt κ pl D Z η) + 1) * Real.exp (-(2 ^ 5 * κ * D Z (pl b))) with hE
    have h1 : bondGradNorm g b η ≤ a * E := by
      rw [hE, ← mul_assoc]
      exact hg.slope η hη b
    have h2 : bondGradNorm h b η ≤ a' * E := by
      rw [hE, ← mul_assoc]
      exact hh.slope η hη b
    have ha : 0 ≤ a * E := ((norm_nonneg _ : 0 ≤ bondGradNorm g b η)).trans h1
    have ha' : 0 ≤ a' * E := ((norm_nonneg _ : 0 ≤ bondGradNorm h b η)).trans h2
    have hB : (|c| * a + |d| * a') * (x * Real.sqrt (weightedSqNormAt κ pl D Z η) + 1) *
        Real.exp (-(2 ^ 5 * κ * D Z (pl b))) = |c| * (a * E) + |d| * (a' * E) := by
      rw [hE]; ring
    rw [hB]
    apply bondGradNorm_le (by positivity)
    intro w
    rw [hf.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have e1 := (abs_fderiv_bondVariation_le g b η w).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg w))
    have e2 := (abs_fderiv_bondVariation_le h b η w).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg w))
    calc _ ≤ |c * fderiv ℝ g η (bondVariation b w)| + |d * fderiv ℝ h η (bondVariation b w)| :=
          abs_add_le _ _
      _ = |c| * |fderiv ℝ g η (bondVariation b w)| + |d| * |fderiv ℝ h η (bondVariation b w)| := by
        rw [abs_mul, abs_mul]
      _ ≤ |c| * (a * E * ‖w‖) + |d| * (a' * E * ‖w‖) := by gcongr
      _ = _ := by ring
  · rw [secondDerivAlong_linear_comb (hg.smooth η (norm_le_of_mem_openPolyball hη))
      (hh.smooth η (norm_le_of_mem_openPolyball hη))]
    have e1 := hg.second η hη b b' u u' hu hu'
    have e2 := hh.second η hη b b' u u' hu hu'
    calc _ ≤ |c * secondDerivAlong g η (bondVariation b u) (bondVariation b' u')| +
          |d * secondDerivAlong h η (bondVariation b u) (bondVariation b' u')| := abs_add_le _ _
      _ = |c| * |secondDerivAlong g η (bondVariation b u) (bondVariation b' u')| +
          |d| * |secondDerivAlong h η (bondVariation b u) (bondVariation b' u')| := by
        rw [abs_mul, abs_mul]
      _ ≤ |c| * (a * x * Real.exp (-(2 ^ 5 * κ * max (D Z (pl b)) (D Z (pl b'))))) +
          |d| * (a' * x * Real.exp (-(2 ^ 5 * κ * max (D Z (pl b)) (D Z (pl b'))))) := by gcongr
      _ = _ := by ring
theorem isLocalTerm_zero (hx : 0 ≤ x) : IsLocalTerm ρ x κ 0 pl D (fun _ => (0 : ℝ)) Z := by
  refine ⟨fun _ _ => contDiffAt_const, fun η _ b => ?_, fun η _ b b' u u' _ _ => ?_⟩
  · simp [bondGradNorm]
  · simp [secondDerivAlong]
theorem IsLocalTerm.sum {α : Type} (hρ : 0 < ρ) (hx : 0 ≤ x) (ha : 0 ≤ a) (s : Finset α)
    (g : α → BondField ι → ℝ) (h : ∀ i ∈ s, IsLocalTerm ρ x κ a pl D (g i) Z) :
    IsLocalTerm ρ x κ (s.card * a) pl D (fun η => ∑ i ∈ s, g i η) Z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isLocalTerm_zero hx
  | insert i s hi ih =>
    have h1 := (h i (Finset.mem_insert_self i s)).linear_comb hρ hx
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)) 1 1
    have h2 := h1.congr (h := fun η => ∑ j ∈ insert i s, g j η) (by
      funext η
      simp [Finset.sum_insert hi])
    refine h2.mono hx (le_of_eq ?_)
    rw [Finset.card_insert_of_notMem hi]
    simp
    ring
end Local
section Concrete
variable {F : BlockFrame} {ρ x κ : ℝ}
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_self (y : F.Cell) : cellSupDist y y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem localSqNorm_eq (κ : ℝ) (Y : F.Cell) (η : StepVariable (finiteCells F)) :
    localSqNorm κ Y η = weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Y η := by
  unfold localSqNorm weightedSqNormAt chordBondCell cellDistReal
  exact Finset.sum_congr rfl fun b _ => by rw [cellSupDist_comm]
theorem leftTranslate_bondSpread_zero {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (W : F.GaugeField j) : leftTranslate (bondSpread c X 0) W = W := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
theorem bondDeriv_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ} (G : F.GaugeField j → E)
    (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p3568 <;> assumption
def emptyBonds {j : ℕ} : Fin 0 → F.Site j × Fin 4 := fun l => l.elim0
def emptyDirections : Fin 0 → imaginaryQuaternions := fun l => l.elim0
theorem areUnitVectors_empty : AreUnitVectors emptyDirections := fun l => l.elim0
theorem cellSupDist_le_bondSpanWithCell {k : ℕ} (Y z : F.Cell) (c : Fin k → F.Site F.top × Fin 4) :
    cellSupDist Y z ≤ bondSpanWithCell Y z c := by
  unfold bondSpanWithCell bondSpan
  refine le_max_of_le_left ?_
  have := Finset.le_sup (f := fun l : Fin (k + 1) => siteSupDist Y
    ((Fin.cons (z, 0) c : Fin (k + 1) → F.Site F.top × Fin 4) l).1) (Finset.mem_univ (0 : Fin (k + 1)))
  simpa [siteSupDist, cellSupDist] using this
theorem cellSupDist_le_chordBondSpan {k : ℕ} (Y : F.Cell) (b : Fin k → ↥(chordBonds (finiteCells F)))
    (l : Fin k) : cellSupDist Y (enclosingCell (b l).1.1) ≤ chordBondSpan Y b := by
  unfold chordBondSpan bondSpan
  refine le_max_of_le_left ?_
  have := Finset.le_sup (f := fun l : Fin k => siteSupDist Y (enclosingCell (b l).1.1 : F.Cell))
    (Finset.mem_univ l)
  simpa [siteSupDist, cellSupDist] using this
theorem exp_decay_le {κ : ℝ} (hκ : 0 ≤ κ) {d s : ℕ} (h : d ≤ s) :
    Real.exp (-(2 ^ 6 * κ * s)) ≤ Real.exp (-(2 ^ 5 * κ * d)) := by
  apply Real.exp_le_exp.mpr
  have h1 : (d : ℝ) ≤ s := by exact_mod_cast h
  have h2 : 0 ≤ (d : ℝ) := by positivity
  nlinarith [mul_nonneg hκ h2, mul_nonneg hκ (sub_nonneg.mpr h1)]
theorem exp_decay_le' {κ : ℝ} (hκ : 0 ≤ κ) {d s : ℕ} (h : d ≤ s) :
    Real.exp (-(2 ^ 5 * κ * s)) ≤ Real.exp (-(2 ^ 5 * κ * d)) := by
  apply Real.exp_le_exp.mpr
  have h1 : (d : ℝ) ≤ s := by exact_mod_cast h
  nlinarith [mul_nonneg hκ (sub_nonneg.mpr h1)]
theorem isLocalTerm_cellExponent {star : Bool} {a ρA C : ℝ} {m : ℕ} {V : F.GaugeField F.top} (hC : 0 ≤ C)
    (hκ : 0 ≤ κ) (hx : 0 ≤ x) (hE : CellExponentBounds star a ρA ρ x κ C m V) (Z : F.Cell) :
    IsLocalTerm ρ x κ C (chordBondCell F) (cellDistReal F) (cellExponent star a ρA x m Z V) Z := by
  refine ⟨fun η hη => ?_, fun η hη b => ?_, fun η hη b b' e e' he he' => ?_⟩
  · have h0 := hE.smooth Z η 0 emptyBonds emptyDirections hη
    have hm : ContDiffAt ℝ 3 (fun η' : StepVariable (finiteCells F) =>
        (((0 : Fin 0 → ℝ), η') : (Fin 0 → ℝ) × StepVariable (finiteCells F))) η :=
      contDiffAt_const.prodMk contDiffAt_id
    have hc := ContDiffAt.comp η h0 hm
    refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ζ => ?_)
    change cellExponent star a ρA x m Z V ζ = cellExponent star a ρA x m Z
      (leftTranslate (bondSpread emptyBonds emptyDirections (0 : Fin 0 → ℝ)) V) ζ
    rw [leftTranslate_bondSpread_zero]
  · have hB : 0 ≤ C * (x * Real.sqrt (weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Z η) + 1) *
        Real.exp (-(2 ^ 5 * κ * cellDistReal F Z (chordBondCell F b))) := by
      have := Real.sqrt_nonneg (weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Z η)
      have := (Real.exp_pos (-(2 ^ 5 * κ * cellDistReal F Z (chordBondCell F b)))).le
      positivity
    apply bondGradNorm_le_of_unit hB
    intro e he
    have h1 := hE.deriv_top_partial Z η b e 0 emptyBonds emptyDirections hη (by omega) areUnitVectors_empty he
    rw [bondDeriv_zero, localSqNorm_eq] at h1
    refine h1.trans ?_
    have h2 := exp_decay_le hκ (cellSupDist_le_bondSpanWithCell Z (enclosingCell b.1.1)
      (emptyBonds (F := F) (j := F.top)))
    have := Real.sqrt_nonneg (weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Z η)
    simp only [cellDistReal, chordBondCell]
    gcongr
  · have h1 := hE.second_deriv Z η b b' e e' hη he he'
    refine h1.trans ?_
    have m1 := cellSupDist_le_chordBondSpan Z ![b, b'] 0
    have m2 := cellSupDist_le_chordBondSpan Z ![b, b'] 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at m1 m2
    have h2 : max (cellSupDist Z (enclosingCell b.1.1)) (cellSupDist Z (enclosingCell b'.1.1)) ≤
        chordBondSpan Z ![b, b'] :=
      max_le m1 m2
    have h3 := exp_decay_le hκ h2
    have e1 : max (cellDistReal F Z (chordBondCell F b)) (cellDistReal F Z (chordBondCell F b')) =
        ((max (cellSupDist Z (enclosingCell b.1.1)) (cellSupDist Z (enclosingCell b'.1.1)) : ℕ) : ℝ) := by
      simp [cellDistReal, chordBondCell]
    rw [e1]
    gcongr
theorem isLocalTerm_centredExpansion {star : Bool} {a ρA δ E E₃ C : ℝ} {L m : ℕ} {f : LocalFamily}
    {V : F.GaugeField F.top} (hC : 0 ≤ C) (hE0 : 0 ≤ E) (hκ : 0 ≤ κ) (hx : 1 ≤ x)
    (hR : CentredExpansionBounds star a ρA ρ κ δ E E₃ C L m f V) (y : F.Site F.depth) :
    IsLocalTerm ρ x κ (C * E) (chordBondCell F) (cellDistReal F) (fun ζ => centredExpansion star a ρA m f y ζ V)
      (enclosingCell y) := by
  have hx0 : 0 ≤ x := by linarith
  refine ⟨fun η hη => ?_, fun η hη b => ?_, fun η hη b b' e e' he he' => ?_⟩
  · have h0 := hR.smooth y η 0 emptyBonds emptyDirections hη
    have hm : ContDiffAt ℝ 3 (fun η' : StepVariable (finiteCells F) =>
        (((0 : Fin 0 → ℝ), η') : (Fin 0 → ℝ) × StepVariable (finiteCells F))) η :=
      contDiffAt_const.prodMk contDiffAt_id
    have hc := ContDiffAt.comp η h0 hm
    refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ζ => ?_)
    change centredExpansion star a ρA m f y ζ V = centredExpansion star a ρA m f y ζ
      (leftTranslate (bondSpread emptyBonds emptyDirections (0 : Fin 0 → ℝ)) V)
    rw [leftTranslate_bondSpread_zero]
  · set u := Real.sqrt (weightedSqNormAt κ (chordBondCell F) (cellDistReal F) (enclosingCell y) η) with hu
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hB : 0 ≤ C * E * (x * u + 1) *
        Real.exp (-(2 ^ 5 * κ * cellDistReal F (enclosingCell y) (chordBondCell F b))) := by
      have := (Real.exp_pos (-(2 ^ 5 * κ * cellDistReal F (enclosingCell y) (chordBondCell F b)))).le
      positivity
    apply bondGradNorm_le_of_unit hB
    intro e he
    have h1 := hR.deriv_top_partial y η b e 0 emptyBonds emptyDirections hη (by omega) areUnitVectors_empty he
    rw [bondDeriv_zero] at h1
    simp only [show ((0 : ℕ) = 2) = False from by simp, if_false] at h1
    refine h1.trans ?_
    have h2 := exp_decay_le' hκ (cellSupDist_le_bondSpanWithCell (enclosingCell y) (enclosingCell b.1.1)
      (emptyBonds (F := F) (j := F.top)))
    have h3 : (1 : ℝ) ≤ x * u + 1 := by nlinarith [mul_nonneg hx0 hu0]
    simp only [cellDistReal, chordBondCell] at h2 ⊢
    calc _ ≤ C * E * Real.exp (-(2 ^ 5 * κ * cellSupDist (enclosingCell y) (enclosingCell b.1.1 : F.Cell))) := by
          gcongr
      _ ≤ C * E * (x * u + 1) *
          Real.exp (-(2 ^ 5 * κ * cellSupDist (enclosingCell y) (enclosingCell b.1.1 : F.Cell))) := by
          have := (Real.exp_pos (-(2 ^ 5 * κ * cellSupDist (enclosingCell y) (enclosingCell b.1.1 : F.Cell)))).le
          have h4 : 0 ≤ C * E := by positivity
          nlinarith [mul_nonneg (mul_nonneg h4 this) (sub_nonneg.mpr h3)]
  · have h1 := hR.second_deriv y η b b' e e' hη he he'
    refine h1.trans ?_
    have m1 := cellSupDist_le_chordBondSpan (enclosingCell y) ![b, b'] 0
    have m2 := cellSupDist_le_chordBondSpan (enclosingCell y) ![b, b'] 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at m1 m2
    have h2 : max (cellSupDist (enclosingCell y : F.Cell) (enclosingCell b.1.1))
        (cellSupDist (enclosingCell y : F.Cell) (enclosingCell b'.1.1)) ≤
        chordBondSpan (enclosingCell y) ![b, b'] := max_le m1 m2
    have h3 := exp_decay_le' hκ h2
    have e1 : max (cellDistReal F (enclosingCell y) (chordBondCell F b))
        (cellDistReal F (enclosingCell y) (chordBondCell F b')) =
        ((max (cellSupDist (enclosingCell y : F.Cell) (enclosingCell b.1.1))
          (cellSupDist (enclosingCell y : F.Cell) (enclosingCell b'.1.1)) : ℕ) : ℝ) := by
      simp [cellDistReal, chordBondCell]
    rw [e1]
    have h4 : 0 ≤ C * E := by positivity
    have h5 := (Real.exp_pos (-(2 ^ 5 * κ * ((max (cellSupDist (enclosingCell y : F.Cell) (enclosingCell b.1.1))
      (cellSupDist (enclosingCell y : F.Cell) (enclosingCell b'.1.1)) : ℕ) : ℝ)))).le
    calc _ ≤ C * E * Real.exp (-(2 ^ 5 * κ * ((max (cellSupDist (enclosingCell y : F.Cell) (enclosingCell b.1.1))
          (cellSupDist (enclosingCell y : F.Cell) (enclosingCell b'.1.1)) : ℕ) : ℝ))) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg h4 h5) (sub_nonneg.mpr hx)]
theorem card_sites_in_cell_le (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (Z : F.Cell) :
    ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Z).card ≤
      (centredCube F.blockSide).card := by
  classical
  obtain ⟨_, s2, _, _⟩ := hS F hL hs
  apply Finset.card_le_card_of_injOn (fun y => cellOffset y)
  · intro y _
    exact (s2 y).2
  · intro y hy y' hy' he
    have h1 : enclosingCell y = Z := (Finset.mem_filter.mp hy).2
    have h2 : enclosingCell y' = Z := (Finset.mem_filter.mp hy').2
    have e1 := (s2 y).1
    have e2 := (s2 y').1
    simp only at he
    rw [← e1, ← e2, h1, h2, he]
theorem isLocalTerm_cellCentredExpansion {star : Bool} {a ρA δ E E₃ C : ℝ} {L m : ℕ} {f : LocalFamily}
    {V : F.GaugeField F.top} (hρ : 0 < ρ) (hS : SiteDecomposition) (hO : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (hC : 0 ≤ C) (hE0 : 0 ≤ E) (hκ : 0 ≤ κ) (hx : 1 ≤ x)
    (hR : CentredExpansionBounds star a ρA ρ κ δ E E₃ C L m f V) (Z : F.Cell) :
    IsLocalTerm ρ x κ ((centredCube F.blockSide).card * (C * E)) (chordBondCell F) (cellDistReal F)
      (fun η => cellCentredExpansion star a ρA m f Z η V) Z := by
  classical
  have hx0 : 0 ≤ x := by linarith
  have h1 := IsLocalTerm.sum (Z := Z) hρ hx0 (mul_nonneg hC hE0)
    ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Z)
    (fun y ζ => centredExpansion star a ρA m f y ζ V) (fun y hy => by
      have := isLocalTerm_centredExpansion hC hE0 hκ hx hR y
      rwa [(Finset.mem_filter.mp hy).2] at this)
  refine (h1.congr ?_).mono hx0 ?_
  · funext η
    unfold cellCentredExpansion
    congr
  · apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC hE0)
    exact_mod_cast card_sites_in_cell_le hS hO hs Z
def bondPairing {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι) (u : BondField ι) :
    BondField ι →L[ℝ] ℝ :=
  ∑ b ∈ S, (innerSL ℝ (u b)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b)
theorem bondPairing_apply {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι) (u v : BondField ι) :
    bondPairing S u v = ∑ b ∈ S, ⟪u b, v b⟫ := by
  simp [bondPairing, ContinuousLinearMap.sum_apply]
theorem hasFDerivAt_weightedSqSum {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι) (c : ℝ)
    (η : BondField ι) :
    HasFDerivAt (fun ζ : BondField ι => c * ∑ b ∈ S, ‖ζ b‖ ^ 2) ((2 * c) • bondPairing S η) η := by
  have h1 : ∀ b, HasFDerivAt (fun ζ : BondField ι => ‖ζ b‖ ^ 2)
      ((2 : ℝ) • (innerSL ℝ (η b)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b)) η := fun b => by
    have := (hasStrictFDerivAt_norm_sq (η b)).hasFDerivAt.comp η
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).hasFDerivAt
    refine HasFDerivAt.congr_fderiv this ?_
    ext v
    simp
  have h2 := (HasFDerivAt.fun_sum (u := S) fun b _ => h1 b).const_mul c
  refine HasFDerivAt.congr_fderiv h2 ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, bondPairing_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring
theorem secondDerivAlong_weightedSqSum {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι) (c : ℝ)
    (η u v : BondField ι) :
    secondDerivAlong (fun ζ : BondField ι => c * ∑ b ∈ S, ‖ζ b‖ ^ 2) η u v =
      2 * c * ∑ b ∈ S, ⟪u b, v b⟫ := by
  unfold secondDerivAlong
  have h : (fun ζ => fderiv ℝ (fun ζ : BondField ι => c * ∑ b ∈ S, ‖ζ b‖ ^ 2) ζ u) =
      fun ζ => ((2 * c) • bondPairing S u) ζ := by
    funext ζ
    rw [(hasFDerivAt_weightedSqSum S c ζ).fderiv]
    simp only [ContinuousLinearMap.smul_apply, bondPairing_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun b _ => real_inner_comm _ _
  rw [h, ContinuousLinearMap.fderiv]
  simp [bondPairing_apply]
theorem sum_inner_bondVariation {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι) (b b' : ι)
    (p q : BondVector) :
    ∑ c ∈ S, ⟪bondVariation b p c, bondVariation b' q c⟫ = if b ∈ S ∧ b = b' then ⟪p, q⟫ else 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.sum_inner_bondVariation_eq <;> assumption
theorem sum_inner_bondVariation_right {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι) (η : BondField ι)
    (b : ι) (e : BondVector) :
    ∑ c ∈ S, ⟪η c, bondVariation b e c⟫ = if b ∈ S then ⟪η b, e⟫ else 0 := by
  by_cases hb : b ∈ S
  · rw [if_pos hb, Finset.sum_eq_single b]
    · simp [bondVariation]
    · intro c _ hc
      simp [bondVariation, hc]
    · exact fun h => absurd hb h
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro c hc
    have : c ≠ b := fun h => hb (h ▸ hc)
    simp [bondVariation, this]
open Classical in
def bondsOfCell (Z : F.Cell) : Finset ↥(chordBonds (finiteCells F)) :=
  Finset.univ.filter fun b => enclosingCell b.1.1 = Z
theorem cellQuadratic_eq (lam x : ℝ) (Z : F.Cell) :
    cellQuadratic lam x Z = fun η : StepVariable (finiteCells F) =>
      (x * lam / 2) * ∑ b ∈ bondsOfCell Z, ‖η b‖ ^ 2 := by
  classical
  funext η
  unfold cellQuadratic bondsOfCell
  rw [Finset.sum_filter, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by split_ifs <;> simp
theorem isLocalTerm_cellQuadratic {lam : ℝ} (hl : 0 ≤ lam) (hx : 0 ≤ x) (Z : F.Cell) :
    IsLocalTerm ρ x κ lam (chordBondCell F) (cellDistReal F) (cellQuadratic lam x Z) Z := by
  have hD : ∀ b ∈ bondsOfCell (F := F) Z, cellDistReal F Z (chordBondCell F b) = 0 := fun b hb => by
    have : enclosingCell b.1.1 = Z := (Finset.mem_filter.mp hb).2
    simp [cellDistReal, chordBondCell, this, cellSupDist_self]
  rw [cellQuadratic_eq]
  refine ⟨fun η _ => ?_, fun η hη b => ?_, fun η hη b b' u u' hu hu' => ?_⟩
  · apply ContDiff.contDiffAt
    apply contDiff_const.mul
    apply ContDiff.sum
    intro b _
    exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ BondVector b)
  · set s := weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Z η with hs
    have hB : 0 ≤ lam * (x * Real.sqrt s + 1) *
        Real.exp (-(2 ^ 5 * κ * cellDistReal F Z (chordBondCell F b))) := by
      have := Real.sqrt_nonneg s
      have := (Real.exp_pos (-(2 ^ 5 * κ * cellDistReal F Z (chordBondCell F b)))).le
      positivity
    apply bondGradNorm_le_of_unit hB
    intro e he
    rw [(hasFDerivAt_weightedSqSum _ _ η).fderiv]
    simp only [ContinuousLinearMap.smul_apply, bondPairing_apply, smul_eq_mul]
    rw [sum_inner_bondVariation_right]
    by_cases hb : b ∈ bondsOfCell (F := F) Z
    · rw [if_pos hb, hD b hb]
      have h3 : ‖η b‖ ≤ Real.sqrt s := by
        apply Real.le_sqrt_of_sq_le
        have h4 := Finset.single_le_sum (f := fun d =>
          Real.exp (-(2 ^ 6 * κ * cellDistReal F Z (chordBondCell F d))) * ‖η d‖ ^ 2)
          (fun d _ => mul_nonneg (Real.exp_pos _).le (by positivity)) (Finset.mem_univ b)
        have e0 : Real.exp (-(2 ^ 6 * κ * cellDistReal F Z (chordBondCell F b))) * ‖η b‖ ^ 2 = ‖η b‖ ^ 2 := by
          rw [hD b hb]
          simp
        rw [← e0]
        exact h4
      have h5 := abs_real_inner_le_norm (η b) e
      rw [he, mul_one] at h5
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (x * lam / 2))]
      simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
      calc _ ≤ 2 * (x * lam / 2) * ‖η b‖ := by gcongr
        _ ≤ 2 * (x * lam / 2) * Real.sqrt s := by gcongr
        _ ≤ lam * (x * Real.sqrt s + 1) := by
          have := Real.sqrt_nonneg s
          nlinarith
    · rw [if_neg hb]
      simpa using hB
  · rw [secondDerivAlong_weightedSqSum, sum_inner_bondVariation]
    by_cases hb : b ∈ bondsOfCell (F := F) Z ∧ b = b'
    · obtain ⟨hb1, rfl⟩ := hb
      rw [if_pos ⟨hb1, rfl⟩, hD b hb1]
      have h5 := abs_real_inner_le_norm u u'
      rw [hu, hu', mul_one] at h5
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (x * lam / 2))]
      simp only [max_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
      calc _ ≤ 2 * (x * lam / 2) * 1 := by gcongr
        _ = _ := by ring
    · rw [if_neg hb]
      have := (Real.exp_pos (-(2 ^ 5 * κ * max (cellDistReal F Z (chordBondCell F b))
        (cellDistReal F Z (chordBondCell F b'))))).le
      simp only [mul_zero, abs_zero]
      positivity
end Concrete
section Parameters
def placementConstant (hCB : commonBondsOfTwoTori) (L : ℕ) (κ : ℝ) : ℝ :=
  open Classical in if h : Odd L ∧ 0 < κ then ((hCB L h.1).1 κ h.2).choose else 0
def comparisonConstant (hLoc : LocalExpectationComparisonInValue) (S lam : ℝ) : ℝ :=
  open Classical in if h : 0 < lam then (hLoc S lam h).choose else 0
def firstAmplitude (Ct lam : ℝ) : ℝ := 1 + Ct + lam
def secondAmplitude (L : ℕ) (Ct E : ℝ) : ℝ := 1 + Ct + ((centredCube L).card : ℝ) * (Ct * E) + E
def constantFloor (C A ε₀ κ : ℝ) (nss : ℕ) : ℝ :=
  |C| * (A ^ 2 + A * ε₀) + 2 * |C| * A * Real.exp (κ * nss / 2 ^ 7)
def ConstantFloors (hLoc : LocalExpectationComparisonInValue) (hCB : commonBondsOfTwoTori)
    (T : StepParameters) : Prop :=
  constantFloor (comparisonConstant hLoc (placementConstant hCB T.L T.κ) T.chainParams.lam)
    (firstAmplitude T.Ct T.chainParams.lam)
    (T.Ct * (1 + |placementConstant hCB T.L T.κ|)) T.κ T.blockIndex ≤ T.Cs ∧
  constantFloor (comparisonConstant hLoc (placementConstant hCB T.L T.κ) T.chainParams.lam)
    (secondAmplitude T.L T.Ct T.E)
    (T.Ct * (1 + T.energyRatio) * (1 + |placementConstant hCB T.L T.κ|)) T.κ T.blockIndex ≤ T.CE ∧
  1 ≤ T.coupling ∧ 2 ≤ T.n₀ ∧ 1 ≤ T.Ct
theorem eventually_constantFloors (hLoc : LocalExpectationComparisonInValue)
    (hCB : commonBondsOfTwoTori) : EventuallyInParameters (ConstantFloors hLoc hCB) := by
  intro a _
  refine ⟨0, fun L _ _ c _ => ⟨1, fun Ct hCt => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun nss _ => ⟨1, one_pos, fun σ _ _ p _ => ⟨constantFloor (comparisonConstant hLoc
      (placementConstant hCB L κ) c.lam) (firstAmplitude Ct c.lam) (Ct * (1 + |placementConstant hCB L κ|)) κ nss,
      fun Cs hCs E _ => ⟨2, fun n₀ hn =>
        ⟨constantFloor (comparisonConstant hLoc (placementConstant hCB L κ) c.lam) (secondAmplitude L Ct E)
          (Ct * (1 + E / η₃) * (1 + |placementConstant hCB L κ|)) κ nss, fun CE hCE =>
            ⟨1, fun y hy => ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  exact ⟨hCs, hCE, hy, hn, hCt⟩
theorem abs_sub_le_of_near_or_far {C A ε₀ κ Cs m m' : ℝ} {nss r : ℕ} (hκ : 0 < κ) (hA : 0 ≤ A)
    (hε : 0 ≤ ε₀)
    (hfar : nss ≤ r → |m - m'| ≤ C * (A ^ 2 * Real.exp (-(κ * r / 2 ^ 4)) +
      A * (ε₀ * Real.exp (-(κ * r)))))
    (hm : |m| ≤ C * A) (hm' : |m'| ≤ C * A) (hCs : constantFloor C A ε₀ κ nss ≤ Cs) :
    |m - m'| ≤ Cs * Real.exp (-(κ * r / 2 ^ 7)) := by
  set E := Real.exp (-(κ * r / 2 ^ 7)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have hκr : 0 ≤ κ * r := by positivity
  have hterm : 0 ≤ |C| * (A ^ 2 + A * ε₀) := by positivity
  have hterm2 : 0 ≤ 2 * |C| * A * Real.exp (κ * nss / 2 ^ 7) := by positivity
  by_cases h : nss ≤ r
  · have h1 := hfar h
    have e1 : Real.exp (-(κ * r / 2 ^ 4)) ≤ E := Real.exp_le_exp.mpr (by nlinarith)
    have e2 : Real.exp (-(κ * r)) ≤ E := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : C * (A ^ 2 * Real.exp (-(κ * r / 2 ^ 4)) + A * (ε₀ * Real.exp (-(κ * r)))) ≤
        |C| * ((A ^ 2 + A * ε₀) * E) := by
      have hp : 0 ≤ A ^ 2 * Real.exp (-(κ * r / 2 ^ 4)) + A * (ε₀ * Real.exp (-(κ * r))) := by
        positivity
      refine (mul_le_mul_of_nonneg_right (le_abs_self C) hp).trans ?_
      apply mul_le_mul_of_nonneg_left _ hC0
      have : A ^ 2 * Real.exp (-(κ * r / 2 ^ 4)) ≤ A ^ 2 * E := by gcongr
      have : A * (ε₀ * Real.exp (-(κ * r))) ≤ A * (ε₀ * E) := by gcongr
      nlinarith
    have h3 : |C| * (A ^ 2 + A * ε₀) ≤ Cs := by
      unfold constantFloor at hCs
      linarith
    calc |m - m'| ≤ |C| * ((A ^ 2 + A * ε₀) * E) := h1.trans h2
      _ = (|C| * (A ^ 2 + A * ε₀)) * E := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 hE0.le
  · have hlt : (r : ℝ) ≤ nss := by
      have : r ≤ nss := by omega
      exact_mod_cast this
    have h1 : |m - m'| ≤ 2 * (|C| * A) := by
      have a1 : C * A ≤ |C| * A := mul_le_mul_of_nonneg_right (le_abs_self C) hA
      have := abs_sub m m'
      linarith
    have h2 : 1 ≤ Real.exp (κ * nss / 2 ^ 7) * E := by
      rw [hE, ← Real.exp_add]
      apply Real.one_le_exp
      have : κ * r ≤ κ * nss := mul_le_mul_of_nonneg_left hlt hκ.le
      have e : κ * nss / 2 ^ 7 + -(κ * r / 2 ^ 7) = (κ * nss - κ * r) / 2 ^ 7 := by ring
      rw [e]
      apply div_nonneg <;> linarith [this]
    have h3 : 2 * |C| * A * Real.exp (κ * nss / 2 ^ 7) ≤ Cs := by
      unfold constantFloor at hCs
      linarith
    have hp : 0 ≤ 2 * (|C| * A) := by positivity
    calc _ ≤ 2 * (|C| * A) * 1 := by linarith
      _ ≤ 2 * (|C| * A) * (Real.exp (κ * nss / 2 ^ 7) * E) := mul_le_mul_of_nonneg_left h2 hp
      _ = (2 * |C| * A * Real.exp (κ * nss / 2 ^ 7)) * E := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 hE0.le
end Parameters
section Sums
variable {F : BlockFrame} [Fintype F.Cell]
theorem finiteCells_eq_univ : finiteCells F = Finset.univ := by
  unfold finiteCells
  rw [dif_pos (Finite.of_fintype F.Cell)]
  ext z
  simp
theorem sum_finiteCells (g : F.Cell → ℝ) : ∑ Y ∈ finiteCells F, g Y = ∑ Y, g Y := by
  rw [finiteCells_eq_univ]
theorem stepExponent_zero {star : Bool} {a ρA x : ℝ} {m : ℕ} (f : LocalFamily) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    stepExponent star a ρA x m f 0 V η = stepExponent star a ρA x m (fun _ _ _ => 0) 0 V η := by
  simp [stepExponent]
theorem stepExponent_eq {star : Bool} {a ρA x : ℝ} {m : ℕ} (f : LocalFamily) (ν : ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    stepExponent star a ρA x m f ν V η = stepExponent star a ρA x m (fun _ _ _ => 0) 0 V η -
      ν * ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion star a ρA m f y η V := by
  simp [stepExponent]
theorem sum_cellQuadratic (lam x : ℝ) (η : StepVariable (finiteCells F)) :
    ∑ Z : F.Cell, cellQuadratic lam x Z η = totalQuadratic lam x η := by
  classical
  unfold cellQuadratic totalQuadratic
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq]
  simp
theorem sum_cellCentredExpansion {star : Bool} {a ρA : ℝ} {m : ℕ} (f : LocalFamily) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    ∑ Z : F.Cell, cellCentredExpansion star a ρA m f Z η V =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion star a ρA m f y η V := by
  classical
  unfold cellCentredExpansion
  rw [← Finset.sum_fiberwise (sitesOfCells (finiteCells F) F.depth) enclosingCell]
end Sums
section Members
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem isConvexClassMember_segment (hSeg : ConvexSmallGradientClassSegment) {ρ κ x lam v : ℝ}
    {d : ι → ι → ℝ} {P : BondField ι → ℝ} {Q : BondField ι → ℝ} (hρ : 0 < ρ) (hx : 0 < x) (hl : 0 < lam)
    (hd : ∀ b, d b b = 0) (h0 : 0 ≤ v) (h1 : v ≤ 1) (hP : IsConvexClassMember ρ (x * lam / 4) κ d P)
    (hQ : ∀ η, Q η = x * lam / 2 * ∑ b, ‖η b‖ ^ 2) :
    IsConvexClassMember ρ (x * lam / 4) κ d (fun η => v * P η + (1 - v) * Q η) := by
  obtain ⟨Ψ, K, he, hK, hsl⟩ := hP
  have hm : 0 < x * lam / 4 := by positivity
  obtain ⟨hs1, hs2⟩ := hSeg ι ρ (x * lam / 4) κ (x * lam / 2) d hρ hm (by nlinarith [mul_pos hx hl]) hd
  obtain ⟨⟨K', hK'⟩, sl⟩ := hs1 _ Ψ v hs2 ⟨⟨K, hK⟩, hsl⟩ h0 h1
  refine ⟨_, K', fun η hη => ?_, hK', sl⟩
  simp only [segmentInterpolant]
  rw [he η hη, hQ]
end Members
section Main
theorem cutoffMean_eq {F : BlockFrame} (ρ : ℝ) (p : ℝ → ℝ) (Ψ H : StepVariable (finiteCells F) → ℝ) :
    cutoffMean ρ p Ψ H = ballExpectation (cutoffFactor ρ p) Ψ H := rfl
theorem placementDist_self (F : BlockFrame) (b : ↥(chordBonds (finiteCells F))) :
    placementDist (chordBondCell F) (cellDistReal F) b b = 0 := by
  simp [placementDist, cellDistReal, cellSupDist_self]
theorem totalQuadratic_eq {F : BlockFrame} (lam x : ℝ) (η : StepVariable (finiteCells F)) :
    totalQuadratic lam x η = x * lam / 2 * ∑ b, ‖η b‖ ^ 2 := by
  unfold totalQuadratic
  rw [Finset.mul_sum]
theorem abs_cellExponent_le {F : BlockFrame} {star : Bool} {a ρA ρ x κ C : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hx : 0 ≤ x) (hE : CellExponentBounds star a ρA ρ x κ C m V) (Y : F.Cell)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < ρ) :
    |cellExponent star a ρA x m Y V η| ≤
      C * (x * weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Y η + 1) := by
  have h1 := hE.deriv_top Y η 0 emptyBonds emptyDirections hη (by omega) areUnitVectors_empty
  rw [bondDeriv_zero (G := fun V' => cellExponent star a ρA x m Y V' η), localSqNorm_eq] at h1
  refine h1.trans ?_
  have h2 : Real.exp (-(2 ^ 6 * κ * (bondSpan Y (emptyBonds (F := F) (j := F.top)) : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ 2 ^ 6 * κ * (bondSpan Y (emptyBonds (F := F) (j := F.top)) : ℝ) := by positivity
    linarith
  have h3 : 0 ≤ weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Y η :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (by positivity)
  calc _ ≤ C * (x * weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Y η + 1) * 1 := by gcongr
    _ = _ := by ring
theorem abs_cellQuadratic_le {F : BlockFrame} {lam x κ : ℝ} (hl : 0 ≤ lam) (hx : 0 ≤ x) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) :
    |cellQuadratic lam x Y η| ≤ lam * (x * weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Y η + 1) := by
  have hD : ∀ b ∈ bondsOfCell (F := F) Y, cellDistReal F Y (chordBondCell F b) = 0 := fun b hb => by
    have : enclosingCell b.1.1 = Y := (Finset.mem_filter.mp hb).2
    simp [cellDistReal, chordBondCell, this, cellSupDist_self]
  have hs : ∑ b ∈ bondsOfCell (F := F) Y, ‖η b‖ ^ 2 ≤
      weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Y η := by
    unfold weightedSqNormAt
    calc _ = ∑ b ∈ bondsOfCell (F := F) Y, Real.exp (-(2 ^ 6 * κ * cellDistReal F Y (chordBondCell F b))) *
          ‖η b‖ ^ 2 := Finset.sum_congr rfl fun b hb => by simp [hD b hb]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => mul_nonneg (Real.exp_pos _).le (by positivity)
  have h0 : 0 ≤ ∑ b ∈ bondsOfCell (F := F) Y, ‖η b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  rw [cellQuadratic_eq]
  simp only
  rw [abs_of_nonneg (by positivity)]
  have h1 : x * lam / 2 * ∑ b ∈ bondsOfCell (F := F) Y, ‖η b‖ ^ 2 ≤
      x * lam / 2 * weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Y η :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h3 := (h0.trans hs)
  nlinarith [mul_nonneg (mul_nonneg hx hl) h3]
set_option maxHeartbeats 1600000 in
theorem meansLocalizeAt_of (hLoc : LocalExpectationComparisonInValue) (hSeg : ConvexSmallGradientClassSegment)
    (hCB : commonBondsOfTwoTori) (hS : SiteDecomposition)
    {T : StepParameters} (hd : T.IsOrdered) (h1 : ExponentsConvexAt T)
    (h2 : CellExponentsBoundedAt T) (h3 : CentredExpansionsBoundedAt T) (h4 : expansionTransportAt T)
    (h5 : StepTermsCloseAt T) (h6 : ConstantFloors hLoc hCB T) : MeansLocalizeAt T := by
  obtain ⟨fl₁, fl₂, hy₁, hn₀, hCt1⟩ := h6
  have hCt : 0 ≤ T.Ct := by linarith
  intro t x f F V hy hrow hF hV star F' V' Y Y' r hF' hV' hag v hv0 hv1
  have hF₀ := hF
  have hF₀' := hF'
  obtain ⟨hFL, hFt, n, hs, hnn⟩ := hF
  obtain ⟨hFL', hFt', n', hs', hnn'⟩ := hF'
  have hx : 1 ≤ x := hy₁.trans hy
  have hx0 : 0 ≤ x := by linarith
  have hκ : 0 < T.κ := hd.κ_pos
  have hρ : 0 < T.ballRadius := by
    have := hd.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hp : IsCutoff T.ballRadius T.p := hd.cutoff
  have hl : 0 < T.chainParams.lam := hd.chain_admissible.positivity.2.2.1
  have hE1 : 1 ≤ T.E := hd.one_le_E
  have hE0 : 0 ≤ T.E := by linarith
  have hE₃ : 0 ≤ T.energyRatio := by
    have := hd.η₃_pos
    unfold StepParameters.energyRatio
    positivity
  have hO : Odd T.L := hd.odd_L
  have hOF : Odd F.blockSide := hFL ▸ hO
  have hOF' : Odd F'.blockSide := hFL' ▸ hO
  have hn2 : 2 ≤ n := hn₀.trans hnn
  have hn2' : 2 ≤ n' := hn₀.trans hnn'
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hs]; exact hn2
  have hs2' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hs']; exact hn2'
  haveI hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    have : F.period F.top i = F.extent i := by simp [BlockFrame.period]
    rw [this, hs]
    omega⟩
  haveI hne' : ∀ i, NeZero (F'.period F'.top i) := fun i => ⟨by
    have : F'.period F'.top i = F'.extent i := by simp [BlockFrame.period]
    rw [this, hs']
    omega⟩
  letI : Fintype F.Cell := inferInstance
  letI : Fintype F'.Cell := inferInstance
  set S := placementConstant hCB T.L T.κ with hSdef
  have hSeq : S = ((hCB T.L hO).1 T.κ hκ).choose := dif_pos ⟨hO, hκ⟩
  have hP : IsDecayingPlacement T.κ S (chordBondCell F) (cellDistReal F) := by
    rw [hSeq]
    exact ((hCB T.L hO).1 T.κ hκ).choose_spec F n hFL hn2 hs
  have hP' : IsDecayingPlacement T.κ S (chordBondCell F') (cellDistReal F') := by
    rw [hSeq]
    exact ((hCB T.L hO).1 T.κ hκ).choose_spec F' n' hFL' hn2' hs'
  set C := comparisonConstant hLoc S T.chainParams.lam with hCdef
  have hCeq : C = (hLoc S T.chainParams.lam hl).choose := dif_pos hl
  have hspec := (hLoc S T.chainParams.lam hl).choose_spec
  rw [← hCeq] at hspec
  obtain ⟨hC₁, hC₂⟩ := hspec
  have hr : 2 * r + 2 < n := by
    rcases hag.1 0 with h | h
    · rw [hs] at h; omega
    · rwa [hs] at h
  have hr' : 2 * r + 2 < n' := by
    rcases hag.2.1 0 with h | h
    · rw [hs'] at h; omega
    · rwa [hs'] at h
  have hcb : HasCommonBonds Y Y' r := (hCB T.L hO).2 F F' Y Y' r n n' hFL hFL' hs hs' hr hr'
  have clause : ∀ (θ : F.Cell → StepVariable (finiteCells F) → ℝ)
      (θ' : F'.Cell → StepVariable (finiteCells F') → ℝ) (Ψ H : StepVariable (finiteCells F) → ℝ)
      (Ψ' H' : StepVariable (finiteCells F') → ℝ) (A ε₀ Cs : ℝ), 1 ≤ A → 0 < ε₀ →
      IsConvexClassMember T.ballRadius (x * T.chainParams.lam / 4) T.κ
        (placementDist (chordBondCell F) (cellDistReal F)) Ψ →
      IsConvexClassMember T.ballRadius (x * T.chainParams.lam / 4) T.κ
        (placementDist (chordBondCell F') (cellDistReal F')) Ψ' →
      IsLocalDecompositionOnBalls T.ballRadius x T.κ A (chordBondCell F) (cellDistReal F) θ Ψ H Y →
      IsLocalDecompositionOnBalls T.ballRadius x T.κ A (chordBondCell F') (cellDistReal F') θ' Ψ' H' Y' →
      (∀ η ∈ openPolyball _ T.ballRadius,
        |H η| ≤ A * (x * weightedSqNormAt T.κ (chordBondCell F) (cellDistReal F) Y η + 1)) →
      (∀ η ∈ openPolyball _ T.ballRadius,
        |H' η| ≤ A * (x * weightedSqNormAt T.κ (chordBondCell F') (cellDistReal F') Y' η + 1)) →
      (T.blockIndex ≤ r →
        IsCloseOnTwoTori T.ballRadius x T.κ (ε₀ * Real.exp (-(2 * T.κ * r))) Y Y' r θ θ' H H') →
      constantFloor C A (ε₀ * (1 + |S|)) T.κ T.blockIndex ≤ Cs →
      |ballExpectation (cutoffFactor T.ballRadius T.p) Ψ H -
        ballExpectation (cutoffFactor T.ballRadius T.p) Ψ' H'| ≤
        Cs * Real.exp (-(T.κ * r / 2 ^ 7)) := by
    intro θ θ' Ψ H Ψ' H' A ε₀ Cs hA hε₀ hM hM' hside hside' hsz hsz' hcmp hfl
    have hA0 : 0 ≤ A := by linarith
    have hCA : C * A ≤ |C| * A := mul_le_mul_of_nonneg_right (le_abs_self C) hA0
    have hfl' : constantFloor |C| A (ε₀ * (1 + |S|)) T.κ T.blockIndex ≤ Cs := by
      simpa [constantFloor, abs_abs] using hfl
    refine abs_sub_le_of_near_or_far hκ hA0 (by positivity) (fun hrn => ?_)
      ((hC₁ _ _ T.ballRadius x T.κ A T.p _ _ Ψ H Y hρ hp hκ hx hA0 hP hM hside.smooth_obs hsz).trans hCA)
      ((hC₁ _ _ T.ballRadius x T.κ A T.p _ _ Ψ' H' Y' hρ hp hκ hx hA0 hP' hM' hside'.smooth_obs hsz').trans hCA)
      hfl'
    have hεε : 0 < ε₀ * Real.exp (-(2 * T.κ * r)) := by positivity
    have hb := hC₂ _ _ _ _ _ _ T.ballRadius x T.κ A (ε₀ * Real.exp (-(2 * T.κ * r))) r T.p (chordBondCell F)
      (cellDistReal F) (chordBondCell F') (cellDistReal F') (commonBondLeft Y Y' (r / 2))
      (commonBondRight Y Y' (r / 2)) (offsetCell Y (r / 8))
      (offsetCell Y' (r / 8)) θ θ' Ψ H Ψ' H' Y Y' hρ hp hκ hx hA hεε (by positivity) hP hP'
      hcb.injective_left hcb.injective_right hcb.injective_offset hcb.injective_offset' hcb.dist_eq
      hcb.dist_centre_eq hcb.far_of_not_common hcb.far_of_not_common' hcb.far_of_not_offset
      hcb.far_of_not_offset' hM hM' hside hside' (hcmp hrn)
    have hcard : (Fintype.card ↥(centredCube (2 * (r / 8) + 1)) : ℝ) * Real.exp (-(T.κ * r / 16)) ≤ |S| := by
      have h1 := hP.cells Y
      have h2 : ∑ c : ↥(centredCube (2 * (r / 8) + 1)),
          Real.exp (-(T.κ / 2 * cellDistReal F Y (offsetCell Y (r / 8) c))) ≤
          ∑ Z', Real.exp (-(T.κ / 2 * cellDistReal F Y Z')) := by
        classical
        rw [← Finset.sum_image (s := Finset.univ) (g := offsetCell Y (r / 8))
          (f := fun Z' => Real.exp (-(T.κ / 2 * cellDistReal F Y Z')))
          (fun p _ q _ h => hcb.injective_offset h)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le
      have h3 : ∀ c : ↥(centredCube (2 * (r / 8) + 1)), Real.exp (-(T.κ * r / 16)) ≤
          Real.exp (-(T.κ / 2 * cellDistReal F Y (offsetCell Y (r / 8) c))) := fun c => by
        apply Real.exp_le_exp.mpr
        have := hcb.offset_near c
        nlinarith
      have h4 := Finset.sum_le_sum (s := Finset.univ) fun c _ => h3 c
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h4
      exact (h4.trans (h2.trans h1)).trans (le_abs_self S)
    have hCb : C * (A ^ 2 * Real.exp (-(T.κ * r / 2 ^ 4)) + A * (ε₀ * Real.exp (-(2 * T.κ * r))) *
        (1 + Fintype.card ↥(centredCube (2 * (r / 8) + 1)))) ≤
        |C| * (A ^ 2 * Real.exp (-(T.κ * r / 2 ^ 4)) + A * (ε₀ * (1 + |S|) * Real.exp (-(T.κ * r)))) := by
      have hr0 : (0 : ℝ) ≤ r := by positivity
      have hx1 : 0 ≤ T.κ * r := by positivity
      have hp0 : 0 ≤ A ^ 2 * Real.exp (-(T.κ * r / 2 ^ 4)) + A * (ε₀ * Real.exp (-(2 * T.κ * r))) *
        (1 + Fintype.card ↥(centredCube (2 * (r / 8) + 1))) := by positivity
      refine (mul_le_mul_of_nonneg_right (le_abs_self C) hp0).trans ?_
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
      have h5 : Real.exp (-(2 * T.κ * r)) * (1 + Fintype.card ↥(centredCube (2 * (r / 8) + 1))) ≤
          (1 + |S|) * Real.exp (-(T.κ * r)) := by
        have e1 : Real.exp (-(2 * T.κ * r)) ≤ Real.exp (-(T.κ * r)) := Real.exp_le_exp.mpr (by nlinarith)
        have e2 : Real.exp (-(2 * T.κ * r)) ≤ Real.exp (-(T.κ * r)) * Real.exp (-(T.κ * r / 16)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith
        have e3 : Real.exp (-(2 * T.κ * r)) * (Fintype.card ↥(centredCube (2 * (r / 8) + 1)) : ℝ) ≤
            Real.exp (-(T.κ * r)) * |S| := by
          calc _ ≤ Real.exp (-(T.κ * r)) * Real.exp (-(T.κ * r / 16)) *
                (Fintype.card ↥(centredCube (2 * (r / 8) + 1)) : ℝ) := by gcongr
            _ = Real.exp (-(T.κ * r)) * ((Fintype.card ↥(centredCube (2 * (r / 8) + 1)) : ℝ) *
                Real.exp (-(T.κ * r / 16))) := by ring
            _ ≤ _ := by gcongr
        nlinarith
      have h6 : A * (ε₀ * Real.exp (-(2 * T.κ * r))) * (1 + Fintype.card ↥(centredCube (2 * (r / 8) + 1))) ≤
          A * (ε₀ * (1 + |S|) * Real.exp (-(T.κ * r))) := by
        calc _ = A * ε₀ * (Real.exp (-(2 * T.κ * r)) * (1 + Fintype.card ↥(centredCube (2 * (r / 8) + 1)))) := by
              ring
          _ ≤ A * ε₀ * ((1 + |S|) * Real.exp (-(T.κ * r))) := by gcongr
          _ = _ := by ring
      linarith
    exact hb.trans hCb
  have hE := (h2 t x F V star hy hF₀ hV).1
  have hE' := (h2 t x F' V' star hy hF₀' hV').1
  have hR := h3 t x f F V star hy hrow hF₀ hV
  have hR' := h3 t x f F' V' star hy hrow hF₀' hV'
  have hT := (h4 t x f F V hy hrow hF₀ hV star).1
  have hT' := (h4 t x f F' V' hy hrow hF₀' hV' star).1
  have psi := fun Z => isLocalTerm_cellExponent hCt hκ.le hx0 hE Z
  have psi' := fun Z => isLocalTerm_cellExponent hCt hκ.le hx0 hE' Z
  have qq : ∀ Z : F.Cell, IsLocalTerm T.ballRadius x T.κ T.chainParams.lam (chordBondCell F) (cellDistReal F)
      (cellQuadratic T.chainParams.lam x Z) Z := fun Z => isLocalTerm_cellQuadratic hl.le hx0 Z
  have qq' : ∀ Z : F'.Cell, IsLocalTerm T.ballRadius x T.κ T.chainParams.lam (chordBondCell F') (cellDistReal F')
      (cellQuadratic T.chainParams.lam x Z) Z := fun Z => isLocalTerm_cellQuadratic hl.le hx0 Z
  have standingConstraints := fun Z => isLocalTerm_cellCentredExpansion hρ hS hOF hs2 hCt hE0 hκ.le hx hR Z
  have expansions' := fun Z => isLocalTerm_cellCentredExpansion hρ hS hOF' hs2' hCt hE0 hκ.le hx hR' Z
  have hcard : ((centredCube F.blockSide).card : ℝ) = (centredCube T.L).card := by rw [hFL]
  have hcard' : ((centredCube F'.blockSide).card : ℝ) = (centredCube T.L).card := by rw [hFL']
  rw [hcard] at standingConstraints
  rw [hcard'] at expansions'
  have hv1' : 0 ≤ 1 - v := by linarith
  have habs : |v| ≤ 1 := by rw [abs_of_nonneg hv0]; exact hv1
  have habs' : |1 - v| ≤ 1 := by rw [abs_of_nonneg hv1']; linarith
  set A₁ := firstAmplitude T.Ct T.chainParams.lam with hA₁
  set A₂ := secondAmplitude T.L T.Ct T.E with hA₂
  have hA₁1 : 1 ≤ A₁ := by
    simp only [hA₁, firstAmplitude]
    linarith
  have hN : 0 ≤ ((centredCube T.L).card : ℝ) * (T.Ct * T.E) := by positivity
  have hA₂1 : 1 ≤ A₂ := by
    simp only [hA₂, secondAmplitude]
    linarith
  constructor
  · rw [cutoffMean_eq, cutoffMean_eq]
    have hθ : ∀ Z, IsLocalTerm T.ballRadius x T.κ A₁ (chordBondCell F) (cellDistReal F)
        (fun η => v * cellExponent star T.a T.chainParams.ρA x (frameRadius x) Z V η +
          (1 - v) * cellQuadratic T.chainParams.lam x Z η) Z := fun Z => by
      refine ((psi Z).linear_comb hρ hx0 (qq Z) v (1 - v)).mono hx0 ?_
      simp only [hA₁, firstAmplitude]
      nlinarith [mul_le_mul_of_nonneg_right habs hCt, mul_le_mul_of_nonneg_right habs' hl.le]
    have hθ' : ∀ Z, IsLocalTerm T.ballRadius x T.κ A₁ (chordBondCell F') (cellDistReal F')
        (fun η => v * cellExponent star T.a T.chainParams.ρA x (frameRadius x) Z V' η +
          (1 - v) * cellQuadratic T.chainParams.lam x Z η) Z := fun Z => by
      refine ((psi' Z).linear_comb hρ hx0 (qq' Z) v (1 - v)).mono hx0 ?_
      simp only [hA₁, firstAmplitude]
      nlinarith [mul_le_mul_of_nonneg_right habs hCt, mul_le_mul_of_nonneg_right habs' hl.le]
    have hH : IsLocalTerm T.ballRadius x T.κ A₁ (chordBondCell F) (cellDistReal F)
        (fun η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y V η -
          cellQuadratic T.chainParams.lam x Y η) Y := by
      have := ((psi Y).linear_comb hρ hx0 (qq Y) 1 (-1)).mono hx0 (a' := A₁) (by
        simp only [hA₁, firstAmplitude, abs_one, abs_neg, one_mul]
        linarith)
      refine this.congr ?_
      funext η
      ring
    have hH' : IsLocalTerm T.ballRadius x T.κ A₁ (chordBondCell F') (cellDistReal F')
        (fun η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y' V' η -
          cellQuadratic T.chainParams.lam x Y' η) Y' := by
      have := ((psi' Y').linear_comb hρ hx0 (qq' Y') 1 (-1)).mono hx0 (a' := A₁) (by
        simp only [hA₁, firstAmplitude, abs_one, abs_neg, one_mul]
        linarith)
      refine this.congr ?_
      funext η
      ring
    have hmem := h1 t x f F V star 0 hy hrow hF₀ hV le_rfl zero_le_one
    have hmem' := h1 t x f F' V' star 0 hy hrow hF₀' hV' le_rfl zero_le_one
    refine clause _ _ _ _ _ _ A₁ T.Ct T.Cs hA₁1 (by linarith)
      (isConvexClassMember_segment hSeg hρ (by linarith) hl (placementDist_self F) hv0 hv1 hmem
        (totalQuadratic_eq _ _))
      (isConvexClassMember_segment hSeg hρ (by linarith) hl (placementDist_self F') hv0 hv1 hmem'
        (totalQuadratic_eq _ _))
      ⟨fun Z => (hθ Z).smooth, hH.smooth, fun η hη => ?_, fun Z => (hθ Z).slope, fun Z => (hθ Z).second,
        hH.slope⟩
      ⟨fun Z => (hθ' Z).smooth, hH'.smooth, fun η hη => ?_, fun Z => (hθ' Z).slope,
        fun Z => (hθ' Z).second, hH'.slope⟩
      (fun η hη => ?_) (fun η hη => ?_) (fun hrn => (h5 t x f F F' V V' Y Y' r star v hy hrow hF₀ hF₀' hV hV'
        hag hrn hv0 hv1).1) fl₁
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_cellQuadratic,
        stepExponent_zero, hE.sum_eq η hη, sum_finiteCells]
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_cellQuadratic,
        stepExponent_zero, hE'.sum_eq η hη, sum_finiteCells]
    · have e1 := abs_cellExponent_le hCt hκ.le hx0 hE Y hη
      have e2 := abs_cellQuadratic_le (κ := T.κ) hl.le hx0 Y η
      have e3 := abs_sub (cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y V η)
        (cellQuadratic T.chainParams.lam x Y η)
      have hq : 0 ≤ x * weightedSqNormAt T.κ (chordBondCell F) (cellDistReal F) Y η + 1 := by
        have : 0 ≤ weightedSqNormAt T.κ (chordBondCell F) (cellDistReal F) Y η :=
          Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (by positivity)
        positivity
      simp only [hA₁, firstAmplitude]
      nlinarith
    · have e1 := abs_cellExponent_le hCt hκ.le hx0 hE' Y' hη
      have e2 := abs_cellQuadratic_le (κ := T.κ) hl.le hx0 Y' η
      have e3 := abs_sub (cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y' V' η)
        (cellQuadratic T.chainParams.lam x Y' η)
      have hq : 0 ≤ x * weightedSqNormAt T.κ (chordBondCell F') (cellDistReal F') Y' η + 1 := by
        have : 0 ≤ weightedSqNormAt T.κ (chordBondCell F') (cellDistReal F') Y' η :=
          Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (by positivity)
        positivity
      simp only [hA₁, firstAmplitude]
      nlinarith
  · rw [cutoffMean_eq, cutoffMean_eq]
    have hθ : ∀ Z, IsLocalTerm T.ballRadius x T.κ A₂ (chordBondCell F) (cellDistReal F)
        (fun η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Z V η -
          v * cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Z η V) Z := fun Z => by
      have := ((psi Z).linear_comb hρ hx0 (standingConstraints Z) 1 (-v)).mono hx0 (a' := A₂) (by
        simp only [hA₂, secondAmplitude, abs_one, abs_neg, one_mul]
        nlinarith [mul_le_mul_of_nonneg_right habs hN])
      refine this.congr ?_
      funext η
      ring
    have hθ' : ∀ Z, IsLocalTerm T.ballRadius x T.κ A₂ (chordBondCell F') (cellDistReal F')
        (fun η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Z V' η -
          v * cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Z η V') Z := fun Z => by
      have := ((psi' Z).linear_comb hρ hx0 (expansions' Z) 1 (-v)).mono hx0 (a' := A₂) (by
        simp only [hA₂, secondAmplitude, abs_one, abs_neg, one_mul]
        nlinarith [mul_le_mul_of_nonneg_right habs hN])
      refine this.congr ?_
      funext η
      ring
    have hH := (standingConstraints Y).mono hx0 (a' := A₂) (by simp only [hA₂, secondAmplitude]; linarith)
    have hH' := (expansions' Y').mono hx0 (a' := A₂) (by simp only [hA₂, secondAmplitude]; linarith)
    have hmem := h1 t x f F V star v hy hrow hF₀ hV hv0 hv1
    have hmem' := h1 t x f F' V' star v hy hrow hF₀' hV' hv0 hv1
    have hEA : T.E ≤ A₂ := by
      simp only [hA₂, secondAmplitude]
      linarith
    have hdec : ∀ {w : ℝ}, 1 ≤ w → 2⁻¹ ^ 8 * T.E / w ≤ T.E := fun {w} hw => by
      have : (0 : ℝ) < w := by linarith
      rw [div_le_iff₀ this]
      nlinarith
    have hw : 1 ≤ torusDecayFactor T.L T.decayRate T.blockIndex := by
      unfold torusDecayFactor
      have e1 : (1 : ℝ) ≤ max 1 (((T.blockIndex : ℝ) / (T.L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) := le_max_left _ _
      have e2 : 1 ≤ Real.exp (T.decayRate * T.blockIndex) := by
        apply Real.one_le_exp
        have : 0 < T.decayRate := by
          unfold StepParameters.decayRate
          positivity
        positivity
      nlinarith
    refine clause _ _ _ _ _ _ A₂ (T.Ct * (1 + T.energyRatio)) T.CE hA₂1 (by have : 0 < T.Ct := by linarith
                                                                            positivity) hmem hmem'
      ⟨fun Z => (hθ Z).smooth, hH.smooth, fun η hη => ?_, fun Z => (hθ Z).slope, fun Z => (hθ Z).second,
        hH.slope⟩
      ⟨fun Z => (hθ' Z).smooth, hH'.smooth, fun η hη => ?_, fun Z => (hθ' Z).slope,
        fun Z => (hθ' Z).second, hH'.slope⟩
      (fun η hη => ?_) (fun η hη => ?_) (fun hrn => (h5 t x f F F' V V' Y Y' r star v hy hrow hF₀ hF₀' hV hV'
        hag hrn hv0 hv1).2) fl₂
    · rw [stepExponent_eq, hE.sum_eq η hη, sum_finiteCells, Finset.sum_sub_distrib, ← Finset.mul_sum,
        sum_cellCentredExpansion]
    · rw [stepExponent_eq, hE'.sum_eq η hη, sum_finiteCells, Finset.sum_sub_distrib, ← Finset.mul_sum,
        sum_cellCentredExpansion]
    · have e1 := (hT.abs_le Y η hη).trans (hdec hw)
      have hq : 0 ≤ weightedSqNormAt T.κ (chordBondCell F) (cellDistReal F) Y η :=
        Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (by positivity)
      have hA0 : 0 ≤ A₂ := by linarith
      nlinarith [mul_nonneg (mul_nonneg hA0 hx0) hq]
    · have e1 := (hT'.abs_le Y' η hη).trans (hdec hw)
      have hq : 0 ≤ weightedSqNormAt T.κ (chordBondCell F') (cellDistReal F') Y' η :=
        Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (by positivity)
      have hA0 : 0 ≤ A₂ := by linarith
      nlinarith [mul_nonneg (mul_nonneg hA0 hx0) hq]
end Main
end LocalTerms
open LocalTerms in
theorem meansLocalizeEventually_holds (hLoc : LocalExpectationComparisonInValue)
    (hSeg : ConvexSmallGradientClassSegment) (hCB : commonBondsOfTwoTori)
    (hS : SiteDecomposition) (hJ : EventuallyInParametersCombines)
    (h₁ : exponentConvexityStatement) (h₂ : CellExponentsBounded)
    (h₃ : CentredExpansionsBounded) (h₄ : expansionTransportStatement)
    (h₅ : StepTermsCloseOnTwoTori) : MeansLocalizeEventually := by
  have j := hJ.1 _ _ h₁ (hJ.1 _ _ h₂ (hJ.1 _ _ h₃ (hJ.1 _ _ h₄ (hJ.1 _ _ h₅
    (eventually_constantFloors hLoc hCB)))))
  exact hJ.2 _ _ (fun T hd ⟨a, b, c, d, e, f⟩ => meansLocalizeAt_of hLoc hSeg hCB hS hd a b c d e f) j
end YangMills.Construction.ColdStepAtMirrorFrames
end
