import YangMills.Construction.ResponseInTheExpansion.EnergyAboveAFramePointProof
import YangMills.Construction.ResponseInTheExpansion.SlopeToSecondOrder
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeMovesByItsKernelsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace WeightedResponses.SlopeExpansion
section Calculus
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
theorem contDiffAt_of_comp_add_left {f : P → ℝ} {x₀ : P} (h : ContDiffAt ℝ 3 (fun v => f (x₀ + v)) 0) :
    ContDiffAt ℝ 3 f x₀ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.contDiffAt_of_comp_add_left <;> assumption
theorem fderiv_three_comp_add_left (f : P → ℝ) (v : P) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ fun y => f (v + y))) 0 = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) v := by
  have h1 : (fderiv ℝ fun y => f (v + y)) = fun y => fderiv ℝ f (v + y) := by
    funext y
    rw [fderiv_comp_add_left]
  have h2 : (fderiv ℝ fun y => fderiv ℝ f (v + y)) = fun y => fderiv ℝ (fderiv ℝ f) (v + y) := by
    funext y
    rw [fderiv_comp_add_left]
  rw [h1, h2]
  have h3 := fderiv_comp_add_left (𝕜 := ℝ) (f := fderiv ℝ (fderiv ℝ f)) (x := (0 : P)) v
  rw [add_zero] at h3
  exact h3
theorem iteratedFDeriv_three_comp_clm {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : P → ℝ}
    (hf : ContDiffAt ℝ 3 f 0) (A : G →L[ℝ] P) (m : Fin 3 → G) :
    iteratedFDeriv ℝ 3 (f ∘ A) 0 m = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) 0 (A (m 0)) (A (m 1)) (A (m 2)) := by
  obtain ⟨u, hu, hcd⟩ := hf.contDiffOn (m := 3) le_rfl (by simp)
  have hu' : u ∈ 𝓝 (0 : P) := by simpa using hu
  obtain ⟨s, hsu, hs, h0⟩ := mem_nhds_iff.1 hu'
  have hcs : ContDiffOn ℝ 3 f s := hcd.mono hsu
  have hpre : IsOpen (A ⁻¹' s) := hs.preimage A.continuous
  have h0' : (0 : G) ∈ A ⁻¹' s := by simpa using h0
  have hc := A.iteratedFDerivWithin_comp_right hcs hs.uniqueDiffOn hpre.uniqueDiffOn
    (x := (0 : G)) (by simpa using h0) (i := 3) le_rfl
  rw [iteratedFDerivWithin_of_isOpen 3 hpre h0', map_zero,
    iteratedFDerivWithin_of_isOpen 3 hs h0] at hc
  rw [hc]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  rfl
theorem abs_fderiv_sub_taylor_le {E : P → ℝ} {x u : P} {M : ℝ} (hM0 : 0 ≤ M)
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 E (t • x))
    (hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, |fderiv ℝ (fderiv ℝ (fderiv ℝ E)) (t • x) x x u| ≤ M) :
    |fderiv ℝ E x u - fderiv ℝ E 0 u - fderiv ℝ (fun v => fderiv ℝ E v u) 0 x| ≤ M := by
  set D₁ := fderiv ℝ E with hD₁
  set D₂ := fderiv ℝ D₁ with hD₂
  set D₃ := fderiv ℝ D₂ with hD₃
  have hl : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s • x) x t := fun t => by
    simpa using (hasDerivAt_id t).smul_const x
  have d₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ D₁ (t • x) := fun t ht =>
    ((hC t ht).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have d₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ D₂ (t • x) := fun t ht =>
    (((hC t ht).fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  have hd2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => D₂ (s • x) x u)
      (D₃ (t • x) x x u) (Set.Icc 0 1) t := by
    intro t ht
    have hs := ((d₂ t ht).hasFDerivAt.clm_apply (hasFDerivAt_const x (t • x))).clm_apply
      (hasFDerivAt_const u (t • x))
    have h2 := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => s • x) t hs (hl t)
    have h2' : HasDerivAt (fun s : ℝ => D₂ (s • x) x u) _ t := h2
    have h3 : HasDerivAt (fun s : ℝ => D₂ (s • x) x u) (D₃ (t • x) x x u) t :=
      h2'.congr_deriv (by simp [hD₃])
    exact h3.hasDerivWithinAt
  have hb2 : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖D₃ (t • x) x x u‖ ≤ M := fun t ht => by
    rw [Real.norm_eq_abs]
    exact hb t ht
  have mv1 := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s : ℝ => D₂ (s • x) x u) hd2 hb2
  set c₀ : ℝ := D₂ ((0 : ℝ) • x) x u with hc₀
  have hk1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => D₁ (s • x) u - s * c₀)
      (D₂ (t • x) x u - c₀) (Set.Icc 0 1) t := by
    intro t ht
    have hs := (d₁ t ht).hasFDerivAt.clm_apply (hasFDerivAt_const u (t • x))
    have h1 := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => s • x) t hs (hl t)
    have h1' : HasDerivAt (fun s : ℝ => D₁ (s • x) u) _ t := h1
    have h2 : HasDerivAt (fun s : ℝ => D₁ (s • x) u) (D₂ (t • x) x u) t :=
      h1'.congr_deriv (by simp [hD₂])
    have h3 := h2.sub ((hasDerivAt_id t).mul_const c₀)
    simp only [one_mul] at h3
    exact h3.hasDerivWithinAt
  have hkb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖D₂ (t • x) x u - c₀‖ ≤ M := by
    intro t ht
    have h1 := mv1 t ⟨ht.1, ht.2.le⟩
    simp only [sub_zero] at h1
    refine h1.trans ?_
    have : M * t ≤ M * 1 := mul_le_mul_of_nonneg_left ht.2.le hM0
    linarith
  have mv2 := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => D₁ (s • x) u - s * c₀) hk1 hkb
  simp only [one_smul, zero_smul, one_mul, zero_mul, sub_zero] at mv2
  have hsec : fderiv ℝ (fun v => D₁ v u) 0 x = c₀ := by
    have hz0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hd0 : DifferentiableAt ℝ D₁ 0 := by simpa using d₁ 0 hz0
    have h := hd0.hasFDerivAt.clm_apply (hasFDerivAt_const u (0 : P))
    rw [h.fderiv, hc₀, zero_smul]
    simp [hD₂]
  rw [hsec]
  have e1 : D₁ x u - D₁ 0 u - c₀ = D₁ x u - c₀ - D₁ 0 u := by ring
  rw [e1, ← Real.norm_eq_abs]
  exact mv2
end Calculus
variable {F : BlockFrame}
abbrev ChordBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
theorem toImaginary_zero : toImaginary (0 : BondVector) = 0 := by apply _root_.YangMills.SharedProofs.p2840 <;> assumption
theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
theorem stepCoordinates_add (x y : StepVariable (finiteCells F)) (s : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (x + y) s i = stepCoordinates x s i + stepCoordinates y s i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_add <;> assumption
theorem stepCoordinates_smul (r : ℝ) (x : StepVariable (finiteCells F)) (s : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (r • x) s i = r • stepCoordinates x s i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_smul <;> assumption
theorem stepCoordinates_bondVariation (b : ChordBond F) (e : BondVector) (s : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (bondVariation b e : StepVariable (finiteCells F)) s i =
      directionCoordinate (Sum.inl (b.1.1, b.1.2, toImaginary e) : ChartDirection F) s i := by
  classical
  change _ = if (b.1.1 = s ∧ b.1.2 = i) then toImaginary e else 0
  unfold stepCoordinates
  by_cases h : (s, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos h]
    by_cases h2 : b.1.1 = s ∧ b.1.2 = i
    · rw [if_pos h2]
      have hb : (⟨(s, i), h⟩ : ChordBond F) = b := by
        apply Subtype.ext
        exact Prod.ext h2.1.symm h2.2.symm
      rw [hb]
      simp [bondVariation]
    · rw [if_neg h2]
      have hb : (⟨(s, i), h⟩ : ChordBond F) ≠ b := by
        intro e'
        apply h2
        have := congrArg Subtype.val e'
        exact ⟨(congrArg Prod.fst this).symm, (congrArg Prod.snd this).symm⟩
      have : (bondVariation b e : StepVariable (finiteCells F)) ⟨(s, i), h⟩ = 0 :=
        Pi.single_eq_of_ne hb _
      rw [this, toImaginary_zero]
  · rw [dif_neg h]
    have h2 : ¬ (b.1.1 = s ∧ b.1.2 = i) := by
      intro h2
      apply h
      have e1 : b.1 = (s, i) := Prod.ext h2.1 h2.2
      rw [← e1]
      exact b.2
    rw [if_neg h2]
theorem chartedEnergyAt_add (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (x y : StepVariable (finiteCells F)) :
    chartedEnergyAt a w V (x + y) = chartedEnergyAt a (shiftCoordinates w x) V y := by apply _root_.YangMills.Construction.ResponseInTheExpansion.BasePointEnergy.chartedEnergyAt_add <;> assumption
theorem leftTranslate_zero (V : F.GaugeField F.top) :
    leftTranslate (fun _ _ => (0 : imaginaryQuaternions)) V = V := by apply _root_.YangMills.SharedProofs.p46723 <;> assumption
def directionMap (u : Fin 3 → StepVariable (finiteCells F)) :
    (Fin 3 → ℝ) →L[ℝ] StepVariable (finiteCells F) :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin 3 → ℝ) →L[ℝ] ℝ).smulRight (u l)
theorem directionMap_apply (u : Fin 3 → StepVariable (finiteCells F)) (c : Fin 3 → ℝ) :
    directionMap u c = c 0 • u 0 + c 1 • u 1 + c 2 • u 2 := by
  simp [directionMap, Fin.sum_univ_three]
theorem directionMap_single (u : Fin 3 → StepVariable (finiteCells F)) (l : Fin 3) :
    directionMap u (Pi.single l 1) = u l := by
  rw [directionMap_apply]
  fin_cases l <;> simp
theorem chartRestriction_eq_comp (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (y : StepVariable (finiteCells F))
    (b : Fin 3 → ChordBond F) (e : Fin 3 → BondVector) :
    chartRestriction a (shiftCoordinates w y) V
        (fun l => (Sum.inl ((b l).1.1, (b l).1.2, toImaginary (e l)) : ChartDirection F)) =
      (fun v => chartedEnergyAt a w V (y + v)) ∘ directionMap fun l => bondVariation (b l) (e l) := by
  funext c
  simp only [Function.comp_apply]
  unfold chartRestriction chartedEnergyAt
  have hm : (fun (z : F.Site F.top) (i : Fin 4) => ∑ l, c l •
      directionMove (Sum.inl ((b l).1.1, (b l).1.2, toImaginary (e l)) : ChartDirection F) z i) =
      fun _ _ => (0 : imaginaryQuaternions) := by
    funext z i
    simp [directionMove]
  rw [hm, leftTranslate_zero]
  congr 1
  funext s i
  rw [directionMap_apply, stepCoordinates_add, stepCoordinates_add, stepCoordinates_add,
    stepCoordinates_smul, stepCoordinates_smul, stepCoordinates_smul,
    stepCoordinates_bondVariation, stepCoordinates_bondVariation, stepCoordinates_bondVariation,
    Fin.sum_univ_three]
  simp only [shiftCoordinates, add_assoc]
theorem bondVariation_eq_norm_smul (b : ChordBond F) {e : BondVector} (he : e ≠ 0) :
    (bondVariation b e : StepVariable (finiteCells F)) = ‖e‖ • bondVariation b (‖e‖⁻¹ • e) := by
  have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
  unfold bondVariation
  rw [← Pi.single_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]
theorem bondVariation_zero (b : ChordBond F) :
    (bondVariation b (0 : BondVector) : StepVariable (finiteCells F)) = 0 := by
  unfold bondVariation
  simp
theorem norm_inv_norm_smul {e : BondVector} (he : e ≠ 0) : ‖(‖e‖⁻¹ • e : BondVector)‖ = 1 := by
  have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
theorem cellSupDist_le_directionDiameter {k : ℕ} (q : Fin k → ChartDirection F) (l l' : Fin k) :
    cellSupDist (directionCell (q l)) (directionCell (q l')) ≤ directionDiameter q := by
  unfold directionDiameter
  refine le_trans ?_ (Finset.le_sup (f := fun l : Fin k => Finset.univ.sup fun l' : Fin k =>
    cellSupDist (directionCell (q l)) (directionCell (q l'))) (Finset.mem_univ l))
  exact Finset.le_sup (f := fun l' : Fin k => cellSupDist (directionCell (q l)) (directionCell (q l')))
    (Finset.mem_univ l')
theorem eq_sum_bondVariation (x : StepVariable (finiteCells F)) :
    x = ∑ b' : ChordBond F, (bondVariation b' (x b') : StepVariable (finiteCells F)) := by
  funext d
  rw [Finset.sum_apply, Finset.sum_eq_single d]
  · simp [bondVariation]
  · intro b' _ hb'
    exact Pi.single_eq_of_ne (Ne.symm hb') _
  · intro h
    exact absurd (Finset.mem_univ d) h
theorem trilinear_sum_sum {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {ι : Type} [Fintype ι]
    (T : P →L[ℝ] P →L[ℝ] P →L[ℝ] ℝ) (a : ι → P) (u : P) :
    T (∑ i, a i) (∑ j, a j) u = ∑ i, ∑ j, T (a i) (a j) u := by
  simp only [map_sum, ContinuousLinearMap.sum_apply]
  exact Finset.sum_comm
set_option maxHeartbeats 4000000 in
theorem energySlopeSecondOrder_holds (hR : ChartEnergyHessianRowsEventually) (hK : ChartEnergyKernelBound)
    (hFr : FrameBoundsEventually) (hJ : EventuallyInParametersCombines) :
    EnergySlopeSecondOrder := by
  refine hJ.2 _ _ ?_ (hJ.1 _ _ hR hFr)
  rintro T hT ⟨hRt, hfr⟩
  obtain ⟨_, _, _, _, _, _, hL40, _⟩ := hfr
  obtain ⟨Ck, hCk, hker⟩ := hK T.a T.L T.chainParams hT.one_le_a hT.odd_L hL40 hT.chain_admissible
  refine ⟨Ck 3, hCk 3, ?_⟩
  intro F V w x hCT hpts b e he
  obtain ⟨KA, _, hKAp, _, _⟩ := hRt F V hCT
  set E : StepVariable (finiteCells F) → ℝ := chartedEnergyAt T.a w V with hE
  have hsm : ∀ y : StepVariable (finiteCells F),
      IsAdmissibleChartPoint T.L T.chainParams.σA (shiftCoordinates w y) V → ContDiffAt ℝ 3 E y := by
    intro y hy
    apply contDiffAt_of_comp_add_left
    have : (fun v => E (y + v)) = chartedEnergyAt T.a (shiftCoordinates w y) V :=
      funext fun v => chartedEnergyAt_add T.a w V y v
    rw [this]
    exact (hKAp _ hy).1
  have hthird : ∀ y : StepVariable (finiteCells F),
      IsAdmissibleChartPoint T.L T.chainParams.σA (shiftCoordinates w y) V →
      ∀ (bb : Fin 3 → ChordBond F) (ee : Fin 3 → BondVector), (∀ l, ‖ee l‖ = 1) →
      |fderiv ℝ (fderiv ℝ (fderiv ℝ E)) y (bondVariation (bb 0) (ee 0)) (bondVariation (bb 1) (ee 1))
          (bondVariation (bb 2) (ee 2))| ≤
        Ck 3 * Real.exp (-(T.chainParams.δ₁ * directionDiameter
          (fun l => (Sum.inl ((bb l).1.1, (bb l).1.2, toImaginary (ee l)) : ChartDirection F)))) := by
    intro y hy bb ee hu
    have hk := ((hker F (shiftCoordinates w y) V hCT hy 3
      (fun l => (Sum.inl ((bb l).1.1, (bb l).1.2, toImaginary (ee l)) : ChartDirection F))).2 (by norm_num)
      (fun l => by
        change ‖toImaginary (ee l)‖ = 1
        rw [norm_toImaginary, hu]))
    unfold chartMixedDeriv at hk
    rw [chartRestriction_eq_comp] at hk
    have hf : ContDiffAt ℝ 3 (fun v => E (y + v)) 0 := by
      have : (fun v => E (y + v)) = chartedEnergyAt T.a (shiftCoordinates w y) V :=
        funext fun v => chartedEnergyAt_add T.a w V y v
      rw [this]
      exact (hKAp _ hy).1
    rw [iteratedFDeriv_three_comp_clm hf, directionMap_single, directionMap_single, directionMap_single,
      fderiv_three_comp_add_left] at hk
    exact hk
  set decay : ChordBond F → ℝ := fun b' => Real.exp (-(T.chainParams.δ₁ / 2 * chordBondDist F b b'))
    with hdecay
  have hdecay0 : ∀ b', 0 < decay b' := fun b' => Real.exp_pos _
  have hδ₁ : 0 < T.chainParams.δ₁ := hT.chain_admissible.positivity.1
  have hC3 : 0 < Ck 3 := hCk 3
  have hk2 : ∀ y : StepVariable (finiteCells F),
      IsAdmissibleChartPoint T.L T.chainParams.σA (shiftCoordinates w y) V →
      ∀ (b₁ b₂ : ChordBond F) (e₁ e₂ : BondVector),
      |fderiv ℝ (fderiv ℝ (fderiv ℝ E)) y (bondVariation b₁ e₁) (bondVariation b₂ e₂) (bondVariation b e)| ≤
        Ck 3 * (decay b₁ * ‖e₁‖) * (decay b₂ * ‖e₂‖) := by
    intro y hy b₁ b₂ e₁ e₂
    by_cases h1 : e₁ = 0
    · subst h1
      rw [bondVariation_zero]
      simp
    by_cases h2 : e₂ = 0
    · subst h2
      rw [bondVariation_zero]
      simp
    have hb := hthird y hy ![b₁, b₂, b] ![‖e₁‖⁻¹ • e₁, ‖e₂‖⁻¹ • e₂, e] (by
      intro l
      fin_cases l
      · exact norm_inv_norm_smul h1
      · exact norm_inv_norm_smul h2
      · exact he)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hb
    set q : Fin 3 → ChartDirection F := fun l => (Sum.inl ((![b₁, b₂, b] l).1.1, (![b₁, b₂, b] l).1.2,
      toImaginary ((![‖e₁‖⁻¹ • e₁, ‖e₂‖⁻¹ • e₂, e] : Fin 3 → BondVector) l)) : ChartDirection F) with hq
    have hd1 : chordBondDist F b b₁ ≤ directionDiameter q := by
      exact show (cellSupDist (directionCell (q 2)) (directionCell (q 0)) : ℝ) ≤ directionDiameter q from by
        exact_mod_cast cellSupDist_le_directionDiameter q 2 0
    have hd2 : chordBondDist F b b₂ ≤ directionDiameter q := by
      exact show (cellSupDist (directionCell (q 2)) (directionCell (q 1)) : ℝ) ≤ directionDiameter q from by
        exact_mod_cast cellSupDist_le_directionDiameter q 2 1
    have hexp : Real.exp (-(T.chainParams.δ₁ * directionDiameter q)) ≤ decay b₁ * decay b₂ := by
      simp only [hdecay]
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith
    rw [bondVariation_eq_norm_smul b₁ h1, bondVariation_eq_norm_smul b₂ h2]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul, abs_norm]
    have hn1 := norm_nonneg e₁
    have hn2 := norm_nonneg e₂
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hexp hC3.le)
    calc _ ≤ ‖e₂‖ * (‖e₁‖ * (Ck 3 * (decay b₁ * decay b₂))) := by gcongr
      _ = Ck 3 * (decay b₁ * ‖e₁‖) * (decay b₂ * ‖e₂‖) := by ring
  have hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 E (t • x) := fun t ht => hsm _ (hpts t ht.1 ht.2)
  have hM0 : 0 ≤ Ck 3 * (∑ b', decay b' * ‖x b'‖) ^ 2 := by positivity
  refine abs_fderiv_sub_taylor_le (u := bondVariation b e) hM0 hC fun t ht => ?_
  have hz := hpts t ht.1 ht.2.le
  have h1 := trilinear_sum_sum (fderiv ℝ (fderiv ℝ (fderiv ℝ E)) (t • x))
    (fun b' : ChordBond F => (bondVariation b' (x b') : StepVariable (finiteCells F))) (bondVariation b e)
  rw [← eq_sum_bondVariation] at h1
  rw [h1]
  calc _ ≤ ∑ b', |∑ b'', fderiv ℝ (fderiv ℝ (fderiv ℝ E)) (t • x) (bondVariation b' (x b'))
        (bondVariation b'' (x b'')) (bondVariation b e)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b', ∑ b'', |fderiv ℝ (fderiv ℝ (fderiv ℝ E)) (t • x) (bondVariation b' (x b'))
        (bondVariation b'' (x b'')) (bondVariation b e)| :=
        Finset.sum_le_sum fun b' _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b', ∑ b'', Ck 3 * (decay b' * ‖x b'‖) * (decay b'' * ‖x b''‖) :=
        Finset.sum_le_sum fun b' _ => Finset.sum_le_sum fun b'' _ =>
          hk2 _ hz b' b'' (x b') (x b'')
    _ = _ := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b'' _ => ?_
        ring
end WeightedResponses.SlopeExpansion
end YangMills.Construction
end
