import YangMills.Construction.ColdStepAtMirrorFrames.OtherTermsOfTheExponentProof
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexAboveAChartPointProof
import YangMills.Construction.ColdStepAtMirrorFrames.DistancesOfSitesAndCells
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfADecayOverTheCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
namespace ChartEnergyRows
section Calculus
variable {P Q R : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
theorem fderiv_fderiv_comp_clm {Φ : Q → R} (l : P →L[ℝ] Q) {x : P} (hΦ : ContDiffAt ℝ 3 Φ (l x))
    (u v : P) :
    fderiv ℝ (fderiv ℝ (Φ ∘ l)) x v u = fderiv ℝ (fderiv ℝ Φ) (l x) (l v) (l u) := by
  have hev : ∀ᶠ ζ in 𝓝 x, ContDiffAt ℝ 3 Φ (l ζ) :=
    l.continuous.continuousAt.eventually (hΦ.eventually (by simp))
  have heq : fderiv ℝ (Φ ∘ l) =ᶠ[𝓝 x] fun ζ => (fderiv ℝ Φ (l ζ)).comp l := by
    filter_upwards [hev] with ζ h
    have hdiff : DifferentiableAt ℝ Φ (l ζ) := h.differentiableAt (by norm_num)
    rw [fderiv_comp ζ hdiff l.differentiableAt, l.fderiv]
  rw [heq.fderiv_eq]
  have h2Φ : ContDiffAt ℝ 2 (fderiv ℝ Φ) (l x) := hΦ.fderiv_right (by norm_num)
  have hdΦ : DifferentiableAt ℝ (fderiv ℝ Φ) (l x) := h2Φ.differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun ζ => fderiv ℝ Φ (l ζ))
      ((fderiv ℝ (fderiv ℝ Φ) (l x)).comp l) x := hdΦ.hasFDerivAt.comp x l.hasFDerivAt
  have h3 : HasFDerivAt (fun ζ => (fderiv ℝ Φ (l ζ)).comp l) _ x :=
    hc.clm_comp (hasFDerivAt_const l x)
  rw [h3.fderiv]
  simp
theorem fderiv_fderiv_apply_eq {f : P → ℝ} {η : P} (hf : ContDiffAt ℝ 3 f η) (u v : P) :
    fderiv ℝ (fun ζ => fderiv ℝ f ζ u) η v = fderiv ℝ (fderiv ℝ f) η v u := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) η := hf.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) η := h2.differentiableAt (by norm_num)
  rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const u η)).fderiv]
  simp
end Calculus
def toImaginaryCLM : BondVector →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => toImaginary v
      map_add' := fun u v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = 0 + 0
          simp
        · change (u + v) 0 = u 0 + v 0
          simp
        · change (u + v) 1 = u 1 + v 1
          simp
        · change (u + v) 2 = u 2 + v 2
          simp
      map_smul' := fun c v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = c * 0
          simp
        · change (c • v) 0 = c * v 0
          simp
        · change (c • v) 1 = c * v 1
          simp
        · change (c • v) 2 = c * v 2
          simp }
theorem toImaginaryCLM_apply (v : BondVector) : toImaginaryCLM v = toImaginary v := rfl
theorem norm_toImaginaryCLM (v : BondVector) : ‖toImaginaryCLM v‖ = ‖v‖ := by
  have h1 : ‖toImaginaryCLM v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h := Quaternion.normSq_eq_norm_mul_self ((toImaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])
    rw [Quaternion.normSq_def'] at h
    have h2 : ‖(toImaginaryCLM v : imaginaryQuaternions)‖ =
        ‖((toImaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
    rw [h2, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, pow_two]
    simp only [toImaginaryCLM_apply, toImaginary, Real.norm_eq_abs, sq_abs] at h ⊢
    linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
variable {F : BlockFrame}
abbrev ChordBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem leftTranslate_of_bondDirections {k : ℕ} (V : F.GaugeField F.top) (q : Fin k → ChartDirection F)
    (hq : ∀ l, ∃ p, q l = .inl p) (σ : Fin k → ℝ) :
    leftTranslate (fun y i => ∑ l, σ l • directionMove (q l) y i) V = V := by
  funext y i
  have h0 : ∑ l, σ l • directionMove (q l) y i = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    obtain ⟨p, hp⟩ := hq l
    simp [hp, directionMove]
  simp [leftTranslate, h0, expUnit_zero]
def bondDirection (b : ChordBond F) (e : BondVector) : ChartDirection F :=
  .inl (b.1.1, b.1.2, toImaginaryCLM e)
theorem stepCoordinates_bondVariation (b : ChordBond F) (e : BondVector) (x : F.Site F.depth)
    (i : Fin 4) :
    stepCoordinates (bondVariation b e : StepVariable (finiteCells F)) x i =
      directionCoordinate (bondDirection b e) x i := by
  classical
  simp only [stepCoordinates, directionCoordinate, bondDirection]
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos h]
    by_cases hb : b.1.1 = x ∧ b.1.2 = i
    · have hbb : (⟨(x, i), h⟩ : ChordBond F) = b := Subtype.ext (Prod.ext hb.1.symm hb.2.symm)
      rw [if_pos hb, hbb]
      simp [bondVariation, toImaginaryCLM_apply]
    · have hbb : (⟨(x, i), h⟩ : ChordBond F) ≠ b := by
        intro hc
        apply hb
        rw [← hc]
        exact ⟨rfl, rfl⟩
      have : (bondVariation b e : StepVariable (finiteCells F)) ⟨(x, i), h⟩ = 0 :=
        Pi.single_eq_of_ne hbb _
      rw [if_neg hb, this]
      exact map_zero toImaginaryCLM
  · rw [dif_neg h, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h b.2
theorem stepCoordinates_add (η ζ : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (η + ζ) x i = stepCoordinates η x i + stepCoordinates ζ x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_add <;> assumption
theorem stepCoordinates_smul (r : ℝ) (η : StepVariable (finiteCells F)) (x : F.Site F.depth)
    (i : Fin 4) : stepCoordinates (r • η) x i = r • stepCoordinates η x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_smul <;> assumption
theorem stepCoordinates_sum {ι : Type} (s : Finset ι) (g : ι → StepVariable (finiteCells F))
    (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (∑ l ∈ s, g l) x i = ∑ l ∈ s, stepCoordinates (g l) x i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := stepCoordinates_smul (0 : ℝ) (0 : StepVariable (finiteCells F)) x i
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, stepCoordinates_add, ih]
theorem chartRestriction_bondDirection {k : ℕ} (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (b : Fin k → ChordBond F) (e : Fin k → BondVector) (σ : Fin k → ℝ) :
    chartRestriction a w V (fun l => bondDirection (b l) (e l)) σ =
      chartedEnergyAt a w V (∑ l, σ l • (bondVariation (b l) (e l) : StepVariable (finiteCells F))) := by
  have ht : leftTranslate (fun y i => ∑ l, σ l • directionMove (bondDirection (b l) (e l)) y i) V = V :=
    leftTranslate_of_bondDirections V (fun l => bondDirection (b l) (e l)) (fun l => ⟨_, rfl⟩) σ
  simp only [chartRestriction, chartedEnergyAt, ht]
  congr 1
  funext x i
  rw [stepCoordinates_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [stepCoordinates_smul, stepCoordinates_bondVariation]
def BondBasisIndex (F : BlockFrame) : Type := ChordBond F × Fin 3
instance : Fintype (BondBasisIndex F) := inferInstanceAs (Fintype (ChordBond F × Fin 3))
theorem eq_sum_bondVariation_basis (η : StepVariable (finiteCells F)) :
    η = ∑ p : BondBasisIndex F, (η p.1 p.2) • (bondVariation p.1 (EuclideanSpace.single p.2 1) :
      StepVariable (finiteCells F)) := by
  classical
  funext d
  rw [Finset.sum_apply]
  have h1 : ∑ p : BondBasisIndex F, ((η p.1 p.2) • (bondVariation p.1 (EuclideanSpace.single p.2 1) :
      StepVariable (finiteCells F))) d = ∑ j : Fin 3, (η d j) • EuclideanSpace.single j (1 : ℝ) := by
    have h2 : ∑ p : BondBasisIndex F, ((η p.1 p.2) • (bondVariation p.1 (EuclideanSpace.single p.2 1) :
        StepVariable (finiteCells F))) d = ∑ b : ChordBond F, ∑ j : Fin 3, ((η b j) • (bondVariation b
          (EuclideanSpace.single j 1) : StepVariable (finiteCells F))) d :=
      Fintype.sum_prod_type _
    rw [h2, Finset.sum_eq_single d]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp [bondVariation]
    · intro b _ hb
      refine Finset.sum_eq_zero fun j _ => ?_
      have : (bondVariation b (EuclideanSpace.single j 1) : StepVariable (finiteCells F)) d = 0 :=
        Pi.single_eq_of_ne (Ne.symm hb) _
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ d) h
  rw [h1]
  ext j
  simp [Finset.sum_apply, PiLp.smul_apply, Pi.single_apply]
theorem contDiffAt_chartedEnergyAt {a : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top}
    (h : ∀ (k : ℕ) (q : Fin k → ChartDirection F), AnalyticAt ℝ (chartRestriction a w V q) 0) :
    ContDiffAt ℝ 3 (chartedEnergyAt a w V) 0 := by
  set en := Fintype.equivFin (BondBasisIndex F) with hen
  set N := Fintype.card (BondBasisIndex F) with hN
  set b : Fin N → ChordBond F := fun l => (en.symm l).1 with hb
  set e : Fin N → BondVector := fun l => EuclideanSpace.single (en.symm l).2 1 with he
  have h1 := (h N fun l => bondDirection (b l) (e l)).contDiffAt (n := 3)
  set tau : StepVariable (finiteCells F) →L[ℝ] (Fin N → ℝ) :=
    ContinuousLinearMap.pi fun l => (EuclideanSpace.proj (𝕜 := ℝ) (en.symm l).2).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ChordBond F => BondVector) (en.symm l).1)
    with htau
  have h2 : ContDiffAt ℝ 3 (chartRestriction a w V (fun l => bondDirection (b l) (e l))) (tau 0) := by
    simpa using h1
  have h3 := ContDiffAt.comp (0 : StepVariable (finiteCells F)) h2 tau.contDiff.contDiffAt
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun η => ?_)
  simp only [Function.comp]
  rw [chartRestriction_bondDirection]
  congr 1
  conv_lhs => rw [eq_sum_bondVariation_basis η]
  refine Fintype.sum_equiv en _ _ fun p => ?_
  simp [htau, hb, he]
def bondPlane (b b' : ChordBond F) (e e' : BondVector) :
    (Fin 2 → ℝ) →L[ℝ] StepVariable (finiteCells F) :=
  ((ContinuousLinearMap.proj (0 : Fin 2)).smulRight (bondVariation b e : StepVariable (finiteCells F))) +
    ((ContinuousLinearMap.proj (1 : Fin 2)).smulRight (bondVariation b' e' : StepVariable (finiteCells F)))
theorem chartMixedDeriv_bondDirection {a : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top}
    (hA : ContDiffAt ℝ 3 (chartedEnergyAt a w V) 0) (b b' : ChordBond F) (e e' : BondVector) :
    chartMixedDeriv a w V ![bondDirection b e, bondDirection b' e'] =
      fderiv ℝ (fderiv ℝ (chartedEnergyAt a w V)) 0 (bondVariation b e) (bondVariation b' e') := by
  have h1 : chartRestriction a w V ![bondDirection b e, bondDirection b' e'] =
      chartedEnergyAt a w V ∘ bondPlane b b' e e' := by
    funext σ
    have hq : (![bondDirection b e, bondDirection b' e'] : Fin 2 → ChartDirection F) =
        fun l => bondDirection ((![b, b'] : Fin 2 → ChordBond F) l) ((![e, e'] : Fin 2 → BondVector) l) := by
      funext l
      fin_cases l <;> rfl
    rw [hq, chartRestriction_bondDirection]
    simp only [Function.comp, bondPlane, Fin.sum_univ_two]
    rfl
  unfold chartMixedDeriv
  rw [h1, iteratedFDeriv_two_apply]
  have h0 : bondPlane b b' e e' 0 = 0 := map_zero _
  have h2 := fderiv_fderiv_comp_clm (Φ := chartedEnergyAt a w V) (bondPlane b b' e e') (x := 0)
    (by rw [h0]; exact hA) (Pi.single 1 1) (Pi.single 0 1)
  change fderiv ℝ (fderiv ℝ (chartedEnergyAt a w V ∘ bondPlane b b' e e')) 0 (Pi.single 0 1)
    (Pi.single 1 1) = _
  rw [h2, h0]
  simp [bondPlane]
theorem cellSupDist_le_directionDiameter (q : Fin 2 → ChartDirection F) :
    cellSupDist (directionCell (q 0)) (directionCell (q 1)) ≤ directionDiameter q := by
  unfold directionDiameter
  have h1 : cellSupDist (directionCell (q 0)) (directionCell (q 1)) ≤ Finset.univ.sup fun l' : Fin 2 =>
      cellSupDist (directionCell (q 0)) (directionCell (q l')) :=
    Finset.le_sup (f := fun l' : Fin 2 => cellSupDist (directionCell (q 0)) (directionCell (q l')))
      (Finset.mem_univ 1)
  exact h1.trans (Finset.le_sup (f := fun l : Fin 2 => Finset.univ.sup fun l' : Fin 2 =>
    cellSupDist (directionCell (q l)) (directionCell (q l'))) (Finset.mem_univ 0))
theorem abs_secondDerivAlong_le_of_unit {f : StepVariable (finiteCells F) → ℝ} (hf : ContDiffAt ℝ 3 f 0)
    {b b' : ChordBond F} {B : ℝ}
    (h : ∀ e e' : BondVector, ‖e‖ = 1 → ‖e'‖ = 1 →
      |fderiv ℝ (fderiv ℝ f) 0 (bondVariation b' e') (bondVariation b e)| ≤ B) (hB : 0 ≤ B)
    (e e' : BondVector) :
    |secondDerivAlong f 0 (bondVariation b e) (bondVariation b' e')| ≤ B * ‖e‖ * ‖e'‖ := by
  unfold secondDerivAlong
  rw [fderiv_fderiv_apply_eq hf]
  by_cases he : e = 0
  · subst he
    have : (bondVariation b 0 : StepVariable (finiteCells F)) = 0 := by simp [bondVariation]
    simp [this]
  by_cases he' : e' = 0
  · subst he'
    have : (bondVariation b' 0 : StepVariable (finiteCells F)) = 0 := by simp [bondVariation]
    simp [this]
  have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
  have hn' : ‖e'‖ ≠ 0 := norm_ne_zero_iff.2 he'
  have u1 : ‖(‖e‖⁻¹ • e : BondVector)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have u2 : ‖(‖e'‖⁻¹ • e' : BondVector)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn']
  have e1 : (bondVariation b e : StepVariable (finiteCells F)) = ‖e‖ • bondVariation b (‖e‖⁻¹ • e) := by
    unfold bondVariation
    rw [← Pi.single_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]
  have e2 : (bondVariation b' e' : StepVariable (finiteCells F)) =
      ‖e'‖ • bondVariation b' (‖e'‖⁻¹ • e') := by
    unfold bondVariation
    rw [← Pi.single_smul, smul_smul, mul_inv_cancel₀ hn', one_smul]
  have h1 := h _ _ u1 u2
  rw [e1, e2, map_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    abs_mul, abs_mul, abs_norm, abs_norm]
  have hp := norm_nonneg e
  have hp' := norm_nonneg e'
  nlinarith [mul_nonneg hp hp']
theorem sum_chordBonds_exp_le {γ S : ℝ} (z : F.Site F.depth)
    (hS : ∀ A : Finset (F.Site F.depth), ∑ u ∈ A, Real.exp (-(γ * siteSupDist z u)) ≤ S) :
    ∑ b : ChordBond F, Real.exp (-(γ * siteSupDist z b.1.1)) ≤ 4 * S := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.RemainderExponent.sum_chordBonds_exp_le <;> assumption
theorem decay_mul_exp_sub_one_le {δ₁ κ d s γ L : ℝ} (hδ : 0 < δ₁) (hκ : 0 < κ) (hκ₀ : κ ≤ δ₁ / 4)
    (hd : 0 ≤ d) (hL : 0 < L) (hγ : γ = δ₁ / (4 * L)) (hs : s ≤ L * (d + 1)) :
    Real.exp (-(δ₁ * d)) * (Real.exp (2 * κ * d) - 1) ≤
      κ * (8 / δ₁ * Real.exp (δ₁ / 4)) * Real.exp (-(γ * s)) := by
  set t : ℝ := 2 * κ * d with ht
  have ht0 : 0 ≤ t := by positivity
  have h1 : Real.exp t - 1 ≤ t * Real.exp t := by
    have h2 := Real.add_one_le_exp (-t)
    have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have h4 := Real.exp_pos t
    nlinarith
  have h2 : Real.exp (-(δ₁ * d)) * (Real.exp t - 1) ≤ t * Real.exp (-(δ₁ / 2 * d)) := by
    calc _ ≤ Real.exp (-(δ₁ * d)) * (t * Real.exp t) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = t * (Real.exp (-(δ₁ * d)) * Real.exp t) := by ring
      _ = t * Real.exp (-(δ₁ * d) + t) := by rw [Real.exp_add]
      _ ≤ t * Real.exp (-(δ₁ / 2 * d)) := by
          refine mul_le_mul_of_nonneg_left ?_ ht0
          rw [Real.exp_le_exp, ht]
          nlinarith
  set u : ℝ := δ₁ / 4 * d with hu
  have h3 : u * Real.exp (-u) ≤ 1 := by
    have h4 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have h5 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
    have h6 := Real.exp_pos (-u)
    nlinarith
  have h4 : t * Real.exp (-u) ≤ κ * (8 / δ₁) := by
    have e : t = κ * (8 / δ₁) * u := by
      rw [ht, hu]
      field_simp
      ring
    rw [e]
    have hk : 0 ≤ κ * (8 / δ₁) := by positivity
    calc _ = κ * (8 / δ₁) * (u * Real.exp (-u)) := by ring
      _ ≤ κ * (8 / δ₁) * 1 := mul_le_mul_of_nonneg_left h3 hk
      _ = _ := mul_one _
  have h5 : Real.exp (-u) ≤ Real.exp (δ₁ / 4) * Real.exp (-(γ * s)) := by
    rw [← Real.exp_add, Real.exp_le_exp, hu, hγ]
    have h6 : δ₁ / (4 * L) * s ≤ δ₁ / 4 * (d + 1) := by
      have : δ₁ / (4 * L) * s ≤ δ₁ / (4 * L) * (L * (d + 1)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      refine this.trans (le_of_eq ?_)
      field_simp
    nlinarith
  have e : Real.exp (-(δ₁ / 2 * d)) = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add, hu]
    congr 1
    ring
  calc _ ≤ t * Real.exp (-(δ₁ / 2 * d)) := h2
    _ = (t * Real.exp (-u)) * Real.exp (-u) := by rw [e]; ring
    _ ≤ (κ * (8 / δ₁)) * (Real.exp (δ₁ / 4) * Real.exp (-(γ * s))) :=
        mul_le_mul h4 h5 (Real.exp_pos _).le (by positivity)
    _ = _ := by ring
set_option maxHeartbeats 2000000 in
theorem chartEnergyHessianRowsEventually_of (hK : ChartEnergyKernelBound) (hS : ExpDecaySumBounded)
    (hD : SupDistCellComparison) : ChartEnergyHessianRowsEventually := by
  intro a ha
  refine ⟨2 ^ 40, fun L hL hL0 c hc => ?_⟩
  obtain ⟨Ck, hCk, hker⟩ := hK a L c ha hL hL0 hc
  have hδ₁ : 0 < c.δ₁ := hc.positivity.1
  have hlam : 0 < c.lam := hc.positivity.2.2.1
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL.pos
  set γ : ℝ := c.δ₁ / (4 * L) with hγ
  have hγ0 : 0 < γ := by positivity
  obtain ⟨S, hSpos, hSb⟩ := hS γ hγ0
  set Q : ℝ := Ck 2 * (8 / c.δ₁ * Real.exp (c.δ₁ / 4)) * (4 * S) with hQ
  have hQ0 : 0 < Q := by
    have := hCk 2
    positivity
  set γ₂ : ℝ := c.δ₁ / L with hγ₂
  have hγ₂0 : 0 < γ₂ := by positivity
  obtain ⟨S₂, hS₂pos, hS₂b⟩ := hS γ₂ hγ₂0
  refine ⟨Ck 2 * Real.exp c.δ₁ * (4 * S₂), fun Ct hCt => ?_⟩
  refine ⟨min (c.δ₁ / 4) (c.lam / (16 * Q)), lt_min (by positivity) (by positivity),
    fun κ hκ hκ₀ => ?_⟩
  refine ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun nss _ => ⟨1, one_pos, fun σ _ _ p _ =>
    ⟨0, fun Cs _ E _ => ⟨0, fun n₀ _ => ⟨0, fun CE _ => ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩⟩⟩⟩
  intro F V hF
  have hFL : F.blockSide = L := hF.1
  obtain ⟨n, hn, hside⟩ := hF.2
  have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hside]; omega
  have hOddF : Odd F.blockSide := hFL ▸ hL
  refine ⟨fun b b' => Ck 2 * Real.exp (-(c.δ₁ * chordBondDist F b b')), ?_, ?_, ?_, ?_⟩
  · intro b b'
    have : chordBondDist F b b' = chordBondDist F b' b := by
      have h := (hD.1 F F.top (enclosingCell b.1.1) (enclosingCell b'.1.1) (enclosingCell b.1.1)).2.1
      change ((siteSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℕ) : ℝ) =
        ((siteSupDist (enclosingCell b'.1.1) (enclosingCell b.1.1) : ℕ) : ℝ)
      rw [h]
    change Ck 2 * Real.exp (-(c.δ₁ * chordBondDist F b b')) =
      Ck 2 * Real.exp (-(c.δ₁ * chordBondDist F b' b))
    rw [this]
  · intro w hw
    have hall := hker F w V hF hw
    have hA : ContDiffAt ℝ 3 (chartedEnergyAt a w V) 0 :=
      contDiffAt_chartedEnergyAt fun k q => (hall k q).1
    refine ⟨hA, fun b b' e e' => ?_⟩
    refine abs_secondDerivAlong_le_of_unit hA (fun e e' he he' => ?_) (by have := hCk 2; positivity) e e'
    rw [← chartMixedDeriv_bondDirection hA b' b e' e]
    have h1 := (hall 2 ![bondDirection b' e', bondDirection b e]).2 le_rfl (by
      intro l
      fin_cases l
      · change ‖toImaginaryCLM e'‖ = 1
        rw [norm_toImaginaryCLM]
        exact he'
      · change ‖toImaginaryCLM e‖ = 1
        rw [norm_toImaginaryCLM]
        exact he)
    refine h1.trans ?_
    have h2 : cellSupDist (enclosingCell b'.1.1) (enclosingCell b.1.1) ≤
        directionDiameter ![bondDirection b' e', bondDirection b e] :=
      cellSupDist_le_directionDiameter ![bondDirection b' e', bondDirection b e]
    have h3 : (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ) =
        (cellSupDist (enclosingCell b'.1.1) (enclosingCell b.1.1) : ℝ) := by
      have h := (hD.1 F F.top (enclosingCell b.1.1) (enclosingCell b'.1.1) (enclosingCell b.1.1)).2.1
      change ((siteSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℕ) : ℝ) =
        ((siteSupDist (enclosingCell b'.1.1) (enclosingCell b.1.1) : ℕ) : ℝ)
      rw [h]
    refine mul_le_mul_of_nonneg_left ?_ (hCk 2).le
    rw [Real.exp_le_exp]
    change _ ≤ -(c.δ₁ * (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ))
    rw [h3]
    have h4 : (cellSupDist (enclosingCell b'.1.1) (enclosingCell b.1.1) : ℝ) ≤
        directionDiameter ![bondDirection b' e', bondDirection b e] := by
      exact_mod_cast h2
    have := mul_le_mul_of_nonneg_left h4 hδ₁.le
    linarith
  · intro b
    have hterm : ∀ b' : ChordBond F, Ck 2 * Real.exp (-(c.δ₁ * chordBondDist F b b')) *
        (Real.exp (2 * κ * chordBondDist F b b') - 1) ≤
        Ck 2 * (κ * (8 / c.δ₁ * Real.exp (c.δ₁ / 4))) *
          Real.exp (-(γ * siteSupDist b.1.1 b'.1.1)) := by
      intro b'
      have hup := ((hD.2.2 F hOddF hpos).2.1 b.1.1 b'.1.1)
      rw [hFL] at hup
      have h1 := decay_mul_exp_sub_one_le (s := siteSupDist b.1.1 b'.1.1) hδ₁ hκ
        (hκ₀.trans (min_le_left _ _))
        (Nat.cast_nonneg _ : (0 : ℝ) ≤ chordBondDist F b b') hLr hγ hup
      rw [mul_assoc]
      calc _ ≤ Ck 2 * (κ * (8 / c.δ₁ * Real.exp (c.δ₁ / 4)) *
            Real.exp (-(γ * siteSupDist b.1.1 b'.1.1))) :=
            mul_le_mul_of_nonneg_left h1 (hCk 2).le
        _ = _ := by ring
    have hsum := sum_chordBonds_exp_le (F := F) b.1.1 fun A => hSb F F.depth b.1.1 A
    have hκq : κ * Q ≤ c.lam / 16 := by
      have h1 : κ ≤ c.lam / (16 * Q) := hκ₀.trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at h1
      linarith
    calc _ ≤ ∑ b' : ChordBond F, Ck 2 * (κ * (8 / c.δ₁ * Real.exp (c.δ₁ / 4))) *
          Real.exp (-(γ * siteSupDist b.1.1 b'.1.1)) := Finset.sum_le_sum fun b' _ => hterm b'
      _ = Ck 2 * (κ * (8 / c.δ₁ * Real.exp (c.δ₁ / 4))) *
          ∑ b' : ChordBond F, Real.exp (-(γ * siteSupDist b.1.1 b'.1.1)) := by rw [Finset.mul_sum]
      _ ≤ Ck 2 * (κ * (8 / c.δ₁ * Real.exp (c.δ₁ / 4))) * (4 * S) :=
          mul_le_mul_of_nonneg_left hsum (by have := hCk 2; positivity)
      _ = κ * Q := by rw [hQ]; ring
      _ ≤ _ := hκq
  · intro b
    have hterm : ∀ b' : ChordBond F, Ck 2 * Real.exp (-(c.δ₁ * chordBondDist F b b')) ≤
        Ck 2 * Real.exp c.δ₁ * Real.exp (-(γ₂ * siteSupDist b.1.1 b'.1.1)) := by
      intro b'
      have hup := ((hD.2.2 F hOddF hpos).2.1 b.1.1 b'.1.1)
      rw [hFL] at hup
      have hup' : (siteSupDist b.1.1 b'.1.1 : ℝ) ≤ L * (chordBondDist F b b' + 1) := hup
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (hCk 2).le
      rw [← Real.exp_add, Real.exp_le_exp, hγ₂]
      have h1 : c.δ₁ / L * siteSupDist b.1.1 b'.1.1 ≤ c.δ₁ / L * (L * (chordBondDist F b b' + 1)) :=
        mul_le_mul_of_nonneg_left hup' (by positivity)
      have h2 : c.δ₁ / L * (L * (chordBondDist F b b' + 1)) = c.δ₁ * (chordBondDist F b b' + 1) := by
        field_simp
      nlinarith
    have hsum := sum_chordBonds_exp_le (F := F) b.1.1 fun A => hS₂b F F.depth b.1.1 A
    calc _ ≤ ∑ b' : ChordBond F, Ck 2 * Real.exp c.δ₁ * Real.exp (-(γ₂ * siteSupDist b.1.1 b'.1.1)) :=
          Finset.sum_le_sum fun b' _ => hterm b'
      _ = Ck 2 * Real.exp c.δ₁ * ∑ b' : ChordBond F, Real.exp (-(γ₂ * siteSupDist b.1.1 b'.1.1)) := by
          rw [Finset.mul_sum]
      _ ≤ Ck 2 * Real.exp c.δ₁ * (4 * S₂) :=
          mul_le_mul_of_nonneg_left hsum (by have := hCk 2; positivity)
      _ ≤ _ := hCt
end ChartEnergyRows
end ColdStepAtMirrorFrames
end YangMills.Construction
end
