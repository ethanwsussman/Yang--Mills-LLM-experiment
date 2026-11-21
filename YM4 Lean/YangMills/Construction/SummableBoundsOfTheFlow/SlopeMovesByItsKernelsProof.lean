import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeMovesByItsKernels
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.SummableBoundsOfTheFlow
variable {F : BlockFrame}
private theorem expUnit_at_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem leftTranslate_by_zero (V : F.GaugeField F.top) :
    leftTranslate (fun _ _ => (0 : imaginaryQuaternions)) V = V := by
  funext y i
  simp [leftTranslate, expUnit_at_zero]
abbrev _root_.YangMills.SharedProofs.p46723 := @leftTranslate_by_zero
private def pairRestriction (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top)
    (p p' : F.Site F.depth × Fin 4 × imaginaryQuaternions) : (Fin 2 → ℝ) → ℝ :=
  chartRestriction a w V ![Sum.inl p, Sum.inl p']
private theorem pairRestriction_eq (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top)
    (p p' : F.Site F.depth × Fin 4 × imaginaryQuaternions) (σ : Fin 2 → ℝ) :
    pairRestriction a w V p p' σ = chartedEnergy a (fun x i => w x i + (σ 0 • directionCoordinate (Sum.inl p) x i +
      σ 1 • directionCoordinate (Sum.inl p') x i)) V := by
  unfold pairRestriction chartRestriction
  have hzero : (fun y i => ∑ l, σ l • directionMove ((![Sum.inl p, Sum.inl p'] : Fin 2 → ChartDirection F) l) y i) =
      fun _ _ => (0 : imaginaryQuaternions) := by
    funext y i
    simp [Fin.sum_univ_two, directionMove]
  rw [hzero, leftTranslate_by_zero]
  congr 1
  funext x i
  simp [Fin.sum_univ_two]
private def shiftAlong (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (θ : ℝ)
    (p : F.Site F.depth × Fin 4 × imaginaryQuaternions) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => w x i + θ • directionCoordinate (Sum.inl p : ChartDirection F) x i
private theorem pairRestriction_shiftAlong (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top)
    (p p' : F.Site F.depth × Fin 4 × imaginaryQuaternions) (θ : ℝ) (σ : Fin 2 → ℝ) :
    pairRestriction a (shiftAlong w θ p) V p p' σ = pairRestriction a w V p p' (σ + ![θ, 0]) := by
  rw [pairRestriction_eq, pairRestriction_eq]
  congr 1
  funext x i
  simp only [shiftAlong, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
  module
private theorem chartedSlope_shiftAlong_eq (a θ : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top)
    (p : F.Site F.depth × Fin 4 × imaginaryQuaternions) (b : F.Site F.depth × Fin 4)
    (e : imaginaryQuaternions)
    (hdiff : DifferentiableAt ℝ (pairRestriction a w V p (b.1, b.2, e)) ![θ, 0]) :
    chartedSlope a (shiftAlong w θ p) V b e =
      fderiv ℝ (pairRestriction a w V p (b.1, b.2, e)) ![θ, 0] (Pi.single 1 1) := by
  have hline : (fun u : ℝ => chartedEnergy a (Function.update (shiftAlong w θ p) b.1
      (Function.update (shiftAlong w θ p b.1) b.2 (shiftAlong w θ p b.1 b.2 + u • e))) V) =
      fun u : ℝ => pairRestriction a w V p (b.1, b.2, e) (![θ, 0] + u • Pi.single 1 1) := by
    funext u
    rw [pairRestriction_eq]
    congr 1
    funext x i
    by_cases hx : x = b.1
    · subst hx
      by_cases hi : i = b.2
      · subst hi
        simp [shiftAlong, directionCoordinate]
        abel
      · simp [shiftAlong, directionCoordinate, hi]
        intro h
        exact absurd h.symm hi
    · simp [shiftAlong, directionCoordinate, hx]
      intro h
      exact absurd h.symm hx
  unfold chartedSlope
  rw [hline]
  have hlin : HasDerivAt (fun u : ℝ => (![θ, 0] : Fin 2 → ℝ) + u • Pi.single 1 1) (Pi.single 1 1) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single 1 1 : Fin 2 → ℝ)).const_add (![θ, 0] : Fin 2 → ℝ)
    simpa using this
  have hfd : HasFDerivAt (pairRestriction a w V p (b.1, b.2, e))
      (fderiv ℝ (pairRestriction a w V p (b.1, b.2, e)) ![θ, 0])
      ((![θ, 0] : Fin 2 → ℝ) + (0 : ℝ) • Pi.single 1 1) := by
    simpa using hdiff.hasFDerivAt
  exact (hfd.comp_hasDerivAt (0 : ℝ) hlin).deriv
private theorem analyticAt_of_shiftAlong {a θ : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top}
    {p p' : F.Site F.depth × Fin 4 × imaginaryQuaternions}
    (h : AnalyticAt ℝ (pairRestriction a (shiftAlong w θ p) V p p') 0) :
    AnalyticAt ℝ (pairRestriction a w V p p') ![θ, 0] := by
  have hrw : pairRestriction a w V p p' = fun σ => pairRestriction a (shiftAlong w θ p) V p p' (σ - ![θ, 0]) := by
    funext σ
    rw [pairRestriction_shiftAlong, sub_add_cancel]
  rw [hrw]
  have h1 : AnalyticAt ℝ (fun σ : Fin 2 → ℝ => σ - ![θ, 0]) ![θ, 0] :=
    analyticAt_id.sub analyticAt_const
  have h2 : AnalyticAt ℝ (pairRestriction a (shiftAlong w θ p) V p p')
      ((fun σ : Fin 2 → ℝ => σ - ![θ, 0]) ![θ, 0]) := by
    simpa using h
  exact AnalyticAt.comp (g := pairRestriction a (shiftAlong w θ p) V p p')
    (f := fun σ : Fin 2 → ℝ => σ - ![θ, 0]) h2 h1
private theorem chartMixedDeriv_shiftAlong (a θ : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top)
    (p p' : F.Site F.depth × Fin 4 × imaginaryQuaternions) :
    chartMixedDeriv a (shiftAlong w θ p) V ![Sum.inl p, Sum.inl p'] =
      fderiv ℝ (fderiv ℝ (pairRestriction a w V p p')) ![θ, 0] (Pi.single 0 1) (Pi.single 1 1) := by
  unfold chartMixedDeriv
  have hrw : chartRestriction a (shiftAlong w θ p) V ![Sum.inl p, Sum.inl p'] =
      fun σ => pairRestriction a w V p p' (σ + ![θ, 0]) :=
    funext fun σ => pairRestriction_shiftAlong a w V p p' θ σ
  rw [hrw, iteratedFDeriv_comp_add_right, iteratedFDeriv_two_apply]
  simp
private theorem chartedSlope_sub_le_of_mixedDeriv {a B t : ℝ}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    {p : F.Site F.depth × Fin 4 × imaginaryQuaternions} {b : F.Site F.depth × Fin 4}
    {e : imaginaryQuaternions} (ht : 0 ≤ t)
    (hk : ∀ θ, 0 ≤ θ → θ ≤ t → AnalyticAt ℝ (pairRestriction a (shiftAlong w θ p) V p (b.1, b.2, e)) 0 ∧
      |chartMixedDeriv a (shiftAlong w θ p) V ![Sum.inl p, Sum.inl (b.1, b.2, e)]| ≤ B) :
    |chartedSlope a (shiftAlong w t p) V b e - chartedSlope a (shiftAlong w 0 p) V b e| ≤ B * t := by
  set f := pairRestriction a w V p (b.1, b.2, e) with hf
  have han : ∀ θ, 0 ≤ θ → θ ≤ t → AnalyticAt ℝ f ![θ, 0] := fun θ h0 h1 =>
    analyticAt_of_shiftAlong (hk θ h0 h1).1
  set g : ℝ → ℝ := fun θ => fderiv ℝ f ![θ, 0] (Pi.single 1 1) with hg
  have hline : ∀ θ : ℝ, HasDerivAt (fun u : ℝ => (![u, 0] : Fin 2 → ℝ)) (Pi.single 0 1) θ := by
    intro θ
    have hrw : (fun u : ℝ => (![u, 0] : Fin 2 → ℝ)) = fun u => u • (Pi.single 0 1 : Fin 2 → ℝ) := by
      funext u
      ext l
      fin_cases l <;> simp
    rw [hrw]
    simpa using (hasDerivAt_id θ).smul_const (Pi.single 0 1 : Fin 2 → ℝ)
  have hder : ∀ θ ∈ Set.Icc (0 : ℝ) t, HasDerivWithinAt g
      (fderiv ℝ (fderiv ℝ f) ![θ, 0] (Pi.single 0 1) (Pi.single 1 1)) (Set.Icc 0 t) θ := by
    intro θ hθ
    have h1 : DifferentiableAt ℝ (fderiv ℝ f) ![θ, 0] :=
      ((han θ hθ.1 hθ.2).fderiv).differentiableAt
    have h2 := h1.hasFDerivAt.comp_hasDerivAt θ (hline θ)
    have h3 := h2.clm_apply (hasDerivAt_const θ (Pi.single 1 1 : Fin 2 → ℝ))
    simp only [add_zero, ContinuousLinearMap.map_zero] at h3
    exact h3.hasDerivWithinAt
  have hbound : ∀ θ ∈ Set.Ico (0 : ℝ) t,
      ‖fderiv ℝ (fderiv ℝ f) ![θ, 0] (Pi.single 0 1) (Pi.single 1 1)‖ ≤ B := by
    intro θ hθ
    have := (hk θ hθ.1 hθ.2.le).2
    rwa [chartMixedDeriv_shiftAlong, ← hf, ← Real.norm_eq_abs] at this
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) hder hbound t
    (Set.right_mem_Icc.2 ht)
  rw [sub_zero, Real.norm_eq_abs] at hmv
  rw [chartedSlope_shiftAlong_eq a t w V p b e (han t ht le_rfl).differentiableAt,
    chartedSlope_shiftAlong_eq a 0 w V p b e (han 0 le_rfl ht).differentiableAt]
  exact hmv
theorem chartedSlopeKernelBound_of_chartEnergyKernelBound (hK : ChartEnergyKernelBound) :
    ChartedSlopeKernelBound := by
  intro a L c ha hL hL0 hc
  obtain ⟨Ck, hCk, hker⟩ := hK a L c ha hL hL0 hc
  have hδ₁ : 0 < c.δ₁ := hc.positivity.1
  refine ⟨Ck 2, hCk 2, fun F w w' V hF hpts hoff b e he => ?_⟩
  classical
  set hyb : Finset (F.Site F.depth × Fin 4) → F.Site F.depth → Fin 4 → imaginaryQuaternions :=
    fun A z i => if (z, i) ∈ A then w' z i else w z i with hhyb
  have hstep : ∀ A : Finset (F.Site F.depth × Fin 4),
      |chartedSlope a (hyb A) V b e - chartedSlope a w V b e| ≤
        ∑ b' ∈ A, Ck 2 * Real.exp (-(c.δ₁ * cellSupDist (enclosingCell b.1) (enclosingCell b'.1))) *
          ‖w' b'.1 b'.2 - w b'.1 b'.2‖ := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      have : hyb ∅ = w := by funext z i; simp [hhyb]
      simp [this]
    | insert b₀ A hb₀ ih =>
      rw [Finset.sum_insert hb₀]
      set t := ‖w' b₀.1 b₀.2 - w b₀.1 b₀.2‖ with ht
      have hone : |chartedSlope a (hyb (insert b₀ A)) V b e - chartedSlope a (hyb A) V b e| ≤
          Ck 2 * Real.exp (-(c.δ₁ * cellSupDist (enclosingCell b.1) (enclosingCell b₀.1))) * t := by
        by_cases ht0 : t = 0
        · have h0 : w' b₀.1 b₀.2 = w b₀.1 b₀.2 := by
            have := norm_eq_zero.1 (ht ▸ ht0)
            exact sub_eq_zero.1 this
          have hsame : hyb (insert b₀ A) = hyb A := by
            funext z i
            by_cases hz : (z, i) = b₀
            · subst hz
              simp [hhyb, hb₀, h0]
            · simp [hhyb, Finset.mem_insert, hz]
          rw [hsame, ht0]
          simp
        · have htp : 0 < t := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ht0)
          set X : imaginaryQuaternions := t⁻¹ • (w' b₀.1 b₀.2 - w b₀.1 b₀.2) with hX
          have hX1 : ‖X‖ = 1 := by
            rw [hX, norm_smul, norm_inv, Real.norm_of_nonneg htp.le, ← ht]
            field_simp
          set p : F.Site F.depth × Fin 4 × imaginaryQuaternions := (b₀.1, b₀.2, X) with hp
          have hA0 : hyb A b₀.1 b₀.2 = w b₀.1 b₀.2 := by simp [hhyb, hb₀]
          have hsh : ∀ θ : ℝ, ∀ z i, shiftAlong (hyb A) θ p z i =
              if (z, i) = b₀ then w b₀.1 b₀.2 + θ • X else hyb A z i := by
            intro θ z i
            by_cases hz : (z, i) = b₀
            · subst hz
              simp only [shiftAlong, directionCoordinate, hp, if_true]
              simp [hA0]
            · have hne : ¬ (b₀.1 = z ∧ b₀.2 = i) := fun h => hz (by
                rw [← h.1, ← h.2])
              simp [shiftAlong, directionCoordinate, hp, hz, hne]
          have hend : shiftAlong (hyb A) t p = hyb (insert b₀ A) := by
            funext z i
            rw [hsh]
            by_cases hz : (z, i) = b₀
            · subst hz
              simp only [if_true]
              have : t • X = w' (z, i).1 (z, i).2 - w (z, i).1 (z, i).2 := by
                rw [hX, smul_smul, mul_inv_cancel₀ ht0, one_smul]
              rw [this]
              simp [hhyb]
            · simp [hhyb, Finset.mem_insert, hz]
          have hstart : shiftAlong (hyb A) 0 p = hyb A := by
            funext z i
            simp [shiftAlong]
          have hk : ∀ θ, 0 ≤ θ → θ ≤ t →
              AnalyticAt ℝ (pairRestriction a (shiftAlong (hyb A) θ p) V p (b.1, b.2, e)) 0 ∧
              |chartMixedDeriv a (shiftAlong (hyb A) θ p) V ![Sum.inl p, Sum.inl (b.1, b.2, e)]| ≤
                Ck 2 * Real.exp (-(c.δ₁ * cellSupDist (enclosingCell b.1) (enclosingCell b₀.1))) := by
            intro θ h0 h1
            have hpt : IsAdmissibleChartPoint L c.σA (shiftAlong (hyb A) θ p) V := by
              apply hpts
              intro z i
              rw [hsh]
              by_cases hz : (z, i) = b₀
              · subst hz
                refine ⟨θ / t, by positivity, (div_le_one htp).2 h1, ?_⟩
                simp only [if_true]
                have : θ • X = (θ / t) • (w' (z, i).1 (z, i).2 - w (z, i).1 (z, i).2) := by
                  rw [hX, smul_smul, div_eq_mul_inv]
                rw [this]
              · simp only [hz, if_false, hhyb]
                by_cases hzA : (z, i) ∈ A
                · exact ⟨1, zero_le_one, le_rfl, by simp [hzA]⟩
                · exact ⟨0, le_rfl, zero_le_one, by simp [hzA]⟩
            obtain ⟨h2, h3⟩ := hker F _ V hF hpt 2 ![Sum.inl p, Sum.inl (b.1, b.2, e)]
            refine ⟨h2, ?_⟩
            have hu : ∀ l, ‖directionVector ((![Sum.inl p, Sum.inl (b.1, b.2, e)] : Fin 2 → ChartDirection F) l)‖ = 1 := by
              intro l
              fin_cases l
              · simpa [directionVector, hp] using hX1
              · simpa [directionVector] using he
            refine (h3 le_rfl hu).trans ?_
            have hd : cellSupDist (enclosingCell b.1) (enclosingCell b₀.1) ≤
                directionDiameter (![Sum.inl p, Sum.inl (b.1, b.2, e)] : Fin 2 → ChartDirection F) := by
              have h5 := Finset.le_sup (f := fun l' : Fin 2 => cellSupDist
                (directionCell ((![Sum.inl p, Sum.inl (b.1, b.2, e)] : Fin 2 → ChartDirection F) 1))
                (directionCell ((![Sum.inl p, Sum.inl (b.1, b.2, e)] : Fin 2 → ChartDirection F) l'))) (Finset.mem_univ (0 : Fin 2))
              have h6 := Finset.le_sup (f := fun l : Fin 2 => Finset.univ.sup fun l' : Fin 2 => cellSupDist
                (directionCell ((![Sum.inl p, Sum.inl (b.1, b.2, e)] : Fin 2 → ChartDirection F) l))
                (directionCell ((![Sum.inl p, Sum.inl (b.1, b.2, e)] : Fin 2 → ChartDirection F) l'))) (Finset.mem_univ (1 : Fin 2))
              exact h5.trans h6
            have hd' : (cellSupDist (enclosingCell b.1) (enclosingCell b₀.1) : ℝ) ≤
                (directionDiameter (![Sum.inl p, Sum.inl (b.1, b.2, e)] : Fin 2 → ChartDirection F) : ℝ) := by
              exact_mod_cast hd
            have hCk2 := (hCk 2).le
            gcongr
          have := chartedSlope_sub_le_of_mixedDeriv (p := p) (b := b) (e := e) htp.le hk
          rwa [hend, hstart] at this
      calc |chartedSlope a (hyb (insert b₀ A)) V b e - chartedSlope a w V b e|
          ≤ |chartedSlope a (hyb (insert b₀ A)) V b e - chartedSlope a (hyb A) V b e| +
            |chartedSlope a (hyb A) V b e - chartedSlope a w V b e| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add hone ih
  have hfin : hyb (chordBonds (finiteCells F)) = w' := by
    funext z i
    by_cases hz : (z, i) ∈ chordBonds (finiteCells F)
    · simp [hhyb, hz]
    · simp only [hhyb, hz, if_false]
      exact (hoff (z, i) hz).symm
  have := hstep (chordBonds (finiteCells F))
  rwa [hfin] at this
end YangMills.Construction.SummableBoundsOfTheFlow
end
