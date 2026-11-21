import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.SecondDerivativeThroughTheChart
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeThroughTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace ChartDerivative
def expDerivAlong (v : imaginaryQuaternions) (e : BondVector) : ℍ[ℝ] :=
  deriv (fun τ : ℝ => ((expUnit (v + τ • toImaginary e) * (expUnit v)⁻¹ : UnitQuaternion) : ℍ[ℝ])) 0
open Classical in
def liftToImaginary (v : imaginaryQuaternions) (e : BondVector) : imaginaryQuaternions :=
  if h : ∃ X : imaginaryQuaternions, (X : ℍ[ℝ]) = expDerivAlong v e then h.choose else 0
variable {F : BlockFrame}
def bondRelativeValue (W₀ : F.GaugeField F.depth) (b : F.Site F.depth × Fin 4) (W : F.GaugeField F.depth) : ℍ[ℝ] :=
  ((W b.1 b.2 * (W₀ b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])
theorem coe_bondSpread {k : ℕ} (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) (b : F.Site F.depth × Fin 4) :
    ((bondSpread c X τ b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
      ∑ l, if c l = b then τ l • (X l : ℍ[ℝ]) else 0 := by
  classical
  simp only [bondSpread]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e : (c l = (b.1, b.2)) ↔ c l = b := by simp
  by_cases h : c l = b
  · rw [if_pos h, if_pos (e.2 h)]
    rfl
  · rw [if_neg h, if_neg (fun h' => h (e.1 h'))]
    rfl
theorem bondRelativeValue_leftTranslate {k : ℕ} (W₀ : F.GaugeField F.depth) (b : F.Site F.depth × Fin 4)
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) :
    bondRelativeValue W₀ b (leftTranslate (bondSpread c X τ) W₀) =
      NormedSpace.exp (∑ l, if c l = b then τ l • (X l : ℍ[ℝ]) else 0) := by
  unfold bondRelativeValue leftTranslate
  rw [mul_inv_cancel_right, ← coe_bondSpread]
  rfl
theorem contDiffThree_bondCoordinate (W₀ : F.GaugeField F.depth) (b : F.Site F.depth × Fin 4) :
    ContDiffThreeAlongBonds (bondRelativeValue W₀ b) W₀ := by
  intro k c X
  have hf : (fun τ : Fin k → ℝ => bondRelativeValue W₀ b (leftTranslate (bondSpread c X τ) W₀)) =
      fun τ => NormedSpace.exp (∑ l, if c l = b then τ l • (X l : ℍ[ℝ]) else 0) := by
    funext τ
    exact bondRelativeValue_leftTranslate W₀ b c X τ
  rw [hf]
  have hlin : ContDiff ℝ 3 (fun τ : Fin k → ℝ => ∑ l, if c l = b then τ l • (X l : ℍ[ℝ]) else 0) := by
    refine ContDiff.sum fun l _ => ?_
    split_ifs
    · exact (contDiff_apply ℝ ℝ l).smul contDiff_const
    · exact contDiff_const
  have hexp : ∀ q : ℍ[ℝ], ContDiffAt ℝ 3 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) q := fun q =>
    (NormedSpace.exp_analytic (𝕂 := ℝ) q).contDiffAt
  exact ContDiffAt.comp (0 : Fin k → ℝ) (hexp _) hlin.contDiffAt
end ChartDerivative
open ChartDerivative in
theorem derivThroughChart_of_bounds (hSD : ChartSecondDerivBound)
    (hLC : ImaginaryCoordinatesIsometric) : DerivThroughChart := by
  classical
  obtain ⟨C, hC, hsd⟩ := hSD
  refine ⟨C, liftToImaginary, hC, ?_⟩
  intro F V w G hw hG b e
  set W₀ := chartedField w V with hW₀
  let Gh : F.GaugeField F.depth → ℝ × ℍ[ℝ] := fun W => (G W, bondRelativeValue W₀ b.1 W)
  have hGh : ContDiffThreeAlongBonds Gh W₀ := fun k c X =>
    (hG k c X).prodMk (contDiffThree_bondCoordinate W₀ b.1 k c X)
  obtain ⟨hcd, hex, _⟩ := hsd F V w (ℝ × ℍ[ℝ]) Gh hw hGh
  obtain ⟨X, _, _, hX, _, _, h1, _⟩ := hex b b e e
  have hdiff : DifferentiableAt ℝ (readInChart Gh w V) 0 := hcd.differentiableAt (by norm_num)
  have hfst : fderiv ℝ (readInChart G w V) 0 (bondVariation b e) =
      (fderiv ℝ (readInChart Gh w V) 0 (bondVariation b e)).1 := by
    have := ((ContinuousLinearMap.fst ℝ ℝ ℍ[ℝ]).hasFDerivAt.comp 0 hdiff.hasFDerivAt).fderiv
    have e1 : readInChart G w V = (ContinuousLinearMap.fst ℝ ℝ ℍ[ℝ]) ∘ readInChart Gh w V := rfl
    rw [e1, this]
    rfl
  have hsnd : fderiv ℝ (readInChart (bondRelativeValue W₀ b.1) w V) 0 (bondVariation b e) =
      (fderiv ℝ (readInChart Gh w V) 0 (bondVariation b e)).2 := by
    have := ((ContinuousLinearMap.snd ℝ ℝ ℍ[ℝ]).hasFDerivAt.comp 0 hdiff.hasFDerivAt).fderiv
    have e1 : readInChart (bondRelativeValue W₀ b.1) w V =
        (ContinuousLinearMap.snd ℝ ℝ ℍ[ℝ]) ∘ readInChart Gh w V := rfl
    rw [e1, this]
    rfl
  set Ψ : (Fin 1 → ℝ) → ℝ × ℍ[ℝ] := fun τ => Gh (leftTranslate (bondSpread ![b.1] ![X] τ) W₀) with hΨ
  have hΨd : DifferentiableAt ℝ Ψ 0 := (hGh 1 ![b.1] ![X]).differentiableAt (by norm_num)
  have hu : bondDeriv Gh W₀ ![b.1] ![X] = fderiv ℝ Ψ 0 (Pi.single 0 1) := by
    unfold bondDeriv
    rw [iteratedFDeriv_one_apply]
  have hG1 : bondDeriv G W₀ ![b.1] ![X] = (fderiv ℝ Ψ 0 (Pi.single 0 1)).1 := by
    unfold bondDeriv
    rw [iteratedFDeriv_one_apply]
    have := ((ContinuousLinearMap.fst ℝ ℝ ℍ[ℝ]).hasFDerivAt.comp 0 hΨd.hasFDerivAt).fderiv
    have e1 : (fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![b.1] ![X] τ) W₀)) =
        (ContinuousLinearMap.fst ℝ ℝ ℍ[ℝ]) ∘ Ψ := rfl
    rw [e1, this]
    rfl
  have hG2 : (fderiv ℝ Ψ 0 (Pi.single 0 1)).2 = (X : ℍ[ℝ]) := by
    have h2 := ((ContinuousLinearMap.snd ℝ ℝ ℍ[ℝ]).hasFDerivAt.comp 0 hΨd.hasFDerivAt).fderiv
    have e1 : (ContinuousLinearMap.snd ℝ ℝ ℍ[ℝ]) ∘ Ψ =
        (fun s : ℝ => NormedSpace.exp (s • (X : ℍ[ℝ]))) ∘
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) := by
      funext τ
      show bondRelativeValue W₀ b.1 (leftTranslate (bondSpread ![b.1] ![X] τ) W₀) = _
      rw [bondRelativeValue_leftTranslate]
      simp
    have h3 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (X : ℍ[ℝ]))) (X : ℍ[ℝ])
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) 0) := by
      have := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : ℍ[ℝ]) (0 : ℝ)
      simpa using this
    have h4 := (h3.hasFDerivAt.comp (0 : Fin 1 → ℝ)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt).fderiv
    rw [e1] at h2
    have h5 := congrArg (fun T => T (Pi.single 0 1)) (h2.symm.trans h4)
    have h6 : (ContinuousLinearMap.snd ℝ ℝ ℍ[ℝ]).comp (fderiv ℝ Ψ 0) (Pi.single 0 1) =
        (fderiv ℝ Ψ 0 (Pi.single 0 1)).2 := rfl
    rw [h6] at h5
    rw [h5]
    simp
  have hsl : fderiv ℝ (readInChart (bondRelativeValue W₀ b.1) w V) 0 (bondVariation b e) =
      expDerivAlong (w b.1.1 b.1.2) e := by
    have hd2 : DifferentiableAt ℝ (readInChart (bondRelativeValue W₀ b.1) w V) 0 := by
      have e1 : readInChart (bondRelativeValue W₀ b.1) w V =
          (ContinuousLinearMap.snd ℝ ℝ ℍ[ℝ]) ∘ readInChart Gh w V := rfl
      rw [e1]
      exact (ContinuousLinearMap.snd ℝ ℝ ℍ[ℝ]).differentiableAt.comp 0 hdiff
    have hline : (fun τ : ℝ => ((expUnit (w b.1.1 b.1.2 + τ • toImaginary e) *
        (expUnit (w b.1.1 b.1.2))⁻¹ : UnitQuaternion) : ℍ[ℝ])) =
        fun τ : ℝ => readInChart (bondRelativeValue W₀ b.1) w V
          (τ • (bondVariation b e : StepVariable (finiteCells F))) := by
      funext τ
      have hco : stepCoordinates (τ • (bondVariation b e : StepVariable (finiteCells F))) b.1.1 b.1.2 =
          τ • toImaginary e := by
        have hb : (b.1.1, b.1.2) ∈ chordBonds (finiteCells F) := b.2
        unfold stepCoordinates
        rw [dif_pos hb]
        have e2 : (τ • (bondVariation b e : StepVariable (finiteCells F))) ⟨(b.1.1, b.1.2), hb⟩ = τ • e := by
          simp [bondVariation]
        rw [e2]
        exact hLC.2.1 τ e
      have hnt : ¬ IsAxialTreeBond (b.1.1, b.1.2) := by
        have hb := b.2
        unfold chordBonds at hb
        exact (Finset.mem_filter.1 hb).2
      unfold readInChart bondRelativeValue
      rw [hW₀]
      simp only [chartedField]
      rw [hco]
      by_cases hc : IsCrossingBond (b.1.1, b.1.2)
      · simp only [if_pos hc, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
      · simp only [if_neg hc, if_neg hnt]
    unfold expDerivAlong
    rw [hline]
    have h1' : HasDerivAt (fun τ : ℝ => τ • (bondVariation b e : StepVariable (finiteCells F)))
        (bondVariation b e) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (bondVariation b e : StepVariable (finiteCells F))
    have h2' : HasFDerivAt (readInChart (bondRelativeValue W₀ b.1) w V)
        (fderiv ℝ (readInChart (bondRelativeValue W₀ b.1) w V) 0)
        ((fun τ : ℝ => τ • (bondVariation b e : StepVariable (finiteCells F))) 0) := by
      simpa using hd2.hasFDerivAt
    exact (h2'.comp_hasDerivAt (0 : ℝ) h1').deriv.symm
  have hval : (X : ℍ[ℝ]) = expDerivAlong (w b.1.1 b.1.2) e := by
    rw [← hsl, hsnd, h1, hu, hG2]
  have hT : liftToImaginary (w b.1.1 b.1.2) e = X := by
    have hex' : ∃ X' : imaginaryQuaternions, (X' : ℍ[ℝ]) = expDerivAlong (w b.1.1 b.1.2) e := ⟨X, hval⟩
    unfold liftToImaginary
    rw [dif_pos hex']
    exact Subtype.ext (hex'.choose_spec.trans hval.symm)
  rw [hT]
  refine ⟨hX, ?_⟩
  rw [hfst, h1, hu, ← hG1]
end YangMills.Construction.ColdStepAtMirrorFrames
end
