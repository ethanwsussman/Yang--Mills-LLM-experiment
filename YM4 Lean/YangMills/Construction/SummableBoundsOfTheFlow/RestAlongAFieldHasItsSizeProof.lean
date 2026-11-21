import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.RestAlongAFieldHasItsSize
import YangMills.Construction.SummableBoundsOfTheFlow.SizeFromAGradient
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames IteratedDerivative Interpolation BondIntegration
namespace IteratedDerivative
namespace MovingFieldRemainderSize
section FieldTerms
variable {ι : Type} [Fintype ι] [DecidableEq ι] {H : BondField ι → ℝ} {U : BondVector → BondVector} {b b' : ι}
  {η : BondField ι}
omit [Fintype ι] in
theorem fieldDerivative_eq : fieldDerivative b U H = fun ζ => fderiv ℝ H ζ (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b (U (ζ b))) := rfl
theorem fieldDerivative_contDiffAt (hH : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) H η) (hU : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) U (η b)) :
    ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fieldDerivative b U H) η := by
  have h1 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fderiv ℝ H) η := hH.fderiv_right (by norm_num)
  have h2 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun ζ : BondField ι => U (ζ b)) η :=
    ContDiffAt.comp (g := U) (f := fun ζ : BondField ι => ζ b) η hU
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).contDiff.contDiffAt
  have h3 := (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b).contDiff.contDiffAt.comp η h2
  rw [fieldDerivative_eq]
  exact h1.clm_apply h3
theorem fderiv_fieldDerivative (hH : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) H η) (hU : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) U (η b))
    (v : BondField ι) :
    fderiv ℝ (fieldDerivative b U H) η v = (fderiv ℝ (fderiv ℝ H) η v) (bondVariation b (U (η b))) +
      fderiv ℝ H η (bondVariation b (fderiv ℝ U (η b) (v b))) := by
  have d1 : DifferentiableAt ℝ (fderiv ℝ H) η := (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have dU : DifferentiableAt ℝ U (η b) := hU.differentiableAt (by simp)
  have h2 : HasFDerivAt (fun ζ : BondField ι => U (ζ b))
      ((fderiv ℝ U (η b)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b)) η :=
    HasFDerivAt.comp (g := U) (f := fun ζ : BondField ι => ζ b) η dU.hasFDerivAt
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).hasFDerivAt
  have h3 := (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b).hasFDerivAt.comp η h2
  have h4 := d1.hasFDerivAt.clm_apply h3
  rw [fieldDerivative_eq]
  change fderiv ℝ (fun ζ => fderiv ℝ H ζ (((ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b) ∘ fun ζ : BondField ι => U (ζ b)) ζ)) η v = _
  rw [h4.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.proj_apply, Function.comp]
  rw [add_comm]
  rfl
omit [Fintype ι] in
theorem abs_apply_bondVariation_le (L : BondField ι →L[ℝ] ℝ) (b : ι) {D : ℝ} (hD0 : 0 ≤ D)
    (h : ∀ e : BondVector, ‖e‖ = 1 → |L (bondVariation b e)| ≤ D) (w : BondVector) : |L (bondVariation b w)| ≤ D * ‖w‖ := by
  have h1 : ‖L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)‖ ≤ D :=
    ContinuousLinearMap.opNorm_le_of_unit_norm hD0 fun e he => by
      rw [Real.norm_eq_abs]
      exact h e he
  have h2 := (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)).le_opNorm w
  rw [Real.norm_eq_abs] at h2
  exact h2.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
theorem abs_fderiv_fieldDerivative_le {D₁ D₂ : ℝ} (e' : BondVector) (hH : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) H η)
    (hU : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) U (η b)) (h0₁ : 0 ≤ D₁) (h0₂ : 0 ≤ D₂)
    (hD₂ : ∀ e : BondVector, ‖e‖ = 1 → |(fderiv ℝ (fderiv ℝ H) η (bondVariation b' e')) (bondVariation b e)| ≤ D₂)
    (hD₁ : ∀ e : BondVector, ‖e‖ = 1 → |fderiv ℝ H η (bondVariation b e)| ≤ D₁) :
    |fderiv ℝ (fieldDerivative b U H) η (bondVariation b' e')| ≤ D₂ * ‖U (η b)‖ +
      if b' = b then D₁ * (‖fderiv ℝ U (η b)‖ * ‖e'‖) else 0 := by
  rw [fderiv_fieldDerivative hH hU]
  refine (abs_add_le _ _).trans (add_le_add (abs_apply_bondVariation_le _ b h0₂ hD₂ _) ?_)
  split_ifs with hb
  · subst hb
    refine (abs_apply_bondVariation_le _ b' h0₁ hD₁ _).trans (mul_le_mul_of_nonneg_left ?_ h0₁)
    have : (bondVariation b' e' : BondField ι) b' = e' := by simp [bondVariation]
    rw [this]
    exact (fderiv ℝ U (η b')).le_opNorm e'
  · have : (bondVariation b' e' : BondField ι) b = 0 := Pi.single_eq_of_ne (Ne.symm hb) _
    rw [this, map_zero]
    simp [bondVariation]
end FieldTerms
section Slopes
variable {F : BlockFrame} {k : ℕ}
abbrev JointSpace (F : BlockFrame) (k : ℕ) : Type := StepVariable (finiteCells F) × (Fin k → ℝ)
abbrev parameterList (F : BlockFrame) (k : ℕ) : List (JointSpace F k) := parameterDirections _ _ (parameterBasis k)
theorem length_parameterList : (parameterList F k).length = k := by simp [parameterDirections, parameterBasis]
theorem iteratedFDeriv_slice_eq_derivAlong (h : DerivAlongRulesHold) (f : JointSpace F k → ℝ) (ζ : StepVariable (finiteCells F))
    (hf : ContDiffAt ℝ (k : WithTop ℕ∞) f (ζ, 0)) :
    iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => f (ζ, τ)) 0 (fun l => Pi.single l 1) =
      derivAlong f (parameterList F k) (ζ, 0) := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.iteratedFDeriv_parameters_eq <;> assumption
theorem fderiv_derivAlong_slice (hL : DerivAlongRulesHold) (f : JointSpace F k → ℝ) (η : StepVariable (finiteCells F))
    (l : List (JointSpace F k)) (h1 : ContDiffAt ℝ ((1 + l.length : ℕ) : WithTop ℕ∞) f (η, 0)) (v : StepVariable (finiteCells F)) :
    fderiv ℝ (fun ζ => derivAlong f l (ζ, 0)) η v = derivAlong f ((v, 0) :: l) (η, 0) := by
  have R := hL.1 (JointSpace F k) ℝ
  have hA : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (derivAlong f l) (η, 0) := R.contDiffAt _ _ 1 _ h1
  have hd : DifferentiableAt ℝ (derivAlong f l) (η, 0) := hA.differentiableAt (by simp)
  have := (HasFDerivAt.comp (g := derivAlong f l) (f := fun ζ => ((ζ, 0) : JointSpace F k)) η hd.hasFDerivAt
    (hasFDerivAt_prodMk_left η 0)).fderiv
  change fderiv ℝ (derivAlong f l ∘ fun ζ => ((ζ, 0) : JointSpace F k)) η v = _
  rw [this]
  simp [derivAlong]
theorem bondDeriv_slopes (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hk : k ≤ 1) (η : StepVariable (finiteCells F))
    (hf : ∀ᶠ ζ in 𝓝 η, ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (ζ, 0)) :
    ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun ζ => bondDeriv (G ζ) V c X) η ∧
    (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
      fderiv ℝ (fun ζ => bondDeriv (G ζ) V c X) η (bondVariation b e) = jointMixedDeriv G η V ![b] ![e] c X) ∧
    ∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
      (fderiv ℝ (fderiv ℝ fun ζ => bondDeriv (G ζ) V c X) η (bondVariation b' e')) (bondVariation b e) =
        jointMixedDeriv G η V ![b', b] ![e', e] c X := by
  classical
  set f := rotatedEval G V c X with hfd
  have h3 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) f (η, 0) := hf.self_of_nhds
  have R := hL.1 (JointSpace F k) ℝ
  set H : StepVariable (finiteCells F) → ℝ := fun ζ => bondDeriv (G ζ) V c X with hH
  have evH : H =ᶠ[𝓝 η] fun ζ => derivAlong f (parameterList F k) (ζ, 0) := by
    filter_upwards [hf] with ζ hζ
    exact iteratedFDeriv_slice_eq_derivAlong hL f ζ (hζ.of_le (by exact_mod_cast (show k ≤ 3 by omega)))
  have hin : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun ζ : StepVariable (finiteCells F) => ((ζ, 0) : JointSpace F k)) η :=
    (contDiff_id.prodMk contDiff_const).contDiffAt
  have hA2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (derivAlong f (parameterList F k)) (η, 0) :=
    R.contDiffAt _ _ 2 _ (h3.of_le (by rw [length_parameterList]; exact_mod_cast (show 2 + k ≤ 3 by omega)))
  have hC2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun ζ => derivAlong f (parameterList F k) (ζ, 0)) η :=
    ContDiffAt.comp (g := derivAlong f (parameterList F k)) (f := fun ζ => ((ζ, 0) : JointSpace F k)) η hA2 hin
  have hH2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) H η := hC2.congr_of_eventuallyEq evH
  have nearD : ∀ v : StepVariable (finiteCells F), (fun ζ => fderiv ℝ H ζ v) =ᶠ[𝓝 η] fun ζ => derivAlong f ((v, 0) :: parameterList F k) (ζ, 0) := by
    intro v
    filter_upwards [hf.eventually_nhds] with ζ hζ
    have e1 : H =ᶠ[𝓝 ζ] fun ζ' => derivAlong f (parameterList F k) (ζ', 0) := by
      filter_upwards [hζ] with ζ' hζ'
      exact iteratedFDeriv_slice_eq_derivAlong hL f ζ' (hζ'.of_le (by exact_mod_cast (show k ≤ 3 by omega)))
    rw [e1.fderiv_eq]
    exact fderiv_derivAlong_slice hL f ζ _ (hζ.self_of_nhds.of_le (by rw [length_parameterList]; exact_mod_cast (show 1 + k ≤ 3 by omega))) v
  have hM1 : ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector), pointDirections (k := k) ![b] ![e] = [((bondVariation b e, 0) : JointSpace F k)] := by
    intro b e
    simp [pointDirections, List.ofFn_succ, variableDirection, bondVariation]
  have hM2 : ∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector), pointDirections (k := k) ![b', b] ![e', e] =
      [((bondVariation b' e', 0) : JointSpace F k), ((bondVariation b e, 0) : JointSpace F k)] := by
    intro b b' e e'
    simp [pointDirections, List.ofFn_succ, variableDirection, bondVariation]
  refine ⟨hH2, fun b e => ?_, fun b b' e e' => ?_⟩
  · have e2 := (hA F V G η k c X).2 1 ![b] ![e] (h3.of_le (by exact_mod_cast (show 1 + k ≤ 3 by omega)))
    rw [e2, hM1]
    exact (nearD (bondVariation b e)).self_of_nhds
  · have e2 := (hA F V G η k c X).2 2 ![b', b] ![e', e] (h3.of_le (by exact_mod_cast (show 2 + k ≤ 3 by omega)))
    rw [e2, hM2]
    have d1 : DifferentiableAt ℝ (fderiv ℝ H) η := (hH2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
    have h5 := (d1.hasFDerivAt.clm_apply (hasFDerivAt_const (bondVariation b e : StepVariable (finiteCells F)) η)).fderiv
    have h6 : (fderiv ℝ (fderiv ℝ H) η (bondVariation b' e')) (bondVariation b e) =
        fderiv ℝ (fun ζ => fderiv ℝ H ζ (bondVariation b e)) η (bondVariation b' e') := by
      rw [h5]
      simp
    rw [h6, (nearD (bondVariation b e)).fderiv_eq]
    exact fderiv_derivAlong_slice hL f η _ (h3.of_le (by
      simp only [List.length_cons, length_parameterList]
      exact_mod_cast (show 1 + (k + 1) ≤ 3 by omega))) _
end Slopes
section CellSets
variable {F : BlockFrame}
theorem cellSupDist_le_diameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
theorem diameter_le_add_of_cover (hD : SupDistCellComparison) {P Q N : Finset F.Cell} {z : F.Cell} (hzP : z ∈ P)
    (hzQ : z ∈ Q) (hN : ∀ u ∈ N, u ∈ P ∨ u ∈ Q) : cellSetDiameter N ≤ cellSetDiameter P + cellSetDiameter Q := by
  have e : ∀ y w : F.Cell, siteSupDist y w = cellSupDist y w := fun _ _ => rfl
  have tri : ∀ u v w : F.Cell, cellSupDist u w ≤ cellSupDist u v + cellSupDist v w := fun u v w => by
    have := (hD.1 F F.top u v w).2.2
    simpa only [e] using this
  have hP : ∀ {u v : F.Cell}, u ∈ P → v ∈ P → cellSupDist u v ≤ cellSetDiameter P := cellSupDist_le_diameter
  have hQ : ∀ {u v : F.Cell}, u ∈ Q → v ∈ Q → cellSupDist u v ≤ cellSetDiameter Q := cellSupDist_le_diameter
  change (N.sup fun u => N.sup fun v => cellSupDist u v) ≤ _
  refine Finset.sup_le fun u hu => Finset.sup_le fun v hv => ?_
  rcases hN u hu with h1 | h1 <;> rcases hN v hv with h2 | h2
  · have := hP h1 h2
    omega
  · have a1 := hP h1 hzP
    have a2 := hQ hzQ h2
    have a3 := tri u z v
    omega
  · have a1 := hQ h1 hzQ
    have a2 := hP hzP h2
    have a3 := tri u z v
    omega
  · have := hQ h1 h2
    omega
theorem exp_mul_exp_le {κ A B n a₁ a₂ : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hn : n ≤ A + B) (h1 : a₁ ≤ A) (h2 : a₂ ≤ A) :
    Real.exp (-(2 ^ 7 * κ * A)) * Real.exp (-(2 ^ 8 * κ * B)) ≤
      Real.exp (-(2 ^ 4 * κ * n)) * (Real.exp (-(2 ^ 5 * κ * a₁)) * Real.exp (-(2 ^ 5 * κ * a₂))) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h : 16 * n + 32 * a₁ + 32 * a₂ ≤ 128 * A + 256 * B := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h hκ.le]
theorem fieldDerivative_term_gradient (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hD : SupDistCellComparison) {κ ρ Cb Cf Ek : ℝ} {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {V : F.GaugeField F.top} {Y : F.Cell} {k : ℕ} (hk : k ≤ 1) (cA : Fin k → F.Site F.top × Fin 4) (XA : Fin k → imaginaryQuaternions)
    (U : BondVector → BondVector) (b : ↥(chordBonds (finiteCells F))) (η : StepVariable (finiteCells F))
    (Q N : Finset F.Cell) (hκ : 0 < κ) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf) (hEk : 0 ≤ Ek) (hη : ∀ b, ‖η b‖ < ρ)
    (hS : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ < ρ) →
      ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (rotatedEval G V cA XA) (ζ, 0))
    (hopen : IsOpen {ζ : StepVariable (finiteCells F) | ∀ b, ‖ζ b‖ < ρ})
    (hG : ∀ (l : ℕ) (bs : Fin l → ↥(chordBonds (finiteCells F))) (es : Fin l → BondVector), 1 ≤ l → l + k ≤ 3 →
      (∀ i, ‖es i‖ = 1) → |jointMixedDeriv G η V bs es cA XA| ≤
        Cb * Ek * Real.exp (-(2 ^ 7 * κ * cellSetDiameter (insert Y (chordBondCells bs ∪ topBondCells cA)))))
    (hU1 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) U (η b)) (hUv : ‖U (η b)‖ ≤ Cf * Real.exp (-(2 ^ 8 * κ * cellSetDiameter Q)))
    (hUd : ‖fderiv ℝ U (η b)‖ ≤ Cf * Real.exp (-(2 ^ 8 * κ * cellSetDiameter Q))) (hbQ : enclosingCell b.1.1 ∈ Q)
    (hN : ∀ u ∈ N, u ∈ Q ∨ u = Y ∨ ∃ l, u = (cA l).1) :
    ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fieldDerivative b U (fun ζ => bondDeriv (G ζ) V cA XA)) η ∧
    ∀ (b' : ↥(chordBonds (finiteCells F))) (e' : BondVector), ‖e'‖ = 1 →
      |fderiv ℝ (fieldDerivative b U (fun ζ => bondDeriv (G ζ) V cA XA)) η (bondVariation b' e')| ≤
        2 * (Cb * Ek * Cf) * (Real.exp (-(2 ^ 4 * κ * cellSetDiameter N)) *
          (Real.exp (-(2 ^ 5 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) *
            Real.exp (-(2 ^ 5 * κ * (cellSupDist (enclosingCell b'.1.1) Y : ℝ))))) := by
  classical
  have hf : ∀ᶠ ζ in 𝓝 η, ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (rotatedEval G V cA XA) (ζ, 0) := by
    filter_upwards [hopen.mem_nhds hη] with ζ hζ
    exact hS ζ hζ
  obtain ⟨h2, h1, h11⟩ := bondDeriv_slopes hL hA G V cA XA hk η hf
  refine ⟨fieldDerivative_contDiffAt h2 hU1, fun b' e' he' => ?_⟩
  set P₂ : Finset F.Cell := insert Y (chordBondCells ![b', b] ∪ topBondCells cA) with hP₂
  set P₁ : Finset F.Cell := insert Y (chordBondCells ![b] ∪ topBondCells cA) with hP₁
  set D₂ : ℝ := Cb * Ek * Real.exp (-(2 ^ 7 * κ * cellSetDiameter P₂)) with hD₂
  set D₁ : ℝ := Cb * Ek * Real.exp (-(2 ^ 7 * κ * cellSetDiameter P₁)) with hD₁
  have hCE : 0 ≤ Cb * Ek := mul_nonneg hCb hEk
  have h0₂ : 0 ≤ D₂ := mul_nonneg hCE (Real.exp_pos _).le
  have h0₁ : 0 ≤ D₁ := mul_nonneg hCE (Real.exp_pos _).le
  have hb2 := abs_fderiv_fieldDerivative_le (b := b) (b' := b') (U := U) (D₁ := D₁) (D₂ := D₂) e' h2 hU1 h0₁ h0₂
    (fun e he => by
      rw [h11 b b' e e']
      exact hG 2 ![b', b] ![e', e] (by omega) (by omega) (fun i => by
        fin_cases i
        · simpa using he'
        · simpa using he))
    (fun e he => by
      rw [h1 b e]
      exact hG 1 ![b] ![e] (by omega) (by omega) (fun i => by
        fin_cases i
        simpa using he))
  refine hb2.trans ?_
  have mem₂ : Y ∈ P₂ ∧ enclosingCell b.1.1 ∈ P₂ ∧ enclosingCell b'.1.1 ∈ P₂ ∧ ∀ l, (cA l).1 ∈ P₂ := by
    refine ⟨Finset.mem_insert_self _ _, ?_, ?_, fun l => ?_⟩
    · refine Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.2 ⟨1, Finset.mem_univ _, by simp⟩))
    · refine Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.2 ⟨0, Finset.mem_univ _, by simp⟩))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩))
  have mem₁ : Y ∈ P₁ ∧ enclosingCell b.1.1 ∈ P₁ ∧ ∀ l, (cA l).1 ∈ P₁ := by
    refine ⟨Finset.mem_insert_self _ _, ?_, fun l => ?_⟩
    · refine Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.2 ⟨0, Finset.mem_univ _, by simp⟩))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩))
  have cover : ∀ P : Finset F.Cell, Y ∈ P → enclosingCell b.1.1 ∈ P → (∀ l, (cA l).1 ∈ P) →
      (cellSetDiameter N : ℝ) ≤ cellSetDiameter P + cellSetDiameter Q := by
    intro P a1 a2 a3
    have := diameter_le_add_of_cover hD a2 hbQ (N := N) (fun u hu => by
      rcases hN u hu with h | h | ⟨l, h⟩
      · exact Or.inr h
      · exact Or.inl (h ▸ a1)
      · exact Or.inl (h ▸ a3 l))
    exact_mod_cast this
  set E₄ : ℝ := Real.exp (-(2 ^ 4 * κ * cellSetDiameter N)) with hE₄
  set eb : ℝ := Real.exp (-(2 ^ 5 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) with heb
  set eb' : ℝ := Real.exp (-(2 ^ 5 * κ * (cellSupDist (enclosingCell b'.1.1) Y : ℝ))) with heb'
  have hWt : 0 ≤ Cb * Ek * Cf := mul_nonneg hCE hCf
  have hE0 : 0 ≤ E₄ * (eb * eb') := by positivity
  have t₂ : D₂ * ‖U (η b)‖ ≤ Cb * Ek * Cf * (E₄ * (eb * eb')) := by
    have hp := exp_mul_exp_le (A := (cellSetDiameter P₂ : ℝ)) (B := (cellSetDiameter Q : ℝ)) (n := (cellSetDiameter N : ℝ))
      (a₁ := (cellSupDist (enclosingCell b.1.1) Y : ℝ)) (a₂ := (cellSupDist (enclosingCell b'.1.1) Y : ℝ)) hκ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (cover P₂ mem₂.1 mem₂.2.1 mem₂.2.2.2) (by exact_mod_cast cellSupDist_le_diameter mem₂.2.1 mem₂.1)
      (by exact_mod_cast cellSupDist_le_diameter mem₂.2.2.1 mem₂.1)
    calc D₂ * ‖U (η b)‖ ≤ D₂ * (Cf * Real.exp (-(2 ^ 8 * κ * cellSetDiameter Q))) := mul_le_mul_of_nonneg_left hUv h0₂
      _ = Cb * Ek * Cf * (Real.exp (-(2 ^ 7 * κ * cellSetDiameter P₂)) * Real.exp (-(2 ^ 8 * κ * cellSetDiameter Q))) := by
          rw [hD₂]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hWt
  have t₁ : (if b' = b then D₁ * (‖fderiv ℝ U (η b)‖ * ‖e'‖) else 0) ≤ Cb * Ek * Cf * (E₄ * (eb * eb')) := by
    split_ifs with hb
    · have hp := exp_mul_exp_le (A := (cellSetDiameter P₁ : ℝ)) (B := (cellSetDiameter Q : ℝ)) (n := (cellSetDiameter N : ℝ))
        (a₁ := (cellSupDist (enclosingCell b.1.1) Y : ℝ)) (a₂ := (cellSupDist (enclosingCell b'.1.1) Y : ℝ)) hκ (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) (cover P₁ mem₁.1 mem₁.2.1 mem₁.2.2) (by exact_mod_cast cellSupDist_le_diameter mem₁.2.1 mem₁.1)
        (by rw [hb]; exact_mod_cast cellSupDist_le_diameter mem₁.2.1 mem₁.1)
      rw [he', mul_one]
      calc D₁ * ‖fderiv ℝ U (η b)‖ ≤ D₁ * (Cf * Real.exp (-(2 ^ 8 * κ * cellSetDiameter Q))) := mul_le_mul_of_nonneg_left hUd h0₁
        _ = Cb * Ek * Cf * (Real.exp (-(2 ^ 7 * κ * cellSetDiameter P₁)) * Real.exp (-(2 ^ 8 * κ * cellSetDiameter Q))) := by
            rw [hD₁]
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hp hWt
    · positivity
  calc _ ≤ Cb * Ek * Cf * (E₄ * (eb * eb')) + Cb * Ek * Cf * (E₄ * (eb * eb')) := add_le_add t₂ t₁
    _ = _ := by ring
end CellSets
end MovingFieldRemainderSize
open MovingFieldRemainderSize in
set_option maxHeartbeats 1600000 in
theorem movingFieldRemainderHasSize_holds (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hD : SupDistCellComparison) (hSG : localSizeOfGradientBoundStatement) :
    MovingFieldRemainderHasSize := by
  classical
  intro F ρ x lam κ W C Cb Cf Ek d Φ p G Z V Y c₀ c X hρ hx hlam hκ hW hCb hCf hEk hp hd hconv hWd hWY hX hS hG hZ1 hZ2
  have hopen : IsOpen {ζ : StepVariable (finiteCells F) | ∀ b, ‖ζ b‖ < ρ} := by
    have : {ζ : StepVariable (finiteCells F) | ∀ b, ‖ζ b‖ < ρ} = ⋂ b, {ζ | ‖ζ b‖ < ρ} := by
      ext ζ
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (by fun_prop) continuous_const
  set N : Finset F.Cell := {Y, c₀.1, (c 0).1, (c 1).1} with hN
  set E₄ : ℝ := Real.exp (-(2 ^ 4 * κ * cellSetDiameter N)) with hE₄
  have hU1 : AreUnitVectors (fun _ : Fin 1 => X 1) := fun _ => hX 1
  have hU0 : AreUnitVectors (fun _ : Fin 1 => X 0) := fun _ => hX 0
  set c₉ : Fin 0 → F.Site F.top × Fin 4 := Fin.elim0 with hc₉
  set X₉ : Fin 0 → imaginaryQuaternions := Fin.elim0 with hX₉
  have hU9 : AreUnitVectors X₉ := fun l => l.elim0
  have e9 : (fun ζ => G ζ V) = fun ζ => bondDeriv (G ζ) V c₉ X₉ := by
    funext ζ
    have : ∀ τ : Fin 0 → ℝ, leftTranslate (ColdStepAtMirrorFrames.bondSpread c₉ X₉ τ) V = V := by
      intro τ
      funext y i
      have e0 : expUnit (0 : imaginaryQuaternions) = 1 := by
        apply Subtype.ext
        simp [expUnit]
      simp [leftTranslate, ColdStepAtMirrorFrames.bondSpread, e0]
    simp [bondDeriv, iteratedFDeriv_zero_apply, this]
  set A : ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) → ℝ := fun b =>
    fieldDerivative b (vectorFieldDerivSingle (Z b) V c X 0) (fun ζ => bondDeriv (G ζ) V (fun _ : Fin 1 => c 1) (fun _ => X 1)) with hAd
  set B : ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) → ℝ := fun b =>
    fieldDerivative b (vectorFieldDerivSingle (Z b) V c X 1) (fun ζ => bondDeriv (G ζ) V (fun _ : Fin 1 => c 0) (fun _ => X 0)) with hBd
  set D : ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) → ℝ := fun b =>
    fieldDerivative b (vectorFieldDerivPair (Z b) V c X) (fun ζ => bondDeriv (G ζ) V c₉ X₉) with hDd
  have hrest : movingFieldRemainder G Z V c X = fun η => ∑ b, (A b η + B b η + D b η) := by
    funext η
    unfold movingFieldRemainder
    simp only [hAd, hBd, hDd, ← e9]
  have tA := fun (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < ρ) (b : ↥(chordBonds (finiteCells F))) =>
    fieldDerivative_term_gradient hL hA hD (le_refl 1) (fun _ : Fin 1 => c 1) (fun _ => X 1) (vectorFieldDerivSingle (Z b) V c X 0) b η
      {enclosingCell b.1.1, c₀.1, (c 0).1} N hκ hCb hCf hEk hη (fun ζ hζ => hS ζ 1 _ _ hζ hU1) hopen
      (fun l bs es h1 h2 h3 => hG η l 1 bs es _ _ hη h1 h2 h3 hU1) (hZ1 b _ 0 (hη b)).1 (hZ1 b _ 0 (hη b)).2.1
      (hZ1 b _ 0 (hη b)).2.2 (by simp) (fun u hu => by
        simp only [hN, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
        rcases hu with h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr ⟨0, h⟩))
  have tB := fun (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < ρ) (b : ↥(chordBonds (finiteCells F))) =>
    fieldDerivative_term_gradient hL hA hD (le_refl 1) (fun _ : Fin 1 => c 0) (fun _ => X 0) (vectorFieldDerivSingle (Z b) V c X 1) b η
      {enclosingCell b.1.1, c₀.1, (c 1).1} N hκ hCb hCf hEk hη (fun ζ hζ => hS ζ 1 _ _ hζ hU0) hopen
      (fun l bs es h1 h2 h3 => hG η l 1 bs es _ _ hη h1 h2 h3 hU0) (hZ1 b _ 1 (hη b)).1 (hZ1 b _ 1 (hη b)).2.1
      (hZ1 b _ 1 (hη b)).2.2 (by simp) (fun u hu => by
        simp only [hN, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
        rcases hu with h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr ⟨0, h⟩)
        · exact Or.inl (Or.inr (Or.inr h)))
  have tD := fun (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < ρ) (b : ↥(chordBonds (finiteCells F))) =>
    fieldDerivative_term_gradient hL hA hD (Nat.zero_le 1) c₉ X₉ (vectorFieldDerivPair (Z b) V c X) b η
      {enclosingCell b.1.1, c₀.1, (c 0).1, (c 1).1} N hκ hCb hCf hEk hη (fun ζ hζ => hS ζ 0 _ _ hζ hU9) hopen
      (fun l bs es h1 h2 h3 => hG η l 0 bs es _ _ hη h1 h2 h3 hU9) (hZ2 b _ (hη b)).1 (hZ2 b _ (hη b)).2.1
      (hZ2 b _ (hη b)).2.2 (by simp) (fun u hu => by
        simp only [hN, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
        rcases hu with h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr h))))
  have hC : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (movingFieldRemainder G Z V c X) η := by
    intro η hη
    rw [hrest]
    exact ContDiffAt.sum fun b _ => ((tA η hη b).1.add (tB η hη b).1).add (tD η hη b).1
  have hWt : 0 ≤ Cb * Ek * Cf := mul_nonneg (mul_nonneg hCb hEk) hCf
  have hE0 : 0 < E₄ := Real.exp_pos _
  set g : ℝ := 6 * (Cb * Ek * Cf) * W * E₄ with hg
  have hg0 : 0 ≤ g := by positivity
  have hgrad : ∀ (η : StepVariable (finiteCells F)) (b' : ↥(chordBonds (finiteCells F))) (e : BondVector), (∀ b, ‖η b‖ < ρ) → ‖e‖ = 1 →
      |fderiv ℝ (movingFieldRemainder G Z V c X) η (bondVariation b' e)| ≤
        g * Real.exp (-(2 * κ * (cellSupDist (enclosingCell b'.1.1) Y : ℝ))) := by
    intro η b' e hη he
    rw [hrest]
    have hd : ∀ b, HasFDerivAt (fun ζ => A b ζ + B b ζ + D b ζ)
        (fderiv ℝ (A b) η + fderiv ℝ (B b) η + fderiv ℝ (D b) η) η := fun b =>
      (((tA η hη b).1.differentiableAt (by simp)).hasFDerivAt.add
        ((tB η hη b).1.differentiableAt (by simp)).hasFDerivAt).add
        ((tD η hη b).1.differentiableAt (by simp)).hasFDerivAt
    have hs := HasFDerivAt.fun_sum (u := Finset.univ) fun b _ => hd b
    rw [hs.fderiv]
    simp only [sum_apply, add_apply]
    set eB : ↥(chordBonds (finiteCells F)) → ℝ := fun b => Real.exp (-(2 ^ 5 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) with heB
    have hterm : ∀ b, |fderiv ℝ (A b) η (bondVariation b' e) + fderiv ℝ (B b) η (bondVariation b' e) + fderiv ℝ (D b) η (bondVariation b' e)| ≤
        6 * (Cb * Ek * Cf) * (E₄ * (eB b * eB b')) := by
      intro b
      have a1 := (tA η hη b).2 b' e he
      have a2 := (tB η hη b).2 b' e he
      have a3 := (tD η hη b).2 b' e he
      calc _ ≤ |fderiv ℝ (A b) η (bondVariation b' e)| + |fderiv ℝ (B b) η (bondVariation b' e)| + |fderiv ℝ (D b) η (bondVariation b' e)| :=
            (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
        _ ≤ _ := by
            have := add_le_add (add_le_add a1 a2) a3
            refine this.trans (le_of_eq ?_)
            ring
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun b _ => hterm b).trans ?_)
    have hsum : ∑ b, eB b ≤ W := by
      refine (Finset.sum_le_sum fun b _ => ?_).trans hWY
      refine Real.exp_le_exp.2 ?_
      have a0 : (0 : ℝ) ≤ cellSupDist (enclosingCell b.1.1) Y := Nat.cast_nonneg _
      nlinarith [mul_nonneg hκ.le a0]
    have hb' : eB b' ≤ Real.exp (-(2 * κ * (cellSupDist (enclosingCell b'.1.1) Y : ℝ))) := by
      refine Real.exp_le_exp.2 ?_
      have a0 : (0 : ℝ) ≤ cellSupDist (enclosingCell b'.1.1) Y := Nat.cast_nonneg _
      nlinarith [mul_nonneg hκ.le a0]
    have e1 : ∑ b, 6 * (Cb * Ek * Cf) * (E₄ * (eB b * eB b')) = 6 * (Cb * Ek * Cf) * E₄ * eB b' * ∑ b, eB b := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e1]
    have hpos : 0 ≤ 6 * (Cb * Ek * Cf) * E₄ * eB b' := by
      have := Real.exp_pos (-(2 ^ 5 * κ * (cellSupDist (enclosingCell b'.1.1) Y : ℝ)))
      positivity
    calc _ ≤ 6 * (Cb * Ek * Cf) * E₄ * eB b' * W := mul_le_mul_of_nonneg_left hsum hpos
      _ = g * eB b' := by rw [hg]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb' hg0
  refine ⟨fun η hη => (hC η hη).contDiffWithinAt, ?_⟩
  exact hSG _ ρ x lam κ W C g d Φ p _ _ hρ hx hlam hκ.le hW hg0 hp hd hconv hWd hWY hC hgrad
end IteratedDerivative
end YangMills.Construction
end
