import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExponentsOfTheStepProof
import YangMills.Construction.SummableBoundsOfTheFlow.FloorOfTheScaledExponents
import YangMills.Construction.SummableBoundsOfTheFlow.ScaledExponentIsTheExponentOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessIsADensityProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledPartsAreSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation FamilyNorms MeasureTheory
open scoped Topology
namespace ScaledVariables
section Analysis
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem le_sub_of_uniformlyConvex {ρ m κ s : ℝ} {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ}
    {K : ι → ι → ℝ}
    (h : IsUniformlyConvexDecaying ρ m κ d Ψ K)
    (hs : ∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ s * ‖e‖)
    {η : BondField ι} (hη : ∀ b, ‖η b‖ < ρ) :
    m * ∑ b, ‖η b‖ ^ 2 - s * ∑ b, ‖η b‖ ≤ Ψ η - Ψ 0 := by
  have hd1 : Differentiable ℝ Ψ := h.smooth.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fun ζ => fderiv ℝ Ψ ζ η) := by
    have h2 : ContDiff ℝ 2 (fderiv ℝ Ψ) := h.smooth.fderiv_right (by norm_num)
    exact (h2.differentiable (by norm_num)).clm_apply (differentiable_const η)
  set C : ℝ := 2 * m * ∑ b, ‖η b‖ ^ 2 with hC
  let g : ℝ → ℝ := fun v => Ψ (v • η)
  let g' : ℝ → ℝ := fun v => fderiv ℝ Ψ (v • η) η
  let g'' : ℝ → ℝ := fun v => secondDerivAlong Ψ (v • η) η η
  have hline : ∀ v : ℝ, HasDerivAt (fun v : ℝ => v • η) η v := by
    intro v
    simpa using (hasDerivAt_id v).smul_const η
  have hg : ∀ v, HasDerivAt g (g' v) v := fun v =>
    HasFDerivAt.comp_hasDerivAt (f := fun v : ℝ => v • η) (l := Ψ) v
      (hd1 (v • η)).hasFDerivAt (hline v)
  have hg' : ∀ v, HasDerivAt g' (g'' v) v := fun v =>
    HasFDerivAt.comp_hasDerivAt (f := fun v : ℝ => v • η) (l := fun ζ => fderiv ℝ Ψ ζ η) v
      (hd2 (v • η)).hasFDerivAt (hline v)
  have hball : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ b, ‖(v • η) b‖ < ρ := by
    intro v hv b
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hv.1]
    have hb := hη b
    have := norm_nonneg (η b)
    nlinarith [hv.1, hv.2]
  have hfl : ∀ v ∈ Set.Icc (0 : ℝ) 1, C ≤ g'' v := fun v hv => h.floor _ (hball v hv) η
  have hmono1 : MonotoneOn (fun v => g' v - C * v) (Set.Icc (0 : ℝ) 1) := by
    have hd : ∀ v, HasDerivAt (fun v => g' v - C * v) (g'' v - C) v := fun v =>
      ((hg' v).fun_sub ((hasDerivAt_id' v).const_mul C)).congr_deriv (by ring)
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun v _ => (hd v).continuousAt.continuousWithinAt)
      (fun v _ => (hd v).differentiableAt.differentiableWithinAt) ?_
    intro v hv
    rw [(hd v).deriv]
    have := hfl v (interior_subset hv)
    linarith
  have h1 : ∀ v ∈ Set.Icc (0 : ℝ) 1, g' 0 + C * v ≤ g' v := by
    intro v hv
    have := hmono1 (Set.left_mem_Icc.2 zero_le_one) hv hv.1
    simp only at this
    linarith
  have hmono2 : MonotoneOn (fun v => g v - g' 0 * v - C / 2 * v ^ 2) (Set.Icc (0 : ℝ) 1) := by
    have hd : ∀ v, HasDerivAt (fun v => g v - g' 0 * v - C / 2 * v ^ 2) (g' v - g' 0 - C * v) v := fun v =>
      (((hg v).fun_sub ((hasDerivAt_id' v).const_mul (g' 0))).fun_sub
        (((hasDerivAt_id' v).fun_pow 2).const_mul (C / 2))).congr_deriv (by norm_num; ring)
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun v _ => (hd v).continuousAt.continuousWithinAt)
      (fun v _ => (hd v).differentiableAt.differentiableWithinAt) ?_
    intro v hv
    rw [(hd v).deriv]
    have := h1 v (interior_subset hv)
    linarith
  have h2 := hmono2 (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have hsum : (∑ b, bondVariation b (η b)) = η := by
    funext b'
    simp [bondVariation, Finset.sum_apply, Pi.single_apply]
  have hg0 : |g' 0| ≤ s * ∑ b, ‖η b‖ := by
    have e : g' 0 = ∑ b, bondPartialDeriv Ψ b 0 (η b) := by
      show fderiv ℝ Ψ ((0 : ℝ) • η) η = _
      rw [zero_smul]
      calc fderiv ℝ Ψ 0 η = fderiv ℝ Ψ 0 (∑ b, bondVariation b (η b)) := by rw [hsum]
        _ = _ := by
          rw [map_sum]
          rfl
    rw [e, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => hs b (η b))
  have e0 : g 0 = Ψ 0 := by simp [g]
  have e1 : g 1 = Ψ η := by simp [g]
  simp only at h2
  have hC2 : C / 2 = m * ∑ b, ‖η b‖ ^ 2 := by rw [hC]; ring
  have := abs_le.1 hg0
  nlinarith [this.1]
end Analysis
variable {F : BlockFrame}
private theorem finite_cell_of_cubicTopTorus {L t n₀ : ℕ} (hn : 1 ≤ n₀) (hF : IsCubicTopTorus L t n₀ F) :
    Finite F.Cell := by
  obtain ⟨-, -, n, hs, hle⟩ := hF
  have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    simp only [BlockFrame.period, Nat.sub_self, pow_zero, mul_one, hs i]
    omega⟩
  have : ∀ i, Finite (ZMod (F.period F.top i)) := fun i => by
    have := hne i
    exact inferInstance
  exact Pi.finite
private theorem mem_finiteCells (hf : Finite F.Cell) (z : F.Cell) : z ∈ finiteCells F := by
  unfold finiteCells
  rw [dif_pos hf]
  exact @Finset.mem_univ _ (Fintype.ofFinite _) z
abbrev _root_.YangMills.SharedProofs.p8277 := @mem_finiteCells
private theorem sum_centredExpansion_eq (hf : Finite F.Cell) (star : Bool) (a ρA : ℝ) (m : ℕ) (f : LocalFamily)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion star a ρA m f y η V =
      ∑ z ∈ finiteCells F, cellCentredExpansion star a ρA m f z η V := by
  classical
  unfold cellCentredExpansion
  exact (Finset.sum_fiberwise_of_maps_to (fun y _ => mem_finiteCells hf (enclosingCell y)) _).symm
private theorem eventually_smul_norm_lt {r : ℝ} (hr : 0 < r) (ζ : StepVariable (finiteCells F)) :
    ∀ᶠ l in 𝓝[>] (0 : ℝ), 0 < l ∧ ∀ b, l * ‖ζ b‖ < r := by
  have hc : 0 < r / (‖ζ‖ + 1) := div_pos hr (by positivity)
  filter_upwards [Ioc_mem_nhdsGT hc] with l hl
  refine ⟨hl.1, fun b => ?_⟩
  have h1 : l * (‖ζ‖ + 1) ≤ r := (le_div_iff₀ (by positivity)).1 hl.2
  have h2 : ‖ζ b‖ ≤ ‖ζ‖ := norm_le_pi_norm ζ b
  nlinarith [hl.1]
abbrev _root_.YangMills.SharedProofs.p61909 := @eventually_smul_norm_lt
private theorem leftTranslate_bondSpread_fin_zero (c : Fin 0 → F.Site F.top × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) (τ : Fin 0 → ℝ) (V : F.GaugeField F.top) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V = V := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExponentBoundsAux.leftTranslate_bondSpread_empty <;> assumption
private theorem tendsto_observable_zero {κ ρ l₁ K : ℝ} {Y : F.Cell} {V : F.GaugeField F.top}
    {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hρ : 0 < ρ) (hl₁ : 0 < l₁)
    (h : IsSmoothObservable κ ρ l₁ K Y V Ob) (ζ : StepVariable (finiteCells F)) :
    Filter.Tendsto (fun l => Ob l ζ V) (𝓝[>] 0) (𝓝 (Ob 0 ζ V)) := by
  have e : ∀ (l : ℝ) (ζ' : StepVariable (finiteCells F)),
      scaleDeriv Ob V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)
        0 ζ' l = Ob l ζ' V := by
    intro l ζ'
    unfold scaleDeriv
    rw [iteratedDeriv_zero]
    unfold bondDeriv
    rw [iteratedFDeriv_zero_apply, leftTranslate_bondSpread_fin_zero]
  have c := h.continuousOn 0 0 (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
    (Fin.elim0 : Fin 0 → imaginaryQuaternions) ‖ζ‖ (Or.inl ⟨by norm_num, by norm_num⟩)
  simp only [e] at c
  have hmem : ((0 : ℝ), ζ) ∈ {q : ℝ × StepVariable (finiteCells F) | 0 ≤ q.1 ∧ q.1 ≤ l₁ ∧
      MemScaledBalls ρ q.1 q.2 ∧ ∀ b, ‖q.2 b‖ ≤ ‖ζ‖} :=
    ⟨le_refl _, hl₁.le, fun b => by simpa using hρ, fun b => norm_le_pi_norm ζ b⟩
  have c0 := (c _ hmem).tendsto
  have hpath : Filter.Tendsto (fun l : ℝ => (l, ζ)) (𝓝[>] 0) (𝓝[{q : ℝ × StepVariable (finiteCells F) |
      0 ≤ q.1 ∧ q.1 ≤ l₁ ∧ MemScaledBalls ρ q.1 q.2 ∧ ∀ b, ‖q.2 b‖ ≤ ‖ζ‖}] ((0 : ℝ), ζ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_id.prodMk continuous_const).tendsto' 0 _ rfl).mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_smul_norm_lt hρ ζ, Ioc_mem_nhdsGT hl₁] with l hl hl'
      exact ⟨hl.1.le, hl'.2, hl.2, fun b => norm_le_pi_norm ζ b⟩
  exact c0.comp hpath
private theorem rescaledExponent_eq_sum (hf : Finite F.Cell) (a ρ lam : ℝ) (g : LocalFamily) (ν l : ℝ)
    (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)) :
    rescaledExponent a ρ g ν l V ζ =
      (∑ Y ∈ finiteCells F, (rescaledCellRemainder a ρ lam l Y V ζ + lam / 2 *
        ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then ‖ζ b‖ ^ 2 else 0)) -
      ν * ∑ Y ∈ finiteCells F, rescaledCellExpansion a ρ g l Y V ζ := by
  unfold rescaledExponent
  rw [sum_centredExpansion_eq hf true a ρ 0 g V (l • ζ)]
  simp only [rescaledCellRemainder, rescaledCellExpansion, sub_add_cancel]
private theorem tendsto_rescaledExponent (hf : Finite F.Cell) {a ρ lam ν : ℝ} {g : LocalFamily}
    {V : F.GaugeField F.top} {ζ : StepVariable (finiteCells F)}
    (hb : ∀ Y : F.Cell, Filter.Tendsto (fun l => rescaledCellRemainder a ρ lam l Y V ζ) (𝓝[>] 0)
      (𝓝 (rescaledCellRemainder a ρ lam 0 Y V ζ)))
    (hr : ∀ Y : F.Cell, Filter.Tendsto (fun l => rescaledCellExpansion a ρ g l Y V ζ) (𝓝[>] 0)
      (𝓝 (rescaledCellExpansion a ρ g 0 Y V ζ))) :
    Filter.Tendsto (fun l => rescaledExponent a ρ g ν l V ζ) (𝓝[>] 0)
      (𝓝 (rescaledExponent a ρ g ν 0 V ζ)) := by
  have e : (fun l => rescaledExponent a ρ g ν l V ζ) = fun l =>
      (∑ Y ∈ finiteCells F, (rescaledCellRemainder a ρ lam l Y V ζ + lam / 2 *
        ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then ‖ζ b‖ ^ 2 else 0)) -
      ν * ∑ Y ∈ finiteCells F, rescaledCellExpansion a ρ g l Y V ζ :=
    funext fun l => rescaledExponent_eq_sum hf a ρ lam g ν l V ζ
  rw [e, rescaledExponent_eq_sum hf a ρ lam g ν 0 V ζ]
  exact (tendsto_finsetSum _ fun Y _ => (hb Y).add tendsto_const_nhds).sub
    ((tendsto_finsetSum _ fun Y _ => hr Y).const_mul ν)
private theorem totalQuadratic_smul {l : ℝ} (hl : 0 < l) (lam : ℝ) (ζ : StepVariable (finiteCells F)) :
    totalQuadratic lam (l⁻¹ ^ 2) (l • ζ) = lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 := by
  unfold totalQuadratic
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hl.le]
  field_simp
private theorem stepLawExponent_smul_eq {a ρ lam l : ℝ} {g : LocalFamily} {V : F.GaugeField F.top}
    {ζ : StepVariable (finiteCells F)} (hl : 0 < l)
    (hs : ∀ ν : ℝ, stepExponent true a ρ (l⁻¹ ^ 2) 0 g ν V (l • ζ) = rescaledExponent a ρ g ν l V ζ)
    (law : StepLaw) :
    stepLawExponent a ρ lam (l⁻¹ ^ 2) g V law (l • ζ) = rescaledLawExponent a ρ lam g l V law ζ := by
  cases law with
  | tilted ν => exact hs ν
  | interpolated τ =>
    show τ * stepExponent true a ρ (l⁻¹ ^ 2) 0 g 0 V (l • ζ) + (1 - τ) * totalQuadratic lam (l⁻¹ ^ 2) (l • ζ) =
      τ * rescaledExponent a ρ g 0 l V ζ + (1 - τ) * (lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2)
    rw [hs 0, totalQuadratic_smul hl]
private theorem stepExponent_radius_eq (a ρ x : ℝ) (m : ℕ) (g : LocalFamily) (ν : ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    stepExponent true a ρ x m g ν V η = stepExponent true a ρ x 0 g ν V η := by apply _root_.YangMills.SharedProofs.p27308 <;> assumption
private theorem stepExponent_affine (a ρ x : ℝ) (m : ℕ) (g : LocalFamily) (ν : ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    stepExponent true a ρ x m g ν V η =
      ν * stepExponent true a ρ x m g 1 V η + (1 - ν) * stepExponent true a ρ x m g 0 V η := by
  simp only [stepExponent]
  ring
private def singleLaw (V : F.GaugeField F.top) (Ψ : StepVariable (finiteCells F) → ℝ) :
    LawOnBondVariables ↥(chordBonds (finiteCells F)) :=
  ⟨F, V, id, Finset.univ, Ψ⟩
private theorem singleLaw_exponent (lam x : ℝ) (V : F.GaugeField F.top) (Ψ : StepVariable (finiteCells F) → ℝ)
    (ζ : StepVariable (finiteCells F)) : (singleLaw V Ψ).exponent lam x ζ = Ψ ζ := by
  show frozenExponent lam x id Finset.univ Ψ ζ = Ψ ζ
  have h : extendByZero id Finset.univ ζ = ζ := by
    funext b
    simp [extendByZero]
  unfold frozenExponent
  rw [h, Finset.sdiff_self]
  simp
private def cellBondDist (F : BlockFrame) (b b' : ↥(chordBonds (finiteCells F))) : ℝ :=
  cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1)
private theorem singleLaw_isAdmissible (T : ColdStepAtMirrorFrames.StepParameters) {t : ℕ} {x : ℝ}
    {V : F.GaugeField F.top} {Ψ : StepVariable (finiteCells F) → ℝ} (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    (hlaw : IsIntermediateLaw T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x)
      (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V Ψ) :
    (singleLaw V Ψ).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio
      T.L t T.n₀ (frameRadius x) (cellBondDist F) :=
  ⟨hF, hV, hlaw, Function.injective_id, fun _ _ => rfl⟩
private theorem hasUniformlyConvexLaw_stepLaw (T : ColdStepAtMirrorFrames.StepParameters) {Cq Cz : ℕ → ℝ}
    {Cr : ℕ → ℕ → ℕ → ℝ} {t : ℕ} {x : ℝ}
    (hE : interpolationAtEndpoints) (hB : InterpolatedFrameBoundsAt T Cq Cz Cr t x) {g : LocalFamily}
    {V : F.GaugeField F.top} {law : StepLaw}
    (hg : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio g)
    (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hlaw : StepLaw.IsUnitWeight law) :
    HasUniformlyConvexLaw T.ballRadius T.chainParams.lam x T.κ T.Ct (cellBondDist F)
      (stepLawExponent T.a T.ρA T.lam x g V law) := by
  have e0 : segmentEnd true = 0 := by simp [segmentEnd]
  have fam : ∀ η : StepVariable (finiteCells F),
      familyLawExponent 0 T.a T.chainParams.ρA x (frameRadius x) g V η =
        stepExponent true T.a T.chainParams.ρA x (frameRadius x) g 1 V η := fun η => by
    have := (hE F true T.a T.chainParams.ρA T.chainParams.lam x 0 (frameRadius x) V).2.2.2.2.2.1 g η
    rwa [e0] at this
  have wt : ∀ (τ : ℝ) (η : StepVariable (finiteCells F)),
      weightLawExponent 0 T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V η =
        τ * stepExponent true T.a T.chainParams.ρA x (frameRadius x) g 0 V η +
          (1 - τ) * totalQuadratic T.chainParams.lam x η := fun τ η => by
    have := (hE F true T.a T.chainParams.ρA T.chainParams.lam x τ (frameRadius x) V).2.2.2.2.2.2 g η
    rwa [e0] at this
  cases law with
  | tilted ν =>
    obtain ⟨h0, h1⟩ := hlaw
    have hw : IsConvexWeights ![ν, 1 - ν] :=
      ⟨Fin.forall_fin_two.2 ⟨h0, by simpa using h1⟩, by simp [Fin.sum_univ_two]⟩
    have hm := (hB.laws _ (cellBondDist F) 2 ![ν, 1 - ν]
      ![singleLaw V (familyLawExponent 0 T.a T.chainParams.ρA x (frameRadius x) g V),
        singleLaw V (weightLawExponent 0 T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) 1 V)] hw
      (Fin.forall_fin_two.2 ⟨singleLaw_isAdmissible T hF hV (.ofFamily 0 g le_rfl zero_le_one hg),
        singleLaw_isAdmissible T hF hV (.ofWeight 0 1 le_rfl zero_le_one zero_le_one le_rfl)⟩)).1
    have e : convexCombinationExponent T.chainParams.lam x ![ν, 1 - ν]
        ![singleLaw V (familyLawExponent 0 T.a T.chainParams.ρA x (frameRadius x) g V),
          singleLaw V (weightLawExponent 0 T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) 1 V)] =
        stepLawExponent T.a T.ρA T.lam x g V (.tilted ν) := by
      funext ζ
      simp only [convexCombinationExponent, Fin.sum_univ_two]
      show ν * (singleLaw V _).exponent T.chainParams.lam x ζ +
          (1 - ν) * (singleLaw V _).exponent T.chainParams.lam x ζ =
        stepExponent true T.a T.chainParams.ρA x 0 g ν V ζ
      rw [singleLaw_exponent, singleLaw_exponent, fam, wt, stepExponent_radius_eq,
        stepExponent_affine T.a T.chainParams.ρA x 0 g ν V ζ,
        stepExponent_radius_eq T.a T.chainParams.ρA x (frameRadius x) g 0 V ζ]
      ring
    rwa [e] at hm
  | interpolated τ =>
    obtain ⟨h0, h1⟩ := hlaw
    have hw : IsConvexWeights ![(1 : ℝ)] := ⟨fun l => by simp, by simp⟩
    have hm := (hB.laws _ (cellBondDist F) 1 ![(1 : ℝ)]
      ![singleLaw V (weightLawExponent 0 T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V)] hw
      (fun l => by
        rw [Fin.eq_zero l]
        exact singleLaw_isAdmissible T hF hV (.ofWeight 0 τ le_rfl zero_le_one h0 h1))).1
    have e : convexCombinationExponent T.chainParams.lam x ![(1 : ℝ)]
        ![singleLaw V (weightLawExponent 0 T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V)] =
        stepLawExponent T.a T.ρA T.lam x g V (.interpolated τ) := by
      funext ζ
      simp only [convexCombinationExponent, Fin.sum_univ_one]
      show 1 * (singleLaw V _).exponent T.chainParams.lam x ζ =
        τ * stepExponent true T.a T.chainParams.ρA x 0 g 0 V ζ + (1 - τ) * totalQuadratic T.chainParams.lam x ζ
      rw [singleLaw_exponent, wt, stepExponent_radius_eq, one_mul]
    rwa [e] at hm
private theorem sqrt_rate_inv_sq {l lam : ℝ} (hl : 0 < l) (hlam : 0 < lam) :
    Real.sqrt (l⁻¹ ^ 2 * lam / 4) = l⁻¹ * (Real.sqrt lam / 2) := by
  have e : l⁻¹ ^ 2 * lam / 4 = (l⁻¹ * (Real.sqrt lam / 2)) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt hlam.le]
    ring
  rw [e, Real.sqrt_sq (by positivity)]
theorem rescaledExponentFloor (hS : RescaledExponentAgrees)
    (hP : StepDensities.rescaledPartsSmoothStatement) (hB : interpolatedFramesStatement)
    (hE : interpolationAtEndpoints) : rescaledExponentFloorStatement := by
  obtain ⟨Cq, Cz, Cr, hB⟩ := hB
  have hB' : EventuallyOrdered fun T => ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x →
      InterpolatedFrameBoundsAt T (Cq (momentParameters T)) (Cz (momentParameters T))
        (Cr (momentParameters T)) t x :=
    EventuallyInParameters.mono hB fun T g _ _ => g
  refine EventuallyOrdered.mono ((hS.and hP).and hB') fun T hT hn h => ?_
  obtain ⟨⟨⟨l₁, hl₁, gS⟩, gP⟩, gB⟩ := h
  intro e
  obtain ⟨l₂, K, hl₂, -, gP⟩ := gP e
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold ColdStepAtMirrorFrames.StepParameters.ballRadius
    positivity
  have hlam : 0 < T.lam := hT.chain_admissible.positivity.2.2.1
  have hc : 0 < |T.coupling| + 1 := by positivity
  have hl₃ : 0 < 1 / (|T.coupling| + 1) := by positivity
  refine ⟨min l₁ (min l₂ (1 / (|T.coupling| + 1))), lt_min hl₁ (lt_min hl₂ hl₃), ?_⟩
  set l₀ := min l₁ (min l₂ (1 / (|T.coupling| + 1))) with hl₀
  have hle₁ : l₀ ≤ l₁ := min_le_left _ _
  have hle₂ : l₀ ≤ l₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hle₃ : l₀ ≤ 1 / (|T.coupling| + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hl₀0 : 0 < l₀ := lt_min hl₁ (lt_min hl₂ hl₃)
  intro t f F V law hf hF hV hlaw
  have hfin : Finite F.Cell := finite_cell_of_cubicTopTorus hn hF
  have hid : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → l ≤ l₀ → MemScaledBalls T.ballRadius l ζ →
      stepLawExponent T.a T.ρA T.lam (l⁻¹ ^ 2) f V law (l • ζ) =
        rescaledLawExponent T.a T.ρA T.lam f l V law ζ := fun l ζ h0 hl hζ =>
    stepLawExponent_smul_eq h0 (fun ν => (gS t F V f ν l 0 ζ hF hV h0 (hl.trans hle₁) hζ).1) law
  have hy : ∀ l : ℝ, 0 < l → l ≤ l₀ → T.coupling ≤ l⁻¹ ^ 2 := by
    intro l h0 hl
    have h1 : l * (|T.coupling| + 1) ≤ 1 := (le_div_iff₀ hc).1 (hl.trans hle₃)
    have h2 : |T.coupling| + 1 ≤ l⁻¹ := by
      rw [← one_div, le_div_iff₀ h0]
      linarith
    have h3 := le_abs_self T.coupling
    have h4 := abs_nonneg T.coupling
    nlinarith
  have hcv : ∀ l : ℝ, 0 < l → l ≤ l₀ →
      HasUniformlyConvexLaw T.ballRadius T.chainParams.lam (l⁻¹ ^ 2) T.κ T.Ct (cellBondDist F)
        (stepLawExponent T.a T.ρA T.lam (l⁻¹ ^ 2) f V law) := fun l h0 hl =>
    hasUniformlyConvexLaw_stepLaw T hE (gB t _ (hy l h0 hl)) hf.1 hF hV hlaw
  have hball : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → MemScaledBalls T.ballRadius l ζ →
      ∀ b, ‖(l • ζ) b‖ < T.ballRadius := by
    intro l ζ h0 hζ b
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg h0.le]
    exact hζ b
  have hlim : ∀ ζ : StepVariable (finiteCells F), Filter.Tendsto
      (fun l => rescaledLawExponent T.a T.ρA T.lam f l V law ζ) (𝓝[>] 0)
      (𝓝 (rescaledLawExponent T.a T.ρA T.lam f 0 V law ζ)) := by
    intro ζ
    have hb : ∀ Y : F.Cell, Filter.Tendsto (fun l => rescaledCellRemainder T.a T.ρA T.lam l Y V ζ) (𝓝[>] 0)
        (𝓝 (rescaledCellRemainder T.a T.ρA T.lam 0 Y V ζ)) := fun Y =>
      tendsto_observable_zero hρ hl₂ (gP l₂ hl₂ le_rfl t f F V Y hf hF hV).1 ζ
    have hr : ∀ Y : F.Cell, Filter.Tendsto (fun l => rescaledCellExpansion T.a T.ρA f l Y V ζ) (𝓝[>] 0)
        (𝓝 (rescaledCellExpansion T.a T.ρA f 0 Y V ζ)) := fun Y =>
      tendsto_observable_zero hρ hl₂ (gP l₂ hl₂ le_rfl t f F V Y hf hF hV).2 ζ
    cases law with
    | tilted ν => exact tendsto_rescaledExponent hfin hb hr
    | interpolated τ =>
      exact ((tendsto_rescaledExponent hfin hb hr).const_mul τ).add tendsto_const_nhds
  have hfloor : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → l ≤ l₀ →
      MemScaledBalls T.ballRadius l ζ →
      T.lam / 4 * ∑ b, ‖ζ b‖ ^ 2 - Real.sqrt T.lam / 2 * ∑ b, ‖ζ b‖ ≤
        rescaledLawExponent T.a T.ρA T.lam f l V law ζ -
          rescaledLawExponent T.a T.ρA T.lam f l V law 0 := by
    intro l ζ h0 hl hζ
    obtain ⟨Φ, K', hag, hconv, hsl, -⟩ := hcv l h0 hl
    have hfl := le_sub_of_uniformlyConvex hconv hsl (hball l ζ h0 hζ)
    have hz : MemScaledBalls T.ballRadius l (0 : StepVariable (finiteCells F)) := fun b => by simpa using hρ
    have e1 : Φ (l • ζ) = rescaledLawExponent T.a T.ρA T.lam f l V law ζ := by
      rw [hag _ (hball l ζ h0 hζ), hid l ζ h0 hl hζ]
    have e0 : Φ 0 = rescaledLawExponent T.a T.ρA T.lam f l V law 0 := by
      have := hid l 0 h0 hl hz
      rw [smul_zero] at this
      rw [hag 0 (fun b => by simpa using hρ), this]
    rw [e1, e0, sqrt_rate_inv_sq (lam := T.chainParams.lam) h0 hlam] at hfl
    have s2 : ∑ b, ‖(l • ζ) b‖ ^ 2 = l ^ 2 * ∑ b, ‖ζ b‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg h0.le, mul_pow]
    have s1 : ∑ b, ‖(l • ζ) b‖ = l * ∑ b, ‖ζ b‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg h0.le]
    rw [s2, s1] at hfl
    have e2 : l⁻¹ ^ 2 * T.chainParams.lam / 4 * (l ^ 2 * ∑ b, ‖ζ b‖ ^ 2) = T.lam / 4 * ∑ b, ‖ζ b‖ ^ 2 := by
      show l⁻¹ ^ 2 * T.lam / 4 * (l ^ 2 * ∑ b, ‖ζ b‖ ^ 2) = T.lam / 4 * ∑ b, ‖ζ b‖ ^ 2
      field_simp
    have e3 : l⁻¹ * (Real.sqrt T.chainParams.lam / 2) * (l * ∑ b, ‖ζ b‖) =
        Real.sqrt T.lam / 2 * ∑ b, ‖ζ b‖ := by
      show l⁻¹ * (Real.sqrt T.lam / 2) * (l * ∑ b, ‖ζ b‖) = Real.sqrt T.lam / 2 * ∑ b, ‖ζ b‖
      field_simp
    rw [e2, e3] at hfl
    exact hfl
  refine ⟨?_, hid, ?_, hlim⟩
  · intro l ζ h0 hl hζ
    rcases h0.eq_or_lt with rfl | hpos
    · refine ge_of_tendsto ((hlim ζ).sub (hlim 0)) ?_
      filter_upwards [eventually_smul_norm_lt hρ ζ, Ioc_mem_nhdsGT hl₀0] with l' h1 h2
      exact hfloor l' ζ h1.1 h2.2 h1.2
    · exact hfloor l ζ hpos hl hζ
  · intro l h0 hl
    obtain ⟨Φ, K', hag, hconv, -, -⟩ := hcv l h0 hl
    refine (hconv.smooth.continuous.comp (continuous_const_smul l)).continuousOn.congr fun ζ hζ => ?_
    show rescaledLawExponent T.a T.ρA T.lam f l V law ζ = Φ (l • ζ)
    rw [hag _ (hball l ζ h0 hζ), hid l ζ h0 hl hζ]
end ScaledVariables
end YangMills.Construction
end
