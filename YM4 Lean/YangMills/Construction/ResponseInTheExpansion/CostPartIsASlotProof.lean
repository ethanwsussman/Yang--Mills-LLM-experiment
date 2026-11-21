import YangMills.Construction.ColdStepAtMirrorFrames.CouplingFloorOfTheFrames
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheCostPart
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheSmoothMoves
import YangMills.Construction.ResponseInTheExpansion.CostPartIsASlot
import YangMills.Construction.RunningCouplingSlope.InverseOfTheHessianOfTheChartProof
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenAtATopProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open scoped Topology
open Set Filter MeasureTheory ColdStepAtMirrorFrames Interpolation TorusComparison
open BlockAverages hiding bondSpread
namespace WeightedResponses
namespace SlopeTermSlot
open Dilation
variable {F : BlockFrame}
open Classical in
def blockBondSet (Y : F.Cell) : Finset ↥(chordBonds (finiteCells F)) :=
  Finset.univ.filter fun b => enclosingCell b.1.1 = Y
abbrev topEnergy (Q : ColdHalfLaw) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    StepVariable (finiteCells F) × (Fin k → ℝ) → ℝ :=
  topTranslated (interpolatedEnergy 1 Q.a Q.chartRadius Q.mirrorRadius) V c X
theorem iteratedFDeriv_congr_of_eventuallyEq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g₁ g₂ : E → ℝ}
    {x : E} (h : g₁ =ᶠ[𝓝 x] g₂) (k : ℕ) : iteratedFDeriv ℝ k g₁ x = iteratedFDeriv ℝ k g₂ x :=
  (h.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds
theorem update_eq_add_smul_directionCoordinate (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (p : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) (u : ℝ) :
    Function.update w p.1 (Function.update (w p.1) p.2 (w p.1 p.2 + u • e)) =
      fun x i => w x i + u • directionCoordinate (Sum.inl (p.1, p.2, e) : ChartDirection F) x i := by
  funext x i
  have hs : directionCoordinate (Sum.inl (p.1, p.2, e) : ChartDirection F) x i =
      if p.1 = x ∧ p.2 = i then e else 0 := rfl
  rw [hs]
  by_cases h : p.1 = x ∧ p.2 = i
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, smul_zero, add_zero]
    by_cases hx : x = p.1
    · subst hx
      have hi : i ≠ p.2 := fun hi => h ⟨rfl, hi.symm⟩
      simp [Function.update_of_ne hi]
    · simp [Function.update_of_ne hx]
theorem chartedSlope_eq_fderiv (Q : ColdHalfLaw) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    {ζ : StepVariable (finiteCells F)} {τ : Fin k → ℝ} (b : ↥(chordBonds (finiteCells F))) (e : BondVector)
    (hd : DifferentiableAt ℝ (topEnergy Q V c X) (ζ, τ)) :
    chartedSlope Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius (leftTranslate (bondSpread c X τ) V) ζ)
        (leftTranslate (bondSpread c X τ) V) b.1 (toImaginary e) =
      fderiv ℝ (topEnergy Q V c X) (ζ, τ) (bondVariation b e, 0) := by
  have hl1 : HasDerivAt (fun u : ℝ => ζ + Pi.single b (u • e))
      (Pi.single b e : StepVariable (finiteCells F)) 0 := by
    have e1 : (fun u : ℝ => ζ + Pi.single b (u • e)) =
        fun u : ℝ => ζ + u • (Pi.single b e : StepVariable (finiteCells F)) := by
      funext u
      rw [Pi.single_smul]
    rw [e1]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single b e : StepVariable (finiteCells F))).const_add ζ
  have hl : HasDerivAt (fun u : ℝ => ((ζ + Pi.single b (u • e), τ) : StepVariable (finiteCells F) × (Fin k → ℝ)))
      (bondVariation b e, 0) 0 := hl1.prodMk (hasDerivAt_const _ _)
  have hp : ((ζ + Pi.single b ((0 : ℝ) • e), τ) : StepVariable (finiteCells F) × (Fin k → ℝ)) = (ζ, τ) := by
    simp
  have hd' : HasFDerivAt (topEnergy Q V c X) (fderiv ℝ (topEnergy Q V c X) (ζ, τ))
      ((ζ + Pi.single b ((0 : ℝ) • e), τ) : StepVariable (finiteCells F) × (Fin k → ℝ)) := by
    rw [hp]
    exact hd.hasFDerivAt
  have h3 := hd'.comp_hasDerivAt (0 : ℝ) hl
  have e2 : (fun u : ℝ => chartedEnergy Q.a (Function.update
      (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius (leftTranslate (bondSpread c X τ) V) ζ) b.1.1
      (Function.update (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius (leftTranslate (bondSpread c X τ) V) ζ b.1.1)
        b.1.2 (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius (leftTranslate (bondSpread c X τ) V) ζ b.1.1 b.1.2
          + u • toImaginary e)))
      (leftTranslate (bondSpread c X τ) V)) =
      topEnergy Q V c X ∘ fun u : ℝ => ((ζ + Pi.single b (u • e), τ) : StepVariable (finiteCells F) × (Fin k → ℝ)) := by
    funext u
    simp only [Function.comp, topTranslated, interpolatedEnergy]
    rw [interpolatedCoords_add_single, update_eq_add_smul_directionCoordinate]
  unfold chartedSlope
  rw [e2, h3.deriv]
theorem slopeTerm_eq_remainder (Q : ColdHalfLaw) (V : F.GaugeField F.top) (Y : F.Cell) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    {ζ : StepVariable (finiteCells F)} {τ : Fin k → ℝ}
    (hd : ∀ v ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (topEnergy Q V c X) (v • ζ, τ)) :
    Q.slopeTerm Y ζ (leftTranslate (bondSpread c X τ) V) =
      Q.coupling * remainder dilateFst (blockBondSet Y) (fun b => liftFst (bondProjection b)) (topEnergy Q V c X) (ζ, τ) := by
  have h1 : DifferentiableAt ℝ (topEnergy Q V c X) (ζ, τ) := by
    simpa using hd 1 ⟨zero_le_one, le_rfl⟩
  unfold ColdHalfLaw.slopeTerm ColdHalfLaw.sumOverBlock remainder blockBondSet
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with hb
  · unfold ColdHalfLaw.slopeRemainder
    have e2 : ∫ v in (0 : ℝ)..1, chartedSlope Q.a
        (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius (leftTranslate (bondSpread c X τ) V) (v • ζ))
        (leftTranslate (bondSpread c X τ) V) b.1 (toImaginary (ζ b)) =
        ∫ v in (0 : ℝ)..1, fderiv ℝ (topEnergy Q V c X) (v • ζ, τ) (bondVariation b (ζ b), 0) := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [uIcc_of_le zero_le_one] at hv
      exact chartedSlope_eq_fderiv Q V c X b (ζ b) (hd v hv)
    exact congrArg₂ (fun p q : ℝ => p - 2 * q) (chartedSlope_eq_fderiv Q V c X b (ζ b) h1) e2
  · rfl
theorem norm_smul_apply_le {ρ : ℝ} {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ ρ) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) : ∀ b, ‖(v • η) b‖ ≤ ρ := by apply _root_.YangMills.Construction.Interpolation.AtTop.smul_mem_ball <;> assumption
theorem eventually_contDiffAt_topEnergy (Q : ColdHalfLaw) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    {η : StepVariable (finiteCells F)}
    (hf : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (1 : ℕ) (topEnergy Q V c X) (v • η, 0)) :
    ∀ᶠ z in 𝓝 ((η, 0) : StepVariable (finiteCells F) × (Fin k → ℝ)), ∀ v ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ (1 : ℕ) (topEnergy Q V c X) (v • z.1, z.2) :=
  eventually_contDiffAt_comp_tube (S := dilateFst) (contDiff_dilateFst (n := 0)).continuous (z := (η, 0)) hf
theorem contDiffAt_slopeTerm (Q : ColdHalfLaw) (V : F.GaugeField F.top) (Y : F.Cell) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    {η : StepVariable (finiteCells F)}
    (hf : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (4 : ℕ) (topEnergy Q V c X) (v • η, 0)) :
    ContDiffAt ℝ (2 : ℕ) (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      Q.slopeTerm Y q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η) := by
  have hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (dilateFst (E₁ := StepVariable (finiteCells F)) (E₂ := Fin k → ℝ)) := contDiff_dilateFst
  have hz : ContDiffAt ℝ ((2 + 2 : ℕ)) (topEnergy Q V c X) (η, 0) := by
    simpa using hf 1 ⟨zero_le_one, le_rfl⟩
  have hR := contDiffAt_remainder hS (blockBondSet Y) (fun b => liftFst (bondProjection b)) (f := topEnergy Q V c X)
    (z := (η, 0)) 2 hz (fun v hv => hf v hv)
  have hx : ContDiffAt ℝ (2 : ℕ) (fun z => Q.coupling * remainder dilateFst (blockBondSet Y)
      (fun b => liftFst (bondProjection b)) (topEnergy Q V c X) z) (η, 0) := contDiffAt_const.mul hR
  have hsw : ContDiffAt ℝ (2 : ℕ) (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => (q.2, q.1)) (0, η) :=
    (contDiff_snd.prodMk contDiff_fst).contDiffAt
  have h := ContDiffAt.comp (0, η) (g := fun z => Q.coupling * remainder dilateFst (blockBondSet Y)
      (fun b => liftFst (bondProjection b)) (topEnergy Q V c X) z)
    (f := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => (q.2, q.1)) hx hsw
  refine h.congr_of_eventuallyEq ?_
  have ht := eventually_contDiffAt_topEnergy Q V c X (η := η) fun v hv => (hf v hv).of_le (by norm_num)
  have htend : Tendsto (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => (q.2, q.1)) (𝓝 (0, η)) (𝓝 (η, 0)) :=
    continuous_swap.tendsto (0, η)
  filter_upwards [htend.eventually ht] with q hq
  exact slopeTerm_eq_remainder Q V Y c X fun v hv => (hq v hv).differentiableAt (by norm_num)
theorem bondDeriv_slopeTerm (Q : ColdHalfLaw) (V : F.GaugeField F.top) (Y : F.Cell) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    {η : StepVariable (finiteCells F)}
    (hf : ∀ v ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (k + 3 : ℕ) (topEnergy Q V c X) (v • η, 0)) :
    bondDeriv (Q.slopeTerm Y η) V c X =
      Q.coupling * remainder dilate (blockBondSet Y) bondProjection
        (secondJet (topEnergy Q V c X) 0 (basisVectors k)) η := by
  have hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (dilateFst (E₁ := StepVariable (finiteCells F)) (E₂ := Fin k → ℝ)) := contDiff_dilateFst
  have ht := eventually_contDiffAt_topEnergy Q V c X (η := η) fun v hv => (hf v hv).of_le (by norm_cast; omega)
  have htend : Tendsto (fun τ : Fin k → ℝ => ((η, τ) : StepVariable (finiteCells F) × (Fin k → ℝ))) (𝓝 0)
      (𝓝 (η, 0)) :=
    (Continuous.prodMk_right η).tendsto 0
  have hev : (fun τ : Fin k → ℝ => Q.slopeTerm Y η (leftTranslate (bondSpread c X τ) V)) =ᶠ[𝓝 0]
      fun τ => Q.coupling * remainder dilateFst (blockBondSet Y) (fun b => liftFst (bondProjection b))
        (topEnergy Q V c X) (η, τ) := by
    filter_upwards [htend.eventually ht] with τ hτ
    exact slopeTerm_eq_remainder Q V Y c X fun v hv => (hτ v hv).differentiableAt (by norm_num)
  have hz : ContDiffAt ℝ (k + 2 : ℕ) (topEnergy Q V c X) (η, 0) := by
    have := hf 1 ⟨zero_le_one, le_rfl⟩
    rw [one_smul] at this
    exact this.of_le (by norm_cast; omega)
  have hR := contDiffAt_remainder hS (blockBondSet Y) (fun b => liftFst (bondProjection b)) (f := topEnergy Q V c X)
    (z := (η, 0)) k hz (fun v hv => (hf v hv).of_le (by norm_cast; omega))
  have hc : ContDiffAt ℝ k (fun τ : Fin k → ℝ => remainder dilateFst (blockBondSet Y)
      (fun b => liftFst (bondProjection b)) (topEnergy Q V c X) (η, τ)) 0 :=
    ContDiffAt.comp (0 : Fin k → ℝ) (g := remainder dilateFst (blockBondSet Y) (fun b => liftFst (bondProjection b))
      (topEnergy Q V c X))
      (f := fun τ : Fin k → ℝ => ((η, τ) : StepVariable (finiteCells F) × (Fin k → ℝ))) hR (by fun_prop)
  show iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => Q.slopeTerm Y η (leftTranslate (bondSpread c X τ) V)) 0
    (basisVectors k) = _
  rw [iteratedFDeriv_congr_of_eventuallyEq hev k, iteratedFDeriv_const_mul_eval hc,
    iteratedFDeriv_remainder_dilateFst (blockBondSet Y) bondProjection (basisVectors k) hf]
theorem trilinear_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (s₁ s₂ s₃ : ℝ) (a b c : E) :
    T ![s₁ • a, s₂ • b, s₃ • c] = s₁ * s₂ * s₃ * T ![a, b, c] := by
  have h := T.map_smul_univ ![s₁, s₂, s₃] ![a, b, c]
  have e : (fun i => (![s₁, s₂, s₃] : Fin 3 → ℝ) i • (![a, b, c] : Fin 3 → E) i) = ![s₁ • a, s₂ • b, s₃ • c] := by
    funext i
    fin_cases i <;> rfl
  rw [e] at h
  rw [h, Fin.prod_univ_three]
  simp
theorem exists_unit_smul (u : BondVector) : ∃ v : BondVector, ‖v‖ = 1 ∧ u = ‖u‖ • v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedEnergyLocal.exists_unit_smul <;> assumption
theorem abs_trilinear_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => BondField ι) ℝ) (b₁ b₂ b₃ : ι) {C : ℝ}
    (h : ∀ u₁ u₂ u₃ : BondVector, ‖u₁‖ = 1 → ‖u₂‖ = 1 → ‖u₃‖ = 1 →
      |T ![bondVariation b₁ u₁, bondVariation b₂ u₂, bondVariation b₃ u₃]| ≤ C)
    (u₁ u₂ u₃ : BondVector) :
    |T ![bondVariation b₁ u₁, bondVariation b₂ u₂, bondVariation b₃ u₃]| ≤ C * (‖u₁‖ * ‖u₂‖ * ‖u₃‖) := by
  obtain ⟨v₁, h₁, e₁⟩ := exists_unit_smul u₁
  obtain ⟨v₂, h₂, e₂⟩ := exists_unit_smul u₂
  obtain ⟨v₃, h₃, e₃⟩ := exists_unit_smul u₃
  have s : ∀ (b : ι) (r : ℝ) (v : BondVector), bondVariation b (r • v) = r • bondVariation b v := fun b r v => by
    simp only [bondVariation]
    rw [Pi.single_smul]
  have e : T ![bondVariation b₁ u₁, bondVariation b₂ u₂, bondVariation b₃ u₃] =
      ‖u₁‖ * ‖u₂‖ * ‖u₃‖ * T ![bondVariation b₁ v₁, bondVariation b₂ v₂, bondVariation b₃ v₃] := by
    conv_lhs => rw [e₁, e₂, e₃, s, s, s]
    exact trilinear_smul (E := BondField ι) T _ _ _ _ _ _
  rw [e, abs_mul, abs_of_nonneg (by positivity), mul_comm]
  exact mul_le_mul_of_nonneg_right (h v₁ v₂ v₃ h₁ h₂ h₃) (by positivity)
theorem bondSpan_le_diameter {k : ℕ} {P : Finset F.Cell} {Y : F.Cell} {c : Fin k → F.Site F.top × Fin 4}
    (hY : Y ∈ P) (hc : ∀ l, (c l).1 ∈ P) : bondSpan Y c ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.bondSpan_le_cellSetDiameter <;> assumption
theorem bondSpan_le_two_mul (hsym : ∀ a b : F.Cell, cellSupDist a b = cellSupDist b a)
    (htri : ∀ a b d : F.Cell, cellSupDist a d ≤ cellSupDist a b + cellSupDist b d) {k : ℕ} (Y : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) : bondSpan Y c ≤ 2 * bondListDistance Y c := by
  have hall : ∀ l, cellSupDist Y (c l).1 ≤ bondListDistance Y c := fun l =>
    Finset.le_sup (f := fun l : Fin k => cellSupDist Y (c l).1) (Finset.mem_univ l)
  unfold bondSpan
  refine max_le (Finset.sup_le fun l _ => ?_) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  · have := hall l
    show cellSupDist Y (c l).1 ≤ 2 * bondListDistance Y c
    omega
  · have h1 := htri (c l).1 Y (c l').1
    have h2 := hall l
    have h3 := hall l'
    have h4 := hsym (c l).1 Y
    show cellSupDist (c l).1 (c l').1 ≤ 2 * bondListDistance Y c
    omega
theorem exp_le_three_factors {δ κ s d₁ d₂ S : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (h : 2 ^ 5 * κ ≤ δ / 3)
    (h1 : d₁ ≤ s) (h2 : d₂ ≤ s) (h3 : S ≤ s) (hS : 0 ≤ S) :
    Real.exp (-(δ * s)) ≤
      Real.exp (-(δ / 3 * d₁)) * Real.exp (-(δ / 3 * d₂)) * Real.exp (-(2 ^ 5 * κ * S)) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have a1 : δ / 3 * d₁ ≤ δ / 3 * s := mul_le_mul_of_nonneg_left h1 (by positivity)
  have a2 : δ / 3 * d₂ ≤ δ / 3 * s := mul_le_mul_of_nonneg_left h2 (by positivity)
  have a3 : 2 ^ 5 * κ * S ≤ δ / 3 * S := mul_le_mul_of_nonneg_right h hS
  have a4 : δ / 3 * S ≤ δ / 3 * s := mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith
theorem momentBound_mono {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℝ → ℝ} {Ψ G : BondField ι → ℝ} {q : ℕ}
    {B B' : ℝ} (h : MomentBound r Ψ G q B) (h0 : 0 ≤ B) (h1 : B ≤ B') : MomentBound r Ψ G q B' :=
  ⟨h.1, h.2.trans (pow_le_pow_left₀ h0 h1 q)⟩
theorem abs_ballExpectation_le {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ}
    (hL : IsBallLaw ρ r Ψ) (G : BondField ι → ℝ) :
    |ballExpectation r Ψ G| ≤ ballExpectation r Ψ fun η => |G η| ^ 1 := by
  unfold ballExpectation
  rw [abs_div, abs_of_pos hL.integral_pos]
  refine div_le_div_of_nonneg_right ?_ hL.integral_pos.le
  have h1 := norm_integral_le_integral_norm (μ := volume) (fun η => G η * ballDensity r Ψ η)
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun η => ?_)))
  show ‖G η * ballDensity r Ψ η‖ = |G η| ^ 1 * ballDensity r Ψ η
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hL.density_nonneg η), pow_one]
theorem remainderMajorant_le {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset ι) (w : ι → ℝ)
    (hw : ∀ b, 0 ≤ w b) {W : ℝ} (hW : ∑ b, w b ≤ W) {y ρ : ℝ} (hy : 0 ≤ y) (hρ : 0 ≤ ρ) (η : BondField ι)
    (hη : ∀ b, ‖η b‖ < ρ) :
    remainderMajorant B w y η ≤ B.card * W ^ 2 * (1 + y * ρ) ^ 3 := by
  have b1 : ∀ e, 1 + y * ‖η e‖ ≤ 1 + y * ρ := fun e => by
    have := mul_le_mul_of_nonneg_left (hη e).le hy
    linarith
  have b0 : ∀ e, 0 ≤ 1 + y * ‖η e‖ := fun e => by positivity
  have hT : ∀ a b c, cubicWeight y a b c η ≤ (1 + y * ρ) ^ 3 := fun a b c => by
    unfold cubicWeight
    calc _ ≤ (1 + y * ρ) * (1 + y * ρ) * (1 + y * ρ) :=
          mul_le_mul (mul_le_mul (b1 a) (b1 b) (b0 b) ((b0 a).trans (b1 a))) (b1 c) (b0 c)
            (mul_nonneg ((b0 a).trans (b1 a)) ((b0 a).trans (b1 a)))
      _ = _ := by ring
  have hK : 0 ≤ (1 + y * ρ) ^ 3 := by positivity
  have hW0 : 0 ≤ ∑ b, w b := Finset.sum_nonneg fun b _ => hw b
  have hF : ∀ b, bondWeightSum w y b η ≤ W ^ 2 * (1 + y * ρ) ^ 3 := fun b => by
    have e : ∑ b₁, ∑ b₂, w b₁ * w b₂ * (1 + y * ρ) ^ 3 = (∑ b, w b) ^ 2 * (1 + y * ρ) ^ 3 := by
      rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b₁ _ => ?_
      rw [Finset.sum_mul]
    unfold bondWeightSum
    calc _ ≤ ∑ b₁, ∑ b₂, w b₁ * w b₂ * (1 + y * ρ) ^ 3 :=
          Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ =>
            mul_le_mul_of_nonneg_left (hT _ _ _) (mul_nonneg (hw _) (hw _))
      _ = (∑ b, w b) ^ 2 * (1 + y * ρ) ^ 3 := e
      _ ≤ W ^ 2 * (1 + y * ρ) ^ 3 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hW0 hW 2) hK
  unfold remainderMajorant
  calc _ ≤ ∑ _b ∈ B, W ^ 2 * (1 + y * ρ) ^ 3 := Finset.sum_le_sum fun b _ => hF b
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
theorem toImaginary_zero : toImaginary (0 : BondVector) = 0 := by apply _root_.YangMills.SharedProofs.p2840 <;> assumption
theorem interpolatedCoords_zero (a ρA : ℝ) (m : ℕ) (V' : F.GaugeField F.top) :
    interpolatedCoords 1 a ρA m V' (0 : StepVariable (finiteCells F)) =
      fun z i => interpolatedFrame 1 a ρA m (z, i) V' := by
  funext z i
  simp only [interpolatedCoords]
  have h0 : stepCoordinates (0 : StepVariable (finiteCells F)) z i = 0 := by
    by_cases h : (z, i) ∈ chordBonds (finiteCells F)
    · simp only [stepCoordinates, dif_pos h, Pi.zero_apply]
      exact toImaginary_zero
    · simp only [stepCoordinates, dif_neg h]
  rw [h0, add_zero]
def bondWeight (δ₂ : ℝ) (Y : F.Cell) (b : ↥(chordBonds (finiteCells F))) : ℝ :=
  Real.exp (-(δ₂ / 3 * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))
def bondDecay (κ : ℝ) (Y : F.Cell) (b : ↥(chordBonds (finiteCells F))) : ℝ :=
  Real.exp (-(2 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))
structure SlopeTermHypotheses (Q : ColdHalfLaw) (V : F.GaugeField F.top) (κ₂ δ₂ Ct ω Dm Wt Nn : ℝ) (Kf : ℕ → ℝ)
    (Dk : ℕ → ℕ → ℝ) (Cm : ℕ → ℝ) : Prop where
  one_le_coupling : 1 ≤ Q.coupling
  rate_pos : 0 < Q.rate
  radius_pos : 0 < Q.ballRadius
  rate_le : 2 ^ 10 * Q.rate ≤ δ₂
  kernel_nonneg : ∀ j, 0 ≤ Dk 3 j
  kernel_le : ∀ j, j ≤ 2 → Dk 3 j ≤ Dm
  kernels : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ Q.ballRadius) →
    HasInterpolationKernels 1 Q.a Q.chartRadius Q.rate κ₂ δ₂ Q.coupling Q.mirrorRadius Kf Dk V η
  stationary : InterpolatedSlopeSmall 1 Q.a Q.chartRadius δ₂ Ct ω Q.coupling Q.mirrorRadius V
  small : Q.coupling * (Ct * ω) ≤ 1
  small_nonneg : 0 ≤ Ct * ω
  law : IsBallLaw Q.ballRadius Q.radialWeight (Q.exponent V)
  moments : ∀ (n : ℕ) (b : ↥(chordBonds (finiteCells F))),
    ballExpectation Q.radialWeight (Q.exponent V) (fun η => ‖η b‖ ^ (2 * n)) ≤ Cm n * (Q.coupling ^ n)⁻¹
  weights : ∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
    Real.exp (-(δ₂ / 3 * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ Wt
  card_le : ∀ z : F.Cell, ((blockBondSet z).card : ℝ) ≤ Nn
  symm : ∀ a b : F.Cell, cellSupDist a b = cellSupDist b a
  triangle : ∀ a b d : F.Cell, cellSupDist a d ≤ cellSupDist a b + cellSupDist b d
section Hypotheses
variable {Q : ColdHalfLaw} {V : F.GaugeField F.top} {κ₂ δ₂ Ct ω Dm Wt Nn : ℝ} {Kf : ℕ → ℝ} {Dk : ℕ → ℕ → ℝ}
  {Cm : ℕ → ℝ}
theorem contDiffAt_topEnergy (H : SlopeTermHypotheses Q V κ₂ δ₂ Ct ω Dm Wt Nn Kf Dk Cm)
    (hne : Nonempty ↥(chordBonds (finiteCells F))) (n : ℕ) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) {ζ : StepVariable (finiteCells F)} (hζ : ∀ b, ‖ζ b‖ ≤ Q.ballRadius) :
    ContDiffAt ℝ n (topEnergy Q V c X) (ζ, 0) := by
  refine topTranslated_contDiffAt _ ζ V c X fun p c' X' hu hnp => ?_
  have hne' : Nonempty (ChordCoord F) := ⟨(hne.some, 0)⟩
  have hc : 0 < Fintype.card (ChordCoord F) := Fintype.card_pos
  have h := ((H.kernels ζ hζ).energy (Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F)) p (doubledBond F)
    (doubledUnit F) c' X' (by omega) (norm_doubledUnit F) hu).1
  exact h.of_le (by exact_mod_cast (by omega))
theorem abs_fderiv_secondJet_le (H : SlopeTermHypotheses Q V κ₂ δ₂ Ct ω Dm Wt Nn Kf Dk Cm) {k : ℕ} (hk : k ≤ 2)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (b : ↥(chordBonds (finiteCells F))) {v : BondVector} (hv : ‖v‖ = 1)
    (hf : ContDiffAt ℝ (k + 2 : ℕ) (topEnergy Q V c X) (0, 0)) :
    |fderiv ℝ (secondJet (topEnergy Q V c X) 0 (basisVectors k)) 0 (bondVariation b v)| ≤
      Ct * ω * Real.exp (-(δ₂ / 8 * bondListDistance (enclosingCell b.1.1) c)) := by
  rw [← secondJet_fderiv_eval hf (basisVectors k) (bondVariation b v)]
  have h1 : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), ContDiffAt ℝ (1 : ℕ) (topEnergy Q V c X) (0, τ) := by
    have h2 : ∀ᶠ z in 𝓝 ((0, 0) : StepVariable (finiteCells F) × (Fin k → ℝ)),
        ContDiffAt ℝ (1 : ℕ) (topEnergy Q V c X) z :=
      (hf.of_le (by norm_cast; omega)).eventually (coe_nat_ne_infty _)
    have h3 : Tendsto (fun τ : Fin k → ℝ => ((0, τ) : StepVariable (finiteCells F) × (Fin k → ℝ))) (𝓝 0)
        (𝓝 (0, 0)) :=
      (Continuous.prodMk_right (0 : StepVariable (finiteCells F))).tendsto 0
    exact h3.eventually h2
  have hev : (fun τ : Fin k → ℝ => fderiv ℝ (topEnergy Q V c X) (0, τ) (bondVariation b v, 0)) =ᶠ[𝓝 0]
      fun τ => interpolatedSlope 1 Q.a Q.chartRadius Q.mirrorRadius b.1 (toImaginary v)
        (leftTranslate (bondSpread c X τ) V) := by
    filter_upwards [h1] with τ hτ
    rw [← chartedSlope_eq_fderiv Q V c X b v (hτ.differentiableAt (by norm_num)), interpolatedCoords_zero]
    rfl
  show |iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => fderiv ℝ (topEnergy Q V c X) (0, τ) (bondVariation b v, 0)) 0
    (basisVectors k)| ≤ _
  rw [iteratedFDeriv_congr_of_eventuallyEq hev k]
  exact H.stationary.deriv_decay b.1 b.2 (toImaginary v) (by rw [norm_toImaginary]; exact hv) k c X (by omega) hX
theorem bondDeriv_slopeTerm_bounds (H : SlopeTermHypotheses Q V κ₂ δ₂ Ct ω Dm Wt Nn Kf Dk Cm)
    (hne : Nonempty ↥(chordBonds (finiteCells F))) (Y : F.Cell) {k : ℕ} (hk : k ≤ 2)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) :
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) →
      ContDiffAt ℝ (1 : ℕ) (fun ζ => bondDeriv (Q.slopeTerm Y ζ) V c X) η) ∧
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) → |bondDeriv (Q.slopeTerm Y η) V c X| ≤
      (Real.sqrt Q.coupling)⁻¹ * ((1 + 5 * Dm) * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c))) *
        remainderMajorant (blockBondSet Y) (bondWeight δ₂ Y) (Real.sqrt Q.coupling) η) ∧
    ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) → ∀ b₀,
      bondGradNorm (fun ζ => bondDeriv (Q.slopeTerm Y ζ) V c X) b₀ η ≤
        (1 + 5 * Dm) * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c)) * bondDecay Q.rate Y b₀ *
          remainderMajorant (blockBondSet Y) (bondWeight δ₂ Y) (Real.sqrt Q.coupling) η := by
  classical
  have hx0 : 0 < Q.coupling := by linarith [H.one_le_coupling]
  have hκ := H.rate_pos
  set f := topEnergy Q V c X with hfdef
  set A := secondJet f 0 (basisVectors k) with hAdef
  set B := blockBondSet Y with hB
  set w := bondWeight (F := F) δ₂ Y with hw'
  set g := bondDecay (F := F) Q.rate Y with hg'
  set E := Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c)) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hδ : 0 ≤ δ₂ := by
    have := H.rate_le
    have h2 : 0 ≤ 2 ^ 10 * Q.rate := by positivity
    linarith
  have h5 : 2 ^ 5 * Q.rate ≤ δ₂ / 3 := by
    have := H.rate_le
    linarith
  have hmemB : ∀ b ∈ B, enclosingCell b.1.1 = Y := fun b hb => by
    simpa [hB, blockBondSet] using hb
  have hself : ∀ z : F.Cell, cellSupDist z z = 0 := fun z => by
    simp [cellSupDist]
  have hw0 : ∀ b, 0 ≤ w b := fun b => (Real.exp_pos _).le
  have hw1 : ∀ b ∈ B, w b = 1 := fun b hb => by
    simp only [hw', bondWeight, hmemB b hb, hself]
    simp
  have hg1 : ∀ b ∈ B, 1 ≤ g b := fun b hb => by
    simp only [hg', bondDecay, hmemB b hb, hself]
    simp
  have hwg : ∀ b, w b ≤ g b := fun b => by
    simp only [hw', hg', bondWeight, bondDecay]
    refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right ?_ (by positivity)))
    have := H.rate_le
    have h2 : 0 < Q.rate := hκ
    nlinarith
  have hfN : ∀ (n : ℕ) (ζ : StepVariable (finiteCells F)), (∀ b, ‖ζ b‖ ≤ Q.ballRadius) →
      ContDiffAt ℝ n f (ζ, 0) :=
    fun n ζ hζ => contDiffAt_topEnergy H hne n c X hζ
  have hA3 : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ Q.ballRadius) → ContDiffAt ℝ (3 : ℕ) A ζ :=
    fun ζ hζ => contDiffAt_secondJet (hfN (3 + k) ζ hζ) le_rfl (basisVectors k)
  have hDk := H.kernel_nonneg k
  have hK : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ Q.ballRadius) →
      ∀ (b₁ b₂ : ↥(chordBonds (finiteCells F))), ∀ b₃ ∈ B, ∀ u₁ u₂ u₃ : BondVector,
        |iteratedFDeriv ℝ 3 A ζ ![bondVariation b₁ u₁, bondVariation b₂ u₂, bondVariation b₃ u₃]| ≤
          Dk 3 k * (w b₁ * w b₂ * E) * (‖u₁‖ * ‖u₂‖ * ‖u₃‖) := by
    intro ζ hζ b₁ b₂ b₃ hb₃ u₁ u₂ u₃
    refine abs_trilinear_le _ b₁ b₂ b₃ (fun v₁ v₂ v₃ h₁ h₂ h₃ => ?_) u₁ u₂ u₃
    have hk3 := (H.kernels ζ hζ).energy 3 k ![b₁, b₂, b₃] ![v₁, v₂, v₃] c X (by norm_num)
      (by intro i; fin_cases i <;> simpa) hX
    have hj := jointMixedDeriv_eq_iteratedFDeriv_secondJet
      (interpolatedEnergy 1 Q.a Q.chartRadius Q.mirrorRadius) ζ V ![b₁, b₂, b₃] ![v₁, v₂, v₃] c X (hfN _ ζ hζ)
    have hv : (fun i => bondVariation ((![b₁, b₂, b₃] : Fin 3 → ↥(chordBonds (finiteCells F))) i)
        ((![v₁, v₂, v₃] : Fin 3 → BondVector) i)) =
        ![bondVariation b₁ v₁, bondVariation b₂ v₂, bondVariation b₃ v₃] := by
      funext i
      fin_cases i <;> rfl
    rw [hv] at hj
    have h := hk3.2
    rw [hj] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hDk)
    set P : Finset F.Cell := ∅ ∪ chordBondCells ![b₁, b₂, b₃] ∪ topBondCells c with hP
    have m1 : ∀ i : Fin 3,
        enclosingCell ((![b₁, b₂, b₃] : Fin 3 → ↥(chordBonds (finiteCells F))) i).1.1 ∈ P := fun i =>
      Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have mY : Y ∈ P := by
      have := m1 2
      simpa [hmemB b₃ hb₃] using this
    have mc : ∀ l, (c l).1 ∈ P := fun l =>
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ l))
    have d1 : (cellSupDist (enclosingCell b₁.1.1) Y : ℝ) ≤ cellSetDiameter P := by
      exact_mod_cast cellSupDist_le_diameter (m1 0) mY
    have d2 : (cellSupDist (enclosingCell b₂.1.1) Y : ℝ) ≤ cellSetDiameter P := by
      exact_mod_cast cellSupDist_le_diameter (m1 1) mY
    have d3 : (bondSpan Y c : ℝ) ≤ cellSetDiameter P := by
      exact_mod_cast bondSpan_le_diameter mY mc
    exact exp_le_three_factors hδ hκ.le h5 d1 d2 d3 (by positivity)
  have hs : ∀ b ∈ B, ∀ u : BondVector, |fderiv ℝ A 0 (bondVariation b u)| ≤ Q.coupling⁻¹ * E * ‖u‖ := by
    intro b hb u
    obtain ⟨v, hv, e⟩ := exists_unit_smul u
    have h1 := abs_fderiv_secondJet_le H hk c X hX b hv (hfN (k + 2) 0 (fun b => by simpa using H.radius_pos.le))
    have hsc : bondVariation b u = ‖u‖ • bondVariation b v := by
      conv_lhs => rw [e]
      simp only [bondVariation]
      rw [Pi.single_smul]
    rw [hsc, map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (norm_nonneg u), mul_comm]
    refine mul_le_mul_of_nonneg_right (h1.trans ?_) (norm_nonneg u)
    have h2 : Ct * ω ≤ Q.coupling⁻¹ := by
      rw [← one_div, le_div_iff₀ hx0]
      linarith [H.small]
    have h3 : Real.exp (-(δ₂ / 8 * bondListDistance (enclosingCell b.1.1) c)) ≤ E := by
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      rw [hmemB b hb]
      have h4 : (bondSpan Y c : ℝ) ≤ 2 * bondListDistance Y c := by
        exact_mod_cast bondSpan_le_two_mul H.symm H.triangle Y c
      have h6 : (0 : ℝ) ≤ bondListDistance Y c := by positivity
      have h7 := H.rate_le
      calc 2 ^ 5 * Q.rate * (bondSpan Y c : ℝ) ≤ 2 ^ 5 * Q.rate * (2 * bondListDistance Y c) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (2 ^ 6 * Q.rate) * bondListDistance Y c := by ring
        _ ≤ (δ₂ / 8) * bondListDistance Y c := mul_le_mul_of_nonneg_right (by linarith) h6
    exact mul_le_mul h2 h3 (Real.exp_pos _).le (inv_nonneg.2 hx0.le)
  have hopen : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ < Q.ballRadius) → ∀ b, ‖ζ b‖ ≤ Q.ballRadius :=
    fun ζ hζ b => (hζ b).le
  have hmaj := fun (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ Q.ballRadius) =>
    remainder_and_fderiv_le_majorant B (ρ := Q.ballRadius) (x := Q.coupling) (D := Dk 3 k) (E := E) (w := w)
      (g := g) hx0 hDk hE0 hw0 hw1 hwg hg1 hA3 hK hs hη
  have eqH : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ Q.ballRadius) →
      bondDeriv (Q.slopeTerm Y ζ) V c X = Q.coupling * remainder dilate B bondProjection A ζ := fun ζ hζ =>
    bondDeriv_slopeTerm Q V Y c X fun v hv => hfN _ _ (norm_smul_apply_le hζ hv)
  have hev : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) →
      (fun ζ => bondDeriv (Q.slopeTerm Y ζ) V c X) =ᶠ[𝓝 η]
        fun ζ => Q.coupling * remainder dilate B bondProjection A ζ := by
    intro η hη
    filter_upwards [(isOpen_openBallProduct Q.ballRadius).mem_nhds hη] with ζ hζ
    exact eqH ζ (hopen ζ hζ)
  have hRc : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ Q.ballRadius) →
      ContDiffAt ℝ (1 : ℕ) (remainder dilate B bondProjection A) η :=
    fun η hη => contDiffAt_remainder (S := dilate) contDiff_dilate B bondProjection 1 (hA3 η hη)
      fun v hv => hA3 _ (norm_smul_apply_le hη hv)
  have hD5 : 1 + 3 * Dk 3 k ≤ 1 + 5 * Dm := by
    have h1 := H.kernel_le k hk
    linarith
  have hD5' : 1 + 5 * Dk 3 k ≤ 1 + 5 * Dm := by
    have h1 := H.kernel_le k hk
    linarith
  have hMaj0 : ∀ η, 0 ≤ remainderMajorant B w (Real.sqrt Q.coupling) η := fun η =>
    Finset.sum_nonneg fun b _ => bondWeightSum_nonneg hw0 (Real.sqrt_nonneg _) b η
  refine ⟨fun η hη => (contDiffAt_const.mul (hRc η (hopen η hη))).congr_of_eventuallyEq (hev η hη),
    fun η hη => ?_, fun η hη b₀ => ?_⟩
  · rw [eqH η (hopen η hη)]
    refine ((hmaj η (hopen η hη)).1).trans ?_
    gcongr
    exact hMaj0 η
  · unfold bondGradNorm
    rw [(hev η hη).fderiv_eq]
    have hd : DifferentiableAt ℝ (remainder dilate B bondProjection A) η :=
      (hRc η (hopen η hη)).differentiableAt (by norm_num)
    rw [fderiv_const_mul hd]
    have hg0 : 0 ≤ g b₀ := (Real.exp_pos _).le
    refine ContinuousLinearMap.opNorm_le_bound _ ?_ fun u => ?_
    · have := hMaj0 η
      have h0 : 0 ≤ 1 + 5 * Dm := by linarith [H.kernel_le 0 (by omega), H.kernel_nonneg 0]
      positivity
    · have h1 := (hmaj η (hopen η hη)).2 b₀ u
      have h2 : ‖((Q.coupling • fderiv ℝ (remainder dilate B bondProjection A) η).comp
          (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b₀)) u‖ =
          |Q.coupling * fderiv ℝ (remainder dilate B bondProjection A) η (bondVariation b₀ u)| := rfl
      rw [h2]
      refine h1.trans ?_
      have := hMaj0 η
      calc _ = (1 + 5 * Dk 3 k) * (E * g b₀ * remainderMajorant B w (Real.sqrt Q.coupling) η * ‖u‖) := by ring
        _ ≤ (1 + 5 * Dm) * (E * g b₀ * remainderMajorant B w (Real.sqrt Q.coupling) η * ‖u‖) :=
            mul_le_mul_of_nonneg_right hD5' (by positivity)
        _ = _ := by ring
theorem rpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 < x) : x ^ (-(1 / 2) : ℝ) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow]
theorem hasSize_of_bounds (H : SlopeTermHypotheses Q V κ₂ δ₂ Ct ω Dm Wt Nn Kf Dk Cm) (Y : F.Cell)
    (Hf : StepVariable (finiteCells F) → ℝ) {E c₁ C : ℝ} (hE : 0 ≤ E) (hc₁ : 0 ≤ c₁) (hC : 1 ≤ C)
    (hC1 : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) → ContDiffAt ℝ (1 : ℕ) Hf η)
    (hv : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) → |Hf η| ≤
      (Real.sqrt Q.coupling)⁻¹ * (c₁ * E) *
        remainderMajorant (blockBondSet Y) (bondWeight δ₂ Y) (Real.sqrt Q.coupling) η)
    (hg : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) → ∀ b₀, bondGradNorm Hf b₀ η ≤
      c₁ * E * bondDecay Q.rate Y b₀ *
        remainderMajorant (blockBondSet Y) (bondWeight δ₂ Y) (Real.sqrt Q.coupling) η) :
    Q.HasSize (fun q => c₁ * (Nn * Wt ^ 2) * (24 * (2 + |Cm (3 * q)|))) V
      (C * Q.coupling ^ (-(1 / 2) : ℝ) * E) Y Hf := by
  have hx0 : 0 < Q.coupling := by linarith [H.one_le_coupling]
  have hsq := rpow_neg_half_eq_inv_sqrt hx0
  set y := Real.sqrt Q.coupling with hy
  have hy0 : 0 < y := Real.sqrt_pos.2 hx0
  have hw0 : ∀ b, 0 ≤ bondWeight (F := F) δ₂ Y b := fun b => (Real.exp_pos _).le
  have hWt : ∑ b, bondWeight (F := F) δ₂ Y b ≤ Wt := H.weights Y
  have hNn : ((blockBondSet Y).card : ℝ) ≤ Nn := H.card_le Y
  have hNn0 : 0 ≤ Nn := (Nat.cast_nonneg _).trans hNn
  have hcard : ((blockBondSet Y).card : ℝ) * Wt ^ 2 ≤ Nn * Wt ^ 2 := by gcongr
  refine ⟨fun η hη => (hC1 η hη).differentiableAt (by norm_num), 0, fun q hq => ⟨?_, fun b => ?_⟩⟩
  · have hM0 : 0 ≤ 24 * (2 + |Cm (3 * q)|) := by positivity
    have hcont : ContinuousOn (fun η => Hf η - 0) {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < Q.ballRadius} :=
      fun η hη => ((hC1 η hη).continuousAt.sub continuousAt_const).continuousWithinAt
    have h1 := momentBound_of_le_majorant H.law hx0 H.radius_pos H.moments (blockBondSet Y) hw0 hWt hcont hq
      (c := y⁻¹ * (c₁ * E)) (by positivity) (fun η hη => by simpa using hv η hη)
    refine momentBound_mono h1 (by positivity) ?_
    rw [hsq]
    set M := 24 * (2 + |Cm (3 * q)|)
    calc y⁻¹ * (c₁ * E) * (((blockBondSet Y).card : ℝ) * Wt ^ 2) * M ≤ y⁻¹ * (c₁ * E) * (Nn * Wt ^ 2) * M := by
          gcongr
      _ = c₁ * (Nn * Wt ^ 2) * M * (1 * y⁻¹ * E) := by ring
      _ ≤ c₁ * (Nn * Wt ^ 2) * M * (C * y⁻¹ * E) := by gcongr
  · have hM0 : 0 ≤ 24 * (2 + |Cm (3 * q)|) := by positivity
    have hcont : ContinuousOn (bondGradNorm Hf b) {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < Q.ballRadius} :=
      fun η hη => by
        have h1 : ContinuousAt (fderiv ℝ Hf) η := ((hC1 η hη).fderiv_right (m := 0) (by norm_num)).continuousAt
        have h2 : ContinuousAt (fun ζ => (fderiv ℝ Hf ζ).comp
            (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b)) η :=
          h1.clm_comp continuousAt_const
        exact h2.norm.continuousWithinAt
    have hd0 : 0 ≤ bondDecay (F := F) Q.rate Y b := (Real.exp_pos _).le
    have h1 := momentBound_of_le_majorant H.law hx0 H.radius_pos H.moments (blockBondSet Y) hw0 hWt hcont hq
      (c := c₁ * E * bondDecay Q.rate Y b) (by positivity) (fun η hη => by
        have hp : 0 ≤ bondGradNorm Hf b η := norm_nonneg _
        rw [abs_of_nonneg hp]
        exact hg η hη b)
    refine momentBound_mono h1 (by positivity) ?_
    rw [hsq]
    show _ ≤ c₁ * (Nn * Wt ^ 2) * (24 * (2 + |Cm (3 * q)|)) * y * (C * y⁻¹ * E) * bondDecay Q.rate Y b
    set M := 24 * (2 + |Cm (3 * q)|)
    have hyy : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0.ne'
    calc c₁ * E * bondDecay Q.rate Y b * (((blockBondSet Y).card : ℝ) * Wt ^ 2) * M ≤
          c₁ * E * bondDecay Q.rate Y b * (Nn * Wt ^ 2) * M := by gcongr
      _ = c₁ * (Nn * Wt ^ 2) * M * (1 * E) * bondDecay Q.rate Y b := by ring
      _ ≤ c₁ * (Nn * Wt ^ 2) * M * (C * E) * bondDecay Q.rate Y b := by gcongr
      _ = c₁ * (Nn * Wt ^ 2) * M * (y * y⁻¹) * (C * E) * bondDecay Q.rate Y b := by rw [hyy]; ring
      _ = _ := by ring
end Hypotheses
section Assembly
variable {V : F.GaugeField F.top} {κ₂ δ₂ Ct ω Dm Wt Nn : ℝ} {Kf : ℕ → ℝ} {Dk : ℕ → ℕ → ℝ} {Cm : ℕ → ℝ}
theorem isSecondOrderRemainder_of_bounds {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {f : LocalFamily}
    (H : SlopeTermHypotheses (coldHalfLawAt T x f) V κ₂ δ₂ Ct ω Dm Wt Nn Kf Dk Cm) (hDm : 0 ≤ Dm) (Y : F.Cell)
    (K : AboveFrames F)
    (hsm : ∀ (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ ≤ (coldHalfLawAt T x f).ballRadius) →
        ContDiffAt ℝ (2 : ℕ) (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
          K q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η))
    (hl : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
      AreUnitVectors X →
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < (coldHalfLawAt T x f).ballRadius) →
        ContDiffAt ℝ (1 : ℕ) (fun ζ => bondDeriv (K ζ) V c X) η) ∧
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < (coldHalfLawAt T x f).ballRadius) →
        |bondDeriv (K η) V c X| ≤
          (Real.sqrt (coldHalfLawAt T x f).coupling)⁻¹ *
            ((1 + 5 * Dm) * Real.exp (-(2 ^ 5 * (coldHalfLawAt T x f).rate * bondSpan Y c))) *
            remainderMajorant (blockBondSet Y) (bondWeight δ₂ Y) (Real.sqrt (coldHalfLawAt T x f).coupling) η) ∧
      ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < (coldHalfLawAt T x f).ballRadius) → ∀ b₀,
        bondGradNorm (fun ζ => bondDeriv (K ζ) V c X) b₀ η ≤
          (1 + 5 * Dm) * Real.exp (-(2 ^ 5 * (coldHalfLawAt T x f).rate * bondSpan Y c)) *
            bondDecay (coldHalfLawAt T x f).rate Y b₀ *
            remainderMajorant (blockBondSet Y) (bondWeight δ₂ Y) (Real.sqrt (coldHalfLawAt T x f).coupling) η) :
    IsSecondOrderRemainder T x f (fun q => (1 + 5 * Dm) * (Nn * Wt ^ 2) * (24 * (2 + |Cm (3 * q)|)))
      (1 + (1 + 5 * Dm) * (Nn * Wt ^ 2) * (24 * (2 + |Cm (3 * 1)|)))
      ((1 + (1 + 5 * Dm) * (Nn * Wt ^ 2) * (24 * (2 + |Cm (3 * 1)|))) * x ^ (-(1 / 2) : ℝ)) Y K V := by
  classical
  set Q := coldHalfLawAt T x f with hQ
  have hx0 : 0 < Q.coupling := by linarith [H.one_le_coupling]
  have hsq := rpow_neg_half_eq_inv_sqrt hx0
  set y := Real.sqrt Q.coupling with hy
  have hc₁ : 0 ≤ 1 + 5 * Dm := by positivity
  have hw0 : ∀ b, 0 ≤ bondWeight (F := F) δ₂ Y b := fun b => (Real.exp_pos _).le
  have hWt : ∑ b, bondWeight (F := F) δ₂ Y b ≤ Wt := H.weights Y
  have hNn : ((blockBondSet Y).card : ℝ) ≤ Nn := H.card_le Y
  have hNn0 : 0 ≤ Nn := (Nat.cast_nonneg _).trans hNn
  set A₁ := (1 + 5 * Dm) * (Nn * Wt ^ 2) * (24 * (2 + |Cm (3 * 1)|)) with hA₁
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hC : 1 ≤ 1 + A₁ := by linarith
  refine ⟨⟨fun η k c X hη => hsm η k c X hη, fun k c X hk hX => ?_⟩, ?_, fun c X hX => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hl k c X (by omega) hX
    exact hasSize_of_bounds H Y _ (Real.exp_pos _).le hc₁ hC h1 h2 h3
  · obtain ⟨h1, h2, -⟩ := hl 0 Fin.elim0 Fin.elim0 (by omega) (fun l => l.elim0)
    have e : ∀ η : StepVariable (finiteCells F), bondDeriv (K η) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions) = K η V := fun η => by
      simp only [bondDeriv, iteratedFDeriv_zero_apply]
      rw [ResponseInTheExpansion.leftTranslate_bondSpread_zero]
    simp only [e] at h1 h2
    have hcont : ContinuousOn (fun η => K η V) {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < Q.ballRadius} :=
      fun η hη => (h1 η hη).continuousAt.continuousWithinAt
    exact integrable_mul_density_of_bounded H.law hcont fun η hη => (h2 η hη).trans
      (mul_le_mul_of_nonneg_left
        (remainderMajorant_le _ _ hw0 hWt (Real.sqrt_nonneg _) H.radius_pos.le η hη) (by positivity))
  · obtain ⟨h1, h2, -⟩ := hl 2 c X le_rfl hX
    have hcont : ContinuousOn (fun η => bondDeriv (K η) V c X)
        {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < Q.ballRadius} :=
      fun η hη => (h1 η hη).continuousAt.continuousWithinAt
    set E := Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c)) with hE
    have hm := momentBound_of_le_majorant H.law hx0 H.radius_pos H.moments (blockBondSet Y) hw0 hWt hcont le_rfl
      (c := y⁻¹ * ((1 + 5 * Dm) * E)) (by positivity) h2
    have h3 := (abs_ballExpectation_le H.law _).trans hm.2
    rw [pow_one] at h3
    refine h3.trans ?_
    have hsq' : x ^ (-(1 / 2) : ℝ) = y⁻¹ := hsq
    rw [hsq']
    show _ ≤ (1 + A₁) * ((1 + A₁) * y⁻¹) * E
    have hcard : ((blockBondSet Y).card : ℝ) * Wt ^ 2 ≤ Nn * Wt ^ 2 := by gcongr
    have h4 : A₁ ≤ (1 + A₁) * (1 + A₁) := by nlinarith
    calc y⁻¹ * ((1 + 5 * Dm) * E) * (((blockBondSet Y).card : ℝ) * Wt ^ 2) * (24 * (2 + |Cm (3 * 1)|)) ≤
          y⁻¹ * ((1 + 5 * Dm) * E) * (Nn * Wt ^ 2) * (24 * (2 + |Cm (3 * 1)|)) := by gcongr
      _ = A₁ * (y⁻¹ * E) := by rw [hA₁]; ring
      _ ≤ (1 + A₁) * (1 + A₁) * (y⁻¹ * E) := by gcongr
      _ = _ := by ring
theorem slopeTerm_eq_zero_of_isEmpty (Q : ColdHalfLaw) (Y : F.Cell) (h : IsEmpty ↥(chordBonds (finiteCells F))) :
    Q.slopeTerm Y = fun _ _ => 0 := by
  funext η V
  simp [ColdHalfLaw.slopeTerm, ColdHalfLaw.sumOverBlock]
theorem isSecondOrderRemainder_slopeTerm {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {f : LocalFamily}
    (H : SlopeTermHypotheses (coldHalfLawAt T x f) V κ₂ δ₂ Ct ω Dm Wt Nn Kf Dk Cm) (hDm : 0 ≤ Dm) (Y : F.Cell) :
    IsSecondOrderRemainder T x f (fun q => (1 + 5 * Dm) * (Nn * Wt ^ 2) * (24 * (2 + |Cm (3 * q)|)))
      (1 + (1 + 5 * Dm) * (Nn * Wt ^ 2) * (24 * (2 + |Cm (3 * 1)|)))
      ((1 + (1 + 5 * Dm) * (Nn * Wt ^ 2) * (24 * (2 + |Cm (3 * 1)|))) * x ^ (-(1 / 2) : ℝ)) Y
      ((coldHalfLawAt T x f).slopeTerm Y) V := by
  by_cases hne : Nonempty ↥(chordBonds (finiteCells F))
  · exact isSecondOrderRemainder_of_bounds H hDm Y _
      (fun η k c X hη => contDiffAt_slopeTerm _ V Y c X fun v hv =>
        contDiffAt_topEnergy H hne 4 c X (norm_smul_apply_le hη hv))
      (fun k c X hk hX => bondDeriv_slopeTerm_bounds H hne Y hk c X hX)
  · have hz := slopeTerm_eq_zero_of_isEmpty (coldHalfLawAt T x f) Y (not_nonempty_iff.1 hne)
    rw [hz]
    have e : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
        bondDeriv (fun _ : F.GaugeField F.top => (0 : ℝ)) V c X = 0 := fun {k} c X => by
      unfold bondDeriv
      have h1 : iteratedFDeriv ℝ k (fun _ : Fin k → ℝ => (0 : ℝ)) = 0 := iteratedFDeriv_fun_zero
      rw [h1]
      rfl
    have hw0 : ∀ b, 0 ≤ bondWeight (F := F) δ₂ Y b := fun b => (Real.exp_pos _).le
    have hMaj0 : ∀ (y : ℝ), 0 ≤ y → ∀ η, 0 ≤ remainderMajorant (blockBondSet Y) (bondWeight δ₂ Y) y η :=
      fun y hy η => Finset.sum_nonneg fun b _ => bondWeightSum_nonneg hw0 hy b η
    refine isSecondOrderRemainder_of_bounds H hDm Y _ (fun η k c X hη => contDiffAt_const)
      (fun k c X hk hX => ?_)
    simp only [e]
    have hs0 := Real.sqrt_nonneg (coldHalfLawAt T x f).coupling
    have hM := hMaj0 _ hs0
    have hc₁ : 0 ≤ 1 + 5 * Dm := by positivity
    refine ⟨fun η _ => contDiffAt_const, fun η _ => ?_, fun η _ b₀ => ?_⟩
    · rw [abs_zero]
      have := hM η
      have hE := (Real.exp_pos (-(2 ^ 5 * (coldHalfLawAt T x f).rate * bondSpan Y c))).le
      positivity
    · have h0 : bondGradNorm (fun _ : StepVariable (finiteCells F) => (0 : ℝ)) b₀ η = 0 := by
        unfold bondGradNorm
        simp
      rw [h0]
      have := hM η
      have hE := (Real.exp_pos (-(2 ^ 5 * (coldHalfLawAt T x f).rate * bondSpan Y c))).le
      have hd := (Real.exp_pos (-(2 * (coldHalfLawAt T x f).rate *
        (cellSupDist (enclosingCell b₀.1.1) Y : ℝ)))).le
      have hd' : 0 ≤ bondDecay (F := F) (coldHalfLawAt T x f).rate Y b₀ := hd
      positivity
end Assembly
def kernelBound (D : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℝ) (U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : ℝ :=
  D (rateParameters U) 3 0 + D (rateParameters U) 3 1 + D (rateParameters U) 3 2
def bondCountBound (U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : ℝ := ((4 * U.L ^ 4 : ℕ) : ℝ)
def weightSumBound (Wf : ℕ → ℝ → ℝ) (U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : ℝ := Wf (4 * U.L ^ 4) (U.chainParams.δ₂ / 3)
def sizeFunction (D : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℝ) (Wf : ℕ → ℝ → ℝ) (Cm : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ)
    (U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (q : ℕ) : ℝ :=
  (1 + 5 * kernelBound D U) * (bondCountBound U * weightSumBound Wf U ^ 2) *
    (24 * (2 + |Cm (momentParameters U) (3 * q)|))
def sizeConstant (D : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℝ) (Wf : ℕ → ℝ → ℝ) (Cm : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ)
    (U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : ℝ :=
  1 + (1 + 5 * kernelBound D U) * (bondCountBound U * weightSumBound Wf U ^ 2) *
    (24 * (2 + |Cm (momentParameters U) (3 * 1)|))
end SlopeTermSlot
open SlopeTermSlot Dilation in
theorem slopeTermRemainderStatement_holds (hFB : interpolatedFramesStatement)
    (hKe : interpolationKernelBoundsStatement) (hFew : Estimates.cellBondsCardStatement)
    (hSum : CellCounting.ExpDecaySumBounded) (hLaw : ConvexObservables.normalizedBallLawIsProbabilityStatement)
    (hCF : CouplingThreshold) (hG : CubicTorusCellGeometry) (hJ : EventuallyInParametersCombines) :
    slopeTermRemainderStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cm, Cz, Cr, hP⟩ := hFB
  obtain ⟨Kf, D, -, hD, hKer⟩ := hKe
  obtain ⟨hg1, -⟩ := hG
  choose! Wf hWf0 hWf using hSum
  have hdm : ∀ U, 0 < kernelBound D U := fun U => by
    have h0 := hD (rateParameters U) 3 0
    have h1 := hD (rateParameters U) 3 1
    have h2 := hD (rateParameters U) 3 2
    unfold kernelBound
    positivity
  have hnn : ∀ U, 0 ≤ bondCountBound U := fun U => Nat.cast_nonneg _
  have hfloors : EventuallyInParameters fun T => 64 ≤ T.n₀ ∧ 1 ≤ T.coupling ∧ 1 ≤ T.Ct ∧
      T.κ ≤ T.chainParams.δ₂ / 2 ^ 14 ∧
      ∀ x, T.coupling ≤ x → T.Ct * x ^ 2 * (T.Ct * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x))) ≤ 1 := by
    intro a _
    refine ⟨0, fun L _ _ c hc => ⟨1, fun Ct hCt => ?_⟩⟩
    obtain ⟨⟨-, -, -, hδ, -⟩, -⟩ := hc.classical
    refine ⟨c.δ₂ / 2 ^ 14, by positivity, fun κ hκ0 hκ => ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun nss _ =>
      ⟨1, one_pos, fun σ hσ0 _ p _ => ⟨0, fun Cs _ E _ => ⟨64, fun n₀ hn => ⟨0, fun CE _ => ?_⟩⟩⟩⟩⟩⟩⟩
    obtain ⟨y₀, hy⟩ := hCF Ct Ct c.δ₂ κ σ 0 hδ hκ0 hκ hσ0
    refine ⟨max y₀ 1, fun y₁ hy₁ => ⟨hn, (le_max_right _ _).trans hy₁, hCt, hκ, fun x hx => ?_⟩⟩
    obtain ⟨-, -, -, h4, -, -⟩ := hy x ((le_max_left _ _).trans (hy₁.trans hx))
    refine h4.trans (Real.exp_le_one_iff.2 ?_)
    have : 0 ≤ 2 ^ 10 * κ * (frameRadius x : ℝ) := by positivity
    linarith
  refine ⟨sizeFunction D Wf Cm, sizeConstant D Wf Cm, fun T q => ?_, fun T => ?_, ?_⟩
  · have := hdm T
    have := hnn T
    unfold sizeFunction
    positivity
  · have := hdm T
    have := hnn T
    unfold sizeConstant
    positivity
  refine weaken _ _ ?_ (join _ _ hP (join _ _ hKer hfloors))
  rintro T hDr ⟨hPT, hKT, h64, hy1, hCt1, hκδ, hsmall⟩
  intro t x f F V Y hst _
  have hfl : T.coupling ≤ x := hst.coupling_le
  have hx1 : 1 ≤ x := hy1.trans hfl
  have hx0 : 0 < x := by linarith
  have hPT' := hPT t x hfl
  set Q := coldHalfLawAt T x f with hQ
  let M : LawOnBondVariables ↥(chordBonds (finiteCells F)) := ResponseInTheExpansion.lawAtTop V (Q.exponent V)
  have hadm : M.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t
      T.n₀ (frameRadius x) (chordBondDist F) :=
    ⟨hst.torus, hst.small_curvature, IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hst.family_bounded,
      Function.injective_id, fun _ _ => rfl⟩
  obtain ⟨hconv, hmom, -⟩ := hPT'.laws _ (chordBondDist F) 1 (fun _ => 1) (fun _ => M)
    ⟨fun _ => zero_le_one, by simp⟩ (fun _ => hadm)
  rw [ResponseInTheExpansion.convexCombinationExponent_lawAtTop] at hconv hmom
  obtain ⟨Ψ', K', hΨ', hconvex, -, -⟩ := hconv
  have hΨc : Continuous Ψ' := hconvex.smooth.continuous
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  have hκ : 0 < T.κ := hDr.κ_pos
  obtain ⟨-, -, -, -, -, hd0, hdi, hdp, -, hnz, -⟩ := hLaw _ T.ballRadius T.p Ψ' hρ hDr.cutoff hΨc
  have hz : ∀ η : BondField ↥(chordBonds (finiteCells F)), ¬ (∀ b, ‖η b‖ < T.ballRadius) →
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' η = 0 := fun η hη => by
    by_contra hne
    exact hη ((hnz η).1 hne)
  have hd : ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent V) =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' := by
    funext η
    by_cases hη' : ∀ b, ‖η b‖ < T.ballRadius
    · unfold ballDensity
      rw [hΨ' η hη']
    · have h0 := hz η hη'
      have h1 : radialWeightProd (cutoffFactor T.ballRadius T.p) η = 0 := by
        unfold ballDensity at h0
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · exact absurd h (Real.exp_pos _).ne'
      rw [h0]
      unfold ballDensity
      rw [h1, zero_mul]
  have hlaw : IsBallLaw Q.ballRadius Q.radialWeight (Q.exponent V) := by
    show IsBallLaw T.ballRadius (cutoffFactor T.ballRadius T.p) (Q.exponent V)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hd]; exact hd0
    · rw [hd]; exact hdi
    · rw [hd]; exact hdp
    · rw [hd]; exact hz
  obtain ⟨hLF, htt, n, hside, hn⟩ := hst.torus
  have hnpos : 64 ≤ n := h64.trans hn
  have hoddF : Odd F.blockSide := by rw [hLF]; exact hDr.odd_L
  have hcub : IsLargeCubicTorus F := ⟨n, hnpos, hside⟩
  obtain ⟨-, -, hsym, htri, -⟩ := hg1 F hoddF hcub
  have hN : ∀ z : F.Cell,
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤
        4 * T.L ^ 4 := fun z => by
    have := hFew F hoddF (fun i => by rw [hside]; omega) z
    rwa [hLF] at this
  have hδ : 0 < T.chainParams.δ₂ := by
    obtain ⟨⟨-, -, -, hδ, -⟩, -⟩ := hDr.chain_admissible.classical
    exact hδ
  have hδ3 : 0 < T.chainParams.δ₂ / 3 := by positivity
  have hgap : frameGapBound T (frameRadius x) =
      T.Ct * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) := rfl
  have hsm := hsmall x hfl
  have hCt0 : 0 < T.Ct := by linarith
  have H : SlopeTermHypotheses Q V T.chainParams.κ₂ T.chainParams.δ₂ T.Ct (frameGapBound T (frameRadius x))
      (kernelBound D (parametersBeforeSide T)) (weightSumBound Wf (parametersBeforeSide T))
      (bondCountBound (parametersBeforeSide T)) (Kf (rateParameters T)) (D (rateParameters T))
      (Cm (momentParameters T)) := by
    refine ⟨hx1, hκ, hρ, ?_, fun j => (hD _ 3 j).le, fun j hj => ?_,
      fun η hη => hKT x t F V 1 η hfl ⟨hLF, htt, n, hside, hn⟩ hst.small_curvature zero_le_one le_rfl hη,
      (hPT'.one_torus F V 1 ⟨hLF, htt, n, hside, hn⟩ hst.small_curvature zero_le_one le_rfl).slope, ?_, ?_, hlaw,
      hmom.moments, ?_, ?_, hsym, htri⟩
    · show 2 ^ 10 * T.κ ≤ T.chainParams.δ₂
      have : 2 ^ 14 * T.κ ≤ T.chainParams.δ₂ := by
        have h2 := hκδ
        rw [le_div_iff₀ (by positivity)] at h2
        linarith
      nlinarith
    · have h0 := hD (rateParameters T) 3 0
      have h1 := hD (rateParameters T) 3 1
      have h2 := hD (rateParameters T) 3 2
      show D (rateParameters T) 3 j ≤
        D (rateParameters T) 3 0 + D (rateParameters T) 3 1 + D (rateParameters T) 3 2
      interval_cases j <;> linarith
    · show x * (T.Ct * frameGapBound T (frameRadius x)) ≤ 1
      rw [hgap]
      have hE : 0 < T.Ct * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) := by positivity
      have h3 : x ≤ x ^ 2 := by nlinarith
      refine le_trans ?_ hsm
      have h4 : x * T.Ct ≤ T.Ct * x ^ 2 := by nlinarith
      calc _ = (x * T.Ct) * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) * T.Ct := by ring
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right h4 hE.le]
    · rw [hgap]
      positivity
    · intro z
      exact hWf (4 * T.L ^ 4) (T.chainParams.δ₂ / 3) hδ3 F _
        (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) hN z
    · intro z
      have h1 := hN z
      show (((blockBondSet z).card : ℕ) : ℝ) ≤ ((4 * T.L ^ 4 : ℕ) : ℝ)
      have h2 : (blockBondSet z).card ≤ 4 * T.L ^ 4 := by
        unfold blockBondSet
        convert h1
      exact_mod_cast h2
  exact isSecondOrderRemainder_slopeTerm H (hdm _).le Y
end WeightedResponses
end YangMills.Construction
end
