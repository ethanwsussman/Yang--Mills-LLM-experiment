import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfTheExpansionAtAFlatTopProof
import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorusProof
import YangMills.Construction.ResponseInTheExpansion.TheResponseContractsCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames WeightedResponses
namespace CurvatureContraction
variable {F : BlockFrame}
private def componentCLM (X : imaginaryQuaternions) (hX : ‖X‖ = 1) : ℍ[ℝ] →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := componentAlong X
      map_add' := componentAlong_add X
      map_smul' := fun r q => by simpa using componentAlong_smul X r q } 1
    (fun q => by simpa using abs_componentAlong_le hX q)
private def conjCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.mkContinuous
    { toFun := star
      map_add' := star_add
      map_smul' := fun r q => by ext <;> simp } 1
    (fun q => by simp)
private theorem minimizingCoordinates_spec (hC : ChartDeterminedByField) {a ρ N0 s : ℝ} (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (hρ : ρ ≤ 1) {V : F.GaugeField F.top}
    (h : HasColdMinimizer a ρ N0 s (finiteCells F) V) :
    IsMinimizingChart a (finiteCells F) V (min ρ (N0 * s)) (minimizingCoordinates a (finiteCells F) V ρ) ∧
      IsCold (finiteCells F) F.depth (s / 8) (chartedField (minimizingCoordinates a (finiteCells F) V ρ) V) := by
  obtain ⟨w, hw, hcold, huniq⟩ := h
  have hw' : IsMinimizingChart a (finiteCells F) V ρ w :=
    ⟨hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩
  have hex : ∃ w, IsMinimizingChart a (finiteCells F) V ρ w := ⟨w, hw'⟩
  have hch : minimizingCoordinates a (finiteCells F) V ρ = hex.choose := by
    unfold minimizingCoordinates
    rw [dif_pos hex]
  have hspec := hex.choose_spec
  obtain ⟨γ, hγ, hsame⟩ := huniq (chartedField hex.choose V) hspec.2.2
  have heq : hex.choose = w := hC F w hex.choose V γ hL hs hw'.1 hspec.1
    (fun b hb => (hw'.2.1 b hb).trans hρ) (fun b hb => (hspec.2.1 b hb).trans hρ) hγ hsame
  rw [hch, heq]
  exact ⟨hw, hcold⟩
private theorem minimizingCoordinates_of_not_mem {a ρ : ℝ} (V : F.GaugeField F.top) (b : F.Site F.depth × Fin 4)
    (hb : b ∉ chordBonds (finiteCells F)) : minimizingCoordinates a (finiteCells F) V ρ b.1 b.2 = 0 := by
  unfold minimizingCoordinates
  split_ifs with h
  · exact h.choose_spec.1 b hb
  · rfl
private theorem hasDerivAt_pathHolonomy {j : ℕ} (X : imaginaryQuaternions) (W : ℝ → F.GaugeField j)
    (d : F.Site j → Fin 4 → ℍ[ℝ]) (h0 : ∀ x i, W 0 x i = 1)
    (hd : ∀ x i, HasDerivAt (fun τ => ((W τ x i : UnitQuaternion) : ℍ[ℝ])) (d x i) 0) (l : List PathStep)
    (x : F.Site j) :
    ∃ D : ℍ[ℝ], HasDerivAt (fun τ => ((pathHolonomy (W τ) x l : UnitQuaternion) : ℍ[ℝ])) D 0 ∧
      componentAlong X D = pathSum (fun y i => componentAlong X (d y i)) x l ∧ pathHolonomy (W 0) x l = 1 := by
  induction l generalizing x with
  | nil =>
    refine ⟨0, ?_, ?_, rfl⟩
    · simpa [pathHolonomy] using hasDerivAt_const (0 : ℝ) (1 : ℍ[ℝ])
    · simp [pathSum, componentAlong_zero]
  | cons st r ih =>
    obtain ⟨D, hD, hc, h1⟩ := ih (x + stepDisplacement j st)
    have hstep : ∃ E : ℍ[ℝ], HasDerivAt (fun τ => ((linkValue (W τ) x st : UnitQuaternion) : ℍ[ℝ])) E 0 ∧
        componentAlong X E = (if st.2 then componentAlong X (d x st.1)
          else - componentAlong X (d (x - BlockAverages.unitStep j st.1) st.1)) ∧ linkValue (W 0) x st = 1 := by
      rcases st with ⟨i, b⟩
      cases b with
      | true =>
        exact ⟨d x i, by simpa [linkValue] using hd x i, by simp, by simp [linkValue, h0]⟩
      | false =>
        refine ⟨star (d (x - BlockAverages.unitStep j i) i), ?_, ?_, by simp [linkValue, h0]⟩
        · have h := conjCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd (x - BlockAverages.unitStep j i) i)
          exact h
        · simp [componentAlong_star]
    obtain ⟨E, hE, hcE, hs1⟩ := hstep
    refine ⟨E + D, ?_, ?_, ?_⟩
    · have hm := hE.mul hD
      have e1 : (fun τ => ((pathHolonomy (W τ) x (st :: r) : UnitQuaternion) : ℍ[ℝ])) =
          (fun τ => ((linkValue (W τ) x st : UnitQuaternion) : ℍ[ℝ])) *
            (fun τ => ((pathHolonomy (W τ) (x + stepDisplacement j st) r : UnitQuaternion) : ℍ[ℝ])) := by
        funext τ
        simp [pathHolonomy]
      have hv : E + D = E * ((pathHolonomy (W 0) (x + stepDisplacement j st) r : UnitQuaternion) : ℍ[ℝ]) +
          ((linkValue (W 0) x st : UnitQuaternion) : ℍ[ℝ]) * D := by
        rw [hs1, h1]
        simp
      rw [e1, hv]
      exact hm
    · rw [componentAlong_add, hc, hcE]
      rfl
    · show linkValue (W 0) x st * pathHolonomy (W 0) (x + stepDisplacement j st) r = 1
      rw [hs1, h1, one_mul]
private theorem hasDerivAt_expUnit {g : ℝ → imaginaryQuaternions} {e : imaginaryQuaternions} (h0 : g 0 = 0)
    (h : HasDerivAt g e 0) :
    HasDerivAt (fun τ => ((expUnit (g τ) : UnitQuaternion) : ℍ[ℝ])) (e : ℍ[ℝ]) 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatTopExpansionHessian.hasDerivAt_expUnit_path <;> assumption
private theorem plaquetteDefect_abelianField_le {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {j : ℕ}
    (θ : LevelForm F j) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteDefect (abelianField X θ) (x, μ, ν) ≤ |plaquetteCurl θ x μ ν| := by
  have h1 := plaquette_abelianField_le hX θ x μ ν
  set g : UnitQuaternion := plaquetteHolonomy (abelianField X θ) (x, μ, ν) with hg
  have hn : ‖(g : ℍ[ℝ])‖ = 1 := CStarRing.norm_coe_unitary g
  have hsq : ‖(g : ℍ[ℝ]) - 1‖ ^ 2 = 2 - 2 * (g : ℍ[ℝ]).re := by
    have := @norm_sub_sq_real ℍ[ℝ] _ _ (g : ℍ[ℝ]) 1
    rw [this, hn, Quaternion.inner_def]
    simp
    ring
  have h2 : ‖(g : ℍ[ℝ]) - 1‖ ^ 2 ≤ |plaquetteCurl θ x μ ν| ^ 2 := by
    rw [hsq, sq_abs]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).mp h2
private theorem isCold_abelianField {X : imaginaryQuaternions} (hX : ‖X‖ = 1) (θ : LevelForm F F.top) {s' : ℝ}
    (h : ∀ y μ ν, μ < ν → |plaquetteCurl θ y μ ν| < s') : IsCold (finiteCells F) F.top s' (abelianField X θ) := by
  intro p hp
  have hlt : p.2.1 < p.2.2 := by
    have := (Finset.mem_filter.mp hp).2.1
    exact this
  obtain ⟨x, μ, ν⟩ := p
  exact (plaquetteDefect_abelianField_le hX θ x μ ν).trans_lt (h x μ ν hlt)
private theorem hasDerivAt_chartedField (X : imaginaryQuaternions) (θ : LevelForm F F.top)
    (w : ℝ → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (e : F.Site F.depth → Fin 4 → imaginaryQuaternions) (h0 : ∀ x i, w 0 x i = 0)
    (hw : ∀ x i, HasDerivAt (fun τ => w τ x i) (e x i) 0)
    (htree : ∀ x i, IsAxialTreeBond (x, i) → e x i = 0) (x : F.Site F.depth) (i : Fin 4) :
    open Classical in
    chartedField (w 0) (abelianField X fun y i => (0 : ℝ) * θ y i) x i = 1 ∧
      HasDerivAt (fun τ => ((chartedField (w τ) (abelianField X fun y i => τ * θ y i) x i : UnitQuaternion) : ℍ[ℝ]))
        ((e x i : ℍ[ℝ]) + if IsCrossingBond (x, i) then θ (enclosingCell x) i • (X : ℍ[ℝ]) else 0) 0 := by
  classical
  have E1 := hasDerivAt_expUnit (h0 x i) (hw x i)
  by_cases hcr : IsCrossingBond (x, i)
  · have hg : HasDerivAt (fun τ : ℝ => (τ * θ (enclosingCell x) i) • X) (θ (enclosingCell x) i • X) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).mul_const (θ (enclosingCell x) i)).smul_const X
      simpa using this
    have E2 := hasDerivAt_expUnit (by simp) hg
    have hm := E1.mul E2
    refine ⟨?_, ?_⟩
    · simp [chartedField, hcr, h0, abelianField, expUnit_zero_eq_one]
    · have e1 : (fun τ => ((chartedField (w τ) (abelianField X fun y i => τ * θ y i) x i : UnitQuaternion) : ℍ[ℝ])) =
          (fun τ => ((expUnit (w τ x i) : UnitQuaternion) : ℍ[ℝ])) *
            (fun τ => ((expUnit ((τ * θ (enclosingCell x) i) • X) : UnitQuaternion) : ℍ[ℝ])) := by
        funext τ
        simp [chartedField, hcr, abelianField]
      have hv : ((e x i : ℍ[ℝ]) + if IsCrossingBond (x, i) then θ (enclosingCell x) i • (X : ℍ[ℝ]) else 0) =
          (e x i : ℍ[ℝ]) * ((expUnit (((0 : ℝ) * θ (enclosingCell x) i) • X) : UnitQuaternion) : ℍ[ℝ]) +
            ((expUnit (w 0 x i) : UnitQuaternion) : ℍ[ℝ]) *
              ((θ (enclosingCell x) i • X : imaginaryQuaternions) : ℍ[ℝ]) := by
        simp [h0, expUnit_zero_eq_one, hcr]
      rw [e1, hv]
      exact hm
  · by_cases ht : IsAxialTreeBond (x, i)
    · refine ⟨by simp [chartedField, hcr, ht], ?_⟩
      have e1 : (fun τ => ((chartedField (w τ) (abelianField X fun y i => τ * θ y i) x i : UnitQuaternion) : ℍ[ℝ])) =
          fun _ => (1 : ℍ[ℝ]) := by
        funext τ
        simp [chartedField, hcr, ht]
      rw [e1]
      simpa [hcr, htree x i ht] using hasDerivAt_const (0 : ℝ) (1 : ℍ[ℝ])
    · refine ⟨by simp [chartedField, hcr, ht, h0, expUnit_zero_eq_one], ?_⟩
      have e1 : (fun τ => ((chartedField (w τ) (abelianField X fun y i => τ * θ y i) x i : UnitQuaternion) : ℍ[ℝ])) =
          fun τ => ((expUnit (w τ x i) : UnitQuaternion) : ℍ[ℝ]) := by
        funext τ
        simp [chartedField, hcr, ht]
      rw [e1]
      simpa [hcr] using E1
private theorem bondDeriv_single {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ}
    (G : F.GaugeField j → E) (W : F.GaugeField j) (c₀ : F.Site j × Fin 4) (X₀ : imaginaryQuaternions) :
    bondDeriv G W ![c₀] ![X₀] =
      fderiv ℝ (fun τ : Fin 1 → ℝ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread ![c₀] ![X₀] τ) W)) 0
        (Pi.single 0 1) := by
  show iteratedFDeriv ℝ 1 _ 0 _ = _
  rw [iteratedFDeriv_one_apply]
private theorem abelianField_eq_rotatedField {X : imaginaryQuaternions} {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (hc : Function.Bijective c) (θ : LevelForm F F.top) (τ : ℝ) :
    (abelianField X fun y i => τ * θ y i) =
      rotatedField (BlockAverages.bondSpread c (fun _ => X)
        (τ • fun l => θ (c l).1 (c l).2)) (uniformField F F.top) := by
  classical
  funext y i
  obtain ⟨l₀, hl₀⟩ := hc.2 (y, i)
  have hs : BlockAverages.bondSpread c (fun _ => X) (τ • fun l => θ (c l).1 (c l).2) y i =
      (τ * θ y i) • X := by
    unfold BlockAverages.bondSpread
    rw [Finset.sum_eq_single l₀]
    · simp [hl₀]
    · intro l _ hl
      rw [if_neg]
      intro h
      exact hl (hc.1 (h.trans hl₀.symm))
    · simp
  simp [rotatedField, hs, abelianField, uniformField]
private theorem leftTranslate_eq_rotatedField {X : imaginaryQuaternions} {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (W : F.GaugeField F.top) (l : Fin k) (τ : Fin 1 → ℝ) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread ![c l] ![X] τ) W =
      rotatedField (BlockAverages.bondSpread c (fun _ => X)
        (τ 0 • (Pi.single l 1 : Fin k → ℝ))) W := by
  classical
  funext y i
  have hs : ColdStepAtMirrorFrames.bondSpread ![c l] ![X] τ y i =
      BlockAverages.bondSpread c (fun _ => X) (τ 0 • (Pi.single l 1 : Fin k → ℝ)) y i := by
    unfold ColdStepAtMirrorFrames.bondSpread BlockAverages.bondSpread
    rw [Finset.sum_eq_single (0 : Fin 1) (by intro b _ hb; exact absurd (Subsingleton.elim b 0) hb) (by simp)]
    by_cases h : c l = (y, i)
    · rw [Finset.sum_eq_single l]
      · simp [h]
      · intro q _ hq
        simp [hq]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [h]
      · intro q _
        by_cases hq : q = l
        · subst hq
          simp [h]
        · simp [hq]
  simp only [leftTranslate, rotatedField, hs]
private theorem hasDerivAt_minimizingCoordinates {a ρ δ : ℝ} {N : ℕ → ℝ}
    (hflat : HasRegularCoordinates a δ ρ N (finiteCells F) (uniformField F F.top))
    {X : imaginaryQuaternions} {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (hc : Function.Bijective c)
    (θ : LevelForm F F.top) (b : F.Site F.depth × Fin 4) :
    ∃ e : imaginaryQuaternions, HasDerivAt (fun τ : ℝ =>
        minimizingCoordinates a (finiteCells F) (abelianField X fun y i => τ * θ y i) ρ b.1 b.2) e 0 ∧
      (b ∉ chordBonds (finiteCells F) → e = 0) ∧
      e = ∑ l, θ (c l).1 (c l).2 •
        bondDeriv (torusCoordinate a ρ b) (uniformField F F.top) ![c l] ![X] := by
  classical
  by_cases hb : b ∈ chordBonds (finiteCells F)
  · set Φ : (Fin k → ℝ) → imaginaryQuaternions := fun σ => minimizingBondCoordinate a ρ (finiteCells F) b
      (rotatedField (BlockAverages.bondSpread c (fun _ => X) σ) (uniformField F F.top)) with hΦdef
    have hA : AnalyticAt ℝ Φ 0 := (hflat b hb).1 k c (fun _ => X)
    have hΦ : HasFDerivAt Φ (fderiv ℝ Φ 0) 0 := hA.differentiableAt.hasFDerivAt
    set α : Fin k → ℝ := fun l => θ (c l).1 (c l).2 with hα
    have hline : HasDerivAt (fun τ : ℝ => τ • α) α 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const α
    have hΦ' : HasFDerivAt Φ (fderiv ℝ Φ 0) ((0 : ℝ) • α) := by simpa using hΦ
    have hcomp := hΦ'.comp_hasDerivAt (0 : ℝ) hline
    have hsingle : ∀ l, bondDeriv (torusCoordinate a ρ b) (uniformField F F.top) ![c l] ![X] =
        fderiv ℝ Φ 0 (Pi.single l 1) := by
      intro l
      rw [bondDeriv_single]
      have hfun : (fun τ : Fin 1 → ℝ => torusCoordinate a ρ b
          (leftTranslate (ColdStepAtMirrorFrames.bondSpread ![c l] ![X] τ) (uniformField F F.top))) =
          Φ ∘ ((ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ).smulRight
            (Pi.single l 1 : Fin k → ℝ)) := by
        funext τ
        simp only [Function.comp, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, hΦdef]
        rw [leftTranslate_eq_rotatedField c]
        rfl
      rw [hfun]
      have hΦ0 : HasFDerivAt Φ (fderiv ℝ Φ 0)
          (((ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ).smulRight
            (Pi.single l 1 : Fin k → ℝ)) 0) := by simpa using hΦ
      rw [(hΦ0.comp (0 : Fin 1 → ℝ) (ContinuousLinearMap.hasFDerivAt _)).fderiv]
      simp
    refine ⟨fderiv ℝ Φ 0 α, ?_, fun h => absurd hb h, ?_⟩
    · have hfun : (fun τ : ℝ =>
          minimizingCoordinates a (finiteCells F) (abelianField X fun y i => τ * θ y i) ρ b.1 b.2) =
          Φ ∘ fun τ : ℝ => τ • α := by
        funext τ
        simp only [Function.comp, hΦdef]
        rw [← abelianField_eq_rotatedField c hc θ τ]
        rfl
      rw [hfun]
      exact hcomp
    · have hsum : α = ∑ l, α l • (Pi.single l 1 : Fin k → ℝ) := by
        funext q
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hsum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, hsingle]
  · refine ⟨0, ?_, fun _ => rfl, ?_⟩
    · have hfun : (fun τ : ℝ =>
          minimizingCoordinates a (finiteCells F) (abelianField X fun y i => τ * θ y i) ρ b.1 b.2) =
          fun _ => 0 := by
        funext τ
        exact minimizingCoordinates_of_not_mem _ b hb
      rw [hfun]
      exact hasDerivAt_const _ _
    · have hz : torusCoordinate a ρ b = fun _ : F.GaugeField F.top => (0 : imaginaryQuaternions) := by
        funext V
        exact minimizingCoordinates_of_not_mem V b hb
      rw [hz]
      symm
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [bondDeriv_single]
      simp
private theorem curl_response_le_frame (hC : ChartDeterminedByField) {a ρ σA δ : ℝ} {N : ℕ → ℝ}
    (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hρ : ρ ≤ 1) (hσ : 0 < σA) (hN : 0 < N 0)
    (hch : ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ σA → IsCold (finiteCells F) F.top s V →
      HasColdMinimizer a ρ (N 0) s (finiteCells F) V ∧ HasRegularCoordinates a δ ρ N (finiteCells F) V)
    {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (hc : Function.Bijective c) (θ : LevelForm F F.top) {s : ℝ} (hs0 : 0 ≤ s)
    (hθ : ∀ y μ ν, μ < ν → |plaquetteCurl θ y μ ν| ≤ s)
    (x : F.Site F.depth) (μ ν : Fin 4) (hμν : μ < ν) :
    open Classical in
    |plaquetteCurl (fun (x : F.Site F.depth) i => ∑ l, θ (c l).1 (c l).2 * componentAlong X
        ((bondDeriv (torusCoordinate a ρ (x, i)) (uniformField F F.top) ![c l] ![X] : imaginaryQuaternions) : ℍ[ℝ]) +
        if IsCrossingBond (x, i) then θ (enclosingCell x) i else 0) x μ ν| ≤ s / 8 := by
  classical
  have hs1 : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  set V : ℝ → F.GaugeField F.top := fun τ => abelianField X fun y i => τ * θ y i with hVdef
  set w : ℝ → F.Site F.depth → Fin 4 → imaginaryQuaternions :=
    fun τ => minimizingCoordinates a (finiteCells F) (V τ) ρ with hwdef
  have hV0 : V 0 = uniformField F F.top := by
    funext y i
    simp [hVdef, abelianField, expUnit_zero_eq_one, uniformField]
  have hcoldV : ∀ (τ s' : ℝ), (∀ y μ ν, μ < ν → |τ * plaquetteCurl θ y μ ν| < s') →
      IsCold (finiteCells F) F.top s' (V τ) := by
    intro τ s' h
    refine isCold_abelianField hX _ fun y μ ν hlt => ?_
    rw [plaquetteCurl_const_mul]
    exact h y μ ν hlt
  have hcold0 : ∀ s' : ℝ, 0 < s' → IsCold (finiteCells F) F.top s' (V 0) := fun s' h =>
    hcoldV 0 s' fun _ _ _ _ => by simpa using h
  have hflatA : HasRegularCoordinates a δ ρ N (finiteCells F) (uniformField F F.top) := by
    rw [← hV0]
    exact (hch σA (V 0) hσ le_rfl (hcold0 σA hσ)).2
  have hw0 : ∀ x i, w 0 x i = 0 := by
    intro x i
    by_cases hb : (x, i) ∈ chordBonds (finiteCells F)
    · by_contra hne
      have hpos : 0 < ‖w 0 x i‖ := norm_pos_iff.mpr hne
      have hs'0 : 0 < min σA (‖w 0 x i‖ / (2 * N 0)) := lt_min hσ (by positivity)
      have h1 := minimizingCoordinates_spec hC hL hs hρ
        (hch _ (V 0) hs'0 (min_le_left _ _) (hcold0 _ hs'0)).1
      have h3 : ‖w 0 x i‖ ≤ N 0 * min σA (‖w 0 x i‖ / (2 * N 0)) :=
        (h1.1.2.1 (x, i) hb).trans (min_le_right _ _)
      have h4 : N 0 * min σA (‖w 0 x i‖ / (2 * N 0)) ≤ N 0 * (‖w 0 x i‖ / (2 * N 0)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hN.le
      have h5 : N 0 * (‖w 0 x i‖ / (2 * N 0)) = ‖w 0 x i‖ / 2 := by
        field_simp
      linarith
    · exact minimizingCoordinates_of_not_mem (V 0) (x, i) hb
  choose e he1 he2 he3 using fun b : F.Site F.depth × Fin 4 =>
    hasDerivAt_minimizingCoordinates (X := X) hflatA c hc θ b
  have htree : ∀ x i, IsAxialTreeBond (x, i) → e (x, i) = 0 := fun x i ht =>
    he2 _ fun hb => (Finset.mem_filter.mp hb).2 ht
  have hchart := hasDerivAt_chartedField X θ w (fun x i => e (x, i)) hw0 (fun x i => he1 (x, i)) htree
  obtain ⟨D, hD, hcD, hP0⟩ := hasDerivAt_pathHolonomy X (fun τ => chartedField (w τ) (V τ))
    (fun x i => (e (x, i) : ℍ[ℝ]) + if IsCrossingBond (x, i) then θ (enclosingCell x) i • (X : ℍ[ℝ]) else 0)
    (fun x i => (hchart x i).1) (fun x i => (hchart x i).2) [(μ, true), (ν, true), (μ, false), (ν, false)] x
  rw [pathSum_plaquetteLoop] at hcD
  have hR : (fun (x : F.Site F.depth) i => ∑ l, θ (c l).1 (c l).2 * componentAlong X
        ((bondDeriv (torusCoordinate a ρ (x, i)) (uniformField F F.top) ![c l] ![X] : imaginaryQuaternions) : ℍ[ℝ]) +
        if IsCrossingBond (x, i) then θ (enclosingCell x) i else 0) =
      fun x i => componentAlong X ((e (x, i) : ℍ[ℝ]) +
        if IsCrossingBond (x, i) then θ (enclosingCell x) i • (X : ℍ[ℝ]) else 0) := by
    funext x i
    rw [componentAlong_add]
    congr 1
    · conv_rhs => rw [he3 (x, i)]
      rw [Submodule.coe_sum, componentAlong_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Submodule.coe_smul, componentAlong_smul]
    · split_ifs
      · rw [componentAlong_smul, componentAlong_self hX, mul_one]
      · rw [componentAlong_zero]
  rw [hR, ← hcD]
  have hh : HasDerivAt (fun τ => componentAlong X ((pathHolonomy (chartedField (w τ) (V τ)) x
      [(μ, true), (ν, true), (μ, false), (ν, false)] : UnitQuaternion) : ℍ[ℝ])) (componentAlong X D) 0 :=
    (componentCLM X hX).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD
  have hh0 : componentAlong X ((pathHolonomy (chartedField (w 0) (V 0)) x
      [(μ, true), (ν, true), (μ, false), (ν, false)] : UnitQuaternion) : ℍ[ℝ]) = 0 := by
    rw [hP0]
    simpa using componentAlong_one X
  have hmem : (x, μ, ν) ∈ innerPlaquettes (finiteCells F) F.depth := by
    have hsite : ∀ z : F.Site F.depth, z ∈ sitesOfCells (finiteCells F) F.depth := fun z =>
      mem_sitesOfCells_finiteCells hL hs1 (Nat.le_succ _) z
    unfold innerPlaquettes
    refine Finset.mem_filter.mpr ⟨?_, hμν, fun z _ => hsite z⟩
    simp [hsite]
  have hall : ∀ ε : ℝ, 0 < ε → |componentAlong X D| ≤ (s + ε) / 8 := by
    intro ε hε
    have hpos : 0 < s + ε := by linarith
    have habs := (hh.tendsto_slope_zero_right).abs
    refine le_of_tendsto habs ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < σA / (s + ε) by positivity)] with τ hτ
    have hτ0 : 0 < τ := hτ.1
    have hsτ : 0 < τ * (s + ε) := by positivity
    have hle : τ * (s + ε) ≤ σA := by
      have := hτ.2
      rw [lt_div_iff₀ hpos] at this
      exact this.le
    have hcold : IsCold (finiteCells F) F.top (τ * (s + ε)) (V τ) := by
      refine hcoldV τ _ fun y μ ν hlt => ?_
      rw [abs_mul, abs_of_pos hτ0]
      exact mul_lt_mul_of_pos_left (by linarith [hθ y μ ν hlt]) hτ0
    have hlow := (minimizingCoordinates_spec hC hL hs hρ (hch _ (V τ) hsτ hle hcold).1).2 _ hmem
    have hcomp : |componentAlong X ((pathHolonomy (chartedField (w τ) (V τ)) x
        [(μ, true), (ν, true), (μ, false), (ν, false)] : UnitQuaternion) : ℍ[ℝ])| < τ * (s + ε) / 8 := by
      refine lt_of_le_of_lt ?_ hlow
      have h1 := abs_componentAlong_le hX (((pathHolonomy (chartedField (w τ) (V τ)) x
        [(μ, true), (ν, true), (μ, false), (ν, false)] : UnitQuaternion) : ℍ[ℝ]) - 1)
      rw [componentAlong_sub, componentAlong_one, sub_zero] at h1
      exact h1
    simp only [zero_add, hh0, sub_zero, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hτ0]
    rw [inv_mul_le_iff₀ hτ0]
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := hall (8 * ε) (by positivity)
  linarith
private theorem norm_unitGenerator : ‖unitGenerator‖ = 1 := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.norm_unitGenerator <;> assumption
private theorem curl_responseMap_le (hC : ChartDeterminedByField) {a ρ σA δ lam cg : ℝ} {N : ℕ → ℝ} {L : ℕ}
    [NeZero L] (hchain : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hL : Odd L) (u n : ℕ) [NeZero n]
    (hn : 64 ≤ n) (A : TorusFields.TorusBond n → ℝ) (s : ℝ)
    (hA : ∀ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n)),
      |WeightedResponses.curl A p| ≤ s)
    (p : TorusFields.TorusPlaquette (n * L)) (hp : p.2.1 < p.2.2) :
    |WeightedResponses.curl (responseMap a ρ L u A) p| ≤ s / 8 := by
  classical
  obtain ⟨-, -, -, -, hρ1, hσ, -, hN, hch⟩ := hchain
  set F : BlockFrame := TorusFields.torusFrame L u n with hF
  have hodd : Odd F.blockSide := hL
  have hside : ∀ i, 64 ≤ F.extent i := fun _ => hn
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by have := hside i; omega
  have hs1 : ∀ i, 0 < F.extent i := fun i => by have := hside i; omega
  have hreg : IsOrthantRegular (finiteCells F) 1024 := fun z =>
    ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => TopLevelSites.mem_finiteCells hs1 _⟩
  have hch' : ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ σA → IsCold (finiteCells F) F.top s V →
      HasColdMinimizer a ρ (N 0) s (finiteCells F) V ∧ HasRegularCoordinates a δ ρ N (finiteCells F) V := by
    intro s V h1 h2 h3
    obtain ⟨a1, -, -, a4, -⟩ := hch F 1024 (finiteCells F) rfl (Or.inr hside) le_rfl hreg s V h1 h2 h3
    exact ⟨a1, a4⟩
  have hpn : ∀ i, F.period F.top i = n := fun i => TopLevelSites.period_top i
  have hpt : ∀ i, F.period F.depth i = n * L := fun i => TopLevelSites.period_depth i
  set e : Fin (Fintype.card (TorusFields.TorusBond n)) ≃ TorusFields.TorusBond n :=
    (Fintype.equivFin _).symm with he
  set c : Fin (Fintype.card (TorusFields.TorusBond n)) → F.Site F.top × Fin 4 :=
    fun l => (StepCosts.torusSiteInFrame F F.top (e l).1, (e l).2) with hcdef
  have hc : Function.Bijective c := by
    constructor
    · intro l l' h
      have h1 : StepCosts.torusSiteInFrame F F.top (e l).1 = StepCosts.torusSiteInFrame F F.top (e l').1 :=
        congrArg (fun q : F.Site F.top × Fin 4 => q.1) h
      have h2 : (e l).2 = (e l').2 := congrArg (fun q : F.Site F.top × Fin 4 => q.2) h
      have h3 : (e l).1 = (e l').1 := by
        rw [← TopLevelSites.toTorusSite_torusSiteInFrame hpn (e l).1,
          ← TopLevelSites.toTorusSite_torusSiteInFrame hpn (e l').1, h1]
      exact e.injective (Prod.ext h3 h2)
    · rintro ⟨y, i⟩
      refine ⟨e.symm (TorusLumps.toTorusSite n y, i), ?_⟩
      simp [hcdef, TopLevelSites.torusSiteInFrame_toTorusSite hpn]
  set θ : LevelForm F F.top := fun y i => A (TorusLumps.toTorusSite n y, i) with hθdef
  have hθ : ∀ y μ ν, μ < ν → |plaquetteCurl θ y μ ν| ≤ s := by
    intro y μ ν h
    have h1 := hA (TorusLumps.toTorusSite n y, μ, ν) (by simp [TorusFields.plaquettesIn, h])
    have e1 : plaquetteCurl θ y μ ν = WeightedResponses.curl A (TorusLumps.toTorusSite n y, μ, ν) := by
      simp only [plaquetteCurl, WeightedResponses.curl, hθdef]
      rw [TopLevelSites.toTorusSite_add hpn, TopLevelSites.toTorusSite_add hpn,
        TopLevelSites.toTorusSite_unitStep hpn, TopLevelSites.toTorusSite_unitStep hpn]
    rw [e1]
    exact h1
  have hs0 : 0 ≤ s := (abs_nonneg _).trans (hθ 0 0 1 (by decide))
  have key := curl_response_le_frame hC hodd hs2 hρ1 hσ (hN 0) hch' norm_unitGenerator c hc θ hs0 hθ
    (StepCosts.torusSiteInFrame F F.depth p.1) p.2.1 p.2.2 hp
  have hR : ∀ b : TorusFields.TorusBond (n * L), responseMap a ρ L u A b =
      (∑ l, θ (c l).1 (c l).2 * componentAlong unitGenerator
        ((bondDeriv (torusCoordinate a ρ (StepCosts.torusSiteInFrame F F.depth b.1, b.2)) (uniformField F F.top)
          ![c l] ![unitGenerator] : imaginaryQuaternions) : ℍ[ℝ])) +
        if IsCrossingBond (StepCosts.torusSiteInFrame F F.depth b.1, b.2) then
          θ (enclosingCell (StepCosts.torusSiteInFrame F F.depth b.1)) b.2 else 0 := by
    intro b
    have hent : ∀ c' : TorusFields.TorusBond n, responseKernel a ρ L u b c' * A c' =
        A c' * componentAlong unitGenerator
          ((bondDeriv (torusCoordinate a ρ (StepCosts.torusSiteInFrame F F.depth b.1, b.2)) (uniformField F F.top)
            ![(StepCosts.torusSiteInFrame F F.top c'.1, c'.2)] ![unitGenerator] : imaginaryQuaternions) : ℍ[ℝ]) +
          (if IsCrossingBond (StepCosts.torusSiteInFrame F F.depth b.1, b.2) ∧
            enclosingCell (StepCosts.torusSiteInFrame F F.depth b.1) = StepCosts.torusSiteInFrame F F.top c'.1 ∧
            b.2 = c'.2 then A c' else 0) := by
      intro c'
      show (componentAlong unitGenerator ((bondDeriv (torusCoordinate a ρ (StepCosts.torusSiteInFrame F F.depth b.1, b.2))
          (uniformField F F.top) ![(StepCosts.torusSiteInFrame F F.top c'.1, c'.2)] ![unitGenerator] :
            imaginaryQuaternions) : ℍ[ℝ]) +
        (if IsCrossingBond (StepCosts.torusSiteInFrame F F.depth b.1, b.2) ∧
          enclosingCell (StepCosts.torusSiteInFrame F F.depth b.1) = StepCosts.torusSiteInFrame F F.top c'.1 ∧
          b.2 = c'.2 then 1 else 0)) * A c' = _
      split_ifs <;> ring
    show (∑ c' : TorusFields.TorusBond n, responseKernel a ρ L u b c' * A c') = _
    simp_rw [hent]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hθdef, hcdef, TopLevelSites.toTorusSite_torusSiteInFrame hpn]
    · by_cases hcr : IsCrossingBond (StepCosts.torusSiteInFrame F F.depth b.1, b.2)
      · rw [if_pos hcr, Finset.sum_eq_single
          (TorusLumps.toTorusSite n (enclosingCell (StepCosts.torusSiteInFrame F F.depth b.1)), b.2)]
        · simp [hcr, TopLevelSites.torusSiteInFrame_toTorusSite hpn, hθdef]
        · rintro ⟨c₁, i₁⟩ _ hne
          rw [if_neg]
          rintro ⟨-, h2, h3⟩
          apply hne
          have h4 : TorusLumps.toTorusSite n (enclosingCell (StepCosts.torusSiteInFrame F F.depth b.1)) = c₁ := by
            rw [h2]
            exact TopLevelSites.toTorusSite_torusSiteInFrame hpn c₁
          exact Prod.ext h4.symm h3.symm
        · simp
      · rw [if_neg hcr]
        exact Finset.sum_eq_zero fun c' _ => by simp [hcr]
  have hadd : ∀ i, StepCosts.torusSiteInFrame F F.depth (p.1 + TorusFields.unitStep (n * L) i) =
      StepCosts.torusSiteInFrame F F.depth p.1 + BlockAverages.unitStep F.depth i := by
    intro i
    apply TopLevelSites.toTorusSite_injective hpt
    rw [TopLevelSites.toTorusSite_add hpt, TopLevelSites.toTorusSite_torusSiteInFrame hpt,
      TopLevelSites.toTorusSite_torusSiteInFrame hpt, TopLevelSites.toTorusSite_unitStep hpt]
  have hfin : WeightedResponses.curl (responseMap a ρ L u A) p = plaquetteCurl (fun (x : F.Site F.depth) i =>
      (∑ l, θ (c l).1 (c l).2 * componentAlong unitGenerator
        ((bondDeriv (torusCoordinate a ρ (x, i)) (uniformField F F.top) ![c l] ![unitGenerator] :
          imaginaryQuaternions) : ℍ[ℝ])) +
        if IsCrossingBond (x, i) then θ (enclosingCell x) i else 0)
      (StepCosts.torusSiteInFrame F F.depth p.1) p.2.1 p.2.2 := by
    unfold WeightedResponses.curl plaquetteCurl
    rw [hR, hR, hR, hR]
    simp only [hadd]
  rw [hfin]
  exact key
end CurvatureContraction
open CurvatureContraction in
theorem responseContractsCurvature (hC : ChartDeterminedByField) : ResponseContractsCurvatureStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ T _ _ hD _ _ _ _
  refine ⟨0, ?_⟩
  intro y _ _ _ u n _ hn A s hA p hp
  exact curl_responseMap_le hC hD.chain hD.L_odd u n hn A s hA p (Finset.mem_filter.mp hp).2.1
end YangMills.Construction.ResponseInTheExpansion
end
