import YangMills.Construction.ColdChainAtEveryLevel.LeastValuesOfAChain
import YangMills.Construction.ColdStepAtMirrorFrames.ComponentsOfAFieldAlongAnElement
import YangMills.Construction.ColdStepAtMirrorFrames.SmallChainUnderASmallField
import YangMills.Construction.ColdStepAtMirrorFrames.TreeResponseOfTheLeastCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages YangMills.Construction.LatticePaths Filter
variable {F : BlockFrame}
private def topAbelianField (X : imaginaryQuaternions) (b : F.Site F.top × Fin 4) (τ : ℝ) :
    F.GaugeField F.top :=
  abelianField X fun y i => τ * topBondIndicator b y i
private theorem leftTranslate_bondSpread_uniformField (b : F.Site F.top × Fin 4) (X : imaginaryQuaternions)
    (t : Fin 1 → ℝ) :
    leftTranslate (bondSpread ![b] ![X] t) (uniformField F F.top) = topAbelianField X b (t 0) := by
  funext y i
  unfold leftTranslate bondSpread uniformField topAbelianField abelianField topBondIndicator
  by_cases h : (y, i) = b
  · subst h
    simp
  · have h' : ¬ b = (y, i) := fun e => h e.symm
    simp [h, h']
abbrev _root_.YangMills.DeltaSharedProofs.p502581 := @leftTranslate_bondSpread_uniformField
private theorem topAbelianField_zero (b : F.Site F.top × Fin 4) (X : imaginaryQuaternions) :
    topAbelianField X b 0 = uniformField F F.top := by
  funext y i
  simp [topAbelianField, abelianField, uniformField, expUnit_zero_eq_one]
private theorem continuous_componentAlong {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    Continuous (componentAlong X) :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun p q => by
    rw [Real.dist_eq, ← componentAlong_sub, dist_eq_norm]
    simpa using abs_componentAlong_le hX (p - q)).continuous
private theorem tendsto_componentAlong_slope {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {P : ℝ → ℍ[ℝ]}
    {d : ℍ[ℝ]} (hP : HasDerivAt P d 0) (h1 : P 0 = 1) :
    Tendsto (fun τ => componentAlong X (P τ) / τ) (𝓝[>] 0) (𝓝 (componentAlong X d)) := by
  have h := hasDerivAt_iff_tendsto_slope_zero.1 hP
  have h2 : Tendsto (fun t : ℝ => t⁻¹ • (P (0 + t) - P 0)) (𝓝[>] 0) (𝓝 d) :=
    h.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  have h3 := ((continuous_componentAlong hX).tendsto d).comp h2
  refine h3.congr fun τ => ?_
  simp only [Function.comp, zero_add, h1, componentAlong_smul, componentAlong_sub, componentAlong_one,
    sub_zero]
  rw [div_eq_inv_mul]
private theorem hasDerivAt_exp_comp {w : ℝ → ℍ[ℝ]} {d : ℍ[ℝ]} (hw : HasDerivAt w d 0) (h0 : w 0 = 0) :
    HasDerivAt (fun τ => NormedSpace.exp (w τ)) d 0 := by
  have he : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) (w 0) := by
    rw [h0]
    exact hasFDerivAt_exp_zero
  have h := he.comp_hasDerivAt 0 hw
  simp only [ContinuousLinearMap.one_apply] at h
  exact h
private theorem hasDerivAt_topAbelianField (b : F.Site F.top × Fin 4) (X : imaginaryQuaternions)
    (y : F.Site F.top) (i : Fin 4) :
    HasDerivAt (fun τ => (topAbelianField X b τ y i : ℍ[ℝ])) (topBondIndicator b y i • (X : ℍ[ℝ])) 0 := by
  have h1 : HasDerivAt (fun τ : ℝ => (τ * topBondIndicator b y i) • (X : ℍ[ℝ]))
      (topBondIndicator b y i • (X : ℍ[ℝ])) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (topBondIndicator b y i)).smul_const (X : ℍ[ℝ])
  exact hasDerivAt_exp_comp h1 (by simp)
private theorem hasDerivAt_of_analyticAt_bondSpread (G : F.GaugeField F.top → imaginaryQuaternions)
    (b : F.Site F.top × Fin 4) (X : imaginaryQuaternions)
    (hG : AnalyticAt ℝ (fun σ : Fin 1 → ℝ =>
      G (leftTranslate (bondSpread ![b] ![X] σ) (uniformField F F.top))) 0) :
    HasDerivAt (fun τ => G (topAbelianField X b τ)) (bondDeriv G (uniformField F F.top) ![b] ![X]) 0 := by
  set f := fun σ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![b] ![X] σ) (uniformField F F.top)) with hf
  have hd : HasFDerivAt f (fderiv ℝ f 0) 0 := hG.differentiableAt.hasFDerivAt
  have e : bondDeriv G (uniformField F F.top) ![b] ![X] = fderiv ℝ f 0 (Pi.single 0 1) := by
    unfold bondDeriv
    rw [iteratedFDeriv_one_apply]
  have hin : HasDerivAt (fun τ : ℝ => (fun _ : Fin 1 => τ)) (Pi.single 0 1 : Fin 1 → ℝ) 0 := by
    have h := hasDerivAt_pi.2 fun _ : Fin 1 => hasDerivAt_id (0 : ℝ)
    have e2 : (fun _ : Fin 1 => (1 : ℝ)) = Pi.single 0 1 := by
      funext l
      rw [Subsingleton.elim l 0]
      simp
    rw [← e2]
    exact h
  have hc := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (f := fun τ : ℝ => (fun _ : Fin 1 => τ)) hd hin
  rw [e]
  refine hc.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
  simp only [Function.comp, hf, leftTranslate_bondSpread_uniformField]
abbrev _root_.YangMills.DeltaSharedProofs.p501209 := @hasDerivAt_of_analyticAt_bondSpread
private theorem torusCoordinate_eq_zero_of_not_mem {a ρ : ℝ} (bd : F.Site F.depth × Fin 4)
    (hb : bd ∉ chordBonds (finiteCells F)) (V : F.GaugeField F.top) : torusCoordinate a ρ bd V = 0 := by
  unfold torusCoordinate minimizingBondCoordinate minimizingCoordinates
  split_ifs with h
  · exact h.choose_spec.1 bd hb
  · rfl
abbrev _root_.YangMills.SharedProofs.p33224 := @torusCoordinate_eq_zero_of_not_mem
section Parameters
variable {a : ℝ} {L : ℕ} {c : ColdChainParameters}
private theorem hasDerivAt_torusCoordinate (hc : c.Admissible a L) (hFL : F.blockSide = L)
    (hF : IsLargeCubicTorus F) (bd : F.Site F.depth × Fin 4) (b : F.Site F.top × Fin 4)
    (X : imaginaryQuaternions) :
    HasDerivAt (fun τ => torusCoordinate a c.ρA bd (topAbelianField X b τ))
      (bondDeriv (torusCoordinate a c.ρA bd) (uniformField F F.top) ![b] ![X]) 0 := by
  apply hasDerivAt_of_analyticAt_bondSpread
  by_cases hb : bd ∈ chordBonds (finiteCells F)
  · have hσ : 0 < c.σA := hc.positivity.2.2.2.1
    have hcold : IsSmallCurvature c.σA (uniformField F F.top) :=
      isSmallCurvature_of_near_one (uniformField F F.top) (m := 0) (by linarith)
        (fun x i => by simp [uniformField])
    have hcl := hc.estimates F c.σA (uniformField F F.top) ⟨hFL, hF⟩ hσ le_rfl hcold
    exact (hcl.coordinates bd hb).1 1 ![b] ![X]
  · have : (fun σ : Fin 1 → ℝ => torusCoordinate a c.ρA bd
        (leftTranslate (bondSpread ![b] ![X] σ) (uniformField F F.top))) = fun _ => 0 :=
      funext fun σ => torusCoordinate_eq_zero_of_not_mem bd hb _
    rw [this]
    exact analyticAt_const
abbrev _root_.YangMills.DeltaSharedProofs.p501622 := @hasDerivAt_torusCoordinate
private theorem torusCoordinate_topAbelianField_zero (hc : c.Admissible a L) (hFL : F.blockSide = L)
    (hF : IsLargeCubicTorus F) (bd : F.Site F.depth × Fin 4) (b : F.Site F.top × Fin 4)
    (X : imaginaryQuaternions) :
    torusCoordinate a c.ρA bd (topAbelianField X b 0) = 0 := by
  rw [topAbelianField_zero]
  by_cases hb : bd ∈ chordBonds (finiteCells F)
  · obtain ⟨⟨-, -, hs0, -, -, -, hC1, -⟩, body⟩ := hc.classical
    by_contra hne
    have hpos : 0 < ‖torusCoordinate a c.ρA bd (uniformField F F.top)‖ := norm_pos_iff.2 hne
    set g := ‖torusCoordinate a c.ρA bd (uniformField F F.top)‖ with hg
    have hCp : 0 < c.C := by linarith
    set s := min c.s₀ (g / (2 * c.C)) with hs
    have hsp : 0 < s := lt_min hs0 (by positivity)
    have hcold : IsSmallCurvature s (uniformField F F.top) :=
      isSmallCurvature_of_near_one (uniformField F F.top) (m := 0) (by linarith)
        (fun x i => by simp [uniformField])
    have h := (body F s (uniformField F F.top) ⟨hFL, hF⟩ hsp (min_le_left _ _) hcold).2.1.1 bd hb
    have h2 : c.C * s ≤ g / 2 := by
      have : s ≤ g / (2 * c.C) := min_le_right _ _
      calc c.C * s ≤ c.C * (g / (2 * c.C)) := mul_le_mul_of_nonneg_left this hCp.le
        _ = g / 2 := by field_simp
    linarith
  · exact torusCoordinate_eq_zero_of_not_mem bd hb _
private theorem tendsto_componentAlong_torusMinimizingField {X : imaginaryQuaternions} (hX : ‖X‖ = 1)
    (hc : c.Admissible a L) (hFL : F.blockSide = L) (hF : IsLargeCubicTorus F)
    (b : F.Site F.top × Fin 4) (x : F.Site F.depth) (i : Fin 4) :
    Tendsto (fun τ => componentAlong X (torusMinimizingField a c.ρA (topAbelianField X b τ) x i : ℍ[ℝ]) / τ)
      (𝓝[>] 0) (𝓝 (minimizerResponse a c.ρA b X x i)) := by
  classical
  set g : ℝ → imaginaryQuaternions := fun τ => torusCoordinate a c.ρA (x, i) (topAbelianField X b τ) with hg
  set Dg : imaginaryQuaternions :=
    bondDeriv (torusCoordinate a c.ρA (x, i)) (uniformField F F.top) ![b] ![X] with hDg
  have hd : HasDerivAt g Dg 0 := hasDerivAt_torusCoordinate hc hFL hF (x, i) b X
  have h0 : g 0 = 0 := torusCoordinate_topAbelianField_zero hc hFL hF (x, i) b X
  have hd' : HasDerivAt (fun τ => (g τ : ℍ[ℝ])) (Dg : ℍ[ℝ]) 0 :=
    (imaginaryQuaternions.subtypeL.hasFDerivAt).comp_hasDerivAt 0 hd
  have hE : HasDerivAt (fun τ => NormedSpace.exp (g τ : ℍ[ℝ])) (Dg : ℍ[ℝ]) 0 :=
    hasDerivAt_exp_comp hd' (by simp [h0])
  have hE1 : NormedSpace.exp (g 0 : ℍ[ℝ]) = 1 := by simp [h0]
  have hresp : minimizerResponse a c.ρA b X x i = componentAlong X (Dg : ℍ[ℝ]) +
      (if IsCrossingBond (x, i) ∧ enclosingCell x = b.1 ∧ i = b.2 then 1 else 0) := rfl
  rw [hresp]
  by_cases hcr : IsCrossingBond (x, i)
  · have hv := hasDerivAt_topAbelianField b X (enclosingCell x) i
    have hv1 : (topAbelianField X b 0 (enclosingCell x) i : ℍ[ℝ]) = 1 := by
      rw [topAbelianField_zero]
      simp [uniformField]
    have hprod := hE.mul hv
    have hval : ∀ τ, (torusMinimizingField a c.ρA (topAbelianField X b τ) x i : ℍ[ℝ]) =
        NormedSpace.exp (g τ : ℍ[ℝ]) * (topAbelianField X b τ (enclosingCell x) i : ℍ[ℝ]) := by
      intro τ
      unfold torusMinimizingField chartedField
      rw [if_pos hcr]
      rfl
    have hs := tendsto_componentAlong_slope hX hprod (by simp only [Pi.mul_apply, hE1, hv1, mul_one])
    simp only [Pi.mul_apply] at hs
    have e : componentAlong X ((Dg : ℍ[ℝ]) * (topAbelianField X b 0 (enclosingCell x) i : ℍ[ℝ]) +
        NormedSpace.exp (g 0 : ℍ[ℝ]) * (topBondIndicator b (enclosingCell x) i • (X : ℍ[ℝ]))) =
        componentAlong X (Dg : ℍ[ℝ]) +
          (if IsCrossingBond (x, i) ∧ enclosingCell x = b.1 ∧ i = b.2 then 1 else 0) := by
      rw [hv1, hE1, mul_one, one_mul, componentAlong_add, componentAlong_smul, componentAlong_self hX,
        mul_one]
      congr 1
      unfold topBondIndicator
      by_cases h : (enclosingCell x, i) = b
      · rw [if_pos h, if_pos ⟨hcr, by rw [← h], by rw [← h]⟩]
      · rw [if_neg h, if_neg fun h' => h (Prod.ext h'.2.1 h'.2.2)]
    rw [e] at hs
    exact hs.congr fun τ => by rw [hval]
  · have hval : ∀ τ, (torusMinimizingField a c.ρA (topAbelianField X b τ) x i : ℍ[ℝ]) =
        NormedSpace.exp (g τ : ℍ[ℝ]) := by
      intro τ
      unfold torusMinimizingField chartedField
      rw [if_neg hcr]
      by_cases ht : IsAxialTreeBond (x, i)
      · rw [if_pos ht]
        have hb : (x, i) ∉ chordBonds (finiteCells F) := by
          unfold chordBonds
          simp [ht]
        have : g τ = 0 := torusCoordinate_eq_zero_of_not_mem (x, i) hb _
        simp [this]
      · rw [if_neg ht]
        rfl
    have hs := tendsto_componentAlong_slope hX hE hE1
    rw [if_neg fun h => hcr h.1, add_zero]
    exact hs.congr fun τ => by rw [hval]
end Parameters
private theorem norm_topAbelianField_sub_one_le {X : imaginaryQuaternions} (hX : ‖X‖ = 1)
    (b : F.Site F.top × Fin 4) {τ : ℝ} (h0 : 0 < τ) (y : F.Site F.top) (i : Fin 4) :
    ‖(topAbelianField X b τ y i : ℍ[ℝ]) - 1‖ ≤ τ := by
  have hw : (((τ * topBondIndicator b y i) • X : imaginaryQuaternions) : ℍ[ℝ]).re = 0 :=
    ((τ * topBondIndicator b y i) • X).2
  refine (norm_exp_sub_one_le hw).trans ?_
  have hXn : ‖(X : ℍ[ℝ])‖ = 1 := hX
  rw [Submodule.coe_smul, norm_smul, hXn, mul_one, Real.norm_eq_abs]
  unfold topBondIndicator
  split_ifs
  · simp [abs_of_pos h0]
  · simp [h0.le]
section NearFlatChains
variable {a : ℝ} {L : ℕ} {c : ColdChainParameters}
private theorem exists_minimizingChain_near_one (hS : SmallMinimizingChainExists)
    (hV : minimalChainExistenceStatement) {X : imaginaryQuaternions} (hX : ‖X‖ = 1) (ha : 0 ≤ a)
    (hL : Odd L) (hc : c.Admissible a L) (hFL : F.blockSide = L) (hF : IsLargeCubicTorus F)
    (b : F.Site F.top × Fin 4) :
    ∃ D τ₀ : ℝ, 0 < D ∧ 0 < τ₀ ∧ ∀ τ, 0 < τ ∧ τ < τ₀ → ∃ Z : F.FieldChain, Z F.top = topAbelianField X b τ ∧
      Z F.depth = torusMinimizingField a c.ρA (topAbelianField X b τ) ∧
      (∀ j, j ≤ F.top → ∀ x i, ‖(Z j x i : ℍ[ℝ]) - 1‖ ≤ D * τ) ∧
      chainAction a (finiteCells F) Z = minimalAction a (finiteCells F) F.top (topAbelianField X b τ) := by
  obtain ⟨C₂, m₂, hC₂, hm₂, hZ⟩ := hS a ha L hL c hc F hFL hF F.depth (by simp [BlockFrame.top])
  obtain ⟨⟨-, -, hs0, -, -, -, hC1, -⟩, body⟩ := hc.classical
  set D₁ : ℝ := 5 * c.C + 1 with hD₁
  have hD₁1 : 1 ≤ D₁ := by rw [hD₁]; linarith
  have hD₁p : 0 < D₁ := by linarith
  refine ⟨C₂ * D₁, min (c.s₀ / 5) (m₂ / D₁), by positivity, lt_min (by positivity) (by positivity), ?_⟩
  rintro τ ⟨h0, h1⟩
  have h1a : τ < c.s₀ / 5 := lt_of_lt_of_le h1 (min_le_left _ _)
  have h1b : D₁ * τ ≤ m₂ := by
    have := (lt_of_lt_of_le h1 (min_le_right _ _)).le
    rwa [le_div_iff₀ hD₁p, mul_comm] at this
  set V := topAbelianField X b τ with hVdef
  have hVn : ∀ y i, ‖(V y i : ℍ[ℝ]) - 1‖ ≤ τ := fun y i => norm_topAbelianField_sub_one_le hX b h0 y i
  have hcold : IsSmallCurvature (5 * τ) V := isSmallCurvature_of_near_one V (by linarith) hVn
  obtain ⟨hleast, hsmall, -, -⟩ := body F (5 * τ) V ⟨hFL, hF⟩ (by linarith) (by linarith) hcold
  set w := minimizingCoordinates a (finiteCells F) V c.ρA with hw
  have hCp : 0 < c.C := by linarith
  have hwb : ∀ x i, ‖w x i‖ ≤ c.C * (5 * τ) := by
    intro x i
    by_cases hb : (x, i) ∈ chordBonds (finiteCells F)
    · exact hsmall.1 (x, i) hb
    · rw [hleast.1 (x, i) hb, norm_zero]
      positivity
  have hWn : ∀ x i, ‖(chartedField w V x i : ℍ[ℝ]) - 1‖ ≤ D₁ * τ := by
    intro x i
    have := norm_chartedField_sub_one_le w V (r := c.C * (5 * τ)) (by positivity) h0.le hwb hVn x i
    rw [hD₁]
    linarith
  obtain ⟨Z, hZt, hZb, hZtot⟩ := hZ (D₁ * τ) (by positivity) h1b (chartedField w V) hWn
  have hup : ∀ j, j ≤ F.depth → Function.update Z F.top V j = Z j := fun j hj =>
    Function.update_of_ne (by simp only [BlockFrame.top]; omega) _ _
  refine ⟨Function.update Z F.top V, by simp, (hup _ le_rfl).trans hZt, ?_, ?_⟩
  · intro j hj x i
    by_cases h : j = F.top
    · subst h
      simp only [Function.update_self]
      refine (hVn x i).trans ?_
      have hCD : 1 ≤ C₂ * D₁ := by nlinarith
      exact le_mul_of_one_le_left h0.le hCD
    · rw [hup j (by simp only [BlockFrame.top] at hj h; omega)]
      have := hZb j (by simp only [BlockFrame.top] at hj h; omega) x i
      rw [mul_assoc]
      exact this
  · have hE : blockEnergy a (finiteCells F) F.depth (chartedField w V) V =
        minimalAction a (finiteCells F) F.top V := by
      obtain ⟨-, -, h3, -⟩ := hV F a (finiteCells F) ha
      obtain ⟨W0, e0, m0⟩ := h3 F.depth V
      have l1 := hleast.2.2 W0
      have l2 := m0 (chartedField w V)
      exact le_antisymm (by rw [show minimalAction a (finiteCells F) F.top V = _ from e0.symm]; exact l1)
        (by rw [show minimalAction a (finiteCells F) F.top V = _ from e0.symm]; exact l2)
    rw [← hE]
    unfold chainAction blockEnergy
    show _ + a * ∑ j ∈ Finset.range (F.depth + 1), _ = _
    rw [Finset.sum_range_succ, hup 0 (by omega), hup F.depth le_rfl, hZt]
    have e1 : Function.update Z F.top V (F.depth + 1) = V := Function.update_self _ _ _
    rw [e1]
    have e : ∑ j ∈ Finset.range F.depth, ∑ b ∈ innerBonds (finiteCells F) (j + 1),
        blockFit (Function.update Z F.top V j) (Function.update Z F.top V (j + 1)) b =
        ∑ j ∈ Finset.range F.depth, ∑ b ∈ innerBonds (finiteCells F) (j + 1), blockFit (Z j) (Z (j + 1)) b := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have := Finset.mem_range.1 hj
      rw [hup j (by omega), hup (j + 1) (by omega)]
    rw [e, ← hZtot]
    ring
end NearFlatChains
private theorem tendsto_cos_mul (ψ : ℝ) : Tendsto (fun τ : ℝ => Real.cos (τ * ψ)) (𝓝[>] 0) (𝓝 1) := by
  have hc : Continuous fun τ : ℝ => Real.cos (τ * ψ) := by fun_prop
  have h := hc.tendsto 0
  simp only [zero_mul, Real.cos_zero] at h
  exact h.mono_left nhdsWithin_le_nhds
private theorem tendsto_sin_mul_div (ψ : ℝ) :
    Tendsto (fun τ : ℝ => Real.sin (τ * ψ) / τ) (𝓝[>] 0) (𝓝 ψ) := by
  have h1 : HasDerivAt (fun τ : ℝ => τ * ψ) ψ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const ψ
  have h2 : HasDerivAt (fun τ : ℝ => Real.sin (τ * ψ)) ψ 0 := by
    simpa using h1.sin
  have h := hasDerivAt_iff_tendsto_slope_zero.1 h2
  have h3 : Tendsto (fun t : ℝ => t⁻¹ • (Real.sin ((0 + t) * ψ) - Real.sin (0 * ψ))) (𝓝[>] 0) (𝓝 ψ) :=
    h.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  refine h3.congr fun τ => ?_
  simp [div_eq_inv_mul]
private theorem tendsto_cosineAverage_sineAverage (hL : Odd F.blockSide) {j : ℕ} (U : LevelForm F j) (u : ℝ)
    (c : F.Site (j + 1) × Fin 4) :
    Tendsto (fun τ : ℝ => cosineAverage (fun x i => τ * U x i) (τ * u) c) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun τ : ℝ => sineAverage (fun x i => τ * U x i) (τ * u) c / τ) (𝓝[>] 0)
        (𝓝 (ColdStepAtMirrorFrames.contourAverage U c.1 c.2 - u)) := by
  have hL0 : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hL.pos.ne'
  have hcard : (1 / (24 * (F.blockSide : ℝ) ^ 4)) *
      ∑ _h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ) = 1 := by
    simp only [Finset.sum_const, card_perm_fin_four, card_centredCube hL, nsmul_eq_mul]
    push_cast
    field_simp
  have earg : ∀ (τ : ℝ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)),
      pathSum (fun x i => τ * U x i) (refineSite c.1) (bondContour F.blockSide h π c.2) - τ * u =
        τ * (pathSum U (refineSite c.1) (bondContour F.blockSide h π c.2) - u) := by
    intro τ h π
    rw [pathSum_const_mul]
    ring
  constructor
  · have h1 : Tendsto (fun τ : ℝ => (1 / (24 * (F.blockSide : ℝ) ^ 4)) *
        ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        Real.cos (τ * (pathSum U (refineSite c.1) (bondContour F.blockSide h π c.2) - u))) (𝓝[>] 0)
        (𝓝 ((1 / (24 * (F.blockSide : ℝ) ^ 4)) *
          ∑ _h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ))) :=
      Tendsto.const_mul _ (tendsto_finset_sum _ fun h _ => tendsto_finset_sum _ fun π _ => tendsto_cos_mul _)
    rw [hcard] at h1
    refine h1.congr fun τ => ?_
    unfold cosineAverage
    simp only [earg]
  · have h1 : Tendsto (fun τ : ℝ => (1 / (24 * (F.blockSide : ℝ) ^ 4)) *
        ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        (Real.sin (τ * (pathSum U (refineSite c.1) (bondContour F.blockSide h π c.2) - u)) / τ)) (𝓝[>] 0)
        (𝓝 ((1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
          (pathSum U (refineSite c.1) (bondContour F.blockSide h π c.2) - u))) :=
      Tendsto.const_mul _ (tendsto_finset_sum _ fun h _ => tendsto_finset_sum _ fun π _ =>
        tendsto_sin_mul_div _)
    have e : (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        (pathSum U (refineSite c.1) (bondContour F.blockSide h π c.2) - u) =
        ColdStepAtMirrorFrames.contourAverage U c.1 c.2 - u := by
      simp only [Finset.sum_sub_distrib, mul_sub]
      congr 1
      simp only [Finset.sum_const, card_perm_fin_four, card_centredCube hL, nsmul_eq_mul]
      push_cast
      field_simp
    rw [e] at h1
    refine h1.congr fun τ => ?_
    unfold sineAverage
    simp only [earg, mul_div_assoc, Finset.sum_div]
private theorem exists_upper_bound_minimalAction (hV : minimalChainExistenceStatement)
    {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {a : ℝ} (ha : 0 ≤ a) (hL : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (b : F.Site F.top × Fin 4) (U : FormChain F)
    (htop : U F.top = topBondIndicator b) :
    ∃ G : ℝ → ℝ, Tendsto G (𝓝[>] 0) (𝓝 (contourChainEnergy a U)) ∧
      ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        2 * minimalAction a (finiteCells F) F.top (topAbelianField X b τ) / τ ^ 2 ≤ G τ := by
  set Am : ℝ → (j : ℕ) → F.Site (j + 1) → Fin 4 → ℝ := fun τ j y i =>
    cosineAverage (fun x i => τ * U j x i) (τ * U (j + 1) y i) (y, i) with hAm
  set Sm : ℝ → (j : ℕ) → F.Site (j + 1) → Fin 4 → ℝ := fun τ j y i =>
    sineAverage (fun x i => τ * U j x i) (τ * U (j + 1) y i) (y, i) with hSm
  refine ⟨fun τ => (∑ x ∈ sitesOfCells (finiteCells F) 0, ∑ e ∈ orientedPlanes,
      plaquetteCurl (U 0) x e.1 e.2 ^ 2) +
    a * ∑ j ∈ Finset.range F.top, ∑ y ∈ sitesOfCells (finiteCells F) (j + 1), ∑ i : Fin 4,
      (Sm τ j y i / τ) ^ 2 / Am τ j y i, ?_, ?_⟩
  · refine Tendsto.add tendsto_const_nhds (Tendsto.const_mul _ (tendsto_finset_sum _ fun j _ =>
      tendsto_finset_sum _ fun y _ => tendsto_finset_sum _ fun i _ => ?_))
    obtain ⟨h1, h2⟩ := tendsto_cosineAverage_sineAverage hL (U j) (U (j + 1) y i) (y, i)
    have h3 := (h2.pow 2).div h1 one_ne_zero
    rw [div_one] at h3
    exact h3
  · have hpos : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ j ∈ Finset.range F.top, ∀ y ∈ sitesOfCells (finiteCells F) (j + 1),
        ∀ i ∈ (Finset.univ : Finset (Fin 4)), 0 < Am τ j y i := by
      refine (Filter.eventually_all_finset _).2 fun j _ => (Filter.eventually_all_finset _).2 fun y _ =>
        (Filter.eventually_all_finset _).2 fun i _ => ?_
      exact (tendsto_cosineAverage_sineAverage hL (U j) (U (j + 1) y i) (y, i)).1.eventually
        (lt_mem_nhds one_pos)
    filter_upwards [hpos, self_mem_nhdsWithin] with τ hA hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    set T : F.FieldChain := fun j => abelianField X fun x i => τ * U j x i with hT
    have hTtop : T F.top = topAbelianField X b τ := by
      simp only [hT, topAbelianField, htop]
    have hle : minimalAction a (finiteCells F) F.top (topAbelianField X b τ) ≤
        chainAction a (finiteCells F) T := by
      obtain ⟨-, -, -, h4⟩ := hV F a (finiteCells F) ha
      obtain ⟨Xm, hm, he⟩ := h4 (topAbelianField X b τ)
      rw [← he]
      exact hm.2 T hTtop
    have hact : wilsonAction (finiteCells F) (T 0) ≤
        τ ^ 2 / 2 * ∑ x ∈ sitesOfCells (finiteCells F) 0, ∑ e ∈ orientedPlanes,
          plaquetteCurl (U 0) x e.1 e.2 ^ 2 := by
      unfold wilsonAction
      rw [sum_innerPlaquettes_finiteCells hL hs (Nat.zero_le _)]
      simp only [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun e _ => ?_
      have := plaquette_abelianField_le hX (fun x i => τ * U 0 x i) x e.1 e.2
      rw [plaquetteCurl_const_mul] at this
      refine this.trans (le_of_eq ?_)
      ring
    have hfit : ∀ j ∈ Finset.range F.top, ∑ c ∈ innerBonds (finiteCells F) (j + 1),
        blockFit (T j) (T (j + 1)) c ≤
        τ ^ 2 / 2 * ∑ y ∈ sitesOfCells (finiteCells F) (j + 1), ∑ i : Fin 4,
          (Sm τ j y i / τ) ^ 2 / Am τ j y i := by
      intro j hj
      rw [sum_innerBonds_finiteCells hL hs (Finset.mem_range.1 hj)]
      simp only [Finset.mul_sum]
      refine Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun i hi => ?_
      have hA' := hA j hj y hy i hi
      have := blockFit_abelianField_le hX (fun x i => τ * U j x i) (fun x i => τ * U (j + 1) x i) (y, i) hA'
      refine this.trans (le_of_eq ?_)
      simp only [hAm, hSm] at hA' ⊢
      field_simp
    have htot : chainAction a (finiteCells F) T ≤ τ ^ 2 / 2 *
        ((∑ x ∈ sitesOfCells (finiteCells F) 0, ∑ e ∈ orientedPlanes, plaquetteCurl (U 0) x e.1 e.2 ^ 2) +
          a * ∑ j ∈ Finset.range F.top, ∑ y ∈ sitesOfCells (finiteCells F) (j + 1), ∑ i : Fin 4,
            (Sm τ j y i / τ) ^ 2 / Am τ j y i) := by
      unfold chainAction
      have h2 := Finset.sum_le_sum hfit
      rw [← Finset.mul_sum] at h2
      have h3 := mul_le_mul_of_nonneg_left h2 ha
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
private def componentLowerSum (X : imaginaryQuaternions) (a : ℝ) (Z : F.FieldChain) (τ : ℝ) : ℝ :=
  (∑ x ∈ sitesOfCells (finiteCells F) 0, ∑ e ∈ orientedPlanes,
      (componentAlong X (plaquetteHolonomy (Z 0) (x, e.1, e.2) : ℍ[ℝ]) / τ) ^ 2) +
    a * ∑ j ∈ Finset.range F.top, ∑ y ∈ sitesOfCells (finiteCells F) (j + 1), ∑ i : Fin 4,
      (componentAlong X (BlockAverages.contourAverage (Z j) (y, i) *
        (((Z (j + 1) y i)⁻¹ : UnitQuaternion) : ℍ[ℝ])) / τ) ^ 2
private theorem mul_add_mul_le_of_le {p A B P Q a : ℝ} (hp : 0 ≤ p) (ha : 0 ≤ a) (h1 : A ≤ P)
    (h2 : B ≤ Q) : p * A + a * (p * B) ≤ p * (P + a * Q) := by
  nlinarith [mul_le_mul_of_nonneg_left h1 hp,
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 ha) hp]
private theorem componentLowerSum_le {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {a : ℝ} (ha : 0 ≤ a)
    (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (Z : F.FieldChain) {τ : ℝ} (h0 : 0 < τ) :
    componentLowerSum X a Z τ ≤ 2 * chainAction a (finiteCells F) Z / τ ^ 2 := by
  have t : ∀ u : ℝ, (u / τ) ^ 2 = (2 / τ ^ 2) * (u ^ 2 / 2) := by
    intro u
    field_simp
  have e : ∀ w : ℝ, 2 * w / τ ^ 2 = (2 / τ ^ 2) * w := fun w => by ring
  unfold componentLowerSum chainAction
  simp only [t, ← Finset.mul_sum]
  rw [e]
  refine mul_add_mul_le_of_le (by positivity) ha ?_ ?_
  · unfold wilsonAction
    rw [sum_innerPlaquettes_finiteCells hL hs (Nat.zero_le _)]
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun e _ =>
      componentAlong_sq_div_two_le_plaquette hX _ _
  · refine Finset.sum_le_sum fun j hj => ?_
    rw [sum_innerBonds_finiteCells hL hs (Finset.mem_range.1 hj)]
    exact Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun i _ =>
      componentAlong_sq_div_two_le_blockFit hX hL _ _ (y, i)
private theorem tendsto_pathSum {l : Filter ℝ} {j : ℕ} {f : ℝ → LevelForm F j} {B : LevelForm F j}
    (h : ∀ x i, Tendsto (fun t => f t x i) l (𝓝 (B x i))) (x : F.Site j) (p : List PathStep) :
    Tendsto (fun t => pathSum (f t) x p) l (𝓝 (pathSum B x p)) := by
  induction p generalizing x with
  | nil =>
    simp only [pathSum]
    exact tendsto_const_nhds
  | cons st r ih =>
    simp only [pathSum]
    refine Tendsto.add ?_ (ih _)
    by_cases hb : st.2 = true
    · simp only [hb, if_true]
      exact h _ _
    · simp only [hb, Bool.false_eq_true, if_false]
      exact (h _ _).neg
private theorem tendsto_of_abs_sub_le_mul {l : Filter ℝ} (hl : l ≤ 𝓝[>] 0) {u v : ℝ → ℝ} {A K τ₀ : ℝ}
    (hτ₀ : 0 < τ₀) (hu : Tendsto u l (𝓝 A)) (hc : ∀ τ, 0 < τ → τ < τ₀ → |v τ - u τ| ≤ K * τ) :
    Tendsto v l (𝓝 A) := by
  have hz : Tendsto (fun τ : ℝ => K * τ) l (𝓝 0) := by
    have h : Tendsto (fun τ : ℝ => τ) l (𝓝 0) := tendsto_id.mono_right (hl.trans nhdsWithin_le_nhds)
    simpa using h.const_mul K
  have hd : Tendsto (fun τ => v τ - u τ) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [hl (Ioo_mem_nhdsGT hτ₀)] with τ hτ
    simpa [Real.norm_eq_abs] using hc τ hτ.1 hτ.2
  have h := hd.add hu
  rw [zero_add] at h
  exact h.congr fun τ => by ring
private theorem contourAverage_const_mul {j : ℕ} (r : ℝ) (B : LevelForm F j) (y : F.Site (j + 1))
    (i : Fin 4) :
    ColdStepAtMirrorFrames.contourAverage (fun x i => r * B x i) y i =
      r * ColdStepAtMirrorFrames.contourAverage B y i := by
  unfold ColdStepAtMirrorFrames.contourAverage
  simp only [pathSum_const_mul, ← Finset.mul_sum]
  ring
theorem axialResponseOfMinimizers_of_smallMinimizingChainExists (hS : SmallMinimizingChainExists)
    (hV : minimalChainExistenceStatement) : AxialResponseOfMinimizers := by
  intro a ha L hL c hc F b X hFL hF hX
  have ha0 : 0 ≤ a := by linarith
  have hLF : Odd F.blockSide := hFL.symm ▸ hL
  have hs : ∀ i, 0 < F.extent i := by
    obtain ⟨n, hn, h⟩ := hF
    intro i
    rw [h i]
    omega
  obtain ⟨D, τ₀, hD, hτ₀, hch⟩ := exists_minimizingChain_near_one hS hV hX ha0 hL hc hFL hF b
  haveI : Nonempty F.FieldChain := ⟨fun _ _ _ => 1⟩
  choose! Z hZ1 hZ2 hZ3 hZ4 using hch
  set 𝒰 : Ultrafilter ℝ := Ultrafilter.of (𝓝[>] (0 : ℝ)) with h𝒰
  have hle : (𝒰 : Filter ℝ) ≤ 𝓝[>] 0 := Ultrafilter.of_le _
  have hIoo : ∀ᶠ τ in (𝒰 : Filter ℝ), 0 < τ ∧ τ < τ₀ := hle (Ioo_mem_nhdsGT hτ₀)
  set f : ℝ → (j : ℕ) → LevelForm F j := fun τ j x i => τ⁻¹ * componentForm X (Z τ j) x i with hf
  have hbd : ∀ τ, 0 < τ ∧ τ < τ₀ → ∀ j, j ≤ F.top → ∀ x i, |f τ j x i| ≤ D := by
    intro τ hτ j hj x i
    have h1 := hZ3 τ hτ j hj x i
    have h2 : |componentForm X (Z τ j) x i| ≤ D * τ := by
      have e : componentForm X (Z τ j) x i = componentAlong X ((Z τ j x i : ℍ[ℝ]) - 1) := by
        rw [componentAlong_sub, componentAlong_one, sub_zero]
        rfl
      rw [e]
      exact (abs_componentAlong_le hX _).trans h1
    simp only [hf]
    rw [abs_mul, abs_of_pos (inv_pos.2 hτ.1)]
    calc τ⁻¹ * _ ≤ τ⁻¹ * (D * τ) := mul_le_mul_of_nonneg_left h2 (inv_pos.2 hτ.1).le
      _ = D := by
        have := hτ.1.ne'
        field_simp
  have hlim : ∀ (j : ℕ) (x : F.Site j) (i : Fin 4), ∃ l : ℝ, j ≤ F.top →
      Tendsto (fun τ => f τ j x i) (𝒰 : Filter ℝ) (𝓝 l) := by
    intro j x i
    by_cases hj : j ≤ F.top
    · obtain ⟨l, -, hl⟩ := isCompact_Icc.ultrafilter_le_nhds (𝒰.map fun τ => f τ j x i) (by
        rw [le_principal_iff]
        show _ ∈ Filter.map (fun τ => f τ j x i) (𝒰 : Filter ℝ)
        rw [Filter.mem_map]
        filter_upwards [hIoo] with τ hτ
        exact abs_le.1 (hbd τ hτ j hj x i) : _ ≤ 𝓟 (Set.Icc (-D) D))
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose β hβ using hlim
  have htop : β F.top = topBondIndicator b := by
    funext y i
    have h1 := hβ F.top y i le_rfl
    have h2 := (tendsto_componentAlong_slope hX (hasDerivAt_topAbelianField b X y i)
      (by rw [topAbelianField_zero]; simp [uniformField])).mono_left hle
    have h3 : Tendsto (fun τ => f τ F.top y i) (𝒰 : Filter ℝ)
        (𝓝 (componentAlong X (topBondIndicator b y i • (X : ℍ[ℝ])))) := by
      refine h2.congr' ?_
      filter_upwards [hIoo] with τ hτ
      simp only [hf, componentForm]
      rw [hZ1 τ hτ, div_eq_inv_mul]
    rw [tendsto_nhds_unique h1 h3, componentAlong_smul, componentAlong_self hX, mul_one]
  have hmem : β F.depth = minimizerResponse a c.ρA b X := by
    funext x i
    have h1 := hβ F.depth x i (by simp [BlockFrame.top])
    have h2 := (tendsto_componentAlong_torusMinimizingField hX hc hFL hF b x i).mono_left hle
    have h3 : Tendsto (fun τ => f τ F.depth x i) (𝒰 : Filter ℝ)
        (𝓝 (minimizerResponse a c.ρA b X x i)) := by
      refine h2.congr' ?_
      filter_upwards [hIoo] with τ hτ
      simp only [hf, componentForm]
      rw [hZ2 τ hτ, div_eq_inv_mul]
    exact tendsto_nhds_unique h1 h3
  have hΞ : Tendsto (fun τ => componentLowerSum X a (Z τ) τ) (𝒰 : Filter ℝ)
      (𝓝 (contourChainEnergy a β)) := by
    unfold componentLowerSum contourChainEnergy
    refine Tendsto.add (tendsto_finset_sum _ fun x _ => tendsto_finset_sum _ fun e _ => ?_)
      (Tendsto.const_mul _ (tendsto_finset_sum _ fun j hj => tendsto_finset_sum _ fun y _ =>
        tendsto_finset_sum _ fun i _ => ?_))
    · apply Tendsto.pow
      have hb0 := fun x i => hβ 0 x i (Nat.zero_le _)
      have hu : Tendsto (fun τ => plaquetteCurl (f τ 0) x e.1 e.2) (𝒰 : Filter ℝ)
          (𝓝 (plaquetteCurl (β 0) x e.1 e.2)) := by
        unfold plaquetteCurl
        exact (((hb0 _ _).add (hb0 _ _)).sub (hb0 _ _)).sub (hb0 _ _)
      refine tendsto_of_abs_sub_le_mul hle hτ₀ hu (K := 16 * D ^ 2) fun τ h0 h1 => ?_
      have hp := abs_componentAlong_plaquetteHolonomy_sub_curl_le hX (Z τ 0) (ε := D * τ) (by positivity)
        (hZ3 τ ⟨h0, h1⟩ 0 (Nat.zero_le _)) x e.1 e.2
      have e1 : plaquetteCurl (f τ 0) x e.1 e.2 = τ⁻¹ * plaquetteCurl (componentForm X (Z τ 0)) x e.1 e.2 :=
        plaquetteCurl_const_mul _ _ _ _ _
      rw [e1, div_eq_inv_mul, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 h0)]
      calc τ⁻¹ * _ ≤ τ⁻¹ * (16 * (D * τ) ^ 2) := mul_le_mul_of_nonneg_left hp (inv_pos.2 h0).le
        _ = 16 * D ^ 2 * τ := by
          have := h0.ne'
          field_simp
    · apply Tendsto.pow
      have hj' : j < F.top := Finset.mem_range.1 hj
      have hu : Tendsto (fun τ => ColdStepAtMirrorFrames.contourAverage (f τ j) y i - f τ (j + 1) y i)
          (𝒰 : Filter ℝ) (𝓝 (contourChainMisfit β j y i)) := by
        refine Tendsto.sub ?_ (hβ (j + 1) y i hj')
        exact Tendsto.const_mul _ (tendsto_finset_sum _ fun h _ => tendsto_finset_sum _ fun π _ =>
          tendsto_pathSum (fun x i => hβ j x i hj'.le) _ _)
      refine tendsto_of_abs_sub_le_mul hle hτ₀ hu
        (K := (25 * (F.blockSide : ℝ) ^ 2 + 5 * (F.blockSide : ℝ)) * D ^ 2) fun τ h0 h1 => ?_
      have hp := abs_componentAlong_contourAverage_sub_le hX hLF (Z τ j) (Z τ (j + 1)) (ε := D * τ)
        (by positivity) (hZ3 τ ⟨h0, h1⟩ j hj'.le) (hZ3 τ ⟨h0, h1⟩ (j + 1) hj') (y, i)
      have e1 : ColdStepAtMirrorFrames.contourAverage (f τ j) y i =
          τ⁻¹ * ColdStepAtMirrorFrames.contourAverage (componentForm X (Z τ j)) y i :=
        contourAverage_const_mul _ _ _ _
      have e2 : f τ (j + 1) y i = τ⁻¹ * componentForm X (Z τ (j + 1)) y i := rfl
      rw [e1, e2, div_eq_inv_mul, ← mul_sub, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 h0)]
      calc τ⁻¹ * _ ≤ τ⁻¹ * ((25 * (F.blockSide : ℝ) ^ 2 + 5 * (F.blockSide : ℝ)) * (D * τ) ^ 2) :=
            mul_le_mul_of_nonneg_left hp (inv_pos.2 h0).le
        _ = (25 * (F.blockSide : ℝ) ^ 2 + 5 * (F.blockSide : ℝ)) * D ^ 2 * τ := by
          have := h0.ne'
          field_simp
  have hleast : ∀ U : FormChain F, U F.top = topBondIndicator b →
      contourChainEnergy a β ≤ chainEnergyPolar a U U := by
    intro U hU
    obtain ⟨Uc, h1, h2, h3⟩ := exists_contourChain_of_lineChain hLF U
    obtain ⟨G, hG1, hG2⟩ := exists_upper_bound_minimalAction hV hX ha0 hLF hs b Uc (h1.trans hU)
    rw [← contourChainEnergy_eq a Uc U (fun x μ ν => h2 0 x μ ν) h3]
    refine le_of_tendsto_of_tendsto hΞ (hG1.mono_left hle) ?_
    filter_upwards [hIoo, hle hG2] with τ hτ hg
    refine (componentLowerSum_le hX ha0 hLF hs (Z τ) hτ.1).trans ?_
    rw [hZ4 τ hτ]
    exact hg
  obtain ⟨B, hB, hcurl, hmean⟩ := exists_flatChain_of_isLeast_contourEnergy a hLF b β htop hleast
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · rintro ⟨x, i⟩ ht
    have hb : (x, i) ∉ chordBonds (finiteCells F) := by
      unfold chordBonds
      simp [ht]
    have hz : bondDeriv (torusCoordinate a c.ρA (x, i)) (uniformField F F.top) ![b] ![X] = 0 := by
      have h1 := hasDerivAt_torusCoordinate hc hFL hF (x, i) b X
      have h2 : HasDerivAt (fun τ => torusCoordinate a c.ρA (x, i) (topAbelianField X b τ))
          (0 : imaginaryQuaternions) 0 := by
        have : (fun τ => torusCoordinate a c.ρA (x, i) (topAbelianField X b τ)) = fun _ => 0 :=
          funext fun τ => torusCoordinate_eq_zero_of_not_mem _ hb _
        rw [this]
        exact hasDerivAt_const _ _
      exact h1.unique h2
    show minimizerResponse a c.ρA b X x i = 0
    unfold minimizerResponse
    rw [hz, if_neg fun h => ht.1 h.1]
    simp
  · intro x e _
    rw [← hmem]
    exact (hcurl x e.1 e.2).symm
  · intro y i
    have := hmean y i
    rw [hmem] at this
    exact this
end YangMills.Construction.ColdStepAtMirrorFrames
end
