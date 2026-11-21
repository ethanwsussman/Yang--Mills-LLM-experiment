import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfASlopeAtATop
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfExpansionsAtATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsWithOneUnboundedSum
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.Estimates YangMills.Construction.LawAtTop YangMills.Construction.ConvexObservables YangMills.Construction.SmoothSlices
namespace YangMills.Construction.Cumulants
variable {F : BlockFrame}
namespace SlopeCumulants
theorem norm_le_of_norm_lt {r : ℝ} {η : StepVariable (finiteCells F)} (h : ∀ b, ‖η b‖ < r) : ∀ b, ‖η b‖ ≤ r :=
  fun b => (h b).le
theorem fieldDeriv_contDiffOn (hS : IteratedFDerivSlices) {r : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hG : JointlyContDiffOnBalls r V G) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 2) :
    ContDiffOn ℝ 1 (fieldDeriv G V c X) {η | ∀ b, ‖η b‖ < r} := by apply _root_.YangMills.Construction.Cumulants.ExpansionBound.fieldDeriv_contDiffOn <;> assumption
theorem fieldDeriv_bounded (hT : UniformDerivBoundNearCompact) {r : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hG : JointlyContDiffOnBalls r V G) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3) :
    ∃ D : ℝ, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ r) → |fieldDeriv G V c X η| ≤ D := by apply _root_.YangMills.Construction.Cumulants.ExpansionBound.fieldDeriv_bounded <;> assumption
theorem bondSpan_le_cellsDiameter_add_sum {M : ℕ} (z : Fin M → F.Cell) (i₀ : Fin M) (j : Fin M → ℕ)
    (cc : ∀ i, Fin (j i) → F.Site F.top × Fin 4) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (hcov : ∀ l, ∃ i a, cc i a = c l) :
    bondSpan (z i₀) c ≤ cellsDiameter z + ∑ i, bondSpan (z i) (cc i) := by apply _root_.YangMills.Construction.Cumulants.ExpansionBound.bondSpan_le_cellsDiameter_add_sum <;> assumption
theorem integrable_mul_ballDensity {ι : Type} [Fintype ι] [DecidableEq ι] {r x κ h : ℝ} {p : ℝ → ℝ}
    {Φ : BondField ι → ℝ} {Cq : ℕ → ℝ} {dZ : ι → ℝ} {H : BondField ι → ℝ}
    (_hr : 0 < r) (hI : Integrable (ballDensity (cutoffFactor r p) Φ))
    (hc : ContinuousOn H {η | ∀ b, ‖η b‖ < r})
    (hs : HasLocalSize r (cutoffFactor r p) Φ Cq x κ h dZ H) :
    Integrable fun η => H η * ballDensity (cutoffFactor r p) Φ η := by
  obtain ⟨-, H₀, hm⟩ := hs
  have h1 := (hm 1 le_rfl).1.1
  set U : Set (BondField ι) := {η | ∀ b, ‖η b‖ < r} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {η : BondField ι | ‖η b‖ < r} := by
      ext η
      simp [hU]
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_apply b).norm continuous_const
  have hoff : ∀ η, η ∉ U → ballDensity (cutoffFactor r p) Φ η = 0 := by
    intro η hη
    have h2 : ¬ ∀ b, ‖η b‖ < r := hη
    push Not at h2
    obtain ⟨b, hb⟩ := h2
    unfold ballDensity radialWeightProd
    rw [Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mpr hb]), zero_mul]
  have hm1 : AEStronglyMeasurable (U.indicator fun η => H η - H₀) volume :=
    (aestronglyMeasurable_indicator_iff hUo.measurableSet).mpr
      ((hc.sub continuousOn_const).aestronglyMeasurable hUo.measurableSet)
  have hmm : AEStronglyMeasurable (fun η => (H η - H₀) * ballDensity (cutoffFactor r p) Φ η) volume := by
    refine (hm1.mul hI.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun η => ?_)
    by_cases hη : η ∈ U
    · simp [Set.indicator_of_mem hη]
    · simp [Set.indicator_of_notMem hη, hoff η hη]
  have h2 : Integrable fun η => (H η - H₀) * ballDensity (cutoffFactor r p) Φ η := by
    refine h1.mono hmm (Filter.Eventually.of_forall fun η => ?_)
    simp only [pow_one, Real.norm_eq_abs, abs_mul, abs_abs, le_refl]
  have h3 := h2.add (hI.const_mul H₀)
  refine h3.congr (Filter.Eventually.of_forall fun η => ?_)
  simp only [Pi.add_apply]
  ring
end SlopeCumulants
open SlopeCumulants in
theorem slopeCumulantDecay_holds (hS : IteratedFDerivSlices) (hT : UniformDerivBoundNearCompact)
    (hC : cumulantDecayBoundOneUnbounded) : slopeCumulantDecay := by
  classical
  intro N N' κ lam M hκ hlam hM2 hM9
  obtain ⟨B, hB0, hB⟩ := hC N N' κ lam M hκ hlam hM2 hM9
  refine ⟨B, hB0, ?_⟩
  intro F s a ρA x m ρ α β p Cq φ V hL hα Y i₀ j cc XX only k c H hSl hX hj hcov
  obtain ⟨Ψ, K, hag, hconv, hslope⟩ := hL.convex
  have third : ∀ {n : ℕ} (Z : ↥(finiteCells F)) (c' : Fin n → F.Site F.top × Fin 4)
      (X' : Fin n → imaginaryQuaternions), n ≤ 3 →
      ContDiffOn ℝ 1 (fieldDeriv (interpolatedExponentTerm s a ρA x m φ (Sum.inl Z)) V c' X')
        {η | ∀ b, ‖η b‖ < ρ} := by
    intro n Z c' X' hn
    by_cases h2 : n ≤ 2
    · exact fieldDeriv_contDiffOn hS (hL.smooth_term _) c' X' h2
    · have h3 : n = 3 := by omega
      subst h3
      exact hL.third_term Z c' X'
  have hP0 : ∀ q, cumulantSlotTerms Y i₀ only i₀ q → termCell q = Y := by
    rintro q (⟨-, h, -⟩ | ⟨h, -⟩)
    · exact h
    · exact absurd rfl h
  have hP1 : ∀ i q, i ≠ i₀ → cumulantSlotTerms Y i₀ only i q → only i →
      ∃ Z : ↥(finiteCells F), q = Sum.inl Z := by
    rintro i q hi (⟨h, -⟩ | ⟨-, h⟩)
    · exact absurd h hi
    · exact h
  let O : Fin M → TermPlace F → StepVariable (finiteCells F) → ℝ := fun i q =>
    if i = i₀ then H else fieldDeriv (interpolatedExponentTerm s a ρA x m φ q) V (cc i) (XX i)
  have hO₀ : ∀ q, O i₀ q = H := fun q => by simp [O]
  have hO : ∀ i q, i ≠ i₀ → O i q = fieldDeriv (interpolatedExponentTerm s a ρA x m φ q) V (cc i) (XX i) :=
    fun i q hi => by simp [O, hi]
  have key := hB F ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1) ρ x p Ψ
    (fun η => interpolatedExponentOfTerms s a ρA x m φ η V) K (TermPlace F) termCell
    (cumulantSlotTerms Y i₀ only) O
    (fun i q => if i = i₀ then (bondSpan Y (cc i₀) : ℝ) else termDecayWeight (cc i) q)
    (fun i => if i = i₀ then α else β) Cq (2 ^ 4 * κ) (bondSpan Y c) Y i₀ hL.ρ_pos hL.x_pos hL.cutoff
    hL.card_bonds_le hconv hslope hag hL.integrable hL.Cq_nonneg ?_ ?_ ?_ ?_ hL.card_places_le hP0
    ?_ ?_ ?_ ?_ ?_
  · have e1 : (fun (i : Fin M) η => ∑ q ∈ Finset.univ.filter (cumulantSlotTerms Y i₀ only i), O i q η) =
        fun i η => if i = i₀ then H η else ∑ q ∈ Finset.univ.filter (cumulantSlotTerms Y i₀ only i),
          fieldDeriv (interpolatedExponentTerm s a ρA x m φ q) V (cc i) (XX i) η := by
      funext i η
      by_cases hi : i = i₀
      · subst hi
        simp only [if_true, hO₀]
        have hf : Finset.univ.filter (cumulantSlotTerms Y i only i) =
            {(Sum.inl ⟨Y, hL.mem_cells Y⟩ : TermPlace F)} := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro (⟨-, h, Z, rfl⟩ | ⟨h, -⟩)
            · have : Z.1 = Y := h
              congr 1
              exact Subtype.ext this
            · exact absurd rfl h
          · rintro rfl
            exact Or.inl ⟨rfl, rfl, _, rfl⟩
        rw [hf, Finset.sum_singleton]
      · simp only [if_neg hi]
        exact Finset.sum_congr rfl fun q _ => by rw [hO i q hi]
    rw [e1] at key
    exact key
  · intro i
    split_ifs
    · exact hα
    · exact hL.β_nonneg
  · intro i q
    split_ifs
    · positivity
    · rcases q with Z | y <;> simp only [termDecayWeight, Sum.elim_inl, Sum.elim_inr] <;> positivity
  · have := hL.κ_pos
    norm_num
    linarith
  · intro i
    by_cases hi : i = i₀
    · exact ⟨Sum.inl ⟨Y, hL.mem_cells Y⟩, Or.inl ⟨hi, rfl, _, rfl⟩⟩
    · exact ⟨Sum.inl ⟨Y, hL.mem_cells Y⟩, Or.inr ⟨hi, fun _ => ⟨_, rfl⟩⟩⟩
  · intro i q hq
    by_cases hi : i = i₀
    · subst hi
      rw [hO₀]
      exact hSl.smooth
    · rw [hO i q hi]
      rcases hj i hi with h2 | ⟨h3, ho⟩
      · exact fieldDeriv_contDiffOn hS (hL.smooth_term q) _ _ h2
      · obtain ⟨Z, rfl⟩ := hP1 i q hi hq ho
        exact third Z _ _ h3
  · intro i q hi _
    have hbd : j i ≤ 3 := (hj i hi).elim (fun h => by omega) fun h => h.1
    obtain ⟨D, hD⟩ := fieldDeriv_bounded hT (hL.smooth_term q) (cc i) (XX i) hbd
    rw [hO i q hi]
    exact ⟨D, fun η hη => hD η (norm_le_of_norm_lt hη)⟩
  · intro q _
    rw [hO₀]
    exact integrable_mul_ballDensity hL.ρ_pos hL.integrable hSl.smooth.continuousOn hSl.size
  · intro i q hq
    by_cases hi : i = i₀
    · subst hi
      have hY := hP0 q hq
      simp only [if_true, hO₀, hY]
      exact hSl.size
    · simp only [if_neg hi, hO i q hi]
      rcases q with Z | y
      · exact hL.size_cell Z _ _ _ ((hj i hi).elim (fun h => by omega) fun h => h.1) (hX i hi)
      · have h2 : j i ≤ 2 := by
          rcases hj i hi with h2 | ⟨-, ho⟩
          · exact h2
          · obtain ⟨Z, hZ⟩ := hP1 i _ hi hq ho
            exact absurd hZ (by simp)
        exact hL.size_site y _ _ _ h2 (hX i hi)
  · intro σ hs
    have h1 := bondSpan_le_cellsDiameter_add_sum (fun i => termCell (σ i)) i₀ j cc c hcov
    have hY : termCell (σ i₀) = Y := hP0 _ (hs i₀)
    simp only [hY] at h1
    have h2 : (bondSpan Y c : ℝ) ≤ (cellsDiameter fun i => termCell (σ i)) +
        ∑ i, (bondSpan (termCell (σ i)) (cc i) : ℝ) := by exact_mod_cast h1
    refine h2.trans (add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_))
    split_ifs with hi
    · subst hi
      rw [hY]
    · rcases hq : σ i with Z | y
      · simp only [termDecayWeight, termCell, Sum.elim_inl]
        have : (0 : ℝ) ≤ (bondSpan Z.1 (cc i) : ℝ) := by positivity
        linarith
      · simp only [termDecayWeight, termCell, Sum.elim_inr]
        exact le_rfl
end YangMills.Construction.Cumulants
end
