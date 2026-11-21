import YangMills.Construction.ColdStepAtMirrorFrames.SmoothOnATube
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfExpansionsAtATop
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfSizedSums
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfTheMeanOfAPartProof
import YangMills.Construction.SummableBoundsOfTheFlow.PartsOfAnExponentHaveTheirSizesProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Cumulants Estimates LawAtTop ConvexObservables SmoothSlices
namespace Cumulants
variable {F : BlockFrame}
namespace ExpansionBound
theorem norm_le_of_norm_lt {ρ : ℝ} {η : StepVariable (finiteCells F)} (h : ∀ b, ‖η b‖ < ρ) :
    ∀ b, ‖η b‖ ≤ ρ :=
  fun b => (h b).le
theorem fieldDeriv_contDiffOn (hS : IteratedFDerivSlices) {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hG : JointlyContDiffOnBalls ρ V G) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 2) :
    ContDiffOn ℝ 1 (fieldDeriv G V c X) {η | ∀ b, ‖η b‖ < ρ} := by
  intro η hη
  refine ContDiffAt.contDiffWithinAt ?_
  have hG3 := hG k c X η (norm_le_of_norm_lt hη)
  have hsl := hS.2.1 (Fin k → ℝ) (StepVariable (finiteCells F))
    (fun q => G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) k 1 (fun l => Pi.single l 1) η
    (ContDiffAt.of_le hG3 (by exact_mod_cast (by omega : 1 + k ≤ 3)))
  exact hsl
theorem fieldDeriv_bounded (hT : UniformDerivBoundNearCompact) {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hG : JointlyContDiffOnBalls ρ V G) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3) :
    ∃ D : ℝ, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) → |fieldDeriv G V c X η| ≤ D := by
  have hK : IsCompact {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ ≤ ρ} := by
    have : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ ≤ ρ} =
        Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
      ext η
      simp
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨r, M, hr, h⟩ := hT k (StepVariable (finiteCells F))
    (fun q => G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) _ hK (fun η hη => hG k c X η hη)
  refine ⟨M, fun η hη => ?_⟩
  have h1 := (h η hη).2 k hk 0 (Metric.mem_ball_self hr)
  have h2 := (iteratedFDeriv ℝ k (fun τ : Fin k → ℝ =>
    G η (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0).le_opNorm
    (fun l => Pi.single l 1)
  have h3 : ∏ l : Fin k, ‖(Pi.single l 1 : Fin k → ℝ)‖ = 1 :=
    Finset.prod_eq_one fun l _ => by rw [Pi.norm_single, norm_one]
  rw [h3, mul_one] at h2
  exact h2.trans h1
theorem cellSupDist_le_bondSpan {Z : F.Cell} {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (a : Fin k) :
    cellSupDist Z (c a).1 ≤ bondSpan Z c :=
  le_trans (Finset.le_sup (f := fun l : Fin k => siteSupDist Z (c l).1) (Finset.mem_univ a)) (le_max_left _ _)
theorem cellSupDist_pair_le_bondSpan {Z : F.Cell} {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (a a' : Fin k) :
    cellSupDist (c a).1 (c a').1 ≤ bondSpan Z c := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.cellSupDist_pair_le_bondSpan <;> assumption
theorem cellSupDist_le_cellsDiameter {M : ℕ} (z : Fin M → F.Cell) (i i' : Fin M) :
    cellSupDist (z i) (z i') ≤ cellsDiameter z := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.cellSupDist_le_cellsDiameter <;> assumption
theorem bondSpan_le_cellsDiameter_add_sum {M : ℕ} (z : Fin M → F.Cell) (i₀ : Fin M) (j : Fin M → ℕ)
    (cc : ∀ i, Fin (j i) → F.Site F.top × Fin 4) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (hcov : ∀ l, ∃ i a, cc i a = c l) :
    bondSpan (z i₀) c ≤ cellsDiameter z + ∑ i, bondSpan (z i) (cc i) := by
  set D := cellsDiameter z with hD
  set S := ∑ i, bondSpan (z i) (cc i) with hS
  have hone : ∀ i, bondSpan (z i) (cc i) ≤ S := fun i =>
    Finset.single_le_sum (f := fun i => bondSpan (z i) (cc i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have htwo : ∀ i i', i ≠ i' → bondSpan (z i) (cc i) + bondSpan (z i') (cc i') ≤ S := fun i i' h => by
    have := Finset.sum_le_sum_of_subset (f := fun i => bondSpan (z i) (cc i))
      (Finset.subset_univ ({i, i'} : Finset (Fin M)))
    rwa [Finset.sum_pair h] at this
  refine max_le (Finset.sup_le fun l _ => ?_) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  · obtain ⟨i, a, ha⟩ := hcov l
    have h1 : cellSupDist (z i₀) (z i) ≤ D := cellSupDist_le_cellsDiameter z i₀ i
    have h2 : cellSupDist (z i) (c l).1 ≤ bondSpan (z i) (cc i) := by
      rw [← ha]
      exact cellSupDist_le_bondSpan (cc i) a
    have h3 := PatchLocality.cellSupDist_triangle (z i₀) (z i) (c l).1
    have h4 := hone i
    change cellSupDist (z i₀) (c l).1 ≤ D + S
    omega
  · obtain ⟨i, a, ha⟩ := hcov l
    obtain ⟨i', a', ha'⟩ := hcov l'
    change cellSupDist (c l).1 (c l').1 ≤ D + S
    by_cases hi : i = i'
    · subst hi
      have h1 : cellSupDist (c l).1 (c l').1 ≤ bondSpan (z i) (cc i) := by
        rw [← ha, ← ha']
        exact cellSupDist_pair_le_bondSpan (cc i) a a'
      have h4 := hone i
      omega
    · have h1 : cellSupDist (z i) (z i') ≤ D := cellSupDist_le_cellsDiameter z i i'
      have h2 : cellSupDist (z i) (c l).1 ≤ bondSpan (z i) (cc i) := by
        rw [← ha]
        exact cellSupDist_le_bondSpan (cc i) a
      have h2' : cellSupDist (z i') (c l').1 ≤ bondSpan (z i') (cc i') := by
        rw [← ha']
        exact cellSupDist_le_bondSpan (cc i') a'
      have h3 := PatchLocality.cellSupDist_triangle (c l).1 (z i) (c l').1
      have h3' := PatchLocality.cellSupDist_triangle (z i) (z i') (c l').1
      have h5 : cellSupDist (c l).1 (z i) = cellSupDist (z i) (c l).1 := PatchLocality.cellSupDist_comm _ _
      have h4 := htwo i i' hi
      omega
end ExpansionBound
open ExpansionBound in
theorem expansionExponentCumulantBound_holds (hS : IteratedFDerivSlices) (hT : UniformDerivBoundNearCompact)
    (hC : sizedSumsCumulantBound) : expansionExponentCumulantBound := by
  classical
  intro N N' κ lam M hκ hlam hM2 hM9
  obtain ⟨B, hB0, hB⟩ := hC N N' κ lam M hκ hlam hM2 hM9
  refine ⟨B, hB0, ?_⟩
  intro F star a ρA x m ρ α β p Cq φ h V hL Y i₀ j cc XX only k c hX hj hcov
  obtain ⟨Ψ, K, hag, hconv, hslope⟩ := hL.convex
  have hP0 : ∀ q, jointSlotPlaces Y i₀ only i₀ q →
      ∃ y : ↥(sitesOfCells (finiteCells F) F.depth), q = Sum.inr y ∧ enclosingCell y.1 = Y := by
    rintro q (⟨-, h⟩ | ⟨h, -⟩)
    · exact h
    · exact absurd rfl h
  have hP1 : ∀ i q, i ≠ i₀ → jointSlotPlaces Y i₀ only i q → only i → ∃ Z : ↥(finiteCells F), q = Sum.inl Z := by
    rintro i q hi (⟨h, -⟩ | ⟨-, h⟩)
    · exact absurd h hi
    · exact h
  have hj₀ : j i₀ ≤ 2 := (hj i₀).elim id fun h => absurd rfl h.2.1
  have hsl : ∀ (i : Fin M) (q : TermPlace F), i ≠ i₀ →
      jointSlotTerm star a ρA x m φ h i₀ i q = exponentTerm star a ρA x m φ q :=
    fun i q hi => by simp [jointSlotTerm, hi]
  have hsl₀ : ∀ q : TermPlace F, jointSlotTerm star a ρA x m φ h i₀ i₀ q = seriesExpansionTerm star a ρA m h q :=
    fun q => by simp [jointSlotTerm]
  have third : ∀ {n : ℕ} (Z : ↥(finiteCells F)) (c' : Fin n → F.Site F.top × Fin 4)
      (X' : Fin n → imaginaryQuaternions), n ≤ 3 →
      ContDiffOn ℝ 1 (fieldDeriv (exponentTerm star a ρA x m φ (Sum.inl Z)) V c' X') {η | ∀ b, ‖η b‖ < ρ} := by
    intro n Z c' X' hn
    by_cases h2 : n ≤ 2
    · exact fieldDeriv_contDiffOn hS (hL.smooth_term _) c' X' h2
    · have h3 : n = 3 := by omega
      subst h3
      exact hL.third_term Z c' X'
  refine hB F ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1) ρ x p Ψ
    (fun η => exponentSum star a ρA x m φ η V) K (TermPlace F) termCell (jointSlotPlaces Y i₀ only)
    (fun i q => fieldDeriv (jointSlotTerm star a ρA x m φ h i₀ i q) V (cc i) (XX i))
    (fun i q => if i = i₀ then (bondSpan (termCell q) (cc i) : ℝ) else termDecayWeight (cc i) q)
    (fun i => if i = i₀ then α else β) Cq (2 ^ 4 * κ) (bondSpan Y c) Y i₀ hL.ρ_pos hL.x_pos hL.cutoff
    hL.card_bonds_le hconv hslope hag hL.integrable hL.Cq_nonneg ?_ ?_ ?_ ?_ hL.card_places_le ?_ ?_ ?_ ?_ ?_
  · intro i
    split_ifs
    · exact hL.α_nonneg
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
    · obtain ⟨y, hy⟩ := hL.cell_nonempty Y
      exact ⟨Sum.inr y, Or.inl ⟨hi, y, rfl, hy⟩⟩
    · exact ⟨Sum.inl ⟨Y, hL.mem_cells Y⟩, Or.inr ⟨hi, fun _ => ⟨_, rfl⟩⟩⟩
  · intro q hq
    obtain ⟨y, rfl, hy⟩ := hP0 q hq
    exact hy
  · intro i q hq
    by_cases hi : i = i₀
    · subst hi
      rw [hsl₀]
      exact fieldDeriv_contDiffOn hS (hL.smooth_expansion q) _ _ hj₀
    · rw [hsl i q hi]
      rcases hj i with h2 | ⟨h3, -, ho⟩
      · exact fieldDeriv_contDiffOn hS (hL.smooth_term q) _ _ h2
      · obtain ⟨Z, rfl⟩ := hP1 i q hi hq ho
        exact third Z _ _ h3
  · intro i q _
    have hbd : j i ≤ 3 := (hj i).elim (fun h => by omega) fun h => h.1
    have hG : JointlyContDiffOnBalls ρ V (jointSlotTerm star a ρA x m φ h i₀ i q) := by
      by_cases hi : i = i₀
      · subst hi
        rw [hsl₀]
        exact hL.smooth_expansion q
      · rw [hsl i q hi]
        exact hL.smooth_term q
    obtain ⟨D, hD⟩ := fieldDeriv_bounded hT hG (cc i) (XX i) hbd
    exact ⟨D, fun η hη => hD η (norm_le_of_norm_lt hη)⟩
  · intro i q hq
    by_cases hi : i = i₀
    · subst hi
      obtain ⟨y, rfl, hy⟩ := hP0 q hq
      simp only [if_true, hsl₀]
      exact hL.size_expansion y _ _ _ hj₀ (hX i)
    · simp only [if_neg hi, hsl i q hi]
      rcases q with Z | y
      · exact hL.size_cell Z _ _ _ ((hj i).elim (fun h => by omega) fun h => h.1) (hX i)
      · have h2 : j i ≤ 2 := by
          rcases hj i with h2 | ⟨-, -, ho⟩
          · exact h2
          · obtain ⟨Z, hZ⟩ := hP1 i _ hi hq ho
            exact absurd hZ (by simp)
        exact hL.size_site y _ _ _ h2 (hX i)
  · intro s hs
    have h1 := bondSpan_le_cellsDiameter_add_sum (fun i => termCell (s i)) i₀ j cc c hcov
    have hY : termCell (s i₀) = Y := by
      obtain ⟨y, hy, hyY⟩ := hP0 _ (hs i₀)
      rw [hy]
      exact hyY
    simp only [hY] at h1
    have h2 : (bondSpan Y c : ℝ) ≤ (cellsDiameter fun i => termCell (s i)) +
        ∑ i, (bondSpan (termCell (s i)) (cc i) : ℝ) := by exact_mod_cast h1
    refine h2.trans (add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_))
    split_ifs with hi
    · exact le_rfl
    · rcases hq : s i with Z | y
      · simp only [termDecayWeight, termCell, Sum.elim_inl]
        have : (0 : ℝ) ≤ (bondSpan Z.1 (cc i) : ℝ) := by positivity
        linarith
      · simp only [termDecayWeight, termCell, Sum.elim_inr]
        exact le_rfl
end Cumulants
end YangMills.Construction
end
