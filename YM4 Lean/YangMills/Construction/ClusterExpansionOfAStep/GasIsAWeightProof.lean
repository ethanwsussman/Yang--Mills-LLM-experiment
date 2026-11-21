import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfTheGasProof
import YangMills.Construction.ClusterExpansionOfAStep.DoubleRatiosOfASettingProof
import YangMills.Construction.ClusterExpansionOfAStep.SizeOfAClass
import YangMills.Construction.ClusterExpansionOfAStep.WeightOfTheGasIsBorel
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.ClusterExpansionOfAStep
open Dobrushin BlockAverages ColdStepAtMirrorFrames StepGas StepSettings TorusLumps TorusFields RenormalizationStepParameters
namespace GasActivity
variable {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n)
theorem measurableSet_vacant (i : G.GasSpin) :
    MeasurableSet ({G.pairConstraint.vacant i} : Set (G.SpinValue i)) := by
  have : ({G.pairConstraint.vacant i} : Set (G.SpinValue i)) = Set.range Sum.inl := by
    ext x
    constructor
    · rintro rfl
      exact ⟨(), rfl⟩
    · rintro ⟨⟨⟩, rfl⟩
      rfl
  rw [this]
  exact measurableSet_range_inl
theorem measurableSet_admissible : MeasurableSet {σ : G.Config | G.pairConstraint.IsAdmissible σ} := by
  classical
  have e : {σ : G.Config | G.pairConstraint.IsAdmissible σ} =
      ⋂ i, ⋂ j, {σ : G.Config | i ≠ j → G.pairConstraint.compatible i j (σ i) (σ j)} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, PairConstraint.IsAdmissible]
  rw [e]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases hij : i = j
  · have : {σ : G.Config | i ≠ j → G.pairConstraint.compatible i j (σ i) (σ j)} = Set.univ := by
      ext σ
      simp [hij]
    rw [this]
    exact MeasurableSet.univ
  by_cases hA : i.1.FarApart j.1
  · have : {σ : G.Config | i ≠ j → G.pairConstraint.compatible i j (σ i) (σ j)} = Set.univ := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact fun _ => Or.inr (Or.inr hA)
    rw [this]
    exact MeasurableSet.univ
  · have : {σ : G.Config | i ≠ j → G.pairConstraint.compatible i j (σ i) (σ j)} =
        (fun σ : G.Config => σ i) ⁻¹' {G.pairConstraint.vacant i} ∪
          (fun σ : G.Config => σ j) ⁻¹' {G.pairConstraint.vacant j} := by
      ext σ
      constructor
      · intro h
        rcases h hij with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hA
      · rintro (h | h) _
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    rw [this]
    exact ((measurable_pi_apply i) (measurableSet_vacant G i)).union
      ((measurable_pi_apply j) (measurableSet_vacant G j))
theorem referenceMeasureOff_vacant (off : G.GasSpin → Prop) (i : G.GasSpin) :
    G.referenceMeasureOff off i {G.pairConstraint.vacant i} = 1 := by
  classical
  have ha := measurableSet_vacant G i
  have h1 : (Measure.map Sum.inl (Measure.dirac ()) : Measure (G.SpinValue i))
      {G.pairConstraint.vacant i} = 1 := by
    rw [Measure.map_apply measurable_inl ha]
    have : (Sum.inl : Unit → G.SpinValue i) ⁻¹' {G.pairConstraint.vacant i} = Set.univ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rfl
    rw [this]
    simp
  unfold StepGas.GasGround.referenceMeasureOff
  split_ifs
  · exact h1
  · unfold withNoneMeasure
    rw [Measure.add_apply, h1, Measure.map_apply measurable_inr ha]
    have : (Sum.inr : G.SpinState i → G.SpinValue i) ⁻¹' {G.pairConstraint.vacant i} = ∅ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun h => by cases h
    rw [this]
    simp
theorem setLIntegral_compl_vacant_le (off : G.GasSpin → Prop) (i : G.GasSpin)
    {f : G.SpinValue i → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ s in {G.pairConstraint.vacant i}ᶜ, f s ∂G.referenceMeasureOff off i ≤
      ∫⁻ v, f (Sum.inr v) ∂G.spinStateMeasure i := by
  classical
  have ha := measurableSet_vacant G i
  have hnull : (Measure.map Sum.inl (Measure.dirac ()) : Measure (G.SpinValue i))
      {G.pairConstraint.vacant i}ᶜ = 0 := by
    rw [Measure.map_apply measurable_inl ha.compl]
    have : (Sum.inl : Unit → G.SpinValue i) ⁻¹' {G.pairConstraint.vacant i}ᶜ = ∅ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_not]
      rfl
    rw [this]
    simp
  unfold StepGas.GasGround.referenceMeasureOff
  split_ifs
  · rw [Measure.restrict_eq_zero.mpr hnull]
    simp
  · unfold withNoneMeasure
    rw [Measure.restrict_add, lintegral_add_measure, Measure.restrict_eq_zero.mpr hnull,
      lintegral_zero_measure, zero_add, setLIntegral_map ha.compl hf measurable_inr]
    have : (Sum.inr : G.SpinState i → G.SpinValue i) ⁻¹' {G.pairConstraint.vacant i}ᶜ = Set.univ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact fun h => by cases h
    rw [this, Measure.restrict_univ]
theorem weightDensity_of_admissible {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) :
    G.pairConstraint.weightDensity G.weight σ = ENNReal.ofReal (G.weight σ) := by
  classical
  simp only [PairConstraint.weightDensity, if_pos hσ]
theorem weightDensity_of_not_admissible {σ : G.Config} (hσ : ¬ G.pairConstraint.IsAdmissible σ) :
    G.pairConstraint.weightDensity G.weight σ = 0 := by
  classical
  simp only [PairConstraint.weightDensity, if_neg hσ]
theorem isAdmissible_update_vacant {σ : G.Config} (i : G.GasSpin)
    (hσ : G.pairConstraint.IsAdmissible σ) :
    G.pairConstraint.IsAdmissible (Function.update σ i (G.pairConstraint.vacant i)) := by
  intro k l hkl
  by_cases hk : k = i
  · subst hk
    simp only [Function.update_self, Function.update_of_ne hkl.symm]
    exact G.pairConstraint.vacant_compatible _ _ _
  · by_cases hl : l = i
    · subst hl
      simp only [Function.update_self, Function.update_of_ne hk]
      exact G.pairConstraint.compatible_symm _ _ _ _ (G.pairConstraint.vacant_compatible _ _ _)
    · have := hσ k l hkl
      simpa only [Function.update_of_ne hk, Function.update_of_ne hl] using this
theorem weight_eq_integral {c : G.Config} (hs : G.pairConstraint.IsAdmissible c)
    (hp : 0 < (G.settingOf (G.familyOf c)).integral) :
    G.weight c = (G.settingOf (G.familyOf c)).integral := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasColumns.weight_eq_integral <;> assumption
theorem agreeOn_refl (s : ChartSetting R n) (B : TorusBond (n * R.params.side) → Prop)
    (Q : Finset (TorusSite n)) : s.AgreeOn s B Q := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HeldBondRatios.agreeOn_refl <;> assumption
theorem lintegral_compl_vacant_le_of {c : ℝ} (off : G.GasSpin → Prop)
    (hd : Measurable (G.pairConstraint.weightDensity G.weight))
    (hset : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ →
      (G.settingOf (G.familyOf σ)).IsAdmissible)
    (size : ∀ (σ : G.Config) (i : G.GasSpin), G.pairConstraint.IsAdmissible σ →
      (G.settingOf (G.familyOf σ)).IsAdmissible →
      σ i = Sum.inl () → (∀ j, σ j = Sum.inl () ∨ i.1.FarApart j.1) →
      ∫⁻ v, ENNReal.ofReal (G.weight (Function.update σ i (Sum.inr v))) ∂(G.spinStateMeasure i) ≤
        ENNReal.ofReal (G.spinActivity c i) * ENNReal.ofReal (G.weight σ))
    (i : G.GasSpin) (σ : G.Config) (hσ : G.pairConstraint.IsAdmissible σ) :
    ∫⁻ s in {G.pairConstraint.vacant i}ᶜ,
        G.pairConstraint.weightDensity G.weight (Function.update σ i s) ∂G.referenceMeasureOff off i ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)) := by
  classical
  have hf : Measurable fun s => G.pairConstraint.weightDensity G.weight (Function.update σ i s) :=
    hd.comp (measurable_update σ)
  refine (setLIntegral_compl_vacant_le G off i hf).trans ?_
  set σ₀ := Function.update σ i (G.pairConstraint.vacant i) with hσ₀
  have hadm : G.pairConstraint.IsAdmissible σ₀ := isAdmissible_update_vacant G i hσ
  have hup : ∀ s, Function.update σ₀ i s = Function.update σ i s := fun s => by
    simp only [hσ₀, Function.update_idem]
  by_cases hcomp : ∀ j, σ₀ j = Sum.inl () ∨ i.1.FarApart j.1
  · have h1 := size σ₀ i hadm (hset _ hadm) (by simp [hσ₀]; rfl) hcomp
    rw [weightDensity_of_admissible G hadm]
    refine le_trans (lintegral_mono fun v => ?_) h1
    rw [hup]
    by_cases hv : G.pairConstraint.IsAdmissible (Function.update σ i (Sum.inr v))
    · rw [weightDensity_of_admissible G hv]
    · rw [weightDensity_of_not_admissible G hv]
      exact bot_le
  · simp only [not_forall, not_or] at hcomp
    obtain ⟨j, hj, hA⟩ := hcomp
    have hji : j ≠ i := by
      rintro rfl
      exact hj (by simp [hσ₀]; rfl)
    have hz : ∀ v : G.SpinState i,
        G.pairConstraint.weightDensity G.weight (Function.update σ i (Sum.inr v)) = 0 := by
      intro v
      apply weightDensity_of_not_admissible
      intro hv
      have := hv i j hji.symm
      simp only [Function.update_self, Function.update_of_ne hji] at this
      rcases this with h | h | h
      · cases h
      · apply hj
        simpa only [hσ₀, Function.update_of_ne hji] using h
      · exact hA h
    simp only [hz]
    simp
end GasActivity
open GasActivity in
theorem gasIsActivityBounded (hsz : StepGas.ClusterIntegralLeWeight)
    (hs : GasConfigIsAdmissibleSetting) (hb : StepGas.GasWeightMeasurable)
    (hd : DoubleRatioDecay) : GasIsActivityBounded := by
  classical
  obtain ⟨a₁, ha₁, hsz⟩ := hsz
  obtain ⟨a₂, ha₂, hd⟩ := hd
  refine ⟨fun c => min (a₁ c) (a₂ c), fun c => lt_min (ha₁ c) (ha₂ c), fun T hT hrt => ?_⟩
  obtain ⟨y₁, hsz⟩ := hsz T hT (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, hd⟩ := hd T hT (hrt.trans (min_le_right _ _))
  obtain ⟨y₃, hs⟩ := hs T hT
  obtain ⟨y₄, hb⟩ := hb T hT
  refine ⟨max y₁ (max y₂ (max y₃ y₄)), fun y hy R hR hxx n _ G hG off => ?_⟩
  have b₁ : y₁ ≤ y := (le_max_left _ _).trans hy
  have b₂ : y₂ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have b₃ : y₃ ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have b₄ : y₄ ≤ y := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have en₀ : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hn₀ : T.n₀ ≤ n := by
    rcases hG with h | h
    · rw [← en₀]
      exact h.n₀_le
    · rw [← en₀]
      obtain ⟨hdvd, hle⟩ := h.isBlockSide
      exact (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne R.params.side))).trans hle
  have hset := fun σ => hs y b₃ R hR hxx n G hG σ
  have hmeas : Measurable G.weight := hb y b₄ R hR hxx n G hG
  have hdens : Measurable (G.pairConstraint.weightDensity G.weight) := by
    unfold PairConstraint.weightDensity
    exact Measurable.ite (measurableSet_admissible G) (ENNReal.measurable_ofReal.comp hmeas)
      measurable_const
  have hpos : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → 0 < G.weight σ := by
    intro σ hσ
    set st := G.settingOf (G.familyOf σ) with hst
    have hc : CompatibleSupports (fun _ _ => st) (∅ : Finset (TorusSite (n * R.params.side))) ∅ :=
      ⟨fun _ h => absurd h (Finset.notMem_empty _), fun _ _ _ _ => Or.inr (Or.inr fun _ h => by simp at h)⟩
    have hf : IsFourSettings (fun _ _ => st)
        (coreBlocks R.params.side R.range (∅ : Finset (TorusSite (n * R.params.side))))
        (coreBlocks R.params.side R.range (∅ : Finset (TorusSite (n * R.params.side)))) :=
      ⟨fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ => agreeOn_refl st _ _, fun _ _ _ => agreeOn_refl st _ _,
        fun _ _ _ _ => agreeOn_refl st _ _⟩
    have hp := (hd y b₂ R hR n hn₀ (fun _ _ => st) ∅ ∅ (fun _ _ => hset σ hσ) hc hf).1 0 0
    rw [weight_eq_integral G hσ hp]
    exact hp
  exact
    { measurableSet_admissible := measurableSet_admissible G
      measurable := hmeas
      pos_of_admissible := hpos
      measurableSet_vacant := measurableSet_vacant G
      measure_vacant := referenceMeasureOff_vacant G off
      activity_nonneg := fun i => (Real.exp_pos _).le
      lintegral_compl_vacant_le := fun i σ hσ => lintegral_compl_vacant_le_of G off hdens hset
        (fun σ i h1 h2 h3 h4 => hsz y b₁ R hR hxx n G σ i hG h1 h2 h3 h4) i σ hσ }
end YangMills.Construction.ClusterExpansionOfAStep
end
