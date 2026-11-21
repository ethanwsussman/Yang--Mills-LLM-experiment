import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfASharedGasProof
import YangMills.Construction.ClusterExpansionOfAStep.TwoSystemsOfTheGasProof
import YangMills.Construction.ResponseInTheExpansion.TwoGroundsAtOscillations
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open Dobrushin StepGas StepSettings RenormalizationStepParameters StepFloors TorusLumps TorusFields CoreColumns ClusterExpansionOfAStep
namespace ResponseInTheExpansion
namespace OscillationComparison
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
section Embedding
variable {I J : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
  {T : J → Type} (P : PairConstraint S) {e : J → I}
theorem embedConfig_apply (v : ∀ j, T j → S (e j)) (he : Function.Injective e) (τ : ∀ j, T j) (j : J) :
    P.embedConfig e v τ (e j) = v j (τ j) := by apply _root_.YangMills.Construction.GasComparison.embedConfig_apply_of_injective <;> assumption
theorem embedConfig_of_not_mem_range (v : ∀ j, T j → S (e j)) (τ : ∀ j, T j) {i : I} (h : ∀ j, e j ≠ i) :
    P.embedConfig e v τ i = P.vacant i := by apply _root_.YangMills.Construction.GasComparison.embedConfig_of_not_mem_range <;> assumption
end Embedding
abbrev InnerIndex (G : GasGround R n) (Y : TorusSite n) (m : ℕ) (A : Finset (TorusSite n)) : Type :=
  {i : G.GasSpin // G.IsInnerSpin Y m A i}
instance (G : GasGround R n) (Y : TorusSite n) (m : ℕ) (A : Finset (TorusSite n)) :
    Fintype (InnerIndex G Y m A) :=
  Fintype.ofFinite _
def innerConstraint (G : GasGround R n) (Y : TorusSite n) (m : ℕ) (A : Finset (TorusSite n)) :
    PairConstraint (fun j : InnerIndex G Y m A => G.SpinValue j.1) where
  vacant _ := Sum.inl ()
  compatible i j s t := s = Sum.inl () ∨ t = Sum.inl () ∨ i.1.1.FarApart j.1.1
  compatible_symm _ _ _ _ h := by
    rcases h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h.symm)
  vacant_compatible _ _ _ := Or.inl rfl
open Classical in
def touchingSpins (G : GasGround R n) (A : Finset (TorusSite n)) : Finset G.GasSpin :=
  Finset.univ.filter fun i => i.1.Touches A
theorem core_nonempty (G : GasGround R n) (i : G.GasSpin) : i.1.core.Nonempty := by apply _root_.YangMills.Construction.StepGas.core_nonempty_of_gasSpin <;> assumption
theorem coreWeightFrom_pos (G : GasGround R n) (Y : TorusSite n) (i : G.GasSpin) :
    0 < G.coreWeightFrom Y i := by apply _root_.YangMills.Construction.GasComparison.coreWeightFrom_pos <;> assumption
theorem hasDobrushinColumns (G : GasGround R n) (Y : TorusSite n) {c : ℝ} {off : G.GasSpin → Prop}
    {h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight (G.spinActivity c)}
    (hs : G.HasSmallColumns off c h) :
    G.pairConstraint.HasDobrushinColumns (G.referenceMeasureOff off) h.measurable_weightDensity
      (G.influenceMatrix c) (G.coreWeightFrom Y) where
  coeff_nonneg := hs.influenceMatrix_nonneg
  weight_pos := coreWeightFrom_pos G Y
  kernel_le := hs.kernel_le
  column_sum_le j := by
    have h1 := hs.column_le Y j
    have h2 := hs.exp_le_half
    have h3 := coreWeightFrom_pos G Y j
    nlinarith
section Compare
variable {G : GasGround R n} {G' : GasGround R n'} {Y : TorusSite n} {Y' : TorusSite n'} {N m : ℕ}
  {A : Finset (TorusSite n)} {A' : Finset (TorusSite n')}
theorem extendSecond_index_injective (g : SharedInnerGas G G' Y Y' N m A A') :
    Function.Injective fun j => (g.spinEquiv j).1 :=
  Subtype.val_injective.comp g.spinEquiv.injective
theorem extendFirst_apply (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) (j : InnerIndex G Y m A) :
    g.extendFirst τ j.1 = τ j := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.extendFirst_apply <;> assumption
theorem extendSecond_apply (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) (j : InnerIndex G Y m A) :
    g.extendSecond τ (g.spinEquiv j).1 = g.valueEquiv j (τ j) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.extendSecond_apply <;> assumption
theorem extendFirst_of_not_inner (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) {i : G.GasSpin}
    (h : ¬ G.IsInnerSpin Y m A i) : g.extendFirst τ i = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.extendFirst_of_not_inner <;> assumption
theorem extendSecond_of_not_mem (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) {i : G'.GasSpin}
    (h : ∀ j : InnerIndex G Y m A, (g.spinEquiv j).1 ≠ i) : g.extendSecond τ i = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.extendSecond_of_forall_ne <;> assumption
theorem valueEquiv_eq_none_iff (g : SharedInnerGas G G' Y Y' N m A A') (j : InnerIndex G Y m A)
    {s : G.SpinValue j.1} : g.valueEquiv j s = Sum.inl () ↔ s = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.valueEquiv_eq_inl_iff <;> assumption
theorem extendFirst_admissible (g : SharedInnerGas G G' Y Y' N m A A') {τ : g.Config}
    (hτ : (innerConstraint G Y m A).IsAdmissible τ) : G.pairConstraint.IsAdmissible (g.extendFirst τ) := by
  intro i i' hii
  by_cases h1 : G.IsInnerSpin Y m A i
  · by_cases h2 : G.IsInnerSpin Y m A i'
    · have hne : (⟨i, h1⟩ : InnerIndex G Y m A) ≠ ⟨i', h2⟩ := fun h => hii (congrArg Subtype.val h)
      have := hτ _ _ hne
      rw [extendFirst_apply g τ ⟨i, h1⟩, extendFirst_apply g τ ⟨i', h2⟩]
      exact this
    · rw [extendFirst_of_not_inner g τ h2]
      exact Or.inr (Or.inl rfl)
  · rw [extendFirst_of_not_inner g τ h1]
    exact Or.inl rfl
theorem extendSecond_admissible (g : SharedInnerGas G G' Y Y' N m A A') {τ : g.Config}
    (hτ : (innerConstraint G Y m A).IsAdmissible τ) : G'.pairConstraint.IsAdmissible (g.extendSecond τ) := by
  intro i i' hii
  by_cases h1 : ∃ j : InnerIndex G Y m A, (g.spinEquiv j).1 = i
  · obtain ⟨j, rfl⟩ := h1
    by_cases h2 : ∃ j' : InnerIndex G Y m A, (g.spinEquiv j').1 = i'
    · obtain ⟨j', rfl⟩ := h2
      have hne : j ≠ j' := fun h => hii (by rw [h])
      rw [extendSecond_apply g τ j, extendSecond_apply g τ j']
      rcases hτ _ _ hne with h | h | h
      · exact Or.inl ((valueEquiv_eq_none_iff g j).mpr h)
      · exact Or.inr (Or.inl ((valueEquiv_eq_none_iff g j').mpr h))
      · exact Or.inr (Or.inr ((g.farApart_iff j j' hne).mp h))
    · rw [extendSecond_of_not_mem g τ fun j' hj => h2 ⟨j', hj⟩]
      exact Or.inr (Or.inl rfl)
  · rw [extendSecond_of_not_mem g τ fun j hj => h1 ⟨j, hj⟩]
    exact Or.inl rfl
theorem extendFirst_eq_allVacant (g : SharedInnerGas G G' Y Y' N m A A') {τ : g.Config}
    (h : ∀ j, τ j = Sum.inl ()) : g.extendFirst τ = G.allVacant := by
  funext i
  by_cases hi : G.IsInnerSpin Y m A i
  · rw [extendFirst_apply g τ ⟨i, hi⟩, h]
    rfl
  · rw [extendFirst_of_not_inner g τ hi]
    rfl
theorem extendSecond_eq_allVacant (g : SharedInnerGas G G' Y Y' N m A A') {τ : g.Config}
    (h : ∀ j, τ j = Sum.inl ()) : g.extendSecond τ = G'.allVacant := by
  funext i
  by_cases hi : ∃ j : InnerIndex G Y m A, (g.spinEquiv j).1 = i
  · obtain ⟨j, rfl⟩ := hi
    rw [extendSecond_apply g τ j, h, g.map_vacant j]
    rfl
  · rw [extendSecond_of_not_mem g τ fun j hj => hi ⟨j, hj⟩]
    rfl
theorem innerAdmissible_of_extendFirst (g : SharedInnerGas G G' Y Y' N m A A') {τ : g.Config}
    (hτ : G.pairConstraint.IsAdmissible (g.extendFirst τ)) : (innerConstraint G Y m A).IsAdmissible τ := by
  intro j j' hne
  have := hτ j.1 j'.1 fun h => hne (Subtype.ext h)
  rw [extendFirst_apply g τ j, extendFirst_apply g τ j'] at this
  exact this
theorem abs_expectation_sub_le (hCmp : oscillationComparisonStatement) (g : SharedInnerGas G G' Y Y' N m A A')
    {c : ℝ}
    (h₁ : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff fun i => i.1.Touches A) G.weight
      (G.spinActivity c))
    (h₂ : G'.pairConstraint.IsActivityBounded (G'.referenceMeasureOff fun i => i.1.Touches A') G'.weight
      (G'.spinActivity c))
    (hs₁ : G.HasSmallColumns (fun i => i.1.Touches A) c h₁)
    (hs₂ : G'.HasSmallColumns (fun i => i.1.Touches A') c h₂)
    {F : G.Config → ℝ} {F' : G'.Config → ℝ} {Kc a : ℝ} (ha : 0 ≤ a)
    (hF : G.pairConstraint.OscillationControlled (G.coreWeightFrom Y) Kc F)
    (hF' : G'.pairConstraint.OscillationControlled (G'.coreWeightFrom Y') Kc F')
    (hnear : ∀ τ : g.Config, G.pairConstraint.IsAdmissible (g.extendFirst τ) →
      |F (g.extendFirst τ) - F' (g.extendSecond τ)| ≤ a)
    (hab : F G.allVacant = F' G'.allVacant)
    (b E : InnerIndex G Y m A → ℝ) (hb0 : ∀ j, 0 ≤ b j)
    (hb : ∀ j, 2 * (G.spinActivity c j.1 + G'.spinActivity c (g.spinEquiv j).1) ≤ b j ∨
      (1 ≤ E j ∧ G.spinActivity c j.1 ≤ 1 ∧ G'.spinActivity c (g.spinEquiv j).1 ≤ 1 ∧
        8 * (E j - 1) * max (G.spinActivity c j.1) (G'.spinActivity c (g.spinEquiv j).1) ≤ b j ∧
        ∀ (τ : g.Config) (s : G.SpinValue j.1), (innerConstraint G Y m A).IsAdmissible (Function.update τ j s) →
          G.weight (g.extendFirst (Function.update τ j s)) *
              G'.weight (g.extendSecond (Function.update τ j (Sum.inl ()))) ≤
            E j * (G.weight (g.extendFirst (Function.update τ j (Sum.inl ()))) *
              G'.weight (g.extendSecond (Function.update τ j s))) ∧
          G'.weight (g.extendSecond (Function.update τ j s)) *
              G.weight (g.extendFirst (Function.update τ j (Sum.inl ()))) ≤
            E j * (G'.weight (g.extendSecond (Function.update τ j (Sum.inl ()))) *
              G.weight (g.extendFirst (Function.update τ j s))))) :
    |G.expectation A F - G'.expectation A' F'| ≤
      Kc * (4 * ∑ i ∈ Finset.univ.filter
            (fun i => (∀ j : InnerIndex G Y m A, j.1 ≠ i) ∧ i ∉ touchingSpins G A),
          G.coreWeightFrom Y i * G.spinActivity c i +
        4 * ∑ i ∈ Finset.univ.filter
            (fun i => (∀ j : InnerIndex G Y m A, (g.spinEquiv j).1 ≠ i) ∧ i ∉ touchingSpins G' A'),
          G'.coreWeightFrom Y' i * G'.spinActivity c i +
        2 * ∑ j : InnerIndex G Y m A, G.coreWeightFrom Y j.1 * b j) +
      ∑ j : InnerIndex G Y m A, a * G'.spinActivity c (g.spinEquiv j).1 := by
  classical
  have hin : ∀ j : InnerIndex G Y m A, G.referenceMeasureOff (fun i => ¬ G.IsInnerSpin Y m A i) j.1 =
      G.referenceMeasureOff (fun i => i.1.Touches A) j.1 := by
    intro j
    unfold GasGround.referenceMeasureOff
    rw [if_neg (not_not.mpr j.2), if_neg j.2.not_touches]
  have hin' : ∀ j : InnerIndex G Y m A,
      G'.referenceMeasureOff (fun i => ¬ G'.IsInnerSpin Y' m A' i) (g.spinEquiv j).1 =
        G'.referenceMeasureOff (fun i => i.1.Touches A') (g.spinEquiv j).1 := by
    intro j
    unfold GasGround.referenceMeasureOff
    rw [if_neg (not_not.mpr (g.spinEquiv j).2), if_neg (g.spinEquiv j).2.not_touches]
  have hH₁ : G.pairConstraint.IsVacantOffRange (G.referenceMeasureOff fun i => i.1.Touches A)
      (G.referenceMeasureOff fun i => ¬ G.IsInnerSpin Y m A i) (Subtype.val : InnerIndex G Y m A → G.GasSpin) := by
    refine ⟨hin, fun i hi => ?_⟩
    unfold GasGround.referenceMeasureOff
    rw [if_pos (fun h => hi ⟨i, h⟩ rfl)]
    exact Measure.map_dirac' measurable_inl ()
  have hH₂ : G'.pairConstraint.IsVacantOffRange (G'.referenceMeasureOff fun i => i.1.Touches A')
      (G'.referenceMeasureOff fun i => ¬ G'.IsInnerSpin Y' m A' i)
      (fun j : InnerIndex G Y m A => (g.spinEquiv j).1) := by
    refine ⟨hin', fun i hi => ?_⟩
    unfold GasGround.referenceMeasureOff
    rw [if_pos (fun h => by
      have := g.spinEquiv.apply_symm_apply ⟨i, h⟩
      exact hi (g.spinEquiv.symm ⟨i, h⟩) (congrArg Subtype.val this))]
    exact Measure.map_dirac' measurable_inl ()
  have hd₁ : ∀ i ∈ touchingSpins G A, G.referenceMeasureOff (fun i => i.1.Touches A) i =
      Measure.dirac (G.pairConstraint.vacant i) := by
    intro i hi
    unfold GasGround.referenceMeasureOff
    rw [if_pos (Finset.mem_filter.mp hi).2]
    exact Measure.map_dirac' measurable_inl ()
  have hd₂ : ∀ i ∈ touchingSpins G' A', G'.referenceMeasureOff (fun i => i.1.Touches A') i =
      Measure.dirac (G'.pairConstraint.vacant i) := by
    intro i hi
    unfold GasGround.referenceMeasureOff
    rw [if_pos (Finset.mem_filter.mp hi).2]
    exact Measure.map_dirac' measurable_inl ()
  have hmp₂ : ∀ j : InnerIndex G Y m A, MeasurePreserving (g.valueEquiv j)
      (G.referenceMeasureOff (fun i => i.1.Touches A) j.1)
      (G'.referenceMeasureOff (fun i => i.1.Touches A') (g.spinEquiv j).1) := by
    intro j
    have e1 : G.referenceMeasureOff (fun i => i.1.Touches A) j.1 = withNoneMeasure (G.spinStateMeasure j.1) := by
      unfold GasGround.referenceMeasureOff
      rw [if_neg j.2.not_touches]
    have e2 : G'.referenceMeasureOff (fun i => i.1.Touches A') (g.spinEquiv j).1 =
        withNoneMeasure (G'.spinStateMeasure (g.spinEquiv j).1) := by
      unfold GasGround.referenceMeasureOff
      rw [if_neg (g.spinEquiv j).2.not_touches]
    rw [e1, e2]
    exact g.measurePreserving j
  have hok₂ : ∀ (j j' : InnerIndex G Y m A) (s : G.SpinValue j.1) (t : G.SpinValue j'.1), j ≠ j' →
      ((innerConstraint G Y m A).compatible j j' s t ↔
        G'.pairConstraint.compatible (g.spinEquiv j).1 (g.spinEquiv j').1 (g.valueEquiv j s)
          (g.valueEquiv j' t)) := by
    intro j j' s t hne
    change (s = Sum.inl () ∨ t = Sum.inl () ∨ j.1.1.FarApart j'.1.1) ↔
      (g.valueEquiv j s = Sum.inl () ∨ g.valueEquiv j' t = Sum.inl () ∨
        (g.spinEquiv j).1.1.FarApart (g.spinEquiv j').1.1)
    rw [valueEquiv_eq_none_iff g j, valueEquiv_eq_none_iff g j', g.farApart_iff j j' hne]
  have hnn : ∀ (τ : g.Config) (j : InnerIndex G Y m A),
      0 ≤ @ite ℝ (τ j = (innerConstraint G Y m A).vacant j) (Classical.propDecidable _) 0 a := by
    intro τ j
    split_ifs
    · exact le_rfl
    · exact ha
  have hdiff : ∀ τ : g.Config, (innerConstraint G Y m A).IsAdmissible τ →
      |F (g.extendFirst τ) - F' (g.extendSecond τ)| ≤
        ∑ j, @ite ℝ (τ j = (innerConstraint G Y m A).vacant j) (Classical.propDecidable _) 0 a := by
    intro τ hτ
    by_cases hall : ∀ j, τ j = Sum.inl ()
    · rw [extendFirst_eq_allVacant g hall, extendSecond_eq_allVacant g hall, hab, sub_self, abs_zero]
      exact Finset.sum_nonneg fun j _ => hnn τ j
    · obtain ⟨j₀, hj₀⟩ := not_forall.mp hall
      refine (hnear τ (extendFirst_admissible g hτ)).trans ?_
      have h1 := Finset.single_le_sum
        (f := fun j => @ite ℝ (τ j = (innerConstraint G Y m A).vacant j) (Classical.propDecidable _) 0 a)
        (fun j _ => hnn τ j) (Finset.mem_univ j₀)
      have h2 : @ite ℝ (τ j₀ = (innerConstraint G Y m A).vacant j₀) (Classical.propDecidable _) 0 a = a :=
        if_neg hj₀
      rw [h2] at h1
      exact h1
  have key := hCmp.2 G.GasSpin G'.GasSpin (InnerIndex G Y m A) G.SpinValue G'.SpinValue
    (fun j => G.SpinValue j.1)
    G.pairConstraint G'.pairConstraint (innerConstraint G Y m A)
    (G.referenceMeasureOff fun i => i.1.Touches A) (G.referenceMeasureOff fun i => ¬ G.IsInnerSpin Y m A i)
    (G'.referenceMeasureOff fun i => i.1.Touches A') (G'.referenceMeasureOff fun i => ¬ G'.IsInnerSpin Y' m A' i)
    (fun j => G.referenceMeasureOff (fun i => i.1.Touches A) j.1)
    G.weight G'.weight (G.spinActivity c) (G'.spinActivity c) Subtype.val (fun j => (g.spinEquiv j).1)
    (fun _ => MeasurableEquiv.refl _) g.valueEquiv (G.influenceMatrix c) (G'.influenceMatrix c)
    (G.coreWeightFrom Y) (G'.coreWeightFrom Y') b E
    (fun _ => a) Kc (touchingSpins G A) (touchingSpins G' A') F F' h₁ h₂ Subtype.val_injective
    (extendSecond_index_injective g) hH₁ hH₂ hd₁ hd₂
    (fun _ => rfl) g.map_vacant (fun _ _ _ _ _ => Iff.rfl) hok₂ (fun _ => MeasurePreserving.id _) hmp₂
    (hasDobrushinColumns G Y hs₁) (hasDobrushinColumns G' Y' hs₂) hF hF' (fun _ => ha) hdiff hb0 hb
  exact key
end Compare
section Numbers
theorem mul_le_exp_mul_of_abs_log_sub {a b a' b' ε : ℝ} (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (h : |(Real.log b - Real.log a) - (Real.log b' - Real.log a')| ≤ ε) :
    b * a' ≤ Real.exp ε * (a * b') ∧ b' * a ≤ Real.exp ε * (a' * b) := by apply _root_.YangMills.Construction.GasComparison.mul_le_exp_mul_of_abs_log_sub_le <;> assumption
theorem exists_tail_le_one {ρ K : ℝ} (hρ : 0 < ρ) : ∃ Lc : ℕ, ∀ l : ℕ, Lc ≤ l →
    32 * ((l : ℝ) + 1) ^ 4 * Real.exp (-(2 * ρ * l)) + K * Real.exp (-(ρ * l)) ≤ 1 := by apply _root_.YangMills.Construction.GasComparison.exists_polyExp_sum_le_one <;> assumption
theorem exp_sub_one_le_two_mul {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : Real.exp ε - 1 ≤ 2 * ε := by apply _root_.YangMills.Construction.GasComparison.exp_sub_one_le_two_mul <;> assumption
variable {G : GasGround R n}
theorem exists_supDist_eq_setGap (Y : TorusSite n) {X : Finset (TorusSite n)} (h : X.Nonempty) :
    ∃ y ∈ X, _root_.YangMills.Construction.TorusFields.supDist Y y = setGap {Y} X := by apply _root_.YangMills.Construction.StepGas.exists_mem_supDist_eq_setGap <;> assumption
theorem spinActivity_nonneg (i : G.GasSpin) (c : ℝ) : 0 ≤ G.spinActivity c i := by apply _root_.YangMills.Construction.GasComparison.spinActivity_nonneg <;> assumption
theorem weighted_activity_le_of_far (Y : TorusSite n) (i : G.GasSpin) {c : ℝ} {D : ℕ} (hrt : 0 < R.params.rt)
    (h : ∃ y ∈ i.1.core, D ≤ _root_.YangMills.Construction.TorusFields.supDist y Y) :
    G.coreWeightFrom Y i * G.spinActivity c i ≤ Real.exp (-(3 * (R.params.rt / 2 ^ 8) * D)) *
      (G.spinActivity c i * (i.1.core.card : ℝ) ^ 4 * Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ))) *
      Real.exp (-(R.params.rt / 2 ^ 8 * (setGap {Y} i.1.core : ℝ))) := by apply _root_.YangMills.Construction.GasComparison.coreWeightFrom_mul_activity_le_far <;> assumption
theorem weighted_scaled_activity_le (Y : TorusSite n) (i : G.GasSpin) {c : ℝ} {D l N₂ : ℕ}
    (hrt : 0 < R.params.rt) (h : ∃ y ∈ i.1.core, D ≤ _root_.YangMills.Construction.TorusFields.supDist y Y) (hN : N₂ ≤ l + D) :
    G.coreWeightFrom Y i *
        (2 * ((i.1.core.card : ℝ) * Real.exp (-(2 * (R.params.rt / 2 ^ 8) * l))) * G.spinActivity c i) ≤
      2 * Real.exp (-(2 * (R.params.rt / 2 ^ 8) * N₂)) *
        (G.spinActivity c i * (i.1.core.card : ℝ) ^ 4 * Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ))) *
        Real.exp (-(R.params.rt / 2 ^ 8 * (setGap {Y} i.1.core : ℝ))) := by apply _root_.YangMills.Construction.GasComparison.coreWeightFrom_mul_activity_le_near <;> assumption
theorem exists_offset_of_supDist_le {p : ℕ} [NeZero p] (y Y : TorusSite p) (m : ℕ) (h : _root_.YangMills.Construction.TorusFields.supDist y Y ≤ m) :
    ∃ g, OffsetInBox m g ∧ y = Y + siteOfInt g := by apply _root_.YangMills.Construction.GasComparison.exists_offset_of_supDist_le <;> assumption
theorem offset_unique {p : ℕ} [NeZero p] (Y : TorusSite p) (N : ℕ) (hN : 2 * N + 2 < p)
    (h h' : Fin 4 → ℤ) (hh : OffsetInBox N h) (hh' : OffsetInBox N h')
    (e : Y + siteOfInt h = Y + siteOfInt h') : h = h' := by exact _root_.YangMills.Construction.CongruentBoxes.eq_of_add_siteOfInt_eq (n := p) (m := N) (y := Y) hN hh hh' e
theorem ceil_radius_le {r L Lc m₀ : ℕ} (hL : 2 ^ 40 ≤ L) (hdiv : r < 2 ^ 11 * (m₀ + 1)) (hm1 : 1 ≤ m₀)
    (hm0 : Lc + 9 ≤ m₀) : Lc + 2 * ⌈(r : ℝ) / (4 * (L : ℝ))⌉₊ + 6 ≤ 5 * m₀ := by apply _root_.YangMills.Construction.GasComparison.range_ceil_le <;> assumption
theorem eight_mul_sub_one_le {e z E : ℝ} (hz : 0 ≤ z) (he : 0 ≤ e) (hE : E - 1 ≤ 2 * e) :
    8 * (E - 1) * z ≤ 32 * e * z := by apply _root_.YangMills.Construction.GasComparison.eight_mul_sub_one_le <;> assumption
theorem two_mul_add_le {e z : ℝ} (hz : 0 ≤ z) (h : 1 / 2 < e) : 2 * (z + z) ≤ 32 * e * z := by
  nlinarith
theorem two_mul_le_four_mul {E U F : ℝ} (hE : 0 ≤ E) (hUF : 0 ≤ U * F) : 2 * E * U * F ≤ 4 * E * U * F := by
  nlinarith [mul_nonneg hE hUF]
theorem mul_four_le {a z E U F : ℝ} (h : a * z ≤ E * U * F) : a * (4 * z) ≤ 4 * E * U * F := by
  linarith
theorem exp_neg_three_le_exp_neg_two {ρ D N : ℝ} (hρ : 0 ≤ ρ) (h : 2 * N ≤ 3 * D) :
    Real.exp (-(3 * ρ * D)) ≤ Real.exp (-(2 * ρ * N)) := by apply _root_.YangMills.Construction.GasComparison.exp_neg_three_le_exp_neg_two <;> assumption
theorem offsetInBox_mono {a b : ℕ} {h : Fin 4 → ℤ} (hh : OffsetInBox a h) (hab : a ≤ b) : OffsetInBox b h :=
  fun i => (hh i).trans (by exact_mod_cast hab)
end Numbers
section Main
def farthestCoreDist (G : GasGround R n) (Y : TorusSite n) (i : G.GasSpin) : ℕ :=
  i.1.core.sup fun y => _root_.YangMills.Construction.TorusFields.supDist y Y
def logRatioBound (T : ParameterAssignment) (k d : ℕ) (p : ℝ) : ℝ :=
  p * (2 * (d : ℝ) + 1) ^ 4 * (2 * Real.exp (-(T.rt / 2 ^ 5 * k))) +
    2 * p * (Real.exp (2 * (T.rt / 2 ^ 5)) * Real.exp (-(3 / 4 * (T.rt / 2 ^ 5) * d)) *
      (2 / (1 - Real.exp (-(T.rt / 2 ^ 5 / 16)))) ^ 4)
theorem logRatioBound_nonneg (T : ParameterAssignment) (hrt : 0 < T.rt) (k d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ logRatioBound T k d p := by
  have h1 : Real.exp (-(T.rt / 2 ^ 5 / 16)) < 1 := Real.exp_lt_one_iff.mpr (by
    have : 0 < T.rt / 2 ^ 5 / 16 := by positivity
    linarith)
  unfold logRatioBound
  positivity
theorem logRatioBound_le (T : ParameterAssignment) (hrt : 0 < T.rt) {l k d : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (hd : d = l / 2) (hk : k = l - d)
    (hl : 32 * ((l : ℝ) + 1) ^ 4 * Real.exp (-(2 * (T.rt / 2 ^ 8) * l)) +
      32 * Real.exp (19 * (T.rt / 2 ^ 8)) * (2 / (1 - Real.exp (-(T.rt / 2 ^ 5 / 16)))) ^ 4 *
        Real.exp (-(T.rt / 2 ^ 8 * l)) ≤ 1) :
    16 * logRatioBound T k d p ≤ p * Real.exp (-(2 * (T.rt / 2 ^ 8) * l)) := by
  set ρ := T.rt / 2 ^ 8 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hc : T.rt / 2 ^ 5 = 8 * ρ := by
    rw [hρ]
    ring
  unfold logRatioBound
  rw [hc] at hl ⊢
  set W := (2 / (1 - Real.exp (-(8 * ρ / 16)))) ^ 4 with hW
  have hW0 : 0 ≤ W := by
    have h1 : Real.exp (-(8 * ρ / 16)) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < 8 * ρ / 16 := by positivity
      linarith)
    rw [hW]
    positivity
  have hd1 : 2 * d ≤ l := by omega
  have hd2 : l ≤ 2 * d + 1 := by omega
  have hk1 : d + k = l := by omega
  have hk2 : d ≤ k := by omega
  have hdr : 2 * (d : ℝ) ≤ l := by exact_mod_cast hd1
  have hdr2 : (l : ℝ) ≤ 2 * d + 1 := by exact_mod_cast hd2
  have hkr : (d : ℝ) + k = l := by exact_mod_cast hk1
  have e1 : Real.exp (-(8 * ρ * k)) ≤ Real.exp (-(2 * ρ * l)) * Real.exp (-(2 * ρ * l)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have e2 : Real.exp (2 * (8 * ρ)) * Real.exp (-(3 / 4 * (8 * ρ) * d)) ≤
      Real.exp (19 * ρ) * (Real.exp (-(2 * ρ * l)) * Real.exp (-(ρ * l))) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have e3 : (2 * (d : ℝ) + 1) ^ 4 ≤ ((l : ℝ) + 1) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  set A := Real.exp (-(2 * ρ * l)) with hA
  have hA0 : 0 < A := Real.exp_pos _
  set B := Real.exp (-(ρ * l)) with hB
  set Q := Real.exp (19 * ρ) with hQ
  have t1 : (2 * (d : ℝ) + 1) ^ 4 * (2 * Real.exp (-(8 * ρ * k))) ≤ ((l : ℝ) + 1) ^ 4 * (2 * (A * A)) :=
    mul_le_mul e3 (by linarith) (by positivity) (by positivity)
  have t2 : Real.exp (2 * (8 * ρ)) * Real.exp (-(3 / 4 * (8 * ρ) * d)) * W ≤ Q * (A * B) * W :=
    mul_le_mul_of_nonneg_right e2 hW0
  have hsum : 16 * (((l : ℝ) + 1) ^ 4 * (2 * (A * A)) + 2 * (Q * (A * B) * W)) ≤ A := by
    have : 16 * (((l : ℝ) + 1) ^ 4 * (2 * (A * A)) + 2 * (Q * (A * B) * W)) =
        A * (32 * ((l : ℝ) + 1) ^ 4 * A + 32 * Q * W * B) := by ring
    rw [this]
    nlinarith
  calc 16 * (p * (2 * (d : ℝ) + 1) ^ 4 * (2 * Real.exp (-(8 * ρ * k))) +
        2 * p * (Real.exp (2 * (8 * ρ)) * Real.exp (-(3 / 4 * (8 * ρ) * d)) * W))
      = p * (16 * ((2 * (d : ℝ) + 1) ^ 4 * (2 * Real.exp (-(8 * ρ * k))) +
        2 * (Real.exp (2 * (8 * ρ)) * Real.exp (-(3 / 4 * (8 * ρ) * d)) * W))) := by ring
    _ ≤ p * (16 * (((l : ℝ) + 1) ^ 4 * (2 * (A * A)) + 2 * (Q * (A * B) * W))) := by
        refine mul_le_mul_of_nonneg_left ?_ hp
        linarith
    _ ≤ p * A := mul_le_mul_of_nonneg_left hsum hp
end Main
end OscillationComparison
set_option maxHeartbeats 4000000 in
open OscillationComparison in
theorem twoGroundsOscillationComparison_of_parts (hCmp : oscillationComparisonStatement)
    (hCol : GasColumnsSmall) (hConf : GasConfigIsAdmissibleSetting) (hShare : GroundsShareInnerGas)
    (hSet : SharedGasSettingsPaired) (hRat : LogMassRatiosClose)
    (hMass : SettingMassEqIntegral) (hGS : GasSumNearBlockBound) (hFl : EventuallyFloorConditions)
    (hCF : CouplingFloorExists) : twoGroundsOscillationComparison := by
  obtain ⟨r₁, p₁, h₁⟩ := hCol
  obtain ⟨r₂, p₂, h₂⟩ := hShare
  obtain ⟨r₃, p₃, h₃⟩ := hSet
  obtain ⟨r₄, p₄, h₄⟩ := hRat
  obtain ⟨r₅, p₅, h₅⟩ := hMass
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (r₅ c)))),
    fun c => lt_min (p₁ c) (lt_min (p₂ c) (lt_min (p₃ c) (lt_min (p₄ c) (p₅ c)))),
    fun T hT hle => ?_⟩
  have c₁ := hle.trans (min_le_left _ _)
  have hle₂ := hle.trans (min_le_right _ _)
  have c₂ := hle₂.trans (min_le_left _ _)
  have hle₃ := hle₂.trans (min_le_right _ _)
  have c₃ := hle₃.trans (min_le_left _ _)
  have hle₄ := hle₃.trans (min_le_right _ _)
  have c₄ := hle₄.trans (min_le_left _ _)
  have c₅ := hle₄.trans (min_le_right _ _)
  obtain ⟨y₁, hy₁⟩ := h₁ T hT c₁
  obtain ⟨y₂, hy₂⟩ := h₂ T hT c₂
  obtain ⟨y₃, hy₃⟩ := h₃ T hT c₃
  obtain ⟨y₄, hy₄⟩ := h₄ T hT c₄
  obtain ⟨y₅, hy₅⟩ := h₅ T hT c₅
  obtain ⟨y₆, hy₆⟩ := hConf T hT
  have hrt := hT.rt_pos
  have hκ₁ : 0 < T.κ₁ := lt_min (div_pos hT.κ_pos (by norm_num))
    (div_pos hT.cE_pos (by have := hT.σ_pos; positivity))
  have hch : 0 < T.gasRate := by
    have h1 : 0 < T.κ * T.threshold ^ 2 := mul_pos hT.κ_pos (pow_pos hT.σ_pos 2)
    have h2 : 0 < T.κ₁ * T.threshold ^ 2 := mul_pos hκ₁ (pow_pos hT.σ_pos 2)
    exact mul_pos (by norm_num) (lt_min hT.cE_pos (lt_min h1 h2))
  have hρ : 0 < T.rt / 2 ^ 8 := by positivity
  obtain ⟨Lc, hLc⟩ := exists_tail_le_one (ρ := T.rt / 2 ^ 8)
    (K := 32 * Real.exp (19 * (T.rt / 2 ^ 8)) * (2 / (1 - Real.exp (-(T.rt / 2 ^ 5 / 16)))) ^ 4) hρ
  obtain ⟨y₇, hy₇⟩ := hFl T hT (2 ^ 11 * ((Lc : ℝ) + 9)) 1 (by positivity) one_pos
  obtain ⟨y₈, hy₈⟩ := hCF T.gasRate T.side T.rt hch
  set W₁ : ℝ := (2 / (1 - Real.exp (-(T.rt / 2 ^ 8 / 4)))) ^ 4 with hW₁
  have hW₁0 : 0 ≤ W₁ := by
    have h1 : Real.exp (-(T.rt / 2 ^ 8 / 4)) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < T.rt / 2 ^ 8 / 4 := by positivity
      linarith)
    have h2 : 0 < 1 - Real.exp (-(T.rt / 2 ^ 8 / 4)) := by linarith
    rw [hW₁]
    positivity
  refine ⟨max y₁ (max y₂ (max y₃ (max y₄ (max y₅ (max y₆ (max y₇ (max y₈
      (max T.floorMin ((32 * W₁ + 1) / T.gasRate))))))))),
    fun y hy R hR hx' n n' _ _ G G' Y Y' N A A' hG hG' hN hAg hBl => ?_⟩
  obtain ⟨a₁, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₂, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₃, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₄, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₅, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₆, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₇, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₈, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₉, a₁₀⟩ := max_le_iff.mp hy
  have hLL : R.params.side = T.side := by
    rw [hR.params_eq]
    rfl
  have hrtR : R.params.rt = T.rt := by
    rw [hR.params_eq]
    rfl
  have hy1R : R.params.y₁ = y := by
    rw [hR.params_eq]
    rfl
  have hn0R : R.params.n₀ = T.n₀ := by
    rw [hR.params_eq]
    rfl
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y a₉
  have hx : y ≤ R.coupling := hR.le_coupling
  have hcf : R.params.RangeFloor T.gasRate := by
    intro x hxx
    rw [hy1R] at hxx
    have := hy₈ x (a₈.trans hxx)
    rw [hLL, hrtR]
    exact this
  have hfloor := hy₇ R.coupling (a₇.trans hx)
  have hrtR0 : 0 < R.params.rt := hrtR ▸ hrt
  have hside : ∀ (p : ℕ) [NeZero p] (H : GasGround R p), H.IsAdmissibleGround → T.n₀ ≤ p := by
    intro p _ H hH
    rcases hH with h | h
    · rw [← hn0R]
      exact h.n₀_le
    · have h1 := h.isBlockSide.2
      have h2 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
      rw [← hn0R]
      exact (Nat.le_mul_of_pos_left _ h2).trans h1
  have hn := hside n G hG
  have hn' := hside n' G' hG'
  have hrr : 2 ^ 11 * (Lc + 9) ≤ R.range := by
    have := hfloor.range_ge
    have h2 : ((2 ^ 11 * (Lc + 9) : ℕ) : ℝ) ≤ (clusterRange R.coupling : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h2
  have hm0 : Lc + 9 ≤ R.frameReach := by
    unfold StepSetup.frameReach
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    linarith
  obtain ⟨g⟩ := hy₂ y a₂ R hR hx' n n' G G' Y Y' N A A' hG hG' hN hAg hBl
  have hall := hy₁ y a₁ R hR hx' n G hG
  have hall' := hy₁ y a₁ R hR hx' n' G' hG'
  obtain ⟨w₁, s₁⟩ := hall (fun i => i.1.Touches A)
  obtain ⟨w₂, s₂⟩ := hall' (fun i => i.1.Touches A')
  have hmass : ∀ (p : ℕ) [NeZero p] (H : GasGround R p) (σ : H.Config), H.IsAdmissibleGround →
      H.pairConstraint.IsAdmissible σ →
      (H.settingOf (H.familyOf σ)).IsAdmissible ∧ 0 < (H.settingOf (H.familyOf σ)).mass ∧
        H.weight σ = (H.settingOf (H.familyOf σ)).mass := by
    intro p _ H σ hH hσ
    have hs := hy₆ y a₆ R hR hx' p H hH σ hσ
    obtain ⟨-, e1, e2⟩ := hy₅ y a₅ R hR p (hside p H hH) _ hs
    refine ⟨hs, e1, ?_⟩
    unfold GasGround.weight
    rw [if_pos hσ, e2, ENNReal.toReal_ofReal e1.le]
  have hm1 : 1 ≤ R.frameReach := by omega
  have hNs := hAg.lt_extent
  have hNs' := hAg.lt_extent'
  have hxpos : 0 < R.coupling := by
    have h1 : (32 * W₁ + 1) / T.gasRate ≤ R.coupling := a₁₀.trans hx
    have h2 : 0 < (32 * W₁ + 1) / T.gasRate := div_pos (by linarith) hch
    linarith
  have hchx : 32 * W₁ + 1 ≤ T.gasRate * R.coupling := by
    have h1 : (32 * W₁ + 1) / T.gasRate ≤ R.coupling := a₁₀.trans hx
    rw [div_le_iff₀ hch] at h1
    linarith
  set q : ℕ := ⌈(R.range : ℝ) / (4 * R.params.side)⌉₊ with hq
  set L₀ : ℕ := Lc + 2 * q + 6 with hL₀
  have hq1 : (R.range : ℝ) / (4 * R.params.side) ≤ q := Nat.le_ceil _
  have hL₀5 : L₀ ≤ 5 * R.frameReach := by
    have hdiv : R.range < 2 ^ 11 * (R.frameReach + 1) := by
      unfold StepSetup.frameReach
      exact Nat.lt_mul_div_succ _ (by norm_num)
    exact ceil_radius_le (hLL ▸ hT.L_ge) hdiv hm1 hm0
  have hfar : ∀ j : G.InnerSpin Y (N - R.frameReach - 1) A,
      farthestCoreDist G Y j.1 ≤ N - R.frameReach - 1 := by
    intro j
    refine Finset.sup_le fun y hy => ?_
    obtain ⟨h, hh, rfl⟩ := j.2.core_near y hy
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
    have := hh i
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  have hplaces : ∀ (j : G.InnerSpin Y (N - R.frameReach - 1) A),
      ∀ h ∈ G.coreOffsets Y (N - R.frameReach - 1) j.1, OffsetInBox (farthestCoreDist G Y j.1) h := by
    intro j h hh
    classical
    obtain ⟨hb, hc⟩ := Finset.mem_filter.mp hh
    have hbox : OffsetInBox (N - R.frameReach - 1) h := fun i => by
      have := Fintype.mem_piFinset.mp hb i
      rw [Finset.mem_Icc] at this
      exact abs_le.mpr this
    have h1 : _root_.YangMills.Construction.TorusFields.supDist (Y + siteOfInt h) Y ≤ farthestCoreDist G Y j.1 :=
      Finset.le_sup (f := fun y => _root_.YangMills.Construction.TorusFields.supDist y Y) hc
    obtain ⟨g', hg', e⟩ := exists_offset_of_supDist_le _ _ _ h1
    have := offset_unique Y N hNs h g' (offsetInBox_mono hbox (by omega))
      (offsetInBox_mono hg' ((hfar j).trans (by omega))) e
    rw [this]
    exact hg'
  have hcard : ∀ j : G.InnerSpin Y (N - R.frameReach - 1) A,
      ((G.coreOffsets Y (N - R.frameReach - 1) j.1).card : ℝ) ≤ (j.1.1.core.card : ℝ) := by
    intro j
    classical
    have : (G.coreOffsets Y (N - R.frameReach - 1) j.1).card ≤ j.1.1.core.card := by
      refine Finset.card_le_card_of_injOn (fun h => Y + siteOfInt h) (fun h hh => ?_)
        fun h hh h' hh' e => ?_
      · exact (Finset.mem_filter.mp hh).2
      · have b1 := offsetInBox_mono (hplaces j h hh)
          ((hfar j).trans (by omega : N - R.frameReach - 1 ≤ N))
        have b2 := offsetInBox_mono (hplaces j h' hh')
          ((hfar j).trans (by omega : N - R.frameReach - 1 ≤ N))
        exact offset_unique Y N hNs h h' b1 b2 e
    exact_mod_cast this
  have hnon : ∀ j : G.InnerSpin Y (N - R.frameReach - 1) A,
      (G.coreOffsets Y (N - R.frameReach - 1) j.1).Nonempty := by
    intro j
    classical
    obtain ⟨y', hy'⟩ := core_nonempty G j.1
    obtain ⟨h, hh, rfl⟩ := j.2.core_near y' hy'
    refine ⟨h, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, hy'⟩⟩
    rw [Finset.mem_Icc]
    exact abs_le.mp (hh i)
  have hpr : ∀ j : G.InnerSpin Y (N - R.frameReach - 1) A,
      G'.spinActivity T.gasRate (g.spinEquiv j).1 = G.spinActivity T.gasRate j.1 := by
    intro j
    unfold GasGround.spinActivity clusterWeight
    rw [g.unitCount_eq j]
  have hp1 : ∀ i : G.GasSpin, G.spinActivity T.gasRate i ≤ 1 := by
    intro i
    unfold GasGround.spinActivity clusterWeight
    refine Real.exp_le_one_iff.mpr ?_
    have : 0 ≤ 16 * T.gasRate * R.coupling * (supportUnitCount R.params.side R.range i.1 : ℝ) := by
      positivity
    linarith
  have hp0 : ∀ i : G.GasSpin, 0 ≤ G.spinActivity T.gasRate i := fun i => spinActivity_nonneg i _
  classical
  obtain ⟨lOf, hlOf⟩ : ∃ f : G.InnerSpin Y (N - R.frameReach - 1) A → ℕ,
      ∀ j, f j = (N - R.frameReach) - farthestCoreDist G Y j.1 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨dOf, hdOf⟩ : ∃ f : G.InnerSpin Y (N - R.frameReach - 1) A → ℕ, ∀ j, f j = lOf j / 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨kOf, hkOf⟩ : ∃ f : G.InnerSpin Y (N - R.frameReach - 1) A → ℕ, ∀ j, f j = lOf j - dOf j :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨pOf, hpOf⟩ : ∃ f : G.InnerSpin Y (N - R.frameReach - 1) A → ℝ,
      ∀ j, f j = ((G.coreOffsets Y (N - R.frameReach - 1) j.1).card : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨eOf, heOf⟩ : ∃ f : G.InnerSpin Y (N - R.frameReach - 1) A → ℝ,
      ∀ j, f j = logRatioBound T (kOf j) (dOf j) (pOf j) := ⟨_, fun _ => rfl⟩
  obtain ⟨bOf, hbOf⟩ : ∃ f : G.InnerSpin Y (N - R.frameReach - 1) A → ℝ,
      ∀ j, f j = if L₀ ≤ lOf j then 32 * eOf j * G.spinActivity T.gasRate j.1
        else 4 * G.spinActivity T.gasRate j.1 := ⟨_, fun _ => rfl⟩
  have hp0' : ∀ j, 0 ≤ pOf j := fun j => by
    rw [hpOf]
    exact Nat.cast_nonneg _
  have he0 : ∀ j, 0 ≤ eOf j := fun j => by
    rw [heOf]
    exact logRatioBound_nonneg T hrt _ _ (hp0' j)
  have hb0 : ∀ j, 0 ≤ bOf j := by
    intro j
    rw [hbOf]
    have h1 := hp0 j.1
    have h2 := he0 j
    split_ifs
    · positivity
    · positivity
  have hlogs : ∀ (j : G.InnerSpin Y (N - R.frameReach - 1) A), L₀ ≤ lOf j →
      ∀ (τ : g.Config) (s : G.SpinValue j.1),
      (innerConstraint G Y (N - R.frameReach - 1) A).IsAdmissible (Function.update τ j s) →
      G.weight (g.extendFirst (Function.update τ j s)) *
          G'.weight (g.extendSecond (Function.update τ j (Sum.inl ()))) ≤
          Real.exp (eOf j) * (G.weight (g.extendFirst (Function.update τ j (Sum.inl ()))) *
            G'.weight (g.extendSecond (Function.update τ j s))) ∧
        G'.weight (g.extendSecond (Function.update τ j s)) *
          G.weight (g.extendFirst (Function.update τ j (Sum.inl ()))) ≤
          Real.exp (eOf j) * (G'.weight (g.extendSecond (Function.update τ j (Sum.inl ()))) *
            G.weight (g.extendFirst (Function.update τ j s))) := by
    intro j hbig τ s hadm
    have hadm0 : (innerConstraint G Y (N - R.frameReach - 1) A).IsAdmissible
        (Function.update τ j (Sum.inl ())) := by
      intro a b hab
      by_cases ha : a = j
      · subst ha
        rw [Function.update_self]
        exact Or.inl rfl
      · by_cases hb' : b = j
        · subst hb'
          rw [Function.update_self]
          exact Or.inr (Or.inl rfl)
        · have := hadm a b hab
          rw [Function.update_of_ne ha, Function.update_of_ne hb'] at this ⊢
          exact this
    obtain ⟨Sa, Pa, Wa⟩ := hmass n G _ hG (extendFirst_admissible g hadm0)
    obtain ⟨Sb, Pb, Wb⟩ := hmass n G _ hG (extendFirst_admissible g hadm)
    obtain ⟨Sa', Pa', Wa'⟩ := hmass n' G' _ hG' (extendSecond_admissible g hadm0)
    obtain ⟨Sb', Pb', Wb'⟩ := hmass n' G' _ hG' (extendSecond_admissible g hadm)
    have e₁ := hlOf j
    have e₂ := hdOf j
    have e₃ := hkOf j
    have hl : lOf j = kOf j + dOf j := by omega
    have hd2 : q + 3 ≤ dOf j := by omega
    have hkd : dOf j ≤ kOf j := by omega
    have hfj := hfar j
    have hl2 : (N - R.frameReach) - lOf j = farthestCoreDist G Y j.1 := by omega
    have hkd2 : kOf j + dOf j ≤ N - R.frameReach := by omega
    have tp := hy₃ y a₃ R hR hx' n n' G G' Y Y' N A A' g τ j s (dOf j) (kOf j) hG hG' hN hAg hBl
      (extendFirst_admissible g hadm)
      (fun h hh => by
        have hpl := hplaces j h hh
        rw [show (N - R.frameReach) - (kOf j + dOf j) = farthestCoreDist G Y j.1 by rw [← hl, hl2]]
        exact hpl)
      hkd2
    have hdr : (R.range : ℝ) / (4 * R.params.side) ≤ (dOf j : ℝ) - 2 := by
      have : (q : ℝ) + 3 ≤ dOf j := by exact_mod_cast hd2
      linarith
    have hkr : (R.range : ℝ) / (4 * R.params.side) ≤ (kOf j : ℝ) := by
      have h1 : (q : ℝ) + 3 ≤ dOf j := by exact_mod_cast hd2
      have h2 : (dOf j : ℝ) ≤ kOf j := by exact_mod_cast hkd
      linarith
    have rr := hy₄ y a₄ R hR n n' hn hn' _ _ _ _ (G.coreOffsets Y (N - R.frameReach - 1) j.1) Y Y'
      (dOf j) (kOf j) Sa Sb Sa' Sb' (hnon j) (by omega) hdr hkr tp
    have rr' : |(Real.log (G.settingOf (G.familyOf (g.extendFirst (Function.update τ j s)))).mass -
        Real.log (G.settingOf (G.familyOf (g.extendFirst (Function.update τ j (Sum.inl ()))))).mass) -
        (Real.log (G'.settingOf (G'.familyOf (g.extendSecond (Function.update τ j s)))).mass -
        Real.log (G'.settingOf (G'.familyOf (g.extendSecond (Function.update τ j (Sum.inl ()))))).mass)| ≤
        eOf j := by
      rw [heOf, hpOf]
      exact rr
    have key := mul_le_exp_mul_of_abs_log_sub Pa Pb Pa' Pb' rr'
    rw [Wa, Wb, Wa', Wb']
    exact key
  have hbmain : ∀ j : G.InnerSpin Y (N - R.frameReach - 1) A,
      2 * (G.spinActivity T.gasRate j.1 + G'.spinActivity T.gasRate (g.spinEquiv j).1) ≤ bOf j ∨
      (1 ≤ Real.exp (eOf j) ∧ G.spinActivity T.gasRate j.1 ≤ 1 ∧
        G'.spinActivity T.gasRate (g.spinEquiv j).1 ≤ 1 ∧
        8 * (Real.exp (eOf j) - 1) *
          max (G.spinActivity T.gasRate j.1) (G'.spinActivity T.gasRate (g.spinEquiv j).1) ≤ bOf j ∧
        ∀ (τ : g.Config) (s : G.SpinValue j.1),
          (innerConstraint G Y (N - R.frameReach - 1) A).IsAdmissible (Function.update τ j s) →
          G.weight (g.extendFirst (Function.update τ j s)) *
              G'.weight (g.extendSecond (Function.update τ j (Sum.inl ()))) ≤
            Real.exp (eOf j) * (G.weight (g.extendFirst (Function.update τ j (Sum.inl ()))) *
              G'.weight (g.extendSecond (Function.update τ j s))) ∧
          G'.weight (g.extendSecond (Function.update τ j s)) *
              G.weight (g.extendFirst (Function.update τ j (Sum.inl ()))) ≤
            Real.exp (eOf j) * (G'.weight (g.extendSecond (Function.update τ j (Sum.inl ()))) *
              G.weight (g.extendFirst (Function.update τ j s)))) := by
    intro j
    rw [hpr j]
    have hz := hp0 j.1
    by_cases hbig : L₀ ≤ lOf j
    · have hbj : bOf j = 32 * eOf j * G.spinActivity T.gasRate j.1 := by
        rw [hbOf, if_pos hbig]
      by_cases hsm : eOf j ≤ 1 / 2
      · right
        refine ⟨Real.one_le_exp (he0 j), hp1 j.1, hp1 j.1, ?_, hlogs j hbig⟩
        rw [max_self, hbj]
        exact eight_mul_sub_one_le hz (he0 j) (exp_sub_one_le_two_mul (he0 j) hsm)
      · left
        rw [hbj]
        exact two_mul_add_le hz (not_le.mp hsm)
    · left
      have hbj : bOf j = 4 * G.spinActivity T.gasRate j.1 := by
        rw [hbOf, if_neg hbig]
      rw [hbj]
      linarith
  refine ⟨g, fun τ hτ => extendSecond_admissible g (innerAdmissible_of_extendFirst g hτ),
    fun F F' Kc a ha hF hF' hnear hab => ?_⟩
  have main := abs_expectation_sub_le hCmp g w₁ w₂ s₁ s₂ ha hF hF' hnear hab bOf
    (fun j => Real.exp (eOf j)) hb0 hbmain
  have hoff₁ : ∀ i ∈ Finset.univ.filter (fun i => (∀ j : G.InnerSpin Y (N - R.frameReach - 1) A, j.1 ≠ i) ∧
      i ∉ touchingSpins G A), ∃ y ∈ i.1.core, N - R.frameReach ≤ _root_.YangMills.Construction.TorusFields.supDist y Y := by
    intro i hi
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hi).2
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hin : G.IsInnerSpin Y (N - R.frameReach - 1) A i := by
      refine ⟨fun ht => h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩), fun y hy => ?_⟩
      obtain ⟨g', hg', e⟩ := exists_offset_of_supDist_le y Y (N - R.frameReach - 1)
        (by have := hcon y hy; omega)
      exact ⟨g', hg', e⟩
    exact h1 ⟨i, hin⟩ rfl
  have hoff₂ : ∀ i ∈ Finset.univ.filter
      (fun i => (∀ j : G.InnerSpin Y (N - R.frameReach - 1) A, (g.spinEquiv j).1 ≠ i) ∧
      i ∉ touchingSpins G' A'), ∃ y ∈ i.1.core, N - R.frameReach ≤ _root_.YangMills.Construction.TorusFields.supDist y Y' := by
    intro i hi
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hi).2
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hin : G'.IsInnerSpin Y' (N - R.frameReach - 1) A' i := by
      refine ⟨fun ht => h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩), fun y hy => ?_⟩
      obtain ⟨g', hg', e⟩ := exists_offset_of_supDist_le y Y' (N - R.frameReach - 1)
        (by have := hcon y hy; omega)
      exact ⟨g', hg', e⟩
    exact h1 (g.spinEquiv.symm ⟨i, hin⟩) (by rw [g.spinEquiv.apply_symm_apply])
  have hκ : 0 < R.params.rt / 2 ^ 8 := by positivity
  have S₁ := hGS R n G T.gasRate (R.params.rt / 2 ^ 8)
    (Real.exp (-(3 * (R.params.rt / 2 ^ 8) * ((N - R.frameReach : ℕ) : ℝ)))) Y _
    (fun i => G.coreWeightFrom Y i * G.spinActivity T.gasRate i) hfit hch hcf (hy1R ▸ hx) hκ (Real.exp_pos _).le
    (fun i hi => weighted_activity_le_of_far Y i hrtR0 (hoff₁ i hi))
  have S₂ := hGS R n' G' T.gasRate (R.params.rt / 2 ^ 8)
    (Real.exp (-(3 * (R.params.rt / 2 ^ 8) * ((N - R.frameReach : ℕ) : ℝ)))) Y' _
    (fun i => G'.coreWeightFrom Y' i * G'.spinActivity T.gasRate i) hfit hch hcf (hy1R ▸ hx) hκ
    (Real.exp_pos _).le
    (fun i hi => weighted_activity_le_of_far Y' i hrtR0 (hoff₂ i hi))
  have hbigterm : ∀ j : G.InnerSpin Y (N - R.frameReach - 1) A,
      ∃ y' ∈ j.1.1.core, farthestCoreDist G Y j.1 = _root_.YangMills.Construction.TorusFields.supDist y' Y := by
    intro j
    obtain ⟨y', hy', e⟩ := Finset.exists_mem_eq_sup j.1.1.core (core_nonempty G j.1) fun y => _root_.YangMills.Construction.TorusFields.supDist y Y
    exact ⟨y', hy', e⟩
  set B₃ : ℝ := 4 * Real.exp (-(2 * (R.params.rt / 2 ^ 8) * ((N - R.frameReach : ℕ) : ℝ))) with hB₃
  have S₃ : ∑ j, G.coreWeightFrom Y j.1 * bOf j ≤
      B₃ * Real.exp (-(8 * T.gasRate * R.coupling)) * (2 / (1 - Real.exp (-(R.params.rt / 2 ^ 8 / 4)))) ^ 4 := by
    let t : G.GasSpin → ℝ := fun i =>
      if h : G.IsInnerSpin Y (N - R.frameReach - 1) A i then G.coreWeightFrom Y i * bOf ⟨i, h⟩ else 0
    have hsum : ∑ j, G.coreWeightFrom Y j.1 * bOf j =
        ∑ i ∈ (Finset.univ : Finset (G.InnerSpin Y (N - R.frameReach - 1) A)).image Subtype.val, t i := by
      rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [t]
      rw [dif_pos j.2]
    rw [hsum]
    refine hGS R n G T.gasRate (R.params.rt / 2 ^ 8) B₃ Y _ t hfit hch hcf (hy1R ▸ hx) hκ (by positivity)
      fun i hi => ?_
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    have ht : t j.1 = G.coreWeightFrom Y j.1 * bOf j := by
      simp only [t]
      rw [dif_pos j.2]
    rw [ht]
    obtain ⟨y', hy', e⟩ := hbigterm j
    have hfj := hfar j
    have hu0 : 0 ≤ G.spinActivity T.gasRate j.1 * (j.1.1.core.card : ℝ) ^ 4 *
        Real.exp (2 * R.params.rt * (j.1.1.coreDiam : ℝ)) *
        Real.exp (-(R.params.rt / 2 ^ 8 * (setGap {Y} j.1.1.core : ℝ))) := by
      have := hp0 j.1
      positivity
    have hs0 : 0 ≤ G.coreWeightFrom Y j.1 := (coreWeightFrom_pos G Y j.1).le
    by_cases hbig : L₀ ≤ lOf j
    · have hbj : bOf j = 32 * eOf j * G.spinActivity T.gasRate j.1 := by
        rw [hbOf, if_pos hbig]
      have hsm := logRatioBound_le T hrt (l := lOf j) (k := kOf j) (d := dOf j) (p := pOf j) (hp0' j)
        (hdOf j) (hkOf j) (hLc (lOf j) (by omega))
      rw [← heOf, ← hrtR] at hsm
      have hA : 0 < Real.exp (-(2 * (R.params.rt / 2 ^ 8) * (lOf j : ℝ))) := Real.exp_pos _
      have h1 : 32 * eOf j ≤
          2 * ((j.1.1.core.card : ℝ) * Real.exp (-(2 * (R.params.rt / 2 ^ 8) * (lOf j : ℝ)))) := by
        have h2 : pOf j * Real.exp (-(2 * (R.params.rt / 2 ^ 8) * (lOf j : ℝ))) ≤
            (j.1.1.core.card : ℝ) * Real.exp (-(2 * (R.params.rt / 2 ^ 8) * (lOf j : ℝ))) := by
          rw [hpOf]
          exact mul_le_mul_of_nonneg_right (hcard j) hA.le
        have h3 : 16 * eOf j ≤ pOf j * Real.exp (-(2 * (R.params.rt / 2 ^ 8) * (lOf j : ℝ))) := hsm
        linarith
      have h4 := weighted_scaled_activity_le (G := G) Y j.1 (c := T.gasRate) (D := farthestCoreDist G Y j.1)
        (l := lOf j) (N₂ := N - R.frameReach) hrtR0 ⟨y', hy', by rw [e]⟩ (by have := hlOf j; omega)
      have h5 : G.coreWeightFrom Y j.1 * bOf j ≤ G.coreWeightFrom Y j.1 *
          (2 * ((j.1.1.core.card : ℝ) * Real.exp (-(2 * (R.params.rt / 2 ^ 8) * (lOf j : ℝ)))) *
            G.spinActivity T.gasRate j.1) := by
        rw [hbj]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (hp0 j.1)) hs0
      refine h5.trans (h4.trans ?_)
      rw [hB₃]
      exact two_mul_le_four_mul (Real.exp_pos _).le hu0
    · have hbj : bOf j = 4 * G.spinActivity T.gasRate j.1 := by
        rw [hbOf, if_neg hbig]
      have hlt : lOf j < L₀ := not_le.mp hbig
      have hD : (N - R.frameReach) - L₀ ≤ _root_.YangMills.Construction.TorusFields.supDist y' Y := by
        rw [← e]
        have := hlOf j
        omega
      have h4 := weighted_activity_le_of_far (G := G) Y j.1 (c := T.gasRate) hrtR0 ⟨y', hy', hD⟩
      have h3D : 2 * (N - R.frameReach) ≤ 3 * ((N - R.frameReach) - L₀) := by omega
      have h3D' : 2 * ((N - R.frameReach : ℕ) : ℝ) ≤ 3 * (((N - R.frameReach) - L₀ : ℕ) : ℝ) := by
        exact_mod_cast h3D
      have hexp : Real.exp (-(3 * (R.params.rt / 2 ^ 8) * (((N - R.frameReach) - L₀ : ℕ) : ℝ))) ≤
          Real.exp (-(2 * (R.params.rt / 2 ^ 8) * ((N - R.frameReach : ℕ) : ℝ))) :=
        exp_neg_three_le_exp_neg_two hκ.le h3D'
      rw [hbj, hB₃]
      have h6 : G.coreWeightFrom Y j.1 * G.spinActivity T.gasRate j.1 ≤
          Real.exp (-(2 * (R.params.rt / 2 ^ 8) * ((N - R.frameReach : ℕ) : ℝ))) *
          (G.spinActivity T.gasRate j.1 * (j.1.1.core.card : ℝ) ^ 4 *
            Real.exp (2 * R.params.rt * (j.1.1.coreDiam : ℝ))) *
          Real.exp (-(R.params.rt / 2 ^ 8 * (setGap {Y} j.1.1.core : ℝ))) := by
        refine h4.trans ?_
        have := mul_le_mul_of_nonneg_right hexp hu0
        calc _ = Real.exp (-(3 * (R.params.rt / 2 ^ 8) * (((N - R.frameReach) - L₀ : ℕ) : ℝ))) *
              (G.spinActivity T.gasRate j.1 * (j.1.1.core.card : ℝ) ^ 4 *
                Real.exp (2 * R.params.rt * (j.1.1.coreDiam : ℝ)) *
              Real.exp (-(R.params.rt / 2 ^ 8 * (setGap {Y} j.1.1.core : ℝ)))) := by ring
          _ ≤ _ := this
          _ = _ := by ring
      exact mul_four_le h6
  rw [hrtR] at S₁ S₂ S₃
  have hE₃ : Real.exp (-(3 * (T.rt / 2 ^ 8) * ((N - R.frameReach : ℕ) : ℝ))) ≤
      Real.exp (-(2 * (T.rt / 2 ^ 8) * ((N - R.frameReach : ℕ) : ℝ))) :=
    exp_neg_three_le_exp_neg_two hρ.le (by
      have : (0 : ℝ) ≤ ((N - R.frameReach : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith)
  have hP : Real.exp (-(3 * (T.rt / 2 ^ 8) * ((N - R.frameReach : ℕ) : ℝ))) *
        Real.exp (-(8 * T.gasRate * R.coupling)) * (2 / (1 - Real.exp (-(T.rt / 2 ^ 8 / 4)))) ^ 4 ≤
      Real.exp (-(2 * (T.rt / 2 ^ 8) * ((N - R.frameReach : ℕ) : ℝ))) *
        Real.exp (-(8 * T.gasRate * R.coupling)) * (2 / (1 - Real.exp (-(T.rt / 2 ^ 8 / 4)))) ^ 4 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE₃ (Real.exp_pos _).le) hW₁0
  have hB₃' : B₃ = 4 * Real.exp (-(2 * (T.rt / 2 ^ 8) * ((N - R.frameReach : ℕ) : ℝ))) := by
    rw [hB₃, hrtR]
  rw [hB₃'] at S₃
  have hS₁ := S₁.trans hP
  have hS₂ := S₂.trans hP
  have S₄ : ∑ j : G.InnerSpin Y (N - R.frameReach - 1) A, G.spinActivity T.gasRate j.1 ≤
      Real.exp (T.rt / 2 ^ 8 * (N : ℝ)) * Real.exp (-(8 * T.gasRate * R.coupling)) *
        (2 / (1 - Real.exp (-(T.rt / 2 ^ 8 / 4)))) ^ 4 := by
    let t : G.GasSpin → ℝ := fun i =>
      if h : G.IsInnerSpin Y (N - R.frameReach - 1) A i then G.spinActivity T.gasRate i else 0
    have hsum : ∑ j : G.InnerSpin Y (N - R.frameReach - 1) A, G.spinActivity T.gasRate j.1 =
        ∑ i ∈ (Finset.univ : Finset (G.InnerSpin Y (N - R.frameReach - 1) A)).image Subtype.val, t i := by
      rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [t]
      rw [dif_pos j.2]
    rw [hsum]
    suffices hterm : ∀ i ∈ (Finset.univ : Finset (G.InnerSpin Y (N - R.frameReach - 1) A)).image Subtype.val,
        t i ≤ Real.exp (T.rt / 2 ^ 8 * (N : ℝ)) * (G.spinActivity T.gasRate i * (i.1.core.card : ℝ) ^ 4 *
          Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ))) *
          Real.exp (-(R.params.rt / 2 ^ 8 * (setGap {Y} i.1.core : ℝ))) by
      have key := hGS R n G T.gasRate (R.params.rt / 2 ^ 8) (Real.exp (T.rt / 2 ^ 8 * (N : ℝ))) Y _ t hfit
        hch hcf (hy1R ▸ hx) hκ (Real.exp_pos _).le hterm
      rw [hrtR] at key
      exact key
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    have ht : t j.1 = G.spinActivity T.gasRate j.1 := by
      simp only [t]
      rw [dif_pos j.2]
    rw [ht, hrtR]
    obtain ⟨y', hy', e⟩ := exists_supDist_eq_setGap Y (core_nonempty G j.1)
    have hgap : (setGap {Y} j.1.1.core : ℝ) ≤ N := by
      have h1 : _root_.YangMills.Construction.TorusFields.supDist y' Y ≤ farthestCoreDist G Y j.1 := Finset.le_sup (f := fun y => _root_.YangMills.Construction.TorusFields.supDist y Y) hy'
      have h2 := hfar j
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm, e] at h1
      exact_mod_cast (by omega : setGap {Y} j.1.1.core ≤ N)
    have hc1 : (1 : ℝ) ≤ (j.1.1.core.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (core_nonempty G j.1)
    have hc4 : (1 : ℝ) ≤ (j.1.1.core.card : ℝ) ^ 4 := one_le_pow₀ hc1
    have hd0 : (0 : ℝ) ≤ 2 * T.rt * (j.1.1.coreDiam : ℝ) := by positivity
    have hed : (1 : ℝ) ≤ Real.exp (2 * T.rt * (j.1.1.coreDiam : ℝ)) := Real.one_le_exp hd0
    have hp := hp0 j.1
    have h1 : (1 : ℝ) ≤ Real.exp (T.rt / 2 ^ 8 * (N : ℝ)) *
        Real.exp (-(T.rt / 2 ^ 8 * (setGap {Y} j.1.1.core : ℝ))) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      nlinarith
    have h2 : (1 : ℝ) ≤ (j.1.1.core.card : ℝ) ^ 4 * Real.exp (2 * T.rt * (j.1.1.coreDiam : ℝ)) :=
      one_le_mul_of_one_le_of_one_le hc4 hed
    have h3 := one_le_mul_of_one_le_of_one_le h1 h2
    calc G.spinActivity T.gasRate j.1 ≤ G.spinActivity T.gasRate j.1 * _ := le_mul_of_one_le_right hp h3
      _ = _ := by ring
  have hpr' : ∑ j : G.InnerSpin Y (N - R.frameReach - 1) A, a * G'.spinActivity T.gasRate (g.spinEquiv j).1 =
      a * ∑ j : G.InnerSpin Y (N - R.frameReach - 1) A, G.spinActivity T.gasRate j.1 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hpr j]
  rw [hpr'] at main
  have hKc := hF.nonneg
  refine main.trans (le_trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hS₁ (by norm_num)) (mul_le_mul_of_nonneg_left hS₂ (by norm_num)))
    (mul_le_mul_of_nonneg_left S₃ (by norm_num))) hKc) (mul_le_mul_of_nonneg_left S₄ ha)) ?_)
  refine le_of_eq ?_
  unfold blockSumConstant
  ring
end ResponseInTheExpansion
end YangMills.Construction
end
