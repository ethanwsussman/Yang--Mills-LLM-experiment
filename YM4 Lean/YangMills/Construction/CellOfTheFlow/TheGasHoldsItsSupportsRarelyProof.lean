import YangMills.Construction.CellOfTheFlow.TheGasHoldsItsSupportsRarely
import YangMills.Construction.ClusterExpansionOfAStep.GasIsAWeight
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace YangMills.Construction.CellWindows
open Dobrushin StepGas TorusLumps RenormalizationStepParameters StepSettings
section Configurations
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
private def occupiedOn (A : PairConstraint S) (J : Finset I) : Set (∀ i, S i) := {ω | ∀ i ∈ J, ω i ≠ A.vacant i}
omit [Fintype I] in
private theorem measurableSet_occupiedOn {A : PairConstraint S} {μ : ∀ i, Measure (S i)} {G : (∀ i, S i) → ℝ}
    {z : I → ℝ} (h : A.IsActivityBounded μ G z) (J : Finset I) : MeasurableSet (occupiedOn A J) := by
  have : occupiedOn A J = ⋂ i ∈ J, (fun ω : ∀ i, S i => ω i) ⁻¹' {A.vacant i}ᶜ := by
    ext ω
    simp [occupiedOn]
  rw [this]
  exact Finset.measurableSet_biInter J fun i _ => (measurable_pi_apply i) (h.measurableSet_vacant i).compl
omit [Fintype I] [∀ i, MeasurableSpace (S i)] in
private theorem isAdmissible_update_vacant (A : PairConstraint S) {ω : ∀ i, S i} (i : I) (hω : A.IsAdmissible ω) :
    A.IsAdmissible (Function.update ω i (A.vacant i)) := by
  intro a b hab
  by_cases ha : a = i
  · subst ha
    rw [Function.update_self]
    exact A.vacant_compatible _ _ _
  · by_cases hb : b = i
    · subst hb
      rw [Function.update_self]
      exact A.compatible_symm _ _ _ _ (A.vacant_compatible _ _ _)
    · rw [Function.update_of_ne ha, Function.update_of_ne hb]
      exact hω a b (by simpa using hab)
omit [Fintype I] in
private theorem lintegral_compl_vacant_update_le {A : PairConstraint S} {μ : ∀ i, Measure (S i)}
    {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded μ G z) (i : I) (ω : ∀ i, S i) :
    ∫⁻ s in {A.vacant i}ᶜ, A.weightDensity G (Function.update ω i s) ∂μ i ≤
      ENNReal.ofReal (z i) * A.weightDensity G (Function.update ω i (A.vacant i)) := by
  classical
  by_cases hω : A.IsAdmissible (Function.update ω i (A.vacant i))
  · have := h.lintegral_compl_vacant_le i _ hω
    simpa only [Function.update_idem] using this
  · have hzero : ∀ s, A.weightDensity G (Function.update ω i s) = 0 := by
      intro s
      unfold PairConstraint.weightDensity
      rw [if_neg]
      intro hs
      apply hω
      have := isAdmissible_update_vacant A i hs
      simpa only [Function.update_idem] using this
    simp [hzero]
omit [Fintype I] in
private theorem weightDensity_vacant_le_lintegral {A : PairConstraint S} {μ : ∀ i, Measure (S i)}
    {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded μ G z) (i : I) (ω : ∀ i, S i) :
    A.weightDensity G (Function.update ω i (A.vacant i)) ≤ ∫⁻ s, A.weightDensity G (Function.update ω i s) ∂μ i := by
  calc A.weightDensity G (Function.update ω i (A.vacant i))
      = ∫⁻ _ in {A.vacant i}, A.weightDensity G (Function.update ω i (A.vacant i)) ∂μ i := by
        rw [setLIntegral_const, h.measure_vacant i, mul_one]
    _ = ∫⁻ s in {A.vacant i}, A.weightDensity G (Function.update ω i s) ∂μ i := by
        refine setLIntegral_congr_fun (h.measurableSet_vacant i) ?_
        intro s hs
        rw [Set.mem_singleton_iff.mp hs]
    _ ≤ ∫⁻ s, A.weightDensity G (Function.update ω i s) ∂μ i := setLIntegral_le_lintegral _ _
private theorem lintegral_occupiedOn_insert_le {A : PairConstraint S} {μ : ∀ i, Measure (S i)}
    [∀ i, SigmaFinite (μ i)] {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded μ G z) {J : Finset I}
    {i : I} (hi : i ∉ J) :
    ∫⁻ ω in occupiedOn A (insert i J), A.weightDensity G ω ∂Measure.pi μ ≤
      ENNReal.ofReal (z i) * ∫⁻ ω in occupiedOn A J, A.weightDensity G ω ∂Measure.pi μ := by
  classical
  have hd := h.measurable_weightDensity
  have hmJ := measurableSet_occupiedOn h J
  have hmI := measurableSet_occupiedOn h (insert i J)
  have hc : ENNReal.ofReal (z i) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← lintegral_indicator hmI, ← lintegral_indicator hmJ, ← lintegral_const_mul' _ _ hc]
  refine lintegral_le_of_lmarginal_le {i} (hd.indicator hmI) ((hd.indicator hmJ).const_mul _) ?_
  intro ω
  rw [lmarginal_singleton, lmarginal_singleton]
  beta_reduce
  rw [lintegral_const_mul' _ _ hc]
  have hJ : ∀ s, (Function.update ω i s ∈ occupiedOn A J ↔ ω ∈ occupiedOn A J) := by
    intro s
    refine forall₂_congr fun j hj => ?_
    have hne : j ≠ i := fun e => hi (e ▸ hj)
    rw [Function.update_of_ne hne]
  by_cases hω : ω ∈ occupiedOn A J
  · have hF : (fun s => (occupiedOn A (insert i J)).indicator (A.weightDensity G) (Function.update ω i s)) =
        ({A.vacant i}ᶜ : Set (S i)).indicator fun s => A.weightDensity G (Function.update ω i s) := by
      funext s
      by_cases hs : s = A.vacant i
      · subst hs
        have h1 : A.vacant i ∉ ({A.vacant i}ᶜ : Set (S i)) := by simp
        have h2 : Function.update ω i (A.vacant i) ∉ occupiedOn A (insert i J) := fun hmem =>
          hmem i (Finset.mem_insert_self _ _) (Function.update_self ..)
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      · rw [Set.indicator_of_mem (show s ∈ ({A.vacant i}ᶜ : Set (S i)) from hs), Set.indicator_of_mem]
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rwa [Function.update_self]
        · exact (hJ s).mpr hω j hj
    have hH : (fun s => (occupiedOn A J).indicator (A.weightDensity G) (Function.update ω i s)) =
        fun s => A.weightDensity G (Function.update ω i s) := by
      funext s
      exact Set.indicator_of_mem ((hJ s).mpr hω) _
    rw [hF, hH, lintegral_indicator (h.measurableSet_vacant i).compl]
    exact (lintegral_compl_vacant_update_le h i ω).trans
      (by gcongr; exact weightDensity_vacant_le_lintegral h i ω)
  · have hF : (fun s => (occupiedOn A (insert i J)).indicator (A.weightDensity G) (Function.update ω i s)) =
        fun _ => 0 := by
      funext s
      refine Set.indicator_of_notMem (fun hmem => hω ?_) _
      exact (hJ s).mp fun j hj => hmem j (Finset.mem_insert_of_mem hj)
    rw [hF]
    simp
private theorem lintegral_occupiedOn_le {A : PairConstraint S} {μ : ∀ i, Measure (S i)} [∀ i, SigmaFinite (μ i)]
    {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded μ G z) (J : Finset I) :
    ∫⁻ ω in occupiedOn A J, A.weightDensity G ω ∂Measure.pi μ ≤
      ENNReal.ofReal (∏ i ∈ J, z i) * ∫⁻ ω, A.weightDensity G ω ∂Measure.pi μ := by
  induction J using Finset.induction_on with
  | empty =>
    simp [occupiedOn]
  | insert i J hi ih =>
    rw [Finset.prod_insert hi, ENNReal.ofReal_mul (h.activity_nonneg i), mul_assoc]
    exact (lintegral_occupiedOn_insert_le h hi).trans (by gcongr)
private theorem lintegral_weightDensity_ne_zero {A : PairConstraint S} {μ : ∀ i, Measure (S i)}
    [∀ i, SigmaFinite (μ i)] {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded μ G z) :
    ∫⁻ ω, A.weightDensity G ω ∂Measure.pi μ ≠ 0 := by
  classical
  have hadm : A.IsAdmissible A.vacant := fun a b _ => A.vacant_compatible _ _ _
  have hpos : A.weightDensity G A.vacant ≠ 0 := by
    unfold PairConstraint.weightDensity
    rw [if_pos hadm]
    exact (ENNReal.ofReal_pos.mpr (h.pos_of_admissible _ hadm)).ne'
  have hset : MeasurableSet (Set.pi Set.univ fun i => ({A.vacant i} : Set (S i))) :=
    MeasurableSet.univ_pi fun i => h.measurableSet_vacant i
  have hmass : Measure.pi μ (Set.pi Set.univ fun i => ({A.vacant i} : Set (S i))) = 1 := by
    rw [Measure.pi_pi]
    simp [h.measure_vacant]
  have hge : A.weightDensity G A.vacant ≤ ∫⁻ ω, A.weightDensity G ω ∂Measure.pi μ := by
    calc A.weightDensity G A.vacant
        = ∫⁻ _ in Set.pi Set.univ (fun i => ({A.vacant i} : Set (S i))), A.weightDensity G A.vacant
            ∂Measure.pi μ := by
          rw [setLIntegral_const, hmass, mul_one]
      _ = ∫⁻ ω in Set.pi Set.univ (fun i => ({A.vacant i} : Set (S i))), A.weightDensity G ω ∂Measure.pi μ := by
          refine setLIntegral_congr_fun hset ?_
          intro ω hω
          have : ω = A.vacant := funext fun i => by simpa using hω i (Set.mem_univ i)
          rw [this]
      _ ≤ _ := setLIntegral_le_lintegral _ _
  exact fun h0 => hpos (le_antisymm (h0 ▸ hge) bot_le)
private theorem gibbsLaw_occupiedOn_le {A : PairConstraint S} {μ : ∀ i, Measure (S i)} [∀ i, SigmaFinite (μ i)]
    {G : (∀ i, S i) → ℝ} {z : I → ℝ} (h : A.IsActivityBounded μ G z) (J : Finset I) :
    A.gibbsLaw μ G (occupiedOn A J) ≤ ENNReal.ofReal (∏ i ∈ J, z i) := by
  unfold PairConstraint.gibbsLaw
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ (measurableSet_occupiedOn h J)]
  by_cases htop : ∫⁻ ω, A.weightDensity G ω ∂Measure.pi μ = ⊤
  · rw [htop]
    simp
  · calc (∫⁻ ω, A.weightDensity G ω ∂Measure.pi μ)⁻¹ * ∫⁻ ω in occupiedOn A J, A.weightDensity G ω ∂Measure.pi μ
        ≤ (∫⁻ ω, A.weightDensity G ω ∂Measure.pi μ)⁻¹ *
            (ENNReal.ofReal (∏ i ∈ J, z i) * ∫⁻ ω, A.weightDensity G ω ∂Measure.pi μ) := by
          gcongr
          exact lintegral_occupiedOn_le h J
      _ = ENNReal.ofReal (∏ i ∈ J, z i) := by
          rw [mul_comm (ENNReal.ofReal _), ← mul_assoc,
            ENNReal.inv_mul_cancel (lintegral_weightDensity_ne_zero h) htop, one_mul]
end Configurations
theorem supportsPresentRarely_of_gasIsActivityBounded (hw : ClusterExpansionOfAStep.GasIsActivityBounded) :
    supportsPresentRarelyStatement := by
  classical
  obtain ⟨r₀, hr, H⟩ := hw
  intro a _
  refine ⟨0, r₀, hr, ?_⟩
  intro L _ _ T _ _ hD hT
  obtain ⟨y₀, hy⟩ := H T hD hT
  refine ⟨y₀, fun y hy₀ _ _ R hR hx μ _ G Θ hG => ?_⟩
  by_cases hs : ∀ θ ∈ Θ, G.IsGasSupport θ
  · have hW := hy y hy₀ R hR hx μ G hG fun j => j.1.Touches ∅
    set J : Finset G.GasSpin := Finset.univ.filter fun i => i.1 ∈ Θ with hJ
    have hΘ : Θ = J.image Subtype.val := by
      ext θ
      constructor
      · intro hθ
        exact Finset.mem_image.mpr ⟨⟨θ, hs θ hθ⟩, by simp [hJ, hθ], rfl⟩
      · intro hθ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hθ
        exact (Finset.mem_filter.mp hi).2
    have hprod : ∏ θ ∈ Θ, clusterWeight R.params.side T.gasRate R.coupling R.range θ =
        ∏ i ∈ J, G.spinActivity T.gasRate i := by
      conv_lhs => rw [hΘ]
      exact Finset.prod_image fun i _ j _ e => Subtype.ext e
    have hsub : supportsPresent G Θ ⊆ occupiedOn G.pairConstraint J := by
      intro ω hω i hi
      obtain ⟨i', hi', hne⟩ := hω i.1 (Finset.mem_filter.mp hi).2
      have : i' = i := Subtype.ext hi'
      exact this ▸ hne
    rw [hprod]
    exact (measure_mono hsub).trans (gibbsLaw_occupiedOn_le hW J)
  · have hemp : supportsPresent G Θ = ∅ := by
      push Not at hs
      obtain ⟨θ, hθ, hn⟩ := hs
      ext ω
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hω
      obtain ⟨i, hi, -⟩ := hω θ hθ
      exact hn (hi ▸ i.2)
    rw [hemp, measure_empty]
    exact zero_le
end YangMills.Construction.CellWindows
end
