import YangMills.Construction.ClusterExpansionOfAStep.CasesOfAFamily
import YangMills.Construction.ClusterExpansionOfAStep.CasesOfAGroundAreFamilies
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace YangMills.Construction.ClusterExpansionOfAStep
namespace GasExpansion
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
open Classical in
theorem referenceMeasure_eq_withNoneMeasure (G : StepGas.GasGround R n) (A : Finset (TorusFields.TorusSite n))
    (i : G.GasSpin) :
    G.referenceMeasure A i =
      TorusLumps.withNoneMeasure (if i.1.Touches A then 0 else G.spinStateMeasure i) := by
  unfold StepGas.GasGround.referenceMeasure StepGas.GasGround.referenceMeasureOff
  by_cases h : i.1.Touches A
  · simp [h, TorusLumps.withNoneMeasure]
  · simp [h]
instance (G : StepGas.GasGround R n) (A : Finset (TorusFields.TorusSite n)) (i : G.GasSpin) :
    SigmaFinite (open Classical in if i.1.Touches A then 0 else G.spinStateMeasure i) := by
  classical
  split_ifs <;> infer_instance
instance (G : StepGas.GasGround R n) (A : Finset (TorusFields.TorusSite n)) (i : G.GasSpin) :
    SigmaFinite (TorusLumps.withNoneMeasure (open Classical in
      if i.1.Touches A then (0 : Measure (G.SpinState i)) else G.spinStateMeasure i)) :=
  StepGas.sigmaFinite_withNoneMeasure _
theorem measure_pi_eq_zero_of_eq_zero {I : Type} [Fintype I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
    (μ : ∀ i, Measure (S i)) [∀ i, SigmaFinite (μ i)] (i : I) (h : μ i = 0) : Measure.pi μ = 0 := by
  classical
  rw [← Measure.measure_univ_eq_zero]
  have : (Set.univ : Set (∀ i, S i)) = Set.pi Set.univ fun _ => Set.univ := by simp
  rw [this, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])
theorem not_isAdmissible_valuesOn {G : StepGas.GasGround R n} {Γ : Finset G.GasSpin}
    (h : ¬ G.IsPairwiseFarApart Γ) (τ : ∀ i : Γ, G.SpinState i) :
    ¬ G.pairConstraint.IsAdmissible (TorusLumps.valuesOn Γ τ) := by
  classical
  intro ha
  apply h
  intro i hi j hj hij
  have := ha i j hij
  rcases this with e | e | e
  · simp [TorusLumps.valuesOn, hi] at e
  · simp [TorusLumps.valuesOn, hj] at e
  · exact e
end GasExpansion
open GasExpansion in
theorem caseMassEqGasMass_of_families (hp : TorusLumps.LintegralPiWithNone)
    (hc : GroundCasesAreFamilies) (hf : FamilyCaseSumEqIntegral) :
    CaseMassEqGasMass := by
  classical
  intro T hT
  obtain ⟨y₁, hc⟩ := hc T hT
  obtain ⟨y₂, hf⟩ := hf T hT
  refine ⟨max y₁ y₂, fun y hy R hR hx' n _ G hG A F hF hB => ?_⟩
  obtain ⟨c1, c2, c3, c4⟩ := hc y ((le_max_left _ _).trans hy) R hR hx' n G hG
  have fam := hf y ((le_max_right _ _).trans hy) R hR hx' n G hG F hF hB
  set P := ENNReal.ofReal (R.functional (n * R.params.side) (TorusFields.trivialField (n * R.params.side))) *
    ENNReal.ofReal (∏ X ∈ TorusLumps.chainComponents R.nextRange G.state.1,
      StepSettings.coarseFactor G.coarse G.state X) with hP
  set S : Finset (Finset G.GasSpin) :=
    Finset.univ.filter fun Γ => G.IsPairwiseFarApart Γ ∧ ∀ i ∈ Γ, ¬ i.1.Touches A with hS
  have gas : G.gasMass A F = ∑ Γ ∈ S, ∫⁻ τ, G.gasIntegrand F (TorusLumps.valuesOn Γ τ)
      ∂Measure.pi (fun i : Γ => G.spinStateMeasure i) := by
    unfold StepGas.GasGround.gasMass
    have e : Measure.pi (G.referenceMeasure A) = Measure.pi fun i =>
        TorusLumps.withNoneMeasure
          (if i.1.Touches A then (0 : Measure (G.SpinState i)) else G.spinStateMeasure i) := by
      congr 1
      funext i
      exact referenceMeasure_eq_withNoneMeasure G A i
    rw [e, hp G.GasSpin G.SpinState _ (G.gasIntegrand F) hB]
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun Γ _ => ?_
    by_cases hΓ : G.IsPairwiseFarApart Γ
    · by_cases ht : ∀ i ∈ Γ, ¬ i.1.Touches A
      · rw [if_pos ⟨hΓ, ht⟩]
        have : (fun i : Γ => (if i.1.1.Touches A then (0 : Measure (G.SpinState i.1))
            else G.spinStateMeasure i.1)) = fun i : Γ => G.spinStateMeasure i.1 := by
          funext i
          rw [if_neg (ht i.1 i.2)]
        simp only [this]
      · rw [if_neg fun h => ht h.2]
        push Not at ht
        obtain ⟨i, hi, hti⟩ := ht
        rw [measure_pi_eq_zero_of_eq_zero _ (⟨i, hi⟩ : Γ) (by simp [hti])]
        simp
    · rw [if_neg fun h => hΓ h.1]
      have : ∀ τ : ∀ i : Γ, G.SpinState i, G.gasIntegrand F (TorusLumps.valuesOn Γ τ) = 0 := fun τ => by
        unfold StepGas.GasGround.gasIntegrand
        rw [if_neg (not_isAdmissible_valuesOn hΓ τ)]
      simp [this]
  have cases : G.caseMass A F = ∑ Γ ∈ S, ∑ b : StepCosts.BaseChoice R.params.side n,
      G.caseIntegral F (G.familyBadBonds Γ) (G.familySites Γ) b := by
    unfold StepGas.GasGround.caseMass
    rw [← Finset.sum_product']
    symm
    refine Finset.sum_of_injOn (fun Γ => (G.familyBadBonds Γ, G.familySites Γ)) ?_ ?_ ?_ ?_
    · intro Γ hΓ Γ' hΓ' e
      have h1 := (Finset.mem_filter.mp hΓ).2.1
      have h2 := (Finset.mem_filter.mp hΓ').2.1
      exact c2 Γ Γ' h1 h2 (congrArg Prod.fst e) (congrArg Prod.snd e)
    · intro Γ hΓ
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powerset, Finset.mem_univ, and_true]
      exact c1 Γ (Finset.mem_filter.mp (Finset.mem_coe.mp hΓ)).2.1
    · rintro ⟨bad, Yt⟩ hm hn
      have hbad : bad ⊆ StepSettings.markedBonds R G.cut := Finset.mem_powerset.mp (Finset.mem_product.mp hm).1
      by_cases ho : G.CaseAvoids A bad Yt
      · simp only [if_pos ho]
        refine Finset.sum_eq_zero fun b _ => ?_
        unfold StepGas.GasGround.caseIntegral
        have : ∀ W (ν : G.state.unlabelled Yt → R.labels.Ω), G.caseIntegrand F bad Yt b W ν = 0 := by
          intro W ν
          unfold StepGas.GasGround.caseIntegrand
          rw [if_neg]
          rintro ⟨t1, t2⟩
          obtain ⟨Γ, g1, g2, g3⟩ := c4 bad Yt b W ν hbad t1 t2
          apply hn
          refine ⟨Γ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, g1, ?_⟩, ?_⟩
          · rw [g2, g3] at ho
            exact (c3 Γ A g1).mp ho
          · rw [g2, g3]
        simp [this]
      · simp only [if_neg ho]
    · intro Γ hΓ
      obtain ⟨g1, g2⟩ := (Finset.mem_filter.mp hΓ).2
      simp only [if_pos ((c3 Γ A g1).mpr g2)]
  rw [cases, gas, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Γ hΓ => ?_
  exact fam Γ (Finset.mem_filter.mp hΓ).2.1
end YangMills.Construction.ClusterExpansionOfAStep
end
