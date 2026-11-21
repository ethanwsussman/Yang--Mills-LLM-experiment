import YangMills.Construction.ClusterExpansionOfAStep.FourDensitiesOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.NumberOfFourDensitiesProof
import YangMills.Construction.ClusterExpansionOfAStep.TopFamiliesOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ClusterExpansionOfAStep.ColdStepDensities
variable {ℓ : TorusLumps.StepParameters}
theorem weight_pos (ℓ : TorusLumps.StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
theorem torusDecayFactor_eq_weight (hn : ℓ.n₁ = (ℓ.side : ℝ) ^ (1 / 640 : ℝ)) (m : ℕ) :
    BlockAverages.torusDecayFactor ℓ.side (ℓ.rt / 2 ^ 10) (m : ℝ) = ℓ.weight m := by
  unfold BlockAverages.torusDecayFactor TorusLumps.StepParameters.weight
    TorusLumps.StepParameters.weightRate
  rw [hn]
theorem constantPlaneCurvature_isLinearPotential (X : BlockAverages.imaginaryQuaternions)
    (μ ν : Fin 4) (hμν : μ < ν) :
    ColdStepAtMirrorFrames.IsLinearPotential
      (ColdStepAtMirrorFrames.constantPlaneCurvature X μ ν)
      (TorusLumps.linearPotential (TorusLumps.planeCurvature X μ ν)) := by
  have hne : μ ≠ ν := hμν.ne
  have ha : ∀ α β, ColdStepAtMirrorFrames.constantPlaneCurvature X μ ν α β =
      - ColdStepAtMirrorFrames.constantPlaneCurvature X μ ν β α := by
    intro α β
    simp only [ColdStepAtMirrorFrames.constantPlaneCurvature]
    by_cases h1 : α = μ ∧ β = ν
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hne, hne.symm]
    · by_cases h2 : α = ν ∧ β = μ
      · obtain ⟨rfl, rfl⟩ := h2
        simp [hne, hne.symm]
      · have h3 : ¬ (β = μ ∧ α = ν) := fun h => h2 ⟨h.2, h.1⟩
        have h4 : ¬ (β = ν ∧ α = μ) := fun h => h1 ⟨h.2, h.1⟩
        simp [h1, h2, h3, h4]
  refine ⟨fun α β => (1 / 2 : ℝ) • ColdStepAtMirrorFrames.constantPlaneCurvature X μ ν β α,
    fun _ => 0, fun x α => ?_, fun α β => ?_⟩
  · simp only [TorusLumps.linearPotential, add_zero]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [smul_comm]
    rfl
  · beta_reduce
    rw [ha β α, smul_neg, sub_neg_eq_add, ← add_smul]
    norm_num
variable {n : ℕ}
theorem localComparison_centeredFamily {h : TorusLumps.LocalDensity} (hσ : 0 < ℓ.threshold)
    (hp : TorusLumps.IsAdmissibleDensity ℓ h) {e : ℕ → ℝ} (he : ∀ m, 0 ≤ e m)
    (hc : TorusLumps.LocalComparison ℓ h e) :
    TorusLumps.LocalComparison ℓ (TorusLumps.centeredFamily h) fun m => 2 * e m := by apply _root_.YangMills.Construction.TorusLumps.SumOfFourCurvature.localComparison_centeredFamily <;> assumption
theorem expansionDensityBoundsOfColdStep_holds (hA : TorusLumps.TopFamilyOnTori) :
    ExpansionDensityBoundsOfColdStep := by
  intro ℓ hF hn t a ρA ρ lam x δ₂ Ct Cs CE e₀ p f u s τ g he₀ hS hg
  have hσ := hF.σ_pos
  have hle : ℓ.threshold ≤ 9 / 8 * ℓ.threshold := by linarith
  have hw : ∀ m : ℕ, BlockAverages.torusDecayFactor ℓ.side (ℓ.rt / 2 ^ 10) (m : ℝ) = ℓ.weight m :=
    torusDecayFactor_eq_weight hn
  obtain ⟨pu, du, cu, -, lu⟩ := hA ℓ hF t (9 / 8 * ℓ.threshold) u hle
  obtain ⟨ps, ds, -, cs, ls⟩ := hA ℓ hF t (9 / 8 * ℓ.threshold) s hle
  obtain ⟨pτ, dτ, cτ, -, -⟩ := hA ℓ hF t (9 / 8 * ℓ.threshold) τ hle
  have hgp : TorusLumps.IsAdmissibleDensity ℓ g := ⟨hg.smooth, hg.gauge, hg.translation⟩
  have fw : ∀ (A : ℕ → ℝ),
      (fun m : ℕ => A m / BlockAverages.torusDecayFactor ℓ.side (ℓ.rt / 2 ^ 10) (m : ℝ)) =
      fun m : ℕ => A m / ℓ.weight m := fun A => funext fun m => by rw [hw]
  refine ⟨pu hS.localDensity_u, ps hS.localDensity_s, pτ hS.localDensity_τ, hgp,
    du _ hS.derivDecay_u, cu _ hS.localOnTori_u, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := ds _ hS.derivDecay_s
    have e : (fun (k n : ℕ) => (2⁻¹ : ℝ) ^ 6 * (if k = 3 then ℓ.E₃ else ℓ.E) /
          BlockAverages.torusDecayFactor ℓ.side (ℓ.rt / 2 ^ 10) (n : ℝ) +
        CE * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(ℓ.rt / 2 ^ 6 * n))) =
        fun k m => 2⁻¹ ^ 6 * (if k = 3 then ℓ.E₃ else ℓ.E) / ℓ.weight m +
          CE * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(ℓ.rt / 2 ^ 6 * m)) := by
      funext k m
      rw [hw]
    rw [e] at h1
    exact h1
  · have h1 := cs _ hS.localOnTori_s
    rw [fw (fun _ => (2⁻¹ : ℝ) ^ 4 * ℓ.E)] at h1
    exact h1
  · intro X μ ν hX hμν
    obtain ⟨q, hq, hb⟩ := hS.flat_limit
    obtain ⟨v, hv, hvb⟩ := hb X μ ν (TorusLumps.linearPotential (TorusLumps.planeCurvature X μ ν))
      hX hμν (constantPlaneCurvature_isLinearPotential X μ ν hμν)
    refine ⟨v, ?_, hvb⟩
    have hterm : TorusLumps.limitFormTerm (ColdStepAtMirrorFrames.densityOfTopFamily ℓ.side t s)
        (TorusLumps.planeCurvature X μ ν) (TorusLumps.planeCurvature X μ ν) =
        fun e => q e.1 e.2 (TorusLumps.linearPotential (TorusLumps.planeCurvature X μ ν) e.1)
          (TorusLumps.linearPotential (TorusLumps.planeCurvature X μ ν) e.2) := by
      funext ⟨c, c'⟩
      have h0 := hq c c' (TorusLumps.linearPotential (TorusLumps.planeCurvature X μ ν) c)
        (TorusLumps.linearPotential (TorusLumps.planeCurvature X μ ν) c')
      have h1 : Filter.Tendsto (fun n : ℕ => TorusFields.mixedDeriv
          (ColdStepAtMirrorFrames.densityOfTopFamily ℓ.side t s n 0) (TorusFields.trivialField n)
          ![TorusLumps.bondFrom 0 c, TorusLumps.bondFrom 0 c']
          ![TorusLumps.linearPotential (TorusLumps.planeCurvature X μ ν) c,
            TorusLumps.linearPotential (TorusLumps.planeCurvature X μ ν) c']) Filter.atTop _ :=
        h0.congr' (by
          filter_upwards [Filter.eventually_ge_atTop ℓ.n₀] with n hn'
          exact (ls c c' _ _ n hn').symm)
      exact h1.limUnder_eq
    rw [hterm]
    exact hv
  · have h1 := dτ _ hS.derivDecay_τ
    have e : (fun (_ n : ℕ) => Ct * x * Real.exp (-(δ₂ / 8 * ColdStepAtMirrorFrames.frameRadius x)) /
        BlockAverages.torusDecayFactor ℓ.side (ℓ.rt / 2 ^ 10) (n : ℝ)) =
        fun _ m => Ct * x * Real.exp (-(δ₂ / 8 * ColdStepAtMirrorFrames.frameRadius x)) /
          ℓ.weight m := by
      funext k m
      rw [hw]
    rw [e] at h1
    exact h1
  · have h1 := cτ _ hS.localOnTori_τ
    rw [fw (fun _ => Ct * x * Real.exp (-(δ₂ / 8 * ColdStepAtMirrorFrames.frameRadius x)))] at h1
    exact h1
  · intro n _ hn y V hV k c X h1 h3 hX
    refine (hg.decay n hn y V hV k c X h1 h3 hX).trans ?_
    exact div_le_div_of_nonneg_right (by linarith) (weight_pos ℓ _).le
  · have h1 := localComparison_centeredFamily hσ hgp (e := fun m => e₀ / ℓ.weight m)
      (fun m => div_nonneg he₀ (weight_pos ℓ m).le) hg.local_density
    intro n n' _ _ hn hn' y y' W W' m h2 h3 hW hW' hAg k b X hk hb hX
    have h4 := h1 n n' hn hn' y y' W W' m h2 h3 hW hW' hAg k b X hk hb hX
    refine h4.trans (le_of_eq ?_)
    beta_reduce
    rw [mul_div_assoc]
end YangMills.Construction.ClusterExpansionOfAStep.ColdStepDensities
end
