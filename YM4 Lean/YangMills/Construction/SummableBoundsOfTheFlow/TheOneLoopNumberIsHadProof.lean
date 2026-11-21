import YangMills.Construction.ClusterExpansionOfAStep.NumberOfFourDensities
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensityOfTheStepIsCarried
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensityOfTheStepIsSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.TheOneLoopNumberIsHad
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepDensities
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps ReferenceDensity
private theorem mixedDeriv_const_zero {n k : ℕ} (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun _ : TorusField n => (0 : ℝ)) W c X = 0 := by apply _root_.YangMills.Construction.WilsonExpansion.mixedDeriv_zero <;> assumption
private theorem isAdmissibleDensity_zero (ℓ : TorusLumps.StepParameters) : IsAdmissibleDensity ℓ 0 :=
  ⟨fun n _ _ y W _ k c X => contDiffAt_const, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
private theorem centeredFamily_zero : centeredFamily (0 : LocalDensity) = 0 := by
  funext n y W
  simp [centeredFamily, centered]
private theorem weight_pos (ℓ : TorusLumps.StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem derivDecay_zero (ℓ : TorusLumps.StepParameters) (e : ℕ → ℕ → ℝ) (he : ∀ k m, 0 ≤ e k m) :
    DerivDecay ℓ 0 e := by
  intro n _ _ y W _ k c X _ _ _
  have : mixedDeriv ((0 : LocalDensity) n y) W c X = 0 := mixedDeriv_const_zero W c X
  rw [this, abs_zero]
  exact he k _
private theorem localComparison_zero (ℓ : TorusLumps.StepParameters) (e : ℕ → ℝ) (he : ∀ m, 0 ≤ e m) :
    LocalComparison ℓ 0 e := by
  intro n n' _ _ _ _ y y' W W' m _ _ _ _ _ k b X _ _ _
  have h1 : mixedDeriv ((0 : LocalDensity) n y) W (fun l => bondFrom y (b l)) X = 0 := mixedDeriv_const_zero W _ X
  have h2 : mixedDeriv ((0 : LocalDensity) n' y') W' (fun l => bondFrom y' (b l)) X = 0 :=
    mixedDeriv_const_zero W' _ X
  rw [h1, h2, sub_zero, abs_zero]
  exact he m
theorem oneLoopCoeffBound_holds (hS : StepDensityIsSmooth) (hC : StepDensitySumInvariant)
    (hN : CurvatureCoefficientOfSum) : oneLoopCoeffBound := by
  refine EventuallyOrdered.mono (hS.and hC) ?_
  rintro T hT hn ⟨⟨C, gS⟩, gC⟩ ℓ hm hF t
  have gb := gS ℓ hm hF t
  have hcar := gC ℓ hm hF t
  have hE := hF.E_pos
  have hE₃ := hF.E₃_pos
  have hn₀ := hF.n₀_ge
  have hCs : 0 ≤ T.Cs := by
    haveI : NeZero ℓ.n₀ := ⟨by omega⟩
    have h1 := gb.comparison ℓ.n₀ ℓ.n₀ le_rfl le_rfl (0 : TorusSite ℓ.n₀) 0 (trivialField ℓ.n₀) (trivialField ℓ.n₀) 0
      (by omega) (by omega)
      (fun x μ ν _ => by simpa [curvature, holonomy, trivialField] using hF.σ_pos)
      (fun x μ ν _ => by simpa [curvature, holonomy, trivialField] using hF.σ_pos) (fun _ _ => rfl) 0 Fin.elim0 Fin.elim0
      (by norm_num) (fun l => l.elim0) (fun l => l.elim0)
    have h2 := (abs_nonneg _).trans h1
    by_contra hneg
    have h4 := Real.exp_pos (-(T.κ / 2 ^ 9 * ((0 : ℕ) : ℝ)))
    nlinarith
  have hrtκ : ℓ.rt = T.κ := hm.rt_eq
  have H : ExpansionDensityBounds ℓ T.Cs 0 0 0 1 (T.stepDensity t) 0 0 0 := by
    refine ⟨gb.admissible, isAdmissibleDensity_zero ℓ, isAdmissibleDensity_zero ℓ, isAdmissibleDensity_zero ℓ,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrtκ]
      exact gb.decay
    · rw [hrtκ]
      exact gb.comparison
    · refine derivDecay_zero ℓ _ fun k m => ?_
      have := weight_pos ℓ m
      split_ifs <;> simp <;> positivity
    · rw [centeredFamily_zero]
      refine localComparison_zero ℓ _ fun m => ?_
      have := weight_pos ℓ m
      positivity
    · intro X μ ν _ _
      have h0 : limitFormTerm (0 : LocalDensity) (planeCurvature X μ ν) (planeCurvature X μ ν) = fun _ => 0 := by
        funext cc
        unfold limitFormTerm secondDerivLimit
        have : (fun n : ℕ => mixedDeriv ((0 : LocalDensity) n 0) (trivialField n) ![bondFrom 0 cc.1, bondFrom 0 cc.2]
            ![linearPotential (planeCurvature X μ ν) cc.1, linearPotential (planeCurvature X μ ν) cc.2]) =
            fun _ => 0 := by
          funext n
          exact mixedDeriv_const_zero _ _ _
        rw [this]
        exact tendsto_const_nhds.limUnder_eq
      refine ⟨0, ?_, ?_⟩
      · rw [h0]
        exact hasSum_zero
      · simp
    · refine derivDecay_zero ℓ _ fun k m => ?_
      simp
    · refine localComparison_zero ℓ _ fun m => ?_
      simp
    · refine derivDecay_zero ℓ _ fun k m => ?_
      simp
    · rw [centeredFamily_zero]
      refine localComparison_zero ℓ _ fun m => ?_
      simp
  have hsum : sumOfFour (T.stepDensity t) 0 0 0 = T.stepDensity t := by
    funext n y W
    simp [sumOfFour]
  have hcar' : SumInvariantUnderIsometries ℓ (sumOfFour (T.stepDensity t) 0 0 0) := by
    rw [hsum]
    exact hcar
  obtain ⟨-, -, -, -, -, h5, h6⟩ := hN ℓ hF T.Cs 0 0 0 1 (T.stepDensity t) 0 0 0 hCs le_rfl le_rfl le_rfl one_pos H hcar'
    (by simp)
  rw [hsum] at h5 h6
  rw [hrtκ] at h6
  exact ⟨h5, h6⟩
end YangMills.Construction.StepDensities
end
