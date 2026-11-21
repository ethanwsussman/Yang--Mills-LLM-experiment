import YangMills.Construction.ColdStepAtMirrorFrames.StepInFixedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.WeightOfTheFramesIsTheArray
import YangMills.Construction.SummableBoundsOfTheFlow.StepIntegralReadsTheTotal
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages TorusFields
namespace ColdStepAtMirrorFrames
theorem stepIntegralDependsOnlyOnFunctional_holds (hw : BoltzmannWeightEqFunctional)
    (hfix : stepIntegralInFixedVariables) : stepIntegralDependsOnlyOnFunctional := by
  intro ℓ t x D f f' F ρA ρ m p V hfit hR hR' hlow hodd hside hframe hcold
  rw [hfix F ℓ.coupling ρA ρ x m p (localFamilyOfDensity f) V hodd hside hframe,
    hfix F ℓ.coupling ρA ρ x m p (localFamilyOfDensity f') V hodd hside hframe]
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun η => ?_
  dsimp only
  by_cases hη : η ∈ openBallProduct F ρ
  · have hc := hcold η hη
    have e1 := hw ℓ t x D f hfit hR F hlow _ hc
    have e2 := hw ℓ t x D f' hfit hR' F hlow _ hc
    have hper : ℓ.n₀ ≤ F.period F.depth 0 := by
      obtain ⟨hL, _, n, hs, hn⟩ := hlow
      have : F.period F.depth 0 = n * ℓ.side := by
        simp [BlockFrame.period, BlockFrame.top, hs, hL]
      rw [this]
      exact hn
    have hne : NeZero (F.period F.depth 0) := ⟨by have := hfit.n₀_ge; omega⟩
    have hflat : IsCold ℓ.threshold (trivialField (F.period F.depth 0)) := by
      intro z μ ν _
      have : curvature (trivialField (F.period F.depth 0)) z μ ν = 0 := by
        simp [curvature, holonomy, trivialField]
      rw [this]
      exact hfit.σ_pos
    have hD : 0 < D (F.period F.depth 0) (trivialField _) := hR.positive _ hper _ hflat
    have e3 : lowerBoltzmann ℓ.coupling x (localFamilyOfDensity f) (finiteCells F)
          (fieldAboveFrame false ℓ.coupling ρA m V η) =
        lowerBoltzmann ℓ.coupling x (localFamilyOfDensity f') (finiteCells F)
          (fieldAboveFrame false ℓ.coupling ρA m V η) :=
      mul_left_cancel₀ hD.ne' (e1.trans e2.symm)
    unfold lowerBoltzmann at e3
    have e4 := Real.exp_injective e3
    have e5 : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
          centredExpansion false ℓ.coupling ρA m (localFamilyOfDensity f) y η V =
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
          centredExpansion false ℓ.coupling ρA m (localFamilyOfDensity f') y η V := by
      unfold centredExpansion
      linarith
    have e6 : stepExponent false ℓ.coupling ρA x m (localFamilyOfDensity f) 1 V η =
        stepExponent false ℓ.coupling ρA x m (localFamilyOfDensity f') 1 V η := by
      unfold stepExponent
      rw [e5]
    rw [e6]
  · have : cutoffWeight ρ p η = 0 := by
      simp only [openBallProduct, Set.mem_ofPred_eq, not_forall, not_lt] at hη
      obtain ⟨b, hb⟩ := hη
      unfold cutoffWeight
      apply Finset.prod_eq_zero (Finset.mem_univ b)
      unfold cutoffFactor
      rw [if_neg (not_lt.mpr hb)]
    rw [this]
    simp
end ColdStepAtMirrorFrames
end YangMills.Construction
end
