import YangMills.Construction.ColdStepAtMirrorFrames.ColdChainOneLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeOfTheLeastActionBelow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
theorem minimalActionDerivComparison_holds (hchain : ColdEstimatesAtEveryDepth) :
    MinimalActionDerivComparison := by
  intro a L c ha hodd hL hc
  obtain ⟨N, hN, -, hcmp⟩ := hchain a L c ha hodd hL hc
  obtain ⟨⟨-, -, hs0, hδ, -⟩, -⟩ := hc.classical
  have hsσ : c.s₀ ≤ c.σA := by
    have := hc.inequalities.2.2.1
    linarith
  refine ⟨N 0 * c.s₀, mul_pos (hN 0) hs0, ?_⟩
  intro F F' W W' y y' R hT hT' ht hcold hcold' hag hR i X hX
  have hb : BondWithinRadius R ((0 : Fin 4 → ℤ), i) := by
    have hR' : (1 : ℤ) ≤ R := by exact_mod_cast (by omega : 1 ≤ R)
    refine ⟨fun l => by simp, fun l => ?_⟩
    by_cases hl : l = i
    · subst hl
      simpa using hR'
    · simp [Pi.single_eq_of_ne hl]
  have hu : AreUnitVectors ![X] := by
    intro l
    have : l = 0 := Subsingleton.elim _ _
    subst this
    simpa using hX
  have h1 := (hcmp F F' c.s₀ W W' y y' R hT hT' ht hs0 hsσ hcold hcold' hag).minimalAction_firstDeriv_close
    le_rfl _ _ hb hu
  have hz : ∀ {H : BlockFrame} (j : ℕ), (siteOfCoords j (0 : Fin 4 → ℤ) : H.Site j) = 0 := by
    intro H j
    funext l
    simp [siteOfCoords]
  have e1 : ∀ {H : BlockFrame} (z : H.Site H.depth),
      bondsAt z (fun _ : Fin 1 => ((0 : Fin 4 → ℤ), i)) = ![(z, i)] := by
    intro H z
    funext l
    have : l = 0 := Subsingleton.elim _ _
    subst this
    simp [bondsAt, hz]
  have e2 : siteSupDist y (y + siteOfCoords F.depth (0 : Fin 4 → ℤ)) = 0 := by
    rw [hz, add_zero]
    simp [siteSupDist]
  rw [e1, e1, e2] at h1
  simpa using h1
end YangMills.Construction.ColdStepAtMirrorFrames
end
