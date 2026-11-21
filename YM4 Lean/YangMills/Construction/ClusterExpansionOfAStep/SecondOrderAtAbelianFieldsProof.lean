import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open BlockAverages TorusFields
theorem SecondOrderAtAbelianFields.of_secondOrderOnMultiplesOfSide (hD : SecondOrderOnMultiplesOfSide) :
    SecondOrderAtAbelianFields := by
  intro ℓ hfit C h hF
  have hF1 : IsCurvatureFamilyOnMultiples ℓ 1 C h :=
    { smooth := fun n _ hn _ => hF.smooth n hn
      gauge := fun n _ hn _ => hF.gauge n hn
      translation := fun n _ hn _ => hF.translation n hn
      decay := fun n _ hn _ => hF.decay n hn
      local_density := fun n n' _ _ hn hn' _ _ => hF.local_density n n' hn hn' }
  have e0 : ∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      (fun m : ℕ => flatSecondDeriv h (1 * m) c c' X X') =
        fun n : ℕ => mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] := by
    intro c c' X X'
    funext m
    rw [one_mul]
    rfl
  have e : ∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      secondDerivLimitOnMultiples 1 h c c' X X' = secondDerivLimit h c c' X X' := by
    intro c c' X X'
    unfold secondDerivLimitOnMultiples
    rw [e0]
    rfl
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := hD ℓ hfit 1 one_pos C h hF1
  simp only [e, e0] at t1 t2 t3 t4 t5 t6 t7 t8
  refine ⟨t1, t2, t3, t4, t5, t6, ?_, ?_⟩
  · intro ω hω ε hε
    obtain ⟨γ₀, h0, hγ⟩ := t7 ω hω ε hε
    exact ⟨γ₀, h0, fun γ a b n _ hs => hγ γ a b n (one_dvd n) hs⟩
  · intro ω l X hω hl hi hX
    obtain ⟨v, hv, hall⟩ := t8 ω l X hω hl hi hX
    refine ⟨v, hv, fun ε hε => ?_⟩
    obtain ⟨n₁, hn⟩ := hall ε hε
    exact ⟨n₁, fun n _ h1 => hn n h1 (one_dvd n)⟩
end YangMills.Construction.TorusLumps
end
