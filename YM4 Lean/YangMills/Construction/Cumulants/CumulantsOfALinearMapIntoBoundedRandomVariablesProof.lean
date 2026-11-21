import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.Cumulants.CumulantsOfALinearMapIntoBoundedRandomVariables
import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.Cumulants
private theorem comp_update_eq_update_comp {Ω F : Type} [AddCommGroup F] [Module ℝ F]
    (O : F →ₗ[ℝ] Ω → ℝ) {n : ℕ} (f : Fin n → F) (j : Fin n) (g : F) :
    (fun i => O (Function.update f j g i)) = Function.update (fun i => O (f i)) j (O g) := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Function.update_of_ne hij]
theorem linearMapCumulantProperties_holds
    (hRel : Cumulants.CumulantMomentRelations) :
    Cumulants.LinearMapCumulantProperties := by
  intro Ω _ ν _ F _ _ O hO
  have hGen := fun (n : ℕ) (y : Fin n → Ω → ℝ) (y' : Ω → ℝ) (hn : 1 ≤ n)
      (hy : ∀ i, Probability.IsBoundedRealRV (y i))
      (hy' : Probability.IsBoundedRealRV y') =>
    (hRel Ω ν 0 Fin.elim0 (fun l => l.elim0)).1 n y y' hn hy hy'
  have hBdd : ∀ {n : ℕ} (f : Fin n → F) (i : Fin n),
      Probability.IsBoundedRealRV ((fun i => O (f i)) i) := fun f i => hO (f i)
  refine ⟨fun n hn => ⟨fun f => ?_, fun f σ => ?_, fun f j g g' => ?_, fun f j a g => ?_⟩,
    fun f => ?_, fun q h => ?_⟩
  · exact (hGen n (fun i => O (f i)) (O 0) hn (hBdd f) (hO 0)).1
  · exact (hGen n (fun i => O (f i)) (O 0) hn (hBdd f) (hO 0)).2.1 σ
  · have hAdd := (hGen n (fun i => O (Function.update f j g i)) (O g') hn
      (hBdd _) (hO g')).2.2 j 1 1
    have hFun : (fun ω => (1 : ℝ) * (fun i => O (Function.update f j g i)) j ω +
        (1 : ℝ) * O g' ω) = O (g + g') := by
      funext ω
      simp
    rw [hFun, ← comp_update_eq_update_comp O (Function.update f j g) j (g + g'),
      ← comp_update_eq_update_comp O (Function.update f j g) j g', Function.update_idem,
      Function.update_idem] at hAdd
    simpa [Cumulants.linearMapCumulant] using hAdd
  · have hSmul := (hGen n (fun i => O (Function.update f j g i)) (O g) hn
      (hBdd _) (hO g)).2.2 j a 0
    have hFun : (fun ω => a * (fun i => O (Function.update f j g i)) j ω +
        (0 : ℝ) * O g ω) = O (a • g) := by
      funext ω
      simp
    rw [hFun, ← comp_update_eq_update_comp O (Function.update f j g) j (a • g),
      Function.update_idem] at hSmul
    simpa [Cumulants.linearMapCumulant] using hSmul
  · exact (hRel Ω ν 1 (fun _ => O f) (fun _ => hO f)).2.1 0
  · exact (hRel Ω ν q (fun l => O (h l)) (fun l => hO (h l))).2.2.2.2.2.1
end YangMills.Construction.Cumulants
