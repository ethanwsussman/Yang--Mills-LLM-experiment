import YangMills.Construction.Geometry.CenteredRepresentative
import YangMills.Construction.Torus.CellsOfATranslatedLatticeAndBallsOfTheTorusProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Conventions.StandingParameters.CenteredLift
theorem torusSide_pos (s : StandingParameters) : 0 < PeriodicLattice.torusSide s.L s.m := by apply _root_.YangMills.Construction.TorusMeasure.TranslatedLatticeCells.torusSide_pos <;> assumption
theorem Ico_neg_half_add_self (S : ℝ) : Ico (-(S / 2)) (-(S / 2) + S) = Ico (-(S / 2)) (S / 2) := by
  congr 1
  ring
theorem centeredLiftUnique_holds : CenteredLiftUnique := by
  intro s y
  have : Fact (0 < PeriodicLattice.torusSide s.L s.m) := ⟨torusSide_pos s⟩
  have hIco := Ico_neg_half_add_self (PeriodicLattice.torusSide s.L s.m)
  let w : Fin 4 → ℝ := fun μ =>
    (AddCircle.equivIco (PeriodicLattice.torusSide s.L s.m)
      (-(PeriodicLattice.torusSide s.L s.m / 2)) (y μ) : ℝ)
  have hw : ∀ μ, w μ ∈ Ico (-(PeriodicLattice.torusSide s.L s.m / 2))
      (-(PeriodicLattice.torusSide s.L s.m / 2) + PeriodicLattice.torusSide s.L s.m) := fun μ =>
    (AddCircle.equivIco (PeriodicLattice.torusSide s.L s.m)
      (-(PeriodicLattice.torusSide s.L s.m / 2)) (y μ)).2
  have hproj : ∀ μ, (w μ : AddCircle (PeriodicLattice.torusSide s.L s.m)) = y μ := fun μ =>
    AddCircle.coe_equivIco
  refine ⟨w, ⟨?_, funext hproj⟩, ?_⟩
  · intro μ _
    have h := hw μ
    rw [hIco] at h
    exact h
  · rintro z ⟨hz, hzy⟩
    funext μ
    have hzμ : z μ ∈ Ico (-(PeriodicLattice.torusSide s.L s.m / 2))
        (-(PeriodicLattice.torusSide s.L s.m / 2) + PeriodicLattice.torusSide s.L s.m) := by
      rw [hIco]
      exact hz μ (mem_univ μ)
    refine (AddCircle.coe_eq_coe_iff_of_mem_Ico hzμ (hw μ)).1 ?_
    rw [hproj μ]
    exact congrFun hzy μ
end YangMills.Construction.Conventions.StandingParameters.CenteredLift
end
