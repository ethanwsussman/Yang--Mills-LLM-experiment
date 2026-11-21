import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnConfigurationsAndFunctions
import YangMills.Construction.InfiniteLattice.MovesOfBondsSupportsAndPlaquettes
import YangMills.Construction.InfiniteLattice.OrbitsAndPeriodicExtensions
import YangMills.Construction.InfiniteLattice.PeriodicExtensionAndPlaquetteActionsOfAPeriodLattice
import YangMills.Construction.InfiniteLattice.TorusOfAPeriodLatticeIsFinite
import YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace GibbsAtFixedSpacing
namespace PeriodSublatticeQuotient
variable {a : ℝ}
theorem latticeSymmetry_ext {r s : LatticeSymmetry a} (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem shift_comp_shift (γ v : LatticePoint a) :
    (shift γ).comp (shift v) = shift (v + γ) := by
  apply latticeSymmetry_ext
  funext x
  change x + (v : AmbientSpace) + (γ : AmbientSpace) = x + ((v : AmbientSpace) + (γ : AmbientSpace))
  rw [add_assoc]
theorem plaquetteMap_shift_zero (hM : SymmetriesTransportPlaquettes a) (P : ElementaryPlaquette a) :
    (shift (0 : LatticePoint a)).plaquetteMap P = P := by
  obtain ⟨hu, hc⟩ := (hM (shift 0)).1 P
  have hid : (shift (0 : LatticePoint a)).pointMap '' P.cornerSet = P.cornerSet := by
    have hm : ∀ x : LatticePoint a, (shift (0 : LatticePoint a)).pointMap x = x := fun x => add_zero x
    simp only [hm, Set.image_id']
  exact hu.unique hc hid.symm
end PeriodSublatticeQuotient
open PeriodSublatticeQuotient in
theorem PeriodSublatticeQuotient.periodSublatticeQuotientFacts_holds
    (hA : LatticeSymmetryActionOnFields)
    (hM : SymmetriesTransportLinksSupportsAndPlaquettes)
    (hT : PeriodQuotientFinite)
    (hP : PeriodicLiftAndQuotientEnergiesStatement) :
    PeriodSublatticeQuotientFacts := by
  intro a ha Γ
  obtain ⟨hfin, hlinks, hfaces⟩ := hT a ha Γ
  obtain ⟨⟨hinv, hcont, hact, -⟩, -⟩ := hP a ha Γ
  have hindex : Γ.periods.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  refine ⟨⟨hindex, hfin, hlinks, hfaces, fun Q _ => ?_⟩,
    ⟨hcont, hinv, fun U γ hγ b => ?_⟩, ?_, ?_, ?_⟩
  · exact AddSubgroup.finite_quotient_of_finiteIndex
  · exact congrArg (fun V : GaugeField a => V b) (hinv U γ hγ)
  · intro E F v w hvw
    have hw : w ∈ pointOrbit Γ v := by
      rw [hvw]
      exact ⟨0, zero_mem _, (add_zero w).symm⟩
    obtain ⟨γ, hγ, rfl⟩ := hw
    funext U
    have hcomp := (hA a ha (shift γ) (shift v)).1.2.1
    rw [shift_comp_shift] at hcomp
    have hU : (shift (v + γ)).pullbackField (Γ.lift U) =
        (shift v).pullbackField (Γ.lift U) := by
      rw [← hcomp, Function.comp_apply, hinv U γ hγ]
    exact congrArg F hU.symm
  · intro P Q hPQ
    have hmem : ∀ R : ElementaryPlaquette a, R ∈ Γ.plaquetteOrbit R := fun R =>
      ⟨0, zero_mem _, (plaquetteMap_shift_zero (hM a ha).2.2 R).symm⟩
    funext U
    have hQ : Q ∈ Γ.plaquetteOrbit P := by
      rw [hPQ]
      exact hmem Q
    exact hact U ⟨Γ.plaquetteOrbit P, P, rfl⟩ P (hmem P) Q hQ
  · intro E _ F hF
    exact hF.comp hcont
end GibbsAtFixedSpacing
end YangMills.Construction
