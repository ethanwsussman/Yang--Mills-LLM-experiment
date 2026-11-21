import YangMills.Construction.ChessboardTori.GroupOfAGridAndCopiesProof
import YangMills.Construction.ChessboardTori.CopiesOfCellFunctions
import YangMills.Construction.ChessboardTori.GroupCoordinateByCoordinate
import YangMills.Construction.ChessboardTori.MirrorPeriodicWeightsAsCellFunctionsProof
import YangMills.Construction.MirrorGridsOfEverySide.RulesOfTheCopiesAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open ChessboardTori (ReflectionGrid orientationSign translate)
open Conventions (signedConj signedConjFun)
namespace MirrorGridsAllSides
namespace TransportLaws
variable {D : GridSetup} {g : ReflectionGrid D}
theorem mover_eq (hG : g.ReflectionGroupCoordForm) {S S' : Set AmbientSpace}
    (hS : S ∈ g.cellSet) (hS' : S' ∈ g.cellSet) (r : g.reflectionGroup)
    (h : (r.1 : AmbientSpace → AmbientSpace) '' S = S') :
    g.mover S S' = r := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGroupAndTransport.mover_eq <;> assumption
theorem signedConj_signedConj (σ τ : ℤˣ) (z : ℂ) :
    signedConj σ (signedConj τ z) = signedConj (σ * τ) z := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionPeriodicWeightsAsCellFunctions.signedConj_signedConj <;> assumption
theorem pullbackField_mul (r t : g.reflectionGroup) (U : D.GaugeField) :
    (g.toLatticeSym (r * t)).pullbackField U =
      (g.toLatticeSym t).pullbackField ((g.toLatticeSym r).pullbackField U) := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGroupAndTransport.pullbackField_toLatticeSym_mul <;> assumption
theorem transportTo_image (hG : g.ReflectionGroupCoordForm) {S S' : Set AmbientSpace}
    (hS : S ∈ g.cellSet) (hS' : S' ∈ g.cellSet) (r : g.reflectionGroup)
    (F : D.GaugeField → ℂ) :
    g.transportTo S (r.1 '' S') F =
      signedConjFun (orientationSign r.1)
        ((g.toLatticeSym r).actOn (g.transportTo S S' F)) := by
  obtain ⟨t, ht⟩ := (hG.2.2.2.2.2.2.1 S hS S' hS').exists
  have hm : g.mover S S' = t := mover_eq hG hS hS' t ht
  have hm' : g.mover S (r.1 '' S') = r * t :=
    mover_eq hG hS (hG.2.2.2.2.2.1 r.1 r.2 S' hS') (r * t) (by
      change ((r.1 * t.1 : Equiv.Perm AmbientSpace) : AmbientSpace → AmbientSpace) '' S = r.1 '' S'
      rw [Equiv.Perm.coe_mul, image_comp, ht])
  simp only [ReflectionGrid.transportTo, hm, hm']
  funext U
  change signedConj (orientationSign (r * t).1)
      (F ((g.toLatticeSym (r * t)).pullbackField U)) =
    signedConj (orientationSign r.1) (signedConj (orientationSign t.1)
      (F ((g.toLatticeSym t).pullbackField ((g.toLatticeSym r).pullbackField U))))
  rw [signedConj_signedConj, pullbackField_mul, ← hG.2.2.2.1 r.1 r.2 t.1 t.2]
  rfl
end TransportLaws
open TransportLaws in
theorem transportLawsEveryGrid_holds
    (h₁ : ChessboardTori.CellFunctionCopies.Statement)
    (h₂ : ChessboardTori.ReflectionGroupCoordinates.Statement) :
    TransportLawsEveryGrid := by
  intro D g _ S hS S' hS' S'' hS'' F hF
  have hG : g.ReflectionGroupCoordForm := h₂ D g
  obtain ⟨t, ht⟩ := (hG.2.2.2.2.2.2.1 S hS S' hS').exists
  obtain ⟨hmem, hid, hcomp, hconj, -, -, -, -⟩ := h₁ D g S hS S' hS' S'' hS'' t ht F hF F hF 0
  refine ⟨hmem, hid, hcomp, fun r => transportTo_image hG hS hS' r F, fun F' hF' => ?_, hconj,
    fun r c => ?_⟩
  · obtain ⟨-, -, -, -, hmul, hadd, -, -⟩ := h₁ D g S hS S' hS' S'' hS'' t ht F hF F' hF' 0
    exact ⟨hadd, hmul⟩
  · exact (h₁ D g S hS (r.1 '' S) (hG.2.2.2.2.2.1 r.1 r.2 S hS) S hS r rfl F hF F hF c).2.2.2.2.2.2.1
end MirrorGridsAllSides
end YangMills.Construction
end
