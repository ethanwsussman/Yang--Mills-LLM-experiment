import YangMills.Construction.InfiniteLattice.AllMirrorsOfPeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.LatticeMirrorsAndTwoFormsOfReflectionPositivityProof
import YangMills.Construction.InfiniteLattice.OneMeanPlaquetteEnergy
import YangMills.Construction.InfiniteLattice.WhatIsReadOfAPeriodicGibbsState
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicGibbsConsequences
open LatticeConventions
variable {a : ℝ}
theorem latticeSymmetry_ext {r s : LatticeSymmetry a} (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem realNormal_axial_or_faceDiagonal (F : ReflectionClass) :
    IsAxialNormal F.realNormal ∨ IsFaceDiagonalNormal F.realNormal := by apply _root_.YangMills.Construction.LatticeConventions.LatticeMirrorsAndReflectionPositivity.realNormal_valid <;> assumption
theorem dotProduct_self_of_isAxialNormal {v : LatticeConventions.Point} (h : IsAxialNormal v) :
    v ⬝ᵥ v = 1 := by
  obtain ⟨μ, rfl⟩ := h
  simp [LatticeConventions.basisVector]
theorem dotProduct_self_of_isFaceDiagonalNormal {v : LatticeConventions.Point}
    (h : IsFaceDiagonalNormal v) : v ⬝ᵥ v = 2 := by
  obtain ⟨μ, lam, hne, rfl | rfl⟩ := h
  · simp only [LatticeConventions.basisVector, dotProduct_add,
      dotProduct_single_one, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne,
      Pi.single_eq_of_ne hne.symm]
    norm_num
  · simp only [LatticeConventions.basisVector, dotProduct_sub,
      dotProduct_single_one, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne,
      Pi.single_eq_of_ne hne.symm]
    norm_num
def normalHyperplane (P : LatticeMirror a) : NormalHyperplane :=
  ⟨P.cls.realNormal, P.level, realNormal_axial_or_faceDiagonal P.cls⟩
theorem normalHyperplane_isLatticeMirror (P : LatticeMirror a) :
    (normalHyperplane P).IsLatticeMirror a := by
  obtain ⟨F, c, hc⟩ := P
  cases F with
  | axial μ =>
    refine ⟨fun _ => hc, fun h => ?_⟩
    have h1 := dotProduct_self_of_isFaceDiagonalNormal h
    have h2 : (ReflectionClass.axial μ).realNormal ⬝ᵥ (ReflectionClass.axial μ).realNormal = 1 :=
      ReflectionClass.realNormal_dot_axial μ
    change (ReflectionClass.axial μ).realNormal ⬝ᵥ (ReflectionClass.axial μ).realNormal = 2 at h1
    rw [h2] at h1
    norm_num at h1
  | diagonal μ ν lt s =>
    refine ⟨fun h => ?_, fun _ => hc⟩
    have h1 := dotProduct_self_of_isAxialNormal h
    have h2 := ReflectionClass.realNormal_dot_diagonal μ ν lt s
    change (ReflectionClass.diagonal μ ν lt s).realNormal ⬝ᵥ
        (ReflectionClass.diagonal μ ν lt s).realNormal = 1 at h1
    rw [h2] at h1
    norm_num at h1
theorem reflectSymmetry_normalHyperplane (P : LatticeMirror a) :
    NormalHyperplane.reflectSymmetry (normalHyperplane_isLatticeMirror P) = P.symmetry :=
  latticeSymmetry_ext (NormalHyperplane.reflect_eq_hyperplaneReflect (normalHyperplane P))
theorem holds (hAll : PeriodicGibbsSymmetries.Statement)
    (hMean : MeanFaceEnergyIsUniform) : SymmetriesAndConstantFaceMean := by
  intro a ha β hβ ν hν
  obtain ⟨hMotions, hMirrors⟩ := (hAll a ha β hβ).1 ν hν
  refine ⟨⟨hMotions, fun P => ?_⟩, hMean a ha β hβ ν hν⟩
  obtain ⟨hInv, hPlus, hMinus⟩ := hMirrors (normalHyperplane P) (normalHyperplane_isLatticeMirror P)
  rw [reflectSymmetry_normalHyperplane] at hInv
  refine ⟨hInv, hν.1.1, fun A hA _ hm => ?_⟩
  obtain ⟨H, hH, hm⟩ := hm
  have key : ∀ F : GaugeField a → ℂ,
      MirrorSideIndependence.reflectedPairing
          (normalHyperplane_isLatticeMirror P) ν F ≥ 0 →
        0 ≤ ∫ U, F U * conj (P.symmetry.actOn F U) ∂ν := by
    intro F hF
    have hSame : MirrorSideIndependence.reflectedPairing
        (normalHyperplane_isLatticeMirror P) ν F =
          ∫ U, F U * conj (P.symmetry.actOn F U) ∂ν := by
      unfold MirrorSideIndependence.reflectedPairing
      rw [reflectSymmetry_normalHyperplane]
      exact integral_congr_ae (Filter.Eventually.of_forall fun U => mul_comm _ _)
    rw [← hSame]
    exact hF
  rcases hH with rfl | rfl
  · exact key A (hPlus A ⟨hA, hm⟩)
  · exact key A (hMinus A ⟨hA, hm⟩)
end YangMills.Construction.InfiniteLattice.PeriodicGibbsConsequences
end
