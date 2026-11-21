import YangMills.Construction.InfiniteLattice.AllMirrorsOfPeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.GibbsStatesReadThroughKernelsAndSymmetries
import YangMills.Construction.InfiniteLattice.LinksAndTheReplacementOfAConfigurationOnAFiniteSet
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyForBondsOfAnyOrientation
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.LatticePhases.GibbsKernelsAndSymmetries
open YangMills.Construction.GibbsAtFixedSpacing
open YangMills.Construction.LatticeConventions.NormalHyperplane (reflectSymmetry)
open YangMills.Construction.LatticeConventions.MirrorSideIndependence (reflectedPairing)
variable {a : ℝ}
theorem faces_eq_plaquettesTouching (ha : 0 < a) (W : OrientedLinkSet a) :
    W.faces = plaquettesTouching W.links := by
  ext p
  rw [mem_plaquettesTouching_iff ha]
  rfl
theorem energy_eq_finsum (ha : 0 < a) (W : OrientedLinkSet a) (U : GaugeField a) :
    W.energy U = ∑ᶠ p ∈ plaquettesTouching W.links, faceEnergy U p := by
  rw [← faces_eq_plaquettesTouching ha, finsum_mem_eq_finite_toFinset_sum _ W.faces_finite]
  rfl
theorem heatBath_eq_wilsonLinkKernel (ha : 0 < a) (β' : ℝ) (W : OrientedLinkSet a)
    (F : GaugeField a → ℂ) (U : GaugeField a) :
    W.heatBath β' F U = wilsonLinkKernel β' W.links W.noOpposites F U := by
  rw [wilsonLinkKernel_apply]
  simp only [OrientedLinkSet.heatBath, OrientedLinkSet.boltzmannDensity,
    OrientedLinkSet.glue, OrientedLinkSet.resampleHaar, energy_eq_finsum ha,
    Complex.ofReal_div, ← mul_div_assoc]
  rw [integral_div]
theorem heatBathInvariant_iff (ha : 0 < a) (β' : ℝ) (ρ : ProbMeasure (GaugeField a)) :
    HeatBathInvariant β' ρ ↔
      AnyOrientationGibbs.PreservesContinuousLocal β' ρ.toMeasure := by
  constructor
  · intro h L hL F hF
    have e := h ⟨L, hL⟩ F ⟨hF.2.1, hF.2.2, hF.1⟩
    simp only [ProbMeasure.eval] at e
    rw [← e]
    exact integral_congr_ae (Filter.Eventually.of_forall fun U =>
      (heatBath_eq_wilsonLinkKernel ha β' ⟨L, hL⟩ F U).symm)
  · intro h W F hF
    have e := h W.links W.noOpposites F ⟨hF.2.2, hF.1, hF.2.1⟩
    simp only [ProbMeasure.eval]
    rw [← e]
    exact integral_congr_ae (Filter.Eventually.of_forall fun U =>
      heatBath_eq_wilsonLinkKernel ha β' W F U)
theorem reflectSymmetry_toNormalHyperplane (P : LatticeMirror a) :
    reflectSymmetry (toNormalHyperplane_isLatticeMirror P) = P.symmetry := by
  have h : (reflectSymmetry (toNormalHyperplane_isLatticeMirror P)).toFun = P.symmetry.toFun :=
    toNormalHyperplane_reflect P
  cases hr : reflectSymmetry (toNormalHyperplane_isLatticeMirror P)
  cases hs : P.symmetry
  rw [hr, hs] at h
  cases h
  rfl
theorem isReflectionPositiveAt_of_halfSpaces (ρ : ProbMeasure (GaugeField a)) (P : LatticeMirror a)
    (h : ∀ (hQ : (toNormalHyperplane P).IsLatticeMirror a),
      (∀ F ∈ regionObservables a (toNormalHyperplane P).upperHalfSpace,
        reflectedPairing hQ ρ.toMeasure F ≥ 0) ∧
      ∀ F ∈ regionObservables a (toNormalHyperplane P).lowerHalfSpace,
        reflectedPairing hQ ρ.toMeasure F ≥ 0) :
    IsReflectionPositiveAt ρ P := by
  obtain ⟨hp, hm⟩ := h (toNormalHyperplane_isLatticeMirror P)
  refine ⟨fun F hF _ => ?_, fun F hF _ => ?_⟩
  · have e := hp F hF
    rw [reflectedPairing, reflectSymmetry_toNormalHyperplane] at e
    exact e
  · have e := hm F hF
    rw [reflectedPairing, reflectSymmetry_toNormalHyperplane] at e
    exact e
theorem assertion_holds (hAll : PeriodicGibbsSymmetries.Statement)
    (hForms : AnyOrientationGibbs.Equivalences) : Assertion := by
  intro D β' hβ
  obtain ⟨hmirrors, hset, hne⟩ := hAll D.mesh D.mesh_pos β' hβ
  have hb : ∀ ρ : ProbMeasure (GaugeField D.mesh), IsPeriodicGibbs β' ρ.toMeasure →
      (∀ r : latticeMotions D.mesh,
        IsSymmetricUnder ρ.toMeasure (latticeMotionSymmetry r)) ∧
      IsShiftInvariant ρ.toMeasure ∧
      ∀ P : LatticeMirror D.mesh, IsReflectionPositiveAt ρ P := by
    intro ρ hρ
    obtain ⟨hmot, hpos⟩ := hmirrors ρ.toMeasure hρ
    have hmem : ρ.toMeasure ∈ PeriodicGibbsSymmetries.periodicStates D.mesh β' := hρ
    rw [hset] at hmem
    exact ⟨hmot, hmem.2, fun P => isReflectionPositiveAt_of_halfSpaces ρ P fun hQ =>
      (hpos (toNormalHyperplane P) hQ).2⟩
  refine ⟨fun ρ => ?_, hb, fun ρ hρ => ?_, hne⟩
  · have h := (hForms D.mesh β' D.mesh_pos hβ ρ.toMeasure inferInstance).out 0 1
    exact h.trans (heatBathInvariant_iff D.mesh_pos β' ρ).symm
  · obtain ⟨-, hT, hR⟩ := hb ρ hρ
    exact ⟨hT, hR⟩
end YangMills.Construction.LatticePhases.GibbsKernelsAndSymmetries
end
