import YangMills.Construction.InfiniteLattice.PeriodicExtensionAndPlaquetteActionsOfAPeriodLattice
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusOfAnyShape
import YangMills.Construction.InfiniteLattice.TorusOfAPeriodLatticeIsFinite
import YangMills.Construction.InfiniteLattice.WhatAnObservableDependsOnAndItsSupport
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace PeriodicQuotientProof
def intVecToPoint : (Fin 4 → ℤ) →+ LatticePoint 1 where
  toFun n := ⟨fun μ => (n μ : ℝ) * 1, n, fun _ => rfl⟩
  map_zero' := by
    ext μ
    simp
  map_add' n n' := by
    ext μ
    simp
theorem intVecToPoint_surjective : Function.Surjective intVecToPoint := by
  rintro ⟨x, n, hn⟩
  exact ⟨n, Subtype.ext (funext fun μ => (hn μ).symm)⟩
theorem finiteIndex_of_hasFullRank (H : AddSubgroup (LatticePoint 1))
    (hH : HasFullRank (H.map (latticeSubgroup 1).subtype)) : H.FiniteIndex := by
  obtain ⟨v, hv, hind⟩ := hH
  choose u hu huv using fun i => AddSubgroup.mem_map.1 (hv i)
  let N : Submodule ℤ (Fin 4 → ℤ) := AddSubgroup.toIntSubmodule (H.comap intVecToPoint)
  choose n hn using fun i => intVecToPoint_surjective (u i)
  have hnN : ∀ i, n i ∈ N := fun i => by
    change intVecToPoint (n i) ∈ H
    rw [hn]
    exact hu i
  let w : Fin 4 → N := fun i => ⟨n i, hnN i⟩
  let ι : N →ₗ[ℤ] AmbientSpace :=
    ((latticeSubgroup 1).subtype.comp (intVecToPoint.comp N.subtype.toAddMonoidHom)).toIntLinearMap
  have hcomp : (ι ∘ w) = v := by
    funext i
    change ((intVecToPoint (n i) : LatticePoint 1) : AmbientSpace) = v i
    rw [hn]
    exact huv i
  have hw : LinearIndependent ℤ w := by
    refine LinearIndependent.of_comp ι ?_
    rw [hcomp]
    exact hind.restrict_scalars (by simpa using Int.cast_injective)
  have hrank : Module.finrank ℤ N = Module.finrank ℤ (Fin 4 → ℤ) := by
    refine le_antisymm (Submodule.finrank_le N) ?_
    have h4 := hw.fintype_card_le_finrank
    simpa using h4
  have hfin : Finite ((Fin 4 → ℤ) ⧸ H.comap intVecToPoint) :=
    Submodule.finiteQuotientOfFreeOfRankEq N hrank
  have hidx : (H.comap intVecToPoint).index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  rw [AddSubgroup.index_comap_of_surjective _ intVecToPoint_surjective] at hidx
  exact ⟨hidx⟩
variable (Γ : PeriodSublattice 1)
theorem lift_injective : Function.Injective Γ.lift := by
  intro U U' h
  funext c
  rw [← Γ.linkClass_linkRep c, ← Γ.lift_apply_positive U,
    ← Γ.lift_apply_positive U', h]
theorem lift_congr_of_eq {U U' : Γ.QuotientField} {b : Link 1} (hb : b.IsPositivelyOriented)
    (h : U (Γ.linkClass ⟨b, hb⟩) = U' (Γ.linkClass ⟨b, hb⟩)) :
    Γ.lift U b = Γ.lift U' b := by
  rw [Γ.lift_apply_positive U ⟨b, hb⟩, Γ.lift_apply_positive U' ⟨b, hb⟩, h]
theorem forwardFrom_isPositivelyOriented (x : LatticePoint 1) (μ : Fin 4) :
    (Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, add_sub_cancel_left _ _⟩
theorem faceEnergy_dependsOn_plaquetteLinks (p : Γ.QuotientPlaquette) :
    PeriodSublattice.DependsOnlyOn (fun U => Γ.quotientFaceEnergy U p)
      (Γ.plaquetteLinks p) := by
  intro U U' h
  have key : ∀ x μ, Link.forwardFrom x μ ∈ (Γ.plaquetteRep p).linkSet →
      Γ.lift U (Link.forwardFrom x μ) = Γ.lift U' (Link.forwardFrom x μ) :=
    fun x μ hm => lift_congr_of_eq Γ (forwardFrom_isPositivelyOriented x μ)
      (h _ ⟨⟨_, forwardFrom_isPositivelyOriented x μ⟩, hm, rfl⟩)
  change faceEnergy (Γ.lift U) (Γ.plaquetteRep p) =
    faceEnergy (Γ.lift U') (Γ.plaquetteRep p)
  unfold faceEnergy faceHolonomy
  rw [key _ _ (by simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges]),
    key _ _ (by simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges]),
    key _ _ (by simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges]),
    key _ _ (by simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges])]
theorem measurable_lift (hc : Continuous Γ.lift) :
    Measurable Γ.lift := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact hc.measurable
theorem integral_map_lift_eq (hc : Continuous Γ.lift)
    (μ : Measure Γ.QuotientField) (F : GaugeField 1 → ℂ) (hF : IsBoundedObservable F) :
    ∫ U, F U ∂(μ.map Γ.lift) = ∫ U, F (Γ.lift U) ∂μ :=
  integral_map (measurable_lift Γ hc).aemeasurable hF.1.aestronglyMeasurable
theorem periodize_supNorm_le (F : GaugeField 1 → ℂ) (hF : IsBoundedObservable F) :
    PeriodSublattice.supNorm (Γ.periodize F) ≤ observableSupNorm F := by
  obtain ⟨C, hC⟩ := hF.2
  exact ciSup_le fun U =>
    le_ciSup (f := fun V : GaugeField 1 => ‖F V‖) ⟨C, by rintro _ ⟨V, rfl⟩; exact hC V⟩
      (Γ.lift U)
theorem periodize_dependsOn_linkClassImage (F : GaugeField 1 → ℂ) {M : Set (Link 1)}
    (hset : IsLinkSet M) (hdep : DependsOnlyOn M F) :
    PeriodSublattice.DependsOnlyOn (Γ.periodize F) (Γ.linkClassImage M) := by
  intro U U' h
  refine hdep _ _ fun b hb => ?_
  have hp : b.IsPositivelyOriented := hset hb
  exact lift_congr_of_eq Γ hp (h _ ⟨⟨b, hp⟩, hb, rfl⟩)
end PeriodicQuotientProof
open PeriodicQuotientProof in
theorem periodicQuotient_finitenessClaim
    (hFinite : PeriodQuotientFinite)
    (hExtension : PeriodicLiftAndQuotientEnergiesStatement)
    (hSupport : ObservableDependence.Statement) :
    PeriodicQuotient.FinitenessClaim := by
  refine ⟨fun Γ => ?_, finiteIndex_of_hasFullRank⟩
  obtain ⟨hTorus, hLinks, hPlaquettes⟩ := hFinite 1 one_pos Γ
  obtain ⟨⟨hInvariant, hContinuous, hLifts, hEnergy⟩, -⟩ := hExtension 1 one_pos Γ
  have hSupportOf : ∀ F ∈ continuousLocalFunctions 1,
      IsLinkSet (observableSupport F) ∧
        DependsOnlyOn (observableSupport F) F := fun F hF => by
    obtain ⟨-, -, -, -, hLeast, -⟩ := hSupport F hF.1 ∅ ∅ (Set.empty_subset _)
      (Set.empty_subset _) Set.univ
    exact (hLeast hF.2.1).1.1
  exact
    { periods_finiteIndex := finiteIndex_of_hasFullRank Γ.periods Γ.hasFullRank
      finite_quotientTorus := hTorus
      finite_quotientLink := hLinks
      finite_quotientPlaquette := hPlaquettes
      lift_apply_link := fun U b => (Γ.orientedValue_orientedClass U b).symm
      lift_shift_invariant := hInvariant
      continuous_lift := hContinuous
      injective_lift := lift_injective Γ
      faceEnergy_lifts_eq := fun p U q q' hq hq' => hLifts U p q hq q' hq'
      continuous_quotientFaceEnergy := fun p => (hEnergy p).1
      quotientFaceEnergy_mem_Icc := fun p U => (hEnergy p).2 U
      quotientFaceEnergy_dependsOn := faceEnergy_dependsOn_plaquetteLinks Γ
      continuous_periodize := fun F hF => hF.2.2.comp hContinuous
      supNorm_periodize_le := fun F hF => periodize_supNorm_le Γ F hF.1
      periodize_dependsOn := fun F hF =>
        periodize_dependsOn_linkClassImage Γ F (hSupportOf F hF).1 (hSupportOf F hF).2
      measurable_bounded_comp_lift := fun F hF => by
        obtain ⟨C, hC⟩ := hF.2
        exact ⟨hF.1.comp (measurable_lift Γ hContinuous), C, fun U => hC _⟩
      integral_map_lift := fun μ _ F hF => integral_map_lift_eq Γ hContinuous μ F hF
      integral_map_lift_eq_periodize := fun μ _ F hF =>
        integral_map_lift_eq Γ hContinuous μ F hF.1 }
end YangMills.Construction.InfiniteLattice
