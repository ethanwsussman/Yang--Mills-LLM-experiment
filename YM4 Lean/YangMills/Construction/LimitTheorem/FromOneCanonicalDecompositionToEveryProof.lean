import YangMills.Construction.LimitTheorem.FromOneCanonicalDecompositionToEvery
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.LimitTheorem.DecompositionTransfer
open SeparatedTuples ReflectionPositivity.TupleForm
open HilbertSpaceBasics (IsPosSemidef)
open ReflectionPositivity.Reconstruction (posClass)
open ReflectionPositivity.PairMeasureOperators (groundStateProjection)
open InfiniteLattice (AmbientSpace)
variable {A B : DecompositionData}
private theorem measurePreserving_of_map_eq (e : A.space ≃ₜ B.space)
    (hmap : A.law.map e = B.law) : MeasurePreserving e A.law B.law :=
  ⟨e.continuous.measurable, hmap⟩
private theorem measurePreserving_symm_of_map_eq (e : A.space ≃ₜ B.space)
    (hmap : A.law.map e = B.law) : MeasurePreserving e.symm B.law A.law := by
  have hmp := measurePreserving_of_map_eq e hmap
  exact MeasurePreserving.symm e.toMeasurableEquiv hmp
private def compHomeomorphL2 (e : A.space ≃ₜ B.space) (hmap : A.law.map e = B.law) :
    Lp ℂ 2 B.law ≃ₗᵢ[ℂ] Lp ℂ 2 A.law :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ e (measurePreserving_of_map_eq e hmap)) (by
      intro g
      have hmp := measurePreserving_of_map_eq e hmap
      have hmp' := measurePreserving_symm_of_map_eq e hmap
      refine ⟨Lp.compMeasurePreservingₗᵢ ℂ e.symm hmp' g, ?_⟩
      apply Lp.ext
      have hfirst := Lp.coeFn_compMeasurePreserving
        (Lp.compMeasurePreservingₗᵢ ℂ e.symm hmp' g) hmp
      have hsecond := Lp.coeFn_compMeasurePreserving g hmp'
      have hthird : ((Lp.compMeasurePreservingₗᵢ ℂ e.symm hmp' g : Lp ℂ 2 B.law) : B.space → ℂ) ∘ e
          =ᵐ[A.law] (g : A.space → ℂ) ∘ e.symm ∘ e :=
        hmp.quasiMeasurePreserving.ae_eq_comp hsecond
      refine hfirst.trans (hthird.trans ?_)
      exact Filter.Eventually.of_forall fun x => by simp)
private theorem compHomeomorphL2_coeFn (e : A.space ≃ₜ B.space) (hmap : A.law.map e = B.law)
    (u : Lp ℂ 2 B.law) :
    (compHomeomorphL2 e hmap u : A.space → ℂ) =ᵐ[A.law] (u : B.space → ℂ) ∘ e :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_of_map_eq e hmap)
private theorem groundStatesAsL2_of_homeomorph {φ : TupleFunctional} (e : A.space ≃ₜ B.space)
    (hmap : A.law.map e = B.law) (hcomp : ∀ x, B.comp (e x) = A.comp x)
    (hground : GroundStatesAsL2 φ B) : GroundStatesAsL2 φ A := by
  intro hpos
  obtain ⟨U, hU, hvac, hcard⟩ := hground hpos
  have hmp := measurePreserving_of_map_eq e hmap
  refine ⟨U.trans (compHomeomorphL2 e hmap), ?_, ?_, ?_⟩
  · intro F
    obtain ⟨hmem, hval⟩ := hU F
    refine ⟨hmem, ?_⟩
    have hfirst := compHomeomorphL2_coeFn e hmap (U ⟨_, hmem⟩)
    have hsecond := hmp.quasiMeasurePreserving.ae_eq_comp hval
    refine hfirst.trans (hsecond.trans ?_)
    exact Filter.Eventually.of_forall fun x => by simp [hcomp]
  · obtain ⟨hmem, hval⟩ := hvac
    refine ⟨hmem, ?_⟩
    have hfirst := compHomeomorphL2_coeFn e hmap (U ⟨_, hmem⟩)
    have hsecond := hmp.quasiMeasurePreserving.ae_eq_comp hval
    exact hfirst.trans hsecond
  · rw [← hcard]
    exact ENat.card_congr e.toEquiv
private theorem inner_groundStateProjection_eq_integral {φ : TupleFunctional}
    (hpos : IsPosSemidef (reflectionForm φ))
    (U : hamiltonianKernel φ hpos ≃ₗᵢ[ℂ] Lp ℂ 2 A.law) (F F' : PositiveSpan)
    (hF : ∃ hmem : groundStateProjection φ hpos (posClass φ hpos F) ∈ hamiltonianKernel φ hpos,
      (U ⟨_, hmem⟩ : A.space → ℂ) =ᵐ[A.law] fun x => (A.comp x).spanExtension F.1)
    (hF' : ∃ hmem : groundStateProjection φ hpos (posClass φ hpos F') ∈ hamiltonianKernel φ hpos,
      (U ⟨_, hmem⟩ : A.space → ℂ) =ᵐ[A.law] fun x => (A.comp x).spanExtension F'.1) :
    ⟪groundStateProjection φ hpos (posClass φ hpos F),
        groundStateProjection φ hpos (posClass φ hpos F')⟫_ℂ =
      ∫ x, (starRingEnd ℂ) ((A.comp x).spanExtension F.1) *
        (A.comp x).spanExtension F'.1 ∂A.law := by
  obtain ⟨hmem, hval⟩ := hF
  obtain ⟨hmem', hval'⟩ := hF'
  have hinner : ⟪groundStateProjection φ hpos (posClass φ hpos F),
        groundStateProjection φ hpos (posClass φ hpos F')⟫_ℂ =
      ⟪U ⟨_, hmem⟩, U ⟨_, hmem'⟩⟫_ℂ := by
    rw [U.inner_map_map]
    rfl
  rw [hinner, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hval, hval'] with x ha hb
  rw [ha, hb, RCLike.inner_apply, mul_comm]
private theorem transported_isCanonical {φ : TupleFunctional} {r : AmbientSpace → AmbientSpace}
    (hA : A.IsCanonical φ) (hperm : PermutesComponents A r) :
    (transportedDecomposition A r).IsCanonical φ := by
  obtain ⟨k, hk, hkcomp⟩ := hperm
  have hmp : MeasurePreserving k A.law A.law := ⟨k.continuous.measurable, hk⟩
  have hcomp : ∀ x, (transportedDecomposition A r).comp x = A.comp (k x) :=
    fun x => (hkcomp x).symm
  exact
    { compact := hA.compact
      metrizable := hA.metrizable
      isProb := hA.isProb
      measureSupport_eq := hA.measureSupport_eq
      comp_permInvariant := fun x => by rw [hcomp]; exact hA.comp_permInvariant (k x)
      comp_entrywiseLinear := fun x => by rw [hcomp]; exact hA.comp_entrywiseLinear (k x)
      continuous_comp := fun X => by
        have hfun : (fun x => (transportedDecomposition A r).comp x X) =
            fun x => A.comp (k x) X :=
          funext fun x => by rw [hcomp]
        rw [hfun]
        exact (hA.continuous_comp X).comp k.continuous
      comp_injective := fun x x' hxx => by
        rw [hcomp, hcomp] at hxx
        exact k.injective (hA.comp_injective hxx)
      iterLimits_exist := hA.iterLimits_exist
      integral_comp_prod := fun X Y => by
        rw [← hA.integral_comp_prod X Y]
        have hint := hmp.integral_comp k.measurableEmbedding
          (fun x => A.comp x X * (Y.map fun Z => A.comp x Z).prod)
        refine Eq.trans ?_ hint
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change (compInv (A.comp x) r) X *
            (Y.map fun Z => (compInv (A.comp x) r) Z).prod = _
        rw [← hkcomp x] }
theorem transferStatement_holds : TransferStatement := by
  intro φ B A hB hA
  obtain ⟨e, hmap, hcomp⟩ := hB.isomorphic_of_canonical A hA
  have hground := groundStatesAsL2_of_homeomorph e hmap hcomp hB.groundStates
  have hperm : ∀ r : AmbientSpace → AmbientSpace, IsEuclidIsometry r → φ.IsInvariant r →
      PermutesComponents A r := by
    intro r hr hφ
    obtain ⟨k, hk, hkcomp⟩ := hB.permutes r hr hφ
    have hmp := measurePreserving_of_map_eq e hmap
    have hmp' := measurePreserving_symm_of_map_eq e hmap
    have hmpk : MeasurePreserving k B.law B.law := ⟨k.continuous.measurable, hk⟩
    refine ⟨(e.trans k).trans e.symm, ?_, ?_⟩
    · exact ((hmp'.comp hmpk).comp hmp).map_eq
    · intro x
      have hpush : B.comp (e (((e.trans k).trans e.symm) x)) =
          A.comp (((e.trans k).trans e.symm) x) := hcomp _
      rw [← hpush]
      simp only [Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
      rw [hkcomp, hcomp]
  refine ⟨⟨⟨e, hmap, hcomp, ?_⟩, ?_⟩, ⟨hground, ?_⟩, hperm, ?_⟩
  · intro f hf
    funext x
    exact hB.isCanonical.comp_injective ((hf x).trans (hcomp x).symm)
  · ext t
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, hcomp x⟩
    · rintro ⟨y, rfl⟩
      refine ⟨e.symm y, ?_⟩
      rw [← hcomp, e.apply_symm_apply]
  · intro hpos
    obtain ⟨U, hU, hvac, hcard⟩ := hground hpos
    refine ⟨fun F F' => inner_groundStateProjection_eq_integral hpos U F F' (hU F) (hU F'), ?_, ?_⟩
    · rw [hcard, U.toLinearEquiv.rank_eq]
    · exact U.toLinearEquiv.rank_eq.symm
  · intro r hr hφ
    exact transported_isCanonical hA (hperm r hr hφ)
end YangMills.Construction.LimitTheorem.DecompositionTransfer
end
