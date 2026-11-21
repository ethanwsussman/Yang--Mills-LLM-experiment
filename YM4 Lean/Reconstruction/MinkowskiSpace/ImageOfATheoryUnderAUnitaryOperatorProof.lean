import Reconstruction.MinkowskiSpace.ArgumentsOfTheFieldProductsOfAWightmanTheoryLieInTheirDomainsProof
import Reconstruction.MinkowskiSpace.ImageOfATheoryUnderAUnitaryOperator
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.MinkowskiSpace.UnitaryImage
open YangMills.Construction.MinkowskiSpace YangMills.Construction.WightmanTheory YangMills.Construction.ProjectionMeasures YangMills.Construction.OneLoopNotation YangMills.Construction.FormsOperators YangMills.Construction.ComplexHilbert YangMills.Construction.FormReconstruction YangMills.Construction.PVMCalculus
variable {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
omit [CompleteSpace E] [CompleteSpace E'] in
theorem inner_unitary_apply (U : UnitaryMap E E') (y : E') (x : E) :
    ⟪y, U x⟫_ℂ = ⟪U.symm y, x⟫_ℂ := by
  rw [← U.inner_map_map (U.symm y) x, U.apply_symm_apply]
def restrictSubmodule (U : UnitaryMap E E') (D : Submodule ℂ E) :
    D ≃ₗ[ℂ] D.map (U.toLinearEquiv : E →ₗ[ℂ] E') :=
  U.toLinearEquiv.submoduleMap D
omit [CompleteSpace E] [CompleteSpace E'] in
theorem coe_restrictSubmodule (U : UnitaryMap E E') (D : Submodule ℂ E) (x : D) :
    ((restrictSubmodule U D x : D.map (U.toLinearEquiv : E →ₗ[ℂ] E')) : E') = U x := rfl
omit [CompleteSpace E] [CompleteSpace E'] in
theorem apply_coe_restrictSubmodule_symm (U : UnitaryMap E E') (D : Submodule ℂ E)
    (v : D.map (U.toLinearEquiv : E →ₗ[ℂ] E')) :
    U ((restrictSubmodule U D).symm v : D) = v := by
  rw [← coe_restrictSubmodule, LinearEquiv.apply_symm_apply]
theorem foldr_equiv_conj {D D' F : Type*} (e : D ≃ D') (φ : F → D → D) (l : List F) (v : D) :
    l.foldr (fun f w => e (φ f (e.symm w))) (e v) = e (l.foldr φ v) := by
  induction l with
  | nil => rfl
  | cons f l ih => simp [List.foldr_cons, ih]
def mapTheory (U : UnitaryMap E E') (T : HermitianScalarTheory E) : HermitianScalarTheory E' where
  rep g := (U.symm.trans (T.rep g)).trans U
  rep_mul g g' g'' h := by
    ext x
    simp [T.rep_mul g g' g'' h]
  rep_continuous x :=
    U.continuous.comp (T.rep_continuous (U.symm x))
  vacuum := U T.vacuum
  norm_vacuum := by rw [U.norm_map, T.norm_vacuum]
  rep_vacuum g := by simp [T.rep_vacuum]
  domain := T.domain.map (U.toLinearEquiv : E →ₗ[ℂ] E')
  dense_domain := by
    rw [Submodule.map_coe]
    exact U.surjective.denseRange.dense_image U.continuous T.dense_domain
  vacuum_mem_domain := ⟨T.vacuum, T.vacuum_mem_domain, rfl⟩
  rep_mem_domain g := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨T.rep g x, T.rep_mem_domain g x hx, by simp⟩
  field f := (restrictSubmodule U T.domain).toLinearMap ∘ₗ T.field f ∘ₗ
    (restrictSubmodule U T.domain).symm.toLinearMap
  field_linear a b f f' f'' h := by
    rw [T.field_linear a b f f' f'' h]
    ext v
    simp
  field_tempered v v' := by
    obtain ⟨k, c, hk, hc, hb⟩ := T.field_tempered ((restrictSubmodule U T.domain).symm v)
      ((restrictSubmodule U T.domain).symm v')
    refine ⟨k, c, hk, hc, fun f => ?_⟩
    have hbf := hb f
    have e₁ : ⟪(v : E'), ((((restrictSubmodule U T.domain).toLinearMap ∘ₗ T.field f ∘ₗ
        (restrictSubmodule U T.domain).symm.toLinearMap) v' :
          T.domain.map (U.toLinearEquiv : E →ₗ[ℂ] E')) : E')⟫_ℂ =
        ⟪(((restrictSubmodule U T.domain).symm v : T.domain) : E),
          (T.field f ((restrictSubmodule U T.domain).symm v') : E)⟫_ℂ := by
      rw [← apply_coe_restrictSubmodule_symm U T.domain v]
      exact U.inner_map_map _ _
    rw [e₁]
    exact hbf
  field_hermitian f := by
    obtain ⟨f', hf', hadj⟩ := T.field_hermitian f
    refine ⟨f', hf', fun v v' => ?_⟩
    have e₁ := hadj ((restrictSubmodule U T.domain).symm v) ((restrictSubmodule U T.domain).symm v')
    have e₂ : ⟪(v : E'), ((((restrictSubmodule U T.domain).toLinearMap ∘ₗ T.field f ∘ₗ
        (restrictSubmodule U T.domain).symm.toLinearMap) v' :
          T.domain.map (U.toLinearEquiv : E →ₗ[ℂ] E')) : E')⟫_ℂ =
        ⟪(((restrictSubmodule U T.domain).symm v : T.domain) : E),
          (T.field f ((restrictSubmodule U T.domain).symm v') : E)⟫_ℂ := by
      rw [← apply_coe_restrictSubmodule_symm U T.domain v]
      exact U.inner_map_map _ _
    have e₃ : ⟪((((restrictSubmodule U T.domain).toLinearMap ∘ₗ T.field f' ∘ₗ
        (restrictSubmodule U T.domain).symm.toLinearMap) v :
          T.domain.map (U.toLinearEquiv : E →ₗ[ℂ] E')) : E'), (v' : E')⟫_ℂ =
        ⟪(T.field f' ((restrictSubmodule U T.domain).symm v) : E),
          (((restrictSubmodule U T.domain).symm v' : T.domain) : E)⟫_ℂ := by
      rw [← apply_coe_restrictSubmodule_symm U T.domain v']
      exact U.inner_map_map _ _
    rw [e₂, e₃, e₁]
  vacuum_cyclic := by
    have hset : (Set.range fun p : Σ n : ℕ, (Fin n → TestFn) =>
        ((fieldWord (fun f v => ((restrictSubmodule U T.domain).toLinearMap ∘ₗ T.field f ∘ₗ
          (restrictSubmodule U T.domain).symm.toLinearMap) v) p.2
          (⟨U T.vacuum, ⟨T.vacuum, T.vacuum_mem_domain, rfl⟩⟩ :
            T.domain.map (U.toLinearEquiv : E →ₗ[ℂ] E')) :
          T.domain.map (U.toLinearEquiv : E →ₗ[ℂ] E')) : E')) =
        (U.toLinearEquiv : E →ₗ[ℂ] E') '' (Set.range fun p : Σ n : ℕ, (Fin n → TestFn) =>
          ((fieldWord (fun f v => T.field f v) p.2 ⟨T.vacuum, T.vacuum_mem_domain⟩ : T.domain) : E)) := by
      rw [← Set.range_comp]
      congr 1
      funext p
      exact congrArg Subtype.val
        (foldr_equiv_conj (restrictSubmodule U T.domain).toEquiv (fun f v => T.field f v)
          (List.ofFn p.2) ⟨T.vacuum, T.vacuum_mem_domain⟩)
    rw [hset, ← Submodule.map_span, Submodule.map_coe]
    exact U.surjective.denseRange.dense_image U.continuous T.vacuum_cyclic
omit [CompleteSpace E] [CompleteSpace E'] in
theorem coe_restrictSubmodule_symm (U : UnitaryMap E E') (D : Submodule ℂ E)
    (v : D.map (U.toLinearEquiv : E →ₗ[ℂ] E')) :
    (((restrictSubmodule U D).symm v : D) : E) = U.symm v := by
  rw [← apply_coe_restrictSubmodule_symm U D v, U.symm_apply_apply]
theorem mapTheory_isUnitaryImage (U : UnitaryMap E E') (T : HermitianScalarTheory E) :
    IsUnitaryImage U T (mapTheory U T) where
  rep_eq g x := by
    show U (T.rep g (U.symm (U x))) = _
    rw [U.symm_apply_apply]
  vacuum_eq := rfl
  domain_eq := rfl
  field_eq f v v' h := by
    have hv : v' = restrictSubmodule U T.domain v := Subtype.ext h
    subst hv
    show U (T.field f ((restrictSubmodule U T.domain).symm (restrictSubmodule U T.domain v))) = _
    rw [LinearEquiv.symm_apply_apply]
theorem wightmanFn_mapTheory (U : UnitaryMap E E') (T : HermitianScalarTheory E) {n : ℕ}
    (f : Fin n → TestFn) :
    (mapTheory U T).wightmanFn f = T.wightmanFn f := by
  have hw : ((fieldWord (fun f v => (mapTheory U T).field f v) f
      (mapTheory U T).vacuumVec : (mapTheory U T).domain) : E') =
      U ((fieldWord (fun f v => T.field f v) f T.vacuumVec : T.domain) : E) :=
    congrArg Subtype.val (foldr_equiv_conj (restrictSubmodule U T.domain).toEquiv
      (fun f v => T.field f v) (List.ofFn f) T.vacuumVec)
  unfold HermitianScalarTheory.wightmanFn
  rw [hw]
  exact U.inner_map_map _ _
omit [CompleteSpace E] [CompleteSpace E'] in
theorem isUnitaryMap_symm (U : UnitaryMap E E') :
    IsUnitaryMap (U.symm.toLinearEquiv : E' →ₗ[ℂ] E) :=
  ⟨fun x => U.symm.norm_map x, U.symm.surjective⟩
theorem unitaryConj_symm_apply (U : UnitaryMap E E') (A : BddOp E) (y : E') :
    unitaryConj (isUnitaryMap_symm U) A y = U (A (U.symm y)) := by
  have hU : unitaryIsometry (isUnitaryMap_symm U) = U.symm := by
    ext x
    rfl
  unfold PVMCalculus.unitaryConj
  rw [hU]
  rfl
def conjMeasure (U : UnitaryMap E E') (P : FourBorelSet → BddOp E) :
    FourBorelSet → BddOp E' :=
  fun B => unitaryConj (isUnitaryMap_symm U) (P B)
theorem spectralScalarMeasure_conjMeasure (U : UnitaryMap E E') (P : FourBorelSet → BddOp E)
    (y y' : E') :
    spectralScalarMeasure (conjMeasure U P) y y' = spectralScalarMeasure P (U.symm y) (U.symm y') := by
  funext B
  simp only [spectralScalarMeasure, conjMeasure, unitaryConj_symm_apply]
  exact inner_unitary_apply U y _
theorem isEnergyMomentumMeasure_conjMeasure
    (hC : BoundedFunctionalCalculus)
    (U : UnitaryMap E E') (T : HermitianScalarTheory E) {P : FourBorelSet → BddOp E}
    (hP : T.IsEnergyMomentumMeasure P) :
    (mapTheory U T).IsEnergyMomentumMeasure (conjMeasure U P) := by
  have hc := ((hC.2 E).2 P closedFutureConeBorel hP.isPVM
    hP.supportedOn).2.2.2.2.2.1 E' _ (isUnitaryMap_symm U)
  refine ⟨hc.1, hc.2.1, fun a y y' => ?_⟩
  rw [spectralScalarMeasure_conjMeasure, ← hP.translation_eq a (U.symm y) (U.symm y')]
  exact inner_unitary_apply U y _
theorem isBddMeasurableFun_expDecay {t : ℝ} (ht : 0 ≤ t) :
    IsBddMeasurableFun
      (closedFutureCone.indicator fun p : RealVec4 => Complex.exp (-((t * p 0 : ℝ) : ℂ))) := by apply _root_.YangMills.Construction.WightmanTheory.DomainFacts.decay_indicator_isBddMeasurable <;> assumption
theorem hamiltonianSemigroup_conjMeasure
    (hC : BoundedFunctionalCalculus)
    (U : UnitaryMap E E') (T : HermitianScalarTheory E) {P : FourBorelSet → BddOp E}
    (hP : T.IsEnergyMomentumMeasure P) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    HermitianScalarTheory.hamiltonianSemigroup (conjMeasure U P) t (U x) =
      U (HermitianScalarTheory.hamiltonianSemigroup P t x) := by
  have hc := ((hC.2 E).2 P closedFutureConeBorel hP.isPVM
    hP.supportedOn).2.2.2.2.2.1 E' _ (isUnitaryMap_symm U)
  have hexp := hc.2.2 _ (isBddMeasurableFun_expDecay ht)
  unfold HermitianScalarTheory.hamiltonianSemigroup conjMeasure
  rw [hexp, unitaryConj_symm_apply, U.symm_apply_apply]
theorem isTheoryOf_mapTheory
    (hC : BoundedFunctionalCalculus)
    (U : UnitaryMap E E') (T : HermitianScalarTheory E) (S : YangMills.Construction.ConfigSpace.FlatSequence)
    (hS : IsTheoryOf T S) : IsTheoryOf (mapTheory U T) S where
  schwinger := by
    refine ⟨hS.schwinger.1, fun m => ?_⟩
    obtain ⟨w, q, c, s, hm⟩ := hS.schwinger.2 m
    refine ⟨w, q, c, s, { hm with boundary_values := fun f => ?_ }⟩
    rw [wightmanFn_mapTheory]
    exact hm.boundary_values f
  covariant g f := by
    obtain ⟨f', hf', hcov⟩ := hS.covariant g f
    refine ⟨f', hf', fun v => ?_⟩
    obtain ⟨v₀, h₀, h₁⟩ := hcov ((restrictSubmodule U T.domain).symm v)
    refine ⟨restrictSubmodule U T.domain v₀, ?_, ?_⟩
    · have h₂ : (v₀ : E) = (T.rep g).symm (U.symm (v : E')) :=
        h₀.trans (congrArg (T.rep g).symm (coe_restrictSubmodule_symm U T.domain v))
      show U (v₀ : E) = U ((T.rep g).symm (U.symm (v : E')))
      rw [h₂]
    · show U (T.rep g (U.symm (U (T.field f
        ((restrictSubmodule U T.domain).symm (restrictSubmodule U T.domain v₀)) : E)))) =
        U (T.field f' ((restrictSubmodule U T.domain).symm v) : E)
      rw [U.symm_apply_apply, LinearEquiv.symm_apply_apply, h₁]
  spectrum := by
    obtain ⟨P, hP⟩ := hS.spectrum
    exact ⟨_, isEnergyMomentumMeasure_conjMeasure hC U T hP⟩
  localField v f h hsupp := by
    have h₁ := hS.localField ((restrictSubmodule U T.domain).symm v) f h hsupp
    show restrictSubmodule U T.domain (T.field f ((restrictSubmodule U T.domain).symm
        (restrictSubmodule U T.domain (T.field h ((restrictSubmodule U T.domain).symm v))))) =
      restrictSubmodule U T.domain (T.field h ((restrictSubmodule U T.domain).symm
        (restrictSubmodule U T.domain (T.field f ((restrictSubmodule U T.domain).symm v)))))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, h₁]
theorem unitaryImageExists (hC : BoundedFunctionalCalculus) :
    UnitaryImageExists := by
  intro E E' _ _ _ _ _ _ U T
  exact ⟨mapTheory U T, mapTheory_isUnitaryImage U T, fun S hS => isTheoryOf_mapTheory hC U T S hS,
    fun P hP => ⟨conjMeasure U P, isEnergyMomentumMeasure_conjMeasure hC U T hP,
      fun t x ht => hamiltonianSemigroup_conjMeasure hC U T hP ht x⟩⟩
end YangMills.Construction.MinkowskiSpace.UnitaryImage
end
