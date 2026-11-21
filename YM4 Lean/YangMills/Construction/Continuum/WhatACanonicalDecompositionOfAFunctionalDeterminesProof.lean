import YangMills.Construction.Continuum.WhatACanonicalDecompositionOfAFunctionalDetermines
import YangMills.Construction.Measures.MomentsDetermineSpaceAndMeasure
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotions
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set Topology
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.CanonicalDecompositionUniqueness
open YangMills.Construction.SeparatedTuples YangMills.Construction.ReflectionPositivity.TupleForm
open YangMills.Construction.LimitTheorem (transportedDecomposition compInv)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.ReflectionPositivity.Reconstruction (posTupleVec timeBasisVec)
private theorem tupleFunctional_ext {σ τ : TupleFunctional} (h : ∀ X, σ X = τ X) : σ = τ := by
  cases σ; cases τ
  congr
  exact funext h
abbrev _root_.YangMills.SharedProofs.p5793 := @tupleFunctional_ext
private theorem momentSupport_eq_univ {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] {μ : Measure Y}
    (h : measureSupport μ = Set.univ) :
    Measures.MomentDetermination.measureSupport μ = Set.univ := by
  ext x
  simp only [Measures.MomentDetermination.measureSupport, mem_ofPred_eq, mem_univ, iff_true]
  intro U hU hx
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have hx' : x ∈ measureSupport μ := by rw [h]; trivial
  exact hx' (mem_sUnion.2 ⟨U, ⟨hU, h0⟩, hx⟩)
private theorem law_pos_of_isOpen {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] {μ : Measure Y}
    (h : measureSupport μ = Set.univ) {U : Set Y} (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U := by
  obtain ⟨x, hx⟩ := hne
  have := momentSupport_eq_univ h
  have hx' : x ∈ Measures.MomentDetermination.measureSupport μ := by
    rw [this]; trivial
  exact hx' U hU hx
private theorem integral_prod_fin {σ : TupleFunctional} {A : DecompositionData}
    (hA : A.IsCanonical σ) {n : ℕ} (t : Fin (n + 1) → SepTuple) :
    ∫ ξ, ∏ i, A.comp ξ (t i) ∂A.law =
      iteratedLimitAtInfinity σ (t 0) (List.ofFn fun i : Fin n => t i.succ) Set.univ := by
  rw [← hA.integral_comp_prod]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp [Fin.prod_univ_succ, List.map_ofFn, List.prod_ofFn, Function.comp_def]
private theorem uniquelyIsomorphic_of_canonical (hM : Measures.MomentDetermination.mixedMoments_determine)
    {σ : TupleFunctional} {A B : DecompositionData} (hA : A.IsCanonical σ)
    (hB : B.IsCanonical σ) : IsUniquelyIsomorphic A B := by
  have := hA.compact
  have := hA.metrizable
  have := hB.compact
  have := hB.metrizable
  have sep : ∀ (C : DecompositionData), C.IsCanonical σ → ∀ a b : C.space, a ≠ b →
      ∃ y : SepTuple, (fun ξ => C.comp ξ y) a ≠ (fun ξ => C.comp ξ y) b := by
    intro C hC a b hab
    by_contra hcon
    push Not at hcon
    exact hab (hC.comp_injective (tupleFunctional_ext hcon))
  obtain ⟨h, h₁, h₂, h₃, h₄⟩ := hM SepTuple A.space B.space A.law B.law
    (fun y ξ => A.comp ξ y) (fun y ξ => B.comp ξ y)
    hA.isProb hB.isProb
    (momentSupport_eq_univ hA.measureSupport_eq) (momentSupport_eq_univ hB.measureSupport_eq)
    hA.continuous_comp hB.continuous_comp (sep A hA) (sep B hB)
    (by
      intro q hq t
      obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
      rw [integral_prod_fin hA t, integral_prod_fin hB t])
  refine ⟨h, fun ξ => tupleFunctional_ext fun X => congrFun (h₁ X) ξ, fun k hk => h₂ k fun y => ?_, h₃, h₄⟩
  funext ξ
  simp [hk ξ]
section RigidMotions
variable {r : AmbientSpace → AmbientSpace} {R L : Matrix (Fin 4) (Fin 4) ℝ} {c : AmbientSpace}
private structure IsAffineIsometry (r : AmbientSpace → AmbientSpace) (R L : Matrix (Fin 4) (Fin 4) ℝ)
    (c : AmbientSpace) : Prop where
  apply_eq : ∀ x, r x = R.mulVec x + c
  mul_inv : R * L = 1
  inv_mul : L * R = 1
  isEuclidIsometry : IsEuclidIsometry r
private theorem IsAffineIsometry.injective (h : IsAffineIsometry r R L c) : Function.Injective r := by
  intro x y hxy
  rw [h.apply_eq, h.apply_eq] at hxy
  have h₁ : R.mulVec x = R.mulVec y := add_right_cancel hxy
  have h₂ := congrArg L.mulVec h₁
  simpa [Matrix.mulVec_mulVec, h.inv_mul] using h₂
private theorem IsAffineIsometry.apply_invForm (h : IsAffineIsometry r R L c) (x : AmbientSpace) :
    r (L.mulVec (x - c)) = x := by
  rw [h.apply_eq, Matrix.mulVec_mulVec, h.mul_inv]
  simp
private theorem IsAffineIsometry.invMap_apply (h : IsAffineIsometry r R L c) (x : AmbientSpace) :
    invMap r x = L.mulVec (x - c) := by
  have hx := h.apply_invForm x
  calc invMap r x = invMap r (r (L.mulVec (x - c))) := by rw [hx]
    _ = L.mulVec (x - c) := Function.leftInverse_invFun h.injective _
private theorem IsAffineIsometry.apply_invMap (h : IsAffineIsometry r R L c) (x : AmbientSpace) :
    r (invMap r x) = x := by
  rw [h.invMap_apply, h.apply_invForm]
private theorem IsAffineIsometry.invMap_apply_self (h : IsAffineIsometry r R L c) (x : AmbientSpace) :
    invMap r (r x) = x :=
  Function.leftInverse_invFun h.injective x
private theorem IsAffineIsometry.invMap_invMap (h : IsAffineIsometry r R L c) : invMap (invMap r) = r := by
  funext x
  have hinj : Function.Injective (invMap r) := fun a b hab => by
    have := congrArg r hab
    rwa [h.apply_invMap, h.apply_invMap] at this
  calc invMap (invMap r) x = invMap (invMap r) (invMap r (r x)) := by rw [h.invMap_apply_self]
    _ = r x := Function.leftInverse_invFun hinj _
private theorem IsAffineIsometry.continuous (h : IsAffineIsometry r R L c) : Continuous r := by
  have : r = fun x => R.mulVec x + c := funext h.apply_eq
  rw [this]
  exact (Continuous.matrix_mulVec continuous_const continuous_id).add continuous_const
private theorem IsAffineIsometry.contDiff (h : IsAffineIsometry r R L c) : ContDiff ℝ 1 r := by
  have : r = fun x => R.mulVec x + c := funext h.apply_eq
  rw [this]
  exact ((Matrix.mulVecLin R).toContinuousLinearMap.contDiff).add contDiff_const
private theorem IsAffineIsometry.continuous_invMap (h : IsAffineIsometry r R L c) :
    Continuous (invMap r) := by
  have : invMap r = fun x => L.mulVec (x - c) := funext h.invMap_apply
  rw [this]
  exact Continuous.matrix_mulVec continuous_const (continuous_id.sub continuous_const)
private def IsAffineIsometry.toHomeomorph (h : IsAffineIsometry r R L c) : AmbientSpace ≃ₜ AmbientSpace where
  toFun := r
  invFun := invMap r
  left_inv := h.invMap_apply_self
  right_inv := h.apply_invMap
  continuous_toFun := h.continuous
  continuous_invFun := h.continuous_invMap
private theorem IsAffineIsometry.disjointlySupported_map (h : IsAffineIsometry r R L c)
    {Y : List RealValued} (hY : IsDisjointlySupported Y) :
    IsDisjointlySupported (Y.map fun f => f ∘ r) := by
  have hs : ∀ f : RealValued, tsupport (f ∘ r) = r ⁻¹' tsupport f := fun f =>
    tsupport_comp_eq_preimage f h.toHomeomorph
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2⟩ := hY.1 f hf
    exact ⟨ContDiff.comp h1 h.contDiff, h2.comp_homeomorph h.toHomeomorph⟩
  · refine List.pairwise_map.2 (hY.2.imp fun {f g} hfg => ?_)
    rw [hs, hs]
    exact hfg.preimage _
private theorem IsAffineIsometry.pushList_invMap (h : IsAffineIsometry r R L c) (Y : List RealValued) :
    pushList (invMap r) Y = Y.map fun f => f ∘ r := by
  simp only [pushList, h.invMap_invMap]
private theorem IsAffineIsometry.push_invMap_val (h : IsAffineIsometry r R L c) (X : SepTuple) :
    (push (invMap r) X).1 = X.1.map fun f => f ∘ r := by
  have hs : IsDisjointlySupported (pushList (invMap r) X.1) := by
    rw [h.pushList_invMap]
    exact h.disjointlySupported_map X.2
  unfold push
  rw [dif_pos hs]
  exact h.pushList_invMap _
private theorem IsAffineIsometry.symm (h : IsAffineIsometry r R L c) :
    IsAffineIsometry (invMap r) L R (-(L.mulVec c)) := by
  refine ⟨fun x => ?_, h.inv_mul, h.mul_inv, fun x y => ?_⟩
  · rw [h.invMap_apply, Matrix.mulVec_sub]
    abel
  · have := h.isEuclidIsometry (invMap r x) (invMap r y)
    rwa [h.apply_invMap, h.apply_invMap, eq_comm] at this
private theorem IsAffineIsometry.push_val (h : IsAffineIsometry r R L c) (X : SepTuple) :
    (push r X).1 = X.1.map fun f => f ∘ invMap r := by
  have := h.symm.push_invMap_val X
  rwa [h.invMap_invMap] at this
private theorem IsAffineIsometry.push_push_invMap (h : IsAffineIsometry r R L c) (X : SepTuple) :
    push r (push (invMap r) X) = X := by
  refine Subtype.ext ?_
  rw [h.push_val, h.push_invMap_val, List.map_map]
  have : ((fun f : RealValued => f ∘ invMap r) ∘ fun f => f ∘ r) = id := by
    funext f x
    simp [h.apply_invMap]
  rw [this, List.map_id]
private theorem IsAffineIsometry.push_invMap_push (h : IsAffineIsometry r R L c) (X : SepTuple) :
    push (invMap r) (push r X) = X := by
  refine Subtype.ext ?_
  rw [h.push_invMap_val, h.push_val, List.map_map]
  have : ((fun f : RealValued => f ∘ r) ∘ fun f => f ∘ invMap r) = id := by
    funext f x
    simp [h.invMap_apply_self]
  rw [this, List.map_id]
private theorem IsAffineIsometry.euclidNormVec_mulVec_inv (h : IsAffineIsometry r R L c) (v : AmbientSpace) :
    euclidNormVec (L.mulVec v) = euclidNormVec v := by
  have := h.symm.isEuclidIsometry v 0
  rw [h.symm.apply_eq, h.symm.apply_eq] at this
  simpa using this
private theorem IsAffineIsometry.push_translate_comm (h : IsAffineIsometry r R L c) (v : AmbientSpace)
    (Y : SepTuple) :
    push (translate (L.mulVec v)) (push (invMap r) Y) = push (invMap r) (push (translate v) Y) := by
  refine Subtype.ext ?_
  rw [push_translate_val, pushList_translate, h.push_invMap_val, h.push_invMap_val,
    push_translate_val, pushList_translate, List.map_map, List.map_map]
  refine List.map_congr_left fun f _ => ?_
  funext x
  simp only [Function.comp_apply]
  congr 1
  rw [h.apply_eq, h.apply_eq, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h.mul_inv]
  simp
  abel
private theorem IsAffineIsometry.shiftedComponents_map (h : IsAffineIsometry r R L c) (X : SepTuple)
    (P : List (SepTuple × AmbientSpace)) :
    shiftedComponents (push (invMap r) X) (P.map fun p => (push (invMap r) p.1, L.mulVec p.2)) =
      (shiftedComponents X P).map fun f => f ∘ r := by
  simp only [shiftedComponents, List.map_append, h.push_invMap_val, List.flatMap_map, List.map_flatMap]
  congr 1
  refine List.flatMap_congr fun p _ => ?_
  rw [h.push_translate_comm, h.push_invMap_val]
private theorem drop_zip_map (s : SepTuple → SepTuple) (g : AmbientSpace → AmbientSpace) (Y : List SepTuple)
    (vs : List AmbientSpace) (k : ℕ) :
    ((Y.map s).drop k).zip (vs.map g) = ((Y.drop k).zip vs).map fun p => (s p.1, g p.2) := by
  rw [← List.map_drop, List.zip_map]
  rfl
variable (h : IsAffineIsometry r R L c) (X : SepTuple) (Y : List SepTuple)
include h
private theorem IsAffineIsometry.mem_iterLimitDomain {k : ℕ} {vs : List AmbientSpace}
    (hvs : vs ∈ iterLimitDomain X Y Set.univ k) :
    vs.map L.mulVec ∈
      iterLimitDomain (push (invMap r) X) (Y.map (push (invMap r))) Set.univ k := by
  refine ⟨by simpa using hvs.1, by simp, ?_⟩
  rw [drop_zip_map, h.shiftedComponents_map]
  exact h.disjointlySupported_map hvs.2.2
private theorem IsAffineIsometry.shiftedJuxt_map {vs : List AmbientSpace}
    (hvs : vs ∈ iterLimitDomain X Y Set.univ 0) :
    shiftedJuxt (push (invMap r) X) ((Y.map (push (invMap r))).zip (vs.map L.mulVec)) =
      push (invMap r) (shiftedJuxt X (Y.zip vs)) := by
  have h₁ := (h.mem_iterLimitDomain X Y hvs).2.2
  have h₀ := hvs.2.2
  simp only [List.drop_zero] at h₁ h₀
  refine Subtype.ext ?_
  rw [shiftedJuxt_val h₁, h.push_invMap_val, shiftedJuxt_val h₀]
  have := drop_zip_map (push (invMap r)) L.mulVec Y vs 0
  simp only [List.drop_zero] at this
  rw [this, h.shiftedComponents_map]
private theorem IsAffineIsometry.iterLimitValue_map {σ : TupleFunctional}
    (hinv : ∀ Z, σ (push (invMap r) Z) = σ Z)
    (hE : IterLimitsExist σ X Y Set.univ)
    (hE' : IterLimitsExist σ (push (invMap r) X) (Y.map (push (invMap r))) Set.univ)
    (k : ℕ) : ∀ vs ∈ iterLimitDomain X Y Set.univ k,
      iterLimitValue σ (push (invMap r) X) (Y.map (push (invMap r))) Set.univ k (vs.map L.mulVec) =
        iterLimitValue σ X Y Set.univ k vs := by
  induction k with
  | zero =>
    intro vs hvs
    simp only [iterLimitValue]
    rw [h.shiftedJuxt_map X Y hvs, hinv]
  | succ k ih =>
    intro vs hvs
    have hk : k < Y.length := by
      have := hvs.1
      omega
    have t₁ := tendsto_iterLimitValue hE hk hvs
    have hvs' := h.mem_iterLimitDomain X Y hvs
    have t₂ := tendsto_iterLimitValue hE' (by simpa using hk) hvs'
    have hL : Tendsto L.mulVec (atInfinityWithin Set.univ) (atInfinityWithin Set.univ) := by
      simp only [atInfinityWithin_univ, atInfinity]
      refine tendsto_comap_iff.2 ?_
      have : euclidNormVec ∘ L.mulVec = euclidNormVec := funext h.euclidNormVec_mulVec_inv
      rw [this]
      exact tendsto_comap
    have t₃ := t₂.comp hL
    have hev : ∀ᶠ v in atInfinityWithin Set.univ, v :: vs ∈ iterLimitDomain X Y Set.univ k :=
      eventually_cons_mem_iterLimitDomain X Y Set.univ hk hvs
    have t₄ : Tendsto (fun v => iterLimitValue σ X Y Set.univ k (v :: vs)) (atInfinityWithin Set.univ)
        (𝓝 (iterLimitValue σ (push (invMap r) X) (Y.map (push (invMap r))) Set.univ (k + 1)
          (vs.map L.mulVec))) := by
      refine t₃.congr' ?_
      filter_upwards [hev] with v hv
      exact ih (v :: vs) hv
    have : (atInfinityWithin (Set.univ : Set AmbientSpace)).NeBot := by
      rw [atInfinityWithin_univ]
      infer_instance
    exact tendsto_nhds_unique t₄ t₁
end RigidMotions
private theorem exists_affineIsometry (hY : Tower.OrthogonalMotions.Classification)
    {r : AmbientSpace → AmbientSpace} (hr : IsEuclidIsometry r) : ∃ R L c, IsAffineIsometry r R L c := by
  obtain ⟨R, hR, c, hc⟩ := hY.2.1 r hr
  have h₁ : R * R.transpose = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).1 hR
  exact ⟨R, R.transpose, c, ⟨hc, h₁, mul_eq_one_comm.1 h₁, hr⟩⟩
private theorem IsAffineIsometry.permInvariant_push_invMap {r : AmbientSpace → AmbientSpace}
    {R L : Matrix (Fin 4) (Fin 4) ℝ} {c : AmbientSpace}
    (h : IsAffineIsometry r R L c) {τ : TupleFunctional} (hτ : τ.IsPermInvariant) (X : SepTuple)
    (ς : Equiv.Perm (Fin X.1.length)) :
    τ (push (invMap r) (X.reorder ς)) = τ (push (invMap r) X) := by
  have key : ∀ Z : SepTuple, Z.1 = X.1.map (fun f => f ∘ r) →
      ∃ ς' : Equiv.Perm (Fin Z.1.length), Z.reorder ς' = push (invMap r) (X.reorder ς) := by
    rintro ⟨l, hl⟩ e
    simp only at e
    subst e
    have hlen : (X.1.map fun f : RealValued => f ∘ r).length = X.1.length := List.length_map _
    refine ⟨(finCongr hlen).trans (ς.trans (finCongr hlen).symm), Subtype.ext ?_⟩
    rw [h.push_invMap_val]
    refine List.ext_getElem (by simp [SepTuple.reorder]) fun i h₁ h₂ => ?_
    simp [SepTuple.reorder, List.getElem_ofFn]
  obtain ⟨ς', e⟩ := key (push (invMap r) X) (h.push_invMap_val X)
  rw [← e, hτ]
private theorem canonical_transport (hM : Measures.MomentDetermination.mixedMoments_determine)
    (hY : Tower.OrthogonalMotions.Classification)
    {σ : TupleFunctional} {A : DecompositionData} (hA : A.IsCanonical σ)
    {r : AmbientSpace → AmbientSpace} (hr : IsEuclidIsometry r) (hinv : σ.IsInvariant r) :
    (transportedDecomposition A r).IsCanonical σ ∧
      IsUniquelyIsomorphic (transportedDecomposition A r) A := by
  obtain ⟨R, L, c, h⟩ := exists_affineIsometry hY hr
  have hinv' : ∀ Z, σ (push (invMap r) Z) = σ Z := fun Z => by
    have := hinv (push (invMap r) Z)
    rw [h.push_push_invMap] at this
    exact this.symm
  have hm : (transportedDecomposition A r).IsCanonical σ := by
    refine ⟨hA.compact, hA.metrizable, hA.isProb, hA.measureSupport_eq, ?_, ?_, ?_, ?_,
      hA.iterLimits_exist, ?_⟩
    · intro ξ X ς
      exact h.permInvariant_push_invMap (hA.comp_permInvariant ξ) X ς
    · intro ξ A' B' f f' α α' X X' Z hX hX' hZ
      refine hA.comp_entrywiseLinear ξ (A'.map fun f => f ∘ r) (B'.map fun f => f ∘ r) (f ∘ r) (f' ∘ r)
        α α' (push (invMap r) X) (push (invMap r) X') (push (invMap r) Z) ?_ ?_ ?_
      · rw [h.push_invMap_val, hX]; simp
      · rw [h.push_invMap_val, hX']; simp
      · rw [h.push_invMap_val, hZ]
        simp only [List.map_append, List.map_cons]
        rfl
    · intro X
      exact hA.continuous_comp (push (invMap r) X)
    · intro ξ ξ' e
      refine hA.comp_injective (tupleFunctional_ext fun X => ?_)
      have := congrArg (fun τ : TupleFunctional => τ (push r X)) e
      simpa [transportedDecomposition, compInv, h.push_invMap_push] using this
    · intro X Y
      have e₁ := hA.integral_comp_prod (push (invMap r) X) (Y.map (push (invMap r)))
      have e₂ := h.iterLimitValue_map X Y hinv' (hA.iterLimits_exist X Y)
        (hA.iterLimits_exist _ _) Y.length []
        (by rw [iterLimitDomain_length]; rfl)
      have e₃ : iteratedLimitAtInfinity σ (push (invMap r) X) (Y.map (push (invMap r))) Set.univ =
          iteratedLimitAtInfinity σ X Y Set.univ := by
        simp only [iteratedLimitAtInfinity, List.length_map]
        simpa using e₂
      rw [← e₃, ← e₁]
      simp [transportedDecomposition, compInv, List.map_map, Function.comp_def]
      rfl
  exact ⟨hm, uniquelyIsomorphic_of_canonical hM hm hA⟩
private theorem exists_linearIsometryEquiv_of_norm_eq {V E G : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (S : V →ₗ[ℂ] E) (T : V →ₗ[ℂ] G) (hS : DenseRange S) (hT : DenseRange T)
    (hn : ∀ a, ‖T a‖ = ‖S a‖) : ∃ U : E ≃ₗᵢ[ℂ] G, ∀ a, U (S a) = T a := by
  have hker : LinearMap.ker S ≤ LinearMap.ker T := fun a ha => by
    rw [LinearMap.mem_ker] at ha ⊢
    have := hn a
    rw [ha, norm_zero] at this
    exact norm_eq_zero.1 this
  let e₁ := (LinearMap.ker S).liftQ S le_rfl
  let e₂ := (LinearMap.ker S).liftQ T hker
  have d₁ : DenseRange e₁ := hS.mono (by
    rintro _ ⟨a, rfl⟩
    exact ⟨Submodule.Quotient.mk a, by simp [e₁]⟩)
  have d₂ : DenseRange e₂ := hT.mono (by
    rintro _ ⟨a, rfl⟩
    exact ⟨Submodule.Quotient.mk a, by simp [e₂]⟩)
  have hnorm : ∀ x, ‖e₂ (LinearEquiv.refl ℂ _ x)‖ = ‖e₁ x‖ := fun x => by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simpa [e₁, e₂] using hn a
  refine ⟨(LinearEquiv.refl ℂ _).extendOfIsometry e₁ e₂ d₁ d₂ hnorm, fun a => ?_⟩
  have := LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ _) e₁ e₂ d₁ d₂ hnorm
    (Submodule.Quotient.mk a)
  simpa [e₁, e₂] using this
private theorem closure_eq_top_of_mul_mem_closure {X : Type} [TopologicalSpace X] [CompactSpace X]
    (S : Submodule ℂ C(X, ℂ)) (h1 : (1 : C(X, ℂ)) ∈ S) (hstar : ∀ a ∈ S, star a ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S.topologicalClosure)
    (hsep : ∀ x y : X, x ≠ y → ∃ a ∈ S, a x ≠ a y) : S.topologicalClosure = ⊤ := by
  set M := S.topologicalClosure with hM
  have hcl : IsClosed (M : Set C(X, ℂ)) := S.isClosed_topologicalClosure
  have hsub : S ≤ M := S.le_topologicalClosure
  have hmemcl : ∀ b ∈ M, b ∈ closure (S : Set C(X, ℂ)) := fun b hb => by
    rwa [hM, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hb
  have hmul₁ : ∀ a ∈ S, ∀ b ∈ M, a * b ∈ M := fun a ha b hb => by
    have := map_mem_closure (f := fun x => a * x) (t := (M : Set C(X, ℂ)))
      (continuous_const.mul continuous_id) (hmemcl b hb) (fun x hx => hmul a ha x hx)
    rwa [hcl.closure_eq] at this
  have hmul₂ : ∀ a ∈ M, ∀ b ∈ M, a * b ∈ M := fun a ha b hb => by
    have := map_mem_closure (f := fun x => x * b) (t := (M : Set C(X, ℂ)))
      (continuous_id.mul continuous_const) (hmemcl a ha) (fun x hx => hmul₁ x hx b hb)
    rwa [hcl.closure_eq] at this
  have hstar₂ : ∀ a ∈ M, star a ∈ M := fun a ha => by
    have := map_mem_closure (f := fun x : C(X, ℂ) => star x) (t := (M : Set C(X, ℂ)))
      continuous_star (hmemcl a ha) (fun x hx => hsub (hstar x hx))
    rwa [hcl.closure_eq] at this
  let B : StarSubalgebra ℂ C(X, ℂ) :=
    { carrier := M
      mul_mem' := fun {a b} ha hb => hmul₂ a ha b hb
      add_mem' := fun {a b} ha hb => M.add_mem ha hb
      algebraMap_mem' := fun z => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact M.smul_mem z (hsub h1)
      star_mem' := fun {a} ha => hstar₂ a ha }
  have hB : B.SeparatesPoints := by
    intro x y hxy
    obtain ⟨a, ha, hne⟩ := hsep x y hxy
    exact ⟨a, ⟨a, hsub ha, rfl⟩, hne⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints B hB
  rw [eq_top_iff]
  intro f _
  have hf : f ∈ (B.topologicalClosure : Set C(X, ℂ)) := by rw [htop]; trivial
  rw [StarSubalgebra.topologicalClosure_coe] at hf
  have hBM : (B : Set C(X, ℂ)) = M := rfl
  rwa [hBM, hcl.closure_eq] at hf
private theorem encard_eq_rank_Lp {X : Type} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (hpos : ∀ U : Set X, IsOpen U → U.Nonempty → 0 < μ U) :
    ENat.card X = Cardinal.toENat (Module.rank ℂ (Lp ℂ 2 μ)) := by
  classical
  have : μ.IsOpenPosMeasure := ⟨fun U hU hne h0 => (hpos U hU hne).ne' h0⟩
  have low : ∀ s : Finset X, (s.card : Cardinal) ≤ Module.rank ℂ (Lp ℂ 2 μ) := by
    intro s
    have hf : ∀ x : s, ∃ f : C(X, ℂ), f x = 1 ∧ ∀ y ∈ s, y ≠ x → f y = 0 := by
      intro x
      have hc : IsClosed ((s.erase x : Finset X) : Set X) := (s.erase x).finite_toSet.isClosed
      obtain ⟨f, h0, h1, -⟩ := exists_continuous_zero_one_of_isClosed hc (isClosed_singleton (x := (x : X)))
        (by simp)
      refine ⟨⟨fun y => (f y : ℂ), Complex.continuous_ofReal.comp f.continuous⟩, ?_, fun y hy hne => ?_⟩
      · have := h1 (Set.mem_singleton (x : X))
        simp [this]
      · have := h0 (show y ∈ ((s.erase x : Finset X) : Set X) by simp [hy, hne])
        simp [this]
    choose f hf₁ hf₂ using hf
    have hli : LinearIndependent ℂ fun x : s => ContinuousMap.toLp (E := ℂ) 2 μ ℂ (f x) := by
      refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
      have h₀ : ContinuousMap.toLp (E := ℂ) 2 μ ℂ (∑ j, g j • f j) = ContinuousMap.toLp (E := ℂ) 2 μ ℂ 0 := by
        rw [map_sum, map_zero, ← hg]
        simp
      have h₁ := ContinuousMap.toLp_injective μ h₀
      have h₂ := congrArg (fun φ : C(X, ℂ) => φ i) h₁
      simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, ContinuousMap.zero_apply] at h₂
      rw [Finset.sum_eq_single i] at h₂
      · simpa [hf₁] using h₂
      · intro j _ hj
        simp [hf₂ j i i.2 (fun e => hj (Subtype.ext e.symm))]
      · simp
    simpa using hli.cardinal_le_rank
  rcases finite_or_infinite X with hX | hX
  · letI := Fintype.ofFinite X
    have hsing : ∀ x : X, μ {x} ≠ 0 := fun x =>
      (hpos {x} (isOpen_discrete _) (Set.singleton_nonempty x)).ne'
    have hae : ∀ f g : X → ℂ, f =ᵐ[μ] g → f = g := fun f g h => by
      funext x
      by_contra hne
      have hx : ({x} : Set X) ⊆ {y | ¬ f y = g y} := by
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        exact hne
      exact hsing x (measure_mono_null hx (ae_iff.1 h))
    let Φ : Lp ℂ 2 μ →ₗ[ℂ] (X → ℂ) :=
      { toFun := fun f => ⇑f
        map_add' := fun f g => hae _ _ (Lp.coeFn_add f g)
        map_smul' := fun z f => hae _ _ (Lp.coeFn_smul z f) }
    have hinj : Function.Injective Φ := fun f g h => Lp.ext (by
      have : (⇑f : X → ℂ) = ⇑g := h
      rw [this])
    have hle := LinearMap.rank_le_of_injective Φ hinj
    rw [rank_fun'] at hle
    have hge := low Finset.univ
    rw [Finset.card_univ] at hge
    rw [le_antisymm hle hge, ENat.card_eq_coe_fintype_card]
    simp
  · rw [ENat.card_eq_top_of_infinite, eq_comm, Cardinal.toENat_eq_top]
    refine Cardinal.aleph0_le.2 fun n => ?_
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq X n
    rw [← hs]
    exact low s
section ComponentValues
variable {σ : TupleFunctional} {A : DecompositionData}
private def componentMap (hA : A.IsCanonical σ) (X : SepTuple) : C(A.space, ℂ) :=
  ⟨fun ξ => ((A.comp ξ X : ℝ) : ℂ), Complex.continuous_ofReal.comp (hA.continuous_comp X)⟩
private def spanComponentMap (hA : A.IsCanonical σ) : FormalSpan →ₗ[ℂ] C(A.space, ℂ) :=
  linearExtend (componentMap hA)
private theorem spanComponentMap_basisVec (hA : A.IsCanonical σ) (X : SepTuple) :
    spanComponentMap hA (basisVec X) = componentMap hA X :=
  linearExtend_basisVec _ X
private theorem spanComponentMap_apply (hA : A.IsCanonical σ) (F : FormalSpan)
    (ξ : A.space) : spanComponentMap hA F ξ = componentValues A F ξ := by
  induction F using Finsupp.induction_linear with
  | zero => simp [componentValues]
  | add f g hf hg =>
    simp only [map_add, ContinuousMap.add_apply, hf, hg, componentValues]
  | single X a =>
    have e : Finsupp.single X a = a • basisVec X := by simp [basisVec]
    rw [e]
    simp [spanComponentMap_basisVec, componentValues, TupleFunctional.spanExtension, linearExtend_basisVec,
      componentMap]
private theorem tendsto_smul_timeBasisVec :
    Tendsto (fun t : ℝ => t • timeBasisVec) atTop atInfinity := by
  refine tendsto_comap_iff.2 (tendsto_atTop_mono (f := id) (fun t => ?_) tendsto_id)
  refine Real.le_sqrt_of_sq_le ?_
  simp [timeBasisVec, PeriodicLattice.coordVec, TimeAxis.timeIdx, Fin.sum_univ_four, Pi.single_apply]
private theorem tendsto_juxt_shift (hA : A.IsCanonical σ) (X Y : SepTuple) :
    Tendsto (fun t : ℝ => σ (SepTuple.juxt X (push (translate (t • timeBasisVec)) Y))) atTop
      (𝓝 (∫ ξ, A.comp ξ X * A.comp ξ Y ∂A.law)) := by
  have h0 : ([] : List AmbientSpace) ∈ iterLimitDomain X [Y] Set.univ 1 := by
    have := iterLimitDomain_length X [Y] Set.univ
    simp only [List.length_cons, List.length_nil, zero_add] at this
    rw [this]
    rfl
  have t := tendsto_iterLimitValue (hA.iterLimits_exist X [Y]) (k := 0) (by simp) h0
  rw [atInfinityWithin_univ] at t
  have e : iterLimitValue σ X [Y] Set.univ 1 [] = ∫ ξ, A.comp ξ X * A.comp ξ Y ∂A.law := by
    have := hA.integral_comp_prod X [Y]
    simpa [iteratedLimitAtInfinity] using this.symm
  rw [e] at t
  refine (t.comp tendsto_smul_timeBasisVec).congr fun s => ?_
  simp [iterLimitValue, shiftedJuxt]
variable [CompactSpace A.space] [IsFiniteMeasure A.law]
private def toL2 (hA : A.IsCanonical σ) : FormalSpan →ₗ[ℂ] Lp ℂ 2 A.law :=
  (ContinuousMap.toLp (E := ℂ) 2 A.law ℂ).toLinearMap ∘ₗ spanComponentMap hA
private theorem inner_toL2 (hA : A.IsCanonical σ) (F F' : FormalSpan) :
    ⟪toL2 hA F, toL2 hA F'⟫_ℂ =
      ∫ ξ, conj (componentValues A F ξ) * componentValues A F' ξ ∂A.law := by
  simp only [toL2, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [ContinuousMap.inner_toLp]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [spanComponentMap_apply, mul_comm]
private theorem inner_toL2_basisVec (hA : A.IsCanonical σ) (X Y : SepTuple) :
    ⟪toL2 hA (basisVec X), toL2 hA (basisVec Y)⟫_ℂ =
      ((∫ ξ, A.comp ξ X * A.comp ξ Y ∂A.law : ℝ) : ℂ) := by
  rw [inner_toL2, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp [componentValues, TupleFunctional.spanExtension, linearExtend_basisVec]
private theorem tendsto_formalMul_shift (hA : A.IsCanonical σ)
    (hθ : ∀ ξ, (A.comp ξ).IsInvariant TimeAxis.timeReflection) (G G' : FormalSpan) :
    Tendsto (fun t : ℝ => σ.spanExtension (formalMul
      (pushSpan TimeAxis.timeReflection (conjugation G))
      (pushSpan (translate (t • timeBasisVec)) G'))) atTop
      (𝓝 ⟪toL2 hA G, toL2 hA G'⟫_ℂ) := by
  have base : ∀ X Y : SepTuple, Tendsto (fun t : ℝ => σ.spanExtension (formalMul
      (pushSpan TimeAxis.timeReflection (conjugation (basisVec X)))
      (pushSpan (translate (t • timeBasisVec)) (basisVec Y)))) atTop
      (𝓝 ⟪toL2 hA (basisVec X), toL2 hA (basisVec Y)⟫_ℂ) := by
    intro X Y
    rw [inner_toL2_basisVec]
    have e : (∫ ξ, A.comp ξ X * A.comp ξ Y ∂A.law) =
        ∫ ξ, A.comp ξ (push TimeAxis.timeReflection X) * A.comp ξ Y ∂A.law := by
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      simp only [hθ ξ X]
    rw [e]
    refine ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_juxt_shift hA (push TimeAxis.timeReflection X) Y)).congr fun t => ?_
    simp [conjugation_basisVec, pushSpan, linearExtend_basisVec, formalMul_basisVec,
      TupleFunctional.spanExtension]
  have step : ∀ (X : SepTuple) (G' : FormalSpan), Tendsto (fun t : ℝ => σ.spanExtension (formalMul
      (pushSpan TimeAxis.timeReflection (conjugation (basisVec X)))
      (pushSpan (translate (t • timeBasisVec)) G'))) atTop
      (𝓝 ⟪toL2 hA (basisVec X), toL2 hA G'⟫_ℂ) := by
    intro X G'
    induction G' using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simpa only [map_add, inner_add_right] using hf.add hg
    | single Y b =>
      have e : Finsupp.single Y b = b • basisVec Y := by simp [basisVec]
      rw [e]
      simpa only [map_smul, inner_smul_right, smul_eq_mul] using (base X Y).const_mul b
  induction G using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simpa only [map_add, LinearMap.add_apply, inner_add_left] using hf.add hg
  | single X a =>
    have e : Finsupp.single X a = a • basisVec X := by simp [basisVec]
    rw [e]
    simpa only [map_smulₛₗ, map_smul, LinearMap.smul_apply, inner_smul_left, smul_eq_mul,
      RingHom.id_apply] using (step X G').const_mul (conj a)
end ComponentValues
private theorem push_translate_mem {Y : SepTuple} (hY : Y ∈ supportedIn TimeAxis.upperHalfSpace) {t : ℝ}
    (ht : 0 ≤ t) : push (translate (t • timeBasisVec)) Y ∈ supportedIn TimeAxis.upperHalfSpace := by
  intro g hg
  rw [push_translate_val, pushList_translate] at hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  rw [tsupport_comp_sub]
  intro x hx
  have h₁ : TimeAxis.timeComponent (x - t • timeBasisVec) > 0 := hY f hf hx
  have h₂ : TimeAxis.timeComponent (x - t • timeBasisVec) = TimeAxis.timeComponent x - t := by
    simp [TimeAxis.timeComponent, timeBasisVec, PeriodicLattice.coordVec]
  show TimeAxis.timeComponent x > 0
  linarith
private theorem juxt_mem {O : Set AmbientSpace} {X Y : SepTuple} (hX : X ∈ supportedIn O)
    (hY : Y ∈ supportedIn O) : SepTuple.juxt X Y ∈ supportedIn O := by
  by_cases h : SepTuple.Composable X Y
  · intro f hf
    rw [SepTuple.juxt_val h] at hf
    rcases List.mem_append.1 hf with hf | hf
    · exact hX f hf
    · exact hY f hf
  · have : SepTuple.juxt X Y = SepTuple.nil := by simp [SepTuple.juxt, h]
    rw [this]
    exact nil_mem_supportedIn O
private theorem exists_shift_into_upperHalf (X : SepTuple) :
    ∃ t : ℝ, push (translate (t • timeBasisVec)) X ∈ supportedIn TimeAxis.upperHalfSpace := by
  have hK : IsCompact (⋃ f ∈ X.1, tsupport f) :=
    (List.finite_toSet X.1).isCompact_biUnion fun f hf => (X.2.1 f hf).2
  have hc : Continuous TimeAxis.timeComponent := continuous_apply _
  obtain ⟨b, hb⟩ := (hK.image hc).bddBelow
  refine ⟨1 - b, ?_⟩
  intro g hg
  rw [push_translate_val, pushList_translate] at hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  rw [tsupport_comp_sub]
  intro x hx
  have h₁ : b ≤ TimeAxis.timeComponent (x - (1 - b) • timeBasisVec) :=
    hb ⟨_, Set.mem_biUnion hf hx, rfl⟩
  have h₂ : TimeAxis.timeComponent (x - (1 - b) • timeBasisVec) = TimeAxis.timeComponent x - (1 - b) := by
    simp [TimeAxis.timeComponent, timeBasisVec, PeriodicLattice.coordVec]
  show TimeAxis.timeComponent x > 0
  linarith
section PlateauKernel
variable {σ : TupleFunctional} {A : DecompositionData}
private theorem closure_span_componentMap [CompactSpace A.space] (hA : A.IsCanonical σ)
    (hC : ComponentsInvariantAndClustering A) :
    (Submodule.span ℂ (Set.range fun X : supportedIn TimeAxis.upperHalfSpace =>
      componentMap hA X.1)).topologicalClosure = ⊤ := by
  set S := Submodule.span ℂ (Set.range fun X : supportedIn TimeAxis.upperHalfSpace =>
    componentMap hA X.1) with hSdef
  have gen : ∀ X (hX : X ∈ supportedIn TimeAxis.upperHalfSpace), componentMap hA X ∈ S := fun X hX =>
    Submodule.subset_span ⟨⟨X, hX⟩, rfl⟩
  refine closure_eq_top_of_mul_mem_closure S ?_ ?_ ?_ ?_
  · have e : (1 : C(A.space, ℂ)) = componentMap hA SepTuple.nil := by
      ext ξ
      simp [componentMap, (A.comp ξ).map_nil]
    rw [e]
    exact gen _ (nil_mem_supportedIn _)
  · intro a ha
    induction ha using Submodule.span_induction with
    | mem a h =>
      obtain ⟨X, rfl⟩ := h
      have e : star (componentMap hA X.1) = componentMap hA X.1 := by
        ext ξ
        simp [componentMap]
      rw [e]
      exact gen _ X.2
    | zero => simp
    | add a b _ _ h₁ h₂ =>
      rw [star_add]
      exact S.add_mem h₁ h₂
    | smul z a _ h =>
      rw [star_smul]
      exact S.smul_mem _ h
  · have pair : ∀ X ∈ supportedIn TimeAxis.upperHalfSpace, ∀ Y ∈ supportedIn TimeAxis.upperHalfSpace,
        componentMap hA X * componentMap hA Y ∈ S.topologicalClosure := by
      intro X hX Y hY
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨T, hT⟩ := hC.cluster_uniform X hX Y hY (ε / 2) (half_pos hε)
      have ht₀ : (0 : ℝ) ≤ max T 0 := le_max_right _ _
      refine ⟨_, gen _ (juxt_mem hX (push_translate_mem hY ht₀)), ?_⟩
      refine lt_of_le_of_lt ((ContinuousMap.dist_le (half_pos hε).le).2 fun ξ => ?_) (half_lt_self hε)
      have := hT _ (le_max_left T 0) ξ
      simp only [ContinuousMap.mul_apply, componentMap, ContinuousMap.coe_mk, Complex.dist_eq,
        ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rwa [abs_sub_comm]
    have left : ∀ X ∈ supportedIn TimeAxis.upperHalfSpace, ∀ b ∈ S,
        componentMap hA X * b ∈ S.topologicalClosure := by
      intro X hX b hb
      induction hb using Submodule.span_induction with
      | mem b h =>
        obtain ⟨Y, rfl⟩ := h
        exact pair X hX _ Y.2
      | zero => simp
      | add a b _ _ h₁ h₂ =>
        rw [mul_add]
        exact Submodule.add_mem _ h₁ h₂
      | smul z a _ h =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ _ h
    intro a ha b hb
    induction ha using Submodule.span_induction with
    | mem a h =>
      obtain ⟨X, rfl⟩ := h
      exact left _ X.2 b hb
    | zero => simp
    | add a c _ _ h₁ h₂ =>
      rw [add_mul]
      exact Submodule.add_mem _ h₁ h₂
    | smul z a _ h =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ _ h
  · intro ξ ξ' hne
    have hex : ∃ X, A.comp ξ X ≠ A.comp ξ' X := by
      by_contra hcon
      push Not at hcon
      exact hne (hA.comp_injective (tupleFunctional_ext hcon))
    obtain ⟨X, hX⟩ := hex
    obtain ⟨t, ht⟩ := exists_shift_into_upperHalf X
    refine ⟨_, gen _ ht, ?_⟩
    simp only [componentMap, ContinuousMap.coe_mk]
    rw [hC.shift_invariant ξ, hC.shift_invariant ξ']
    exact_mod_cast hX
private def upperValues [CompactSpace A.space] [IsFiniteMeasure A.law]
    (hA : A.IsCanonical σ) : PositiveSpan →ₗ[ℂ] Lp ℂ 2 A.law :=
  toL2 hA ∘ₗ Submodule.subtype _
private theorem upperValues_ae [CompactSpace A.space] [IsFiniteMeasure A.law]
    (hA : A.IsCanonical σ) (F : PositiveSpan) :
    (upperValues hA F : A.space → ℂ) =ᵐ[A.law] componentValues A F.1 := by
  have h₁ := ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := A.law) (𝕜 := ℂ) (spanComponentMap hA F.1)
  exact h₁.trans (Eventually.of_forall fun ξ => spanComponentMap_apply hA F.1 ξ)
private theorem denseRange_upperValues [CompactSpace A.space]
    [TopologicalSpace.MetrizableSpace A.space] [IsProbabilityMeasure A.law]
    (hA : A.IsCanonical σ) (hC : ComponentsInvariantAndClustering A) :
    DenseRange (upperValues hA) := by
  have hd := ContinuousMap.toLp_denseRange ℂ A.law ℂ (p := 2) (by norm_num)
  have hr : ∀ a ∈ Submodule.span ℂ (Set.range fun X : supportedIn TimeAxis.upperHalfSpace =>
      componentMap hA X.1), ContinuousMap.toLp (E := ℂ) 2 A.law ℂ a ∈
        Set.range (upperValues hA) := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a h =>
      obtain ⟨X, rfl⟩ := h
      refine ⟨posTupleVec X, ?_⟩
      simp [upperValues, toL2, posTupleVec, spanComponentMap_basisVec]
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ h₁ h₂ =>
      obtain ⟨F, hF⟩ := h₁
      obtain ⟨G, hG⟩ := h₂
      exact ⟨F + G, by rw [map_add, map_add, hF, hG]⟩
    | smul z a _ h =>
      obtain ⟨F, hF⟩ := h
      exact ⟨z • F, by rw [map_smul, map_smul, hF]⟩
  have hcl : Set.range (ContinuousMap.toLp (E := ℂ) 2 A.law ℂ) ⊆
      closure (Set.range (upperValues hA)) := by
    rintro _ ⟨f, rfl⟩
    have hf : f ∈ closure (Submodule.span ℂ (Set.range fun X : supportedIn TimeAxis.upperHalfSpace =>
        componentMap hA X.1) : Set C(A.space, ℂ)) := by
      rw [← Submodule.topologicalClosure_coe, closure_span_componentMap hA hC]
      trivial
    exact map_mem_closure (ContinuousMap.toLp (E := ℂ) 2 A.law ℂ).continuous hf hr
  have huniv := hd.closure_range
  refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
  rw [← huniv]
  exact closure_minimal hcl isClosed_closure
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
private def projClass {c : PositiveSpan →ₗ[ℂ] ℋ} {K : Submodule ℂ ℋ} {Q : ℋ →L[ℂ] ℋ}
    (hS : IsPlateauSpace σ c K Q) : PositiveSpan →ₗ[ℂ] K :=
  (Q.toLinearMap ∘ₗ c).codRestrict K fun _ => hS.proj_mem _
private theorem denseRange_projClass {c : PositiveSpan →ₗ[ℂ] ℋ} {K : Submodule ℂ ℋ}
    {Q : ℋ →L[ℂ] ℋ} (hS : IsPlateauSpace σ c K Q) : DenseRange (projClass hS) := by
  let Q' : ℋ →L[ℂ] K := Q.codRestrict K hS.proj_mem
  have hQ' : Function.Surjective Q' := fun ψ => ⟨ψ, Subtype.ext (hS.proj_fix _ ψ.2)⟩
  exact hQ'.denseRange.comp hS.denseRange Q'.continuous
private theorem inner_proj_eq [CompactSpace A.space] [IsFiniteMeasure A.law]
    (hA : A.IsCanonical σ) (hC : ComponentsInvariantAndClustering A)
    {c : PositiveSpan →ₗ[ℂ] ℋ} {K : Submodule ℂ ℋ} {Q : ℋ →L[ℂ] ℋ}
    (hS : IsPlateauSpace σ c K Q) (F F' : PositiveSpan) :
    ⟪Q (c F), Q (c F')⟫_ℂ = ⟪upperValues hA F, upperValues hA F'⟫_ℂ := by
  have h₁ : ⟪Q (c F), Q (c F')⟫_ℂ = ⟪c F, Q (c F')⟫_ℂ := by
    rw [hS.proj_symm, hS.proj_fix _ (hS.proj_mem _)]
  rw [h₁]
  exact tendsto_nhds_unique (hS.tendsto_inner F F') (tendsto_formalMul_shift hA hC.reflect_invariant F.1 F'.1)
private theorem norm_upperValues_eq [CompactSpace A.space] [IsFiniteMeasure A.law]
    (hA : A.IsCanonical σ) (hC : ComponentsInvariantAndClustering A)
    {c : PositiveSpan →ₗ[ℂ] ℋ} {K : Submodule ℂ ℋ} {Q : ℋ →L[ℂ] ℋ}
    (hS : IsPlateauSpace σ c K Q) (F : PositiveSpan) :
    ‖upperValues hA F‖ = ‖projClass hS F‖ := by
  have h₁ := inner_proj_eq hA hC hS F F
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h₁
  have h₂ : ‖Q (c F)‖ ^ 2 = ‖upperValues hA F‖ ^ 2 := by exact_mod_cast h₁
  have h₃ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h₂
  rw [Submodule.coe_norm]
  exact h₃.symm
private theorem exists_unitary_plateau [CompactSpace A.space]
    [TopologicalSpace.MetrizableSpace A.space] [IsProbabilityMeasure A.law]
    (hA : A.IsCanonical σ) (hC : ComponentsInvariantAndClustering A)
    {c : PositiveSpan →ₗ[ℂ] ℋ} {K : Submodule ℂ ℋ} {Q : ℋ →L[ℂ] ℋ} [CompleteSpace K]
    (hS : IsPlateauSpace σ c K Q) :
    ∃ U : K ≃ₗᵢ[ℂ] Lp ℂ 2 A.law, ∀ F, U (projClass hS F) = upperValues hA F := by
  have h₁ := denseRange_projClass hS
  have h₂ := denseRange_upperValues hA hC
  refine exists_linearIsometryEquiv_of_norm_eq (V := PositiveSpan) (E := K) (G := Lp ℂ 2 A.law)
    (projClass hS) (upperValues hA) h₁ h₂ fun F => ?_
  convert norm_upperValues_eq hA hC hS F using 1
private theorem kernelIsL2_of_plateau (hA : A.IsCanonical σ) (hC : ComponentsInvariantAndClustering A)
    {c : PositiveSpan →ₗ[ℂ] ℋ} {K : Submodule ℂ ℋ} {Q : ℋ →L[ℂ] ℋ}
    (hS : IsPlateauSpace σ c K Q) : KernelIsL2 A c K Q := by
  have := hA.compact
  have := hA.metrizable
  have := hA.isProb
  have : CompleteSpace K := hS.isClosed.completeSpace_coe
  have hpos : ∀ U : Set A.space, IsOpen U → U.Nonempty → 0 < A.law U := fun U hU hne =>
    law_pos_of_isOpen hA.measureSupport_eq hU hne
  have hTd := denseRange_projClass hS
  obtain ⟨U, hU⟩ := exists_unitary_plateau hA hC hS
  have hvalue := upperValues_ae hA
  have hrank : ENat.card A.space = Cardinal.toENat (Module.rank ℂ K) := by
    rw [U.toLinearEquiv.rank_eq]
    exact encard_eq_rank_Lp A.law hpos
  have hext : IsValueExtension A c K Q U := fun F => ⟨hS.proj_mem _, by
    have : U ⟨_, hS.proj_mem (c F)⟩ = upperValues hA F := hU F
    rw [this]
    exact hvalue F⟩
  have hone : ∀ U' : K ≃ₗᵢ[ℂ] Lp ℂ 2 A.law, IsValueExtension A c K Q U' → U' = U := by
    intro U' hU'
    have hon : ∀ F, U' (projClass hS F) = U (projClass hS F) := fun F => by
      obtain ⟨hF, hv⟩ := hU' F
      rw [hU]
      exact Lp.ext (hv.trans (hvalue F).symm)
    have hfun : (U' : K → Lp ℂ 2 A.law) = U :=
      hTd.equalizer U'.continuous U.continuous (funext hon)
    exact LinearIsometryEquiv.coe_injective hfun
  have hvac : (U ⟨_, hS.vacuum_mem⟩ : A.space → ℂ) =ᵐ[A.law] fun _ => 1 := by
    have e : (⟨_, hS.vacuum_mem⟩ : K) =
        projClass hS (posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩) :=
      Subtype.ext (hS.proj_fix _ hS.vacuum_mem).symm
    rw [e, hU]
    refine (hvalue _).trans (Eventually.of_forall fun ξ => ?_)
    simp [componentValues, posTupleVec, TupleFunctional.spanExtension, linearExtend_basisVec,
      (A.comp ξ).map_nil]
  refine ⟨fun F F' => ?_, U, hext, hone, ⟨hS.vacuum_mem, hvac⟩, hrank⟩
  rw [inner_proj_eq hA hC hS]
  exact inner_toL2 hA F.1 F'.1
end PlateauKernel
theorem decompositionDeterminations_holds (hM : Measures.MomentDetermination.mixedMoments_determine)
    (hY : Tower.OrthogonalMotions.Classification) : DecompositionDeterminations := by
  intro σ
  refine ⟨fun A B hA hB => uniquelyIsomorphic_of_canonical hM hA hB, fun A B hA hB => ?_,
    fun A hA r hr hi => canonical_transport hM hY hA hr hi,
    fun A hA hC ℋ _ _ _ c K Q hS => kernelIsL2_of_plateau hA hC hS⟩
  obtain ⟨h, h₁, -, h₃, -⟩ := uniquelyIsomorphic_of_canonical hM hA hB
  ext τ
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨h ξ, h₁ ξ⟩
  · rintro ⟨ξ', rfl⟩
    obtain ⟨ξ, rfl⟩ := h₃.surjective ξ'
    exact ⟨ξ, (h₁ ξ).symm⟩
end YangMills.Construction.CanonicalDecompositionUniqueness
end
