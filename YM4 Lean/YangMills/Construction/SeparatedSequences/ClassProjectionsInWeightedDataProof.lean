import YangMills.Construction.Lattice.ExistenceOfTheOperatorsOfASeparatedSequence
import YangMills.Construction.Lattice.IdentitiesOfTheDirichletOperators
import YangMills.Construction.SeparatedSequences.ClassProjectionsInWeightedData
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInWeightedData
import YangMills.Construction.Torus.AveragingOperatorAndMatrices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass
open Set PeriodicLattice.DirichletOperators
open SingleSequence SingleSequence.SequenceData
section Transport
variable {X X' : Type} {R : X → X' → Prop}
def equivOfPairs (h : PairsUniquely R) : X ≃ X' where
  toFun x := (h.1 x).exists.choose
  invFun x' := (h.2 x').exists.choose
  left_inv x := (h.2 _).unique (h.2 _).exists.choose_spec (h.1 x).exists.choose_spec
  right_inv x' := (h.1 _).unique (h.1 _).exists.choose_spec (h.2 x').exists.choose_spec
theorem equivOfPairs_rel (h : PairsUniquely R) (x : X) : R x (equivOfPairs h x) :=
  (h.1 x).exists.choose_spec
theorem equivOfPairs_symm_rel (h : PairsUniquely R) (y : X') :
    R ((equivOfPairs h).symm y) y := by
  simpa using equivOfPairs_rel h ((equivOfPairs h).symm y)
def pushAlong (h : PairsUniquely R) : (X → ℝ) ≃ₗ[ℝ] (X' → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (equivOfPairs h).symm
theorem pushAlong_apply (h : PairsUniquely R) (f : X → ℝ) (y : X') :
    pushAlong h f y = f ((equivOfPairs h).symm y) := rfl
theorem agreeAlong_pushAlong (h : PairsUniquely R) (f : X → ℝ) :
    AgreeAlong R f (pushAlong h f) := by
  intro x y hxy
  rw [pushAlong_apply]
  have hx : (equivOfPairs h).symm y = x :=
    (h.2 y).unique (equivOfPairs_symm_rel h y) hxy
  rw [hx]
theorem eq_pushAlong (h : PairsUniquely R) {f : X → ℝ} {g : X' → ℝ} (hfg : AgreeAlong R f g) :
    g = pushAlong h f := by
  funext y
  rw [pushAlong_apply]
  exact (hfg _ _ (equivOfPairs_symm_rel h y)).symm
theorem eq_pushAlong_symm (h : PairsUniquely R) {f : X → ℝ} {g : X' → ℝ}
    (hfg : AgreeAlong R f g) : f = (pushAlong h).symm g := by
  rw [eq_pushAlong h hfg, LinearEquiv.symm_apply_apply]
def pushAlongSubspace (h : PairsUniquely R) {V : Submodule ℝ (X → ℝ)} {V' : Submodule ℝ (X' → ℝ)}
    (hV : SpacesCorrespond R (V : Set (X → ℝ)) (V' : Set (X' → ℝ))) : ↥V ≃ₗ[ℝ] ↥V' where
  toFun f := ⟨pushAlong h f.1, by
    obtain ⟨g, hg, hfg⟩ := hV.1 f.1 f.2
    rw [← eq_pushAlong h hfg]
    exact hg⟩
  map_add' f g := by
    ext x
    simp
  map_smul' c f := by
    ext x
    simp
  invFun f := ⟨(pushAlong h).symm f.1, by
    obtain ⟨g, hg, hgf⟩ := hV.2 f.1 f.2
    rw [← eq_pushAlong_symm h hgf]
    exact hg⟩
  left_inv f := by
    ext x
    simp
  right_inv f := by
    ext x
    simp
theorem extendByZero_coe {Y : Type} (V : Submodule ℝ (X → ℝ)) (T : ↥V → Y → ℝ) (f : ↥V) :
    extendByZero V T f.1 = T f := by
  simp [extendByZero, f.2]
end Transport
theorem conj_ringInverse {M M' : Type} [AddCommGroup M] [Module ℝ M] [AddCommGroup M']
    [Module ℝ M'] (e : M ≃ₗ[ℝ] M') {A : Module.End ℝ M} {A' : Module.End ℝ M'} (hA : IsUnit A)
    (hconj : ∀ m, e (A m) = A' (e m)) (m : M) :
    e (Ring.inverse A m) = Ring.inverse A' (e m) := by
  obtain ⟨u, rfl⟩ := hA
  rw [Ring.inverse_unit]
  have hl : ∀ z, (u : Module.End ℝ M) (((u⁻¹ : (Module.End ℝ M)ˣ) : Module.End ℝ M) z) = z :=
    fun z => LinearMap.congr_fun u.mul_inv z
  have hr : ∀ z, ((u⁻¹ : (Module.End ℝ M)ˣ) : Module.End ℝ M) ((u : Module.End ℝ M) z) = z :=
    fun z => LinearMap.congr_fun u.inv_mul z
  let J : Module.End ℝ M' :=
    e.toLinearMap ∘ₗ ((u⁻¹ : (Module.End ℝ M)ˣ) : Module.End ℝ M) ∘ₗ e.symm.toLinearMap
  have hAJ : A' * J = 1 := by
    refine LinearMap.ext fun v => ?_
    show A' (e (((u⁻¹ : (Module.End ℝ M)ˣ) : Module.End ℝ M) (e.symm v))) = v
    rw [← hconj, hl, LinearEquiv.apply_symm_apply]
  have hJA : J * A' = 1 := by
    refine LinearMap.ext fun v => ?_
    show e (((u⁻¹ : (Module.End ℝ M)ˣ) : Module.End ℝ M) (e.symm (A' v))) = v
    obtain ⟨z, rfl⟩ := e.surjective v
    rw [← hconj, LinearEquiv.symm_apply_apply, hr]
  have hJ : Ring.inverse A' = J := by
    have hU : A' = ((⟨A', J, hAJ, hJA⟩ : (Module.End ℝ M')ˣ) : Module.End ℝ M') := rfl
    rw [hU, Ring.inverse_unit]
    rfl
  rw [hJ]
  show _ = e (((u⁻¹ : (Module.End ℝ M)ˣ) : Module.End ℝ M) (e.symm (e m)))
  rw [LinearEquiv.symm_apply_apply]
section Projections
variable {X X' Y Y' : Type} {R : X → X' → Prop} {Rc : Y → Y' → Prop}
  {V : Submodule ℝ (X → ℝ)} {V' : Submodule ℝ (X' → ℝ)}
theorem projections_correspond (hR : PairsUniquely R) (hRc : PairsUniquely Rc)
    (hV : SpacesCorrespond R (V : Set (X → ℝ)) (V' : Set (X' → ℝ)))
    {p : (X → ℝ) → (X → ℝ) → ℝ} {p' : (X' → ℝ) → (X' → ℝ) → ℝ}
    (hp : PairingsCorrespond R (V : Set (X → ℝ)) (V' : Set (X' → ℝ)) p p')
    {c : (Y → ℝ) → (Y → ℝ) → ℝ} {c' : (Y' → ℝ) → (Y' → ℝ) → ℝ}
    (hc : PairingsCorrespond Rc univ univ c c')
    (Q : ↥V →ₗ[ℝ] (Y → ℝ)) (Q' : ↥V' →ₗ[ℝ] (Y' → ℝ))
    (S : (Y → ℝ) →ₗ[ℝ] ↥V) (S' : (Y' → ℝ) →ₗ[ℝ] ↥V')
    (G : Module.End ℝ ↥V) (G' : Module.End ℝ ↥V')
    (hQ : OperatorsCorrespond R Rc (V : Set (X → ℝ)) (V' : Set (X' → ℝ))
      (extendByZero V fun f => Q f) (extendByZero V' fun f => Q' f))
    (hG : OperatorsCorrespond R R (V : Set (X → ℝ)) (V' : Set (X' → ℝ))
      (extendByZero V fun f => (G f).1) (extendByZero V' fun f => (G' f).1))
    (hadj : ∀ (f : ↥V) (w : Y → ℝ), c w (Q f) = p (S w).1 f.1)
    (hadj' : ∀ (f : ↥V') (w : Y' → ℝ), c' w (Q' f) = p' (S' w).1 f.1)
    (hdeg : ∀ u v : ↥V', (∀ g : ↥V', p' u.1 g.1 = p' v.1 g.1) → u = v)
    (hT : IsUnit (Q ∘ₗ (G ^ 2) ∘ₗ S)) :
    OperatorsCorrespond Rc Rc univ univ (Q ∘ₗ (G ^ 2) ∘ₗ S) (Q' ∘ₗ (G' * G') ∘ₗ S') ∧
    OperatorsCorrespond Rc Rc univ univ
      ⇑(Ring.inverse (Q ∘ₗ (G ^ 2) ∘ₗ S) : Module.End ℝ (Y → ℝ))
      ⇑(Ring.inverse (Q' ∘ₗ (G' * G') ∘ₗ S') : Module.End ℝ (Y' → ℝ)) ∧
    OperatorsCorrespond R R (V : Set (X → ℝ)) (V' : Set (X' → ℝ))
      (extendByZero V fun f =>
        ((G ∘ₗ S ∘ₗ Ring.inverse (Q ∘ₗ (G ^ 2) ∘ₗ S) ∘ₗ Q ∘ₗ G) f).1)
      (extendByZero V' fun f =>
        ((G' ∘ₗ S' ∘ₗ Ring.inverse (Q' ∘ₗ (G' * G') ∘ₗ S') ∘ₗ Q' ∘ₗ G') f).1) ∧
    OperatorsCorrespond R R (V : Set (X → ℝ)) (V' : Set (X' → ℝ))
      (extendByZero V fun f =>
        (((1 : Module.End ℝ ↥V) -
          G ∘ₗ S ∘ₗ Ring.inverse (Q ∘ₗ (G ^ 2) ∘ₗ S) ∘ₗ Q ∘ₗ G) f).1)
      (extendByZero V' fun f =>
        (((1 : Module.End ℝ ↥V') -
          G' ∘ₗ S' ∘ₗ Ring.inverse (Q' ∘ₗ (G' * G') ∘ₗ S') ∘ₗ Q' ∘ₗ G') f).1) := by
  set eC := pushAlong hRc with heC
  set eF := pushAlongSubspace hR hV with heF
  have hagree : ∀ f : ↥V, AgreeAlong R f.1 (eF f).1 := fun f => agreeAlong_pushAlong hR f.1
  have hQc : ∀ f : ↥V, eC (Q f) = Q' (eF f) := by
    intro f
    have h := hQ f.1 f.2 (eF f).1 (eF f).2 (hagree f)
    rw [extendByZero_coe V (fun f => Q f) f, extendByZero_coe V' (fun f => Q' f) (eF f)] at h
    exact (eq_pushAlong hRc h).symm
  have hGc : ∀ f : ↥V, eF (G f) = G' (eF f) := by
    intro f
    have h := hG f.1 f.2 (eF f).1 (eF f).2 (hagree f)
    rw [extendByZero_coe V (fun f => (G f).1) f,
      extendByZero_coe V' (fun f => (G' f).1) (eF f)] at h
    exact Subtype.ext (eq_pushAlong hR h).symm
  have hSc : ∀ w, eF (S w) = S' (eC w) := by
    intro w
    refine hdeg _ _ fun g' => ?_
    obtain ⟨g, rfl⟩ := eF.surjective g'
    have h1 : p (S w).1 g.1 = p' (eF (S w)).1 (eF g).1 :=
      hp _ (S w).2 _ g.2 _ (eF (S w)).2 _ (eF g).2 (hagree _) (hagree _)
    have h2 : c w (Q g) = c' (eC w) (eC (Q g)) :=
      hc _ (mem_univ _) _ (mem_univ _) _ (mem_univ _) _ (mem_univ _)
        (agreeAlong_pushAlong hRc _) (agreeAlong_pushAlong hRc _)
    rw [← h1, ← hadj, h2, hQc, hadj']
  have hTc : ∀ w, eC ((Q ∘ₗ (G ^ 2) ∘ₗ S) w) = (Q' ∘ₗ (G' * G') ∘ₗ S') (eC w) := by
    intro w
    show eC (Q ((G ^ 2) (S w))) = Q' ((G' * G') (S' (eC w)))
    rw [pow_two, hQc]
    show Q' (eF (G (G (S w)))) = Q' (G' (G' (S' (eC w))))
    rw [hGc, hGc, hSc]
  have hIc := conj_ringInverse eC hT hTc
  have hPc : ∀ f, eF ((G ∘ₗ S ∘ₗ Ring.inverse (Q ∘ₗ (G ^ 2) ∘ₗ S) ∘ₗ Q ∘ₗ G) f) =
      (G' ∘ₗ S' ∘ₗ Ring.inverse (Q' ∘ₗ (G' * G') ∘ₗ S') ∘ₗ Q' ∘ₗ G') (eF f) := by
    intro f
    simp only [LinearMap.comp_apply]
    rw [hGc, hSc, hIc, hQc, hGc]
  have hFine : ∀ (A : Module.End ℝ ↥V) (A' : Module.End ℝ ↥V'), (∀ f, eF (A f) = A' (eF f)) →
      OperatorsCorrespond R R (V : Set (X → ℝ)) (V' : Set (X' → ℝ))
        (extendByZero V fun f => (A f).1) (extendByZero V' fun f => (A' f).1) := by
    intro A A' hA f hf f' hf' hs
    have hfe : f' = (eF ⟨f, hf⟩).1 := eq_pushAlong hR hs
    subst hfe
    rw [extendByZero_coe V (fun f => (A f).1) ⟨f, hf⟩,
      extendByZero_coe V' (fun f => (A' f).1) (eF ⟨f, hf⟩), ← hA]
    exact hagree _
  have hCoarse : ∀ (A : Module.End ℝ (Y → ℝ)) (A' : Module.End ℝ (Y' → ℝ)),
      (∀ w, eC (A w) = A' (eC w)) → OperatorsCorrespond Rc Rc univ univ A A' := by
    intro A A' hA w _ w' _ hs
    have hwe : w' = eC w := eq_pushAlong hRc hs
    subst hwe
    rw [← hA]
    exact agreeAlong_pushAlong hRc _
  refine ⟨hCoarse _ _ hTc, hCoarse _ _ hIc, hFine _ _ hPc, hFine _ _ fun f => ?_⟩
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [hPc]
end Projections
section Data
variable {D : Weighted.TorusData} (B : Weighted.SeparatedChain D)
theorem layerInner_comm (w w' : B.LayerFn) : B.layerInner w w' = B.layerInner w' w := by
  simp only [Weighted.SeparatedChain.layerInner, mul_comm (w _) (w' _)]
theorem bareInner_comm (f g : D.BareSite → ℝ) : B.bareInner f g = B.bareInner g f := by
  simp only [Weighted.SeparatedChain.bareInner, mul_comm (f _) (g _)]
theorem bareInner_nondegenerate (u v : ↥B.bareSpace)
    (h : ∀ g : ↥B.bareSpace, B.bareInner u.1 g.1 = B.bareInner v.1 g.1) : u = v := by
  have hfin := D.bareSite_finite
  have hsc : D.scale 0 ^ 4 ≠ 0 := by
    have : D.scale 0 ≠ 0 := by
      simp [Weighted.TorusData.scale, D.bareSpacing_pos.ne']
    exact pow_ne_zero _ this
  have h0 := h (u - v)
  simp only [Weighted.SeparatedChain.bareInner] at h0
  have h1 := mul_left_cancel₀ hsc h0
  have hF : (D.bareSites (B.stage 0)).Finite := toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hF, finsum_mem_eq_finite_toFinset_sum _ hF,
    ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
  have h2 : ∀ x ∈ hF.toFinset, ((u : D.BareSite → ℝ) x - (v : D.BareSite → ℝ) x) ^ 2 = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg fun x _ => sq_nonneg _).1 ?_
    rw [← h1]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Submodule.coe_sub, Pi.sub_apply]
    ring
  ext x
  by_cases hx : x ∈ D.bareSites (B.stage 0)
  · have hx2 := h2 x (hF.mem_toFinset.2 hx)
    exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 hx2)
  · rw [u.2 x hx, v.2 x hx]
end Data
theorem statement_holds (hScalar : ScalarDataOfWeightedCorresponds)
    (hAvg : Weighted.AvgAndMatrixFacts)
    (hExist : SeparatedSequences.OperatorExistenceStatement)
    (hIdent : SeparatedSequences.DirichletOperatorIdentities) : Statement := by
  intro s D B hDB
  have hS := hScalar s D B hDB
  let Sd : SeparatedSequences.SequenceDatum := ⟨s.params, s.Ω, s.Ω_mem.2.1, s.Ω_mem.1⟩
  have hdefined : s.params.OperatorsWellDefined s.Ω s.frame := (hExist.1 Sd s.frame).2.2.2.2
  have hrep : (s.params.GaugeProjectionFormulas s.Ω) :=
    (hIdent Sd s.frame).2.2.2.2.2.2.2.1
  have hne : (B.stage 0).Nonempty := by
    rw [hDB.stage_eq 0]
    exact s.Ω_mem.1.image _
  have hrel : ∀ (f : ↥B.bareSpace) (w : B.LayerFn),
      B.layerInner (B.avgOp f) w = B.bareInner f (B.avgOpAdjoint w) :=
    (hAvg ⟨D, B, hne⟩).1.1
  have hcorr := projections_correspond
    (R := s.scalarData.SiteRel (scalarDataOfWeighted B) (s.toTorus D.side))
    (Rc := s.scalarData.CoarseRel (scalarDataOfWeighted B) (s.toTorus D.side))
    (V := zeroFormsOn s.data.cutoff (s.Ω 0)) (V' := B.bareSpace)
    hS.sites hS.coarse hS.space hS.inner hS.coarseInner
    (s.params.averageZero s.Ω) B.avgOp
    (s.params.averageZeroAdjoint s.Ω) B.avgOpAdjoint
    (s.params.zeroGreen s.Ω) B.greenOp
    hS.avg hS.inv hdefined.zero_adjoint
    (fun (f : ↥B.bareSpace) (w : B.LayerFn) =>
      (layerInner_comm B w (B.avgOp f)).trans ((hrel f w).trans (bareInner_comm B _ _)))
    (bareInner_nondegenerate B)
    hdefined.averaged_zero_green_sq_invertible
  obtain ⟨h1, h2, h3, h4⟩ := hcorr
  have hmass := hrep.of_massive
  have hrange : s.params.gaugeRangeProjection s.Ω =
      1 - s.params.gaugeComplementProjection s.Ω :=
    (sub_sub_cancel (1 : Module.End ℝ ↥(zeroFormsOn s.data.cutoff (s.Ω 0)))
      (s.params.gaugeRangeProjection s.Ω)).symm
  refine ⟨h1, h2, ?_, ?_⟩
  · show OperatorsCorrespond _ _ _ _
      (extendByZero (zeroFormsOn s.data.cutoff (s.Ω 0)) fun f =>
        (s.params.gaugeRangeProjection s.Ω f).1) _
    rw [hrange, hmass]
    exact h4
  · show OperatorsCorrespond _ _ _ _
      (extendByZero (zeroFormsOn s.data.cutoff (s.Ω 0)) fun f =>
        (s.params.gaugeComplementProjection s.Ω f).1) _
    rw [hmass]
    exact h3
end YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass
