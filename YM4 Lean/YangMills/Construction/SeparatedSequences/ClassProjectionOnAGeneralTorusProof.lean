import YangMills.Construction.SeparatedSequences.ClassExpansionsOnAGeneralTorusProof
import YangMills.Construction.SeparatedSequences.ClassGeometryOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice.DirichletOperators
noncomputable section
namespace YangMills.Construction.SeparatedClasses.GaugeProjectionOfClass
open SingleSequence SingleSequence.SequenceData
section Forms
variable {V U : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup U] [Module ℝ U]
theorem exists_adjoint_of_definite (p : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : ∀ v, p v v = 0 → v = 0)
    (q : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] U) :
    ∃ T : U →ₗ[ℝ] V, ∀ v u, q (K v) u = p (T u) v := by
  have hinj : Function.Injective p :=
    (injective_iff_map_eq_zero p).2 fun v hv => hp v (by rw [hv]; rfl)
  obtain ⟨e, he⟩ : ∃ e : V ≃ₗ[ℝ] Module.Dual ℝ V, ∀ v, e v = p v :=
    ⟨LinearMap.linearEquivOfInjective p hinj Subspace.dual_finrank_eq.symm, fun v => rfl⟩
  refine ⟨e.symm.toLinearMap ∘ₗ (q.comp K).flip, fun v u => ?_⟩
  have h : p (e.symm ((q.comp K).flip u)) = (q.comp K).flip u := by
    rw [← he, e.apply_symm_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h]
  rfl
theorem exists_orthogonalProjection_of_definite (p : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsymm : ∀ v w, p v w = p w v)
    (hp : ∀ v, p v v = 0 → v = 0) (E : Submodule ℝ V) :
    ∃ P : V →ₗ[ℝ] ↥E, (∀ e : ↥E, P e = e) ∧ ∀ v, ∀ e ∈ E, p (v - P v) e = 0 := by
  obtain ⟨T, hT⟩ := exists_adjoint_of_definite (p.domRestrict₁₂ E E)
    (fun v hv => Subtype.ext (hp _ hv)) p E.subtype
  have horth : ∀ v, ∀ e ∈ E, p (v - T v) e = 0 := by
    intro v e he
    have h := hT ⟨e, he⟩ v
    simp only [Submodule.subtype_apply, LinearMap.domRestrict₁₂_apply] at h
    rw [map_sub, LinearMap.sub_apply, hsymm v e, h, sub_self]
  refine ⟨T, fun e => ?_, horth⟩
  have h := horth e (e.1 - (T e).1) (E.sub_mem e.2 (T e).2)
  exact Subtype.ext (sub_eq_zero.1 (hp _ h)).symm
end Forms
section ScaledDot
variable {ι : Type}
def scaledDot [Finite ι] (c : ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => c * ∑ᶠ i, f i * g i)
    (fun f f' g => by
      simp only [Pi.add_apply, add_mul, SeparatedSequences.BaseParameters.finsum_add_finite,
        mul_add])
    (fun a f g => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc,
        SeparatedSequences.BaseParameters.finsum_const_mul_finite]
      ring)
    (fun f g g' => by
      simp only [Pi.add_apply, mul_add, SeparatedSequences.BaseParameters.finsum_add_finite])
    (fun a f g => by
      simp only [Pi.smul_apply, smul_eq_mul]
      have : ∀ i, f i * (a * g i) = a * (f i * g i) := fun i => by ring
      simp only [this, SeparatedSequences.BaseParameters.finsum_const_mul_finite]
      ring)
variable [Finite ι]
theorem scaledDot_apply (c : ℝ) (f g : ι → ℝ) : scaledDot c f g = c * ∑ᶠ i, f i * g i := rfl
theorem scaledDot_comm (c : ℝ) (f g : ι → ℝ) : scaledDot c f g = scaledDot c g f := by
  simp only [scaledDot_apply, mul_comm (f _)]
theorem eq_zero_of_scaledDot_self {c : ℝ} (hc : c ≠ 0) (f : ι → ℝ) (h : scaledDot c f f = 0) :
    f = 0 := by
  have := Fintype.ofFinite ι
  rw [scaledDot_apply, finsum_eq_sum_of_fintype] at h
  have h' := (mul_eq_zero.1 h).resolve_left hc
  have h'' := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (f i)).1 h'
  funext i
  exact mul_self_eq_zero.1 (h'' i (Finset.mem_univ i))
theorem scaledDot_comp_equiv {ι' : Type} [Finite ι'] (c : ℝ) (e : ι ≃ ι') (f g : ι' → ℝ) :
    scaledDot c (f ∘ e) (g ∘ e) = scaledDot c f g := by
  simp only [scaledDot_apply, Function.comp]
  rw [finsum_comp_equiv e (f := fun i => f i * g i)]
end ScaledDot
theorem orthProj_transport {ι ι' κ κ' : Type} [Finite ι] [Finite ι'] [Finite κ] [Finite κ']
    {c : ℝ} (hc : c ≠ 0) (e : ι ≃ ι') (β : κ ≃ κ')
    (D : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (D' : (ι' → ℝ) →ₗ[ℝ] (κ' → ℝ))
    (hD : ∀ f b, D' (f ∘ e.symm) (β b) = D f b)
    (F : Submodule ℝ (ι → ℝ)) (F' : Submodule ℝ (ι' → ℝ))
    (hF : ∀ f, f ∈ F ↔ f ∘ e.symm ∈ F')
    (Δ : Module.End ℝ ↥F) (Δ' : Module.End ℝ ↥F')
    (hΔ : ∀ f g : ↥F, scaledDot c g.1 (Δ f).1 = scaledDot c (D f.1) (D g.1))
    (hΔ' : ∀ f g : ↥F', scaledDot c g.1 (Δ' f).1 = scaledDot c (D' f.1) (D' g.1))
    (N : Submodule ℝ ↥F) (N' : Submodule ℝ ↥F')
    (hN : ∀ (f : ↥F) (f' : ↥F'), f'.1 = f.1 ∘ e.symm → (f ∈ N ↔ f' ∈ N'))
    (P : ↥F → ↥F) (P' : ↥F' → ↥F')
    (hP : ∀ f, P f ∈ N.map Δ ∧ ∀ w ∈ N.map Δ, scaledDot c (f - P f).1 w.1 = 0)
    (hP' : ∀ f, P' f ∈ N'.map Δ' ∧ ∀ w ∈ N'.map Δ', scaledDot c (f - P' f).1 w.1 = 0)
    (f : ↥F) (f' : ↥F') (hf : f'.1 = f.1 ∘ e.symm) : (P' f').1 = (P f).1 ∘ e.symm := by
  let τ : ↥F → ↥F' := fun g => ⟨g.1 ∘ e.symm, (hF _).1 g.2⟩
  have hσ : ∀ g : ↥F', g.1 ∘ e ∈ F := fun g => (hF _).2 (by
    have : (g.1 ∘ e) ∘ e.symm = g.1 := by
      funext i
      simp
    rw [this]
    exact g.2)
  let σ : ↥F' → ↥F := fun g => ⟨g.1 ∘ e, hσ g⟩
  have hτσ : ∀ g, τ (σ g) = g := fun g => Subtype.ext (by
    funext i
    simp [τ, σ])
  have hστ : ∀ g, σ (τ g) = g := fun g => Subtype.ext (by
    funext i
    simp [τ, σ])
  have hτ_sub : ∀ g h : ↥F, τ (g - h) = τ g - τ h := fun g h => rfl
  have hw : ∀ g h : ι → ℝ, scaledDot c (g ∘ e.symm) (h ∘ e.symm) = scaledDot c g h :=
    fun g h => scaledDot_comp_equiv c e.symm g h
  have hgr : ∀ g h : ι → ℝ,
      scaledDot c (D' (g ∘ e.symm)) (D' (h ∘ e.symm)) = scaledDot c (D g) (D h) := by
    intro g h
    have e1 : ∀ u : ι → ℝ, D' (u ∘ e.symm) ∘ β = D u := fun u => funext (hD u)
    rw [← scaledDot_comp_equiv c β (D' (g ∘ e.symm)) (D' (h ∘ e.symm)), e1, e1]
  have hcomm : ∀ g : ↥F, Δ' (τ g) = τ (Δ g) := by
    intro g
    have hzero : ∀ h : ↥F, scaledDot c (τ h).1 (Δ' (τ g) - τ (Δ g)).1 = 0 := by
      intro h
      rw [Submodule.coe_sub, map_sub, hΔ', show (τ h).1 = h.1 ∘ e.symm from rfl,
        show (τ g).1 = g.1 ∘ e.symm from rfl, show (τ (Δ g)).1 = (Δ g).1 ∘ e.symm from rfl,
        hgr, hw, hΔ, sub_self]
    have h0 := hzero (σ (Δ' (τ g) - τ (Δ g)))
    rw [hτσ] at h0
    exact sub_eq_zero.1 (Subtype.ext (eq_zero_of_scaledDot_self hc _ h0))
  have hinj : Function.Injective τ := fun a b h => by rw [← hστ a, h, hστ]
  have hmem : ∀ w : ↥F, w ∈ N.map Δ ↔ τ w ∈ N'.map Δ' := by
    intro w
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨τ n, (hN n (τ n) rfl).1 hn, hcomm n⟩
    · rintro ⟨n', hn', h⟩
      refine ⟨σ n', (hN (σ n') n' (by rw [← congrArg Subtype.val (hτσ n')])).2 hn', ?_⟩
      apply hinj
      rw [← hcomm, hτσ]
      exact h
  have hfτ : f' = τ f := Subtype.ext hf
  have ha : τ (P f) ∈ N'.map Δ' := (hmem _).1 (hP f).1
  have hb := (hP' f').1
  have horth : ∀ w ∈ N'.map Δ', scaledDot c (f' - τ (P f)).1 w.1 = 0 := by
    intro w hw'
    have hwσ : σ w ∈ N.map Δ := (hmem _).2 (by rw [hτσ]; exact hw')
    have h' := hw (f - P f).1 (σ w).1
    rw [(hP f).2 _ hwσ, show (σ w).1 ∘ e.symm = w.1 from congrArg Subtype.val (hτσ w)] at h'
    rw [hfτ, ← hτ_sub]
    exact h'
  have hd : (P' f' - τ (P f)) ∈ N'.map Δ' := Submodule.sub_mem _ hb ha
  have h1 := horth _ hd
  have h2 := (hP' f').2 _ hd
  have h3 : scaledDot c (P' f' - τ (P f)).1 (P' f' - τ (P f)).1 = 0 := by
    have : (P' f' - τ (P f)).1 = (f' - τ (P f)).1 - (f' - P' f').1 := by
      simp only [Submodule.coe_sub]
      abel
    nth_rewrite 1 [this]
    rw [map_sub, LinearMap.sub_apply, h1, h2, sub_self]
  have h4 := eq_zero_of_scaledDot_self hc _ h3
  exact sub_eq_zero.1 h4
section Rescaling
variable (s : SequenceData)
theorem blockFactor_cast_ne_zero : (s.data.L : ℝ) ≠ 0 := by
  have h := s.data.isAdmissible.2
  exact_mod_cast (by omega : s.data.L ≠ 0)
theorem torusSide_levelUnits_eq : s.levelUnitData.torusSide =
    PeriodicLattice.torusSide s.data.L s.data.m * (s.data.L : ℝ) ^ (s.data.cutoff - s.data.t) := by
  show 2 * (s.data.L : ℝ) ^ ((s.data.m : ℕ) + s.data.cutoff - s.data.t) = _
  rw [Nat.add_sub_assoc s.data.t_le_cutoff, pow_add, PeriodicLattice.torusSide]
  ring
theorem torusSide_levelUnits_ne_zero : s.levelUnitData.torusSide ≠ 0 := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeOneFormsProof.TorusComponents.gaugeSide_ne_zero <;> assumption
theorem meshSize_mul_rescale (n : ℕ) :
    PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) *
      ((PeriodicLattice.torusSide s.data.L s.data.m)⁻¹ * s.levelUnitData.torusSide) =
        s.levelUnitData.levelSpacing n := by
  have hL := blockFactor_cast_ne_zero s
  rw [torusSide_levelUnits_eq, ← mul_assoc (PeriodicLattice.torusSide s.data.L s.data.m)⁻¹,
    inv_mul_cancel₀ s.torusSide_ne_zero, one_mul]
  show (s.data.L : ℝ) ^ (-(((s.data.cutoff : ℕ) : ℤ) - (n : ℤ))) *
      (s.data.L : ℝ) ^ (s.data.cutoff - s.data.t) =
    (s.data.L : ℝ) ^ n * (s.data.L : ℝ) ^ (-(s.data.t : ℤ))
  rw [← zpow_natCast (s.data.L : ℝ) (s.data.cutoff - s.data.t), ← zpow_natCast (s.data.L : ℝ) n,
    ← zpow_add₀ hL, ← zpow_add₀ hL]
  congr 1
  push_cast [Nat.cast_sub s.data.t_le_cutoff]
  ring
theorem levelSpacing_zero_eq :
    s.levelUnitData.levelSpacing 0 = PeriodicLattice.finestMeshInLevelUnits s.data.L s.data.t := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeOneFormsProof.TorusComponents.levelSpacing_zero <;> assumption
theorem levelSpacing_eq_coarseMesh (n : ℕ) :
    s.levelUnitData.levelSpacing n = s.data.coarseMesh n := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeOneFormsProof.TorusComponents.levelSpacing_eq_meshRatio <;> assumption
def rescaleEquiv : s.data.Point ≃+ s.levelUnitData.Space :=
  AddEquiv.piCongrRight fun _ =>
    AddCircle.equivAddCircle _ _ s.torusSide_ne_zero (torusSide_levelUnits_ne_zero s)
theorem rescaleEquiv_apply (x : s.data.Point) (μ : Fin 4) :
    rescaleEquiv s x μ = AddCircle.equivAddCircle (PeriodicLattice.torusSide s.data.L s.data.m)
      s.levelUnitData.torusSide s.torusSide_ne_zero (torusSide_levelUnits_ne_zero s) (x μ) := rfl
theorem toTorus_eq_rescaleEquiv (x : s.data.Point) :
    s.toTorus s.levelUnitData.torusSide x = rescaleEquiv s x := by
  unfold SequenceData.toTorus
  rw [dif_pos (torusSide_levelUnits_ne_zero s)]
  rfl
theorem rescaleEquiv_torusProj (k : Fin 4 → ℤ) (n : ℕ) :
    rescaleEquiv s (fun μ => (((k μ : ℝ) *
        PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) : ℝ) :
          AddCircle (PeriodicLattice.torusSide s.data.L s.data.m))) =
      torusProj s.levelUnitData.torusSide fun μ => s.levelUnitData.levelSpacing n * (k μ : ℝ) := by
  funext μ
  rw [rescaleEquiv_apply, AddCircle.equivAddCircle_apply_mk]
  show _ = ((s.levelUnitData.levelSpacing n * (k μ : ℝ) : ℝ) : AddCircle s.levelUnitData.torusSide)
  rw [← meshSize_mul_rescale]
  congr 1
  ring
theorem mem_sublattice_iff_rescale (x : s.data.Point) :
    x ∈ PeriodicLattice.sublattice s.data.L s.data.m (PeriodicLattice.levelDepth s.data.cutoff 0) ↔
      rescaleEquiv s x ∈ s.levelUnitData.levelSublattice 0 := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h : x = _ := funext hk
    rw [h]
    exact rescaleEquiv_torusProj s k 0
  · rintro ⟨k, hk⟩
    refine ⟨k, fun μ => ?_⟩
    have h : x = fun μ => (((k μ : ℝ) *
        PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff 0) : ℝ) :
          AddCircle (PeriodicLattice.torusSide s.data.L s.data.m)) :=
      (rescaleEquiv s).injective (by rw [hk]; exact (rescaleEquiv_torusProj s k 0).symm)
    rw [h]
theorem rescaleEquiv_unitStep (μ : Fin 4) :
    rescaleEquiv s (PeriodicLattice.unitStep s.data.L s.data.m
        (PeriodicLattice.levelDepth s.data.cutoff 0) μ : s.data.Point) =
      (GeneralTorus.unitStep s.levelUnitData.torusSide (s.levelUnitData.levelSpacing 0) μ :
        s.levelUnitData.Space) := by
  funext ν
  rw [rescaleEquiv_apply]
  show _ = torusProj s.levelUnitData.torusSide (Pi.single μ (s.levelUnitData.levelSpacing 0)) ν
  show AddCircle.equivAddCircle _ _ _ _ (PeriodicLattice.pointOnAxis s.data.L s.data.m μ _ ν) = _
  by_cases h : ν = μ
  · subst h
    simp only [PeriodicLattice.pointOnAxis, Pi.single_eq_same, torusProj]
    rw [AddCircle.equivAddCircle_apply_mk, meshSize_mul_rescale]
  · simp only [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h, torusProj, map_zero]
    rfl
def bareSiteEquiv : s.data.BareSite ≃ s.levelUnitData.BaseSite :=
  (rescaleEquiv s).toEquiv.subtypeEquiv (mem_sublattice_iff_rescale s)
theorem coe_bareSiteEquiv (x : s.data.BareSite) :
    (bareSiteEquiv s x : s.levelUnitData.Space) = rescaleEquiv s x := rfl
theorem sub_eq_unitStep_iff (x y : s.data.BareSite) (μ : Fin 4) :
    y - x = PeriodicLattice.unitStep s.data.L s.data.m
        (PeriodicLattice.levelDepth s.data.cutoff 0) μ ↔
      bareSiteEquiv s y - bareSiteEquiv s x =
        GeneralTorus.unitStep s.levelUnitData.torusSide (s.levelUnitData.levelSpacing 0) μ := by
  rw [Subtype.ext_iff, Subtype.ext_iff]
  show (y : s.data.Point) - x = _ ↔ rescaleEquiv s y - rescaleEquiv s x = _
  rw [← map_sub, ← rescaleEquiv_unitStep, (rescaleEquiv s).injective.eq_iff]
def bareBondEquiv : s.data.BareBond ≃ s.levelUnitData.BaseBond where
  toFun b := ⟨⟨bareSiteEquiv s b.1.source, bareSiteEquiv s b.1.target,
      b.2.elim fun μ h => ⟨μ, Or.inl ((sub_eq_unitStep_iff s _ _ μ).1 h)⟩⟩,
    b.2.elim fun μ h => ⟨μ, (sub_eq_unitStep_iff s _ _ μ).1 h⟩⟩
  invFun b := ⟨⟨(bareSiteEquiv s).symm b.1.src, (bareSiteEquiv s).symm b.1.tgt,
      b.2.elim fun μ h => ⟨μ, Or.inl ((sub_eq_unitStep_iff s _ _ μ).2 (by simpa using h))⟩⟩,
    b.2.elim fun μ h => ⟨μ, (sub_eq_unitStep_iff s _ _ μ).2 (by simpa using h)⟩⟩
  left_inv b := Subtype.ext (PeriodicLattice.Bond.ext (by simp) (by simp))
  right_inv b := Subtype.ext (GeneralTorus.LatticeBond.ext (by simp) (by simp))
theorem grad_comp_bareSiteEquiv_symm (f : s.data.SiteFn) (b : s.data.BareBond) :
    s.levelUnitData.grad (f ∘ (bareSiteEquiv s).symm) (bareBondEquiv s b) =
      grad s.data.t f b := by
  set c := bareBondEquiv s b with hc
  have hh : c.1.src + GeneralTorus.unitStep s.levelUnitData.torusSide
      (s.levelUnitData.levelSpacing 0) (GeneralTorus.ScaleData.posBondDir c) = c.1.tgt := by
    have h : c.1.tgt - c.1.src = GeneralTorus.unitStep s.levelUnitData.torusSide
        (s.levelUnitData.levelSpacing 0) (GeneralTorus.ScaleData.posBondDir c) :=
      c.2.choose_spec
    rw [← h, add_sub_cancel]
  show (s.levelUnitData.levelSpacing 0)⁻¹ * ((f ∘ (bareSiteEquiv s).symm) (c.1.src + _) -
      (f ∘ (bareSiteEquiv s).symm) c.1.src) =
    (PeriodicLattice.finestMeshInLevelUnits s.data.L s.data.t)⁻¹ * _
  have hval : (f ∘ (bareSiteEquiv s).symm) c.1.tgt - (f ∘ (bareSiteEquiv s).symm) c.1.src =
      f b.1.target - f b.1.source := by
    show f ((bareSiteEquiv s).symm (bareSiteEquiv s b.1.target)) -
      f ((bareSiteEquiv s).symm (bareSiteEquiv s b.1.source)) = _
    simp
  rw [hh, hval]
  exact congrArg (fun r => r⁻¹ * (f b.1.target - f b.1.source)) (levelSpacing_zero_eq s)
end Rescaling
section QuadraticForms
theorem scaledDot_indicator {ι : Type} [Finite ι] (c : ℝ) (X : Set ι) (g u : ι → ℝ)
    (hg : ∀ i, i ∉ X → g i = 0) : scaledDot c g (X.indicator u) = scaledDot c g u := by
  simp only [scaledDot_apply]
  congr 1
  refine finsum_congr fun i => ?_
  by_cases h : i ∈ X
  · simp [h]
  · simp [h, hg i h]
open PeriodicLattice in
theorem scaledDot_dirichletLaplacian {L m K : ℕ} [Finite (BareSite L m K)]
    [Finite (BareBond L m K)] (t : ℕ)
    (hc : finestMeshInLevelUnits L t ^ 4 ≠ 0) (Ω₀ : Set (FourTorus L m))
    (f g : ↥(zeroFormsOn K Ω₀)) :
    scaledDot (finestMeshInLevelUnits L t ^ 4) g.1 (dirichletLaplacian K t Ω₀ f).1 =
      scaledDot (finestMeshInLevelUnits L t ^ 4) (grad t f.1) (grad t g.1) := by
  have hadj : ∀ f g, latticeInner L t g (grad t f) =
      latticeInner L t (gradAdjoint L m K t g) f := by
    obtain ⟨T, hT⟩ := exists_adjoint_of_definite
      (scaledDot (finestMeshInLevelUnits L t ^ 4) (ι := BareSite L m K))
      (fun v => eq_zero_of_scaledDot_self hc v)
      (scaledDot (finestMeshInLevelUnits L t ^ 4) (ι := BareBond L m K)) (grad t)
    exact Classical.epsilon_spec
      (p := fun T' : OneForms L m K →ₗ[ℝ] ZeroForms L m K =>
        ∀ f g, latticeInner L t g (grad t f) = latticeInner L t (T' g) f)
      ⟨T, fun f g => (scaledDot_comm _ _ _).trans (hT f g)⟩
  have hf : siteProjection K Ω₀ f.1 = f.1 := by
    obtain ⟨h, hh⟩ := f.2
    rw [← hh]
    show (sitesOfRegion K Ω₀).indicator ((sitesOfRegion K Ω₀).indicator h) = _
    rw [Set.indicator_indicator, Set.inter_self]
    rfl
  have hg0 : ∀ i, i ∉ sitesOfRegion K Ω₀ → g.1 i = 0 := by
    obtain ⟨h, hh⟩ := g.2
    intro i hi
    rw [← hh]
    exact Set.indicator_of_notMem hi h
  calc scaledDot (finestMeshInLevelUnits L t ^ 4) g.1 (dirichletLaplacian K t Ω₀ f).1
      = scaledDot (finestMeshInLevelUnits L t ^ 4) g.1
          (gradAdjoint L m K t (grad t f.1)) := by
        show scaledDot _ g.1 ((sitesOfRegion K Ω₀).indicator
          (scalarLaplacian L m K t (siteProjection K Ω₀ f.1))) = _
        rw [scaledDot_indicator _ _ _ _ hg0, hf]
        rfl
    _ = scaledDot (finestMeshInLevelUnits L t ^ 4) (gradAdjoint L m K t (grad t f.1)) g.1 :=
        scaledDot_comm _ _ _
    _ = scaledDot (finestMeshInLevelUnits L t ^ 4) (grad t f.1) (grad t g.1) :=
        (hadj g.1 (grad t f.1)).symm
theorem scaledDot_dirichletLap {D : GeneralTorus.ScaleData} [Finite D.BaseBond]
    (B : GeneralTorus.SeparatedChain D) (hc : D.levelSpacing 0 ^ 4 ≠ 0)
    (f g : ↥B.dirichletSites) :
    scaledDot (D.levelSpacing 0 ^ 4) g.1 (B.dirichletLap f).1 =
      scaledDot (D.levelSpacing 0 ^ 4) (D.grad f.1) (D.grad g.1) := by
  have hχ : GeneralTorus.IsOrthProjFor D.siteInner B.dirichletSites B.siteProj := by
    obtain ⟨P, h1, h2⟩ := exists_orthogonalProjection_of_definite
      (scaledDot (D.levelSpacing 0 ^ 4) (ι := D.BaseSite))
      (scaledDot_comm _) (fun v => eq_zero_of_scaledDot_self hc v) B.dirichletSites
    exact Classical.epsilon_spec (p := GeneralTorus.IsOrthProjFor D.siteInner B.dirichletSites)
      ⟨P, h1, h2⟩
  have hT : GeneralTorus.IsAdjointFor D.siteInner D.bondInner D.grad D.gradAdjoint := by
    obtain ⟨T, hT⟩ := exists_adjoint_of_definite
      (scaledDot (D.levelSpacing 0 ^ 4) (ι := D.BaseSite))
      (fun v => eq_zero_of_scaledDot_self hc v)
      (scaledDot (D.levelSpacing 0 ^ 4) (ι := D.BaseBond)) D.grad
    exact Classical.epsilon_spec
      (p := GeneralTorus.IsAdjointFor D.siteInner D.bondInner D.grad)
      ⟨T, fun v u => (hT v u).trans (scaledDot_comm _ _ _)⟩
  have h1 : scaledDot (D.levelSpacing 0 ^ 4) (D.gradAdjoint (D.grad f.1) -
      (B.siteProj (D.gradAdjoint (D.grad f.1))).1) g.1 = 0 :=
    hχ.2 _ g.1 g.2
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h1
  have h2 : scaledDot (D.levelSpacing 0 ^ 4) (D.grad g.1) (D.grad f.1) =
      scaledDot (D.levelSpacing 0 ^ 4) g.1 (D.gradAdjoint (D.grad f.1)) :=
    hT g.1 (D.grad f.1)
  calc scaledDot (D.levelSpacing 0 ^ 4) g.1 (B.dirichletLap f).1
      = scaledDot (D.levelSpacing 0 ^ 4) (B.siteProj (D.gradAdjoint (D.grad f.1))).1 g.1 :=
        scaledDot_comm _ _ _
    _ = scaledDot (D.levelSpacing 0 ^ 4) g.1 (D.gradAdjoint (D.grad f.1)) := by
        rw [← h1, scaledDot_comm]
    _ = scaledDot (D.levelSpacing 0 ^ 4) (D.grad f.1) (D.grad g.1) := by
        rw [← h2, scaledDot_comm]
theorem gaugeRangeProjection_spec (D : SeparatedSequences.BaseParameters) (Ω : ℕ → Set D.Torus)
    [Finite (BareSite D.L D.m D.K)]
    (hc : PeriodicLattice.finestMeshInLevelUnits D.L D.t ^ 4 ≠ 0)
    (f : ↥(zeroFormsOn D.K (Ω 0))) :
    D.gaugeRangeProjection Ω f ∈
        (D.averageZeroKernel Ω).map (dirichletLaplacian D.K D.t (Ω 0)) ∧
      ∀ w ∈ (D.averageZeroKernel Ω).map (dirichletLaplacian D.K D.t (Ω 0)),
        scaledDot (PeriodicLattice.finestMeshInLevelUnits D.L D.t ^ 4)
          (f - D.gaugeRangeProjection Ω f).1 w.1 = 0 := by
  have h : RealInnerForms.IsOrthogonalProjectionFor (D.restrictedZeroInner Ω)
      (D.laplacianImageOfAverageZeroKernel Ω) (D.gaugeRangeProjection Ω) := by
    obtain ⟨P, -, h2⟩ := exists_orthogonalProjection_of_definite
      ((scaledDot (PeriodicLattice.finestMeshInLevelUnits D.L D.t ^ 4)
        (ι := BareSite D.L D.m D.K)).domRestrict₁₂
        (zeroFormsOn D.K (Ω 0)) (zeroFormsOn D.K (Ω 0)))
      (fun v w => scaledDot_comm _ _ _)
      (fun v hv => Subtype.ext (eq_zero_of_scaledDot_self hc _ hv))
      (D.laplacianImageOfAverageZeroKernel Ω)
    exact Classical.epsilon_spec
      (p := RealInnerForms.IsOrthogonalProjectionFor (D.restrictedZeroInner Ω)
        (D.laplacianImageOfAverageZeroKernel Ω))
      ⟨(D.laplacianImageOfAverageZeroKernel Ω).subtype ∘ₗ P, fun f => ⟨(P f).2, h2 f⟩⟩
  exact h f
theorem lapImageProj_spec {D : GeneralTorus.ScaleData}
    (B : GeneralTorus.SeparatedChain D) (hc : D.levelSpacing 0 ^ 4 ≠ 0) (f : ↥B.dirichletSites) :
    B.lapImageProj f ∈ B.siteMeansKer.map B.dirichletLap ∧
      ∀ w ∈ B.siteMeansKer.map B.dirichletLap,
        scaledDot (D.levelSpacing 0 ^ 4) (f - B.lapImageProj f).1 w.1 = 0 := by
  have h : GeneralTorus.IsOrthProjFor B.dirichletInner
      (B.siteMeansKer.map B.dirichletLap)
      (GeneralTorus.orthProjFor B.dirichletInner
        (B.siteMeansKer.map B.dirichletLap)) := by
    obtain ⟨P, h1, h2⟩ := exists_orthogonalProjection_of_definite
      ((scaledDot (D.levelSpacing 0 ^ 4) (ι := D.BaseSite)).domRestrict₁₂
        B.dirichletSites B.dirichletSites)
      (fun v w => scaledDot_comm _ _ _)
      (fun v hv => Subtype.ext (eq_zero_of_scaledDot_self hc _ hv))
      (B.siteMeansKer.map B.dirichletLap)
    exact Classical.epsilon_spec
      (p := GeneralTorus.IsOrthProjFor B.dirichletInner
        (B.siteMeansKer.map B.dirichletLap))
      ⟨P, h1, h2⟩
  exact ⟨(GeneralTorus.orthProjFor B.dirichletInner
    (B.siteMeansKer.map B.dirichletLap) f).2, fun w hw => h.2 f w hw⟩
end QuadraticForms
section BlockMeans
variable (s : SequenceData) (B : GeneralTorus.SeparatedChain s.levelUnitData)
theorem levelSpacing_injective : Function.Injective s.levelUnitData.levelSpacing := by
  intro a b h
  have h2 : (1 : ℝ) < s.data.L := by
    have := s.data.isAdmissible.2
    exact_mod_cast (by omega : 1 < s.data.L)
  have h' : (s.data.L : ℝ) ^ a * s.levelUnitData.baseSpacing =
      (s.data.L : ℝ) ^ b * s.levelUnitData.baseSpacing := h
  exact pow_right_injective₀ (by linarith) h2.ne'
    (mul_right_cancel₀ s.levelUnitData.baseSpacing_pos.ne' h')
variable {s B}
theorem blockSiteMean_rescale (hs : s.LayerSitesMatch B.shellSites)
    (hsp : s.MeshesMatch B.localSpacing)
    (hcu : s.BlocksMatch B.localCube) (u : s.data.SiteFn) {n : ℕ} (hn : n ≤ s.data.t)
    (z : s.data.LatticeSite n) (hz : z ∈ s.data.layerSitesAt s.Ω n) :
    rescaleEquiv s (z : s.data.Point) ∈ B.shellSites n ∧
      B.shellIndex (rescaleEquiv s (z : s.data.Point)) = n ∧
      s.levelUnitData.blockSiteMean n (u ∘ (bareSiteEquiv s).symm)
          (rescaleEquiv s (z : s.data.Point)) =
        s.params.blockAverageZero n u z := by
  have hread : s.toTorus s.levelUnitData.torusSide = rescaleEquiv s :=
    funext (toTorus_eq_rescaleEquiv s)
  let Y : s.data.Apex s.Ω := ⟨⟨n, z⟩, hn, hz⟩
  have hlay : rescaleEquiv s (z : s.data.Point) ∈ B.shellSites n := by
    rw [← hs n hn]
    exact ⟨z, hz, toTorus_eq_rescaleEquiv s _⟩
  have hxi : B.localSpacing (rescaleEquiv s (z : s.data.Point)) =
      s.levelUnitData.levelSpacing n := by
    have h := hsp Y
    rw [hread] at h
    exact h.trans (levelSpacing_eq_coarseMesh s n).symm
  have hlev : B.shellIndex (rescaleEquiv s (z : s.data.Point)) = n := levelSpacing_injective s hxi
  have hcube : B.localCube (rescaleEquiv s (z : s.data.Point)) = rescaleEquiv s '' Y.block := by
    have h := hcu Y
    rw [hread] at h
    exact h
  have hcl : GeneralTorus.supCube (s.levelUnitData.levelSpacing n)
      (rescaleEquiv s (z : s.data.Point)) = B.localCube (rescaleEquiv s (z : s.data.Point)) := by
    rw [GeneralTorus.SeparatedChain.localCube, hxi]
  have hblock : ∀ x : s.data.BareSite,
      (x : s.data.Point) ∈ SeparatedSequences.BaseParameters.fineBlock (D := s.params) z ↔
        bareSiteEquiv s x ∈ GeneralTorus.sitesIn (S := s.levelUnitData.torusSide)
          (s.levelUnitData.levelSpacing 0)
          (s.levelUnitData.baseBlock n (rescaleEquiv s (z : s.data.Point))) := by
    intro x
    show (x : s.data.Point) ∈ Y.block ∩
        (PeriodicLattice.sublattice s.data.L s.data.m (PeriodicLattice.levelDepth s.data.cutoff 0) :
          Set s.data.Point) ↔
      rescaleEquiv s (x : s.data.Point) ∈
        GeneralTorus.supCube (s.levelUnitData.levelSpacing n) (rescaleEquiv s (z : s.data.Point)) ∩
          (GeneralTorus.spacingLattice s.levelUnitData.torusSide (s.levelUnitData.levelSpacing 0) :
            Set s.levelUnitData.Space)
    rw [hcl, hcube]
    constructor
    · rintro ⟨h, -⟩
      exact ⟨⟨_, h, rfl⟩, (bareSiteEquiv s x).2⟩
    · rintro ⟨⟨w, hw, hwx⟩, -⟩
      rw [(rescaleEquiv s).injective hwx] at hw
      exact ⟨hw, x.2⟩
  refine ⟨hlay, hlev, ?_⟩
  have hsum : ∑ᶠ x ∈ GeneralTorus.sitesIn (S := s.levelUnitData.torusSide)
        (s.levelUnitData.levelSpacing 0)
        (s.levelUnitData.baseBlock n (rescaleEquiv s (z : s.data.Point))),
        (u ∘ (bareSiteEquiv s).symm) x =
      ∑ᶠ x : {x : s.data.BareSite //
        (x : s.data.Point) ∈ SeparatedSequences.BaseParameters.fineBlock (D := s.params) z},
          u x.1 := by
    rw [← finsum_set_coe_eq_finsum_mem,
      ← finsum_comp_equiv ((bareSiteEquiv s).subtypeEquiv hblock)]
    refine finsum_congr fun x => ?_
    simp [Function.comp]
  have hN : ((s.levelUnitData.blockSize n : ℕ) : ℝ) ^ 4 = (s.data.L : ℝ) ^ (n * 4) := by
    show (((s.data.L ^ n : ℕ)) : ℝ) ^ 4 = _
    push_cast
    rw [pow_mul]
  show (((s.levelUnitData.blockSize n : ℕ) : ℝ) ^ 4)⁻¹ * _ = ((s.data.L : ℝ) ^ (n * 4))⁻¹ * _
  rw [hN, hsum]
theorem mem_averageZeroKernel_iff (hs : s.LayerSitesMatch B.shellSites)
    (hsp : s.MeshesMatch B.localSpacing)
    (hcu : s.BlocksMatch B.localCube) (hal : s.AllLayerSitesMatch B.shellSitesUnion)
    (f : ↥(zeroFormsOn s.params.K (s.Ω 0))) (g : ↥B.dirichletSites)
    (hg : g.1 = f.1 ∘ (bareSiteEquiv s).symm) :
    f ∈ s.params.averageZeroKernel s.Ω ↔ g ∈ B.siteMeansKer := by
  have key : ∀ y : ↥(s.params.allLayerPoints s.Ω), ∃ hy : rescaleEquiv s y.1 ∈ B.shellSitesUnion,
      B.siteMeans g ⟨rescaleEquiv s y.1, hy⟩ = s.params.averageZero s.Ω f y := by
    intro y
    obtain ⟨hn, hz, hyz⟩ : (s.params.levelSite s.Ω y).1 ≤ s.data.t ∧
        (s.params.levelSite s.Ω y).2 ∈
          s.params.layerSites s.Ω (s.params.levelSite s.Ω y).1 ∧
        ((s.params.levelSite s.Ω y).2 : s.data.Point) = y.1 :=
      (s.params.exists_levelSite s.Ω y).choose_spec
    obtain ⟨hlay, hlev, hav⟩ := blockSiteMean_rescale hs hsp hcu f.1 hn _ hz
    have e1 : rescaleEquiv s y.1 =
        rescaleEquiv s ((s.params.levelSite s.Ω y).2 : s.data.Point) := by
      rw [hyz]
    have hall : rescaleEquiv s y.1 ∈ B.shellSitesUnion := by
      rw [e1]
      exact mem_iUnion₂.2 ⟨_, hn, hlay⟩
    refine ⟨hall, ?_⟩
    show s.levelUnitData.blockSiteMean (B.shellIndex (rescaleEquiv s y.1)) g.1
        (rescaleEquiv s y.1) =
      s.params.blockAverageZero (s.params.levelSite s.Ω y).1 f.1 (s.params.levelSite s.Ω y).2
    rw [e1, hlev, hg]
    exact hav
  constructor
  · intro h
    have h0 : s.params.averageZero s.Ω f = 0 := h
    show B.siteMeans g = 0
    funext ⟨y', hy'⟩
    have hy'' : y' ∈ s.toTorus s.levelUnitData.torusSide '' s.data.layerPts s.Ω := by
      rw [hal]
      exact hy'
    obtain ⟨y, hy, rfl⟩ := hy''
    obtain ⟨h1, h2⟩ := key ⟨y, hy⟩
    have e2 : (⟨s.toTorus s.levelUnitData.torusSide y, hy'⟩ : ↥B.shellSitesUnion) =
        ⟨rescaleEquiv s y, h1⟩ :=
      Subtype.ext (toTorus_eq_rescaleEquiv s y)
    rw [e2, h2, h0]
    rfl
  · intro h
    have h0 : B.siteMeans g = 0 := h
    show s.params.averageZero s.Ω f = 0
    funext y
    obtain ⟨h1, h2⟩ := key y
    rw [← h2, h0]
    rfl
end BlockMeans
theorem statement_holds (hgeo : GaugeGeometryOfClass.Statement) : Statement := by
  intro s W hW
  have hG := hgeo s W hW
  obtain ⟨D, B, hgap, ch, a, ha⟩ := W
  obtain ⟨hd, hm, -, -⟩ := hW
  change D = s.levelUnitData at hd
  subst hd
  change ∀ n, B.set n = s.regionOn s.levelUnitData.torusSide n at hm
  have hs : s.LayerSitesMatch B.shellSites := hG.layerSites
  have hsp : s.MeshesMatch B.localSpacing := hG.meshes
  have hcu : s.BlocksMatch B.localCube := hG.blocks
  have hal : s.AllLayerSitesMatch B.shellSitesUnion := hG.allLayerSites
  have hLpos : 0 < s.data.L := by
    have := s.data.isAdmissible.2
    omega
  have : Finite (BareSite s.data.L s.data.m s.data.cutoff) :=
    SeparatedSequences.BaseParameters.site_finite hLpos _ _
  have : Finite (BareBond s.data.L s.data.m s.data.cutoff) :=
    s.params.instFiniteLevelBond 0
  have : Finite s.levelUnitData.BaseBond := Finite.of_equiv _ (bareBondEquiv s)
  have hread : s.toTorus s.levelUnitData.torusSide = rescaleEquiv s :=
    funext (toTorus_eq_rescaleEquiv s)
  have hR : ∀ (x : s.data.BareSite) (x' : s.levelUnitData.BaseSite),
      s.toTorus s.levelUnitData.torusSide (x : s.data.Point) = (x' : s.levelUnitData.Space) ↔
        x' = bareSiteEquiv s x := by
    intro x x'
    rw [toTorus_eq_rescaleEquiv, Subtype.ext_iff, coe_bareSiteEquiv]
    exact eq_comm
  have hmem0 : ∀ x : s.data.BareSite, (x : s.data.Point) ∈ s.Ω 0 ↔
      (bareSiteEquiv s x : s.levelUnitData.Space) ∈ B.set 0 := by
    intro x
    rw [hm, SequenceData.regionOn, hread, coe_bareSiteEquiv]
    exact (rescaleEquiv s).injective.mem_set_image.symm
  have hzero : ∀ f : s.data.SiteFn, f ∈ zeroFormsOn s.data.cutoff (s.Ω 0) ↔
      ∀ x : s.data.BareSite, (x : s.data.Point) ∉ s.Ω 0 → f x = 0 := by
    intro f
    constructor
    · rintro ⟨h, rfl⟩ x hx
      exact Set.indicator_of_notMem (show x ∉ sitesOfRegion s.data.cutoff (s.Ω 0) from hx) h
    · intro h
      refine ⟨f, funext fun x => ?_⟩
      by_cases hx : (x : s.data.Point) ∈ s.Ω 0
      · exact Set.indicator_of_mem (s := sitesOfRegion s.data.cutoff (s.Ω 0)) hx f
      · rw [h x hx]
        exact Set.indicator_of_notMem (show x ∉ sitesOfRegion s.data.cutoff (s.Ω 0) from hx) f
  have hF : ∀ f : s.data.SiteFn, f ∈ zeroFormsOn s.data.cutoff (s.Ω 0) ↔
      f ∘ (bareSiteEquiv s).symm ∈ B.dirichletSites := by
    intro f
    rw [hzero]
    constructor
    · intro h x' hx'
      refine h _ fun hin => hx' ?_
      have := (hmem0 _).1 hin
      simpa using this
    · intro h x hx
      have h1 := h (bareSiteEquiv s x) fun hin => hx ((hmem0 x).2 hin)
      simpa using h1
  obtain ⟨c, hc1⟩ : ∃ c, c = s.levelUnitData.levelSpacing 0 ^ 4 := ⟨_, rfl⟩
  have hc2 : c = PeriodicLattice.finestMeshInLevelUnits s.data.L s.data.t ^ 4 := by
    rw [hc1, levelSpacing_zero_eq]
  have hc0 : c ≠ 0 := by
    rw [hc1]
    exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ (blockFactor_cast_ne_zero s))
      s.levelUnitData.baseSpacing_pos.ne')
  have key := orthProj_transport (c := c) hc0 (bareSiteEquiv s) (bareBondEquiv s)
    (grad s.data.t) s.levelUnitData.grad (grad_comp_bareSiteEquiv_symm s)
    (zeroFormsOn s.data.cutoff (s.Ω 0)) B.dirichletSites hF
    (dirichletLaplacian s.data.cutoff s.data.t (s.Ω 0)) B.dirichletLap
    (fun f g => by
      rw [hc2]
      exact scaledDot_dirichletLaplacian s.data.t (hc2 ▸ hc0) (s.Ω 0) f g)
    (fun f g => by
      rw [hc1]
      exact scaledDot_dirichletLap B (hc1 ▸ hc0) f g)
    (s.params.averageZeroKernel s.Ω) B.siteMeansKer
    (fun f f' h => mem_averageZeroKernel_iff hs hsp hcu hal f f' h)
    (s.params.gaugeRangeProjection s.Ω) B.lapImageProj
    (fun f => by
      rw [hc2]
      exact gaugeRangeProjection_spec s.params s.Ω (hc2 ▸ hc0) f)
    (fun f => by
      rw [hc1]
      exact lapImageProj_spec B (hc1 ▸ hc0) f)
  refine ⟨⟨fun x => ⟨bareSiteEquiv s x, (hR x _).2 rfl, fun y hy => (hR x y).1 hy⟩,
    fun x' => ⟨(bareSiteEquiv s).symm x', (hR _ x').2 (by simp), fun y hy => ?_⟩⟩, ⟨?_, ?_⟩, ?_⟩
  · have := (hR y x').1 hy
    simp [this]
  · intro f hf
    refine ⟨f ∘ (bareSiteEquiv s).symm, (hF f).1 hf, fun x x' hx => ?_⟩
    have h : x' = bareSiteEquiv s x := (hR x x').1 hx
    simp [h]
  · intro f' hf'
    have hcomp : (f' ∘ bareSiteEquiv s) ∘ (bareSiteEquiv s).symm = f' := by
      funext x
      simp
    refine ⟨f' ∘ bareSiteEquiv s, (hF _).2 (by rw [hcomp]; exact hf'), fun x x' hx => ?_⟩
    have h : x' = bareSiteEquiv s x := (hR x x').1 hx
    simp [h]
  · intro f hf f' hf' hsame x x' hx
    have hf1 : f ∈ zeroFormsOn s.data.cutoff (s.Ω 0) := hf
    have hf2 : f' ∈ B.dirichletSites := hf'
    have heq : f' = f ∘ (bareSiteEquiv s).symm := by
      funext y
      exact (hsame ((bareSiteEquiv s).symm y) y ((hR _ y).2 (by simp))).symm
    have h := key ⟨f, hf1⟩ ⟨f', hf2⟩ heq
    have hx' : x' = bareSiteEquiv s x := (hR x x').1 hx
    show s.rangeProj f x = _root_.YangMills.Construction.SeparatedClasses.SingleSequence.extendByZero B.dirichletSites
      (fun f => (B.lapImageProj f).1) f' x'
    simp only [SequenceData.rangeProj, _root_.YangMills.Construction.SeparatedClasses.SingleSequence.extendByZero, dif_pos hf1, dif_pos hf2]
    rw [h, hx']
    simp
end YangMills.Construction.SeparatedClasses.GaugeProjectionOfClass
