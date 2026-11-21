import YangMills.Construction.Lattice.DecompositionOfTheFormGreenOperatorProof
import YangMills.Construction.SeparatedSequences.ClassExpansionsAndAveragesInASettingOfRegionsProof
import YangMills.Construction.SeparatedSequences.ClassExpansionsInASettingOfRegionsProof
import YangMills.Construction.SeparatedSequences.ClassExpansionsOnAGeneralTorus
import YangMills.Construction.SeparatedSequences.ClassProjectionOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice.DirichletOperators
open scoped Pointwise
noncomputable section
namespace YangMills.Construction.SeparatedClasses.GaugeOneFormsProof
open SingleSequence SingleSequence.SequenceData
namespace TorusComponents
variable (s : SequenceData)
theorem blockFactor_pos : (0 : ℝ) < s.data.L := by apply _root_.YangMills.Construction.SeparatedClasses.SingleSequence.NestedRescale.blockFactor_pos <;> assumption
theorem one_lt_blockFactor : (1 : ℝ) < s.data.L := by
  have h := s.data.isAdmissible.2
  exact_mod_cast (by omega : 1 < s.data.L)
theorem unitScale_pos : 0 < s.unitScale := pow_pos (blockFactor_pos s) _
theorem unitScale_eq_zpow :
    s.unitScale = (s.data.L : ℝ) ^ (((s.data.cutoff : ℕ) : ℤ) - (s.data.t : ℤ)) := by
  have h : s.data.t ≤ s.data.cutoff := s.data.t_le_cutoff
  change (s.data.L : ℝ) ^ (s.data.cutoff - s.data.t) = _
  rw [← zpow_natCast, Nat.cast_sub h]
theorem gaugeSide_eq :
    s.levelUnitData.torusSide = s.unitScale * PeriodicLattice.torusSide s.data.L s.data.m := by
  have h : s.data.t ≤ s.data.cutoff := s.data.t_le_cutoff
  have hL := (blockFactor_pos s).ne'
  change 2 * (s.data.L : ℝ) ^ ((s.data.m : ℕ) + s.data.cutoff - s.data.t) = _
  rw [unitScale_eq_zpow, PeriodicLattice.torusSide, ← zpow_natCast,
    ← zpow_natCast (s.data.L : ℝ) (s.data.m : ℕ), mul_left_comm, ← zpow_add₀ hL]
  congr 2
  have : s.data.t ≤ (s.data.m : ℕ) + s.data.cutoff := by omega
  rw [Nat.cast_sub this]
  push_cast
  ring
theorem gaugeSide_ne_zero : s.levelUnitData.torusSide ≠ 0 := by
  rw [gaugeSide_eq]
  exact mul_ne_zero (unitScale_pos s).ne' s.torusSide_ne_zero
theorem levelSpacing_eq (n : ℕ) :
    s.levelUnitData.levelSpacing n =
      s.unitScale * PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) := by
  have hL := (blockFactor_pos s).ne'
  change (s.data.L : ℝ) ^ n * (s.data.L : ℝ) ^ (-(s.data.t : ℤ)) = _
  rw [unitScale_eq_zpow, PeriodicLattice.meshSize, ← zpow_add₀ hL, ← zpow_natCast, ← zpow_add₀ hL]
  congr 1
  simp only [PeriodicLattice.levelDepth]
  ring
theorem levelSpacing_pos (n : ℕ) : 0 < s.levelUnitData.levelSpacing n := by
  rw [levelSpacing_eq]
  exact mul_pos (unitScale_pos s) (zpow_pos (blockFactor_pos s) _)
def torusEquiv : s.data.Point ≃+ Torus4 s.levelUnitData.torusSide :=
  AddEquiv.piCongrRight fun _ =>
    AddCircle.equivAddCircle _ _ s.torusSide_ne_zero (gaugeSide_ne_zero s)
theorem toTorus_eq (x : s.data.Point) : s.toTorus s.levelUnitData.torusSide x = torusEquiv s x := by
  unfold SequenceData.toTorus
  rw [dif_pos (gaugeSide_ne_zero s)]
  rfl
theorem torusEquiv_coe (v : Fin 4 → ℝ) :
    torusEquiv s (fun μ => ((v μ : ℝ) : AddCircle (PeriodicLattice.torusSide s.data.L s.data.m))) =
      torusProj s.levelUnitData.torusSide (s.unitScale • v) := by
  funext μ
  change AddCircle.equivAddCircle _ _ s.torusSide_ne_zero (gaugeSide_ne_zero s)
    ((v μ : ℝ) : AddCircle _) = _
  rw [AddCircle.equivAddCircle_apply_mk]
  simp only [torusProj, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [gaugeSide_eq, mul_comm]
  congr 1
  field_simp [s.torusSide_ne_zero]
theorem torusEquiv_mem_lattice (n : ℕ) (x : s.data.Point) :
    x ∈ PeriodicLattice.sublattice s.data.L s.data.m (PeriodicLattice.levelDepth s.data.cutoff n) ↔
      torusEquiv s x ∈
        GeneralTorus.spacingLattice s.levelUnitData.torusSide (s.levelUnitData.levelSpacing n) := by
  have key : ∀ k : Fin 4 → ℤ,
      torusEquiv s (fun μ => (((k μ : ℝ) *
        PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) : ℝ) :
          AddCircle (PeriodicLattice.torusSide s.data.L s.data.m))) =
      torusProj s.levelUnitData.torusSide fun μ => s.levelUnitData.levelSpacing n * (k μ : ℝ) := by
    intro k
    rw [torusEquiv_coe]
    congr 1
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [levelSpacing_eq]
    ring
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← key]
    congr 1
    funext μ
    exact hk μ
  · rintro ⟨k, hk⟩
    refine ⟨k, fun μ => ?_⟩
    rw [← key] at hk
    exact congrFun ((torusEquiv s).injective hk) μ
theorem torusEquiv_coordPoint (μ : Fin 4) (n : ℕ) :
    torusEquiv s (PeriodicLattice.pointOnAxis s.data.L s.data.m μ
        (PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n))) =
      GeneralTorus.coordPoint s.levelUnitData.torusSide μ (s.levelUnitData.levelSpacing n) := by
  have e : PeriodicLattice.pointOnAxis s.data.L s.data.m μ
      (PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n)) =
      fun ν => (((Pi.single μ (PeriodicLattice.meshSize s.data.L
        (PeriodicLattice.levelDepth s.data.cutoff n)) : Fin 4 → ℝ) ν : ℝ) :
          AddCircle (PeriodicLattice.torusSide s.data.L s.data.m)) := by
    funext ν
    by_cases h : ν = μ
    · subst h
      simp [PeriodicLattice.pointOnAxis]
    · simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
  rw [e, torusEquiv_coe, GeneralTorus.coordPoint, levelSpacing_eq]
  congr 1
  funext ν
  by_cases h : ν = μ
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]
def siteEquiv (n : ℕ) : s.data.LatticeSite n ≃+ s.levelUnitData.SiteAt n where
  toFun x := ⟨torusEquiv s x.1, (torusEquiv_mem_lattice s n x.1).1 x.2⟩
  invFun y := ⟨(torusEquiv s).symm y.1, (torusEquiv_mem_lattice s n _).2 (by simp)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
theorem siteEquiv_unitStep (n : ℕ) (μ : Fin 4) :
    siteEquiv s n
        (PeriodicLattice.unitStep s.data.L s.data.m (PeriodicLattice.levelDepth s.data.cutoff n) μ) =
      GeneralTorus.unitStep s.levelUnitData.torusSide (s.levelUnitData.levelSpacing n) μ :=
  Subtype.ext (torusEquiv_coordPoint s μ n)
def bondEquiv (n : ℕ) : s.data.PosLatticeBond n ≃ s.levelUnitData.PosBond n where
  toFun c := ⟨⟨siteEquiv s n c.1.source, siteEquiv s n c.1.target, by
      obtain ⟨μ, h⟩ := c.2
      exact ⟨μ, Or.inl (by rw [← map_sub, h, siteEquiv_unitStep])⟩⟩, by
      obtain ⟨μ, h⟩ := c.2
      exact ⟨μ, by
        change siteEquiv s n c.1.target - siteEquiv s n c.1.source = _
        rw [← map_sub, h, siteEquiv_unitStep]⟩⟩
  invFun c := ⟨⟨(siteEquiv s n).symm c.1.src, (siteEquiv s n).symm c.1.tgt, by
      obtain ⟨μ, h⟩ := c.2
      refine ⟨μ, Or.inl ?_⟩
      rw [← map_sub, h, ← siteEquiv_unitStep, AddEquiv.symm_apply_apply]⟩, by
      obtain ⟨μ, h⟩ := c.2
      refine ⟨μ, ?_⟩
      change (siteEquiv s n).symm c.1.tgt - (siteEquiv s n).symm c.1.src = _
      rw [← map_sub, h, ← siteEquiv_unitStep, AddEquiv.symm_apply_apply]⟩
  left_inv c := Subtype.ext (PeriodicLattice.Bond.ext (by simp) (by simp))
  right_inv c := Subtype.ext (GeneralTorus.LatticeBond.ext (by simp) (by simp))
theorem bondEquiv_src (n : ℕ) (c : s.data.PosLatticeBond n) :
    (bondEquiv s n c).1.src = siteEquiv s n c.1.source := rfl
theorem bondEquiv_tgt (n : ℕ) (c : s.data.PosLatticeBond n) :
    (bondEquiv s n c).1.tgt = siteEquiv s n c.1.target := rfl
end TorusComponents
namespace FunctionTransport
def transport {X Y : Type} (e : X ≃ Y) : (X → ℝ) ≃ₗ[ℝ] (Y → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ e.symm
theorem transport_apply {X Y : Type} (e : X ≃ Y) (f : X → ℝ) (y : Y) :
    transport e f y = f (e.symm y) := rfl
theorem transport_apply_equiv {X Y : Type} (e : X ≃ Y) (f : X → ℝ) (x : X) :
    transport e f (e x) = f x := by
  rw [transport_apply, Equiv.symm_apply_apply]
theorem exists_transport_eq {X Y : Type} (e : X ≃ Y) (g : Y → ℝ) : ∃ f, transport e f = g :=
  (transport e).surjective g
theorem finsum_transport_mul {X Y : Type} (e : X ≃ Y) (f g : X → ℝ) :
    ∑ᶠ y, transport e f y * transport e g y = ∑ᶠ x, f x * g x := by
  rw [← finsum_comp_equiv e]
  simp only [transport_apply_equiv]
theorem exists_weighted_adjoint {ι κ : Type} [Finite ι] [Finite κ] (w : κ → ℝ)
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    ∃ T' : (κ → ℝ) →ₗ[ℝ] (ι → ℝ), ∀ f g, ∑ᶠ k, w k * (T f k * g k) = ∑ᶠ i, f i * T' g i := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  let W : (κ → ℝ) →ₗ[ℝ] (κ → ℝ) :=
    { toFun := fun g k => w k * g k
      map_add' := fun g h => by funext k; simp [mul_add]
      map_smul' := fun c g => by funext k; simp; ring }
  refine ⟨Matrix.toLin' (LinearMap.toMatrix' T).transpose ∘ₗ W, fun f g => ?_⟩
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have h1 : ∑ i, f i * (Matrix.toLin' (LinearMap.toMatrix' T).transpose ∘ₗ W) g i =
      f ⬝ᵥ ((LinearMap.toMatrix' T).transpose.mulVec (W g)) := by
    simp [dotProduct]
  have h2 : ∑ k, w k * (T f k * g k) = (T f) ⬝ᵥ (W g) := by
    simp only [dotProduct, W, LinearMap.coe_mk, AddHom.coe_mk]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h1, h2, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
theorem formalAdjoint_spec {ι κ : Type} [Finite ι] [Finite κ] (L t : ℕ)
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (f : ι → ℝ) (g : κ → ℝ) :
    latticeInner L t g (T f) = latticeInner L t (formalAdjoint L t T g) f := by apply _root_.YangMills.Construction.SeparatedSequences.GreenDecomposition.formalAdjoint_spec <;> assumption
theorem eq_of_forall_weighted_sum {ι : Type} {c : ℝ} (hc : c ≠ 0) (Y : Set ι) {a b : ι → ℝ}
    (ha : ∀ i, i ∉ Y → a i = 0) (hb : ∀ i, i ∉ Y → b i = 0)
    (h : ∀ f : ι → ℝ, (∀ i, i ∉ Y → f i = 0) → c * ∑ᶠ i, f i * a i = c * ∑ᶠ i, f i * b i) :
    a = b := by
  classical
  funext i
  by_cases hi : i ∈ Y
  · have h1 := h (Pi.single i 1) fun j hj => by
      have : j ≠ i := fun e => hj (e ▸ hi)
      simp [Pi.single_eq_of_ne this]
    have hs : ∀ d : ι → ℝ, ∑ᶠ j, (Pi.single i 1 : ι → ℝ) j * d j = d i := fun d => by
      rw [finsum_eq_single _ i fun j hj => by simp [Pi.single_eq_of_ne hj]]
      simp
    rw [hs, hs] at h1
    exact mul_left_cancel₀ hc h1
  · rw [ha i hi, hb i hi]
theorem adjointFor_eq {V U : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup U] [Module ℝ U]
    {p : V → V → ℝ} {q : U → U → ℝ} {K : V →ₗ[ℝ] U} {T : U →ₗ[ℝ] V}
    (hT : GeneralTorus.IsAdjointFor p q K T) (hp : ∀ a b, (∀ v, p v a = p v b) → a = b) :
    GeneralTorus.adjointFor p q K = T := by
  have hex : ∃ T', GeneralTorus.IsAdjointFor p q K T' := ⟨T, hT⟩
  have spec : GeneralTorus.IsAdjointFor p q K (GeneralTorus.adjointFor p q K) :=
    Classical.epsilon_spec hex
  refine LinearMap.ext fun u => hp _ _ fun v => ?_
  rw [← spec v u, hT v u]
theorem adjointFor_transport {X Y X' Y' : Type} [Finite X] [Finite Y] (L t : ℕ)
    (eX : X ≃ X') (eY : Y ≃ Y') {p : (X' → ℝ) → (X' → ℝ) → ℝ} {q : (Y' → ℝ) → (Y' → ℝ) → ℝ}
    (hc : PeriodicLattice.finestMeshInLevelUnits L t ≠ 0)
    (hp : ∀ f g, p f g = latticeInner L t f g) (hq : ∀ f g, q f g = latticeInner L t f g)
    (K : (X → ℝ) →ₗ[ℝ] (Y → ℝ)) (K' : (X' → ℝ) →ₗ[ℝ] (Y' → ℝ))
    (hK : ∀ f, K' (transport eX f) = transport eY (K f)) (g : Y → ℝ) :
    GeneralTorus.adjointFor p q K' (transport eY g) = transport eX (formalAdjoint L t K g) := by
  have hpair : ∀ {A B : Type} (e : A ≃ B) (f g : A → ℝ),
      latticeInner L t (transport e f) (transport e g) = latticeInner L t f g := fun e f g => by
    simp only [latticeInner, finsum_transport_mul]
  have hcomm : ∀ {A : Type} (f g : A → ℝ), latticeInner L t f g = latticeInner L t g f :=
    fun f g => by
    simp only [latticeInner]
    congr 1
    exact finsum_congr fun i => mul_comm _ _
  have hT : GeneralTorus.IsAdjointFor p q K'
      ((transport eX).toLinearMap ∘ₗ formalAdjoint L t K ∘ₗ (transport eY).symm.toLinearMap) := by
    intro v u
    obtain ⟨f, rfl⟩ := exists_transport_eq eX v
    obtain ⟨g, rfl⟩ := exists_transport_eq eY u
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hK, hp, hq, hpair, hpair, hcomm, formalAdjoint_spec, hcomm]
  have hnd : ∀ a b : X' → ℝ, (∀ v, p v a = p v b) → a = b := by
    intro a b h
    have hpow : (PeriodicLattice.finestMeshInLevelUnits L t) ^ 4 ≠ 0 := pow_ne_zero _ hc
    refine eq_of_forall_weighted_sum hpow univ (fun i hi => absurd (mem_univ i) hi)
      (fun i hi => absurd (mem_univ i) hi) fun f _ => ?_
    have := h f
    rw [hp, hp] at this
    exact this
  rw [adjointFor_eq hT hnd]
  simp
theorem orthProjFor_apply {ι : Type} {c : ℝ} (hc : c ≠ 0) {p : (ι → ℝ) → (ι → ℝ) → ℝ}
    (hp : ∀ f g, p f g = c * ∑ᶠ i, f i * g i) (E : Submodule ℝ (ι → ℝ)) (Y : Set ι)
    (hE : ∀ f, f ∈ E ↔ ∀ i, i ∉ Y → f i = 0) (v : ι → ℝ) :
    ((GeneralTorus.orthProjFor p E v : ↥E) : ι → ℝ) = Y.indicator v := by
  classical
  have hex : ∃ P, GeneralTorus.IsOrthProjFor p E P := by
    let P : (ι → ℝ) →ₗ[ℝ] ↥E :=
      { toFun := fun v => ⟨Y.indicator v, (hE _).2 fun i hi => indicator_of_notMem hi v⟩
        map_add' := fun f g => Subtype.ext (indicator_add Y f g)
        map_smul' := fun r f => Subtype.ext (indicator_const_smul Y r f) }
    refine ⟨P, fun e => Subtype.ext ?_, fun v e he => ?_⟩
    · funext i
      by_cases hi : i ∈ Y
      · exact indicator_of_mem hi _
      · change Y.indicator _ i = _
        rw [indicator_of_notMem hi, (hE _).1 e.2 i hi]
    · rw [hp]
      have : ∀ i, (v - (P v : ι → ℝ)) i * e i = 0 := fun i => by
        by_cases hi : i ∈ Y
        · have : (P v : ι → ℝ) i = v i := indicator_of_mem hi _
          simp [this]
        · simp [(hE _).1 he i hi]
      rw [finsum_congr this]
      simp
  have spec : GeneralTorus.IsOrthProjFor p E (GeneralTorus.orthProjFor p E) :=
    Classical.epsilon_spec hex
  funext i
  by_cases hi : i ∈ Y
  · have hs : Pi.single i 1 ∈ E := (hE _).2 fun j hj => by
      have : j ≠ i := fun e => hj (e ▸ hi)
      simp [Pi.single_eq_of_ne this]
    have h0 := spec.2 v _ hs
    rw [hp] at h0
    rw [finsum_eq_single _ i fun j hj => by simp [Pi.single_eq_of_ne hj]] at h0
    simp only [Pi.single_eq_same, mul_one, Pi.sub_apply] at h0
    have h1 := (mul_eq_zero.1 h0).resolve_left hc
    rw [indicator_of_mem hi]
    linarith
  · rw [indicator_of_notMem hi]
    exact (hE _).1 (GeneralTorus.orthProjFor p E v).2 i hi
section Inverse
variable {V V' : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']
theorem exists_unit_of_conj (e : V ≃ₗ[ℝ] V') {T : Module.End ℝ V} {T' : Module.End ℝ V'}
    (h : ∀ v, T' (e v) = e (T v)) (hT : IsUnit T) :
    ∃ U : (Module.End ℝ V')ˣ, (U : Module.End ℝ V') = T' ∧
      ∀ v, ((U⁻¹ : (Module.End ℝ V')ˣ) : Module.End ℝ V') (e v) = e (Ring.inverse T v) := by
  obtain ⟨u, rfl⟩ := hT
  let I : Module.End ℝ V' := e.toLinearMap ∘ₗ ((u⁻¹ : (Module.End ℝ V)ˣ) : Module.End ℝ V) ∘ₗ
    e.symm.toLinearMap
  have h1 : T' * I = 1 := by
    ext x
    obtain ⟨v, rfl⟩ := e.surjective x
    simp only [Module.End.mul_apply, I, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, h, Module.End.one_apply]
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  have h2 : I * T' = 1 := by
    ext x
    obtain ⟨v, rfl⟩ := e.surjective x
    simp only [Module.End.mul_apply, I, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, h, Module.End.one_apply]
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  refine ⟨⟨T', I, h1, h2⟩, rfl, fun v => ?_⟩
  rw [Ring.inverse_unit]
  change I (e v) = _
  simp [I]
theorem ring_inverse_conj (e : V ≃ₗ[ℝ] V') {T : Module.End ℝ V} {T' : Module.End ℝ V'}
    (h : ∀ v, T' (e v) = e (T v)) (v : V) : Ring.inverse T' (e v) = e (Ring.inverse T v) := by
  by_cases hT : IsUnit T
  · obtain ⟨U, rfl, hU⟩ := exists_unit_of_conj e h hT
    rw [Ring.inverse_unit, hU]
  · have hT' : ¬IsUnit T' := fun hu => by
      have h' : ∀ w, T (e.symm w) = e.symm (T' w) := fun w => by
        obtain ⟨x, rfl⟩ := e.surjective w
        rw [h]
        simp
      obtain ⟨U, hU, -⟩ := exists_unit_of_conj e.symm h' hu
      exact hT (hU ▸ U.isUnit)
    rw [Ring.inverse_non_unit _ hT, Ring.inverse_non_unit _ hT']
    simp
end Inverse
end FunctionTransport
namespace TorusComponents
variable (s : SequenceData)
open FunctionTransport
instance finite_latticeSite (n : ℕ) : Finite (s.data.LatticeSite n) :=
  SeparatedSequences.BaseParameters.instFiniteLatticeSite s.params n
instance finite_posLatticeBond (n : ℕ) : Finite (s.data.PosLatticeBond n) :=
  SeparatedSequences.BaseParameters.instFiniteLevelBond s.params n
instance finite_bareSite : Finite s.data.BareSite := finite_latticeSite s 0
instance finite_bareBond : Finite s.data.BareBond := finite_posLatticeBond s 0
instance finite_barePlaquette : Finite (BarePlaquette s.data.L s.data.m s.data.cutoff) :=
  Finite.of_injective (fun p => (p.origin, p.firstAxis, p.secondAxis)) fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact PeriodicLattice.Plaquette.ext h.1 h.2.1 h.2.2
instance finite_posBond (n : ℕ) : Finite (s.levelUnitData.PosBond n) :=
  Finite.of_equiv _ (bondEquiv s n)
def plaquetteEquiv : BarePlaquette s.data.L s.data.m s.data.cutoff ≃ s.levelUnitData.BasePlaquette where
  toFun p := ⟨siteEquiv s 0 p.origin, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
  invFun p := ⟨(siteEquiv s 0).symm p.basePoint, p.dir₁, p.dir₂, p.dir₁_lt_dir₂⟩
  left_inv p := PeriodicLattice.Plaquette.ext (by simp) rfl rfl
  right_inv p := GeneralTorus.LatticePlaquette.ext (by simp) rfl rfl
abbrev siteTransport : s.data.SiteFn ≃ₗ[ℝ] s.levelUnitData.SiteField :=
  transport (siteEquiv s 0).toEquiv
abbrev bondTransport : s.data.BondFn ≃ₗ[ℝ] s.levelUnitData.BondField := transport (bondEquiv s 0)
abbrev plaquetteTransport :
    TwoForms s.data.L s.data.m s.data.cutoff ≃ₗ[ℝ] s.levelUnitData.PlaquetteField :=
  transport (plaquetteEquiv s)
theorem siteTransport_apply (f : s.data.SiteFn) (x : s.data.BareSite) :
    siteTransport s f (siteEquiv s 0 x) = f x := transport_apply_equiv (siteEquiv s 0).toEquiv f x
theorem bondTransport_apply (f : s.data.BondFn) (b : s.data.BareBond) :
    bondTransport s f (bondEquiv s 0 b) = f b := transport_apply_equiv (bondEquiv s 0) f b
theorem plaquetteTransport_apply (f : TwoForms s.data.L s.data.m s.data.cutoff)
    (p : BarePlaquette s.data.L s.data.m s.data.cutoff) :
    plaquetteTransport s f (plaquetteEquiv s p) = f p :=
  transport_apply_equiv (plaquetteEquiv s) f p
theorem levelSpacing_zero :
    s.levelUnitData.levelSpacing 0 = PeriodicLattice.finestMeshInLevelUnits s.data.L s.data.t := by
  change (s.data.L : ℝ) ^ 0 * (s.data.L : ℝ) ^ (-(s.data.t : ℤ)) = _
  simp [PeriodicLattice.finestMeshInLevelUnits]
theorem finestMesh_ne_zero : PeriodicLattice.finestMeshInLevelUnits s.data.L s.data.t ≠ 0 := by
  rw [← levelSpacing_zero]
  exact (levelSpacing_pos s 0).ne'
theorem siteInner_eq (f g : s.levelUnitData.SiteField) :
    s.levelUnitData.siteInner f g = latticeInner s.data.L s.data.t f g := by
  simp only [GeneralTorus.ScaleData.siteInner, latticeInner, levelSpacing_zero]
theorem bondInner_eq (f g : s.levelUnitData.BondField) :
    s.levelUnitData.bondInner f g = latticeInner s.data.L s.data.t f g := by
  simp only [GeneralTorus.ScaleData.bondInner, latticeInner, levelSpacing_zero]
theorem plaquetteInner_eq (f g : s.levelUnitData.PlaquetteField) :
    s.levelUnitData.plaquetteInner f g = latticeInner s.data.L s.data.t f g := by
  simp only [GeneralTorus.ScaleData.plaquetteInner, latticeInner, levelSpacing_zero]
theorem unitStep_injective {n : ℕ} (hn : n ≤ s.data.cutoff) {μ ν : Fin 4}
    (h : PeriodicLattice.unitStep s.data.L s.data.m (PeriodicLattice.levelDepth s.data.cutoff n) μ =
      PeriodicLattice.unitStep s.data.L s.data.m (PeriodicLattice.levelDepth s.data.cutoff n) ν) :
    μ = ν := by
  by_contra hne
  have h1 := congrFun (congrArg Subtype.val h) μ
  simp only [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_same,
    Pi.single_eq_of_ne hne] at h1
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 h1
  have hσ0 : 0 < PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) :=
    zpow_pos (blockFactor_pos s) _
  have hσ1 : PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) ≤ 1 := by
    refine zpow_le_one_of_nonpos₀ (one_lt_blockFactor s).le ?_
    simp only [PeriodicLattice.levelDepth]
    have : (n : ℤ) ≤ ((s.data.cutoff : ℕ) : ℤ) := by exact_mod_cast hn
    omega
  have hside : 2 ≤ PeriodicLattice.torusSide s.data.L s.data.m := by
    have : (1 : ℝ) ≤ (s.data.L : ℝ) ^ (s.data.m : ℕ) := one_le_pow₀ (one_lt_blockFactor s).le
    simp only [PeriodicLattice.torusSide]
    linarith
  rw [zsmul_eq_mul] at hk
  rcases lt_trichotomy k 0 with hk0 | rfl | hk0
  · have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
    nlinarith
  · simp at hk
    linarith
  · have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    nlinarith
theorem target_eq {n : ℕ} (c : s.data.PosLatticeBond n) :
    c.1.target = c.1.source +
      PeriodicLattice.unitStep _ _ _ (SeparatedSequences.BaseParameters.bondAxis c) := by
  have h : c.1.target - c.1.source =
      PeriodicLattice.unitStep _ _ _ (SeparatedSequences.BaseParameters.bondAxis c) :=
    c.2.choose_spec
  rw [← h]
  abel
theorem posBondDir_bondEquiv {n : ℕ} (hn : n ≤ s.data.cutoff) (c : s.data.PosLatticeBond n) :
    GeneralTorus.ScaleData.posBondDir (bondEquiv s n c) =
      SeparatedSequences.BaseParameters.bondAxis c := by
  have h1 : (bondEquiv s n c).1.tgt - (bondEquiv s n c).1.src =
      GeneralTorus.unitStep _ _ (GeneralTorus.ScaleData.posBondDir (bondEquiv s n c)) :=
    (bondEquiv s n c).2.choose_spec
  rw [bondEquiv_tgt, bondEquiv_src, ← map_sub, ← siteEquiv_unitStep] at h1
  have h2 := (siteEquiv s n).injective h1
  have h3 : c.1.target - c.1.source =
      PeriodicLattice.unitStep _ _ _ (SeparatedSequences.BaseParameters.bondAxis c) :=
    c.2.choose_spec
  exact unitStep_injective s hn (h2.symm.trans h3)
theorem bondEquiv_bondFrom (x : s.data.BareSite) (μ : Fin 4) :
    bondEquiv s 0 (bondFrom x μ) = GeneralTorus.ScaleData.bondFrom (siteEquiv s 0 x) μ := by
  refine Subtype.ext (GeneralTorus.LatticeBond.ext rfl ?_)
  change siteEquiv s 0 (x + PeriodicLattice.unitStep _ _ _ μ) =
    siteEquiv s 0 x + GeneralTorus.unitStep _ _ μ
  rw [map_add, siteEquiv_unitStep]
theorem formComponent_bondTransport (μ : Fin 4) (A : s.data.BondFn) :
    s.levelUnitData.formComponent μ (bondTransport s A) = siteTransport s (axisComponent A μ) := by
  funext y
  obtain ⟨x, rfl⟩ := (siteEquiv s 0).surjective y
  change bondTransport s A (GeneralTorus.ScaleData.bondFrom (siteEquiv s 0 x) μ) =
    siteTransport s (axisComponent A μ) (siteEquiv s 0 x)
  rw [← bondEquiv_bondFrom, bondTransport_apply, siteTransport_apply]
  rfl
theorem forwardDiff_siteTransport (μ : Fin 4) (f : s.data.SiteFn) :
    s.levelUnitData.forwardDiff μ (siteTransport s f) =
      siteTransport s (forwardDifference s.data.t μ f) := by
  funext y
  obtain ⟨x, rfl⟩ := (siteEquiv s 0).surjective y
  change (s.levelUnitData.levelSpacing 0)⁻¹ *
      (siteTransport s f (siteEquiv s 0 x + GeneralTorus.unitStep _ _ μ) -
        siteTransport s f (siteEquiv s 0 x)) =
    siteTransport s (forwardDifference s.data.t μ f) (siteEquiv s 0 x)
  rw [← siteEquiv_unitStep, ← map_add, siteTransport_apply, siteTransport_apply,
    siteTransport_apply, levelSpacing_zero]
  rfl
theorem grad_siteTransport (f : s.data.SiteFn) :
    s.levelUnitData.grad (siteTransport s f) = bondTransport s (grad s.data.t f) := by
  funext c'
  obtain ⟨c, rfl⟩ := (bondEquiv s 0).surjective c'
  change s.levelUnitData.forwardDiff (GeneralTorus.ScaleData.posBondDir (bondEquiv s 0 c))
    (siteTransport s f) (siteEquiv s 0 c.1.source) = bondTransport s (grad s.data.t f) (bondEquiv s 0 c)
  rw [posBondDir_bondEquiv s (Nat.zero_le _), forwardDiff_siteTransport, siteTransport_apply,
    bondTransport_apply]
  change (PeriodicLattice.finestMeshInLevelUnits s.data.L s.data.t)⁻¹ *
      (f (c.1.source + _) - f c.1.source) =
    (PeriodicLattice.finestMeshInLevelUnits s.data.L s.data.t)⁻¹ * (f c.1.target - f c.1.source)
  rw [← target_eq s c]
theorem plaquetteCurl_bondTransport (A : s.data.BondFn) :
    s.levelUnitData.plaquetteCurl (bondTransport s A) = plaquetteTransport s (curl s.data.t A) := by
  funext p'
  obtain ⟨p, rfl⟩ := (plaquetteEquiv s).surjective p'
  change s.levelUnitData.forwardDiff p.firstAxis
      (s.levelUnitData.formComponent p.secondAxis (bondTransport s A)) (siteEquiv s 0 p.origin) -
    s.levelUnitData.forwardDiff p.secondAxis
      (s.levelUnitData.formComponent p.firstAxis (bondTransport s A)) (siteEquiv s 0 p.origin) =
    plaquetteTransport s (curl s.data.t A) (plaquetteEquiv s p)
  rw [formComponent_bondTransport, formComponent_bondTransport, forwardDiff_siteTransport,
    forwardDiff_siteTransport, siteTransport_apply, siteTransport_apply, plaquetteTransport_apply]
  rfl
theorem gradAdjoint_bondTransport (A : s.data.BondFn) :
    s.levelUnitData.gradAdjoint (bondTransport s A) =
      siteTransport s (gradAdjoint s.data.L s.data.m s.data.cutoff s.data.t A) :=
  adjointFor_transport s.data.L s.data.t (siteEquiv s 0).toEquiv (bondEquiv s 0)
    (finestMesh_ne_zero s) (siteInner_eq s) (bondInner_eq s) _ _ (grad_siteTransport s) A
theorem plaquetteCurlAdjoint_plaquetteTransport (F : TwoForms s.data.L s.data.m s.data.cutoff) :
    s.levelUnitData.plaquetteCurlAdjoint (plaquetteTransport s F) =
      bondTransport s (curlAdjoint s.data.L s.data.m s.data.cutoff s.data.t F) :=
  adjointFor_transport s.data.L s.data.t (bondEquiv s 0) (plaquetteEquiv s) (finestMesh_ne_zero s)
    (bondInner_eq s) (plaquetteInner_eq s) _ _ (plaquetteCurl_bondTransport s) F
end TorusComponents
namespace TorusComponents
open FunctionTransport
theorem pairsUniquely_of_equiv {X Y : Type} (e : X ≃ Y) {R : X → Y → Prop}
    (h : ∀ x y, R x y ↔ e x = y) : PairsUniquely R := by
  refine ⟨fun x => ⟨e x, (h _ _).2 rfl, fun y hy => ((h _ _).1 hy).symm⟩, fun y =>
    ⟨e.symm y, (h _ _).2 (by simp), fun x hx => ?_⟩⟩
  rw [← (h _ _).1 hx]
  simp
theorem agreeAlong_iff {X Y : Type} (e : X ≃ Y) {R : X → Y → Prop} (h : ∀ x y, R x y ↔ e x = y)
    (f : X → ℝ) (f' : Y → ℝ) : AgreeAlong R f f' ↔ f' = transport e f := by
  constructor
  · intro hs
    funext y
    rw [transport_apply]
    exact (hs _ _ ((h _ _).2 (by simp))).symm
  · rintro rfl x y hxy
    rw [← (h _ _).1 hxy, transport_apply_equiv]
theorem mem_range_indicatorMul {ι : Type} (X : Set ι) (f : ι → ℝ) :
    f ∈ LinearMap.range (indicatorMul X) ↔ ∀ i, i ∉ X → f i = 0 := by apply _root_.YangMills.Construction.SeparatedClasses.NestedOneForms.mem_range_indicatorMul <;> assumption
theorem indicatorMul_of_mem {ι : Type} (X : Set ι) {f : ι → ℝ}
    (hf : f ∈ LinearMap.range (indicatorMul X)) : indicatorMul X f = f := by apply _root_.YangMills.Construction.SeparatedClasses.NestedOneForms.indicatorMul_of_mem <;> assumption
structure GaugeFit (s : SequenceData) where
  chain : GeneralTorus.SeparatedChain s.levelUnitData
  gap_le : s.levelUnitData.L ≤ s.levelUnitData.gapCount
  mass_pos : (0 : ℝ) < 1
  chain_set_eq : ∀ n, chain.set n = s.regionOn s.levelUnitData.torusSide n
variable {s : SequenceData} (c : GaugeFit s)
abbrev GaugeFit.setting : GeneralTorus.GaugeSetting :=
  ⟨s.levelUnitData, c.chain, c.gap_le, bondSetChoice s.frame, 1, c.mass_pos⟩
theorem GaugeFit.mem_set_iff (n : ℕ) (x : s.data.Point) :
    torusEquiv s x ∈ c.chain.set n ↔ x ∈ s.Ω n := by
  rw [c.chain_set_eq n]
  constructor
  · rintro ⟨y, hy, h⟩
    rw [toTorus_eq] at h
    exact (torusEquiv s).injective h ▸ hy
  · intro h
    exact ⟨x, h, toTorus_eq s x⟩
theorem memberAt_eq (s : SequenceData) (n : ℕ) : s.params.memberAt s.Ω n = s.Ω n := by
  change (if n ≤ s.data.t then s.Ω n else ∅) = s.Ω n
  split_ifs with h
  · rfl
  · exact (s.Ω_mem.2.2 n (not_le.1 h)).symm
theorem GaugeFit.mem_framedBonds_iff (b : s.data.BareBond) :
    b ∈ framedBonds s.data.cutoff (s.Ω 0) s.frame ↔ bondEquiv s 0 b ∈ c.setting.bondSet := by
  have h1 := c.mem_set_iff 0 (b.1.source : s.data.Point)
  have h2 := c.mem_set_iff 0 (b.1.target : s.data.Point)
  unfold GeneralTorus.GaugeSetting.bondSet
  cases hf : s.frame with
  | interior =>
    change (((b.1.source : s.data.Point) ∈ s.Ω 0) ∧ ((b.1.target : s.data.Point) ∈ s.Ω 0)) ↔
      bondEquiv s 0 b ∈ (match bondSetChoice s.frame with
        | .meeting => c.chain.meetingBonds
        | .interior => c.chain.interiorBonds)
    rw [hf]
    exact (and_congr h1 h2).symm
  | star =>
    change (((b.1.source : s.data.Point) ∈ s.Ω 0) ∨ ((b.1.target : s.data.Point) ∈ s.Ω 0)) ↔
      bondEquiv s 0 b ∈ (match bondSetChoice s.frame with
        | .meeting => c.chain.meetingBonds
        | .interior => c.chain.interiorBonds)
    rw [hf]
    exact (or_congr h1 h2).symm
theorem GaugeFit.mem_bondsMeeting_iff {n : ℕ} (k : ℕ) (d : s.data.PosLatticeBond n) :
    d.1 ∈ (PeriodicLattice.bondsMeeting (s.params.memberAt s.Ω k) :
        Set (PeriodicLattice.Bond _ _ _)) ↔
      (((bondEquiv s n d).1.src : s.levelUnitData.Space) ∈ c.chain.set k ∨
        ((bondEquiv s n d).1.tgt : s.levelUnitData.Space) ∈ c.chain.set k) := by
  rw [memberAt_eq]
  exact (or_congr (c.mem_set_iff k _) (c.mem_set_iff k _)).symm
theorem GaugeFit.mem_layer_iff {n : ℕ} (d : s.data.PosLatticeBond n) :
    d ∈ s.params.layerBondSet s.Ω s.frame n ↔ bondEquiv s n d ∈ c.setting.coarseBondsAt n := by
  cases n with
  | zero =>
    change (d ∈ framedBonds s.data.cutoff (s.Ω 0) s.frame ∧ d.1 ∉ _) ↔
      (bondEquiv s 0 d ∈ c.setting.bondSet ∧
        ((bondEquiv s 0 d).1.src : s.levelUnitData.Space) ∉ c.chain.set 1 ∧
        ((bondEquiv s 0 d).1.tgt : s.levelUnitData.Space) ∉ c.chain.set 1)
    rw [c.mem_framedBonds_iff, c.mem_bondsMeeting_iff, not_or]
  | succ n =>
    change (d.1 ∈ _ ∧ d.1 ∉ _) ↔
      ((((bondEquiv s (n + 1) d).1.src : s.levelUnitData.Space) ∈ c.chain.set (n + 1) ∨
        ((bondEquiv s (n + 1) d).1.tgt : s.levelUnitData.Space) ∈ c.chain.set (n + 1)) ∧
        ((bondEquiv s (n + 1) d).1.src : s.levelUnitData.Space) ∉ c.chain.set (n + 2) ∧
        ((bondEquiv s (n + 1) d).1.tgt : s.levelUnitData.Space) ∉ c.chain.set (n + 2))
    rw [c.mem_bondsMeeting_iff, c.mem_bondsMeeting_iff, not_or]
def GaugeFit.coarseEquiv : ↥(s.params.principalBonds s.Ω s.frame) ≃ c.setting.CoarseBond where
  toFun d := ⟨⟨d.1.1, Nat.lt_succ_of_le d.2.1⟩,
    ⟨bondEquiv s d.1.1 d.1.2, (c.mem_layer_iff _).1 d.2.2⟩⟩
  invFun d := ⟨⟨d.1.1, (bondEquiv s d.1.1).symm d.2.1⟩, Nat.le_of_lt_succ d.1.2,
    (c.mem_layer_iff _).2 (by simp)⟩
  left_inv := by
    rintro ⟨⟨n, d⟩, h⟩
    refine Subtype.ext (Sigma.ext rfl (heq_of_eq ?_))
    simp
  right_inv := by
    rintro ⟨⟨n, hn⟩, ⟨d, h⟩⟩
    refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
    simp
def GaugeFit.formEquiv :
    ↥(oneFormsOn s.data.cutoff (s.Ω 0) s.frame) ≃ₗ[ℝ] ↥c.setting.formSubspace where
  toFun A := ⟨bondTransport s A.1, fun b' hb' => by
    obtain ⟨b, rfl⟩ := (bondEquiv s 0).surjective b'
    rw [bondTransport_apply]
    exact (mem_range_indicatorMul _ _).1 A.2 b fun h => hb' ((c.mem_framedBonds_iff b).1 h)⟩
  invFun A := ⟨(bondTransport s).symm A.1, (mem_range_indicatorMul _ _).2 fun b hb => by
    have : (bondTransport s).symm A.1 b = A.1 (bondEquiv s 0 b) := rfl
    rw [this]
    exact A.2 _ fun h => hb ((c.mem_framedBonds_iff b).2 h)⟩
  map_add' A A' := Subtype.ext (map_add (bondTransport s) A.1 A'.1)
  map_smul' r A := Subtype.ext (map_smul (bondTransport s) r A.1)
  left_inv A := Subtype.ext ((bondTransport s).symm_apply_apply A.1)
  right_inv A := Subtype.ext ((bondTransport s).apply_symm_apply A.1)
theorem GaugeFit.formEquiv_coe (A : ↥(oneFormsOn s.data.cutoff (s.Ω 0) s.frame)) :
    ((c.formEquiv A : ↥c.setting.formSubspace) : s.levelUnitData.BondField) =
      bondTransport s A.1 := rfl
theorem GaugeFit.bondRel_iff (b : s.data.BareBond) (b' : s.levelUnitData.BaseBond) :
    s.oneFormData.BondRel (oneFormDataOfGauge c.setting) (s.toTorus s.levelUnitData.torusSide)
        b b' ↔
      bondEquiv s 0 b = b' := by
  constructor
  · intro h
    have h1 : s.toTorus s.levelUnitData.torusSide (b.1.source : s.data.Point) =
        (b'.1.src : s.levelUnitData.Space) := congrArg Prod.fst h
    have h2 : s.toTorus s.levelUnitData.torusSide (b.1.target : s.data.Point) =
        (b'.1.tgt : s.levelUnitData.Space) := congrArg Prod.snd h
    rw [toTorus_eq] at h1 h2
    exact Subtype.ext (GeneralTorus.LatticeBond.ext (Subtype.ext h1) (Subtype.ext h2))
  · rintro rfl
    refine Prod.ext ?_ ?_
    · exact toTorus_eq s _
    · exact toTorus_eq s _
theorem GaugeFit.expansionRel_iff (d : ↥(s.params.principalBonds s.Ω s.frame))
    (d' : c.setting.CoarseBond) :
    s.oneFormData.RowRel (oneFormDataOfGauge c.setting) (s.toTorus s.levelUnitData.torusSide)
        d d' ↔
      c.coarseEquiv d = d' := by
  obtain ⟨⟨n, e⟩, hd⟩ := d
  obtain ⟨⟨n', hn'⟩, ⟨e', he'⟩⟩ := d'
  constructor
  · intro h
    have h0 : n = n' := congrArg Prod.fst h
    subst h0
    have h1 : s.toTorus s.levelUnitData.torusSide (e.1.source : s.data.Point) =
        (e'.1.src : s.levelUnitData.Space) := congrArg (fun p => p.2.1) h
    have h2 : s.toTorus s.levelUnitData.torusSide (e.1.target : s.data.Point) =
        (e'.1.tgt : s.levelUnitData.Space) := congrArg (fun p => p.2.2) h
    rw [toTorus_eq] at h1 h2
    refine Sigma.ext rfl (heq_of_eq (Subtype.ext (Subtype.ext ?_)))
    exact GeneralTorus.LatticeBond.ext (Subtype.ext h1) (Subtype.ext h2)
  · intro h
    obtain rfl : n = n' := congrArg (fun p : c.setting.CoarseBond => (p.1 : ℕ)) h
    have h3 : bondEquiv s n e = e' := by
      have := h
      simp only [GaugeFit.coarseEquiv, Equiv.coe_fn_mk, Sigma.mk.injEq, heq_eq_eq,
        true_and] at this
      exact congrArg Subtype.val this
    subst h3
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · exact toTorus_eq s _
    · exact toTorus_eq s _
theorem GaugeFit.oneForms_correspond :
    OneFormData.Corresponds s.oneFormData.toOneFormData
      (oneFormDataOfGauge c.setting).toOneFormData (s.toTorus s.levelUnitData.torusSide) where
  bonds := pairsUniquely_of_equiv (bondEquiv s 0) c.bondRel_iff
  space := by
    refine ⟨fun f hf => ⟨(c.formEquiv ⟨f, hf⟩).1, (c.formEquiv ⟨f, hf⟩).2, ?_⟩, fun f' hf' =>
      ⟨(c.formEquiv.symm ⟨f', hf'⟩).1, (c.formEquiv.symm ⟨f', hf'⟩).2, ?_⟩⟩
    · exact (agreeAlong_iff _ c.bondRel_iff _ _).2 rfl
    · refine (agreeAlong_iff _ c.bondRel_iff _ _).2 ?_
      exact congrArg Subtype.val (c.formEquiv.apply_symm_apply ⟨f', hf'⟩).symm
  inner := by
    intro f _ g _ f' _ g' _ hf hg
    rw [(agreeAlong_iff _ c.bondRel_iff _ _).1 hf, (agreeAlong_iff _ c.bondRel_iff _ _).1 hg]
    change latticeInner s.data.L s.data.t f g = s.levelUnitData.bondInner _ _
    rw [bondInner_eq]
    simp only [latticeInner]
    congr 1
    exact (finsum_transport_mul (bondEquiv s 0) f g).symm
end TorusComponents
namespace TorusComponents
open FunctionTransport
theorem supNormVec_smul {k : ℝ} (hk : 0 < k) (v : Fin 4 → ℝ) :
    supNormVec (k • v) = k * supNormVec v := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun μ _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hk]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ)) hk.le
  · rw [← le_div_iff₀' hk]
    refine Finset.sup'_le _ _ fun μ _ => ?_
    rw [le_div_iff₀' hk]
    have h : |(k • v) μ| ≤ supNormVec (k • v) :=
      Finset.le_sup' (fun μ => |(k • v) μ|) (Finset.mem_univ μ)
    rwa [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hk] at h
theorem torusEquiv_torusProj (s : SequenceData) (v : Fin 4 → ℝ) :
    torusEquiv s (torusProj (PeriodicLattice.torusSide s.data.L s.data.m) v) =
      torusProj s.levelUnitData.torusSide (s.unitScale • v) := torusEquiv_coe s v
theorem torusSupNorm_torusEquiv (s : SequenceData) (x : s.data.Point) :
    torusSupNorm (torusEquiv s x) = s.unitScale * torusSupNorm x := by
  have hk := unitScale_pos s
  have e : supNormVec '' (torusProj s.levelUnitData.torusSide ⁻¹' {torusEquiv s x}) =
      s.unitScale • (supNormVec '' (torusProj (PeriodicLattice.torusSide s.data.L s.data.m) ⁻¹' {x})) := by
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨_, ⟨s.unitScale⁻¹ • w, ?_, rfl⟩, ?_⟩
      · have hw' : torusProj s.levelUnitData.torusSide w = torusEquiv s x := hw
        change torusProj _ _ = x
        apply (torusEquiv s).injective
        rw [torusEquiv_torusProj, smul_smul, mul_inv_cancel₀ hk.ne', one_smul, hw']
      · simp only [smul_eq_mul]
        rw [← supNormVec_smul hk, smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨s.unitScale • v, ?_, supNormVec_smul hk v⟩
      rw [mem_preimage, mem_singleton_iff] at hv ⊢
      rw [← torusEquiv_torusProj, hv]
  rw [torusSupNorm, e, Real.sInf_smul_of_nonneg hk.le, smul_eq_mul]
  rfl
theorem mem_fineBlock_iff (s : SequenceData) {n : ℕ} (y : s.data.LatticeSite n)
    (x : s.data.BareSite) :
    (x : s.data.Point) ∈ SeparatedSequences.BaseParameters.fineBlock (D := s.params) y ↔
      torusEquiv s x ∈ s.levelUnitData.baseBlock n (torusEquiv s y) := by
  have key : torusSupNorm (torusEquiv s x - torusEquiv s y) ≤ s.levelUnitData.levelSpacing n / 2 ↔
      torusSupNorm ((x : s.data.Point) - (y : s.data.Point)) ≤
        PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) / 2 := by
    rw [← map_sub, torusSupNorm_torusEquiv, levelSpacing_eq, mul_div_assoc]
    exact mul_le_mul_iff_right₀ (unitScale_pos s)
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨key.2 h1, (torusEquiv_mem_lattice s 0 _).1 x.2⟩
  · rintro ⟨h1, -⟩
    exact ⟨key.1 h1, x.2⟩
theorem lineSum_forwardFlow {L m K : ℕ} (A : OneForms L m K) (μ : Fin 4) (N : ℕ)
    (x : BareSite L m K) :
    lineSum A (PeriodicLattice.forwardAxisPath x μ N) =
      ∑ i ∈ Finset.range N,
        A (bondFrom (x + i • PeriodicLattice.unitStep L m (PeriodicLattice.levelDepth K 0) μ) μ) := by
  induction N generalizing x with
  | zero => simp [PeriodicLattice.forwardAxisPath, lineSum]
  | succ N ih =>
    have hv : orientedValue A (PeriodicLattice.Bond.forwardFrom x μ) = A (bondFrom x μ) :=
      dif_pos ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
    have ih' := ih (x + PeriodicLattice.unitStep L m (PeriodicLattice.levelDepth K 0) μ)
    simp only [lineSum] at ih' ⊢
    simp only [PeriodicLattice.forwardAxisPath, List.map_cons, List.sum_cons]
    rw [ih', hv, Finset.sum_range_succ', add_comm]
    simp only [zero_smul, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [succ_nsmul', add_assoc]
theorem blockBondMean_bondTransport (s : SequenceData) {n : ℕ} (hn : n ≤ s.data.cutoff)
    (A : s.data.BondFn) (d : s.data.PosLatticeBond n) :
    s.levelUnitData.blockBondMean n (bondTransport s A) (bondEquiv s n d) =
      s.params.blockAverageOne n A d := by
  classical
  have hdir := posBondDir_bondEquiv s hn d
  change (((s.levelUnitData.blockSize n : ℕ) : ℝ) ^ 5)⁻¹ *
      ∑ᶠ x ∈ GeneralTorus.sitesIn (S := s.levelUnitData.torusSide) (s.levelUnitData.levelSpacing 0)
          (s.levelUnitData.baseBlock n (torusEquiv s d.1.source)),
        ∑ i ∈ Finset.range (s.levelUnitData.blockSize n),
          s.levelUnitData.formComponent (GeneralTorus.ScaleData.posBondDir (bondEquiv s n d))
            (bondTransport s A)
            (x + i • GeneralTorus.unitStep s.levelUnitData.torusSide (s.levelUnitData.levelSpacing 0)
              (GeneralTorus.ScaleData.posBondDir (bondEquiv s n d))) =
    ((s.data.L : ℝ) ^ (n * (4 + 1)))⁻¹ *
      ∑ᶠ x : {x : s.data.BareSite //
          (x : s.data.Point) ∈ SeparatedSequences.BaseParameters.fineBlock (D := s.params) d.1.source},
        lineSum A (PeriodicLattice.forwardAxisPath x.1 (SeparatedSequences.BaseParameters.bondAxis d)
          (s.data.L ^ n))
  rw [hdir]
  have hw : (((s.levelUnitData.blockSize n : ℕ) : ℝ) ^ 5) = (s.data.L : ℝ) ^ (n * (4 + 1)) := by
    change (((s.data.L ^ n : ℕ) : ℝ) ^ 5) = _
    push_cast
    rw [pow_mul]
  rw [hw]
  congr 1
  rw [← finsum_set_coe_eq_finsum_mem]
  let eq : {x : s.data.BareSite //
      (x : s.data.Point) ∈ SeparatedSequences.BaseParameters.fineBlock (D := s.params) d.1.source} ≃
      ↥(GeneralTorus.sitesIn (S := s.levelUnitData.torusSide) (s.levelUnitData.levelSpacing 0)
        (s.levelUnitData.baseBlock n (torusEquiv s d.1.source))) :=
    (siteEquiv s 0).toEquiv.subtypeEquiv fun x => mem_fineBlock_iff s d.1.source x
  rw [← finsum_comp_equiv eq]
  refine finsum_congr fun x => ?_
  rw [lineSum_forwardFlow]
  refine Finset.sum_congr rfl fun i _ => ?_
  change s.levelUnitData.formComponent _ (bondTransport s A) (siteEquiv s 0 x.1 + i • _) = _
  rw [formComponent_bondTransport, ← siteEquiv_unitStep, ← map_nsmul, ← map_add, siteTransport_apply]
  rfl
theorem levelSpacing_eq_meshRatio (s : SequenceData) (n : ℕ) :
    s.levelUnitData.levelSpacing n = s.params.levelMeshRatio n := by
  have hL := (blockFactor_pos s).ne'
  change (s.data.L : ℝ) ^ n * (s.data.L : ℝ) ^ (-(s.data.t : ℤ)) =
    (s.data.L : ℝ) ^ ((n : ℤ) - (s.data.t : ℤ))
  rw [← zpow_natCast, ← zpow_add₀ hL, sub_eq_add_neg]
theorem finsum_sigma_fin_eq_sum {N : ℕ} {β : Fin N → Type} [∀ i, Finite (β i)]
    (F : (Σ i, β i) → ℝ) : ∑ᶠ p, F p = ∑ i, ∑ᶠ b, F ⟨i, b⟩ := by
  classical
  have := fun i => Fintype.ofFinite (β i)
  rw [finsum_eq_sum_of_fintype, Fintype.sum_sigma]
  simp only [finsum_eq_sum_of_fintype]
variable {s : SequenceData} (c : GaugeFit s)
instance GaugeFit.finite_coarseBondsAt (n : ℕ) : Finite ↥(c.setting.coarseBondsAt n) :=
  have := finite_posBond s n
  Subtype.finite
instance GaugeFit.finite_principalBonds : Finite ↥(s.params.principalBonds s.Ω s.frame) :=
  SeparatedSequences.BaseParameters.instFinitePrincipalBonds s.params s.Ω s.frame
instance GaugeFit.finite_coarseBond : Finite c.setting.CoarseBond :=
  Finite.of_equiv _ c.coarseEquiv
theorem GaugeFit.coarseInner_transport (b b' : s.params.CoarseOneForms s.Ω s.frame) :
    c.setting.coarseInner (transport c.coarseEquiv b) (transport c.coarseEquiv b') =
      s.params.coarseOneInner s.Ω s.frame b b' := by
  let lv : ∀ n, ↥(s.params.layerBondSet s.Ω s.frame n) ≃ ↥(c.setting.coarseBondsAt n) := fun n =>
    (bondEquiv s n).subtypeEquiv fun d => c.mem_layer_iff d
  change ∑ᶠ d : c.setting.CoarseBond, GeneralTorus.GaugeSetting.coarseSpacing d ^ 4 *
    (transport c.coarseEquiv b d * transport c.coarseEquiv b' d) = _
  rw [finsum_sigma_fin_eq_sum]
  change _ = ∑ n ∈ Finset.range (s.data.t + 1), s.params.levelMeshRatio n ^ 4 *
    ∑ᶠ d : ↥(s.params.layerBondSet s.Ω s.frame n),
      SeparatedSequences.BaseParameters.principalBondValue b ⟨n, d.1⟩ *
        SeparatedSequences.BaseParameters.principalBondValue b' ⟨n, d.1⟩
  rw [← Fin.sum_univ_eq_sum_range (fun n => s.params.levelMeshRatio n ^ 4 *
    ∑ᶠ d : ↥(s.params.layerBondSet s.Ω s.frame n),
      SeparatedSequences.BaseParameters.principalBondValue b ⟨n, d.1⟩ *
        SeparatedSequences.BaseParameters.principalBondValue b' ⟨n, d.1⟩)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← finsum_comp_equiv (lv i), ← SeparatedSequences.BaseParameters.finsum_const_mul_finite]
  refine finsum_congr fun d => ?_
  have hm : (⟨(i : ℕ), d.1⟩ : Σ n : ℕ, s.params.LevelBond n) ∈
      s.params.principalBonds s.Ω s.frame := ⟨Nat.le_of_lt_succ i.2, d.2⟩
  have hr : (⟨i, lv i d⟩ : c.setting.CoarseBond) = c.coarseEquiv ⟨_, hm⟩ := rfl
  have hv : ∀ f : s.params.CoarseOneForms s.Ω s.frame,
      SeparatedSequences.BaseParameters.principalBondValue f ⟨(i : ℕ), d.1⟩ = f ⟨_, hm⟩ :=
    fun f => dif_pos hm
  rw [hr, transport_apply_equiv, transport_apply_equiv, hv, hv, ← levelSpacing_eq_meshRatio]
  rfl
theorem GaugeFit.coarseInner_comm (f g : c.setting.CoarseField) :
    c.setting.coarseInner f g = c.setting.coarseInner g f :=
  finsum_congr fun d => by ring
theorem GaugeFit.meanOp_formEquiv (A : ↥(oneFormsOn s.data.cutoff (s.Ω 0) s.frame)) :
    c.setting.meanOp (c.formEquiv A) =
      transport c.coarseEquiv (s.params.averageOne s.Ω s.frame A) := by
  funext d'
  obtain ⟨⟨⟨n, d⟩, hn, hd⟩, rfl⟩ := c.coarseEquiv.surjective d'
  rw [transport_apply_equiv]
  exact blockBondMean_bondTransport s (hn.trans s.data.t_le_cutoff) A.1 d
theorem GaugeFit.formProj_coe (Y : s.levelUnitData.BondField) :
    ((c.setting.formProj Y : ↥c.setting.formSubspace) : s.levelUnitData.BondField) =
      c.setting.bondSet.indicator Y :=
  orthProjFor_apply (pow_ne_zero 4 (levelSpacing_pos s 0).ne') (fun _ _ => rfl)
    c.setting.formSubspace c.setting.bondSet (fun _ => Iff.rfl) Y
theorem GaugeFit.siteProj_coe (Y : s.levelUnitData.SiteField) :
    ((c.chain.siteProj Y : ↥c.chain.dirichletSites) : s.levelUnitData.SiteField) =
      {x : s.levelUnitData.BaseSite | (x : s.levelUnitData.Space) ∈ c.chain.set 0}.indicator Y :=
  orthProjFor_apply (pow_ne_zero 4 (levelSpacing_pos s 0).ne') (fun _ _ => rfl)
    c.chain.dirichletSites
    {x : s.levelUnitData.BaseSite | (x : s.levelUnitData.Space) ∈ c.chain.set 0}
    (fun _ => Iff.rfl) Y
theorem GaugeFit.meanOpAdjoint_spec :
    GeneralTorus.IsAdjointFor c.setting.formInner c.setting.coarseInner c.setting.meanOp
      c.setting.meanOpAdjoint := by
  have hex : ∃ T, GeneralTorus.IsAdjointFor c.setting.formInner c.setting.coarseInner
      c.setting.meanOp T := by
    obtain ⟨T₀, hT₀⟩ := exists_weighted_adjoint
      (fun d : c.setting.CoarseBond => GeneralTorus.GaugeSetting.coarseSpacing d ^ 4)
      (c.setting.meanOp ∘ₗ c.setting.formProj)
    refine ⟨c.setting.formProj ∘ₗ ((s.levelUnitData.levelSpacing 0 ^ 4)⁻¹ • T₀), fun v u => ?_⟩
    have hv : c.setting.formProj (v : s.levelUnitData.BondField) = v := by
      refine Subtype.ext ?_
      rw [c.formProj_coe]
      funext b
      by_cases hb : b ∈ c.setting.bondSet
      · exact indicator_of_mem hb _
      · rw [indicator_of_notMem hb, v.2 b hb]
    have h1 := hT₀ v u
    simp only [LinearMap.comp_apply, hv] at h1
    change ∑ᶠ d : c.setting.CoarseBond, GeneralTorus.GaugeSetting.coarseSpacing d ^ 4 *
        (c.setting.meanOp v d * u d) =
      s.levelUnitData.levelSpacing 0 ^ 4 * ∑ᶠ b, (v : s.levelUnitData.BondField) b *
        ((c.setting.formProj ((s.levelUnitData.levelSpacing 0 ^ 4)⁻¹ • T₀ u) :
          ↥c.setting.formSubspace) : s.levelUnitData.BondField) b
    rw [h1, c.formProj_coe, ← SeparatedSequences.BaseParameters.finsum_const_mul_finite]
    refine finsum_congr fun b => ?_
    by_cases hb : b ∈ c.setting.bondSet
    · rw [indicator_of_mem hb]
      simp only [Pi.smul_apply, smul_eq_mul]
      have h0 := (levelSpacing_pos s 0).ne'
      field_simp
    · rw [v.2 b hb]
      simp
  exact Classical.epsilon_spec hex
theorem GaugeFit.formInner_formEquiv (A A' : ↥(oneFormsOn s.data.cutoff (s.Ω 0) s.frame)) :
    c.setting.formInner (c.formEquiv A) (c.formEquiv A') =
      s.params.restrictedOneInner s.Ω s.frame A A' := by
  change s.levelUnitData.bondInner (bondTransport s A.1) (bondTransport s A'.1) =
    latticeInner s.data.L s.data.t A.1 A'.1
  rw [bondInner_eq]
  simp only [latticeInner]
  congr 1
  exact finsum_transport_mul (bondEquiv s 0) A.1 A'.1
theorem GaugeFit.averageOneAdjoint_eq (b : s.params.CoarseOneForms s.Ω s.frame) :
    s.params.averageOneAdjoint s.Ω s.frame b =
      c.formEquiv.symm (c.setting.meanOpAdjoint (transport c.coarseEquiv b)) := by
  let T : s.params.CoarseOneForms s.Ω s.frame →ₗ[ℝ] ↥(oneFormsOn s.data.cutoff (s.Ω 0) s.frame) :=
    c.formEquiv.symm.toLinearMap ∘ₗ c.setting.meanOpAdjoint ∘ₗ (transport c.coarseEquiv).toLinearMap
  have hT : FiniteDimReal.IsAdjointFor (s.params.restrictedOneInner s.Ω s.frame)
      (s.params.coarseOneInner s.Ω s.frame) (s.params.averageOne s.Ω s.frame) T := by
    intro f g
    rw [← c.coarseInner_transport, ← c.meanOp_formEquiv, c.coarseInner_comm, c.meanOpAdjoint_spec,
      show T g = c.formEquiv.symm (c.setting.meanOpAdjoint (transport c.coarseEquiv g)) from rfl]
    have hc : ∀ X Y : ↥(oneFormsOn s.data.cutoff (s.Ω 0) s.frame),
        s.params.restrictedOneInner s.Ω s.frame X Y =
          s.params.restrictedOneInner s.Ω s.frame Y X := fun X Y => by
      change latticeInner s.data.L s.data.t X.1 Y.1 = latticeInner s.data.L s.data.t Y.1 X.1
      simp only [latticeInner]
      congr 1
      exact finsum_congr fun i => mul_comm _ _
    rw [hc, ← c.formInner_formEquiv, LinearEquiv.apply_symm_apply]
  have spec : FiniteDimReal.IsAdjointFor (s.params.restrictedOneInner s.Ω s.frame)
      (s.params.coarseOneInner s.Ω s.frame) (s.params.averageOne s.Ω s.frame)
      (s.params.averageOneAdjoint s.Ω s.frame) :=
    Classical.epsilon_spec (p := FiniteDimReal.IsAdjointFor
      (s.params.restrictedOneInner s.Ω s.frame) (s.params.coarseOneInner s.Ω s.frame)
      (s.params.averageOne s.Ω s.frame)) ⟨T, hT⟩
  refine Subtype.ext ?_
  refine eq_of_forall_weighted_sum (pow_ne_zero 4 (finestMesh_ne_zero s))
    (framedBonds s.data.cutoff (s.Ω 0) s.frame)
    ((mem_range_indicatorMul _ _).1 (Subtype.property _))
    ((mem_range_indicatorMul _ _).1 (Subtype.property _)) fun f hf => ?_
  have hf' : f ∈ oneFormsOn s.data.cutoff (s.Ω 0) s.frame := (mem_range_indicatorMul _ _).2 hf
  have h1 := spec ⟨f, hf'⟩ b
  have h2 := hT ⟨f, hf'⟩ b
  rw [h2] at h1
  have hcomm : ∀ g : ↥(oneFormsOn s.data.cutoff (s.Ω 0) s.frame),
      s.params.restrictedOneInner s.Ω s.frame g ⟨f, hf'⟩ =
        PeriodicLattice.finestMeshInLevelUnits s.data.L s.data.t ^ 4 * ∑ᶠ i, f i * g.1 i :=
    fun g => by
    change PeriodicLattice.finestMeshInLevelUnits s.data.L s.data.t ^ 4 * ∑ᶠ i, g.1 i * f i = _
    congr 1
    exact finsum_congr fun i => mul_comm _ _
  rw [hcomm, hcomm] at h1
  exact h1.symm
theorem GaugeFit.massMul_transport (b : s.params.CoarseOneForms s.Ω s.frame) :
    c.setting.massMul (transport c.coarseEquiv b) =
      transport c.coarseEquiv (s.params.weightMulOne s.Ω s.frame b) := by
  funext d'
  obtain ⟨d, rfl⟩ := c.coarseEquiv.surjective d'
  rw [transport_apply_equiv]
  change (1 : ℝ) * (s.levelUnitData.levelSpacing d.1.1 ^ 2)⁻¹ *
      transport c.coarseEquiv b (c.coarseEquiv d) =
    (1 : ℝ) * (s.params.levelMeshRatio d.1.1 ^ 2)⁻¹ * b d
  rw [transport_apply_equiv, levelSpacing_eq_meshRatio]
theorem GaugeFit.massPart_formEquiv (A : ↥(oneFormsOn s.data.cutoff (s.Ω 0) s.frame)) :
    c.setting.massPart (c.formEquiv A) =
      c.formEquiv (s.params.weightedAverageOne s.Ω s.frame A) := by
  change c.setting.meanOpAdjoint (c.setting.massMul (c.setting.meanOp (c.formEquiv A))) =
    c.formEquiv (s.params.averageOneAdjoint s.Ω s.frame
      (s.params.weightMulOne s.Ω s.frame (s.params.averageOne s.Ω s.frame A)))
  rw [c.meanOp_formEquiv, c.massMul_transport, c.averageOneAdjoint_eq, LinearEquiv.apply_symm_apply]
end TorusComponents
namespace TorusComponents
variable {s : SequenceData} (c : GaugeFit s)
open FunctionTransport
theorem GaugeFit.indicator_bondTransport (Z : s.data.BondFn) :
    c.setting.bondSet.indicator (bondTransport s Z) =
      bondTransport s (indicatorMul (framedBonds s.data.cutoff (s.Ω 0) s.frame) Z) := by
  funext b'
  obtain ⟨b, rfl⟩ := (bondEquiv s 0).surjective b'
  rw [bondTransport_apply]
  change _ = (framedBonds s.data.cutoff (s.Ω 0) s.frame).indicator Z b
  by_cases hb : b ∈ framedBonds s.data.cutoff (s.Ω 0) s.frame
  · rw [indicator_of_mem ((c.mem_framedBonds_iff b).1 hb), indicator_of_mem hb, bondTransport_apply]
  · rw [indicator_of_notMem (fun h => hb ((c.mem_framedBonds_iff b).2 h)), indicator_of_notMem hb]
theorem GaugeFit.indicator_siteTransport (Z : s.data.SiteFn) :
    {x : s.levelUnitData.BaseSite | (x : s.levelUnitData.Space) ∈ c.chain.set 0}.indicator
        (siteTransport s Z) =
      siteTransport s (indicatorMul (sitesOfRegion s.data.cutoff (s.Ω 0)) Z) := by
  funext x'
  obtain ⟨x, rfl⟩ := (siteEquiv s 0).surjective x'
  rw [siteTransport_apply]
  change _ = (sitesOfRegion s.data.cutoff (s.Ω 0)).indicator Z x
  by_cases hx : x ∈ sitesOfRegion s.data.cutoff (s.Ω 0)
  · rw [indicator_of_mem (show siteEquiv s 0 x ∈ {x : s.levelUnitData.BaseSite |
      (x : s.levelUnitData.Space) ∈ c.chain.set 0} from (c.mem_set_iff 0 _).2 hx),
      indicator_of_mem hx, siteTransport_apply]
  · rw [indicator_of_notMem (show siteEquiv s 0 x ∉ {x : s.levelUnitData.BaseSite |
      (x : s.levelUnitData.Space) ∈ c.chain.set 0} from fun h => hx ((c.mem_set_iff 0 _).1 h)),
      indicator_of_notMem hx]
theorem extendByZero_of_mem {X Y : Type} {E : Submodule ℝ (X → ℝ)} (T : ↥E → Y → ℝ) {f : X → ℝ}
    (h : f ∈ E) : _root_.YangMills.Construction.SeparatedClasses.SingleSequence.extendByZero E T f = T ⟨f, h⟩ := dif_pos h
theorem GaugeFit.gaugeSiteRel_iff (x : s.data.BareSite) (x' : s.levelUnitData.BaseSite) :
    s.GaugeSiteRel c.setting x x' ↔ (siteEquiv s 0).toEquiv x = x' := by
  constructor
  · intro h
    refine Subtype.ext ?_
    have h' : s.toTorus s.levelUnitData.torusSide (x : s.data.Point) =
        (x' : s.levelUnitData.Space) := h
    rw [toTorus_eq] at h'
    exact h'
  · rintro rfl
    exact toTorus_eq s _
theorem GaugeFit.gaugeProj_transport (hP : s.GaugeProjection c.setting)
    (f : ↥(zeroFormsOn s.data.cutoff (s.Ω 0))) (f' : ↥c.chain.dirichletSites)
    (hf : (f' : s.levelUnitData.SiteField) = siteTransport s f.1) :
    ((c.chain.lapImageProj f' : ↥c.chain.dirichletSites) : s.levelUnitData.SiteField) =
      siteTransport s (s.params.gaugeRangeProjection s.Ω f).1 := by
  have h1 : AgreeAlong (s.GaugeSiteRel c.setting) f.1 f'.1 :=
    (agreeAlong_iff (siteEquiv s 0).toEquiv c.gaugeSiteRel_iff _ _).2 hf
  have h2 := hP.range f.1 f.2 f'.1 f'.2 h1
  rw [agreeAlong_iff (siteEquiv s 0).toEquiv c.gaugeSiteRel_iff] at h2
  have h3 : s.rangeProj f.1 = (s.params.gaugeRangeProjection s.Ω f).1 :=
    extendByZero_of_mem (fun g => (s.params.gaugeRangeProjection s.Ω g).1) f.2
  rw [h3, extendByZero_of_mem (fun g => (c.chain.lapImageProj g).1) f'.2] at h2
  exact h2
theorem GaugeFit.gaugeLap_formEquiv (hP : s.GaugeProjection c.setting)
    (A : ↥(oneFormsOn s.data.cutoff (s.Ω 0) s.frame)) :
    c.setting.gaugeLap (c.formEquiv A) = c.formEquiv (s.params.massiveOneOperator s.Ω s.frame A) := by
  have hχA : indicatorMul (framedBonds s.data.cutoff (s.Ω 0) s.frame) A.1 = A.1 :=
    indicatorMul_of_mem _ A.2
  let f : ↥(zeroFormsOn s.data.cutoff (s.Ω 0)) :=
    dirichletGradAdjoint s.data.cutoff s.data.t (s.Ω 0) s.frame A
  let f' : ↥c.chain.dirichletSites :=
    c.chain.siteProj (s.levelUnitData.gradAdjoint (bondTransport s A.1))
  have hf' : (f' : s.levelUnitData.SiteField) = siteTransport s f.1 := by
    change ((c.chain.siteProj _ : ↥c.chain.dirichletSites) : s.levelUnitData.SiteField) = _
    rw [c.siteProj_coe, gradAdjoint_bondTransport, c.indicator_siteTransport]
    rfl
  have hR := c.gaugeProj_transport hP f f' hf'
  have hcs : (dirichletCurlCurl s.data.cutoff s.data.t (s.Ω 0) s.frame A).1 =
      indicatorMul (framedBonds s.data.cutoff (s.Ω 0) s.frame)
        (curlAdjoint s.data.L s.data.m s.data.cutoff s.data.t (curl s.data.t A.1)) := by
    change indicatorMul (framedBonds s.data.cutoff (s.Ω 0) s.frame)
      (curlCurl s.data.L s.data.m s.data.cutoff s.data.t
        (indicatorMul (framedBonds s.data.cutoff (s.Ω 0) s.frame) A.1)) = _
    rw [hχA]
    rfl
  have hgf : (s.params.gaugeFixingTerm s.Ω s.frame A).1 =
      indicatorMul (framedBonds s.data.cutoff (s.Ω 0) s.frame)
        (grad s.data.t (s.params.gaugeRangeProjection s.Ω f).1) := rfl
  refine Subtype.ext ?_
  change ((c.setting.formProj (s.levelUnitData.plaquetteCurlAdjoint
        (s.levelUnitData.plaquetteCurl (bondTransport s A.1)) +
      s.levelUnitData.grad
        ((c.chain.lapImageProj f' : ↥c.chain.dirichletSites) : s.levelUnitData.SiteField)) :
        ↥c.setting.formSubspace) : s.levelUnitData.BondField) +
      ((c.setting.massPart (c.formEquiv A) : ↥c.setting.formSubspace) :
        s.levelUnitData.BondField) =
    bondTransport s ((dirichletCurlCurl s.data.cutoff s.data.t (s.Ω 0) s.frame A).1 +
      (s.params.gaugeFixingTerm s.Ω s.frame A).1 +
      (s.params.weightedAverageOne s.Ω s.frame A).1)
  rw [c.massPart_formEquiv, c.formEquiv_coe, c.formProj_coe, plaquetteCurl_bondTransport,
    plaquetteCurlAdjoint_plaquetteTransport, hR, grad_siteTransport, ← map_add,
    c.indicator_bondTransport, hcs, hgf, map_add, map_add (bondTransport s) (_ + _), map_add]
theorem GaugeFit.corresponds (hP : s.GaugeProjection c.setting) :
    s.oneFormData.Corresponds (oneFormDataOfGauge c.setting)
      (s.toTorus s.levelUnitData.torusSide) where
  forms := c.oneForms_correspond
  standingConstraints := pairsUniquely_of_equiv c.coarseEquiv c.expansionRel_iff
  avg := by
    intro f hf f' hf' hs
    obtain rfl := (agreeAlong_iff _ c.bondRel_iff _ _).1 hs
    refine (agreeAlong_iff _ c.expansionRel_iff _ _).2 ?_
    change _root_.YangMills.Construction.SeparatedClasses.SingleSequence.extendByZero c.setting.formSubspace (fun A => c.setting.meanOp A) _ =
      transport c.coarseEquiv
        (extendByZero (oneFormsOn s.data.cutoff (s.Ω 0) s.frame)
          (fun A => s.params.averageOne s.Ω s.frame A) f)
    rw [extendByZero_of_mem _ hf', extendByZero_of_mem _ hf]
    exact c.meanOp_formEquiv ⟨f, hf⟩
  op := by
    intro f hf f' hf' hs
    obtain rfl := (agreeAlong_iff _ c.bondRel_iff _ _).1 hs
    refine (agreeAlong_iff _ c.bondRel_iff _ _).2 ?_
    change _root_.YangMills.Construction.SeparatedClasses.SingleSequence.extendByZero c.setting.formSubspace (fun A => (c.setting.gaugeLap A).1) _ =
      bondTransport s
        (extendByZero (oneFormsOn s.data.cutoff (s.Ω 0) s.frame)
          (fun A => (s.params.massiveOneOperator s.Ω s.frame A).1) f)
    rw [extendByZero_of_mem _ hf', extendByZero_of_mem _ hf]
    exact congrArg Subtype.val (c.gaugeLap_formEquiv hP ⟨f, hf⟩)
  inv := by
    intro f hf f' hf' hs
    obtain rfl := (agreeAlong_iff _ c.bondRel_iff _ _).1 hs
    refine (agreeAlong_iff _ c.bondRel_iff _ _).2 ?_
    change _root_.YangMills.Construction.SeparatedClasses.SingleSequence.extendByZero c.setting.formSubspace (fun A => (c.setting.greenOp A).1) _ =
      bondTransport s
        (extendByZero (oneFormsOn s.data.cutoff (s.Ω 0) s.frame)
          (fun A => (s.params.oneGreen s.Ω s.frame A).1) f)
    rw [extendByZero_of_mem _ hf', extendByZero_of_mem _ hf]
    exact congrArg Subtype.val (ring_inverse_conj c.formEquiv (c.gaugeLap_formEquiv hP) ⟨f, hf⟩)
end TorusComponents
end YangMills.Construction.SeparatedClasses.GaugeOneFormsProof
