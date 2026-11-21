import YangMills.Construction.Lattice.MapsInducedOnTheTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TorusDescent
open InfiniteLattice (AmbientSpace)
open BoxTorus (IsLiftOf hyperplane slab projection translate basisVector periods)
variable {L : ℕ} {κ : ℤ}
theorem projection_eq_iff {ℓ : Fin 4 → ℝ} (x y : AmbientSpace) :
    projection ℓ x = projection ℓ y ↔ ∀ μ, ∃ k : ℤ, x μ = y μ + k * ℓ μ := by
  rw [← sub_eq_zero, ← map_sub, ← AddMonoidHom.mem_ker, BoxTorus.projection_ker]
  simp only [periods, AddSubgroup.mem_pi, mem_univ, forall_const,
    AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul, Pi.sub_apply]
  refine forall_congr' fun μ => exists_congr fun k => ?_
  constructor <;> intro h <;> linarith
theorem continuous_projection (ℓ : Fin 4 → ℝ) : Continuous (projection ℓ) :=
  continuous_coinduced_rng
theorem isOpenMap_projection (ℓ : Fin 4 → ℝ) : IsOpenMap (projection ℓ) := by
  intro U hU
  rw [BoxTorus.isOpen_iff_preimage]
  have h : projection ℓ ⁻¹' (projection ℓ '' U) =
      ⋃ p : (projection ℓ).ker, (fun x : AmbientSpace => x + (p : AmbientSpace)) ⁻¹' U := by
    ext x
    simp only [mem_preimage, mem_image, mem_iUnion]
    constructor
    · rintro ⟨u, hu, h⟩
      refine ⟨⟨u - x, ?_⟩, by simpa using hu⟩
      rw [AddMonoidHom.mem_ker, map_sub, h, sub_self]
    · rintro ⟨⟨p, hp⟩, h⟩
      exact ⟨x + p, h, by rw [map_add, AddMonoidHom.mem_ker.mp hp, add_zero]⟩
  rw [h]
  exact isOpen_iUnion fun p => hU.preimage (continuous_id.add continuous_const)
theorem continuous_of_comp_projection {ℓ : Fin 4 → ℝ} {f : BoxTorus.Space ℓ → BoxTorus.Space ℓ}
    (h : Continuous (f ∘ projection ℓ)) : Continuous f := by
  rw [continuous_def]
  intro s hs
  rw [BoxTorus.isOpen_iff_preimage]
  exact hs.preimage h
def diagMap (r w x : AmbientSpace) : AmbientSpace := fun μ => r μ * x μ + w μ
def IsSignVector (r : AmbientSpace) : Prop := ∀ μ, r μ = 1 ∨ r μ = -1
theorem IsSignVector.mul_self {r : AmbientSpace} (hr : IsSignVector r) (μ : Fin 4) :
    r μ * r μ = 1 := by
  rcases hr μ with h | h <;> simp [h]
theorem signAffine_diagonal (r w : AmbientSpace) :
    signAffine (Matrix.diagonal r) w = diagMap r w := by
  funext x μ
  simp [signAffine, diagMap, Matrix.mulVec_diagonal]
theorem mulVec_diagonal_eq_diagMap (r x : AmbientSpace) :
    (Matrix.diagonal r).mulVec x = diagMap r 0 x := by
  funext μ
  simp [diagMap, Matrix.mulVec_diagonal]
theorem mem_signAffineGroup_iff {g : AmbientSpace → AmbientSpace} :
    g ∈ signAffineGroup ↔ ∃ r w, IsSignVector r ∧ g = diagMap r w := by
  constructor
  · rintro ⟨R, w, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, w, hr, signAffine_diagonal r w⟩
  · rintro ⟨r, w, hr, rfl⟩
    exact ⟨Matrix.diagonal r, w, ⟨r, hr, rfl⟩, (signAffine_diagonal r w).symm⟩
theorem diagMap_mem {r : AmbientSpace} (hr : IsSignVector r) (w : AmbientSpace) :
    diagMap r w ∈ signAffineGroup :=
  mem_signAffineGroup_iff.2 ⟨r, w, hr, rfl⟩
theorem id_mem_signAffineGroup : (id : AmbientSpace → AmbientSpace) ∈ signAffineGroup := by
  refine mem_signAffineGroup_iff.2 ⟨fun _ => 1, 0, fun _ => Or.inl rfl, ?_⟩
  funext x μ
  simp [diagMap]
theorem comp_mem_signAffineGroup {g h : AmbientSpace → AmbientSpace} (hg : g ∈ signAffineGroup)
    (hh : h ∈ signAffineGroup) : g ∘ h ∈ signAffineGroup := by
  obtain ⟨r, w, hr, rfl⟩ := mem_signAffineGroup_iff.1 hg
  obtain ⟨r', w', hr', rfl⟩ := mem_signAffineGroup_iff.1 hh
  refine mem_signAffineGroup_iff.2 ⟨fun μ => r μ * r' μ, fun μ => r μ * w' μ + w μ, ?_, ?_⟩
  · intro μ
    rcases hr μ with h | h <;> rcases hr' μ with h' | h' <;> simp [h, h']
  · funext x μ
    simp only [diagMap, Function.comp]
    ring
theorem exists_inverse_mem {g : AmbientSpace → AmbientSpace} (hg : g ∈ signAffineGroup) :
    ∃ g' ∈ signAffineGroup, g ∘ g' = id ∧ g' ∘ g = id := by
  obtain ⟨r, w, hr, rfl⟩ := mem_signAffineGroup_iff.1 hg
  refine ⟨diagMap r (fun μ => -(r μ * w μ)), diagMap_mem hr _, ?_, ?_⟩
  · funext x μ
    have h := hr.mul_self μ
    simp only [diagMap, Function.comp, id]
    linear_combination (x μ - w μ) * h
  · funext x μ
    have h := hr.mul_self μ
    simp only [diagMap, Function.comp, id]
    linear_combination (x μ) * h
theorem projection_apply_eq {ℓ : Fin 4 → ℝ} {g : AmbientSpace → AmbientSpace}
    (hg : g ∈ signAffineGroup) {x y : AmbientSpace} (h : projection ℓ x = projection ℓ y) :
    projection ℓ (g x) = projection ℓ (g y) := by
  obtain ⟨r, w, hr, rfl⟩ := mem_signAffineGroup_iff.1 hg
  rw [projection_eq_iff] at h ⊢
  intro μ
  obtain ⟨k, hk⟩ := h μ
  rcases hr μ with e | e
  · exact ⟨k, by simp only [diagMap, e, hk]; ring⟩
  · exact ⟨-k, by simp only [diagMap, e, hk]; push_cast; ring⟩
theorem continuous_of_mem_signAffineGroup {g : AmbientSpace → AmbientSpace}
    (hg : g ∈ signAffineGroup) : Continuous g := by
  obtain ⟨r, w, -, rfl⟩ := mem_signAffineGroup_iff.1 hg
  exact continuous_pi fun μ => (continuous_const.mul (continuous_apply μ)).add continuous_const
section Induced
variable (d : CellGrid L κ)
theorem exists_isInducedMap {g : AmbientSpace → AmbientSpace} (hg : g ∈ signAffineGroup) :
    ∃ gbar : d.Space → d.Space, d.IsInducedMap gbar g := by
  have hs := BoxTorus.projection_surjective d.sideLengths
  refine ⟨fun t => projection d.sideLengths (g (Function.surjInv hs t)), ?_⟩
  funext x
  exact projection_apply_eq hg (Function.surjInv_eq hs _)
theorem isInducedMap_descend {g : AmbientSpace → AmbientSpace} (hg : g ∈ signAffineGroup) :
    d.IsInducedMap (descend d g) g :=
  Classical.epsilon_spec (exists_isInducedMap d hg)
theorem descend_projection {g : AmbientSpace → AmbientSpace} (hg : g ∈ signAffineGroup)
    (x : AmbientSpace) :
    descend d g (projection d.sideLengths x) = projection d.sideLengths (g x) :=
  congrFun (isInducedMap_descend d hg) x
theorem isInducedMap_unique {g : AmbientSpace → AmbientSpace} {a b : d.Space → d.Space}
    (ha : d.IsInducedMap a g) (hb : d.IsInducedMap b g) : a = b :=
  (BoxTorus.projection_surjective d.sideLengths).injective_comp_right (ha.trans hb.symm)
theorem descend_comp {g h : AmbientSpace → AmbientSpace} (hg : g ∈ signAffineGroup)
    (hh : h ∈ signAffineGroup) : descend d (g ∘ h) = descend d g ∘ descend d h := by
  refine isInducedMap_unique d (isInducedMap_descend d (comp_mem_signAffineGroup hg hh)) ?_
  funext x
  simp only [Function.comp, descend_projection d hg, descend_projection d hh]
theorem descend_id : descend d id = id :=
  isInducedMap_unique d (isInducedMap_descend d id_mem_signAffineGroup) rfl
theorem continuous_descend {g : AmbientSpace → AmbientSpace} (hg : g ∈ signAffineGroup) :
    Continuous (descend d g) := by
  apply continuous_of_comp_projection
  rw [show descend d g ∘ projection d.sideLengths = _ from isInducedMap_descend d hg]
  exact (continuous_projection _).comp (continuous_of_mem_signAffineGroup hg)
theorem exists_descend_inverse {g : AmbientSpace → AmbientSpace} (hg : g ∈ signAffineGroup) :
    ∃ g' ∈ signAffineGroup, descend d g ∘ descend d g' = id ∧
      descend d g' ∘ descend d g = id := by
  obtain ⟨g', hg', h₁, h₂⟩ := exists_inverse_mem hg
  refine ⟨g', hg', ?_, ?_⟩
  · rw [← descend_comp d hg hg', h₁, descend_id]
  · rw [← descend_comp d hg' hg, h₂, descend_id]
theorem isHomeomorph_descend {g : AmbientSpace → AmbientSpace} (hg : g ∈ signAffineGroup) :
    IsHomeomorph (descend d g) := by
  obtain ⟨g', hg', h₁, h₂⟩ := exists_descend_inverse d hg
  exact (Homeomorph.mk
    ⟨descend d g, descend d g', congrFun h₂, congrFun h₁⟩
    (continuous_descend d hg) (continuous_descend d hg')).isHomeomorph
theorem bijective_descend {g : AmbientSpace → AmbientSpace} (hg : g ∈ signAffineGroup) :
    Function.Bijective (descend d g) :=
  (isHomeomorph_descend d hg).bijective
theorem torusDist_descend {r w : AmbientSpace} (hr : IsSignVector r) (x y : d.Space) :
    BoxTorus.torusDist (descend d (diagMap r w) x) (descend d (diagMap r w) y) =
      BoxTorus.torusDist x y := by
  have hg := diagMap_mem hr w
  have hs := diagMap_mem hr 0
  obtain ⟨a, rfl⟩ := BoxTorus.projection_surjective d.sideLengths x
  obtain ⟨b, rfl⟩ := BoxTorus.projection_surjective d.sideLengths y
  have hnorm : ∀ z : AmbientSpace,
      Real.sqrt (∑ μ, diagMap r 0 z μ ^ 2) = Real.sqrt (∑ μ, z μ ^ 2) := by
    intro z
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    have h := hr.mul_self μ
    simp only [diagMap, Pi.zero_apply, add_zero]
    linear_combination (z μ ^ 2) * h
  have hinv : ∀ z : AmbientSpace, diagMap r 0 (diagMap r 0 z) = z := by
    intro z
    funext μ
    have h := hr.mul_self μ
    simp only [diagMap, add_zero, Pi.zero_apply]
    linear_combination (z μ) * h
  have hdiff : diagMap r w a - diagMap r w b = diagMap r 0 (a - b) := by
    funext μ
    simp only [diagMap, Pi.sub_apply, Pi.zero_apply]
    ring
  have e₁ : descend d (diagMap r w) (projection d.sideLengths a) -
      descend d (diagMap r w) (projection d.sideLengths b) =
      projection d.sideLengths (diagMap r 0 (a - b)) := by
    rw [descend_projection d hg, descend_projection d hg, ← map_sub, hdiff]
  have e₂ : projection d.sideLengths a - projection d.sideLengths b =
      projection d.sideLengths (a - b) :=
    (map_sub _ _ _).symm
  unfold BoxTorus.torusDist
  rw [e₁, e₂]
  congr 1
  ext t
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨diagMap r 0 z, ?_, hnorm z⟩
    have := projection_apply_eq (ℓ := d.sideLengths) hs
      (show projection d.sideLengths z = _ from hz)
    rw [hinv] at this
    exact this
  · rintro ⟨z, hz, rfl⟩
    refine ⟨diagMap r 0 z, ?_, hnorm z⟩
    exact projection_apply_eq (ℓ := d.sideLengths) hs (show projection d.sideLengths z = _ from hz)
theorem image_descend_image {g : AmbientSpace → AmbientSpace} (hg : g ∈ signAffineGroup)
    (S : Set AmbientSpace) :
    descend d g '' BoxTorus.image d.sideLengths S = BoxTorus.image d.sideLengths (g '' S) := by
  simp only [BoxTorus.image, image_image, descend_projection d hg]
theorem descend_translate {r w : AmbientSpace} (hr : IsSignVector r) (x : d.Space)
    (w' : AmbientSpace) :
    descend d (diagMap r w) (translate x w') =
      translate (descend d (diagMap r w) x) (diagMap r 0 w') := by
  have hg := diagMap_mem hr w
  obtain ⟨a, rfl⟩ := BoxTorus.projection_surjective d.sideLengths x
  have e : diagMap r w (a + w') = diagMap r w a + diagMap r 0 w' := by
    funext μ
    simp only [diagMap, Pi.add_apply, Pi.zero_apply]
    ring
  rw [BoxTorus.translate, BoxTorus.translate, ← map_add, descend_projection d hg, descend_projection d hg, e, map_add]
theorem gridSubgroup_eq_image :
    (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) =
      BoxTorus.image d.sideLengths
        (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L κ) : Set AmbientSpace) := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨_, ⟨n, fun _ => rfl⟩, rfl⟩
  · rintro ⟨y, ⟨n, hn⟩, rfl⟩
    exact ⟨n, congrArg _ (funext hn)⟩
end Induced
theorem projection_mem_image_iff (ℓ : Fin 4 → ℝ) (μ : Fin 4) (E : Set ℝ) (y : AmbientSpace) :
    projection ℓ y ∈ BoxTorus.image ℓ {w | w μ ∈ E} ↔ y μ ∈ addPeriodMultiples E (ℓ μ) := by
  constructor
  · rintro ⟨w, hw, h⟩
    obtain ⟨k, hk⟩ := (projection_eq_iff y w).1 h.symm μ
    exact ⟨w μ, hw, k, hk⟩
  · rintro ⟨s, hs, k, e⟩
    refine ⟨Function.update y μ s, by simpa using hs, ?_⟩
    rw [projection_eq_iff]
    intro ν
    by_cases h : ν = μ
    · subst h
      exact ⟨-k, by simp [e]⟩
    · exact ⟨0, by simp [Function.update_of_ne h]⟩
theorem mem_slab_iff {ℓ : Fin 4 → ℝ} {x : BoxTorus.Space ℓ} {y : AmbientSpace}
    (hy : IsLiftOf y x) (μ : Fin 4) (a b : ℝ) :
    x ∈ slab ℓ μ a b ↔ y μ ∈ addPeriodMultiples (Ioo a b) (ℓ μ) := by
  have h : projection ℓ y = x := hy
  subst h
  exact projection_mem_image_iff ℓ μ (Ioo a b) y
theorem mem_hyperplane_iff {ℓ : Fin 4 → ℝ} {x : BoxTorus.Space ℓ} {y : AmbientSpace}
    (hy : IsLiftOf y x) (μ : Fin 4) (a : ℝ) :
    x ∈ hyperplane ℓ μ a ↔ y μ ∈ addPeriodMultiples {a} (ℓ μ) := by
  have h : projection ℓ y = x := hy
  subst h
  exact projection_mem_image_iff ℓ μ {a} y
def fracPhase (c p t : ℝ) : ℝ := Int.fract ((t - c) / p)
theorem fracPhase_eq {c p t v : ℝ} (hp : 0 < p) (k : ℤ) (h₀ : 0 ≤ v) (h₁ : v < 1)
    (ht : t = c + p * v + k * p) : fracPhase c p t = v := by
  have e : (t - c) / p = v + k := by
    rw [ht]
    field_simp
    ring
  rw [fracPhase, e, Int.fract_add_intCast, Int.fract_eq_self]
  exact ⟨h₀, h₁⟩
theorem eq_fracPhase (c : ℝ) {p : ℝ} (hp : 0 < p) (t : ℝ) :
    t = c + p * fracPhase c p t + (⌊(t - c) / p⌋ : ℤ) * p := by
  have h := Int.floor_add_fract ((t - c) / p)
  have h' : (t - c) / p * p = t - c := by field_simp
  rw [fracPhase]
  linear_combination (-p) * h - h'
theorem fracPhase_mem (c p t : ℝ) : 0 ≤ fracPhase c p t ∧ fracPhase c p t < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
theorem mem_addPeriodMultiples_iff {c p t : ℝ} (hp : 0 < p) {E V : Set ℝ} (m : ℤ)
    (hV : ∀ v ∈ V, 0 ≤ v ∧ v < 1) (hE : ∀ u : ℝ, c + p * u ∈ E ↔ u + m ∈ V) :
    t ∈ addPeriodMultiples E p ↔ fracPhase c p t ∈ V := by
  constructor
  · rintro ⟨s, hs, k, rfl⟩
    have e : p * ((s - c) / p) = s - c := by field_simp
    have hsE : c + p * ((s - c) / p) ∈ E := by
      rw [e]
      simpa using hs
    have hv := (hE _).1 hsE
    have hb := hV _ hv
    rw [fracPhase_eq hp (k - m) hb.1 hb.2 (by push_cast; linear_combination -e)]
    exact hv
  · intro hf
    refine ⟨c + p * (fracPhase c p t - m), (hE _).2 (by simpa using hf),
      ⌊(t - c) / p⌋ + m, ?_⟩
    have := eq_fracPhase c hp t
    push_cast
    linear_combination this
theorem mem_addPeriodMultiples_upper {c p t : ℝ} (hp : 0 < p) :
    t ∈ addPeriodMultiples (Ioo c (c + 1 / 2 * p)) p ↔ fracPhase c p t ∈ Ioo (0 : ℝ) (1 / 2) := by
  refine mem_addPeriodMultiples_iff hp 0 (fun v hv => ⟨hv.1.le, by linarith [hv.2]⟩) fun u => ?_
  simp only [mem_Ioo, Int.cast_zero, add_zero]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor <;> nlinarith
  · rintro ⟨h₁, h₂⟩
    constructor <;> nlinarith
theorem mem_addPeriodMultiples_lower {c p t : ℝ} (hp : 0 < p) :
    t ∈ addPeriodMultiples (Ioo (c - 1 / 2 * p) c) p ↔ fracPhase c p t ∈ Ioo (1 / 2 : ℝ) 1 := by
  refine mem_addPeriodMultiples_iff hp 1 (fun v hv => ⟨by linarith [hv.1], hv.2⟩) fun u => ?_
  simp only [mem_Ioo, Int.cast_one]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor <;> nlinarith
  · rintro ⟨h₁, h₂⟩
    constructor <;> nlinarith
theorem mem_addPeriodMultiples_point {c p t : ℝ} (hp : 0 < p) :
    t ∈ addPeriodMultiples {c} p ↔ fracPhase c p t = 0 := by
  refine mem_addPeriodMultiples_iff hp 0 (V := {0}) (fun v hv => ?_) fun u => ?_
  · rw [mem_singleton_iff.1 hv]
    norm_num
  · simp [hp.ne']
theorem mem_addPeriodMultiples_mid {c p t : ℝ} (hp : 0 < p) :
    t ∈ addPeriodMultiples {c + 1 / 2 * p} p ↔ fracPhase c p t = 1 / 2 := by
  refine mem_addPeriodMultiples_iff hp 0 (V := {1 / 2}) (fun v hv => ?_) fun u => ?_
  · rw [mem_singleton_iff.1 hv]
    norm_num
  · simp only [mem_singleton_iff, Int.cast_zero, add_zero]
    constructor
    · intro h
      exact mul_left_cancel₀ hp.ne' (by linarith)
    · rintro rfl
      ring
def phaseCells : Fin 4 → Set ℝ := ![Ioo 0 (1 / 2), Ioo (1 / 2) 1, {0}, {1 / 2}]
theorem phaseCells_disjoint {i j : Fin 4} (hij : i ≠ j) {t : ℝ} (hi : t ∈ phaseCells i)
    (hj : t ∈ phaseCells j) : False := by
  fin_cases i <;> fin_cases j <;> first
    | exact hij rfl
    | (simp [phaseCells] at hi hj <;> linarith)
theorem phaseCells_cover {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t < 1) : ∃ i, t ∈ phaseCells i := by
  rcases h₀.eq_or_lt with h | h
  · exact ⟨2, by simp [phaseCells, h.symm]⟩
  rcases lt_trichotomy t (1 / 2) with h' | h' | h'
  · exact ⟨0, show t ∈ Ioo (0 : ℝ) (1 / 2) from ⟨h, h'⟩⟩
  · exact ⟨3, by simp [phaseCells, h']⟩
  · exact ⟨1, show t ∈ Ioo (1 / 2 : ℝ) 1 from ⟨h', h₁⟩⟩
section Parts
variable (d : CellGrid L κ)
theorem sideLengths_pos (μ : Fin 4) : 0 < d.sideLengths μ :=
  mul_pos (Nat.cast_pos.2 (d.counts_pos μ)) d.cellLength_pos
theorem mem_partition_iff {x : d.Space} {y : AmbientSpace} (hy : IsLiftOf y x) (μ : Fin 4)
    (c : ℝ) (i : Fin 4) :
    x ∈ partition d μ c i ↔ fracPhase c (d.sideLengths μ) (y μ) ∈ phaseCells i := by
  have hp := sideLengths_pos d μ
  fin_cases i
  · exact (mem_slab_iff hy μ _ _).trans (mem_addPeriodMultiples_upper hp)
  · exact (mem_slab_iff hy μ _ _).trans (mem_addPeriodMultiples_lower hp)
  · exact (mem_hyperplane_iff hy μ _).trans (mem_addPeriodMultiples_point hp)
  · exact (mem_hyperplane_iff hy μ _).trans (mem_addPeriodMultiples_mid hp)
theorem liftCharacterization (μ : Fin 4) (c : ℝ) : LiftCharacterization d μ c := by
  refine ⟨fun x y hy => ⟨mem_slab_iff hy μ _ _, mem_slab_iff hy μ _ _,
    mem_hyperplane_iff hy μ _, mem_hyperplane_iff hy μ _⟩, ?_, ?_⟩
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨y, hy⟩ := BoxTorus.projection_surjective d.sideLengths x
    obtain ⟨i, hi⟩ := phaseCells_cover (fracPhase_mem c (d.sideLengths μ) (y μ)).1
      (fracPhase_mem c (d.sideLengths μ) (y μ)).2
    exact mem_iUnion.2 ⟨i, (mem_partition_iff d hy μ c i).2 hi⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    obtain ⟨y, hy⟩ := BoxTorus.projection_surjective d.sideLengths x
    exact phaseCells_disjoint hij ((mem_partition_iff d hy μ c i).1 hi)
      ((mem_partition_iff d hy μ c j).1 hj)
end Parts
theorem coordReflection_apply (μ : Fin 4) (c : ℝ) (x : AmbientSpace) (ν : Fin 4) :
    coordReflection μ c x ν = if ν = μ then 2 * c - x μ else x ν := by
  by_cases h : ν = μ
  · subst h
    simp [coordReflection, basisVector]
    ring
  · simp [coordReflection, basisVector, h]
theorem coordReflection_coordReflection (μ : Fin 4) (c : ℝ) (x : AmbientSpace) :
    coordReflection μ c (coordReflection μ c x) = x := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [coordReflection_apply]
  · simp [coordReflection_apply, h]
theorem coordReflection_mem (μ : Fin 4) (c : ℝ) : coordReflection μ c ∈ signAffineGroup := by
  refine mem_signAffineGroup_iff.2 ⟨fun ν => if ν = μ then -1 else 1,
    fun ν => if ν = μ then 2 * c else 0, fun ν => ?_, ?_⟩
  · by_cases h : ν = μ <;> simp [h]
  · funext x ν
    rw [coordReflection_apply]
    by_cases h : ν = μ
    · subst h
      simp [diagMap]
      ring
    · simp [diagMap, h]
theorem coordReflection_image_band (μ : Fin 4) (c a b : ℝ) :
    coordReflection μ c '' {w | a < w μ ∧ w μ < b} =
      {w | 2 * c - b < w μ ∧ w μ < 2 * c - a} := by
  ext w
  constructor
  · rintro ⟨v, ⟨h₁, h₂⟩, rfl⟩
    simp only [mem_ofPred_eq, coordReflection_apply, if_true]
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    refine ⟨coordReflection μ c w, ?_, coordReflection_coordReflection μ c w⟩
    simp only [mem_ofPred_eq, coordReflection_apply, if_true]
    constructor <;> linarith
section Reflection
variable (d : CellGrid L κ)
theorem reflectionInvolutive (μ : Fin 4) (c : ℝ) : ReflectionInvolutive d μ c := by
  have hm := coordReflection_mem μ c
  have hp := sideLengths_pos d μ
  refine ⟨?_, ?_⟩
  · rw [← descend_comp d hm hm,
      show coordReflection μ c ∘ coordReflection μ c = id from
        funext (coordReflection_coordReflection μ c),
      descend_id]
  · ext x
    obtain ⟨y, rfl⟩ := BoxTorus.projection_surjective d.sideLengths x
    have hl : IsLiftOf y (projection d.sideLengths y) := rfl
    simp only [mem_ofPred_eq, descend_projection d hm, fixedPlanes, mem_union,
      mem_hyperplane_iff hl, projection_eq_iff]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := h μ
      rw [coordReflection_apply, if_pos rfl] at hk
      rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
      · refine Or.inl ⟨c, rfl, -m, ?_⟩
        push_cast at hk ⊢
        linarith
      · refine Or.inr ⟨c + 1 / 2 * d.sideLengths μ, rfl, -m - 1, ?_⟩
        push_cast at hk ⊢
        linarith
    · have key : ∀ k : ℤ, 2 * c - y μ = y μ + k * d.sideLengths μ →
          ∀ ν, ∃ k : ℤ, coordReflection μ c y ν = y ν + k * d.sideLengths ν := by
        intro k hk ν
        by_cases h : ν = μ
        · subst h
          exact ⟨k, by rw [coordReflection_apply, if_pos rfl, hk]⟩
        · exact ⟨0, by simp [coordReflection_apply, h]⟩
      rintro (⟨s, hs, k, e⟩ | ⟨s, hs, k, e⟩)
      · rw [mem_singleton_iff] at hs
        subst hs
        refine key (-2 * k) ?_
        push_cast
        linarith
      · rw [mem_singleton_iff] at hs
        subst hs
        refine key (-2 * k - 1) ?_
        push_cast
        linarith
theorem isOpen_slab (ℓ : Fin 4 → ℝ) (μ : Fin 4) (a b : ℝ) : IsOpen (slab ℓ μ a b) :=
  isOpenMap_projection ℓ _ ((isOpen_lt continuous_const (continuous_apply μ)).inter
    (isOpen_lt (continuous_apply μ) continuous_const))
theorem isPreconnected_slab (ℓ : Fin 4 → ℝ) (μ : Fin 4) (a b : ℝ) :
    IsPreconnected (slab ℓ μ a b) := by
  have h : Convex ℝ {w : AmbientSpace | a < w μ ∧ w μ < b} :=
    (convex_Ioo a b).linear_preimage (LinearMap.proj μ : AmbientSpace →ₗ[ℝ] ℝ)
  exact h.isPreconnected.image _ (continuous_projection ℓ).continuousOn
theorem slab_nonempty (ℓ : Fin 4 → ℝ) (μ : Fin 4) {a b : ℝ} (h : a < b) :
    (slab ℓ μ a b).Nonempty :=
  ⟨_, fun _ => (a + b) / 2, ⟨by simp only; linarith, by simp only; linarith⟩, rfl⟩
theorem connectedComponentIn_union_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B) (hc : IsPreconnected A) {x : X}
    (hx : x ∈ A) : connectedComponentIn (A ∪ B) x = A := by
  refine Subset.antisymm ?_ (hc.subset_connectedComponentIn hx subset_union_left)
  exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hA hB hAB
    (connectedComponentIn_subset _ _)
    ⟨x, mem_connectedComponentIn (Or.inl hx), hx⟩
theorem fixedPlanes_compl (μ : Fin 4) (c : ℝ) :
    (fixedPlanes d μ c)ᶜ = posHalf d μ c ∪ negHalf d μ c := by
  have hparts := liftCharacterization d μ c
  have hdis := hparts.2.2
  ext x
  have hx : x ∈ ⋃ i, partition d μ c i := by
    rw [hparts.2.1]
    exact mem_univ x
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  have h02 := Set.disjoint_left.1 (hdis (show (0 : Fin 4) ≠ 2 by decide))
  have h03 := Set.disjoint_left.1 (hdis (show (0 : Fin 4) ≠ 3 by decide))
  have h12 := Set.disjoint_left.1 (hdis (show (1 : Fin 4) ≠ 2 by decide))
  have h13 := Set.disjoint_left.1 (hdis (show (1 : Fin 4) ≠ 3 by decide))
  constructor
  · intro hn
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
    · exact absurd (Or.inl hi) hn
    · exact absurd (Or.inr hi) hn
  · rintro (h | h) (h' | h')
    · exact h02 h h'
    · exact h03 h h'
    · exact h12 h h'
    · exact h13 h h'
theorem halvesAreComponents (μ : Fin 4) (c : ℝ) : HalvesAreComponents d μ c := by
  have hp := sideLengths_pos d μ
  have hm := coordReflection_mem μ c
  have hoU : IsOpen (posHalf d μ c) := isOpen_slab _ _ _ _
  have hoL : IsOpen (negHalf d μ c) := isOpen_slab _ _ _ _
  have hcU : IsPreconnected (posHalf d μ c) := isPreconnected_slab _ _ _ _
  have hcL : IsPreconnected (negHalf d μ c) := isPreconnected_slab _ _ _ _
  have hnU : (posHalf d μ c).Nonempty := slab_nonempty _ _ (by linarith)
  have hnL : (negHalf d μ c).Nonempty := slab_nonempty _ _ (by linarith)
  have hdis : Disjoint (posHalf d μ c) (negHalf d μ c) :=
    (liftCharacterization d μ c).2.2 (show (0 : Fin 4) ≠ 1 by decide)
  have hcompl := fixedPlanes_compl d μ c
  refine ⟨?_, ?_, hoU, hoL, ?_, ?_⟩
  · rw [hcompl]
    ext C
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨x, hx | hx, rfl⟩
      · exact Or.inl (connectedComponentIn_union_of_isOpen hoU hoL hdis hcU hx)
      · refine Or.inr ?_
        rw [union_comm]
        exact connectedComponentIn_union_of_isOpen hoL hoU hdis.symm hcL hx
    · rintro (rfl | rfl)
      · obtain ⟨x, hx⟩ := hnU
        exact ⟨x, Or.inl hx, (connectedComponentIn_union_of_isOpen hoU hoL hdis hcU hx).symm⟩
      · obtain ⟨x, hx⟩ := hnL
        refine ⟨x, Or.inr hx, ?_⟩
        rw [union_comm]
        exact (connectedComponentIn_union_of_isOpen hoL hoU hdis.symm hcL hx).symm
  · intro h
    obtain ⟨x, hx⟩ := hnU
    exact Set.disjoint_left.1 hdis hx (h ▸ hx)
  · refine (image_descend_image d hm _).trans ?_
    rw [coordReflection_image_band]
    simp only [negHalf, slab]
    congr 1
    ext w
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  · refine (image_descend_image d hm _).trans ?_
    rw [coordReflection_image_band]
    simp only [posHalf, slab]
    congr 1
    ext w
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
theorem slab_add_period (ℓ : Fin 4 → ℝ) (μ : Fin 4) (a b : ℝ) :
    slab ℓ μ (a + ℓ μ) (b + ℓ μ) = slab ℓ μ a b := by
  ext x
  obtain ⟨y, rfl⟩ := BoxTorus.projection_surjective ℓ x
  have hl : IsLiftOf y (projection ℓ y) := rfl
  rw [mem_slab_iff hl, mem_slab_iff hl]
  constructor
  · rintro ⟨s, ⟨h₁, h₂⟩, k, e⟩
    exact ⟨s - ℓ μ, ⟨by linarith, by linarith⟩, k + 1, by push_cast; linarith⟩
  · rintro ⟨s, ⟨h₁, h₂⟩, k, e⟩
    exact ⟨s + ℓ μ, ⟨by linarith, by linarith⟩, k - 1, by push_cast; linarith⟩
theorem shiftedMirrorAgrees (μ : Fin 4) (c : ℝ) : ShiftedMirrorAgrees d μ c := by
  have hm := coordReflection_mem μ c
  refine ⟨?_, ?_, ?_⟩
  · funext x
    simp only [Function.comp]
    rw [descend_projection d hm, projection_eq_iff]
    intro ν
    by_cases h : ν = μ
    · subst h
      refine ⟨-1, ?_⟩
      rw [coordReflection_apply, coordReflection_apply, if_pos rfl, if_pos rfl]
      push_cast
      ring
    · exact ⟨0, by simp [coordReflection_apply, h]⟩
  · simp only [posHalf, negHalf]
    rw [← slab_add_period d.sideLengths μ (c - 1 / 2 * d.sideLengths μ) c]
    congr 1 <;> ring
  · simp only [posHalf, negHalf]
    congr 1 <;> ring
end Reflection
theorem descentTheorem : DescentTheorem := by
  intro L κ d
  refine ⟨⟨continuous_projection _, isOpenMap_projection _⟩,
    ⟨id_mem_signAffineGroup, fun _ hg _ hh => comp_mem_signAffineGroup hg hh,
      fun _ hg => exists_inverse_mem hg⟩, ?_, ?_,
    fun μ c => ⟨coordReflection_mem μ c, liftCharacterization d μ c, reflectionInvolutive d μ c,
      halvesAreComponents d μ c, shiftedMirrorAgrees d μ c⟩⟩
  · refine ⟨fun g hg => ⟨descend d g, isInducedMap_descend d hg, fun b hb =>
      isInducedMap_unique d hb (isInducedMap_descend d hg)⟩,
      fun g hg => isInducedMap_descend d hg, fun g hg h hh => descend_comp d hg hh,
      descend_id d, fun g hg => ⟨⟨bijective_descend d hg, ?_⟩, isHomeomorph_descend d hg⟩⟩
    obtain ⟨r, w, hr, rfl⟩ := mem_signAffineGroup_iff.1 hg
    exact torusDist_descend d hr
  · rintro R w ⟨r, hr, rfl⟩
    have hg : signAffine (Matrix.diagonal r) w ∈ signAffineGroup := by
      rw [signAffine_diagonal]
      exact diagMap_mem hr w
    refine ⟨fun S => image_descend_image d hg S, fun x w' => ?_, fun h => ?_⟩
    · rw [signAffine_diagonal, mulVec_diagonal_eq_diagMap]
      exact descend_translate d hr x w'
    · rw [gridSubgroup_eq_image, image_descend_image d hg, h]
end YangMills.Construction.TorusDescent
end
