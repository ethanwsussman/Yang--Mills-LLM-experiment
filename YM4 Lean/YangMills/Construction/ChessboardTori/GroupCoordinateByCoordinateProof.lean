import YangMills.Construction.ChessboardTori.GroupCoordinateByCoordinate
import YangMills.Construction.ChessboardTori.GroupOfAGridAndCopiesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ReflectionGroupCoordinatesProof
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem reflect_apply_self (μ : Fin 4) (k : ℤ) (x : AmbientSpace) :
    g.reflect μ k x μ = 2 * (g.origin μ + k * g.cellSide) - x μ := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGroupAndTransport.reflect_apply_self <;> assumption
theorem reflect_apply_of_ne {μ ν : Fin 4} (h : ν ≠ μ) (k : ℤ) (x : AmbientSpace) :
    g.reflect μ k x ν = x ν := by
  simp [ReflectionGrid.reflect, coordVec, Pi.single_eq_of_ne h]
theorem isProductOfCoordMaps_reflectPerm (μ : Fin 4) (k : ℤ) :
    g.IsProductOfCoordMaps (g.reflectPerm μ k) := by
  intro ν
  by_cases h : ν = μ
  · subst h
    refine Or.inr ⟨k, fun x => ?_⟩
    show g.reflect ν k x ν - _ = _
    rw [reflect_apply_self]
    simp only [ReflectionGrid.coordReflect]
    ring
  · refine Or.inl ⟨0, fun x => ?_⟩
    show g.reflect μ k x ν - _ = _
    rw [reflect_apply_of_ne g h]
    simp [ReflectionGrid.coordShift]
theorem isProductOfCoordMaps_comp {r s : AmbientSpace → AmbientSpace} (hr : g.IsProductOfCoordMaps r)
    (hs : g.IsProductOfCoordMaps s) : g.IsProductOfCoordMaps (r ∘ s) := by
  intro μ
  rcases hr μ with ⟨t, ht⟩ | ⟨k, hk⟩ <;> rcases hs μ with ⟨t', ht'⟩ | ⟨k', hk'⟩
  · refine Or.inl ⟨t + t', fun x => ?_⟩
    simp only [Function.comp, ht (s x), ht' x, ReflectionGrid.coordShift]
    push_cast
    ring
  · refine Or.inr ⟨k' + t, fun x => ?_⟩
    simp only [Function.comp, ht (s x), hk' x, ReflectionGrid.coordShift,
      ReflectionGrid.coordReflect]
    push_cast
    ring
  · refine Or.inr ⟨k - t', fun x => ?_⟩
    simp only [Function.comp, hk (s x), ht' x, ReflectionGrid.coordShift,
      ReflectionGrid.coordReflect]
    push_cast
    ring
  · refine Or.inl ⟨k - k', fun x => ?_⟩
    simp only [Function.comp, hk (s x), hk' x, ReflectionGrid.coordShift,
      ReflectionGrid.coordReflect]
    push_cast
    ring
theorem isProductOfCoordMaps_inv {r : Equiv.Perm AmbientSpace} (hr : g.IsProductOfCoordMaps r) :
    g.IsProductOfCoordMaps (r⁻¹ : Equiv.Perm AmbientSpace) := by
  intro μ
  rcases hr μ with ⟨t, ht⟩ | ⟨k, hk⟩
  · refine Or.inl ⟨-t, fun x => ?_⟩
    have h := ht ((r⁻¹ : Equiv.Perm AmbientSpace) x)
    rw [show r ((r⁻¹ : Equiv.Perm AmbientSpace) x) = x by simp] at h
    simp only [ReflectionGrid.coordShift] at h ⊢
    push_cast
    linarith
  · refine Or.inr ⟨k, fun x => ?_⟩
    have h := hk ((r⁻¹ : Equiv.Perm AmbientSpace) x)
    rw [show r ((r⁻¹ : Equiv.Perm AmbientSpace) x) = x by simp] at h
    simp only [ReflectionGrid.coordReflect] at h ⊢
    linarith
theorem isProductOfCoordMaps_id : g.IsProductOfCoordMaps (id : AmbientSpace → AmbientSpace) := fun _ =>
  Or.inl ⟨0, fun x => by simp [ReflectionGrid.coordShift]⟩
theorem isProductOfCoordMaps_of_mem {r : Equiv.Perm AmbientSpace} (hr : r ∈ g.reflectionGroup) :
    g.IsProductOfCoordMaps r := by
  refine Subgroup.closure_induction
    (p := fun (r : Equiv.Perm AmbientSpace) _ => g.IsProductOfCoordMaps r) ?_ ?_ ?_ ?_ hr
  · rintro _ ⟨⟨μ, k⟩, rfl⟩
    exact isProductOfCoordMaps_reflectPerm g μ k
  · exact isProductOfCoordMaps_id g
  · intro r s _ _ h h'
    show g.IsProductOfCoordMaps (r ∘ s)
    exact isProductOfCoordMaps_comp g h h'
  · intro r _ h
    exact isProductOfCoordMaps_inv g h
theorem reflectPerm_mem (μ : Fin 4) (k : ℤ) : g.reflectPerm μ k ∈ g.reflectionGroup :=
  Subgroup.subset_closure ⟨(μ, k), rfl⟩
theorem exists_mem_actsOnCoord_single {r : AmbientSpace → AmbientSpace}
    (hr : g.IsProductOfCoordMaps r) (μ : Fin 4) :
    ∃ a ∈ g.reflectionGroup, ∃ f : ℝ → ℝ, g.ActsOnCoord a μ f ∧ g.ActsOnCoord r μ f ∧
      ∀ ν, ν ≠ μ → ∀ x, a x ν = x ν := by
  rcases hr μ with ⟨t, ht⟩ | ⟨k, hk⟩
  · refine ⟨g.reflectPerm μ t * g.reflectPerm μ 0,
      g.reflectionGroup.mul_mem (reflectPerm_mem g μ t) (reflectPerm_mem g μ 0),
      g.coordShift t, fun x => ?_, ht, fun ν h x => ?_⟩
    · show g.reflect μ t (g.reflect μ 0 x) μ - _ = _
      rw [reflect_apply_self, reflect_apply_self]
      simp only [ReflectionGrid.coordShift]
      push_cast
      ring
    · show g.reflect μ t (g.reflect μ 0 x) ν = _
      rw [reflect_apply_of_ne g h, reflect_apply_of_ne g h]
  · refine ⟨g.reflectPerm μ k, reflectPerm_mem g μ k, g.coordReflect k, fun x => ?_,
      hk, fun ν h x => reflect_apply_of_ne g h k x⟩
    show g.reflect μ k x μ - _ = _
    rw [reflect_apply_self]
    simp only [ReflectionGrid.coordReflect]
    ring
theorem exists_mem_agree_on {r : AmbientSpace → AmbientSpace} (hr : g.IsProductOfCoordMaps r)
    (A : Finset (Fin 4)) :
    ∃ s ∈ g.reflectionGroup, (∀ μ ∈ A, ∀ x, s x μ = r x μ) ∧ ∀ μ, μ ∉ A → ∀ x, s x μ = x μ := by
  induction A using Finset.induction_on with
  | empty => exact ⟨1, g.reflectionGroup.one_mem, by simp, by simp⟩
  | insert μ A hμ ih =>
    obtain ⟨s, hs, hA, hB⟩ := ih
    obtain ⟨a, ha, f, haf, hrf, hother⟩ := exists_mem_actsOnCoord_single g hr μ
    refine ⟨a * s, g.reflectionGroup.mul_mem ha hs, fun ν hν x => ?_, fun ν hν x => ?_⟩
    · rw [Equiv.Perm.mul_apply]
      by_cases h : ν = μ
      · subst h
        have h1 := haf (s x)
        have h2 := hrf x
        rw [hB ν hμ x] at h1
        linarith
      · rw [hother ν h]
        exact hA ν (Finset.mem_of_mem_insert_of_ne hν h) x
    · rw [Equiv.Perm.mul_apply, hother ν (fun h => hν (h ▸ Finset.mem_insert_self _ _))]
      exact hB ν (fun h => hν (Finset.mem_insert_of_mem h)) x
theorem exists_mem_eq_of_isProductOfCoordMaps {r : AmbientSpace → AmbientSpace}
    (hr : g.IsProductOfCoordMaps r) :
    ∃ s ∈ g.reflectionGroup, (s : AmbientSpace → AmbientSpace) = r := by
  obtain ⟨s, hs, hA, -⟩ := exists_mem_agree_on g hr Finset.univ
  exact ⟨s, hs, funext fun x => funext fun μ => hA μ (Finset.mem_univ μ) x⟩
theorem orientationSign_eq_prod_of_diagonal {r : AmbientSpace → AmbientSpace} (e : Fin 4 → ℤˣ)
    (v : AmbientSpace) (h : ∀ x μ, r x μ = ((e μ : ℤ) : ℝ) * x μ + v μ) :
    orientationSign r = ∏ μ, e μ := by
  set R : AmbientSpace →ₗ[ℝ] AmbientSpace :=
    Matrix.toLin' (Matrix.diagonal fun μ => ((e μ : ℤ) : ℝ)) with hRdef
  have hRapply : ∀ (x : AmbientSpace) μ, R x μ = ((e μ : ℤ) : ℝ) * x μ := by
    intro x μ
    simp [hRdef, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have hR : HasLinearComponent r R := ⟨v, fun x => funext fun μ => by
    rw [h x μ, Pi.add_apply, hRapply]⟩
  obtain ⟨w, hw⟩ : HasLinearComponent r (linearComponent r) := Classical.epsilon_spec ⟨R, hR⟩
  have hwv : w = v := by
    have h0 := hw 0
    funext μ
    have h1 := congrFun h0 μ
    rw [h 0 μ] at h1
    simpa using h1.symm
  have hL : linearComponent r = R := by
    refine LinearMap.ext fun x => funext fun μ => ?_
    have h1 := congrFun (hw x) μ
    rw [h x μ, hwv, Pi.add_apply] at h1
    rw [hRapply]
    linarith
  have hdet : LinearMap.det (linearComponent r) = (((∏ μ, e μ : ℤˣ) : ℤ) : ℝ) := by
    rw [hL, hRdef, LinearMap.det_toLin', Matrix.det_diagonal]
    simp
  unfold orientationSign
  rw [hdet]
  rcases Int.units_eq_one_or (∏ μ, e μ) with h1 | h1 <;> rw [h1] <;> norm_num
open Classical in
def diagEntry (r : AmbientSpace → AmbientSpace) (μ : Fin 4) : ℤˣ :=
  if g.ReflectsCoord r μ then -1 else 1
theorem exists_diagonal_affine {r : AmbientSpace → AmbientSpace} (hr : g.IsProductOfCoordMaps r) :
    ∃ v : AmbientSpace, ∀ x μ, r x μ = ((diagEntry g r μ : ℤ) : ℝ) * x μ + v μ := by
  have h : ∀ μ, ∃ v : ℝ, ∀ x, r x μ = ((diagEntry g r μ : ℤ) : ℝ) * x μ + v := by
    intro μ
    by_cases hf : g.ReflectsCoord r μ
    · obtain ⟨k, hk⟩ := hf
      have hf' : g.ReflectsCoord r μ := ⟨k, hk⟩
      refine ⟨2 * k * g.cellSide + 2 * g.origin μ, fun x => ?_⟩
      have h1 := hk x
      simp only [ReflectionGrid.coordReflect] at h1
      simp only [diagEntry, if_pos hf']
      push_cast
      linarith
    · rcases hr μ with ⟨t, ht⟩ | hf'
      · refine ⟨2 * t * g.cellSide, fun x => ?_⟩
        have h1 := ht x
        simp only [ReflectionGrid.coordShift] at h1
        simp only [diagEntry, if_neg hf]
        push_cast
        linarith
      · exact absurd hf' hf
  choose v hv using h
  exact ⟨v, fun x μ => hv μ x⟩
theorem prod_diagEntry (r : AmbientSpace → AmbientSpace) :
    ∏ μ, diagEntry g r μ = (-1) ^ g.numReflectedCoords r := by
  classical
  simp only [diagEntry, ReflectionGrid.numReflectedCoords, Finset.prod_ite, Finset.prod_const,
    one_pow, mul_one]
theorem orientationSign_eq_neg_one_pow {r : AmbientSpace → AmbientSpace}
    (hr : g.IsProductOfCoordMaps r) : orientationSign r = (-1) ^ g.numReflectedCoords r := by
  obtain ⟨v, hv⟩ := exists_diagonal_affine g hr
  rw [orientationSign_eq_prod_of_diagonal (diagEntry g r) v hv, prod_diagEntry]
theorem orientationSign_comp {r s : AmbientSpace → AmbientSpace} (hr : g.IsProductOfCoordMaps r)
    (hs : g.IsProductOfCoordMaps s) :
    orientationSign (r ∘ s) = orientationSign r * orientationSign s := by
  obtain ⟨v, hv⟩ := exists_diagonal_affine g hr
  obtain ⟨w, hw⟩ := exists_diagonal_affine g hs
  rw [orientationSign_eq_prod_of_diagonal (diagEntry g r) v hv,
    orientationSign_eq_prod_of_diagonal (diagEntry g s) w hw,
    orientationSign_eq_prod_of_diagonal (fun μ => diagEntry g r μ * diagEntry g s μ)
      (fun μ => ((diagEntry g r μ : ℤ) : ℝ) * w μ + v μ) (fun x μ => ?_),
    Finset.prod_mul_distrib]
  simp only [Function.comp, hv (s x) μ, hw x μ, Units.val_mul, Int.cast_mul]
  ring
theorem apply_mem_walls {r : AmbientSpace → AmbientSpace} (hr : g.IsProductOfCoordMaps r)
    {x : AmbientSpace} (hx : x ∈ g.walls) : r x ∈ g.walls := by
  simp only [ReflectionGrid.walls, mem_iUnion, ReflectionGrid.wall, mem_ofPred_eq] at hx ⊢
  obtain ⟨μ, k, hk⟩ := hx
  rcases hr μ with ⟨t, ht⟩ | ⟨m, hm⟩
  · refine ⟨μ, k + 2 * t, ?_⟩
    have h1 := ht x
    simp only [ReflectionGrid.coordShift] at h1
    push_cast
    rw [hk] at h1
    linarith
  · refine ⟨μ, 2 * m - k, ?_⟩
    have h1 := hm x
    simp only [ReflectionGrid.coordReflect] at h1
    push_cast
    rw [hk] at h1
    linarith
theorem image_walls {r : Equiv.Perm AmbientSpace} (hr : r ∈ g.reflectionGroup) :
    r '' g.walls = g.walls := by
  refine Subset.antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact apply_mem_walls g (isProductOfCoordMaps_of_mem g hr) hx
  · exact ⟨(r⁻¹ : Equiv.Perm AmbientSpace) y,
      apply_mem_walls g (isProductOfCoordMaps_of_mem g (g.reflectionGroup.inv_mem hr)) hy, by simp⟩
theorem reflect_mem_Icc_iff (s z : ℝ) : s - z ∈ Icc 0 s ↔ z ∈ Icc 0 s := by
  simp only [mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
theorem coordShift_sub_mul (t j j' : ℤ) (h : j' = j + 2 * t) (y : ℝ) :
    g.coordShift t y - g.cellSide * j' = y - g.cellSide * j := by
  subst h
  simp only [ReflectionGrid.coordShift]
  push_cast
  ring
theorem coordReflect_sub_mul (m j j' : ℤ) (h : j' = 2 * m - 1 - j) (y : ℝ) :
    g.coordReflect m y - g.cellSide * j' = g.cellSide - (y - g.cellSide * j) := by
  subst h
  simp only [ReflectionGrid.coordReflect]
  push_cast
  ring
theorem mem_cell_iff_coords (k : Fin 4 → ℤ) (x : AmbientSpace) :
    x ∈ g.cell k ↔ ∀ μ, (x μ - g.origin μ) - g.cellSide * k μ ∈ Icc 0 g.cellSide := by
  simp only [ReflectionGrid.cell, mem_ofPred_eq, sub_sub]
theorem exists_cell_image_index {r : AmbientSpace → AmbientSpace} (hr : g.IsProductOfCoordMaps r)
    (k : Fin 4 → ℤ) :
    ∃ k' : Fin 4 → ℤ, (∀ x, x ∈ g.cell k ↔ r x ∈ g.cell k') ∧
      ∀ μ, k' μ = k μ → ∀ x, r x μ = x μ := by
  have h : ∀ μ, ∃ j : ℤ, (∀ x, (x μ - g.origin μ) - g.cellSide * k μ ∈ Icc 0 g.cellSide ↔
      (r x μ - g.origin μ) - g.cellSide * j ∈ Icc 0 g.cellSide) ∧ (j = k μ → ∀ x, r x μ = x μ) := by
    intro μ
    rcases hr μ with ⟨t, ht⟩ | ⟨m, hm⟩
    · refine ⟨k μ + 2 * t, fun x => ?_, fun hj x => ?_⟩
      · rw [ht x, coordShift_sub_mul g t (k μ) _ rfl]
      · have ht0 : t = 0 := by omega
        have h1 := ht x
        simp only [ReflectionGrid.coordShift, ht0] at h1
        push_cast at h1
        linarith
    · refine ⟨2 * m - 1 - k μ, fun x => ?_, fun hj => ?_⟩
      · rw [hm x, coordReflect_sub_mul g m (k μ) _ rfl, reflect_mem_Icc_iff]
      · omega
  choose k' hk' hid using h
  refine ⟨k', fun x => ?_, hid⟩
  rw [mem_cell_iff_coords, mem_cell_iff_coords]
  exact forall_congr' fun μ => hk' μ x
theorem image_cell_eq {r : Equiv.Perm AmbientSpace} {k k' : Fin 4 → ℤ}
    (h : ∀ x, x ∈ g.cell k ↔ r x ∈ g.cell k') : r '' g.cell k = g.cell k' := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hz
    exact ⟨(r⁻¹ : Equiv.Perm AmbientSpace) z, (h _).2 (by simpa using hz), by simp⟩
theorem cell_injective : Function.Injective g.cell := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGrid.cell_injective <;> assumption
theorem exists_coordMap_interval (j j' : ℤ) :
    ∃ f : ℝ → ℝ, ((∃ t : ℤ, f = g.coordShift t) ∨ ∃ m : ℤ, f = g.coordReflect m) ∧
      ∀ y, y - g.cellSide * j ∈ Icc 0 g.cellSide ↔ f y - g.cellSide * j' ∈ Icc 0 g.cellSide := by
  rcases Int.even_or_odd' (j' - j) with ⟨n, hn | hn⟩
  · refine ⟨g.coordShift n, Or.inl ⟨n, rfl⟩, fun y => ?_⟩
    rw [coordShift_sub_mul g n j j' (by omega)]
  · refine ⟨g.coordReflect (j + n + 1), Or.inr ⟨_, rfl⟩, fun y => ?_⟩
    rw [coordReflect_sub_mul g (j + n + 1) j j' (by omega), reflect_mem_Icc_iff]
theorem exists_mem_image_cell (k k' : Fin 4 → ℤ) :
    ∃ r : g.reflectionGroup, r.1 '' g.cell k = g.cell k' := by
  choose f hf hmem using fun μ => exists_coordMap_interval g (k μ) (k' μ)
  set r : AmbientSpace → AmbientSpace := fun x μ => g.origin μ + f μ (x μ - g.origin μ) with hrdef
  have hact : ∀ μ, g.ActsOnCoord r μ (f μ) := fun μ x => by simp [hrdef]
  have hr : g.IsProductOfCoordMaps r := by
    intro μ
    rcases hf μ with ⟨t, ht⟩ | ⟨m, hm⟩
    · exact Or.inl ⟨t, ht ▸ hact μ⟩
    · exact Or.inr ⟨m, hm ▸ hact μ⟩
  obtain ⟨s, hs, hsr⟩ := exists_mem_eq_of_isProductOfCoordMaps g hr
  refine ⟨⟨s, hs⟩, image_cell_eq g fun x => ?_⟩
  rw [mem_cell_iff_coords, mem_cell_iff_coords, hsr]
  refine forall_congr' fun μ => ?_
  rw [hact μ x]
  exact hmem μ _
theorem eq_one_of_image_cell {h : Equiv.Perm AmbientSpace} (hh : h ∈ g.reflectionGroup)
    {k : Fin 4 → ℤ} (hk : h '' g.cell k = g.cell k) : h = 1 := by
  obtain ⟨k', hk', hid⟩ := exists_cell_image_index g (isProductOfCoordMaps_of_mem g hh) k
  have himg : h '' g.cell k = g.cell k' := image_cell_eq g hk'
  have hkk : k' = k := cell_injective g (himg.symm.trans hk)
  exact Equiv.ext fun x => funext fun μ => hid μ (congrFun hkk μ) x
theorem existsUnique_image_cell (k k' : Fin 4 → ℤ) :
    ∃! r : g.reflectionGroup, r.1 '' g.cell k = g.cell k' := by
  obtain ⟨r, hr⟩ := exists_mem_image_cell g k k'
  refine ⟨r, hr, fun s hs => ?_⟩
  have h : (r.1⁻¹ * s.1) '' g.cell k = g.cell k := by
    rw [Equiv.Perm.coe_mul, image_comp, hs, ← hr, ← image_comp]
    simp
  have h1 := eq_one_of_image_cell g
    (g.reflectionGroup.mul_mem (g.reflectionGroup.inv_mem r.2) s.2) h
  exact Subtype.ext (inv_mul_eq_one.mp h1).symm
theorem isProductOfCoordMaps_translate (t : Fin 4 → ℤ) :
    g.IsProductOfCoordMaps (translate fun μ => 2 * g.cellSide * t μ) := fun μ =>
  Or.inl ⟨t μ, fun x => by
    simp only [translate, Pi.add_apply, ReflectionGrid.coordShift]
    ring⟩
theorem statement_holds : ReflectionGroupCoordinates.Statement := by
  intro D g
  refine ⟨fun r hr => isProductOfCoordMaps_of_mem g hr,
    fun r hr => exists_mem_eq_of_isProductOfCoordMaps g hr,
    fun r hr => orientationSign_eq_neg_one_pow g (isProductOfCoordMaps_of_mem g hr),
    fun r hr s hs => ?_, fun r hr => image_walls g hr, ?_, ?_, fun t => ?_⟩
  · exact orientationSign_comp g (isProductOfCoordMaps_of_mem g hr) (isProductOfCoordMaps_of_mem g hs)
  · rintro r hr _ ⟨k, rfl⟩
    obtain ⟨k', hk', -⟩ := exists_cell_image_index g (isProductOfCoordMaps_of_mem g hr) k
    exact ⟨k', (image_cell_eq g hk').symm⟩
  · rintro _ ⟨k, rfl⟩ _ ⟨k', rfl⟩
    exact existsUnique_image_cell g k k'
  · obtain ⟨s, hs, hst⟩ := exists_mem_eq_of_isProductOfCoordMaps g (isProductOfCoordMaps_translate g t)
    refine ⟨s, hs, hst, ?_⟩
    rw [hst, orientationSign_eq_prod_of_diagonal (fun _ => 1) (fun μ => 2 * g.cellSide * t μ)
      (fun x μ => ?_)]
    · simp
    · simp [translate]
end ReflectionGroupCoordinatesProof
end YangMills.Construction.ChessboardTori
end
