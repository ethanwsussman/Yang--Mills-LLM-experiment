import YangMills.Construction.Towers.IndicesNearAPointOfTheFinestLattice
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.FinestLatticeNeighbours
open YangMills.Construction.PeriodicOperators
theorem floor_div_mem_Icc_five {a x y : ℝ} (ha : 0 < a) (n : ℤ) (hx : x = n * a)
    (h : |x - y| ≤ 2 * a) : ⌊x / a⌋ ∈ Finset.Icc ⌈y / a - 2⌉ (⌈y / a - 2⌉ + 4) := by
  have hxa : x / a = n := by rw [hx]; field_simp
  rw [hxa, Int.floor_intCast, Finset.mem_Icc]
  obtain ⟨h₁, h₂⟩ := abs_le.mp h
  rw [hx] at h₁ h₂
  have hlo : y / a - 2 ≤ n := by
    rw [sub_le_iff_le_add, div_le_iff₀ ha]
    linarith
  have hhi : (n : ℝ) ≤ y / a + 2 := by
    have : (n : ℝ) - 2 ≤ y / a := by
      rw [le_div_iff₀ ha]
      linarith
    linarith
  have hc : y / a - 2 ≤ (⌈y / a - 2⌉ : ℝ) := Int.le_ceil _
  refine ⟨Int.ceil_le.mpr hlo, ?_⟩
  have : (n : ℝ) ≤ ((⌈y / a - 2⌉ + 4 : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this
theorem latticePoint_eq_of_floor {a : ℝ} (ha : 0 < a) (x x' : InfiniteLattice.LatticePoint a)
    (h : ∀ μ, ⌊(x : InfiniteLattice.AmbientSpace) μ / a⌋ = ⌊(x' : InfiniteLattice.AmbientSpace) μ / a⌋) :
    x = x' := by
  obtain ⟨n, hn⟩ : ∃ n : Fin 4 → ℤ, ∀ μ, (x : InfiniteLattice.AmbientSpace) μ = (n μ : ℝ) * a := x.2
  obtain ⟨n', hn'⟩ : ∃ n : Fin 4 → ℤ, ∀ μ, (x' : InfiniteLattice.AmbientSpace) μ = (n μ : ℝ) * a := x'.2
  apply Subtype.ext
  funext μ
  have e := h μ
  rw [hn μ, hn' μ, mul_div_cancel_right₀ _ ha.ne', mul_div_cancel_right₀ _ ha.ne',
    Int.floor_intCast, Int.floor_intCast] at e
  rw [hn μ, hn' μ, e]
theorem encard_withinBox_le {a : ℝ} (ha : 0 < a) (y : InfiniteLattice.AmbientSpace) {J : Type}
    (pt : J → InfiniteLattice.LatticePoint a) (d : J → Fin 4 × Fin 4) (D : Finset (Fin 4 × Fin 4))
    (hD : ∀ j, d j ∈ D) (hcard : D.card ≤ 6)
    (hinj : ∀ j j', pt j = pt j' → d j = d j' → j = j') :
    {ι : Fin 3 × J | WithinBox (2 * a) (pt ι.2 : InfiniteLattice.AmbientSpace) y}.encard ≤ 11250 := by
  classical
  let P : Finset (Fin 4 → ℤ) :=
    Fintype.piFinset fun μ => Finset.Icc ⌈y μ / a - 2⌉ (⌈y μ / a - 2⌉ + 4)
  let T : Finset (Fin 3 × (Fin 4 → ℤ) × (Fin 4 × Fin 4)) := Finset.univ ×ˢ P ×ˢ D
  let f : Fin 3 × J → Fin 3 × (Fin 4 → ℤ) × (Fin 4 × Fin 4) := fun ι =>
    (ι.1, (fun μ => ⌊(pt ι.2 : InfiniteLattice.AmbientSpace) μ / a⌋), d ι.2)
  have hmaps : MapsTo f
      {ι : Fin 3 × J | WithinBox (2 * a) (pt ι.2 : InfiniteLattice.AmbientSpace) y} (T : Set _) := by
    intro ι hι
    obtain ⟨n, hn⟩ : ∃ n : Fin 4 → ℤ, ∀ μ, (pt ι.2 : InfiniteLattice.AmbientSpace) μ = (n μ : ℝ) * a :=
      (pt ι.2).2
    simp only [T, P, f, Finset.coe_product, Finset.coe_univ, mem_prod, mem_univ, true_and,
      Finset.mem_coe, Fintype.mem_piFinset]
    exact ⟨fun μ => floor_div_mem_Icc_five ha (n μ) (hn μ) (hι μ), hD _⟩
  have hinjOn : InjOn f
      {ι : Fin 3 × J | WithinBox (2 * a) (pt ι.2 : InfiniteLattice.AmbientSpace) y} := by
    rintro ⟨c, j⟩ - ⟨c', j'⟩ - e
    simp only [f, Prod.mk.injEq] at e
    obtain ⟨e₁, e₂, e₃⟩ := e
    have : j = j' := hinj j j' (latticePoint_eq_of_floor ha _ _ (congrFun e₂)) e₃
    rw [e₁, this]
  have hT : T.card ≤ 11250 := by
    have h5 : ∀ m : ℤ, (Finset.Icc m (m + 4)).card = 5 := fun m => by
      rw [Int.card_Icc, show m + 4 + 1 - m = 5 by ring]
      rfl
    have hP : P.card = 625 := by
      simp only [P, Fintype.card_piFinset, h5, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      norm_num
    simp only [T, Finset.card_product, Finset.card_univ, Fintype.card_fin, hP]
    omega
  calc {ι : Fin 3 × J | WithinBox (2 * a) (pt ι.2 : InfiniteLattice.AmbientSpace) y}.encard
      ≤ (T : Set _).encard := encard_le_encard_of_injOn hmaps hinjOn
    _ = (T.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard T
    _ ≤ 11250 := by exact_mod_cast hT
theorem neighbourCountBound : NeighbourCountBound := by
  intro L hL k _ y
  have ha : 0 < YangMills.Construction.Tower.meshAt L k 0 := by
    have hL0 : 0 < L := by
      have := hL.2
      omega
    exact zpow_pos (by exact_mod_cast hL0) _
  refine ⟨?_, ?_, ?_⟩
  · exact encard_withinBox_le ha y (J := YangMills.Construction.Tower.FullSpace.Vertex L k 0) id
      (fun _ => (0, 0)) {(0, 0)} (fun _ => Finset.mem_singleton_self _) (by simp) (fun j j' e _ => e)
  · refine encard_withinBox_le ha y (J := PosEdge L k 0)
      (fun b => b.1.initial) (fun b => (Classical.choose b.2, 0))
      (Finset.univ.filter fun q => q.2 = 0) (fun b => by simp) (by decide) ?_
    intro b b' e e'
    have h₁ := Classical.choose_spec b.2
    have h₂ := Classical.choose_spec b'.2
    have e₂ : Classical.choose b.2 = Classical.choose b'.2 := (Prod.mk.inj e').1
    rw [e₂] at h₁
    apply Subtype.ext
    apply InfiniteLattice.Link.ext e
    have e₃ : b.1.terminal - b.1.initial = b'.1.terminal - b'.1.initial := h₁.trans h₂.symm
    have e₄ : b.1.initial = b'.1.initial := e
    rw [e₄] at e₃
    exact sub_left_injective e₃
  · refine encard_withinBox_le ha y (J := YangMills.Construction.Tower.FullSpace.Face L k 0)
      (fun p => p.corner) (fun p => (p.lowAxis, p.highAxis))
      (Finset.univ.filter fun q => q.1 < q.2) (fun p => by simpa using p.lowAxis_lt_highAxis)
      (by decide) ?_
    intro p p' e e'
    obtain ⟨e₁, e₂⟩ := Prod.mk.inj e'
    exact InfiniteLattice.ElementaryPlaquette.ext e e₁ e₂
end YangMills.Construction.Tower.FullSpace.FinestLatticeNeighbours
end
