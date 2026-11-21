import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.ChessboardTori.MirrorPeriodicWeightsAsCellFunctions
import YangMills.Construction.ChessboardTori.PeriodicRealizationOnARectangularTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori.ReflectionPeriodicWeightsAsCellFunctions
open InfiniteLattice (AmbientSpace)
theorem signedConj_one_apply (z : ℂ) : Conventions.signedConj 1 z = z := by
  simp [Conventions.signedConj]
theorem signedConj_negOne_apply (z : ℂ) : Conventions.signedConj (-1) z = starRingEnd ℂ z := by
  rw [Conventions.signedConj, if_neg (by decide)]
theorem signedConj_signedConj (s t : ℤˣ) (z : ℂ) :
    Conventions.signedConj s (Conventions.signedConj t z) = Conventions.signedConj (s * t) z := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
    simp [signedConj_one_apply, signedConj_negOne_apply]
section Group
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem comp_inv_eq_signedConjFun
    (hχ : ∃ χ : g.reflectionGroup →* ℤˣ, ∀ r : g.reflectionGroup, χ r = orientationSign r.1)
    (hθ : ∀ (μ : Fin 4) (k : ℤ), orientationSign (g.reflect μ k) = -1) {W : AmbientSpace → ℂ}
    (hM : ∀ (μ : Fin 4) (k : ℤ), W ∘ g.reflect μ k = fun x => starRingEnd ℂ (W x))
    (r : Equiv.Perm AmbientSpace) (hr : r ∈ g.reflectionGroup) :
    W ∘ ⇑(r⁻¹) = Conventions.signedConjFun (orientationSign r) W := by
  obtain ⟨χ, hχ⟩ := hχ
  induction hr using Subgroup.closure_induction with
  | mem r hr =>
    obtain ⟨⟨μ, k⟩, rfl⟩ := hr
    have e : ⇑(g.reflectPerm μ k)⁻¹ = g.reflect μ k := rfl
    have e' : orientationSign ⇑(g.reflectPerm μ k) = -1 := hθ μ k
    rw [e, e', hM μ k]
    funext x
    exact (signedConj_negOne_apply _).symm
  | one =>
    have e : orientationSign ⇑(1 : Equiv.Perm AmbientSpace) = 1 := by
      have h := hχ 1
      rw [map_one] at h
      exact h.symm
    rw [e]
    funext x
    exact (signedConj_one_apply _).symm
  | mul r s hr hs ihr ihs =>
    have e : orientationSign ⇑(r * s) = orientationSign ⇑r * orientationSign ⇑s := by
      have h := hχ (⟨r, hr⟩ * ⟨s, hs⟩)
      rw [map_mul, hχ, hχ] at h
      exact h.symm
    funext x
    have h₁ := congrFun ihs (r⁻¹ x)
    have h₂ := congrFun ihr x
    simp only [Function.comp, Conventions.signedConjFun] at h₁ h₂ ⊢
    rw [e, mul_inv_rev, Equiv.Perm.mul_apply, h₁, h₂, signedConj_signedConj, mul_comm]
  | inv r hr ih =>
    have e : orientationSign ⇑(r⁻¹) = orientationSign ⇑r := by
      have h := hχ (⟨r, hr⟩⁻¹)
      rw [map_inv, hχ, Int.units_inv_eq_self] at h
      exact h.symm
    funext x
    have h₁ := congrFun ih (r x)
    have e₀ : r⁻¹ (r x) = x := by simp
    simp only [Function.comp, Conventions.signedConjFun, e₀] at h₁ ⊢
    rw [e, inv_inv, h₁, signedConj_signedConj, Int.units_mul_self, signedConj_one_apply]
end Group
section Cells
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem cell_eq_pi (k : Fin 4 → ℤ) : g.cell k = Set.pi univ fun μ =>
    Icc (g.origin μ + g.cellSide * k μ) (g.origin μ + g.cellSide * k μ + g.cellSide) := by
  ext y
  simp only [ReflectionGrid.cell, mem_ofPred_eq, mem_Icc, mem_pi, mem_univ, true_implies]
  exact forall_congr' fun μ => by constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
theorem mem_interior_cell_iff (k : Fin 4 → ℤ) (x : AmbientSpace) :
    x ∈ interior (g.cell k) ↔ ∀ μ, x μ - (g.origin μ + g.cellSide * k μ) ∈ Ioo 0 g.cellSide := by
  rw [cell_eq_pi, interior_pi_set finite_univ]
  simp only [interior_Icc, mem_pi, mem_univ, true_implies, mem_Ioo]
  exact forall_congr' fun μ => by constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
theorem isBounded_cell (k : Fin 4 → ℤ) : Bornology.IsBounded (g.cell k) := by
  rw [cell_eq_pi]
  exact (isCompact_univ_pi fun μ => isCompact_Icc).isBounded
theorem cellIndex_unique {k k' : Fin 4 → ℤ} {x : AmbientSpace} (h : x ∈ interior (g.cell k))
    (h' : x ∈ interior (g.cell k')) : k = k' := by
  have hs := g.cellSide_pos
  rw [mem_interior_cell_iff] at h h'
  funext μ
  obtain ⟨h₁, h₂⟩ := h μ
  obtain ⟨h₃, h₄⟩ := h' μ
  have a₁ : (k μ : ℝ) < k' μ + 1 := by
    have : g.cellSide * k μ < g.cellSide * (k' μ + 1) := by linarith
    exact lt_of_mul_lt_mul_left this hs.le
  have a₂ : (k' μ : ℝ) < k μ + 1 := by
    have : g.cellSide * k' μ < g.cellSide * (k μ + 1) := by linarith
    exact lt_of_mul_lt_mul_left this hs.le
  have b₁ : k μ < k' μ + 1 := by exact_mod_cast a₁
  have b₂ : k' μ < k μ + 1 := by exact_mod_cast a₂
  omega
theorem not_mem_walls_of_mem_interior {k : Fin 4 → ℤ} {x : AmbientSpace}
    (h : x ∈ interior (g.cell k)) : x ∉ g.walls := by
  have hs := g.cellSide_pos
  rw [mem_interior_cell_iff] at h
  intro hx
  obtain ⟨μ, m, hm⟩ := mem_iUnion₂.mp hx
  have hm' : x μ = g.origin μ + m * g.cellSide := hm
  obtain ⟨h₁, h₂⟩ := h μ
  rw [hm'] at h₁ h₂
  have a₁ : (k μ : ℝ) < m := by
    have : g.cellSide * k μ < g.cellSide * m := by linarith
    exact lt_of_mul_lt_mul_left this hs.le
  have a₂ : (m : ℝ) < k μ + 1 := by
    have : g.cellSide * m < g.cellSide * (k μ + 1) := by linarith
    exact lt_of_mul_lt_mul_left this hs.le
  have b₁ : k μ < m := by exact_mod_cast a₁
  have b₂ : m < k μ + 1 := by exact_mod_cast a₂
  omega
theorem coord_ne_wall_of_not_mem {x : AmbientSpace} (h : x ∉ g.walls) (μ : Fin 4) (m : ℤ) :
    x μ ≠ g.origin μ + m * g.cellSide := fun e => h (mem_iUnion₂.mpr ⟨μ, m, e⟩)
theorem mem_interior_of_mem_cell {k : Fin 4 → ℤ} {x : AmbientSpace} (hx : x ∈ g.cell k)
    (h : x ∉ g.walls) : x ∈ interior (g.cell k) := by
  rw [mem_interior_cell_iff]
  intro μ
  obtain ⟨h₁, h₂⟩ := hx μ
  have n₁ := coord_ne_wall_of_not_mem g h μ (k μ)
  have n₂ := coord_ne_wall_of_not_mem g h μ (k μ + 1)
  push_cast at n₂
  refine ⟨lt_of_le_of_ne h₁ fun e => n₁ ?_, lt_of_le_of_ne h₂ fun e => n₂ ?_⟩ <;> linarith
theorem exists_mem_interior_cell {x : AmbientSpace} (h : x ∉ g.walls) :
    ∃ k, x ∈ interior (g.cell k) := by
  have hs := g.cellSide_pos
  refine ⟨fun μ => ⌊(x μ - g.origin μ) / g.cellSide⌋, mem_interior_of_mem_cell g (fun μ => ?_) h⟩
  have e : x μ - g.origin μ = (x μ - g.origin μ) / g.cellSide * g.cellSide := by
    field_simp
  have h₁ := Int.floor_le ((x μ - g.origin μ) / g.cellSide)
  have h₂ := Int.lt_floor_add_one ((x μ - g.origin μ) / g.cellSide)
  have a₁ := mul_le_mul_of_nonneg_right h₁ hs.le
  have a₂ := mul_lt_mul_of_pos_right h₂ hs
  constructor <;> nlinarith
end Cells
section Plaquettes
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem faceCorner_coord (p : D.Plaquette) {z : InfiniteLattice.LatticePoint D.mesh}
    (hz : z ∈ D.faceCorners p) (ν : Fin 4) :
    (z : AmbientSpace) ν = (p.corner : AmbientSpace) ν ∨
      ((ν = p.lowAxis ∨ ν = p.highAxis) ∧
        (z : AmbientSpace) ν = (p.corner : AmbientSpace) ν + D.mesh) := by
  have hne := p.lowAxis_lt_highAxis.ne
  have s₁ : ∀ μ, ((InfiniteLattice.axisStep D.mesh μ : InfiniteLattice.LatticePoint D.mesh) :
      AmbientSpace) ν = if ν = μ then D.mesh else 0 := fun μ => by
    simp [InfiniteLattice.axisStep, Pi.single_apply]
  simp only [ChessboardSetup.faceCorners, mem_insert_iff, mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · simp only [AddSubgroup.coe_add, Pi.add_apply, s₁]
    split_ifs with e
    · exact Or.inr ⟨Or.inl e, rfl⟩
    · exact Or.inl (add_zero _)
  · simp only [AddSubgroup.coe_add, Pi.add_apply, s₁]
    split_ifs with e₁ e₂ e₂
    · exact absurd (e₁.symm.trans e₂) hne
    · exact Or.inr ⟨Or.inl e₁, add_zero _⟩
    · exact Or.inr ⟨Or.inr e₂, by ring⟩
    · exact Or.inl (by ring)
  · simp only [AddSubgroup.coe_add, Pi.add_apply, s₁]
    split_ifs with e
    · exact Or.inr ⟨Or.inr e, rfl⟩
    · exact Or.inl (add_zero _)
theorem center_apply (p : D.Plaquette) (ν : Fin 4) :
    p.center ν = (p.corner : AmbientSpace) ν + (if ν = p.lowAxis then D.mesh / 2 else 0) +
      (if ν = p.highAxis then D.mesh / 2 else 0) := by
  simp only [InfiniteLattice.ElementaryPlaquette.center, Pi.add_apply, Pi.single_apply]
theorem wall_eq_midpoint {x : InfiniteLattice.LatticePoint D.mesh} {μ : Fin 4} {k : ℤ}
    (h₁ : (x : AmbientSpace) μ < g.origin μ + k * g.cellSide)
    (h₂ : g.origin μ + k * g.cellSide < (x : AmbientSpace) μ + D.mesh) :
    g.origin μ + k * g.cellSide = (x : AmbientSpace) μ + D.mesh / 2 := by
  have ha := D.mesh_pos
  obtain ⟨n, hn⟩ := x.2
  obtain ⟨i, hi⟩ := g.origin_mem μ
  obtain ⟨m, hm⟩ : ∃ m : ℤ, g.origin μ + k * g.cellSide = ((m : ℝ) + 1 / 2) * D.mesh :=
    ⟨i + k * g.cellRatio, by rw [hi, g.cellSide_eq]; push_cast; ring⟩
  rw [hm] at h₁ h₂ ⊢
  rw [hn μ] at h₁ h₂ ⊢
  have a₁ : (n μ : ℝ) < (m : ℝ) + 1 / 2 := lt_of_mul_lt_mul_right h₁ ha.le
  have a₂ : (m : ℝ) + 1 / 2 < (n μ : ℝ) + 1 :=
    lt_of_mul_lt_mul_right (by linarith) ha.le
  have b₁ : 2 * n μ < 2 * m + 1 := by
    have : ((2 * n μ : ℤ) : ℝ) < ((2 * m + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have b₂ : 2 * m + 1 < 2 * n μ + 2 := by
    have : ((2 * m + 1 : ℤ) : ℝ) < ((2 * n μ + 2 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have e : m = n μ := by omega
  rw [e]
  ring
theorem straddles_or_inside_cell (hsite : ∀ x ∈ D.gridPoints, x ∉ g.walls) (p : D.Plaquette) :
    g.HasEdgeStraddlingWall p ∨ ∃ k,
      (∀ z ∈ D.faceCorners p, (z : AmbientSpace) ∈ interior (g.cell k)) ∧
        p.center ∈ interior (g.cell k) := by
  have ha := D.mesh_pos
  have hne := p.lowAxis_lt_highAxis.ne
  by_cases h : g.HasEdgeStraddlingWall p
  · exact Or.inl h
  refine Or.inr ?_
  obtain ⟨k, hk⟩ := exists_mem_interior_cell g (hsite _ p.corner.2)
  have hbase := (mem_interior_cell_iff g k _).mp hk
  have hstep : ∀ ν, (ν = p.lowAxis ∨ ν = p.highAxis) →
      (p.corner : AmbientSpace) ν + D.mesh - (g.origin ν + g.cellSide * k ν) < g.cellSide := by
    intro ν hν
    by_contra hc
    have hc := not_lt.mp hc
    have hcoord : ((p.corner + InfiniteLattice.axisStep D.mesh ν :
        InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) ν =
        (p.corner : AmbientSpace) ν + D.mesh := by
      simp [InfiniteLattice.axisStep]
    have hH := coord_ne_wall_of_not_mem g
      (hsite _ (p.corner + InfiniteLattice.axisStep D.mesh ν).2) ν (k ν + 1)
    rw [hcoord] at hH
    push_cast at hH
    have hb := hbase ν
    apply h
    refine ⟨InfiniteLattice.Link.forwardFrom p.corner ν, ⟨Or.inl rfl, ?_⟩, ν, k ν + 1,
      Or.inl ⟨?_, ?_⟩⟩
    · rcases hν with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr rfl))
    · change (p.corner : AmbientSpace) ν < _
      push_cast
      linarith [hb.2]
    · change _ < ((p.corner + InfiniteLattice.axisStep D.mesh ν :
        InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) ν
      rw [hcoord]
      push_cast
      refine lt_of_le_of_ne ?_ hH.symm
      linarith
  refine ⟨k, fun z hz => ?_, ?_⟩
  · rw [mem_interior_cell_iff]
    intro ν
    rcases faceCorner_coord p hz ν with e | ⟨hν, e⟩
    · rw [e]
      exact hbase ν
    · rw [e]
      exact ⟨by linarith [(hbase ν).1], hstep ν hν⟩
  · rw [mem_interior_cell_iff]
    intro ν
    rw [center_apply]
    have hb := hbase ν
    by_cases e₁ : ν = p.lowAxis
    · have e₂ : ν ≠ p.highAxis := fun e => hne (e₁.symm.trans e)
      have := hstep ν (Or.inl e₁)
      simp only [if_pos e₁, if_neg e₂]
      constructor <;> linarith [hb.1]
    · by_cases e₂ : ν = p.highAxis
      · have := hstep ν (Or.inr e₂)
        simp only [if_neg e₁, if_pos e₂]
        constructor <;> linarith [hb.1]
      · simp only [if_neg e₁, if_neg e₂]
        constructor <;> linarith [hb.1, hb.2]
theorem center_mem_walls_of_straddle {p : D.Plaquette} (h : g.HasEdgeStraddlingWall p) :
    p.center ∈ g.walls := by
  have ha := D.mesh_pos
  have hne := p.lowAxis_lt_highAxis.ne
  obtain ⟨b, ⟨ht, hh⟩, μ, k, hc⟩ := h
  have key : ∀ {x y : InfiniteLattice.LatticePoint D.mesh}, x ∈ D.faceCorners p →
      y ∈ D.faceCorners p → (x : AmbientSpace) μ < g.origin μ + k * g.cellSide →
      g.origin μ + k * g.cellSide < (y : AmbientSpace) μ →
      p.center μ = g.origin μ + k * g.cellSide := by
    intro x y hx hy h₁ h₂
    rcases faceCorner_coord p hx μ with ex | ⟨_, ex⟩ <;>
      rcases faceCorner_coord p hy μ with ey | ⟨hμ, ey⟩
    · exfalso
      linarith
    · rw [ex] at h₁
      rw [ey] at h₂
      have e := wall_eq_midpoint g h₁ h₂
      rw [center_apply, e]
      rcases hμ with e' | e'
      · rw [if_pos e', if_neg (fun e'' => hne (e'.symm.trans e''))]
        ring
      · rw [if_neg (fun e'' => hne (e''.symm.trans e')), if_pos e']
        ring
    · exfalso
      linarith
    · exfalso
      linarith
  refine mem_iUnion₂.mpr ⟨μ, k, ?_⟩
  rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact key ht hh h₁ h₂
  · exact key hh ht h₁ h₂
theorem finite_faces_center_in_cell (k : Fin 4 → ℤ) :
    {p : D.Plaquette | p.center ∈ interior (g.cell k)}.Finite := by
  classical
  have ha := D.mesh_pos
  let c : AmbientSpace := fun μ => g.origin μ + g.cellSide * k μ
  let A : Set (Fin 4 → ℤ) :=
    Set.pi univ fun μ => Icc ⌊(c μ - D.mesh) / D.mesh⌋ ⌈(c μ + g.cellSide) / D.mesh⌉
  have hA : A.Finite := Set.Finite.pi fun μ => finite_Icc _ _
  let φ : D.Plaquette → AmbientSpace × Fin 4 × Fin 4 :=
    fun p => ((p.corner : AmbientSpace), p.lowAxis, p.highAxis)
  have hinj : Function.Injective φ := by
    intro p q h
    simp only [φ, Prod.mk.injEq] at h
    exact InfiniteLattice.ElementaryPlaquette.ext (Subtype.ext h.1) h.2.1 h.2.2
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine Set.Finite.subset
    ((hA.image fun n μ => (n μ : ℝ) * D.mesh).prod (finite_univ (α := Fin 4 × Fin 4))) ?_
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨n, hn⟩ := p.corner.2
  refine ⟨⟨n, fun μ _ => ?_, funext fun μ => (hn μ).symm⟩, mem_univ _⟩
  have hb := (mem_interior_cell_iff g k _).mp hp μ
  rw [center_apply, hn μ] at hb
  have t₁ : 0 ≤ (if μ = p.lowAxis then D.mesh / 2 else (0 : ℝ)) ∧
      (if μ = p.lowAxis then D.mesh / 2 else (0 : ℝ)) ≤ D.mesh / 2 := by
    split_ifs <;> constructor <;> linarith
  have t₂ : 0 ≤ (if μ = p.highAxis then D.mesh / 2 else (0 : ℝ)) ∧
      (if μ = p.highAxis then D.mesh / 2 else (0 : ℝ)) ≤ D.mesh / 2 := by
    split_ifs <;> constructor <;> linarith
  refine ⟨?_, ?_⟩
  · have h1 : (⌊(c μ - D.mesh) / D.mesh⌋ : ℝ) ≤ (n μ : ℝ) := by
      refine (Int.floor_le _).trans ?_
      rw [div_le_iff₀ ha]
      simp only [c]
      linarith [hb.1, t₁.2, t₂.2]
    exact_mod_cast h1
  · have h1 : (n μ : ℝ) ≤ (⌈(c μ + g.cellSide) / D.mesh⌉ : ℝ) := by
      refine le_trans ?_ (Int.le_ceil _)
      rw [le_div_iff₀ ha]
      simp only [c]
      linarith [hb.2, t₁.1, t₂.1]
    exact_mod_cast h1
end Plaquettes
section Algebra
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def boundaryLinks {a : ℝ} (p : InfiniteLattice.ElementaryPlaquette a) :
    Fin 4 → InfiniteLattice.Link a :=
  ![InfiniteLattice.Link.forwardFrom p.corner p.lowAxis,
    InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.lowAxis) p.highAxis,
    InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.highAxis) p.lowAxis,
    InfiniteLattice.Link.forwardFrom p.corner p.highAxis]
def energyOfFour (v : Fin 4 → Matrices.ComplexMatrix2.specialUnitary) : ℝ :=
  1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
    ((v 0 * v 1 * (v 2)⁻¹ * (v 3)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
      Matrices.ComplexMatrix2)).re
theorem continuous_energyOfFour : Continuous energyOfFour := by
  have h : Continuous fun v : Fin 4 → Matrices.ComplexMatrix2.specialUnitary =>
      v 0 * v 1 * (v 2)⁻¹ * (v 3)⁻¹ := by fun_prop
  have h' : Continuous fun v : Fin 4 → Matrices.ComplexMatrix2.specialUnitary =>
      ((v 0 * v 1 * (v 2)⁻¹ * (v 3)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
        Matrices.ComplexMatrix2) := continuous_subtype_val.comp h
  have htr : Continuous fun v : Fin 4 → Matrices.ComplexMatrix2.specialUnitary =>
      Matrices.ComplexMatrix2.fullTrace
        ((v 0 * v 1 * (v 2)⁻¹ * (v 3)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
          Matrices.ComplexMatrix2) := h'.matrix_trace
  unfold energyOfFour
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp htr))
theorem faceEnergy_eq_energyOfFour {a : ℝ}
    (U : InfiniteLattice.Link a → Matrices.ComplexMatrix2.specialUnitary)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    InfiniteLattice.faceEnergy U p = energyOfFour fun i => U (boundaryLinks p i) := rfl
theorem boundaryLinks_mem {S : Set AmbientSpace} {p : D.Plaquette}
    (hc : ∀ z ∈ D.faceCorners p, (z : AmbientSpace) ∈ interior S) (i : Fin 4) :
    boundaryLinks p i ∈ ReflectionGrid.interiorLinks (D := D) S := by
  have c00 : (p.corner : AmbientSpace) ∈ interior S := hc _ (Or.inl rfl)
  have c10 : ((p.corner + InfiniteLattice.axisStep D.mesh p.lowAxis :
      InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) ∈ interior S :=
    hc _ (Or.inr (Or.inl rfl))
  have c11 : ((p.corner + InfiniteLattice.axisStep D.mesh p.lowAxis +
      InfiniteLattice.axisStep D.mesh p.highAxis : InfiniteLattice.LatticePoint D.mesh) :
        AmbientSpace) ∈ interior S := hc _ (Or.inr (Or.inr (Or.inl rfl)))
  have c01 : ((p.corner + InfiniteLattice.axisStep D.mesh p.highAxis :
      InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) ∈ interior S :=
    hc _ (Or.inr (Or.inr (Or.inr rfl)))
  have c11' : ((p.corner + InfiniteLattice.axisStep D.mesh p.highAxis +
      InfiniteLattice.axisStep D.mesh p.lowAxis : InfiniteLattice.LatticePoint D.mesh) :
        AmbientSpace) ∈ interior S := by rwa [add_right_comm]
  fin_cases i
  · exact ⟨c00, c10⟩
  · exact ⟨c10, c11⟩
  · exact ⟨c01, c11'⟩
  · exact ⟨c00, c01⟩
def extendByOne (S : Set AmbientSpace)
    (u : ReflectionGrid.interiorLinks (D := D) S → Conventions.StandingParameters.gaugeGroup)
    (b : D.Link) : Matrices.ComplexMatrix2.specialUnitary :=
  open Classical in
  if h : b ∈ ReflectionGrid.interiorLinks (D := D) S then u ⟨b, h⟩ else 1
theorem measurable_extendByOne (S : Set AmbientSpace) (b : D.Link) :
    Measurable fun u : ReflectionGrid.interiorLinks (D := D) S →
      Conventions.StandingParameters.gaugeGroup => extendByOne S u b := by
  by_cases h : b ∈ ReflectionGrid.interiorLinks (D := D) S
  · simp only [extendByOne, h, dite_true]
    exact measurable_pi_apply _
  · simp only [extendByOne, h, dite_false]
    exact measurable_const
variable {W : AmbientSpace → ℂ}
theorem eq_zero_of_straddle (hW : g.IsReflectionPeriodic W) {p : D.Plaquette}
    (h : g.HasEdgeStraddlingWall p) : W p.center = 0 :=
  hW.2.2 p h
theorem center_not_mem_walls_of_ne_zero (hsite : ∀ x ∈ D.gridPoints, x ∉ g.walls)
    (hW : g.IsReflectionPeriodic W) {p : D.Plaquette} (h : W p.center ≠ 0) :
    p.center ∉ g.walls := by
  rcases straddles_or_inside_cell g hsite p with hc | ⟨k, -, hb⟩
  · exact absurd (eq_zero_of_straddle g hW hc) h
  · exact not_mem_walls_of_mem_interior g hb
theorem smeared_mul_indicator_eq (hsite : ∀ x ∈ D.gridPoints, x ∉ g.walls)
    (hW : g.IsReflectionPeriodic W) (k : Fin 4 → ℤ) (U : D.GaugeField) :
    D.smeared (W * (g.cell k).indicator 1) U =
      ∑ᶠ p ∈ {p : D.Plaquette | p.center ∈ interior (g.cell k)},
        W p.center * (InfiniteLattice.faceEnergy U p : ℂ) := by
  rw [finsum_mem_def]
  refine finsum_congr fun p => ?_
  by_cases hin : p.center ∈ interior (g.cell k)
  · rw [indicator_of_mem (show p ∈ {p : D.Plaquette | p.center ∈ interior (g.cell k)} from hin)]
    have hS : p.center ∈ g.cell k := interior_subset hin
    simp only [Pi.mul_apply, indicator_of_mem hS, Pi.one_apply, mul_one, Complex.real_smul]
    ring
  · rw [indicator_of_notMem
      (show p ∉ {p : D.Plaquette | p.center ∈ interior (g.cell k)} from hin)]
    by_cases hS : p.center ∈ g.cell k
    · have hz : W p.center = 0 := by
        by_contra hne
        exact hin (mem_interior_of_mem_cell g hS
          (center_not_mem_walls_of_ne_zero g hsite hW hne))
      simp [hz]
    · simp [indicator_of_notMem hS]
theorem faceCorners_mem_interior (hsite : ∀ x ∈ D.gridPoints, x ∉ g.walls) {k : Fin 4 → ℤ}
    {p : D.Plaquette} (hp : p.center ∈ interior (g.cell k)) :
    ∀ z ∈ D.faceCorners p, (z : AmbientSpace) ∈ interior (g.cell k) := by
  rcases straddles_or_inside_cell g hsite p with hc | ⟨k', hk', hb⟩
  · exact absurd (center_mem_walls_of_straddle g hc) (not_mem_walls_of_mem_interior g hp)
  · rw [cellIndex_unique g hp hb]
    exact hk'
theorem exp_smeared_mem_cellObservables (hsite : ∀ x ∈ D.gridPoints, x ∉ g.walls)
    (hW : g.IsReflectionPeriodic W) (k : Fin 4 → ℤ) :
    (fun U : D.GaugeField => Complex.exp (D.smeared (W * (g.cell k).indicator 1) U)) ∈
      ReflectionGrid.cellObservables (D := D) (g.cell k) := by
  classical
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hfin := finite_faces_center_in_cell g k
  obtain ⟨A, hA⟩ : ∃ A : ℝ, ∀ v, ‖energyOfFour v‖ ≤ A := by
    obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn
      continuous_energyOfFour.continuousOn
    exact ⟨A, fun v => hA v (mem_univ _)⟩
  obtain ⟨C, hC⟩ := hW.1
  refine ⟨fun u => Complex.exp (∑ p ∈ hfin.toFinset, W p.center *
      (energyOfFour (fun i => extendByOne (g.cell k) u (boundaryLinks p i)) : ℂ)), ?_,
    ⟨Real.exp (∑ _p ∈ hfin.toFinset, C * A), fun u => ?_⟩, ?_⟩
  · refine Complex.measurable_exp.comp (Finset.measurable_sum _ fun p _ => ?_)
    exact (Complex.measurable_ofReal.comp (continuous_energyOfFour.measurable.comp
      (measurable_pi_lambda _ fun i => measurable_extendByOne _ _))).const_mul _
  · rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    refine (Complex.re_le_norm _).trans
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_))
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul (hC _) (hA _) (norm_nonneg _) ((norm_nonneg _).trans (hC p.center))
  · funext U
    change Complex.exp (D.smeared (W * (g.cell k).indicator 1) U) = Complex.exp _
    rw [smeared_mul_indicator_eq g hsite hW, finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine congrArg Complex.exp (Finset.sum_congr rfl fun p hp => ?_)
    have hp' : p.center ∈ interior (g.cell k) := by simpa using hp
    have hU : (fun i => extendByOne (g.cell k) (ReflectionGrid.restrictField (g.cell k) U)
        (boundaryLinks p i)) = fun i => U (boundaryLinks p i) := by
      funext i
      have hm := boundaryLinks_mem (faceCorners_mem_interior g hsite hp') i
      simp only [extendByOne, hm, dite_true]
      rfl
    rw [faceEnergy_eq_energyOfFour, hU]
theorem transportTo_exp_smeared (hexp : D.ExpSmearedRules)
    (hcarry : ∀ S ∈ g.cellSet, ∀ S' ∈ g.cellSet, ∃ r : g.reflectionGroup, r.1 '' S = S')
    (hA : ∀ r : g.reflectionGroup,
      W ∘ ⇑(r.1⁻¹) = Conventions.signedConjFun (orientationSign r.1) W)
    (hb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (k k' : Fin 4 → ℤ) :
    g.transportTo (g.cell k) (g.cell k')
        (fun U : D.GaugeField => Complex.exp (D.smeared (W * (g.cell k).indicator 1) U)) =
      fun U => Complex.exp (D.smeared (W * (g.cell k').indicator 1) U) := by
  classical
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hbound : ∀ (V : AmbientSpace → ℂ), (∀ x, ‖V x‖ ≤ C) → ∀ l : Fin 4 → ℤ,
      (∃ C : ℝ, ∀ x, ‖(V * (g.cell l).indicator 1 : AmbientSpace → ℂ) x‖ ≤ C) ∧
        ChessboardSetup.HasBoundedSupport (V * (g.cell l).indicator 1) := by
    intro V hV l
    refine ⟨⟨C, fun x => ?_⟩, g.cell l, isBounded_cell g l, fun x hx => ?_⟩
    · by_cases hx : x ∈ g.cell l
      · simpa [indicator_of_mem hx] using hV x
      · simpa [indicator_of_notMem hx] using hC0
    · simp [indicator_of_notMem hx]
  have hr : (g.mover (g.cell k) (g.cell k')).1 '' g.cell k = g.cell k' :=
    Classical.epsilon_spec (p := fun r : g.reflectionGroup => r.1 '' g.cell k = g.cell k')
      (hcarry _ ⟨k, rfl⟩ _ ⟨k', rfl⟩)
  set r := g.mover (g.cell k) (g.cell k') with hrdef
  obtain ⟨b₁, c₁⟩ := hbound W hC k
  have hrule := (hexp (g.toLatticeSym r) _ _ b₁ c₁ b₁ c₁).1
  have hinvmap : invMap (g.toLatticeSym r).toFun = ⇑(r.1⁻¹) := by
    funext x
    have hinj : Function.Injective (g.toLatticeSym r).toFun := r.1.injective
    have e : (g.toLatticeSym r).toFun (r.1⁻¹ x) = x := r.1.apply_symm_apply x
    change Function.invFun (g.toLatticeSym r).toFun x = r.1⁻¹ x
    conv_lhs => rw [← e]
    exact Function.leftInverse_invFun hinj _
  have hcomp : (W * (g.cell k).indicator 1) ∘ invMap (g.toLatticeSym r).toFun =
      Conventions.signedConjFun (orientationSign r.1) W * (g.cell k').indicator 1 := by
    rw [hinvmap]
    funext x
    have h₁ := congrFun (hA r) x
    have h₂ : r.1⁻¹ x ∈ g.cell k ↔ x ∈ g.cell k' := by
      rw [← hr]
      constructor
      · intro h
        exact ⟨_, h, r.1.apply_symm_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    simp only [Function.comp, Pi.mul_apply] at h₁ ⊢
    rw [h₁]
    by_cases hx : x ∈ g.cell k'
    · rw [indicator_of_mem hx, indicator_of_mem (h₂.mpr hx)]
      rfl
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (h₂.mp h))]
  change Conventions.signedConjFun (orientationSign (g.mover (g.cell k) (g.cell k')).1)
    ((g.toLatticeSym (g.mover (g.cell k) (g.cell k'))).actOn _) = _
  rw [← hrdef, hrule, hcomp]
  rcases Int.units_eq_one_or (orientationSign r.1) with hs | hs
  · rw [hs]
    have e : Conventions.signedConjFun (1 : ℤˣ) W = W :=
      funext fun x => signedConj_one_apply _
    rw [e]
    funext U
    exact signedConj_one_apply _
  · rw [hs]
    have hV : ∀ x, ‖Conventions.signedConjFun (-1 : ℤˣ) W x‖ ≤ C := fun x => by
      simpa [Conventions.signedConjFun, signedConj_negOne_apply] using hC x
    obtain ⟨b₂, c₂⟩ := hbound _ hV k'
    have hconj := (hexp (g.toLatticeSym r) _ _ b₂ c₂ b₂ c₂).2.1
    have e : (fun x => starRingEnd ℂ
        ((Conventions.signedConjFun (-1 : ℤˣ) W * (g.cell k').indicator 1 :
          AmbientSpace → ℂ) x)) = W * (g.cell k').indicator 1 := by
      funext x
      by_cases hx : x ∈ g.cell k'
      · simp [Conventions.signedConjFun, signedConj_negOne_apply, indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
    rw [e] at hconj
    rw [← hconj]
    funext U
    exact signedConj_negOne_apply _
end Algebra
section Torus
variable {D : ChessboardSetup}
theorem finite_gridPoint (P : PeriodSubgroup D) : Finite P.GridPoint := by
  have hM : ∀ μ, P.mult μ ≠ 0 := fun μ => by
    have := P.four_le_mult μ
    omega
  have : Finite ↥(Icc (0 : Fin 4 → ℤ) fun μ => |P.mult μ|) := (Set.finite_Icc _ _).to_subtype
  refine Finite.of_surjective (α := ↥(Icc (0 : Fin 4 → ℤ) fun μ => |P.mult μ|))
    (fun r => (⟨BoxTorus.projection P.sideLengths fun μ =>
      (r.1 μ : ℝ) * PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ), ⟨r.1, rfl⟩⟩ : P.GridPoint)) ?_
  rintro ⟨x, n, rfl⟩
  refine ⟨⟨fun μ => n μ % P.mult μ, Set.mem_Icc.mpr
    ⟨fun μ => Int.emod_nonneg _ (hM μ), fun μ => (Int.emod_lt_abs _ (hM μ)).le⟩⟩, ?_⟩
  refine Subtype.ext (funext fun μ => ?_)
  refine (QuotientAddGroup.eq_iff_sub_mem).mpr ?_
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨-(n μ / P.mult μ), ?_⟩
  have h := Int.emod_add_mul_ediv (n μ) (P.mult μ)
  have h' : (n μ : ℝ) = ((n μ % P.mult μ : ℤ) : ℝ) +
      ((P.mult μ : ℤ) : ℝ) * ((n μ / P.mult μ : ℤ) : ℝ) := by
    exact_mod_cast h.symm
  have hs : P.sideLengths μ =
      (P.mult μ : ℝ) * PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ) := rfl
  rw [zsmul_eq_mul, hs]
  show _ = ((n μ % P.mult μ : ℤ) : ℝ) * PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ) -
    (n μ : ℝ) * PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)
  rw [h']
  push_cast
  ring
theorem finite_face (P : PeriodSubgroup D) : Finite P.Face := by
  have := finite_gridPoint P
  exact Finite.of_injective (fun p : P.Face => (p.corner, p.dir₁, p.dir₂)) fun p p' hp => by
    simp only [Prod.mk.injEq] at hp
    exact BoxTorus.Face.ext hp.1 hp.2.1 hp.2.2
theorem center_shiftPlaquette (p : D.Plaquette) (v : InfiniteLattice.LatticePoint D.mesh) :
    (D.shiftPlaquette p v).center = p.center + (v : AmbientSpace) := by
  funext μ
  simp only [InfiniteLattice.ElementaryPlaquette.center, ChessboardSetup.shiftPlaquette,
    AddSubgroup.coe_add, Pi.add_apply]
  ring
variable (g : ReflectionGrid D) {P : PeriodSubgroup D} {n : Fin 4 → ℤ}
theorem period_coords (hs : ∀ μ, (P.mult μ : ℝ) * D.mesh = n μ * g.cellSide)
    {v : InfiniteLattice.LatticePoint D.mesh} (hv : v ∈ D.periodSubgroupOfGrid P.mult) :
    ∃ z : Fin 4 → ℤ, ∀ μ, (v : AmbientSpace) μ = z μ * (n μ * g.cellSide) := by
  have hx : (v : AmbientSpace) ∈ D.periodGroup P.mult := hv
  have h : ∀ μ, ∃ z : ℤ, z • D.periodLengths P.mult μ = (v : AmbientSpace) μ := fun μ =>
    AddSubgroup.mem_zmultiples_iff.mp (((AddSubgroup.mem_pi _).mp hx) μ (mem_univ μ))
  choose z hz using h
  refine ⟨z, fun μ => ?_⟩
  rw [← hz μ, zsmul_eq_mul, ChessboardSetup.periodLengths, hs μ]
theorem exists_period_of_coords (hs : ∀ μ, (P.mult μ : ℝ) * D.mesh = n μ * g.cellSide)
    (z : Fin 4 → ℤ) :
    ∃ v ∈ D.periodSubgroupOfGrid P.mult, ∀ μ, (v : AmbientSpace) μ = z μ * (n μ * g.cellSide) := by
  have hv : (fun μ => (z μ : ℝ) * (n μ * g.cellSide)) ∈ D.periodGroup P.mult :=
    (AddSubgroup.mem_pi _).mpr fun μ _ => AddSubgroup.mem_zmultiples_iff.mpr
      ⟨z μ, by rw [zsmul_eq_mul, ChessboardSetup.periodLengths, hs μ]⟩
  exact ⟨⟨_, D.periodGroup_le_gridPoints _ hv⟩, hv, fun μ => rfl⟩
theorem sum_over_cells_eq_sum_faces (hpos : ∀ μ, 0 < n μ)
    (hs : ∀ μ, (P.mult μ : ℝ) * D.mesh = n μ * g.cellSide)
    (hsame : ∀ p p' : D.Plaquette, P.projFace p = P.projFace p' ↔
      ∃ v ∈ D.periodSubgroupOfGrid P.mult, p' = D.shiftPlaquette p v)
    (hsurj : Function.Surjective P.projFace)
    (I : Finset (Fin 4 → ℤ)) (hI : ∀ k, k ∈ I ↔ ∀ μ, 0 ≤ k μ ∧ k μ < n μ) (f : P.Face → ℂ)
    (hf : ∀ p : D.Plaquette, f (P.projFace p) ≠ 0 → p.center ∉ g.walls) :
    ∑ k ∈ I, ∑ᶠ p ∈ {p : D.Plaquette | p.center ∈ interior (g.cell k)},
      f (P.projFace p) = ∑ᶠ q, f q := by
  classical
  have hsd := g.cellSide_pos
  have hdisj : (I : Set (Fin 4 → ℤ)).PairwiseDisjoint
      (fun k => {p : D.Plaquette | p.center ∈ interior (g.cell k)}) :=
    fun k _ k' _ hne => Set.disjoint_left.mpr fun p hp hp' => hne (cellIndex_unique g hp hp')
  have hunion := finsum_mem_biUnion (f := fun p => f (P.projFace p)) hdisj I.finite_toSet
    (fun k _ => finite_faces_center_in_cell g k)
  rw [finsum_mem_coe_finset] at hunion
  rw [← hunion]
  have hinj : InjOn P.projFace (⋃ k ∈ (I : Set (Fin 4 → ℤ)),
      {p : D.Plaquette | p.center ∈ interior (g.cell k)}) := by
    intro p hp p' hp' e
    obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.mp hp
    obtain ⟨k', hk', hpk'⟩ := mem_iUnion₂.mp hp'
    obtain ⟨v, hv, rfl⟩ := (hsame p p').mp e
    obtain ⟨z, hz⟩ := period_coords g hs hv
    have hk := (hI k).mp hk
    have hk' := (hI k').mp hk'
    have hz0 : ∀ μ, z μ = 0 := by
      intro μ
      have hb := (mem_interior_cell_iff g k _).mp hpk μ
      have hb' := (mem_interior_cell_iff g k' _).mp hpk' μ
      rw [center_shiftPlaquette] at hb'
      have e' : (p.center + (v : AmbientSpace)) μ = p.center μ + z μ * (n μ * g.cellSide) := by
        rw [Pi.add_apply, hz]
      rw [e'] at hb'
      have hN : 0 < (n μ : ℝ) * g.cellSide := mul_pos (by exact_mod_cast hpos μ) hsd
      have l₁ : 0 ≤ g.cellSide * (k μ : ℝ) := mul_nonneg hsd.le (by exact_mod_cast (hk μ).1)
      have l₂ : g.cellSide * (k μ : ℝ) + g.cellSide ≤ n μ * g.cellSide := by
        have : ((k μ : ℝ) + 1) ≤ n μ := by exact_mod_cast (hk μ).2
        nlinarith
      have l₃ : 0 ≤ g.cellSide * (k' μ : ℝ) := mul_nonneg hsd.le (by exact_mod_cast (hk' μ).1)
      have l₄ : g.cellSide * (k' μ : ℝ) + g.cellSide ≤ n μ * g.cellSide := by
        have : ((k' μ : ℝ) + 1) ≤ n μ := by exact_mod_cast (hk' μ).2
        nlinarith
      obtain ⟨u₁, u₂⟩ := hb
      obtain ⟨u₃, u₄⟩ := hb'
      have a₁ : (z μ : ℝ) * (n μ * g.cellSide) < 1 * (n μ * g.cellSide) := by linarith
      have a₂ : (-1 : ℝ) * (n μ * g.cellSide) < (z μ : ℝ) * (n μ * g.cellSide) := by linarith
      have b₁ : (z μ : ℝ) < 1 := lt_of_mul_lt_mul_right a₁ hN.le
      have b₂ : (-1 : ℝ) < z μ := lt_of_mul_lt_mul_right a₂ hN.le
      have c₁ : z μ < 1 := by exact_mod_cast b₁
      have c₂ : -1 < z μ := by exact_mod_cast b₂
      omega
    have hv0 : v = 0 := Subtype.ext (funext fun μ => by rw [hz μ, hz0 μ]; simp)
    subst hv0
    exact InfiniteLattice.ElementaryPlaquette.ext (add_zero _).symm rfl rfl
  rw [← finsum_mem_image (f := f) hinj, finsum_mem_def]
  refine finsum_congr fun q => ?_
  by_cases hq : f q = 0
  · rw [indicator_apply]
    split_ifs
    · rfl
    · exact hq.symm
  · refine indicator_of_mem ?_ _
    obtain ⟨p₀, rfl⟩ := hsurj q
    have hoff := hf p₀ hq
    obtain ⟨k₀, hk₀⟩ := exists_mem_interior_cell g hoff
    obtain ⟨v, hv, hvc⟩ := exists_period_of_coords g hs (fun μ => -(k₀ μ / n μ))
    refine ⟨D.shiftPlaquette p₀ v, mem_iUnion₂.mpr ⟨fun μ => k₀ μ % n μ, ?_, ?_⟩,
      ((hsame p₀ _).mpr ⟨v, hv, rfl⟩).symm⟩
    · exact Finset.mem_coe.mpr ((hI _).mpr fun μ =>
        ⟨Int.emod_nonneg _ (hpos μ).ne', Int.emod_lt_of_pos _ (hpos μ)⟩)
    · change (D.shiftPlaquette p₀ v).center ∈ interior (g.cell _)
      rw [center_shiftPlaquette, mem_interior_cell_iff]
      intro μ
      have hb := (mem_interior_cell_iff g k₀ _).mp hk₀ μ
      have hmod : ((k₀ μ % n μ : ℤ) : ℝ) = k₀ μ - n μ * ((k₀ μ / n μ : ℤ) : ℝ) := by
        have h := Int.emod_add_mul_ediv (k₀ μ) (n μ)
        have h' : ((k₀ μ % n μ : ℤ) : ℝ) + (n μ : ℝ) * ((k₀ μ / n μ : ℤ) : ℝ) = k₀ μ := by
          exact_mod_cast h
        linarith
      have e : (p₀.center + (v : AmbientSpace)) μ -
          (g.origin μ + g.cellSide * ((k₀ μ % n μ : ℤ) : ℝ)) =
          p₀.center μ - (g.origin μ + g.cellSide * k₀ μ) := by
        rw [Pi.add_apply, hvc μ, hmod]
        push_cast
        ring
      show (p₀.center + (v : AmbientSpace)) μ -
        (g.origin μ + g.cellSide * ((k₀ μ % n μ : ℤ) : ℝ)) ∈ Ioo 0 g.cellSide
      rw [e]
      exact hb
end Torus
theorem statement_holds (h₁ : BoxTorusQuotient.Statement)
    (h₂ : GridBasicProperties.Statement) (h₃ : ReflectionGroupAndTransport.Statement) :
    ReflectionPeriodicWeightsAsCellFunctions.Statement := by
  intro O W hW
  obtain ⟨⟨hsite, -, -⟩, -, hexp, -, -, -, -⟩ := h₂ O.toChessboardSetup O.grid
  obtain ⟨-, hcarry, ⟨hχ, hθ, htrans⟩, -⟩ := h₃ O.toChessboardSetup O.grid O.isCoarse
  have hcarry' : ∀ S ∈ O.grid.cellSet, ∀ S' ∈ O.grid.cellSet,
      ∃ r : O.grid.reflectionGroup, r.1 '' S = S' :=
    fun S hS S' hS' => (hcarry S hS S' hS').exists
  have hA : ∀ r : O.grid.reflectionGroup,
      W ∘ ⇑(r.1⁻¹) = Conventions.signedConjFun (orientationSign r.1) W :=
    fun r => comp_inv_eq_signedConjFun O.grid hχ hθ hW.2.1 r.1 r.2
  have hperiod : ∀ (x : AmbientSpace) (k : Fin 4 → ℤ),
      W (x + TestFunctions.latticeTranslate (2 * O.grid.cellSide) k) = W x := by
    intro x k
    obtain ⟨r, hr, hrt, hsg⟩ := htrans k
    have h := congrFun (hA ⟨r, hr⟩) (r x)
    have e₀ : r⁻¹ (r x) = x := by simp
    have e₁ : r x = x + TestFunctions.latticeTranslate (2 * O.grid.cellSide) k := by
      rw [hrt]
      rfl
    simp only [Function.comp, Conventions.signedConjFun, e₀, hsg, signedConj_one_apply] at h
    rw [← e₁]
    exact h.symm
  refine ⟨hA, hperiod, fun p => ?_, fun S hS => ?_, fun n S hS => ?_⟩
  · refine ⟨?_, center_mem_walls_of_straddle O.grid, ?_⟩
    · rcases straddles_or_inside_cell O.grid hsite p with h | ⟨k, hc, hb⟩
      · exact Or.inl h
      · exact Or.inr ⟨_, ⟨k, rfl⟩, hc, hb⟩
    · rintro ⟨_, ⟨k, rfl⟩, -, hb⟩
      exact not_mem_walls_of_mem_interior O.grid hb
  · obtain ⟨k, rfl⟩ := hS
    refine ⟨fun U => smeared_mul_indicator_eq O.grid hsite hW k U,
      exp_smeared_mem_cellObservables O.grid hsite hW k, ?_⟩
    rintro _ ⟨k', rfl⟩
    exact transportTo_exp_smeared O.grid hexp hcarry' hA hW.1 k k'
  · obtain ⟨k₀, rfl⟩ := hS
    obtain ⟨hfwd, hevery, hsame, -, -, hext, -, hper, -⟩ := (h₁ O).1 n.coord n.two_le
    have hPeq : O.periodSubgroupOf n = O.grid.boxPeriods n.coord n.two_le := rfl
    unfold CoupledGrid.chessboardPartitionOn
    rw [hPeq]
    generalize hP : O.grid.boxPeriods n.coord n.two_le = P at *
    have hs : ∀ μ, (P.mult μ : ℝ) * O.toChessboardSetup.mesh = n.coord μ * O.grid.cellSide := by
      intro μ
      rw [← hP, O.grid.cellSide_eq]
      simp only [ReflectionGrid.boxPeriods]
      push_cast
      ring
    have hpos : ∀ μ, 0 < n.coord μ := fun μ => by
      have := n.two_le μ
      omega
    have hI : ∀ k, k ∈ n.indexBox ↔ ∀ μ, 0 ≤ k μ ∧ k μ < n.coord μ := by
      intro k
      simp [EvenIndexVector.indexBox, Fintype.mem_piFinset, Finset.mem_Ico]
    have hPerW : ∀ x, ∀ v ∈ P.subgroup, W (x + v) = W x := by
      intro x v hv
      have hv' := (hper n.even).1 hv
      have h : ∀ μ, ∃ z : ℤ, z • (2 * O.grid.cellSide) = v μ := fun μ =>
        AddSubgroup.mem_zmultiples_iff.mp (((AddSubgroup.mem_pi _).mp hv') μ (mem_univ μ))
      choose z hz using h
      have e : v = TestFunctions.latticeTranslate (2 * O.grid.cellSide) z := funext fun μ => by
        rw [← hz μ, zsmul_eq_mul, TestFunctions.latticeTranslate, mul_comm]
      rw [e]
      exact hperiod x z
    have hread : ∀ p : O.toChessboardSetup.Plaquette,
        P.descend W (P.faceCenter (P.projFace p)) = W p.center := by
      intro p
      rw [(hfwd.2.2 p).2]
      exact P.descend_proj hPerW _
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    have hsum := sum_over_cells_eq_sum_faces O.grid hpos hs hsame.2.2 hevery.2.2 n.indexBox hI
      (fun q => P.descend W (P.faceCenter q) * (P.faceEnergy U q : ℂ))
      (fun p hne => center_not_mem_walls_of_ne_zero O.grid hsite hW fun h0 => hne (by
        simp only [hread, h0, zero_mul]))
    have hobs : ∀ k, O.toChessboardSetup.smeared (W * (O.grid.cell k).indicator 1)
        (P.liftGaugeField U) =
        ∑ᶠ p ∈ {p : O.toChessboardSetup.Plaquette | p.center ∈ interior (O.grid.cell k)},
          P.descend W (P.faceCenter (P.projFace p)) *
            (P.faceEnergy U (P.projFace p) : ℂ) := by
      intro k
      rw [smeared_mul_indicator_eq O.grid hsite hW]
      refine finsum_mem_congr rfl fun p _ => ?_
      rw [hread, hext.2.2.1 U p]
    have hprod : ∏ k ∈ n.indexBox, O.grid.transportTo (O.grid.cell k₀) (O.grid.cell k)
          (O.cellExpWeight W (O.grid.cell k₀)) (P.liftGaugeField U) =
        Complex.exp (∑ᶠ q, P.descend W (P.faceCenter q) * (P.faceEnergy U q : ℂ)) := by
      rw [← hsum, Complex.exp_sum]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← hobs k]
      exact congrFun (transportTo_exp_smeared O.grid hexp hcarry' hA hW.1 k₀ k) _
    have hfinite := finite_face P
    have hfin : Fintype P.Face := Fintype.ofFinite _
    have haction : P.wilsonAction U = ∑ q, P.faceEnergy U q := finsum_eq_sum_of_fintype _
    have hsplit : (∑ᶠ q, (P.descend W (P.faceCenter q) - (O.β : ℂ)) *
        (P.faceEnergy U q : ℂ)) =
        (∑ᶠ q, P.descend W (P.faceCenter q) * (P.faceEnergy U q : ℂ)) +
          -(O.β : ℂ) * (P.wilsonAction U : ℂ) := by
      rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, haction]
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ => by ring
    show (∏ k ∈ n.indexBox, O.grid.transportTo (O.grid.cell k₀) (O.grid.cell k)
          (O.cellExpWeight W (O.grid.cell k₀)) (P.liftGaugeField U)) *
        Complex.exp (-(O.β : ℂ) * (P.wilsonAction U : ℂ)) = Complex.exp _
    rw [hprod, ← Complex.exp_add, hsplit]
end YangMills.Construction.ChessboardTori.ReflectionPeriodicWeightsAsCellFunctions
end
