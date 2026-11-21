import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import YangMills.Construction.InfiniteLattice.GroupOfLatticeIsometriesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace LatticeQuotients
def coordVector (μ : Fin 4) : Fin 4 → ℤ := fun κ => if κ = μ then 1 else 0
def faceOffset (μ ν : Fin 4) : Fin 4 → Fin 4 → ℤ :=
  ![0, coordVector μ, coordVector μ + coordVector ν, coordVector ν]
theorem faceOffset_sub_abs_le : ∀ μ ν i j κ : Fin 4,
    |(faceOffset μ ν i - faceOffset μ ν j) κ| ≤ 3 := by
  decide +kernel
theorem faceOffset_add_sub_abs_le : ∀ μ ν ρ i j κ : Fin 4,
    |(faceOffset μ ν i + coordVector ρ - faceOffset μ ν j) κ| ≤ 3 := by
  decide +kernel
theorem faceOffset_injective : ∀ μ ν i j : Fin 4, μ < ν →
    faceOffset μ ν i = faceOffset μ ν j → i = j := by
  decide +kernel
theorem faceOffset_eq_zero_of_two_steps : ∀ μ ν μ' ν' i j k : Fin 4, μ < ν → μ' < ν' →
    faceOffset μ ν i + coordVector μ' = faceOffset μ ν j →
    faceOffset μ ν i + coordVector ν' = faceOffset μ ν k → i = 0 ∧ μ = μ' ∧ ν = ν' := by
  decide +kernel
def nearOffset : Option (ℤˣ × Fin 4) → Fin 4 → ℤ
  | none => 0
  | some (ε, μ) => (ε : ℤ) • coordVector μ
theorem nearOffset_abs_le (o : Option (ℤˣ × Fin 4)) (κ : Fin 4) : |nearOffset o κ| ≤ 1 := by
  rcases o with _ | ⟨ε, μ⟩
  · simp [nearOffset]
  · rcases Int.units_eq_one_or ε with rfl | rfl <;> by_cases h : κ = μ <;>
      simp [nearOffset, coordVector, h]
theorem nearOffset_injective : Function.Injective nearOffset := by
  have hunit : ∀ ε : ℤˣ, (ε : ℤ) ≠ 0 := fun ε => ε.ne_zero
  intro o o' h
  rcases o with _ | ⟨ε, μ⟩ <;> rcases o' with _ | ⟨ε', μ'⟩
  · rfl
  · have := congrFun h μ'
    simp [nearOffset, coordVector] at this
    exact absurd this.symm (hunit ε')
  · have := congrFun h μ
    simp [nearOffset, coordVector] at this
  · have h1 := congrFun h μ
    by_cases hμ : μ = μ'
    · subst hμ
      have : (ε : ℤ) = ε' := by simpa [nearOffset, coordVector] using h1
      rw [Units.ext this]
    · exfalso
      simp [nearOffset, coordVector, hμ] at h1
variable (D : ChessboardSetup)
theorem mesh_pos : 0 < D.mesh := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardSetup.mesh_pos <;> assumption
def gridHom : (Fin 4 → ℤ) →+ InfiniteLattice.LatticePoint D.mesh where
  toFun := D.gridVector
  map_zero' := Subtype.ext (funext fun μ => by simp [ChessboardSetup.gridVector])
  map_add' n m := Subtype.ext (funext fun μ => by simp [ChessboardSetup.gridVector, add_mul])
theorem gridHom_apply (n : Fin 4 → ℤ) (μ : Fin 4) :
    ((gridHom D n : InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) μ = (n μ : ℝ) * D.mesh :=
  rfl
theorem gridHom_bijective : Function.Bijective (gridHom D) := by
  have ha := (mesh_pos D).ne'
  constructor
  · intro n m h
    funext μ
    have h1 := congrFun (congrArg Subtype.val h) μ
    rw [gridHom_apply, gridHom_apply] at h1
    exact_mod_cast mul_right_cancel₀ ha h1
  · rintro ⟨x, n, hn⟩
    exact ⟨n, Subtype.ext (funext fun μ => (hn μ).symm)⟩
theorem axisStep_eq_gridHom (μ : Fin 4) :
    InfiniteLattice.axisStep D.mesh μ = gridHom D (coordVector μ) := by
  refine Subtype.ext (funext fun κ => ?_)
  rw [gridHom_apply]
  by_cases h : κ = μ
  · subst h
    simp [InfiniteLattice.axisStep, coordVector]
  · simp [InfiniteLattice.axisStep, coordVector, h]
theorem mem_periodGroup_iff (s : Fin 4 → ℤ) (x : AmbientSpace) :
    x ∈ D.periodGroup s ↔ ∀ μ, ∃ k : ℤ, x μ = (k : ℝ) * ((s μ : ℝ) * D.mesh) := by
  constructor
  · intro hx μ
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (((AddSubgroup.mem_pi _).mp hx) μ (mem_univ μ))
    refine ⟨k, ?_⟩
    rw [← hk, ChessboardSetup.periodLengths, zsmul_eq_mul]
  · intro h
    refine (AddSubgroup.mem_pi _).mpr fun μ _ => ?_
    obtain ⟨k, hk⟩ := h μ
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k, ?_⟩
    rw [hk, ChessboardSetup.periodLengths, zsmul_eq_mul]
theorem gridHom_mem_periodSubgroupOfGrid_iff (s : Fin 4 → ℤ) (n : Fin 4 → ℤ) :
    gridHom D n ∈ D.periodSubgroupOfGrid s ↔ ∀ μ, s μ ∣ n μ := by
  have ha := (mesh_pos D).ne'
  change ((gridHom D n : InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) ∈ D.periodGroup s ↔ _
  rw [mem_periodGroup_iff]
  refine forall_congr' fun μ => ?_
  rw [gridHom_apply]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : (n μ : ℝ) = (s μ : ℝ) * k := by
      apply mul_right_cancel₀ ha
      rw [hk]
      ring
    exact_mod_cast this
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    push_cast
    ring
section Group
variable {G : Type} [AddCommGroup G] (q : InfiniteLattice.LatticePoint D.mesh →+ G)
theorem map_gridHom_ne_zero {s : Fin 4 → ℤ} (hs : ∀ μ, 4 ≤ s μ)
    (hk : q.ker = D.periodSubgroupOfGrid s ∨ q.ker = ⊥) (n : Fin 4 → ℤ) (hn : n ≠ 0)
    (hb : ∀ μ, |n μ| ≤ 3) : q (gridHom D n) ≠ 0 := by
  intro h0
  have hmem : gridHom D n ∈ q.ker := (AddMonoidHom.mem_ker).mpr h0
  apply hn
  rcases hk with hk | hk
  · rw [hk, gridHom_mem_periodSubgroupOfGrid_iff] at hmem
    funext μ
    exact Int.eq_zero_of_abs_lt_dvd (hmem μ) (lt_of_le_of_lt (hb μ) (by linarith [hs μ]))
  · rw [hk, AddSubgroup.mem_bot] at hmem
    exact (gridHom_bijective D).1 (hmem.trans (map_zero (gridHom D)).symm)
variable {D q}
theorem eq_of_map_gridHom_eq
    (hq : ∀ n : Fin 4 → ℤ, n ≠ 0 → (∀ μ, |n μ| ≤ 3) → q (gridHom D n) ≠ 0)
    {m n : Fin 4 → ℤ} (hb : ∀ κ, |(m - n) κ| ≤ 3)
    (h : q (gridHom D m) = q (gridHom D n)) : m = n := by
  by_contra hne
  apply hq (m - n) (sub_ne_zero.mpr hne) hb
  rw [map_sub, map_sub, h, sub_self]
variable (D q)
theorem signedAxisStep_one (μ : Fin 4) :
    D.signedAxisStep q 1 μ = q (gridHom D (coordVector μ)) := by
  simp [ChessboardSetup.signedAxisStep, axisStep_eq_gridHom]
theorem nearNeighbourhood_eq (o : Option (ℤˣ × Fin 4)) :
    D.nearNeighbourhood q o = q (gridHom D (nearOffset o)) := by
  rcases o with _ | ⟨ε, μ⟩
  · simp [ChessboardSetup.nearNeighbourhood, nearOffset]
  · simp only [ChessboardSetup.nearNeighbourhood, ChessboardSetup.signedAxisStep, nearOffset,
      axisStep_eq_gridHom, map_zsmul]
theorem faceVertices_eq (x : G) (μ ν i : Fin 4) :
    D.faceVertices q x μ ν i = x + q (gridHom D (faceOffset μ ν i)) := by
  fin_cases i <;> simp [ChessboardSetup.faceVertices, faceOffset, signedAxisStep_one, add_assoc]
variable {D q}
theorem quotientRegularity
    (hq : ∀ n : Fin 4 → ℤ, n ≠ 0 → (∀ μ, |n μ| ≤ 3) → q (gridHom D n) ≠ 0) :
    D.QuotientRegularity q := by
  have hinj : Function.Injective (D.nearNeighbourhood q) := by
    intro o o' h
    rw [nearNeighbourhood_eq, nearNeighbourhood_eq] at h
    refine nearOffset_injective (eq_of_map_gridHom_eq hq (fun κ => ?_) h)
    have h1 := abs_le.mp (nearOffset_abs_le o κ)
    have h2 := abs_le.mp (nearOffset_abs_le o' κ)
    exact abs_le.mpr ⟨by simp only [Pi.sub_apply]; linarith [h1.1, h2.2],
      by simp only [Pi.sub_apply]; linarith [h1.2, h2.1]⟩
  have huniq : ∀ (x x' : G) (ε ε' : ℤˣ) (μ μ' : Fin 4), x' - x = D.signedAxisStep q ε μ →
      x' - x = D.signedAxisStep q ε' μ' → ε = ε' ∧ μ = μ' := by
    intro x x' ε ε' μ μ' h1 h2
    have := hinj (show D.nearNeighbourhood q (some (ε, μ)) = D.nearNeighbourhood q (some (ε', μ'))
      from h1.symm.trans h2)
    simpa using this
  refine ⟨hq, ⟨hinj, huniq, ?_⟩, ?_, ?_⟩
  · intro x x' ε μ h
    have hneg : x - x' = D.signedAxisStep q (-ε) μ := by
      rw [← neg_sub, h]
      simp [ChessboardSetup.signedAxisStep]
    refine ⟨hneg, ?_⟩
    rcases Int.units_eq_one_or ε with rfl | rfl
    · refine Or.inl ⟨⟨μ, h⟩, ?_⟩
      rintro ⟨ν, hν⟩
      exact absurd (huniq x' x (-1) 1 μ ν hneg hν).1 (by decide)
    · rw [neg_neg] at hneg
      refine Or.inr ⟨⟨μ, hneg⟩, ?_⟩
      rintro ⟨ν, hν⟩
      exact absurd (huniq x x' (-1) 1 μ ν h hν).1 (by decide)
  · intro x μ ν hμν i j h
    rw [faceVertices_eq, faceVertices_eq] at h
    exact faceOffset_injective μ ν i j hμν
      (eq_of_map_gridHom_eq hq (faceOffset_sub_abs_le μ ν i j) (add_left_cancel h))
  · intro x x' μ ν μ' ν' hμν hμν' hr
    have m0 : x' ∈ range (D.faceVertices q x' μ' ν') := ⟨0, rfl⟩
    have m1 : x' + D.signedAxisStep q 1 μ' ∈ range (D.faceVertices q x' μ' ν') := ⟨1, rfl⟩
    have m3 : x' + D.signedAxisStep q 1 ν' ∈ range (D.faceVertices q x' μ' ν') := ⟨3, rfl⟩
    rw [← hr] at m0 m1 m3
    obtain ⟨i, hi⟩ := m0
    obtain ⟨j, hj⟩ := m1
    obtain ⟨k, hk⟩ := m3
    rw [faceVertices_eq] at hi hj hk
    rw [signedAxisStep_one, ← hi] at hj hk
    have e1 : faceOffset μ ν i + coordVector μ' = faceOffset μ ν j := by
      refine eq_of_map_gridHom_eq hq (faceOffset_add_sub_abs_le μ ν μ' i j) ?_
      apply add_left_cancel (a := x)
      rw [hj, map_add, map_add, add_assoc]
    have e2 : faceOffset μ ν i + coordVector ν' = faceOffset μ ν k := by
      refine eq_of_map_gridHom_eq hq (faceOffset_add_sub_abs_le μ ν ν' i k) ?_
      apply add_left_cancel (a := x)
      rw [hk, map_add, map_add, add_assoc]
    obtain ⟨h0, h1, h2⟩ := faceOffset_eq_zero_of_two_steps μ ν μ' ν' i j k hμν hμν' e1 e2
    refine ⟨?_, h1, h2⟩
    subst h0
    rw [← hi]
    simp [faceOffset]
end Group
theorem exists_round_minimizer (u c : ℝ) (hc : 0 < c) :
    ∃ k : ℤ, ∀ k' : ℤ, |u + (k : ℝ) * c| ≤ |u + (k' : ℝ) * c| := by
  have e : ∀ z : ℤ, |u + (z : ℝ) * c| = c * |-u / c - (z : ℝ)| := by
    intro z
    have : u + (z : ℝ) * c = -(c * (-u / c - (z : ℝ))) := by
      field_simp
      ring
    rw [this, abs_neg, abs_mul, abs_of_pos hc]
  refine ⟨round (-u / c), fun k' => ?_⟩
  rw [e, e]
  exact mul_le_mul_of_nonneg_left (round_le _ k') hc.le
theorem exists_nearest_period (s : Fin 4 → ℤ) (hs : ∀ μ, 4 ≤ s μ) (u : AmbientSpace) :
    ∃ v ∈ D.periodGroup s, ∀ w ∈ D.periodGroup s,
      TorusMetric.euclidNormVec (u + v) ≤ TorusMetric.euclidNormVec (u + w) := by
  have hc : ∀ μ, 0 < (s μ : ℝ) * D.mesh := fun μ => by
    have : (0 : ℝ) < s μ := by exact_mod_cast (by linarith [hs μ] : 0 < s μ)
    exact mul_pos this (mesh_pos D)
  choose k hk using fun μ => exists_round_minimizer (u μ) _ (hc μ)
  refine ⟨fun μ => (k μ : ℝ) * ((s μ : ℝ) * D.mesh),
    (mem_periodGroup_iff D s _).mpr fun μ => ⟨k μ, rfl⟩, fun w hw => ?_⟩
  choose k' hk' using (mem_periodGroup_iff D s w).mp hw
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => ?_)
  simp only [Pi.add_apply]
  rw [hk' μ]
  exact sq_le_sq.mpr (hk μ (k' μ))
theorem periodicDistance_isLeast (s : Fin 4 → ℤ) (hs : ∀ μ, 4 ≤ s μ) (y y' : AmbientSpace) :
    IsLeast ((fun v : AmbientSpace => TorusMetric.euclidNormVec (y - y' + v)) ''
      (D.periodGroup s : Set AmbientSpace)) (D.periodicDistance s y y') := by
  obtain ⟨v, hv, hmin⟩ := exists_nearest_period D s hs (y - y')
  have hl : IsLeast ((fun v : AmbientSpace => TorusMetric.euclidNormVec (y - y' + v)) ''
      (D.periodGroup s : Set AmbientSpace)) (TorusMetric.euclidNormVec (y - y' + v)) := by
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmin w hw
  have he : D.periodicDistance s y y' = TorusMetric.euclidNormVec (y - y' + v) := hl.csInf_eq
  rw [he]
  exact hl
theorem periodicDistance_congr (s : Fin 4 → ℤ) (y₁ y₂ y₁' y₂' : AmbientSpace)
    (h : y₁ - y₂ ∈ D.periodGroup s) (h' : y₁' - y₂' ∈ D.periodGroup s) :
    D.periodicDistance s y₁ y₁' = D.periodicDistance s y₂ y₂' := by
  unfold ChessboardSetup.periodicDistance
  congr 1
  ext t
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v + (y₁ - y₂) - (y₁' - y₂'), sub_mem (add_mem hv h) h', ?_⟩
    show TorusMetric.euclidNormVec _ = TorusMetric.euclidNormVec _
    congr 1
    abel
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v - (y₁ - y₂) + (y₁' - y₂'), add_mem (sub_mem hv h) h', ?_⟩
    show TorusMetric.euclidNormVec _ = TorusMetric.euclidNormVec _
    congr 1
    abel
theorem eq_zero_of_euclidNormVec_eq_zero {x : AmbientSpace}
    (h : TorusMetric.euclidNormVec x = 0) : x = 0 := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetryGroup.eq_zero_of_euclidNormVec_eq_zero <;> assumption
theorem sub_mem_periodGroup_of_periodicDistance_eq_zero (s : Fin 4 → ℤ) (hs : ∀ μ, 4 ≤ s μ)
    (y y' : AmbientSpace) (h : D.periodicDistance s y y' = 0) : y - y' ∈ D.periodGroup s := by
  obtain ⟨v, hv, hval⟩ := (periodicDistance_isLeast D s hs y y').1
  have h0 : y - y' + v = 0 := eq_zero_of_euclidNormVec_eq_zero (hval.trans h)
  rw [eq_neg_of_add_eq_zero_left h0]
  exact neg_mem hv
theorem card_quotient_periodSubgroupOfGrid (s : Fin 4 → ℤ) (hs : ∀ μ, 4 ≤ s μ) :
    (Nat.card (InfiniteLattice.LatticePoint D.mesh ⧸ D.periodSubgroupOfGrid s) : ℤ) = ∏ μ, s μ := by
  have ht : ∀ μ, (((s μ).toNat : ℕ) : ℤ) = s μ := fun μ =>
    Int.toNat_of_nonneg (by linarith [hs μ])
  let θ := AddEquiv.ofBijective (gridHom D) (gridHom_bijective D)
  let Ψ : (Fin 4 → ℤ) →+ ∀ μ, ZMod (s μ).toNat :=
    { toFun := fun n μ => ((n μ : ℤ) : ZMod (s μ).toNat)
      map_zero' := by
        funext μ
        simp
      map_add' := fun n m => by
        funext μ
        simp }
  let ψ : InfiniteLattice.LatticePoint D.mesh →+ ∀ μ, ZMod (s μ).toNat :=
    Ψ.comp θ.symm.toAddMonoidHom
  have hψ : ∀ n, ψ (gridHom D n) = Ψ n := fun n => by
    change Ψ (θ.symm (θ n)) = Ψ n
    rw [AddEquiv.symm_apply_apply]
  have hsurj : Function.Surjective ψ := by
    intro f
    choose n hn using fun μ => ZMod.intCast_surjective (f μ)
    exact ⟨gridHom D n, by rw [hψ]; exact funext hn⟩
  have hker : ψ.ker = D.periodSubgroupOfGrid s := by
    ext x
    obtain ⟨n, rfl⟩ := (gridHom_bijective D).2 x
    rw [AddMonoidHom.mem_ker, hψ, gridHom_mem_periodSubgroupOfGrid_iff]
    constructor
    · intro h μ
      have h1 : ((n μ : ℤ) : ZMod (s μ).toNat) = 0 := congrFun h μ
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ht] at h1
      exact h1
    · intro h
      funext μ
      change ((n μ : ℤ) : ZMod (s μ).toNat) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ht]
      exact h μ
  have e := QuotientAddGroup.quotientKerEquivOfSurjective ψ hsurj
  rw [← hker, Nat.card_congr e.toEquiv, Nat.card_pi]
  simp only [Nat.card_zmod]
  push_cast
  exact Finset.prod_congr rfl fun μ _ => ht μ
end LatticeQuotients
open LatticeQuotients in
theorem LatticeQuotients.statement_holds : LatticeQuotients.Statement := by
  intro D s hs
  refine ⟨fun G _ q _ hk => quotientRegularity (map_gridHom_ne_zero D q hs hk),
    ⟨periodicDistance_isLeast D s hs,
    fun y₁ y₂ y₁' y₂' h h' => periodicDistance_congr D s y₁ y₂ y₁' y₂' h h',
    sub_mem_periodGroup_of_periodicDistance_eq_zero D s hs⟩, card_quotient_periodSubgroupOfGrid D s hs⟩
end YangMills.Construction.ChessboardTori
end
