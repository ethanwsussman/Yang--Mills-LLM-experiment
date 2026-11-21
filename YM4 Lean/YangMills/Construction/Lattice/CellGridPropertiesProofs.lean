import YangMills.Construction.Dirichlet.CubeBumpBoundsProof
import YangMills.Construction.Lattice.CellGridProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set BoxTorus
open PeriodicLattice (meshSize)
namespace GridLattice
variable {L : ℕ} {κ : ℤ}
theorem meshSize_pos (G : CellGrid L κ) : 0 < meshSize L κ := by
  have hL : (0 : ℝ) < L := by
    have := G.admissible.2
    exact_mod_cast (by omega : 0 < L)
  exact zpow_pos hL _
theorem addCircle_coe_eq_coe_iff {p x y : ℝ} :
    (x : AddCircle p) = y ↔ ∃ k : ℤ, x - y = k * p := by apply _root_.YangMills.Construction.Dirichlet.CubeBump.addCircle_coe_eq_iff <;> assumption
theorem exists_side_counts (G : CellGrid L κ) :
    ∃ N : Fin 4 → ℕ, (∀ μ, G.sideLengths μ = (N μ : ℝ) * meshSize L κ) ∧ (∀ μ, Even (N μ)) ∧
      ∀ μ, 4 ≤ N μ := by
  have ha := meshSize_pos G
  obtain ⟨z, hz⟩ := G.cellLength_div_meshSize
  have hzpos : (0 : ℝ) < z := by
    rw [← hz]
    exact div_pos G.cellLength_pos ha
  have hz0 : 0 ≤ z := by
    have : (0 : ℤ) < z := by exact_mod_cast hzpos
    omega
  obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
  have hc : G.cellLength = (t : ℝ) * meshSize L κ := by
    have e : (((t : ℕ) : ℤ) : ℝ) = t := by simp
    rw [e] at hz
    rw [← hz]
    field_simp
  have hs : ∀ μ, G.sideLengths μ = ((G.counts μ * t : ℕ) : ℝ) * meshSize L κ := by
    intro μ
    simp only [CellGrid.sideLengths, hc]
    push_cast
    ring
  refine ⟨fun μ => G.counts μ * t, hs, fun μ => (G.counts_even μ).mul_right t, fun μ => ?_⟩
  have h := G.four_meshSize_le μ
  have h2 : (G.counts μ : ℝ) * G.cellLength = G.sideLengths μ := rfl
  rw [h2, hs μ] at h
  have h3 : (4 : ℝ) ≤ ((G.counts μ * t : ℕ) : ℝ) := le_of_mul_le_mul_right h ha
  exact_mod_cast h3
theorem eq_of_projection_eq_of_close (G : CellGrid L κ) {w w' : Fin 4 → ℝ}
    (h : projection G.sideLengths w = projection G.sideLengths w')
    (hb : ∀ μ, |w μ - w' μ| ≤ 3 * meshSize L κ) : w = w' := by
  have ha := meshSize_pos G
  funext μ
  obtain ⟨k, hk⟩ := addCircle_coe_eq_coe_iff.mp
    (show ((w μ : ℝ) : AddCircle (G.sideLengths μ)) = (w' μ : ℝ) from congrFun h μ)
  have hk0 : k = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have hs : 4 * meshSize L κ ≤ G.sideLengths μ := G.four_meshSize_le μ
    have hspos : 0 < G.sideLengths μ := by linarith
    have h3 := hb μ
    rw [hk, abs_mul, abs_of_pos hspos] at h3
    nlinarith
  rw [hk0] at hk
  simp only [Int.cast_zero, zero_mul] at hk
  linarith
def latticeVec (L : ℕ) (κ : ℤ) (m : Fin 4 → ℤ) : Fin 4 → ℝ := fun μ => (m μ : ℝ) * meshSize L κ
theorem latticeVec_injective_of_close (G : CellGrid L κ) {m m' : Fin 4 → ℤ}
    (h : projection G.sideLengths (latticeVec L κ m) = projection G.sideLengths (latticeVec L κ m'))
    (hb : ∀ μ, |m μ - m' μ| ≤ 3) : m = m' := by
  have ha := meshSize_pos G
  have e := eq_of_projection_eq_of_close G h fun μ => by
    have h3 : |((m μ - m' μ : ℤ) : ℝ)| ≤ 3 := by exact_mod_cast hb μ
    simp only [latticeVec]
    rw [← sub_mul, abs_mul, abs_of_pos ha]
    push_cast at h3
    exact mul_le_mul_of_nonneg_right h3 ha.le
  funext μ
  have e' := congrFun e μ
  simp only [latticeVec] at e'
  exact_mod_cast mul_right_cancel₀ ha.ne' e'
theorem smul_basisVector_eq_latticeVec (s : ℤ) (ν : Fin 4) :
    (((s : ℝ) * meshSize L κ) • basisVector ν : Fin 4 → ℝ) = latticeVec L κ (Pi.single ν s) := by
  funext μ
  by_cases h : μ = ν
  · subst h
    simp [basisVector, latticeVec]
  · simp [basisVector, latticeVec, Pi.single_eq_of_ne h]
theorem exists_int_of_sign {σ : ℝ} (h : σ = 1 ∨ σ = -1) : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ σ = s := by
  rcases h with rfl | rfl
  · exact ⟨1, Or.inl rfl, by simp⟩
  · exact ⟨-1, Or.inr rfl, by simp⟩
theorem abs_sub_single_le_three {ν ν' : Fin 4} {s s' : ℤ} (hs : s = 1 ∨ s = -1)
    (hs' : s' = 1 ∨ s' = -1) (μ : Fin 4) :
    |(Pi.single ν s : Fin 4 → ℤ) μ - (Pi.single ν' s' : Fin 4 → ℤ) μ| ≤ 3 := by
  simp only [Pi.single_apply]
  split_ifs <;> rw [abs_le] <;> constructor <;> omega
theorem eq_of_single_eq_single {ν ν' : Fin 4} {s s' : ℤ} (hs : s ≠ 0)
    (h : (Pi.single ν s : Fin 4 → ℤ) = Pi.single ν' s') : ν = ν' ∧ s = s' := by
  by_cases e : ν = ν'
  · subst e
    exact ⟨rfl, by simpa using congrFun h ν⟩
  · have h1 := congrFun h ν
    simp [Pi.single_eq_of_ne e] at h1
    exact absurd h1 hs
theorem translate_eq_add {ℓ : Fin 4 → ℝ} (x : BoxTorus.Space ℓ) (w : Fin 4 → ℝ) :
    BoxTorus.translate x w = x + projection ℓ w :=
  rfl
theorem eq_of_projection_signed_basis (G : CellGrid L κ) (ν ν' : Fin 4) (σ σ' : ℝ)
    (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1)
    (h : projection G.sideLengths ((σ * meshSize L κ) • basisVector ν) =
      projection G.sideLengths ((σ' * meshSize L κ) • basisVector ν')) : ν = ν' ∧ σ = σ' := by
  obtain ⟨s, hs, rfl⟩ := exists_int_of_sign hσ
  obtain ⟨s', hs', rfl⟩ := exists_int_of_sign hσ'
  rw [smul_basisVector_eq_latticeVec, smul_basisVector_eq_latticeVec] at h
  obtain ⟨e1, e2⟩ := eq_of_single_eq_single (by rcases hs with rfl | rfl <;> simp)
    (latticeVec_injective_of_close G h (abs_sub_single_le_three hs hs'))
  exact ⟨e1, by rw [e2]⟩
theorem neighbourStep_unique (G : CellGrid L κ) {x x' : G.GridPoint} {ν ν' : Fin 4} {σ σ' : ℝ}
    (h : IsNeighbourStep x x' ν σ) (h' : IsNeighbourStep x x' ν' σ') : ν = ν' ∧ σ = σ' := by
  refine eq_of_projection_signed_basis G ν ν' σ σ' h.1 h'.1 ?_
  have e := h.2.symm.trans h'.2
  rw [translate_eq_add, translate_eq_add] at e
  exact add_left_cancel e
theorem segment_eq_of_neighbourStep (G : CellGrid L κ) {x x' : G.GridPoint} {ν : Fin 4} {σ : ℝ}
    (h : IsNeighbourStep x x' ν σ) :
    {p | ∃ t ∈ Icc (0 : ℝ) 1,
      p = translate (x : G.Space) ((t * σ * meshSize L κ) • basisVector ν)} =
    {p | ∃ t ∈ Icc (0 : ℝ) 1,
      p = translate (x' : G.Space) ((t * (-σ) * meshSize L κ) • basisVector ν)} := by
  have hx : ∀ w : Fin 4 → ℝ, translate (x' : G.Space) w =
      translate (x : G.Space) ((σ * meshSize L κ) • basisVector ν + w) := by
    intro w
    rw [h.2]
    simp only [translate_eq_add, map_add, add_assoc]
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    rw [hx]
    congr 1
    module
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    rw [hx]
    congr 1
    module
theorem not_isForward_flip (G : CellGrid L κ) {b : G.DirectedEdge} (h : b.IsForward) :
    ¬ b.flip.IsForward := by
  rintro ⟨ν', h'⟩
  obtain ⟨ν, hν⟩ := h
  have hs := IsNeighbourStep.symm h'
  have e := (neighbourStep_unique G hν hs).2
  norm_num at e
theorem ncard_meshMultiplesMod (G : CellGrid L κ) (μ : Fin 4) {N : ℕ}
    (hN : G.sideLengths μ = (N : ℝ) * meshSize L κ) (h4 : 4 ≤ N) :
    (meshMultiplesMod G μ).ncard = N := by
  have ha := meshSize_pos G
  set f : ℕ → AddCircle (G.sideLengths μ) :=
    fun i => (((i : ℝ) * meshSize L κ : ℝ) : AddCircle (G.sideLengths μ)) with hf
  have himg : meshMultiplesMod G μ = f '' (↑(Finset.range N) : Set ℕ) := by
    ext t
    constructor
    · rintro ⟨n, rfl⟩
      have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      have h0 : 0 ≤ n % (N : ℤ) := Int.emod_nonneg _ hN0
      have h1 : n % (N : ℤ) < N := Int.emod_lt_of_pos _ (by omega)
      obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le h0
      refine ⟨i, by simp only [Finset.coe_range, mem_Iio]; omega, ?_⟩
      refine addCircle_coe_eq_coe_iff.mpr ⟨-(n / (N : ℤ)), ?_⟩
      have h2 := Int.emod_add_mul_ediv n (N : ℤ)
      rw [hi] at h2
      have h3 : (n : ℝ) = (i : ℝ) + (N : ℝ) * ((n / (N : ℤ) : ℤ) : ℝ) := by exact_mod_cast h2.symm
      rw [hN, h3]
      push_cast
      ring
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, by simp [hf]⟩
  have hinj : InjOn f (↑(Finset.range N) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, mem_Iio] at hi hj
    obtain ⟨k, hk⟩ := addCircle_coe_eq_coe_iff.mp hij
    rw [hN] at hk
    have h1 : (i : ℝ) - j = k * N := by
      have : ((i : ℝ) - j) * meshSize L κ = (k * N) * meshSize L κ := by linarith
      exact mul_right_cancel₀ ha.ne' this
    have h2 : (i : ℤ) - j = k * N := by exact_mod_cast h1
    have h3 : (N : ℤ) ∣ (i : ℤ) - j := ⟨k, by rw [h2]; ring⟩
    have h4' : |(i : ℤ) - j| < N := by
      rw [abs_lt]
      constructor <;> omega
    have h5 := Int.eq_zero_of_abs_lt_dvd h3 h4'
    omega
  rw [himg, hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]
theorem exists_latticeVec_of_isLiftOf (G : CellGrid L κ) (x : G.GridPoint) (w : Fin 4 → ℝ)
    (h : IsLiftOf w (x : G.Space)) : ∃ m, w = latticeVec L κ m := by
  obtain ⟨N, hN, -, -⟩ := exists_side_counts G
  obtain ⟨x, n, rfl⟩ := x
  have hk : ∀ μ, ∃ k : ℤ, w μ - (n μ : ℝ) * meshSize L κ = k * G.sideLengths μ := fun μ =>
    addCircle_coe_eq_coe_iff.mp
      (show ((w μ : ℝ) : AddCircle (G.sideLengths μ)) = ((n μ : ℝ) * meshSize L κ : ℝ)
        from congrFun h μ)
  choose k hk using hk
  refine ⟨fun μ => n μ + k μ * N μ, ?_⟩
  funext μ
  have h1 := hk μ
  rw [hN μ] at h1
  simp only [latticeVec]
  push_cast
  linarith
theorem pointCountsAndLifts (G : CellGrid L κ) : PointCountsAndLifts G := by
  have ha := meshSize_pos G
  obtain ⟨N, hN, hev, h4⟩ := exists_side_counts G
  refine ⟨fun μ => ⟨?_, N μ, ?_, ncard_meshMultiplesMod G μ (hN μ) (h4 μ), hev μ, h4 μ⟩, ?_, ?_⟩
  · simp only [CellGrid.sideLengths, mul_div_assoc]
  · rw [hN μ]
    field_simp
  · exact fun w w' h hb => eq_of_projection_eq_of_close G h hb
  · intro x w h
    obtain ⟨m, rfl⟩ := exists_latticeVec_of_isLiftOf G x w h
    exact ⟨m, fun _ => rfl⟩
def gridPointOf (G : CellGrid L κ) (m : Fin 4 → ℤ) : G.GridPoint :=
  ⟨projection G.sideLengths (latticeVec L κ m), ⟨m, rfl⟩⟩
theorem gridPointOf_add (G : CellGrid L κ) (m m' : Fin 4 → ℤ) :
    gridPointOf G (m + m') = gridPointOf G m + gridPointOf G m' := by
  refine Subtype.ext ?_
  change projection G.sideLengths (latticeVec L κ (m + m')) =
    projection G.sideLengths (latticeVec L κ m) + projection G.sideLengths (latticeVec L κ m')
  rw [← map_add]
  congr 1
  funext μ
  simp [latticeVec, add_mul]
theorem gridPointOf_zero (G : CellGrid L κ) : gridPointOf G 0 = 0 := by
  refine Subtype.ext ?_
  change projection G.sideLengths (latticeVec L κ 0) = 0
  have : latticeVec L κ 0 = 0 := by
    funext μ
    simp [latticeVec]
  rw [this, map_zero]
theorem gridPointOf_single (G : CellGrid L κ) (ν : Fin 4) :
    gridPointOf G (Pi.single ν 1) = gridStep L κ G.sideLengths ν := by
  refine Subtype.ext ?_
  change projection G.sideLengths (latticeVec L κ (Pi.single ν 1)) =
    projection G.sideLengths (meshSize L κ • basisVector ν)
  congr 1
  have h := smul_basisVector_eq_latticeVec (L := L) (κ := κ) 1 ν
  simpa using h.symm
theorem gridPointOf_injective_of_close (G : CellGrid L κ) {m m' : Fin 4 → ℤ}
    (h : gridPointOf G m = gridPointOf G m') (hb : ∀ μ, |m μ - m' μ| ≤ 3) : m = m' :=
  latticeVec_injective_of_close G (congrArg Subtype.val h) hb
theorem exists_coeffs_of_mem_vertexSet (G : CellGrid L κ) (p : G.Face) {z : G.GridPoint}
    (hz : z ∈ p.vertexSet) :
    ∃ ε ε' : ℤ, (ε = 0 ∨ ε = 1) ∧ (ε' = 0 ∨ ε' = 1) ∧
      z = p.corner + gridPointOf G (Pi.single p.dir₁ ε + Pi.single p.dir₂ ε') := by
  simp only [Face.vertexSet, mem_insert_iff, mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · refine ⟨0, 0, Or.inl rfl, Or.inl rfl, ?_⟩
    simp [gridPointOf_zero]
  · refine ⟨1, 0, Or.inr rfl, Or.inl rfl, ?_⟩
    simp [gridPointOf_single]
  · refine ⟨1, 1, Or.inr rfl, Or.inr rfl, ?_⟩
    rw [gridPointOf_add, gridPointOf_single, gridPointOf_single, add_assoc]
  · refine ⟨0, 1, Or.inl rfl, Or.inr rfl, ?_⟩
    simp [gridPointOf_single]
theorem ncard_vertexSet (G : CellGrid L κ) (p : G.Face) : p.vertexSet.ncard = 4 := by
  have hne : p.dir₁ ≠ p.dir₂ := p.dir₁_lt_dir₂.ne
  have key : ∀ m m' : Fin 4 → ℤ, (∀ μ, |m μ - m' μ| ≤ 3) → m ≠ m' →
      p.corner + gridPointOf G m ≠ p.corner + gridPointOf G m' := fun m m' hb hm e =>
    hm (gridPointOf_injective_of_close G (add_left_cancel e) hb)
  set f := p.dir₁
  set g := p.dir₂
  have e0 : p.corner = p.corner + gridPointOf G 0 := by simp [gridPointOf_zero]
  have e1 : p.corner + gridStep L κ G.sideLengths f = p.corner + gridPointOf G (Pi.single f 1) := by
    rw [gridPointOf_single]
  have e3 : p.corner + gridStep L κ G.sideLengths g = p.corner + gridPointOf G (Pi.single g 1) := by
    rw [gridPointOf_single]
  have e2 : p.corner + gridStep L κ G.sideLengths f + gridStep L κ G.sideLengths g =
      p.corner + gridPointOf G (Pi.single f 1 + Pi.single g 1) := by
    rw [gridPointOf_add, gridPointOf_single, gridPointOf_single, add_assoc]
  have bd : ∀ (u v : Fin 4 → ℤ), (∀ μ, 0 ≤ u μ ∧ u μ ≤ 2) → (∀ μ, 0 ≤ v μ ∧ v μ ≤ 2) →
      ∀ μ, |u μ - v μ| ≤ 3 := fun u v hu hv μ => by
    have := hu μ
    have := hv μ
    rw [abs_le]
    constructor <;> omega
  have r0 : ∀ μ, 0 ≤ (0 : Fin 4 → ℤ) μ ∧ (0 : Fin 4 → ℤ) μ ≤ 2 := fun μ => by simp
  have r1' : ∀ (ν μ : Fin 4), 0 ≤ (Pi.single ν (1 : ℤ) : Fin 4 → ℤ) μ ∧
      (Pi.single ν (1 : ℤ) : Fin 4 → ℤ) μ ≤ 1 := fun ν μ => by
    simp only [Pi.single_apply]
    split_ifs <;> omega
  have r1 : ∀ (ν μ : Fin 4), 0 ≤ (Pi.single ν (1 : ℤ) : Fin 4 → ℤ) μ ∧
      (Pi.single ν (1 : ℤ) : Fin 4 → ℤ) μ ≤ 2 := fun ν μ => by
    have := r1' ν μ
    omega
  have r2 : ∀ μ, 0 ≤ ((Pi.single f 1 + Pi.single g 1 : Fin 4 → ℤ)) μ ∧
      ((Pi.single f 1 + Pi.single g 1 : Fin 4 → ℤ)) μ ≤ 2 := fun μ => by
    have h1 := r1' f μ
    have h2 := r1' g μ
    simp only [Pi.add_apply]
    omega
  have n01 : (0 : Fin 4 → ℤ) ≠ Pi.single f 1 := fun h => by simpa using congrFun h f
  have n03 : (0 : Fin 4 → ℤ) ≠ Pi.single g 1 := fun h => by simpa using congrFun h g
  have n02 : (0 : Fin 4 → ℤ) ≠ Pi.single f 1 + Pi.single g 1 := fun h => by
    have h1 := congrFun h f
    simp [Pi.single_eq_of_ne hne] at h1
  have n12 : (Pi.single f 1 : Fin 4 → ℤ) ≠ Pi.single f 1 + Pi.single g 1 := fun h => by
    have h1 := congrFun h g
    simp [Pi.single_eq_of_ne hne.symm] at h1
  have n13 : (Pi.single f 1 : Fin 4 → ℤ) ≠ Pi.single g 1 := fun h => by
    have h1 := congrFun h f
    simp [Pi.single_eq_of_ne hne] at h1
  have n23 : (Pi.single f 1 + Pi.single g 1 : Fin 4 → ℤ) ≠ Pi.single g 1 := fun h => by
    have h1 := congrFun h f
    simp [Pi.single_eq_of_ne hne] at h1
  have a01 := key _ _ (bd _ _ r0 (r1 f)) n01
  have a03 := key _ _ (bd _ _ r0 (r1 g)) n03
  have a02 := key _ _ (bd _ _ r0 r2) n02
  have a12 := key _ _ (bd _ _ (r1 f) r2) n12
  have a13 := key _ _ (bd _ _ (r1 f) (r1 g)) n13
  have a23 := key _ _ (bd _ _ r2 (r1 g)) n23
  rw [← e0, ← e1] at a01
  rw [← e0, ← e3] at a03
  rw [← e0, ← e2] at a02
  rw [← e1, ← e2] at a12
  rw [← e1, ← e3] at a13
  rw [← e2, ← e3] at a23
  simp only [Face.vertexSet]
  rw [Set.ncard_insert_of_notMem (by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨a01, a02, a03⟩) (Set.toFinite _),
    Set.ncard_insert_of_notMem (by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨a12, a13⟩) (Set.toFinite _), Set.ncard_pair a23]
theorem axis_eq_of_single_add_single_add {ν ν' l : Fin 4} (hne : ν ≠ ν') {ε ε' δ δ' : ℤ}
    (hε : ε = 0 ∨ ε = 1) (hε' : ε' = 0 ∨ ε' = 1) (hδ : δ = 0 ∨ δ = 1) (hδ' : δ' = 0 ∨ δ' = 1)
    (h : (Pi.single ν ε + Pi.single ν' ε' + Pi.single l 1 : Fin 4 → ℤ) =
      Pi.single ν δ + Pi.single ν' δ') : (l = ν ∧ ε = 0) ∨ (l = ν' ∧ ε' = 0) := by
  have hl := congrFun h l
  simp only [Pi.add_apply, Pi.single_apply, if_true] at hl
  by_cases a : l = ν
  · subst a
    simp [hne] at hl
    left
    exact ⟨rfl, by omega⟩
  · by_cases b : l = ν'
    · subst b
      simp [a] at hl
      right
      exact ⟨rfl, by omega⟩
    · exfalso
      simp [a, b] at hl
theorem face_eq_of_vertexSet_eq (G : CellGrid L κ) (p p' : G.Face)
    (h : p.vertexSet = p'.vertexSet) : p = p' := by
  have hb : p'.corner ∈ p.vertexSet := by
    rw [h]
    simp [Face.vertexSet]
  have h1 : p'.corner + gridStep L κ G.sideLengths p'.dir₁ ∈ p.vertexSet := by
    rw [h]
    simp [Face.vertexSet]
  have h2 : p'.corner + gridStep L κ G.sideLengths p'.dir₂ ∈ p.vertexSet := by
    rw [h]
    simp [Face.vertexSet]
  obtain ⟨ε, ε', hε, hε', e0⟩ := exists_coeffs_of_mem_vertexSet G p hb
  obtain ⟨δ, δ', hδ, hδ', e1⟩ := exists_coeffs_of_mem_vertexSet G p h1
  obtain ⟨γ, γ', hγ, hγ', e2⟩ := exists_coeffs_of_mem_vertexSet G p h2
  have hne : p.dir₁ ≠ p.dir₂ := p.dir₁_lt_dir₂.ne
  have bd : ∀ (ε ε' δ δ' : ℤ) (l : Fin 4), (ε = 0 ∨ ε = 1) → (ε' = 0 ∨ ε' = 1) →
      (δ = 0 ∨ δ = 1) → (δ' = 0 ∨ δ' = 1) → ∀ μ,
      |(Pi.single p.dir₁ ε + Pi.single p.dir₂ ε' + Pi.single l 1 : Fin 4 → ℤ) μ -
        (Pi.single p.dir₁ δ + Pi.single p.dir₂ δ' : Fin 4 → ℤ) μ| ≤ 3 := by
    intro ε ε' δ δ' l hε hε' hδ hδ' μ
    simp only [Pi.add_apply, Pi.single_apply]
    rw [abs_le]
    split_ifs <;> omega
  have step_eq : ∀ {δ δ' : ℤ} (l : Fin 4), (δ = 0 ∨ δ = 1) → (δ' = 0 ∨ δ' = 1) →
      p'.corner + gridStep L κ G.sideLengths l =
        p.corner + gridPointOf G (Pi.single p.dir₁ δ + Pi.single p.dir₂ δ') →
      (l = p.dir₁ ∧ ε = 0) ∨ (l = p.dir₂ ∧ ε' = 0) := by
    intro δ δ' l hδ hδ' e
    refine axis_eq_of_single_add_single_add hne hε hε' hδ hδ'
      (gridPointOf_injective_of_close G ?_ (bd _ _ _ _ l hε hε' hδ hδ'))
    rw [gridPointOf_add, gridPointOf_single]
    rw [e0, add_assoc] at e
    exact add_left_cancel e
  have r1 := step_eq _ hδ hδ' e1
  have r2 := step_eq _ hγ hγ' e2
  have hlt := p'.dir₁_lt_dir₂
  have hlt' := p.dir₁_lt_dir₂
  have hfs : p'.dir₁ = p.dir₁ ∧ p'.dir₂ = p.dir₂ ∧ ε = 0 ∧ ε' = 0 := by
    rcases r1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases r2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · rw [a1, a2] at hlt
      exact absurd hlt (lt_irrefl _)
    · exact ⟨a1, a2, b1, b2⟩
    · rw [a1, a2] at hlt
      exact absurd hlt (not_lt_of_gt hlt')
    · rw [a1, a2] at hlt
      exact absurd hlt (lt_irrefl _)
  obtain ⟨f1, f2, z1, z2⟩ := hfs
  subst z1 z2
  have hbase : p'.corner = p.corner := by
    rw [e0]
    simp [gridPointOf_zero]
  exact BoxTorus.Face.ext hbase.symm f1.symm f2.symm
theorem edgesAndFaces (G : CellGrid L κ) : EdgesAndFaces G := by
  refine ⟨fun ν ν' σ σ' hσ hσ' h => eq_of_projection_signed_basis G ν ν' σ σ' hσ hσ' h,
    fun b => ?_, ncard_vertexSet G, fun b b' hp hp' e => ?_, face_eq_of_vertexSet_eq G⟩
  · obtain ⟨ν, σ, h⟩ := b.isNeighbour
    have rev_seg : ∀ (c : G.DirectedEdge) (S : Set G.Space), c.IsSegmentSet S →
        c.flip.IsSegmentSet S := by
      rintro c S ⟨ν, σ, h, rfl⟩
      exact ⟨ν, -σ, h.symm, segment_eq_of_neighbourStep G h⟩
    have rev_dir : ∀ (c : G.DirectedEdge) (ν : Fin 4), c.HasAxis ν → c.flip.HasAxis ν := by
      rintro c ν ⟨σ, h⟩
      exact ⟨-σ, h.symm⟩
    refine ⟨⟨ν, ⟨σ, h⟩, fun ν' ⟨σ', h'⟩ => (neighbourStep_unique G h h').1.symm⟩,
      ⟨_, ⟨ν, σ, h, rfl⟩, ?_⟩, fun ν' => ⟨rev_dir b.flip ν', rev_dir b ν'⟩,
      fun S => ⟨rev_seg b.flip S, rev_seg b S⟩, ?_⟩
    · rintro S ⟨ν', σ', h', rfl⟩
      obtain ⟨rfl, rfl⟩ := neighbourStep_unique G h h'
      rfl
    · by_cases hp : b.IsForward
      · exact Or.inl ⟨hp, not_isForward_flip G hp⟩
      · exact Or.inr ⟨DirectedEdge.flip_isForward hp, hp⟩
  · rcases Set.pair_eq_pair_iff.mp e with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact BoxTorus.DirectedEdge.ext e1 e2
    · exfalso
      have hrev : b' = b.flip := BoxTorus.DirectedEdge.ext e2.symm e1.symm
      exact not_isForward_flip G hp (hrev ▸ hp')
theorem gaugeConfigsAsEdgeMaps (G : CellGrid L κ) : GaugeConfigsAsEdgeMaps G := by
  have rev : ∀ (U : G.GaugeConfig) (b : G.DirectedEdge),
      edgeVariable U b.flip = (edgeVariable U b)⁻¹ := by
    intro U b
    by_cases hp : b.IsForward
    · have hn := not_isForward_flip G hp
      rw [edgeVariable, dif_neg hn, edgeVariable, dif_pos hp]
      rfl
    · have hr := DirectedEdge.flip_isForward hp
      rw [edgeVariable, dif_pos hr, edgeVariable, dif_neg hp, inv_inv]
  refine ⟨rev, fun u hu => ⟨fun b => u b.1, fun b => ?_, fun U hU => ?_⟩⟩
  · by_cases hp : b.IsForward
    · rw [edgeVariable, dif_pos hp]
    · rw [edgeVariable, dif_neg hp, hu, inv_inv]
  · funext b
    have h := hU b.1
    rwa [edgeVariable, dif_pos b.2] at h
theorem eq_single_of_sum_sq_eq_one {m : Fin 4 → ℤ} (h : ∑ μ, m μ ^ 2 = 1) :
    ∃ (ν : Fin 4) (s : ℤ), (s = 1 ∨ s = -1) ∧ m = Pi.single ν s := by
  obtain ⟨ν, hν⟩ : ∃ ν, m ν ≠ 0 := by
    by_contra hall
    have h0 : ∀ μ, m μ = 0 := fun μ => by_contra fun e => hall ⟨μ, e⟩
    simp [h0] at h
  have hsplit : m ν ^ 2 + ∑ μ ∈ Finset.univ.erase ν, m μ ^ 2 = ∑ μ, m μ ^ 2 :=
    Finset.add_sum_erase Finset.univ (fun μ => m μ ^ 2) (Finset.mem_univ ν)
  have hpos : 0 < m ν ^ 2 := by positivity
  have hrest : 0 ≤ ∑ μ ∈ Finset.univ.erase ν, m μ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : m ν ^ 2 = 1 := by omega
  have h0 : ∑ μ ∈ Finset.univ.erase ν, m μ ^ 2 = 0 := by omega
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp h0
  refine ⟨ν, m ν, ?_, ?_⟩
  · have h2 : (m ν - 1) * (m ν + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · funext μ
    by_cases e : μ = ν
    · subst e
      simp
    · rw [Pi.single_eq_of_ne e]
      exact pow_eq_zero_iff (two_ne_zero) |>.mp (hz μ (Finset.mem_erase.mpr ⟨e, Finset.mem_univ _⟩))
theorem sqrt_sum_sq_latticeVec (G : CellGrid L κ) (m : Fin 4 → ℤ) :
    Real.sqrt (∑ μ, latticeVec L κ m μ ^ 2) =
      meshSize L κ * Real.sqrt ((∑ μ, m μ ^ 2 : ℤ) : ℝ) := by
  have ha := meshSize_pos G
  have h : ∑ μ, latticeVec L κ m μ ^ 2 = meshSize L κ ^ 2 * ((∑ μ, m μ ^ 2 : ℤ) : ℝ) := by
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by
      simp only [latticeVec]
      ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha.le]
theorem torusDist_eq_meshSize_iff (G : CellGrid L κ) (x y : G.GridPoint) :
    torusDist (x : G.Space) (y : G.Space) = meshSize L κ ↔
      ∃ (ν : Fin 4) (σ : ℝ), IsNeighbourStep y x ν σ := by
  have ha := meshSize_pos G
  have hdef : torusDist (x : G.Space) (y : G.Space) =
      sInf ((fun z : Fin 4 → ℝ => Real.sqrt (∑ μ, z μ ^ 2)) ''
        {z | IsLiftOf z ((x : G.Space) - (y : G.Space))}) := rfl
  rw [hdef]
  set A : Set ℝ := (fun z : Fin 4 → ℝ => Real.sqrt (∑ μ, z μ ^ 2)) ''
    {z | IsLiftOf z ((x : G.Space) - (y : G.Space))} with hA
  have hbdd : BddBelow A := ⟨0, by
    rintro _ ⟨z, _, rfl⟩
    exact Real.sqrt_nonneg _⟩
  have hlift : ∀ z, IsLiftOf z ((x : G.Space) - (y : G.Space)) → ∃ m, z = latticeVec L κ m :=
    fun z hz => exists_latticeVec_of_isLiftOf G (x - y) z hz
  obtain ⟨z0, hz0⟩ := projection_surjective G.sideLengths ((x : G.Space) - (y : G.Space))
  have hne : A.Nonempty := ⟨_, z0, hz0, rfl⟩
  have hnn : ∀ m : Fin 4 → ℤ, 0 ≤ ∑ μ, m μ ^ 2 := fun m =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  constructor
  · intro h
    by_contra hno
    have hzero : ∀ m, IsLiftOf (latticeVec L κ m) ((x : G.Space) - (y : G.Space)) →
        ∑ μ, m μ ^ 2 ≠ 0 := by
      intro m hm h0
      have h1 : sInf A ≤ Real.sqrt (∑ μ, latticeVec L κ m μ ^ 2) := csInf_le hbdd ⟨_, hm, rfl⟩
      rw [sqrt_sum_sq_latticeVec G, h0, h] at h1
      simp at h1
      linarith
    have hone : ∀ m, IsLiftOf (latticeVec L κ m) ((x : G.Space) - (y : G.Space)) →
        ∑ μ, m μ ^ 2 ≠ 1 := by
      intro m hm h1
      obtain ⟨ν, s, hs, rfl⟩ := eq_single_of_sum_sq_eq_one h1
      refine hno ⟨ν, s, ?_, ?_⟩
      · rcases hs with rfl | rfl <;> simp
      · rw [translate_eq_add, smul_basisVector_eq_latticeVec]
        have hm' : projection G.sideLengths (latticeVec L κ (Pi.single ν s)) =
          (x : G.Space) - (y : G.Space) := hm
        rw [hm']
        abel
    have hge : meshSize L κ * Real.sqrt 2 ≤ sInf A := le_csInf hne (by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨m, rfl⟩ := hlift z hz
      have h2 : 2 ≤ ∑ μ, m μ ^ 2 := by
        have := hzero m hz
        have := hone m hz
        have := hnn m
        omega
      have h2' : (2 : ℝ) ≤ ((∑ μ, m μ ^ 2 : ℤ) : ℝ) := by exact_mod_cast h2
      change _ ≤ Real.sqrt (∑ μ, latticeVec L κ m μ ^ 2)
      rw [sqrt_sum_sq_latticeVec G]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2') ha.le)
    have h1 : 1 < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    rw [h] at hge
    nlinarith
  · rintro ⟨ν, σ, hσ, hxy⟩
    obtain ⟨s, hs, rfl⟩ := exists_int_of_sign hσ
    rw [translate_eq_add, smul_basisVector_eq_latticeVec] at hxy
    have hl : IsLiftOf (latticeVec L κ (Pi.single ν s)) ((x : G.Space) - (y : G.Space)) := by
      change projection G.sideLengths (latticeVec L κ (Pi.single ν s)) = _
      rw [hxy]
      abel
    have hs1 : ∑ μ, (Pi.single ν s : Fin 4 → ℤ) μ ^ 2 = 1 := by
      rw [Finset.sum_eq_single ν (fun μ _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
      rcases hs with rfl | rfl <;> simp
    refine IsLeast.csInf_eq ⟨⟨_, hl, ?_⟩, ?_⟩
    · change Real.sqrt (∑ μ, latticeVec L κ (Pi.single ν s) μ ^ 2) = _
      rw [sqrt_sum_sq_latticeVec G, hs1]
      simp
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨m, rfl⟩ := hlift z hz
      have h1 : 1 ≤ ∑ μ, m μ ^ 2 := by
        by_contra hlt
        have h0 : ∑ μ, m μ ^ 2 = 0 := by
          have := hnn m
          omega
        have hz0 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp h0
        have hm0 : m = 0 := funext fun μ =>
          pow_eq_zero_iff (two_ne_zero) |>.mp (hz0 μ (Finset.mem_univ _))
        subst hm0
        have hb : ∀ μ, |(0 : Fin 4 → ℤ) μ - (Pi.single ν s : Fin 4 → ℤ) μ| ≤ 3 := fun μ => by
          simp only [Pi.zero_apply, Pi.single_apply]
          rw [abs_le]
          split_ifs <;> omega
        have e := latticeVec_injective_of_close G (show projection G.sideLengths (latticeVec L κ 0) =
          projection G.sideLengths (latticeVec L κ (Pi.single ν s)) from hz.trans hl.symm) hb
        have e' := congrFun e ν
        simp at e'
        omega
      have h1' : (1 : ℝ) ≤ ((∑ μ, m μ ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
      change _ ≤ Real.sqrt (∑ μ, latticeVec L κ m μ ^ 2)
      rw [sqrt_sum_sq_latticeVec G]
      have h2 : 1 ≤ Real.sqrt ((∑ μ, m μ ^ 2 : ℤ) : ℝ) := Real.one_le_sqrt.mpr h1'
      nlinarith
theorem edgesByDistance (G : CellGrid L κ) : EdgesByDistance G := by
  refine ⟨fun x y => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨b, hb⟩
    obtain ⟨ν, σ, h⟩ := b.isNeighbour
    refine (torusDist_eq_meshSize_iff G x y).mpr ?_
    rcases Set.pair_eq_pair_iff.mp hb with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2] at h
      exact ⟨ν, -σ, h.symm⟩
    · rw [e1, e2] at h
      exact ⟨ν, σ, h⟩
  · intro h
    obtain ⟨ν, σ, hs⟩ := (torusDist_eq_meshSize_iff G x y).mp h
    exact ⟨⟨y, x, ν, σ, hs⟩, Set.pair_comm _ _⟩
  · intro g hg him b
    have mem : ∀ t : G.GridPoint, g (t : G.Space) ∈ gridSubgroup L κ G.sideLengths := fun t => by
      have h : g (t : G.Space) ∈ g '' (gridSubgroup L κ G.sideLengths : Set G.Space) :=
        ⟨t, t.2, rfl⟩
      rw [him] at h
      exact h
    obtain ⟨ν₀, σ₀, h₀⟩ := b.isNeighbour
    have hd : torusDist (b.target : G.Space) (b.source : G.Space) = meshSize L κ :=
      (torusDist_eq_meshSize_iff G b.target b.source).mpr ⟨ν₀, σ₀, h₀⟩
    obtain ⟨ν, σ, hs⟩ :=
      (torusDist_eq_meshSize_iff G ⟨g b.target, mem _⟩ ⟨g b.source, mem _⟩).mp
        ((hg.2 _ _).trans hd)
    exact ⟨⟨⟨g b.source, mem _⟩, ⟨g b.target, mem _⟩, ν, σ, hs⟩, rfl, rfl⟩
theorem continuous_edgeVariable (G : CellGrid L κ) (b : G.DirectedEdge) :
    Continuous fun U : G.GaugeConfig => edgeVariable U b := by
  by_cases hp : b.IsForward
  · simp only [edgeVariable, dif_pos hp]
    exact continuous_apply _
  · simp only [edgeVariable, dif_neg hp]
    exact (continuous_apply _).inv
theorem continuous_faceEnergy (G : CellGrid L κ) (p : G.Face) :
    Continuous fun U : G.GaugeConfig => faceEnergy U p := by
  have h : Continuous fun U : G.GaugeConfig => faceHolonomy U p :=
    (((continuous_edgeVariable G _).mul (continuous_edgeVariable G _)).mul
      (continuous_edgeVariable G _).inv).mul (continuous_edgeVariable G _).inv
  have h' : Continuous fun U : G.GaugeConfig => (faceHolonomy U p : Matrices.ComplexMatrix2) :=
    continuous_subtype_val.comp h
  unfold faceEnergy
  exact continuous_const.sub (continuous_const.mul
    (Complex.continuous_re.comp (Continuous.matrix_trace h')))
theorem continuous_wilsonAction (G : CellGrid L κ) :
    Continuous fun U : G.GaugeConfig => G.wilsonAction U := by
  have : Fintype G.Face := Fintype.ofFinite _
  have h : (fun U : G.GaugeConfig => G.wilsonAction U) =
      fun U => ∑ p : G.Face, faceEnergy U p := by
    funext U
    exact finsum_eq_sum_of_fintype _
  rw [h]
  exact continuous_finsetSum _ fun p _ => continuous_faceEnergy G p
theorem boltzmannWeightIntegrable (G : CellGrid L κ) : BoltzmannWeightIntegrable G := by
  have hprob : IsProbabilityMeasure (haarConfigMeasure L κ G.sideLengths) := by
    unfold haarConfigMeasure Matrices.ComplexMatrix2.haarPi
    infer_instance
  refine ⟨inferInstance, fun β _ => ?_⟩
  have hc : Continuous fun U : G.GaugeConfig => Real.exp (-β * G.wilsonAction U) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonAction G))
  have hi : Integrable (fun U : G.GaugeConfig => Real.exp (-β * G.wilsonAction U))
      (haarConfigMeasure L κ G.sideLengths) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact ⟨hc, fun U => Real.exp_pos _, hi, integral_exp_pos hi⟩
theorem properties : Properties := fun _ _ G =>
  ⟨pointCountsAndLifts G, edgesAndFaces G, gaugeConfigsAsEdgeMaps G, edgesByDistance G,
    boltzmannWeightIntegrable G⟩
end GridLattice
end YangMills.Construction
end
