import YangMills.Construction.LatticeFields.WeightConjProjComplProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.BlockAveraging
section Chains
theorem sq_weighted_sum_le {ι : Type} (s : Finset ι) {c : ℝ} (hc : c * s.card = 1) (a : ι → ℝ) :
    (∑ i ∈ s, c * a i) ^ 2 ≤ ∑ i ∈ s, c * a i ^ 2 := by
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := a)
  calc (c * ∑ i ∈ s, a i) ^ 2 = c ^ 2 * (∑ i ∈ s, a i) ^ 2 := by ring
    _ ≤ c ^ 2 * (s.card * ∑ i ∈ s, a i ^ 2) := mul_le_mul_of_nonneg_left h (sq_nonneg c)
    _ = c * (c * s.card) * ∑ i ∈ s, a i ^ 2 := by ring
    _ = c * ∑ i ∈ s, a i ^ 2 := by rw [hc, mul_one]
end Chains
section Cube
variable {d N : ℕ}
def lineMean (ν : Fin d) (g : (Fin d → Fin N) → ℝ) (k : Fin d → Fin N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j, g (Function.update k ν j)
variable [NeZero N]
theorem cast_pos_of_neZero : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
end Cube
section Blocks
variable {d N : ℕ} [NeZero N] {κ : LatticeShape d}
theorem latticeSpacing_pos : 0 < latticeSpacing N := inv_pos.mpr cast_pos_of_neZero
theorem latticeSpacing_one : latticeSpacing 1 = 1 := by simp [latticeSpacing]
theorem latticeSpacing_mul_cast : latticeSpacing N * N = 1 := by
  rw [latticeSpacing, inv_mul_cancel₀ cast_pos_of_neZero.ne']
def cellOffset (N : ℕ) (k : Fin d → Fin N) : scaledIntLattice d N :=
  ⟨fun μ => latticeSpacing N * ((k μ : ℕ) : ℝ), fun μ => ⟨((k μ : ℕ) : ℤ), by simp⟩⟩
def cellPoint (q : LatticeSite 1 κ × (Fin d → Fin N)) : LatticeSite N κ :=
  unitSiteHom N κ q.1 + toSite N κ (cellOffset N q.2)
theorem cellOffset_nonneg (k : Fin d → Fin N) (μ : Fin d) :
    0 ≤ (cellOffset N k : Fin d → ℝ) μ :=
  mul_nonneg latticeSpacing_pos.le (Nat.cast_nonneg _)
theorem cellOffset_lt_one (k : Fin d → Fin N) (μ : Fin d) :
    (cellOffset N k : Fin d → ℝ) μ < 1 := by
  have hN : (0 : ℝ) < N := cast_pos_of_neZero
  have hk : (((k μ : ℕ)) : ℝ) < N := Nat.cast_lt.mpr (k μ).2
  change latticeSpacing N * (((k μ : ℕ)) : ℝ) < 1
  rw [latticeSpacing, inv_mul_lt_iff₀ hN, mul_one]
  exact hk
theorem exists_int_coord_unit (w : scaledIntLattice d 1) (μ : Fin d) :
    ∃ m : ℤ, (w : Fin d → ℝ) μ = m := by
  obtain ⟨m, hm⟩ := w.2 μ
  exact ⟨m, by simpa [latticeSpacing] using hm⟩
theorem exists_cellOffset (w : scaledIntLattice d 1) (v : scaledIntLattice d N)
    (h : ∀ μ, (w : Fin d → ℝ) μ ≤ (v : Fin d → ℝ) μ ∧ (v : Fin d → ℝ) μ < (w : Fin d → ℝ) μ + 1) :
    ∃ k, v = AddSubgroup.inclusion (scaledIntLattice_one_le (d := d) N) w + cellOffset N k := by
  have hN : (0 : ℝ) < N := cast_pos_of_neZero
  have key : ∀ μ, ∃ r : Fin N, (v : Fin d → ℝ) μ =
      (w : Fin d → ℝ) μ + latticeSpacing N * (((r : ℕ)) : ℝ) := by
    intro μ
    obtain ⟨n, hn⟩ := v.2 μ
    obtain ⟨m, hm⟩ := exists_int_coord_unit w μ
    have hv : (v : Fin d → ℝ) μ = latticeSpacing N * n := hn
    have ht : (((n - N * m : ℤ)) : ℝ) = N * ((v : Fin d → ℝ) μ - (w : Fin d → ℝ) μ) := by
      rw [hv, hm, latticeSpacing]
      push_cast
      field_simp
    have h0 : 0 ≤ n - N * m := by
      have : (0 : ℝ) ≤ ((n - N * m : ℤ) : ℝ) := by
        rw [ht]
        exact mul_nonneg hN.le (sub_nonneg.mpr (h μ).1)
      exact_mod_cast this
    have h1 : n - N * m < N := by
      have : ((n - N * m : ℤ) : ℝ) < N := by
        rw [ht]
        have := (h μ).2
        nlinarith
      exact_mod_cast this
    obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨⟨r, by omega⟩, ?_⟩
    have hr' : (r : ℝ) = N * ((v : Fin d → ℝ) μ - (w : Fin d → ℝ) μ) := by
      rw [← ht, hr]
      simp
    change (v : Fin d → ℝ) μ = (w : Fin d → ℝ) μ + latticeSpacing N * (r : ℝ)
    rw [hr', latticeSpacing]
    field_simp
    ring
  choose k hk using key
  refine ⟨k, Subtype.ext (funext fun μ => ?_)⟩
  exact hk μ
theorem cellPoint_toSite (w : scaledIntLattice d 1) (k : Fin d → Fin N) :
    cellPoint (toSite 1 κ w, k) =
      toSite N κ (AddSubgroup.inclusion (scaledIntLattice_one_le (d := d) N) w + cellOffset N k) := by
  rw [map_add]
  rfl
theorem cellPoint_surjective : Function.Surjective (cellPoint (N := N) (κ := κ)) := by
  intro x
  obtain ⟨v, rfl⟩ := toSite_surjective N κ x
  let w : scaledIntLattice d 1 := ⟨fun μ => (⌊(v : Fin d → ℝ) μ⌋ : ℝ), fun μ =>
    ⟨⌊(v : Fin d → ℝ) μ⌋, by simp [latticeSpacing]⟩⟩
  obtain ⟨k, hk⟩ := exists_cellOffset (N := N) w v fun μ =>
    ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  exact ⟨(toSite 1 κ w, k), by rw [cellPoint_toSite, hk]⟩
theorem cellPoint_injective : Function.Injective (cellPoint (N := N) (κ := κ)) := by
  rintro ⟨y, k⟩ ⟨y', k'⟩ h
  obtain ⟨w, rfl⟩ := toSite_surjective 1 κ y
  obtain ⟨w', rfl⟩ := toSite_surjective 1 κ y'
  rw [cellPoint_toSite, cellPoint_toSite] at h
  set a := AddSubgroup.inclusion (scaledIntLattice_one_le (d := d) N) w with ha
  set a' := AddSubgroup.inclusion (scaledIntLattice_one_le (d := d) N) w' with ha'
  have hz : (((a + cellOffset N k) - (a' + cellOffset N k') : scaledIntLattice d N) :
      Fin d → ℝ) ∈ periodSubgroup κ := by
    rw [← toSite_eq_zero_iff N κ, map_sub, h, sub_self]
  have hint := periodSubgroup_le_scaledIntLattice 1 κ hz
  have hN : (0 : ℝ) < N := cast_pos_of_neZero
  have hkk : k = k' := by
    funext μ
    obtain ⟨n, hn⟩ := hint μ
    obtain ⟨m, hm⟩ := exists_int_coord_unit w μ
    obtain ⟨m', hm'⟩ := exists_int_coord_unit w' μ
    have hn' : ((w : Fin d → ℝ) μ + latticeSpacing N * ((k μ : ℕ) : ℝ)) -
        ((w' : Fin d → ℝ) μ + latticeSpacing N * ((k' μ : ℕ) : ℝ)) = latticeSpacing 1 * n := hn
    rw [latticeSpacing_one, one_mul] at hn'
    have hdiv : ((((k μ : ℕ) : ℤ) - ((k' μ : ℕ) : ℤ) : ℤ)) = N * (n - m + m') := by
      have : ((((k μ : ℕ) : ℝ)) - (((k' μ : ℕ)) : ℝ)) = N * ((n : ℝ) - m + m') := by
        rw [hm, hm', latticeSpacing] at hn'
        field_simp at hn'
        linarith
      exact_mod_cast this
    have hz0 : ((k μ : ℕ) : ℤ) - ((k' μ : ℕ) : ℤ) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd (m := (N : ℤ)) ⟨_, hdiv⟩ ?_
      have h1 := (k μ).2
      have h2 := (k' μ).2
      rw [abs_lt]
      omega
    exact Fin.ext (by omega)
  subst hkk
  have hw : ((w - w' : scaledIntLattice d 1) : Fin d → ℝ) ∈ periodSubgroup κ := by
    have : (((a + cellOffset N k) - (a' + cellOffset N k) : scaledIntLattice d N) : Fin d → ℝ) =
        ((w - w' : scaledIntLattice d 1) : Fin d → ℝ) := by
      funext μ
      simp [ha, ha']
    rwa [this] at hz
  have hy : toSite 1 κ w = toSite 1 κ w' := by
    have := (toSite_eq_zero_iff 1 κ (w - w')).mpr hw
    rw [map_sub] at this
    exact sub_eq_zero.mp this
  rw [hy]
def cellEquiv : LatticeSite 1 κ × (Fin d → Fin N) ≃ LatticeSite N κ :=
  Equiv.ofBijective cellPoint ⟨cellPoint_injective, cellPoint_surjective⟩
theorem cellPoint_mem_coarseBlock (y : LatticeSite 1 κ) (k : Fin d → Fin N) :
    cellPoint (y, k) ∈ coarseBlock N y := by
  obtain ⟨w, rfl⟩ := toSite_surjective 1 κ y
  refine ⟨w, _, rfl, (cellPoint_toSite w k).symm, fun μ => ?_⟩
  have h0 := cellOffset_nonneg k μ
  have h1 := cellOffset_lt_one k μ
  change (w : Fin d → ℝ) μ ≤ (w : Fin d → ℝ) μ + (cellOffset N k : Fin d → ℝ) μ ∧
    (w : Fin d → ℝ) μ + (cellOffset N k : Fin d → ℝ) μ < (w : Fin d → ℝ) μ + 1
  constructor <;> linarith
theorem coarseBlock_eq_range (y : LatticeSite 1 κ) :
    coarseBlock N y = Set.range fun k : Fin d → Fin N => cellPoint (y, k) := by
  ext x
  constructor
  · rintro ⟨w, v, rfl, rfl, h⟩
    obtain ⟨k, hk⟩ := exists_cellOffset (N := N) w v h
    exact ⟨k, (cellPoint_toSite w k).trans (by rw [hk])⟩
  · rintro ⟨k, rfl⟩
    exact cellPoint_mem_coarseBlock y k
def topIndex (N : ℕ) [NeZero N] : Fin N :=
  ⟨N - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne N)) one_pos⟩
theorem nsmul_unitStep (ν : Fin d) :
    N • unitStep N κ ν = unitSiteHom N κ (unitStep 1 κ ν) := by
  have hN : (0 : ℝ) < N := cast_pos_of_neZero
  unfold unitStep
  rw [unitSiteHom_toSite, ← map_nsmul]
  congr 1
  refine Subtype.ext (funext fun μ => ?_)
  by_cases h : μ = ν
  · subst h
    change N • (Pi.single μ (latticeSpacing N) : Fin d → ℝ) μ =
      (Pi.single μ (latticeSpacing 1) : Fin d → ℝ) μ
    simp [latticeSpacing, hN.ne']
  · change N • (Pi.single ν (latticeSpacing N) : Fin d → ℝ) μ =
      (Pi.single ν (latticeSpacing 1) : Fin d → ℝ) μ
    simp [Pi.single_eq_of_ne h]
end Blocks
section Energies
variable {d N : ℕ} [NeZero N] {κ : LatticeShape d} [Fintype (LatticeSite N κ)]
  [Fintype (LatticeSite 1 κ)]
def cellMean (y : LatticeSite 1 κ) (u : LatticeSite N κ → ℝ) : ℝ :=
  ∑ k : Fin d → Fin N, latticeSpacing N ^ d * u (cellPoint (y, k))
theorem latticeSpacing_pow_mul_card :
    latticeSpacing N ^ d * ((Finset.univ : Finset (Fin d → Fin N)).card : ℝ) = 1 := by
  have : ((Finset.univ : Finset (Fin d → Fin N)).card : ℝ) = (N : ℝ) ^ d := by simp
  rw [this, ← mul_pow, latticeSpacing_mul_cast, one_pow]
end Energies
section Forms
variable {d : ℕ} {κ : LatticeShape d}
theorem directionIndex_apply_zero (i : Fin 1 → Fin d) : directionIndex (i 0) = i := by
  funext j
  rw [Subsingleton.elim j 0]
  rfl
def directionIndexEquiv : Fin d ≃ (Fin 1 → Fin d) where
  toFun := directionIndex
  invFun i := i 0
  left_inv _ := rfl
  right_inv := directionIndex_apply_zero
def pairIndexEquiv : Fin d × Fin d ≃ (Fin 2 → Fin d) where
  toFun p := Fin.cons p.1 (directionIndex p.2)
  invFun i := (i 0, i 1)
  left_inv _ := rfl
  right_inv i := by
    funext j
    refine Fin.cases rfl (fun j' => ?_) j
    rw [Subsingleton.elim j' 0]
    rfl
section Inner
variable {M : ℕ} {I : Type}
theorem latticeSpacing_nonneg : 0 ≤ latticeSpacing M := inv_nonneg.mpr (Nat.cast_nonneg M)
theorem fieldInner_self_nonneg (F : LatticeField M κ I) : 0 ≤ fieldInner F F :=
  tsum_nonneg fun _ => by
    rw [mul_assoc]
    exact mul_nonneg (pow_nonneg latticeSpacing_nonneg d) (mul_self_nonneg _)
theorem fieldNorm_sq (F : LatticeField M κ I) : fieldNorm F ^ 2 = fieldInner F F :=
  Real.sq_sqrt (fieldInner_self_nonneg F)
theorem fieldNorm_nonneg (F : LatticeField M κ I) : 0 ≤ fieldNorm F := Real.sqrt_nonneg _
variable [Fintype (LatticeSite M κ)] [Fintype I]
theorem fieldInner_eq_sum (F G : LatticeField M κ I) :
    fieldInner F G = ∑ i, ∑ x, latticeSpacing M ^ d * F x i * G x i := by
  unfold fieldInner
  rw [tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm]
end Inner
section Norms
variable {M : ℕ} [Fintype (LatticeSite M κ)]
end Norms
variable {N : ℕ} [NeZero N]
variable [Fintype (LatticeSite N κ)] [Fintype (LatticeSite 1 κ)]
end Forms
section Main
variable {d N : ℕ} [NeZero N] {κ : LatticeShape d}
theorem sum_latticeSpacing_pow : ∑ _k : Fin d → Fin N, latticeSpacing N ^ d = 1 := by
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact latticeSpacing_pow_mul_card
theorem cellMean_sub (y : LatticeSite 1 κ) (a b : LatticeSite N κ → ℝ) :
    cellMean y (fun x => a x - b x) = cellMean y a - cellMean y b := by
  simp only [cellMean, mul_sub, Finset.sum_sub_distrib]
theorem cellMean_const (y : LatticeSite 1 κ) (c : ℝ) :
    cellMean (N := N) y (fun _ => c) = c := by
  simp only [cellMean]
  rw [← Finset.sum_mul, sum_latticeSpacing_pow, one_mul]
variable [Fintype (LatticeSite N κ)] [Fintype (LatticeSite 1 κ)]
end Main
theorem finite_torus_sites {d : ℕ} (N : ℕ) [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.finite_torusSites <;> assumption
end YangMills.Construction.LatticeFields.BlockAveraging
