import YangMills.Construction.Continuum.TorusTransportData
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace TorusTransport
open TorusMetric TestFunctions
namespace TransportData
variable (D : TransportData)
theorem zero_lt_side : 0 < D.side := by
  have h13 : 13 ≤ D.L := D.isAdmissible.2
  have h : 0 < PeriodicLattice.torusSide D.L D.m := by
    unfold PeriodicLattice.torusSide
    positivity
  exact h
def periods : AddSubgroup (Fin 4 → ℝ) where
  carrier := Set.range (latticeTranslate D.side)
  zero_mem' := ⟨0, by funext μ; simp [latticeTranslate]⟩
  add_mem' := by
    rintro _ _ ⟨k, rfl⟩ ⟨k', rfl⟩
    exact ⟨k + k', latticeTranslate_add _ k k'⟩
  neg_mem' := by
    rintro _ ⟨k, rfl⟩
    exact ⟨-k, by funext μ; simp [latticeTranslate]⟩
def projHom : (Fin 4 → ℝ) →+ D.Torus where
  toFun := torusProj (PeriodicLattice.torusSide D.L D.m)
  map_zero' := by
    funext μ
    simp [torusProj]
  map_add' x y := by
    funext μ
    simp [torusProj]
theorem projHom_surjective : Function.Surjective D.projHom :=
  torusProj_surjective _
variable {D} in
theorem projHom_eq_iff {x y : Fin 4 → ℝ} :
    D.projHom x = D.projHom y ↔ x - y ∈ D.periods := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq h
    refine ⟨k, ?_⟩
    change latticeTranslate (PeriodicLattice.torusSide D.L D.m) k = x - y
    rw [hk]
    abel
  · rintro ⟨k, hk⟩
    have hx : x = y + latticeTranslate (PeriodicLattice.torusSide D.L D.m) k := by
      have hk' : latticeTranslate (PeriodicLattice.torusSide D.L D.m) k = x - y := hk
      rw [hk']
      abel
    rw [hx]
    exact torusProj_add_latticeTranslate _ y k
def periodDistances (v : Fin 4 → ℝ) : Set ℝ :=
  (fun γ => euclidNorm (v - γ)) '' (D.periods : Set (Fin 4 → ℝ))
def torusDist (ξ η : D.Torus) : ℝ :=
  sInf (D.periodDistances (liftPoint ξ - liftPoint η))
theorem exists_isLeast_periodDistances (v : Fin 4 → ℝ) :
    ∃ r, IsLeast (D.periodDistances v) r := by
  have hℓ := D.zero_lt_side
  refine ⟨_, ⟨latticeTranslate D.side fun μ => round (v μ / D.side), ⟨_, rfl⟩, rfl⟩, ?_⟩
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => ?_)
  have h := round_le (v μ / D.side) (k μ)
  have e : ∀ z : ℤ, v μ - D.side * (z : ℝ) = D.side * (v μ / D.side - z) := by
    intro z
    field_simp
  simp only [Pi.sub_apply, latticeTranslate, e]
  rw [sq_le_sq, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
variable {D} in
theorem periodDistances_eq_of_sub_mem {v w : Fin 4 → ℝ} (h : v - w ∈ D.periods) :
    D.periodDistances v = D.periodDistances w := by
  ext r
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨γ - (v - w), D.periods.sub_mem hγ h, ?_⟩
    change euclidNorm (w - (γ - (v - w))) = euclidNorm (v - γ)
    rw [show w - (γ - (v - w)) = v - γ by abel]
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨γ + (v - w), D.periods.add_mem hγ h, ?_⟩
    change euclidNorm (v - (γ + (v - w))) = euclidNorm (w - γ)
    rw [show v - (γ + (v - w)) = w - γ by abel]
theorem isLeast_torusDist (x y : Fin 4 → ℝ) :
    IsLeast (D.periodDistances (x - y)) (D.torusDist (D.projHom x) (D.projHom y)) := by
  have hx : liftPoint (D.projHom x) - x ∈ D.periods :=
    projHom_eq_iff.mp (torusProj_liftPoint (D.projHom x))
  have hy : liftPoint (D.projHom y) - y ∈ D.periods :=
    projHom_eq_iff.mp (torusProj_liftPoint (D.projHom y))
  have hxy : (liftPoint (D.projHom x) - liftPoint (D.projHom y)) - (x - y) ∈
      D.periods := by
    have h := D.periods.sub_mem hx hy
    have e : (liftPoint (D.projHom x) - liftPoint (D.projHom y)) - (x - y) =
        (liftPoint (D.projHom x) - x) - (liftPoint (D.projHom y) - y) := by
      abel
    rwa [e]
  obtain ⟨r, hr⟩ := D.exists_isLeast_periodDistances (x - y)
  rw [torusDist, periodDistances_eq_of_sub_mem hxy, hr.csInf_eq]
  exact hr
end TransportData
end TorusTransport
end YangMills.Construction
end
