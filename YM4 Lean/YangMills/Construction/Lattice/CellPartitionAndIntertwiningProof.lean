import YangMills.Construction.Lattice.PeriodicTorus
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace Cells
variable {d N : ℕ}
theorem exists_int_of_mem_zmultiples {a : ℝ} {u : AddCircle (N : ℝ)}
    (hu : u ∈ AddSubgroup.zmultiples ((a : ℝ) : AddCircle (N : ℝ))) :
    ∃ n : ℤ, u = (((n : ℝ) * a : ℝ) : AddCircle (N : ℝ)) := by
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hu
  refine ⟨n, ?_⟩
  rw [← zsmul_eq_mul, AddCircle.coe_zsmul]
theorem int_mul_mem_zmultiples (a : ℝ) (n : ℤ) :
    (((n : ℝ) * a : ℝ) : AddCircle (N : ℝ)) ∈
      AddSubgroup.zmultiples ((a : ℝ) : AddCircle (N : ℝ)) := by
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨n, ?_⟩
  rw [← zsmul_eq_mul, AddCircle.coe_zsmul]
theorem exists_coarse_add_rem {s s' : Mesh N} {m : ℕ} (hm : s'.h = m * s.h) (hmpos : 0 < m)
    {u : AddCircle (N : ℝ)}
    (hu : u ∈ AddSubgroup.zmultiples ((s.h : ℝ) : AddCircle (N : ℝ))) :
    ∃ (p : ℤ) (r : ℕ), r < m ∧
      u = (((p : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) +
        (((r : ℝ) * s.h : ℝ) : AddCircle (N : ℝ)) := by
  obtain ⟨n, rfl⟩ := exists_int_of_mem_zmultiples hu
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hmz : (0 : ℤ) < m := by exact_mod_cast hmpos
  have hr0 := Int.emod_nonneg n hm0
  have hr1 := Int.emod_lt_of_pos n hmz
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le hr0
  refine ⟨n / m, r, ?_, ?_⟩
  · rw [hr] at hr1
    exact_mod_cast hr1
  · have hdiv : n = m * (n / m) + r := by rw [← hr]; exact (Int.mul_ediv_add_emod n m).symm
    have hdivR : (n : ℝ) = m * ((n / m : ℤ) : ℝ) + r := by exact_mod_cast hdiv
    rw [← AddCircle.coe_add, hm]
    congr 1
    rw [hdivR]
    ring
theorem coarse_add_rem_unique (s' : Mesh N) {p q : ℤ} {w w' : ℝ} (hw : 0 ≤ w ∧ w < s'.h)
    (hw' : 0 ≤ w' ∧ w' < s'.h)
    (he : (((p : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) + (w : AddCircle (N : ℝ)) =
      (((q : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) + (w' : AddCircle (N : ℝ))) :
    (((p : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) = (((q : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) ∧
      w = w' := by
  have hz : (((p : ℝ) * s'.h + w - ((q : ℝ) * s'.h + w') : ℝ) : AddCircle (N : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_add, AddCircle.coe_add, he, sub_self]
  obtain ⟨l, hl⟩ := (AddCircle.coe_eq_zero_iff _).mp hz
  rw [zsmul_eq_mul, s'.period_eq] at hl
  have hk : (((l * s'.count - p + q : ℤ) : ℝ)) * s'.h = w - w' := by
    push_cast
    linarith
  have hk1 : (((l * s'.count - p + q : ℤ) : ℝ)) < 1 := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [hw.1, hw.2, hw'.1, hw'.2]
  have hk2 : (-1 : ℝ) < (((l * s'.count - p + q : ℤ) : ℝ)) := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [hw.1, hw.2, hw'.1, hw'.2]
  have hk0 : l * (s'.count : ℤ) - p + q = 0 := by
    have h1 : l * (s'.count : ℤ) - p + q < 1 := by exact_mod_cast hk1
    have h2 : -1 < l * (s'.count : ℤ) - p + q := by exact_mod_cast hk2
    omega
  have hww : w = w' := by
    rw [hk0] at hk
    push_cast at hk
    linarith
  subst hww
  exact ⟨add_right_cancel he, rfl⟩
theorem mem_sitesInCube {s : Mesh N} {u : Torus d N} {r : ℝ} {x : GridPoint d s} :
    x ∈ sitesInCube s u r ↔ ∃ w : Fin d → ℝ, (∀ μ, 0 ≤ w μ ∧ w μ < r) ∧
      (x : Torus d N) = u + fun μ => (w μ : AddCircle (N : ℝ)) := by
  simp only [sitesInCube, mem_filter, mem_univ, true_and]
  exact Iff.rfl
theorem existsUnique_cell {s s' : Mesh N} {m : ℕ} (hm : s'.h = m * s.h) (hmpos : 0 < m)
    (x : GridPoint d s) : ∃! y : GridPoint d s', x ∈ sitesInCube s (y : Torus d N) s'.h := by
  have hx : ∀ μ, ∃ (p : ℤ) (r : ℕ), r < m ∧
      (x : Torus d N) μ = (((p : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) +
        (((r : ℝ) * s.h : ℝ) : AddCircle (N : ℝ)) :=
    fun μ => exists_coarse_add_rem hm hmpos (x.2 μ (Set.mem_univ μ))
  choose p r hr hxr using hx
  have hs := s.h_pos
  have hbound : ∀ μ, 0 ≤ (r μ : ℝ) * s.h ∧ (r μ : ℝ) * s.h < s'.h := fun μ => by
    refine ⟨by positivity, ?_⟩
    rw [hm]
    have : (r μ : ℝ) < m := by exact_mod_cast hr μ
    exact mul_lt_mul_of_pos_right this hs
  let y : GridPoint d s' := ⟨fun μ => (((p μ : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)),
    fun μ _ => int_mul_mem_zmultiples _ _⟩
  refine ⟨y, mem_sitesInCube.mpr ⟨fun μ => (r μ : ℝ) * s.h, hbound, funext hxr⟩, ?_⟩
  intro y₂ hy₂
  obtain ⟨w, hw, hxw⟩ := mem_sitesInCube.mp hy₂
  refine Subtype.ext (funext fun μ => ?_)
  obtain ⟨q, hq⟩ := exists_int_of_mem_zmultiples (y₂.2 μ (Set.mem_univ μ))
  have he : (((q : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) + (w μ : AddCircle (N : ℝ)) =
      (((p μ : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) +
        (((r μ : ℝ) * s.h : ℝ) : AddCircle (N : ℝ)) := by
    rw [← hq, ← hxr μ, hxw]
    rfl
  have := (coarse_add_rem_unique s' (hw μ) (hbound μ) he).1
  rw [hq, this]
theorem card_cell {s s' : Mesh N} {m : ℕ} (hm : s'.h = m * s.h) (hmpos : 0 < m)
    (hle : gridSubgroup d s' ≤ gridSubgroup d s) (y : GridPoint d s') :
    (sitesInCube s (y : Torus d N) s'.h).card = m ^ d := by
  have hs := s.h_pos
  have hbound : ∀ r : ℕ, r < m → 0 ≤ (r : ℝ) * s.h ∧ (r : ℝ) * s.h < s'.h := fun r hr => by
    refine ⟨by positivity, ?_⟩
    rw [hm]
    have : (r : ℝ) < m := by exact_mod_cast hr
    exact mul_lt_mul_of_pos_right this hs
  have hy : ∀ μ, ∃ q : ℤ, (y : Torus d N) μ = (((q : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) :=
    fun μ => exists_int_of_mem_zmultiples (y.2 μ (Set.mem_univ μ))
  choose q hq using hy
  have hmem : ∀ σ : Fin d → Fin m, ((y : Torus d N) + fun μ =>
      ((((σ μ : ℕ) : ℝ) * s.h : ℝ) : AddCircle (N : ℝ))) ∈ gridSubgroup d s := fun σ =>
    (gridSubgroup d s).add_mem (hle y.2) fun μ _ => by
      simp
  let φ : (Fin d → Fin m) → GridPoint d s := fun σ => ⟨_, hmem σ⟩
  have hinj : Function.Injective φ := by
    intro σ τ hστ
    funext μ
    have h1 := congrFun (congrArg Subtype.val hστ) μ
    have h2 : (((q μ : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) +
        ((((σ μ : ℕ) : ℝ) * s.h : ℝ) : AddCircle (N : ℝ)) =
        (((q μ : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) +
        ((((τ μ : ℕ) : ℝ) * s.h : ℝ) : AddCircle (N : ℝ)) := by
      rw [← hq μ]
      exact h1
    have h3 := (coarse_add_rem_unique s' (hbound _ (σ μ).2) (hbound _ (τ μ).2) h2).2
    have h4 : ((σ μ : ℕ) : ℝ) = ((τ μ : ℕ) : ℝ) := mul_right_cancel₀ hs.ne' h3
    exact Fin.ext (by exact_mod_cast h4)
  have himg : sitesInCube s (y : Torus d N) s'.h = univ.image φ := by
    ext x
    simp only [mem_image, mem_univ, true_and]
    constructor
    · intro hx
      obtain ⟨w, hw, hxw⟩ := mem_sitesInCube.mp hx
      have hc : ∀ μ, ∃ (p : ℤ) (r : ℕ), r < m ∧
          (x : Torus d N) μ = (((p : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) +
            (((r : ℝ) * s.h : ℝ) : AddCircle (N : ℝ)) :=
        fun μ => exists_coarse_add_rem hm hmpos (x.2 μ (Set.mem_univ μ))
      choose p r hr hxr using hc
      refine ⟨fun μ => ⟨r μ, hr μ⟩, Subtype.ext (funext fun μ => ?_)⟩
      have he : (((q μ : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) + (w μ : AddCircle (N : ℝ)) =
          (((p μ : ℝ) * s'.h : ℝ) : AddCircle (N : ℝ)) +
            (((r μ : ℝ) * s.h : ℝ) : AddCircle (N : ℝ)) := by
        rw [← hq μ, ← hxr μ, hxw]
        rfl
      have h5 := (coarse_add_rem_unique s' (hw μ) (hbound _ (hr μ)) he).2
      have h6 : (x : Torus d N) μ = (y : Torus d N) μ + (w μ : AddCircle (N : ℝ)) := by
        rw [hxw]
        rfl
      rw [h6, h5]
      rfl
    · rintro ⟨σ, rfl⟩
      exact mem_sitesInCube.mpr ⟨fun μ => ((σ μ : ℕ) : ℝ) * s.h,
        fun μ => hbound _ (σ μ).2, rfl⟩
  rw [himg, card_image_of_injective _ hinj]
  simp
theorem image_add_cell {s s' : Mesh N} (hle : gridSubgroup d s' ≤ gridSubgroup d s) (r : ℝ)
    (y z : GridPoint d s') :
    (fun x => x + AddSubgroup.inclusion hle z) ''
        (sitesInCube s (y : Torus d N) r : Set (GridPoint d s)) =
      sitesInCube s ((y + z : GridPoint d s') : Torus d N) r := by
  ext x
  simp only [Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨x₀, hx₀, rfl⟩
    obtain ⟨w, hw, hxw⟩ := mem_sitesInCube.mp hx₀
    refine mem_sitesInCube.mpr ⟨w, hw, ?_⟩
    change (x₀ : Torus d N) + (z : Torus d N) = ((y : Torus d N) + (z : Torus d N)) + _
    rw [hxw]
    abel
  · intro hx
    obtain ⟨w, hw, hxw⟩ := mem_sitesInCube.mp hx
    refine ⟨x - AddSubgroup.inclusion hle z, mem_sitesInCube.mpr ⟨w, hw, ?_⟩, sub_add_cancel _ _⟩
    change (x : Torus d N) - (z : Torus d N) = _
    rw [hxw]
    change (y : Torus d N) + (z : Torus d N) + _ - (z : Torus d N) = _
    abel
theorem sum_cell_add {s s' : Mesh N} (hle : gridSubgroup d s' ≤ gridSubgroup d s) (r : ℝ)
    (y z : GridPoint d s') (g : GridPoint d s → ℝ) :
    ∑ x ∈ sitesInCube s ((y + z : GridPoint d s') : Torus d N) r, g x =
      ∑ x ∈ sitesInCube s (y : Torus d N) r, g (x + AddSubgroup.inclusion hle z) := by
  classical
  have himg : sitesInCube s ((y + z : GridPoint d s') : Torus d N) r =
      (sitesInCube s (y : Torus d N) r).image fun x => x + AddSubgroup.inclusion hle z := by
    apply Finset.coe_injective
    rw [Finset.coe_image, image_add_cell]
  rw [himg, sum_image fun a _ b _ h => add_right_cancel h]
end Cells
end YangMills.Construction.PeriodicLattice
