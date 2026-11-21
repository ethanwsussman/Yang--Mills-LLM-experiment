import YangMills.Construction.Lattice.DifferenceOperatorsCellAveragesTrees
import YangMills.Construction.Lattice.TorusCharacters
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
namespace CellAverageLift
variable {d L j N : ℕ}
def angle (N : ℕ) (a : ℤ) : ℝ := 2 * Real.pi * a / N
theorem exp_angle_mul (N : ℕ) (a : ℤ) (c : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (c : ℂ) / (N : ℂ)) =
      Complex.exp (Complex.I * ((angle N a * c : ℝ) : ℂ)) := by
  congr 1
  simp only [angle]
  push_cast
  ring
theorem abs_angle_le (hN : 0 < N) {a : ℤ} (ha₁ : -((N : ℤ) / 2) ≤ a) (ha₂ : a < (N : ℤ) / 2) :
    |angle N a| ≤ Real.pi := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hz : |2 * a| ≤ (N : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  have hr : |2 * (a : ℝ)| ≤ N := by exact_mod_cast hz
  have hrew : 2 * Real.pi * (a : ℝ) = Real.pi * (2 * a) := by ring
  rw [angle, abs_div, abs_of_pos hNr, div_le_iff₀ hNr, hrew, abs_mul,
    abs_of_pos Real.pi_pos]
  exact mul_le_mul_of_nonneg_left hr Real.pi_pos.le
theorem coe_nsmul_basisStep (s : Mesh N) (μ : Fin d) (t : ℕ) :
    ((t • s.basisStep μ : GridPoint d s) : Torus d N) = axisMultiple μ ((t : ℝ) * s.h) := by
  have h : ((t • s.basisStep μ : GridPoint d s) : Torus d N) =
      t • (axisMultiple μ s.h : Torus d N) := rfl
  rw [h]
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp only [Pi.smul_apply, axisMultiple, Pi.single_eq_same]
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  · simp [axisMultiple, Pi.single_eq_of_ne hν]
theorem fineScale_pos (S : Scales d L j N) : 0 < fineScale L j := S.fineMesh.h_pos
theorem fineScale_mul (S : Scales d L j N) : fineScale L j * ((L ^ j : ℕ) : ℝ) = 1 := by
  have h : ((L : ℝ) ^ j) ≠ 0 := pow_ne_zero j (by exact_mod_cast S.factor_pos.ne')
  rw [fineScale]
  push_cast
  field_simp
def cellSite (S : Scales d L j N) (y : GridPoint d S.unitMesh) (k : Fin d → ℕ) :
    GridPoint d S.fineMesh :=
  S.unitToFine y + ∑ ν, k ν • S.fineMesh.basisStep ν
theorem coe_cellSite (S : Scales d L j N) (y : GridPoint d S.unitMesh) (k : Fin d → ℕ) :
    ((cellSite S y k : GridPoint d S.fineMesh) : Torus d N) =
      (y : Torus d N) + fun μ => (((k μ : ℝ) * fineScale L j : ℝ) : AddCircle (N : ℝ)) := by
  have hsum : ((∑ ν, k ν • S.fineMesh.basisStep ν : GridPoint d S.fineMesh) : Torus d N) =
      ∑ ν, ((k ν • S.fineMesh.basisStep ν : GridPoint d S.fineMesh) : Torus d N) :=
    map_sum (AddSubgroup.subtype (gridSubgroup d S.fineMesh)) _ _
  have hsplit : ((cellSite S y k : GridPoint d S.fineMesh) : Torus d N) =
      (y : Torus d N) +
        ((∑ ν, k ν • S.fineMesh.basisStep ν : GridPoint d S.fineMesh) : Torus d N) := rfl
  rw [hsplit, hsum]
  congr 1
  funext μ
  rw [Finset.sum_apply]
  simp only [coe_nsmul_basisStep]
  rw [Finset.sum_eq_single μ]
  · simp only [axisMultiple, Pi.single_eq_same]
    rfl
  · intro ν _ hν
    simp [axisMultiple, Pi.single_eq_of_ne hν.symm]
  · intro h
    exact absurd (mem_univ μ) h
theorem cell_coordinate_bounds (S : Scales d L j N) {t : ℕ} (ht : t < L ^ j) :
    0 ≤ (t : ℝ) * fineScale L j ∧ (t : ℝ) * fineScale L j < 1 := by
  have hx := fineScale_pos S
  refine ⟨by positivity, ?_⟩
  have ht' : (t : ℝ) < ((L ^ j : ℕ) : ℝ) := by exact_mod_cast ht
  calc (t : ℝ) * fineScale L j < ((L ^ j : ℕ) : ℝ) * fineScale L j :=
        mul_lt_mul_of_pos_right ht' hx
    _ = 1 := by rw [mul_comm, fineScale_mul S]
theorem cellSite_mem (S : Scales d L j N) (y : GridPoint d S.unitMesh) {k : Fin d → ℕ}
    (hk : ∀ ν, k ν < L ^ j) : cellSite S y k ∈ S.fineCell y := by
  simp only [Scales.fineCell, sitesInCube, mem_filter, mem_univ, true_and]
  exact ⟨fun μ => (k μ : ℝ) * fineScale L j, fun μ => cell_coordinate_bounds S (hk μ),
    coe_cellSite S y k⟩
def fourierSum (a : (Fin d → ℤ) → ℂ) (u : Torus d N) : ℂ :=
  ∑ m ∈ centeredFrequencies d N, a m * fourierCharacter m u
def realSynthesis (s : Mesh N) (a : (Fin d → ℤ) → ℂ) : SiteFun d s :=
  ofMap fun x => (fourierSum a (x : Torus d N)).re
theorem inner_laplacian_eq (s : Mesh N) (f : SiteFun d s) :
    inner ℝ f (discreteLaplacian s f) = ∑ ν, ‖forwardDiff s ν f‖ ^ 2 := by
  simp only [discreteLaplacian, LinearMap.sum_apply, LinearMap.comp_apply, inner_sum,
    LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
theorem norm_forwardDiff_sq_le (S : Scales d L j N)
    (hadd : ∀ (m : Fin d → ℤ) (u v : Torus d N),
      fourierCharacter m (u + v) = fourierCharacter m u * fourierCharacter m v)
    (haxis : ∀ (m : Fin d → ℤ) (μ : Fin d) (c : ℝ),
      fourierCharacter m (axisMultiple μ c : Torus d N) =
        Complex.exp (2 * Real.pi * Complex.I * (m μ : ℂ) * (c : ℂ) / (N : ℂ)))
    (hfine : CharactersOrthogonalOn d S.fineMesh)
    (a : (Fin d → ℤ) → ℂ) (ν : Fin d) :
    ‖forwardDiff S.fineMesh ν (realSynthesis S.fineMesh a)‖ ^ 2 ≤
      (N : ℝ) ^ d * ∑ m ∈ centeredFrequencies d N, ‖a m‖ ^ 2 * angle N (m ν) ^ 2 := by
  obtain ⟨b, hb⟩ : ∃ b : (Fin d → ℤ) → ℂ, ∀ m, b m = a m * (((fineScale L j)⁻¹ : ℝ) : ℂ) *
      (fourierCharacter m (axisMultiple ν (fineScale L j) : Torus d N) - 1) :=
    ⟨_, fun _ => rfl⟩
  have hx := (fineScale_pos S).ne'
  have hG : ∀ x : GridPoint d S.fineMesh,
      forwardDiff S.fineMesh ν (realSynthesis S.fineMesh a) x =
        (∑ m ∈ centeredFrequencies d N, b m * fourierCharacter m (x : Torus d N)).re := by
    intro x
    change (fineScale L j)⁻¹ *
      ((fourierSum a ((x + S.fineMesh.basisStep ν : GridPoint d S.fineMesh) : Torus d N)).re -
        (fourierSum a (x : Torus d N)).re) = _
    rw [← Complex.sub_re, ← Complex.re_ofReal_mul]
    congr 1
    rw [fourierSum, fourierSum, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    have h1 : fourierCharacter m ((x + S.fineMesh.basisStep ν : GridPoint d S.fineMesh) :
          Torus d N) =
        fourierCharacter m (x : Torus d N) *
          fourierCharacter m (axisMultiple ν (fineScale L j) : Torus d N) :=
      hadd m _ _
    rw [h1, hb m]
    ring
  have hpar := hfine b
  have hh : S.fineMesh.h = fineScale L j := rfl
  rw [hh] at hpar
  have hw : 0 ≤ fineScale L j ^ d := (pow_pos (fineScale_pos S) d).le
  rw [← real_inner_self_eq_norm_sq, ScaledFun.inner_eq]
  calc ∑ x, S.fineMesh.h ^ d * forwardDiff S.fineMesh ν (realSynthesis S.fineMesh a) x *
        forwardDiff S.fineMesh ν (realSynthesis S.fineMesh a) x
      ≤ ∑ x : GridPoint d S.fineMesh, fineScale L j ^ d *
          ‖∑ m ∈ centeredFrequencies d N, b m * fourierCharacter m (x : Torus d N)‖ ^ 2 := by
        refine sum_le_sum fun x _ => ?_
        rw [hG x, hh, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hw
        have h := Complex.abs_re_le_norm
          (∑ m ∈ centeredFrequencies d N, b m * fourierCharacter m (x : Torus d N))
        rw [← pow_two, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (N : ℝ) ^ d * ∑ m ∈ centeredFrequencies d N, ‖b m‖ ^ 2 := by
        rw [← mul_sum]
        exact hpar
    _ ≤ (N : ℝ) ^ d * ∑ m ∈ centeredFrequencies d N, ‖a m‖ ^ 2 * angle N (m ν) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun m _ => ?_) (by positivity)
        have he : ‖fourierCharacter m (axisMultiple ν (fineScale L j) : Torus d N) - 1‖ ≤
            |angle N (m ν)| * fineScale L j := by
          rw [haxis, exp_angle_mul]
          have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := angle N (m ν) * fineScale L j)
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (fineScale_pos S)] at h
          exact h
        have hξ : ‖(((fineScale L j)⁻¹ : ℝ) : ℂ)‖ = (fineScale L j)⁻¹ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (fineScale_pos S))]
        have hn : ‖b m‖ ≤ ‖a m‖ * |angle N (m ν)| := by
          rw [hb m, norm_mul, norm_mul, hξ]
          have hξ0 : 0 ≤ (fineScale L j)⁻¹ := (inv_pos.mpr (fineScale_pos S)).le
          calc ‖a m‖ * (fineScale L j)⁻¹ *
                ‖fourierCharacter m (axisMultiple ν (fineScale L j) : Torus d N) - 1‖
              ≤ ‖a m‖ * (fineScale L j)⁻¹ * (|angle N (m ν)| * fineScale L j) :=
                mul_le_mul_of_nonneg_left he (mul_nonneg (norm_nonneg _) hξ0)
            _ = ‖a m‖ * |angle N (m ν)| := by field_simp
        calc ‖b m‖ ^ 2 ≤ (‖a m‖ * |angle N (m ν)|) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hn 2
          _ = ‖a m‖ ^ 2 * angle N (m ν) ^ 2 := by rw [mul_pow, sq_abs]
theorem energy_le (S : Scales d L j N)
    (hadd : ∀ (m : Fin d → ℤ) (u v : Torus d N),
      fourierCharacter m (u + v) = fourierCharacter m u * fourierCharacter m v)
    (haxis : ∀ (m : Fin d → ℤ) (μ : Fin d) (c : ℝ),
      fourierCharacter m (axisMultiple μ c : Torus d N) =
        Complex.exp (2 * Real.pi * Complex.I * (m μ : ℂ) * (c : ℂ) / (N : ℂ)))
    (hfine : CharactersOrthogonalOn d S.fineMesh) (a : (Fin d → ℤ) → ℂ) :
    inner ℝ (realSynthesis S.fineMesh a)
        (discreteLaplacian S.fineMesh (realSynthesis S.fineMesh a)) ≤
      (N : ℝ) ^ d * ∑ m ∈ centeredFrequencies d N, ‖a m‖ ^ 2 * ((d : ℝ) * Real.pi ^ 2) := by
  rw [inner_laplacian_eq]
  calc ∑ ν, ‖forwardDiff S.fineMesh ν (realSynthesis S.fineMesh a)‖ ^ 2
      ≤ ∑ ν : Fin d, (N : ℝ) ^ d *
          ∑ m ∈ centeredFrequencies d N, ‖a m‖ ^ 2 * angle N (m ν) ^ 2 :=
        sum_le_sum fun ν _ => norm_forwardDiff_sq_le S hadd haxis hfine a ν
    _ = (N : ℝ) ^ d *
          ∑ m ∈ centeredFrequencies d N, ‖a m‖ ^ 2 * ∑ ν : Fin d, angle N (m ν) ^ 2 := by
        rw [← mul_sum, sum_comm]
        simp only [mul_sum]
    _ ≤ (N : ℝ) ^ d *
          ∑ m ∈ centeredFrequencies d N, ‖a m‖ ^ 2 * ((d : ℝ) * Real.pi ^ 2) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun m hm => ?_) (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hbound : ∀ ν : Fin d, angle N (m ν) ^ 2 ≤ Real.pi ^ 2 := fun ν => by
          have h := mem_Ico.mp (Fintype.mem_piFinset.mp hm ν)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_angle_le S.period_pos h.1 h.2) 2
        calc ∑ ν : Fin d, angle N (m ν) ^ 2 ≤ ∑ _ν : Fin d, Real.pi ^ 2 :=
              sum_le_sum fun ν _ => hbound ν
          _ = (d : ℝ) * Real.pi ^ 2 := by
              rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
theorem norm_sq_eq (S : Scales d L j N)
    (hunit : CharactersOrthogonalOn d S.unitMesh) (b : SiteFun d S.unitMesh)
    (c : (Fin d → ℤ) → ℂ)
    (hc : ∀ y : GridPoint d S.unitMesh, ((b y : ℝ) : ℂ) =
      ∑ m ∈ centeredFrequencies d N, c m * fourierCharacter m (y : Torus d N)) :
    ‖b‖ ^ 2 = (N : ℝ) ^ d * ∑ m ∈ centeredFrequencies d N, ‖c m‖ ^ 2 := by
  have h := hunit c
  have hh : S.unitMesh.h = 1 := rfl
  rw [hh, one_pow, one_mul] at h
  rw [← h, ← real_inner_self_eq_norm_sq, ScaledFun.inner_eq]
  refine sum_congr rfl fun y _ => ?_
  rw [← hc y, hh, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, pow_two]
end CellAverageLift
end YangMills.Construction.PeriodicLattice
