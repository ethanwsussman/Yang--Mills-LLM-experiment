import YangMills.Construction.Towers.FourierSumsOnTheSitesOfTheFinestLattice
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.FinestFourierSums
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (toComplexVec bilinDot castVec intShift)
open PlaneWaves (VertexClass fourierCoeff freqBox freqWindow fourierPhase shiftedFreq)
open PlaneWaveCalculus (integerWave tracelessPairing expWave)
theorem window_geom_sum_eq_zero (M : ℕ) {ζ : ℂ} (h : ζ ^ (2 * M + 1) = 1) (h1 : ζ ≠ 1) :
    ∑ j ∈ Finset.Icc (-(M : ℤ)) M, ζ ^ j = 0 := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp at h
  have himg : Finset.Icc (-(M : ℤ)) M =
      (Finset.range (2 * M + 1)).image fun i : ℕ => (i : ℤ) - M := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨(j + M).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [himg, Finset.sum_image (fun a _ b _ e => by simpa using e)]
  have e : ∀ i : ℕ, ζ ^ ((i : ℤ) - M) = ζ ^ (-(M : ℤ)) * ζ ^ i := fun i => by
    rw [sub_eq_add_neg, add_comm, zpow_add₀ h0, zpow_natCast]
  simp only [e, ← Finset.mul_sum]
  have g := mul_geom_sum ζ (2 * M + 1)
  rw [h, sub_self] at g
  rw [(mul_eq_zero.mp g).resolve_left (sub_ne_zero.mpr h1), mul_zero]
theorem window_sum_rootPow (M : ℕ) {w : ℂ} (hw : IsPrimitiveRoot w (2 * M + 1)) (a : ℤ) :
    ∑ j ∈ Finset.Icc (-(M : ℤ)) M, (w ^ a) ^ j =
      if ((2 * M + 1 : ℕ) : ℤ) ∣ a then ((2 * M + 1 : ℕ) : ℂ) else 0 := by
  split_ifs with h
  · rw [(hw.zpow_eq_one_iff_dvd a).mpr h]
    simp only [one_zpow, Finset.sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
    have : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
    rw [this]
  · refine window_geom_sum_eq_zero M ?_ fun e => h ((hw.zpow_eq_one_iff_dvd a).mp e)
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw.pow_eq_one, one_zpow]
theorem box_sum_rootPow (M : ℕ) {w : ℂ} (hw : IsPrimitiveRoot w (2 * M + 1)) (a : Fin 4 → ℤ) :
    ∑ n ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(M : ℤ)) M), w ^ dotProduct n a =
      if ∀ μ, ((2 * M + 1 : ℕ) : ℤ) ∣ a μ then ((2 * M + 1 : ℕ) : ℂ) ^ 4 else 0 := by
  have hw0 : w ≠ 0 := hw.ne_zero (by omega)
  have e : ∀ n : Fin 4 → ℤ, w ^ dotProduct n a = ∏ μ, (w ^ a μ) ^ n μ := fun n => by
    simp only [dotProduct, Fin.sum_univ_four, Fin.prod_univ_four, zpow_add₀ hw0]
    simp only [← zpow_mul, mul_comm]
  simp only [e]
  rw [← Finset.prod_univ_sum (fun _ : Fin 4 => Finset.Icc (-(M : ℤ)) M)
    (fun μ j => (w ^ a μ) ^ j)]
  simp only [window_sum_rootPow M hw]
  split_ifs with h
  · rw [Finset.prod_congr rfl fun μ _ => if_pos (h μ)]
    simp
  · obtain ⟨μ, hμ⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ μ) (if_neg hμ)
section Window
variable {L k : ℕ}
def halfSide (L k : ℕ) : ℕ := L ^ k / 2
theorem two_mul_halfSide_add_one (hL : Conventions.IsAdmissibleBlockingFactor L) :
    2 * halfSide L k + 1 = L ^ k := by
  have h : Odd (L ^ k) := hL.1.pow
  obtain ⟨r, hr⟩ := h
  unfold halfSide
  omega
theorem meshAt_zero_eq (L k : ℕ) : meshAt L k 0 = ((L ^ k : ℕ) : ℝ)⁻¹ := by
  simp [meshAt, zpow_neg]
theorem sidePow_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < L ^ k := by
  rw [← two_mul_halfSide_add_one hL]
  omega
theorem side_mul_meshAt_zero (hL : Conventions.IsAdmissibleBlockingFactor L) :
    ((L ^ k : ℕ) : ℝ) * meshAt L k 0 = 1 := by
  rw [meshAt_zero_eq]
  exact mul_inv_cancel₀ (by exact_mod_cast (sidePow_pos hL).ne')
theorem freqWindow_eq_Icc (hL : Conventions.IsAdmissibleBlockingFactor L) :
    freqWindow L k = Finset.Icc (-(halfSide L k : ℤ)) (halfSide L k) := by
  have hN : (((L ^ k : ℕ)) : ℝ) = 2 * (halfSide L k : ℝ) + 1 := by
    rw [← two_mul_halfSide_add_one hL]
    push_cast
    ring
  have e : ⌊1 / 2 * ((finestMesh L k)⁻¹ - 1)⌋ = (halfSide L k : ℤ) := by
    have : 1 / 2 * ((finestMesh L k)⁻¹ - 1) = (((halfSide L k : ℤ)) : ℝ) := by
      rw [finestMesh, meshAt_zero_eq, inv_inv, hN]
      push_cast
      ring
    rw [this, Int.floor_intCast]
  rw [freqWindow, e]
theorem freqBox_eq_piFinset (hL : Conventions.IsAdmissibleBlockingFactor L) :
    freqBox L k =
      Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(halfSide L k : ℤ)) (halfSide L k) := by
  rw [freqBox, freqWindow_eq_Icc hL]
theorem neg_mem_freqBox (hL : Conventions.IsAdmissibleBlockingFactor L) {m : Fin 4 → ℤ}
    (hm : m ∈ freqBox L k) : -m ∈ freqBox L k := by
  rw [freqBox_eq_piFinset hL, Fintype.mem_piFinset] at hm ⊢
  intro μ
  have := Finset.mem_Icc.mp (hm μ)
  simp only [Pi.neg_apply, Finset.mem_Icc]
  omega
theorem eq_of_side_dvd_sub (hL : Conventions.IsAdmissibleBlockingFactor L) {n n' : Fin 4 → ℤ}
    (hn : n ∈ freqBox L k) (hn' : n' ∈ freqBox L k)
    (h : ∀ μ, ((L ^ k : ℕ) : ℤ) ∣ n μ - n' μ) : n = n' := by
  rw [freqBox_eq_piFinset hL, Fintype.mem_piFinset] at hn hn'
  funext μ
  have a := Finset.mem_Icc.mp (hn μ)
  have b := Finset.mem_Icc.mp (hn' μ)
  have hN : ((L ^ k : ℕ) : ℤ) = 2 * (halfSide L k : ℤ) + 1 := by
    rw [← two_mul_halfSide_add_one hL]
    push_cast
    ring
  have z := Int.eq_zero_of_abs_lt_dvd (h μ) (by rw [abs_lt]; omega)
  omega
theorem exists_freqBox_add_smul (hL : Conventions.IsAdmissibleBlockingFactor L) (z : Fin 4 → ℤ) :
    ∃ n ∈ freqBox L k, ∃ v : Fin 4 → ℤ, z = n + ((L ^ k : ℕ) : ℤ) • v := by
  have hN : ((L ^ k : ℕ) : ℤ) = 2 * (halfSide L k : ℤ) + 1 := by
    rw [← two_mul_halfSide_add_one hL]
    push_cast
    ring
  have hpos : (0 : ℤ) < ((L ^ k : ℕ) : ℤ) := by omega
  have one : ∀ t : ℤ, ∃ j ∈ Finset.Icc (-(halfSide L k : ℤ)) (halfSide L k),
      ∃ v : ℤ, t = j + ((L ^ k : ℕ) : ℤ) * v := fun t => by
    refine ⟨(t + halfSide L k) % ((L ^ k : ℕ) : ℤ) - halfSide L k, ?_,
      (t + halfSide L k) / ((L ^ k : ℕ) : ℤ), ?_⟩
    · have a := Int.emod_nonneg (t + halfSide L k) hpos.ne'
      have b := Int.emod_lt_of_pos (t + halfSide L k) hpos
      rw [Finset.mem_Icc]
      omega
    · have := Int.emod_add_mul_ediv (t + halfSide L k) ((L ^ k : ℕ) : ℤ)
      linarith
  choose j hj v hv using one
  refine ⟨fun μ => j (z μ), ?_, fun μ => v (z μ), ?_⟩
  · rw [freqBox_eq_piFinset hL, Fintype.mem_piFinset]
    exact fun μ => hj _
  · funext μ
    simpa using hv (z μ)
end Window
section Sites
variable {L k : ℕ}
def gridPoint (L k : ℕ) (z : Fin 4 → ℤ) : FullSpace.Vertex L k 0 :=
  ⟨fun μ => (z μ : ℝ) * meshAt L k 0, z, fun _ => rfl⟩
theorem exists_eq_gridPoint (x : FullSpace.Vertex L k 0) : ∃ z, x = gridPoint L k z := by
  obtain ⟨x, z, hz⟩ := x
  exact ⟨z, Subtype.ext (funext hz)⟩
theorem meshAt_zero_ne_zero (hL : Conventions.IsAdmissibleBlockingFactor L) :
    meshAt L k 0 ≠ 0 := by
  intro h
  have := side_mul_meshAt_zero (k := k) hL
  rw [h] at this
  simp at this
theorem gridPoint_injective (hL : Conventions.IsAdmissibleBlockingFactor L) :
    Function.Injective (gridPoint L k) := by
  intro z z' e
  funext μ
  have h : (z μ : ℝ) * meshAt L k 0 = (z' μ : ℝ) * meshAt L k 0 :=
    congrFun (congrArg Subtype.val e) μ
  exact_mod_cast mul_right_cancel₀ (meshAt_zero_ne_zero hL) h
theorem coe_gridPoint_add_smul (hL : Conventions.IsAdmissibleBlockingFactor L) (z n : Fin 4 → ℤ) :
    ((gridPoint L k (z + ((L ^ k : ℕ) : ℤ) • n) : FullSpace.Vertex L k 0) : AmbientSpace) =
      (gridPoint L k z : AmbientSpace) + castVec n := by
  funext μ
  have h := side_mul_meshAt_zero (k := k) hL
  show (((z + ((L ^ k : ℕ) : ℤ) • n) μ : ℤ) : ℝ) * meshAt L k 0 =
    (z μ : ℝ) * meshAt L k 0 + (n μ : ℝ)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast at h ⊢
  linear_combination (n μ : ℝ) * h
theorem vertexImage_intShift_gridPoint (hL : Conventions.IsAdmissibleBlockingFactor L)
    (z n : Fin 4 → ℤ) :
    FullSpace.vertexImage (intShift n) (gridPoint L k z) =
      gridPoint L k (z + ((L ^ k : ℕ) : ℤ) • n) := by
  have hs := Classical.epsilon_spec
    (p := fun x' : FullSpace.Vertex L k 0 => (x' : AmbientSpace) = intShift n (gridPoint L k z))
    ⟨gridPoint L k (z + ((L ^ k : ℕ) : ℤ) • n), coe_gridPoint_add_smul hL z n⟩
  exact Subtype.ext (hs.trans (coe_gridPoint_add_smul hL z n).symm)
theorem coe_vertexImage_intShift (hL : Conventions.IsAdmissibleBlockingFactor L) (n : Fin 4 → ℤ)
    (x : FullSpace.Vertex L k 0) :
    ((FullSpace.vertexImage (intShift n) x : FullSpace.Vertex L k 0) : AmbientSpace) =
      (x : AmbientSpace) + castVec n := by
  obtain ⟨z, rfl⟩ := exists_eq_gridPoint x
  rw [vertexImage_intShift_gridPoint hL, coe_gridPoint_add_smul hL]
theorem gridPoint_periodic {V : Type} {g : FullSpace.Vertex L k 0 → V}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hg : IsIntPeriodic L k g) (z v : Fin 4 → ℤ) :
    g (gridPoint L k (z + ((L ^ k : ℕ) : ℤ) • v)) = g (gridPoint L k z) := by
  rw [← vertexImage_intShift_gridPoint hL]
  exact hg v _
def residueClass (x : FullSpace.Vertex L k 0) : Fin 4 → ZMod (L ^ k) :=
  fun μ => ((Classical.choose (exists_eq_gridPoint x) μ : ℤ) : ZMod (L ^ k))
theorem residueClass_gridPoint (hL : Conventions.IsAdmissibleBlockingFactor L) (z : Fin 4 → ℤ) :
    residueClass (gridPoint L k z) = fun μ => ((z μ : ℤ) : ZMod (L ^ k)) := by
  have h := gridPoint_injective hL
    (Classical.choose_spec (exists_eq_gridPoint (gridPoint L k z)))
  unfold residueClass
  rw [← h]
theorem residueClass_eq_of_shift (hL : Conventions.IsAdmissibleBlockingFactor L)
    (x x' : FullSpace.Vertex L k 0)
    (h : ∃ n : Fin 4 → ℤ, x' = FullSpace.vertexImage (intShift n) x) :
    residueClass x = residueClass x' := by
  obtain ⟨n, rfl⟩ := h
  obtain ⟨z, rfl⟩ := exists_eq_gridPoint x
  rw [vertexImage_intShift_gridPoint hL, residueClass_gridPoint hL, residueClass_gridPoint hL]
  funext μ
  have h0 : (((L ^ k : ℕ) : ℤ) : ZMod (L ^ k)) = 0 := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_self _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul, h0, zero_mul,
    add_zero]
def vertexClassOf (L k : ℕ) (n : freqBox L k) : VertexClass L k :=
  Quot.mk _ (gridPoint L k n.1)
theorem vertexClassOf_bijective (hL : Conventions.IsAdmissibleBlockingFactor L) :
    Function.Bijective (vertexClassOf L k) := by
  constructor
  · rintro ⟨n, hn⟩ ⟨n', hn'⟩ e
    have e' := congrArg (Quot.lift residueClass (residueClass_eq_of_shift hL)) e
    change residueClass (gridPoint L k n) = residueClass (gridPoint L k n') at e'
    rw [residueClass_gridPoint hL, residueClass_gridPoint hL] at e'
    refine Subtype.ext (eq_of_side_dvd_sub hL hn hn' fun μ => ?_)
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun e' μ).symm
  · intro d
    induction d using Quot.ind with
    | mk x =>
      obtain ⟨z, rfl⟩ := exists_eq_gridPoint x
      obtain ⟨n, hn, v, rfl⟩ := exists_freqBox_add_smul (k := k) hL z
      exact ⟨⟨n, hn⟩, Quot.sound ⟨v, (vertexImage_intShift_gridPoint hL n v).symm⟩⟩
theorem finsum_vertexClass_eq_sum {V : Type} [AddCommMonoid V]
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {h : FullSpace.Vertex L k 0 → V} (hh : IsIntPeriodic L k h) :
    ∑ᶠ d : VertexClass L k, h (Quot.out d) = ∑ n ∈ freqBox L k, h (gridPoint L k n) := by
  let H : VertexClass L k → V := Quot.lift h (by
    rintro x _ ⟨n, rfl⟩
    exact (hh n x).symm)
  have e : ∀ d : VertexClass L k, h (Quot.out d) = H d := fun d => by
    have : H (Quot.mk _ (Quot.out d)) = H d := congrArg H (Quot.out_eq d)
    exact this
  simp only [e]
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (vertexClassOf_bijective hL)),
    finsum_eq_sum_of_fintype]
  exact Finset.sum_coe_sort (freqBox L k) fun n => h (gridPoint L k n)
end Sites
section Waves
variable {L k : ℕ}
def unitRoot (L k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((L ^ k : ℕ) : ℂ))
theorem unitRoot_ne_zero : unitRoot L k ≠ 0 := Complex.exp_ne_zero _
theorem unitRoot_isPrimitiveRoot (hL : Conventions.IsAdmissibleBlockingFactor L) :
    IsPrimitiveRoot (unitRoot L k) (2 * halfSide L k + 1) := by
  rw [two_mul_halfSide_add_one hL]
  exact Complex.isPrimitiveRoot_exp (L ^ k) (sidePow_pos hL).ne'
theorem unitRoot_zpow_add_side_mul (hL : Conventions.IsAdmissibleBlockingFactor L) (t s : ℤ) :
    unitRoot L k ^ (t + ((L ^ k : ℕ) : ℤ) * s) = unitRoot L k ^ t := by
  have h : unitRoot L k ^ (L ^ k) = 1 := by
    have := (unitRoot_isPrimitiveRoot (k := k) hL).pow_eq_one
    rwa [two_mul_halfSide_add_one hL] at this
  rw [zpow_add₀ unitRoot_ne_zero, zpow_mul, zpow_natCast, h, one_zpow, mul_one]
theorem integerWave_gridPoint (m z : Fin 4 → ℤ) :
    integerWave m (gridPoint L k z : AmbientSpace) = unitRoot L k ^ dotProduct m z := by
  rw [unitRoot, ← Complex.exp_int_mul, integerWave]
  congr 1
  simp only [bilinDot, toComplexVec, castVec, gridPoint, meshAt_zero_eq, dotProduct,
    Fin.sum_univ_four]
  push_cast
  ring
theorem fourierPhase_gridPoint (m z : Fin 4 → ℤ) :
    fourierPhase m (gridPoint L k z : AmbientSpace) = unitRoot L k ^ (-dotProduct m z) := by
  rw [unitRoot, ← Complex.exp_int_mul, fourierPhase]
  congr 1
  simp only [bilinDot, toComplexVec, castVec, gridPoint, meshAt_zero_eq, dotProduct,
    Fin.sum_univ_four]
  push_cast
  ring
theorem integerWave_isIntPeriodic (hL : Conventions.IsAdmissibleBlockingFactor L)
    (m : Fin 4 → ℤ) :
    IsIntPeriodic L k fun x : FullSpace.Vertex L k 0 => integerWave m (x : AmbientSpace) := by
  intro n x
  obtain ⟨z, rfl⟩ := exists_eq_gridPoint x
  show integerWave m
      (FullSpace.vertexImage (intShift n) (gridPoint L k z) : FullSpace.Vertex L k 0) =
    integerWave m (gridPoint L k z : AmbientSpace)
  rw [vertexImage_intShift_gridPoint hL, integerWave_gridPoint, integerWave_gridPoint,
    dotProduct_add, dotProduct_smul, smul_eq_mul, unitRoot_zpow_add_side_mul hL]
theorem fourierPhase_isIntPeriodic (hL : Conventions.IsAdmissibleBlockingFactor L)
    (m : Fin 4 → ℤ) :
    IsIntPeriodic L k fun x : FullSpace.Vertex L k 0 => fourierPhase m (x : AmbientSpace) := by
  intro n x
  obtain ⟨z, rfl⟩ := exists_eq_gridPoint x
  show fourierPhase m
      (FullSpace.vertexImage (intShift n) (gridPoint L k z) : FullSpace.Vertex L k 0) =
    fourierPhase m (gridPoint L k z : AmbientSpace)
  rw [vertexImage_intShift_gridPoint hL, fourierPhase_gridPoint, fourierPhase_gridPoint,
    dotProduct_add, dotProduct_smul, smul_eq_mul]
  have e : -(dotProduct m z + ((L ^ k : ℕ) : ℤ) * dotProduct m n) =
      -dotProduct m z + ((L ^ k : ℕ) : ℤ) * -dotProduct m n := by ring
  rw [e, unitRoot_zpow_add_side_mul hL]
theorem conj_unitRoot_zpow (hL : Conventions.IsAdmissibleBlockingFactor L) (t : ℤ) :
    conj (unitRoot L k ^ t) = unitRoot L k ^ (-t) := by
  have hn : ‖unitRoot L k‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (unitRoot_isPrimitiveRoot hL).pow_eq_one (by omega)
  rw [map_zpow₀, ← Complex.inv_eq_conj hn, inv_zpow, zpow_neg]
theorem freqBox_sum_unitRoot (hL : Conventions.IsAdmissibleBlockingFactor L) (a : Fin 4 → ℤ) :
    ∑ n ∈ freqBox L k, unitRoot L k ^ dotProduct n a =
      if ∀ μ, ((L ^ k : ℕ) : ℤ) ∣ a μ then ((L ^ k : ℕ) : ℂ) ^ 4 else 0 := by
  have h := box_sum_rootPow (halfSide L k) (unitRoot_isPrimitiveRoot (k := k) hL) a
  rw [two_mul_halfSide_add_one hL] at h
  rw [freqBox_eq_piFinset hL]
  exact h
abbrev meshPow4 (L k : ℕ) : ℂ := ((finestMesh L k ^ 4 : ℝ) : ℂ)
theorem meshPow4_mul_side_pow (hL : Conventions.IsAdmissibleBlockingFactor L) :
    meshPow4 L k * ((L ^ k : ℕ) : ℂ) ^ 4 = 1 := by
  have h := side_mul_meshAt_zero (k := k) hL
  have h4 : finestMesh L k ^ 4 * ((L ^ k : ℕ) : ℝ) ^ 4 = 1 := by
    rw [← mul_pow, finestMesh, mul_comm, h, one_pow]
  rw [meshPow4, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul, h4,
    Complex.ofReal_one]
theorem meshPow4_mul_sum_eq_ite (hL : Conventions.IsAdmissibleBlockingFactor L)
    {n n' : Fin 4 → ℤ} (hn : n ∈ freqBox L k) (hn' : n' ∈ freqBox L k) :
    meshPow4 L k * ∑ m ∈ freqBox L k, unitRoot L k ^ dotProduct m (n - n') =
      if n = n' then 1 else 0 := by
  rw [freqBox_sum_unitRoot hL]
  by_cases h : n = n'
  · subst h
    rw [if_pos fun μ => by simp, if_pos rfl, meshPow4_mul_side_pow hL]
  · rw [if_neg h, if_neg (show ¬∀ μ, ((L ^ k : ℕ) : ℤ) ∣ (n - n') μ from
      fun d => h (eq_of_side_dvd_sub hL hn hn' d)), mul_zero]
theorem freqBox_sum_neg {A : Type} [AddCommMonoid A] (hL : Conventions.IsAdmissibleBlockingFactor L)
    (f : (Fin 4 → ℤ) → A) :
    ∑ m ∈ freqBox L k, f (-m) = ∑ m ∈ freqBox L k, f m :=
  Finset.sum_nbij' Neg.neg Neg.neg (fun _ h => neg_mem_freqBox hL h)
    (fun _ h => neg_mem_freqBox hL h) (by simp) (by simp) (by simp)
theorem fourierCoeff_eq_sum (hL : Conventions.IsAdmissibleBlockingFactor L)
    {g : FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2}
    (hg : IsIntPeriodic L k g) (m : Fin 4 → ℤ) :
    fourierCoeff L k g m =
      meshPow4 L k • ∑ n ∈ freqBox L k, unitRoot L k ^ (-dotProduct m n) • g (gridPoint L k n) := by
  have hp : IsIntPeriodic L k fun x : FullSpace.Vertex L k 0 =>
      fourierPhase m (x : AmbientSpace) • g x :=
    fun n x => by
      have a := fourierPhase_isIntPeriodic (k := k) hL m n x
      have b := hg n x
      simp only at a
      simp only [a, b]
  have e : (∑ᶠ c : VertexClass L k,
      fourierPhase m (Quot.out c : FullSpace.Vertex L k 0) • g (Quot.out c)) =
      ∑ n ∈ freqBox L k, fourierPhase m (gridPoint L k n : AmbientSpace) • g (gridPoint L k n) :=
    finsum_vertexClass_eq_sum hL hp
  rw [PlaneWaves.fourierCoeff, e]
  simp only [fourierPhase_gridPoint]
theorem fourier_inversion {V : Type} [AddCommGroup V] [Module ℂ V]
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {g : FullSpace.Vertex L k 0 → V} (hg : IsIntPeriodic L k g) (z : Fin 4 → ℤ) :
    ∑ m ∈ freqBox L k, unitRoot L k ^ dotProduct m z •
        (meshPow4 L k • ∑ n ∈ freqBox L k, unitRoot L k ^ (-dotProduct m n) • g (gridPoint L k n)) =
      g (gridPoint L k z) := by
  obtain ⟨n₀, h₀, v, rfl⟩ := exists_freqBox_add_smul (k := k) hL z
  have e : ∀ m : Fin 4 → ℤ, unitRoot L k ^ dotProduct m (n₀ + ((L ^ k : ℕ) : ℤ) • v) =
      unitRoot L k ^ dotProduct m n₀ := fun m => by
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, unitRoot_zpow_add_side_mul hL]
  rw [gridPoint_periodic hL hg]
  calc _ = ∑ m ∈ freqBox L k, ∑ n ∈ freqBox L k,
        (meshPow4 L k * unitRoot L k ^ dotProduct m (n₀ - n)) • g (gridPoint L k n) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [e, Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [smul_smul, smul_smul, dotProduct_sub, sub_eq_add_neg, zpow_add₀ unitRoot_ne_zero]
        congr 1
        ring
    _ = ∑ n ∈ freqBox L k,
        (meshPow4 L k * ∑ m ∈ freqBox L k, unitRoot L k ^ dotProduct m (n₀ - n)) •
          g (gridPoint L k n) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum, Finset.sum_smul]
    _ = ∑ n ∈ freqBox L k, (if n₀ = n then (1 : ℂ) else 0) • g (gridPoint L k n) :=
        Finset.sum_congr rfl fun n hn => by rw [meshPow4_mul_sum_eq_ite hL h₀ hn]
    _ = g (gridPoint L k n₀) := by
        simp [ite_smul, h₀]
end Waves
section Parseval
variable {L k : ℕ}
def dft (L k : ℕ) (ψ : (Fin 4 → ℤ) → ℂ) (m : Fin 4 → ℤ) : ℂ :=
  meshPow4 L k * ∑ n ∈ freqBox L k, unitRoot L k ^ (-dotProduct m n) * ψ n
theorem sum_dft_mul_dft_neg (hL : Conventions.IsAdmissibleBlockingFactor L)
    (ψ ψ' : (Fin 4 → ℤ) → ℂ) :
    ∑ m ∈ freqBox L k, dft L k ψ m * dft L k ψ' (-m) =
      meshPow4 L k * ∑ n ∈ freqBox L k, ψ n * ψ' n := by
  have step : ∀ m : Fin 4 → ℤ, dft L k ψ m * dft L k ψ' (-m) =
      ∑ n ∈ freqBox L k, ∑ n' ∈ freqBox L k,
        meshPow4 L k * meshPow4 L k * (ψ n * ψ' n') * unitRoot L k ^ dotProduct m (n' - n) :=
      fun m => by
    unfold dft
    rw [mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [neg_dotProduct, neg_neg, dotProduct_sub, sub_eq_add_neg, zpow_add₀ unitRoot_ne_zero]
    ring
  simp only [step]
  rw [Finset.sum_comm]
  have inner : ∀ n ∈ freqBox L k, ∑ m ∈ freqBox L k, ∑ n' ∈ freqBox L k,
      meshPow4 L k * meshPow4 L k * (ψ n * ψ' n') * unitRoot L k ^ dotProduct m (n' - n) =
      meshPow4 L k * (ψ n * ψ' n) := fun n hn => by
    rw [Finset.sum_comm]
    calc _ = ∑ n' ∈ freqBox L k, (meshPow4 L k * (ψ n * ψ' n')) *
          (meshPow4 L k * ∑ m ∈ freqBox L k, unitRoot L k ^ dotProduct m (n' - n)) :=
          Finset.sum_congr rfl fun n' _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
      _ = ∑ n' ∈ freqBox L k, (meshPow4 L k * (ψ n * ψ' n')) * (if n' = n then 1 else 0) :=
          Finset.sum_congr rfl fun n' hn' => by rw [meshPow4_mul_sum_eq_ite hL hn' hn]
      _ = _ := by simp [hn]
  rw [Finset.sum_congr rfl inner, Finset.mul_sum]
theorem conj_dft (hL : Conventions.IsAdmissibleBlockingFactor L) (ψ : (Fin 4 → ℤ) → ℂ)
    (m : Fin 4 → ℤ) :
    conj (dft L k ψ m) = dft L k (fun n => conj (ψ n)) (-m) := by
  unfold dft
  rw [map_mul, map_sum, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, conj_unitRoot_zpow hL, neg_dotProduct, neg_neg]
theorem sum_norm_dft_sq (hL : Conventions.IsAdmissibleBlockingFactor L) (ψ : (Fin 4 → ℤ) → ℂ) :
    ∑ m ∈ freqBox L k, ‖dft L k ψ m‖ ^ 2 =
      finestMesh L k ^ 4 * ∑ n ∈ freqBox L k, ‖ψ n‖ ^ 2 := by
  apply Complex.ofReal_injective
  have P := sum_dft_mul_dft_neg (k := k) hL (fun n => conj (ψ n)) ψ
  have e : ∀ m : Fin 4 → ℤ, dft L k (fun n => conj (ψ n)) m * dft L k ψ (-m) =
      ((‖dft L k ψ (-m)‖ ^ 2 : ℝ) : ℂ) := fun m => by
    have c := conj_dft (k := k) hL ψ (-m)
    rw [neg_neg] at c
    rw [← c, Complex.conj_mul']
    push_cast
    rfl
  simp only [e, Complex.conj_mul'] at P
  rw [freqBox_sum_neg hL fun m => ((‖dft L k ψ m‖ ^ 2 : ℝ) : ℂ)] at P
  push_cast at P ⊢
  exact P
end Parseval
section Colours
variable {L k : ℕ}
theorem pauli_combination_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_combination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • Matrices.ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem ofPauliCoeffs_isIntPeriodic {c : Fin 3 × FullSpace.Vertex L k 0 → ℂ}
    (hc : ∀ a, IsIntPeriodic L k fun x => c (a, x)) : IsIntPeriodic L k (ofPauliCoeffs c) :=
  fun n x => Finset.sum_congr rfl fun a _ =>
    congrArg (· • Matrices.ComplexMatrix2.pauliFamily a) (hc a n x)
theorem fourierCoeff_ofPauliCoeffs (hL : Conventions.IsAdmissibleBlockingFactor L)
    {c : Fin 3 × FullSpace.Vertex L k 0 → ℂ} (hc : ∀ a, IsIntPeriodic L k fun x => c (a, x))
    (m : Fin 4 → ℤ) :
    fourierCoeff L k (ofPauliCoeffs c) m =
      ∑ a, dft L k (fun n => c (a, gridPoint L k n)) m • Matrices.ComplexMatrix2.pauliFamily a := by
  rw [fourierCoeff_eq_sum hL (ofPauliCoeffs_isIntPeriodic hc)]
  simp only [ofPauliCoeffs, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dft, Finset.mul_sum, Finset.sum_smul]
theorem tracelessPairing_combination (hP : OneLoop.PauliMatrixRelations) (x y : Fin 3 → ℂ) :
    tracelessPairing (∑ a, x a • Matrices.ComplexMatrix2.pauliFamily a)
      (∑ a, y a • Matrices.ComplexMatrix2.pauliFamily a) = ∑ a, x a * y a := by
  unfold tracelessPairing
  rw [dif_pos ⟨pauli_combination_mem_traceless x, pauli_combination_mem_traceless y⟩]
  exact hP.2.2.2.2.1 _ _ x y rfl rfl
theorem parseval_norm (hL : Conventions.IsAdmissibleBlockingFactor L)
    (c : Fin 3 × FullSpace.Vertex L k 0 → ℂ)
    (hc : ∀ a, IsIntPeriodic L k fun x => c (a, x)) :
    finestMesh L k ^ 4 * ∑ a, ∑ᶠ d : VertexClass L k, ‖c (a, Quot.out d)‖ ^ 2 =
      ∑ m ∈ freqBox L k, pauliNorm (fourierCoeff L k (ofPauliCoeffs c) m) ^ 2 := by
  have e₁ : ∀ a, ∑ᶠ d : VertexClass L k, ‖c (a, Quot.out d)‖ ^ 2 =
      ∑ n ∈ freqBox L k, ‖c (a, gridPoint L k n)‖ ^ 2 := fun a =>
    finsum_vertexClass_eq_sum (h := fun x => ‖c (a, x)‖ ^ 2) hL fun n x => by
      have h := hc a n x
      simp only at h
      simp only [h]
  have e₂ : ∀ m : Fin 4 → ℤ, pauliNorm (fourierCoeff L k (ofPauliCoeffs c) m) ^ 2 =
      ∑ a, ‖dft L k (fun n => c (a, gridPoint L k n)) m‖ ^ 2 := fun m => by
    rw [fourierCoeff_ofPauliCoeffs hL hc, pauliNorm, Real.sq_sqrt (by positivity)]
    simp only [pauliCoeff_combination]
  simp only [e₁, e₂]
  rw [Finset.sum_comm (s := freqBox L k) (t := Finset.univ)]
  simp only [sum_norm_dft_sq hL]
  rw [Finset.mul_sum]
theorem parseval_pairing (hP : OneLoop.PauliMatrixRelations)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (c c' : Fin 3 × FullSpace.Vertex L k 0 → ℂ)
    (hc : ∀ a, IsIntPeriodic L k fun x => c (a, x))
    (hc' : ∀ a, IsIntPeriodic L k fun x => c' (a, x)) :
    ((finestMesh L k ^ 4 : ℝ) : ℂ) *
        ∑ a, ∑ᶠ d : VertexClass L k, c (a, Quot.out d) * c' (a, Quot.out d) =
      ∑ m ∈ freqBox L k,
        tracelessPairing (fourierCoeff L k (ofPauliCoeffs c) m)
          (fourierCoeff L k (ofPauliCoeffs c') (-m)) := by
  have e₁ : ∀ a, ∑ᶠ d : VertexClass L k, c (a, Quot.out d) * c' (a, Quot.out d) =
      ∑ n ∈ freqBox L k, c (a, gridPoint L k n) * c' (a, gridPoint L k n) := fun a =>
    finsum_vertexClass_eq_sum (h := fun x => c (a, x) * c' (a, x)) hL fun n x => by
      have h := hc a n x
      have h' := hc' a n x
      simp only at h h'
      simp only [h, h']
  simp only [e₁, fourierCoeff_ofPauliCoeffs hL hc, fourierCoeff_ofPauliCoeffs hL hc',
    tracelessPairing_combination hP]
  rw [Finset.sum_comm (s := freqBox L k) (t := Finset.univ)]
  simp only [sum_dft_mul_dft_neg hL]
  rw [Finset.mul_sum]
end Colours
theorem claim_holds (hP : OneLoop.PauliMatrixRelations) : Claim := by
  intro L hL k _
  refine
    { finite_vertexClass := Finite.of_surjective _ (vertexClassOf_bijective hL).2
      coe_vertexImage := coe_vertexImage_intShift hL
      integerWave_periodic := integerWave_isIntPeriodic hL
      expWave_mul_integerWave := ?_
      orthonormal := ?_
      span := ?_
      expansion := ?_
      norm_sq := parseval_norm hL
      pairing_eq := parseval_pairing hP hL }
  · intro κ m x
    rw [expWave, integerWave, expWave, ← Complex.exp_add]
    congr 1
    simp only [bilinDot, shiftedFreq, toComplexVec, castVec, Fin.sum_univ_four]
    push_cast
    ring
  · intro m hm m' hm'
    have hh : IsIntPeriodic L k fun x : FullSpace.Vertex L k 0 =>
        conj (integerWave m (x : AmbientSpace)) * integerWave m' (x : AmbientSpace) :=
      fun n x => by
        have a := integerWave_isIntPeriodic (k := k) hL m n x
        have b := integerWave_isIntPeriodic (k := k) hL m' n x
        simp only at a b
        simp only [a, b]
    have e : (∑ᶠ d : VertexClass L k,
        conj (integerWave m (Quot.out d : FullSpace.Vertex L k 0)) *
          integerWave m' (Quot.out d : FullSpace.Vertex L k 0)) =
        ∑ n ∈ freqBox L k, conj (integerWave m (gridPoint L k n : AmbientSpace)) *
          integerWave m' (gridPoint L k n : AmbientSpace) := finsum_vertexClass_eq_sum hL hh
    rw [e]
    have t : ∀ n : Fin 4 → ℤ, conj (integerWave m (gridPoint L k n : AmbientSpace)) *
        integerWave m' (gridPoint L k n : AmbientSpace) =
          unitRoot L k ^ dotProduct n (m' - m) := fun n => by
      rw [integerWave_gridPoint, integerWave_gridPoint, conj_unitRoot_zpow hL,
        ← zpow_add₀ unitRoot_ne_zero, dotProduct_sub, dotProduct_comm n m', dotProduct_comm n m]
      congr 1
      ring
    simp only [t]
    have d := meshPow4_mul_sum_eq_ite (k := k) hL hm' hm
    simp only [eq_comm (a := m')] at d
    exact d
  · intro φ hφ
    refine ⟨fun m => meshPow4 L k • ∑ n ∈ freqBox L k,
      unitRoot L k ^ (-dotProduct m n) • φ (gridPoint L k n), fun x => ?_⟩
    obtain ⟨z, rfl⟩ := exists_eq_gridPoint x
    rw [← fourier_inversion hL hφ z]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integerWave_gridPoint, smul_eq_mul, mul_comm]
  · intro g hg x
    obtain ⟨z, rfl⟩ := exists_eq_gridPoint x
    rw [← fourier_inversion hL hg z]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integerWave_gridPoint, fourierCoeff_eq_sum hL hg]
end YangMills.Construction.Tower.FinestFourierSums
end
