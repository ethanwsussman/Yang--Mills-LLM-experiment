import Mathlib
import YangMills.Construction.Geometry.TorusMetric
set_option autoImplicit false

section
open Complex
noncomputable section
namespace YangMills.Construction
namespace DiscreteFourier
abbrev DiscreteTorus (n : ℕ) : Type := Fin 4 → ZMod n
end DiscreteFourier
end YangMills.Construction
end
end

open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
open TorusMetric
abbrev IntegerTorus (n : ℕ) : Type := DiscreteFourier.DiscreteTorus n
section Torus
variable {n : ℕ} [NeZero n]
def torusInner (f f' : IntegerTorus n → ℝ) : ℝ := ∑ z, f z * f' z
def torusIndicator (z : IntegerTorus n) : IntegerTorus n → ℝ := Pi.single z 1
def kernelOf (X : (IntegerTorus n → ℝ) →ₗ[ℝ] IntegerTorus n → ℝ) (z z' : IntegerTorus n) : ℝ :=
  torusInner (torusIndicator z) (X (torusIndicator z'))
end Torus
section Differences
variable {A R : Type*} [Ring A] [AddCommGroup R]
def unitVector (μ : Fin 4) : Fin 4 → A := Pi.single μ 1
def forwardDiff (μ : Fin 4) (f : (Fin 4 → A) → R) : (Fin 4 → A) → R :=
  fun z => f (z + unitVector μ) - f z
def backwardDiff (μ : Fin 4) (f : (Fin 4 → A) → R) : (Fin 4 → A) → R :=
  fun z => f z - f (z - unitVector μ)
def discreteLaplacian (f : (Fin 4 → A) → R) : (Fin 4 → A) → R :=
  -∑ μ, backwardDiff μ (forwardDiff μ f)
def discreteLaplacianLinear (K : Type*) [Semiring K] [Module K R] :
    ((Fin 4 → A) → R) →ₗ[K] (Fin 4 → A) → R where
  toFun := discreteLaplacian
  map_add' f g := by
    funext z
    simp only [discreteLaplacian, backwardDiff, forwardDiff, Pi.neg_apply,
      Finset.sum_apply, Pi.add_apply, ← Finset.sum_add_distrib, ← neg_add]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    abel
  map_smul' c f := by
    funext z
    simp only [discreteLaplacian, backwardDiff, forwardDiff, Pi.neg_apply,
      Finset.sum_apply, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_neg, smul_sub]
end Differences
def laplacianSymbol (k : Fin 4 → ℝ) : ℝ := ∑ μ, 4 * Real.sin (k μ / 2) ^ 2
def wavePairing (k : Fin 4 → ℝ) (z : Fin 4 → ℤ) : ℝ := ∑ μ, k μ * (z μ : ℝ)
def expWave (k : Fin 4 → ℝ) (z : Fin 4 → ℤ) : ℂ :=
  Complex.exp (Complex.I * (wavePairing k z : ℝ))
def momentumSet (n : ℕ) : Set (Fin 4 → ℝ) :=
  {k | (∃ N : Fin 4 → ℤ, ∀ μ, k μ = 2 * Real.pi / n * (N μ : ℝ)) ∧
    ∀ μ, k μ ∈ Ioc (-Real.pi) Real.pi}
def residueLift {n : ℕ} (z : IntegerTorus n) : Fin 4 → ℤ := fun μ => ((z μ).val : ℤ)
def zmodClass (n : ℕ) (N : Fin 4 → ℤ) : IntegerTorus n := fun μ => (N μ : ZMod n)
def expWaveOnTorus {n : ℕ} (k : Fin 4 → ℝ) (z : IntegerTorus n) : ℂ :=
  expWave k (residueLift z)
def latticeGreenFunction (n : ℕ) (z : IntegerTorus n) : ℂ :=
  (1 / (n : ℂ) ^ 4) *
    ∑ᶠ k ∈ momentumSet n \ {0}, expWaveOnTorus k z / (laplacianSymbol k : ℂ)
def continuumGreenFunction (u : Fin 4 → ℝ) : ℝ := 1 / (4 * Real.pi ^ 2 * euclidNormVec u ^ 2)
section Facts
def momentumRange (n : ℕ) : Finset ℤ := Finset.Ioc ((n : ℤ) / 2 - n) ((n : ℤ) / 2)
theorem mem_momentumRange {n : ℕ} {N : ℤ} :
    N ∈ momentumRange n ↔ -(n : ℤ) < 2 * N ∧ 2 * N ≤ n := by
  simp only [momentumRange, Finset.mem_Ioc]
  omega
theorem card_momentumRange (n : ℕ) : (momentumRange n).card = n := by
  simp [momentumRange]
def momentumVec (n : ℕ) (N : Fin 4 → ℤ) : Fin 4 → ℝ := fun μ => 2 * Real.pi / n * (N μ : ℝ)
theorem momentumSet_eq_image {n : ℕ} (hn : n ≠ 0) :
    momentumSet n = momentumVec n ''
      (Fintype.piFinset fun _ : Fin 4 => momentumRange n : Finset (Fin 4 → ℤ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have key : ∀ N : ℤ, 2 * Real.pi / n * (N : ℝ) ∈ Ioc (-Real.pi) Real.pi ↔
      N ∈ momentumRange n := by
    intro N
    rw [mem_momentumRange, mem_Ioc]
    have hpi := Real.pi_pos
    have e : 2 * Real.pi / n * (N : ℝ) = Real.pi * (2 * N / n) := by field_simp
    rw [e]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : (-1 : ℝ) < 2 * N / n := by
        by_contra h
        push Not at h
        nlinarith
      have h2' : 2 * (N : ℝ) / n ≤ 1 := by
        by_contra h
        push Not at h
        nlinarith
      rw [lt_div_iff₀ hn'] at h1'
      rw [div_le_iff₀ hn'] at h2'
      constructor
      · have : (-(n : ℝ)) < 2 * N := by linarith
        exact_mod_cast this
      · have : 2 * (N : ℝ) ≤ n := by linarith
        exact_mod_cast this
    · rintro ⟨h1, h2⟩
      have h1' : (-(n : ℝ)) < 2 * N := by exact_mod_cast h1
      have h2' : 2 * (N : ℝ) ≤ n := by exact_mod_cast h2
      have a1 : (-1 : ℝ) < 2 * N / n := by
        rw [lt_div_iff₀ hn']
        linarith
      have a2 : 2 * (N : ℝ) / n ≤ 1 := by
        rw [div_le_iff₀ hn']
        linarith
      constructor <;> nlinarith
  ext k
  simp only [momentumSet, Set.mem_ofPred_eq, mem_image, Finset.mem_coe, Fintype.mem_piFinset]
  constructor
  · rintro ⟨⟨N, hN⟩, hk⟩
    refine ⟨N, fun μ => ?_, funext fun μ => (hN μ).symm⟩
    rw [← key, ← hN μ]
    exact hk μ
  · rintro ⟨N, hN, rfl⟩
    exact ⟨⟨N, fun μ => rfl⟩, fun μ => (key (N μ)).2 (hN μ)⟩
theorem momentumVec_injective {n : ℕ} (hn : n ≠ 0) : Function.Injective (momentumVec n) := by
  intro N N' h
  funext μ
  have h' := congrFun h μ
  have hc : 2 * Real.pi / n ≠ 0 := by positivity
  simpa [momentumVec, hc] using h'
theorem momentumSet_finite {n : ℕ} (hn : n ≠ 0) : (momentumSet n).Finite := by
  rw [momentumSet_eq_image hn]
  exact (Finset.finite_toSet _).image _
theorem momentumSet_ncard {n : ℕ} (hn : n ≠ 0) : (momentumSet n).ncard = n ^ 4 := by
  rw [momentumSet_eq_image hn, Set.ncard_image_of_injective _ (momentumVec_injective hn),
    Set.ncard_coe_finset, Fintype.card_piFinset]
  simp [card_momentumRange]
theorem expWaveOnTorus_zmodClass {n : ℕ} [NeZero n] {k : Fin 4 → ℝ} (hk : k ∈ momentumSet n)
    (N : Fin 4 → ℤ) : expWaveOnTorus k (zmodClass n N) = expWave k N := by
  obtain ⟨⟨M, hM⟩, -⟩ := hk
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hres : ∀ μ, residueLift (zmodClass n N) μ = N μ - n * (N μ / n) := by
    intro μ
    simp only [residueLift, zmodClass, ZMod.val_intCast]
    exact Int.emod_def _ _
  have hpair : wavePairing k (residueLift (zmodClass n N)) =
      wavePairing k N - 2 * Real.pi * ((∑ μ, M μ * (N μ / n) : ℤ) : ℝ) := by
    simp only [wavePairing, hres, hM]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    field_simp
  simp only [expWaveOnTorus, expWave, hpair]
  push_cast
  rw [mul_sub, Complex.exp_sub]
  have hone : Complex.exp (Complex.I * (2 * Real.pi * ∑ μ, (M μ : ℂ) * ((N μ / n : ℤ) : ℂ))) = 1 := by
    rw [Complex.exp_eq_one_iff]
    refine ⟨∑ μ, M μ * (N μ / n), ?_⟩
    push_cast
    ring
  rw [hone, div_one]
theorem laplacianSymbol_pos {n : ℕ} {k : Fin 4 → ℝ} (hk : k ∈ momentumSet n \ {0}) :
    0 < laplacianSymbol k := by
  obtain ⟨⟨-, hI⟩, h0⟩ := hk
  obtain ⟨μ, hμ⟩ : ∃ μ, k μ ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (funext h)
  refine Finset.sum_pos' (fun ν _ => by positivity) ⟨μ, Finset.mem_univ _, ?_⟩
  have hpi := Real.pi_pos
  have hs : Real.sin (k μ / 2) ≠ 0 := by
    intro h
    have h1 := (hI μ).1
    have h2 := (hI μ).2
    have := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)).1 h
    exact hμ (by linarith)
  positivity
end Facts
end YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
