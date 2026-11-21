import YangMills.Construction.Dirichlet.RegionSequenceOperators
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.PartitionCubes
structure IsSqPartitionBump (f : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  compact_support : HasCompactSupport f
  support_subset : tsupport f ⊆ Ioo (-(2 / 3) : ℝ) (2 / 3)
  nonneg : ∀ x, 0 ≤ f x
  le_one : ∀ x, f x ≤ 1
  eq_one : ∀ x ∈ Icc (-(1 / 3) : ℝ) (1 / 3), f x = 1
  sum_squares : ∀ x, ∑ᶠ i : ℤ, f (x - i) ^ 2 = 1
structure IsMollifierBump (f : (Fin 4 → ℝ) → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  compact_support : HasCompactSupport f
  support_subset : tsupport f ⊆ Metric.closedBall 0 1
  nonneg : ∀ v, 0 ≤ f v
  integral_eq_one : ∫ v, f v = 1
def smoothRise (x : ℝ) : ℝ := Real.smoothTransition (6 * x - 5 / 2)
theorem smoothRise_add_smoothRise_one_sub (x : ℝ) : smoothRise x + smoothRise (1 - x) = 1 := by
  have key : ∀ u : ℝ, Real.smoothTransition u + Real.smoothTransition (1 - u) = 1 := by
    intro u
    have h₁ := Real.smoothTransition.pos_denom u
    have h₂ := Real.smoothTransition.pos_denom (1 - u)
    simp only [Real.smoothTransition, sub_sub_cancel] at h₂ ⊢
    field_simp
    ring
  have h := key (6 * x - 5 / 2)
  have e : 1 - (6 * x - 5 / 2) = 6 * (1 - x) - 5 / 2 := by ring
  rw [e] at h
  exact h
theorem smoothRise_eq_zero {x : ℝ} (h : x ≤ 5 / 12) : smoothRise x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
theorem smoothRise_eq_one {x : ℝ} (h : 7 / 12 ≤ x) : smoothRise x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
def cosBump (x : ℝ) : ℝ := Real.cos (Real.pi / 2 * (smoothRise x + smoothRise (-x)))
theorem cosBump_of_nonneg {x : ℝ} (h : 0 ≤ x) :
    cosBump x = Real.cos (Real.pi / 2 * smoothRise x) := by
  simp [cosBump, smoothRise_eq_zero (show -x ≤ 5 / 12 by linarith)]
theorem cosBump_of_nonpos {x : ℝ} (h : x ≤ 0) :
    cosBump x = Real.cos (Real.pi / 2 * smoothRise (-x)) := by
  simp [cosBump, smoothRise_eq_zero (show x ≤ 5 / 12 by linarith)]
theorem cos_half_pi_smoothRise_nonneg (x : ℝ) : 0 ≤ Real.cos (Real.pi / 2 * smoothRise x) := by
  have h₀ : 0 ≤ smoothRise x := Real.smoothTransition.nonneg _
  have h₁ : smoothRise x ≤ 1 := Real.smoothTransition.le_one _
  have hp := Real.pi_pos
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith
theorem cosBump_eq_zero {x : ℝ} (h : 7 / 12 ≤ |x|) : cosBump x = 0 := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h
    rw [cosBump_of_nonneg hx, smoothRise_eq_one h]
    simp
  · rw [abs_of_nonpos hx] at h
    rw [cosBump_of_nonpos hx, smoothRise_eq_one h]
    simp
theorem cosBump_sum_sq (x : ℝ) : ∑ᶠ i : ℤ, cosBump (x - i) ^ 2 = 1 := by
  set k : ℤ := ⌊x⌋ with hk
  have hk₀ : (k : ℝ) ≤ x := Int.floor_le x
  have hk₁ : x < k + 1 := Int.lt_floor_add_one x
  have hsupp : (Function.support fun i : ℤ => cosBump (x - i) ^ 2) ⊆
      (({k, k + 1} : Finset ℤ) : Set ℤ) := by
    intro i hi
    by_contra hne
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff,
      not_or] at hne
    apply hi
    have hfar : 7 / 12 ≤ |x - i| := by
      rcases lt_or_gt_of_ne hne.1 with hlt | hgt
      · have h₁ : (i : ℝ) + 1 ≤ k := by exact_mod_cast hlt
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have h₂ : k + 2 ≤ i := by omega
        have h₃ : (k : ℝ) + 2 ≤ i := by exact_mod_cast h₂
        rw [abs_of_nonpos (by linarith)]
        linarith
    simp [cosBump_eq_zero hfar]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair (by omega)]
  push_cast
  have h₁ : cosBump (x - k) = Real.cos (Real.pi / 2 * smoothRise (x - k)) :=
    cosBump_of_nonneg (by linarith)
  have h₂ : cosBump (x - (k + 1)) = Real.sin (Real.pi / 2 * smoothRise (x - k)) := by
    rw [cosBump_of_nonpos (by linarith)]
    have e : -(x - (k + 1)) = 1 - (x - k) := by ring
    have r := smoothRise_add_smoothRise_one_sub (x - k)
    rw [e, show smoothRise (1 - (x - k)) = 1 - smoothRise (x - k) by linarith, mul_sub, mul_one,
      Real.cos_pi_div_two_sub]
  rw [h₁, h₂]
  exact Real.cos_sq_add_sin_sq _
theorem exists_isSqPartitionBump : ∃ f : ℝ → ℝ, IsSqPartitionBump f := by
  have hsupp : tsupport cosBump ⊆ Icc (-(7 / 12) : ℝ) (7 / 12) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hn
    apply hx
    apply cosBump_eq_zero
    rcases not_and_or.mp hn with h | h
    · rw [abs_of_nonpos (by linarith [not_le.mp h])]
      linarith [not_le.mp h]
    · rw [abs_of_nonneg (by linarith [not_le.mp h])]
      linarith [not_le.mp h]
  refine ⟨cosBump, ?_, ?_, ?_, ?_, ?_, ?_, cosBump_sum_sq⟩
  · have hr : ContDiff ℝ ∞ smoothRise :=
      Real.smoothTransition.contDiff.comp (by fun_prop)
    have hr' : ContDiff ℝ ∞ fun x : ℝ => smoothRise (-x) := hr.comp contDiff_neg
    exact Real.contDiff_cos.comp (contDiff_const.mul (hr.add hr'))
  · exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport _).trans hsupp)
  · refine hsupp.trans fun x hx => ⟨?_, ?_⟩ <;> linarith [hx.1, hx.2]
  · intro x
    rcases le_total 0 x with hx | hx
    · rw [cosBump_of_nonneg hx]
      exact cos_half_pi_smoothRise_nonneg x
    · rw [cosBump_of_nonpos hx]
      exact cos_half_pi_smoothRise_nonneg (-x)
  · exact fun x => Real.cos_le_one _
  · rintro x ⟨h₁, h₂⟩
    simp [cosBump, smoothRise_eq_zero (show x ≤ 5 / 12 by linarith),
      smoothRise_eq_zero (show -x ≤ 5 / 12 by linarith)]
theorem exists_isMollifierBump : ∃ f : (Fin 4 → ℝ) → ℝ, IsMollifierBump f := by
  let b : ContDiffBump (0 : Fin 4 → ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed, ?_,
    fun v => b.nonneg_normed v, b.integral_normed⟩
  rw [b.tsupport_normed_eq]
def sqPartitionBump : ℝ → ℝ := Classical.choose exists_isSqPartitionBump
theorem sqPartitionBump_spec : IsSqPartitionBump sqPartitionBump :=
  Classical.choose_spec exists_isSqPartitionBump
def mollifierBump : (Fin 4 → ℝ) → ℝ := Classical.choose exists_isMollifierBump
theorem mollifierBump_spec : IsMollifierBump mollifierBump :=
  Classical.choose_spec exists_isMollifierBump
def mollifierScaled (r : ℝ) (v : Fin 4 → ℝ) : ℝ := (r ^ 4)⁻¹ * mollifierBump (r⁻¹ • v)
variable (𝒮 : RegionSequence.NestedRegions) (M : ℕ)
def cubeSide (n : ℕ) : ℝ := (M : ℝ) * 𝒮.scale n
def topLevel : ℕ := Torus.lastNonemptyIndex 𝒮.Ω
def IsCornerOf (c : 𝒮.Point) (σ : ℝ) (z : 𝒮.Point) : Prop :=
  ∃ ε : Fin 4 → ℝ, (∀ μ, ε μ = 1 ∨ ε μ = -1) ∧
    z = c + Torus.torusProj 4 𝒮.side fun μ => ε μ * (σ / 2)
def cornerSet (n : ℕ) : Set 𝒮.Point :=
  {z | ∃ c ∈ Torus.spacingLattice 4 𝒮.side (cubeSide 𝒮 M n),
    IsCornerOf 𝒮 c (cubeSide 𝒮 M n) z}
@[ext]
structure LevelCube where
  level : ℕ
  centre : 𝒮.Point
  level_le : level ≤ topLevel 𝒮
  centre_mem : centre ∈ cornerSet 𝒮 M level
variable {𝒮 M}
def LevelCube.pts (Q : LevelCube 𝒮 M) : Set 𝒮.Point :=
  {x | Torus.supNorm (x - Q.centre) ≤ cubeSide 𝒮 M Q.level}
def LevelCube.enlarge (Q : LevelCube 𝒮 M) (i : ℕ) : Set 𝒮.Point :=
  {x | Torus.supNorm (x - Q.centre) ≤ (1 + (i : ℝ)) * cubeSide 𝒮 M Q.level}
def LevelCube.strictPts (Q : LevelCube 𝒮 M) : Set 𝒮.Point :=
  {x | Torus.supNorm (x - Q.centre) < cubeSide 𝒮 M Q.level}
def circleCentredRep {S : ℝ} (θ : AddCircle S) : ℝ :=
  Classical.epsilon fun v : ℝ => v ∈ Ico (-(S / 2)) (S / 2) ∧ (v : AddCircle S) = θ
def LevelCube.productBump (Q : LevelCube 𝒮 M) (x : 𝒮.Point) : ℝ :=
  ∏ μ, sqPartitionBump (circleCentredRep (x μ - Q.centre μ) / cubeSide 𝒮 M Q.level)
variable (𝒮 M)
def mollifyRadius (n : ℕ) : ℝ := cubeSide 𝒮 M n / (6 * (𝒮.L : ℝ))
def distToOutside (n : ℕ) (x : 𝒮.Point) : ℝ≥0∞ :=
  Torus.supSetDist {x} (closure (𝒮.Ω n)ᶜ)
variable {𝒮}
def smoothedIndicator (r : ℝ) (A : Set 𝒮.Point) (x : 𝒮.Point) : ℝ :=
  ∫ v : Fin 4 → ℝ,
    indicator A (fun _ => (1 : ℝ)) (x - Torus.torusProj 4 𝒮.side v) * mollifierScaled r v
variable (𝒮)
def levelTransition (n : ℕ) : 𝒮.Point → ℝ :=
  smoothedIndicator (mollifyRadius 𝒮 M n / 2)
    {x | ENNReal.ofReal (3 / 2 * mollifyRadius 𝒮 M n) ≤ distToOutside 𝒮 n x}
open Classical in
def sinCutoff (n : ℕ) (x : 𝒮.Point) : ℝ :=
  if n = 0 then 1 else Real.sin (Real.pi / 2 * levelTransition 𝒮 M n x)
def cosCutoff (n : ℕ) (x : 𝒮.Point) : ℝ := Real.cos (Real.pi / 2 * levelTransition 𝒮 M n x)
variable {𝒮 M}
def LevelCube.partitionFn (Q : LevelCube 𝒮 M) (x : 𝒮.Point) : ℝ :=
  Q.productBump x * sinCutoff 𝒮 M Q.level x * cosCutoff 𝒮 M (Q.level + 1) x
def LevelCube.supp (Q : LevelCube 𝒮 M) : Set 𝒮.Point := tsupport Q.partitionFn
def LevelCube.thicken (Q : LevelCube 𝒮 M) (ς : ℝ) : Set 𝒮.Point :=
  {x | Torus.supSetDist {x} Q.supp ≤ ENNReal.ofReal (ς * mollifyRadius 𝒮 M Q.level)}
variable (𝒮 M)
def activeAt (n : ℕ) : Set (LevelCube 𝒮 M) :=
  {Q | Q.level = n ∧ ∃ b ∈ 𝒮.bonds, Q.partitionFn (b.source : 𝒮.Point) ≠ 0}
def active : Set (LevelCube 𝒮 M) := {Q | ∃ n ≤ topLevel 𝒮, Q ∈ activeAt 𝒮 M n}
variable {𝒮 M}
def LevelCube.IsSecondType (Q : LevelCube 𝒮 M) : Prop :=
  Q ∈ activeAt 𝒮 M 0 ∧ Q.enlarge 2 ∩ 𝒮.Ω 1 = ∅
def LevelCube.IsFirstType (Q : LevelCube 𝒮 M) : Prop := Q ∈ active 𝒮 M ∧ ¬Q.IsSecondType
def LevelCube.smallCutoff (Q : LevelCube 𝒮 M) : 𝒮.Point → ℝ :=
  smoothedIndicator (mollifyRadius 𝒮 M Q.level / 12) (Q.thicken (1 / 4))
def LevelCube.largeCutoff (Q : LevelCube 𝒮 M) : 𝒮.Point → ℝ :=
  smoothedIndicator (mollifyRadius 𝒮 M Q.level / 12) (Q.thicken (7 / 12))
end YangMills.Construction.PartitionCubes
