import YangMills.Construction.Dirichlet.NearCentresOfCubeProof
import YangMills.Construction.DirichletOperator.CornerCubeInALayerOfASequenceProof
import YangMills.Construction.DirichletOperator.DifferenceOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.Lattice.StandardPartitionCubeGeometryArgument
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
open Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes
namespace NextRegionOfFirstType
variable {S : ℝ}
theorem addCircle_norm_le_abs (hS : 0 < S) (x : ℝ) : ‖(x : AddCircle S)‖ ≤ |x| := by apply _root_.YangMills.Construction.Dirichlet.NearCentres.norm_coe_le_abs_of_pos <;> assumption
theorem exists_lift_abs_eq_norm (θ : AddCircle S) :
    ∃ x : ℝ, (x : AddCircle S) = θ ∧ |x| = ‖θ‖ := by apply _root_.YangMills.Construction.TorusMetric.exists_coe_eq_abs_eq_norm <;> assumption
theorem supNorm_torusProj_le_norm (v : Fin 4 → ℝ) : supNorm (torusProj 4 S v) ≤ ‖v‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_proj_le <;> assumption
theorem exists_lift_norm_eq_supNorm (hS : 0 < S) (p : PeriodicTorus 4 S) :
    ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ ‖v‖ = supNorm p := by
  choose v hv hn using fun μ => exists_lift_abs_eq_norm (p μ)
  have hproj : torusProj 4 S v = p := funext hv
  refine ⟨v, hproj, le_antisymm ?_ ?_⟩
  · refine le_csInf ⟨‖v‖, v, hproj, rfl⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ => ?_
    rw [Real.norm_eq_abs, hn μ, ← congrFun hw μ]
    exact (addCircle_norm_le_abs hS (w μ)).trans (norm_le_pi_norm w μ)
  · rw [← hproj]
    exact supNorm_torusProj_le_norm v
theorem torusProj_add (u v : Fin 4 → ℝ) :
    torusProj 4 S (u + v) = torusProj 4 S u + torusProj 4 S v := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_add <;> assumption
theorem torusProj_sub (u v : Fin 4 → ℝ) :
    torusProj 4 S (u - v) = torusProj 4 S u - torusProj 4 S v := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusBonds.torusProj_sub <;> assumption
theorem exists_int_eq_add_mul_of_coe_eq {a b : ℝ} (h : (a : AddCircle S) = b) :
    ∃ m : ℤ, a = b + m * S := by apply _root_.YangMills.Construction.PeriodicLattice.StandardCubes.exists_int_eq_add_mul_of_coe_eq <;> assumption
theorem cubeAt_torusProj (hS : 0 < S) (c : Fin 4 → ℝ) (σ : ℝ) :
    cubeAt (torusProj 4 S c) σ = torusProj 4 S '' closedCube c σ := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, hn⟩ := exists_lift_norm_eq_supNorm hS (x - torusProj 4 S c)
    have hle : ‖v‖ ≤ σ / 2 := hn.le.trans hx
    refine ⟨c + v, fun μ => ?_, ?_⟩
    · have h₁ := (norm_le_pi_norm v μ).trans hle
      simpa using h₁
    · rw [torusProj_add, hv]
      abel
  · rintro ⟨p, hp, rfl⟩
    show supNorm _ ≤ σ / 2
    rw [← torusProj_sub]
    refine (supNorm_torusProj_le_norm _).trans ?_
    have hσ : 0 ≤ σ / 2 := (abs_nonneg _).trans (hp 0)
    exact (pi_norm_le_iff_of_nonneg hσ).2 fun μ => by simpa using hp μ
theorem exists_int_eq_add_mul_of_arcs {w a b : ℝ} (hw : 0 < w) (hS : 2 * w ≤ S)
    (h₁ : ∃ q : ℝ, |q - b| ≤ w / 2 ∧ ((a + w / 2 : ℝ) : AddCircle S) = q)
    (h₂ : ∃ q : ℝ, |q - b| ≤ w / 2 ∧ ((a + -(w / 2) : ℝ) : AddCircle S) = q)
    (h₃ : ∃ q : ℝ, |q - b| ≤ w / 2 ∧ ((a + 0 : ℝ) : AddCircle S) = q) :
    ∃ m : ℤ, a = b + m * S := by
  obtain ⟨q₁, hq₁, e₁⟩ := h₁
  obtain ⟨q₂, hq₂, e₂⟩ := h₂
  obtain ⟨q₃, hq₃, e₃⟩ := h₃
  obtain ⟨m₁, hm₁⟩ := exists_int_eq_add_mul_of_coe_eq e₁
  obtain ⟨m₂, hm₂⟩ := exists_int_eq_add_mul_of_coe_eq e₂
  obtain ⟨m₃, hm₃⟩ := exists_int_eq_add_mul_of_coe_eq e₃
  obtain ⟨l₁, u₁⟩ := abs_le.1 hq₁
  obtain ⟨l₂, u₂⟩ := abs_le.1 hq₂
  obtain ⟨l₃, u₃⟩ := abs_le.1 hq₃
  have hSpos : 0 < S := by linarith
  have hd : ((m₁ - m₂ : ℤ) : ℝ) * S = w - (q₁ - q₂) := by
    push_cast
    linarith
  have hd₀ : 0 ≤ m₁ - m₂ := by
    by_contra hn
    have hc : ((m₁ - m₂ : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : m₁ - m₂ ≤ -1)
    have hm := mul_le_mul_of_nonneg_right hc hSpos.le
    linarith
  have hd₁ : m₁ - m₂ ≤ 1 := by
    by_contra hn
    have hc : (2 : ℝ) ≤ ((m₁ - m₂ : ℤ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ m₁ - m₂)
    have hm := mul_le_mul_of_nonneg_right hc hSpos.le
    linarith
  obtain h0 | h1 : m₁ - m₂ = 0 ∨ m₁ - m₂ = 1 := by omega
  · rw [h0] at hd
    simp only [Int.cast_zero, zero_mul] at hd
    exact ⟨m₁, by linarith⟩
  · exfalso
    rw [h1] at hd
    simp only [Int.cast_one, one_mul] at hd
    have hSw : S = 2 * w := by linarith
    have hq₁' : q₁ = b - w / 2 := by linarith
    obtain ⟨e, he⟩ : ∃ e : ℤ, e = m₁ - m₃ := ⟨_, rfl⟩
    have hq : q₃ - b = (2 * (e : ℝ) - 1) * w := by
      rw [he]
      push_cast
      linear_combination hm₁ - hm₃ + hq₁' + ((m₁ : ℝ) - m₃) * hSw
    rcases le_or_gt 1 e with hc | hc
    · have hc' : (1 : ℝ) ≤ e := by exact_mod_cast hc
      have hm := mul_le_mul_of_nonneg_right hc' hw.le
      linarith
    · have hc' : (e : ℝ) ≤ 0 := by exact_mod_cast (by omega : e ≤ 0)
      have hm := mul_le_mul_of_nonneg_right hc' hw.le
      linarith
theorem exists_centre_eq_add_mul_of_image_eq {w : ℝ} (hw : 0 < w) (hS : 2 * w ≤ S)
    {c c' : Fin 4 → ℝ}
    (h : torusProj 4 S '' closedCube c w = torusProj 4 S '' closedCube c' w) (μ : Fin 4) :
    ∃ m : ℤ, c μ = c' μ + m * S := by
  have key : ∀ a : ℝ, |a| ≤ w / 2 →
      ∃ q : ℝ, |q - c' μ| ≤ w / 2 ∧ ((c μ + a : ℝ) : AddCircle S) = q := by
    intro a ha
    have hm : torusProj 4 S (Function.update c μ (c μ + a)) ∈
        torusProj 4 S '' closedCube c' w := by
      rw [← h]
      refine ⟨_, fun ν => ?_, rfl⟩
      by_cases hν : ν = μ
      · subst hν
        simpa using ha
      · rw [Function.update_of_ne hν, sub_self, abs_zero]
        linarith
    obtain ⟨q, hq, e⟩ := hm
    refine ⟨q μ, hq μ, ?_⟩
    have h₁ := congrFun e μ
    simpa [torusProj] using h₁.symm
  have hw' : 0 ≤ w / 2 := by linarith
  exact exists_int_eq_add_mul_of_arcs hw hS (key _ (by rw [abs_of_nonneg hw']))
    (key _ (by rw [abs_neg, abs_of_nonneg hw'])) (key _ (by simpa using hw'))
theorem exists_int_near_of_abs_le {a : ℕ} {u : ℝ} (h : |u| ≤ (a : ℝ) + 1 / 2) :
    ∃ i : ℤ, |u - (i : ℝ)| ≤ 1 / 2 ∧ -(a : ℝ) ≤ i ∧ (i : ℝ) ≤ a := by
  obtain ⟨h₁, h₂⟩ := abs_le.1 h
  by_cases hu : u = (a : ℝ) + 1 / 2
  · refine ⟨a, ?_, ?_, ?_⟩
    · rw [hu]
      norm_num
    · push_cast
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      linarith
    · simp
  · have hlt : u + 1 / 2 < (a : ℝ) + 1 := by
      have := lt_of_le_of_ne h₂ hu
      linarith
    have hf₁ : (⌊u + 1 / 2⌋ : ℝ) ≤ u + 1 / 2 := Int.floor_le _
    have hf₂ : u + 1 / 2 < ⌊u + 1 / 2⌋ + 1 := Int.lt_floor_add_one _
    refine ⟨⌊u + 1 / 2⌋, ?_, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> linarith
    · have h₃ : -(a : ℤ) ≤ ⌊u + 1 / 2⌋ := by
        apply Int.le_floor.2
        push_cast
        linarith
      exact_mod_cast h₃
    · have h₃ : ⌊u + 1 / 2⌋ < (a : ℤ) + 1 := by
        apply Int.floor_lt.2
        push_cast
        exact hlt
      have h₄ : ⌊u + 1 / 2⌋ ≤ (a : ℤ) := by omega
      exact_mod_cast h₄
theorem isCubeUnion_of_odd_mul (hS : 0 < S) {τ : ℝ} (hτ : 0 < τ) {r : ℕ} (hr : Odd r)
    {X : Set (PeriodicTorus 4 S)} (h : IsCubeUnion ((r : ℝ) * τ) X) : IsCubeUnion τ X := by
  obtain ⟨𝒞, h𝒞, rfl⟩ := h
  refine ⟨{C | C ∈ cubePartition 4 S τ ∧ ∃ D ∈ 𝒞, C ⊆ D}, fun C hC => hC.1, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨D, hD, hx⟩
    obtain ⟨c₀, hc₀, rfl⟩ := h𝒞 hD
    obtain ⟨k, rfl⟩ : ∃ k : Fin 4 → ℤ, c₀ = torusProj 4 S fun μ => (k μ : ℝ) * ((r : ℝ) * τ) :=
      hc₀
    rw [cubeAt_torusProj hS] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨a, rfl⟩ := hr
    have hbound : ∀ μ, ∃ i : ℤ,
        |(p μ - (k μ : ℝ) * (((2 * a + 1 : ℕ) : ℝ) * τ)) / τ - (i : ℝ)| ≤ 1 / 2 ∧
          -(a : ℝ) ≤ i ∧ (i : ℝ) ≤ a := by
      intro μ
      apply exists_int_near_of_abs_le
      rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
      have h₁ := hp μ
      push_cast at h₁ ⊢
      linarith
    choose i hi₁ hi₂ hi₃ using hbound
    have hc : ∀ μ, (((k μ * ((2 * a + 1 : ℕ) : ℤ) + i μ : ℤ) : ℝ)) * τ =
        (k μ : ℝ) * (((2 * a + 1 : ℕ) : ℝ) * τ) + (i μ : ℝ) * τ := by
      intro μ
      push_cast
      ring
    refine ⟨cubeAt (torusProj 4 S fun μ =>
      ((k μ * ((2 * a + 1 : ℕ) : ℤ) + i μ : ℤ) : ℝ) * τ) τ, ⟨⟨_, ⟨_, rfl⟩, rfl⟩, _, hD, ?_⟩, ?_⟩
    · rw [cubeAt_torusProj hS, cubeAt_torusProj hS]
      refine image_mono fun q hq μ => ?_
      have h₁ := hq μ
      simp only [hc] at h₁
      obtain ⟨l, u⟩ := abs_le.1 h₁
      have h₂ : -(a : ℝ) * τ ≤ (i μ : ℝ) * τ := mul_le_mul_of_nonneg_right (hi₂ μ) hτ.le
      have h₃ : (i μ : ℝ) * τ ≤ (a : ℝ) * τ := mul_le_mul_of_nonneg_right (hi₃ μ) hτ.le
      rw [abs_le]
      push_cast at l u ⊢
      constructor <;> linarith
    · rw [cubeAt_torusProj hS]
      refine ⟨p, fun μ => ?_, rfl⟩
      have h₁ := hi₁ μ
      show |p μ - ((k μ * ((2 * a + 1 : ℕ) : ℤ) + i μ : ℤ) : ℝ) * τ| ≤ τ / 2
      rw [hc]
      rw [show p μ - ((k μ : ℝ) * (((2 * a + 1 : ℕ) : ℝ) * τ) + (i μ : ℝ) * τ) =
        ((p μ - (k μ : ℝ) * (((2 * a + 1 : ℕ) : ℝ) * τ)) / τ - (i μ : ℝ)) * τ by
          rw [sub_mul, div_mul_cancel₀ _ hτ.ne']
          ring]
      rw [abs_mul, abs_of_pos hτ]
      linarith [mul_le_mul_of_nonneg_right h₁ hτ.le]
  · rintro x ⟨C, ⟨-, D, hD, hCD⟩, hx⟩
    exact ⟨D, hD, hCD hx⟩
theorem isCubeUnion_univ (hS : 0 < S) {τ : ℝ} (hτ : 0 < τ) :
    IsCubeUnion τ (univ : Set (PeriodicTorus 4 S)) := by
  refine ⟨cubePartition 4 S τ, Subset.rfl, (eq_univ_of_forall fun x => ?_).symm⟩
  obtain ⟨p, hp, -⟩ := exists_lift_norm_eq_supNorm hS x
  subst hp
  refine ⟨cubeAt (torusProj 4 S fun μ => ((round (p μ / τ) : ℤ) : ℝ) * τ) τ,
    ⟨_, ⟨_, rfl⟩, rfl⟩, ?_⟩
  rw [cubeAt_torusProj hS]
  refine ⟨p, fun μ => ?_, rfl⟩
  have hr := abs_sub_round (p μ / τ)
  rw [show p μ - ((round (p μ / τ) : ℤ) : ℝ) * τ = (p μ / τ - round (p μ / τ)) * τ by
    rw [sub_mul, div_mul_cancel₀ _ hτ.ne']]
  rw [abs_mul, abs_of_pos hτ]
  linarith [mul_le_mul_of_nonneg_right hr hτ.le]
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
theorem zero_lt_L (𝒮 : RegionSequence.NestedRegions) : (0 : ℝ) < 𝒮.L := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.blockFactor_pos <;> assumption
theorem scale_eq (𝒮 : RegionSequence.NestedRegions) (n : ℕ) :
    𝒮.scale n = (𝒮.L : ℝ) ^ n * 𝒮.ξ := by apply _root_.YangMills.Construction.RegionSequence.NestedRegions.scale_eq_pow_mul <;> assumption
theorem scale_pos (𝒮 : RegionSequence.NestedRegions) (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem exists_eq_L_pow_succ {K m R₁ : ℕ} (h : 𝒮.IsLevelUnitChain K m M R₁) :
    ∃ e : ℕ, M = 𝒮.L ^ (e + 1) := by
  obtain ⟨h₁, μ, rfl⟩ := h.separated.blockSize_isPowerGe
  have h₂ := 𝒮.thirteen_le_L
  cases μ with
  | zero =>
    simp only [pow_zero] at h₁
    omega
  | succ e => exact ⟨e, rfl⟩
theorem cubeSide_pos {K m R₁ : ℕ} (h : 𝒮.IsLevelUnitChain K m M R₁) (n : ℕ) :
    0 < cubeSide 𝒮 M n := by
  obtain ⟨e, rfl⟩ := exists_eq_L_pow_succ h
  unfold cubeSide
  push_cast
  exact mul_pos (pow_pos (zero_lt_L 𝒮) _) (scale_pos 𝒮 n)
theorem cubeSide_L_pow_succ (e n : ℕ) :
    cubeSide 𝒮 (𝒮.L ^ (e + 1)) n = ((𝒮.L ^ e : ℕ) : ℝ) * 𝒮.scale (n + 1) := by
  unfold cubeSide
  rw [scale_eq, scale_eq]
  push_cast
  ring
theorem cubeSide_succ (n : ℕ) : cubeSide 𝒮 M (n + 1) = (𝒮.L : ℝ) * cubeSide 𝒮 M n := by apply _root_.YangMills.Construction.PartitionCubes.CornerShell.cubeSide_succ <;> assumption
theorem exists_side_eq_two_mul_cubeSide {K m R₁ : ℕ} (h : 𝒮.IsLevelUnitChain K m M R₁)
    {n : ℕ} (hn : n ≤ topLevel 𝒮) :
    ∃ N : ℕ, 0 < N ∧ 𝒮.side = 2 * (N : ℝ) * cubeSide 𝒮 M n := by
  obtain ⟨k, hk, hside⟩ := h.separated.period_eq_even_mul
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hn
  have hL := 𝒮.thirteen_le_L
  refine ⟨k * 𝒮.L ^ e, Nat.mul_pos hk (Nat.pow_pos (by omega)), ?_⟩
  have hs : scaleSpacing 𝒮.L 𝒮.ξ (lastNonemptyIndex 𝒮.Ω : ℤ) = (𝒮.L : ℝ) ^ e * 𝒮.scale n := by
    have he' : lastNonemptyIndex 𝒮.Ω = n + e := he
    rw [he', scale_eq]
    simp only [scaleSpacing, zpow_natCast]
    ring
  rw [hside, hs]
  unfold cubeSide
  push_cast
  ring
theorem exists_nextCentre_eq {K m R₁ : ℕ} (h : 𝒮.IsLevelUnitChain K m M R₁) (Q : LevelCube 𝒮 M)
    {c : Fin 4 → ℝ} (hc : c ∈ Q.nextCentres) :
    ∃ j : Fin 4 → ℤ, c = fun μ => (j μ : ℝ) * cubeSide 𝒮 M Q.level := by
  obtain ⟨-, ⟨c₀, hc₀, hC⟩, -⟩ := hc
  obtain ⟨k, rfl⟩ : ∃ k : Fin 4 → ℤ,
      c₀ = torusProj 4 𝒮.side fun μ => (k μ : ℝ) * cubeSide 𝒮 M Q.level := hc₀
  rw [cubeAt_torusProj 𝒮.side_pos] at hC
  obtain ⟨N, hN, hside⟩ := exists_side_eq_two_mul_cubeSide h Q.level_le
  have hw := cubeSide_pos h Q.level
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hle : 2 * cubeSide 𝒮 M Q.level ≤ 𝒮.side := by
    rw [hside]
    linarith [mul_le_mul_of_nonneg_right hN' hw.le]
  choose i hi using exists_centre_eq_add_mul_of_image_eq hw hle hC
  refine ⟨fun μ => k μ + 2 * (N : ℤ) * i μ, funext fun μ => ?_⟩
  rw [hi μ, hside]
  push_cast
  ring
theorem torusSide_pos {K m R₁ : ℕ} (h : 𝒮.IsLevelUnitChain K m M R₁) (Q : LevelCube 𝒮 M) :
    0 < Q.torusSide :=
  mul_pos (by norm_num) (cubeSide_pos h Q.level)
theorem isCubeUnion_nextRegion_cubeSide {K m R₁ : ℕ} (h : 𝒮.IsLevelUnitChain K m M R₁)
    (Q : LevelCube 𝒮 M) : IsCubeUnion (cubeSide 𝒮 M Q.level) Q.nextRegion := by
  refine ⟨(fun c => torusProj 4 Q.torusSide '' closedCube c (cubeSide 𝒮 M Q.level)) ''
    Q.nextCentres, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    obtain ⟨j, rfl⟩ := exists_nextCentre_eq h Q hc
    exact ⟨_, ⟨j, rfl⟩, (cubeAt_torusProj (torusSide_pos h Q) _ _).symm⟩
  · rw [sUnion_image, LevelCube.nextRegion, image_iUnion₂]
theorem isCubeUnion_nextRegion_scale {K m R₁ : ℕ} (h : 𝒮.IsLevelUnitChain K m M R₁)
    (Q : LevelCube 𝒮 M) : IsCubeUnion (𝒮.scale (Q.level + 1)) Q.nextRegion := by
  obtain ⟨e, rfl⟩ := exists_eq_L_pow_succ h
  have hb := isCubeUnion_nextRegion_cubeSide h Q
  rw [cubeSide_L_pow_succ] at hb
  exact isCubeUnion_of_odd_mul (torusSide_pos h Q) (scale_pos 𝒮 _) (𝒮.odd_L.pow) hb
theorem isAdmissible {K m R₁ : ℕ} (h : 𝒮.IsLevelUnitChain K m M R₁) (Q : LevelCube 𝒮 M) :
    Q.IsAdmissible := by
  refine ⟨torusSide_pos h Q, ?_, ?_⟩
  · obtain ⟨e, rfl⟩ := exists_eq_L_pow_succ h
    refine ⟨4 * ((𝒮.L ^ e : ℕ) : ℤ), ?_⟩
    have hs : scaleSpacing 𝒮.L 𝒮.ξ ((Q.level + 1 : ℕ) : ℤ) = 𝒮.scale (Q.level + 1) := rfl
    rw [hs, LevelCube.torusSide, cubeSide_L_pow_succ]
    push_cast
    ring
  · intro j hj
    by_cases hjn : j ≤ Q.level
    · simp only [LevelCube.torusRegions, hjn, if_true]
      exact isCubeUnion_univ (torusSide_pos h Q) (scale_pos 𝒮 j)
    · have hj' : j = Q.level + 1 := by omega
      subst hj'
      have hs : Q.torusRegions (Q.level + 1) = Q.nextRegion := by simp [LevelCube.torusRegions]
      rw [hs]
      exact isCubeUnion_nextRegion_scale h Q
theorem torusProj_liftedCentre (Q : LevelCube 𝒮 M) :
    torusProj 4 𝒮.side Q.liftedCentre = Q.centre := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_liftedCentre <;> assumption
end NextRegionOfFirstType
end PartitionCubes
end YangMills.Construction
