import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.DirichletOperator.BondsNearACubeCarriedToItsTorusProof
import YangMills.Construction.DirichletOperator.DifferenceOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.Torus.NestedCubePartitionsProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
open Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes.FirstTypeMaps
section Projection
variable {T τ : ℝ}
theorem torusProj_add (u v : Fin 4 → ℝ) :
    torusProj 4 T (u + v) = torusProj 4 T u + torusProj 4 T v := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_add <;> assumption
theorem torusProj_sub (u v : Fin 4 → ℝ) :
    torusProj 4 T (u - v) = torusProj 4 T u - torusProj 4 T v := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusBonds.torusProj_sub <;> assumption
theorem torusProj_surjective : Function.Surjective (torusProj 4 T) := by apply _root_.YangMills.Construction.TestFunctions.torusProj_surjective <;> assumption
theorem supNorm_torusProj_le (v : Fin 4 → ℝ) : supNorm (torusProj 4 T v) ≤ ‖v‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_proj_le <;> assumption
theorem abs_apply_le_norm (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ ‖v‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.abs_apply_le_pi_norm <;> assumption
theorem exists_lift_norm_le_supNorm (x : PeriodicTorus 4 T) :
    ∃ v : Fin 4 → ℝ, torusProj 4 T v = x ∧ ‖v‖ ≤ supNorm x := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.exists_proj_eq_norm_le <;> assumption
theorem cubeAt_torusProj (hτ : 0 ≤ τ) (u : Fin 4 → ℝ) :
    cubeAt (torusProj 4 T u) τ = torusProj 4 T '' closedCube u τ := by
  ext x
  constructor
  · intro hx
    have hx' : supNorm (x - torusProj 4 T u) ≤ τ / 2 := hx
    obtain ⟨w, hw, hn⟩ := exists_lift_norm_le_supNorm (x - torusProj 4 T u)
    refine ⟨u + w, fun μ => ?_, ?_⟩
    · have h₁ := abs_apply_le_norm w μ
      simp only [Pi.add_apply, add_sub_cancel_left]
      linarith
    · rw [torusProj_add, hw]
      abel
  · rintro ⟨p, hp, rfl⟩
    show supNorm (torusProj 4 T p - torusProj 4 T u) ≤ τ / 2
    rw [← torusProj_sub]
    refine (supNorm_torusProj_le _).trans
      ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => ?_)
    simpa [Real.norm_eq_abs] using hp μ
theorem exists_int_mul_of_torusProj_eq {p q : Fin 4 → ℝ}
    (h : torusProj 4 T p = torusProj 4 T q) (μ : Fin 4) :
    ∃ a : ℤ, p μ - q μ = a * T := by
  have h₁ : ((p μ - q μ : ℝ) : AddCircle T) = 0 := by
    rw [AddCircle.coe_sub, sub_eq_zero]
    exact congrFun h μ
  obtain ⟨a, ha⟩ := (AddCircle.coe_eq_zero_iff T).1 h₁
  exact ⟨a, by rw [← ha]; simp⟩
theorem eq_of_torusProj_eq (hT : 0 < T) {p q : Fin 4 → ℝ}
    (h : torusProj 4 T p = torusProj 4 T q) (hpq : ∀ μ, |p μ - q μ| < T) : p = q := by
  funext μ
  obtain ⟨a, ha⟩ := exists_int_mul_of_torusProj_eq h μ
  have h₁ := hpq μ
  rw [ha, abs_mul, abs_of_pos hT] at h₁
  have h₂ : |(a : ℝ)| < 1 := lt_of_mul_lt_mul_right (by simpa using h₁) hT.le
  have h₃ : a = 0 := by
    have h₄ : |a| < 1 := by exact_mod_cast h₂
    exact Int.abs_lt_one_iff.1 h₄
  rw [h₃] at ha
  simp only [Int.cast_zero, zero_mul] at ha
  linarith
theorem exists_int_near (a : ℕ) (y : ℝ) (hy : |y| ≤ (2 * a + 1) / 2) :
    ∃ i : ℤ, |(i : ℝ)| ≤ a ∧ |y - i| ≤ 1 / 2 := by apply _root_.YangMills.Construction.Torus.NestedCubes.Refinement.exists_int_near_of_abs_le <;> assumption
theorem isCubeUnion_univ (hτ : 0 < τ) : IsCubeUnion τ (univ : Set (PeriodicTorus 4 T)) := by
  refine ⟨cubePartition 4 T τ, Subset.rfl, ?_⟩
  symm
  rw [eq_univ_iff_forall]
  intro x
  obtain ⟨v, rfl⟩ := torusProj_surjective x
  refine ⟨cubeAt (torusProj 4 T fun μ => (round (v μ / τ) : ℝ) * τ) τ,
    ⟨_, ⟨fun μ => round (v μ / τ), rfl⟩, rfl⟩, ?_⟩
  rw [cubeAt_torusProj hτ.le]
  refine ⟨v, fun μ => ?_, rfl⟩
  show |v μ - (round (v μ / τ) : ℝ) * τ| ≤ τ / 2
  have h := abs_sub_round (v μ / τ)
  have e : v μ - (round (v μ / τ) : ℝ) * τ = (v μ / τ - round (v μ / τ)) * τ := by
    field_simp
  rw [e, abs_mul, abs_of_pos hτ]
  nlinarith
theorem isCubeUnion_image_of_aligned (hτ : 0 < τ) (a : ℕ) (C : Set (Fin 4 → ℝ))
    (hC : ∀ c ∈ C, ∀ μ, ∃ j : ℤ, c μ = j * ((2 * a + 1) * τ)) :
    IsCubeUnion τ (torusProj 4 T '' ⋃ c ∈ C, closedCube c ((2 * a + 1) * τ)) := by
  refine ⟨{X | ∃ k : Fin 4 → ℤ, closedCube (fun μ => (k μ : ℝ) * τ) τ ⊆
        (⋃ c ∈ C, closedCube c ((2 * (a : ℝ) + 1) * τ)) ∧
      X = torusProj 4 T '' closedCube (fun μ => (k μ : ℝ) * τ) τ}, ?_, ?_⟩
  · rintro X ⟨k, -, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, (cubeAt_torusProj hτ.le _).symm⟩
  · ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.1 hp
      have near : ∀ μ, ∃ k : ℤ, |p μ - k * τ| ≤ τ / 2 ∧
          ∀ w : ℝ, |w - k * τ| ≤ τ / 2 → |w - c μ| ≤ (2 * a + 1) * τ / 2 := by
        intro μ
        obtain ⟨j, hj⟩ := hC c hc μ
        have hy : |(p μ - c μ) / τ| ≤ (2 * a + 1) / 2 := by
          have h₁ : |p μ - c μ| ≤ (2 * a + 1) * τ / 2 := hpc μ
          rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
          linarith
        obtain ⟨i, hi, hi'⟩ := exists_int_near a _ hy
        have ek : ((j * (2 * a + 1) + i : ℤ) : ℝ) * τ = c μ + i * τ := by
          rw [hj]
          push_cast
          ring
        refine ⟨j * (2 * a + 1) + i, ?_, fun w hw => ?_⟩
        · rw [ek]
          have e : p μ - (c μ + i * τ) = ((p μ - c μ) / τ - i) * τ := by
            field_simp
            ring
          rw [e, abs_mul, abs_of_pos hτ]
          nlinarith
        · rw [ek] at hw
          have h₁ : |(i : ℝ) * τ| ≤ a * τ := by
            rw [abs_mul, abs_of_pos hτ]
            exact mul_le_mul_of_nonneg_right hi hτ.le
          have e : w - c μ = (w - (c μ + i * τ)) + i * τ := by ring
          rw [e]
          refine (abs_add_le _ _).trans ?_
          linarith
      choose k hk₁ hk₂ using near
      refine ⟨_, ⟨k, fun w hw => ?_, rfl⟩, ⟨p, hk₁, rfl⟩⟩
      exact mem_iUnion₂.2 ⟨c, hc, fun μ => hk₂ μ (w μ) (hw μ)⟩
    · rintro ⟨X, ⟨k, hk, rfl⟩, p, hp, rfl⟩
      exact ⟨p, hk hp, rfl⟩
theorem centre_mem_lattice {S σ : ℝ} (hσ : 0 < σ) (K : ℕ) (hS : S = 2 * K * σ)
    (c : Fin 4 → ℝ) (h : torusProj 4 S '' closedCube c σ ∈ cubePartition 4 S σ) (μ : Fin 4) :
    ∃ j : ℤ, c μ = j * σ := by
  subst hS
  obtain ⟨y, ⟨k, rfl⟩, hQ⟩ := h
  rw [cubeAt_torusProj hσ.le] at hQ
  have hmem : ∀ e : ℝ, |e| ≤ σ / 2 → ∃ q ∈ closedCube (fun ν => (k ν : ℝ) * σ) σ,
      torusProj 4 (2 * K * σ) q = torusProj 4 (2 * K * σ) fun ν => c ν + e := by
    intro e he
    have h₁ : torusProj 4 (2 * K * σ) (fun ν => c ν + e) ∈
        torusProj 4 (2 * K * σ) '' closedCube c σ :=
      ⟨_, fun ν => by simpa using he, rfl⟩
    rw [hQ] at h₁
    exact h₁
  have hhalf : |σ / 2| = σ / 2 := abs_of_pos (half_pos hσ)
  obtain ⟨q₁, hq₁, e₁⟩ := hmem (σ / 2) hhalf.le
  obtain ⟨q₂, hq₂, e₂⟩ := hmem (-(σ / 2)) (by rw [abs_neg, hhalf])
  obtain ⟨a, ha⟩ := exists_int_mul_of_torusProj_eq e₁ μ
  obtain ⟨b, hb⟩ := exists_int_mul_of_torusProj_eq e₂ μ
  have i₁ := abs_le.1 (show |q₁ μ - k μ * σ| ≤ σ / 2 from hq₁ μ)
  have i₂ := abs_le.1 (show |q₂ μ - k μ * σ| ≤ σ / 2 from hq₂ μ)
  have n₀ : (0 : ℤ) ≤ b * K - a * K := by
    have h₁ : (0 : ℝ) * σ ≤ ((b * K - a * K : ℤ) : ℝ) * σ := by
      push_cast
      linarith [i₁.2, i₂.1]
    exact_mod_cast le_of_mul_le_mul_right h₁ hσ
  have n₁ : b * K - a * K ≤ (1 : ℤ) := by
    have h₁ : ((b * K - a * K : ℤ) : ℝ) * σ ≤ 1 * σ := by
      push_cast
      linarith [i₁.1, i₂.2]
    exact_mod_cast le_of_mul_le_mul_right h₁ hσ
  rcases (by omega : b * K - a * K = 0 ∨ b * K - a * K = 1) with m | m
  · have hm : ((b * K - a * K : ℤ) : ℝ) * σ = 0 := by rw [m, Int.cast_zero, zero_mul]
    refine ⟨k μ - 2 * (a * K), ?_⟩
    push_cast at hm ⊢
    linarith [i₁.2, i₂.1]
  · have hm : ((b * K - a * K : ℤ) : ℝ) * σ = σ := by rw [m, Int.cast_one, one_mul]
    refine ⟨k μ - 2 * (a * K) - 1, ?_⟩
    push_cast at hm ⊢
    linarith [i₁.1, i₂.2]
theorem bijOn_torusProj_box {S σ : ℝ} (hσ : 0 < σ) (hS : 2 * σ ≤ S) (c : Fin 4 → ℝ) :
    BijOn (torusProj 4 S) {p | ∀ μ, |p μ - c μ| < σ}
      {x | supNorm (x - torusProj 4 S c) < σ} := by
  refine ⟨fun p hp => ?_, fun p hp q hq h => ?_, fun x hx => ?_⟩
  · show supNorm (torusProj 4 S p - torusProj 4 S c) < σ
    rw [← torusProj_sub]
    refine lt_of_le_of_lt (supNorm_torusProj_le _) ((pi_norm_lt_iff hσ).2 fun μ => ?_)
    simpa [Real.norm_eq_abs] using hp μ
  · refine eq_of_torusProj_eq (by linarith) h fun μ => ?_
    have h₁ := abs_lt.1 (hp μ)
    have h₂ := abs_lt.1 (hq μ)
    rw [abs_lt]
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  · obtain ⟨v, hv, hn⟩ := exists_lift_norm_le_supNorm (x - torusProj 4 S c)
    have hx' : supNorm (x - torusProj 4 S c) < σ := hx
    refine ⟨c + v, fun μ => ?_, ?_⟩
    · have h₁ := abs_apply_le_norm v μ
      simp only [Pi.add_apply, add_sub_cancel_left]
      linarith
    · rw [torusProj_add, hv]
      abel
end Projection
section LevelCubes
variable {𝒮 : RegionSequence.NestedRegions} {K m M R₁ : ℕ}
theorem torusProj_liftedCentre (Q : LevelCube 𝒮 M) :
    torusProj 4 𝒮.side Q.liftedCentre = Q.centre := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_liftedCentre <;> assumption
theorem cast_L_pos (𝒮 : RegionSequence.NestedRegions) : (0 : ℝ) < 𝒮.L := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.blockFactor_pos <;> assumption
theorem scaleSpacing_pos (𝒮 : RegionSequence.NestedRegions) (j : ℤ) :
    0 < scaleSpacing 𝒮.L 𝒮.ξ j :=
  mul_pos (zpow_pos (cast_L_pos 𝒮) _) 𝒮.ξ_pos
theorem cubeSide_pos (hS : 𝒮.IsLevelUnitChain K m M R₁) (n : ℕ) :
    0 < cubeSide 𝒮 M n := by
  have h₁ := hS.separated.blockSize_isPowerGe.1
  have h₂ := 𝒮.thirteen_le_L
  have h₃ : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  exact mul_pos h₃ (scaleSpacing_pos 𝒮 _)
theorem exists_side_eq_even_mul_cubeSide (hS : 𝒮.IsLevelUnitChain K m M R₁)
    (Q : LevelCube 𝒮 M) :
    ∃ N : ℕ, 0 < N ∧ 𝒮.side = 2 * N * cubeSide 𝒮 M Q.level := by
  obtain ⟨k, hk, hside⟩ := hS.separated.period_eq_even_mul
  have hle : Q.level ≤ lastNonemptyIndex 𝒮.Ω := Q.level_le
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  have hL := 𝒮.thirteen_le_L
  refine ⟨k * 𝒮.L ^ e, Nat.mul_pos hk (Nat.pow_pos (by omega)), ?_⟩
  rw [hside, he]
  have hL₀ : (𝒮.L : ℝ) ≠ 0 := (cast_L_pos 𝒮).ne'
  simp only [cubeSide, scale, scaleSpacing]
  push_cast
  rw [zpow_add₀ hL₀, zpow_natCast (𝒮.L : ℝ) e]
  ring
theorem exists_eq_L_mul_odd (hS : 𝒮.IsLevelUnitChain K m M R₁) :
    ∃ a : ℕ, M = 𝒮.L * (2 * a + 1) := by
  obtain ⟨hLM, e, he⟩ := hS.separated.blockSize_isPowerGe
  have hL := 𝒮.thirteen_le_L
  cases e with
  | zero =>
    rw [pow_zero] at he
    omega
  | succ e =>
    obtain ⟨a, ha⟩ := 𝒮.odd_L.pow (n := e)
    exact ⟨a, by rw [he, pow_succ, ha]; ring⟩
theorem cubeSide_eq_odd_mul {a : ℕ} (ha : M = 𝒮.L * (2 * a + 1)) (n : ℕ) :
    cubeSide 𝒮 M n = (2 * a + 1) * scaleSpacing 𝒮.L 𝒮.ξ ((n + 1 : ℕ) : ℤ) := by
  have hL₀ : (𝒮.L : ℝ) ≠ 0 := (cast_L_pos 𝒮).ne'
  simp only [cubeSide, scale, scaleSpacing]
  rw [ha]
  push_cast
  rw [zpow_add₀ hL₀, zpow_one]
  ring
theorem isAdmissible (hS : 𝒮.IsLevelUnitChain K m M R₁) (Q : LevelCube 𝒮 M) :
    Q.IsAdmissible := by
  obtain ⟨a, ha⟩ := exists_eq_L_mul_odd hS
  have hτ := scaleSpacing_pos 𝒮 ((Q.level + 1 : ℕ) : ℤ)
  refine ⟨mul_pos (by norm_num) (cubeSide_pos hS _), ⟨4 * (2 * a + 1), ?_⟩, fun j hj => ?_⟩
  · show 8 * cubeSide 𝒮 M Q.level = _
    rw [cubeSide_eq_odd_mul ha]
    push_cast
    ring
  · by_cases h : j ≤ Q.level
    · have e : Q.torusRegions j = univ := by simp [LevelCube.torusRegions, h]
      rw [e]
      exact isCubeUnion_univ (scaleSpacing_pos 𝒮 _)
    · have hj' : j = Q.level + 1 := by omega
      subst hj'
      have e : Q.torusRegions (Q.level + 1) = Q.nextRegion := by
        simp [LevelCube.torusRegions]
      rw [e]
      have e₂ : Q.nextRegion = torusProj 4 Q.torusSide '' ⋃ c ∈ Q.nextCentres,
          closedCube c ((2 * a + 1) * scaleSpacing 𝒮.L 𝒮.ξ ((Q.level + 1 : ℕ) : ℤ)) := by
        rw [← cubeSide_eq_odd_mul ha]
        rfl
      rw [e₂]
      refine isCubeUnion_image_of_aligned hτ a _ fun c hc μ => ?_
      obtain ⟨N, -, hN⟩ := exists_side_eq_even_mul_cubeSide hS Q
      rw [← cubeSide_eq_odd_mul ha]
      exact centre_mem_lattice (cubeSide_pos hS _) N hN c hc.2.1 μ
theorem firstTypeSystem_maps (hS : 𝒮.IsLevelUnitChain K m M R₁) (Q : LevelCube 𝒮 M) :
    (∃ h : Q.IsAdmissible, Q.firstTypeSystem.setting = Q.torusSetting h) ∧
    BijOn (torusProj 4 𝒮.side) {p | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level}
      Q.strictPts ∧
    InjOn (torusProj 4 Q.firstTypeSystem.setting.side)
      (closedCube Q.liftedCentre (6 * cubeSide 𝒮 M Q.level)) ∧
    (∀ p ∈ {p : Fin 4 → ℝ | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level},
      Q.firstTypeSystem.embed (torusProj 4 𝒮.side p) =
        torusProj 4 Q.firstTypeSystem.setting.side p) ∧
    BijOn Q.firstTypeSystem.embed Q.strictPts
      (torusProj 4 Q.firstTypeSystem.setting.side ''
        {p | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level}) ∧
    ∀ p v : Fin 4 → ℝ,
      p ∈ {p : Fin 4 → ℝ | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level} →
      p + v ∈ {p : Fin 4 → ℝ | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level} →
      Q.firstTypeSystem.embed (torusProj 4 𝒮.side p + torusProj 4 𝒮.side v) =
        Q.firstTypeSystem.embed (torusProj 4 𝒮.side p) +
          torusProj 4 Q.firstTypeSystem.setting.side v := by
  have hadm := isAdmissible hS Q
  have hset : Q.firstTypeSetting = Q.torusSetting hadm := dif_pos hadm
  have hT : Q.firstTypeSetting.side = 8 * cubeSide 𝒮 M Q.level := by
    rw [hset]
    rfl
  have hσ := cubeSide_pos hS (𝒮 := 𝒮) Q.level
  obtain ⟨N, hN, hside⟩ := exists_side_eq_even_mul_cubeSide hS Q
  have h2σ : 2 * cubeSide 𝒮 M Q.level ≤ 𝒮.side := by
    have h₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [hside]
    nlinarith
  have hbij : BijOn (torusProj 4 𝒮.side)
      {p | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level} Q.strictPts := by
    have h₁ := bijOn_torusProj_box hσ h2σ Q.liftedCentre
    rw [torusProj_liftedCentre] at h₁
    exact h₁
  have hTpos : 0 < Q.firstTypeSetting.side := by
    rw [hT]
    linarith
  have hinj : InjOn (torusProj 4 Q.firstTypeSetting.side)
      (closedCube Q.liftedCentre (6 * cubeSide 𝒮 M Q.level)) := by
    intro p hp q hq h
    refine eq_of_torusProj_eq hTpos h fun μ => ?_
    have h₁ := abs_le.1 (hp μ)
    have h₂ := abs_le.1 (hq μ)
    rw [abs_lt, hT]
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  have hsub : {p : Fin 4 → ℝ | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level} ⊆
      closedCube Q.liftedCentre (6 * cubeSide 𝒮 M Q.level) := by
    intro p hp μ
    have h₁ : |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level := hp μ
    linarith
  have hchart : ∀ p ∈ {p : Fin 4 → ℝ | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level},
      Q.chart (torusProj 4 𝒮.side p) = p := by
    intro p hp
    have hex : ∃ p' : Fin 4 → ℝ, (∀ μ, |p' μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level) ∧
        torusProj 4 𝒮.side p' = torusProj 4 𝒮.side p := ⟨p, hp, rfl⟩
    have h := Classical.epsilon_spec hex
    exact hbij.injOn h.1 hp h.2
  have hemb : ∀ p ∈ {p : Fin 4 → ℝ | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level},
      Q.firstTypeSystem.embed (torusProj 4 𝒮.side p) =
        torusProj 4 Q.firstTypeSetting.side p := by
    intro p hp
    show torusProj 4 Q.firstTypeSetting.side (Q.chart (torusProj 4 𝒮.side p)) = _
    rw [hchart p hp]
  refine ⟨⟨hadm, hset⟩, hbij, hinj, hemb, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := hbij.surjOn hx
    exact ⟨p, hp, (hemb p hp).symm⟩
  · intro x hx y hy h
    obtain ⟨p, hp, rfl⟩ := hbij.surjOn hx
    obtain ⟨q, hq, rfl⟩ := hbij.surjOn hy
    rw [hemb p hp, hemb q hq] at h
    rw [hinj (hsub hp) (hsub hq) h]
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨torusProj 4 𝒮.side p, hbij.mapsTo hp, hemb p hp⟩
  · intro p v hp hpv
    rw [← torusProj_add, hemb _ hpv, hemb _ hp]
    exact torusProj_add p v
end LevelCubes
theorem statement_holds : Statement := by
  intro 𝒮 K m M R₁ hS Q hQ
  have hsys : Q.system = Q.firstTypeSystem := if_neg hQ.2
  rw [hsys]
  exact firstTypeSystem_maps hS Q
end PartitionCubes.FirstTypeMaps
end YangMills.Construction
