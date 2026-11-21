import YangMills.Construction.Lattice.CornersAndEdgesInTwoCoordinates
import YangMills.Construction.Lattice.LiftsOfCubesVerticesAndEdges
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubeAgreement
variable (S : LevelUnitPartition)
theorem proj_add_of_isPointLift (hL : S.params.L ≠ 0) {y : S.Points} {c : Fin 4 → ℝ}
    (hc : S.IsPointLift y c) (r : Fin 4 → ℝ) (μ : Fin 4) :
    S.proj (c + r) μ = y μ +
      ((meshSize S.params.L (levelDepth S.params.K S.level) * r μ : ℝ) :
        AddCircle (torusSide S.params.L S.params.m)) := by
  have h0 : levelProj S.params.L S.params.m S.params.K S.level c = y :=
    (levelProj_eq_iff_isLevelLift hL _ _ _ y c).mpr hc
  have h1 := congrFun h0 μ
  simp only [levelProj, TorusMetric.torusProj, Pi.smul_apply, smul_eq_mul] at h1
  simp only [LevelUnitPartition.proj, levelProj, TorusMetric.torusProj, Pi.smul_apply,
    smul_eq_mul, Pi.add_apply, mul_add, AddCircle.coe_add, h1]
theorem eq_zero_of_zsmul_eq_of_abs_le {a P N r : ℝ} (ha : 0 < a) (hP : P = N * a) (hN : 2 ≤ N)
    (k : ℤ) (hk : k • P = r) (hr : |r| ≤ a) : r = 0 := by
  by_contra hne
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hk.symm)
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
    exact_mod_cast this
  have hNa : 2 * a ≤ P := by rw [hP]; nlinarith
  have hPpos : 0 < P := by linarith
  have hr' : |r| = |(k : ℝ)| * P := by
    rw [← hk, zsmul_eq_mul, abs_mul, abs_of_pos hPpos]
  nlinarith
theorem edgeAt_eq_setOf (hL : S.params.L ≠ 0) {s a N : ℝ}
    (hs : s = meshSize S.params.L (levelDepth S.params.K S.level)) (hs0 : 0 < s)
    (hMs : (S.side : ℝ) * s = a) (ha : a = meshSize S.params.L S.index) (ha0 : 0 < a)
    (hside : torusSide S.params.L S.params.m = N * a) (hN : 2 ≤ N)
    {y : Site S.params.L S.params.m S.index} {c : Fin 4 → ℝ}
    (hc : S.IsPointLift (y : S.Points) c)
    (hcube : cubeAround y = S.proj '' S.closedBox c)
    {ε : Fin 4 → ℝ} (hε : ∀ ν, ε ν = 1 ∨ ε ν = -1) {μ : Fin 4} (hμ : ε μ = -1) :
    S.edgeAt (c + ((S.side : ℝ) / 2) • ε) μ =
      {x | x ∈ cubeAround y ∧ ∀ ν, ν ≠ μ →
        x ν = (y : S.Points) ν +
          ((ε ν * meshSize S.params.L S.index / 2 : ℝ) :
            AddCircle (torusSide S.params.L S.params.m))} := by
  have hM0 : 0 < (S.side : ℝ) := by
    have : s * (S.side : ℝ) > 0 := by rw [mul_comm, hMs]; exact ha0
    exact (pos_iff_pos_of_mul_pos this).mp hs0
  ext x
  constructor
  · rintro ⟨z, ⟨t, ht0, ht1, rfl⟩, rfl⟩
    refine ⟨?_, fun ν hν => ?_⟩
    · rw [hcube]
      refine ⟨_, fun ν => ?_, rfl⟩
      by_cases hνμ : ν = μ
      · subst hνμ
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordVec, Pi.single_eq_same,
          hμ, Set.mem_Icc]
        constructor <;> linarith
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordVec,
          Pi.single_eq_of_ne hνμ, Set.mem_Icc]
        rcases hε ν with h | h <;> rw [h] <;> constructor <;> linarith
    · have hrw : c + ((S.side : ℝ) / 2) • ε + t • coordVec μ =
          c + (((S.side : ℝ) / 2) • ε + t • coordVec μ) := by
        rw [add_assoc]
      rw [hrw, proj_add_of_isPointLift S hL hc, ← hs, ← ha]
      congr 2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordVec,
        Pi.single_eq_of_ne hν]
      rw [← hMs]
      ring
  · rintro ⟨hx, hx'⟩
    rw [hcube] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hzν : ∀ ν, ν ≠ μ → z ν = c ν + (S.side : ℝ) / 2 * ε ν := by
      intro ν hν
      have h1 := hx' ν hν
      have hrw : z = c + (z - c) := by simp
      rw [hrw, proj_add_of_isPointLift S hL hc, ← hs, ← ha] at h1
      have h2 := add_left_cancel h1
      have h3 : (((s * (z - c) ν - ε ν * a / 2 : ℝ)) :
          AddCircle (torusSide S.params.L S.params.m)) = 0 := by
        rw [AddCircle.coe_sub, h2, sub_self]
      obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).mp h3
      have hzc := hz ν
      simp only [Set.mem_Icc] at hzc
      have hb1 : s * (z ν - c ν) ≤ a / 2 := by
        have := mul_le_mul_of_nonneg_left (show z ν - c ν ≤ (S.side : ℝ) / 2 by linarith)
          hs0.le
        rw [← hMs]; linarith
      have hb2 : -(a / 2) ≤ s * (z ν - c ν) := by
        have := mul_le_mul_of_nonneg_left (show -((S.side : ℝ) / 2) ≤ z ν - c ν by linarith)
          hs0.le
        rw [← hMs]; linarith
      have hzero : s * (z - c) ν - ε ν * a / 2 = 0 := by
        refine eq_zero_of_zsmul_eq_of_abs_le ha0 hside hN k hk ?_
        simp only [Pi.sub_apply]
        rw [abs_le]
        rcases hε ν with h | h <;> rw [h] <;> constructor <;> linarith
      simp only [Pi.sub_apply] at hzero
      have : s * (z ν - (c ν + (S.side : ℝ) / 2 * ε ν)) = 0 := by
        rw [← hMs] at hzero
        linarith
      have := (mul_eq_zero.mp this).resolve_left hs0.ne'
      linarith
    have hzμ := hz μ
    simp only [Set.mem_Icc] at hzμ
    refine ⟨z, ⟨z μ - c μ + (S.side : ℝ) / 2, by linarith, by linarith, ?_⟩, rfl⟩
    funext ν
    by_cases hνμ : ν = μ
    · subst hνμ
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordVec, Pi.single_eq_same,
        hμ]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordVec,
        Pi.single_eq_of_ne hνμ]
      rw [hzν ν hνμ]
      ring
theorem cubeVertexEdgeAgreement_holds (h : CubeLifts.Statement) :
    CubeVertexEdgeAgreement := by
  intro S Δ _
  obtain ⟨-, -, hS⟩ := h
  obtain ⟨hT, -, hSites, -, -, -⟩ := hS S
  obtain ⟨-, hMs, -, -, -, hSide, hLift, -, -, hn2, -⟩ := hT
  have hL : S.params.L ≠ 0 := by
    have := S.params.isAdmissible.2
    omega
  have hLr : (0 : ℝ) < (S.params.L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hL
  have hs0 : 0 < meshSize S.params.L (levelDepth S.params.K S.level) := zpow_pos hLr _
  have ha0 : 0 < meshSize S.params.L S.index := zpow_pos hLr _
  have hone : (S.params.L : ℝ) ^ levelDepth S.params.K S.level *
      meshSize S.params.L (levelDepth S.params.K S.level) = 1 := by
    simp only [meshSize]
    rw [← zpow_add₀ hLr.ne']
    simp
  have hS2 : torusSide S.params.L S.params.m * (S.params.L : ℝ) ^ levelDepth S.params.K S.level =
      (S.cubeCount : ℝ) * (S.side : ℝ) := hSide
  have hside : torusSide S.params.L S.params.m =
      (S.cubeCount : ℝ) * meshSize S.params.L S.index := by
    calc torusSide S.params.L S.params.m
        = torusSide S.params.L S.params.m * (S.params.L : ℝ) ^ levelDepth S.params.K S.level *
            meshSize S.params.L (levelDepth S.params.K S.level) := by rw [mul_assoc, hone, mul_one]
      _ = (S.cubeCount : ℝ) * (S.side : ℝ) *
            meshSize S.params.L (levelDepth S.params.K S.level) := by rw [hS2]
      _ = (S.cubeCount : ℝ) * meshSize S.params.L S.index := by rw [mul_assoc, hMs]
  have hN : (2 : ℝ) ≤ (S.cubeCount : ℝ) := by exact_mod_cast hn2
  have hscale : ∀ (ε : Fin 4 → ℝ) (ν : Fin 4),
      meshSize S.params.L (levelDepth S.params.K S.level) * (((S.side : ℝ) / 2) • ε) ν =
        ε ν * meshSize S.params.L S.index / 2 := by
    intro ε ν
    rw [← hMs]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨fun v => ⟨?_, ?_⟩, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hΔ, ε, hε, hv⟩
    obtain ⟨c, hc⟩ := hLift (y : S.Points)
    refine ⟨y, hΔ, c, hc, ε, hε, ?_⟩
    funext ν
    rw [proj_add_of_isPointLift S hL hc, hv ν, hscale]
  · rintro ⟨y, hΔ, c, hc, ε, hε, rfl⟩
    exact ⟨y, hΔ, ε, hε, fun ν => by rw [proj_add_of_isPointLift S hL hc, hscale]⟩
  · rintro ⟨y, rfl, μ, ε, hε, rfl⟩
    obtain ⟨c, hc⟩ := hLift (y : S.Points)
    have hsign : ∀ ν, Function.update ε μ (-1) ν = 1 ∨ Function.update ε μ (-1) ν = -1 := by
      intro ν
      by_cases hνμ : ν = μ
      · subst hνμ
        simp
      · simpa [Function.update_of_ne hνμ] using hε ν
    refine ⟨y, rfl, c, hc, Function.update ε μ (-1), μ, hsign, by simp, ?_⟩
    rw [edgeAt_eq_setOf S hL rfl hs0 hMs rfl ha0 hside hN hc (hSites.2.1 y c hc) hsign (by simp)]
    ext x
    refine and_congr_right fun _ => forall_congr' fun ν => imp_congr_right fun hν => ?_
    rw [Function.update_of_ne hν]
  · rintro ⟨y, rfl, c, hc, ε, ν, hε, hν, rfl⟩
    exact ⟨y, rfl, ν, ε, hε,
      edgeAt_eq_setOf S hL rfl hs0 hMs rfl ha0 hside hN hc (hSites.2.1 y c hc) hε hν⟩
end YangMills.Construction.PeriodicLattice.CubeAgreement
end
