import YangMills.Construction.InfiniteLattice.CubicTorusOfACutoffIsAPeriodicExtensionProof
import YangMills.Construction.Lattice.CubesAndBlocksAtUnitSpacingProof
import YangMills.Construction.ReflectionPositivity.NestedLatticesLinkPositionsAndDensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.NestedRefinement
variable (s : Conventions.StandingParameters)
theorem one_lt_factor : (1 : ℝ) < (s.L : ℝ) := by apply _root_.YangMills.Construction.InfiniteLattice.CubicTorusAtCutoffLifts.one_lt_L <;> assumption
theorem meshAt_pos (k : ℕ+) : 0 < EveryCutoff.meshAt s k := by
  rw [EveryCutoff.meshAt_eq]
  exact zpow_pos (by linarith [one_lt_factor s]) _
theorem meshAt_eq_pow_mul {k k' : ℕ+} {e : ℕ} (hkk : (k' : ℕ) = (k : ℕ) + e) :
    EveryCutoff.meshAt s k = (s.L : ℝ) ^ e * EveryCutoff.meshAt s k' := by
  have hL : (s.L : ℝ) ≠ 0 := by linarith [one_lt_factor s]
  rw [EveryCutoff.meshAt_eq, EveryCutoff.meshAt_eq, hkk]
  push_cast
  rw [show -((k : ℤ) + (e : ℤ)) = -(k : ℤ) + -(e : ℤ) by ring, zpow_add₀ hL, zpow_neg (s.L : ℝ) (e : ℤ),
    zpow_natCast]
  field_simp
theorem mem_sublatticeAt_iff (k : ℕ+) (v : s.Torus) :
    v ∈ EveryCutoff.sublatticeAt s k ↔ ∃ n : Fin 4 → ℤ, ∀ μ,
      v μ = (((n μ : ℝ) * EveryCutoff.meshAt s k : ℝ) : AddCircle (PeriodicLattice.torusSide s.L s.m)) :=
  Iff.rfl
theorem sublatticeAt_subset {k k' : ℕ+} (hle : k ≤ k') :
    (EveryCutoff.sublatticeAt s k : Set s.Torus) ⊆ EveryCutoff.sublatticeAt s k' := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (PNat.coe_le_coe k k' |>.mpr hle)
  intro v hv
  obtain ⟨n, hn⟩ := (mem_sublatticeAt_iff s k v).mp hv
  refine (mem_sublatticeAt_iff s k' v).mpr ⟨fun μ => n μ * (s.L : ℤ) ^ e, fun μ => ?_⟩
  rw [hn μ, meshAt_eq_pow_mul s he]
  congr 1
  push_cast
  ring
theorem linkLevelsAt_subset {k k' : ℕ+} (hle : k ≤ k') :
    EveryCutoff.linkLevelsAt s k ⊆ EveryCutoff.linkLevelsAt s k' := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (PNat.coe_le_coe k k' |>.mpr hle)
  rintro c ⟨n, rfl⟩
  have hodd : Odd ((s.L : ℤ) ^ e * (2 * n + 1)) :=
    (Odd.pow (by exact_mod_cast s.isAdmissible.1)).mul (odd_two_mul_add_one n)
  obtain ⟨n', hn'⟩ := hodd
  have hreal : (s.L : ℝ) ^ e * (2 * (n : ℝ) + 1) = 2 * (n' : ℝ) + 1 := by exact_mod_cast hn'
  refine ⟨n', ?_⟩
  rw [meshAt_eq_pow_mul s he]
  have hhalf : (n' : ℝ) + 1 / 2 = (s.L : ℝ) ^ e * (2 * (n : ℝ) + 1) / 2 := by rw [hreal]; ring
  rw [hhalf]
  ring
theorem exists_meshAt_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ+, EveryCutoff.meshAt s k < ε := by
  have h1 := one_lt_factor s
  have hinv : (s.L : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hinv
  refine ⟨n.succPNat, ?_⟩
  have hpow : EveryCutoff.meshAt s n.succPNat = ((s.L : ℝ)⁻¹) ^ (n + 1) := by
    rw [EveryCutoff.meshAt_eq, Nat.succPNat_coe, zpow_neg, zpow_natCast, inv_pow]
  rw [hpow, pow_succ]
  have hnn : 0 ≤ ((s.L : ℝ)⁻¹) ^ n := by positivity
  have hmul : ((s.L : ℝ)⁻¹) ^ n * (s.L : ℝ)⁻¹ ≤ ((s.L : ℝ)⁻¹) ^ n * 1 :=
    mul_le_mul_of_nonneg_left hinv.le hnn
  linarith
theorem exists_near_multiple (a : ℝ) (ha : 0 < a) (y : ℝ) :
    ∃ z : ℤ, |y - (z : ℝ) * a| ≤ a / 2 := by apply _root_.YangMills.Construction.PeriodicLattice.UnitSpacingCubes.exists_int_mul_near <;> assumption
theorem unionOfSublattices_add_mem {x y : s.Torus} (hx : x ∈ EveryCutoff.unionOfSublattices s)
    (hy : y ∈ EveryCutoff.unionOfSublattices s) : x + y ∈ EveryCutoff.unionOfSublattices s := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  obtain ⟨k', hk'⟩ := Set.mem_iUnion.mp hy
  refine Set.mem_iUnion.mpr ⟨max k k', ?_⟩
  exact (EveryCutoff.sublatticeAt s (max k k')).add_mem (sublatticeAt_subset s (le_max_left k k') hk)
    (sublatticeAt_subset s (le_max_right k k') hk')
theorem unionIsAddSubgroup : UnionIsAddSubgroup s :=
  ⟨{ carrier := EveryCutoff.unionOfSublattices s
     add_mem' := unionOfSublattices_add_mem s
     zero_mem' := Set.mem_iUnion.mpr ⟨1, (EveryCutoff.sublatticeAt s 1).zero_mem⟩
     neg_mem' := by
      intro x hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨k, (EveryCutoff.sublatticeAt s k).neg_mem hk⟩ }, rfl⟩
theorem torusDist_le_of_lift {x y : s.Torus} (w : Fin 4 → ℝ)
    (hw : x - y = TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) w) :
    TorusCutoffs.torusDist x y ≤ TorusMetric.euclidNormVec w := by
  refine csInf_le ⟨0, ?_⟩ ⟨w, hw.symm, rfl⟩
  rintro _ ⟨v, _, rfl⟩
  exact Real.sqrt_nonneg _
theorem unionIsDense : UnionIsDense s := by
  intro x ε hε
  obtain ⟨k, hk⟩ := exists_meshAt_lt s hε
  have ha := meshAt_pos s k
  obtain ⟨y, hy⟩ := TorusCutoffs.exists_proj_eq s x
  choose z hz using fun μ => exists_near_multiple (EveryCutoff.meshAt s k) ha (y μ)
  let p : s.Torus := fun μ =>
    (((z μ : ℝ) * EveryCutoff.meshAt s k : ℝ) : AddCircle (PeriodicLattice.torusSide s.L s.m))
  have hp : p ∈ EveryCutoff.sublatticeAt s k := (mem_sublatticeAt_iff s k p).mpr ⟨z, fun _ => rfl⟩
  refine ⟨p, Set.mem_iUnion.mpr ⟨k, hp⟩, lt_of_le_of_lt ?_ hk⟩
  have hdiff : x - p = TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m)
      (fun μ => y μ - (z μ : ℝ) * EveryCutoff.meshAt s k) := by
    subst hy
    funext μ
    rfl
  refine (torusDist_le_of_lift s _ hdiff).trans ?_
  refine Real.sqrt_le_iff.mpr ⟨ha.le, ?_⟩
  have hsq : ∀ μ, (y μ - (z μ : ℝ) * EveryCutoff.meshAt s k) ^ 2 ≤
      (EveryCutoff.meshAt s k / 2) ^ 2 := fun μ =>
    sq_le_sq' (by linarith [(abs_le.mp (hz μ)).1]) (abs_le.mp (hz μ)).2
  rw [Fin.sum_univ_four]
  nlinarith [hsq 0, hsq 1, hsq 2, hsq 3]
theorem linkLevelsAreDense : LinkLevelsAreDense s := by
  refine Metric.dense_iff.mpr fun c r hr => ?_
  obtain ⟨k, hk⟩ := exists_meshAt_lt s hr
  have ha := meshAt_pos s k
  obtain ⟨z, hz⟩ := exists_near_multiple (EveryCutoff.meshAt s k) ha
    (c - EveryCutoff.meshAt s k / 2)
  refine ⟨EveryCutoff.meshAt s k * ((z : ℝ) + 1 / 2), ?_,
    Set.mem_iUnion.mpr ⟨k, z, rfl⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
  have he : c - EveryCutoff.meshAt s k * ((z : ℝ) + 1 / 2) =
      c - EveryCutoff.meshAt s k / 2 - (z : ℝ) * EveryCutoff.meshAt s k := by ring
  rw [he]
  linarith
theorem nestedAndDense : NestedAndDense := fun s =>
  ⟨⟨fun _ _ hle => ⟨sublatticeAt_subset s hle, linkLevelsAt_subset s hle⟩,
      fun _ _ hv _ hle => sublatticeAt_subset s hle hv,
      fun _ _ hc _ hle => linkLevelsAt_subset s hle hc⟩,
    ⟨unionIsAddSubgroup s, unionIsDense s⟩,
    linkLevelsAreDense s⟩
end YangMills.Construction.ReflectionPositivity.NestedRefinement
end
