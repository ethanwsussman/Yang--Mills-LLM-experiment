import YangMills.Construction.Torus.EndPointsOfTheExpansionsAreNearProof
import YangMills.Construction.Towers.IsometriesOfATowerAreHypercubicMotionsProof
import YangMills.Construction.Towers.LatticesOfATowerAreNestedAndCounted
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.SublatticesNestedAndCounted
open YangMills.Construction.TorusMetric (torusProj)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
theorem latticeSubgroup_meshAt_le {L : ℕ} (hL : 0 < L) (k : ℕ) {i j : ℕ} (h : i ≤ j) :
    InfiniteLattice.latticeSubgroup (meshAt L k j) ≤ InfiniteLattice.latticeSubgroup (meshAt L k i) := by apply _root_.YangMills.Construction.Tower.HypercubicMotions.latticeSubgroup_le_of_le <;> assumption
theorem meshSize_eq_mul_succ {L : ℕ} (hL : 0 < L) (j : ℤ) :
    PeriodicLattice.meshSize L j = (L : ℝ) * PeriodicLattice.meshSize L (j + ((1 : ℕ) : ℤ)) := by
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hexp : -j = 1 + -(j + ((1 : ℕ) : ℤ)) := by push_cast; ring
  simp only [PeriodicLattice.meshSize]
  conv_lhs => rw [hexp, zpow_add₀ hLne, zpow_one]
theorem exists_lift_of_mem_unitBlock {L m : ℕ} {j : ℤ}
    (hb : PeriodicLattice.RefinedBlockCoordinates L m j 1)
    (y : PeriodicLattice.Site L m j) (A : AmbientSpace)
    (hA : torusProj (PeriodicLattice.torusSide L m) A = (y : PeriodicLattice.FourTorus L m))
    {x : PeriodicLattice.FourTorus L m} (hx : x ∈ PeriodicLattice.unitBlock y) :
    ∃ v : AmbientSpace, torusProj (PeriodicLattice.torusSide L m) (A + v) = x ∧
      ∀ μ, 2 * |v μ| ≤ ((L : ℝ) - 1) * PeriodicLattice.meshSize L (j + ((1 : ℕ) : ℤ)) := by
  obtain ⟨hmem, hset, -⟩ := hb y
  rw [PeriodicLattice.unitBlock, hset] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  have hmesh : 0 ≤ PeriodicLattice.meshSize L (j + ((1 : ℕ) : ℤ)) := by
    simp only [PeriodicLattice.meshSize]; positivity
  have hsub : ((y.toSublattice (j + ((1 : ℕ) : ℤ)) : PeriodicLattice.Site L m (j + ((1 : ℕ) : ℤ))) :
      PeriodicLattice.FourTorus L m) = y :=
    Classical.epsilon_spec
      (p := fun z : PeriodicLattice.Site L m (j + ((1 : ℕ) : ℤ)) =>
        (z : PeriodicLattice.FourTorus L m) = y) ⟨⟨y, hmem⟩, rfl⟩
  refine ⟨fun μ => (p μ : ℝ) * PeriodicLattice.meshSize L (j + ((1 : ℕ) : ℤ)), ?_, fun μ => ?_⟩
  · funext ν
    have hy := congrFun hA ν
    simp only [torusProj] at hy
    simp only [torusProj, PeriodicLattice.refinedOffsetSite, PeriodicLattice.offsetSite,
      AddSubgroup.coe_add, AddSubgroup.val_finsetSum, AddSubgroup.coe_zsmul, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, hsub]
    rw [← hy, AddCircle.coe_add]
    congr 1
    rw [Finset.sum_eq_single ν (fun μ _ h => by simp [Pi.single_eq_of_ne h.symm])
      (fun h => absurd (Finset.mem_univ ν) h), Pi.single_eq_same, ← zsmul_eq_mul]
    rfl
  · have h1 : (2 * |p μ| : ℤ) ≤ (L : ℤ) ^ 1 - 1 := hp μ
    have h2 : (2 * |(p μ : ℝ)|) ≤ (L : ℝ) - 1 := by
      have : ((2 * |p μ| : ℤ) : ℝ) ≤ (((L : ℤ) ^ 1 - 1 : ℤ) : ℝ) := by exact_mod_cast h1
      simpa using this
    rw [abs_mul, abs_of_nonneg hmesh, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h2 hmesh
theorem torusProj_add_single (S : ℝ) (A : AmbientSpace) (ν : Fin 4) (t : ℝ) :
    torusProj S (A + Pi.single ν t) = torusProj S A + Pi.single ν (t : AddCircle S) := by
  funext μ
  by_cases h : μ = ν
  · subst h
    simp [torusProj]
  · simp [torusProj, Pi.single_eq_of_ne h]
theorem abs_single_apply_le (ν μ : Fin 4) (t : ℝ) : |(Pi.single ν t : AmbientSpace) μ| ≤ |t| := by apply _root_.YangMills.Construction.GeneralTorus.EndpointsNear.abs_piSingle_apply_le <;> assumption
theorem exists_close_lifts_of_mem_bondDoubleBlock {L n : ℕ} (hL : 0 < L) {j : ℤ}
    (hb : PeriodicLattice.RefinedBlockCoordinates L n j 1) (c : PeriodicLattice.Bond L n j)
    {x x' : PeriodicLattice.FourTorus L n} (hx : x ∈ PeriodicLattice.bondDoubleBlock c)
    (hx' : x' ∈ PeriodicLattice.bondDoubleBlock c) :
    ∃ a b : AmbientSpace, torusProj (PeriodicLattice.torusSide L n) a = x ∧
      torusProj (PeriodicLattice.torusSide L n) b = x' ∧
      ∀ μ, |a μ - b μ| < 2 * (L : ℝ) * PeriodicLattice.meshSize L (j + ((1 : ℕ) : ℤ)) := by
  have hfine : 0 < PeriodicLattice.meshSize L (j + ((1 : ℕ) : ℤ)) := by
    simp only [PeriodicLattice.meshSize]; positivity
  have hcoarse := meshSize_eq_mul_succ hL j
  have hcnonneg : 0 ≤ PeriodicLattice.meshSize L j := by
    simp only [PeriodicLattice.meshSize]; positivity
  obtain ⟨N, hN⟩ := c.source.2
  let A : AmbientSpace := fun μ => (N μ : ℝ) * PeriodicLattice.meshSize L j
  have hA : torusProj (PeriodicLattice.torusSide L n) A = (c.source : PeriodicLattice.FourTorus L n) :=
    funext fun μ => (hN μ).symm
  obtain ⟨E, hE, hEb⟩ : ∃ E : AmbientSpace,
      torusProj (PeriodicLattice.torusSide L n) (A + E) = (c.target : PeriodicLattice.FourTorus L n) ∧
        ∀ μ, |E μ| ≤ PeriodicLattice.meshSize L j := by
    obtain ⟨ν, h | h⟩ := c.isNeighbour
    · refine ⟨Pi.single ν (PeriodicLattice.meshSize L j), ?_, fun μ => ?_⟩
      · have hh : (c.target : PeriodicLattice.FourTorus L n) =
            c.source + (PeriodicLattice.unitStep L n j ν : PeriodicLattice.FourTorus L n) := by
          rw [← h]; simp
        rw [torusProj_add_single, hA, hh]
        rfl
      · exact (abs_single_apply_le ν μ _).trans (abs_of_nonneg hcnonneg).le
    · refine ⟨Pi.single ν (-PeriodicLattice.meshSize L j), ?_, fun μ => ?_⟩
      · have hh : (c.target : PeriodicLattice.FourTorus L n) =
            c.source - (PeriodicLattice.unitStep L n j ν : PeriodicLattice.FourTorus L n) := by
          have h' : c.source - c.target = PeriodicLattice.unitStep L n j ν := by
            rw [← neg_sub, h, neg_neg]
          rw [← h']; simp
        rw [torusProj_add_single, hA, hh, AddCircle.coe_neg, Pi.single_neg, sub_eq_add_neg]
        rfl
      · exact (abs_single_apply_le ν μ _).trans (by rw [abs_neg, abs_of_nonneg hcnonneg])
  have choose : ∀ z ∈ PeriodicLattice.bondDoubleBlock c, ∃ w v : AmbientSpace,
      torusProj (PeriodicLattice.torusSide L n) (A + w + v) = z ∧ (∀ μ, w μ = 0 ∨ w μ = E μ) ∧
        ∀ μ, 2 * |v μ| ≤ ((L : ℝ) - 1) * PeriodicLattice.meshSize L (j + ((1 : ℕ) : ℤ)) := by
    rintro z (hz | hz)
    · obtain ⟨v, hv, hvb⟩ := exists_lift_of_mem_unitBlock hb c.source A hA hz
      exact ⟨0, v, by simpa using hv, fun _ => Or.inl rfl, hvb⟩
    · obtain ⟨v, hv, hvb⟩ := exists_lift_of_mem_unitBlock hb c.target (A + E) hE hz
      exact ⟨E, v, hv, fun _ => Or.inr rfl, hvb⟩
  obtain ⟨w, v, ha, hw, hv⟩ := choose x hx
  obtain ⟨w', v', ha', hw', hv'⟩ := choose x' hx'
  refine ⟨A + w + v, A + w' + v', ha, ha', fun μ => ?_⟩
  have hww : |w μ - w' μ| ≤ PeriodicLattice.meshSize L j := by
    rcases hw μ with h | h <;> rcases hw' μ with h' | h' <;> rw [h, h']
    · simpa using hcnonneg
    · simpa using hEb μ
    · simpa using hEb μ
    · simpa using hcnonneg
  have hvv : |v μ - v' μ| ≤ ((L : ℝ) - 1) * PeriodicLattice.meshSize L (j + ((1 : ℕ) : ℤ)) := by
    have := abs_sub (v μ) (v' μ)
    have h1 := hv μ
    have h2 := hv' μ
    linarith
  have heq : (A + w + v) μ - (A + w' + v') μ = (w μ - w' μ) + (v μ - v' μ) := by
    simp only [Pi.add_apply]; ring
  rw [heq]
  have := abs_add_le (w μ - w' μ) (v μ - v' μ)
  rw [hcoarse] at hww
  nlinarith
theorem holds (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hB : PeriodicLattice.CoordinateDescription) : Statement := by
  intro L hL hS k
  obtain ⟨hodd, h13⟩ := id hS
  refine ⟨fun i j hij _ => latticeSubgroup_meshAt_le hL k hij, fun n hn => ?_⟩
  have hcount : ∀ j ≤ k, ∀ (y : Vertex L n k j) (μ : Fin 4),
      (PeriodicLattice.axisLine y μ).ncard =
        QuotientLattices.sitesPerAxis L n k j := by
    intro j hj y μ
    obtain ⟨-, hq, -⟩ := hA L hS n j k hn hj
    obtain ⟨-, -, -, -, -, -, -, -, -, hc, -⟩ := hq
    exact hc y μ
  unfold SublatticeCounts
  refine ⟨fun i j hij hjk => PeriodicLattice.sublattice_mono hL n
      (by simp only [PeriodicLattice.levelDepth]; omega),
    hcount, fun i hi y μ => ?_, fun i hi c x hx x' hx' => ?_⟩
  · rw [hcount i hi.le y μ, QuotientLattices.sitesPerAxis]
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hL (by omega))
  · have hb := (hB L n hodd h13 hn).2.2.1 (PeriodicLattice.levelDepth k (i + 1)) 1
      (by simp only [PeriodicLattice.levelDepth]; push_cast; omega)
    obtain ⟨a, b, ha, hb', h⟩ := exists_close_lifts_of_mem_bondDoubleBlock hL hb c hx hx'
    refine ⟨a, b, ha, hb', fun μ => ?_⟩
    have hs : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k (i + 1) + ((1 : ℕ) : ℤ)) =
        meshAt L k i := by
      rw [← meshSize_levelDepth]
      congr 1
      simp only [PeriodicLattice.levelDepth]
      push_cast
      ring
    rw [← hs]
    exact h μ
end YangMills.Construction.Tower.SublatticesNestedAndCounted
end
