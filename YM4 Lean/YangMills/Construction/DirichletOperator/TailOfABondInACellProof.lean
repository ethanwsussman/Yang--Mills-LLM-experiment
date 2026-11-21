import YangMills.Construction.Dirichlet.CutoffDifferenceBoundsProof
import YangMills.Construction.DirichletOperator.TailOfABondInACell
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
namespace YangMills.Construction.PartitionCubes.SourceInCell
variable {d : ℕ} {S : ℝ}
theorem supNorm_le_norm_of_proj {p : PeriodicTorus d S} {v : Fin d → ℝ} (h : torusProj d S v = p) :
    supNorm p ≤ ‖v‖ :=
  csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg w⟩ ⟨v, h, rfl⟩
theorem torusProj_surjective : Function.Surjective (torusProj d S) := by apply _root_.YangMills.Construction.Dirichlet.CoverCountProof.torusProj_surjective <;> assumption
theorem exists_lift_norm_lt {p : PeriodicTorus d S} {r : ℝ} (h : supNorm p < r) :
    ∃ v : Fin d → ℝ, torusProj d S v = p ∧ ‖v‖ < r := by
  obtain ⟨v, hv⟩ := torusProj_surjective p
  obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt
    (s := {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = ‖v‖}) ⟨_, v, hv, rfl⟩ h
  exact ⟨w, hw, hlt⟩
theorem torusProj_sub (v w : Fin d → ℝ) :
    torusProj d S (v - w) = torusProj d S v - torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.CutoffDifferences.torusProj_sub <;> assumption
theorem lift_eq_zero_of_mem_lattice {ξ : ℝ} (hξ : 0 < ξ) {j : ℤ} (hS : S = (j : ℝ) * ξ)
    {p : PeriodicTorus d S} (hp : p ∈ spacingLattice d S ξ) {v : Fin d → ℝ}
    (hv : torusProj d S v = p) (hn : ‖v‖ < ξ) : v = 0 := by
  obtain ⟨k, rfl⟩ := hp
  funext μ
  have h0 : ((v μ - (k μ : ℝ) * ξ : ℝ) : AddCircle S) = 0 := by
    have h := congrFun hv μ
    simp only [torusProj] at h
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn'⟩ := (AddCircle.coe_eq_zero_iff S).1 h0
  have hv' : v μ = ((k μ + n * j : ℤ) : ℝ) * ξ := by
    have h : v μ = n • S + (k μ : ℝ) * ξ := by rw [hn']; ring
    rw [h, zsmul_eq_mul, hS]
    push_cast
    ring
  have habs : |v μ| < ξ := lt_of_le_of_lt (norm_le_pi_norm v μ) hn
  rw [hv', abs_mul, abs_of_pos hξ] at habs
  have h1 : |((k μ + n * j : ℤ) : ℝ)| < 1 := by
    by_contra hge
    nlinarith [not_lt.1 hge]
  have h2 : k μ + n * j = 0 := by
    rw [← Int.cast_abs] at h1
    have h3 : |k μ + n * j| < 1 := by exact_mod_cast h1
    exact Int.abs_lt_one_iff.1 h3
  rw [hv', h2]
  simp
theorem statement_holds : Statement := by
  intro 𝒮 K m M R₁ _ b _ y hy hin
  have hξ := 𝒮.ξ_pos
  have hL : (13 : ℝ) ≤ (𝒮.L : ℝ) := by exact_mod_cast 𝒮.thirteen_le_L
  obtain ⟨n, -, hyn⟩ := hy
  have hmem : shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y ∈ {n | y ∈ shellSites 𝒮.L 𝒮.ξ 𝒮.Ω n} :=
    Nat.sInf_mem ⟨n, hyn⟩
  have hσdef : shellSpacing 𝒮.L 𝒮.ξ 𝒮.Ω y =
      (𝒮.L : ℝ) ^ ((shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y : ℕ) : ℤ) * 𝒮.ξ := rfl
  have hσ : 𝒮.ξ ≤ shellSpacing 𝒮.L 𝒮.ξ 𝒮.Ω y := by
    rw [hσdef, zpow_natCast]
    have : (1 : ℝ) ≤ (𝒮.L : ℝ) ^ shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y := one_le_pow₀ (by linarith)
    nlinarith
  change supNorm ((b.source : 𝒮.Point) - y) ≤ 2 * shellSpacing 𝒮.L 𝒮.ξ 𝒮.Ω y / 2
  have hin' : supNorm ((𝒮.anchor b : 𝒮.Point) - y) ≤ shellSpacing 𝒮.L 𝒮.ξ 𝒮.Ω y / 2 := hin
  by_cases hc : (b.source : 𝒮.Point) ∉ 𝒮.Ω 0 ∧ (b.target : 𝒮.Point) ∈ 𝒮.Ω 0
  swap
  · have hbase : 𝒮.anchor b = b.source := if_neg hc
    rw [hbase] at hin'
    linarith
  have hbase : 𝒮.anchor b = b.target := if_pos hc
  rw [hbase] at hin'
  have hhead : (b.target : 𝒮.Point) =
      (b.source : 𝒮.Point) + torusProj 4 𝒮.side (Pi.single b.dir 𝒮.ξ) := rfl
  have hlift : ∀ v : Fin 4 → ℝ, torusProj 4 𝒮.side v = (b.target : 𝒮.Point) - y →
      torusProj 4 𝒮.side (v - Pi.single b.dir 𝒮.ξ) = (b.source : 𝒮.Point) - y := by
    intro v hv
    rw [torusProj_sub, hv, hhead]
    abel
  have hsingle : ‖(Pi.single b.dir 𝒮.ξ : Fin 4 → ℝ)‖ = 𝒮.ξ := by
    rw [Pi.norm_single, Real.norm_eq_abs, abs_of_pos hξ]
  rcases Nat.eq_zero_or_pos (shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y) with h0 | hpos
  · have hσ0 : shellSpacing 𝒮.L 𝒮.ξ 𝒮.Ω y = 𝒮.ξ := by
      rw [hσdef, h0]
      simp
    rw [hσ0] at hin'
    obtain ⟨v, hv, hvn⟩ := exists_lift_norm_lt (lt_of_le_of_lt hin' (half_lt_self hξ))
    have hylat : y ∈ spacingLattice 4 𝒮.side 𝒮.ξ := by
      have h := hmem.2.1
      rw [h0] at h
      have hs : scaleSpacing 𝒮.L 𝒮.ξ ((0 : ℕ) : ℤ) = 𝒮.ξ := by simp [scaleSpacing]
      rwa [hs] at h
    have hdiff : (b.target : 𝒮.Point) - y ∈ spacingLattice 4 𝒮.side 𝒮.ξ :=
      (spacingLattice 4 𝒮.side 𝒮.ξ).sub_mem b.target.2 hylat
    obtain ⟨k, hk⟩ := 𝒮.side_mem_zmultiples
    have hS : 𝒮.side = ((k * 2 * (𝒮.L : ℤ) ^ 𝒮.s : ℤ) : ℝ) * 𝒮.ξ := by
      rw [hk, scaleSpacing, zpow_natCast]
      push_cast
      ring
    have hv0 : v = 0 := lift_eq_zero_of_mem_lattice hξ hS hdiff hv hvn
    have hle := supNorm_le_norm_of_proj (hlift v hv)
    rw [hv0, zero_sub, norm_neg, hsingle] at hle
    linarith
  · have h2 : 2 * 𝒮.ξ ≤ shellSpacing 𝒮.L 𝒮.ξ 𝒮.Ω y := by
      rw [hσdef, zpow_natCast]
      have : (𝒮.L : ℝ) ≤ (𝒮.L : ℝ) ^ shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y :=
        le_self_pow₀ (by linarith) hpos.ne'
      nlinarith
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨v, hv, hvn⟩ := exists_lift_norm_lt
      (lt_of_le_of_lt hin' (lt_add_of_pos_right _ hε))
    have hle := supNorm_le_norm_of_proj (hlift v hv)
    have htri := norm_sub_le v (Pi.single b.dir 𝒮.ξ : Fin 4 → ℝ)
    rw [hsingle] at htri
    linarith
end YangMills.Construction.PartitionCubes.SourceInCell
