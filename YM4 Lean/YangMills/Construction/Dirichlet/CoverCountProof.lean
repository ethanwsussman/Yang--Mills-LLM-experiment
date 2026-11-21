import YangMills.Construction.Dirichlet.CentresAndCellsProof
import YangMills.Construction.Dirichlet.CoverCubeCount
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus Dirichlet Dirichlet.CoverCount
namespace Dirichlet.CoverCountProof
variable {d L : ℕ} {S aLow aHigh : ℝ} (𝒮 : BlockSetting d L aLow aHigh S)
theorem domain_antitone {i j : ℕ} (hij : i ≤ j) : 𝒮.Ω j ⊆ 𝒮.Ω i := by
  induction j, hij using Nat.le_induction with
  | base => exact Subset.rfl
  | succ j _ ih =>
    refine Subset.trans ?_ ih
    by_cases hj : j < 𝒮.t
    · exact 𝒮.isSeparatedChain.succ_subset j hj
    · rw [𝒮.isSeparatedChain.eq_empty_of_lt (j + 1) (by omega)]
      exact empty_subset _
theorem lastNonemptyIndex_le_t : lastNonemptyIndex 𝒮.Ω ≤ 𝒮.t := by
  refine csSup_le ⟨0, 𝒮.isSeparatedChain.zero_nonempty⟩ ?_
  intro n hn
  by_contra hlt
  have hne : (𝒮.Ω n).Nonempty := hn
  rw [𝒮.isSeparatedChain.eq_empty_of_lt n (by omega)] at hne
  exact not_nonempty_empty hne
theorem cubeComplement_eq_closure_compl (sides : ChainSideFacts d L 𝒮.ξ S 𝒮.M 𝒮.Ω) {n : ℕ}
    (hn : n ≤ lastNonemptyIndex 𝒮.Ω) {Y : Set (PeriodicTorus d S)}
    (hY : IsCubeUnion ((𝒮.M : ℝ) * scaleSpacing L 𝒮.ξ n) Y) :
    cubeComplement ((𝒮.M : ℝ) * scaleSpacing L 𝒮.ξ n) Y = closure Yᶜ := by
  obtain ⟨i, hi, ⟨k, hk, hS⟩, hfacts⟩ := sides.block_side n hn
  have hside : IsAdmissibleSide L 𝒮.ξ S ((𝒮.M : ℝ) * scaleSpacing L 𝒮.ξ n) :=
    ⟨i, hi, 2 * k, by omega, by rw [hS]; push_cast; ring⟩
  have hf := hfacts i le_rfl
  rw [← hi] at hf
  exact hf.cubeComplement_eq_closure Y hY _ hside hY
theorem spacingLattice_finite {σ : ℝ} {K : ℕ} (hK : 0 < K) (hS : S = K * σ) :
    ((spacingLattice d S σ : AddSubgroup (PeriodicTorus d S)) : Set (PeriodicTorus d S)).Finite := by apply _root_.YangMills.Construction.Dirichlet.CentresCellsProof.spacingLattice_finite <;> assumption
theorem torusProj_surjective : Function.Surjective (torusProj d S) := by
  intro q
  choose v hv using fun μ => QuotientAddGroup.mk_surjective (q μ)
  exact ⟨v, funext hv⟩
def lowHalfIndex (σ u : ℝ) : ℤ := ⌊u / σ - 3 / 2⌋ + 1
theorem halfIndex_near_cases {σ u : ℝ} (hσ : 0 < σ) {j : ℤ}
    (h : |u - ((j : ℝ) + 1 / 2) * σ| < σ) :
    j = lowHalfIndex σ u ∨ j = lowHalfIndex σ u + 1 := by
  obtain ⟨h₁, h₂⟩ := abs_lt.mp h
  have hx : u = u / σ * σ := by field_simp
  set x := u / σ with hxdef
  have hfi : lowHalfIndex σ u = ⌊x - 3 / 2⌋ + 1 := rfl
  have hlow : x - 1 < (j : ℝ) + 1 / 2 := by
    by_contra hc
    have := mul_le_mul_of_nonneg_right (not_lt.1 hc) hσ.le
    nlinarith
  have hhigh : (j : ℝ) + 1 / 2 < x + 1 := by
    by_contra hc
    have := mul_le_mul_of_nonneg_right (not_lt.1 hc) hσ.le
    nlinarith
  have ha : lowHalfIndex σ u ≤ j := by
    have : ⌊x - 3 / 2⌋ < j := Int.floor_lt.2 (by linarith)
    omega
  have hb : j < lowHalfIndex σ u + 2 := by
    have h₃ : x - 3 / 2 < (⌊x - 3 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have : (j : ℝ) < ((⌊x - 3 / 2⌋ + 3 : ℤ) : ℝ) := by
      push_cast
      linarith
    have : j < ⌊x - 3 / 2⌋ + 3 := by exact_mod_cast this
    omega
  omega
theorem centre_of_supNorm_lt {σ : ℝ} (hσ : 0 < σ) {k : ℕ} (hS : S = 2 * k * σ)
    {c z p : PeriodicTorus d S} (hc : c ∈ spacingLattice d S σ) (hz : IsCubeVertex c σ z)
    {u : Fin d → ℝ} (hu : torusProj d S u = p) (hnear : supNorm (p - z) < σ) :
    ∃ b : Fin d → Bool, z = torusProj d S fun μ =>
      (((lowHalfIndex σ (u μ) + if b μ then 1 else 0 : ℤ) : ℝ) + 1 / 2) * σ := by
  obtain ⟨v₀, hv₀⟩ := torusProj_surjective (d := d) (S := S) (p - z)
  have hne : {r | ∃ v : Fin d → ℝ, torusProj d S v = p - z ∧ r = ‖v‖}.Nonempty :=
    ⟨‖v₀‖, v₀, hv₀, rfl⟩
  obtain ⟨r, ⟨v, hv, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne hnear
  have hz' : z = torusProj d S (u - v) := by
    have : z = p - (p - z) := by abel
    rw [this, ← hv, ← hu]
    funext μ
    simp [torusProj]
  obtain ⟨κ, rfl⟩ := hc
  obtain ⟨ε, hε, hzε⟩ := hz
  have hcoord : ∀ μ, ∃ j : ℤ, u μ - v μ = ((j : ℝ) + 1 / 2) * σ := by
    intro μ
    have hμ : ((u μ - v μ - ((κ μ : ℝ) * σ + ε μ * (σ / 2)) : ℝ) : AddCircle S) = 0 := by
      have h₁ := congrFun hz' μ
      rw [hzε] at h₁
      simp only [torusProj, Pi.add_apply, Pi.sub_apply] at h₁
      rw [AddCircle.coe_sub, AddCircle.coe_add, h₁, sub_self]
    obtain ⟨l, hl⟩ := (AddCircle.coe_eq_zero_iff S).1 hμ
    rw [zsmul_eq_mul, hS] at hl
    rcases hε μ with h | h
    · refine ⟨κ μ + 2 * k * l, ?_⟩
      rw [h] at hl
      push_cast
      linarith
    · refine ⟨κ μ + 2 * k * l - 1, ?_⟩
      rw [h] at hl
      push_cast
      linarith
  choose j hj using hcoord
  have hnear' : ∀ μ, j μ = lowHalfIndex σ (u μ) ∨ j μ = lowHalfIndex σ (u μ) + 1 := by
    intro μ
    refine halfIndex_near_cases hσ ?_
    rw [← hj μ]
    have : |v μ| ≤ ‖v‖ := norm_le_pi_norm v μ
    have h₂ : u μ - (u μ - v μ) = v μ := by ring
    rw [h₂]
    linarith
  refine ⟨fun μ => decide (j μ = lowHalfIndex σ (u μ) + 1), ?_⟩
  rw [hz']
  congr 1
  funext μ
  show u μ - v μ = _
  rw [hj μ]
  rcases hnear' μ with h | h
  · simp [h]
  · simp [h]
theorem encard_near_centres_le {m : ℕ} (hσ : 0 < 𝒮.blockWidth m) {k : ℕ}
    (hS : S = 2 * k * 𝒮.blockWidth m) (p : PeriodicTorus d S) :
    {Q | Q ∈ 𝒮.coverCubesAt m ∧ supNorm (p - Q.centre) < 𝒮.blockWidth m}.encard ≤
      (2 ^ d : ℕ∞) := by
  obtain ⟨u, hu⟩ := torusProj_surjective (d := d) (S := S) p
  let g : (Fin d → Bool) → CentredCube d S := fun b =>
    ⟨m, torusProj d S fun μ =>
      (((lowHalfIndex (𝒮.blockWidth m) (u μ) + if b μ then 1 else 0 : ℤ) : ℝ) + 1 / 2) *
        𝒮.blockWidth m⟩
  have hsub : {Q | Q ∈ 𝒮.coverCubesAt m ∧ supNorm (p - Q.centre) < 𝒮.blockWidth m} ⊆
      g '' univ := by
    rintro Q ⟨⟨hlev, -, c, hc, -, hz⟩, hnear⟩
    obtain ⟨b, hb⟩ := centre_of_supNorm_lt hσ hS hc hz hu hnear
    exact ⟨b, mem_univ _, CentredCube.ext hlev.symm hb.symm⟩
  calc _ ≤ (g '' univ).encard := encard_le_encard hsub
    _ ≤ (univ : Set (Fin d → Bool)).encard := encard_image_le g univ
    _ = (2 ^ d : ℕ∞) := by
      rw [encard_univ, ENat.card_eq_coe_fintype_card]
      simp
end Dirichlet.CoverCountProof
end YangMills.Construction
