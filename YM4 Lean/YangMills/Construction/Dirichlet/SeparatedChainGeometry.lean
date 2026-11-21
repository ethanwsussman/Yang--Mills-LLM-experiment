import YangMills.Construction.Dirichlet.CutoffDifferenceBoundsProof
import YangMills.Construction.Dirichlet.GreenBoundsOnRegionsProof
import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Dirichlet.Geometry
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
section ProjectionLemmas
variable {d : ℕ} {S : ℝ}
theorem torusProj_add (v w : Fin d → ℝ) :
    torusProj d S (v + w) = torusProj d S v + torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.Commutator.torusProj_add <;> assumption
theorem torusProj_sub (v w : Fin d → ℝ) :
    torusProj d S (v - w) = torusProj d S v - torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.CutoffDifferences.torusProj_sub <;> assumption
theorem torusProj_neg (v : Fin d → ℝ) : torusProj d S (-v) = -torusProj d S v := by apply _root_.YangMills.Construction.Dirichlet.Commutator.torusProj_neg <;> assumption
theorem torusProj_zero : torusProj d S (0 : Fin d → ℝ) = 0 := by
  funext μ; simp [torusProj]
theorem exists_torusProj_eq_norm_eq_supNorm (p : PeriodicTorus d S) :
    ∃ v : Fin d → ℝ, torusProj d S v = p ∧ ‖v‖ = supNorm p := by
  choose b hb hb' using fun μ => TorusMetric.exists_coe_eq_abs_eq_norm (p μ)
  have hproj : torusProj d S b = p := funext hb
  refine ⟨b, hproj, le_antisymm ?_ ?_⟩
  · refine le_csInf ⟨_, b, hproj, rfl⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ => ?_
    have hpv : p μ = (v μ : AddCircle S) := by rw [← hv]; rfl
    rw [Real.norm_eq_abs, hb', hpv]
    exact (TorusMetric.addCircle_norm_coe_le_abs _).trans (by simpa using norm_le_pi_norm v μ)
  · exact csInf_le ⟨0, by rintro _ ⟨v, -, rfl⟩; exact norm_nonneg _⟩ ⟨b, hproj, rfl⟩
theorem supNorm_torusProj_le (v : Fin d → ℝ) : supNorm (torusProj d S v) ≤ ‖v‖ :=
  csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg _⟩ ⟨v, rfl, rfl⟩
theorem supNorm_nonneg (p : PeriodicTorus d S) : 0 ≤ supNorm p := by apply _root_.YangMills.Construction.Dirichlet.CutoffDifferences.supNorm_nonneg <;> assumption
theorem supNorm_zero : supNorm (0 : PeriodicTorus d S) = 0 := by
  refine le_antisymm ?_ (supNorm_nonneg _)
  have h := supNorm_torusProj_le (d := d) (S := S) 0
  rwa [torusProj_zero, norm_zero] at h
theorem supNorm_sub_comm (p q : PeriodicTorus d S) : supNorm (p - q) = supNorm (q - p) := by apply _root_.YangMills.Construction.Dirichlet.Commutator.supNorm_sub_comm <;> assumption
theorem supSetDist_le {A B : Set (PeriodicTorus d S)} {p q : PeriodicTorus d S} (hp : p ∈ A)
    (hq : q ∈ B) : supSetDist A B ≤ ENNReal.ofReal (supNorm (p - q)) :=
  iInf₂_le_of_le p hp (iInf₂_le q hq)
end ProjectionLemmas
section ScaleLemmas
variable {L : ℕ} {ξ : ℝ}
theorem scaleSpacing_pos (hL : 0 < L) (hξ : 0 < ξ) (n : ℤ) : 0 < scaleSpacing L ξ n :=
  mul_pos (zpow_pos (by exact_mod_cast hL) n) hξ
theorem scaleSpacing_mono (hL : 0 < L) (hξ : 0 < ξ) {m n : ℤ} (h : m ≤ n) :
    scaleSpacing L ξ m ≤ scaleSpacing L ξ n :=
  mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ (by exact_mod_cast hL) h) hξ.le
theorem scaleSpacing_zero : scaleSpacing L ξ 0 = ξ := by simp [scaleSpacing]
theorem scaleSpacing_injective (hL : 1 < L) (hξ : 0 < ξ) {m n : ℤ}
    (h : scaleSpacing L ξ m = scaleSpacing L ξ n) : m = n := by
  have hL' : (1 : ℝ) < L := by exact_mod_cast hL
  have h' : (L : ℝ) ^ m = (L : ℝ) ^ n := mul_right_cancel₀ hξ.ne' h
  exact zpow_right_injective₀ (by linarith) hL'.ne' h'
end ScaleLemmas
section InSetting
variable {d L : ℕ} {S aMinus aPlus : ℝ}
structure GeometryInputs (𝒮 : BlockSetting d L aMinus aPlus S) : Prop where
  params : Parameters d L aMinus aPlus
  proj : ProjectionFacts d S
  sides : ChainSideFacts d L 𝒮.ξ S 𝒮.M 𝒮.Ω
  members : ChainMemberFacts L 𝒮.ξ 𝒮.M 𝒮.t 𝒮.Ω
  shells : ∀ n ≤ lastNonemptyIndex 𝒮.Ω, ShellCubeFacts L 𝒮.ξ 𝒮.M 𝒮.t 𝒮.Ω n
  places : SiteLocationFacts L 𝒮.ξ 𝒮.t 𝒮.Ω
  cubeSites : ∀ n ≤ lastNonemptyIndex 𝒮.Ω, ∀ y ∈ shellSites L 𝒮.ξ 𝒮.Ω n, ∀ z : Fin d → ℝ,
    torusProj d S z = y → CubeSiteFacts L 𝒮.ξ 𝒮.Ω y z
  bounds : WeightedLength.Bounds 𝒮
theorem nestedPartitionFacts_self {ξ σ : ℝ} (h : ScaleSideFacts d L ξ S σ) :
    NestedPartitionFacts d L ξ S σ σ := by
  obtain ⟨i, hi, -, hpf⟩ := h
  have h' := hpf i le_rfl
  rwa [← hi] at h'
theorem cubeComplement_eq_closure_compl {ξ σ : ℝ} (h : ScaleSideFacts d L ξ S σ)
    {Y : Set (PeriodicTorus d S)} (hY : IsCubeUnion σ Y) : cubeComplement σ Y = closure Yᶜ := by
  have hpf := nestedPartitionFacts_self h
  obtain ⟨i, hi, ⟨k, hk, hk'⟩, -⟩ := h
  refine hpf.cubeComplement_eq_closure Y hY σ ⟨i, hi, ⟨2 * k, by omega, ?_⟩⟩ hY
  rw [hk']
  push_cast
  ring
variable {𝒮 : BlockSetting d L aMinus aPlus S}
theorem bddAbove_nonempty (𝒮 : BlockSetting d L aMinus aPlus S) :
    BddAbove {n | (𝒮.Ω n).Nonempty} := by
  refine ⟨𝒮.t, fun n hn => ?_⟩
  by_contra h
  have hn' : (𝒮.Ω n).Nonempty := hn
  rw [𝒮.isSeparatedChain.eq_empty_of_lt n (not_le.1 h)] at hn'
  exact Set.not_nonempty_empty hn'
theorem le_lastNonemptyIndex {n : ℕ} (h : (𝒮.Ω n).Nonempty) : n ≤ lastNonemptyIndex 𝒮.Ω :=
  le_csSup (bddAbove_nonempty 𝒮) h
theorem lastNonemptyIndex_le (𝒮 : BlockSetting d L aMinus aPlus S) :
    lastNonemptyIndex 𝒮.Ω ≤ 𝒮.t := by apply _root_.YangMills.Construction.Dirichlet.CoverCountProof.lastNonemptyIndex_le_t <;> assumption
theorem domain_antitone {n m : ℕ} (h : n ≤ m) : 𝒮.Ω m ⊆ 𝒮.Ω n := by apply _root_.YangMills.Construction.Dirichlet.CoverCountProof.domain_antitone <;> assumption
variable (F : GeometryInputs 𝒮)
include F
theorem blockFactor_pos : 0 < L := by
  have := F.params.three_le_blockFactor
  omega
theorem one_lt_blockFactor : 1 < L := by
  have := F.params.three_le_blockFactor
  omega
theorem scaleSpacing_pos_of (n : ℤ) : 0 < scaleSpacing L 𝒮.ξ n :=
  scaleSpacing_pos (blockFactor_pos F) 𝒮.isSeparatedChain.scale_pos n
theorem shell_subset_domain {n : ℕ} (hn : n ≤ lastNonemptyIndex 𝒮.Ω) : shell 𝒮.Ω n ⊆ 𝒮.Ω n :=
  fun _ hx => (F.members.shell_subset n hn hx).1
theorem shell_subset_domain_zero {n : ℕ} (hn : n ≤ lastNonemptyIndex 𝒮.Ω) :
    shell 𝒮.Ω n ⊆ 𝒮.Ω 0 :=
  (shell_subset_domain F hn).trans (domain_antitone (Nat.zero_le n))
theorem spacingLattice_le_base {n : ℕ} (hn : n ≤ lastNonemptyIndex 𝒮.Ω) :
    spacingLattice d S (scaleSpacing L 𝒮.ξ n) ≤ spacingLattice d S 𝒮.ξ := by
  obtain ⟨i, hi, -, hpf⟩ := F.sides.spacing_side n hn
  have hin : (n : ℤ) = i :=
    scaleSpacing_injective (one_lt_blockFactor F) 𝒮.isSeparatedChain.scale_pos hi
  have h0 : (0 : ℤ) ≤ i := by omega
  have h := hpf 0 h0
  have h' := h.spacingLattice_le
  rwa [scaleSpacing_zero] at h'
theorem exists_side_eq_mul : ∃ c : ℤ, S = c * 𝒮.ξ := by
  obtain ⟨i, -, ⟨k, -, hk'⟩, -⟩ := F.sides.spacing_side 0 (Nat.zero_le _)
  have h0 : scaleSpacing L 𝒮.ξ ((0 : ℕ) : ℤ) = 𝒮.ξ := by simp [scaleSpacing]
  rw [h0, div_eq_iff 𝒮.isSeparatedChain.scale_pos.ne'] at hk'
  exact ⟨2 * k, by push_cast; linarith⟩
theorem shell_index_unique {x : PeriodicTorus d S} (hx : x ∈ spacingLattice d S 𝒮.ξ) {n m : ℕ}
    (hn : n ≤ 𝒮.t) (hm : m ≤ 𝒮.t) (h₁ : x ∈ shell 𝒮.Ω n) (h₂ : x ∈ shell 𝒮.Ω m)
    (h0 : x ∈ 𝒮.Ω 0) : n = m := by
  obtain ⟨y, ⟨k, -, hyk⟩, -, -, -, hl⟩ := F.places.exists_of_mem x hx h0
  have hy := hl k hyk
  by_contra hne
  by_cases hnk : n = k
  · exact hy.2 m hm (by omega) h₂
  · exact hy.2 n hn hnk h₁
theorem shellIndex_eq {n : ℕ} {y : PeriodicTorus d S} (hy : y ∈ shellSites L 𝒮.ξ 𝒮.Ω n) :
    shellIndex L 𝒮.ξ 𝒮.Ω y = n := by
  have hmem : y ∈ shellSites L 𝒮.ξ 𝒮.Ω (shellIndex L 𝒮.ξ 𝒮.Ω y) :=
    Nat.sInf_mem (s := {k | y ∈ shellSites L 𝒮.ξ 𝒮.Ω k}) ⟨n, hy⟩
  obtain ⟨a₁, -, a₃⟩ := hmem
  obtain ⟨b₁, b₂, b₃⟩ := hy
  exact shell_index_unique F (spacingLattice_le_base F b₁ b₂) (a₁.trans (lastNonemptyIndex_le 𝒮))
    (b₁.trans (lastNonemptyIndex_le 𝒮)) a₃ b₃ (shell_subset_domain_zero F b₁ b₃)
theorem chainWeightedLength_nonneg (Γ : List (TorusSegment d)) :
    0 ≤ chainWeightedLength L 𝒮.ξ 𝒮.t 𝒮.Ω Γ := by
  have hlen : ∀ X : Set (PeriodicTorus d S), 0 ≤ lengthWithin Γ X := by
    intro X
    refine List.sum_nonneg fun r hr => ?_
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hr
    exact mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) ENNReal.toReal_nonneg
  refine add_nonneg (Finset.sum_nonneg fun n _ => ?_) ?_
  · exact mul_nonneg (inv_nonneg.2 (scaleSpacing_pos_of F _).le) (hlen _)
  · exact mul_nonneg (inv_nonneg.2 (scaleSpacing_pos_of F _).le) (hlen _)
theorem blockDist_self_nonpos (y : PeriodicTorus d S) : 𝒮.blockDist y y ≤ 0 := by
  obtain ⟨v, hv, -⟩ := exists_torusProj_eq_norm_eq_supNorm y
  have hpt : ∀ τ : ℝ, (⟨v, 0⟩ : TorusSegment d).pointAt S τ = y := by
    intro τ
    simp [TorusSegment.pointAt, hv]
  have hsupp : segmentUnion S [(⟨v, 0⟩ : TorusSegment d)] = {y} := by
    ext p
    constructor
    · rintro ⟨s', hs', τ, -, rfl⟩
      rw [List.mem_singleton] at hs'
      subst hs'
      exact hpt τ
    · rintro rfl
      exact ⟨_, List.mem_singleton.2 rfl, 0, by simp, (hpt 0).symm⟩
  have hlen : chainWeightedLength L 𝒮.ξ 𝒮.t 𝒮.Ω [(⟨v, 0⟩ : TorusSegment d)] = 0 := by
    simp [chainWeightedLength, lengthWithin, TorusSegment.lOneLength]
  unfold BlockSetting.blockDist chainWeightedDist
  refine csInf_le ⟨0, ?_⟩ ⟨[(⟨v, 0⟩ : TorusSegment d)], ?_, ?_, ?_, hlen.symm⟩
  · rintro _ ⟨Γ, -, -, -, rfl⟩
    exact chainWeightedLength_nonneg F Γ
  · rw [hsupp]; exact isConnected_singleton
  · rw [hsupp]; rfl
  · rw [hsupp]; rfl
section CollarLemmas
variable {n : ℕ} {y : PeriodicTorus d S}
end CollarLemmas
omit F in
theorem eq_of_torusProj_eq (hS : 0 < S) {a b : Fin d → ℝ} (h : torusProj d S a = torusProj d S b)
    (hlt : ∀ μ, |a μ - b μ| < S) : a = b := by
  funext μ
  have h₁ : (a μ : AddCircle S) = (b μ : AddCircle S) := congrFun h μ
  have h₀ : ((a μ - b μ : ℝ) : AddCircle S) = 0 := by rw [AddCircle.coe_sub, h₁, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at h₀
  obtain ⟨n, hn⟩ := h₀
  have hlt' := hlt μ
  rw [← hn, zsmul_eq_mul, abs_mul, abs_of_pos hS] at hlt'
  have h1 : |(n : ℝ)| < 1 := lt_of_mul_lt_mul_right (by simpa using hlt') hS.le
  have hn0 : n = 0 := by
    have h2 : |n| < 1 := by exact_mod_cast h1
    exact Int.abs_lt_one_iff.1 h2
  subst hn0
  simp at hn
  linarith
section LiftedLemmas
variable {n : ℕ} {y : PeriodicTorus d S}
end LiftedLemmas
end InSetting
end YangMills.Construction.Dirichlet.Geometry
