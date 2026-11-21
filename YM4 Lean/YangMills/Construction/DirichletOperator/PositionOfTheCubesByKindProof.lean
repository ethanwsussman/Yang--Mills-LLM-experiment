import YangMills.Construction.RegionSequence.ShellDecomposition
import YangMills.Construction.DirichletOperator.CornerCubeInALayerOfASequenceProof
import YangMills.Construction.DirichletOperator.FunctionsNearACubeReadOnItsTorusProof
import YangMills.Construction.DirichletOperator.InequalitiesOnCubesOfTheFirstKindProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
open YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.PositionByType
theorem supNorm_eq_norm {S : ℝ} (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem supNorm_sub_le {S : ℝ} (p q r : PeriodicTorus 4 S) :
    supNorm (p - r) ≤ supNorm (p - q) + supNorm (q - r) := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.supNorm_sub_le <;> assumption
theorem supNorm_sub_comm {S : ℝ} (p q : PeriodicTorus 4 S) : supNorm (p - q) = supNorm (q - p) := by apply _root_.YangMills.Construction.PartitionCubes.TorusComponents.supNorm_sub_comm <;> assumption
theorem supSetDist_le {S : ℝ} {A B : Set (PeriodicTorus 4 S)} {p q : PeriodicTorus 4 S}
    (hp : p ∈ A) (hq : q ∈ B) :
    supSetDist A B ≤ ENNReal.ofReal (supNorm (p - q)) :=
  iInf₂_le_of_le p hp (iInf₂_le q hq)
theorem le_supSetDist {S r : ℝ} {A B : Set (PeriodicTorus 4 S)}
    (h : ∀ p ∈ A, ∀ q ∈ B, r ≤ supNorm (p - q)) : ENNReal.ofReal r ≤ supSetDist A B :=
  le_iInf₂ fun p hp => le_iInf₂ fun q hq => ENNReal.ofReal_le_ofReal (h p hp q hq)
theorem exists_mem_supNorm_lt {S t t' : ℝ} {C : Set (PeriodicTorus 4 S)} {x : PeriodicTorus 4 S}
    (h : supSetDist {x} C ≤ ENNReal.ofReal t) (ht : t < t') (ht' : 0 < t') :
    ∃ y ∈ C, supNorm (x - y) < t' := by
  have hlt : supSetDist {x} C < ENNReal.ofReal t' :=
    h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff ht').2 ht)
  simp only [supSetDist, iInf_singleton, iInf_lt_iff] at hlt
  obtain ⟨y, hy, hlt⟩ := hlt
  exact ⟨y, hy, (ENNReal.ofReal_lt_ofReal_iff ht').1 hlt⟩
variable {𝒮 : NestedRegions} {M : ℕ}
theorem le_s_of_Ω_nonempty {n : ℕ} (h : (𝒮.Ω n).Nonempty) : n ≤ 𝒮.s := by apply _root_.YangMills.Construction.PartitionCubes.CellsTransferProof.nested_le_s_of_nonempty <;> assumption
theorem le_topLevel_of_Ω_nonempty {n : ℕ} (h : (𝒮.Ω n).Nonempty) : n ≤ topLevel 𝒮 := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.le_lastNonemptyIndex <;> assumption
theorem Ω_subset_Ω_one {n : ℕ} (h₁ : 1 ≤ n) (h : n ≤ 𝒮.s) : 𝒮.Ω n ⊆ 𝒮.Ω 1 := by
  induction n, h₁ using Nat.le_induction with
  | base => exact subset_rfl
  | succ k hk ih => exact (𝒮.Ω_succ_subset k (by omega)).trans (ih (by omega))
theorem mem_Ω_of_distToOutside_pos {n : ℕ} {x : 𝒮.Point} (h : 0 < distToOutside 𝒮 n x) :
    x ∈ 𝒮.Ω n := by
  by_contra hx
  have hle : distToOutside 𝒮 n x ≤ ENNReal.ofReal (supNorm (x - x)) :=
    supSetDist_le (mem_singleton x) (subset_closure hx)
  rw [sub_self, supNorm_eq_norm, norm_zero, ENNReal.ofReal_zero] at hle
  exact absurd h (not_lt.2 hle)
theorem not_mem_closure_compl_of_lt_distToOutside {n : ℕ} {p p' : 𝒮.Point} {r : ℝ}
    (h : ENNReal.ofReal r < distToOutside 𝒮 n p) (hl : supNorm (p - p') ≤ r) :
    p' ∉ closure (𝒮.Ω n)ᶜ := by
  intro hp
  have hle : distToOutside 𝒮 n p ≤ ENNReal.ofReal (supNorm (p - p')) :=
    supSetDist_le (mem_singleton p) hp
  exact absurd (h.trans_le hle) (not_lt.2 (ENNReal.ofReal_le_ofReal hl))
theorem cubeSide_pos (hM : 𝒮.L ^ 5 ≤ M) (n : ℕ) : 0 < cubeSide 𝒮 M n := by
  have hL := 𝒮.thirteen_le_L
  have hM' : 0 < M := lt_of_lt_of_le (pow_pos (by omega) 5) hM
  have hLr : (0 : ℝ) < 𝒮.L := by exact_mod_cast (by omega : 0 < 𝒮.L)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM'
  rw [cubeSide, 𝒮.scale_eq_pow_mul]
  exact mul_pos hMr (mul_pos (pow_pos hLr n) 𝒮.ξ_pos)
theorem cubeSide_succ (n : ℕ) : cubeSide 𝒮 M (n + 1) = (𝒮.L : ℝ) * cubeSide 𝒮 M n := by apply _root_.YangMills.Construction.PartitionCubes.CornerShell.cubeSide_succ <;> assumption
theorem cubeSide_zero : cubeSide 𝒮 M 0 = (M : ℝ) * 𝒮.ξ := by
  simp [cubeSide, 𝒮.scale_eq_pow_mul]
theorem enlarge_three_subset_Ω {R₁ : ℕ} (hs : DistanceSeparation.Holds 𝒮 M R₁)
    (hM : 𝒮.L ^ 5 ≤ M) (Q : LevelCube 𝒮 M) (h : (Q.enlarge 2 ∩ 𝒮.Ω (Q.level + 1)).Nonempty) :
    Q.enlarge 3 ⊆ 𝒮.Ω Q.level := by
  obtain ⟨p, hp₂, hp⟩ := h
  have hB := cubeSide_pos hM Q.level
  have hR : (13 : ℝ) ≤ R₁ := by
    exact_mod_cast hs.thirteen_le_L.trans hs.L_le_gap
  have hns : Q.level < 𝒮.s := le_s_of_Ω_nonempty ⟨p, hp⟩
  have hd := hs.lt_distToOutside Q.level hns p hp
  intro p' hp'
  by_contra hn
  refine not_mem_closure_compl_of_lt_distToOutside hd ?_ (subset_closure hn)
  have h₁ : supNorm (p - Q.centre) ≤ (1 + ((2 : ℕ) : ℝ)) * cubeSide 𝒮 M Q.level := hp₂
  have h₂ : supNorm (p' - Q.centre) ≤ (1 + ((3 : ℕ) : ℝ)) * cubeSide 𝒮 M Q.level := hp'
  have h₃ := supNorm_sub_le p Q.centre p'
  rw [supNorm_sub_comm Q.centre p'] at h₃
  push_cast at h₁ h₂
  have h₄ : 13 * cubeSide 𝒮 M Q.level ≤ (R₁ : ℝ) * cubeSide 𝒮 M Q.level :=
    mul_le_mul_of_nonneg_right hR hB.le
  linarith
theorem twentySix_mul_cubeSide_le_side {K m R₁ : ℕ} (hSides : LevelCubeSides.Statement)
    (h𝒮 : 𝒮.IsLevelUnitChain K m M R₁) (hM : 𝒮.L ^ 5 ≤ M) (Q : LevelCube 𝒮 M)
    (h : (Q.enlarge 2 ∩ 𝒮.Ω (Q.level + 1)).Nonempty) :
    26 * cubeSide 𝒮 M Q.level ≤ 𝒮.side := by
  obtain ⟨p, -, hp⟩ := h
  have h₁ := (hSides 𝒮 K m M R₁ h𝒮 (Q.level + 1) (le_topLevel_of_Ω_nonempty ⟨p, hp⟩)).2.1
  rw [cubeSide_succ] at h₁
  have hB := cubeSide_pos hM Q.level
  have hL : (13 : ℝ) ≤ 𝒮.L := by exact_mod_cast 𝒮.thirteen_le_L
  have h₂ : 13 * cubeSide 𝒮 M Q.level ≤ (𝒮.L : ℝ) * cubeSide 𝒮 M Q.level :=
    mul_le_mul_of_nonneg_right hL hB.le
  linarith
theorem enlarge_three_inter_Ω_add_two {R₁ : ℕ} (hWhere : ∀ Q : LevelCube 𝒮 M, Q.supp ⊆
      {x | supNorm (x - Q.centre) < 2 / 3 * cubeSide 𝒮 M Q.level} ∩
        {x | Q.level ≠ 0 →
          ENNReal.ofReal (mollifyRadius 𝒮 M Q.level) ≤ distToOutside 𝒮 Q.level x} ∩
        {x | distToOutside 𝒮 (Q.level + 1) x ≤
          ENNReal.ofReal (2 * mollifyRadius 𝒮 M (Q.level + 1))})
    (hs : DistanceSeparation.Holds 𝒮 M R₁) (hM : 𝒮.L ^ 5 ≤ M) (Q : LevelCube 𝒮 M)
    (hQ : Q ∈ active 𝒮 M) : Q.enlarge 3 ∩ 𝒮.Ω (Q.level + 2) = ∅ := by
  obtain ⟨n, -, hn, b, -, hb⟩ := hQ
  have hx : (b.source : 𝒮.Point) ∈ Q.supp := subset_tsupport _ hb
  obtain ⟨⟨hx₁, -⟩, hx₂⟩ := hWhere Q hx
  have hB := cubeSide_pos hM Q.level
  have hL : (13 : ℝ) ≤ 𝒮.L := by exact_mod_cast 𝒮.thirteen_le_L
  have hR : (13 : ℝ) ≤ R₁ := by
    exact_mod_cast hs.thirteen_le_L.trans hs.L_le_gap
  have hx₃ : distToOutside 𝒮 (Q.level + 1) (b.source : 𝒮.Point) ≤
      ENNReal.ofReal (2 * mollifyRadius 𝒮 M (Q.level + 1)) := hx₂
  rw [hs.two_mul_mollifyRadius_succ] at hx₃
  obtain ⟨y, hy, hxy⟩ := exists_mem_supNorm_lt hx₃ (by linarith : cubeSide 𝒮 M Q.level / 3 <
    cubeSide 𝒮 M Q.level) hB
  rw [eq_empty_iff_forall_notMem]
  rintro q ⟨hq₃, hq⟩
  have hns : Q.level + 1 < 𝒮.s := le_s_of_Ω_nonempty ⟨q, hq⟩
  have hd := hs.lt_distToOutside (Q.level + 1) hns q hq
  refine not_mem_closure_compl_of_lt_distToOutside hd ?_ hy
  have h₂ : supNorm (q - Q.centre) ≤ (1 + ((3 : ℕ) : ℝ)) * cubeSide 𝒮 M Q.level := hq₃
  have h₃ := supNorm_sub_le q Q.centre y
  have h₄ := supNorm_sub_le Q.centre (b.source : 𝒮.Point) y
  rw [supNorm_sub_comm Q.centre (b.source : 𝒮.Point)] at h₄
  push_cast at h₂
  rw [cubeSide_succ]
  have hLB : 13 * cubeSide 𝒮 M Q.level ≤ (𝒮.L : ℝ) * cubeSide 𝒮 M Q.level :=
    mul_le_mul_of_nonneg_right hL hB.le
  have hRB : 13 * (13 * cubeSide 𝒮 M Q.level) ≤ (R₁ : ℝ) * ((𝒮.L : ℝ) * cubeSide 𝒮 M Q.level) :=
    mul_le_mul hR hLB (by positivity) (by positivity)
  have hx₁' : supNorm ((b.source : 𝒮.Point) - Q.centre) < 2 / 3 * cubeSide 𝒮 M Q.level := hx₁
  linarith
theorem cubeComplementAt_zero_eq_closure (hCells : CellStructure.CellStructureClaim)
    (𝒮 : NestedRegions) :
    𝒮.cubeComplementAt 0 (𝒮.Ω 0) = closure (𝒮.Ω 0)ᶜ := by
  obtain ⟨hp, hc, -⟩ := hCells 𝒮
  refine hp.complement_eq_closure 0 ?_ _ (hc.regions 0 (Nat.zero_le _)).1
  obtain ⟨k, hk⟩ := 𝒮.side_mem_zmultiples
  have hLr : (0 : ℝ) < 𝒮.L := by
    exact_mod_cast (by have := 𝒮.thirteen_le_L; omega : 0 < 𝒮.L)
  have hsp : scaleSpacing 𝒮.L 𝒮.ξ 𝒮.s = (𝒮.L : ℝ) ^ 𝒮.s * 𝒮.ξ := 𝒮.scale_eq_pow_mul 𝒮.s
  have hξ := 𝒮.ξ_pos
  have hz : 𝒮.scale 0 = 𝒮.ξ := by simpa using 𝒮.scale_eq_pow_mul 0
  have hk₀ : 0 < k := by
    by_contra hn
    have : (k : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 hn
    have h₂ : 𝒮.side ≤ 0 := by
      rw [hk, hsp]
      exact mul_nonpos_of_nonpos_of_nonneg this (by positivity)
    exact absurd 𝒮.side_pos (not_lt.2 h₂)
  refine ⟨k * (2 * (𝒮.L : ℤ) ^ 𝒮.s), ?_, ?_⟩
  · have hL₁ : (1 : ℤ) ≤ (𝒮.L : ℤ) := by
      exact_mod_cast (by have := 𝒮.thirteen_le_L; omega : 1 ≤ 𝒮.L)
    have hk₁ : (1 : ℤ) ≤ k * (𝒮.L : ℤ) ^ 𝒮.s :=
      one_le_mul_of_one_le_of_one_le (by omega) (one_le_pow₀ hL₁)
    linarith
  · rw [hz, hk, hsp, div_eq_iff hξ.ne']
    push_cast
    ring
theorem lt_supSetDist_thicken_cubeComplementAt_zero {R₁ : ℕ}
    (hs : DistanceSeparation.Holds 𝒮 M R₁)
    (hM : 𝒮.L ^ 5 ≤ M) (hcomp : 𝒮.cubeComplementAt 0 (𝒮.Ω 0) = closure (𝒮.Ω 0)ᶜ)
    (Q : LevelCube 𝒮 M) (hpos : ThickenedCubeLocation.Located Q)
    (hcase : 1 ≤ Q.level ∨ (Q.level = 0 ∧ Q.enlarge 3 ⊆ 𝒮.Ω 0)) :
    ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) <
      supSetDist (Q.thicken (5 / 6)) (𝒮.cubeComplementAt 0 (𝒮.Ω 0)) := by
  have hB0 := cubeSide_pos (𝒮 := 𝒮) hM 0
  rw [cubeSide_zero] at hB0
  have hR : (13 : ℝ) ≤ R₁ := by
    exact_mod_cast hs.thirteen_le_L.trans hs.L_le_gap
  have hlt : ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) < ENNReal.ofReal (2 * ((M : ℝ) * 𝒮.ξ)) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  refine hlt.trans_le (le_supSetDist ?_)
  rw [hcomp]
  intro x hx y hy
  rcases hcase with hn | ⟨hn, h₃⟩
  · have hr : 0 < mollifyRadius 𝒮 M Q.level := by
      have hB := cubeSide_pos hM Q.level
      have hL : (0 : ℝ) < 𝒮.L := by
        exact_mod_cast (by have := 𝒮.thirteen_le_L; omega : 0 < 𝒮.L)
      exact div_pos hB (mul_pos (by norm_num) hL)
    have hd := hpos.far_from_outside hn hx
    have hd₀ : 0 < distToOutside 𝒮 Q.level x :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.2 (mul_pos (by norm_num) hr)) hd
    have hxn := mem_Ω_of_distToOutside_pos hd₀
    have hx1 : x ∈ 𝒮.Ω 1 := Ω_subset_Ω_one hn (le_s_of_Ω_nonempty ⟨x, hxn⟩) hxn
    have hs0 : 0 < 𝒮.s := le_s_of_Ω_nonempty ⟨x, hx1⟩
    have hdist := hs.lt_distToOutside 0 hs0 x hx1
    by_contra hnot
    refine not_mem_closure_compl_of_lt_distToOutside hdist ?_ hy
    rw [cubeSide_zero]
    have h₁ : 13 * ((M : ℝ) * 𝒮.ξ) ≤ (R₁ : ℝ) * ((M : ℝ) * 𝒮.ξ) :=
      mul_le_mul_of_nonneg_right hR hB0.le
    linarith [not_le.1 hnot]
  · by_contra hnot
    rw [not_le] at hnot
    have hc : supNorm (x - Q.centre) < 5 / 6 * cubeSide 𝒮 M Q.level := hpos.near_centre hx
    rw [hn, cubeSide_zero] at hc
    have hopen : IsOpen {p : 𝒮.Point | ‖p - Q.centre‖ < 4 * ((M : ℝ) * 𝒮.ξ)} :=
      isOpen_lt (by fun_prop) continuous_const
    have hyU : ‖y - Q.centre‖ < 4 * ((M : ℝ) * 𝒮.ξ) := by
      have h₁ := supNorm_sub_le y x Q.centre
      rw [supNorm_sub_comm y x] at h₁
      rw [← supNorm_eq_norm]
      linarith
    obtain ⟨w, hwU, hw⟩ := mem_closure_iff.1 hy _ hopen hyU
    apply hw
    apply h₃
    show supNorm (w - Q.centre) ≤ (1 + ((3 : ℕ) : ℝ)) * cubeSide 𝒮 M Q.level
    rw [hn, cubeSide_zero, supNorm_eq_norm]
    push_cast
    have : ‖w - Q.centre‖ < 4 * ((M : ℝ) * 𝒮.ξ) := hwU
    linarith
theorem two_mul_le_supSetDist_pts_Ω_one (Q : LevelCube 𝒮 M) (hQ : Q.IsSecondType) :
    ENNReal.ofReal (2 * (M : ℝ) * 𝒮.ξ) ≤ supSetDist Q.pts (𝒮.Ω 1) := by
  obtain ⟨⟨hl, -⟩, he⟩ := hQ
  refine le_supSetDist fun x hx y hy => ?_
  by_contra hlt
  rw [not_le] at hlt
  have hx' : supNorm (x - Q.centre) ≤ cubeSide 𝒮 M Q.level := hx
  rw [hl, cubeSide_zero] at hx'
  have hy₂ : y ∈ Q.enlarge 2 := by
    show supNorm (y - Q.centre) ≤ (1 + ((2 : ℕ) : ℝ)) * cubeSide 𝒮 M Q.level
    rw [hl, cubeSide_zero]
    have h₁ := supNorm_sub_le y x Q.centre
    rw [supNorm_sub_comm y x] at h₁
    push_cast
    linarith
  exact (eq_empty_iff_forall_notMem.1 he y) ⟨hy₂, hy⟩
theorem statement_holds (hSep : DistanceSeparation.Statement)
    (hThick : ThickenedCubeLocation.Claim)
    (hWhere : PartitionFnSupportStatement)
    (hSides : LevelCubeSides.Statement)
    (hCells : CellStructure.CellStructureClaim) : Statement := by
  intro K m M R₁ 𝒮 h𝒮 hM
  have hs := hSep K m M R₁ 𝒮 h𝒮 hM
  refine ⟨fun Q hQ => ?_, two_mul_le_supSetDist_pts_Ω_one⟩
  have hQc := hQ.1
  have hpos := hThick K m M R₁ 𝒮 h𝒮 hM Q hQc
  have hcubes := hQ.1
  have hzero : Q.level = 0 → (Q.enlarge 2 ∩ 𝒮.Ω (Q.level + 1)).Nonempty := by
    intro h0
    by_contra hne
    apply hQ.2
    obtain ⟨n, -, hn, hb⟩ := hQc
    refine ⟨⟨h0, hb⟩, ?_⟩
    rw [h0] at hne
    exact not_nonempty_iff_eq_empty.1 hne
  refine ⟨?_, enlarge_three_subset_Ω hs hM Q, twentySix_mul_cubeSide_le_side hSides h𝒮 hM Q,
    enlarge_three_inter_Ω_add_two (fun Q => (hWhere 𝒮 K m M R₁ h𝒮 Q).1) hs hM Q hcubes, ?_⟩
  · by_cases hne : (Q.enlarge 2 ∩ 𝒮.Ω (Q.level + 1)).Nonempty
    · exact Or.inr hne
    · refine Or.inl ⟨not_nonempty_iff_eq_empty.1 hne, ?_⟩
      by_contra h1
      exact hne (hzero (by omega))
  · refine lt_supSetDist_thicken_cubeComplementAt_zero hs hM
      (cubeComplementAt_zero_eq_closure hCells 𝒮) Q hpos ?_
    by_cases h1 : 1 ≤ Q.level
    · exact Or.inl h1
    · have h0 : Q.level = 0 := by omega
      have h3 := enlarge_three_subset_Ω hs hM Q (hzero h0)
      rw [h0] at h3
      exact Or.inr ⟨h0, h3⟩
end YangMills.Construction.PartitionCubes.PositionByType
