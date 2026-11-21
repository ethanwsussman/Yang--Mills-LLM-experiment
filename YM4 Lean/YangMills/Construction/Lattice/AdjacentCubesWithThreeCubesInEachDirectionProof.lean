import YangMills.Construction.Lattice.AdjacentCubesWithThreeCubesInEachDirection
import YangMills.Construction.Lattice.CubesAdjacentToACubeOfAPartition
import YangMills.Construction.Lattice.LiftsOfCubesVerticesAndEdges
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ThreeWideNeighbours
open EdgeGraphCubeProperties CubeLifts
variable (S : LevelUnitPartition)
theorem proj_eq_iff_isPointLift (x : S.Points) (w : Fin 4 → ℝ) :
    S.proj w = x ↔ S.IsPointLift x w :=
  levelProj_eq_iff_isLevelLift
    (by have := S.params.isAdmissible.2; omega) _ _ _ x w
theorem sideInLevelUnits_eq_scaledTorusSide :
    sideInLevelUnits S.params.L S.params.m S.params.K S.level = scaledTorusSide S := by
  have hL : (S.params.L : ℝ) ≠ 0 := by
    have := S.params.isAdmissible.2
    have h0 : S.params.L ≠ 0 := by omega
    exact_mod_cast h0
  change 2 * (S.params.L : ℝ) ^ (((S.params.m : ℕ) : ℤ) + ((S.params.K : ℕ) : ℤ) - S.level) =
    2 * (S.params.L : ℝ) ^ (S.params.m : ℕ) * (S.params.L : ℝ) ^ levelDepth S.params.K S.level
  rw [mul_assoc, ← zpow_natCast (S.params.L : ℝ) (S.params.m : ℕ), ← zpow_add₀ hL]
  congr 2
  simp only [levelDepth]
  ring
theorem signedStep_apply (ν μ : Fin 4) (σ : ℝ) :
    EdgeGraphCubeProperties.signedStep S ν σ μ = if μ = ν then σ * (S.side : ℝ) else 0 := by
  by_cases h : μ = ν
  · subst h
    simp [EdgeGraphCubeProperties.signedStep, coordVec]
  · simp [EdgeGraphCubeProperties.signedStep, coordVec, h]
theorem add_signedStep_add_signedStep_neg (c : Fin 4 → ℝ) (ν : Fin 4) (σ : ℝ) :
    c + EdgeGraphCubeProperties.signedStep S ν σ + EdgeGraphCubeProperties.signedStep S ν (-σ) = c := by
  funext μ
  simp only [Pi.add_apply, signedStep_apply]
  split_ifs <;> ring
theorem int_eq_zero_of_abs_mul_le_two_mul {N M : ℝ} (hM : 0 < M) (hN : 3 ≤ N) {a : ℤ}
    (h : |N * M * (a : ℝ)| ≤ 2 * M) : a = 0 := by
  by_contra ha
  have h1 : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
  have hNM : 0 < N * M := mul_pos (by linarith) hM
  rw [abs_mul, abs_of_pos hNM] at h
  have e1 : 0 ≤ N * M * (|(a : ℝ)| - 1) := mul_nonneg hNM.le (by linarith)
  have e2 : 0 ≤ (N - 3) * M := mul_nonneg (by linarith) hM.le
  nlinarith
theorem isCubeCentre_add_signedStep {c : Fin 4 → ℝ} (hc : IsCubeCentre S c) (ν : Fin 4)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : IsCubeCentre S (c + EdgeGraphCubeProperties.signedStep S ν σ) := by
  intro μ
  obtain ⟨a, ha⟩ := hc μ
  simp only [Pi.add_apply, signedStep_apply, ha]
  by_cases h : μ = ν
  · rcases hσ with rfl | rfl
    · exact ⟨a + 1, by simp [h]; ring⟩
    · exact ⟨a - 1, by simp [h]; ring⟩
  · exact ⟨a, by simp [h]⟩
theorem eq_of_isCubeCentredAt_signedStep (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    (hShort : ShortVectorsNotPeriods S) (h3 : 3 ≤ S.cubeCount) (c : Fin 4 → ℝ)
    (ν ν' : Fin 4) (σ σ' : ℝ) (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1) (Δ : Set S.Points)
    (h₁ : IsCubeCentredAt S Δ (S.proj (c + EdgeGraphCubeProperties.signedStep S ν σ)))
    (h₂ : IsCubeCentredAt S Δ (S.proj (c + EdgeGraphCubeProperties.signedStep S ν' σ'))) :
    ν = ν' ∧ σ = σ' := by
  obtain ⟨-, -, -, -, -, -, -, hper, -, -, hM⟩ := hT
  have hMr : (0 : ℝ) < (S.side : ℝ) := by exact_mod_cast hM
  obtain ⟨y₁, hy₁, rfl⟩ := h₁
  obtain ⟨y₂, hy₂, hΔ⟩ := h₂
  have hyy : y₁ = y₂ := by
    by_contra h
    exact hC.2.2.1 y₁ y₂ h hΔ
  subst hyy
  have hcov : S.proj (c + EdgeGraphCubeProperties.signedStep S ν' σ') =
      S.proj (c + EdgeGraphCubeProperties.signedStep S ν σ) := hy₂.symm.trans hy₁
  have hperiod : IsPeriodVector S
      ((c + EdgeGraphCubeProperties.signedStep S ν σ) - (c + EdgeGraphCubeProperties.signedStep S ν' σ')) :=
    (hper _ _).1 ⟨_, (proj_eq_iff_isPointLift S _ _).1 rfl, (proj_eq_iff_isPointLift S _ _).1 hcov⟩
  rw [add_sub_add_left_eq_sub] at hperiod
  have hzero : EdgeGraphCubeProperties.signedStep S ν σ - EdgeGraphCubeProperties.signedStep S ν' σ' = 0 := by
    by_contra h
    refine hShort.2 h3 _ h (fun μ => ?_) hperiod
    simp only [Pi.sub_apply, signedStep_apply]
    split_ifs <;> rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;>
      first
        | (left; ring1)
        | (right; left; ring1)
        | (right; right; left; ring1)
        | (right; right; right; left; ring1)
        | (right; right; right; right; ring1)
  have hν := congrFun hzero ν
  simp only [Pi.sub_apply, Pi.zero_apply, signedStep_apply, if_true] at hν
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  by_cases hνν : ν = ν'
  · subst hνν
    refine ⟨rfl, ?_⟩
    simp only [if_true] at hν
    have : (σ - σ') * (S.side : ℝ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hMr.ne'
  · simp only [hνν, if_false, sub_zero] at hν
    rcases mul_eq_zero.1 hν with h | h
    · exact absurd h hσ0
    · exact absurd h hMr.ne'
theorem mem_closedBox_signedStep_of_facet (c : Fin 4 → ℝ) (ν : Fin 4) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {x : Fin 4 → ℝ} (hx : x ∈ S.closedBox c)
    (hxν : x ν = c ν + σ * (S.side : ℝ) / 2) :
    x ∈ S.closedBox (c + EdgeGraphCubeProperties.signedStep S ν σ) ∧
      x ν = (c + EdgeGraphCubeProperties.signedStep S ν σ) ν + -σ * (S.side : ℝ) / 2 := by
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hk : k = ν
    · subst hk
      simp only [Pi.add_apply, signedStep_apply, if_true]
      rw [hxν]
      rcases hσ with rfl | rfl <;> constructor <;> linarith
    · simp only [Pi.add_apply, signedStep_apply, hk, if_false, add_zero]
      exact hx k
  · simp only [Pi.add_apply, signedStep_apply, if_true]
    rw [hxν]
    ring
theorem facetAt_eq_facetAt_signedStep (c : Fin 4 → ℝ) (ν : Fin 4) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    S.facetAt c ν σ = S.facetAt (c + EdgeGraphCubeProperties.signedStep S ν σ) ν (-σ) := by
  have hσ' : -σ = 1 ∨ -σ = -1 := by
    rcases hσ with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg 1)
  unfold LevelUnitPartition.facetAt
  congr 1
  ext x
  constructor
  · rintro ⟨hx, hxν⟩
    exact mem_closedBox_signedStep_of_facet S c ν hσ hx hxν
  · rintro ⟨hx, hxν⟩
    have h := mem_closedBox_signedStep_of_facet S _ ν hσ' hx hxν
    rw [add_signedStep_add_signedStep_neg, neg_neg] at h
    exact h
theorem projectedBox_inter_signedStep_eq_facetAt (hT : TorusInCubeUnits S) (h3 : 3 ≤ S.cubeCount)
    (c : Fin 4 → ℝ) (ν : Fin 4) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    projectedBox S c ∩ projectedBox S (c + EdgeGraphCubeProperties.signedStep S ν σ) = S.facetAt c ν σ := by
  obtain ⟨-, -, -, -, -, -, -, hper, -, -, hM⟩ := hT
  have hMr : (0 : ℝ) < (S.side : ℝ) := by exact_mod_cast hM
  have hN : (3 : ℝ) ≤ (S.cubeCount : ℝ) := by exact_mod_cast h3
  ext p
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ⟨x', hx', hxx⟩⟩
    obtain ⟨a, ha⟩ : IsPeriodVector S (x' - x) :=
      (hper _ _).1 ⟨_, (proj_eq_iff_isPointLift S _ _).1 rfl, (proj_eq_iff_isPointLift S _ _).1 hxx.symm⟩
    have hz : ∀ μ, a μ = 0 := by
      intro μ
      apply int_eq_zero_of_abs_mul_le_two_mul hMr hN
      rw [← ha μ, abs_le]
      have h₁ := hx μ
      have h₂ := hx' μ
      simp only [Pi.add_apply, signedStep_apply, mem_Icc] at h₂
      simp only [mem_Icc] at h₁
      simp only [Pi.sub_apply]
      split_ifs at h₂ <;> rcases hσ with rfl | rfl <;> constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
    have hxx' : x' = x := by
      funext μ
      have h := ha μ
      rw [hz μ] at h
      simp only [Pi.sub_apply, Int.cast_zero, mul_zero] at h
      linarith
    subst hxx'
    refine ⟨x', ⟨hx, ?_⟩, rfl⟩
    have h₁ := hx ν
    have h₂ := hx' ν
    simp only [Pi.add_apply, signedStep_apply, if_true, mem_Icc] at h₂
    simp only [mem_Icc] at h₁
    rcases hσ with rfl | rfl <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  · rintro ⟨x, ⟨hx, hxν⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, ⟨x, (mem_closedBox_signedStep_of_facet S c ν hσ hx hxν).1, rfl⟩⟩
theorem isCubeFace_of_signedStep (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    (h3 : 3 ≤ S.cubeCount) (y y' : Site S.params.L S.params.m S.index) {c : Fin 4 → ℝ}
    {ν : Fin 4} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hc : S.IsPointLift (y : S.Points) c)
    (hc' : S.IsPointLift (y' : S.Points) (c + EdgeGraphCubeProperties.signedStep S ν σ)) :
    IsCubeFace S.index (cubeAround y ∩ cubeAround y') (cubeAround y) := by
  have hface := projectedBox_inter_signedStep_eq_facetAt S hT h3 c ν hσ
  have hcov : S.proj c = (y : S.Points) := (proj_eq_iff_isPointLift S _ _).2 hc
  obtain ⟨-, hsp, -, -, hunitS, hsideN, -, -, -, -, hM⟩ := hT
  have hMr : (0 : ℝ) < (S.side : ℝ) := by exact_mod_cast hM
  have hN : (3 : ℝ) ≤ (S.cubeCount : ℝ) := by exact_mod_cast h3
  have hL : (S.params.L : ℝ) ≠ 0 := by
    have := S.params.isAdmissible.2
    have h0 : S.params.L ≠ 0 := by omega
    exact_mod_cast h0
  obtain ⟨sp, hspdef⟩ : ∃ sp : ℝ, sp = meshSize S.params.L (levelDepth S.params.K S.level) :=
    ⟨_, rfl⟩
  have hsp0 : sp ≠ 0 := by
    rw [hspdef]
    exact zpow_ne_zero _ hL
  have hinv : sp * (S.params.L : ℝ) ^ levelDepth S.params.K S.level = 1 := by
    rw [hspdef]
    simp only [meshSize]
    rw [← zpow_add₀ hL, neg_add_cancel, zpow_zero]
  have hside : torusSide S.params.L S.params.m =
      (S.cubeCount : ℝ) * ((S.side : ℝ) * sp) := by
    have h₁ : (S.params.L : ℝ) ^ levelDepth S.params.K S.level *
        torusSide S.params.L S.params.m = scaledTorusSide S := hunitS
    rw [hsideN] at h₁
    calc torusSide S.params.L S.params.m
        = sp * ((S.params.L : ℝ) ^ levelDepth S.params.K S.level *
            torusSide S.params.L S.params.m) := by
          rw [← mul_assoc, hinv, one_mul]
      _ = _ := by rw [h₁]; ring
  have hcoord : ∀ x : Fin 4 → ℝ, S.proj x ν = (y : S.Points) ν +
      ((sp * (x ν - c ν) : ℝ) : AddCircle (torusSide S.params.L S.params.m)) := by
    intro x
    rw [← hcov]
    change ((meshSize S.params.L (levelDepth S.params.K S.level) * x ν : ℝ) :
        AddCircle (torusSide S.params.L S.params.m)) =
      ((meshSize S.params.L (levelDepth S.params.K S.level) * c ν : ℝ) :
        AddCircle (torusSide S.params.L S.params.m)) + _
    rw [← AddCircle.coe_add, ← hspdef]
    congr 1
    ring
  have hhalf : σ * meshSize S.params.L S.index / 2 =
      sp * (σ * (S.side : ℝ) / 2) := by
    rw [← hsp, ← hspdef]
    ring
  refine ⟨y, rfl, ν, σ, hσ, ?_⟩
  have hcube := hC.2.1
  have hinter : cubeAround y ∩ cubeAround y' = S.facetAt c ν σ := by
    rw [hcube y c hc, hcube y' _ hc']
    exact hface
  rw [hinter, hhalf, hcube y c hc]
  ext p
  constructor
  · rintro ⟨x, ⟨hx, hxν⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rw [hcoord x, hxν]
    congr 2
    ring
  · rintro ⟨⟨x, hx, rfl⟩, hp⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    rw [hcoord x] at hp
    have hcoe := add_left_cancel hp
    have hzero : ((sp * (x ν - c ν) - sp * (σ * (S.side : ℝ) / 2) : ℝ) :
        AddCircle (torusSide S.params.L S.params.m)) = 0 := by
      rw [AddCircle.coe_sub, hcoe, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 hzero
    rw [hside, zsmul_eq_mul] at hn
    have hcancel : (S.cubeCount : ℝ) * (S.side : ℝ) * (n : ℝ) =
        x ν - c ν - σ * (S.side : ℝ) / 2 := by
      apply mul_left_cancel₀ hsp0
      linear_combination hn
    have hxb := hx ν
    simp only [mem_Icc] at hxb
    have hn0 : n = 0 := by
      apply int_eq_zero_of_abs_mul_le_two_mul hMr hN
      rw [hcancel, abs_le]
      rcases hσ with rfl | rfl <;> constructor <;> linarith [hxb.1, hxb.2]
    rw [hn0] at hcancel
    simp only [Int.cast_zero, mul_zero] at hcancel
    linarith
theorem cubesShareFace_of_signedStep (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    (h3 : 3 ≤ S.cubeCount) (y y' : Site S.params.L S.params.m S.index) {c : Fin 4 → ℝ}
    {ν : Fin 4} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hc : S.IsPointLift (y : S.Points) c)
    (hc' : S.IsPointLift (y' : S.Points) (c + EdgeGraphCubeProperties.signedStep S ν σ)) :
    CubesShareFace S.index (cubeAround y) (cubeAround y') := by
  have hσ' : -σ = 1 ∨ -σ = -1 := by
    rcases hσ with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg 1)
  refine ⟨isCubeFace_of_signedStep S hT hC h3 y y' hσ hc hc', ?_⟩
  rw [inter_comm]
  refine isCubeFace_of_signedStep S hT hC h3 y' y (ν := ν) hσ' hc' ?_
  rw [add_signedStep_add_signedStep_neg]
  exact hc
theorem exists_site_of_signedStep (hC : SiteAndCubeLifts S) {c : Fin 4 → ℝ} (hcen : IsCubeCentre S c)
    (ν : Fin 4) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ y' : Site S.params.L S.params.m S.index,
      S.IsPointLift (y' : S.Points) (c + EdgeGraphCubeProperties.signedStep S ν σ) ∧
      cubeAround y' = projectedBox S (c + EdgeGraphCubeProperties.signedStep S ν σ) ∧
      IsCubeCentredAt S (projectedBox S (c + EdgeGraphCubeProperties.signedStep S ν σ))
        (S.proj (c + EdgeGraphCubeProperties.signedStep S ν σ)) := by
  obtain ⟨y', hy'⟩ := (hC.1 _).2 (isCubeCentre_add_signedStep S hcen ν hσ)
  have hcube : cubeAround y' = projectedBox S (c + EdgeGraphCubeProperties.signedStep S ν σ) :=
    hC.2.1 y' _ hy'
  exact ⟨y', hy', hcube, y', ((proj_eq_iff_isPointLift S _ _).2 hy').symm, hcube.symm⟩
theorem cubeNeighboursOnThreeWideTorus (hLifts : CubeLifts.Statement)
    (hAdj : PartitionCubeNeighbours) : CubeNeighboursOnThreeWideTorus := by
  intro S
  obtain ⟨-, -, hS⟩ := hLifts
  obtain ⟨hT, hCases, hC, -, -, hShort⟩ := hS S
  have hlift : ∀ x : S.Points, ∃ w, S.IsPointLift x w := hT.2.2.2.2.2.2.1
  have hiff : 3 * (S.side : ℝ) ≤ sideInLevelUnits S.params.L S.params.m S.params.K S.level ↔
      3 ≤ S.cubeCount := by
    rw [sideInLevelUnits_eq_scaledTorusSide]
    exact hCases.1.symm
  refine ⟨hiff.trans hCases.2.2.2.2.2.2.2, fun h3' => ?_⟩
  have h3 := hiff.1 h3'
  refine ⟨?_, ?_, ?_⟩
  · intro c _ ν ν' σ σ' hσ hσ' Δ h₁ h₂
    exact eq_of_isCubeCentredAt_signedStep S hT hC hShort h3 c ν ν' σ σ' hσ hσ' Δ h₁ h₂
  · intro c _ ν σ hσ
    exact ⟨projectedBox_inter_signedStep_eq_facetAt S hT h3 c ν hσ,
      facetAt_eq_facetAt_signedStep S c ν hσ⟩
  · intro Δ hΔ
    obtain ⟨y, rfl⟩ : ∃ y : Site S.params.L S.params.m S.index, cubeAround y = Δ := hΔ
    obtain ⟨c, hc⟩ := hlift (y : S.Points)
    have hcen : IsCubeCentre S c := (hC.1 c).1 ⟨y, hc⟩
    have hsign : ∀ b : Bool, ((if b then 1 else -1 : ℝ) = 1 ∨ (if b then 1 else -1 : ℝ) = -1) := by
      intro b
      cases b <;> simp
    obtain ⟨f, hf⟩ : ∃ f : Fin 4 × Bool → Set S.Points, f = fun p =>
        projectedBox S (c + EdgeGraphCubeProperties.signedStep S p.1 (if p.2 then 1 else -1)) :=
      ⟨_, rfl⟩
    have hinj : Function.Injective f := by
      rintro ⟨ν, b⟩ ⟨ν', b'⟩ hpq
      obtain ⟨-, -, -, h₁⟩ := exists_site_of_signedStep S hC hcen ν (hsign b)
      obtain ⟨-, -, -, h₂⟩ := exists_site_of_signedStep S hC hcen ν' (hsign b')
      simp only [hf] at hpq
      rw [← hpq] at h₂
      obtain ⟨hν, hb⟩ :=
        eq_of_isCubeCentredAt_signedStep S hT hC hShort h3 c ν ν' _ _ (hsign b) (hsign b') _ h₁ h₂
      subst hν
      have : b = b' := by
        cases b <;> cases b' <;> first | rfl | (norm_num at hb)
      rw [this]
    have hsub : range f ⊆ neighbourCubes S (cubeAround y) := by
      rintro _ ⟨⟨ν, b⟩, rfl⟩
      obtain ⟨y', hy', hcube, -⟩ := exists_site_of_signedStep S hC hcen ν (hsign b)
      simp only [hf]
      rw [← hcube]
      exact ⟨⟨y', rfl⟩, cubesShareFace_of_signedStep S hT hC h3 y y' (hsign b) hc hy'⟩
    refine le_antisymm ((hAdj S).2 _ ⟨y, rfl⟩) ?_
    have hcard : (range f).encard = 8 := by
      rw [← image_univ, hinj.encard_image, encard_univ, ENat.card_eq_coe_fintype_card]
      simp
    rw [← hcard]
    exact encard_le_encard hsub
end YangMills.Construction.PeriodicLattice.ThreeWideNeighbours
end
