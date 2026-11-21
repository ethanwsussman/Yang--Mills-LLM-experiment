import YangMills.Construction.Torus.BoundsOnTheCompressedOperatorsProof
import YangMills.Construction.Torus.DifferencesAndAveragesOnAGeneralTorusProof
import YangMills.Construction.Torus.FunctionsOfTheSupDistanceAndTheWeightedDistanceProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace GeneralTorus.CoarseBondForms
section Generic
variable {V U : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup U] [Module ℝ U]
structure IsInnerForm (p : V → V → ℝ) : Prop where
  add_left : ∀ u v w, p (u + v) w = p u w + p v w
  smul_left : ∀ (r : ℝ) u v, p (r • u) v = r * p u v
  symm : ∀ u v, p u v = p v u
  pos : ∀ v, v ≠ 0 → 0 < p v v
namespace IsInnerForm
variable {p : V → V → ℝ} (hp : IsInnerForm p)
include hp
theorem add_right (u v w : V) : p u (v + w) = p u v + p u w := by
  rw [hp.symm, hp.add_left, hp.symm v, hp.symm w]
theorem smul_right (r : ℝ) (u v : V) : p u (r • v) = r * p u v := by
  rw [hp.symm, hp.smul_left, hp.symm v]
theorem zero_left (v : V) : p 0 v = 0 := by
  have := hp.smul_left 0 0 v
  simpa using this
theorem sub_left (u v w : V) : p (u - v) w = p u w - p v w := by
  have h1 := hp.add_left (u - v) v w
  rw [sub_add_cancel] at h1
  linarith
theorem sub_right (u v w : V) : p u (v - w) = p u v - p u w := by
  rw [hp.symm, hp.sub_left, hp.symm v, hp.symm w]
theorem self_nonneg (v : V) : 0 ≤ p v v := by
  by_cases h : v = 0
  · rw [h, hp.zero_left]
  · exact (hp.pos v h).le
theorem eq_zero_of_self_eq_zero (v : V) (h : p v v = 0) : v = 0 := by
  by_contra hv
  exact (hp.pos v hv).ne' h
end IsInnerForm
theorem exists_isAdjointFor [FiniteDimensional ℝ V] {p : V → V → ℝ} {q : U → U → ℝ}
    (hp : IsInnerForm p) (hq : IsInnerForm q) (K : V →ₗ[ℝ] U) :
    ∃ T : U →ₗ[ℝ] V, IsAdjointFor p q K T := by
  let Φ : V →ₗ[ℝ] Module.Dual ℝ V :=
    LinearMap.mk₂ ℝ p hp.add_left hp.smul_left hp.add_right hp.smul_right
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun v hv => hp.eq_zero_of_self_eq_zero v ?_
    have : Φ v v = 0 := by rw [hv]; rfl
    exact this
  let e := LinearMap.linearEquivOfInjective Φ hinj (Subspace.dual_finrank_eq).symm
  let F : U →ₗ[ℝ] Module.Dual ℝ V :=
    LinearMap.mk₂ ℝ (fun u v => q (K v) u)
      (fun u u' v => hq.add_right _ _ _)
      (fun r u v => hq.smul_right _ _ _)
      (fun u v v' => by simp only [map_add]; exact hq.add_left _ _ _)
      (fun r u v => by simp only [map_smul]; exact hq.smul_left _ _ _)
  refine ⟨e.symm.toLinearMap ∘ₗ F, fun v u => ?_⟩
  have h : Φ (e.symm (F u)) = F u := e.apply_symm_apply (F u)
  have h2 : Φ (e.symm (F u)) v = F u v := by rw [h]
  have h3 : p (e.symm (F u)) v = q (K v) u := h2
  rw [← h3, hp.symm]
  rfl
end Generic
section Numbers
variable (D : ScaleData)
theorem thirteen_le_L : 13 ≤ D.L := D.blocking.thirteen_le
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem admitsPartition_levelSpacing {n : ℕ} (h : n ≤ D.lastLevel) :
    D.AdmitsPartition (D.levelSpacing n) := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.admitsPartition_levelSpacing_of_le_lastLevel <;> assumption
theorem levelSpacing_lt_torusSide {n : ℕ} (h : n ≤ D.lastLevel) :
    D.levelSpacing n < D.torusSide := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.levelSpacing_lt_torusSide <;> assumption
theorem torusSide_pos : 0 < D.torusSide := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.torusSide_pos <;> assumption
theorem finite_latticeBond {S σ : ℝ} [Finite (LatticeSite S σ)] : Finite (LatticeBond S σ) := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.finite_latticeBond <;> assumption
theorem finite_latticePlaquette {S σ : ℝ} [Finite (LatticeSite S σ)] :
    Finite (LatticePlaquette S σ) := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.finite_latticePlaquette <;> assumption
instance instFiniteBaseBond : Finite D.BaseBond :=
  have : Finite (D.BondAt 0) := finite_latticeBond
  Subtype.finite
instance instFiniteBasePlaquette : Finite D.BasePlaquette := finite_latticePlaquette
end Numbers
section Sequences
variable {D : ScaleData} (B : SeparatedChain D)
theorem set_antitone {i j : ℕ} (h : i ≤ j) : B.set j ⊆ B.set i := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.Chain.set_antitone <;> assumption
theorem shell_index_unique {y : D.Space} {n m : ℕ} (h1 : y ∈ B.set n) (h2 : y ∉ B.set (n + 1))
    (h3 : y ∈ B.set m) (h4 : y ∉ B.set (m + 1)) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact absurd (set_antitone B h h3) h2
  · exact h
  · exact absurd (set_antitone B h h1) h4
variable (hc : SeparatedChainStructure)
include hc
theorem mem_shellSites_iff {n : ℕ} (hn : n ≤ D.lastLevel) (y : D.Space) :
    y ∈ B.shellSites n ↔ y ∈ (D.levelSublattice n : Set D.Space) ∧ y ∈ B.set n ∧
      y ∉ B.set (n + 1) := by
  rw [((hc D B).2.1 n hn).2.2.1]
  rfl
omit hc in
theorem shellSites_eq_empty {n : ℕ} (hn : D.lastLevel < n) : B.shellSites n = ∅ := by
  have h : B.shell n = ∅ := by
    unfold SeparatedChain.shell
    rw [if_neg (by omega), if_neg (by omega)]
  unfold SeparatedChain.shellSites
  rw [h, inter_empty]
theorem shellIndex_eq {n : ℕ} (hn : n ≤ D.lastLevel) {y : D.Space} (hy : y ∈ B.shellSites n) :
    B.shellIndex y = n := by
  have hs : {i | y ∈ B.shellSites i} = {n} := by
    ext i
    simp only [mem_ofPred_eq, mem_singleton_iff]
    refine ⟨fun hi => ?_, fun hi => hi ▸ hy⟩
    by_cases hit : i ≤ D.lastLevel
    · have a := (mem_shellSites_iff B hc hit y).1 hi
      have b := (mem_shellSites_iff B hc hn y).1 hy
      exact shell_index_unique B a.2.1 a.2.2 b.2.1 b.2.2
    · rw [shellSites_eq_empty B (by omega)] at hi
      exact absurd hi (notMem_empty _)
  unfold SeparatedChain.shellIndex
  rw [hs]
  simp
end Sequences
section Averages
variable (D : ScaleData)
end Averages
section SeriesExpansions
variable (W : GaugeSetting)
theorem finite_coarseBond : Finite W.CoarseBond := by apply _root_.YangMills.Construction.GeneralTorus.InnerProductsAdjointsProjections.finite_coarseBond <;> assumption
theorem coarseSpacing_pos (c : W.CoarseBond) : 0 < GaugeSetting.coarseSpacing c := by apply _root_.YangMills.Construction.GeneralTorus.CompressedBoundsProof.coarseSpacing_pos <;> assumption
variable {W}
variable (hc : SeparatedChainStructure)
include hc
end SeriesExpansions
section Forms
variable (W : GaugeSetting)
end Forms
section Matrices
variable (W : GaugeSetting)
theorem coarseUnit_self (c : W.CoarseBond) :
    W.coarseUnit c c = (GaugeSetting.coarseSpacing c ^ 2)⁻¹ := by
  simp [GaugeSetting.coarseUnit, GaugeSetting.coarseDelta]
theorem coarseUnit_of_ne {c x : W.CoarseBond} (h : x ≠ c) : W.coarseUnit c x = 0 := by
  have h1 : W.coarseDelta c x = 0 := by
    simp [GaugeSetting.coarseDelta, h]
  change (GaugeSetting.coarseSpacing c ^ 2)⁻¹ * W.coarseDelta c x = 0
  rw [h1, mul_zero]
theorem coarseInner_coarseUnit (c : W.CoarseBond) (f : W.CoarseField) :
    W.coarseInner (W.coarseUnit c) f = GaugeSetting.coarseSpacing c ^ 2 * f c := by
  unfold GaugeSetting.coarseInner
  rw [finsum_eq_single _ c fun x hx => by rw [coarseUnit_of_ne W hx]; ring, coarseUnit_self]
  have h := (coarseSpacing_pos W c).ne'
  field_simp
theorem matrixEntry_eq (K : Module.End ℝ W.CoarseField) (c c' : W.CoarseBond) :
    W.matrixEntry K c c' = GaugeSetting.coarseSpacing c ^ 2 * K (W.coarseUnit c') c :=
  coarseInner_coarseUnit W c _
theorem coarseUnit_expansion [Fintype W.CoarseBond] (f : W.CoarseField) :
    f = ∑ c, W.coarseInner (W.coarseUnit c) f • W.coarseUnit c := by
  funext x
  rw [Finset.sum_apply, Finset.sum_eq_single x]
  · rw [Pi.smul_apply, coarseUnit_self, coarseInner_coarseUnit, smul_eq_mul]
    have h := (coarseSpacing_pos W x).ne'
    field_simp
  · intro c _ hc
    rw [Pi.smul_apply, coarseUnit_of_ne W (Ne.symm hc), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ x) h
theorem matrixEntry_comp (K K' : Module.End ℝ W.CoarseField) (c c'' : W.CoarseBond) :
    W.matrixEntry (K ∘ₗ K') c c'' =
      ∑ᶠ c' : W.CoarseBond, W.matrixEntry K c c' * W.matrixEntry K' c' c'' := by
  have := finite_coarseBond W
  have := Fintype.ofFinite W.CoarseBond
  rw [finsum_eq_sum_of_fintype, matrixEntry_eq, LinearMap.comp_apply,
    coarseUnit_expansion W (K' (W.coarseUnit c'')), map_sum, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, matrixEntry_eq W K]
  change _ = _ * W.coarseInner _ _
  ring
end Matrices
section Bonds
theorem addCircle_coe_ne_zero {S a : ℝ} (hS : 0 < S) (ha : a ≠ 0) (hlt : |a| < S) :
    (a : AddCircle S) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff S).1 h
  have hk' : (k : ℝ) * S = a := by simpa using hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply ha
    rw [← hk']
    simp
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  rw [← hk', abs_mul, abs_of_pos hS] at hlt
  nlinarith
open Classical in
def setIndicator (D : ScaleData) (T : Set D.Space) : D.SiteField :=
  fun x => if (x : D.Space) ∈ T then 1 else 0
end Bonds
end GeneralTorus.CoarseBondForms
end YangMills.Construction
end
