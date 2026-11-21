import YangMills.Construction.TransferOperators.PeriodicGibbsStatesAreInvariantUnderLinkMirrors
import YangMills.Construction.InfiniteLattice.TwoWaysOfNamingALatticeMirror
import Mathlib
set_option autoImplicit false
open YangMills.Construction.NormalFamilies YangMills.Construction.LatticeConventions
open scoped ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice.LatticeMirrorNaming
theorem normSq_basisVector (μ : Direction) : normSq (basisVector μ) = 1 := by apply _root_.YangMills.Construction.TransferOperators.normSq_coordVec <;> assumption
theorem normSq_basisVector_add_smul {μ ν : Direction} (h : μ ≠ ν) (s : ℝ) (hs : s * s = 1) :
    normSq (basisVector μ + s • basisVector ν) = 2 := by
  rw [normSq_eq_dotProduct]
  simp only [basisVector, dotProduct_add, dotProduct_smul, dotProduct_single_one, Pi.add_apply,
    Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h.symm, smul_eq_mul]
  linear_combination hs
theorem normSq_of_isAxialNormal {n : Point} (h : LatticeConventions.IsAxialNormal n) :
    normSq n = 1 := by
  obtain ⟨μ, rfl⟩ := h
  exact normSq_basisVector μ
theorem normSq_of_isFaceDiagonalNormal {n : Point} (h : IsFaceDiagonalNormal n) :
    normSq n = 2 := by
  obtain ⟨μ, ν, hne, rfl | rfl⟩ := h
  · simpa using normSq_basisVector_add_smul hne 1 (by norm_num)
  · simpa [sub_eq_add_neg] using normSq_basisVector_add_smul hne (-1) (by norm_num)
theorem isNormal_of_mem_normalSet {n : Point} (h : n ∈ normalSet) :
    LatticeConventions.IsAxialNormal n ∨ IsFaceDiagonalNormal n := by
  rcases h with ⟨μ, rfl⟩ | ⟨μ, ν, hlt, rfl | rfl⟩
  · exact Or.inl ⟨μ, rfl⟩
  · exact Or.inr ⟨μ, ν, hlt.ne, Or.inl rfl⟩
  · exact Or.inr ⟨μ, ν, hlt.ne, Or.inr rfl⟩
theorem neg_mem_normalSet_of_not_mem {n : Point}
    (h : LatticeConventions.IsAxialNormal n ∨ IsFaceDiagonalNormal n)
    (hn : n ∉ normalSet) : -n ∈ normalSet ∧ IsFaceDiagonalNormal n := by
  rcases h with ⟨μ, rfl⟩ | ⟨μ, ν, hne, hd⟩
  · exact absurd (Or.inl ⟨μ, rfl⟩) hn
  · rcases lt_or_gt_of_ne hne with hlt | hlt
    · rcases hd with rfl | rfl
      · exact absurd (Or.inr ⟨μ, ν, hlt, Or.inl rfl⟩) hn
      · exact absurd (Or.inr ⟨μ, ν, hlt, Or.inr rfl⟩) hn
    · rcases hd with rfl | rfl
      · exact absurd (Or.inr ⟨ν, μ, hlt, Or.inl (add_comm _ _)⟩) hn
      · exact ⟨Or.inr ⟨ν, μ, hlt, Or.inr (neg_sub _ _)⟩, μ, ν, hne, Or.inr rfl⟩
theorem isAllowedLevel_of_isLatticeMirror {a : ℝ} {Q : NormalHyperplane}
    (hQ : Q.IsLatticeMirror a) (hn : Q.normal ∈ normalSet) :
    IsAllowedLevel a Q.normal Q.level := by
  constructor
  · intro h1
    rcases isNormal_of_mem_normalSet hn with hc | hd
    · exact hQ.1 hc
    · rw [normSq_of_isFaceDiagonalNormal hd] at h1
      norm_num at h1
  · intro h2
    rcases isNormal_of_mem_normalSet hn with hc | hd
    · rw [normSq_of_isAxialNormal hc] at h2
      norm_num at h2
    · exact hQ.2 hd
theorem isAllowedLevel_neg_of_isLatticeMirror {a : ℝ} {Q : NormalHyperplane}
    (hQ : Q.IsLatticeMirror a) (hd : IsFaceDiagonalNormal Q.normal) :
    IsAllowedLevel a (-Q.normal) (-Q.level) := by
  have hq : normSq (-Q.normal) = 2 := by
    rw [normSq_eq_dotProduct, neg_dotProduct, dotProduct_neg, neg_neg,
      ← normSq_eq_dotProduct, normSq_of_isFaceDiagonalNormal hd]
  constructor
  · intro h1
    rw [hq] at h1
    norm_num at h1
  · intro _
    obtain ⟨k, hk⟩ := hQ.2 hd
    exact ⟨-k, by rw [hk]; push_cast; ring⟩
theorem normal_dotProduct_self_ne_zero {a : ℝ} (P : NormalLevelPair a) :
    P.normal ⬝ᵥ P.normal ≠ 0 := by
  rw [← P.toLatticeMirror_realNormal]
  exact P.toLatticeMirror.cls.realNormal_dot_ne_zero
theorem reflectAcross_comp_self {a : ℝ} (P : NormalLevelPair a) :
    reflectAcross P.normal P.level ∘ reflectAcross P.normal P.level = id := by
  rw [reflectAcross_eq_hyperplaneReflect]
  funext x
  exact hyperplaneReflect_hyperplaneReflect (normal_dotProduct_self_ne_zero P) P.level x
theorem conj_actOn_eq {a : ℝ} {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a)
    (P : NormalLevelPair a) (h : Q.reflect = reflectAcross P.normal P.level)
    (F : GaugeField a → ℂ) :
    (fun U => conj ((NormalHyperplane.reflectSymmetry hQ).actOn F U)) =
      P.conjReflectObservable F := by
  have hs : NormalHyperplane.reflectSymmetry hQ = P.reflectSymmetry :=
    ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext h
  rw [hs]
  rfl
theorem statement_holds : LatticeMirrorNaming.Statement := by
  intro a _
  refine ⟨fun P => ⟨⟨P.reflectSymmetry, rfl⟩, reflectAcross_comp_self P⟩, ?_, ?_⟩
  · intro Q hQ
    by_cases hn : Q.normal ∈ normalSet
    · have hr : Q.reflect = reflectAcross Q.normal Q.level := by
        rw [NormalHyperplane.reflect_eq_hyperplaneReflect, reflectAcross_eq_hyperplaneReflect]
      let P : NormalLevelPair a := ⟨Q.normal, hn, Q.level, isAllowedLevel_of_isLatticeMirror hQ hn⟩
      refine ⟨P, 1, Or.inl ⟨hn, rfl, rfl, rfl⟩, rfl, hr,
        fun F _ => conj_actOn_eq hQ P hr F, ?_, ?_⟩
      · show regionObservables a Q.upperHalfSpace =
          regionObservables a (closedHalfSpace Q.normal Q.level 1)
        congr 1
        ext x
        simp [NormalHyperplane.upperHalfSpace, closedHalfSpace, euclidDot, dotProduct]
      · show regionObservables a Q.lowerHalfSpace =
          regionObservables a (closedHalfSpace Q.normal Q.level (-1))
        congr 1
        ext x
        simp [NormalHyperplane.lowerHalfSpace, closedHalfSpace, euclidDot, dotProduct]
    · obtain ⟨hneg, hd⟩ := neg_mem_normalSet_of_not_mem Q.normal_valid hn
      have hr : Q.reflect = reflectAcross (-Q.normal) (-Q.level) := by
        rw [NormalHyperplane.reflect_eq_hyperplaneReflect, reflectAcross_eq_hyperplaneReflect,
          ReflectionPositivity.MirrorHyperplanes.hyperplaneReflect_neg]
      let P : NormalLevelPair a :=
        ⟨-Q.normal, hneg, -Q.level, isAllowedLevel_neg_of_isLatticeMirror hQ hd⟩
      refine ⟨P, -1, Or.inr ⟨hn, rfl, rfl, rfl⟩, ?_, hr,
        fun F _ => conj_actOn_eq hQ P hr F, ?_, ?_⟩
      · ext x
        show euclidDot Q.normal x = Q.level ↔ (-Q.normal) ⬝ᵥ x = -Q.level
        rw [neg_dotProduct, neg_inj]
        rfl
      · show regionObservables a Q.upperHalfSpace =
          regionObservables a (closedHalfSpace (-Q.normal) (-Q.level) (-1))
        congr 1
        ext x
        simp [NormalHyperplane.upperHalfSpace, closedHalfSpace, euclidDot, dotProduct]
      · show regionObservables a Q.lowerHalfSpace =
          regionObservables a (closedHalfSpace (-Q.normal) (-Q.level) (- -1))
        congr 1
        ext x
        simp [NormalHyperplane.lowerHalfSpace, closedHalfSpace, euclidDot, dotProduct]
  · intro P
    refine ⟨⟨P.normal, P.level, isNormal_of_mem_normalSet P.normal_mem⟩, rfl, rfl, ?_, ?_⟩
    · intro hc
      exact P.allowed.1 (normSq_of_isAxialNormal hc)
    · intro hd
      exact P.allowed.2 (normSq_of_isFaceDiagonalNormal hd)
end YangMills.Construction.InfiniteLattice.LatticeMirrorNaming
end
