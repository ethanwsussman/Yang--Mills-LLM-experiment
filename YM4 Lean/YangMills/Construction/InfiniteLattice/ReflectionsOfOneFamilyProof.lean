import YangMills.Construction.InfiniteLattice.ReconstructionAtALatticeMirrorProof
import YangMills.Construction.InfiniteLattice.PropertiesOfTheSixteenFamiliesProof
import YangMills.Construction.InfiniteLattice.ReflectionsOfOneFamily
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open InfiniteLattice
namespace ReflectionIdentities
theorem symmetry_ext_of_toFun {a : ℝ} {r s : LatticeSymmetry a} (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem actOn_eq_self_of_toFun_eq_id {a : ℝ} (r : LatticeSymmetry a) (h : r.toFun = id)
    (F : GaugeField a → ℂ) : r.actOn F = F := by
  have hpt : ∀ x : LatticePoint a, r.pointMap x = x := fun x => Subtype.ext (congrFun h (x : AmbientSpace))
  have hlk : ∀ e : Link a, r.linkMap e = e := fun e =>
    Link.ext (hpt e.initial) (hpt e.terminal)
  funext U
  have hU : r.pullbackField U = U := by
    apply Subtype.ext
    funext e
    exact congrArg U.1 (hlk e)
  change F (r.pullbackField U) = F U
  rw [hU]
theorem normSq_eq_one_or_two {n : AmbientSpace} (hn : n ∈ normalSet) :
    normSq n = 1 ∨ normSq n = 2 := by apply _root_.YangMills.Construction.NormalFamilies.Properties.normSq_eq_one_or_two <;> assumption
theorem dotProduct_reflectAcross {n : AmbientSpace} (hnn : n ⬝ᵥ dualVector n = 1) (c : ℝ)
    (x : AmbientSpace) : n ⬝ᵥ reflectAcross n c x = 2 * c - n ⬝ᵥ x := by
  simp only [reflectAcross, dotProduct_sub, dotProduct_smul, smul_eq_mul, hnn]
  ring
theorem reflectAcross_reflectAcross {n : AmbientSpace} (hnn : n ⬝ᵥ dualVector n = 1) (c c' : ℝ)
    (x : AmbientSpace) :
    reflectAcross n c' (reflectAcross n c x) = x + (2 * (c' - c)) • dualVector n := by
  have h : reflectAcross n c' (reflectAcross n c x) =
      reflectAcross n c x - (2 * (n ⬝ᵥ reflectAcross n c x - c')) • dualVector n := rfl
  rw [h, dotProduct_reflectAcross hnn]
  simp only [reflectAcross]
  module
theorem translateBy_reflectAcross_translateBy (n : AmbientSpace) (c : ℝ) (v x : AmbientSpace) :
    translateBy v (reflectAcross n c (translateBy (-v) x)) =
      reflectAcross n (c + n ⬝ᵥ v) x := by
  simp only [translateBy, reflectAcross, dotProduct_add, dotProduct_neg]
  module
theorem reflectAcross_mem_closedHalfSpace {n : AmbientSpace} (hnn : n ⬝ᵥ dualVector n = 1)
    {c : ℝ} {ε : ℤˣ} {x : AmbientSpace} (hx : x ∈ closedHalfSpace n c ε) :
    reflectAcross n c x ∈ closedHalfSpace n c (-ε) := by
  have hx' : 0 ≤ ((ε : ℤ) : ℝ) * (n ⬝ᵥ x - c) := hx
  change 0 ≤ (((-ε : ℤˣ) : ℤ) : ℝ) * (n ⬝ᵥ reflectAcross n c x - c)
  rw [dotProduct_reflectAcross hnn]
  push_cast
  linarith
theorem image_reflectAcross_closedHalfSpace {n : AmbientSpace} (hnn : n ⬝ᵥ dualVector n = 1)
    (c : ℝ) (ε : ℤˣ) : reflectAcross n c '' closedHalfSpace n c ε = closedHalfSpace n c (-ε) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact reflectAcross_mem_closedHalfSpace hnn hy
  · intro hx
    refine ⟨reflectAcross n c x, ?_, ?_⟩
    · simpa using reflectAcross_mem_closedHalfSpace hnn hx
    · rw [reflectAcross_reflectAcross hnn]
      simp
theorem two_mul_sub_smul_dualVector_mem {n : AmbientSpace} (hq : normSq n = 1 ∨ normSq n = 2)
    (hent : ∀ ρ, n ρ = 0 ∨ n ρ = 1 ∨ n ρ = -1) {c c' : ℝ} (hc : IsAllowedLevel 1 n c)
    (hc' : IsAllowedLevel 1 n c') : (2 * (c' - c)) • dualVector n ∈ latticeSubgroup 1 := by
  have hm : ∃ m : ℤ, 2 * (c' - c) * (normSq n)⁻¹ = (m : ℝ) := by
    rcases hq with hq | hq
    · obtain ⟨k, hk⟩ := hc.1 hq
      obtain ⟨k', hk'⟩ := hc'.1 hq
      refine ⟨k' - k, ?_⟩
      rw [hq, hk, hk']
      push_cast
      ring
    · obtain ⟨k, hk⟩ := hc.2 hq
      obtain ⟨k', hk'⟩ := hc'.2 hq
      refine ⟨k' - k, ?_⟩
      rw [hq, hk, hk']
      push_cast
      ring
  obtain ⟨m, hm⟩ := hm
  have hj : ∀ ρ, ∃ j : ℤ, n ρ = (j : ℝ) := fun ρ => by
    rcases hent ρ with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  choose j hj using hj
  change ∃ k : Fin 4 → ℤ, ∀ μ, ((2 * (c' - c)) • dualVector n) μ = (k μ : ℝ) * 1
  refine ⟨fun μ => m * j μ, fun μ => ?_⟩
  simp only [dualVector, Pi.smul_apply, smul_eq_mul, hj μ]
  rw [← mul_assoc, hm]
  push_cast
  ring
theorem isAllowedLevel_add_int {n : AmbientSpace} {c t : ℝ} (hc : IsAllowedLevel 1 n c)
    (ht : ∃ m : ℤ, t = (m : ℝ)) : IsAllowedLevel 1 n (c + t) := by
  obtain ⟨m, rfl⟩ := ht
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · obtain ⟨k, hk⟩ := hc.1 hq
    refine ⟨k + 2 * m, ?_⟩
    rw [hk]
    push_cast
    ring
  · obtain ⟨k, hk⟩ := hc.2 hq
    refine ⟨k + m, ?_⟩
    rw [hk]
    push_cast
    ring
theorem isBoundedObservable_conj {a : ℝ} {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (fun U => conj (F U)) := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.isBoundedObservable_conjFun <;> assumption
theorem conj_mem_regionObservables {a : ℝ} {S : Set AmbientSpace} {F : GaugeField a → ℂ}
    (hF : F ∈ regionObservables a S) : (fun U => conj (F U)) ∈ regionObservables a S := by
  refine ⟨isBoundedObservable_conj hF.1, ?_⟩
  have hm : Measurable[regionSigma S] F := hF.2
  exact Complex.continuous_conj.measurable.comp hm
section Action
variable (hSym : FieldSpace.SymmetryProperties)
include hSym
theorem actOn_comp (r r' : LatticeSymmetry 1) {F : GaugeField 1 → ℂ}
    (hF : IsBoundedObservable F) : (r.comp r').actOn F = r.actOn (r'.actOn F) :=
  (((hSym 1 one_pos).2.1 r r').2.2.1 F F hF hF).2.2.2.2.2
theorem isBoundedObservable_actOn (r : LatticeSymmetry 1) {F : GaugeField 1 → ℂ}
    (hF : IsBoundedObservable F) : IsBoundedObservable (r.actOn F) :=
  (((hSym 1 one_pos).2.1 r r).2.2.1 F F hF hF).1
theorem reflectObservable_reflectObservable (hProp : Properties.Statement)
    (P : NormalLevelPair 1) {F : GaugeField 1 → ℂ} (hF : IsBoundedObservable F) :
    P.reflectObservable (P.reflectObservable F) = F := by
  have hnn := (hProp.1.2.2.2 P.normal P.normal_mem).1
  have hid : (P.reflectSymmetry.comp P.reflectSymmetry).toFun = id := by
    funext x
    change reflectAcross P.normal P.level (reflectAcross P.normal P.level x) = x
    rw [reflectAcross_reflectAcross hnn]
    simp
  have h := actOn_comp hSym P.reflectSymmetry P.reflectSymmetry hF
  rw [actOn_eq_self_of_toFun_eq_id _ hid] at h
  exact h.symm
theorem conjReflect_conjReflect (hProp : Properties.Statement)
    (P : NormalLevelPair 1) {F : GaugeField 1 → ℂ} (hF : IsBoundedObservable F) :
    P.conjReflectObservable (P.conjReflectObservable F) = F := by
  funext U
  have h := congrFun (reflectObservable_reflectObservable hSym hProp P hF) U
  change conj (conj (P.reflectObservable (P.reflectObservable F) U)) = F U
  rw [h]
  simp
theorem isBoundedObservable_conjReflect (P : NormalLevelPair 1) {F : GaugeField 1 → ℂ}
    (hF : IsBoundedObservable F) : IsBoundedObservable (P.conjReflectObservable F) :=
  isBoundedObservable_conj (isBoundedObservable_actOn hSym P.reflectSymmetry hF)
theorem conjReflect_mem_halfSpaceObservables (hProp : Properties.Statement)
    (P : NormalLevelPair 1) (ε : ℤˣ) {F : GaugeField 1 → ℂ}
    (hF : F ∈ halfSpaceObservables 1 P.normal P.level ε) :
    P.conjReflectObservable F ∈ halfSpaceObservables 1 P.normal P.level (-ε) := by
  have hnn := (hProp.1.2.2.2 P.normal P.normal_mem).1
  have himg := ((hSym 1 one_pos).2.1 P.reflectSymmetry P.reflectSymmetry).2.2.2
    (closedHalfSpace P.normal P.level ε)
  have hS : P.reflectSymmetry.imageSet (closedHalfSpace P.normal P.level ε) =
      closedHalfSpace P.normal P.level (-ε) := image_reflectAcross_closedHalfSpace hnn P.level ε
  rw [hS] at himg
  have h : P.reflectSymmetry.actOn F ∈
      regionObservables 1 (closedHalfSpace P.normal P.level (-ε)) := by
    rw [← himg]
    exact ⟨F, hF, rfl⟩
  exact conj_mem_regionObservables h
theorem image_conjReflect_halfSpaceObservables (hProp : Properties.Statement)
    (P : NormalLevelPair 1) (ε : ℤˣ) :
    P.conjReflectObservable '' halfSpaceObservables 1 P.normal P.level ε =
      halfSpaceObservables 1 P.normal P.level (-ε) := by
  ext G
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact conjReflect_mem_halfSpaceObservables hSym hProp P ε hF
  · intro hG
    refine ⟨P.conjReflectObservable G, ?_, conjReflect_conjReflect hSym hProp P hG.1⟩
    simpa using conjReflect_mem_halfSpaceObservables hSym hProp P (-ε) hG
omit hSym in
theorem conjReflect_mem_continuousLocal (hElem : ElementaryLatticeFacts)
    (P : NormalLevelPair 1) {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1) :
    P.conjReflectObservable F ∈ continuousLocalFunctions 1 := by
  have hE := hElem 1 1 one_pos one_pos
  have hiso := (hE.2.2.2.2.2.2.2.1 P.reflectSymmetry P.reflectSymmetry).2.2.2.2.1
  have h : P.reflectSymmetry.actOn F ∈ continuousLocalFunctions 1 := by
    rw [← hiso]
    exact ⟨F, hF, rfl⟩
  exact hE.2.2.2.1.2.2.2.1 _ h
theorem image_conjReflect_halfSpaceContinuousLocal (hProp : Properties.Statement)
    (hElem : ElementaryLatticeFacts) (P : NormalLevelPair 1) (ε : ℤˣ) :
    P.conjReflectObservable '' halfSpaceContinuousLocal 1 P.normal P.level ε =
      halfSpaceContinuousLocal 1 P.normal P.level (-ε) := by
  ext G
  constructor
  · rintro ⟨F, ⟨hF, hF'⟩, rfl⟩
    exact ⟨conjReflect_mem_halfSpaceObservables hSym hProp P ε hF,
      conjReflect_mem_continuousLocal hElem P hF'⟩
  · rintro ⟨hG, hG'⟩
    refine ⟨P.conjReflectObservable G, ⟨?_, conjReflect_mem_continuousLocal hElem P hG'⟩,
      conjReflect_conjReflect hSym hProp P hG.1⟩
    simpa using conjReflect_mem_halfSpaceObservables hSym hProp P (-ε) hG
end Action
theorem holds (hProp : Properties.Statement) (hSym : FieldSpace.SymmetryProperties)
    (hElem : ElementaryLatticeFacts) : ReflectionIdentities.Statement := by
  intro n hn c c' hc hc' v P P'
  obtain ⟨hnn, -, hent, hint⟩ := hProp.1.2.2.2 n hn
  have hadm : IsAllowedLevel 1 n (c + n ⬝ᵥ (v : AmbientSpace)) :=
    isAllowedLevel_add_int hc (hint (v : AmbientSpace) v.2)
  let w : LatticePoint 1 := ⟨(2 * (c' - c)) • dualVector n,
    two_mul_sub_smul_dualVector_mem (normSq_eq_one_or_two hn) hent hc hc'⟩
  refine ⟨fun x => ?_, dotProduct_reflectAcross hnn c, fun x => ?_, fun x => ?_, fun F hF => ?_,
    ⟨w, rfl, ?_, fun F hF => ?_⟩, ⟨hadm, fun F hF => ?_⟩,
    fun F hF => isBoundedObservable_conjReflect hSym P hF, fun α F H _ _ => ?_, fun F H _ _ => ?_,
    fun F hF => conjReflect_conjReflect hSym hProp P hF,
    fun ε => image_conjReflect_halfSpaceObservables hSym hProp P ε,
    fun ε => image_conjReflect_halfSpaceContinuousLocal hSym hProp hElem P ε, fun F hF => ?_⟩
  · rw [reflectAcross_reflectAcross hnn]
    simp
  · rw [reflectAcross_reflectAcross hnn]
    rfl
  · exact translateBy_reflectAcross_translateBy n c (v : AmbientSpace) x
  · exact reflectObservable_reflectObservable hSym hProp P hF
  · change n ⬝ᵥ ((2 * (c' - c)) • dualVector n) = 2 * (c' - c)
    rw [dotProduct_smul, smul_eq_mul, hnn, mul_one]
  · have hr : P'.reflectSymmetry.comp P.reflectSymmetry = shift w := by
      apply symmetry_ext_of_toFun
      funext x
      exact reflectAcross_reflectAcross hnn c c' x
    have h := actOn_comp hSym P'.reflectSymmetry P.reflectSymmetry hF
    rw [hr] at h
    exact h.symm
  · have hr : (shift v).comp (P.reflectSymmetry.comp (shift (-v))) =
        (⟨n, hn, c + n ⬝ᵥ (v : AmbientSpace), hadm⟩ : NormalLevelPair 1).reflectSymmetry := by
      apply symmetry_ext_of_toFun
      funext x
      exact translateBy_reflectAcross_translateBy n c (v : AmbientSpace) x
    have h1 := actOn_comp hSym (shift v) (P.reflectSymmetry.comp (shift (-v))) hF
    have h2 := actOn_comp hSym P.reflectSymmetry (shift (-v)) hF
    rw [hr, h2] at h1
    exact h1.symm
  · funext U
    simp [NormalLevelPair.conjReflectObservable, NormalLevelPair.reflectObservable,
      LatticeSymmetry.actOn]
  · funext U
    simp [NormalLevelPair.conjReflectObservable, NormalLevelPair.reflectObservable,
      LatticeSymmetry.actOn]
  · have hF' : P.conjReflectObservable F ∈ halfSpaceObservables 1 n c 1 := by
      simpa using conjReflect_mem_halfSpaceObservables hSym hProp P (-1) hF
    refine ⟨hF', ?_⟩
    rw [conjReflect_conjReflect hSym hProp P hF.1]
end ReflectionIdentities
end YangMills.Construction.NormalFamilies
