import YangMills.Construction.InfiniteLattice.ReconstructionAtALatticeMirrorProof
import YangMills.Construction.InfiniteLattice.ReflectionPositivityDoesNotDependOnTheSide
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.LatticeConventions.MirrorSideIndependence
open InfiniteLattice (GaugeField IsBoundedObservable LatticeSymmetry localRegionObservables)
open NormalHyperplane
variable (hSym : InfiniteLattice.SymmetryActionOnObservables)
  (hRefl : MirrorReflections.MirrorReflectionsStatement)
theorem isBoundedObservable_of_mem_localRegion {b : ℝ} {R : Set InfiniteLattice.AmbientSpace}
    {f : GaugeField b → ℂ} (hf : f ∈ localRegionObservables b R) : IsBoundedObservable f := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.isBoundedObservable_of_mem_local <;> assumption
include hSym hRefl in
theorem actOn_actOn_reflect {a : Spacing} {H : NormalHyperplane}
    (hH : H.IsLatticeMirror (a : ℝ)) {f : GaugeField (a : ℝ) → ℂ} (hf : IsBoundedObservable f) :
    (reflectSymmetry hH).actOn ((reflectSymmetry hH).actOn f) = f := by
  have hinv : H.reflect ∘ H.reflect = id := ((hRefl a).2.2.2.2.1 H).1.2.1
  have hleft : Function.LeftInverse (reflectSymmetry hH).toFun (reflectSymmetry hH).toFun :=
    fun x => congrFun hinv x
  have hact := (hSym a).2.2.2.2.2.2.2.2.2.1 (reflectSymmetry hH)
  exact ((hact.2.2 (reflectSymmetry hH) ⟨hleft, hleft⟩).1 f hf).1
include hSym hRefl in
theorem image_lowerHalfSpace {a : Spacing} {H : NormalHyperplane}
    (hH : H.IsLatticeMirror (a : ℝ)) :
    (fun f : GaugeField (a : ℝ) → ℂ => (reflectSymmetry hH).actOn f) ''
        localRegionObservables (a : ℝ) H.lowerHalfSpace =
      localRegionObservables (a : ℝ) H.upperHalfSpace := by
  have hset : (reflectSymmetry hH).setImage H.lowerHalfSpace = H.upperHalfSpace :=
    ((hRefl a).1 H).1.2.2
  have h := (hSym a).2.2.2.2.2.2.2.2.1.1 (reflectSymmetry hH) H.lowerHalfSpace
  rwa [hset] at h
include hSym hRefl in
theorem reflectBijOnHalfSpaces {a : Spacing} {H : NormalHyperplane}
    (hH : H.IsLatticeMirror (a : ℝ)) : ReflectBijOnHalfSpaces hH := by
  have himg := image_lowerHalfSpace hSym hRefl hH
  refine ⟨fun f hf => ?_, fun f hf g hg h => ?_, fun f hf => ?_⟩
  · rw [← himg]
    exact ⟨f, hf, rfl⟩
  · have h' : (reflectSymmetry hH).actOn f = (reflectSymmetry hH).actOn g := h
    rw [← actOn_actOn_reflect hSym hRefl hH (isBoundedObservable_of_mem_localRegion hf),
      ← actOn_actOn_reflect hSym hRefl hH (isBoundedObservable_of_mem_localRegion hg), h']
  · rw [← himg] at hf
    exact hf
include hSym hRefl in
theorem reflectedPairing_eq_conj {a : Spacing} {H : NormalHyperplane}
    (hH : H.IsLatticeMirror (a : ℝ)) (ν : Measure (GaugeField (a : ℝ)))
    {f : GaugeField (a : ℝ) → ℂ} (hf : IsBoundedObservable f) :
    reflectedPairing hH ν f =
      (starRingEnd ℂ) (reflectedPairing hH ν ((reflectSymmetry hH).actOn f)) := by
  unfold reflectedPairing
  rw [actOn_actOn_reflect hSym hRefl hH hf, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [conjFun, map_mul, Complex.conj_conj]
  exact mul_comm _ _
include hSym hRefl in
theorem isReflectionPositiveAcrossMirror_iff_isLowerPositive {a : Spacing} {H : NormalHyperplane}
    (hH : H.IsLatticeMirror (a : ℝ)) (ν : Measure (GaugeField (a : ℝ)))
    [IsProbabilityMeasure ν] :
    IsReflectionPositiveAcrossMirror hH ν ↔ IsLowerPositive hH ν := by
  have hbij := reflectBijOnHalfSpaces hSym hRefl hH
  constructor
  · intro h f hf
    have hp := h ⟨_, hbij.1 hf⟩
    rw [reflectionForm_self_eq_reflectedPairing] at hp
    rw [reflectedPairing_eq_conj hSym hRefl hH ν (isBoundedObservable_of_mem_localRegion hf)]
    simpa using hp
  · rintro h ⟨f', hf'⟩
    obtain ⟨f, hf, rfl⟩ := hbij.2.2 hf'
    have hp := h f hf
    rw [reflectedPairing_eq_conj hSym hRefl hH ν (isBoundedObservable_of_mem_localRegion hf)] at hp
    rw [reflectionForm_self_eq_reflectedPairing]
    simpa using hp
theorem latticeSymmetry_ext {b : ℝ} {r s : LatticeSymmetry b} (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem isReflectionPositiveAcrossMirror_iff_of_swapped {a : Spacing} {H H' : NormalHyperplane}
    (hH : H.IsLatticeMirror (a : ℝ)) (hH' : H'.IsLatticeMirror (a : ℝ))
    (hr : H'.reflect = H.reflect) (hs : H'.upperHalfSpace = H.lowerHalfSpace)
    (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν] :
    IsReflectionPositiveAcrossMirror hH' ν ↔ IsLowerPositive hH ν := by
  have hθ : reflectSymmetry hH' = reflectSymmetry hH := latticeSymmetry_ext hr
  have hpair : ∀ f : GaugeField (a : ℝ) → ℂ, reflectedPairing hH' ν f = reflectedPairing hH ν f := by
    intro f
    unfold reflectedPairing
    rw [hθ]
  constructor
  · intro h f hf
    have hf' : f ∈ localRegionObservables (a : ℝ) H'.upperHalfSpace := by
      rw [hs]
      exact hf
    have hp := h ⟨f, hf'⟩
    rw [reflectionForm_self_eq_reflectedPairing] at hp
    rwa [hpair] at hp
  · rintro h ⟨f, hf⟩
    rw [hs] at hf
    rw [reflectionForm_self_eq_reflectedPairing]
    show (reflectedPairing hH' ν f).im = 0 ∧ 0 ≤ (reflectedPairing hH' ν f).re
    rw [hpair]
    exact h f hf
include hSym hRefl in
theorem isReflectionPositiveAcrossMirror_iff_of_carrier_eq {a : Spacing} {H H' : NormalHyperplane}
    (hH : H.IsLatticeMirror (a : ℝ)) (hH' : H'.IsLatticeMirror (a : ℝ))
    (hcar : H.carrier = H'.carrier) (ν : Measure (GaugeField (a : ℝ)))
    [IsProbabilityMeasure ν] :
    IsReflectionPositiveAcrossMirror hH ν ↔ IsReflectionPositiveAcrossMirror hH' ν := by
  by_cases hsame : (H'.normal, H'.level) = (H.normal, H.level)
  · obtain ⟨e, c, he⟩ := H
    obtain ⟨e', c', he'⟩ := H'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hsame
    exact Iff.rfl
  · obtain ⟨hr, -, -, hs, -⟩ := ((hRefl a).2.2.2.2.2 H H' hsame).2 hcar.symm
    exact (isReflectionPositiveAcrossMirror_iff_isLowerPositive hSym hRefl hH ν).trans
      (isReflectionPositiveAcrossMirror_iff_of_swapped hH hH' hr hs ν).symm
theorem antidiagonal_carrier_eq {μ κ : Direction} (hne : μ ≠ κ) (c : ℝ) :
    (antidiagonal μ κ hne c).carrier = (antidiagonal κ μ hne.symm (-c)).carrier := by
  have hdot : ∀ x : Point, euclidDot (basisVector μ - basisVector κ) x =
      -euclidDot (basisVector κ - basisVector μ) x := by
    intro x
    simp only [euclidDot, Pi.sub_apply, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  ext x
  show euclidDot (basisVector μ - basisVector κ) x = c ↔
    euclidDot (basisVector κ - basisVector μ) x = -c
  rw [hdot x]
  constructor <;> intro h <;> linarith
theorem holds (hSym : InfiniteLattice.SymmetryActionOnObservables)
    (hRefl : MirrorReflections.MirrorReflectionsStatement) : Statement := by
  intro a
  refine ⟨fun H hH => ⟨reflectBijOnHalfSpaces hSym hRefl hH, fun ν _ =>
      ⟨fun f hf => reflectedPairing_eq_conj hSym hRefl hH ν (isBoundedObservable_of_mem_localRegion hf),
        isReflectionPositiveAcrossMirror_iff_isLowerPositive hSym hRefl hH ν⟩⟩, ?_,
    fun H H' hH hH' hcar ν _ =>
      isReflectionPositiveAcrossMirror_iff_of_carrier_eq hSym hRefl hH hH' hcar ν⟩
  rintro μ κ hne c ⟨k, rfl⟩
  have h₁ : (antidiagonal μ κ hne ((k : ℝ) * (a : ℝ))).IsLatticeMirror (a : ℝ) :=
    antidiagonal_isLatticeMirror hne k
  have h₂ : (antidiagonal κ μ hne.symm (-((k : ℝ) * (a : ℝ)))).IsLatticeMirror (a : ℝ) := by
    have h := antidiagonal_isLatticeMirror (a := (a : ℝ)) hne.symm (-k)
    rwa [Int.cast_neg, neg_mul] at h
  exact ⟨h₁, h₂, fun ν _ => isReflectionPositiveAcrossMirror_iff_of_carrier_eq hSym hRefl h₁ h₂
    (antidiagonal_carrier_eq hne _) ν⟩
end YangMills.Construction.LatticeConventions.MirrorSideIndependence
end
