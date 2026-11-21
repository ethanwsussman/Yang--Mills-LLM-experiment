import YangMills.Construction.ReflectionPositivity.CorrelationsOfTwoCubesProof
import YangMills.Construction.ReflectionPositivity.CorrelationsOfTwoLinkCubes
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField IsBoundedObservable IsShiftInvariant
  LatticePoint AmbientSpace axisStep shift halfSpaceLocalObservables unitRegionObservables
  regionSigma_mono)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (SymmetryActionAndReflections
  ActionRulesOn linkPlane linkReflect latticeSymmetry_ext unitPositiveClass basisVec)
namespace LinkBlockCorrelations
theorem linkReflect_coord (μ k : Fin 4) (x : AmbientSpace) :
    (linkReflect μ).toFun x k = if k = μ then -x μ - 1 else x k := by
  rw [MirrorHyperplanes.linkReflect_apply]
  by_cases h : k = μ
  · subst h
    simp only [Pi.sub_apply, Pi.smul_apply, basisVec, Pi.single_eq_same, smul_eq_mul, mul_one,
      if_true]
    ring
  · simp [basisVec, h]
theorem linkReflect_linkReflect (μ : Fin 4) (x : AmbientSpace) :
    (linkReflect μ).toFun ((linkReflect μ).toFun x) = x := by
  funext k
  rw [linkReflect_coord, linkReflect_coord μ μ]
  by_cases h : k = μ
  · subst h
    simp
  · simp [h, linkReflect_coord]
theorem imageSet_linkReflect_linkBlock (r : ℕ+) (μ : Fin 4) :
    (linkReflect μ).setImage (linkBlock r) = linkBlock r := by
  have key : ∀ x ∈ linkBlock r, (linkReflect μ).toFun x ∈ linkBlock r := by
    intro x hx k
    rw [linkReflect_coord]
    split_ifs with h
    · subst h
      have := hx k
      exact ⟨by linarith [this.2], by linarith [this.1]⟩
    · exact hx k
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact key z hz
  · exact fun hx => ⟨_, key x hx, linkReflect_linkReflect μ x⟩
theorem isBoundedObservable_conj_mul {F G : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) : IsBoundedObservable fun U => conj (F U) * G U := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound.isBoundedObservable_conj_mul <;> assumption
theorem isBoundedObservable_of_mem {R : Set AmbientSpace} {F : GaugeField (1 : ℝ) → ℂ}
    (h : F ∈ unitRegionObservables R) : IsBoundedObservable F :=
  h.1
theorem shift_mem_halfSpace (hAction : SymmetryActionAndReflections) (r : ℕ+)
    (μ : Fin 4) {F : GaugeField (1 : ℝ) → ℂ} (h : F ∈ unitRegionObservables (linkBlock r)) :
    (shift ((r : ℕ) • axisStep 1 μ)).actOn F ∈ halfSpaceLocalObservables μ := by
  have hmem : (shift ((r : ℕ) • axisStep 1 μ)).actOn F ∈
      unitRegionObservables ((shift ((r : ℕ) • axisStep 1 μ)).setImage (linkBlock r)) := by
    rw [← hAction.2.1]
    exact ⟨F, h, rfl⟩
  refine (InfiniteLattice.mem_halfSpaceLocalObservables_iff μ _).mpr ⟨⟨hmem.1, ?_⟩, _,
    isBounded_imageSet_shift_linkBlock r μ, hmem.2⟩
  exact Measurable.mono hmem.2 (regionSigma_mono (imageSet_shift_linkBlock_subset r μ)) le_rfl
theorem isBoundedObservable_actOn (hAction : SymmetryActionAndReflections)
    (g : InfiniteLattice.UnitLatticeSymmetry) {F : GaugeField (1 : ℝ) → ℂ}
    (hF : IsBoundedObservable F) : IsBoundedObservable (g.actOn F) := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound.isBoundedObservable_actOn <;> assumption
theorem actOn_comp (hAction : SymmetryActionAndReflections)
    (g g' : InfiniteLattice.UnitLatticeSymmetry) {F : GaugeField (1 : ℝ) → ℂ}
    (hF : IsBoundedObservable F) :
    (g.comp g').actOn F = g.actOn (g'.actOn F) := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.CubeCorrelations.actOn_comp <;> assumption
theorem actOn_shift_add (hAction : SymmetryActionAndReflections)
    (v w : LatticePoint (1 : ℝ)) {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F) :
    (shift (v + w)).actOn F = (shift v).actOn ((shift w).actOn F) := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.CubeCorrelations.actOn_shift_add <;> assumption
theorem coe_nsmul_axisStep_apply (m : ℕ) (μ k : Fin 4) :
    ((m • axisStep (1 : ℝ) μ : LatticePoint (1 : ℝ)) : AmbientSpace) k =
      if k = μ then (m : ℝ) else 0 := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.CubeCorrelations.coe_nsmul_axisStep_apply <;> assumption
theorem linkReflect_shift_linkReflect (hAction : SymmetryActionAndReflections) (r : ℕ+)
    (μ : Fin 4) {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F) :
    (linkReflect μ).actOn ((shift ((r : ℕ) • axisStep 1 μ)).actOn ((linkReflect μ).actOn F)) =
      (shift (-((r : ℕ) • axisStep 1 μ))).actOn F := by
  have hθF := isBoundedObservable_actOn hAction (linkReflect μ) hF
  have hrel : (linkReflect μ).comp (shift ((r : ℕ) • axisStep 1 μ)) =
      (shift (-((r : ℕ) • axisStep 1 μ))).comp (linkReflect μ) := by
    obtain ⟨-, -, -, -, -, -, -, -, hRefl, -⟩ := hAction
    obtain ⟨-, -, -, -, -, -, -, hk⟩ := hRefl (linkPlane μ)
    have h := hk (-(r : ℤ)) (-((r : ℕ) • axisStep 1 μ)) (by
      funext k
      change -(((r : ℕ) • axisStep (1 : ℝ) μ : LatticePoint (1 : ℝ)) : AmbientSpace) k =
        ((-(r : ℤ) : ℤ) : ℝ) * basisVec μ k
      rw [coe_nsmul_axisStep_apply]
      by_cases hk' : k = μ
      · subst hk'
        simp [basisVec]
      · simp [basisVec, hk'])
    rw [neg_neg] at h
    exact h
  have hinv : (linkReflect μ).IsInverse (linkReflect μ) :=
    ⟨linkReflect_linkReflect μ, linkReflect_linkReflect μ⟩
  obtain ⟨-, -, -, -, -, hRules, -⟩ := id hAction
  rw [← actOn_comp hAction _ _ hθF, hrel, actOn_comp hAction _ _ hθF]
  rw [(hRules (linkReflect μ) (linkReflect μ) F F hF hF).2.1 _ hinv]
theorem shift_decomposition (r : ℕ+) (μ : Fin 4) (y : Fin 4 → ℤ) (hy : 2 * (r : ℤ) ≤ y μ) :
    (y μ - 2 * (r : ℤ)).toNat • axisStep 1 μ + intPoint (transversePart μ y) +
        (r : ℕ) • axisStep 1 μ =
      -((r : ℕ) • axisStep 1 μ) + intPoint y := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.CubeCorrelations.shifted_point_sum <;> assumption
theorem shift_shift_neg (hAction : SymmetryActionAndReflections)
    (y : Fin 4 → ℤ) {G : GaugeField (1 : ℝ) → ℂ} (hG : IsBoundedObservable G) :
    (shift (intPoint y)).actOn ((shift (intPoint (-y))).actOn G) = G := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.CubeCorrelations.shift_actOn_shift_neg <;> assumption
end LinkBlockCorrelations
open LinkBlockCorrelations in
theorem linkBlockCorrelationTheorem_holds (hAction : SymmetryActionAndReflections)
    (hMatrix : MatrixElementsEqCorrelations) (hPairs : ReflectionPairTheorem) :
    LinkBlockCorrelationTheorem := by
  intro ν r A B hA hB y
  have hobsA : IsBoundedObservable A := isBoundedObservable_of_mem hA
  have hobsB : IsBoundedObservable B := isBoundedObservable_of_mem hB
  have htr : IsShiftInvariant (ν : Measure (GaugeField (1 : ℝ))) := ν.2.2.1
  have hreflected : ∀ μ : Fin 4, (linkReflect μ).actOn A ∈
      unitRegionObservables (linkBlock r) := fun μ => by
    rw [← imageSet_linkReflect_linkBlock r μ, ← hAction.2.1]
    exact ⟨A, hA, rfl⟩
  refine ⟨fun μ => ⟨imageSet_linkReflect_linkBlock r μ, hreflected μ,
    imageSet_shift_linkBlock_subset r μ, shift_mem_halfSpace hAction r μ hA, ?_⟩,
    fun μ hy => ?_, ?_⟩
  · have h1 := (hPairs ν μ ReflectionPair.link).1.2.2 _ (shift_mem_halfSpace hAction r μ hA)
    obtain ⟨-, -, -, -, hNorm, -⟩ := hAction
    exact h1.trans (hNorm _ A hobsA).2.1.le
  · have hw : transversePart μ y μ = 0 := by simp [transversePart]
    have hm := (hMatrix ν μ _ (shift_mem_halfSpace hAction r μ (hreflected μ)) _
      (shift_mem_halfSpace hAction r μ hB) (y μ - 2 * (r : ℤ)).toNat
      (transversePart μ y) hw).1
    refine Eq.trans ?_ hm.symm
    rw [linkReflect_shift_linkReflect hAction r μ hobsA,
      ← actOn_shift_add hAction _ _ hobsB, shift_decomposition r μ y hy,
      actOn_shift_add hAction _ _ hobsB]
    exact (htr (-((r : ℕ) • axisStep 1 μ)) _ (isBoundedObservable_conj_mul hobsA
      (isBoundedObservable_actOn hAction _ hobsB))).symm
  · have hinv := htr (intPoint y) _ (isBoundedObservable_conj_mul hobsA
      (isBoundedObservable_actOn hAction (shift (intPoint (-y))) hobsB))
    have hback := shift_shift_neg hAction y hobsB
    unfold blockCorrelation
    rw [← hinv, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    have hU := congrFun hback U
    change conj (A _) * (shift (intPoint y)).actOn ((shift (intPoint (-y))).actOn B) U = _
    rw [hU]
    change _ = conj (conj (B U) * (shift (intPoint y)).actOn A U)
    rw [map_mul, Complex.conj_conj, mul_comm]
    rfl
end YangMills.Construction.ReflectionPositivity.DirectionPictures
