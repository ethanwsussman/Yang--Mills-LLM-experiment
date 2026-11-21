import YangMills.Construction.ReflectionPositiveLimits.LimitsOfLatticeStatesProof
import YangMills.Construction.ReflectionPositivity.BoundedMomentumDensityWithReflectionSizesProof
import YangMills.Construction.ReflectionPositivity.CorrelationsOfTwoCubes
import YangMills.Construction.ReflectionPositivity.MatrixElementsAreCorrelations
import YangMills.Construction.ReflectionPositivity.SignChangesAndTheCube
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open InfiniteLattice (GaugeField IsBoundedObservable IsShiftInvariant LatticePoint AmbientSpace
  axisStep shift unitRegionObservables)
open MirrorHyperplanes (SymmetryActionAndReflections ActionRulesOn sitePlane siteReflect
  latticeSymmetry_ext unitPositiveClass basisVec)
namespace CubeCorrelations
theorem imageSet_siteReflect_cubeOfRadius (r : ℕ+) (μ : Fin 4) :
    (siteReflect μ).setImage (cubeOfRadius r) = cubeOfRadius r := by
  have hmem : ∀ x ∈ cubeOfRadius r, (siteReflect μ).toFun x ∈ cubeOfRadius r := by
    intro x hx l
    rw [siteReflect_coord]
    have hxl := hx l
    split_ifs with h
    · exact ⟨by linarith [hxl.2], by linarith [hxl.1]⟩
    · simpa using hxl
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hmem z hz
  · exact fun hx => ⟨_, hmem x hx, siteReflect_involutive μ x⟩
theorem isBoundedObservable_conj_mul {F G : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) : IsBoundedObservable fun U => conj (F U) * G U := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound.isBoundedObservable_conj_mul <;> assumption
theorem isBoundedObservable_actOn (hSym : SymmetryActionAndReflections)
    (g : InfiniteLattice.UnitLatticeSymmetry) {F : GaugeField (1 : ℝ) → ℂ}
    (hF : IsBoundedObservable F) : IsBoundedObservable (g.actOn F) := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound.isBoundedObservable_actOn <;> assumption
theorem actOn_comp (hSym : SymmetryActionAndReflections)
    (g g' : InfiniteLattice.UnitLatticeSymmetry) {F : GaugeField (1 : ℝ) → ℂ}
    (hF : IsBoundedObservable F) :
    (g.comp g').actOn F = g.actOn (g'.actOn F) := by
  obtain ⟨-, -, -, -, -, hRules, -⟩ := hSym
  exact (hRules g g' F F hF hF).1
theorem actOn_shift_add (hSym : SymmetryActionAndReflections)
    (v w : LatticePoint (1 : ℝ)) {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F) :
    (shift (v + w)).actOn F = (shift v).actOn ((shift w).actOn F) := by
  have hc : shift (v + w) = (shift v).comp (shift w) := by
    apply latticeSymmetry_ext
    funext x
    change x + ((v : AmbientSpace) + (w : AmbientSpace)) = x + (w : AmbientSpace) + (v : AmbientSpace)
    abel
  rw [hc]
  exact actOn_comp hSym _ _ hF
theorem coe_nsmul_axisStep_apply (k : ℕ) (μ l : Fin 4) :
    ((k • axisStep (1 : ℝ) μ : LatticePoint (1 : ℝ)) : AmbientSpace) l =
      if l = μ then (k : ℝ) else 0 := by
  by_cases h : l = μ
  · subst h
    simp [axisStep]
  · simp [axisStep, h]
theorem siteReflect_actOn_actOn (hSym : SymmetryActionAndReflections)
    (μ : Fin 4) {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F) :
    (siteReflect μ).actOn ((siteReflect μ).actOn F) = F := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound.actOn_siteReflect_involutive <;> assumption
theorem siteReflect_shift_siteReflect (hSym : SymmetryActionAndReflections) (r : ℕ+)
    (μ : Fin 4) {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F) :
    (siteReflect μ).actOn ((shift ((r : ℕ) • axisStep 1 μ)).actOn
        ((siteReflect μ).actOn F)) =
      (shift (-((r : ℕ) • axisStep 1 μ))).actOn F := by
  have hθF := isBoundedObservable_actOn hSym (siteReflect μ) hF
  have hrel : (siteReflect μ).comp (shift ((r : ℕ) • axisStep 1 μ)) =
      (shift (-((r : ℕ) • axisStep 1 μ))).comp (siteReflect μ) := by
    obtain ⟨-, -, -, -, -, -, -, -, hRefl, -⟩ := hSym
    obtain ⟨-, -, -, -, -, -, -, hk⟩ := hRefl (sitePlane μ)
    have h := hk (-(r : ℤ)) (-((r : ℕ) • axisStep 1 μ)) (by
      funext l
      change -(((r : ℕ) • axisStep (1 : ℝ) μ : LatticePoint (1 : ℝ)) : AmbientSpace) l =
        ((-(r : ℤ) : ℤ) : ℝ) * basisVec μ l
      rw [coe_nsmul_axisStep_apply]
      by_cases hl : l = μ
      · subst hl
        simp [basisVec]
      · simp [basisVec, hl])
    rw [neg_neg] at h
    exact h
  rw [← actOn_comp hSym _ _ hθF, hrel, actOn_comp hSym _ _ hθF,
    siteReflect_actOn_actOn hSym μ hF]
theorem shifted_point_sum (r : ℕ+) (μ : Fin 4) (y : Fin 4 → ℤ) (hy : 2 * (r : ℤ) ≤ y μ) :
    (y μ - 2 * (r : ℤ)).toNat • axisStep 1 μ + intPoint (y - y μ • Pi.single μ 1) +
        (r : ℕ) • axisStep 1 μ =
      -((r : ℕ) • axisStep 1 μ) + intPoint y := by
  have hk : (((y μ - 2 * (r : ℤ)).toNat : ℕ) : ℝ) = (y μ : ℝ) - 2 * ((r : ℕ) : ℝ) := by
    have h : (((y μ - 2 * (r : ℤ)).toNat : ℕ) : ℤ) = y μ - 2 * (r : ℤ) :=
      Int.toNat_of_nonneg (by omega)
    have h' : ((((y μ - 2 * (r : ℤ)).toNat : ℕ) : ℤ) : ℝ) = ((y μ - 2 * (r : ℤ) : ℤ) : ℝ) := by
      rw [h]
    push_cast at h'
    exact h'
  apply Subtype.ext
  funext l
  change ((((y μ - 2 * (r : ℤ)).toNat • axisStep (1 : ℝ) μ : LatticePoint (1 : ℝ)) : AmbientSpace) l +
      (((y - y μ • Pi.single μ 1 : Fin 4 → ℤ) l : ℤ) : ℝ)) +
        (((r : ℕ) • axisStep (1 : ℝ) μ : LatticePoint (1 : ℝ)) : AmbientSpace) l =
    -(((r : ℕ) • axisStep (1 : ℝ) μ : LatticePoint (1 : ℝ)) : AmbientSpace) l + (y l : ℝ)
  rw [coe_nsmul_axisStep_apply, coe_nsmul_axisStep_apply]
  by_cases hl : l = μ
  · subst hl
    simp only [if_true, hk, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      sub_self, Int.cast_zero]
    ring
  · simp [hl]
theorem intPoint_two_mul_single (r : ℕ+) (μ : Fin 4) :
    intPoint ((2 * (r : ℤ)) • Pi.single μ 1) = (2 * (r : ℕ)) • axisStep (1 : ℝ) μ := by
  apply Subtype.ext
  funext l
  change ((((2 * (r : ℤ)) • (Pi.single μ 1 : Fin 4 → ℤ)) l : ℤ) : ℝ) =
    (((2 * (r : ℕ)) • axisStep (1 : ℝ) μ : LatticePoint (1 : ℝ)) : AmbientSpace) l
  rw [coe_nsmul_axisStep_apply]
  by_cases hl : l = μ
  · subst hl
    simp
  · simp [hl]
theorem unitaryMonomial_zero {𝒦 : Type*} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦]
    [CompleteSpace 𝒦] {J : Type*} [Fintype J] [Nonempty J]
    (S : JointSpectrum.CommutingFamily 𝒦 J) :
    S.unitaryMonomial (fun _ => 0) = 1 := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeLimits.unitaryMonomial_zero <;> assumption
theorem shift_actOn_shift_neg (hSym : SymmetryActionAndReflections)
    (y : Fin 4 → ℤ) {G : GaugeField (1 : ℝ) → ℂ} (hG : IsBoundedObservable G) :
    (shift (intPoint y)).actOn ((shift (intPoint (-y))).actOn G) = G := by
  obtain ⟨-, -, -, -, -, hRules, -⟩ := hSym
  have hinv : (shift (intPoint y)).IsInverse (shift (intPoint (-y))) := by
    constructor
    · intro x
      funext l
      change x l + ((-y l : ℤ) : ℝ) + (y l : ℝ) = x l
      push_cast
      ring
    · intro x
      funext l
      change x l + (y l : ℝ) + ((-y l : ℤ) : ℝ) = x l
      push_cast
      ring
  exact (hRules (shift (intPoint (-y))) (shift (intPoint (-y))) G G hG hG).2.1 _ hinv
end CubeCorrelations
open CubeCorrelations in
theorem cubeCorrelationsTheorem_of (hSym : SymmetryActionAndReflections)
    (hMatrix : MatrixElementsEqCorrelations) (hSign : SignFlipsPreserveCube) :
    CubeCorrelationsTheorem := by
  intro ν μ r
  have hshift : IsShiftInvariant (ν : Measure (GaugeField (1 : ℝ))) := ν.2.2.1
  have hhalf : ∀ F ∈ unitRegionObservables (cubeOfRadius r),
      (shift ((r : ℕ) • axisStep (1 : ℝ) μ)).actOn F ∈
        InfiniteLattice.halfSpaceLocalObservables μ :=
    fun F hF => ((hSign ν μ r).2.2.2.2.2 F hF).2.1
  have hrefl : ∀ F ∈ unitRegionObservables (cubeOfRadius r),
      (siteReflect μ).actOn F ∈ unitRegionObservables (cubeOfRadius r) := fun F hF => by
    rw [← imageSet_siteReflect_cubeOfRadius r μ, ← hSym.2.1]
    exact ⟨F, hF, rfl⟩
  have hfirst : ∀ F ∈ unitRegionObservables (cubeOfRadius r),
      ∀ G ∈ unitRegionObservables (cubeOfRadius r),
      ∀ y : Fin 4 → ℤ, 2 * (r : ℤ) ≤ y μ →
        ∫ U, conj (F U) * (shift (intPoint y)).actOn G U
            ∂(ν : Measure (GaugeField (1 : ℝ))) =
          inner ℂ (cubeVector ν μ r ((siteReflect μ).actOn F))
            ((ReflectionPair.site.transferOp ν μ ^ (y μ - 2 * (r : ℤ)).toNat *
              ReflectionPair.site.shiftMonomial ν μ (y - y μ • Pi.single μ 1))
              (cubeVector ν μ r G)) := by
    intro F hF G hG y hy
    have hobsF : IsBoundedObservable F := hF.1
    have hobsG : IsBoundedObservable G := hG.1
    have hw : (y - y μ • Pi.single μ 1 : Fin 4 → ℤ) μ = 0 := by simp
    have hm := (hMatrix ν μ _ (hhalf _ (hrefl F hF)) _ (hhalf G hG)
      (y μ - 2 * (r : ℤ)).toNat (y - y μ • Pi.single μ 1) hw).2
    refine Eq.trans ?_ hm.symm
    rw [siteReflect_shift_siteReflect hSym r μ hobsF,
      ← actOn_shift_add hSym _ _ hobsG, shifted_point_sum r μ y hy,
      actOn_shift_add hSym _ _ hobsG]
    exact (hshift (-((r : ℕ) • axisStep 1 μ)) _ (isBoundedObservable_conj_mul hobsF
      (isBoundedObservable_actOn hSym _ hobsG))).symm
  refine ⟨hfirst, ?_, ?_⟩
  · intro F hF G hG y
    have hobsF : IsBoundedObservable F := hF.1
    have hobsG : IsBoundedObservable G := hG.1
    have hinv := hshift (intPoint y) _ (isBoundedObservable_conj_mul hobsF
      (isBoundedObservable_actOn hSym (shift (intPoint (-y))) hobsG))
    have hback := shift_actOn_shift_neg hSym y hobsG
    rw [← hinv, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    have hU := congrFun hback U
    change conj (F _) * (shift (intPoint y)).actOn
      ((shift (intPoint (-y))).actOn G) U = _
    rw [hU]
    change _ = conj (conj (G U) * (shift (intPoint y)).actOn F U)
    rw [map_mul, Complex.conj_conj, mul_comm]
    rfl
  · intro F hF
    have hy : (((2 * (r : ℤ)) • Pi.single μ 1 : Fin 4 → ℤ)) μ = 2 * (r : ℤ) := by simp
    have h := hfirst _ (hrefl F hF) F hF ((2 * (r : ℤ)) • Pi.single μ 1) hy.ge
    have hU : ReflectionPair.site.shiftMonomial ν μ 0 = 1 := unitaryMonomial_zero _
    rw [intPoint_two_mul_single, siteReflect_actOn_actOn hSym μ hF.1, hy, sub_self,
      Int.toNat_zero, pow_zero, one_mul, sub_self, hU] at h
    rw [h, one_apply_eq_self, inner_self_eq_norm_sq_to_K]
    norm_cast
end YangMills.Construction.ReflectionPositivity.DirectionPictures
