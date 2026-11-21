import YangMills.Construction.Torus.BallOfTheTorusAndTheBallOverItProof
import YangMills.Construction.Torus.CellsOfATranslatedLatticeAndBallsOfTheTorusProof
import YangMills.Construction.ReflectionPositivity.ReflectionOfAMirrorOfOneTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.TorusMirrors.AxisReflection
variable (s : Conventions.StandingParameters) (M : AxisLevel)
def flipCoord (μ : Fin 4) (v : Fin 4 → ℝ) : Fin 4 → ℝ := Function.update v μ (-(v μ))
theorem flipCoord_flipCoord (μ : Fin 4) (v : Fin 4 → ℝ) :
    flipCoord μ (flipCoord μ v) = v := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [flipCoord]
  · simp [flipCoord, Function.update_of_ne h]
theorem euclidNormVec_flipCoord (μ : Fin 4) (v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (flipCoord μ v) = TorusMetric.euclidNormVec v := by
  simp only [TorusMetric.euclidNormVec]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases h : ν = μ
  · subst h
    simp [flipCoord]
  · simp [flipCoord, Function.update_of_ne h]
theorem proj_sub (y w : Fin 4 → ℝ) :
    TorusCutoffs.proj s (y - w) = TorusCutoffs.proj s y - TorusCutoffs.proj s w := by apply _root_.YangMills.Construction.TorusMeasure.BallProjection.proj_map_sub <;> assumption
theorem proj_flipCoord (μ : Fin 4) {u v : Fin 4 → ℝ}
    (h : TorusCutoffs.proj s u = TorusCutoffs.proj s v) :
    TorusCutoffs.proj s (flipCoord μ u) = TorusCutoffs.proj s (flipCoord μ v) := by
  funext ν
  change ((flipCoord μ u ν : ℝ) : AddCircle (PeriodicLattice.torusSide s.L s.m)) =
    ((flipCoord μ v ν : ℝ) : AddCircle (PeriodicLattice.torusSide s.L s.m))
  have hν : ((u ν : ℝ) : AddCircle (PeriodicLattice.torusSide s.L s.m)) = ((v ν : ℝ) : _) :=
    congrFun h ν
  by_cases e : ν = μ
  · subst e
    simp only [flipCoord, Function.update_self, AddCircle.coe_neg, hν]
  · simpa only [flipCoord, Function.update_of_ne e] using hν
theorem torusEuclidNorm_proj_flipCoord (μ : Fin 4) (v : Fin 4 → ℝ) :
    TorusMetric.torusEuclidNorm (S := PeriodicLattice.torusSide s.L s.m)
        (TorusCutoffs.proj s (flipCoord μ v)) =
      TorusMetric.torusEuclidNorm (S := PeriodicLattice.torusSide s.L s.m)
        (TorusCutoffs.proj s v) := by
  have key : ∀ w : Fin 4 → ℝ,
      TorusMetric.euclidNormVec ''
          (TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) ⁻¹'
            {TorusCutoffs.proj s w}) ⊆
        TorusMetric.euclidNormVec ''
          (TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) ⁻¹'
            {TorusCutoffs.proj s (flipCoord μ w)}) := by
    rintro w _ ⟨u, hu, rfl⟩
    exact ⟨flipCoord μ u, proj_flipCoord s μ (v := w) hu, euclidNormVec_flipCoord μ u⟩
  have e := key (flipCoord μ v)
  rw [flipCoord_flipCoord] at e
  simp only [TorusMetric.torusEuclidNorm]
  rw [Subset.antisymm e (key v)]
theorem affineReflect_eq (y : Fin 4 → ℝ) : M.affineReflect y = reflectVec s M.axis M.level y := by
  have hμ : (unitCouplingData s M.axis).dir = M.axis := rfl
  simp only [reflectVec, CutoffMirrors.MirrorData.reflectVec_eq_sub, hμ, AxisLevel.affineReflect]
  funext ν
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem reflectVec_axis (y : Fin 4 → ℝ) :
    reflectVec s M.axis M.level y M.axis = 2 * M.level - y M.axis := by
  have hμ : (unitCouplingData s M.axis).dir = M.axis := rfl
  simp only [reflectVec, CutoffMirrors.MirrorData.reflectVec_eq_sub, hμ]
  simp [PeriodicLattice.coordVec]
  ring
theorem reflectVec_sub (y y' : Fin 4 → ℝ) :
    reflectVec s M.axis M.level y - reflectVec s M.axis M.level y' =
      flipCoord M.axis (y - y') := by
  have hμ : (unitCouplingData s M.axis).dir = M.axis := rfl
  simp only [reflectVec, CutoffMirrors.MirrorData.reflectVec_eq_sub, hμ]
  funext ν
  by_cases h : ν = M.axis
  · subst h
    simp [flipCoord, PeriodicLattice.coordVec]
    ring
  · simp [flipCoord, PeriodicLattice.coordVec, Function.update_of_ne h, Pi.single_eq_of_ne h]
theorem isTorusIsometry : TorusTuples.IsTorusIsometry s (M.reflect s) := by
  intro x y
  obtain ⟨a, rfl⟩ := TorusCutoffs.exists_proj_eq s x
  obtain ⟨b, rfl⟩ := TorusCutoffs.exists_proj_eq s y
  rw [M.reflect_proj s, M.reflect_proj s]
  change TorusMetric.torusEuclidNorm (S := PeriodicLattice.torusSide s.L s.m)
      (TorusCutoffs.proj s (reflectVec s M.axis M.level a) -
        TorusCutoffs.proj s (reflectVec s M.axis M.level b)) =
    TorusMetric.torusEuclidNorm (S := PeriodicLattice.torusSide s.L s.m)
      (TorusCutoffs.proj s a - TorusCutoffs.proj s b)
  rw [← proj_sub, ← proj_sub, reflectVec_sub, torusEuclidNorm_proj_flipCoord]
theorem torusProperties : TorusProperties s M := by
  refine ⟨fun y y' h => ?_, fun y => ?_, isTorusIsometry s M, (M.reflect_involutive s).comp_self,
    fun _ _ => rfl⟩
  · rw [affineReflect_eq, affineReflect_eq, ← M.reflect_proj s, ← M.reflect_proj s, h]
  · rw [affineReflect_eq, M.reflect_proj s]
theorem openSlab_pos :
    M.openSlab s .pos =
      TorusCutoffs.proj s '' {y | M.level < y M.axis ∧ y M.axis < M.level + s.side / 2} := by
  change TorusCutoffs.proj s '' {y | 0 < CutoffMirrors.SlabSide.toReal .pos * (y M.axis - M.level) ∧
    CutoffMirrors.SlabSide.toReal .pos * (y M.axis - M.level) < s.side / 2} = _
  congr 1
  ext y
  simp only [mem_ofPred_eq, CutoffMirrors.SlabSide.toReal]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
theorem openSlab_neg :
    M.openSlab s .neg =
      TorusCutoffs.proj s '' {y | M.level - s.side / 2 < y M.axis ∧ y M.axis < M.level} := by
  change TorusCutoffs.proj s '' {y | 0 < CutoffMirrors.SlabSide.toReal .neg * (y M.axis - M.level) ∧
    CutoffMirrors.SlabSide.toReal .neg * (y M.axis - M.level) < s.side / 2} = _
  congr 1
  ext y
  simp only [mem_ofPred_eq, CutoffMirrors.SlabSide.toReal]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
theorem reflectVec_image_strip :
    reflectVec s M.axis M.level '' {y | M.level < y M.axis ∧ y M.axis < M.level + s.side / 2} =
      {y | M.level - s.side / 2 < y M.axis ∧ y M.axis < M.level} := by
  ext y
  constructor
  · rintro ⟨u, ⟨h₁, h₂⟩, rfl⟩
    simp only [mem_ofPred_eq, reflectVec_axis]
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    refine ⟨reflectVec s M.axis M.level y, ?_, M.reflectVec_reflectVec s y⟩
    simp only [mem_ofPred_eq, reflectVec_axis]
    constructor <;> linarith
theorem reflect_image_pos : M.reflect s '' M.openSlab s .pos = M.openSlab s .neg := by
  rw [openSlab_pos, openSlab_neg, ← reflectVec_image_strip, image_image, image_image]
  exact image_congr fun y _ => M.reflect_proj s y
theorem reflect_image_neg : M.reflect s '' M.openSlab s .neg = M.openSlab s .pos := by
  rw [← reflect_image_pos, image_image]
  simp only [M.reflect_involutive s _, image_id']
theorem side_pos : 0 < s.side := by apply _root_.YangMills.Construction.TorusMeasure.TranslatedLatticeCells.torusSide_pos <;> assumption
theorem openSlab_pos_inter_neg : M.openSlab s .pos ∩ M.openSlab s .neg = ∅ := by
  rw [openSlab_pos, openSlab_neg]
  refine eq_empty_of_forall_notMem ?_
  rintro _ ⟨⟨y, ⟨h₁, h₂⟩, rfl⟩, ⟨y', ⟨h₃, h₄⟩, e⟩⟩
  have hc : ((y M.axis - y' M.axis : ℝ) : AddCircle (PeriodicLattice.torusSide s.L s.m)) = 0 := by
    rw [AddCircle.coe_sub, sub_eq_zero]
    exact (congrFun e M.axis).symm
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).mp hc
  have hℓ := side_pos s
  have hn' : (n : ℝ) * s.side = y M.axis - y' M.axis := by
    rw [← hn, zsmul_eq_mul]
    rfl
  have b : (n : ℝ) * s.side < 1 * s.side := by linarith
  have a' : (0 : ℝ) < n := by
    by_contra h
    nlinarith [not_lt.mp h]
  have b' : (n : ℝ) < 1 := lt_of_mul_lt_mul_right b hℓ.le
  have a'' : 0 < n := by exact_mod_cast a'
  have b'' : n < 1 := by exact_mod_cast b'
  omega
theorem axisReflectionProperties : AxisReflectionProperties := fun s M =>
  ⟨torusProperties s M, openSlab_neg s M, reflect_image_pos s M, reflect_image_neg s M,
    openSlab_pos_inter_neg s M⟩
end YangMills.Construction.ReflectionPositivity.TorusMirrors.AxisReflection
end
