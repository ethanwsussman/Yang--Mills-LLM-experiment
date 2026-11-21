import YangMills.Construction.ColdStepAtMirrorFrames.BlocksCoverTheLevelBelow
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem blocksCoverLowerLevel : BlocksCoverLowerLevel := by
  intro F hodd hpos x
  obtain ⟨k, hk⟩ := hodd
  have hside : 0 < F.blockSide := by omega
  have hdiff : F.top - F.depth = 1 := by simp [BlockFrame.top]
  have hperTop : ∀ i, F.period F.top i = F.extent i := by
    intro i
    simp [BlockFrame.period]
  have hperDepth : ∀ i, F.period F.depth i = F.extent i * F.blockSide := by
    intro i
    simp [BlockFrame.period, hdiff]
  have hneTop : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by rw [hperTop]; exact (hpos i).ne'⟩
  have hneDepth : ∀ i, NeZero (F.period F.depth i) := fun i =>
    ⟨by rw [hperDepth]; exact (Nat.mul_pos (hpos i) hside).ne'⟩
  have hfinite : Finite F.Cell := by
    have : ∀ i, Finite (ZMod (F.period F.top i)) := fun i => by
      have := hneTop i
      exact inferInstance
    exact Pi.finite
  have hcell : ∀ z : F.Cell, z ∈ finiteCells F := by
    intro z
    unfold finiteCells
    rw [dif_pos hfinite]
    exact @Finset.mem_univ _ (Fintype.ofFinite _) z
  set c : Fin 4 → ℤ := siteCoords x with hc
  set q : Fin 4 → ℤ := fun i => (c i + k) / (F.blockSide : ℤ) with hq
  set r : Fin 4 → ℤ := fun i => c i - (F.blockSide : ℤ) * q i with hr
  have hsideZ : (0 : ℤ) < (F.blockSide : ℤ) := by exact_mod_cast hside
  have hsideOdd : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  unfold sitesOfCells
  rw [Finset.mem_biUnion]
  refine ⟨siteOfCoords F.top q, hcell _, ?_⟩
  rw [Finset.mem_image]
  refine ⟨r, ?_, ?_⟩
  · unfold centredCube
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc, hdiff, pow_one]
    have h1 := Int.emod_add_mul_ediv (c i + k) (F.blockSide : ℤ)
    have h2 := Int.emod_nonneg (c i + k) hsideZ.ne'
    have h3 := Int.emod_lt_of_pos (c i + k) hsideZ
    have h4 : ((F.blockSide : ℤ) - 1) / 2 = k := by
      rw [hsideOdd]
      omega
    rw [h4]
    simp only [hr, hq]
    constructor <;> nlinarith
  · funext i
    have := hneTop i
    have := hneDepth i
    simp only [cellCentre, siteOfCoords, siteCoords, hdiff, pow_one, Pi.add_apply]
    have h1 : (((F.blockSide : ℤ) * ZMod.cast ((q i : ZMod (F.period F.top i)) : ZMod (F.period F.top i)) : ℤ) :
        ZMod (F.period F.depth i)) = (((F.blockSide : ℤ) * q i : ℤ) : ZMod (F.period F.depth i)) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      rw [ZMod.coe_intCast]
      have h2 := Int.emod_add_mul_ediv (q i) (F.period F.top i : ℤ)
      refine ⟨q i / (F.period F.top i : ℤ), ?_⟩
      rw [hperDepth, hperTop i] at *
      push_cast
      linear_combination (-(F.blockSide : ℤ)) * h2
    rw [h1, ← Int.cast_add]
    have h3 : (F.blockSide : ℤ) * q i + r i = c i := by
      simp only [hr]
      ring
    rw [h3]
    simp only [hc, siteCoords]
    exact ZMod.intCast_zmod_cast (x i)
end YangMills.Construction.ColdStepAtMirrorFrames
end
