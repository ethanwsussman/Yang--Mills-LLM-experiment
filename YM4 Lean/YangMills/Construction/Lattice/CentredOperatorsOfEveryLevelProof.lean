import YangMills.Construction.Lattice.GreenOperatorsOfCubesInLevelUnits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set SeparatedSequences PeriodicLattice
namespace CubeCovering.CenteredLevels
def sameLevelScales (s e : ℕ) : ScaleData := ⟨s, s, s, e, le_rfl, le_rfl⟩
theorem isSeparatedSequence_empty (L m s e : ℕ) (R : ℝ) :
    IsSeparatedSequence (sameLevelScales s e) R (fun _ => (∅ : Set (FourTorus L m))) := by
  refine ⟨fun _ _ => Or.inl rfl, fun n _ => ⟨subset_rfl, ?_⟩⟩
  have hd : ∀ A : Set (FourTorus L m), TorusMetric.setSupDist A ∅ = ⊤ := fun A => by
    simp [TorusMetric.setSupDist]
  have hK : (L : ℝ) ^ levelDepth (sameLevelScales s e).levels (sameLevelScales s e).unitLevel = 1 := by
    simp [sameLevelScales, levelDepth]
  rw [supDistInLevelUnits, hd, hK]
  simp
def emptyCubeData (L e s : ℕ) (hL : Odd L) (h13 : 13 ≤ L) (he : 1 ≤ e) : CubeData L e where
  scales := sameLevelScales s e
  unitLevel_eq_top := rfl
  gapExp := 1
  seq := fun _ => ∅
  isSeparated := isSeparatedSequence_empty L e s e _
  odd := hL
  le_blockSize := Nat.le_self_pow (by simp [sameLevelScales]; omega) L
  eight_le_gap := by simpa using (by omega : 8 ≤ L)
def cornerPoint (a : ℝ) (b : Fin 4 → Bool) : Space := fun μ => if b μ then a else 0
theorem closedCube_center_le_of_eq {c c' : Space} {a : ℝ} (ha : 0 ≤ a)
    (h : closedCube c a = closedCube c' a) (μ : Fin 4) : c' μ ≤ c μ := by
  have hx : (fun ν => c ν - a / 2) ∈ closedCube c a := fun ν => by
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity)]
  rw [h] at hx
  have := (abs_le.mp (hx μ)).1
  linarith
theorem cornerPoint_injective {a : ℝ} (ha : 0 < a) : Function.Injective (cornerPoint a) := by
  intro b b' h
  funext μ
  have h1 := congrFun h μ
  simp only [cornerPoint] at h1
  cases hb : b μ <;> cases hb' : b' μ <;> simp [hb, hb', ha.ne, ha.ne'] at h1 ⊢
theorem closedCube_cornerPoint_injective {a : ℝ} (ha : 0 < a) :
    Function.Injective fun b => closedCube (cornerPoint a b) a := by
  intro b b' h
  refine cornerPoint_injective ha (funext fun μ => le_antisymm ?_ ?_)
  · exact closedCube_center_le_of_eq ha.le h.symm μ
  · exact closedCube_center_le_of_eq ha.le h μ
theorem closedCube_double_eq_iUnion {a : ℝ} (ha : 0 < a) :
    closedCube (fun _ => a / 2) (2 * a) = ⋃ b : Fin 4 → Bool, closedCube (cornerPoint a b) a := by
  ext x
  simp only [mem_iUnion]
  constructor
  · intro hx
    refine ⟨fun μ => decide (a / 2 ≤ x μ), fun μ => ?_⟩
    have h := abs_le.mp (hx μ)
    by_cases hc : a / 2 ≤ x μ
    · simp only [cornerPoint, hc, decide_true, if_true]
      exact abs_le.mpr ⟨by linarith, by linarith [h.2]⟩
    · simp only [cornerPoint, hc, decide_false, Bool.false_eq_true, if_false]
      exact abs_le.mpr ⟨by linarith [h.1], by linarith⟩
  · rintro ⟨b, hb⟩ μ
    have h := abs_le.mp (hb μ)
    simp only [cornerPoint] at h
    refine abs_le.mpr ?_
    split_ifs at h <;> constructor <;> linarith [h.1, h.2]
section DoubledCube
variable {L e s : ℕ} (hL : Odd L) (h13 : 13 ≤ L) (he : 1 ≤ e) (j : ℕ)
def cellSide : ℝ := ((emptyCubeData L e s hL h13 he).blockSize : ℝ) * (emptyCubeData L e s hL h13 he).levelScale j
theorem cellSide_eq :
    cellSide (s := s) hL h13 he j = (L : ℝ) ^ (-(((s : ℤ) - (j : ℤ)) - (e : ℤ))) := by
  have hL0 : (L : ℝ) ≠ 0 := by
    have : L ≠ 0 := by omega
    exact_mod_cast this
  change ((L ^ e : ℕ) : ℝ) * (L : ℝ) ^ ((j : ℤ) - (s : ℤ)) = _
  rw [Nat.cast_pow, ← zpow_natCast, ← zpow_add₀ hL0]
  congr 1
  ring
theorem cellSide_pos : 0 < cellSide (s := s) hL h13 he j := by
  rw [cellSide_eq]
  have : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  positivity
theorem blockPartitionIndex_eq :
    (emptyCubeData L e s hL h13 he).scales.blockPartitionIndex j = ((s : ℤ) - (j : ℤ)) - (e : ℤ) := rfl
theorem isCellCentre_cornerPoint (hj : j ≤ s) (b : Fin 4 → Bool) :
    (emptyCubeData L e s hL h13 he).IsCellCentre j (cornerPoint (cellSide (s := s) hL h13 he j) b) := by
  refine ⟨?_, ?_⟩
  · rw [blockPartitionIndex_eq]
    omega
  · have hs : meshSize L (levelDepth (emptyCubeData L e s hL h13 he).scales.levels
        (emptyCubeData L e s hL h13 he).scales.top) = 1 := by
      simp [emptyCubeData, sameLevelScales, meshSize, levelDepth]
    exact show ∃ n : Fin 4 → ℤ, ∀ μ, (emptyCubeData L e s hL h13 he).coveringMap
        (cornerPoint (cellSide (s := s) hL h13 he j) b) μ =
        (((n μ : ℝ) * meshSize L ((emptyCubeData L e s hL h13 he).scales.blockPartitionIndex j) : ℝ) :
          AddCircle (torusSide L e)) from by
      refine ⟨fun μ => if b μ then 1 else 0, fun μ => ?_⟩
      rw [CubeData.coveringMap, hs, one_mul, blockPartitionIndex_eq, meshSize, ← cellSide_eq hL h13 he j]
      congr 1
      by_cases hb : b μ <;> simp [cornerPoint, hb]
def doubledCube (hj : j ≤ s) : Cube (emptyCubeData L e s hL h13 he) where
  level := j
  level_le := hj
  center := fun _ => cellSide (s := s) hL h13 he j / 2
  sideLength := 2 * cellSide (s := s) hL h13 he j
  sideLength_pos := mul_pos two_pos (cellSide_pos hL h13 he j)
  isUnion_cells := by
    classical
    have ha := cellSide_pos (s := s) hL h13 he j
    refine ⟨Finset.univ.image fun b => closedCube (cornerPoint (cellSide (s := s) hL h13 he j) b)
      (cellSide (s := s) hL h13 he j), ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (closedCube_cornerPoint_injective ha)]
      simp
    · intro D hD
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hD
      exact ⟨_, isCellCentre_cornerPoint hL h13 he j hj b, rfl⟩
    · rw [closedCube_double_eq_iUnion ha]
      ext x
      simp
end DoubledCube
end CubeCovering.CenteredLevels
end YangMills.Construction
