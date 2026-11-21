import YangMills.Construction.ChessboardTori.DistanceToFacePlanesAndOpenCells
import YangMills.Construction.ChessboardTori.MirrorPeriodicWeightsAsCellFunctionsProof
import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace WallDistance
theorem abs_apply_le_euclidNormVec (w : AmbientSpace) (i : Fin 4) :
    |w i| ≤ TorusMetric.euclidNormVec w := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
theorem euclidNormVec_nonneg (w : AmbientSpace) : 0 ≤ TorusMetric.euclidNormVec w :=
  Real.sqrt_nonneg _
theorem euclidNormVec_sub_update (x : AmbientSpace) (i : Fin 4) (c : ℝ) :
    TorusMetric.euclidNormVec (x - Function.update x i c) = |x i - c| := by
  unfold TorusMetric.euclidNormVec
  rw [Finset.sum_eq_single i]
  · simp [Real.sqrt_sq_eq_abs]
  · intro j _ hj
    simp [Function.update_of_ne hj]
  · simp
variable {D : ChessboardSetup} (G : ReflectionGrid D)
theorem cellSide_pos : 0 < G.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
theorem euclidInfDist_le (x w : AmbientSpace) {A : Set AmbientSpace} (hw : w ∈ A) :
    euclidInfDist x A ≤ TorusMetric.euclidNormVec (x - w) :=
  csInf_le ⟨0, by rintro _ ⟨z, _, rfl⟩; exact euclidNormVec_nonneg _⟩ ⟨w, hw, rfl⟩
theorem update_mem_walls (x : AmbientSpace) (i : Fin 4) (n : ℤ) :
    Function.update x i (G.origin i + n * G.cellSide) ∈ G.walls := by
  refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨n, ?_⟩⟩
  simp [ReflectionGrid.wall]
theorem euclidInfDist_walls_le_abs (x : AmbientSpace) (i : Fin 4) (n : ℤ) :
    euclidInfDist x G.walls ≤ |x i - (G.origin i + n * G.cellSide)| := by
  have hle := euclidInfDist_le x _ (update_mem_walls G x i n)
  rwa [euclidNormVec_sub_update] at hle
theorem euclidInfDist_walls_eq (x : AmbientSpace) :
    euclidInfDist x G.walls =
      Finset.univ.inf' Finset.univ_nonempty fun i : Fin 4 =>
        Metric.infDist (x i - G.origin i) (range fun n : ℤ => (n : ℝ) * G.cellSide) := by
  apply le_antisymm
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun i : Fin 4 => Metric.infDist (x i - G.origin i) (range fun n : ℤ => (n : ℝ) * G.cellSide))
    rw [hi]
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hne : (range fun n : ℤ => (n : ℝ) * G.cellSide).Nonempty := range_nonempty _
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (Metric.infDist_lt_iff hne).mp
      (lt_add_of_pos_right (Metric.infDist (x i - G.origin i)
        (range fun n : ℤ => (n : ℝ) * G.cellSide)) hε)
    refine lt_of_le_of_lt (euclidInfDist_walls_le_abs G x i n) ?_
    rw [Real.dist_eq] at hn
    have : x i - (G.origin i + n * G.cellSide) = x i - G.origin i - n * G.cellSide := by ring
    rwa [this]
  · refine le_csInf ?_ ?_
    · exact ⟨_, ⟨_, update_mem_walls G x 0 0, rfl⟩⟩
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨i, hw⟩ := mem_iUnion.mp hw
      obtain ⟨n, hw⟩ := mem_iUnion.mp hw
      have hwi : w i = G.origin i + n * G.cellSide := hw
      refine (Finset.inf'_le _ (Finset.mem_univ i)).trans ?_
      refine (Metric.infDist_le_dist_of_mem (mem_range_self n)).trans ?_
      rw [Real.dist_eq]
      refine le_trans (le_of_eq ?_) (abs_apply_le_euclidNormVec (x - w) i)
      simp only [Pi.sub_apply, hwi]
      congr 1
      ring
theorem mem_interior_cell_iff (n : Fin 4 → ℤ) (z : AmbientSpace) :
    z ∈ interior (G.cell n) ↔ ∀ i, z i - (G.origin i + G.cellSide * n i) ∈ Ioo 0 G.cellSide := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionPeriodicWeightsAsCellFunctions.mem_interior_cell_iff <;> assumption
theorem floor_eq_of_mem_interior_cell {n : Fin 4 → ℤ} {z : AmbientSpace}
    (hz : z ∈ interior (G.cell n)) (i : Fin 4) :
    ⌊(z i - G.origin i) / G.cellSide⌋ = n i := by
  have hs := cellSide_pos G
  have hi := (mem_interior_cell_iff G n z).mp hz i
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hs]
    nlinarith [hi.1]
  · rw [div_lt_iff₀ hs]
    nlinarith [hi.2]
theorem mem_interior_cell_floor {x : AmbientSpace} (hx : x ∉ G.walls) :
    x ∈ interior (G.cell fun i => ⌊(x i - G.origin i) / G.cellSide⌋) := by
  have hs := cellSide_pos G
  rw [mem_interior_cell_iff]
  intro i
  have hlo := Int.floor_le ((x i - G.origin i) / G.cellSide)
  have hhi := Int.lt_floor_add_one ((x i - G.origin i) / G.cellSide)
  rw [le_div_iff₀ hs] at hlo
  rw [div_lt_iff₀ hs] at hhi
  refine ⟨lt_of_le_of_ne ?_ fun h0 => hx ?_, ?_⟩
  · linarith
  · refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨⌊(x i - G.origin i) / G.cellSide⌋, ?_⟩⟩
    change x i = G.origin i + (⌊(x i - G.origin i) / G.cellSide⌋ : ℝ) * G.cellSide
    linarith
  · linarith
theorem existsUnique_cell_of_not_mem_walls {x : AmbientSpace} (hx : x ∉ G.walls) :
    ∃! S, S ∈ G.cellSet ∧ x ∈ interior S := by
  refine ⟨_, ⟨mem_range_self _, mem_interior_cell_floor G hx⟩, ?_⟩
  rintro _ ⟨⟨n, rfl⟩, hn⟩
  congr 1
  funext i
  exact (floor_eq_of_mem_interior_cell G hn i).symm
theorem exists_mem_segment_apply_eq {a b : AmbientSpace} {i : Fin 4} {c : ℝ}
    (hac : a i < c) (hcb : c < b i) :
    ∃ p ∈ segment ℝ a b, p i = c := by
  have hd : 0 < b i - a i := by linarith
  refine ⟨AffineMap.lineMap a b ((c - a i) / (b i - a i)), ?_, ?_⟩
  · rw [segment_eq_image_lineMap]
    refine mem_image_of_mem _ ⟨div_nonneg (by linarith) hd.le, ?_⟩
    rw [div_le_one hd]
    linarith
  · simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
theorem walls_separate_of_apply_lt {a b : AmbientSpace} {i : Fin 4} {n : ℤ}
    (ha : a i < G.origin i + n * G.cellSide) (hb : G.origin i + n * G.cellSide < b i) :
    (segment ℝ a b ∩ G.walls).Nonempty ∧
      euclidInfDist a G.walls + euclidInfDist b G.walls ≤ TorusMetric.euclidNormVec (a - b) := by
  constructor
  · obtain ⟨p, hp, hpi⟩ := exists_mem_segment_apply_eq ha hb
    exact ⟨p, hp, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨n, hpi⟩⟩⟩
  · have hda := euclidInfDist_walls_le_abs G a i n
    have hdb := euclidInfDist_walls_le_abs G b i n
    rw [abs_of_neg (by linarith)] at hda
    rw [abs_of_pos (by linarith)] at hdb
    have hn := abs_apply_le_euclidNormVec (a - b) i
    have hn' : b i - a i ≤ |(a - b) i| := by
      rw [Pi.sub_apply, abs_sub_comm]
      exact le_abs_self _
    linarith
theorem walls_separate_distinct_cells {n n' : Fin 4 → ℤ} (hne : n ≠ n') {a b : AmbientSpace}
    (ha : a ∈ interior (G.cell n)) (hb : b ∈ interior (G.cell n')) :
    (segment ℝ a b ∩ G.walls).Nonempty ∧
      euclidInfDist a G.walls + euclidInfDist b G.walls ≤ TorusMetric.euclidNormVec (a - b) := by
  have hs := cellSide_pos G
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have ha' := (mem_interior_cell_iff G n a).mp ha i
  have hb' := (mem_interior_cell_iff G n' b).mp hb i
  rcases lt_or_gt_of_ne hi with h | h
  · have hle : ((n i + 1 : ℤ) : ℝ) ≤ n' i := by exact_mod_cast h
    have hm : ((n i + 1 : ℤ) : ℝ) * G.cellSide ≤ n' i * G.cellSide :=
      mul_le_mul_of_nonneg_right hle hs.le
    push_cast at hm
    refine walls_separate_of_apply_lt G (i := i) (n := n i + 1) ?_ ?_
    · push_cast
      nlinarith [ha'.2]
    · push_cast
      nlinarith [hb'.1]
  · have hle : ((n' i + 1 : ℤ) : ℝ) ≤ n i := by exact_mod_cast h
    have hm : ((n' i + 1 : ℤ) : ℝ) * G.cellSide ≤ n i * G.cellSide :=
      mul_le_mul_of_nonneg_right hle hs.le
    push_cast at hm
    have hsep := walls_separate_of_apply_lt G (a := b) (b := a) (i := i) (n := n' i + 1)
      (by push_cast; nlinarith [hb'.2]) (by push_cast; nlinarith [ha'.1])
    refine ⟨by rw [segment_symm]; exact hsep.1, ?_⟩
    have hsym : TorusMetric.euclidNormVec (b - a) = TorusMetric.euclidNormVec (a - b) := by
      unfold TorusMetric.euclidNormVec
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.sub_apply]
      ring
    rw [← hsym, add_comm]
    exact hsep.2
theorem convex_subset_interior_cell {C : Set AmbientSpace} (hC : Convex ℝ C)
    (hd : Disjoint C G.walls) : ∃ S ∈ G.cellSet, C ⊆ interior S := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact ⟨_, mem_range_self 0, empty_subset _⟩
  · have hoff : ∀ {z}, z ∈ C → z ∉ G.walls := fun hz => disjoint_left.mp hd hz
    refine ⟨G.cell fun i => ⌊(x i - G.origin i) / G.cellSide⌋, mem_range_self _, fun z hz => ?_⟩
    have hxi := mem_interior_cell_floor G (hoff hx)
    have hzi := mem_interior_cell_floor G (hoff hz)
    by_cases he : (fun i => ⌊(x i - G.origin i) / G.cellSide⌋) =
        fun i => ⌊(z i - G.origin i) / G.cellSide⌋
    · rwa [he]
    · obtain ⟨p, hp, hpw⟩ := (walls_separate_distinct_cells G he hxi hzi).1
      exact absurd hpw (hoff (hC.segment_subset hx hz hp))
end WallDistance
theorem wallDistanceAndOpenCells_holds : WallDistanceAndOpenCells.Statement := by
  intro D G
  refine ⟨WallDistance.euclidInfDist_walls_eq G,
    fun x hx => WallDistance.existsUnique_cell_of_not_mem_walls G hx, ?_,
    fun C hC hd => WallDistance.convex_subset_interior_cell G hC hd⟩
  rintro _ ⟨n, rfl⟩ _ ⟨n', rfl⟩ hne a ha b hb
  exact WallDistance.walls_separate_distinct_cells G (fun h => hne (by rw [h])) ha hb
end YangMills.Construction.ChessboardTori
end
