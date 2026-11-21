import YangMills.Construction.Continuum.DisjointCompactSetsAreSeparated
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open AmbientPoints Continuum.SeparatedFourTuples
open TestFunctions (HasSeparatedSupportsR4 setDistR4)
namespace CompactSeparation
theorem exists_pos_ofReal_le_setDist {s : Conventions.StandingParameters}
    {A A' : Set (EuclideanFour s)}
    (hA : IsCompact A) (hA' : IsCompact A') (hd : Disjoint A A') :
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ setDist s .euclidean A A' := by
  obtain ⟨r, hr, h⟩ := Metric.exists_pos_forall_lt_edist hA hA'.isClosed hd
  refine ⟨r, by exact_mod_cast hr, ?_⟩
  refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
  have hlt := h a ha b hb
  rw [edist_dist] at hlt
  rw [ENNReal.ofReal_coe_nnreal]
  exact hlt.le
theorem setDistR4_tsupport_eq {s : Conventions.StandingParameters} (f g : EuclideanFour s → ℝ) :
    setDistR4 (tsupport (X := Fin 4 → ℝ) f) (tsupport (X := Fin 4 → ℝ) g) =
      setDist s .euclidean (tsupport f) (tsupport g) := by
  rw [tsupport_eq_of_r4 f, tsupport_eq_of_r4 g]
  rfl
theorem exists_common_pos_lower_bound {n : ℕ} (D : Fin n → Fin n → ENNReal)
    (h : ∀ i k, i ≠ k → ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ D i k) :
    ∃ d : ℝ, 0 < d ∧ ∀ i k, i ≠ k → ENNReal.ofReal d ≤ D i k := by
  classical
  choose! r hr hrD using h
  let g : Fin n × Fin n → ℝ := fun p => if p.1 ≠ p.2 then r p.1 p.2 else 1
  let T : Finset ℝ := insert 1 (Finset.univ.image g)
  have hT : T.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨T.min' hT, ?_, fun i k hik => ?_⟩
  · refine (Finset.lt_min'_iff T hT).2 fun y hy => ?_
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy
      by_cases hp : p.1 ≠ p.2
      · simpa [g, hp] using hr p.1 p.2 hp
      · have hg : g p = 1 := if_neg hp
        rw [hg]
        exact one_pos
  · have hmem : r i k ∈ T := Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨(i, k), Finset.mem_univ _, by simp [g, hik]⟩)
    exact (ENNReal.ofReal_le_ofReal (Finset.min'_le T _ hmem)).trans (hrD i k hik)
theorem compactSetsSeparated_holds : CompactSetsSeparated := by
  intro s
  refine ⟨fun A A' hA hA' hd => ?_, fun X => ?_⟩
  · obtain ⟨r, hr, hle⟩ := exists_pos_ofReal_le_setDist hA hA' hd
    exact (ENNReal.ofReal_pos.2 hr).trans_le hle
  · have hmem := tupleComponents_mem X
    obtain ⟨d, hd, hsep⟩ := exists_common_pos_lower_bound
      (fun i k => setDist s .euclidean (tsupport (tupleComponents X i)) (tsupport (tupleComponents X k)))
      (fun i k hik => exists_pos_ofReal_le_setDist (hmem.1 i).2 (hmem.1 k).2 (hmem.2 hik))
    refine ⟨d, ⟨hd, fun i k hik => ?_⟩, fun I => ⟨hd, fun i k hik => ?_⟩⟩
    · exact (hsep i k hik).trans_eq (setDistR4_tsupport_eq _ _).symm
    · exact (hsep _ _ fun h => hik ((I.orderEmbOfFin rfl).injective h)).trans_eq
        (setDistR4_tsupport_eq _ _).symm
end CompactSeparation
end YangMills.Construction
end
