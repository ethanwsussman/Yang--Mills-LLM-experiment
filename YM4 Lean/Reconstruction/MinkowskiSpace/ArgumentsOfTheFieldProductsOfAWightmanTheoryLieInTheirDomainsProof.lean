import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import Reconstruction.MinkowskiSpace.ArgumentsOfTheFieldProductsOfAWightmanTheoryLieInTheirDomains
import YangMills.Construction.Continuum.TestSpacesAndNormsOfTheAxiomsOnSchwartzFunctions
import Reconstruction.MinkowskiSpace.ConeTubeAndLorentzGroup
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MinkowskiSpace
namespace WightmanTheory.DomainFacts
theorem minkowskiForm_toComplex_toComplex (a p : RealVec4) :
    minkowskiForm (MinkowskiSpace.toComplex a) (MinkowskiSpace.toComplex p) =
      ((a 0 * p 0 - (a 1 * p 1 + a 2 * p 2 + a 3 * p 3) : ℝ) : ℂ) := by
  simp [minkowskiForm, spaceBilin, spacePart, MinkowskiSpace.toComplex, Fin.sum_univ_three]
theorem minkowskiPhase_isBddMeasurable (a : RealVec4) :
    ProjectionMeasures.IsBddMeasurableFun (minkowskiPhase a) := by
  have hc : Continuous (minkowskiPhase a) := by
    unfold minkowskiPhase
    simp only [minkowskiForm_toComplex_toComplex]
    fun_prop
  refine ⟨hc.measurable, 1, fun p => ?_⟩
  unfold minkowskiPhase
  rw [minkowskiForm_toComplex_toComplex, mul_comm, Complex.norm_exp_ofReal_mul_I]
theorem time_nonneg_of_mem_closedFutureCone {p : RealVec4} (hp : p ∈ closedFutureCone) :
    0 ≤ p 0 := by
  have h1 : coneGap p ≥ 0 := hp
  have h2 : 0 ≤ spaceNorm (spacePart p) := Real.sqrt_nonneg _
  unfold coneGap at h1
  linarith
theorem decay_indicator_isBddMeasurable (t : ℝ) (ht : 0 ≤ t) :
    ProjectionMeasures.IsBddMeasurableFun
      (closedFutureCone.indicator fun p => Complex.exp (-((t * p 0 : ℝ) : ℂ))) := by
  have hm : MeasurableSet closedFutureCone := closedFutureConeBorel.2
  have hc : Continuous fun p : RealVec4 => Complex.exp (-((t * p 0 : ℝ) : ℂ)) := by fun_prop
  refine ⟨hc.measurable.indicator hm, 1, fun p => ?_⟩
  by_cases hp : p ∈ closedFutureCone
  · rw [Set.indicator_of_mem hp, ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hneg : -(t * p 0) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg ht (time_nonneg_of_mem_closedFutureCone hp))
    simpa using Real.exp_le_one_iff.mpr hneg
  · rw [Set.indicator_of_notMem hp]
    simp
theorem coneGap_smul_timeUnit (s : ℝ) : coneGap (s • timeUnit) = s := by
  have h0 : (s • timeUnit) 0 = s := by simp [timeUnit, mkTimeSpace]
  have hs : spacePart (s • timeUnit) = 0 := by
    funext i
    simp [spacePart, timeUnit, mkTimeSpace]
  simp [coneGap, h0, hs, spaceNorm]
theorem boundaryApproach_mem_tubeTuples (m : ℕ) (x : TestSpaces.PointTuple (m + 1)) (ε : ℝ)
    (hε : 0 < ε) : boundaryApproach x ε ∈ tubeTuples m := by
  intro k _
  have him : MinkowskiSpace.imPart (boundaryApproach x ε k) = ε • timeUnit := by
    funext μ
    simp [MinkowskiSpace.imPart, boundaryApproach, successiveDiffs, tupleToComplex,
      MinkowskiSpace.toComplex]
  show coneGap (MinkowskiSpace.imPart (boundaryApproach x ε k)) > 0
  rw [him, coneGap_smul_timeUnit]
  exact hε
theorem wickDiffs_mem_tubeTuples (m : ℕ) (y : TestSpaces.PointTuple (m + 1))
    (hy : y ∈ TestSpaces.increasingTimes (m + 1)) : wickDiffs y ∈ tubeTuples m := by
  intro k _
  have hlt : y k.castSucc 3 < y k.succ 3 := hy Fin.castSucc_lt_succ
  have him : MinkowskiSpace.imPart (wickDiffs y k) =
      (y k.succ 3 - y k.castSucc 3) • timeUnit := by
    funext μ
    fin_cases μ <;>
      simp [MinkowskiSpace.imPart, wickDiffs, successiveDiffs, wickMapTuple, tupleToComplex,
        MinkowskiSpace.toComplex, wickMap, timeUnit, mkTimeSpace] <;> (right; rfl)
  show coneGap (MinkowskiSpace.imPart (wickDiffs y k)) > 0
  rw [him, coneGap_smul_timeUnit]
  exact sub_pos.mpr hlt
theorem partitionBlockCardLt_holds : PartitionBlockCardLt := by
  intro n η hη J hJ
  obtain ⟨hne, hp⟩ := Finset.mem_erase.mp hη
  have hpart : ClusterExpansion.SymGraph.IsPartition η := by
    simp only [ClusterExpansion.SymGraph.partitions, Finset.mem_filter] at hp
    exact hp.2
  by_contra hlt
  have hcard : J.card = Fintype.card (Fin n) := by
    have hle := Finset.card_le_univ J
    simp only [Fintype.card_fin] at hle ⊢
    omega
  have hJu : J = Finset.univ := (Finset.card_eq_iff_eq_univ J).1 hcard
  apply hne
  ext K
  simp only [Finset.mem_singleton]
  constructor
  · intro hK
    by_contra hKu
    have hd : Disjoint K J :=
      hpart.2.1 (by exact_mod_cast hK) (by exact_mod_cast hJ) (by rw [hJu]; exact hKu)
    rw [hJu] at hd
    obtain ⟨x, hx⟩ := hpart.1 K hK
    exact Finset.disjoint_left.1 hd hx (Finset.mem_univ x)
  · rintro rfl
    rwa [← hJu]
theorem linearCombinationMemSchwartz_holds (h : TestSpaces.Elementary.BasicProperties) :
    LinearCombinationMemSchwartz := by
  intro a b f f'
  show asOnePointFn (a • f.1 + b • f'.1) ∈ TestSpaces.schwartzSet 1
  exact ((h 1 one_pos).1.1 _ f.2 _ f'.2 a b).1.1
theorem smoothCompactSuppSubsetFlatSchwartz_holds (h : TestSpaces.Elementary.BasicProperties) :
    SmoothCompactSuppSubsetFlatSchwartz := by
  intro m φ hφ
  obtain ⟨_, h2, h3, _, _⟩ := h (m + 1) (Nat.succ_pos m)
  have hc := h3 _ h2.1 φ hφ
  have hm : φ ∈ TestSpaces.flatSchwartzSet (m + 1) := by
    rw [h2.2.2.2.2.2.2.1]
    exact ⟨hc.1, hc.2.1⟩
  exact SchwartzAxioms.flatSchwartzSet_eq ▸ hm
theorem statement_holds (hCone : ConeTubeLorentz.Statement)
    (hTest : TestSpaces.Elementary.BasicProperties)
    (hCalculus : PVMCalculus.BoundedFunctionalCalculus) : Statement := by
  have hPoincare : ConeTubeLorentz.PoincareGroupAction :=
    hCone.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨fun g g' => hPoincare.2.1 _ g.2 _ g'.2,
    linearCombinationMemSchwartz_holds hTest, boundaryApproach_mem_tubeTuples,
    wickDiffs_mem_tubeTuples, smoothCompactSuppSubsetFlatSchwartz_holds hTest,
    partitionBlockCardLt_holds, ?_, fun f k hk => f.2.2 k hk, ?_⟩
  · refine fun t ht => ⟨decay_indicator_isBddMeasurable t ht, ?_⟩
    intro H _ _ _ E hE hC
    exact ((hCalculus.2 H).2 E closedFutureConeBorel hE hC).2.1.1 _
      (decay_indicator_isBddMeasurable t ht) |>.1
  · refine fun a => ⟨minkowskiPhase_isBddMeasurable a, ?_⟩
    intro H _ _ _ E hE hC
    exact ((hCalculus.2 H).2 E closedFutureConeBorel hE hC).2.1.1 _
      (minkowskiPhase_isBddMeasurable a) |>.1
end WightmanTheory.DomainFacts
end YangMills.Construction
end
