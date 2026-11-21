import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import YangMills.Construction.Lattice.QuotientLatticesAndNeighbours
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfiguration
import YangMills.Construction.Towers.IteratesOfTheCovariantAveragesAtOneAtTheSideInfinity
import YangMills.Construction.Towers.IteratesOfTheCovariantAveragesAtOneOnTheSides
import YangMills.Construction.Towers.PropertiesOfTheCovariantAverages
import YangMills.Construction.Towers.QuadraticFormsAndTransposesOnTheRealSpaces
import YangMills.Construction.Towers.StepOfTheCovariantAveragesAtOneAtTheSideInfinity
import YangMills.Construction.Towers.StepOfTheCovariantAveragesAtOneOnTheSides
import Mathlib
set_option autoImplicit false
open Set Filter
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace TrivialFieldAverages
theorem conjugateBy_sub (V X Y : Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.conjugateBy V (X - Y) =
      Matrices.ComplexMatrix2.conjugateBy V X - Matrices.ComplexMatrix2.conjugateBy V Y := by
  simp only [Matrices.ComplexMatrix2.conjugateBy, mul_sub, sub_mul]
theorem conjugateBy_mem_traceless_of_det {V X : Matrices.ComplexMatrix2} (hV : V.det = 1)
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    Matrices.ComplexMatrix2.conjugateBy V X ∈ Matrices.ComplexMatrix2.traceless := by
  have hu : IsUnit V.det := by rw [hV]; exact isUnit_one
  show Matrix.trace (V * X * V⁻¹) = 0
  rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul]
  exact hX
theorem traceFinsumPairing_comm {ι : Type*} (f f' : ι → Matrices.ComplexMatrix2) :
    traceFinsumPairing f f' = traceFinsumPairing f' f := by
  unfold traceFinsumPairing
  refine finsum_congr fun i => ?_
  simp only [Matrices.ComplexMatrix2.halfTrace, Matrices.ComplexMatrix2.fullTrace]
  rw [Matrix.trace_mul_comm]
theorem traceFinsumPairing_zero_right {ι : Type*} (f : ι → Matrices.ComplexMatrix2) :
    traceFinsumPairing f (0 : ι → Matrices.ComplexMatrix2) = 0 := by
  unfold traceFinsumPairing
  simp [Matrices.ComplexMatrix2.halfTrace, Matrices.ComplexMatrix2.fullTrace]
section FiniteSide
variable {L n k j : ℕ}
theorem edge_positive_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · exact Or.inl ⟨μ, h⟩
  · refine Or.inr ⟨μ, ?_⟩
    change b.source - b.target = _
    rw [← neg_sub, h, neg_neg]
theorem edge_not_both_positive (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := hb
  rintro ⟨ν, hν⟩
  have hN := (hA L hL n j k hn hj).2.2.2.2.2.1
  have hs : QuotientLattices.IsSignedAxisStep
      (QuotientLattices.torusAxisSteps L n k j)
      (b.source : PeriodicLattice.FourTorus L n) (b.target : PeriodicLattice.FourTorus L n) 1 μ := by
    have h := congrArg Subtype.val hμ
    simpa [QuotientLattices.IsSignedAxisStep,
      QuotientLattices.torusAxisSteps] using h
  have hs' : QuotientLattices.IsSignedAxisStep
      (QuotientLattices.torusAxisSteps L n k j)
      (b.target : PeriodicLattice.FourTorus L n) (b.source : PeriodicLattice.FourTorus L n) 1 ν := by
    have h := congrArg Subtype.val hν
    simpa [QuotientLattices.IsSignedAxisStep,
      QuotientLattices.torusAxisSteps, PeriodicLattice.Bond.opposite] using h
  have hX := ((hN.2.2 _ b.source.2 _ b.target.2).2 1 μ hs).2
  rcases hX with ⟨-, h⟩ | ⟨-, h⟩
  · exact h ⟨ν, hs'⟩
  · exact h ⟨μ, hs⟩
theorem edge_opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b :=
  PeriodicLattice.Bond.ext rfl rfl
theorem covDiff_sub (V : Edge L n k j → Matrices.ComplexMatrix2)
    (l l' : Vertex L n k j → Matrices.ComplexMatrix2) :
    covDiff V (l - l') = covDiff V l - covDiff V l' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [covDiff, extendOddly, if_pos hb, Pi.sub_apply, conjugateBy_sub]
    abel
  · simp only [covDiff, extendOddly, if_neg hb, Pi.sub_apply, conjugateBy_sub]
    abel
theorem covDiff_mem_complexEdgeForms (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {U : Edge L n k j → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    {l : Vertex L n k j → Matrices.ComplexMatrix2}
    (hl : ∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) :
    covDiff U l ∈ complexEdgeForms L n k j := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [covDiff, extendOddly, if_pos hb]
    exact Matrices.ComplexMatrix2.traceless.sub_mem
      (conjugateBy_mem_traceless_of_det (hU.1 b trivial) (hl _)) (hl _)
  · by_cases hb : b.IsPositivelyOriented
    · have h' := edge_not_both_positive hA hL hn hj b hb
      simp only [covDiff, extendOddly, if_neg h', if_pos hb, edge_opposite_opposite]
    · have h' := (edge_positive_or_opposite b).resolve_left hb
      simp only [covDiff, extendOddly, if_neg hb, if_pos h', neg_neg]
theorem gaugeDirectionIdentity_of (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hC : CovariantSmoothingProperties.Statement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) : GaugeDirectionIdentity L n k j := by
  intro U hU l hl
  obtain ⟨h₁, h₂, -⟩ := ((hC L hL).1 n k hn).2 j hj |>.1 U hU
  have hs : ∀ x, l x ∈ Matrices.ComplexMatrix2.traceless := fun x => hl x trivial
  have hB := covDiff_mem_complexEdgeForms hA hL hn (Nat.zero_le k) hU.1 hs
  have e₁ := h₁ _ hB
  obtain ⟨e₂, e₃⟩ := h₂ l hs
  have e₄ : complexIterDeriv L n k j U (covDiff U l) =
      covDiff (PeriodicLattice.complexBlockFieldAtLevel j U)
          (iterAdjointCubeAverage L n k U j l) -
        covDiff (PeriodicLattice.complexBlockFieldAtLevel j U)
          (iterContourLogDrift L n k U j (covDiff U l)) := by
    rw [← e₃, e₁, add_sub_cancel_right]
  rw [e₄, ← covDiff_sub, e₂, add_sub_cancel_right]
theorem isOrthogonalProjection_eventually (hY : RealLinearMaps.RealLinearMapsStatement)
    (hQ : RealQuadraticTransposes.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 0 < k) :
    EventuallyNearIdentity (fieldSpace L n k 0) (IsOrthogonalProjection L n k) := by
  have hY' : EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
      ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k,
        ∀ l : vertexFunctionSpace L n k 0,
        (T l : Vertex L n k k → Matrices.ComplexMatrix2) =
          iterAdjointCubeAverage L n k U k (l : Vertex L n k 0 → Matrices.ComplexMatrix2) := by
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    exact ((hY L n (i + 1) hL hn (by omega)).1 i (by omega)).iterAdjointCubeAverage_isLinear
  have hQ' := (hQ L n k hL hn hk).2
  filter_upwards [hY', hQ'] with U hU hq
  have hv : ∀ x : vertexFunctionSpace L n k 0,
      (iterAverageLinear L n k U x :
        Vertex L n k k → Matrices.ComplexMatrix2) = iterAdjointCubeAverage L n k U k x :=
    Classical.epsilon_spec hU
  obtain ⟨-, hT, -⟩ := hq
  obtain ⟨T, hTv, -, hk₂, hk₃⟩ := hT.average_transpose
  refine ⟨T, hTv, fun f hf => ?_⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 0 < L)
  have hr0 : ((L : ℝ) ^ (4 * k)) ≠ 0 := (pow_pos hL0 _).ne'
  let f₀ : vertexFunctionSpace L n k 0 := ⟨f.1, hf⟩
  let g : vertexFunctionSpace L n k k := iterAverageLinear L n k U f₀
  let p : vertexFunctionSpace L n k 0 :=
    ((L : ℝ) ^ (4 * k)) • iterAverageRealTranspose L n k U g
  have hg : (T f).1 = g.1 := (hTv f).trans (hv f₀).symm
  have ht := hk₂ g (T f) hg
  have hp : projectionMap L n k T f = p := by
    unfold projectionMap
    rw [← ht]
    funext x
    have e : (p : Vertex L n k 0 → Matrices.ComplexMatrix2) x = ((L : ℝ) ^ (4 * k)) •
        (iterAverageRealTranspose L n k U g : Vertex L n k 0 → Matrices.ComplexMatrix2) x := rfl
    have c : algebraMap ℝ ℂ ((L : ℝ) ^ (4 * k)) = (L : ℂ) ^ (4 * k) := by simp
    rw [e, ← algebraMap_smul ℂ ((L : ℝ) ^ (4 * k)), c]
    rfl
  have hTp : iterAverageLinear L n k U p = g := by
    show iterAverageLinear L n k U
      (((L : ℝ) ^ (4 * k)) • iterAverageRealTranspose L n k U g) = g
    rw [map_smul, hT.average_comp_transpose g, smul_smul, mul_inv_cancel₀ hr0, one_smul]
  have hker : iterAdjointCubeAverage L n k U k
      ((f₀ - p : vertexFunctionSpace L n k 0) : Vertex L n k 0 → Matrices.ComplexMatrix2) = 0 := by
    rw [← hv, map_sub, hTp]
    simp [g]
  refine ⟨?_, fun w hw => ?_⟩
  · rw [hp]
    refine ⟨p.2, fun l' hl' h0 => ?_⟩
    have h3 := hk₃ (((L : ℝ) ^ (4 * k)) • g) ⟨l', hl'⟩
    have hz : iterAverageLinear L n k U ⟨l', hl'⟩ = 0 :=
      Subtype.ext (by rw [hv]; exact h0)
    have hz' : (iterAverageLinear L n k U ⟨l', hl'⟩ : Vertex L n k k → Matrices.ComplexMatrix2) =
        0 := by
      rw [hz]; rfl
    have hpR : p = PairedFunctionSpace.realTransposeMap (S := pairedFunctions (Vertex L n k 0))
        (S' := pairedFunctions (Vertex L n k k)) (iterAverageLinear L n k U)
        (((L : ℝ) ^ (4 * k)) • g) := (map_smul _ _ _).symm
    rw [hpR]
    refine h3.trans ?_
    show traceFinsumPairing _
      (iterAverageLinear L n k U ⟨l', hl'⟩ : Vertex L n k k → Matrices.ComplexMatrix2) = 0
    rw [hz', traceFinsumPairing_zero_right]
  · rw [hp]
    have e : (fun x => f.1 x - (p : Vertex L n k 0 → Matrices.ComplexMatrix2) x) =
        ((f₀ - p : vertexFunctionSpace L n k 0) : Vertex L n k 0 → Matrices.ComplexMatrix2) := rfl
    have h := traceFinsumPairing_comm (ι := Vertex L n k 0)
      ((f₀ - p : vertexFunctionSpace L n k 0) : Vertex L n k 0 → Matrices.ComplexMatrix2) w
    rw [e]
    exact h.trans (hw.2 _ (f₀ - p).2 hker)
end FiniteSide
section FullSpaceSide
variable {L k j : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < meshAt L k j := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 0 < L)
  exact zpow_pos hL0 _
theorem link_opposite_positive_iff {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented := by
  have h := InfiniteLattice.xor_mem_positiveLinks ha b
  simp only [InfiniteLattice.mem_positiveLinks_iff] at h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨fun h => absurd h h₂, fun h => absurd h₁ h⟩
  · exact ⟨fun _ => h₂, fun _ => h₁⟩
theorem fullSpace_covDiff_sub {a : ℝ} (V : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (l l' : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    FullSpace.covDiff V (l - l') = FullSpace.covDiff V l - FullSpace.covDiff V l' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [FullSpace.covDiff, FullSpace.extendOddly, if_pos hb, Pi.sub_apply, conjugateBy_sub]
    abel
  · simp only [FullSpace.covDiff, FullSpace.extendOddly, if_neg hb, Pi.sub_apply, conjugateBy_sub]
    abel
theorem fullSpace_covDiff_mem {a : ℝ} (ha : 0 < a)
    {U : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hU : ∀ b, U b ∈ PeriodicLattice.complexGaugeGroup)
    {l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2}
    (hl : ∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) :
    FullSpace.covDiff U l ∈ FullSpace.complexEdgeForms a := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [FullSpace.covDiff, FullSpace.extendOddly, if_pos hb]
    exact Matrices.ComplexMatrix2.traceless.sub_mem
      (conjugateBy_mem_traceless_of_det (hU b) (hl _)) (hl _)
  · by_cases hb : b.IsPositivelyOriented
    · have h' : ¬ b.opposite.IsPositivelyOriented := fun h =>
        (link_opposite_positive_iff ha b).1 h hb
      simp only [FullSpace.covDiff, FullSpace.extendOddly, if_neg h', if_pos hb,
        InfiniteLattice.Link.opposite_opposite]
    · have h' := (link_opposite_positive_iff ha b).2 hb
      simp only [FullSpace.covDiff, FullSpace.extendOddly, if_neg hb, if_pos h', neg_neg]
theorem fullSpace_gaugeDirectionIdentity_of (hC : CovariantSmoothingProperties.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) :
    FullSpace.TrivialFieldAverages.GaugeDirectionIdentity L k j := by
  intro U hU l hl
  obtain ⟨h₁, h₂, -⟩ := ((hC L hL).2 k).2 j hj |>.1 U hU
  have hs : ∀ x, l x ∈ Matrices.ComplexMatrix2.traceless := fun x => hl x trivial
  have hB := fullSpace_covDiff_mem (meshAt_pos hL) hU.1.1 hs
  have e₁ := h₁ _ hB
  obtain ⟨e₂, e₃⟩ := h₂ l hs
  have e₄ : FullSpace.complexIterDeriv L k j U (FullSpace.covDiff U l) =
      FullSpace.covDiff (FullSpace.complexIter L k j U)
          (FullSpace.iterAdjointCubeAverage L k U j l) -
        FullSpace.covDiff (FullSpace.complexIter L k j U)
          (FullSpace.iterContourLogDrift L k U j (FullSpace.covDiff U l)) := by
    rw [← e₃, e₁, add_sub_cancel_right]
  rw [e₄, ← fullSpace_covDiff_sub, e₂, add_sub_cancel_right]
end FullSpaceSide
theorem atTrivialField_holds (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hC : CovariantSmoothingProperties.Statement)
    (hY : RealLinearMaps.RealLinearMapsStatement)
    (hQ : RealQuadraticTransposes.Statement)
    (hS : TrivialFieldSmoothingStep.Statement)
    (hI : CovariantIteratesAtTrivialField)
    (hSW : FullSpace.SmoothingStepAtOne)
    (hIW : FullSpace.CovariantIteratesAtIdentity) : AtTrivialField := by
  intro L hL
  refine ⟨fun n k hn hk => ⟨fun i hi => hS L hL n k i hn hi,
    fun j hj => hI L hL n k j hn hk hj, isOrthogonalProjection_eventually hY hQ hL hn hk,
    fun j hj => gaugeDirectionIdentity_of hA hC hL hn hj⟩,
    fun k hk => ⟨fun i hi => hSW L hL k i hi, fun j hj => hIW L hL k j hk hj,
      fun j hj => fullSpace_gaugeDirectionIdentity_of hC hL hj⟩⟩
end TrivialFieldAverages
end Tower
end YangMills.Construction
end
