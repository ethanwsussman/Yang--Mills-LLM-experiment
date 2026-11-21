import YangMills.Construction.Lattice.AveragingMapIsABorelMapProof
import YangMills.Construction.Towers.ChartAtOneAndTheImagesOfSmallFamiliesProof
import YangMills.Construction.Towers.ChartAtOneOnTheConfigurations
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower.IdentityChart
open Matrices IdentityExpChart Matrices.GroupLieProduct Matrices.PowerExpCharts
theorem inv_mem_specialUnitary {V : ComplexMatrix2} (hV : V ∈ ComplexMatrix2.specialUnitary) :
    V⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem inv_inv_of_mem_specialUnitary {V : ComplexMatrix2}
    (hV : V ∈ ComplexMatrix2.specialUnitary) : (V⁻¹)⁻¹ = V := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
theorem continuous_toMatrix : Continuous ComplexMatrix2.LieElement.toMatrix :=
  (LinearMap.isClosedEmbedding_of_injective
    (f := (⟨⟨ComplexMatrix2.LieElement.toMatrix, fun _ _ => rfl⟩, fun _ _ => rfl⟩ :
      ComplexMatrix2.LieElement →ₗ[ℝ] ComplexMatrix2))
    (LinearMap.ker_eq_bot.mpr fun _ _ h => Subtype.ext h)).continuous
section Families
variable {ι : Type}
theorem mem_lieBall_iff [Finite ι] [Nonempty ι] (ε : ℝ) (Y : ι → ComplexMatrix2.LieElement) :
    Y ∈ lieBall ι ε ↔ ∀ i, ComplexMatrix2.operatorNorm (Y i).toMatrix < ε := by apply _root_.YangMills.Construction.IdentityExpChart.BallImages.mem_lieBall_iff <;> assumption
theorem isOpen_lieBall [Finite ι] [Nonempty ι] (ε : ℝ) : IsOpen (lieBall ι ε) := by
  have e : lieBall ι ε =
      ⋂ i, {Y : ι → ComplexMatrix2.LieElement | ComplexMatrix2.operatorNorm (Y i).toMatrix < ε} := by
    ext Y
    rw [mem_iInter]
    exact mem_lieBall_iff ε Y
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_lt ?_ continuous_const
  exact continuous_norm.comp (continuous_toMatrix.comp (continuous_apply i))
theorem zero_mem_lieBall_half [Finite ι] [Nonempty ι] :
    (0 : ι → ComplexMatrix2.LieElement) ∈ lieBall ι (1 / 2) := by
  refine (mem_lieBall_iff _ _).2 fun i => ?_
  have e : ((0 : ι → ComplexMatrix2.LieElement) i).toMatrix = 0 := rfl
  rw [e]
  simp [ComplexMatrix2.operatorNorm]
theorem expFamily_zero : expFamily (0 : ι → ComplexMatrix2.LieElement) = oneFamily ι := by
  funext i
  have e : ((0 : ι → ComplexMatrix2.LieElement) i).toMatrix = 0 := rfl
  simp only [expFamily, e, smul_zero, oneFamily, ComplexMatrix2.matExp, NormedSpace.exp_zero]
theorem isRelativelyOpen_expFamily_image [Fintype ι] (H : ExpChartAtOne ι)
    {A : Set (ι → ComplexMatrix2.LieElement)}
    (hA : IsOpen A) (hs : A ⊆ lieBall ι (1 / 2)) :
    ComplexMatrix2.IsRelativelyOpen (specialUnitaryPower ι) (expFamily '' A) := by
  obtain ⟨-, ⟨O, hO, hOe⟩, hinv, -, -, hci, -⟩ := H
  obtain ⟨u, hu, hue⟩ := continuousOn_iff'.mp hci A hA
  refine ⟨u ∩ O, hu.inter hO, ?_⟩
  have e : expFamily '' A = IdentityExpChart.logChart ⁻¹' A ∩ expImage ι := by
    ext X
    constructor
    · rintro ⟨Y, hY, rfl⟩
      exact ⟨by rw [mem_preimage, hinv Y (hs hY)]; exact hY, mem_image_of_mem _ (hs hY)⟩
    · rintro ⟨hX, Y, hY, rfl⟩
      rw [mem_preimage, hinv Y hY] at hX
      exact ⟨Y, hX, rfl⟩
  rw [e, hue, hOe]
  ext X
  simp only [mem_inter_iff]
  tauto
theorem expFamily_mem_power [Fintype ι] (H : ExpChartAtOne ι) {Y : ι → ComplexMatrix2.LieElement}
    (hY : Y ∈ lieBall ι (1 / 2)) : expFamily Y ∈ specialUnitaryPower ι := by
  obtain ⟨-, ⟨O, -, hOe⟩, -⟩ := H
  have h : expFamily Y ∈ expImage ι := mem_image_of_mem _ hY
  rw [hOe] at h
  exact h.2
theorem tendsto_logChart_oneFamily [Fintype ι] [Nonempty ι] (H : ExpChartAtOne ι) :
    Tendsto (IdentityExpChart.logChart (σ := ι)) (𝓝[specialUnitaryPower ι] oneFamily ι) (𝓝 0) := by
  obtain ⟨-, ⟨O, hO, hOe⟩, hinv, -, -, hci, -⟩ := H
  have h0 := zero_mem_lieBall_half (ι := ι)
  have hu : oneFamily ι ∈ expImage ι := ⟨0, h0, expFamily_zero⟩
  have hval : IdentityExpChart.logChart (oneFamily ι) = 0 := by
    rw [← expFamily_zero, hinv 0 h0]
  have hmem : expImage ι ∈ 𝓝[specialUnitaryPower ι] oneFamily ι := by
    have huO : oneFamily ι ∈ O := by
      rw [hOe] at hu
      exact hu.1
    rw [hOe]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (hO.mem_nhds huO)) self_mem_nhdsWithin
  have hc := (hci _ hu).mono_of_mem_nhdsWithin hmem
  have ht : Tendsto (IdentityExpChart.logChart (σ := ι)) (𝓝[specialUnitaryPower ι] oneFamily ι)
      (𝓝 (IdentityExpChart.logChart (oneFamily ι))) := hc
  rwa [hval] at ht
end Families
variable {L n k j : ℕ}
theorem positive_or_opposite_positive (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem not_opposite_positive (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
theorem nonempty_positiveEdge : Nonempty (PositiveEdge L n k j) := by
  rcases positive_or_opposite_positive
      (PeriodicLattice.Bond.forwardFrom (0 : Vertex L n k j) 0) with h | h
  · exact ⟨⟨_, h⟩⟩
  · exact ⟨⟨_, h⟩⟩
theorem finite_edge [Finite (PositiveEdge L n k j)] : Finite (Edge L n k j) := by
  refine Finite.of_surjective
    (fun s : PositiveEdge L n k j ⊕ PositiveEdge L n k j =>
      Sum.elim (fun b => b.1) (fun b => b.1.opposite) s) fun b => ?_
  rcases positive_or_opposite_positive b with h | h
  · exact ⟨Sum.inl ⟨b, h⟩, rfl⟩
  · exact ⟨Sum.inr ⟨b.opposite, h⟩, opposite_opposite b⟩
theorem eq_of_restrictToPositiveEdges_eq {U V : Edge L n k j → ComplexMatrix2}
    (hU : ∀ b : Edge L n k j, U b.opposite = (U b)⁻¹)
    (hV : ∀ b : Edge L n k j, V b.opposite = (V b)⁻¹)
    (h : restrictToPositiveEdges U = restrictToPositiveEdges V) : U = V := by
  funext b
  rcases positive_or_opposite_positive b with hb | hb
  · exact congrFun h ⟨b, hb⟩
  · have e : U b.opposite = V b.opposite := congrFun h ⟨b.opposite, hb⟩
    have e₁ := hU b.opposite
    have e₂ := hV b.opposite
    rw [opposite_opposite] at e₁ e₂
    rw [e₁, e₂, e]
theorem extendOddly_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by
  by_cases hb : b.IsPositivelyOriented
  · have h' := not_opposite_positive hA hL hn hj b hb
    simp only [extendOddly, if_neg h', if_pos hb, opposite_opposite]
  · have h' := (positive_or_opposite_positive b).resolve_left hb
    simp only [extendOddly, if_neg hb, if_pos h', neg_neg]
theorem ofValues_of_positive (y : PositiveEdge L n k j → ComplexMatrix2.LieElement)
    {b : Edge L n k j} (hb : b.IsPositivelyOriented) : ofValues y b = (y ⟨b, hb⟩).toMatrix := by
  simp only [ofValues, extendOddly, if_pos hb, dif_pos hb]
theorem formValues_toMatrix_of_positive {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    (formValues B ⟨b, hb⟩).toMatrix = B b := by
  have h : restrictToPositiveEdges B ⟨b, hb⟩ ∈ ComplexMatrix2.hermitianTraceless := hB.1 b hb
  have e : toLieFamily (restrictToPositiveEdges B) ⟨b, hb⟩ =
      (id (⟨restrictToPositiveEdges B ⟨b, hb⟩, h⟩ : ComplexMatrix2.hermitianTraceless) :
        ComplexMatrix2.LieElement) := dif_pos h
  exact congrArg ComplexMatrix2.LieElement.toMatrix e
theorem ofValues_mem_edgeFormSpace (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) : ofValues y ∈ edgeFormSpace L n k j := by
  refine ⟨fun b hb => ?_, fun b => extendOddly_opposite hA hL hn hj _ b⟩
  rw [ofValues_of_positive y hb]
  exact (y ⟨b, hb⟩).2
theorem formValues_ofValues (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    formValues (ofValues y) = y := by
  have e : restrictToPositiveEdges (ofValues y) = toMatrices y :=
    funext fun s => ofValues_of_positive y s.2
  unfold formValues
  rw [e]
  funext s
  exact dif_pos (show toMatrices y s ∈ ComplexMatrix2.hermitianTraceless from (y s).2)
theorem ofValues_formValues {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j) :
    ofValues (formValues B) = B := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [ofValues_of_positive _ hb, formValues_toMatrix_of_positive hB hb]
  · have hr := (positive_or_opposite_positive b).resolve_left hb
    have e : ofValues (formValues B) b = -ofValues (formValues B) b.opposite := by
      simp only [ofValues, extendOddly, if_neg hb, if_pos hr, dif_pos hr]
    rw [e, ofValues_of_positive _ hr, formValues_toMatrix_of_positive hB hr, hB.2 b, neg_neg]
theorem identityChartPoint_of_positive (y : PositiveEdge L n k j → ComplexMatrix2.LieElement)
    {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    identityChartPoint y b = ComplexMatrix2.matExp (Complex.I • (y ⟨b, hb⟩).toMatrix) := by
  simp only [identityChartPoint, expForm, PeriodicLattice.expTwist, if_pos hb,
    ofValues_of_positive y hb, Pi.one_apply, mul_one]
theorem identityChartPoint_opposite_of_positive
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) (h : ¬ b.opposite.IsPositivelyOriented) :
    identityChartPoint y b.opposite = (ComplexMatrix2.matExp (Complex.I • (y ⟨b, hb⟩).toMatrix))⁻¹ := by
  simp only [identityChartPoint, expForm, PeriodicLattice.expTwist, if_neg h, opposite_opposite,
    ofValues_of_positive y hb, Pi.one_apply, mul_one]
theorem restrictToPositiveEdges_identityChartPoint
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    restrictToPositiveEdges (identityChartPoint y) = expFamily y :=
  funext fun b => identityChartPoint_of_positive y b.2
theorem identityChartLog_eq (V : Edge L n k j → ComplexMatrix2) :
    identityChartLog V = IdentityExpChart.logChart (restrictToPositiveEdges V) := by
  have e : restrictToPositiveEdges
      (extendOddly fun c => (1 / Complex.I) • ComplexMatrix2.logSeries (V c)) =
      logFamily (restrictToPositiveEdges V) := by
    funext b
    simp only [restrictToPositiveEdges, logFamily, extendOddly, if_pos b.2]
  unfold identityChartLog IdentityExpChart.logChart formValues
  rw [e]
theorem identityChartPoint_opposite {y : PositiveEdge L n k j → ComplexMatrix2.LieElement}
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (hy : ∀ s, expFamily y s ∈ ComplexMatrix2.specialUnitary) (b : Edge L n k j) :
    identityChartPoint y b.opposite = (identityChartPoint y b)⁻¹ := by
  by_cases hb : b.IsPositivelyOriented
  · rw [identityChartPoint_opposite_of_positive y hb (not_opposite_positive hA hL hn hj b hb),
      identityChartPoint_of_positive y hb]
  · have hr := (positive_or_opposite_positive b).resolve_left hb
    have e := identityChartPoint_opposite_of_positive y hr (by rwa [opposite_opposite])
    rw [opposite_opposite] at e
    have hS : ComplexMatrix2.matExp (Complex.I • (y ⟨b.opposite, hr⟩).toMatrix) ∈
        ComplexMatrix2.specialUnitary := hy ⟨b.opposite, hr⟩
    rw [e, inv_inv_of_mem_specialUnitary hS, identityChartPoint_of_positive y hr]
theorem identityChartPoint_mem_fieldSpace {y : PositiveEdge L n k j → ComplexMatrix2.LieElement}
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (hy : ∀ s, expFamily y s ∈ ComplexMatrix2.specialUnitary) :
    identityChartPoint y ∈ fieldSpace L n k j := by
  refine ⟨fun b _ => ?_, fun b _ => identityChartPoint_opposite hA hL hn hj hy b⟩
  by_cases hb : b.IsPositivelyOriented
  · rw [identityChartPoint_of_positive y hb]
    exact hy ⟨b, hb⟩
  · have hr := (positive_or_opposite_positive b).resolve_left hb
    have e := identityChartPoint_opposite_of_positive y hr (by rwa [opposite_opposite])
    rw [opposite_opposite] at e
    rw [e]
    exact inv_mem_specialUnitary (hy ⟨b.opposite, hr⟩)
theorem continuous_identityChartPoint :
    Continuous (identityChartPoint (L := L) (n := n) (k := k) (j := j)) := by
  let _ : NormedAlgebra ℚ ComplexMatrix2 := NormedAlgebra.restrictScalars ℚ ℂ ComplexMatrix2
  have hexp : ∀ s : PositiveEdge L n k j,
      Continuous fun y : PositiveEdge L n k j → ComplexMatrix2.LieElement =>
        ComplexMatrix2.matExp (Complex.I • (y s).toMatrix) := fun s =>
    NormedSpace.exp_continuous.comp
      ((continuous_toMatrix.comp (continuous_apply s)).const_smul Complex.I)
  refine continuous_pi fun b => ?_
  by_cases hb : b.IsPositivelyOriented
  · exact (hexp ⟨b, hb⟩).congr fun y => (identityChartPoint_of_positive y hb).symm
  · have hr := (positive_or_opposite_positive b).resolve_left hb
    have hc : Continuous fun y : PositiveEdge L n k j → ComplexMatrix2.LieElement =>
        ComplexMatrix2.matExp (-(Complex.I • (y ⟨b.opposite, hr⟩).toMatrix)) :=
      NormedSpace.exp_continuous.comp
        (((continuous_toMatrix.comp (continuous_apply _)).const_smul Complex.I).neg)
    refine hc.congr fun y => ?_
    have e := identityChartPoint_opposite_of_positive y hr (by rwa [opposite_opposite])
    rw [opposite_opposite] at e
    rw [e]
    exact Matrix.exp_neg _
theorem identityChartOnFields_proof (h₁ : IdentityExpChart.ChartAndBallImages.Statement)
    (h₂ : QuotientLattices.TorusAndSpaceLatticeProperties) :
    IdentityChartOnFields := by
  intro L n k j hL hn hj _
  have : Nonempty (PositiveEdge L n k j) := nonempty_positiveEdge
  have : Finite (Edge L n k j) := finite_edge
  obtain ⟨H, himg, hnear⟩ := h₁ (PositiveEdge L n k j)
  have hinv := H.2.2.1
  have hsmall : ∀ y ∈ lieBall (PositiveEdge L n k j) (1 / 2),
      identityChartPoint y ∈ fieldSpace L n k j ∧ identityChartLog (identityChartPoint y) = y := by
    intro y hy
    refine ⟨identityChartPoint_mem_fieldSpace h₂ hL hn hj fun s => expFamily_mem_power H hy s, ?_⟩
    rw [identityChartLog_eq, restrictToPositiveEdges_identityChartPoint, hinv y hy]
  have hrev : ∀ {y : PositiveEdge L n k j → ComplexMatrix2.LieElement},
      y ∈ lieBall (PositiveEdge L n k j) (1 / 2) →
        ∀ b : Edge L n k j, identityChartPoint y b.opposite = (identityChartPoint y b)⁻¹ :=
    fun hy b => identityChartPoint_opposite h₂ hL hn hj (fun s => expFamily_mem_power H hy s) b
  have h0 := zero_mem_lieBall_half (ι := PositiveEdge L n k j)
  have hone : identityChartPoint (0 : PositiveEdge L n k j → ComplexMatrix2.LieElement) =
      trivialField L n k j := by
    refine eq_of_restrictToPositiveEdges_eq (hrev h0) (fun b => ?_) ?_
    · simp [trivialField]
    · rw [restrictToPositiveEdges_identityChartPoint, expFamily_zero]
      rfl
  refine ⟨isOpen_lieBall _, h0, hone, hsmall, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A hA hs
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (hsmall y (hs hy)).1
    · rw [image_image]
      have e : (fun y => restrictToPositiveEdges (identityChartPoint y)) =
          expFamily (σ := PositiveEdge L n k j) := funext restrictToPositiveEdges_identityChartPoint
      rw [e]
      exact isRelativelyOpen_expFamily_image H hA hs
  · have h := (continuous_identityChartPoint (L := L) (n := n) (k := k) (j := j)).tendsto 0
    rwa [hone] at h
  · have e : identityChartLog (L := L) (n := n) (k := k) (j := j) =
        IdentityExpChart.logChart ∘ restrictToPositiveEdges :=
      funext identityChartLog_eq
    rw [e]
    refine (tendsto_logChart_oneFamily H).comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous (restrictToPositiveEdges (L := L) (m := n) (k := k) (j := j)) :=
        continuous_pi fun s => continuous_apply _
      exact (hc.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with V hV s
      exact hV.1 s.1 (mem_univ _)
  · intro A hA
    have hA'o : IsOpen (interior A ∩ lieBall (PositiveEdge L n k j) (1 / 2)) :=
      isOpen_interior.inter (isOpen_lieBall _)
    obtain ⟨O, hO, hOe⟩ := isRelativelyOpen_expFamily_image H hA'o inter_subset_right
    have hu : oneFamily (PositiveEdge L n k j) ∈
        expFamily '' (interior A ∩ lieBall (PositiveEdge L n k j) (1 / 2)) :=
      ⟨0, ⟨mem_interior_iff_mem_nhds.2 hA, h0⟩, expFamily_zero⟩
    have hN : expFamily '' (interior A ∩ lieBall (PositiveEdge L n k j) (1 / 2)) ∈
        𝓝[specialUnitaryPower (PositiveEdge L n k j)] oneFamily (PositiveEdge L n k j) := by
      have huO : oneFamily (PositiveEdge L n k j) ∈ O := by
        rw [hOe] at hu
        exact hu.1
      rw [hOe]
      exact inter_mem (mem_nhdsWithin_of_mem_nhds (hO.mem_nhds huO)) self_mem_nhdsWithin
    obtain ⟨ε, hε, hε2, hsub⟩ := hnear _ hN
    have hsin : 0 < Real.sin (ε / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])
    refine ⟨2 * Real.sin (ε / 2), by linarith, ?_⟩
    rintro V ⟨hV, hb⟩
    have hX : restrictToPositiveEdges V ∈ expFamily '' lieBall (PositiveEdge L n k j) ε := by
      rw [himg ε hε hε2]
      exact ⟨fun s => hV.1 s.1 (mem_univ _), fun s => hb s.1⟩
    obtain ⟨y, hy, hyV⟩ := hsub hX
    refine ⟨y, interior_subset hy.1, ?_⟩
    refine eq_of_restrictToPositiveEdges_eq (hrev hy.2) (fun b => hV.2 b (mem_univ _)) ?_
    rw [restrictToPositiveEdges_identityChartPoint, hyV]
  · intro ε hε
    have hopen : IsOpen {V : Edge L n k j → ComplexMatrix2 | ∀ b, ‖V b - 1‖ < ε} := by
      have e : {V : Edge L n k j → ComplexMatrix2 | ∀ b, ‖V b - 1‖ < ε} =
          ⋂ b, {V : Edge L n k j → ComplexMatrix2 | ‖V b - 1‖ < ε} := by
        ext V
        simp
      rw [e]
      exact isOpen_iInter_of_finite fun b =>
        isOpen_lt ((continuous_apply b).sub continuous_const).norm continuous_const
    refine mem_nhdsWithin.2 ⟨_, hopen, fun b => ?_, fun V hV => ⟨hV.2, hV.1⟩⟩
    simpa [trivialField] using hε
  · exact fun y => ⟨ofValues_mem_edgeFormSpace h₂ hL hn hj y, formValues_ofValues y⟩
  · exact fun B hB => ofValues_formValues hB
end Tower.IdentityChart
end YangMills.Construction
end
