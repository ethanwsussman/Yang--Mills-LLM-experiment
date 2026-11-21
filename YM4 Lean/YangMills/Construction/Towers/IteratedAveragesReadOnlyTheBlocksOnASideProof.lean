import YangMills.Construction.Towers.ConfigurationsFormedLevelByLevelOnThePolydiscsProof
import YangMills.Construction.Towers.IteratedAveragesReadOnlyTheBlocksAtTheSideInfinityProof
import YangMills.Construction.Towers.IteratedAveragesReadOnlyTheBlocksOnASide
import YangMills.Construction.Towers.StepKernelsAreHolomorphicOnASide
import YangMills.Construction.Towers.StepKernelsOfTheCovariantAveragesOnASide
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.BlockLocality
open SupportOfMeans (DefinedAlike HasEndpointsIn supportEdges baseFields)
open StepKernels (stepKernel IsBoundedTracelessEndo)
open StepKernelHolomorphy (smoothingDerivCoeff)
theorem pauliFamily_mem_traceless (a : Fin 3) :
    Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem sum_pauliCoeff_smul {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • Matrices.ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem eq_of_pauliCoeff_eq {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless)
    (h : ∀ a, pauliCoeff a X = pauliCoeff a Y) : X = Y := by apply _root_.YangMills.Construction.Tower.FullSpace.IterLocality.eq_of_pauliCoeff_eq <;> assumption
theorem map_sum_smul_pauliFamily {T : Matrices.ComplexMatrix2 → Matrices.ComplexMatrix2} {C : ℝ}
    (h : IsBoundedTracelessEndo T C) (x : Fin 3 → ℂ) :
    T (∑ a, x a • Matrices.ComplexMatrix2.pauliFamily a) =
      ∑ a, x a • T (Matrices.ComplexMatrix2.pauliFamily a) := by
  have hm : ∀ a, x a • Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless :=
    fun a => Matrices.ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem_traceless a)
  simp only [Fin.sum_univ_three]
  rw [h.map_add _ (Matrices.ComplexMatrix2.traceless.add_mem (hm 0) (hm 1)) _ (hm 2),
    h.map_add _ (hm 0) _ (hm 1),
    h.map_smul _ _ (pauliFamily_mem_traceless 0), h.map_smul _ _ (pauliFamily_mem_traceless 1),
    h.map_smul _ _ (pauliFamily_mem_traceless 2)]
theorem eq_of_coeffs_eq {T T' : Matrices.ComplexMatrix2 → Matrices.ComplexMatrix2} {C C' : ℝ}
    (h : IsBoundedTracelessEndo T C) (h' : IsBoundedTracelessEndo T' C')
    (he : ∀ a' a, pauliCoeff a' (T (Matrices.ComplexMatrix2.pauliFamily a)) =
      pauliCoeff a' (T' (Matrices.ComplexMatrix2.pauliFamily a)))
    {X : Matrices.ComplexMatrix2} (hX : X ∈ Matrices.ComplexMatrix2.traceless) : T X = T' X := by
  have e : ∀ a, T (Matrices.ComplexMatrix2.pauliFamily a) =
      T' (Matrices.ComplexMatrix2.pauliFamily a) := fun a =>
    eq_of_pauliCoeff_eq (h.mapsTo _ (pauliFamily_mem_traceless a))
      (h'.mapsTo _ (pauliFamily_mem_traceless a)) fun a' => he a' a
  rw [← sum_pauliCoeff_smul hX, map_sum_smul_pauliFamily h, map_sum_smul_pauliFamily h']
  simp only [e]
variable {L n k : ℕ}
theorem opposite_opposite {j : ℕ} (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
theorem isPositivelyOriented_or_opposite {j : ℕ} (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem not_opposite_isPositivelyOriented (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    (b : Edge L n k j) (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.not_isPositivelyOriented_opposite <;> assumption
theorem extendOddly_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    (f : Edge L n k j → Matrices.ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by
  by_cases hb : b.IsPositivelyOriented
  · have h' := not_opposite_isPositivelyOriented hA hL hn hj b hb
    simp only [extendOddly, if_neg h', if_pos hb, opposite_opposite]
  · have h' := (isPositivelyOriented_or_opposite b).resolve_left hb
    simp only [extendOddly, if_neg hb, if_pos h', neg_neg]
theorem covariantSmoothingDeriv_of_not_isPositivelyOriented {j : ℕ}
    (V B : Edge L n k j → Matrices.ComplexMatrix2) {c : Edge L n k (j + 1)}
    (hc : ¬c.IsPositivelyOriented) :
    covariantSmoothingDeriv V B c = -covariantSmoothingDeriv V B c.opposite := by
  have hr := (isPositivelyOriented_or_opposite c).resolve_left hc
  simp only [covariantSmoothingDeriv, complexSmoothingDeriv, holLeftDifferential,
    covDiff, Pi.add_apply, extendOddly, if_neg hc, if_pos hr, neg_add]
theorem covariantSmoothingDeriv_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j + 1 ≤ k)
    (V B : Edge L n k j → Matrices.ComplexMatrix2) (c : Edge L n k (j + 1)) :
    covariantSmoothingDeriv V B c.opposite = -covariantSmoothingDeriv V B c := by
  simp only [covariantSmoothingDeriv, complexSmoothingDeriv, holLeftDifferential,
    covDiff, Pi.add_apply]
  rw [extendOddly_opposite hA hL hn hj, extendOddly_opposite hA hL hn hj, neg_add]
theorem remainderGaugeField_congr {a a' : Edge L n k 0 → Matrices.ComplexMatrix2}
    {b : Edge L n k 0} (hb : b.IsPositivelyOriented) (h : a b = a' b) :
    remainderGaugeField a b = remainderGaugeField a' b := by
  simp only [remainderGaugeField, IdentityExpChart.expForm,
    PeriodicLattice.expTwist, if_pos hb, scaledRemainderForm, Pi.smul_apply, h]
theorem polydiscRadius_pos_of_lt {X : Matrices.ComplexMatrix2}
    (h : Matrices.ComplexMatrix2.operatorNorm X < polydiscRadius L / 2) :
    0 < polydiscRadius L := by apply _root_.YangMills.Construction.Tower.FullSpace.IterLocality.polydiscRadius_pos_of_lt <;> assumption
theorem operatorNorm_lt_three_quarters {X : Matrices.ComplexMatrix2}
    (h : Matrices.ComplexMatrix2.operatorNorm X < polydiscRadius L / 2) :
    Matrices.ComplexMatrix2.operatorNorm X < 3 / 4 * polydiscRadius L := by apply _root_.YangMills.Construction.Tower.FullSpace.IterLocality.lt_three_quarters_polydiscRadius <;> assumption
abbrev IsSmallEdgeForm (ρ : ℝ) (a : Edge L n k 0 → Matrices.ComplexMatrix2) : Prop :=
  a ∈ complexEdgeForms L n k 0 ∧ maxOperatorNorm a ≤ ENNReal.ofReal ρ
section Iterates
variable {ρ : ℝ} (hS : IteratesSmall L n k ρ)
include hS in
theorem levelwiseMean_eq_some (hP : LevelwiseMeans.PeriodicConditions L n k)
    {a : Edge L n k 0 → Matrices.ComplexMatrix2} (ha : IsSmallEdgeForm ρ a) {j : ℕ} (hj : j < k)
    (c : Edge L n k j) :
    LevelwiseMeans.levelwiseMean (remainderGaugeField a) j c =
      some (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) c) := by
  have hV : LevelwiseMeans.IsMeanSequence j
      fun i => PeriodicLattice.complexBlockFieldAtLevel i (remainderGaugeField a) :=
    { mem_fields := fun i hi => (hS a ha i (by omega)).1
      norm_sub_one_lt := fun i hi b => by
        have h := (hS a ha i (by omega)).2 b
        have := polydiscRadius_pos_of_lt h
        linarith
      eq_mean := fun i _ c _ => rfl }
  exact hP.sequence_is_levelwise j hj.le _ hV j le_rfl c
include hS in
theorem complexBlockFieldAtLevel_congr (hk : 1 ≤ k) (hP : LevelwiseMeans.PeriodicConditions L n k)
    (hR : SupportOfMeans.SideRequirements L n k)
    {a a' : Edge L n k 0 → Matrices.ComplexMatrix2} (ha : IsSmallEdgeForm ρ a)
    (ha' : IsSmallEdgeForm ρ a') {j : ℕ}
    (hj : j < k) (c : Edge L n k j) (h : ∀ b ∈ supportEdges c, a b = a' b) :
    PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) c =
      PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a') c := by
  obtain ⟨hfin, -⟩ := hR.finite_nonempty j hj.le c
  have hRd := hR.dependsOnlyOn j hj.le c hfin.toFinset (by simp)
  have hU : remainderGaugeField a ∈ baseFields L n k := (hS a ha 0 (by omega)).1
  have hU' : remainderGaugeField a' ∈ baseFields L n k := (hS a' ha' 0 (by omega)).1
  have hA := hRd.definedAlike_of_eqOn _ hU _ hU' fun b hb => by
    have hb' := hfin.mem_toFinset.1 hb
    exact remainderGaugeField_congr hb'.1 (h b hb')
  exact hA.2 _ _ (levelwiseMean_eq_some hS hP ha hj c) (levelwiseMean_eq_some hS hP ha' hj c)
end Iterates
theorem mem_refinedBlock_zero (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k)
    (y : Vertex L n k j) :
    (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock 0 y := by
  have H := ((hZ L hL k 0 j hk (Nat.zero_le _) hj).1 n hn).1.eq_image y
  rw [H]
  have e : ∀ μ : Fin 4, PeriodicLattice.pointOnAxis L n μ 0 = 0 := fun μ => by
    rw [PeriodicLattice.pointOnAxis,
      show ((0 : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = 0 from rfl, Pi.single_zero]
  exact ⟨0, by simp [offsetBox], by simp [offsetPoint, e]⟩
theorem refinedBlock_subset_succ (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (hx : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y) :
    PeriodicLattice.refinedBlock j x ⊆ PeriodicLattice.refinedBlock (j + 1) y := by apply _root_.YangMills.Construction.Tower.SupportOfMeans.refinedBlock_subset <;> assumption
theorem orderedContour_endpoints_mem (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    (σ : PeriodicLattice.AxisOrdering y x) {b : Edge L n k j}
    (hb : b ∈ PeriodicLattice.orderedContour y x σ) :
    (b.source : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
  obtain ⟨Hb, -, -, -, -, Hc⟩ := (hZ L hL k 1 (j + 1) hk (by omega) (by omega)).1 n hn
  have hx' : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock 1 y := hx
  rw [Hb.eq_image y] at hx'
  obtain ⟨ν, hν, hxν⟩ := hx'
  obtain ⟨-, -, -, -, hz⟩ := ((Hc (by omega)).1.contours y ν hν x hxν.symm).2 _ ⟨σ, rfl⟩
  exact ⟨hz b.source (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩)),
    hz b.target (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩))⟩
structure Hypotheses (L n k : ℕ) : Prop where
  lattices : QuotientLattices.TorusAndSpaceLatticeProperties
  blocks : BlockPathContourPivotStatement
  factor : Conventions.IsAdmissibleBlockingFactor L
  side_pos : 0 < n
  depth_pos : 1 ≤ k
  levelwise : LevelwiseMeans.PeriodicConditions L n k
  support : SupportOfMeans.SideRequirements L n k
  kernels : StepKernels.StepKernelBounds
  holomorphy : StepKernelHolomorphy.StepKernelsHolomorphic
section Induction
variable {ρ : ℝ} (G : Hypotheses L n k) (hS : IteratesSmall L n k ρ)
include hS in
theorem complexBlockFieldAtLevel_small {a : Edge L n k 0 → Matrices.ComplexMatrix2}
    (ha : IsSmallEdgeForm ρ a) {j : ℕ} (hj : j < k) :
    PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) ∈
        fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
      ∀ b, Matrices.ComplexMatrix2.operatorNorm
          (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) b - 1) <
        3 / 4 * polydiscRadius L :=
  ⟨(hS a ha j hj).1, fun b => operatorNorm_lt_three_quarters ((hS a ha j hj).2 b)⟩
include G hS in
theorem iterCovariantDeriv_mem {a : Edge L n k 0 → Matrices.ComplexMatrix2}
    (ha : IsSmallEdgeForm ρ a) :
    ∀ j ≤ k, ∀ B ∈ complexEdgeForms L n k 0,
      iterCovariantDeriv L n k (remainderGaugeField a) j B ∈ complexEdgeForms L n k j := by
  intro j
  induction j with
  | zero => exact fun _ B hB => hB
  | succ j ih =>
    intro hj B hB
    have hC := ih (by omega) B hB
    obtain ⟨h₁, h₂⟩ := complexBlockFieldAtLevel_small hS ha (j := j) (by omega)
    refine ⟨fun c hc => ?_,
      fun c => covariantSmoothingDeriv_opposite G.lattices G.factor G.side_pos hj _ _ c⟩
    obtain ⟨e, hT, -⟩ := G.kernels L G.factor n k j G.side_pos (by omega) c hc _ h₁ h₂
    change covariantSmoothingDeriv _ _ c ∈ Matrices.ComplexMatrix2.traceless
    rw [e _ hC]
    refine finsum_mem_induction (· ∈ Matrices.ComplexMatrix2.traceless)
      Matrices.ComplexMatrix2.traceless.zero_mem
      (fun _ _ => Matrices.ComplexMatrix2.traceless.add_mem) fun b hb => ?_
    exact (hT b hb).mapsTo _ (hC.1 b hb.2)
include G hS in
theorem iterCovariantDeriv_congr : ∀ j ≤ k, ∀ (c : Edge L n k j)
    (a a' B B' : Edge L n k 0 → Matrices.ComplexMatrix2),
    IsSmallEdgeForm ρ a → IsSmallEdgeForm ρ a' → B ∈ complexEdgeForms L n k 0 →
    B' ∈ complexEdgeForms L n k 0 →
    (∀ b, HasEndpointsIn c b → a b = a' b) → (∀ b, HasEndpointsIn c b → B b = B' b) →
    iterCovariantDeriv L n k (remainderGaugeField a) j B c =
      iterCovariantDeriv L n k (remainderGaugeField a') j B' c := by
  intro j
  induction j with
  | zero =>
    intro hj c a a' B B' _ _ _ _ _ h
    exact h c ⟨Or.inl (mem_refinedBlock_zero G.blocks G.factor G.side_pos G.depth_pos hj c.source),
      Or.inr (mem_refinedBlock_zero G.blocks G.factor G.side_pos G.depth_pos hj c.target)⟩
  | succ j ih =>
    intro hj c a a' B B' ha ha' hB hB' h₁ h₂
    have hjk : j < k := by omega
    have pos : ∀ (c : Edge L n k (j + 1)), c.IsPositivelyOriented →
        (∀ b, HasEndpointsIn c b → a b = a' b) → (∀ b, HasEndpointsIn c b → B b = B' b) →
        covariantSmoothingDeriv
            (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a))
            (iterCovariantDeriv L n k (remainderGaugeField a) j B) c =
          covariantSmoothingDeriv
            (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a'))
            (iterCovariantDeriv L n k (remainderGaugeField a') j B') c := by
      intro c hc h₁ h₂
      have hC := iterCovariantDeriv_mem G hS ha j (by omega) B hB
      have hC' := iterCovariantDeriv_mem G hS ha' j (by omega) B' hB'
      obtain ⟨s₁, s₂⟩ := complexBlockFieldAtLevel_small hS ha hjk
      obtain ⟨s₁', s₂'⟩ := complexBlockFieldAtLevel_small hS ha' hjk
      obtain ⟨e, hT, -⟩ := G.kernels L G.factor n k j G.side_pos hjk c hc _ s₁ s₂
      obtain ⟨e', hT', -⟩ := G.kernels L G.factor n k j G.side_pos hjk c hc _ s₁' s₂'
      rw [e _ hC, e' _ hC']
      refine finsum_mem_congr rfl fun b hb => ?_
      have below : ∀ w, HasEndpointsIn b w → HasEndpointsIn c w := fun w =>
        G.support.hasEndpointsIn_of_doubleBlock j hjk c hc b hb.1 w
      rw [ih (by omega) b a a' B B' ha ha' hB hB' (fun w hw => h₁ w (below w hw))
        (fun w hw => h₂ w (below w hw))]
      have hH := G.holomorphy L G.factor n k j G.side_pos hjk c hc
      have hV : PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) ∈
          nearIdentityPolydisc (3 / 4 * polydiscRadius L) c :=
        ⟨⟨fun b _ => s₁.1 b (mem_univ b), fun b _ => s₁.2 b (mem_univ b)⟩, fun b _ => s₂ b⟩
      have hV' : PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a') ∈
          nearIdentityPolydisc (3 / 4 * polydiscRadius L) c :=
        ⟨⟨fun b _ => s₁'.1 b (mem_univ b), fun b _ => s₁'.2 b (mem_univ b)⟩, fun b _ => s₂' b⟩
      have hEq : EqOn (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a))
          (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a'))
          (DoubleBlockPolydisc.doubleBlockBonds c) := fun b' hb' =>
        complexBlockFieldAtLevel_congr hS G.depth_pos G.levelwise G.support ha ha' hjk b'
          fun w hw => h₁ w (G.support.hasEndpointsIn_of_doubleBlock j hjk c hc b' hb' w hw.2)
      exact eq_of_coeffs_eq (hT b hb) (hT' b hb)
        (fun a₁ a₂ => hH.smoothing_local _ hV _ hV' hEq ⟨b, hb.2⟩ hb.1 a₁ a₂) (hC'.1 b hb.2)
    by_cases hc : c.IsPositivelyOriented
    · exact pos c hc h₁ h₂
    · have hr := (isPositivelyOriented_or_opposite c).resolve_left hc
      have sw : ∀ b, HasEndpointsIn c.opposite b → HasEndpointsIn c b := fun b hb =>
        ⟨Or.symm hb.1, Or.symm hb.2⟩
      change covariantSmoothingDeriv _ _ c = covariantSmoothingDeriv _ _ c
      rw [covariantSmoothingDeriv_of_not_isPositivelyOriented _ _ hc,
        covariantSmoothingDeriv_of_not_isPositivelyOriented _ _ hc,
        pos c.opposite hr (fun b hb => h₁ b (sw b hb)) fun b hb => h₂ b (sw b hb)]
include G hS in
theorem iterAdjointCubeAverage_congr : ∀ j ≤ k, ∀ (y : Vertex L n k j)
    (a a' : Edge L n k 0 → Matrices.ComplexMatrix2)
    (l l' : Vertex L n k 0 → Matrices.ComplexMatrix2), IsSmallEdgeForm ρ a → IsSmallEdgeForm ρ a' →
    (∀ x : Vertex L n k 0, (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock j y →
      l x = l' x) →
    EqOn a a' (PeriodicLattice.bondsInside (PeriodicLattice.refinedBlock j y)) →
    iterAdjointCubeAverage L n k (remainderGaugeField a) j l y =
      iterAdjointCubeAverage L n k (remainderGaugeField a') j l' y := by
  intro j
  induction j with
  | zero =>
    intro hj y a a' l l' _ _ h _
    exact h y (mem_refinedBlock_zero G.blocks G.factor G.side_pos G.depth_pos hj y)
  | succ j ih =>
    intro hj y a a' l l' ha ha' h₁ h₂
    have hjk : j < k := by omega
    simp only [iterAdjointCubeAverage, adjointCubeAverage]
    refine congrArg _ (finsum_mem_congr rfl fun x hx => ?_)
    have sub := refinedBlock_subset_succ G.blocks G.factor G.side_pos G.depth_pos hjk
      (y := y) (x := x) hx
    rw [ih (by omega) x a a' l l' ha ha' (fun z hz => h₁ z (sub hz))
      fun b hb => h₂ ⟨sub hb.1, sub hb.2⟩]
    have e : PeriodicLattice.contourHolonomies
          (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a)) y x =
        PeriodicLattice.contourHolonomies
          (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a')) y x := by
      funext σ
      simp only [PeriodicLattice.contourHolonomies, PeriodicLattice.pathHolonomy]
      refine congrArg List.prod (List.map_congr_left fun b hb => ?_)
      obtain ⟨e₁, e₂⟩ :=
        orderedContour_endpoints_mem G.blocks G.factor G.side_pos G.depth_pos hjk hx σ hb
      have sub' : ∀ p, p ∈ PeriodicLattice.refinedBlock j b.source ∪
            PeriodicLattice.refinedBlock j b.target →
          p ∈ PeriodicLattice.refinedBlock (j + 1) y := fun p hp =>
        hp.elim (fun h => refinedBlock_subset_succ G.blocks G.factor G.side_pos G.depth_pos hjk e₁ h)
          fun h => refinedBlock_subset_succ G.blocks G.factor G.side_pos G.depth_pos hjk e₂ h
      exact complexBlockFieldAtLevel_congr hS G.depth_pos G.levelwise G.support ha ha' hjk b
        fun w hw => h₂ ⟨sub' _ hw.2.1, sub' _ hw.2.2⟩
    simp only [PeriodicLattice.complexMeanContourHolonomy, e]
end Induction
theorem localDependence_holds (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hZ : BlockPathContourPivotStatement)
    (hP : LevelwiseMeans.LevelwiseMeansHold)
    (hR : SupportOfMeans.SupportOfMeansHolds)
    (hK : StepKernels.StepKernelBounds)
    (hH : StepKernelHolomorphy.StepKernelsHolomorphic) : LocalDependence := by
  intro L hL n k hn hk ρ _ hS
  have G : Hypotheses L n k :=
    ⟨hA, hZ, hL, hn, hk, (hP L hL k hk).1 n hn, (hR L hL k hk).1 n hn, hK, hH⟩
  refine ⟨fun c a ha a' ha' B hB B' hB' h₁ h₂ => ?_,
    fun y a ha a' ha' l l' _ _ h₁ h₂ =>
      iterAdjointCubeAverage_congr G hS k le_rfl y a a' l l' ha ha' h₁ h₂⟩
  simp only [Pi.smul_apply]
  rw [iterCovariantDeriv_congr G hS k le_rfl c a a' B B' ha ha' hB hB' (fun b hb => h₁ hb)
    fun b hb => h₂ hb]
end YangMills.Construction.Tower.BlockLocality
end
