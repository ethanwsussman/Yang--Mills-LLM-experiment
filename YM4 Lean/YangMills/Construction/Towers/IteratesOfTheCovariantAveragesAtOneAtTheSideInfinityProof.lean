import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnTheWholeProof
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.CovariantIteratesAtIdentityProof
section Trivial
variable {a a' : ℝ}
theorem logSeries_one : Matrices.ComplexMatrix2.logSeries 1 = 0 := by
  simp [Matrices.ComplexMatrix2.logSeries]
theorem linkHolonomy_const_one (Γ : List (InfiniteLattice.Link a)) :
    linkHolonomy (fun _ : InfiniteLattice.Link a => (1 : Matrices.ComplexMatrix2)) Γ = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.linkHolonomy_const_one <;> assumption
theorem complexLogMean_const_one (h : Averaging.IdentityFamilyMeanIsOne) {ι : Type} [Fintype ι]
    [Nonempty ι] :
    PeriodicLattice.complexLogMean (fun _ : ι => (1 : Matrices.ComplexMatrix2)) = 1 := by
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hne : Nonempty (Fin (Fintype.card ι)) := ⟨⟨0, hn⟩⟩
  have h1 := (h _ hn).2.2
  unfold PeriodicLattice.complexLogMean at h1 ⊢
  convert h1 using 2
  funext W
  apply propext
  simp [Averaging.identityFamily, Matrices.ComplexMatrix2.IsLogMean]
variable (L : ℕ)
theorem contourHolonomies_const_one (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') :
    contourHolonomies L (fun _ : InfiniteLattice.Link a' => (1 : Matrices.ComplexMatrix2)) y x =
      fun _ => 1 :=
  funext fun _ => linkHolonomy_const_one _
theorem complexContourMean_const_one (h : Averaging.IdentityFamilyMeanIsOne)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    complexContourMean L (fun _ : InfiniteLattice.Link a' => (1 : Matrices.ComplexMatrix2)) y x =
      1 := by
  have : Nonempty (ContourOrder L y x) := ⟨(Finset.equivFin _).symm⟩
  unfold complexContourMean
  rw [contourHolonomies_const_one]
  exact complexLogMean_const_one h
theorem crossingDefect_const_one (h : Averaging.IdentityFamilyMeanIsOne)
    (c : InfiniteLattice.Link a) (x : InfiniteLattice.LatticePoint a') :
    crossingDefect L (fun _ : InfiniteLattice.Link a' => (1 : Matrices.ComplexMatrix2)) c x = 1 := by
  simp [crossingDefect, complexContourMean_const_one L h, transportAlong, linkHolonomy_const_one]
theorem complexSmoothingPositive_const_one (h : Averaging.IdentityFamilyMeanIsOne)
    (c : InfiniteLattice.Link a) :
    complexSmoothingPositive L (fun _ : InfiniteLattice.Link a' => (1 : Matrices.ComplexMatrix2))
      c = 1 := by
  simp [complexSmoothingPositive, crossingDefect_const_one L h, logSeries_one, transportAlong,
    linkHolonomy_const_one, Matrices.ComplexMatrix2.matExp]
end Trivial
section Tower
variable {L k : ℕ}
theorem smoothingMap_const_one (h : Averaging.IdentityFamilyMeanIsOne) (j : ℕ) :
    smoothingMap L k j (fun _ => (1 : Matrices.ComplexMatrix2)) = fun _ => 1 := by
  funext c
  change complexSmoothing L (fun _ => (1 : Matrices.ComplexMatrix2)) c = 1
  unfold complexSmoothing
  split_ifs
  · exact complexSmoothingPositive_const_one L h c
  · rw [complexSmoothingPositive_const_one L h c.opposite]
    simp
theorem complexIter_const_one (h : Averaging.IdentityFamilyMeanIsOne) :
    ∀ j, complexIter L k j (fun _ => (1 : Matrices.ComplexMatrix2)) = fun _ => 1
  | 0 => rfl
  | j + 1 => by
    simp only [complexIter]
    rw [complexIter_const_one h j]
    exact smoothingMap_const_one h j
theorem const_one_mem_fieldsValuedIn (j : ℕ) :
    (fun _ => (1 : Matrices.ComplexMatrix2)) ∈
      fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.one_mem_fieldsValuedIn <;> assumption
theorem const_one_mem_smallIterateFields (h : Averaging.IdentityFamilyMeanIsOne)
    (hρ : 0 < polydiscRadius L) :
    (fun _ => (1 : Matrices.ComplexMatrix2)) ∈ smallIterateFields L k := by
  refine ⟨const_one_mem_fieldsValuedIn 0, fun j _ => ?_⟩
  rw [complexIter_const_one h j]
  exact ⟨const_one_mem_fieldsValuedIn j, fun _ => by
    simpa [Matrices.ComplexMatrix2.operatorNorm] using hρ⟩
end Tower
section Real
variable {a a' : ℝ}
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (b : InfiniteLattice.Link a) : extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem mem_vertexFunctionSpace {l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2} :
    l ∈ vertexFunctionSpace a ↔ ∀ x, l x ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  simp [vertexFunctionSpace, Matrices.GroupLieProduct.hermitianTracelessFunctions,
    Submodule.mem_pi]
theorem apply_mem_hermitianTraceless {B : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace a) (b : InfiniteLattice.Link a) :
    B b ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.apply_mem_hermitianTraceless <;> assumption
theorem sumAlong_mem {B : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace a) (Γ : List (InfiniteLattice.Link a)) :
    sumAlong B Γ ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  induction Γ with
  | nil => simp [sumAlong]
  | cons b Γ ih =>
    simpa [sumAlong] using
      Matrices.ComplexMatrix2.hermitianTraceless.add_mem (apply_mem_hermitianTraceless hB b) ih
theorem ofReal_smul_mem_hermitianTraceless {r : ℝ} {X : Matrices.ComplexMatrix2}
    (h : X ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    (r : ℂ) • X ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_smul_mem_hermitianTraceless <;> assumption
theorem weight_smul_finsum_mem (L : ℕ) {ι : Type} {s : Set ι} {f : ι → Matrices.ComplexMatrix2}
    (h : ∀ x ∈ s, f x ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ s, f x ∈
      Matrices.ComplexMatrix2.hermitianTraceless :=
  ofReal_smul_mem_hermitianTraceless
    (finsum_mem_induction (fun X => X ∈ Matrices.ComplexMatrix2.hermitianTraceless)
      Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
      (fun _ _ => Matrices.ComplexMatrix2.hermitianTraceless.add_mem) h)
theorem contourAverage_mem (L : ℕ) {B : InfiniteLattice.Link a' → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace a') (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') :
    _root_.YangMills.Construction.Tower.FullSpace.contourAverage L B y x ∈ Matrices.ComplexMatrix2.hermitianTraceless :=
  ofReal_smul_mem_hermitianTraceless (sum_mem fun _ _ => sumAlong_mem hB _)
theorem cubeContourAverage_mem (L : ℕ) {B : InfiniteLattice.Link a' → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace a') : cubeContourAverage (a := a) L B ∈ vertexFunctionSpace a :=
  mem_vertexFunctionSpace.2 fun _ =>
    weight_smul_finsum_mem L fun _ _ => contourAverage_mem L hB _ _
theorem vertexSmoothing_mem (L : ℕ)
    {l : InfiniteLattice.LatticePoint a' → Matrices.ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace a') : vertexSmoothing (a := a) L l ∈ vertexFunctionSpace a :=
  mem_vertexFunctionSpace.2 fun _ =>
    weight_smul_finsum_mem L fun _ _ => mem_vertexFunctionSpace.1 hl _
theorem restrictVertexFunction_mem
    {l : InfiniteLattice.LatticePoint a' → Matrices.ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace a') : restrictVertexFunction a l ∈ vertexFunctionSpace a :=
  mem_vertexFunctionSpace.2 fun _ => mem_vertexFunctionSpace.1 hl _
theorem vertexCoboundary_mem {l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace a) : vertexCoboundary l ∈ edgeFormSpace a := by apply _root_.YangMills.Construction.Tower.FullSpace.OneStepComplexForms.vertexCoboundary_mem_edgeFormSpace <;> assumption
end Real
section Additive
variable {a a' : ℝ}
theorem sumAlong_sub (A C : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (Γ : List (InfiniteLattice.Link a)) :
    sumAlong (A - C) Γ = sumAlong A Γ - sumAlong C Γ := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.sumAlong_sub <;> assumption
theorem contourAverage_sub (L : ℕ) (A C : InfiniteLattice.Link a' → Matrices.ComplexMatrix2)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    _root_.YangMills.Construction.Tower.FullSpace.contourAverage L (A - C) y x = _root_.YangMills.Construction.Tower.FullSpace.contourAverage L A y x - _root_.YangMills.Construction.Tower.FullSpace.contourAverage L C y x := by
  simp only [_root_.YangMills.Construction.Tower.FullSpace.contourAverage, sumAlong_sub, Finset.sum_sub_distrib, smul_sub]
theorem cubeContourAverage_sub (L : ℕ)
    (hfin : ∀ y : InfiniteLattice.LatticePoint a, (cubeVertices L a' y).Finite)
    (A C : InfiniteLattice.Link a' → Matrices.ComplexMatrix2) :
    cubeContourAverage (a := a) L (A - C) = cubeContourAverage L A - cubeContourAverage L C := by
  funext y
  simp only [cubeContourAverage, Pi.sub_apply, contourAverage_sub]
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
    finsum_mem_eq_finite_toFinset_sum _ (hfin y), Finset.sum_sub_distrib, smul_sub]
theorem cubeVertices_finite {L k i : ℕ} (hZ : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hi : i < k) (y : Vertex L k (i + 1)) :
    (cubeVertices L (meshAt L k i) y).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldSteps.cubeVertices_finite <;> assumption
theorem coe_toFiner {y : InfiniteLattice.LatticePoint a}
    (h : (y : InfiniteLattice.AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a') :
    ((toFiner a' y : InfiniteLattice.LatticePoint a') : InfiniteLattice.AmbientSpace) = y := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.coe_toFiner <;> assumption
theorem restrictVertexFunction_self (l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    restrictVertexFunction a l = l := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.restrict_self <;> assumption
theorem restrictVertexFunction_restrictVertexFunction {a₁ a₂ a₃ : ℝ}
    (h₂ : InfiniteLattice.latticeSubgroup a₃ ≤ InfiniteLattice.latticeSubgroup a₂)
    (h₁ : InfiniteLattice.latticeSubgroup a₃ ≤ InfiniteLattice.latticeSubgroup a₁)
    (l : InfiniteLattice.LatticePoint a₁ → Matrices.ComplexMatrix2) :
    restrictVertexFunction a₃ (restrictVertexFunction a₂ l) = restrictVertexFunction a₃ l := by
  funext x
  change l (toFiner a₁ (toFiner a₂ x)) = l (toFiner a₁ x)
  congr 1
  apply Subtype.ext
  have e₂ : ((toFiner a₂ x : InfiniteLattice.LatticePoint a₂) : InfiniteLattice.AmbientSpace) = x :=
    coe_toFiner (h₂ x.2)
  rw [coe_toFiner (by rw [e₂]; exact h₁ x.2), e₂, coe_toFiner (h₁ x.2)]
theorem cubeContourAverageIter_succ {L k j : ℕ} (hj : j + 1 ≤ k)
    (hnest : SublatticesNested L k) (B : Edge L k 0 → Matrices.ComplexMatrix2) :
    cubeContourAverageIter L k (j + 1) B =
      restrictVertexFunction (meshAt L k (j + 1)) (cubeContourAverageIter L k j B) +
        cubeContourAverage (a := meshAt L k (j + 1)) L (crossingSmoothingIter L k j B) := by
  unfold cubeContourAverageIter
  rw [Finset.sum_range_succ, restrictVertexFunction_self]
  congr 1
  funext x
  change _ = (∑ i ∈ Finset.range j, restrictVertexFunction (meshAt L k j)
    (cubeContourAverage L (a := meshAt L k (i + 1)) (crossingSmoothingIter L k i B)))
      (toFiner (meshAt L k j) x)
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  exact (congrFun (restrictVertexFunction_restrictVertexFunction (hnest j (j + 1) (by omega) hj)
    (hnest (i + 1) (j + 1) (by omega) hj) _) x).symm
end Additive
section Induction
variable {L k : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (j : ℕ) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.meshAt_pos <;> assumption
theorem crossingSmoothing_mem {i : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    {X : Edge L k i → Matrices.ComplexMatrix2} (hX : X ∈ edgeFormSpace (meshAt L k i))
    (h₁ : linearSmoothing (a := meshAt L k (i + 1)) L X =
      crossingSmoothing (a := meshAt L k (i + 1)) L X -
        vertexCoboundary (cubeContourAverage (a := meshAt L k (i + 1)) L X))
    (h₂ : complexSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) X =
      linearSmoothing (a := meshAt L k (i + 1)) L X) :
    crossingSmoothing (a := meshAt L k (i + 1)) L X ∈ edgeFormSpace (meshAt L k (i + 1)) := by
  refine ⟨fun c _ => weight_smul_finsum_mem L fun _ _ => sumAlong_mem hX _, fun b => ?_⟩
  have e : crossingSmoothing (a := meshAt L k (i + 1)) L X =
      complexSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) X +
        vertexCoboundary (cubeContourAverage (a := meshAt L k (i + 1)) L X) := by
    rw [h₂, h₁, sub_add_cancel]
  have hd : ∀ l : Vertex L k (i + 1) → Matrices.ComplexMatrix2,
      vertexCoboundary l b.opposite = -vertexCoboundary l b := fun l => by
    change l b.initial - l b.terminal = -(l b.terminal - l b.initial)
    abel
  rw [e]
  simp only [Pi.add_apply, hd, neg_add]
  congr 1
  unfold complexSmoothingDeriv holLeftDifferential
  exact extendOddly_opposite (meshAt_pos hL _) _ b
variable (hM : Averaging.IdentityFamilyMeanIsOne) (hZ : BlockStructure)
  (hS : SmoothingStepAtOne)
  (hR : TrivialLinearization.AllRelationsStatement) (hP : CovariantSmoothingProperties.Statement)
  (hF : LeftChartFacts.HoldEverywhere)
  (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
  (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
include hM hP hF hA in
theorem complexIterDeriv_at_one (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ}
    (hj : j ≤ k) {B : Edge L k 0 → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace (meshAt L k 0)) :
    complexIterDeriv L k j (fun _ => 1) B =
      iterCovariantDeriv L k (fun _ => 1) j B -
        vertexCoboundary (iterContourLogDrift L k (fun _ => 1) j B) := by
  have hρ : 0 < polydiscRadius L := (hA.1 L hL).2.2.pos
  have h := ((((hP L hL).2 k).2 j hj).1 _ (const_one_mem_smallIterateFields hM hρ)).1 B
    ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
  rw [complexIter_const_one hM j, (hF L k j j j hL hj hj hj).2.2.2.2.2.1.2] at h
  rw [h, add_sub_cancel_right]
include hM hZ hS hR hP hF hA hT in
theorem iterates_on_edgeForms (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 0 < k)
    {B : Edge L k 0 → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace (meshAt L k 0)) :
    ∀ j, j ≤ k → crossingSmoothingIter L k j B ∈ edgeFormSpace (meshAt L k j) ∧
      cubeContourAverageIter L k j B ∈ vertexFunctionSpace (meshAt L k j) ∧
      iterCovariantDeriv L k (fun _ => 1) j B = crossingSmoothingIter L k j B ∧
      iterContourLogDrift L k (fun _ => 1) j B = cubeContourAverageIter L k j B := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨hB, ?_, rfl, ?_⟩
    · simp [cubeContourAverageIter]
    · simp [cubeContourAverageIter, iterContourLogDrift]
  | succ j ih =>
    intro hj
    have hjk : j < k := by omega
    obtain ⟨hc, hn, hq, hd⟩ := ih (by omega)
    have hnest : SublatticesNested L k :=
      (hT L (by have := hL.2; omega) hL k).2.1
    obtain ⟨hf, hs⟩ := hS L hL k j hjk
    obtain ⟨-, -, -, -, hIt, -⟩ := ((hR L hL).2 k 0 j hk (by omega))
    obtain ⟨hS₁, -, -, -, -, -⟩ := ((hR L hL).2 k j 0 hjk (by omega))
    have hlin := (hIt B hB).1
    have hcid : complexIterDeriv L k j (fun _ => 1) B = linearSmoothingIter L k j B := by
      rw [complexIterDeriv_at_one hM hP hF hA hL (by omega) hB, hq, hd, hlin]
    have hlinF : linearSmoothingIter L k j B ∈ edgeFormSpace (meshAt L k j) := by
      rw [hlin]
      exact (edgeFormSpace _).sub_mem hc (vertexCoboundary_mem hn)
    have hone := complexIter_const_one (L := L) (k := k) hM j
    have hcr : crossingSmoothingIter L k (j + 1) B ∈ edgeFormSpace (meshAt L k (j + 1)) :=
      crossingSmoothing_mem hL hc (hS₁.1 _ hc) (hf _ hc).1
    have hnext := cubeContourAverageIter_succ hj hnest B
    refine ⟨hcr, ?_, ?_, ?_⟩
    · rw [hnext]
      exact (vertexFunctionSpace _).add_mem (restrictVertexFunction_mem hn)
        (cubeContourAverage_mem L hc)
    · change covariantSmoothingDeriv (complexIter L k j fun _ => 1)
        (iterCovariantDeriv L k (fun _ => 1) j B) = _
      rw [hone, hq]
      exact (hf _ hc).2.2
    · change adjointCubeAverage (complexIter L k j fun _ => 1)
          (iterContourLogDrift L k (fun _ => 1) j B) +
        contourLogDrift (complexIter L k j fun _ => 1)
          (complexIterDeriv L k j (fun _ => 1) B) = _
      rw [hone, hd, hcid, hs _ hn, (hf _ hlinF).2.1, hlin,
        cubeContourAverage_sub L (fun y => cubeVertices_finite hZ hL hjk y),
        (hS₁.2 _ hn).2.2.1, hnext]
      abel
include hM hS in
theorem iterates_on_vertexFunctions (hL : Conventions.IsAdmissibleBlockingFactor L)
    {l : Vertex L k 0 → Matrices.ComplexMatrix2} (hl : l ∈ vertexFunctionSpace (meshAt L k 0)) :
    ∀ j, j ≤ k → vertexSmoothingIter L k j l ∈ vertexFunctionSpace (meshAt L k j) ∧
      iterAdjointCubeAverage L k (fun _ => 1) j l = vertexSmoothingIter L k j l := by
  intro j
  induction j with
  | zero => exact fun _ => ⟨hl, rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨hm, he⟩ := ih (by omega)
    refine ⟨vertexSmoothing_mem L hm, ?_⟩
    change adjointCubeAverage (complexIter L k j fun _ => 1)
      (iterAdjointCubeAverage L k (fun _ => 1) j l) = _
    rw [complexIter_const_one hM j, he]
    exact (hS L hL k j (by omega)).2 _ hm
end Induction
theorem covariantIteratesAtIdentity (hS : SmoothingStepAtOne)
    (hP : CovariantSmoothingProperties.Statement)
    (hR : TrivialLinearization.AllRelationsStatement)
    (hF : LeftChartFacts.HoldEverywhere)
    (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hZ : BlockStructure)
    (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hM : Averaging.IdentityFamilyMeanIsOne) :
    CovariantIteratesAtIdentity := by
  intro L hL k j hk hj
  refine ⟨fun B hB => ?_, fun l hl => (iterates_on_vertexFunctions hM hS hL hl j hj).2⟩
  obtain ⟨-, -, hq, hd⟩ := iterates_on_edgeForms hM hZ hS hR hP hF hA hT hL hk hB j hj
  refine ⟨?_, hq, hd⟩
  obtain ⟨-, -, -, -, hIt, -⟩ := ((hR L hL).2 k 0 j hk hj)
  rw [complexIterDeriv_at_one hM hP hF hA hL hj hB, hq, hd, (hIt B hB).1]
end YangMills.Construction.Tower.FullSpace.CovariantIteratesAtIdentityProof
end
