import YangMills.Construction.QuaternionicWilsonModel.TheArgumentsLieInTheirDomainsProof
import Reconstruction.MinkowskiSpace.ArgumentsOfTheFieldProductsOfAWightmanTheoryLieInTheirDomains
import Reconstruction.Predicates

set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ConditionDomains
open YangMills.Construction.ConfigSpace YangMills.Construction.SystemsWithFiveBounds
open YangMills.Construction.SeparatedTuples (TupleFunctional)
open YangMills.Construction.MinkowskiSpace (poincareMul spacelikeSet)
open YangMills.Construction.WightmanTheory (PoincareElt TestFn HermitianScalarTheory
  IsAnalyticContinuationData wickDiffs tubeTuples)
structure TheoryIdentitiesEverywhere : Prop where
  rep_mul : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : HermitianScalarTheory H) (g g' : PoincareElt), ∃ g'' : PoincareElt,
      g''.1 = poincareMul g.1 g'.1 ∧ W.rep g'' = W.rep g * W.rep g'
  field_linComb : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : HermitianScalarTheory H) (a b : ℂ) (f f' : TestFn), ∃ f'' : TestFn,
      f''.1 = a • f.1 + b • f'.1 ∧ W.field f'' = a • W.field f + b • W.field f'
  ordered_mem_tube : ∀ (m : ℕ) (ς : Equiv.Perm (Fin (m + 1))), (∃ x : TestSpaces.PointTuple (m + 1),
      TestSpaces.rotatePermute 1 ς x ∈ TestSpaces.increasingTimes (m + 1)) ∧
    ∀ x : TestSpaces.PointTuple (m + 1),
      TestSpaces.rotatePermute 1 ς x ∈ TestSpaces.increasingTimes (m + 1) →
        wickDiffs (TestSpaces.rotatePermute 1 ς x) ∈ tubeTuples m
  schwinger_values : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : HermitianScalarTheory H) (T : FlatSequence) (m : ℕ)
    (w : (Fin m → MinkowskiSpace.ComplexVec4) → ℂ)
    (q : ℕ) (c : ℝ) (s : TestSpaces.PointTuple (m + 1) → ℂ), IsAnalyticContinuationData W T m w q c s →
      ∀ φ ∈ TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus (m + 1)),
        ∃ h : φ ∈ schwartzFlatOffDiagonal (m + 1),
          MeasureTheory.Integrable (fun x : TestSpaces.PointTuple (m + 1) => s x * φ x) ∧
            T.atSucc m ⟨φ, h⟩ = ∫ x : TestSpaces.PointTuple (m + 1), s x * φ x
  exists_spacelike : ∃ f h : TestFn, f.1 ≠ 0 ∧ h.1 ≠ 0 ∧
    ∀ x ∈ tsupport f.1, ∀ y ∈ tsupport h.1, x - y ∈ spacelikeSet
def Statement : Prop :=
  DomainsContainArguments ∧ ArgumentsNotAllZero ∧
    (∀ (σ : TupleFunctional) (T : FlatSequence), HasSchwingerSequence σ T →
      SequenceIdentitiesEverywhere (evalOnSepFamily σ) T ∧
        ∀ K : LimitConstants, OSAxioms K T → AxiomsEverywhere T) ∧
    (∀ (M ϑ d₀ : ℝ) (ηBar : ℝ → ℝ) (K : LimitConstants) (σ : TupleFunctional),
      ComponentProperties M ϑ d₀ ηBar K σ →
        ∃ T : FlatSequence, HasSchwingerSequence σ T ∧ OSAxioms K T ∧
          IsWightmanSchwingerSequence T ∧ AxiomsEverywhere T) ∧
    TheoryIdentitiesEverywhere ∧ WightmanTheory.DomainFacts.Statement
end YangMills.Construction.ConditionDomains
end

set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate ContDiff
noncomputable section
namespace YangMills.Construction.ConditionDomains
open ConfigSpace SystemsWithFiveBounds
open SeparatedTuples (TupleFunctional)
open WightmanTheory (TestFn)
def bumpTestFn (hC : CompactSupportTensorFacts) (c : Fin 4 → ℝ) : TestFn :=
  ⟨fun u => (((unitBump c) u : ℝ) : ℂ),
    ((hC 1 le_rfl).1 _ (unitBump_mem_realSmoothCompactIn c).1 _ (unitBump_mem_realSmoothCompactIn c)).1⟩
theorem bumpTestFn_ne_zero (hC : CompactSupportTensorFacts) (c : Fin 4 → ℝ) :
    (bumpTestFn hC c).1 ≠ 0 := by
  intro h
  have h' := congrFun h c
  have h'' : (((unitBump c) c : ℝ) : ℂ) = 0 := h'
  rw [unitBump_self] at h''
  simp at h''
theorem tsupport_bumpTestFn (hC : CompactSupportTensorFacts) (c : Fin 4 → ℝ) :
    tsupport (bumpTestFn hC c).1 = Metric.closedBall c (1 / 2) := by
  rw [← tsupport_unitBump]
  unfold tsupport
  congr 1
  ext u
  simp [bumpTestFn]
theorem sub_mem_spacelikeSet_of_mem_closedBall {x y : Fin 4 → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin 4 → ℝ) (1 / 2))
    (hy : y ∈ Metric.closedBall (Pi.single 1 10 : Fin 4 → ℝ) (1 / 2)) :
    x - y ∈ MinkowskiSpace.spacelikeSet := by
  have hx' := Metric.mem_closedBall.1 hx
  have hy' := Metric.mem_closedBall.1 hy
  have a₀ := (dist_le_pi_dist x 0 0).trans hx'
  have a₁ := (dist_le_pi_dist x 0 1).trans hx'
  have b₀ := (dist_le_pi_dist y (Pi.single 1 10) 0).trans hy'
  have b₁ := (dist_le_pi_dist y (Pi.single 1 10) 1).trans hy'
  simp only [Real.dist_eq, Pi.zero_apply, sub_zero] at a₀ a₁
  simp only [Real.dist_eq] at b₀ b₁
  have e₀ : (Pi.single 1 10 : Fin 4 → ℝ) 0 = 0 := by simp
  have e₁ : (Pi.single 1 10 : Fin 4 → ℝ) 1 = 10 := by simp
  rw [e₀, sub_zero] at b₀
  rw [e₁] at b₁
  have ha₀ := abs_le.1 a₀
  have ha₁ := abs_le.1 a₁
  have hb₀ := abs_le.1 b₀
  have hb₁ := abs_le.1 b₁
  show MinkowskiSpace.IsSpacelikeVec (x - y)
  rw [MinkowskiSpace.isSpacelikeVec_iff]
  unfold MinkowskiSpace.spaceNorm
  rw [gt_iff_lt, Real.lt_sqrt (abs_nonneg _), sq_abs]
  simp only [Fin.sum_univ_three, MinkowskiSpace.spacePart, Pi.sub_apply]
  have h₀ : (x 0 - y 0) ^ 2 ≤ 1 := by nlinarith [ha₀.1, ha₀.2, hb₀.1, hb₀.2]
  have h₁ : (81 : ℝ) ≤ (x (Fin.succ 0) - y (Fin.succ 0)) ^ 2 := by
    have e : (Fin.succ 0 : Fin 4) = 1 := rfl
    rw [e]
    nlinarith [ha₁.1, ha₁.2, hb₁.1, hb₁.2]
  nlinarith [sq_nonneg (x (Fin.succ 1) - y (Fin.succ 1)), sq_nonneg (x (Fin.succ 2) - y (Fin.succ 2))]
def timeOrderedConfig {m : ℕ} (ς : Equiv.Perm (Fin (m + 1))) : TestSpaces.PointTuple (m + 1) :=
  fun i => Pi.single 3 (((ς.symm i : Fin (m + 1)) : ℕ) : ℝ)
theorem rotatePermute_timeOrderedConfig_mem {m : ℕ} (ς : Equiv.Perm (Fin (m + 1))) :
    TestSpaces.rotatePermute 1 ς (timeOrderedConfig ς) ∈ TestSpaces.increasingTimes (m + 1) := by
  intro a b hab
  have h : ∀ i : Fin (m + 1), TestSpaces.timeCoord
      (TestSpaces.rotatePermute 1 ς (timeOrderedConfig ς)) i = ((i : ℕ) : ℝ) := by
    intro i
    simp [TestSpaces.rotatePermute, timeOrderedConfig, TestSpaces.timeCoord]
  rw [h, h]
  exact_mod_cast hab
theorem theoryIdentitiesEverywhere_of (hC : CompactSupportTensorFacts)
    (hW : WightmanTheory.DomainFacts.Statement) :
    TheoryIdentitiesEverywhere := by
  obtain ⟨hprod, hcomb, -, heuc, hsmooth, -⟩ := hW
  exact
    { rep_mul := fun H _ _ _ W g g' =>
        ⟨⟨_, hprod g g'⟩, rfl, W.rep_mul _ _ _ rfl⟩
      field_linComb := fun H _ _ _ W a b f f' =>
        ⟨⟨_, hcomb a b f f'⟩, rfl, W.field_linear a b f f' _ rfl⟩
      ordered_mem_tube := fun m ς => ⟨⟨_, rotatePermute_timeOrderedConfig_mem ς⟩, fun x hx => heuc m _ hx⟩
      schwinger_values := fun H _ _ _ W T m w q c s hs φ hφ =>
        ⟨hsmooth m φ hφ, hs.schwinger_values ⟨φ, hsmooth m φ hφ⟩ hφ⟩
      exists_spacelike := ⟨bumpTestFn hC 0, bumpTestFn hC (Pi.single 1 10), bumpTestFn_ne_zero hC _,
        bumpTestFn_ne_zero hC _, fun x hx y hy => by
          rw [tsupport_bumpTestFn] at hx hy
          exact sub_mem_spacelikeSet_of_mem_closedBall hx hy⟩ }
theorem statement_holds (hA : domainsAndFiniteSumsStatement)
    (hL : FlatSpaceClosure)
    (hW : WightmanTheory.DomainFacts.Statement)
    (hC : CompactSupportTensorFacts)
    (hS : OpenLociAndFlatSubspaces)
    (reconstruct : ∀ {σ T}, LimitTheorem.ComponentFieldData σ → HasSchwingerSequence σ T →
      IsWightmanSchwingerSequence T) : Statement := by
  have hD := domainsContainArguments_of hA hL
  have hseq : ∀ {σ : TupleFunctional} {T : FlatSequence}, HasSchwingerSequence σ T →
      IsLinearFunctionalSeq T := fun h => ⟨h.2.1, fun m => (h.2.2 m).1.1⟩
  have hcl : ∀ {K : LimitConstants} {σ : TupleFunctional} {T : FlatSequence},
      HasSchwingerSequence σ T → OSAxioms K T → AxiomsEverywhere T :=
    fun h six => axiomsEverywhere_of hD (hseq h) six.euclidInv six.osPositive
      six.permSymm six.cluster six.reality
  refine ⟨hD, argumentsNotAllZero_of hS hC, fun σ T h => ⟨sequenceIdentitiesEverywhere_of hD h, fun K six =>
    hcl h six⟩, fun M ϑ d₀ ηBar K σ hc => ?_, theoryIdentitiesEverywhere_of hC hW, hW⟩
  obtain ⟨T, hT, -⟩ := hc.growth
  have six := hc.componentOS T hT
  exact ⟨T, hT, six, reconstruct hc.fieldData hT, hcl hT six⟩
end YangMills.Construction.ConditionDomains
end
