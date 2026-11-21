import YangMills.Construction.Torus.ClassesOverABallTensorsAndTheCentredFunctional
import YangMills.Construction.Torus.TestFunctionsAndDistributionsOnOpenSetsOfTuples
import YangMills.Construction.TorusOrFourSpace.ClassesOfFunctionsWithSupportInASet
import YangMills.Construction.TorusOrFourSpace.PermutationsDiagonalActionsTranslationsAndInvariance
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints.Identification
section Transport
variable {s : Conventions.StandingParameters} {E : Ambient}
def headPoint (y : Tuple s E 1) : Pt s E := y 0
def complexOnSingletons (φ : Pt s E → ℂ) : Tuple s E 1 → ℂ := fun y => φ (headPoint y)
def liftFn {Z : Type*} (f : Pt s E → Z) : (kindOf E).Pt (paramsOf s) → Z :=
  f ∘ (ptEquiv s E).symm
def liftTuple {Z : Type*} {n : ℕ} (f : Fin n → Pt s E → Z) :
    Fin n → (kindOf E).Pt (paramsOf s) → Z :=
  fun i => liftFn (f i)
variable (s E) in
def tupleEquiv (p : ℕ+) :
    Tuple s E (p : ℕ) ≃ (kindOf E).Tuple (paramsOf s) p :=
  Equiv.piCongrRight fun _ => ptEquiv s E
def liftTupleFn {p : ℕ+} (F : Tuple s E (p : ℕ) → ℂ) :
    (kindOf E).Tuple (paramsOf s) p → ℂ :=
  F ∘ (tupleEquiv s E p).symm
end Transport
section Expansion
variable (s : Conventions.StandingParameters) (E : Ambient)
abbrev BallFamily (ρ : ℝ≥0∞) : Type :=
  (n : ℕ) → 2 ≤ n → ballSepTuples s E n ρ → ℝ
variable {s E} {ρ : ℝ≥0∞}
def blockTerm (Ψ : BallFamily s E ρ) {q : ℕ} (f : ballSepTuples s E q ρ)
    (J : Finset (Fin q)) : ℝ :=
  if h : 2 ≤ J.card then Ψ J.card h ⟨restrictTuple f.1 J, restrictTuple_mem_sepTuplesIn f.2 J⟩ else 0
def partitionExpansion (Ψ : BallFamily s E ρ) {q : ℕ} (f : ballSepTuples s E q ρ) : ℝ :=
  ∑ π ∈ SetPartition.singletonFree q, ∏ J ∈ π.parts, blockTerm Ψ f J
end Expansion
structure Coincidences (s : Conventions.StandingParameters) (E : Ambient) : Prop where
  pt_torus : Pt s .torus = s.Torus
  pt_euclidean : Pt s .euclidean = (Fin 4 → ℝ)
  pointDist_torus : ∀ y y' : s.Torus, pointDist s .torus y y' =
    TorusMetric.torusEuclidNorm (S := PeriodicLattice.torusSide s.L s.m) (y - y')
  pointDist_euclidean : ∀ y y' : Fin 4 → ℝ, pointDist s .euclidean y y' =
    TorusMetric.euclidNormVec (y - y')
  setDist_torus_eq : ∀ A B : Set s.Torus, setDist s .torus A B =
    TorusMetric.setEuclidDist (S := PeriodicLattice.torusSide s.L s.m) A B
  setDist_eq_iInf : ∀ A B : Set (Pt s E), setDist s E A B =
    ⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (pointDist s E a b)
  setDist_empty : ∀ A : Set (Pt s E), setDist s E A ∅ = ⊤
  proj_torus : ∀ (β : ℝ) (hβ : 0 < β) (x : Fin 4 → ℝ), proj s .torus x =
    (ConnectedFunctions.CouplingData.mk s β hβ).proj x
  supDist_single : ∀ y y' : Tuple s E 1,
    supDist y y' = pointDist s E (headPoint y) (headPoint y')
  closure_single : ∀ Z : Set (Pt s E),
    closure (headPoint ⁻¹' Z) = headPoint ⁻¹' closure Z
  isCompact_single : ∀ Z : Set (Pt s E), IsCompact (headPoint ⁻¹' Z) ↔ IsCompact Z
  continuous_comp_head : ∀ {X : Type} [PseudoMetricSpace X] (g : Pt s E → X),
    Continuous (g ∘ headPoint) ↔ Continuous g
  continuous_into_single : ∀ {X : Type} [PseudoMetricSpace X] (g : X → Tuple s E 1),
    Continuous g ↔ Continuous (headPoint ∘ g)
  closedSupport_single : ∀ φ : Pt s E → ℂ,
    closedSupport (complexOnSingletons φ) = headPoint ⁻¹' tsupport φ
  closedSupport_real_single : ∀ f : Pt s E → ℝ,
    closedSupport (asFunctionOnOnePoint f) = headPoint ⁻¹' tsupport f
  isC1_iff : ∀ f : Pt s E → ℝ,
    IsC1 f ↔ ContDiff ℝ 1 (f ∘ proj s E)
  isC1Fn_iff : ∀ f : Pt s E → ℝ,
    IsC1Fn f ↔ ContDiff ℝ 1 (f ∘ proj s E)
  c1CompactSupportIn_eq : ∀ A : Set (Pt s E),
    c1CompactSupportIn A = c1CompactlySupportedIn A
  sepTuples_eq : ∀ n, 1 ≤ n → sepTuples s E n = separatedTuples s E n
  isOpen_originBall : ∀ ρ : ℝ≥0∞, 0 < ρ → IsOpen (originBall s E ρ)
  ballSepTuples_top : ∀ n, 1 ≤ n → ballSepTuples s E n ∞ = sepTuples s E n
  restrictTuple_mem_ball : ∀ (ρ : ℝ≥0∞), 0 < ρ → ∀ q, 1 ≤ q → ∀ f ∈ ballSepTuples s E q ρ,
    ∀ J : Finset (Fin q), J.Nonempty → restrictTuple f J ∈ ballSepTuples s E J.card ρ
  blockTerm_defined : ∀ (ρ : ℝ≥0∞), 0 < ρ → ∀ q, 1 ≤ q → ∀ f ∈ ballSepTuples s E q ρ,
    ∀ π ∈ SetPartition.singletonFree q, ∀ J ∈ π.parts,
      2 ≤ J.card ∧ restrictTuple f J ∈ ballSepTuples s E J.card ρ
  partitionExpansion_connected : ∀ (S : ConnectedFamily s E) (Ψ : BallFamily s E ∞),
    (∀ (n : ℕ) (hn : 2 ≤ n) (g : ballSepTuples s E n ∞)
      (h : g.1 ∈ separatedTuples s E n), Ψ n hn g = S.fn n hn ⟨g.1, h⟩) →
    ∀ (q : ℕ), 1 ≤ q → ∀ (f : ballSepTuples s E q ∞)
      (h : f.1 ∈ separatedTuples s E q),
      partitionExpansion Ψ f = S.centredAt ⟨f.1, h⟩
  quotMap_eq : ∀ x : Fin 4 → ℝ,
    (kindOf E).quotMap (paramsOf s) x = ptEquiv s E (proj s E x)
  isLift_lift_iff : ∀ (y : Pt s E) (x : Fin 4 → ℝ),
    PeriodicSpace.Kind.IsLift (paramsOf s) (kindOf E) (ptEquiv s E y) x ↔ IsLift s E y x
  quotDist_eq : ∀ y y' : Pt s E,
    PeriodicSpace.Kind.quotDist (paramsOf s) (kindOf E) (ptEquiv s E y)
      (ptEquiv s E y') = pointDist s E y y'
  setInfDist_eq : ∀ A B : Set (Pt s E),
    PeriodicSpace.Kind.setInfDist (paramsOf s) (kindOf E) (ptEquiv s E '' A)
      (ptEquiv s E '' B) = setDist s E A B
  setDiam_eq : ∀ A : Set (Pt s E),
    PeriodicSpace.Kind.setDiam (paramsOf s) (kindOf E) (ptEquiv s E '' A) =
      setDiam s E A
  isOpenQ_iff : ∀ Z : Set (Pt s E),
    PeriodicSpace.Kind.IsOpenQ (paramsOf s) (kindOf E) (ptEquiv s E '' Z) ↔
      IsOpen (headPoint ⁻¹' Z)
  isClosedQ_iff : ∀ Z : Set (Pt s E),
    PeriodicSpace.Kind.IsClosedQ (paramsOf s) (kindOf E) (ptEquiv s E '' Z) ↔
      IsClosed (headPoint ⁻¹' Z)
  isCompactQ_iff : ∀ Z : Set (Pt s E),
    PeriodicSpace.Kind.IsCompactQ (paramsOf s) (kindOf E) (ptEquiv s E '' Z) ↔
      IsCompact (headPoint ⁻¹' Z)
  mem_periodGroup_iff : ∀ k : Fin 4 → ℝ, k ∈ (kindOf E).periodGroup (paramsOf s) ↔
    IsTuplePeriod s E 1 (flattenCoords 1 fun _ => k)
  origin_eq_proj : PeriodicSpace.Kind.origin (paramsOf s) (kindOf E) =
    ptEquiv s E (proj s E 0)
  origin_eq_zero : PeriodicSpace.Kind.origin (paramsOf s) (kindOf E) = 0
  centredBall_eq : ∀ ρ : ℝ≥0∞, 0 < ρ → ρ < ∞ →
    PeriodicSpace.Kind.centredBall (paramsOf s) (kindOf E) ρ =
      ptEquiv s E '' openBall s E (origin s E) ρ.toReal
  centredBall_top : PeriodicSpace.Kind.centredBall (paramsOf s) (kindOf E) ∞ = univ
  image_originBall : ∀ ρ : ℝ≥0∞, 0 < ρ → ptEquiv s E '' originBall s E ρ =
    PeriodicSpace.Kind.centredBall (paramsOf s) (kindOf E) ρ
  isC1Fn_lift_iff : ∀ f : Pt s E → ℝ,
    PeriodicSpace.Kind.IsC1Fn (paramsOf s) (kindOf E) (liftFn f) ↔
      IsC1 f
  supportQ_lift : ∀ φ : Pt s E → ℂ,
    (fun y : Tuple s E 1 => ptEquiv s E (headPoint y)) ⁻¹'
        PeriodicSpace.Kind.supportQ (paramsOf s) (kindOf E) (liftFn φ) =
      closedSupport (complexOnSingletons φ)
  supportQ_real_lift : ∀ f : Pt s E → ℝ,
    (fun y : Tuple s E 1 => ptEquiv s E (headPoint y)) ⁻¹'
        PeriodicSpace.Kind.supportQ (paramsOf s) (kindOf E) (liftFn f) =
      closedSupport (asFunctionOnOnePoint f)
  lift_mem_c1SupportedIn_iff : ∀ (A : Set (Pt s E)) (f : Pt s E → ℝ),
    liftFn f ∈
        PeriodicSpace.Kind.c1SupportedIn (paramsOf s) (kindOf E) (ptEquiv s E '' A) ↔
      f ∈ c1CompactSupportIn A
  lift_mem_sepC1TuplesWithin_iff : ∀ n, 1 ≤ n → ∀ O : Set (Pt s E), IsOpen O →
    ∀ f : Fin n → Pt s E → ℝ,
      liftTuple f ∈ PeriodicSpace.Kind.sepC1TuplesWithin (paramsOf s) (kindOf E) n
          (ptEquiv s E '' O) ↔
        f ∈ sepTuplesIn n O
  lift_mem_sepC1Tuples_iff : ∀ n, 1 ≤ n → ∀ f : Fin n → Pt s E → ℝ,
    liftTuple f ∈ PeriodicSpace.Kind.sepC1Tuples (paramsOf s) (kindOf E) n ↔
      f ∈ separatedTuples s E n
  restrictTuple_lift : ∀ n, 1 ≤ n → ∀ (f : Fin n → Pt s E → ℝ) (J : Finset (Fin n)), J.Nonempty →
    PeriodicSpace.Kind.restrictTuple (paramsOf s) (kindOf E) (liftTuple f) J =
      liftTuple (restrictTuple f J)
  tensorFn_lift : ∀ n, 1 ≤ n → ∀ (φ : Fin n → Pt s E → ℂ) (y : Tuple s E n),
    PeriodicSpace.Kind.tensorFn (paramsOf s) (kindOf E) (liftTuple φ)
      (fun i => ptEquiv s E (y i)) = tensorProd φ y
  partitionsNoSingletons_eq : ∀ q, 1 ≤ q →
    PeriodicSpace.partitionsNoSingletons q = SetPartition.singletonFree q
  ballSepTensors_eq_span : ∀ q, 1 ≤ q → ∀ ρ : ℝ≥0∞, 0 < ρ →
    ballSepTensors s E q ρ = Submodule.span ℂ
      {F | ∃ f ∈ ballSepTuples s E q ρ, F = tensorProd fun i y => ((f i y : ℝ) : ℂ)}
  centredFunc_lift_eq : ∀ (ρ : ℝ≥0∞), 0 < ρ →
    ∀ (Ψ : PeriodicSpace.Kind.BallMultilinearFamily (paramsOf s) (kindOf E) ρ)
      (Ψ' : BallFamily s E ρ),
    (∀ (n : ℕ) (hn : 2 ≤ n) (g : ballSepTuples s E n ρ)
      (h : liftTuple g.1 ∈ PeriodicSpace.Kind.sepC1TuplesWithin (paramsOf s)
        (kindOf E) n (PeriodicSpace.Kind.centredBall (paramsOf s) (kindOf E) ρ)),
      Ψ' n hn g = Ψ.func n hn ⟨liftTuple g.1, h⟩) →
    ∀ (q : ℕ), 1 ≤ q → ∀ (f : ballSepTuples s E q ρ)
      (h : liftTuple f.1 ∈ PeriodicSpace.Kind.sepC1TuplesWithin (paramsOf s)
        (kindOf E) q (PeriodicSpace.Kind.centredBall (paramsOf s) (kindOf E) ρ)),
      Ψ.centredFunc ⟨liftTuple f.1, h⟩ = partitionExpansion Ψ' f
  centredFunc_eq : ∀ (ρ : ℝ≥0∞), 0 < ρ → ∀ (Ψ : RealMultilinearBallFamily s E ρ) (q : ℕ),
    1 ≤ q → ∀ f : ballSepTuples s E q ρ,
      Ψ.centredFunc f = partitionExpansion Ψ.func f
  tupleProj_eq : ∀ (p : ℕ+) (x : Fin (4 * (p : ℕ)) → ℝ),
    PeriodicSpace.Kind.Tuple.proj (paramsOf s) (kindOf E) x =
      tupleEquiv s E p (tupleProj s E (p : ℕ) x)
  isOpenT_iff : ∀ (p : ℕ+) (Z : Set (Tuple s E (p : ℕ))),
    PeriodicSpace.Kind.Tuple.IsOpenT (paramsOf s) (kindOf E)
      (tupleEquiv s E p '' Z) ↔ IsOpen Z
  isClosedT_iff : ∀ (p : ℕ+) (Z : Set (Tuple s E (p : ℕ))),
    PeriodicSpace.Kind.Tuple.IsClosedT (paramsOf s) (kindOf E)
      (tupleEquiv s E p '' Z) ↔ IsClosed Z
  isCompactT_iff : ∀ (p : ℕ+) (Z : Set (Tuple s E (p : ℕ))),
    PeriodicSpace.Kind.Tuple.IsCompactT (paramsOf s) (kindOf E)
      (tupleEquiv s E p '' Z) ↔ IsCompact Z
  closureT_image : ∀ (p : ℕ+) (Z : Set (Tuple s E (p : ℕ))),
    PeriodicSpace.Kind.Tuple.closureT (paramsOf s) (kindOf E)
      (tupleEquiv s E p '' Z) = tupleEquiv s E p '' closure Z
  isClassC_iff : ∀ (p : ℕ+) (ν : ℕ) (F : Tuple s E (p : ℕ) → ℂ),
    PeriodicSpace.Kind.Tuple.IsClassC (paramsOf s) (kindOf E) ν
      (liftTupleFn F) ↔ IsCn (ν : ℕ∞) F
  partialDeriv_lift : ∀ (p : ℕ+) (ν : ℕ) (F : Tuple s E (p : ℕ) → ℂ), IsCn (ν : ℕ∞) F →
    ∀ α : PowerSeries.MultiIndex (4 * (p : ℕ)), α.order ≤ ν →
      PeriodicSpace.Kind.Tuple.partialDeriv (paramsOf s) (kindOf E) (p := p) α
        (liftTupleFn F) = liftTupleFn (multiDeriv α F)
  cNorm_lift : ∀ (p : ℕ+) (ν : ℕ) (F : Tuple s E (p : ℕ) → ℂ), IsCn (ν : ℕ∞) F →
    PeriodicSpace.Kind.Tuple.cNorm (paramsOf s) (kindOf E) ν
      (liftTupleFn F) = cnNorm ν F
  isSmoothT_iff : ∀ (p : ℕ+) (F : Tuple s E (p : ℕ) → ℂ),
    PeriodicSpace.Kind.Tuple.IsSmoothT (paramsOf s) (kindOf E)
      (liftTupleFn F) ↔ IsSmoothFn F
  supportT_lift : ∀ (p : ℕ+) (F : Tuple s E (p : ℕ) → ℂ),
    PeriodicSpace.Kind.Tuple.supportT (paramsOf s) (kindOf E)
      (liftTupleFn F) = tupleEquiv s E p '' closedSupport F
  lift_mem_testFns_iff : ∀ (p : ℕ+) (Ω : Set (Tuple s E (p : ℕ))), IsOpen Ω →
    ∀ F : Tuple s E (p : ℕ) → ℂ,
      liftTupleFn F ∈ PeriodicSpace.Kind.Tuple.testFns
          (paramsOf s) (kindOf E) (tupleEquiv s E p '' Ω) ↔
        F ∈ testFns Ω
  isDistrib_iff : ∀ (p : ℕ+) (Ω : Set (Tuple s E (p : ℕ))), IsOpen Ω →
    ∀ (T : testFns Ω → ℂ)
      (T' : PeriodicSpace.Kind.Tuple.testFns (paramsOf s) (kindOf E)
        (tupleEquiv s E p '' Ω) → ℂ),
      (∀ (F : testFns Ω)
        (G : PeriodicSpace.Kind.Tuple.testFns (paramsOf s) (kindOf E)
          (tupleEquiv s E p '' Ω)),
        G.1 = liftTupleFn F.1 → T' G = T F) →
      (PeriodicSpace.Kind.Tuple.IsDistrib T' ↔ IsDistrib T)
  pairwiseDistinct_eq : ∀ n : ℕ+,
    PeriodicSpace.Kind.pairwiseDistinct (paramsOf s) (kindOf E) n =
      tupleEquiv s E n '' pairwiseDistinctTuples s E (n : ℕ)
  addPt_eq : ∀ y v : Pt s E,
    PeriodicSpace.Kind.addPt (paramsOf s) (kindOf E) (ptEquiv s E y)
      (ptEquiv s E v) = ptEquiv s E y + ptEquiv s E v
  subPt_eq : ∀ y v : Pt s E,
    PeriodicSpace.Kind.subPt (paramsOf s) (kindOf E) (ptEquiv s E y)
      (ptEquiv s E v) = ptEquiv s E y - ptEquiv s E v
def AllCoincide : Prop := ∀ (s : Conventions.StandingParameters) (E : Ambient), Coincidences s E
end YangMills.Construction.AmbientPoints.Identification
end
