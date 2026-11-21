import YangMills.Construction.GrowingTori.BoundFunctionsHierarchiesAndCentredMomentsOfFourSpace
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriLimits
namespace TestTupleClass
def region : TestTupleClass → Set (Fin 4 → ℝ)
  | sep => univ
  | ball ρ _ => ballOrigin ρ
def lipSubmodule (A : Set (Fin 4 → ℝ)) : Submodule ℝ RealFn where
  carrier := lipSuppIn A
  zero_mem' := by
    have h : fnSupport (0 : RealFn) = ∅ := by simp [fnSupport]
    refine ⟨⟨0, le_rfl, fun x y => by simp⟩, ?_, ?_⟩ <;> simp [h]
  add_mem' := by
    rintro f g ⟨⟨C, hC, hf⟩, cf, sf⟩ ⟨⟨C', hC', hg⟩, cg, sg⟩
    have hsub : fnSupport (f + g) ⊆ fnSupport f ∪ fnSupport g :=
      closure_minimal
        (fun x hx => by
          by_cases h : f x = 0
          · refine Or.inr (subset_closure fun h' => hx ?_)
            simp [h, h']
          · exact Or.inl (subset_closure h))
        (isClosed_closure.union isClosed_closure)
    refine ⟨⟨C + C', add_nonneg hC hC', fun x y => ?_⟩,
      (cf.union cg).of_isClosed_subset isClosed_closure hsub,
      hsub.trans (union_subset sf sg)⟩
    calc ‖(f + g) x - (f + g) y‖ = ‖(f x - f y) + (g x - g y)‖ := by
          simp only [Pi.add_apply]
          congr 1
          ring
      _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
      _ ≤ _ := by
          rw [add_mul]
          exact add_le_add (hf x y) (hg x y)
  smul_mem' := by
    rintro c f ⟨⟨C, hC, hf⟩, cf, sf⟩
    have hsub : fnSupport (c • f) ⊆ fnSupport f :=
      closure_mono fun x hx h => hx (by simp [h])
    refine ⟨⟨|c| * C, mul_nonneg (abs_nonneg c) hC, fun x y => ?_⟩,
      cf.of_isClosed_subset isClosed_closure hsub, hsub.trans sf⟩
    calc ‖(c • f) x - (c • f) y‖ = |c| * ‖f x - f y‖ := by
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, norm_mul, Real.norm_eq_abs]
      _ ≤ |c| * (C * _) := mul_le_mul_of_nonneg_left (hf x y) (abs_nonneg c)
      _ = _ := by ring
def entrySubmodule (s : Conventions.StandingParameters) : TestTupleClass → Set (Fin 4 → ℝ) →
    Submodule ℝ RealFn
  | sep, A => AmbientPoints.c1Submodule (s := s) (E := .euclidean) A
  | ball _ _, A => lipSubmodule A
theorem prod_mem_members (s : Conventions.StandingParameters) (K : TestTupleClass) {n : ℕ}
    {A : Fin n → Set (Fin 4 → ℝ)}
    (hO : ∀ l, A l ⊆ K.region) (hA : Pairwise fun l k => PosSeparated (A l) (A k))
    (g : (l : Fin n) → K.entrySubmodule s (A l)) :
    (fun l => (g l : RealFn)) ∈ K.members s n := by
  cases K with
  | sep =>
    exact AmbientPoints.mem_separatedTuples_of_forall_mem_c1 (s := s)
      (E := .euclidean) hA fun l => (g l).2
  | ball ρ hρ =>
    refine ⟨⟨fun l => (g l).2.1, fun l => (g l).2.2.1, fun l k hlk => ?_⟩,
      fun l => (g l).2.2.2.trans (hO l)⟩
    exact (AmbientPoints.PositivelySeparated.disjoint (s := s) (E := .euclidean)
      (hA hlk)).mono (g l).2.2.2 (g k).2.2.2
def IsMultilinearOnProducts (s : Conventions.StandingParameters) (K : TestTupleClass) {n : ℕ}
    (Ψ : K.members s n → ℝ) : Prop :=
  ∀ (A : Fin n → Set (Fin 4 → ℝ)) (hO : ∀ l, A l ⊆ K.region)
    (hA : Pairwise fun l k => PosSeparated (A l) (A k)),
    ∃ Λ : MultilinearMap ℝ (fun l => K.entrySubmodule s (A l)) ℝ,
      ∀ g, Λ g = Ψ ⟨fun l => (g l : RealFn), K.prod_mem_members s hO hA g⟩
def periodicClass (D : PeriodicSpace.Params) (K : TestTupleClass) (n : ℕ) :
    Set (PeriodicSpace.Kind.FnTuple D .euclidean n) :=
  match K with
  | sep =>
    PeriodicSpace.Kind.sepC1TuplesWithin D .euclidean n
      (PeriodicSpace.Kind.centredBall D .euclidean ∞)
  | ball ρ _ =>
    PeriodicSpace.Kind.sepLipTuplesWithin D .euclidean n
      (PeriodicSpace.Kind.centredBall D .euclidean (ENNReal.ofReal ρ))
end TestTupleClass
namespace NonlinearDomain
def AgreeOnCommon {n : ℕ} {S S' : Set (Fin n → RealFn)} (Ψ : S → ℝ) (Ψ' : S' → ℝ) : Prop :=
  ∀ f (hf : f ∈ S) (hf' : f ∈ S'), Ψ ⟨f, hf⟩ = Ψ' ⟨f, hf'⟩
def UpdateStaysInClass (s : Conventions.StandingParameters) : Prop :=
  ∀ (K : TestTupleClass) (n : ℕ) (i : Fin n) (h h' : K.members s n),
    (∀ l, l ≠ i → h.1 l = h'.1 l) → ∀ α α' : ℝ,
      Function.update h.1 i (α • h.1 i + α' • h'.1 i) ∈ K.members s n
def MultilinearIffOnProducts (D : TorusTransport.TransportData) : Prop :=
  ∀ (K : TestTupleClass) (n : ℕ) (hn : 1 ≤ n) (Ψ : K.members D.toStandingParameters n → ℝ),
    IsClassMultilinear D K hn Ψ ↔ K.IsMultilinearOnProducts D.toStandingParameters Ψ
def OnProductsIffTupleMultilinear (s : Conventions.StandingParameters) : Prop :=
  ∀ (n : ℕ) (_ : 1 ≤ n) (Ψ : TestTupleClass.sep.members s n → ℝ),
    TestTupleClass.sep.IsMultilinearOnProducts s Ψ ↔
      AmbientPoints.IsTupleMultilinear (s := s) (E := .euclidean) Ψ
def PartialFamilyTransportsAgree (D : TorusTransport.TransportData) : Prop :=
  ∀ (L n : ℕ) (hn : 2 ≤ n) (ρ : ℝ) (hρ : 0 < ρ) (Ψ : GrowingTori.lipTuplesInBall L n ρ → ℝ)
    (Ψ' : (TestTupleClass.ball ρ hρ).members D.toStandingParameters n → ℝ), AgreeOnCommon Ψ Ψ' →
      (GrowingTori.IsMultilinearOnTuples hn Ψ ↔
        IsClassMultilinear D (.ball ρ hρ) (by omega : 1 ≤ n) Ψ') ∧
      (GrowingTori.IsSymmetricOnTuples Ψ ↔
        IsClassSymmetric D.toStandingParameters (.ball ρ hρ) Ψ')
def PartialHierarchyEquivExplicit (D : TorusTransport.TransportData) : Prop :=
  ∀ (L : ℕ) (ρ : ℝ) (hρ : 0 < ρ),
    ∃ e : PartialHierarchy L ρ ≃ ExplicitPartialHierarchy D ρ hρ,
      ∀ (Φ : PartialHierarchy L ρ) (n : ℕ) (hn : 2 ≤ n),
        AgreeOnCommon (Φ.phi n hn) ((e Φ).func n hn)
def EqZeroOfEntryEqZero (D : TorusTransport.TransportData) : Prop :=
  ∀ (K : TestTupleClass) (n : ℕ) (hn : 1 ≤ n) (Ψ : K.members D.toStandingParameters n → ℝ),
    IsClassMultilinear D K hn Ψ →
      ∀ (h : K.members D.toStandingParameters n) (i : Fin n), h.1 i = 0 → Ψ h = 0
def PartialCentredMomentsSymmMultilinear (D : TorusTransport.TransportData) : Prop :=
  ∀ (L : ℕ) (ρ : ℝ) (Φ : PartialHierarchy L ρ) (q : ℕ) (hq : 1 ≤ q),
    IsClassSymmetric D.toStandingParameters (.ball ρ Φ.radius_pos) (n := q)
        (fun h => centredMomentOf Φ h) ∧
      IsClassMultilinear D (.ball ρ Φ.radius_pos) hq (fun h => centredMomentOf Φ h)
def CentredMomentsSymmMultilinear (D : TorusTransport.TransportData)
    (Y : PeriodicSpace.Params) : Prop :=
  ∀ (Φ : EuclidHierarchy Y) (q : ℕ) (hq : 1 ≤ q)
    (Ψ : TestTupleClass.sep.members D.toStandingParameters q → ℝ),
    AgreeOnCommon Ψ (Φ.partitionMoment (p := q)) →
      IsClassSymmetric D.toStandingParameters .sep Ψ ∧ IsClassMultilinear D .sep hq Ψ
def ExplicitHierarchyEquivSymmConnected (D : TorusTransport.TransportData) : Prop :=
  ∃ e : ExplicitHierarchy D ≃
      {S : AmbientPoints.ConnectedFamily D.toStandingParameters .euclidean //
        ∀ n hn, AmbientPoints.IsTupleSymmetric (S.fn n hn)},
    ∀ (Φ : ExplicitHierarchy D) (n : ℕ) (hn : 2 ≤ n)
      (f : TestTupleClass.sep.members D.toStandingParameters n),
      (e Φ).1.fn n hn f = Φ.func n hn f
def PartitionMomentEqCentred (s : Conventions.StandingParameters)
    (Y : PeriodicSpace.Params) : Prop :=
  ∀ (Φ : EuclidHierarchy Y)
    (S : AmbientPoints.ConnectedFamily s .euclidean),
    (∀ (n : ℕ) (hn : 2 ≤ n), AgreeOnCommon (Φ.func n hn) (S.fn n hn)) →
      ∀ (q : ℕ) (f : Fin q → RealFn)
        (hf : f ∈ PeriodicSpace.Kind.sepC1Tuples Y .euclidean q)
        (hg : f ∈ AmbientPoints.separatedTuples s .euclidean q),
        Φ.partitionMoment ⟨f, hf⟩ = S.centred (AmbientPoints.toAllSeparated ⟨f, hg⟩)
def MembersEqPeriodicClass (s : Conventions.StandingParameters) (Y : PeriodicSpace.Params) :
    Prop :=
  ∀ (K : TestTupleClass) (n : ℕ), 1 ≤ n → K.members s n = K.periodicClass Y n
def MultilinearIffPeriodicMultilinear (D : TorusTransport.TransportData)
    (Y : PeriodicSpace.Params) : Prop :=
  ∀ (K : TestTupleClass) (n : ℕ) (hn : 1 ≤ n) (Ψ : K.members D.toStandingParameters n → ℝ)
    (Ψ' : K.periodicClass Y n → ℝ), AgreeOnCommon Ψ Ψ' →
      (IsClassMultilinear D K hn Ψ ↔
        PeriodicSpace.Kind.IsMultilinearOn Y .euclidean (K.periodicClass Y n) Ψ')
def EuclidHierarchyEquivExplicit (D : TorusTransport.TransportData)
    (Y : PeriodicSpace.Params) : Prop :=
  ∃ e : EuclidHierarchy Y ≃ ExplicitHierarchy D,
    (∀ (Φ : EuclidHierarchy Y) (n : ℕ) (hn : 2 ≤ n),
      AgreeOnCommon (Φ.func n hn) ((e Φ).func n hn)) ∧
    (∀ (C : PeriodicSpace.BoundFamily) (Φ : EuclidHierarchy Y),
      Φ.IsBoundedBy C ↔ (e Φ).IsBoundedBy C) ∧
    ∀ C : PeriodicSpace.BoundFamily,
      e '' boundedEuclidHierarchies Y C = boundedExplicitHierarchies D C
def PartialSeqEquivExplicit (D : TorusTransport.TransportData) (Y : PeriodicSpace.Params) :
    Prop :=
  ∀ (J₀ : Sequences.PNatIndexSet) (ρ' : J₀.carrier → ℝ),
    ∃ e : PeriodicSpace.Kind.PartialHierarchySeq Y .euclidean J₀
          (fun j => ENNReal.ofReal (ρ' j)) ≃
        ExplicitPartialHierarchySeq D.L J₀ ρ',
      ∀ Ψ : PeriodicSpace.Kind.PartialHierarchySeq Y .euclidean J₀
          (fun j => ENNReal.ofReal (ρ' j)),
        (∀ (j : J₀.carrier) (n : ℕ) (hn : 2 ≤ n),
          AgreeOnCommon (Ψ.func j n hn) (((e Ψ).term j).phi n hn)) ∧
        (∀ (C : PeriodicSpace.BoundFamily) (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : 0 < R)
          (j₀ : ℤ), Ψ.BoundedFrom C n hn R j₀ ↔ (e Ψ).BoundedFrom D.M C n hn R hR j₀) ∧
        (∀ C : PeriodicSpace.BoundFamily,
          Ψ.EventuallyBounded C ↔ (e Ψ).EventuallyBounded D.M C) ∧
        ∀ (J : Sequences.PNatIndexSet) (hJ : J.carrier ⊆ J₀.carrier),
          ∃ F : PeriodicSpace.Kind.IndexedFunctionalFamily Y .euclidean J,
            (∀ (j : J.carrier) (n : ℕ),
              F.dom j n = PeriodicSpace.Kind.sepLipTuplesWithin Y .euclidean n
                (PeriodicSpace.Kind.centredBall Y .euclidean
                  (ENNReal.ofReal (ρ' ⟨j.1, hJ j.2⟩)))) ∧
            (∀ (j : J.carrier) (n : ℕ) (hn : 2 ≤ n),
              AgreeOnCommon (F.func j n hn) (Ψ.func ⟨j.1, hJ j.2⟩ n hn)) ∧
            ∀ (Φ : EuclidHierarchy Y) (Φ' : ExplicitHierarchy D),
              (∀ (n : ℕ) (hn : 2 ≤ n), AgreeOnCommon (Φ.func n hn) (Φ'.func n hn)) →
                (F.TendsToOnSep Φ ↔
                  (e Ψ).TendsToOnSep hJ Φ')
def Statement : Prop :=
  ∀ D : TorusTransport.TransportData,
    UpdateStaysInClass D.toStandingParameters ∧
    MultilinearIffOnProducts D ∧
    OnProductsIffTupleMultilinear D.toStandingParameters ∧
    PartialFamilyTransportsAgree D ∧
    PartialHierarchyEquivExplicit D ∧
    EqZeroOfEntryEqZero D ∧
    PartialCentredMomentsSymmMultilinear D ∧
    ExplicitHierarchyEquivSymmConnected D ∧
    ∀ Y : PeriodicSpace.Params, Y.M = D.M →
      CentredMomentsSymmMultilinear D Y ∧
      PartitionMomentEqCentred D.toStandingParameters Y ∧
      MembersEqPeriodicClass D.toStandingParameters Y ∧
      MultilinearIffPeriodicMultilinear D Y ∧
      EuclidHierarchyEquivExplicit D Y ∧
      PartialSeqEquivExplicit D Y
end NonlinearDomain
end YangMills.Construction.ToriLimits
end
