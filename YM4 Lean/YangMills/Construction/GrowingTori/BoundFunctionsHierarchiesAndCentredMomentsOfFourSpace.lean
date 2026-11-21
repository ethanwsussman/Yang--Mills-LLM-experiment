import YangMills.Construction.Continuum.CentredFunctionalOfAFamily
import YangMills.Construction.GrowingTori.MultilinearFunctionalsOnTuplesAndPartialFamilies
import YangMills.Construction.GrowingTori.TranslationsIsometriesAndMirrorsOfFourSpaceProof
import YangMills.Construction.GrowingTori.TuplesOfFourSpaceAndTheirRestrictionToATorus
import YangMills.Construction.TorusOrFourSpace.MomentNumbersAndMomentSums
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriLimits
theorem ambient_topology_eq (L : ℕ) :
    (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).topology =
      (inferInstance : TopologicalSpace (Fin 4 → ℝ)) := by apply _root_.YangMills.Construction.BallTuples.ambient_topology_euclidean <;> assumption
theorem ambient_supp_eq (L : ℕ) (f : RealFn) :
    (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).supp f = fnSupport f := by
  change @closure _ (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).topology _ = _
  rw [ambient_topology_eq]
  rfl
theorem lipschitzR4_of_contDiff {f : RealFn} (hf : ContDiff ℝ 1 f)
    (hK : IsCompact (fnSupport f)) : LipschitzR4 f := by apply _root_.YangMills.Construction.ToriLimits.EuclideanSymmetryFacts.lipschitzR4_of_contDiff <;> assumption
def sepLipTuplesInBall (n : ℕ) (r : ℝ) (_hr : 0 < r) : Set (Fin n → RealFn) :=
  {f | IsSepLipTuple f ∧ SuppsWithin f (ballOrigin r)}
theorem sepLipTuplesInBall_eq_lipTuplesInBall (L : ℕ) {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    sepLipTuplesInBall n r hr = GrowingTori.lipTuplesInBall L n r := by
  have hsupp : ∀ f : RealFn,
      (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).supp f = fnSupport f :=
    ambient_supp_eq L
  have hcpt : ∀ A : Set (Fin 4 → ℝ),
      (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).IsEuclidCompact A ↔ IsCompact A := by
    intro A
    change @IsCompact _ (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).topology A ↔ _
    rw [ambient_topology_eq]
    exact Iff.rfl
  ext f
  constructor
  · rintro ⟨⟨hl, hk, hd⟩, hb⟩
    refine ⟨⟨hn, fun i => ⟨hl i, ?_, ?_⟩, fun i k hik => ?_⟩, fun i => ?_⟩
    · rw [hsupp]
      exact (hcpt _).2 (hk i)
    · exact subset_univ _
    · rw [hsupp, hsupp]
      exact hd i k hik
    · rw [hsupp]
      exact hb i
  · rintro ⟨⟨-, hl, hd⟩, hb⟩
    refine ⟨⟨fun i => (hl i).1, fun i => ?_, fun i k hik => ?_⟩, fun i => ?_⟩
    · have h := (hl i).2.1
      rw [hsupp] at h
      exact (hcpt _).1 h
    · have h := hd i k hik
      rwa [hsupp, hsupp] at h
    · have h := hb i
      rwa [hsupp] at h
theorem comp_mem_sepLipTuplesInBall {r : ℝ} (hr : 0 < r) {n k : ℕ}
    {f : Fin n → RealFn} (hf : f ∈ sepLipTuplesInBall n r hr)
    {e : Fin k → Fin n} (he : Function.Injective e) :
    (fun i => f (e i)) ∈ sepLipTuplesInBall k r hr := by
  obtain ⟨⟨hl, hk, hd⟩, hb⟩ := hf
  exact ⟨⟨fun i => hl (e i), fun i => hk (e i), fun i k hik => hd _ _ (he.ne hik)⟩,
    fun i => hb (e i)⟩
inductive TestTupleClass where
  | sep
  | ball (r : ℝ) (hr : 0 < r)
namespace TestTupleClass
def members (s : Conventions.StandingParameters) :
    TestTupleClass → (n : ℕ) → Set (Fin n → RealFn)
  | sep, n => sepTuplesR4 s n
  | ball r hr, n => sepLipTuplesInBall n r hr
variable {s : Conventions.StandingParameters}
theorem comp_mem_members (T : TestTupleClass) {n k : ℕ} {f : Fin n → RealFn}
    (hf : f ∈ T.members s n) {e : Fin k → Fin n} (he : Function.Injective e) :
    (fun i => f (e i)) ∈ T.members s k := by
  cases T with
  | sep =>
    obtain ⟨hl, hk, hd⟩ := (mem_sepTuplesR4_iff s f).1 hf
    exact (mem_sepTuplesR4_iff s _).2
      ⟨fun i => hl (e i), fun i => hk (e i), fun i k hik => hd _ _ (he.ne hik)⟩
  | ball r hr => exact comp_mem_sepLipTuplesInBall hr hf he
theorem isSepLipTuple_of_mem (T : TestTupleClass) {n : ℕ} {f : Fin n → RealFn}
    (hf : f ∈ T.members s n) : IsSepLipTuple f := by
  cases T with
  | sep =>
    obtain ⟨hl, hk, hd⟩ := (mem_sepTuplesR4_iff s f).1 hf
    exact ⟨fun i => lipschitzR4_of_contDiff (hl i) (hk i), hk, hd⟩
  | ball r hr => exact hf.1
end TestTupleClass
theorem isSepLipschitz_of_isSepLipTuple (D : TorusTransport.TransportData) {n : ℕ+}
    {f : Fin n → RealFn} (hf : IsSepLipTuple f) :
    TorusTransport.Domain.euclidean.IsSepLipschitz D f :=
  ⟨fun i => (TorusTransport.Domain.lipschitzOn_iff D .euclidean).2 (hf.1 i), hf.2.1, hf.2.2⟩
def IsClassMultilinear (D : TorusTransport.TransportData) (T : TestTupleClass) {n : ℕ} (hn : 1 ≤ n)
    (Ψ : T.members D.toStandingParameters n → ℝ) : Prop :=
  TorusTransport.IsMultilinearOn (n := ⟨n, hn⟩) D (T.members D.toStandingParameters n)
    (fun _ hf => isSepLipschitz_of_isSepLipTuple D
      (T.isSepLipTuple_of_mem hf)) Ψ
def IsClassSymmetric (s : Conventions.StandingParameters) (T : TestTupleClass) {n : ℕ}
    (Ψ : T.members s n → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (h : T.members s n),
    Ψ ⟨fun i => h.1 (σ i), T.comp_mem_members h.2 σ.injective⟩ = Ψ h
abbrev EuclidHierarchy (D : PeriodicSpace.Params) : Type :=
  PeriodicSpace.Kind.Hierarchy D .euclidean
abbrev boundedEuclidHierarchies (D : PeriodicSpace.Params) (C : PeriodicSpace.BoundFamily) :
    Set (EuclidHierarchy D) :=
  PeriodicSpace.Kind.boundedHierarchies D .euclidean C
structure ExplicitHierarchy (D : TorusTransport.TransportData) where
  func : (n : ℕ) → 2 ≤ n → TestTupleClass.sep.members D.toStandingParameters n → ℝ
  multilinear : ∀ n (hn : 2 ≤ n),
    IsClassMultilinear D .sep (by omega : 1 ≤ n) (func n hn)
  symmetric : ∀ n (hn : 2 ≤ n), IsClassSymmetric D.toStandingParameters .sep (func n hn)
def ExplicitHierarchy.IsBoundedBy {D : TorusTransport.TransportData} (Φ : ExplicitHierarchy D)
    (C : PeriodicSpace.BoundFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (d R : ℝ) (hd : 0 < d) (hR : 0 < R)
    (f : TestTupleClass.sep.members D.toStandingParameters n),
    f.1 ∈ lipTuples n hn d R hd hR →
      |Φ.func n hn f| ≤ C.val n d R * ∏ i, TestFunctions.sharpNormR4 D.M (f.1 i)
def boundedExplicitHierarchies (D : TorusTransport.TransportData)
    (C : PeriodicSpace.BoundFamily) : Set (ExplicitHierarchy D) :=
  {Φ | Φ.IsBoundedBy C}
abbrev PartialHierarchy (L : ℕ) (r : ℝ) : Type := GrowingTori.PartialFamily L r
structure ExplicitPartialHierarchy (D : TorusTransport.TransportData) (r : ℝ) (hr : 0 < r) where
  func : (n : ℕ) → 2 ≤ n → (TestTupleClass.ball r hr).members D.toStandingParameters n → ℝ
  multilinear : ∀ n (hn : 2 ≤ n),
    IsClassMultilinear D (.ball r hr) (by omega : 1 ≤ n) (func n hn)
  symmetric : ∀ n (hn : 2 ≤ n),
    IsClassSymmetric D.toStandingParameters (.ball r hr) (func n hn)
structure ExplicitPartialHierarchySeq (L : ℕ) (I₀ : Sequences.PNatIndexSet)
    (r : I₀.carrier → ℝ) where
  radius_eventually_gt : ∀ t : ℝ, 0 < t → ∃ m : ℤ, ∀ j : I₀.carrier,
    m ≤ (((j.1 : ℕ+) : ℕ) : ℤ) → t < r j
  term : (j : I₀.carrier) → PartialHierarchy L (r j)
namespace ExplicitPartialHierarchySeq
variable {L : ℕ} {I₀ : Sequences.PNatIndexSet} {r : I₀.carrier → ℝ}
def BoundedFrom (Ψ : ExplicitPartialHierarchySeq L I₀ r) (M : ℝ)
    (C : PeriodicSpace.BoundFamily) (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : 0 < R) (m : ℤ) :
    Prop :=
  ∀ j : I₀.carrier, m ≤ (((j.1 : ℕ+) : ℕ) : ℤ) → ∀ (d : ℝ) (hd : 0 < d)
    (f : GrowingTori.lipTuplesInBall L n (r j)),
    f.1 ∈ lipTuples n hn d R hd hR →
      |(Ψ.term j).phi n hn f| ≤
        C.val n d R * ∏ i, TestFunctions.sharpNormR4 M (f.1 i)
def EventuallyBounded (Ψ : ExplicitPartialHierarchySeq L I₀ r) (M : ℝ)
    (C : PeriodicSpace.BoundFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : 0 < R), ∃ m : ℤ, Ψ.BoundedFrom M C n hn R hR m
def TendsToOnSep {D : TorusTransport.TransportData}
    (Ψ : ExplicitPartialHierarchySeq D.L I₀ r) {I : Sequences.PNatIndexSet}
    (hI : I.carrier ⊆ I₀.carrier) (Φ : ExplicitHierarchy D) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : TestTupleClass.sep.members D.toStandingParameters n),
    ∃ (m : ℤ) (hf : ∀ j : (I.filterGe m).carrier,
        f.1 ∈ GrowingTori.lipTuplesInBall D.L n (r ⟨j.1, hI j.2.1⟩)),
      PeriodicSpace.IndexedLimits.ConvergesToAlong I m
        (fun j => (((Ψ.term ⟨j.1, hI j.2.1⟩).phi n hn ⟨f.1, hf j⟩ : ℝ) : ℂ))
        ((Φ.func n hn f : ℝ) : ℂ)
end ExplicitPartialHierarchySeq
theorem subfamily_mem_lipTuplesInBall (L : ℕ) {r : ℝ} (hr : 0 < r) {q : ℕ}
    {h : Fin q → RealFn} (hh : h ∈ sepLipTuplesInBall q r hr)
    (B : Finset (Fin q)) (hB : 1 ≤ B.card) :
    subfamily h B ∈ GrowingTori.lipTuplesInBall L B.card r := by
  rw [← sepLipTuplesInBall_eq_lipTuplesInBall L hB r hr]
  exact comp_mem_sepLipTuplesInBall hr hh (B.orderEmbOfFin rfl).injective
def centredMomentOf {L : ℕ} {r : ℝ} (Φ : PartialHierarchy L r) {q : ℕ}
    (h : sepLipTuplesInBall q r Φ.radius_pos) : ℝ :=
  ∑ π ∈ (SetPartition.singletonFree q).attach, ∏ B ∈ π.1.parts.attach,
    Φ.phi B.1.card (PeriodicSpace.two_le_card_of_mem_singletonFree π.2 B.2)
      ⟨subfamily h.1 B.1, subfamily_mem_lipTuplesInBall L Φ.radius_pos h.2 B.1
        (by have := PeriodicSpace.two_le_card_of_mem_singletonFree π.2 B.2; omega)⟩
theorem centredMomentOf_eq_centredFunctionalOf {L : ℕ} {r : ℝ} (Φ : PartialHierarchy L r) {q : ℕ}
    (h : sepLipTuplesInBall q r Φ.radius_pos)
    (S : (n : ℕ) → (Fin n → RealFn) → ℝ)
    (hS : ∀ (n : ℕ) (hn : 2 ≤ n) (g : GrowingTori.lipTuplesInBall L n r),
      S n g.1 = Φ.phi n hn g) :
    centredMomentOf Φ h = SchwingerFunctions.centredFunctionalOf S h.1 := by
  rw [SchwingerFunctions.centredFunctionalOf, ← SetPartition.singletonFree_eq_nonSingletonPartitions,
    ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Finset.prod_attach π.1.parts]
  exact Finset.prod_congr rfl fun B _ => (hS _ _ _).symm
def momentBoundSum (C : PeriodicSpace.BoundFamily) (q : ℕ) (d R : ℝ) : ℝ :=
  ∑ π ∈ SetPartition.singletonFree q, ∏ B ∈ π.parts, C.val B.card d R
end YangMills.Construction.ToriLimits
end
