import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinatesProof
import YangMills.Construction.PeriodicOperators.TransposesOfJetsProof
import YangMills.Construction.Towers.SumsProductsAndTransposesOfJetsWithHolomorphicComponents
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.JetClosure
open YangMills.Construction.Coordinates
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions
open YangMills.Construction.PeriodicOperators.StripSymbols (openStripInterior)
theorem splitCoords_appendCoords (x y : ComplexCoordinates 4) :
    splitCoords (n := 4) (n' := 4) (appendCoords x y) = (x, y) := by
  refine Prod.ext ?_ ?_ <;> funext i <;>
    simp only [splitCoords, appendCoords, Fin.append_left, Fin.append_right]
theorem appendCoords_splitCoords (w : ComplexCoordinates (4 + 4)) :
    appendCoords (splitCoords (n := 4) (n' := 4) w).1 (splitCoords (n := 4) (n' := 4) w).2 = w := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp only [appendCoords, splitCoords, Fin.append_left, Fin.append_right]
theorem mem_appendSet (S : Set (ComplexCoordinates 4 × ComplexCoordinates 4))
    (w : ComplexCoordinates (4 + 4)) : w ∈ appendSet S ↔ splitCoords w ∈ S := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [splitCoords_appendCoords]
    exact hq
  · intro h
    exact ⟨_, h, appendCoords_splitCoords w⟩
theorem isOpen_appendSet_inter {U U' : Set (ComplexCoordinates 4 × ComplexCoordinates 4)}
    (h : IsOpen (appendSet U)) (h' : IsOpen (appendSet U')) : IsOpen (appendSet (U ∩ U')) := by
  have e : appendSet (U ∩ U') = appendSet U ∩ appendSet U' := by
    ext w
    simp only [mem_appendSet, mem_inter_iff]
  rw [e]
  exact h.inter h'
def affineSubst (s t : ℂ) (w : ComplexCoordinates (4 + 4)) : ComplexCoordinates (4 + 4) :=
  appendCoords (s • (splitCoords (n := 4) (n' := 4) w).1 + t • (splitCoords (n := 4) (n' := 4) w).2)
    (splitCoords (n := 4) (n' := 4) w).2
theorem differentiable_affineSubst (s t : ℂ) : Differentiable ℂ (affineSubst s t) := by
  rw [differentiable_pi]
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have e : (fun w => affineSubst s t w (Fin.castAdd 4 i)) =
        fun w => s * w (Fin.castAdd 4 i) + t * w (Fin.natAdd 4 i) := by
      funext w
      simp only [affineSubst, appendCoords, splitCoords, Fin.append_left, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
    rw [e]
    fun_prop
  · have e : (fun w => affineSubst s t w (Fin.natAdd 4 i)) = fun w => w (Fin.natAdd 4 i) := by
      funext w
      simp only [affineSubst, appendCoords, splitCoords, Fin.append_right]
    rw [e]
    fun_prop
theorem affineSubst_isHolomorphicIn (s t : ℂ) {O : Set (ComplexCoordinates (4 + 4))}
    (hO : IsOpen O) : ComplexCoordinates.IsHolomorphicIn O (affineSubst s t) := by
  refine ⟨hO, (differentiable_affineSubst s t).continuous.continuousOn, fun a _ j => ?_⟩
  refine Eventually.of_forall fun ζ => ?_
  have h : DifferentiableAt ℂ
      (fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ζ := by fun_prop
  exact (differentiable_affineSubst s t _).comp ζ h
section Scalars
variable {N : ℕ} {O O' : Set (ComplexCoordinates N)} {f g : ComplexCoordinates N → ℂ}
abbrev ScalarHolomorphic (O : Set (ComplexCoordinates N)) (f : ComplexCoordinates N → ℂ) : Prop :=
  ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun x _ => f x
theorem scalarHolomorphic_iff : ScalarHolomorphic O f ↔ IsOpen O ∧ ContinuousOn f O ∧
    ∀ a ∈ O, ∀ j : Fin N, ∀ᶠ ζ in 𝓝 (0 : ℂ),
      DifferentiableAt ℂ (fun ζ : ℂ => f (a + ζ • ComplexCoordinates.stdBasisVector j)) ζ := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isHolomorphicScalarIn_iff <;> assumption
theorem ScalarHolomorphic.mono (h : ScalarHolomorphic O f) (hO : IsOpen O') (hs : O' ⊆ O) :
    ScalarHolomorphic O' f := by
  obtain ⟨_, hc, hd⟩ := scalarHolomorphic_iff.1 h
  exact scalarHolomorphic_iff.2 ⟨hO, hc.mono hs, fun a ha => hd a (hs ha)⟩
theorem ScalarHolomorphic.add (h : ScalarHolomorphic O f) (h' : ScalarHolomorphic O g) :
    ScalarHolomorphic O fun x => f x + g x := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.HolomorphicFnOn.add <;> assumption
theorem ScalarHolomorphic.mul (h : ScalarHolomorphic O f) (h' : ScalarHolomorphic O g) :
    ScalarHolomorphic O fun x => f x * g x := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.HolomorphicFnOn.mul <;> assumption
theorem ScalarHolomorphic.const_mul (c : ℂ) (h : ScalarHolomorphic O f) :
    ScalarHolomorphic O fun x => c * f x := by
  obtain ⟨hO, hc, hd⟩ := scalarHolomorphic_iff.1 h
  refine scalarHolomorphic_iff.2 ⟨hO, continuousOn_const.mul hc, fun a ha j => ?_⟩
  filter_upwards [hd a ha j] with ζ e using e.const_mul c
theorem ScalarHolomorphic.zero (hO : IsOpen O) : ScalarHolomorphic O fun _ => 0 :=
  scalarHolomorphic_iff.2 ⟨hO, continuousOn_const, fun _ _ _ =>
    Eventually.of_forall fun _ => differentiableAt_const _⟩
theorem ScalarHolomorphic.sum {J : Type} (s : Finset J) {F : J → ComplexCoordinates N → ℂ}
    (hO : IsOpen O) (h : ∀ c, ScalarHolomorphic O (F c)) :
    ScalarHolomorphic O fun x => ∑ c ∈ s, F c x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ScalarHolomorphic.zero hO
  | insert c s hc ih =>
    simp only [Finset.sum_insert hc]
    exact (h c).add ih
end Scalars
section Entries
variable {I I' I'' : PeriodicData}
open Classical in
theorem linearMapEntry_comp {J J' J'' : Type} [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (M' : (J'' → ℂ) →ₗ[ℂ] (J → ℂ)) (c' : J') (c'' : J'') :
    linearMapEntry (M.comp M') c' c'' = ∑ c, linearMapEntry M c' c * linearMapEntry M' c c'' := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.linearMapEntry_comp <;> assumption
theorem linearMapEntry_quotHomTranspose [Finite I'.UnitQuot] (M : QuotHom I I') (c : I.UnitQuot)
    (c' : I'.UnitQuot) :
    linearMapEntry (quotHomTranspose M) c c' =
      ((I'.quotWeight 1 c' / I.quotWeight 1 c : ℝ) : ℂ) * linearMapEntry M c' c := by apply _root_.YangMills.Construction.PeriodicOperators.JetTranspose.linearMapEntry_quotHomTranspose_eq <;> assumption
end Entries
section Components
variable {I I' I'' : PeriodicData} {P : Set (ComplexCoordinates 4)}
  {D D' : ComplexCoordinates 4 → Set (Fin 4 → ℂ)}
theorem isHolomorphicInMomentumPair_iff {U : Set (ComplexCoordinates 4 × ComplexCoordinates 4)}
    {A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'} :
    IsHolomorphicInMomentumPair U A ↔ IsOpen (appendSet U) ∧ ∀ c' c, ScalarHolomorphic (appendSet U)
      fun x => linearMapEntry (A (splitCoords (n := 4) (n' := 4) x).2
        (splitCoords (n := 4) (n' := 4) x).1) c' c := by
  constructor
  · rintro ⟨_, ho, h⟩
    exact ⟨ho, fun c' c => h (c', c)⟩
  · rintro ⟨ho, h⟩
    exact ⟨by norm_num, ho, fun e => h e.1 e.2⟩
theorem isHolomorphicInMomentumPair_mono {U U' : Set (ComplexCoordinates 4 × ComplexCoordinates 4)}
    {A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'} (h : IsHolomorphicInMomentumPair U A)
    (ho : IsOpen (appendSet U')) (hs : U' ⊆ U) : IsHolomorphicInMomentumPair U' A := by
  obtain ⟨_, he⟩ := isHolomorphicInMomentumPair_iff.1 h
  exact isHolomorphicInMomentumPair_iff.2 ⟨ho, fun c' c => (he c' c).mono ho (image_mono hs)⟩
theorem isOpen_appendSet_of_isHolomorphicInMomentumPair
    {U : Set (ComplexCoordinates 4 × ComplexCoordinates 4)}
    {A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'} (h : IsHolomorphicInMomentumPair U A) :
    IsOpen (appendSet U) := (isHolomorphicInMomentumPair_iff.1 h).1
theorem _root_.YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions.ComponentOpenDomain.restrict
    {A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'}
    (h : ComponentOpenDomain P D' A) (hD : ∀ p ∈ P, ∀ κ ∈ D p, κ ∈ D' p) :
    ComponentOpenDomain P D A := by
  obtain ⟨U, hP, hU, hA⟩ := h
  exact ⟨U, hP, fun p hp κ hκ => hU p hp κ (hD p hp κ hκ), hA⟩
theorem _root_.YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions.ComponentOpenDomain.add
    {A B : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'}
    (hA : ComponentOpenDomain P D A) (hB : ComponentOpenDomain P D B) :
    ComponentOpenDomain P D fun p κ => A p κ + B p κ := by
  obtain ⟨U, hP, hU, hA⟩ := hA
  obtain ⟨U', _, hU', hB⟩ := hB
  have ho := isOpen_appendSet_inter (isOpen_appendSet_of_isHolomorphicInMomentumPair hA)
    (isOpen_appendSet_of_isHolomorphicInMomentumPair hB)
  refine ⟨U ∩ U', fun q hq => hP q hq.1, fun p hp κ hκ => ⟨hU p hp κ hκ, hU' p hp κ hκ⟩, ?_⟩
  have hA' := isHolomorphicInMomentumPair_iff.1 (isHolomorphicInMomentumPair_mono hA ho inter_subset_left)
  have hB' := isHolomorphicInMomentumPair_iff.1 (isHolomorphicInMomentumPair_mono hB ho inter_subset_right)
  refine isHolomorphicInMomentumPair_iff.2 ⟨ho, fun c' c => ?_⟩
  exact (hA'.2 c' c).add (hB'.2 c' c)
theorem _root_.YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions.ComponentOpenDomain.comp
    [Finite I.UnitQuot]
    {A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'}
    {B : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I'' I}
    (hA : ComponentOpenDomain P D A) (hB : ComponentOpenDomain P D B) :
    ComponentOpenDomain P D fun p κ => (A p κ).comp (B p κ) := by
  have := Fintype.ofFinite I.UnitQuot
  obtain ⟨U, hP, hU, hA⟩ := hA
  obtain ⟨U', _, hU', hB⟩ := hB
  have ho := isOpen_appendSet_inter (isOpen_appendSet_of_isHolomorphicInMomentumPair hA)
    (isOpen_appendSet_of_isHolomorphicInMomentumPair hB)
  refine ⟨U ∩ U', fun q hq => hP q hq.1, fun p hp κ hκ => ⟨hU p hp κ hκ, hU' p hp κ hκ⟩, ?_⟩
  have hA' := isHolomorphicInMomentumPair_iff.1 (isHolomorphicInMomentumPair_mono hA ho inter_subset_left)
  have hB' := isHolomorphicInMomentumPair_iff.1 (isHolomorphicInMomentumPair_mono hB ho inter_subset_right)
  refine isHolomorphicInMomentumPair_iff.2 ⟨ho, fun c' c'' => ?_⟩
  simp only [linearMapEntry_comp]
  exact ScalarHolomorphic.sum _ ho fun c => (hA'.2 c' c).mul (hB'.2 c c'')
theorem _root_.YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions.ComponentOpenDomain.transpose
    [Finite I'.UnitQuot]
    {A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'}
    (hA : ComponentOpenDomain P D A) :
    ComponentOpenDomain P D fun p κ => quotHomTranspose (A p κ) := by
  obtain ⟨U, hP, hU, hA⟩ := hA
  obtain ⟨ho, he⟩ := isHolomorphicInMomentumPair_iff.1 hA
  refine ⟨U, hP, hU, isHolomorphicInMomentumPair_iff.2 ⟨ho, fun c c' => ?_⟩⟩
  simp only [linearMapEntry_quotHomTranspose]
  exact (he c' c).const_mul _
theorem _root_.YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions.ComponentOpenDomain.substitute
    (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties) (s t : ℂ)
    (g : ComplexCoordinates 4 → ComplexCoordinates 4 → ComplexCoordinates 4)
    (hg : ∀ κ p, g κ p = s • κ + t • p)
    {A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'}
    (hA : ComponentOpenDomain P D' A) (hD : ∀ p ∈ P, ∀ κ ∈ D p, g κ p ∈ D' p) :
    ComponentOpenDomain P D fun p κ => A p (g κ p) := by
  obtain ⟨U, hP, hU, hA⟩ := hA
  obtain ⟨ho, he⟩ := isHolomorphicInMomentumPair_iff.1 hA
  refine ⟨{q | (g q.1 q.2, q.2) ∈ U}, fun q hq => hP (g q.1 q.2, q.2) hq,
    fun p hp κ hκ => hU p hp _ (hD p hp κ hκ), ?_⟩
  have hset : appendSet {q : ComplexCoordinates 4 × ComplexCoordinates 4 | (g q.1 q.2, q.2) ∈ U} =
      affineSubst s t ⁻¹' appendSet U := by
    ext w
    simp only [mem_appendSet, mem_preimage, mem_ofPred_eq, affineSubst, splitCoords_appendCoords, hg]
  have ho' : IsOpen (appendSet {q : ComplexCoordinates 4 × ComplexCoordinates 4 |
      (g q.1 q.2, q.2) ∈ U}) := by
    rw [hset]
    exact ho.preimage (differentiable_affineSubst s t).continuous
  refine isHolomorphicInMomentumPair_iff.2 ⟨ho', fun c' c => ?_⟩
  have hmaps : MapsTo (affineSubst s t) (appendSet {q : ComplexCoordinates 4 × ComplexCoordinates 4 |
      (g q.1 q.2, q.2) ∈ U}) (appendSet U) := by
    intro w hw
    rw [hset] at hw
    exact hw
  have hc := ((hS.1 (4 + 4) _ ho).1 1 _ (he c' c)).2.2.2.1 (4 + 4) _ (affineSubst s t)
    (affineSubst_isHolomorphicIn s t ho') hmaps
  convert hc using 1
  funext w _
  simp only [Function.comp, affineSubst, splitCoords_appendCoords, hg]
end Components
theorem mem_imStrip_of_mem_openStripInterior {δ : ℝ} {p : Fin 4 → ℂ} (hp : p ∈ openStripInterior δ) :
    p ∈ imStrip δ := by
  obtain ⟨O, _, hO, hs⟩ := hp
  exact hs (hO rfl)
theorem jetOpsClosed_holds (hLocal : JetDomains.OpFunJetTheory)
    (hArguments : JetArgumentsAndEqualJets)
    (hSeries : ComplexCoordinates.PowerSeriesHolomorphy.Properties) : JetOpsClosed := by
  intro δ hδ P _ hPs I I' I'' hI hI' hI''
  have hstrip : ∀ p ∈ P, p ∈ imStrip δ := fun p hp => mem_imStrip_of_mem_openStripInterior (hPs hp)
  have hFacts : ∀ p ∈ P, JetDomains.JetAlgebra I I' I'' δ p :=
    fun p hp => hLocal.2.2 I I' I'' hI hI' hI'' δ p hδ (hstrip p hp)
  have hProduct : ∀ p ∈ P, ProductJetArguments δ p :=
    fun p hp => (hArguments.1 δ p hδ (hstrip p hp)).2.1
  have hTranspose : ∀ p ∈ P, TransposeJetArguments δ p :=
    fun p hp => (hArguments.1 δ p hδ (hstrip p hp)).2.2
  have : Finite I.UnitQuot := hI.finite_quot
  have : Finite I'.UnitQuot := hI'.finite_quot
  have plus : ∀ κ p : ComplexCoordinates 4, κ + p = (1 : ℂ) • κ + (1 : ℂ) • p := by
    intro κ p
    simp
  have minus : ∀ κ p : ComplexCoordinates 4, κ - p = (1 : ℂ) • κ + (-1 : ℂ) • p := by
    intro κ p
    simp [sub_eq_add_neg]
  have negative : ∀ κ p : ComplexCoordinates 4, -κ = (-1 : ℂ) • κ + (0 : ℂ) • p := by
    intro κ p
    simp
  have negMinus : ∀ κ p : ComplexCoordinates 4, -κ - p = (-1 : ℂ) • κ + (-1 : ℂ) • p := by
    intro κ p
    simp [sub_eq_add_neg]
  have negPlus : ∀ κ p : ComplexCoordinates 4, -κ + p = (-1 : ℂ) • κ + (1 : ℂ) • p := by
    intro κ p
    simp
  refine ⟨fun T S hT hS => ?_, fun T S hT hS => ?_, fun T hT => ?_⟩
  · exact
      { is_jet := fun p hp => (hFacts p hp).add_isJet _ _ (hT.is_jet p hp) (hS.is_jet p hp)
        open00 := hT.open00.add hS.open00
        open10 := hT.open10.add hS.open10
        open01 := hT.open01.add hS.open01
        open11 := hT.open11.add hS.open11 }
  · refine
      { is_jet := fun p hp => (hFacts p hp).mul_isJet _ _ (hT.is_jet p hp) (hS.is_jet p hp)
        open00 := hT.open00.comp hS.open00
        open10 := ?_
        open01 := ?_
        open11 := ?_ }
    · refine ComponentOpenDomain.add
        (A := fun p κ => ((T p).f10 κ).comp ((S p).f00 κ))
        (B := fun p κ => ((T p).f00 (κ + p)).comp ((S p).f10 κ)) ?_ ?_
      · exact (hT.open10.restrict fun p hp κ hκ => ((hProduct p hp).comp10 κ hκ).1).comp
          (hS.open00.restrict fun p hp κ hκ => ((hProduct p hp).comp10 κ hκ).2.1)
      · exact ComponentOpenDomain.comp
          (A := fun p κ => (T p).f00 (κ + p)) (B := fun p κ => (S p).f10 κ)
          (hT.open00.substitute hSeries 1 1 (fun κ p => κ + p) plus
            fun p hp κ hκ => ((hProduct p hp).comp10 κ hκ).2.2.1)
          (hS.open10.restrict fun p hp κ hκ => ((hProduct p hp).comp10 κ hκ).2.2.2)
    · refine ComponentOpenDomain.add
        (A := fun p κ => ((T p).f01 κ).comp ((S p).f00 κ))
        (B := fun p κ => ((T p).f00 (κ - p)).comp ((S p).f01 κ)) ?_ ?_
      · exact (hT.open01.restrict fun p hp κ hκ => ((hProduct p hp).comp01 κ hκ).1).comp
          (hS.open00.restrict fun p hp κ hκ => ((hProduct p hp).comp01 κ hκ).2.1)
      · exact ComponentOpenDomain.comp
          (A := fun p κ => (T p).f00 (κ - p)) (B := fun p κ => (S p).f01 κ)
          (hT.open00.substitute hSeries 1 (-1) (fun κ p => κ - p) minus
            fun p hp κ hκ => ((hProduct p hp).comp01 κ hκ).2.2.1)
          (hS.open01.restrict fun p hp κ hκ => ((hProduct p hp).comp01 κ hκ).2.2.2)
    · refine ComponentOpenDomain.add
        (A := fun p κ => ((T p).f11 κ).comp ((S p).f00 κ) + ((T p).f00 κ).comp ((S p).f11 κ) +
          ((T p).f10 (κ - p)).comp ((S p).f01 κ))
        (B := fun p κ => ((T p).f01 (κ + p)).comp ((S p).f10 κ)) ?_ ?_
      · refine ComponentOpenDomain.add
          (A := fun p κ => ((T p).f11 κ).comp ((S p).f00 κ) + ((T p).f00 κ).comp ((S p).f11 κ))
          (B := fun p κ => ((T p).f10 (κ - p)).comp ((S p).f01 κ)) ?_ ?_
        · refine ComponentOpenDomain.add
            (A := fun p κ => ((T p).f11 κ).comp ((S p).f00 κ))
            (B := fun p κ => ((T p).f00 κ).comp ((S p).f11 κ)) ?_ ?_
          · exact (hT.open11.restrict fun p hp κ hκ => ((hProduct p hp).comp11 κ hκ).1).comp
              (hS.open00.restrict fun p hp κ hκ => ((hProduct p hp).comp11 κ hκ).2.1)
          · exact (hT.open00.restrict fun p hp κ hκ =>
              ((hProduct p hp).comp11 κ hκ).2.2.1).comp
              (hS.open11.restrict fun p hp κ hκ => ((hProduct p hp).comp11 κ hκ).2.2.2.1)
        · exact ComponentOpenDomain.comp
            (A := fun p κ => (T p).f10 (κ - p)) (B := fun p κ => (S p).f01 κ)
            (hT.open10.substitute hSeries 1 (-1) (fun κ p => κ - p) minus
              fun p hp κ hκ => ((hProduct p hp).comp11 κ hκ).2.2.2.2.1)
            (hS.open01.restrict fun p hp κ hκ => ((hProduct p hp).comp11 κ hκ).2.2.2.2.2.1)
      · exact ComponentOpenDomain.comp
          (A := fun p κ => (T p).f01 (κ + p)) (B := fun p κ => (S p).f10 κ)
          (hT.open01.substitute hSeries 1 1 (fun κ p => κ + p) plus
            fun p hp κ hκ => ((hProduct p hp).comp11 κ hκ).2.2.2.2.2.2.1)
          (hS.open10.restrict fun p hp κ hκ => ((hProduct p hp).comp11 κ hκ).2.2.2.2.2.2.2)
  · refine
      { is_jet := fun p hp => (hFacts p hp).transpose_isJet _ (hT.is_jet p hp)
        open00 := ?_
        open10 := ?_
        open01 := ?_
        open11 := ?_ }
    · exact ComponentOpenDomain.transpose (A := fun p κ => (T p).f00 (-κ))
        (hT.open00.substitute hSeries (-1) 0 (fun κ _ => -κ) negative
          fun p hp κ hκ => (hTranspose p hp).comp00 κ hκ)
    · exact ComponentOpenDomain.transpose (A := fun p κ => (T p).f10 (-κ - p))
        (hT.open10.substitute hSeries (-1) (-1) (fun κ p => -κ - p) negMinus
          fun p hp κ hκ => (hTranspose p hp).comp10 κ hκ)
    · exact ComponentOpenDomain.transpose (A := fun p κ => (T p).f01 (-κ + p))
        (hT.open01.substitute hSeries (-1) 1 (fun κ p => -κ + p) negPlus
          fun p hp κ hκ => (hTranspose p hp).comp01 κ hκ)
    · exact ComponentOpenDomain.transpose (A := fun p κ => (T p).f11 (-κ))
        (hT.open11.substitute hSeries (-1) 0 (fun κ _ => -κ) negative
          fun p hp κ hκ => (hTranspose p hp).comp11 κ hκ)
end YangMills.Construction.Tower.FullSpace.JetClosure
end
