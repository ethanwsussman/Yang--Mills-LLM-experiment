import YangMills.Construction.Lattice.ComplexAverageOnHolomorphicFamilies
import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlock
import YangMills.Construction.Lattice.IteratedAveragesAtComplexConfigurations
import YangMills.Construction.Lattice.LieFieldsOnBondSets
import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.Lattice.SitesTopsAndIndicesAreFinitelyMany
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.Matrices.ExponentialOfLieElements
import YangMills.Construction.Matrices.LogSeriesTracelessOnUnitDet
import YangMills.Construction.Matrices.MatrixOperationsKeepHolomorphy
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
namespace HolomorphicFamilies
open ComplexIteratedAverages Matrices.GroupLieProduct
theorem opposite_isPositivelyOriented_of_not {L m : ℕ} {j : ℤ} {b : Bond L m j}
    (h : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.Bond.opposite_isPositivelyOriented <;> assumption
def positivePoint {L m K k : ℕ} (ℬ : Set (BondAtLevel L m K k))
    (V : BondAtLevel L m K k → ComplexMatrix2) : PositiveBondOf ℬ ⊕ Empty → ComplexMatrix2 :=
  Sum.elim (fun b => V b.1) fun e => e.elim
theorem fieldOfPoint_positivePoint {L m K k : ℕ} {ℬ : Set (BondAtLevel L m K k)}
    (hcl : IsReversalClosed ℬ) {V : BondAtLevel L m K k → ComplexMatrix2}
    (hV : IsGaugeField complexGaugeGroup ℬ V) {b : BondAtLevel L m K k} (hb : b ∈ ℬ) :
    fieldOfPoint ℬ (positivePoint ℬ V) b = V b := by
  classical
  by_cases hp : b.IsPositivelyOriented
  · simp only [fieldOfPoint, extendFromPositive]
    rw [dif_pos ⟨hb, hp⟩]
    rfl
  · have hr : b.opposite ∈ ℬ ∧ b.opposite.IsPositivelyOriented :=
      ⟨hcl b hb, opposite_isPositivelyOriented_of_not hp⟩
    simp only [fieldOfPoint, extendFromPositive]
    rw [dif_neg (fun h => hp h.2), dif_pos hr]
    exact (hV.2 _ hr.1).symm
theorem complexBlockAverage_holomorphic_on_family
    (h₁ : ComplexIteratedAveragesHolomorphic)
    (h₂ : ComplexAverageIsLocal)
    (h₃ : ExpChartHolomorphy.ExpChartTheory)
    (h₄ : HolomorphyClosureStatement)
    (h₅ : SeparatedRegions.FinitenessOfSitesTopsAndIndices)
    {L m K k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K)
    {ι κ : Type} [Fintype ι] [Fintype κ] {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {U : (ι ⊕ κ → ComplexMatrix2) → BondAtLevel L m K k → ComplexMatrix2}
    (hU : IsHolomorphicGaugeFieldFamily b W U)
    {c : BondAtLevel L m K (k + 1)} (hc : c.IsPositivelyOriented) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ)
        {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
          Set (BondAtLevel L m K k → ComplexMatrix2))} ∧
      MapsTo (fun p => complexBlockAverage (U p) c)
        {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
          Set (BondAtLevel L m K k → ComplexMatrix2))}
        complexGaugeGroup ∧
      IsHolomorphicToMatrixEntries b
        {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
          Set (BondAtLevel L m K k → ComplexMatrix2))}
        (fun p => complexBlockAverage (U p) c) := by
  classical
  have hfin : Finite (BondAtLevel L m K k) :=
    ((h₅ L m hL hm).1 K k (by omega) (by omega)).2.1
  let ℬ : Set (BondAtLevel L m K k) := bondsInDoubleBlock c
  have hcl : IsReversalClosed ℬ := fun _ hb => ⟨hb.2, hb.1⟩
  let _ : Fintype (PositiveBondOf ℬ) := Fintype.ofFinite _
  obtain ⟨hA, -, hD⟩ := (h₁ L m K hL hm k hk ℬ hcl inferInstance).1 1 hk c
  have hloc := h₂ L m K k hL.1 hL.2 hm hk c hc
  have hpos : c.positivelyOriented = c := by simp [Bond.positivelyOriented, hc]
  obtain ⟨-, -, -, hprod, hcomp, -, -⟩ := h₃
  have hagree : ∀ V : BondAtLevel L m K k → ComplexMatrix2, IsGaugeField complexGaugeGroup ℬ V →
      ∀ b' ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)),
        onSetElseOne ℬ (fieldOfPoint ℬ (positivePoint ℬ V)) b' = V b' := by
    intro V hV b' hb'
    have hb'' : b' ∈ ℬ := hb'
    simp only [onSetElseOne, if_pos hb'', fieldOfPoint_positivePoint hcl hV hb'']
  have hiff : ∀ V : BondAtLevel L m K k → ComplexMatrix2, IsGaugeField complexGaugeGroup ℬ V →
      (positivePoint ℬ V ∈ productDomain ℬ 1 c ↔
        V ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2))) := by
    intro V hV
    have hag₀ : ∀ b' ∈ ℬ, fieldOfPoint ℬ (positivePoint ℬ V) b' = V b' :=
      fun b' hb' => fieldOfPoint_positivePoint hcl hV hb'
    constructor
    · intro hr
      have h' : fieldOfPoint ℬ (positivePoint ℬ V) ∈ {U | IsComplexGaugeField ℬ U ∧
          ComplexPartialDefinedAt (K := K) k ⟨ℬ, U⟩ 1 c} := hD.domain_eq ▸ hr.2
      have hid : onSetElseOne ℬ (fieldOfPoint ℬ (positivePoint ℬ V)) ∈
          (complexAveragingDomainNearOne c.positivelyOriented :
            Set (BondAtLevel L m K k → ComplexMatrix2)) := h'.2.2
      rw [hpos] at hid
      exact (hloc.mem_domain_iff _ _ (hagree V hV)).1 hid
    · intro hVs
      refine ⟨?_, ?_⟩
      · rintro (b' | e)
        · exact hV.1 b'.1 b'.2.1
        · exact e.elim
      · rw [hD.domain_eq]
        refine ⟨⟨fun b' hb' => by rw [hag₀ b' hb']; exact hV.1 b' hb', fun b' hb' => by
          rw [hag₀ b' hb', hag₀ _ (hcl b' hb')]; exact hV.2 b' hb'⟩, fun b' hb' => hb', ?_⟩
        show onSetElseOne ℬ (fieldOfPoint ℬ (positivePoint ℬ V)) ∈
          (complexAveragingDomainNearOne c.positivelyOriented :
            Set (BondAtLevel L m K k → ComplexMatrix2))
        rw [hpos]
        exact (hloc.mem_domain_iff _ _ (hagree V hV)).2 hVs
  have hval : ∀ V : BondAtLevel L m K k → ComplexMatrix2, IsGaugeField complexGaugeGroup ℬ V →
      positivePoint ℬ V ∈ productDomain ℬ 1 c →
        iteratedValue ℬ 1 c (positivePoint ℬ V) = complexBlockAverage V c := by
    intro V hV hr
    have hv : iteratedValue ℬ 1 c (positivePoint ℬ V) =
        complexBlockAverage (onSetElseOne ℬ (fieldOfPoint ℬ (positivePoint ℬ V))) c :=
      hD.value_eq _ hr.2
    rw [hv]
    simp only [complexBlockAverage, if_pos hc]
    exact hloc.average_eq _ _ (hagree V hV)
  have hconf : ∀ p ∈ W, IsGaugeField complexGaugeGroup ℬ (U p) := fun p hp =>
    ⟨fun b' _ => (hU.isGaugeField p hp).1 b' (mem_univ _),
      fun b' _ => (hU.isGaugeField p hp).2 b' (mem_univ _)⟩
  let Ψ : (ι ⊕ κ → ComplexMatrix2) → PositiveBondOf ℬ ⊕ Empty → ComplexMatrix2 :=
    fun p => positivePoint ℬ (U p)
  have hΨ : IsHolomorphicToProduct b W Ψ := by
    refine ⟨hU.isOpen, fun i => ?_, fun e => e.elim⟩
    have hmaps : MapsTo (fun p => Ψ p (.inl i)) W ComplexMatrix2.unitDeterminant :=
      fun p hp => (hU.isGaugeField p hp).1 i.1 (mem_univ _)
    exact ((hprod ι κ).2.1 b W _ hU.isOpen hmaps).2 (hU.holomorphic i.1)
  have hΦ : IsHolomorphicToCoords b Coordinates.ComplexCoordinates.matrixEquiv
      (productDomain ℬ 1 c) (iteratedValue ℬ 1 c) := by
    have hmaps : MapsTo (iteratedValue ℬ 1 c) (productDomain ℬ 1 c)
        ComplexMatrix2.unitDeterminant :=
      fun r hr => hA.value_mem _ hr.2
    exact ((hprod (PositiveBondOf ℬ) Empty).2.1 b _ _ hA.isOpen hmaps).1 (hA.holomorphic b)
  obtain ⟨-, hopen, hhol⟩ := hcomp ι κ (PositiveBondOf ℬ) Empty b W Ψ hU.isOpen hΨ
    ComplexMatrix2 4 Coordinates.ComplexCoordinates.matrixEquiv _ _ hΦ
  have hset : W ∩ Ψ ⁻¹' productDomain ℬ 1 c =
      {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
        Set (BondAtLevel L m K k → ComplexMatrix2))} := by
    ext p
    constructor
    · rintro ⟨hp, hq⟩
      exact ⟨hp, (hiff _ (hconf p hp)).1 hq⟩
    · rintro ⟨hp, hq⟩
      exact ⟨hp, (hiff _ (hconf p hp)).2 hq⟩
  rw [hset] at hopen hhol
  have heq : ∀ p ∈ {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
      Set (BondAtLevel L m K k → ComplexMatrix2))},
      (iteratedValue ℬ 1 c ∘ Ψ) p = complexBlockAverage (U p) c := fun p hp =>
    hval _ (hconf p hp.1) ((hiff _ (hconf p hp.1)).2 hp.2)
  refine ⟨hopen, fun p hp => ?_, ?_⟩
  · show complexBlockAverage (U p) c ∈ complexGaugeGroup
    rw [← heq p hp]
    exact hA.value_mem _ ((hiff _ (hconf p hp.1)).2 hp.2).2
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hsame⟩ := h₄ ι κ b _ hopen
    exact hsame _ _ hhol fun p hp => (heq p hp).symm
theorem expTwist_isHolomorphicGaugeFieldFamily
    (h₄ : HolomorphyClosureStatement)
    (h₆ : ComplexMatrix2.ExpImaginaryLieMem)
    {L m K k : ℕ} (hL : 2 ≤ L) (hm : 0 < m) (hk : k < K)
    {ι κ : Type} [Fintype ι] [Fintype κ] {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {U B : (ι ⊕ κ → ComplexMatrix2) → BondAtLevel L m K k → ComplexMatrix2}
    (hU : IsHolomorphicGaugeFieldFamily b W U) (hB : IsHolomorphicBondFormFamily b W B) :
    IsHolomorphicGaugeFieldFamily b W fun p => expTwist (B p) (U p) := by
  classical
  have hj : -(m : ℤ) < levelDepth K k := by
    simp only [levelDepth]
    omega
  have hpos : ∀ e : BondAtLevel L m K k, e.IsPositivelyOriented → ∀ p ∈ W,
      ComplexMatrix2.matExp (Complex.I • B p e) * U p e ∈ ComplexMatrix2.unitDeterminant := by
    intro e he p hp
    have h₁ : (ComplexMatrix2.matExp (Complex.I • B p e)).det = 1 :=
      h₆.2 _ ((hB.isBondForm p hp).1 e he)
    have h₂ : (U p e).det = 1 := (hU.isGaugeField p hp).1 e (mem_univ _)
    show (ComplexMatrix2.matExp (Complex.I • B p e) * U p e).det = 1
    rw [Matrix.det_mul, h₁, h₂, one_mul]
  have hinv : ∀ X : ComplexMatrix2, X ∈ ComplexMatrix2.unitDeterminant →
      X⁻¹ ∈ ComplexMatrix2.unitDeterminant := by
    intro X hX
    have hX' : X.det = 1 := hX
    show (X⁻¹).det = 1
    rw [Matrix.det_nonsing_inv, hX', Ring.inverse_one]
  have hvalpos : ∀ (p : ι ⊕ κ → ComplexMatrix2) (e : BondAtLevel L m K k),
      e.IsPositivelyOriented →
      expTwist (B p) (U p) e = ComplexMatrix2.matExp (Complex.I • B p e) * U p e :=
    fun p e he => by
      simp only [expTwist, if_pos he]
  have hvalneg : ∀ (p : ι ⊕ κ → ComplexMatrix2) (e : BondAtLevel L m K k),
      ¬ e.IsPositivelyOriented →
      expTwist (B p) (U p) e =
        (ComplexMatrix2.matExp (Complex.I • B p e.opposite) * U p e.opposite)⁻¹ :=
    fun p e he => by
      simp only [expTwist, if_neg he]
  refine ⟨hU.isOpen, fun p hp => ⟨fun e _ => ?_, fun e _ => ?_⟩, fun e => ?_⟩
  · by_cases he : e.IsPositivelyOriented
    · rw [hvalpos p e he]
      exact hpos e he p hp
    · rw [hvalneg p e he]
      exact hinv _ (hpos _ (opposite_isPositivelyOriented_of_not he) p hp)
  · rcases MatrixValued.xor_isPositivelyOriented_opposite hL hj e with ⟨he, hr⟩ | ⟨hr, he⟩
    · have hrr : e.opposite.opposite = e := Bond.ext rfl rfl
      rw [hvalneg p _ hr, hvalpos p e he, hrr]
    · rw [hvalpos p _ hr, hvalneg p e he]
      have hdet : IsUnit
          (ComplexMatrix2.matExp (Complex.I • B p e.opposite) * U p e.opposite).det := by
        have h1 : (ComplexMatrix2.matExp (Complex.I • B p e.opposite) * U p e.opposite).det = 1 :=
          hpos _ hr p hp
        rw [h1]
        exact isUnit_one
      exact (Matrix.nonsing_inv_nonsing_inv _ hdet).symm
  · obtain ⟨-, -, -, hmul, hlin, hinvh, hexp, -, -, -, -⟩ := h₄ ι κ b W hU.isOpen
    have hbase : ∀ e' : BondAtLevel L m K k, IsHolomorphicToMatrixEntries b W
        fun p => ComplexMatrix2.matExp (Complex.I • B p e') * U p e' := fun e' =>
      hmul _ _ (hexp _ (hlin (Complex.I • LinearMap.id) _ (hB.holomorphic e')))
        (hU.holomorphic e')
    by_cases he : e.IsPositivelyOriented
    · have hfun : (fun p => expTwist (B p) (U p) e) =
          fun p => ComplexMatrix2.matExp (Complex.I • B p e) * U p e :=
        funext fun p => hvalpos p e he
      rw [hfun]
      exact hbase e
    · have hfun : (fun p => expTwist (B p) (U p) e) =
          fun p => (ComplexMatrix2.matExp (Complex.I • B p e.opposite) * U p e.opposite)⁻¹ :=
        funext fun p => hvalneg p e he
      rw [hfun]
      refine hinvh _ (hbase _) fun p hp => ?_
      have h1 : (ComplexMatrix2.matExp (Complex.I • B p e.opposite) * U p e.opposite).det = 1 :=
        hpos _ (opposite_isPositivelyOriented_of_not he) p hp
      rw [h1]
      exact isUnit_one
theorem isOpen_logBall : IsOpen ComplexMatrix2.logBall := by
  have hcont : Continuous fun X : ComplexMatrix2 => ‖X - 1‖ :=
    (continuous_id.sub continuous_const).norm
  exact isOpen_lt hcont continuous_const
end HolomorphicFamilies
open HolomorphicFamilies ComplexIteratedAverages Matrices.GroupLieProduct in
theorem holomorphicFamilyComplexAverage_holds
    (h₁ : ComplexIteratedAveragesHolomorphic)
    (h₂ : ComplexAverageIsLocal)
    (h₃ : ExpChartHolomorphy.ExpChartTheory)
    (h₄ : HolomorphyClosureStatement)
    (h₅ : SeparatedRegions.FinitenessOfSitesTopsAndIndices)
    (h₆ : ComplexMatrix2.ExpImaginaryLieMem)
    (h₇ : ComplexMatrix2.LogSeriesTracelessOfUnitDet) :
    HolomorphicFamilyComplexAverage := by
  classical
  intro L m K k hL hm hk ι κ _ _ b W U hU c hc
  obtain ⟨hS, hSm, hSh⟩ := complexBlockAverage_holomorphic_on_family h₁ h₂ h₃ h₄ h₅ hL hm hk hU hc
  refine ⟨hS, hSm, hSh, fun B hB => ?_⟩
  have hL2 : 2 ≤ L := by have := hL.2; omega
  have hU' := expTwist_isHolomorphicGaugeFieldFamily h₄ h₆ hL2 hm hk hU hB
  set S : Set (ι ⊕ κ → ComplexMatrix2) :=
    {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
      Set (BondAtLevel L m K k → ComplexMatrix2))} with hSdef
  have hSW : S ⊆ W := fun p hp => hp.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hsubW, -⟩ := h₄ ι κ b W hU.isOpen
  have hU'' : IsHolomorphicGaugeFieldFamily b S fun p => expTwist (B p) (U p) :=
    ⟨hS, fun p hp => hU'.isGaugeField p hp.1, fun e => hsubW S hSW hS _ (hU'.holomorphic e)⟩
  obtain ⟨hT, hTm, hTh⟩ :=
    complexBlockAverage_holomorphic_on_family h₁ h₂ h₃ h₄ h₅ hL hm hk hU'' hc
  set T : Set (ι ⊕ κ → ComplexMatrix2) :=
    {p | p ∈ S ∧ expTwist (B p) (U p) ∈
      (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2))} with hTdef
  have hTS : T ⊆ S := fun p hp => hp.1
  obtain ⟨-, -, -, hmulT, hlinT, hinvT, -, -, hpreT, -, -⟩ := h₄ ι κ b T hT
  obtain ⟨-, -, -, -, -, -, -, -, -, hsubS, -⟩ := h₄ ι κ b S hS
  have hM₀ : IsHolomorphicToMatrixEntries b T fun p => complexBlockAverage (U p) c :=
    hsubS T hTS hT _ hSh
  have hdet₀ : ∀ p ∈ T, (complexBlockAverage (U p) c).det = 1 := fun p hp => hSm hp.1
  have hdet₁ : ∀ p ∈ T, (complexBlockAverage (expTwist (B p) (U p)) c).det = 1 :=
    fun p hp => hTm hp
  have hQ : IsHolomorphicToMatrixEntries b T fun p =>
      complexBlockAverage (expTwist (B p) (U p)) c * (complexBlockAverage (U p) c)⁻¹ :=
    hmulT _ _ hTh (hinvT _ hM₀ fun p hp => by rw [hdet₀ p hp]; exact isUnit_one)
  have hR := hpreT _ hQ ComplexMatrix2.logBall isOpen_logBall
  have hset : {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
      Set (BondAtLevel L m K k → ComplexMatrix2)) ∧
      ConstraintMapDefined (U p) (B p) c} = T ∩ (fun p =>
        complexBlockAverage (expTwist (B p) (U p)) c * (complexBlockAverage (U p) c)⁻¹) ⁻¹'
        ComplexMatrix2.logBall := by
    ext p
    constructor
    · rintro ⟨hp, hs, he, hl⟩
      exact ⟨⟨⟨hp, hs⟩, he⟩, hl⟩
    · rintro ⟨⟨⟨hp, hs⟩, he⟩, hl⟩
      exact ⟨hp, hs, he, hl⟩
  rw [hset]
  refine ⟨hR, ?_, ?_⟩
  · intro p hp
    have hQdet : complexBlockAverage (expTwist (B p) (U p)) c *
        (complexBlockAverage (U p) c)⁻¹ ∈ ComplexMatrix2.unitDeterminant := by
      show (complexBlockAverage (expTwist (B p) (U p)) c *
        (complexBlockAverage (U p) c)⁻¹).det = 1
      rw [Matrix.det_mul, hdet₁ p hp.1, Matrix.det_nonsing_inv, hdet₀ p hp.1, Ring.inverse_one,
        one_mul]
    exact ComplexMatrix2.traceless.smul_mem _ (h₇ _ hQdet hp.2)
  · obtain ⟨-, -, -, -, hlinR, -, -, hlogR, -, -, -⟩ := h₄ ι κ b _ hR
    obtain ⟨-, -, -, -, -, -, -, -, -, hsubT, -⟩ := h₄ ι κ b T hT
    have hQR := hsubT _ inter_subset_left hR _ hQ
    exact hlinR (Complex.I⁻¹ • LinearMap.id) _ (hlogR _ hQR fun p hp => hp.2)
end YangMills.Construction.PeriodicLattice
