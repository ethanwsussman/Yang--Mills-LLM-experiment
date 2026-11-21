import YangMills.Construction.InfiniteLattice.TraceOnTheGroupAndOneBondWeightProof
import YangMills.Construction.TransferOperators.ConfigurationsOfACubicTorusByLayersProof
import YangMills.Construction.TransferOperators.GaugeAveragesOfFunctionsOfLayersProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set InfiniteLattice SpinHarmonics Matrices
namespace TransferOperators.TemporalGauge
variable {μ : Fin 4}
theorem parallelTransport_lower (S : Stack) (U : GaugeField 1) (y : SliceSite μ) :
    S.parallelTransport μ U S.lower y = 1 := by
  simp [Stack.parallelTransport]
theorem parallelTransport_succ (S : Stack) (U : GaugeField 1) (y : SliceSite μ) {j : ℤ}
    (hj : S.lower ≤ j) :
    S.parallelTransport μ U (j + 1) y =
      S.parallelTransport μ U j y * temporalLinkVariable μ U j y := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = S.lower + (n : ℤ) := ⟨(j - S.lower).toNat, by omega⟩
  have e₀ : (S.lower + (n : ℤ) - S.lower).toNat = n := by omega
  have e₁ : (S.lower + (n : ℤ) + 1 - S.lower).toNat = n + 1 := by omega
  simp only [Stack.parallelTransport, e₀, e₁, List.range_succ, List.map_append, List.prod_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
theorem temporalLinkVariable_act (g : GaugeTransform 1) (U : GaugeField 1) (j : ℤ)
    (y : SliceSite μ) :
    temporalLinkVariable μ (g.act U) j y = g.toFun (pointAtLevel μ j y) *
      temporalLinkVariable μ U j y * (g.toFun (pointAtLevel μ (j + 1) y))⁻¹ := rfl
theorem spatialLinkVariable_act (g : GaugeTransform 1) (U : GaugeField 1) (j : ℤ)
    (b : SliceLink μ) :
    spatialLinkVariable μ (g.act U) j b = g.toFun (pointAtLevel μ j b.source) *
      spatialLinkVariable μ U j b * (g.toFun (pointAtLevel μ j b.target))⁻¹ := rfl
theorem parallelTransport_act (S : Stack) (g : GaugeTransform 1) (U : GaugeField 1)
    (y : SliceSite μ) {j : ℤ} (hj : S.lower ≤ j) :
    S.parallelTransport μ (g.act U) j y = g.toFun (pointAtLevel μ S.lower y) *
      S.parallelTransport μ U j y * (g.toFun (pointAtLevel μ j y))⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = S.lower + (n : ℤ) := ⟨(j - S.lower).toNat, by omega⟩
  clear hj
  induction n with
  | zero => simp [parallelTransport_lower]
  | succ n ih =>
    have e : S.lower + ((n + 1 : ℕ) : ℤ) = S.lower + (n : ℤ) + 1 := by
      push_cast
      ring
    rw [e, parallelTransport_succ S _ y (by omega), parallelTransport_succ S _ y (by omega), ih,
      temporalLinkVariable_act]
    group
theorem transportedLinkVariable_act (S : Stack) (g : GaugeTransform 1) (U : GaugeField 1)
    (b : SliceLink μ) {j : ℤ} (hj : S.lower ≤ j) :
    S.transportedLinkVariable μ (g.act U) j b =
      g.toFun (pointAtLevel μ S.lower b.source) * S.transportedLinkVariable μ U j b *
        (g.toFun (pointAtLevel μ S.lower b.target))⁻¹ := by
  simp only [Stack.transportedLinkVariable]
  rw [parallelTransport_act S g U _ hj, parallelTransport_act S g U _ hj, spatialLinkVariable_act]
  group
theorem gaugeActionOnTransported (S : Stack) : GaugeActionOnTransported μ S :=
  fun g U _ hj _ =>
    ⟨fun y => parallelTransport_act S g U y hj, fun b => transportedLinkVariable_act S g U b hj⟩
theorem level_pointAtLevel (j : ℤ) (y : SliceSite μ) :
    level μ (pointAtLevel μ j y) = j := by apply _root_.YangMills.Construction.TransferOperators.SliceDecomposition.level_pointAtLevel <;> assumption
theorem slicePart_pointAtLevel (j : ℤ) (y : SliceSite μ) :
    slicePart μ (pointAtLevel μ j y) = y := by
  apply Subtype.ext
  change pointAtLevel μ j y - level μ (pointAtLevel μ j y) • axisStep 1 μ = y
  rw [level_pointAtLevel, pointAtLevel, add_sub_cancel_left]
theorem pointAtLevel_level_slicePart (x : LatticePoint 1) :
    pointAtLevel μ (level μ x) (slicePart μ x) = x := by apply _root_.YangMills.Construction.TransferOperators.SliceDecomposition.pointAtLevel_level_slicePart <;> assumption
open Classical in
def columnGauge (S : Stack) (v : Set (SliceSite μ)) [Finite v]
    (f : ℤ → SliceSite μ → ComplexMatrix2.specialUnitary) : GaugeTransform 1 where
  toFun x := if S.lower ≤ level μ x ∧ level μ x ≤ S.upper ∧ slicePart μ x ∈ v then
    f (level μ x) (slicePart μ x) else 1
  finite_ne_one := by
    have hfin : ((fun q : ℤ × SliceSite μ => pointAtLevel μ q.1 q.2) ''
        (Icc S.lower S.upper ×ˢ v)).Finite :=
      ((finite_Icc _ _).prod (toFinite v)).image _
    refine hfin.subset fun x hx => ?_
    have hc : S.lower ≤ level μ x ∧ level μ x ≤ S.upper ∧ slicePart μ x ∈ v := by
      by_contra hc
      exact hx (if_neg hc)
    exact ⟨(level μ x, slicePart μ x), ⟨⟨hc.1, hc.2.1⟩, hc.2.2⟩, pointAtLevel_level_slicePart x⟩
theorem columnGauge_toFun (S : Stack) (v : Set (SliceSite μ)) [Finite v]
    (f : ℤ → SliceSite μ → ComplexMatrix2.specialUnitary) {j : ℤ} {y : SliceSite μ}
    (h₁ : S.lower ≤ j) (h₂ : j ≤ S.upper) (h₃ : y ∈ v) :
    (columnGauge S v f).toFun (pointAtLevel μ j y) = f j y := by
  refine (if_pos ⟨by rw [level_pointAtLevel]; exact h₁, by rw [level_pointAtLevel]; exact h₂,
    by rw [slicePart_pointAtLevel]; exact h₃⟩).trans ?_
  rw [level_pointAtLevel, slicePart_pointAtLevel]
theorem isTemporalGaugeWith_parallelTransport (S : Stack) (v : Set (SliceSite μ)) [Finite v]
    (U : GaugeField 1) :
    S.IsTemporalGaugeWith v (S.transportedIndexed v U)
      ((columnGauge S v (S.parallelTransport μ U)).act U) := by
  refine ⟨fun p => ?_, fun j y h₁ h₂ h₃ => ?_⟩
  · obtain ⟨⟨j, b⟩, h₁, h₂, h₃⟩ := p
    rw [spatialLinkVariable_act, columnGauge_toFun S v _ h₁ h₂ h₃.1,
      columnGauge_toFun S v _ h₁ h₂ h₃.2]
    rfl
  · rw [temporalLinkVariable_act, columnGauge_toFun S v _ h₁ h₂.le h₃,
      columnGauge_toFun S v _ (by omega) (by omega) h₃, parallelTransport_succ S U y h₁]
    group
theorem eq_on_links_of_isTemporalGaugeWith {S : Stack} {v : Set (SliceSite μ)}
    {u : S.indexPairs v → ComplexMatrix2.specialUnitary} {U U' : GaugeField 1}
    (h : S.IsTemporalGaugeWith v u U) (h' : S.IsTemporalGaugeWith v u U') :
    ∀ b ∈ Subtype.val '' S.linksOver v, U b = U' b := by
  rintro _ ⟨c, (⟨j, b, h₁, h₂, h₃, rfl⟩ | ⟨j, y, h₁, h₂, h₃, rfl⟩), rfl⟩
  · exact (h.1 ⟨(j, b), h₁, h₂, h₃⟩).trans (h'.1 ⟨(j, b), h₁, h₂, h₃⟩).symm
  · exact (h.2 j y h₁ h₂ h₃).trans (h'.2 j y h₁ h₂ h₃).symm
instance instCountableSliceLink : Countable (SliceLink μ) :=
  Function.Injective.countable (f := fun b : SliceLink μ => (⟨b.1, b.2.1⟩ : positiveLinks (1 : ℝ)))
    fun _ _ h => Subtype.ext (congrArg (fun c : positiveLinks (1 : ℝ) => c.1) h)
theorem continuous_extendFromPositive (b : Link 1) :
    Continuous fun g : positiveLinks (1 : ℝ) → ComplexMatrix2.specialUnitary =>
      extendFromPositive g b := by
  unfold extendFromPositive
  by_cases h : b ∈ positiveLinks (1 : ℝ)
  · simp only [dif_pos h]
    exact continuous_apply _
  · by_cases h' : b.opposite ∈ positiveLinks (1 : ℝ)
    · simp only [dif_neg h, dif_pos h']
      exact (continuous_apply _).inv
    · simp only [dif_neg h, dif_neg h']
      exact continuous_const
theorem continuous_gaugeFieldOfPositive :
    Continuous (gaugeFieldOfPositive (a := 1) one_pos) :=
  Continuous.subtype_mk (continuous_pi continuous_extendFromPositive) _
theorem continuous_temporalGaugeFamily (S : Stack) (v : Set (SliceSite μ)) :
    Continuous (S.temporalGaugeFamily v) := by
  refine continuous_pi fun c => ?_
  unfold Stack.temporalGaugeFamily
  by_cases h : ∃ p : S.indexPairs v, (spatialLink μ p.1.1 p.1.2).1 = c.1
  · simp only [dif_pos h]
    exact continuous_apply _
  · simp only [dif_neg h]
    exact continuous_const
theorem continuous_temporalGaugeField (S : Stack) (v : Set (SliceSite μ)) :
    Continuous (S.temporalGaugeField v) :=
  continuous_gaugeFieldOfPositive.comp (continuous_temporalGaugeFamily S v)
theorem continuous_transportedLinkVariable (S : Stack) (j : ℤ) (b : SliceLink μ) :
    Continuous fun U : GaugeField 1 => S.transportedLinkVariable μ U j b := by apply _root_.YangMills.Construction.TransferOperators.SliceMean.continuous_transportedLinkVariable <;> assumption
theorem continuous_transportedIndexed (S : Stack) (v : Set (SliceSite μ)) :
    Continuous (S.transportedIndexed v) :=
  continuous_pi fun p => continuous_transportedLinkVariable S p.1.1 p.1.2
theorem parallelTransport_congr (S : Stack) {U U' : GaugeField 1} {j : ℤ} {y : SliceSite μ}
    (h : ∀ k, S.lower ≤ k → k < j →
      temporalLinkVariable μ U k y = temporalLinkVariable μ U' k y) :
    S.parallelTransport μ U j y = S.parallelTransport μ U' j y := by
  unfold Stack.parallelTransport
  congr 1
  refine List.map_congr_left fun k hk => h _ (by omega) ?_
  have := List.mem_range.mp hk
  omega
theorem transportedIndexed_congr (S : Stack) (v : Set (SliceSite μ)) {U U' : GaugeField 1}
    (h : ∀ b ∈ Subtype.val '' S.linksOver v, U b = U' b) :
    S.transportedIndexed v U = S.transportedIndexed v U' := by
  funext ⟨⟨j, b⟩, h₁, h₂, h₃⟩
  have ht : ∀ y ∈ v, S.parallelTransport μ U j y = S.parallelTransport μ U' j y := fun y hy =>
    parallelTransport_congr S fun k hk hk' =>
      h _ ⟨temporalLink μ k y, Or.inr ⟨k, y, hk, by omega, hy, rfl⟩, rfl⟩
  have hs : spatialLinkVariable μ U j b = spatialLinkVariable μ U' j b :=
    h _ ⟨spatialLink μ j b, Or.inl ⟨j, b, h₁, h₂, h₃, rfl⟩, rfl⟩
  change S.transportedLinkVariable μ U j b = S.transportedLinkVariable μ U' j b
  rw [Stack.transportedLinkVariable, Stack.transportedLinkVariable, ht _ h₃.1, ht _ h₃.2, hs]
section Polynomials
variable {K : Type*}
theorem exists_star_entry_eq (hT : SpecialUnitaryTraceFacts) (i j : Fin 2) :
    ∃ (k l : Fin 2) (s : ℂ), ∀ w : ComplexMatrix2.specialUnitary,
      star ((w : ComplexMatrix2) i j) = s * (w : ComplexMatrix2) k l := by
  have h₁ := fun w => (hT.2 w).1
  have h₂ := fun w => (hT.2 w).2.1
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact ⟨1, 1, 1, fun w => by rw [one_mul, h₁ w]⟩
  · exact ⟨1, 0, -1, fun w => by rw [h₂ w]; ring⟩
  · exact ⟨0, 1, -1, fun w => by rw [h₂ w, star_neg, star_star]; ring⟩
  · exact ⟨0, 0, 1, fun w => by rw [one_mul, h₁ w, star_star]⟩
def HasPolynomialEntries (f : (K → ComplexMatrix2.specialUnitary) → ComplexMatrix2.specialUnitary) :
    Prop :=
  ∀ i j, ∃ q : MvPolynomial (EntryVar K) ℂ, ∀ u,
    ((f u : ComplexMatrix2.specialUnitary) : ComplexMatrix2) i j = MvPolynomial.eval (entryEval u) q
theorem HasPolynomialEntries.const (w : ComplexMatrix2.specialUnitary) :
    HasPolynomialEntries (K := K) fun _ => w :=
  fun i j => ⟨MvPolynomial.C ((w : ComplexMatrix2) i j), fun u => by simp⟩
theorem HasPolynomialEntries.eval (k : K) :
    HasPolynomialEntries fun u : K → ComplexMatrix2.specialUnitary => u k :=
  fun i j => ⟨MvPolynomial.X (.inl (k, i, j)), fun u => by simp [entryEval]⟩
theorem HasPolynomialEntries.mul
    {f g : (K → ComplexMatrix2.specialUnitary) → ComplexMatrix2.specialUnitary}
    (hf : HasPolynomialEntries f) (hg : HasPolynomialEntries g) :
    HasPolynomialEntries fun u => f u * g u := by
  intro i j
  obtain ⟨a₀, ha₀⟩ := hf i 0
  obtain ⟨a₁, ha₁⟩ := hf i 1
  obtain ⟨b₀, hb₀⟩ := hg 0 j
  obtain ⟨b₁, hb₁⟩ := hg 1 j
  refine ⟨a₀ * b₀ + a₁ * b₁, fun u => ?_⟩
  rw [Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha₀, ha₁, hb₀, hb₁]
  simp
theorem HasPolynomialEntries.inv (hT : SpecialUnitaryTraceFacts)
    {f : (K → ComplexMatrix2.specialUnitary) → ComplexMatrix2.specialUnitary}
    (hf : HasPolynomialEntries f) : HasPolynomialEntries fun u => (f u)⁻¹ := by
  intro i j
  obtain ⟨k, l, s, hs⟩ := exists_star_entry_eq hT j i
  obtain ⟨q, hq⟩ := hf k l
  refine ⟨MvPolynomial.C s * q, fun u => ?_⟩
  have h : (((f u)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) i j =
      star (((f u : ComplexMatrix2.specialUnitary) : ComplexMatrix2) j i) := rfl
  rw [h, hs, hq]
  simp
theorem HasPolynomialEntries.list_prod {ι : Type*}
    (f : ι → (K → ComplexMatrix2.specialUnitary) → ComplexMatrix2.specialUnitary) (l : List ι)
    (hf : ∀ i ∈ l, HasPolynomialEntries (f i)) :
    HasPolynomialEntries fun u => (l.map fun i => f i u).prod := by
  induction l with
  | nil => simpa using HasPolynomialEntries.const (K := K) 1
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hf a (by simp)).mul (ih fun i hi => hf i (by simp [hi]))
theorem isEntryPolynomial_comp {J : Type*} (hT : SpecialUnitaryTraceFacts)
    {Ψ : (K → ComplexMatrix2.specialUnitary) → J → ComplexMatrix2.specialUnitary}
    (hΨ : ∀ x, HasPolynomialEntries fun u => Ψ u x)
    {F : (J → ComplexMatrix2.specialUnitary) → ℂ} (hF : IsEntryPolynomial F) :
    IsEntryPolynomial fun u => F (Ψ u) := by
  obtain ⟨p, hp⟩ := hF
  have key : ∀ x : EntryVar J, ∃ q : MvPolynomial (EntryVar K) ℂ, ∀ u,
      entryEval (Ψ u) x = MvPolynomial.eval (entryEval u) q := by
    rintro (⟨b, i, j⟩ | ⟨b, i, j⟩)
    · exact hΨ b i j
    · obtain ⟨k, l, s, hs⟩ := exists_star_entry_eq hT i j
      obtain ⟨q, hq⟩ := hΨ b k l
      refine ⟨MvPolynomial.C s * q, fun u => ?_⟩
      simp only [entryEval]
      rw [hs, hq]
      simp
  choose f hf using key
  refine ⟨MvPolynomial.bind₁ f p, fun u => ?_⟩
  change F (Ψ u) = _
  rw [hp]
  clear hp
  induction p using MvPolynomial.induction_on
  · simp
  · simp [*]
  · simp [*]
end Polynomials
theorem hasPolynomialEntries_link (c : positiveLinks (1 : ℝ)) :
    HasPolynomialEntries fun g : positiveLinks (1 : ℝ) → ComplexMatrix2.specialUnitary =>
      (gaugeFieldOfPositive one_pos g) c.1 := by
  have h : (fun g : positiveLinks (1 : ℝ) → ComplexMatrix2.specialUnitary =>
      (gaugeFieldOfPositive one_pos g) c.1) = fun g => g c := funext fun g => dif_pos c.2
  rw [h]
  exact .eval c
theorem hasPolynomialEntries_parallelTransport (S : Stack) (j : ℤ) (y : SliceSite μ) :
    HasPolynomialEntries fun g : positiveLinks (1 : ℝ) → ComplexMatrix2.specialUnitary =>
      S.parallelTransport μ (gaugeFieldOfPositive one_pos g) j y :=
  HasPolynomialEntries.list_prod
    (fun (k : ℕ) g =>
      temporalLinkVariable μ (gaugeFieldOfPositive one_pos g) (S.lower + (k : ℤ)) y) _
    fun _ _ => hasPolynomialEntries_link ⟨(temporalLink μ _ y).1, (temporalLink μ _ y).2⟩
theorem hasPolynomialEntries_transportedLinkVariable (hT : SpecialUnitaryTraceFacts) (S : Stack)
    (j : ℤ) (b : SliceLink μ) :
    HasPolynomialEntries fun g : positiveLinks (1 : ℝ) → ComplexMatrix2.specialUnitary =>
      S.transportedLinkVariable μ (gaugeFieldOfPositive one_pos g) j b :=
  ((hasPolynomialEntries_parallelTransport S j _).mul
    (hasPolynomialEntries_link ⟨(spatialLink μ j b).1, (spatialLink μ j b).2⟩)).mul
    ((hasPolynomialEntries_parallelTransport S j _).inv hT)
open Classical in
def extendOne (v : Set (SliceSite μ)) (g : v → ComplexMatrix2.specialUnitary) (y : SliceSite μ) :
    ComplexMatrix2.specialUnitary :=
  if hy : y ∈ v then g ⟨y, hy⟩ else 1
theorem extendOne_of_mem {v : Set (SliceSite μ)} (g : v → ComplexMatrix2.specialUnitary)
    {y : SliceSite μ} (hy : y ∈ v) : extendOne v g y = g ⟨y, hy⟩ := dif_pos hy
theorem isTemporalGaugeWith_diagonalGaugeAct (S : Stack) (v : Set (SliceSite μ)) [Finite v]
    (g : v → ComplexMatrix2.specialUnitary) {u : S.indexPairs v → ComplexMatrix2.specialUnitary}
    {U : GaugeField 1} (hU : S.IsTemporalGaugeWith v u U) :
    S.IsTemporalGaugeWith v
      (diagonalGaugeAct (S.snd_mem_linksWithin_of_mem_indexPairs v) g u)
      ((columnGauge S v fun _ => extendOne v g).act U) := by
  refine ⟨fun p => ?_, fun j y h₁ h₂ h₃ => ?_⟩
  · have hu := hU.1 p
    obtain ⟨⟨j, b⟩, h₁, h₂, h₃⟩ := p
    rw [spatialLinkVariable_act, columnGauge_toFun S v _ h₁ h₂ h₃.1,
      columnGauge_toFun S v _ h₁ h₂ h₃.2, hu, extendOne_of_mem g h₃.1, extendOne_of_mem g h₃.2]
    rfl
  · rw [temporalLinkVariable_act, columnGauge_toFun S v _ h₁ h₂.le h₃,
      columnGauge_toFun S v _ (by omega) (by omega) h₃, hU.2 j y h₁ h₂ h₃]
    group
theorem observableFactorsThroughTransported (hT : SpecialUnitaryTraceFacts) (S : Stack)
    (v : Set (SliceSite μ)) [Finite v] : ObservableFactorsThroughTransported S v := by
  intro F hF hG hD
  have first : ∀ u U, S.IsTemporalGaugeWith v u U → F U = S.temporalGaugeValue v F u :=
    fun u U h =>
      hD _ _ (eq_on_links_of_isTemporalGaugeWith h (S.isTemporalGaugeWith_temporalGaugeField v u))
  have hinv : ∀ (g : GaugeTransform 1) (U : GaugeField 1), F (g.act U) = F U :=
    fun g U => congrFun (hG g) U
  obtain ⟨C, hC⟩ := hF.2
  refine ⟨first, fun U => ?_, ?_, ⟨C, fun u => hC _⟩, fun g u => ?_,
    fun hc => hc.comp (continuous_temporalGaugeField S v), fun hp => ?_⟩
  · rw [← hinv (columnGauge S v (S.parallelTransport μ U)) U]
    exact first _ _ (isTemporalGaugeWith_parallelTransport S v U)
  · exact hF.1.comp (continuous_temporalGaugeField S v).measurable
  · have hu := S.isTemporalGaugeWith_temporalGaugeField v u
    rw [← first _ _ (isTemporalGaugeWith_diagonalGaugeAct S v g hu), hinv]
    rfl
  · refine isEntryPolynomial_comp hT (Ψ := S.temporalGaugeFamily v)
      (F := fun g => F (gaugeFieldOfPositive one_pos g)) (fun c => ?_) hp
    unfold Stack.temporalGaugeFamily
    by_cases h : ∃ p : S.indexPairs v, (spatialLink μ p.1.1 p.1.2).1 = c.1
    · simp only [dif_pos h]
      exact .eval _
    · simp only [dif_neg h]
      exact .const 1
theorem transportedFunctionIsObservable (hT : SpecialUnitaryTraceFacts) (S : Stack)
    (v : Set (SliceSite μ)) : TransportedFunctionIsObservable S v := by
  rintro Φ hΦ ⟨C, hC⟩ hI
  have hm : Measurable (S.transportedIndexed v) :=
    measurable_pi_iff.2 fun p => (continuous_transportedLinkVariable S p.1.1 p.1.2).measurable
  refine ⟨⟨hΦ.comp hm, C, fun U => hC _⟩, fun g => funext fun U => ?_,
    fun U U' h => congrArg Φ (transportedIndexed_congr S v h),
    fun hc => hc.comp (continuous_transportedIndexed S v), fun hp => ?_⟩
  · have e : S.transportedIndexed v (g.act U) =
        diagonalGaugeAct (S.snd_mem_linksWithin_of_mem_indexPairs v)
          (fun y : v => g.toFun (pointAtLevel μ S.lower y)) (S.transportedIndexed v U) :=
      funext fun p => transportedLinkVariable_act S g U p.1.2 p.2.1
    change Φ (S.transportedIndexed v (g.act U)) = Φ (S.transportedIndexed v U)
    rw [e]
    exact hI _ _
  · have e : ∀ p : S.indexPairs v, HasPolynomialEntries
        fun g : positiveLinks (1 : ℝ) → ComplexMatrix2.specialUnitary =>
          S.transportedIndexed v (gaugeFieldOfPositive one_pos g) p :=
      fun p => hasPolynomialEntries_transportedLinkVariable hT S p.1.1 p.1.2
    exact isEntryPolynomial_comp hT
      (Ψ := fun g : positiveLinks (1 : ℝ) → ComplexMatrix2.specialUnitary =>
        S.transportedIndexed v (gaugeFieldOfPositive one_pos g)) e hp
theorem fullTrace_conj (g w : ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.fullTrace ((g * w * g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      ComplexMatrix2.fullTrace (w : ComplexMatrix2) := by apply _root_.YangMills.Construction.InfiniteLattice.SUTwoTrace.fullTrace_conj <;> assumption
theorem ofReal_one_sub_half_re_fullTrace (hT : SpecialUnitaryTraceFacts)
    (w : ComplexMatrix2.specialUnitary) :
    ((1 - (1 / 2) * (ComplexMatrix2.fullTrace (w : ComplexMatrix2)).re : ℝ) : ℂ) =
      1 - (1 / 2 : ℂ) * ComplexMatrix2.fullTrace (w : ComplexMatrix2) := by
  have him : (ComplexMatrix2.fullTrace (w : ComplexMatrix2)).im = 0 := (hT.2 w).2.2.2.2.2.1
  generalize ComplexMatrix2.fullTrace (w : ComplexMatrix2) = t at him ⊢
  obtain ⟨r, rfl⟩ : ∃ r : ℝ, t = r := ⟨t.re, Complex.ext (by simp) (by simp [him])⟩
  simp
theorem spatialLink_ofAxis (j : ℤ) (y : SliceSite μ) (ρ : Fin 4) (h : ρ ≠ μ) {x : LatticePoint 1}
    (hx : x = (y : LatticePoint 1) + j • axisStep 1 μ) :
    (spatialLink μ j (SliceLink.ofAxis y ρ h)).1 = Link.forwardFrom x ρ := by
  subst hx
  refine InfiniteLattice.Link.ext ?_ ?_
  · change j • axisStep 1 μ + (y : LatticePoint 1) = (y : LatticePoint 1) + j • axisStep 1 μ
    exact add_comm _ _
  change j • axisStep 1 μ + ((y : LatticePoint 1) + axisStep 1 ρ) =
    (y : LatticePoint 1) + j • axisStep 1 μ + axisStep 1 ρ
  abel
theorem faceHolonomy_shiftedPlaquette (U : GaugeField 1) (j : ℤ) (p : SlicePlaquette μ) :
    faceHolonomy U (shiftedPlaquette μ j p) =
      spatialLinkVariable μ U j p.bottomLink * spatialLinkVariable μ U j p.rightLink *
        (spatialLinkVariable μ U j p.topLink)⁻¹ * (spatialLinkVariable μ U j p.leftLink)⁻¹ := by
  have h₁ : (spatialLink μ j p.bottomLink).1 =
      Link.forwardFrom (p.1.corner + j • axisStep 1 μ) p.1.lowAxis :=
    spatialLink_ofAxis j p.origin _ _ rfl
  have h₂ : (spatialLink μ j p.rightLink).1 =
      Link.forwardFrom (p.1.corner + j • axisStep 1 μ + axisStep 1 p.1.lowAxis) p.1.highAxis :=
    spatialLink_ofAxis j _ _ _ (add_right_comm p.1.corner _ _)
  have h₃ : (spatialLink μ j p.topLink).1 =
      Link.forwardFrom (p.1.corner + j • axisStep 1 μ + axisStep 1 p.1.highAxis) p.1.lowAxis :=
    spatialLink_ofAxis j _ _ _ (add_right_comm p.1.corner _ _)
  have h₄ : (spatialLink μ j p.leftLink).1 =
      Link.forwardFrom (p.1.corner + j • axisStep 1 μ) p.1.highAxis :=
    spatialLink_ofAxis j p.origin _ _ rfl
  simp only [spatialLinkVariable, h₁, h₂, h₃, h₄]
  rfl
theorem conj_loop_four {H : Type*} [Group H] (g₀ g₁ g₂ g₃ g₄ a b c d : H) (h : g₂ = g₄) :
    (g₀ * a * g₁⁻¹) * (g₁ * b * g₂⁻¹) * (g₃ * c * g₄⁻¹)⁻¹ * (g₀ * d * g₃⁻¹)⁻¹ =
      g₀ * (a * b * c⁻¹ * d⁻¹) * g₀⁻¹ := by
  subst h
  group
theorem plaquetteHolonomy_eq_conj (S : Stack) (U : GaugeField 1) (j : ℤ) (p : SlicePlaquette μ)
    {T : Set (SliceLink μ)} (hT : p.links ⊆ T) (f : T → ComplexMatrix2.specialUnitary)
    (hf : ∀ b, f b = S.transportedLinkVariable μ U j b.1) :
    plaquetteHolonomy p hT f = S.parallelTransport μ U j p.origin *
      faceHolonomy U (shiftedPlaquette μ j p) * (S.parallelTransport μ U j p.origin)⁻¹ := by
  have hc : (p.origin.shift p.1.lowAxis p.lowAxis_ne).shift p.1.highAxis p.highAxis_ne =
      (p.origin.shift p.1.highAxis p.highAxis_ne).shift p.1.lowAxis p.lowAxis_ne :=
    Subtype.ext (add_right_comm _ _ _)
  rw [faceHolonomy_shiftedPlaquette]
  simp only [plaquetteHolonomy, hf]
  exact conj_loop_four _ (S.parallelTransport μ U j (p.origin.shift p.1.lowAxis p.lowAxis_ne))
    (S.parallelTransport μ U j
      ((p.origin.shift p.1.lowAxis p.lowAxis_ne).shift p.1.highAxis p.highAxis_ne))
    (S.parallelTransport μ U j (p.origin.shift p.1.highAxis p.highAxis_ne))
    (S.parallelTransport μ U j
      ((p.origin.shift p.1.highAxis p.highAxis_ne).shift p.1.lowAxis p.lowAxis_ne))
    _ _ _ _ (by rw [hc])
theorem faceEnergy_shiftedPlaquette (hT : SpecialUnitaryTraceFacts) (S : Stack) (U : GaugeField 1)
    (j : ℤ) (p : SlicePlaquette μ) {T : Set (SliceLink μ)} (hb : p.links ⊆ T)
    (f : T → ComplexMatrix2.specialUnitary) (hf : ∀ b, f b = S.transportedLinkVariable μ U j b.1) :
    ((faceEnergy U (shiftedPlaquette μ j p) : ℝ) : ℂ) =
      1 - (1 / 2 : ℂ) * ComplexMatrix2.fullTrace
        ((plaquetteHolonomy p hb f : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by
  rw [plaquetteHolonomy_eq_conj S U j p hb f hf, fullTrace_conj, faceEnergy]
  exact ofReal_one_sub_half_re_fullTrace hT _
theorem faceEnergy_temporalPlaquette (hT : SpecialUnitaryTraceFacts) (hP : PlaquetteProperties 1)
    (S : Stack) (U : GaugeField 1) {j : ℤ} (hj : S.lower ≤ j) (b : SliceLink μ) :
    ((faceEnergy U (temporalPlaquette μ j b) : ℝ) : ℂ) =
      1 - (1 / 2 : ℂ) * ComplexMatrix2.fullTrace ((S.transportedLinkVariable μ U j b *
        (S.transportedLinkVariable μ U (j + 1) b)⁻¹ : ComplexMatrix2.specialUnitary) :
          ComplexMatrix2) := by
  have hc := hP.2.1 (temporalPlaquette μ j b) U (spatialLink μ j b).1
    (temporalLink μ j b.target).1 (spatialLink μ (j + 1) b).1.opposite
    (temporalLink μ j b.source).1.opposite (cornerSet_temporalPlaquette μ j b).symm rfl rfl rfl rfl
  have hW : U (spatialLink μ j b).1 * U (temporalLink μ j b.target).1 *
      U (spatialLink μ (j + 1) b).1.opposite * U (temporalLink μ j b.source).1.opposite =
      spatialLinkVariable μ U j b * temporalLinkVariable μ U j b.target *
        (spatialLinkVariable μ U (j + 1) b)⁻¹ * (temporalLinkVariable μ U j b.source)⁻¹ := by
    rw [U.2 (spatialLink μ (j + 1) b).1, U.2 (temporalLink μ j b.source).1]
    rfl
  rw [hW] at hc
  have hg : S.transportedLinkVariable μ U j b * (S.transportedLinkVariable μ U (j + 1) b)⁻¹ =
      S.parallelTransport μ U j b.source * (spatialLinkVariable μ U j b *
        temporalLinkVariable μ U j b.target * (spatialLinkVariable μ U (j + 1) b)⁻¹ *
          (temporalLinkVariable μ U j b.source)⁻¹) * (S.parallelTransport μ U j b.source)⁻¹ := by
    simp only [Stack.transportedLinkVariable]
    rw [parallelTransport_succ S U _ hj, parallelTransport_succ S U _ hj]
    group
  rw [hg, fullTrace_conj, ← ofReal_one_sub_half_re_fullTrace hT, faceEnergy, hc]
theorem faceEnergiesInTransported (hT : SpecialUnitaryTraceFacts) (hP : PlaquetteProperties 1)
    (β : ℝ) (S : Stack) : FaceEnergiesInTransported μ β S := by
  intro U
  refine ⟨fun j b h₁ _ => faceEnergy_temporalPlaquette hT hP S U h₁ b,
    fun j p _ _ => faceEnergy_shiftedPlaquette hT S U j p _ _ fun _ => rfl, fun j B _ _ => ?_⟩
  rw [Block.sliceEnergy]
  congr 1
  refine finsum_congr fun p => faceEnergy_shiftedPlaquette hT S U j p.1 _ _ fun b => ?_
  by_cases h : b.1 ∈ B.links
  · exact (dif_pos h).trans rfl
  · exact (dif_neg h).trans rfl
theorem mainStatement (hE : ElementaryLatticeFacts) (hT : TraceAndSingleBondWeight) :
    MainStatement := by
  have hP : PlaquetteProperties 1 := (hE 1 1 one_pos one_pos).2.1
  intro μ S
  exact ⟨fun v _ _ => ⟨observableFactorsThroughTransported hT.1 S v,
      transportedFunctionIsObservable hT.1 S v⟩,
    fun β _ => faceEnergiesInTransported hT.1 hP β S, gaugeActionOnTransported S⟩
end TransferOperators.TemporalGauge
end YangMills.Construction
end
