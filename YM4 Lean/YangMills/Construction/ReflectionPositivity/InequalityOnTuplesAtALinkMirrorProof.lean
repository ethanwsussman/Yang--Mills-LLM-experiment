import YangMills.Construction.ReflectionPositivity.CentredMomentsAreSumsOfCumulants
import YangMills.Construction.ReflectionPositivity.DoublingOfTheCrossingVariables
import YangMills.Construction.ReflectionPositivity.FourSetsOfHeightsAndTheLinkPositionHalfASideOn
import YangMills.Construction.ReflectionPositivity.InequalityOnTuplesAtALinkMirror
import YangMills.Construction.ReflectionPositivity.ObservablesOfOneSideOfALinkMirror
import YangMills.Construction.ReflectionPositivity.PositivityOfTheWilsonMeasureAtALinkMirror
import YangMills.Construction.ReflectionPositivity.ReflectionInALinkMirror
import YangMills.Construction.ReflectionPositivity.SpaceOfConfigurationsAndPlaquetteEnergiesAtOneCutoff
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.TupleInequality
noncomputable section
section
variable {D : MirrorData}
theorem ae_mem_compactGaugeFields
    (h₁ : IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling))
    (h₂ : IsProbabilityMeasure D.gibbsMeasureOnFields) :
    ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling,
      U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) := by
  set μ := PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling with hμ
  set W := PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) with hW
  have hinj : Function.Injective (Subtype.val : W → _) ∧
      ∀ s : Set W, MeasurableSet s → NullMeasurableSet (Subtype.val '' s) μ := by
    by_contra h
    have hzero : μ.comap (Subtype.val : W → _) = 0 := by
      rw [Measure.comap, dif_neg h]
    exact IsProbabilityMeasure.ne_zero D.gibbsMeasureOnFields hzero
  have hW1 : μ W = 1 := by
    have e := Measure.comap_apply₀ (Subtype.val : W → _) μ hinj.1 hinj.2
      (s := univ) MeasurableSet.univ.nullMeasurableSet
    have e' : (μ.comap (Subtype.val : W → _)) univ = 1 := h₂.measure_univ
    rw [e'] at e
    rw [image_univ, Subtype.range_val] at e
    exact e.symm
  have hnull : NullMeasurableSet W μ := by
    have := hinj.2 univ MeasurableSet.univ
    rwa [image_univ, Subtype.range_val] at this
  exact mem_ae_iff.2 ((prob_compl_eq_zero_iff₀ hnull).2 hW1)
theorem measurable_mul_of_matrix {X : Type*} [MeasurableSpace X]
    {f g : X → Matrices.ComplexMatrix2}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x * g x := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have h : Measurable fun x : Matrices.ComplexMatrix2 × Matrices.ComplexMatrix2 => x.1 * x.2 :=
    (continuous_fst.mul continuous_snd).measurable
  exact h.comp (hf.prodMk hg)
theorem measurable_plaquetteEnergy (p : D.Face) :
    Measurable fun U : D.BondField => PeriodicLattice.plaquetteCost U p := by
  have hU : ∀ b : D.DirectedBond, Measurable fun U : D.BondField => U b :=
    fun b => measurable_pi_apply b
  have hl : ∀ γ : List D.DirectedBond, Measurable fun U : D.BondField => (γ.map U).prod := by
    intro γ
    induction γ with
    | nil => simpa using measurable_const
    | cons b γ ih => simpa using measurable_mul_of_matrix (hU b) ih
  have hv : Measurable fun U : D.BondField => PeriodicLattice.plaquetteHolonomy U p := by
    unfold PeriodicLattice.plaquetteHolonomy PeriodicLattice.pathHolonomy
    exact hl _
  have ht : Measurable fun A : Matrices.ComplexMatrix2 =>
      (Matrices.ComplexMatrix2.fullTrace A).re := by
    have : Continuous fun A : Matrices.ComplexMatrix2 =>
        (Matrices.ComplexMatrix2.fullTrace A).re := by
      unfold Matrices.ComplexMatrix2.fullTrace
      fun_prop
    exact this.measurable
  unfold PeriodicLattice.plaquetteCost
  exact measurable_const.sub (measurable_const.mul (ht.comp hv))
def BoundedBorel (g : D.BondField → ℝ) : Prop :=
  Measurable g ∧ ∃ B : ℝ, ∀ U : D.FieldSpace, |g U.1| ≤ B
theorem BoundedBorel.const (r : ℝ) : BoundedBorel (D := D) fun _ => r :=
  ⟨measurable_const, |r|, fun _ => le_rfl⟩
theorem BoundedBorel.mul {g h : D.BondField → ℝ} (hg : BoundedBorel g) (hh : BoundedBorel h) :
    BoundedBorel fun U => g U * h U := by
  obtain ⟨mg, B, hB⟩ := hg
  obtain ⟨mh, B', hB'⟩ := hh
  refine ⟨mg.mul mh, |B| * |B'|, fun U => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hB U).trans (le_abs_self _)) ((hB' U).trans (le_abs_self _)) (abs_nonneg _)
    (abs_nonneg _)
theorem BoundedBorel.sub_const {g : D.BondField → ℝ} (hg : BoundedBorel g) (r : ℝ) :
    BoundedBorel fun U => g U - r := by
  obtain ⟨mg, B, hB⟩ := hg
  refine ⟨mg.sub measurable_const, B + |r|, fun U => ?_⟩
  exact (abs_sub _ _).trans (add_le_add (hB U) le_rfl)
theorem BoundedBorel.pow {g : D.BondField → ℝ} (hg : BoundedBorel g) (n : ℕ) :
    BoundedBorel fun U => g U ^ n := by
  induction n with
  | zero => simpa using BoundedBorel.const (D := D) 1
  | succ n ih => simpa [pow_succ] using ih.mul hg
theorem BoundedBorel.finset_prod {ι : Type*} (S : Finset ι) {g : ι → D.BondField → ℝ}
    (hg : ∀ k ∈ S, BoundedBorel (g k)) : BoundedBorel fun U => ∏ k ∈ S, g k U := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using BoundedBorel.const (D := D) 1
  | insert a S ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hg a (Finset.mem_insert_self a S)).mul
      (ih fun k hk => hg k (Finset.mem_insert_of_mem hk))
theorem boundedBorel_smearedObservable (hS : FieldSpaceAndFaceEnergies.Statement)
    (f : D.Torus → ℝ) : BoundedBorel (D := D) (PeriodicLattice.smearedObservable f) := by
  obtain ⟨⟨-, -, hP, -⟩, -, -, hB, -⟩ := hS D
  have : Finite D.Face := hP
  have := Fintype.ofFinite D.Face
  refine ⟨?_, (hB f).2⟩
  have e : (PeriodicLattice.smearedObservable f : D.BondField → ℝ) = fun U =>
      ∑ p : D.Face, PeriodicLattice.plaquetteCost U p • f p.barycenter := by
    funext U
    exact finsum_eq_sum_of_fintype _
  rw [e]
  refine Finset.measurable_sum _ fun p _ => ?_
  simpa [smul_eq_mul] using (measurable_plaquetteEnergy p).mul_const (f p.barycenter)
theorem boundedBorel_centredObservable (hS : FieldSpaceAndFaceEnergies.Statement)
    (f : D.Torus → ℝ) : BoundedBorel (D := D) (D.centredObservable f) :=
  (boundedBorel_smearedObservable hS f).sub_const _
theorem BoundedBorel.integrable (hS : FieldSpaceAndFaceEnergies.Statement)
    {g : D.BondField → ℝ} (hg : BoundedBorel g) :
    Integrable g (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) := by
  obtain ⟨-, -, hE⟩ := hS D
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h₁, h₂⟩ := hE
  have := h₁
  obtain ⟨mg, B, hB⟩ := hg
  refine Integrable.of_bound mg.aestronglyMeasurable B ?_
  filter_upwards [ae_mem_compactGaugeFields h₁ h₂] with U hU
  simpa using hB ⟨U, hU⟩
theorem thetaForm_eq_double_sum (hS : FieldSpaceAndFaceEnergies.Statement)
    (C : LinkLevel D) {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (P Q : ι → D.BondField → ℝ) (hP : ∀ k ∈ S, BoundedBorel (P k))
    (hQ : ∀ k ∈ S, BoundedBorel (Q k))
    (F : D.FieldSpace → ℂ) (hF : ∀ U : D.FieldSpace, F U = ∑ k ∈ S, c k * (Q k U.1 : ℂ))
    (hFθ : ∀ U : D.FieldSpace, F (C.reflectField U) =
      ∑ k ∈ S, c k * (P k U.1 : ℂ)) :
    C.thetaForm F F = ∑ i ∈ S, ∑ j ∈ S, conj (c i) * c j *
      ((PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
        (fun U => P i U * Q j U) : ℝ) : ℂ) := by
  classical
  have hae := by
    obtain ⟨-, -, hE⟩ := hS D
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h₁, h₂⟩ := hE
    exact ae_mem_compactGaugeFields h₁ h₂
  have hint : ∀ i ∈ S, ∀ j ∈ S, Integrable (fun U => P i U * Q j U)
      (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) :=
    fun i hi j hj => ((hP i hi).mul (hQ j hj)).integrable hS
  have hcongr : (fun U : D.BondField =>
      if h : U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) then
        conj (F (C.reflectField ⟨U, h⟩)) * F ⟨U, h⟩ else 0)
      =ᵐ[PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling]
      fun U => ∑ i ∈ S, ∑ j ∈ S, conj (c i) * c j * ((P i U * Q j U : ℝ) : ℂ) := by
    filter_upwards [hae] with U hU
    rw [dif_pos hU, hFθ, hF, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  unfold LinkLevel.thetaForm MirrorData.fieldExpectation
  unfold PeriodicLattice.gibbsExpectation
  rw [integral_congr_ae hcongr, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_complex_ofReal]
    · exact fun j hj => ((hint i hi j hj).ofReal).const_mul _
  · exact fun i hi => integrable_finsetSum _ fun j hj => ((hint i hi j hj).ofReal).const_mul _
theorem BoundedBorel.list_prod {α : Type*} (X : List α) {g : α → D.BondField → ℝ}
    (hg : ∀ x ∈ X, BoundedBorel (g x)) : BoundedBorel fun U => (X.map fun x => g x U).prod := by
  induction X with
  | nil => simpa using BoundedBorel.const (D := D) 1
  | cons x X ih =>
    simpa using (hg x (List.mem_cons_self)).mul
      (ih fun y hy => hg y (List.mem_cons_of_mem x hy))
end
section
variable {D : MirrorData} {C : LinkLevel D}
theorem sum_mem_halfAlgebra (hA : DoubledTransversal.HalfAlgebraClosed C .pos)
    {ι : Type*} (S : Finset ι) {G : ι → D.FieldSpace → ℂ}
    (hG : ∀ k ∈ S, G k ∈ C.halfAlgebra .pos) (c : ι → ℂ) :
    (fun U => ∑ k ∈ S, c k * G k U) ∈ C.halfAlgebra .pos := by
  classical
  obtain ⟨-, h0, hadd, hsmul, -, -⟩ := hA
  induction S using Finset.induction_on with
  | empty => simpa using h0 0
  | insert a S ha ih =>
    have h := hadd _ (hsmul (c a) _ (hG a (Finset.mem_insert_self a S))) _
      (ih fun k hk => hG k (Finset.mem_insert_of_mem hk))
    convert h using 1
    funext U
    simp [Finset.sum_insert ha]
theorem list_prod_mem_halfAlgebra (hA : DoubledTransversal.HalfAlgebraClosed C .pos)
    {α : Type*} (X : List α) {G : α → D.FieldSpace → ℂ}
    (hG : ∀ x ∈ X, G x ∈ C.halfAlgebra .pos) :
    (fun U => (X.map fun x => G x U).prod) ∈ C.halfAlgebra .pos := by
  obtain ⟨-, h0, -, -, hmul, -⟩ := hA
  induction X with
  | nil => simpa using h0 1
  | cons x X ih =>
    have e : (fun U => ((x :: X).map fun y => G y U).prod) =
        G x * fun U => (X.map fun y => G y U).prod := by
      funext U
      simp
    rw [e]
    exact hmul _ (hG x List.mem_cons_self) _ (ih fun y hy => hG y (List.mem_cons_of_mem x hy))
theorem pow_mem_halfAlgebra (hA : DoubledTransversal.HalfAlgebraClosed C .pos)
    {F : D.FieldSpace → ℂ} (hF : F ∈ C.halfAlgebra .pos) (n : ℕ) :
    (fun U => F U ^ n) ∈ C.halfAlgebra .pos := by
  obtain ⟨-, h0, -, -, hmul, -⟩ := hA
  induction n with
  | zero => simpa using h0 1
  | succ n ih =>
    have e : (fun U => F U ^ (n + 1)) = (fun U => F U ^ n) * F := by
      funext U
      simp [pow_succ]
    rw [e]
    exact hmul _ ih _ hF
theorem finset_prod_mem_halfAlgebra (hA : DoubledTransversal.HalfAlgebraClosed C .pos)
    {ι : Type*} (S : Finset ι) {G : ι → D.FieldSpace → ℂ}
    (hG : ∀ k ∈ S, G k ∈ C.halfAlgebra .pos) :
    (fun U => ∏ k ∈ S, G k U) ∈ C.halfAlgebra .pos := by
  classical
  obtain ⟨-, h0, -, -, hmul, -⟩ := hA
  induction S using Finset.induction_on with
  | empty => simpa using h0 1
  | insert a S ha ih =>
    simp only [Finset.prod_insert ha]
    exact hmul _ (hG a (Finset.mem_insert_self a S)) _
      (ih fun k hk => hG k (Finset.mem_insert_of_mem hk))
end
section
variable {D : MirrorData}
theorem get_map_cast {α β : Type*} (g : α → β) (X : List α) (l : Fin (X.map g).length) :
    (X.map g).get l = g (X.get (l.cast (List.length_map g))) := by
  simp [List.get_eq_getElem]
theorem ofReal_prodOver (X : D.FunTuple ℝ) (G : (D.Torus → ℝ) → ℝ) :
    ((MirrorData.FunTuple.prodOver X G : ℝ) : ℂ) =
      MirrorData.FunTuple.prodOver X fun f => (G f : ℂ) := by
  induction X with
  | nil => simp [MirrorData.FunTuple.prodOver]
  | cons f X ih =>
    simp only [MirrorData.FunTuple.prodOver, List.map_cons, List.prod_cons,
      Complex.ofReal_mul] at ih ⊢
    rw [ih]
theorem prod_get_eq_prodOver (Y : D.FunTuple ℝ) (G : (D.Torus → ℝ) → ℝ) :
    ∏ l : Fin Y.length, G (Y.get l) = MirrorData.FunTuple.prodOver Y G := by
  simpa [MirrorData.FunTuple.prodOver] using Fin.prod_univ_fun_getElem Y G
theorem prodOver_append (A B : D.FunTuple ℝ) (G : (D.Torus → ℝ) → ℝ) :
    MirrorData.FunTuple.prodOver (A ++ B) G =
      MirrorData.FunTuple.prodOver A G * MirrorData.FunTuple.prodOver B G := by
  simp [MirrorData.FunTuple.prodOver]
theorem prodOver_reflectTuple (C : LinkLevel D) (X : D.FunTuple ℝ) (G : (D.Torus → ℝ) → ℝ) :
    MirrorData.FunTuple.prodOver (C.reflectTuple X) G =
      MirrorData.FunTuple.prodOver X fun f => G (C.reflectFn f) := by
  simp [MirrorData.FunTuple.prodOver, LinkLevel.reflectTuple, List.map_map, Function.comp_def]
theorem prodOver_congr (X : D.FunTuple ℝ) {R : Type*} [Monoid R] {G G' : (D.Torus → ℝ) → R}
    (h : ∀ f ∈ X, G f = G' f) :
    MirrorData.FunTuple.prodOver X G = MirrorData.FunTuple.prodOver X G' := by
  unfold MirrorData.FunTuple.prodOver
  rw [List.map_congr_left h]
theorem disjoint_openSlabs (hH : LevelPartition.Claim) (C : LinkLevel D) :
    Disjoint (C.openSlab .pos) (C.openSlab .neg) :=
  (hH D C).1.2.1.1 (show (0 : Fin 4) ≠ 1 by decide)
theorem reflectTuple_isAdmissibleArg (hCl : TorusMetricSpace.MetricTorusFacts)
    (hR : LinkReflection.LinkReflectionProperties) (hO : OneSideObservables.HalfSpaceObservables)
    (C : LinkLevel D) (X : D.FunTuple ℝ) (hX : IsPosSideArgs C X.get) :
    D.IsAdmissibleArg (C.reflectTuple X).get ∧
      ∀ l, D.supp ((C.reflectTuple X).get l) ⊆ C.openSlab .neg := by
  obtain ⟨⟨hinv, hiso, -⟩, -⟩ := hR D C
  obtain ⟨-, hBd, -, hIso⟩ := hCl D
  obtain ⟨-, hfun, -, hdisj⟩ := hIso C.refl hinv.bijective hiso
  have hlen : (C.reflectTuple X).length = X.length := by simp [LinkLevel.reflectTuple]
  have get_eq : ∀ l : Fin (C.reflectTuple X).length,
      (C.reflectTuple X).get l = C.reflectFn (X.get (l.cast hlen)) :=
    fun l => get_map_cast C.reflectFn X l
  refine ⟨⟨fun l => ?_, fun l l' hne => ?_⟩, fun l => ?_⟩
  · rw [get_eq]
    exact (hfun ℝ _).2.2.2 (hX.1.1 _)
  · rw [get_eq, get_eq]
    refine (hdisj ℝ X.length X.get).1 hX.1.2 _ _ ?_
    intro h
    exact hne (Fin.ext (by simpa using congrArg Fin.val h))
  · rw [get_eq]
    exact (((hO D C).1 _ (hBd ℝ _ (hX.1.1 _)).2.1 (hX.2 _)).2.2.2).2.1
theorem append_isAdmissibleArg (C : LinkLevel D)
    (hd : Disjoint (C.openSlab .pos) (C.openSlab .neg))
    (A B : D.FunTuple ℝ) (hA : D.IsAdmissibleArg A.get)
    (hB : D.IsAdmissibleArg B.get) (hAs : ∀ l, D.supp (A.get l) ⊆ C.openSlab .neg)
    (hBs : ∀ l, D.supp (B.get l) ⊆ C.openSlab .pos) : D.IsAdmissibleArg (A ++ B).get := by
  have hcase : ∀ l : Fin (A ++ B).length,
      (∃ k : Fin A.length, k.1 = l.1 ∧ (A ++ B).get l = A.get k) ∨
        ∃ k : Fin B.length, k.1 + A.length = l.1 ∧ (A ++ B).get l = B.get k := by
    intro l
    by_cases h : l.1 < A.length
    · exact Or.inl ⟨⟨l.1, h⟩, rfl, by simp [List.getElem_append_left h]⟩
    · have h' : l.1 - A.length < B.length := by
        have := l.2
        simp only [List.length_append] at this
        omega
      refine Or.inr ⟨⟨l.1 - A.length, h'⟩, by simp; omega, ?_⟩
      simp [List.getElem_append_right (not_lt.1 h)]
  have hcross : ∀ (k : Fin A.length) (k' : Fin B.length),
      D.supp (A.get k) ∩ D.supp (B.get k') = ∅ := by
    intro k k'
    apply Set.eq_empty_of_forall_notMem
    rintro x ⟨hx, hx'⟩
    exact Set.disjoint_left.1 hd (hBs k' hx') (hAs k hx)
  refine ⟨fun l => ?_, fun l l' hne => ?_⟩
  · rcases hcase l with ⟨k, -, e⟩ | ⟨k, -, e⟩
    · rw [e]
      exact hA.1 k
    · rw [e]
      exact hB.1 k
  · have hval : l.1 ≠ l'.1 := fun h => hne (Fin.ext h)
    rcases hcase l with ⟨k, hk, e⟩ | ⟨k, hk, e⟩ <;> rcases hcase l' with ⟨k', hk', e'⟩ | ⟨k', hk', e'⟩
    · rw [e, e']
      exact hA.2 k k' fun h => hval (by rw [← hk, ← hk', h])
    · rw [e, e']
      exact hcross k k'
    · rw [e, e', Set.inter_comm]
      exact hcross k' k
    · rw [e, e']
      exact hB.2 k k' fun h => hval (by rw [← hk, ← hk', h])
theorem mem_observable_facts (hCl : TorusMetricSpace.MetricTorusFacts)
    (hO : OneSideObservables.HalfSpaceObservables) (C : LinkLevel D) (X : D.FunTuple ℝ)
    (hX : IsPosSideArgs C X.get) {f : D.Torus → ℝ} (hf : f ∈ X) :
    OneSideObservables.ObservablesMemHalfAlgebra Complex.ofReal C f ∧
      OneSideObservables.ReflectImage C f := by
  obtain ⟨l, rfl⟩ := List.get_of_mem hf
  have h := (hO D C).1 _ ((hCl D).2.1 ℝ _ (hX.1.1 l)).2.1 (hX.2 l)
  exact ⟨h.2.2.1, h.2.2.2⟩
theorem positiveOnTuples (hOS : LinkPositivity.ReflectionPositivityAtLink)
    (hCl : TorusMetricSpace.MetricTorusFacts)
    (hDb : DoubledTransversal.DoublingProperties) (hH : LevelPartition.Claim)
    (hO : OneSideObservables.HalfSpaceObservables)
    (hS : FieldSpaceAndFaceEnergies.Statement)
    (hM : CentredMomentCumulantExpansion) (hR : LinkReflection.LinkReflectionProperties)
    (C : LinkLevel D) : PositiveOnTuples C := by
  intro t _ X ζ hX
  have hA : DoubledTransversal.HalfAlgebraClosed C .pos :=
    ((hDb D C).2.2.1 .pos).2.1
  have harg : ∀ i j, D.IsAdmissibleArg (C.reflectTuple (X i) ++ X j).get := fun i j =>
    append_isAdmissibleArg C (disjoint_openSlabs hH C) _ _
      (reflectTuple_isAdmissibleArg hCl hR hO C _ (hX i)).1
      (hX j).1 (reflectTuple_isAdmissibleArg hCl hR hO C _ (hX i)).2 (hX j).2
  let P : Fin t → D.BondField → ℝ := fun i U =>
    MirrorData.FunTuple.prodOver (X i) fun f => D.centredObservable (C.reflectFn f) U
  let Q : Fin t → D.BondField → ℝ := fun i U =>
    MirrorData.FunTuple.prodOver (X i) fun f => D.centredObservable f U
  have hP : ∀ i ∈ (Finset.univ : Finset (Fin t)), BoundedBorel (P i) := fun i _ =>
    BoundedBorel.list_prod (X i) fun f _ => boundedBorel_centredObservable hS _
  have hQ : ∀ i ∈ (Finset.univ : Finset (Fin t)), BoundedBorel (Q i) := fun i _ =>
    BoundedBorel.list_prod (X i) fun f _ => boundedBorel_centredObservable hS _
  have hmem : tupleCombination X ζ ∈ C.halfAlgebra .pos := by
    refine sum_mem_halfAlgebra hA Finset.univ (G := fun i U =>
      MirrorData.FunTuple.prodOver (X i) fun f =>
      ((D.centredObservable f U.1 : ℝ) : ℂ)) (fun i _ => ?_) ζ
    exact list_prod_mem_halfAlgebra hA (X i)
      (G := fun f U => ((D.centredObservable f U.1 : ℝ) : ℂ))
      fun f hf => (mem_observable_facts hCl hO C _ (hX i) hf).1.2
  have hF : ∀ U : D.FieldSpace, tupleCombination X ζ U =
      ∑ i ∈ Finset.univ, ζ i * (Q i U.1 : ℂ) := by
    intro U
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ofReal_prodOver]
  have hFθ : ∀ U : D.FieldSpace, tupleCombination X ζ (C.reflectField U) =
      ∑ i ∈ Finset.univ, ζ i * (P i U.1 : ℂ) := by
    intro U
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ofReal_prodOver]
    congr 1
    refine prodOver_congr (X i) fun f hf => ?_
    rw [(mem_observable_facts hCl hO C _ (hX i) hf).2.2.2.2 U]
  have hform := thetaForm_eq_double_sum hS C Finset.univ ζ P Q hP hQ
    (tupleCombination X ζ) hF hFθ
  have hgibbs : ∀ i j, D.gibbsFunctionalList (C.reflectTuple (X i) ++ X j) =
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling (fun U => P i U * Q j U) := by
    intro i j
    unfold MirrorData.gibbsFunctionalList MirrorData.gibbsFunctional
    congr 1
    funext U
    rw [prod_get_eq_prodOver _ fun f => D.centredObservable f U, prodOver_append,
      prodOver_reflectTuple]
  have htrunc : ∀ i j, D.truncatedFunctionalList (C.reflectTuple (X i) ++ X j) =
      ((D.gibbsFunctionalList (C.reflectTuple (X i) ++ X j) : ℝ) : ℂ) := by
    intro i j
    obtain ⟨e₁, e₂⟩ := hM.2 D _ _ (harg i j)
    unfold MirrorData.truncatedFunctionalList MirrorData.gibbsFunctionalList
    rw [e₁, e₂]
  have hpos : 0 ≤ C.thetaForm (tupleCombination X ζ) (tupleCombination X ζ) :=
    (hOS D C).2.1.2.2.1 _ hmem
  have hsum : pairSum C X ζ (fun Y => ((D.gibbsFunctionalList Y : ℝ) : ℂ)) =
      C.thetaForm (tupleCombination X ζ) (tupleCombination X ζ) := by
    rw [hform]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact congrArg (fun z : ℝ => conj (ζ i) * ζ j * (z : ℂ)) (hgibbs i j)
  refine ⟨harg, hmem, ⟨hsum, hpos⟩, ⟨?_, hpos⟩⟩
  rw [← hsum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (fun z : ℂ => conj (ζ i) * ζ j * z) (htrunc i j)
theorem selectTuple_isPosSideArgs (C : LinkLevel D) {q : ℕ} {f : Fin q → D.Torus → ℝ}
    (hf : IsPosSideArgs C f) (A : Finset (Fin q)) :
    IsPosSideArgs C (selectTuple f A).get := by
  have hnd : (A.sort (· ≤ ·)).Nodup := A.sort_nodup (· ≤ ·)
  have get_eq : ∀ l : Fin (selectTuple f A).length,
      (selectTuple f A).get l = f ((A.sort (· ≤ ·)).get (l.cast (List.length_map f))) :=
    fun l => get_map_cast f _ l
  refine ⟨⟨fun l => ?_, fun l l' hne => ?_⟩, fun l => ?_⟩
  · rw [get_eq]
    exact hf.1.1 _
  · rw [get_eq, get_eq]
    refine hf.1.2 _ _ fun h => hne ?_
    have := hnd.injective_get h
    have hval := Fin.val_eq_of_eq this
    exact Fin.ext hval
  · rw [get_eq]
    exact hf.2 _
theorem positiveOnSubtuples (C : LinkLevel D) (h : PositiveOnTuples C) :
    PositiveOnSubtuples C := by
  intro q _ f ζ hf
  let e : Finset (Fin q) ≃ Fin (Fintype.card (Finset (Fin q))) := Fintype.equivFin _
  obtain ⟨-, -, -, hsum, hpos⟩ := h (Fintype.card (Finset (Fin q))) Fintype.card_pos
    (fun k => selectTuple f (e.symm k)) (fun k => ζ (e.symm k))
    fun k => selectTuple_isPosSideArgs C hf _
  rw [← hsum] at hpos
  have hre : ∀ A : Finset (Fin q), C.reflectTuple (selectTuple f A) =
      selectTuple (fun i => C.reflectFn (f i)) A := by
    intro A
    simp [LinkLevel.reflectTuple, selectTuple, List.map_map, Function.comp_def]
  have e₁ : pairSum C (fun k => selectTuple f (e.symm k)) (fun k => ζ (e.symm k))
      D.truncatedFunctionalList =
      ∑ A : Finset (Fin q), ∑ A' : Finset (Fin q), conj (ζ A) * ζ A' *
        D.truncatedFunctionalList
          (selectTuple (fun i => C.reflectFn (f i)) A ++ selectTuple f A') := by
    unfold pairSum
    rw [← e.symm.sum_comp (fun A => ∑ A' : Finset (Fin q), conj (ζ A) * ζ A' *
        D.truncatedFunctionalList
          (selectTuple (fun i => C.reflectFn (f i)) A ++ selectTuple f A'))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← e.symm.sum_comp (fun A' => conj (ζ (e.symm i)) * ζ A' *
        D.truncatedFunctionalList
          (selectTuple (fun i => C.reflectFn (f i)) (e.symm i) ++ selectTuple f A'))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hre]
  rwa [e₁] at hpos
theorem positiveOnPolynomials (hOS : LinkPositivity.ReflectionPositivityAtLink)
    (hCl : TorusMetricSpace.MetricTorusFacts)
    (hDb : DoubledTransversal.DoublingProperties) (hO : OneSideObservables.HalfSpaceObservables)
    (hS : FieldSpaceAndFaceEnergies.Statement)
    (C : LinkLevel D) : PositiveOnPolynomials C := by
  intro q _ f S ξ hf
  have hA : DoubledTransversal.HalfAlgebraClosed C .pos :=
    ((hDb D C).2.2.1 .pos).2.1
  have hfacts : ∀ i, OneSideObservables.ObservablesMemHalfAlgebra Complex.ofReal C (f i) ∧
      OneSideObservables.ReflectImage C (f i) := fun i => by
    have h := (hO D C).1 _ ((hCl D).2.1 ℝ _ (hf.1.1 i)).2.1 (hf.2 i)
    exact ⟨h.2.2.1, h.2.2.2⟩
  let P : (Fin q → ℕ) → D.BondField → ℝ := fun η U =>
    ∏ i, PeriodicLattice.smearedObservable (C.reflectFn (f i)) U ^ η i
  let Q : (Fin q → ℕ) → D.BondField → ℝ := fun η U =>
    ∏ i, PeriodicLattice.smearedObservable (f i) U ^ η i
  have hP : ∀ η ∈ S, BoundedBorel (P η) := fun η _ =>
    BoundedBorel.finset_prod _ fun i _ => (boundedBorel_smearedObservable hS _).pow _
  have hQ : ∀ η ∈ S, BoundedBorel (Q η) := fun η _ =>
    BoundedBorel.finset_prod _ fun i _ => (boundedBorel_smearedObservable hS _).pow _
  let F : D.FieldSpace → ℂ := fun U => ∑ η ∈ S, ξ η * ((Q η U.1 : ℝ) : ℂ)
  have hmem : F ∈ C.halfAlgebra .pos := by
    refine sum_mem_halfAlgebra hA S (G := fun η U => ((Q η U.1 : ℝ) : ℂ)) (fun η _ => ?_) ξ
    have h := finset_prod_mem_halfAlgebra hA Finset.univ
      (G := fun i U => ((PeriodicLattice.smearedObservable (f i) U.1 : ℝ) : ℂ) ^ η i)
      fun i _ => pow_mem_halfAlgebra hA (hfacts i).1.1 (η i)
    convert h using 1
    funext U
    simp [Q]
  have hFθ : ∀ U : D.FieldSpace, F (C.reflectField U) =
      ∑ η ∈ S, ξ η * ((P η U.1 : ℝ) : ℂ) := by
    intro U
    refine Finset.sum_congr rfl fun η _ => ?_
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(hfacts i).2.1 U]
  have hform := thetaForm_eq_double_sum hS C S ξ P Q hP hQ F (fun _ => rfl) hFθ
  have hpos : 0 ≤ C.thetaForm F F := (hOS D C).2.1.2.2.1 _ hmem
  rw [hform] at hpos
  exact hpos
end
theorem statement_holds (hOS : LinkPositivity.ReflectionPositivityAtLink)
    (hCl : TorusMetricSpace.MetricTorusFacts)
    (hDb : DoubledTransversal.DoublingProperties) (hH : LevelPartition.Claim)
    (hO : OneSideObservables.HalfSpaceObservables)
    (hS : FieldSpaceAndFaceEnergies.Statement)
    (hM : CentredMomentCumulantExpansion) (hR : LinkReflection.LinkReflectionProperties) :
    Statement := fun _ C =>
  have h := positiveOnTuples hOS hCl hDb hH hO hS hM hR C
  ⟨h, positiveOnSubtuples C h, positiveOnPolynomials hOS hCl hDb hO hS C⟩
end
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.TupleInequality
