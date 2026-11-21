import YangMills.Construction.Continuum.MultilinearFunctionalsOnAClassOfTuples
import YangMills.Construction.Continuum.TwoScalesOfClassesOfTuples
import YangMills.Construction.TorusOrFourSpace.ChoicesOfDenseSetsComponentsAndTheirFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TimeAxisSymbols
open TorusTransport TorusTransport.TupleVectors TorusTransport.TestFunctionOrders
open TorusLifts (signedCoordinateEquiv)
abbrev timeAxisVec : Fin 4 → ℝ := TorusTransport.basisVec 3
def spaceTimePoint (a : Fin 3 → ℝ) (t : ℝ) : Fin 4 → ℝ := Fin.snoc (α := fun _ => ℝ) a t
theorem spaceTimePoint_castSucc (a : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    spaceTimePoint a t i.castSucc = a i :=
  Fin.snoc_castSucc (α := fun _ => ℝ) t a i
theorem spaceTimePoint_last (a : Fin 3 → ℝ) (t : ℝ) : spaceTimePoint a t 3 = t :=
  Fin.snoc_last (α := fun _ => ℝ) t a
theorem spaceTimePoint_init (x : Fin 4 → ℝ) :
    spaceTimePoint (fun i => x i.castSucc) (x 3) = x :=
  Fin.snoc_init_self (α := fun _ => ℝ) x
def spatialBasisVec (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1
def timeAxisStabilizer : Subgroup hyperoctahedral where
  carrier := {w | w.1 timeAxisVec = timeAxisVec}
  mul_mem' := by
    intro a b ha hb
    have ha' : a.1 timeAxisVec = timeAxisVec := ha
    have hb' : b.1 timeAxisVec = timeAxisVec := hb
    show a.1 (b.1 timeAxisVec) = timeAxisVec
    rw [hb', ha']
  one_mem' := rfl
  inv_mem' := by
    intro a ha
    have ha' : a.1 timeAxisVec = timeAxisVec := ha
    show (a.1)⁻¹ timeAxisVec = timeAxisVec
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact ha'.symm
theorem mem_timeAxisStabilizer_iff (w : hyperoctahedral) :
    w ∈ timeAxisStabilizer ↔ w.1 timeAxisVec = timeAxisVec :=
  Iff.rfl
variable (D : TransportData)
abbrev symbolsOfCard (k : ℕ+) : Set (Domain.euclidean.FnFamily D k ℝ) :=
  Domain.euclidean.sepC1Families D k
theorem lipschitzOn_of_isC1On {f : RealFun (Fin 4 → ℝ)} (hf : Domain.euclidean.IsC1On D f)
    (hc : Domain.euclidean.IsCompactSubset D (entrySupp D f)) :
    Domain.euclidean.LipschitzOn D f := by
  have hf' : ContDiff ℝ 1 f := hf
  have hc' : HasCompactSupport f := hc
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc' hf' one_ne_zero
  refine (Domain.euclidean.lipschitzOn_iff D).mpr ⟨C, C.2, fun x y => ?_⟩
  have h₁ : ‖f x - f y‖ ≤ C * ‖x - y‖ := by simpa [dist_eq_norm] using hC.dist_le_mul x y
  have h₂ : ‖x - y‖ ≤ TorusMetric.euclidNormVec (x - y) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun μ => ?_
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun ν => (x - y) ν ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ μ)
  exact h₁.trans (mul_le_mul_of_nonneg_left h₂ C.2)
abbrev spaceTimeSymbols : Set FnTuple := sepTuples D Set.univ
abbrev SpaceTimeSymbol : Type := SepTuple D Set.univ
theorem mem_spaceTimeSymbols_iff (t : FnTuple) :
    t ∈ spaceTimeSymbols D ↔ t = nilTuple _ ∨
      ∃ (k : ℕ+) (f : Domain.euclidean.FnFamily D k ℝ), f ∈ symbolsOfCard D k ∧ t = ⟨k, f⟩ := by
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨k, f, hf, rfl⟩ := Set.mem_iUnion.mp h
      have hf' : f ∈ sepC1FamiliesIn D k Set.univ := hf
      rw [sepC1FamiliesIn_univ] at hf'
      exact Or.inr ⟨k, f, hf', rfl⟩
  · rintro (rfl | ⟨k, f, hf, rfl⟩)
    · exact nilTuple_mem_sepTuples D _
    · have hf' : f ∈ sepC1FamiliesIn D k Set.univ := by
        rw [sepC1FamiliesIn_univ]
        exact hf
      exact Or.inr (Set.mem_iUnion.mpr ⟨k, f, hf', rfl⟩)
def unitSymbol : SpaceTimeSymbol D := ⟨nilTuple _, nilTuple_mem_sepTuples D _⟩
variable {D}
def SpaceTimeSymbol.len (X : SpaceTimeSymbol D) : ℕ := X.1.1
def SpaceTimeSymbol.fn (X : SpaceTimeSymbol D) (i : Fin X.len) : RealFun (Fin 4 → ℝ) := X.1.2 i
def SpaceTimeSymbol.supp (X : SpaceTimeSymbol D) (i : Fin X.len) : Set (Fin 4 → ℝ) :=
  entrySupp D (X.fn i)
variable (D)
def posTimeHalf : Set (Fin 4 → ℝ) := {x | 0 < x 3}
abbrev posSymbols : Set FnTuple := sepTuples D posTimeHalf
abbrev PosSymbol : Type := SepTuple D posTimeHalf
theorem mem_posSymbols_iff (t : FnTuple) :
    t ∈ posSymbols D ↔ t ∈ spaceTimeSymbols D ∧ ∀ i, entrySupp D (t.2 i) ⊆ posTimeHalf := by
  rw [mem_sepTuples_iff, mem_sepTuples_iff]
  constructor
  · rintro ⟨hl, hk, hd, hc, ho⟩
    exact ⟨⟨hl, hk, hd, hc, fun _ => Set.subset_univ _⟩, ho⟩
  · rintro ⟨⟨hl, hk, hd, hc, -⟩, ho⟩
    exact ⟨hl, hk, hd, hc, ho⟩
abbrev scaledSymbols (d R : ℝ) (hd : 0 < d) (hR : 0 < R) : Set FnTuple :=
  admissibleSepTuples D d R hd hR
variable {D}
theorem contDiff_of_isEuclideanMotion {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) :
    ContDiff ℝ 1 s := by
  obtain ⟨S, -, v, rfl⟩ := hs
  show ContDiff ℝ 1 fun x => Matrix.mulVec S x + v
  exact (Matrix.mulVecLin S).toContinuousLinearMap.contDiff.add contDiff_const
def motionHomeomorph {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) :
    (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toEquiv := hs.toPerm
  continuous_toFun := (contDiff_of_isEuclideanMotion hs).continuous
  continuous_invFun := (contDiff_of_isEuclideanMotion hs.symm).continuous
theorem actAny_mem_spaceTimeSymbols {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s)
    {t : FnTuple} (ht : t ∈ spaceTimeSymbols D) : actAny hs t ∈ spaceTimeSymbols D := by
  obtain ⟨hl, hk, hd, hc, -⟩ := (mem_sepTuples_iff D _ t).mp ht
  have supp : ∀ f : RealFun (Fin 4 → ℝ), entrySupp D (f ∘ hs.toPerm.symm) =
      hs.toPerm.symm ⁻¹' entrySupp D f := fun f =>
    tsupport_comp_eq_preimage f (motionHomeomorph hs).symm
  refine (mem_sepTuples_iff D _ _).mpr
    ⟨fun i => ?_, fun i => ?_, fun i k hik => ?_, fun i => ?_, fun _ => Set.subset_univ _⟩
  · obtain ⟨C, hC, H⟩ := (Domain.euclidean.lipschitzOn_iff D).mp (hl i)
    refine (Domain.euclidean.lipschitzOn_iff D).mpr ⟨C, hC, fun x y => ?_⟩
    have e := hs.symm.isDistancePreserving x y
    have h := H (hs.toPerm.symm x) (hs.toPerm.symm y)
    have e' : Domain.euclidean.pointDist D (hs.toPerm.symm x) (hs.toPerm.symm y) =
        Domain.euclidean.pointDist D x y := e
    rw [e'] at h
    exact h
  · change IsCompact (entrySupp D (t.2 i ∘ hs.toPerm.symm))
    rw [supp]
    exact (motionHomeomorph hs).symm.isCompact_preimage.mpr (hk i)
  · change Disjoint (entrySupp D (t.2 i ∘ hs.toPerm.symm))
      (entrySupp D (t.2 k ∘ hs.toPerm.symm))
    rw [supp, supp]
    exact (hd hik).preimage _
  · have h₁ : ContDiff ℝ 1 (t.2 i) := hc i
    exact h₁.comp (contDiff_of_isEuclideanMotion hs.symm)
def motionSymbol {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s)
    (X : SpaceTimeSymbol D) : SpaceTimeSymbol D :=
  ⟨actAny hs X.1, actAny_mem_spaceTimeSymbols hs X.2⟩
theorem isEuclideanMotion_translationEquiv (v : Fin 4 → ℝ) :
    IsEuclideanMotion (translationEquiv v) :=
  ⟨1, one_mem _, v, funext fun x => by simp [orthoAffine]⟩
def translateSymbol (v : Fin 4 → ℝ) (X : SpaceTimeSymbol D) : SpaceTimeSymbol D :=
  motionSymbol (isEuclideanMotion_translationEquiv v) X
theorem translateSymbol_fn (v : Fin 4 → ℝ) (X : SpaceTimeSymbol D) (i : Fin X.1.1) :
    (translateSymbol v X).1.2 i = Domain.euclidean.translateFn D v (X.1.2 i) := by
  funext x
  have e : (isEuclideanMotion_translationEquiv v).toPerm.symm x = x - v :=
    (Equiv.symm_apply_eq _).mpr (by simp)
  show X.1.2 i ((isEuclideanMotion_translationEquiv v).toPerm.symm x) = X.1.2 i (x - v)
  rw [e]
theorem isEuclideanMotion_hyperoctahedral (w : hyperoctahedral) : IsEuclideanMotion w.1 := by
  obtain ⟨_, p, s, rfl⟩ := w
  have sq : ∀ μ, (((s μ : ℤˣ) : ℤ) : ℝ) * (((s μ : ℤˣ) : ℤ) : ℝ) = 1 := fun μ => by
    rcases Int.units_eq_one_or (s μ) with h | h <;> simp [h]
  refine ⟨Matrix.of fun μ ν => if ν = p μ then (((s μ : ℤˣ) : ℤ) : ℝ) else 0, ?_, 0,
    funext fun x => ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext μ ν
    by_cases h : μ = ν
    · subst h
      simp [Matrix.mul_apply, sq]
    · simp [Matrix.mul_apply, Matrix.one_apply_ne h, Ne.symm h]
  · funext μ
    simp [orthoAffine, Matrix.mulVec, dotProduct, signedCoordinateEquiv_apply]
theorem isEuclideanMotion_timeReflect : IsEuclideanMotion timeReflect := by
  obtain ⟨w, hw⟩ := exists_hyperoctahedral_eq_timeReflect
  rw [← hw]
  exact isEuclideanMotion_hyperoctahedral w
theorem timeReflect_timeReflect (x : Fin 4 → ℝ) : timeReflect (timeReflect x) = x := by
  rw [timeReflect_apply, timeReflect_apply]
  funext ν
  fin_cases ν <;> simp
def reflectSymbol (X : SpaceTimeSymbol D) : SpaceTimeSymbol D :=
  motionSymbol isEuclideanMotion_timeReflect X
theorem reflectSymbol_fn (X : SpaceTimeSymbol D) (i : Fin X.1.1) :
    (reflectSymbol X).1.2 i = X.1.2 i ∘ timeReflect := by
  funext x
  have e : isEuclideanMotion_timeReflect.toPerm.symm x = timeReflect x :=
    (Equiv.symm_apply_eq _).mpr (timeReflect_timeReflect x).symm
  show X.1.2 i (isEuclideanMotion_timeReflect.toPerm.symm x) = X.1.2 i (timeReflect x)
  rw [e]
variable (D)
abbrev SymbolSpan : Type := SepSpan D Set.univ
abbrev PosSymbolSpan : Type := SepSpan D posTimeHalf
abbrev posSymbolSpanInclusion : PosSymbolSpan D →ₗ[ℂ] SymbolSpan D :=
  spanInclusion (Set.subset_univ _)
variable {D}
def linExtendSymbolMap (φ : SpaceTimeSymbol D → SpaceTimeSymbol D) :
    SymbolSpan D →ₗ[ℂ] SymbolSpan D :=
  linExtend fun X => TupleVectors.basisVec (φ X)
theorem linExtendSymbolMap_basisVec (φ : SpaceTimeSymbol D → SpaceTimeSymbol D)
    (X : SpaceTimeSymbol D) :
    linExtendSymbolMap φ (TupleVectors.basisVec X) = TupleVectors.basisVec (φ X) :=
  linExtend_basisVec _ X
variable (D)
def IsMultilinearOnSymbolsOfCard {k : ℕ+} (Ψ : symbolsOfCard D k → ℝ) : Prop :=
  IsMultilinearOn D (symbolsOfCard D k) (fun _ hf => hf.1) Ψ
variable {D}
theorem comp_perm_mem_symbolsOfCard {k : ℕ+} {f : Domain.euclidean.FnFamily D k ℝ}
    (hf : f ∈ symbolsOfCard D k) (σ : Equiv.Perm (Fin k)) :
    (fun i => f (σ i)) ∈ symbolsOfCard D k :=
  ⟨⟨fun _ => hf.1.lipschitzOn _, fun _ => hf.1.isCompact_support _,
    fun _ _ hij => hf.1.pairwise_disjoint _ _ fun e => hij (σ.injective e)⟩, fun _ => hf.2 _⟩
def IsPermSymmetric {k : ℕ+} (Ψ : symbolsOfCard D k → ℝ) : Prop :=
  ∀ (f : symbolsOfCard D k) (σ : Equiv.Perm (Fin k)),
    Ψ f = Ψ ⟨_, comp_perm_mem_symbolsOfCard f.2 σ⟩
variable (D)
abbrev euclideanParams : PeriodicSpace.Params :=
  PeriodicSpace.Params.ofStanding D.toStandingParameters D.M D.one_le_M
abbrev euclideanStock : Set (Set (PeriodicSpace.Kind.euclidean.Pt (euclideanParams D))) :=
  PeriodicSpace.Kind.supportStock (euclideanParams D) .euclidean
structure DenseChoice where
  dense : euclideanStock D → Set (PeriodicSpace.Kind.euclidean.Pt (euclideanParams D) → ℝ)
  isCountable :
    PeriodicSpace.Kind.IsCountableDenseChoice (euclideanParams D) .euclidean dense
variable {D}
abbrev DenseChoice.family (C : DenseChoice D) :
    Set (Σ n : ℕ, Fin n → PeriodicSpace.Kind.euclidean.Pt (euclideanParams D) → ℝ) :=
  PeriodicSpace.Kind.choiceTupleFamily (euclideanParams D) .euclidean C.dense
end TimeAxisSymbols
end YangMills.Construction
end
