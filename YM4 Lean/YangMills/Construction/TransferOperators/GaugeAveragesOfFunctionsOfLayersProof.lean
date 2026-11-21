import YangMills.Construction.InfiniteLattice.ContinuousLocalFunctionsAreDenseAndTestMeasuresProof
import YangMills.Construction.InfiniteLattice.EquilibriumEquationsGaugeInvarianceAndCompactness
import YangMills.Construction.Matrices.FactsOnFunctionsAndOperatorsOfSeveralVariablesOnG
import YangMills.Construction.TransferOperators.GaugeAveragesOfFunctionsOfLayers
import YangMills.Construction.TransferOperators.TemporalGaugeOfAStack
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter
noncomputable section
namespace YangMills.Construction.TransferOperators
open YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices
namespace SliceMean
variable {μ : Fin 4} {v : Set (SliceSite μ)} {I : Set (ℤ × SliceLink μ)}
theorem continuous_diagonalGaugeAct_joint (hI : ∀ i ∈ I, i.2 ∈ linksWithin v) :
    Continuous fun p : (I → ComplexMatrix2.specialUnitary) × (v → ComplexMatrix2.specialUnitary) =>
      diagonalGaugeAct hI p.2 p.1 := by
  have hg : ∀ y : v, Continuous fun p : (I → ComplexMatrix2.specialUnitary) ×
      (v → ComplexMatrix2.specialUnitary) => p.2 y := fun y =>
    (continuous_apply y).comp continuous_snd
  have hu : ∀ i : I, Continuous fun p : (I → ComplexMatrix2.specialUnitary) ×
      (v → ComplexMatrix2.specialUnitary) => p.1 i := fun i =>
    (continuous_apply i).comp continuous_fst
  exact continuous_pi fun i => ((hg _).mul (hu i)).mul (hg _).inv
theorem continuous_integrand_joint (hI : ∀ i ∈ I, i.2 ∈ linksWithin v)
    (Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ)) :
    Continuous fun p : (I → ComplexMatrix2.specialUnitary) × (v → ComplexMatrix2.specialUnitary) =>
      Ψ (diagonalGaugeAct hI p.2 p.1) :=
  Ψ.continuous.comp (continuous_diagonalGaugeAct_joint hI)
theorem continuous_integrand_fixed (hI : ∀ i ∈ I, i.2 ∈ linksWithin v)
    (Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ)) (u : I → ComplexMatrix2.specialUnitary) :
    Continuous fun g : v → ComplexMatrix2.specialUnitary => Ψ (diagonalGaugeAct hI g u) := by
  have hg : ∀ y : v, Continuous fun g : v → ComplexMatrix2.specialUnitary => g y :=
    fun y => continuous_apply y
  have h : Continuous fun g : v → ComplexMatrix2.specialUnitary => diagonalGaugeAct hI g u :=
    continuous_pi fun i => ((hg _).mul continuous_const).mul (hg _).inv
  exact Ψ.continuous.comp h
theorem diagonalGaugeAct_diagonalGaugeAct (hI : ∀ i ∈ I, i.2 ∈ linksWithin v)
    (g g' : v → ComplexMatrix2.specialUnitary) (u : I → ComplexMatrix2.specialUnitary) :
    diagonalGaugeAct hI g (diagonalGaugeAct hI g' u) =
      diagonalGaugeAct hI (fun y => g y * g' y) u := by
  funext i
  simp only [diagonalGaugeAct, mul_inv_rev, mul_assoc]
theorem diagonalGaugeAct_levelExchange (hI : ∀ i ∈ I, i.2 ∈ linksWithin v)
    {s : Equiv.Perm I} (hs : IsLevelExchange s) (g : v → ComplexMatrix2.specialUnitary)
    (u : I → ComplexMatrix2.specialUnitary) :
    (fun i => diagonalGaugeAct hI g u (s i)) =
      diagonalGaugeAct hI g fun i => u (s i) := by
  obtain ⟨s₀, h₀⟩ := hs
  funext i
  have hb : (s i).1.2 = i.1.2 := by rw [h₀ i]
  have ht : (⟨(s i).1.2.source, (hI (s i).1 (s i).2).1⟩ : v) = ⟨i.1.2.source, (hI i.1 i.2).1⟩ :=
    Subtype.ext (congrArg SliceLink.source hb)
  have hh : (⟨(s i).1.2.target, (hI (s i).1 (s i).2).2⟩ : v) = ⟨i.1.2.target, (hI i.1 i.2).2⟩ :=
    Subtype.ext (congrArg SliceLink.target hb)
  simp only [diagonalGaugeAct, ht, hh]
section Mean
variable [Finite v] [Finite I] (hI : ∀ i ∈ I, i.2 ∈ linksWithin v)
theorem integrable_integrand (Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ))
    (u : I → ComplexMatrix2.specialUnitary) :
    Integrable (fun g : v → ComplexMatrix2.specialUnitary => Ψ (diagonalGaugeAct hI g u))
      (ComplexMatrix2.haarPi v) :=
  (continuous_integrand_fixed hI Ψ u).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
theorem continuous_sliceGaugeMean (Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ)) :
    Continuous (sliceGaugeMean hI Ψ) := by
  have h := continuous_parametric_integral_of_continuous (μ := ComplexMatrix2.haarPi v)
    (f := fun (u : I → ComplexMatrix2.specialUnitary) (g : v → ComplexMatrix2.specialUnitary) =>
      Ψ (diagonalGaugeAct hI g u))
    (s := Set.univ) (continuous_integrand_joint hI Ψ) isCompact_univ
  exact show Continuous fun u : I → ComplexMatrix2.specialUnitary =>
      ∫ g, Ψ (diagonalGaugeAct hI g u) ∂ComplexMatrix2.haarPi v from by
    simpa only [Measure.restrict_univ] using h
theorem sliceGaugeMean_add (Ψ Φ : C(I → ComplexMatrix2.specialUnitary, ℂ)) :
    sliceGaugeMean hI (Ψ + Φ) = sliceGaugeMean hI Ψ + sliceGaugeMean hI Φ := by
  funext u
  simp only [sliceGaugeMean, ContinuousMap.add_apply, Pi.add_apply]
  exact integral_add (integrable_integrand hI Ψ u) (integrable_integrand hI Φ u)
theorem sliceGaugeMean_smul (c : ℂ) (Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ)) :
    sliceGaugeMean hI (c • Ψ) = c • sliceGaugeMean hI Ψ := by
  funext u
  simp only [sliceGaugeMean, ContinuousMap.smul_apply, Pi.smul_apply]
  exact integral_smul c _
theorem norm_sliceGaugeMean_le (Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ))
    (u : I → ComplexMatrix2.specialUnitary) :
    ‖sliceGaugeMean hI Ψ u‖ ≤ ‖Ψ‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := ComplexMatrix2.haarPi v) (C := ‖Ψ‖)
    (f := fun g : v → ComplexMatrix2.specialUnitary => Ψ (diagonalGaugeAct hI g u))
    (Eventually.of_forall fun g => Ψ.norm_coe_le_norm _)
  simpa [sliceGaugeMean] using h
theorem sliceGaugeMean_eq_of_invariant (Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ))
    (h : IsDiagonalGaugeInvariant hI (Ψ : (I → ComplexMatrix2.specialUnitary) → ℂ)) :
    sliceGaugeMean hI Ψ = Ψ := by
  funext u
  simp only [sliceGaugeMean]
  rw [integral_congr_ae (Eventually.of_forall fun g => h g u)]
  simp
theorem sliceGaugeMean_real (Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ))
    (h : IsRealValuedSliceFunction (Ψ : (I → ComplexMatrix2.specialUnitary) → ℂ)) :
    IsRealValuedSliceFunction (sliceGaugeMean hI Ψ) := by
  intro u
  have h₁ := Complex.imCLM.integral_comp_comm (integrable_integrand hI Ψ u)
  have h₂ : (fun g : v → ComplexMatrix2.specialUnitary =>
      Complex.imCLM (Ψ (diagonalGaugeAct hI g u))) = fun _ => 0 := funext fun g => h _
  rw [h₂] at h₁
  simpa [sliceGaugeMean] using h₁.symm
theorem sliceGaugeMean_invariant
    (hH : ∀ g g' : v → ComplexMatrix2.specialUnitary, MeasurePreserving
      (fun (u : v → ComplexMatrix2.specialUnitary) (b : v) => g b * u b * g' b)
      (ComplexMatrix2.haarPi v) (ComplexMatrix2.haarPi v))
    (Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ)) :
    IsDiagonalGaugeInvariant hI (sliceGaugeMean hI Ψ) := by
  intro g' u
  have hm := hH 1 g'
  have hc := continuous_integrand_fixed hI Ψ u
  simp only [sliceGaugeMean, diagonalGaugeAct_diagonalGaugeAct]
  conv_rhs => rw [← hm.map_eq]
  rw [integral_map hm.measurable.aemeasurable hc.aestronglyMeasurable]
  simp
end Mean
def evalRingHom {K : Type} [TopologicalSpace K] (g : K) : C(K, ℂ) →+* ℂ where
  toFun a := a g
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
def sourceCoeff (hI : ∀ i ∈ I, i.2 ∈ linksWithin v) (i : I) (a c : Fin 2) :
    C(v → ComplexMatrix2.specialUnitary, ℂ) :=
  ⟨fun g => (g ⟨i.1.2.source, (hI i.1 i.2).1⟩ : ComplexMatrix2) a c,
    Continuous.matrix_elem
      (A := fun g : v → ComplexMatrix2.specialUnitary =>
        (g ⟨i.1.2.source, (hI i.1 i.2).1⟩ : ComplexMatrix2))
      (continuous_subtype_val.comp (continuous_apply _)) a c⟩
def targetInvCoeff (hI : ∀ i ∈ I, i.2 ∈ linksWithin v) (i : I) (d b : Fin 2) :
    C(v → ComplexMatrix2.specialUnitary, ℂ) :=
  ⟨fun g => (((g ⟨i.1.2.target, (hI i.1 i.2).2⟩)⁻¹ : ComplexMatrix2.specialUnitary) :
      ComplexMatrix2) d b,
    Continuous.matrix_elem
      (A := fun g : v → ComplexMatrix2.specialUnitary =>
        (((g ⟨i.1.2.target, (hI i.1 i.2).2⟩)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2))
      (continuous_subtype_val.comp (continuous_apply _).inv) d b⟩
def actedEntry (hI : ∀ i ∈ I, i.2 ∈ linksWithin v) :
    EntryVar I → MvPolynomial (EntryVar I) C(v → ComplexMatrix2.specialUnitary, ℂ)
  | .inl (i, a, b) => ∑ c : Fin 2, ∑ d : Fin 2,
      MvPolynomial.C (sourceCoeff hI i a c * targetInvCoeff hI i d b) *
        MvPolynomial.X (.inl (i, c, d))
  | .inr (i, a, b) => ∑ c : Fin 2, ∑ d : Fin 2,
      MvPolynomial.C (star (sourceCoeff hI i a c * targetInvCoeff hI i d b)) *
        MvPolynomial.X (.inr (i, c, d))
theorem entryEval_diagonalGaugeAct (hI : ∀ i ∈ I, i.2 ∈ linksWithin v)
    (g : v → ComplexMatrix2.specialUnitary) (u : I → ComplexMatrix2.specialUnitary)
    (x : EntryVar I) :
    entryEval (diagonalGaugeAct hI g u) x =
      MvPolynomial.eval₂ (evalRingHom g) (entryEval u) (actedEntry hI x) := by
  have hentry : ∀ (i : I) (a b : Fin 2), (diagonalGaugeAct hI g u i : ComplexMatrix2) a b =
      ∑ c : Fin 2, ∑ d : Fin 2, (sourceCoeff hI i a c * targetInvCoeff hI i d b) g *
        (u i : ComplexMatrix2) c d := by
    intro i a b
    simp only [diagonalGaugeAct, sourceCoeff, targetInvCoeff, ContinuousMap.mul_apply,
      ContinuousMap.coe_mk, Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rcases x with ⟨i, a, b⟩ | ⟨i, a, b⟩
  · simp only [actedEntry, entryEval, hentry, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, MvPolynomial.eval₂_sum]
    rfl
  · simp only [actedEntry, entryEval, hentry, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, MvPolynomial.eval₂_sum, star_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [star_mul']
    rfl
def actedPolynomial (hI : ∀ i ∈ I, i.2 ∈ linksWithin v)
    (p : MvPolynomial (EntryVar I) ℂ) :
    MvPolynomial (EntryVar I) C(v → ComplexMatrix2.specialUnitary, ℂ) :=
  MvPolynomial.eval₂ (MvPolynomial.C.comp (algebraMap ℂ C(v → ComplexMatrix2.specialUnitary, ℂ)))
    (actedEntry hI) p
theorem eval_diagonalGaugeAct (hI : ∀ i ∈ I, i.2 ∈ linksWithin v)
    (g : v → ComplexMatrix2.specialUnitary) (u : I → ComplexMatrix2.specialUnitary)
    (p : MvPolynomial (EntryVar I) ℂ) :
    MvPolynomial.eval (entryEval (diagonalGaugeAct hI g u)) p =
      MvPolynomial.eval₂ (evalRingHom g) (entryEval u) (actedPolynomial hI p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [actedPolynomial, MvPolynomial.eval_C, MvPolynomial.eval₂_C, RingHom.comp_apply]
    rfl
  | add p q hp hq =>
    simp only [actedPolynomial, map_add, MvPolynomial.eval₂_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p x hp =>
    simp only [actedPolynomial, map_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval_X,
      MvPolynomial.eval₂_X] at hp ⊢
    rw [hp, entryEval_diagonalGaugeAct hI g u x]
theorem sliceGaugeMean_polynomial [Finite v] [Finite I] (hI : ∀ i ∈ I, i.2 ∈ linksWithin v)
    (Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ))
    (h : IsEntryPolynomial (Ψ : (I → ComplexMatrix2.specialUnitary) → ℂ)) :
    IsEntryPolynomial (sliceGaugeMean hI Ψ) := by
  obtain ⟨p, hp⟩ := h
  set P := actedPolynomial hI p with hP
  have hcoef : ∀ (m : EntryVar I →₀ ℕ),
      Integrable (fun g : v → ComplexMatrix2.specialUnitary => (P.coeff m) g)
        (ComplexMatrix2.haarPi v) := fun m =>
    (P.coeff m).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨∑ m ∈ P.support,
    MvPolynomial.monomial m (∫ g, (P.coeff m) g ∂ComplexMatrix2.haarPi v), fun u => ?_⟩
  have hexp : ∀ g : v → ComplexMatrix2.specialUnitary, Ψ (diagonalGaugeAct hI g u) =
      ∑ m ∈ P.support, (P.coeff m) g * ∏ x ∈ m.support, entryEval u x ^ m x := by
    intro g
    rw [hp, eval_diagonalGaugeAct, ← hP, MvPolynomial.eval₂_eq]
    rfl
  simp only [sliceGaugeMean, hexp]
  rw [integral_finsetSum _ fun m _ => (hcoef m).mul_const _, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_mul_const, MvPolynomial.eval_monomial]
  rfl
def exchangedEntry (s : Equiv.Perm I) : EntryVar I → EntryVar I
  | .inl (b, i, j) => .inl (s b, i, j)
  | .inr (b, i, j) => .inr (s b, i, j)
theorem entryEval_levelExchange (s : Equiv.Perm I) (u : I → ComplexMatrix2.specialUnitary) :
    entryEval (fun b => u (s b)) = entryEval u ∘ exchangedEntry s := by
  funext x
  rcases x with ⟨b, i, j⟩ | ⟨b, i, j⟩ <;> rfl
theorem polynomial_levelExchange (s : Equiv.Perm I)
    {F : (I → ComplexMatrix2.specialUnitary) → ℂ} (h : IsEntryPolynomial F) :
    IsEntryPolynomial fun u => F fun b => u (s b) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨MvPolynomial.rename (exchangedEntry s) p, fun u => ?_⟩
  change F (fun b => u (s b)) = _
  rw [hp, MvPolynomial.eval_rename, entryEval_levelExchange]
theorem norm_levelExchanged (s : Equiv.Perm I) (Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ))
    [CompactSpace (I → ComplexMatrix2.specialUnitary)] :
    ‖levelExchanged s Ψ‖ = ‖Ψ‖ := by
  refine le_antisymm ?_ ?_
  · exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun u => Ψ.norm_coe_le_norm _
  · refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun u => ?_
    have h := (levelExchanged s Ψ).norm_coe_le_norm fun b => u (s.symm b)
    rw [levelExchanged_apply] at h
    simpa using h
theorem continuous_linkValue (c : InfiniteLattice.Link 1) :
    Continuous fun U : InfiniteLattice.GaugeField 1 => U c := by apply _root_.YangMills.Construction.InfiniteLattice.ContinuousLocalDensity.continuous_eval_link <;> assumption
theorem continuous_transportedLinkVariable (S : Stack) (j : ℤ) (b : SliceLink μ) :
    Continuous fun U : InfiniteLattice.GaugeField 1 => S.transportedLinkVariable μ U j b := by
  have ht : ∀ y : SliceSite μ, Continuous fun U : InfiniteLattice.GaugeField 1 =>
      S.parallelTransport μ U j y :=
    fun y => continuous_list_prod _ fun k _ => continuous_linkValue _
  exact ((ht _).mul (continuous_linkValue _)).mul (ht _).inv
def lowerGauge [Finite v] (S : Stack) (g : v → ComplexMatrix2.specialUnitary) :
    InfiniteLattice.GaugeTransform 1 where
  toFun := Function.extend (fun y : v => pointAtLevel μ S.lower y.1) g 1
  finite_ne_one := (Set.finite_range fun y : v => pointAtLevel μ S.lower y.1).subset fun x hx => by
    by_contra hr
    exact hx (Function.extend_apply' _ _ _ (by simpa using hr))
theorem lowerGauge_toFun [Finite v] (S : Stack) (g : v → ComplexMatrix2.specialUnitary) (y : v) :
    (lowerGauge S g).toFun (pointAtLevel μ S.lower y.1) = g y := by
  have hinj : Function.Injective fun y : v => pointAtLevel μ S.lower y.1 := fun a b h =>
    Subtype.ext (Subtype.ext (add_left_cancel (a := S.lower • InfiniteLattice.axisStep 1 μ) h))
  exact hinj.extend_apply g 1 y
theorem continuous_transportedFamily (S : Stack) :
    Continuous (S.transportedFamily I) :=
  continuous_pi fun i => continuous_transportedLinkVariable S i.1.1 i.1.2
theorem transportedFamily_lowerGauge [Finite v] (hI : ∀ i ∈ I, i.2 ∈ linksWithin v) (S : Stack)
    (hS : ∀ i ∈ I, S.lower ≤ i.1 ∧ i.1 ≤ S.upper)
    (hTr : TemporalGauge.GaugeActionOnTransported μ S)
    (g : v → ComplexMatrix2.specialUnitary) (U : InfiniteLattice.GaugeField 1) :
    S.transportedFamily I ((lowerGauge S g).act U) =
      diagonalGaugeAct hI g (S.transportedFamily I U) := by
  funext i
  have h := (hTr (lowerGauge S g) U i.1.1 (hS i.1 i.2).1 (hS i.1 i.2).2).2 i.1.2
  have h₁ := lowerGauge_toFun S g ⟨i.1.2.source, (hI i.1 i.2).1⟩
  have h₂ := lowerGauge_toFun S g ⟨i.1.2.target, (hI i.1 i.2).2⟩
  simp only [Stack.transportedFamily, diagonalGaugeAct]
  rw [h, h₁, h₂]
theorem integrable_uncurry_integrand [Finite v] [Finite I] (hI : ∀ i ∈ I, i.2 ∈ linksWithin v)
    (Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ)) {X : Type} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {T : X → I → ComplexMatrix2.specialUnitary} (hT : Measurable T) :
    Integrable (Function.uncurry fun (U : X) (g : v → ComplexMatrix2.specialUnitary) =>
      Ψ (diagonalGaugeAct hI g (T U))) (ν.prod (ComplexMatrix2.haarPi v)) := by
  have hm : Measurable fun p : X × (v → ComplexMatrix2.specialUnitary) => (T p.1, p.2) :=
    (hT.comp measurable_fst).prodMk measurable_snd
  have hc := (continuous_integrand_joint hI Ψ).measurable
  have hjoint := hc.comp hm
  have hb : ∀ p : X × (v → ComplexMatrix2.specialUnitary),
      ‖(Function.uncurry fun (U : X) (g : v → ComplexMatrix2.specialUnitary) =>
        Ψ (diagonalGaugeAct hI g (T U))) p‖ ≤ ‖Ψ‖ := fun p => Ψ.norm_coe_le_norm _
  exact Integrable.of_bound hjoint.aestronglyMeasurable ‖Ψ‖ (Eventually.of_forall hb)
theorem integral_sliceGaugeMean_of_invariant [Finite v] [Finite I]
    (hI : ∀ i ∈ I, i.2 ∈ linksWithin v) (Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ)) {X : Type}
    [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    {T : X → I → ComplexMatrix2.specialUnitary} (hT : Measurable T)
    (key : ∀ g : v → ComplexMatrix2.specialUnitary,
      ∫ U, Ψ (diagonalGaugeAct hI g (T U)) ∂ν = ∫ U, Ψ (T U) ∂ν) :
    ∫ U, sliceGaugeMean hI Ψ (T U) ∂ν = ∫ U, Ψ (T U) ∂ν := by
  simp only [sliceGaugeMean]
  rw [integral_integral_swap (integrable_uncurry_integrand hI Ψ ν hT)]
  simp only [key]
  simp
theorem sliceGaugeMean_preservesExpectation [Finite v] [Finite I]
    (hI : ∀ i ∈ I, i.2 ∈ linksWithin v) (β : ℝ)
    (hInv : ∀ ν ∈ InfiniteLattice.gibbsClass (a := 1) one_pos β,
      ∀ F : InfiniteLattice.GaugeField 1 → ℂ, InfiniteLattice.IsBoundedObservable F →
      ∀ h : InfiniteLattice.GaugeTransform 1, ∫ U, h.pullback F U ∂ν = ∫ U, F U ∂ν)
    (hTr : ∀ S : Stack, TemporalGauge.GaugeActionOnTransported μ S) :
    SliceGaugeMeanPreservesExpectation hI β := by
  intro S hS ν hν Ψ
  have : IsProbabilityMeasure ν := hν.1
  have hTm : Measurable (S.transportedFamily I) :=
    (continuous_transportedFamily S).measurable
  have hF : InfiniteLattice.IsBoundedObservable fun U => Ψ (S.transportedFamily I U) :=
    ⟨Ψ.continuous.measurable.comp hTm, ‖Ψ‖, fun U => Ψ.norm_coe_le_norm _⟩
  refine integral_sliceGaugeMean_of_invariant hI Ψ ν hTm fun g => ?_
  rw [← hInv ν hν _ hF (lowerGauge S g)]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp only [InfiniteLattice.GaugeTransform.pullback, transportedFamily_lowerGauge hI S hS (hTr S)]
end SliceMean
theorem sliceGaugeMeanProperties_holds
    (hEq : InfiniteLattice.GibbsClassStructure)
    (hFacts : SpinHarmonics.SeveralVariables.SeveralVariablesFacts)
    (hStates : GibbsHaarKernels.Statement)
    (hTemp : TemporalGauge.MainStatement) :
    SliceGaugeMeanProperties := by
  intro μ β hβ v I _ _ hv hIne hI
  have : Nonempty v := hv.to_subtype
  have : Nonempty I := hIne.to_subtype
  have hH := (hStates.2.1 v).1
  have hInvariant := SliceMean.sliceGaugeMean_invariant hI hH
  have hReal : ∀ Ψ : C(I → ComplexMatrix2.specialUnitary, ℂ),
      IsRealEntryPolynomial (Ψ : (I → ComplexMatrix2.specialUnitary) → ℂ) →
      IsRealEntryPolynomial (sliceGaugeMean hI Ψ) := fun Ψ h =>
    ⟨SliceMean.sliceGaugeMean_polynomial hI Ψ h.1,
      SliceMean.sliceGaugeMean_real hI Ψ h.2⟩
  refine ⟨⟨fun Ψ => ⟨SliceMean.continuous_sliceGaugeMean hI Ψ, hInvariant Ψ⟩,
      SliceMean.sliceGaugeMean_add hI,
      SliceMean.sliceGaugeMean_smul hI,
      SliceMean.norm_sliceGaugeMean_le hI,
      SliceMean.sliceGaugeMean_real hI,
      SliceMean.sliceGaugeMean_eq_of_invariant hI⟩,
    fun Ψ => ⟨SliceMean.sliceGaugeMean_polynomial hI Ψ, hReal Ψ⟩,
    ?_, ?_,
    SliceMean.sliceGaugeMean_preservesExpectation hI β
      (hEq 1 one_pos β hβ).2.1.1 fun S => (hTemp μ S).2.2⟩
  · intro Ψ hr hinv
    have hdense := (hFacts I (fun _ => ⟨0⟩) ⟨0⟩).2.2.2.2.2.2.2.2.1
    have happrox : ∀ n : ℕ, ∃ F : (I → ComplexMatrix2.specialUnitary) → ℂ,
        IsRealEntryPolynomial F ∧ ∀ u, ‖F u - Ψ u‖ < 1 / ((n : ℝ) + 1) := by
      intro n
      let f : C(I → ComplexMatrix2.specialUnitary, ℝ) :=
        ⟨fun u => (Ψ u).re, Complex.continuous_re.comp Ψ.continuous⟩
      obtain ⟨F, hF, hb⟩ := hdense.2.2.2.2 f (1 / ((n : ℝ) + 1)) (by positivity)
      refine ⟨F, hF, fun u => ?_⟩
      have hu : ((f u : ℝ) : ℂ) = Ψ u := Complex.ext rfl (by simpa using (hr u).symm)
      rw [← hu]
      exact hb u
    choose F hF hb using happrox
    have hFc : ∀ n, Continuous (F n) := fun n => (hF n).1.continuous
    let Fc : ℕ → C(I → ComplexMatrix2.specialUnitary, ℂ) := fun n => ⟨F n, hFc n⟩
    refine ⟨fun n => sliceGaugeMean hI (Fc n), fun n => ⟨hReal _ (hF n), hInvariant _⟩, ?_⟩
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with n hn u
    have hav : sliceGaugeMean hI (Fc n) u - Ψ u =
        sliceGaugeMean hI (Fc n + (-1 : ℂ) • Ψ) u := by
      rw [SliceMean.sliceGaugeMean_add,
        SliceMean.sliceGaugeMean_smul,
        SliceMean.sliceGaugeMean_eq_of_invariant hI Ψ hinv]
      simp [sub_eq_add_neg]
    have hsup : ‖Fc n + (-1 : ℂ) • Ψ‖ ≤ 1 / ((n : ℝ) + 1) := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun w => ?_
      have := (hb n w).le
      simpa [Fc, sub_eq_add_neg] using this
    have hmono : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [dist_comm, dist_eq_norm, hav]
    exact ((SliceMean.norm_sliceGaugeMean_le hI _ u).trans hsup).trans_lt
      (hmono.trans_lt hN)
  · intro s hs Ψ
    refine ⟨?_, SliceMean.norm_levelExchanged s Ψ, fun h g u => ?_,
      fun h => ⟨SliceMean.polynomial_levelExchange s h.1, fun u => h.2 _⟩⟩
    · funext u
      simp only [sliceGaugeMean, permuteArgs, levelExchanged_apply,
        SliceMean.diagonalGaugeAct_levelExchange hI hs]
    · simp only [levelExchanged_apply, SliceMean.diagonalGaugeAct_levelExchange hI hs]
      exact h g _
end YangMills.Construction.TransferOperators
end
