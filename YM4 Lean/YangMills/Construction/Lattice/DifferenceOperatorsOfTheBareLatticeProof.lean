import YangMills.Construction.Lattice.CurlOfTheDirichletDifferenceProof
import YangMills.Construction.Lattice.DirichletFormLaplacianWithItsBoundaryTermProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.DirichletOperators.BareLatticeOperators
variable {L m K : ℕ}
theorem finite_site (hL : 0 < L) (m : ℕ) (j : ℤ) : Finite (Site L m j) := by apply _root_.YangMills.Construction.SeparatedSequences.BaseParameters.site_finite <;> assumption
theorem unitStep_apply_apply (j : ℤ) (μ ν : Fin 4) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) ν =
      Pi.single (M := fun _ => AddCircle (torusSide L m)) μ ((meshSize L j : ℝ) : AddCircle (torusSide L m)) ν :=
  rfl
theorem unitStep_ne_zero (hL : 2 ≤ L) {j : ℤ} (hj : 0 ≤ j) (μ : Fin 4) : unitStep L m j μ ≠ 0 := by apply _root_.YangMills.Construction.DirichletCurl.unitStep_ne_zero <;> assumption
theorem unitStep_injective (hL : 2 ≤ L) {j : ℤ} (hj : 0 ≤ j) :
    Function.Injective (unitStep L m j) := by apply _root_.YangMills.Construction.PeriodicLattice.DirichletLaplacianSplitsOffBoundary.unitStep_injective <;> assumption
theorem exists_eq_sum_zsmul_unitStep {j : ℤ} (z : Site L m j) :
    ∃ n : Fin 4 → ℤ, z = ∑ μ, n μ • unitStep L m j μ := by
  obtain ⟨x, n, hn⟩ := z
  refine ⟨n, Subtype.ext (funext fun ν => ?_)⟩
  have h : ((∑ μ, n μ • unitStep L m j μ : Site L m j) : FourTorus L m) ν =
      n ν • ((meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
    simp [Finset.sum_apply, unitStep_apply_apply, Pi.single_apply]
  rw [h]
  change x ν = _
  rw [hn ν, ← zsmul_eq_mul]
  rfl
section Pairing
variable {ι κ α : Type} {t : ℕ}
theorem latticeInner_eq_sum [Fintype ι] (f g : ι → ℝ) :
    latticeInner L t f g = finestMeshInLevelUnits L t ^ 4 * ∑ i, f i * g i := by
  rw [latticeInner, finsum_eq_sum_of_fintype]
theorem latticeInner_comm [Fintype ι] (f g : ι → ℝ) : latticeInner L t f g = latticeInner L t g f := by
  simp only [latticeInner_eq_sum, mul_comm (f _)]
theorem latticeInner_add_right [Fintype ι] (f g h : ι → ℝ) :
    latticeInner L t f (g + h) = latticeInner L t f g + latticeInner L t f h := by
  simp only [latticeInner_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem latticeInner_sub_right [Fintype ι] (f g h : ι → ℝ) :
    latticeInner L t f (g - h) = latticeInner L t f g - latticeInner L t f h := by
  simp only [latticeInner_eq_sum, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
theorem latticeInner_sub_left [Fintype ι] (f g h : ι → ℝ) :
    latticeInner L t (f - g) h = latticeInner L t f h - latticeInner L t g h := by
  simp only [latticeInner_eq_sum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]
theorem latticeInner_sum_left [Fintype ι] (s : Finset α) (F : α → ι → ℝ) (g : ι → ℝ) :
    latticeInner L t (∑ a ∈ s, F a) g = ∑ a ∈ s, latticeInner L t (F a) g := by
  simp only [latticeInner_eq_sum, Finset.sum_apply, Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
theorem latticeInner_sum_right [Fintype ι] (s : Finset α) (F : α → ι → ℝ) (g : ι → ℝ) :
    latticeInner L t g (∑ a ∈ s, F a) = ∑ a ∈ s, latticeInner L t g (F a) := by
  rw [latticeInner_comm, latticeInner_sum_left]
  exact Finset.sum_congr rfl fun a _ => latticeInner_comm _ _
theorem normSq_sub [Fintype ι] (f g : ι → ℝ) :
    normSq L t (f - g) =
      normSq L t f + normSq L t g - 2 * latticeInner L t f g := by
  simp only [normSq, latticeInner_sub_left, latticeInner_sub_right, latticeInner_comm g f]
  ring
theorem ext_latticeInner [Fintype ι] (hξ : finestMeshInLevelUnits L t ≠ 0) {u v : ι → ℝ}
    (h : ∀ f : ι → ℝ, latticeInner L t u f = latticeInner L t v f) : u = v := by apply _root_.YangMills.Construction.DirichletLaplacian.ext_of_latticeInner <;> assumption
theorem latticeInner_formalAdjoint [Fintype ι] [Fintype κ] (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (f : ι → ℝ) (g : κ → ℝ) : latticeInner L t (formalAdjoint L t T g) f = latticeInner L t g (T f) := by apply _root_.YangMills.Construction.DirichletLaplacian.latticeInner_formalAdjoint <;> assumption
theorem indicatorMul_apply (X : Set ι) (f : ι → ℝ) (i : ι) :
    indicatorMul X f i = X.indicator f i := rfl
theorem latticeInner_indicatorMul [Fintype ι] (X : Set ι) (f g : ι → ℝ) :
    latticeInner L t (indicatorMul X g) f = latticeInner L t g (indicatorMul X f) := by
  simp only [latticeInner_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [indicatorMul_apply]
  by_cases h : i ∈ X <;> simp [h]
theorem indicatorMul_of_mem_range {X : Set ι} {f : ι → ℝ}
    (h : f ∈ LinearMap.range (indicatorMul X)) : indicatorMul X f = f := by apply _root_.YangMills.Construction.SeparatedClasses.NestedOneForms.indicatorMul_of_mem <;> assumption
theorem apply_eq_zero_of_mem_range_indicatorMul {X : Set ι} {f : ι → ℝ}
    (h : f ∈ LinearMap.range (indicatorMul X)) {i : ι} (hi : i ∉ X) : f i = 0 := by apply _root_.YangMills.Construction.DirichletLaplacian.apply_eq_zero_of_mem_range_indicatorMul <;> assumption
theorem indicatorMul_add_sdiff {X Y : Set ι} (h : X ⊆ Y) :
    indicatorMul X + indicatorMul (Y \ X) = indicatorMul Y := by
  refine LinearMap.ext fun f => funext fun i => ?_
  change X.indicator f i + (Y \ X).indicator f i = Y.indicator f i
  by_cases hX : i ∈ X
  · simp [hX, h hX]
  · by_cases hY : i ∈ Y <;> simp [hX, hY]
theorem indicatorMul_empty : indicatorMul (∅ : Set ι) = 0 := by
  refine LinearMap.ext fun f => funext fun i => ?_
  change (∅ : Set ι).indicator f i = 0
  simp
theorem finsum_mul_self_eq_finsum_mem_sq {X : Set ι} (g : ι → ℝ) (h : ∀ i, i ∉ X → g i = 0) :
    ∑ᶠ i, g i * g i = ∑ᶠ i ∈ X, |g i| ^ 2 := by
  rw [finsum_mem_def]
  refine finsum_congr fun i => ?_
  by_cases hi : i ∈ X
  · rw [Set.indicator_of_mem hi, sq_abs, pow_two]
  · rw [Set.indicator_of_notMem hi, h i hi, mul_zero]
end Pairing
section Sums
variable {t : ℕ}
theorem bondFrom_bijective (hs : Function.Injective (unitStep L m (levelDepth K 0))) :
    Function.Bijective (fun q : BareSite L m K × Fin 4 => bondFrom q.1 q.2) := by apply _root_.YangMills.Construction.DirichletLaplacian.bondFrom_bijective <;> assumption
def barePlaquetteEquiv (L m K : ℕ) :
    BarePlaquette L m K ≃ BareSite L m K × {q : Fin 4 × Fin 4 // q.1 < q.2} where
  toFun p := (p.origin, ⟨(p.firstAxis, p.secondAxis), p.firstAxis_lt_secondAxis⟩)
  invFun q := ⟨q.1, q.2.1.1, q.2.1.2, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem sum_ordered_pairs (G : Fin 4 → Fin 4 → ℝ) (hs : ∀ μ ν, G μ ν = G ν μ) (hd : ∀ μ, G μ μ = 0) :
    ∑ q : {q : Fin 4 × Fin 4 // q.1 < q.2}, G q.1.1 q.1.2 = (1 / 2 : ℝ) * ∑ μ, ∑ ν, G μ ν := by
  have h : ∑ q : {q : Fin 4 × Fin 4 // q.1 < q.2}, G q.1.1 q.1.2 =
      ∑ q ∈ Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2), G q.1 q.2 :=
    (Finset.sum_subtype _ (by simp) (fun q : Fin 4 × Fin 4 => G q.1 q.2)).symm
  rw [h, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four]
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h30 := hs 3 0
  have h21 := hs 2 1
  have h31 := hs 3 1
  have h32 := hs 3 2
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  simp
  linarith
variable [Fintype (BareSite L m K)] [Fintype (BareBond L m K)] [Fintype (BarePlaquette L m K)]
theorem sum_barePlaquette (F : BarePlaquette L m K → ℝ) :
    ∑ p, F p = ∑ x : BareSite L m K, ∑ q : {q : Fin 4 × Fin 4 // q.1 < q.2},
      F ⟨x, q.1.1, q.1.2, q.2⟩ := by
  rw [← (barePlaquetteEquiv L m K).symm.sum_comp, Fintype.sum_prod_type]
  rfl
theorem latticeInner_oneForms (hs : Function.Injective (unitStep L m (levelDepth K 0))) (A B : OneForms L m K) :
    latticeInner L t A B = ∑ μ, latticeInner L t (axisComponent A μ) (axisComponent B μ) := by apply _root_.YangMills.Construction.DirichletLaplacian.latticeInner_oneForms <;> assumption
theorem sum_comp_add (s : BareSite L m K) (F : BareSite L m K → ℝ) :
    ∑ x, F (x + s) = ∑ x, F x := Equiv.sum_comp (Equiv.addRight s) F
theorem latticeInner_forwardDifference (μ : Fin 4) (f g : ZeroForms L m K) :
    latticeInner L t g (forwardDifference t μ f) = latticeInner L t (forwardDifferenceAdjoint t μ g) f := by
  set s := unitStep L m (levelDepth K 0) μ
  have hshift : ∑ x, g x * f (x + s) = ∑ x, g (x - s) * f x := by
    rw [← sum_comp_add s (fun x => g (x - s) * f x)]
    simp only [add_sub_cancel_right]
  simp only [latticeInner_eq_sum]
  congr 1
  simp only [forwardDifference, forwardDifferenceAdjoint]
  calc ∑ x, g x * ((finestMeshInLevelUnits L t)⁻¹ * (f (x + s) - f x))
      = (finestMeshInLevelUnits L t)⁻¹ * (∑ x, g x * f (x + s) - ∑ x, g x * f x) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ = (finestMeshInLevelUnits L t)⁻¹ * (∑ x, g (x - s) * f x - ∑ x, g x * f x) := by rw [hshift]
    _ = ∑ x, (finestMeshInLevelUnits L t)⁻¹ * (g (x - s) - g x) * f x := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
theorem forwardDifference_comm (μ ν : Fin 4) (f : ZeroForms L m K) :
    forwardDifference t μ (forwardDifference t ν f) = forwardDifference t ν (forwardDifference t μ f) := by
  funext x
  simp only [forwardDifference]
  rw [add_right_comm x (unitStep L m (levelDepth K 0) μ) (unitStep L m (levelDepth K 0) ν)]
  ring
theorem forwardDifference_adjoint_comm (μ ν : Fin 4) (f : ZeroForms L m K) :
    forwardDifference t μ (forwardDifferenceAdjoint t ν f) = forwardDifferenceAdjoint t ν (forwardDifference t μ f) := by
  funext x
  simp only [forwardDifference, forwardDifferenceAdjoint]
  rw [show x + unitStep L m (levelDepth K 0) μ - unitStep L m (levelDepth K 0) ν =
    x - unitStep L m (levelDepth K 0) ν + unitStep L m (levelDepth K 0) μ by abel]
  ring
theorem forwardDifferenceAdjoint_comm (μ ν : Fin 4) (f : ZeroForms L m K) :
    forwardDifferenceAdjoint t μ (forwardDifferenceAdjoint t ν f) = forwardDifferenceAdjoint t ν (forwardDifferenceAdjoint t μ f) := by
  funext x
  simp only [forwardDifferenceAdjoint]
  rw [show x - unitStep L m (levelDepth K 0) μ - unitStep L m (levelDepth K 0) ν =
    x - unitStep L m (levelDepth K 0) ν - unitStep L m (levelDepth K 0) μ by abel]
  ring
theorem differenceAdjointsCommute : DifferenceAdjointsCommute L m K t :=
  ⟨fun μ f g => latticeInner_forwardDifference μ f g, fun μ ν f => forwardDifference_comm μ ν f,
    fun μ ν f => forwardDifference_adjoint_comm μ ν f, fun μ ν f => forwardDifferenceAdjoint_comm μ ν f⟩
theorem latticeInner_gradAdjoint (A : OneForms L m K) (f : ZeroForms L m K) :
    latticeInner L t (gradAdjoint L m K t A) f = latticeInner L t A (grad t f) :=
  latticeInner_formalAdjoint _ _ _
theorem latticeInner_curlAdjoint (F : TwoForms L m K) (A : OneForms L m K) :
    latticeInner L t (curlAdjoint L m K t F) A = latticeInner L t F (curl t A) :=
  latticeInner_formalAdjoint _ _ _
theorem gradAdjoint_eq_sum (hξ : finestMeshInLevelUnits L t ≠ 0)
    (hs : Function.Injective (unitStep L m (levelDepth K 0))) (A : OneForms L m K) :
    gradAdjoint L m K t A = ∑ μ, forwardDifferenceAdjoint t μ (axisComponent A μ) := by
  refine ext_latticeInner hξ fun f => ?_
  rw [latticeInner_gradAdjoint, latticeInner_oneForms hs, latticeInner_sum_left]
  exact Finset.sum_congr rfl fun μ _ => latticeInner_forwardDifference μ f _
theorem scalarLaplacian_eq_sum (hξ : finestMeshInLevelUnits L t ≠ 0)
    (hs : Function.Injective (unitStep L m (levelDepth K 0))) (f : ZeroForms L m K) :
    scalarLaplacian L m K t f = ∑ μ, forwardDifferenceAdjoint t μ (forwardDifference t μ f) := by
  change gradAdjoint L m K t (grad t f) = _
  rw [gradAdjoint_eq_sum hξ hs]
  rfl
theorem scalarLaplacian_apply (hξ : finestMeshInLevelUnits L t ≠ 0)
    (hs : Function.Injective (unitStep L m (levelDepth K 0))) (f : ZeroForms L m K) (x : BareSite L m K) :
    scalarLaplacian L m K t f x = (finestMeshInLevelUnits L t ^ 2)⁻¹ * ∑ μ,
      ((f x - f (x + unitStep L m (levelDepth K 0) μ)) + (f x - f (x - unitStep L m (levelDepth K 0) μ))) := by
  rw [scalarLaplacian_eq_sum hξ hs, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [forwardDifferenceAdjoint, forwardDifference, sub_add_cancel]
  ring
theorem curl_grad (f : ZeroForms L m K) : curl t (grad t f) = 0 := by
  funext p
  change forwardDifference t p.firstAxis (axisComponent (grad t f) p.secondAxis) p.origin -
    forwardDifference t p.secondAxis (axisComponent (grad t f) p.firstAxis) p.origin = 0
  rw [axisComponent_grad, axisComponent_grad, forwardDifference_comm, sub_self]
theorem eq_of_grad_eq_zero (hξ : finestMeshInLevelUnits L t ≠ 0) (f : ZeroForms L m K)
    (h : grad t f = 0) (x y : BareSite L m K) : f x = f y := by
  have hstep : ∀ (x : BareSite L m K) (μ : Fin 4), f (x + unitStep L m (levelDepth K 0) μ) = f x := by
    intro x μ
    have h1 : (finestMeshInLevelUnits L t)⁻¹ * (f (x + unitStep L m (levelDepth K 0) μ) - f x) = 0 :=
      congrFun h (bondFrom x μ)
    have h2 := (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hξ)
    linarith
  have hzs : ∀ (n : ℤ) (x : BareSite L m K) (μ : Fin 4),
      f (x + n • unitStep L m (levelDepth K 0) μ) = f x := by
    intro n x μ
    induction n using Int.induction_on generalizing x with
    | zero => simp
    | succ i ih =>
      rw [add_smul, one_smul, ← add_assoc, hstep, ih]
    | pred i ih =>
      have h1 := hstep (x + (-(i : ℤ) - 1) • unitStep L m (levelDepth K 0) μ) μ
      rw [← h1, ← ih x]
      congr 1
      rw [sub_smul, one_smul]
      abel
  have hsum : ∀ (n : Fin 4 → ℤ) (S : Finset (Fin 4)) (x : BareSite L m K),
      f (x + ∑ μ ∈ S, n μ • unitStep L m (levelDepth K 0) μ) = f x := by
    intro n S
    induction S using Finset.induction_on with
    | empty => simp
    | insert μ S hμ ih =>
      intro x
      rw [Finset.sum_insert hμ, ← add_assoc, ih, hzs]
  obtain ⟨n, hn⟩ := exists_eq_sum_zsmul_unitStep (y - x)
  have h1 := hsum n Finset.univ x
  rw [← hn, add_sub_cancel] at h1
  exact h1.symm
theorem wholeLatticeFormulas (hξ : finestMeshInLevelUnits L t ≠ 0) (hs : Function.Injective (unitStep L m (levelDepth K 0))) :
    WholeLatticeFormulas L m K t := by
  refine ⟨gradAdjoint_eq_sum hξ hs, fun A x => ?_, scalarLaplacian_eq_sum hξ hs, scalarLaplacian_apply hξ hs,
    curl_grad, fun f h x y => eq_of_grad_eq_zero hξ f h x y⟩
  rw [gradAdjoint_eq_sum hξ hs, Finset.sum_apply]
  rfl
theorem latticeInner_forwardDifference_swap (A : OneForms L m K) (μ ν : Fin 4) :
    latticeInner L t (forwardDifference t μ (axisComponent A ν)) (forwardDifference t ν (axisComponent A μ)) =
      latticeInner L t (forwardDifferenceAdjoint t ν (axisComponent A ν)) (forwardDifferenceAdjoint t μ (axisComponent A μ)) := by
  rw [latticeInner_forwardDifference ν, ← forwardDifference_adjoint_comm, latticeInner_comm,
    latticeInner_forwardDifference μ, latticeInner_comm]
theorem normSq_curl (A : OneForms L m K) :
    normSq L t (curl t A) = (1 / 2 : ℝ) * ∑ μ, ∑ ν,
      normSq L t (forwardDifference t μ (axisComponent A ν) - forwardDifference t ν (axisComponent A μ)) := by
  have h : ∑ p, curl t A p * curl t A p = (1 / 2 : ℝ) * ∑ x, ∑ μ, ∑ ν,
      (forwardDifference t μ (axisComponent A ν) - forwardDifference t ν (axisComponent A μ)) x *
        (forwardDifference t μ (axisComponent A ν) - forwardDifference t ν (axisComponent A μ)) x := by
    rw [sum_barePlaquette, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact sum_ordered_pairs (fun μ ν => (forwardDifference t μ (axisComponent A ν) - forwardDifference t ν (axisComponent A μ)) x *
        (forwardDifference t μ (axisComponent A ν) - forwardDifference t ν (axisComponent A μ)) x)
      (fun μ ν => by simp only [Pi.sub_apply]; ring) (fun μ => by simp)
  have e : ∑ x, ∑ μ, ∑ ν, (forwardDifference t μ (axisComponent A ν) - forwardDifference t ν (axisComponent A μ)) x *
        (forwardDifference t μ (axisComponent A ν) - forwardDifference t ν (axisComponent A μ)) x =
      ∑ μ, ∑ ν, ∑ x, (forwardDifference t μ (axisComponent A ν) - forwardDifference t ν (axisComponent A μ)) x *
        (forwardDifference t μ (axisComponent A ν) - forwardDifference t ν (axisComponent A μ)) x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_comm
  simp only [normSq, latticeInner_eq_sum]
  rw [h, e]
  simp only [← Finset.mul_sum]
  ring
theorem sum_latticeInner_swap (hξ : finestMeshInLevelUnits L t ≠ 0)
    (hs : Function.Injective (unitStep L m (levelDepth K 0))) (A : OneForms L m K) :
    ∑ μ, ∑ ν, latticeInner L t (forwardDifference t μ (axisComponent A ν)) (forwardDifference t ν (axisComponent A μ)) =
      normSq L t (gradAdjoint L m K t A) := by
  rw [normSq, gradAdjoint_eq_sum hξ hs, latticeInner_sum_left]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [latticeInner_sum_right]
  exact Finset.sum_congr rfl fun ν _ => (latticeInner_forwardDifference_swap A μ ν).trans (latticeInner_comm _ _)
theorem half_sum_normSq_sub (hξ : finestMeshInLevelUnits L t ≠ 0)
    (hs : Function.Injective (unitStep L m (levelDepth K 0))) (A : OneForms L m K) :
    (1 / 2 : ℝ) * ∑ μ, ∑ ν,
        normSq L t (forwardDifference t μ (axisComponent A ν) - forwardDifference t ν (axisComponent A μ)) =
      ∑ μ, ∑ ν, normSq L t (forwardDifference t μ (axisComponent A ν)) -
        normSq L t (gradAdjoint L m K t A) := by
  have hswap : ∑ μ, ∑ ν, normSq L t (forwardDifference t ν (axisComponent A μ)) =
      ∑ μ, ∑ ν, normSq L t (forwardDifference t μ (axisComponent A ν)) := Finset.sum_comm
  simp only [normSq_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_latticeInner_swap hξ hs, hswap]
  ring
theorem latticeInner_hodgeLaplacian (A : OneForms L m K) :
    latticeInner L t A (hodgeLaplacian L m K t A) =
      normSq L t (curl t A) + normSq L t (gradAdjoint L m K t A) := by
  change latticeInner L t A (curlAdjoint L m K t (curl t A) + grad t (gradAdjoint L m K t A)) = _
  rw [latticeInner_add_right, latticeInner_comm A (curlAdjoint L m K t _), latticeInner_curlAdjoint,
    ← latticeInner_gradAdjoint]
  rfl
theorem latticeInner_scalarLaplacian (f : ZeroForms L m K) :
    latticeInner L t f (scalarLaplacian L m K t f) = normSq L t (grad t f) := by
  change latticeInner L t f (gradAdjoint L m K t (grad t f)) = _
  rw [latticeInner_comm, latticeInner_gradAdjoint]
  rfl
theorem latticeInner_curlCurl (A : OneForms L m K) :
    latticeInner L t A (curlCurl L m K t A) = normSq L t (curl t A) := by
  change latticeInner L t A (curlAdjoint L m K t (curl t A)) = _
  rw [latticeInner_comm, latticeInner_curlAdjoint]
  rfl
theorem normSq_grad (hs : Function.Injective (unitStep L m (levelDepth K 0))) (f : ZeroForms L m K) :
    normSq L t (grad t f) = ∑ μ, normSq L t (forwardDifference t μ f) := by
  rw [normSq, latticeInner_oneForms hs]
  rfl
theorem summationByParts_holds (hξ : finestMeshInLevelUnits L t ≠ 0)
    (hs : Function.Injective (unitStep L m (levelDepth K 0))) : SummationByParts L m K t := by
  intro A
  refine ⟨normSq_curl A, half_sum_normSq_sub hξ hs A, ?_, ?_⟩
  · rw [latticeInner_hodgeLaplacian, normSq_curl, half_sum_normSq_sub hξ hs]
    ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [latticeInner_scalarLaplacian, normSq_grad hs]
theorem framedBonds_subset_starBonds (Ω₀ : Set (FourTorus L m)) (φ : BondFrame) :
    framedBonds K Ω₀ φ ⊆ starBonds K Ω₀ := by
  cases φ
  · exact fun b hb => Or.inl hb.1
  · exact fun b hb => hb
theorem frameProjections (Ω₀ : Set (FourTorus L m)) : FrameProjections K Ω₀ := by
  refine ⟨fun φ => indicatorMul_add_sdiff (framedBonds_subset_starBonds Ω₀ φ), ?_, rfl, ?_⟩
  · change indicatorMul (starBonds K Ω₀ \ starBonds K Ω₀) = 0
    rw [Set.sdiff_self, indicatorMul_empty]
  · rintro b ⟨h1, h2⟩
    have h3 : ¬(b.1.source ∈ sitesOfRegion K Ω₀ ∧ b.1.target ∈ sitesOfRegion K Ω₀) := h2
    have h4 : b.1.source ∈ sitesOfRegion K Ω₀ ∨ b.1.target ∈ sitesOfRegion K Ω₀ := h1
    change (_ ∧ ¬_) ∨ (_ ∧ ¬_)
    tauto
theorem frontierBonds_univ :
    frontierBonds K (Set.univ : Set (FourTorus L m)) = ∅ :=
  Set.sdiff_eq_empty.2 fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩
theorem wholeTorusFrames : WholeTorusFrames L m K := by
  have hb : ∀ (φ : BondFrame), framedBonds K (Set.univ : Set (FourTorus L m)) φ = Set.univ := by
    intro φ
    cases φ
    · exact Set.eq_univ_of_forall fun _ => ⟨Set.mem_univ _, Set.mem_univ _⟩
    · exact Set.eq_univ_of_forall fun _ => Or.inl (Set.mem_univ _)
  refine ⟨Set.eq_univ_of_forall fun _ => Set.mem_univ _, hb, fun φ => ?_, frontierBonds_univ, ?_⟩
  · refine Set.eq_univ_of_forall fun p => ⟨bondFrom p.origin p.firstAxis, Set.mem_insert _ _, ?_⟩
    rw [hb]
    exact Set.mem_univ _
  · refine Set.subset_empty_iff.1 fun x hx => ?_
    obtain ⟨_, b, hb', _⟩ := hx
    rw [frontierBonds_univ] at hb'
    exact hb'
theorem dirichletGradAdjointIdentity (Ω₀ : Set (FourTorus L m)) : DirichletGradAdjointIdentity K t Ω₀ := by
  intro φ f A
  have hA : indicatorMul (framedBonds K Ω₀ φ) (A : OneForms L m K) = A :=
    indicatorMul_of_mem_range A.2
  have hf : indicatorMul (sitesOfRegion K Ω₀) (f : ZeroForms L m K) = f :=
    indicatorMul_of_mem_range f.2
  change latticeInner L t (A : OneForms L m K)
      (indicatorMul (framedBonds K Ω₀ φ) (grad t (f : ZeroForms L m K))) =
    latticeInner L t (indicatorMul (sitesOfRegion K Ω₀) (gradAdjoint L m K t (A : OneForms L m K)))
      (f : ZeroForms L m K)
  rw [← latticeInner_indicatorMul, hA, latticeInner_indicatorMul, hf, latticeInner_gradAdjoint]
theorem dirichletZeroFormFacts (Ω₀ : Set (FourTorus L m)) : DirichletZeroFormFacts K t Ω₀ := by
  intro f
  have hf : indicatorMul (sitesOfRegion K Ω₀) (f : ZeroForms L m K) = f :=
    indicatorMul_of_mem_range f.2
  have hf0 : ∀ x, x ∉ sitesOfRegion K Ω₀ → (f : ZeroForms L m K) x = 0 :=
    fun x hx => apply_eq_zero_of_mem_range_indicatorMul f.2 hx
  have hvan : ∀ b, b ∉ starBonds K Ω₀ → grad t (f : ZeroForms L m K) b = 0 := by
    intro b hb
    have h1 : b.1.source ∉ sitesOfRegion K Ω₀ := fun h => hb (Or.inl h)
    have h2 : b.1.target ∉ sitesOfRegion K Ω₀ := fun h => hb (Or.inr h)
    change (finestMeshInLevelUnits L t)⁻¹ * ((f : ZeroForms L m K) b.1.target - (f : ZeroForms L m K) b.1.source) = 0
    rw [hf0 _ h1, hf0 _ h2]
    simp
  refine ⟨hvan, ?_, ?_, ?_⟩
  · rintro b ⟨_, hin⟩ x hx (h | h)
    · right
      have hh : b.1.target ∉ sitesOfRegion K Ω₀ := fun h' => hin ⟨by rw [h]; exact hx, h'⟩
      change (finestMeshInLevelUnits L t)⁻¹ * ((f : ZeroForms L m K) b.1.target - (f : ZeroForms L m K) b.1.source) = _
      rw [hf0 _ hh, h]
      ring
    · left
      have ht : b.1.source ∉ sitesOfRegion K Ω₀ := fun h' => hin ⟨h', by rw [h]; exact hx⟩
      change (finestMeshInLevelUnits L t)⁻¹ * ((f : ZeroForms L m K) b.1.target - (f : ZeroForms L m K) b.1.source) = _
      rw [hf0 _ ht, h]
      ring
  · change latticeInner L t (f : ZeroForms L m K) (indicatorMul (sitesOfRegion K Ω₀)
      (scalarLaplacian L m K t (indicatorMul (sitesOfRegion K Ω₀) (f : ZeroForms L m K)))) = _
    rw [hf, ← latticeInner_indicatorMul, hf, latticeInner_scalarLaplacian]
  · rw [normSq, latticeInner, finsum_mul_self_eq_finsum_mem_sq _ hvan]
theorem dirichletOneFormFacts (Ω₀ : Set (FourTorus L m)) : DirichletOneFormFacts K t Ω₀ := by
  intro φ A
  have hA : indicatorMul (framedBonds K Ω₀ φ) (A : OneForms L m K) = A :=
    indicatorMul_of_mem_range A.2
  have hA0 : ∀ b, b ∉ framedBonds K Ω₀ φ → (A : OneForms L m K) b = 0 :=
    fun b hb => apply_eq_zero_of_mem_range_indicatorMul A.2 hb
  have hvan : ∀ p, p ∉ framedPlaquettes K Ω₀ φ → curl t (A : OneForms L m K) p = 0 := by
    intro p hp
    have hb : ∀ b ∈ edgesOf p, (A : OneForms L m K) b = 0 :=
      fun b h => hA0 b fun h' => hp ⟨b, h, h'⟩
    have h1 := hb (bondFrom p.origin p.firstAxis) (by simp [edgesOf])
    have h2 := hb (bondFrom (p.origin + unitStep L m (levelDepth K 0) p.firstAxis) p.secondAxis)
      (by simp [edgesOf])
    have h3 := hb (bondFrom (p.origin + unitStep L m (levelDepth K 0) p.secondAxis) p.firstAxis)
      (by simp [edgesOf])
    have h4 := hb (bondFrom p.origin p.secondAxis) (by simp [edgesOf])
    change curlAxes t (A : OneForms L m K) p.firstAxis p.secondAxis p.origin = 0
    simp only [curlAxes, forwardDifference, axisComponent, Pi.sub_apply, h1, h2, h3, h4]
    ring
  refine ⟨hvan, ?_, ?_⟩
  · change latticeInner L t (A : OneForms L m K) (indicatorMul (framedBonds K Ω₀ φ)
      (curlCurl L m K t (indicatorMul (framedBonds K Ω₀ φ) (A : OneForms L m K)))) = _
    rw [hA, ← latticeInner_indicatorMul, hA, latticeInner_curlCurl]
  · rw [normSq, latticeInner, finsum_mul_self_eq_finsum_mem_sq _ hvan]
def incidentBond (x : BareSite L m K) (q : Fin 4 × Bool) : BareBond L m K :=
  cond q.2 (bondFrom x q.1) (bondFrom (x - unitStep L m (levelDepth K 0) q.1) q.1)
theorem incidentBond_injective (hs : Function.Injective (unitStep L m (levelDepth K 0)))
    (h0 : ∀ μ, unitStep L m (levelDepth K 0) μ ≠ 0) (x : BareSite L m K) :
    Function.Injective (incidentBond x) := by
  rintro ⟨μ, _ | _⟩ ⟨ν, _ | _⟩ h
  · have h1 : x - unitStep L m (levelDepth K 0) μ = x - unitStep L m (levelDepth K 0) ν :=
      congrArg (fun b : BareBond L m K => b.1.source) h
    rw [hs (sub_right_injective h1)]
  · have h1 : x - unitStep L m (levelDepth K 0) μ = x := congrArg (fun b : BareBond L m K => b.1.source) h
    exact absurd (sub_eq_self.mp h1) (h0 μ)
  · have h1 : x = x - unitStep L m (levelDepth K 0) ν := congrArg (fun b : BareBond L m K => b.1.source) h
    exact absurd (sub_eq_self.mp h1.symm) (h0 ν)
  · have h1 : x + unitStep L m (levelDepth K 0) μ = x + unitStep L m (levelDepth K 0) ν :=
      congrArg (fun b : BareBond L m K => b.1.target) h
    rw [hs (add_left_cancel h1)]
theorem mem_range_incidentBond (x : BareSite L m K) (b : BareBond L m K) :
    b ∈ Set.range (incidentBond x) ↔ (b.1.source = x ∨ b.1.target = x) := by
  constructor
  · rintro ⟨⟨μ, _ | _⟩, rfl⟩
    · exact Or.inr (sub_add_cancel x _)
    · exact Or.inl rfl
  · obtain ⟨b, μ, hμ⟩ := b
    rintro (h | h)
    · change b.source = x at h
      subst h
      refine ⟨(μ, true), Subtype.ext (Bond.ext rfl ?_)⟩
      change b.source + unitStep L m (levelDepth K 0) μ = b.target
      rw [← hμ]
      abel
    · change b.target = x at h
      subst h
      refine ⟨(μ, false), Subtype.ext (Bond.ext ?_ ?_)⟩
      · change b.target - unitStep L m (levelDepth K 0) μ = b.source
        rw [← hμ]
        abel
      · exact sub_add_cancel _ _
theorem oppositeEnd_of_source {b : BareBond L m K} {x : BareSite L m K} (h : b.1.source = x) :
    oppositeEnd b x = b.1.target := if_pos h
theorem oppositeEnd_of_not_source {b : BareBond L m K} {x : BareSite L m K} (h : b.1.source ≠ x) :
    oppositeEnd b x = b.1.source := if_neg h
theorem finsum_frontierBondsAt (hs : Function.Injective (unitStep L m (levelDepth K 0)))
    (h0 : ∀ μ, unitStep L m (levelDepth K 0) μ ≠ 0) (Ω₀ : Set (FourTorus L m)) (f : ZeroForms L m K)
    (hf0 : ∀ y, y ∉ sitesOfRegion K Ω₀ → f y = 0) (x : BareSite L m K)
    (hx : x ∉ sitesOfRegion K Ω₀) :
    ∑ᶠ b ∈ frontierBondsAt K Ω₀ x, f (oppositeEnd b x) =
      ∑ μ, (f (x + unitStep L m (levelDepth K 0) μ) + f (x - unitStep L m (levelDepth K 0) μ)) := by
  have h1 : ∑ᶠ b ∈ frontierBondsAt K Ω₀ x, f (oppositeEnd b x) =
      ∑ᶠ b ∈ Set.range (incidentBond x), f (oppositeEnd b x) := by
    rw [finsum_mem_def, finsum_mem_def]
    refine finsum_congr fun b => ?_
    by_cases hB : b ∈ frontierBondsAt K Ω₀ x
    · have hR : b ∈ Set.range (incidentBond x) := (mem_range_incidentBond x b).2 hB.2
      rw [Set.indicator_of_mem hB, Set.indicator_of_mem hR]
    · rw [Set.indicator_of_notMem hB]
      by_cases hR : b ∈ Set.range (incidentBond x)
      · rw [Set.indicator_of_mem hR]
        have hend := (mem_range_incidentBond x b).1 hR
        symm
        refine hf0 _ fun hy => hB ⟨?_, hend⟩
        by_cases ht : b.1.source = x
        · rw [oppositeEnd_of_source ht] at hy
          exact ⟨Or.inr hy, fun h => hx (ht ▸ h.1)⟩
        · have hh : b.1.target = x := hend.resolve_left ht
          rw [oppositeEnd_of_not_source ht] at hy
          exact ⟨Or.inl hy, fun h => hx (hh ▸ h.2)⟩
      · rw [Set.indicator_of_notMem hR]
  rw [h1, finsum_mem_range (incidentBond_injective hs h0 x), finsum_eq_sum_of_fintype,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Fintype.sum_bool]
  have ht : (incidentBond x (μ, true)).1.source = x := rfl
  have hn : (incidentBond x (μ, false)).1.source ≠ x := fun h => h0 μ (sub_eq_self.mp h)
  rw [oppositeEnd_of_source ht, oppositeEnd_of_not_source hn]
  rfl
theorem laplacianRowsOutside (hξ : finestMeshInLevelUnits L t ≠ 0)
    (hs : Function.Injective (unitStep L m (levelDepth K 0)))
    (h0 : ∀ μ, unitStep L m (levelDepth K 0) μ ≠ 0) (Ω₀ : Set (FourTorus L m)) : LaplacianRowsOutside K t Ω₀ := by
  intro f x hx
  have hf0 : ∀ y, y ∉ sitesOfRegion K Ω₀ → (f : ZeroForms L m K) y = 0 :=
    fun y hy => apply_eq_zero_of_mem_range_indicatorMul f.2 hy
  refine ⟨?_, ?_⟩
  · rintro b ⟨⟨hst, hin⟩, hend⟩
    by_cases ht : b.1.source = x
    · have hh : b.1.target ∈ sitesOfRegion K Ω₀ :=
        (hst : b.1.source ∈ sitesOfRegion K Ω₀ ∨ b.1.target ∈ sitesOfRegion K Ω₀).resolve_left
          (fun h => hx (ht ▸ h))
      rw [oppositeEnd_of_source ht]
      exact ⟨hh, b, ⟨hst, hin⟩, Or.inr rfl⟩
    · have hh : b.1.target = x := hend.resolve_left ht
      have htl : b.1.source ∈ sitesOfRegion K Ω₀ :=
        (hst : b.1.source ∈ sitesOfRegion K Ω₀ ∨ b.1.target ∈ sitesOfRegion K Ω₀).resolve_right
          (fun h => hx (hh ▸ h))
      rw [oppositeEnd_of_not_source ht]
      exact ⟨htl, b, ⟨hst, hin⟩, Or.inl rfl⟩
  · rw [scalarLaplacian_apply hξ hs, finsum_frontierBondsAt hs h0 Ω₀ _ hf0 x hx, hf0 x hx, ← mul_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    ring
end Sums
theorem statement : Statement := by
  intro D
  have h3 := D.three_le_L
  have hL0 : 0 < D.L := by omega
  have hL2 : 2 ≤ D.L := by omega
  have hj : (0 : ℤ) ≤ levelDepth D.K 0 := by simp [levelDepth]
  have hξ : finestMeshInLevelUnits D.L D.t ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hL0.ne')
  have hs : Function.Injective (unitStep D.L D.m (levelDepth D.K 0)) := unitStep_injective hL2 hj
  have h0 : ∀ μ, unitStep D.L D.m (levelDepth D.K 0) μ ≠ 0 := unitStep_ne_zero hL2 hj
  have : Finite (BareSite D.L D.m D.K) := finite_site hL0 D.m (levelDepth D.K 0)
  have : Finite (BareBond D.L D.m D.K) :=
    Finite.of_surjective _ (bondFrom_bijective hs).surjective
  have : Finite (BarePlaquette D.L D.m D.K) :=
    Finite.of_equiv _ (barePlaquetteEquiv D.L D.m D.K).symm
  let _ : Fintype (BareSite D.L D.m D.K) := Fintype.ofFinite _
  let _ : Fintype (BareBond D.L D.m D.K) := Fintype.ofFinite _
  let _ : Fintype (BarePlaquette D.L D.m D.K) := Fintype.ofFinite _
  exact ⟨differenceAdjointsCommute, wholeLatticeFormulas hξ hs, summationByParts_holds hξ hs, wholeTorusFrames, fun Ω₀ =>
    ⟨frameProjections Ω₀, dirichletGradAdjointIdentity Ω₀, dirichletZeroFormFacts Ω₀, dirichletOneFormFacts Ω₀,
      laplacianRowsOutside hξ hs h0 Ω₀⟩⟩
end YangMills.Construction.PeriodicLattice.DirichletOperators.BareLatticeOperators
