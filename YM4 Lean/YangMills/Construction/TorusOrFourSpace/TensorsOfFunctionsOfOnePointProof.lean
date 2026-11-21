import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNormProof
import YangMills.Construction.TorusOrFourSpace.DerivativesOfFunctionsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.DistanceAndLiftsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.IteratedPartialsOfProductsOverTheFactors
import YangMills.Construction.TorusOrFourSpace.ProductsAndProjectionsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.TensorsOfFunctionsOfOnePoint
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicSpace.TensorOfSingles
open Kind
private theorem isClosedWrt_closureWrt {X : Type*} {d : X → X → ℝ}
    (tri : ∀ x y z, d x z ≤ d x y + d y z) (Z : Set X) :
    MetricNotions.IsClosedWrt d (MetricNotions.closureWrt d Z) := by apply _root_.YangMills.SharedProofs.p11892 <;> assumption
private theorem closureWrt_subset_of_isClosedWrt {X : Type*} {d : X → X → ℝ} {A C : Set X}
    (hC : MetricNotions.IsClosedWrt d C) (h : A ⊆ C) : MetricNotions.closureWrt d A ⊆ C := by
  intro x hx
  by_contra hxC
  obtain ⟨r, hr, hy⟩ := hC x hxC
  obtain ⟨y, hyA, hxy⟩ := hx r hr
  exact hy y hxy (h hyA)
private theorem IsCompactWrt.of_isClosedWrt_subset {X : Type*} {d : X → X → ℝ} {K T : Set X}
    (hK : MetricNotions.IsCompactWrt d K) (hT : MetricNotions.IsClosedWrt d T)
    (hTK : T ⊆ K) : MetricNotions.IsCompactWrt d T := by apply _root_.YangMills.SharedProofs.p5019 <;> assumption
private theorem Coords.block_zero_of_one (z : Fin 4 → ℝ) :
    Coords.block (p := 1) z ⟨0, (1 : ℕ+).pos⟩ = z := by
  funext μ
  show z ⟨4 * 0 + (μ : ℕ), _⟩ = z μ
  congr 1
  apply Fin.ext
  simp
private theorem tensorProd_comp_proj (D : Params) (E : Kind) {p : ℕ+} (φ : Fin (p : ℕ) → E.Pt D → ℂ) :
    Tuple.tensorProd D E φ ∘ Tuple.proj D E =
      fun x : Coords p => ∏ i, (Tuple.ofSingle D E (φ i) ∘
        Tuple.proj D E) (x.block i) := by
  funext x
  show (∏ i, φ i (E.quotMap D (x.block i))) = _
  refine Finset.prod_congr rfl fun i _ => ?_
  exact congrArg (fun w : Fin 4 → ℝ => φ i (E.quotMap D w)) (Coords.block_zero_of_one (x.block i)).symm
private theorem CoordIndex.degree_block_le {p : ℕ+} (α : CoordIndex p) (i : Fin (p : ℕ))
    (hlt : ∀ j : Fin (4 * ((1 : ℕ+) : ℕ)), 4 * (i : ℕ) + (j : ℕ) < 4 * (p : ℕ)) :
    CoordIndex.degree (p := 1) (fun j => α ⟨4 * (i : ℕ) + (j : ℕ), hlt j⟩) ≤ α.degree := by
  unfold CoordIndex.degree
  have hinj : Function.Injective
      (fun j : Fin (4 * ((1 : ℕ+) : ℕ)) => (⟨4 * (i : ℕ) + (j : ℕ), hlt j⟩ : Fin (4 * (p : ℕ)))) := by
    intro a b h
    have h' : 4 * (i : ℕ) + (a : ℕ) = 4 * (i : ℕ) + (b : ℕ) := congrArg Fin.val h
    exact Fin.ext (by omega)
  calc ∑ j : Fin (4 * ((1 : ℕ+) : ℕ)), α ⟨4 * (i : ℕ) + (j : ℕ), hlt j⟩
      = ∑ k ∈ Finset.univ.image
          (fun j : Fin (4 * ((1 : ℕ+) : ℕ)) =>
            (⟨4 * (i : ℕ) + (j : ℕ), hlt j⟩ : Fin (4 * (p : ℕ)))), α k :=
        (Finset.sum_image fun _ _ _ _ h => hinj h).symm
    _ ≤ ∑ k, α k := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
private theorem tensorProd_isClassC (partials : PartialDerivatives.IteratedPartialsOfBlockProduct)
    (D : Params) (E : Kind) {p : ℕ+} {ν : ℕ} {φ : Fin (p : ℕ) → E.Pt D → ℂ}
    (h : ∀ i, Tuple.IsClassC D E ν (Tuple.ofSingle D E (φ i))) :
    Tuple.IsClassC D E ν (Tuple.tensorProd D E φ) := by
  have key := (partials p ν
    (fun i => Tuple.ofSingle D E (φ i) ∘ Tuple.proj D E) h).1
  rw [Tuple.IsClassC, tensorProd_comp_proj]
  exact key
private theorem supportQ_eq_image_supportT (D : Params) (E : Kind) (φ : E.Pt D → ℂ)
    (nn : ∀ y y' : E.Pt D, 0 ≤ Kind.quotDist D E y y')
    (proj : ∀ y y' : E.Tuple D 1,
      Kind.quotDist D E (y ⟨0, (1 : ℕ+).pos⟩) (y' ⟨0, (1 : ℕ+).pos⟩) ≤
        Tuple.tupleDist D E y y') :
    Kind.supportQ D E φ = (fun y : E.Tuple D 1 => y ⟨0, (1 : ℕ+).pos⟩) ''
      Tuple.supportT D E (Tuple.ofSingle D E φ) := by
  ext y
  constructor
  · intro hy
    refine ⟨fun _ => y, ?_, rfl⟩
    intro r hr
    obtain ⟨z, hz, hyz⟩ := hy r hr
    refine ⟨fun _ => z, hz, ?_⟩
    have hd : Tuple.tupleDist D E (p := 1) (fun _ => y) (fun _ => z) =
        Kind.quotDist D E y z := by
      show Real.sqrt (∑ _i : Fin ((1 : ℕ+) : ℕ), Kind.quotDist D E y z ^ 2) = _
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [Real.sqrt_sq (nn y z)]
    rw [hd]
    exact hyz
  · rintro ⟨w, hw, rfl⟩ r hr
    obtain ⟨z, hz, hwz⟩ := hw r hr
    exact ⟨z ⟨0, (1 : ℕ+).pos⟩, hz, (proj w z).trans_lt hwz⟩
private theorem supportT_tensorProd_subset_boxSet (D : Params) (E : Kind) {p : ℕ+} (φ : Fin (p : ℕ) → E.Pt D → ℂ)
    (zero : ∀ y : E.Pt D, Kind.quotDist D E y y = 0)
    (hclosed : Tuple.IsClosedT D E
      (Tuple.boxSet D E fun i => Kind.supportQ D E (φ i))) :
    Tuple.supportT D E (Tuple.tensorProd D E φ) ⊆
      Tuple.boxSet D E fun i => Kind.supportQ D E (φ i) := by
  refine closureWrt_subset_of_isClosedWrt hclosed fun y hy i r hr => ?_
  have hne : ∏ j, φ j (y j) ≠ 0 := hy
  refine ⟨y i, Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i), ?_⟩
  rw [zero]
  exact hr
private theorem tensorProd_update_apply (D : Params) (E : Kind) {p : ℕ+} (φ : Fin (p : ℕ) → E.Pt D → ℂ)
    (i : Fin (p : ℕ)) (f : E.Pt D → ℂ) (y : E.Tuple D p) :
    Tuple.tensorProd D E (Function.update φ i f) y =
      f (y i) * ∏ j ∈ Finset.univ.erase i, φ j (y j) := by
  show ∏ j, Function.update φ i f j (y j) = _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
theorem claim_holds
    (partials : PartialDerivatives.IteratedPartialsOfBlockProduct)
    (products : TupleProducts.Statement)
    (derivatives : TupleDerivatives.Statement)
    (lifts : TupleMetric.QuotientDistanceAndLifts)
    (metric : Kind.QuotientCompactC1.Claim) : Claim := by
  intro D E p
  obtain ⟨⟨nnY, zeroY, -, triY, -, -⟩, -⟩ := metric D E
  obtain ⟨-, -, ⟨-, -, -, triP⟩, -, -⟩ := lifts D E p
  have zero : ∀ y : E.Pt D, Kind.quotDist D E y y = 0 := fun y => (zeroY y y).2 rfl
  have closedSupport : ∀ u : E.Pt D → ℂ, Kind.IsClosedQ D E (Kind.supportQ D E u) :=
    fun u => isClosedWrt_closureWrt triY _
  have closedProduct : ∀ φ : Fin (p : ℕ) → E.Pt D → ℂ, Tuple.IsClosedT D E
      (Tuple.boxSet D E fun i => Kind.supportQ D E (φ i)) :=
    fun φ => ((products D E p).1 _).2.1 fun i => closedSupport (φ i)
  refine ⟨fun ν φ h => ⟨tensorProd_isClassC partials D E h, fun α hα => ?_,
    supportT_tensorProd_subset_boxSet D E φ zero (closedProduct φ)⟩, fun Ω φ _ hφ => ?_, fun φ i ψ χ c => ?_⟩
  · obtain ⟨hex, hd, -⟩ := (derivatives D E p).1 ν _ (tensorProd_isClassC partials D E h) α hα
    refine hex.unique hd ?_
    rw [tensorProd_comp_proj D E φ, (partials p ν
      (fun i => Tuple.ofSingle D E (φ i) ∘ Tuple.proj D E) h).2 α hα,
      tensorProd_comp_proj]
    funext x
    refine Finset.prod_congr rfl fun i _ => ?_
    have hβ := (CoordIndex.degree_block_le α i (by
      intro j
      have h1 := i.2
      have h2 := j.2
      simp only [PNat.one_coe] at h2
      omega)).trans hα
    have key := congrFun ((derivatives D E 1).1 ν _ (h i) _ hβ).2.1 (x.block i)
    rw [← key]
    show Tuple.partialDeriv D E _ _ (fun _ => _) =
      Tuple.partialDeriv D E _ _ (Tuple.proj D E (p := 1) (x.block i))
    congr 1
    funext j
    have hj : j = ⟨0, (1 : ℕ+).pos⟩ := Fin.ext (by
      have h2 := j.2
      simp only [PNat.one_coe] at h2
      show (j : ℕ) = 0
      omega)
    subst hj
    rfl
  · have hφ' : ∀ i, Tuple.IsSmoothT D E (Tuple.ofSingle D E (φ i)) ∧
        Tuple.IsCompactT D E
          (Tuple.supportT D E (Tuple.ofSingle D E (φ i))) ∧
        Tuple.supportT D E (Tuple.ofSingle D E (φ i)) ⊆
          Tuple.singleSet D E (Ω i) := hφ
    have hproj := (products D E 1).2.1 ⟨0, (1 : ℕ+).pos⟩
    have hS : ∀ i, Kind.supportQ D E (φ i) =
        (fun y : E.Tuple D 1 => y ⟨0, (1 : ℕ+).pos⟩) ''
          Tuple.supportT D E (Tuple.ofSingle D E (φ i)) :=
      fun i => supportQ_eq_image_supportT D E (φ i) nnY hproj.1
    have hcomp : ∀ i, Kind.IsCompactQ D E (Kind.supportQ D E (φ i)) := by
      intro i
      rw [hS i]
      exact hproj.2 _ (hφ' i).2.1
    have hsub := supportT_tensorProd_subset_boxSet D E φ zero (closedProduct φ)
    refine ⟨fun ν => tensorProd_isClassC partials D E fun i => (hφ' i).1 ν,
      IsCompactWrt.of_isClosedWrt_subset (((products D E p).1 _).2.2 hcomp)
        (isClosedWrt_closureWrt triP _) hsub,
      fun y hy i => ?_⟩
    have hyi : y i ∈ Kind.supportQ D E (φ i) := hsub hy i
    rw [hS i] at hyi
    obtain ⟨w, hw, hwy⟩ := hyi
    have hmem : w ⟨0, (1 : ℕ+).pos⟩ ∈ Ω i := (hφ' i).2.2 hw
    rw [← hwy]
    exact hmem
  · constructor
    · funext y
      simp only [Pi.add_apply, tensorProd_update_apply]
      ring
    · funext y
      simp only [Pi.smul_apply, tensorProd_update_apply, smul_eq_mul]
      ring
end YangMills.Construction.PeriodicSpace.TensorOfSingles
