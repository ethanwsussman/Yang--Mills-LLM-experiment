import YangMills.Construction.RealFunctions.ExponentialSumsDetermined
import YangMills.Construction.RotationInvariance.CovarianceOfTheHarmonicsBetweenOrderedPositions
import YangMills.Construction.RotationInvariance.DensityOfThePlateFunctionsAtDistinctPointsProof
import YangMills.Construction.RotationInvariance.InvariantTwoPointFunctionHasTopFrequencyZeroProof
import YangMills.Construction.RotationInvariance.MotionsOfPlatesAndQuarterRotationsProof
import YangMills.Construction.RotationInvariance.RulesOfTheRotationsTheForwardTubeAndTheSector
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Complex (I)
open RealPlane ForwardTube Filter
open Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
open scoped Topology
namespace EuclideanFunctionals.HarmonicRotationCovariance
section Plane
theorem rotate_apply_zero (t : ℝ) (a : RealPlane) :
    rotate t a 0 = a 0 * Real.cos t - a 1 * Real.sin t := by
  simp [RealPlane.rotate]
theorem rotate_apply_one (t : ℝ) (a : RealPlane) :
    rotate t a 1 = a 0 * Real.sin t + a 1 * Real.cos t := by
  simp [RealPlane.rotate]
theorem realPlane_ext {a b : RealPlane} (h₀ : a 0 = b 0) (h₁ : a 1 = b 1) : a = b := by apply _root_.YangMills.Construction.EuclideanFunctionals.HarmonicDensity.ext_of_coords <;> assumption
theorem inner_eq_coord_sum (a b : RealPlane) : inner ℝ a b = a 0 * b 0 + a 1 * b 1 := by apply _root_.YangMills.Construction.ForwardTube.inner_eq_coord_sum <;> assumption
theorem rotate_sub (t : ℝ) (a b : RealPlane) :
    rotate t (a - b) = rotate t a - rotate t b := by
  apply realPlane_ext
  · simp only [rotate_apply_zero, PiLp.sub_apply]
    ring
  · simp only [rotate_apply_one, PiLp.sub_apply]
    ring
theorem rotate_rotate (t s : ℝ) (a : RealPlane) :
    rotate t (rotate s a) = rotate (s + t) a := by
  apply realPlane_ext
  · simp only [rotate_apply_zero, rotate_apply_one, Real.cos_add, Real.sin_add]
    ring
  · simp only [rotate_apply_zero, rotate_apply_one, Real.cos_add, Real.sin_add]
    ring
theorem rotate_zero (a : RealPlane) : rotate 0 a = a := by apply _root_.YangMills.Construction.EuclideanFunctionals.ProductMotions.rotate_zero <;> assumption
theorem inner_rotate_rotate (t : ℝ) (a b : RealPlane) :
    inner ℝ (rotate t a) (rotate t b) = inner ℝ a b := by
  simp only [inner_eq_coord_sum, rotate_apply_zero, rotate_apply_one]
  linear_combination (a 0 * b 0 + a 1 * b 1) * Real.sin_sq_add_cos_sq t
theorem continuous_rotate (t : ℝ) : Continuous (rotate t) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.continuous_rotate <;> assumption
theorem inner_rotate_right (e v : RealPlane) (t : ℝ) :
    inner ℝ e (rotate t v) =
      inner ℝ e v * Real.cos t + (e 1 * v 0 - e 0 * v 1) * Real.sin t := by
  simp only [inner_eq_coord_sum, rotate_apply_zero, rotate_apply_one]
  ring
theorem exists_cos_shift_form {A : ℝ} (hA : 0 < A) (B : ℝ) :
    ∃ r ψ : ℝ, 0 < r ∧ |ψ| < Real.pi / 2 ∧
      ∀ t : ℝ, A * Real.cos t + B * Real.sin t = r * Real.cos (ψ + t) := by
  set z : ℂ := ⟨A, -B⟩ with hz
  have hz0 : z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hz] at this
    exact hA.ne' this
  refine ⟨‖z‖, Complex.arg z, norm_pos_iff.2 hz0, ?_, fun t => ?_⟩
  · exact Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by simpa [hz] using hA))
  · have h₁ : ‖z‖ * Real.cos (Complex.arg z) = A := Complex.norm_mul_cos_arg z
    have h₂ : ‖z‖ * Real.sin (Complex.arg z) = -B := Complex.norm_mul_sin_arg z
    rw [Real.cos_add]
    linear_combination (-Real.cos t) * h₁ + (Real.sin t) * h₂
theorem cos_add_pos_iff {ψ t : ℝ} (hψ : |ψ| < Real.pi / 2) (ht : t ∈ Set.Ioo (-Real.pi) Real.pi) :
    0 < Real.cos (ψ + t) ↔ t ∈ Set.Ioo (-(Real.pi / 2) - ψ) (Real.pi / 2 - ψ) := by
  obtain ⟨h₁, h₂⟩ := abs_lt.1 hψ
  obtain ⟨h₃, h₄⟩ := ht
  constructor
  · intro hc
    constructor
    · by_contra hlt
      have : Real.cos (-(ψ + t)) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
      rw [Real.cos_neg] at this
      linarith
    · by_contra hlt
      have : Real.cos (ψ + t) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
      linarith
  · rintro ⟨h₅, h₆⟩
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
theorem exists_Ioo_eq_iInter_Ioo {q : ℕ} [Nonempty (Fin q)] (A B : Fin q → ℝ)
    (hA : ∀ i, A i < 0) (hB : ∀ i, 0 < B i) :
    ∃ a b : ℝ, (∀ t, t ∈ Set.Ioo a b ↔ ∀ i, t ∈ Set.Ioo (A i) (B i)) ∧ (0 : ℝ) ∈ Set.Ioo a b := by
  have hne : (Finset.univ : Finset (Fin q)).Nonempty := Finset.univ_nonempty
  have key : ∀ t, t ∈ Set.Ioo (Finset.univ.sup' hne A) (Finset.univ.inf' hne B) ↔
      ∀ i, t ∈ Set.Ioo (A i) (B i) := by
    intro t
    simp only [Set.mem_Ioo, Finset.sup'_lt_iff, Finset.lt_inf'_iff, Finset.mem_univ, true_implies]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  exact ⟨_, _, key, (key 0).2 fun i => ⟨hA i, hB i⟩⟩
end Plane
section Generic
variable {n : ℕ}
abbrev IndexPairPair (n : ℕ) : Type :=
  {p : Fin n × Fin n × Fin n × Fin n // p.1 ≠ p.2.1 ∧ p.2.2.1 ≠ p.2.2.2}
def nonOrthogonalSet (p : IndexPairPair n) : Set (Fin n → RealPlane) :=
  {y | inner ℝ (y p.1.1 - y p.1.2.1) (y p.1.2.2.1 - y p.1.2.2.2) ≠ 0}
theorem mem_genericTuples_iff (y : Fin n → RealPlane) :
    y ∈ genericTuples n ↔
      ∀ i j k l : Fin n, i ≠ j → k ≠ l → inner ℝ (y i - y j) (y k - y l) ≠ 0 := by
  constructor
  · rintro ⟨hinj, h⟩ i j k l hij hkl
    have hd : ∀ a b : Fin n, a ≠ b → y a - y b ≠ 0 := fun a b hab hy =>
      hab (hinj (sub_eq_zero.1 hy))
    by_cases hs : ({i, j} : Finset (Fin n)) = {k, l}
    · have hi : i ∈ ({k, l} : Finset (Fin n)) := hs ▸ (by simp)
      have hj : j ∈ ({k, l} : Finset (Fin n)) := hs ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact absurd rfl hij
      · exact inner_self_ne_zero.2 (hd _ _ hij)
      · rw [← neg_sub (y _) (y _), inner_neg_left]
        exact neg_ne_zero.2 (inner_self_ne_zero.2 (hd _ _ hkl))
      · exact absurd rfl hij
    · exact h i j k l hij hkl hs
  · intro h
    refine ⟨fun i j hy => ?_, fun i j k l hij hkl _ => h i j k l hij hkl⟩
    by_contra hne
    exact h i j i j hne hne (by rw [hy, sub_self, inner_zero_left])
theorem genericTuples_eq_iInter :
    genericTuples n = ⋂ p : IndexPairPair n, nonOrthogonalSet p := by
  ext y
  rw [mem_genericTuples_iff, Set.mem_iInter]
  exact ⟨fun h p => h _ _ _ _ p.2.1 p.2.2, fun h i j k l hij hkl => h ⟨(i, j, k, l), hij, hkl⟩⟩
theorem isOpen_nonOrthogonalSet (p : IndexPairPair n) : IsOpen (nonOrthogonalSet p) := by
  refine isOpen_ne_fun ?_ continuous_const
  fun_prop
def collinearTuple (n : ℕ) : Fin n → RealPlane :=
  fun a => !₂[((a : ℕ) : ℝ), 0]
theorem inner_collinearTuple_ne_zero {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) :
    inner ℝ (collinearTuple n i - collinearTuple n j)
      (collinearTuple n k - collinearTuple n l) ≠ 0 := by
  have h₁ : ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hij (Fin.ext (by exact_mod_cast h))
  have h₂ : ((k : ℕ) : ℝ) - ((l : ℕ) : ℝ) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hkl (Fin.ext (by exact_mod_cast h))
  rw [inner_eq_coord_sum]
  simpa [collinearTuple] using And.intro h₁ h₂
theorem dense_nonOrthogonalSet (p : IndexPairPair n) : Dense (nonOrthogonalSet p) := by
  obtain ⟨⟨i, j, k, l⟩, hij, hkl⟩ := p
  intro y
  set w := collinearTuple n
  set c : ℝ := inner ℝ (w i - w j) (w k - w l) with hc
  have hc0 : c ≠ 0 := inner_collinearTuple_ne_zero hij hkl
  set A : ℝ := inner ℝ (y i - y j) (y k - y l) with hA
  set B : ℝ := inner ℝ (y i - y j) (w k - w l) + inner ℝ (w i - w j) (y k - y l) with hB
  have hP : ∀ t : ℝ, inner ℝ ((y + t • w) i - (y + t • w) j) ((y + t • w) k - (y + t • w) l) =
      c * t ^ 2 + B * t + A := by
    intro t
    have e₁ : (y + t • w) i - (y + t • w) j = (y i - y j) + t • (w i - w j) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_sub]
      abel
    have e₂ : (y + t • w) k - (y + t • w) l = (y k - y l) + t • (w k - w l) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_sub]
      abel
    rw [e₁, e₂]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hc, hB,
      hA]
    ring
  let Q : Polynomial ℝ := Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C B * Polynomial.X +
    Polynomial.C A
  have hQ : Q ≠ 0 := by
    intro h
    have := congrArg (fun r => Polynomial.coeff r 2) h
    simp [Q] at this
    exact hc0 this
  have hfin : {t : ℝ | Q.IsRoot t}.Finite := Polynomial.finite_setOfPred_isRoot hQ
  have hnear : ({t : ℝ | Q.IsRoot t} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hfin.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), y + t • w ∈
      nonOrthogonalSet (⟨(i, j, k, l), hij, hkl⟩ : IndexPairPair n) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin] with t h₁ h₂
    show inner ℝ ((y + t • w) i - (y + t • w) j) ((y + t • w) k - (y + t • w) l) ≠ 0
    rw [hP]
    intro h₀
    refine h₁ ⟨?_, h₂⟩
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, Q, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact h₀
  have htend : Tendsto (fun t : ℝ => y + t • w) (𝓝[≠] (0 : ℝ)) (𝓝 y) := by
    have : Tendsto (fun t : ℝ => y + t • w) (𝓝 (0 : ℝ)) (𝓝 (y + (0 : ℝ) • w)) :=
      (Continuous.tendsto (by fun_prop) _)
    simpa using this.mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto htend hev
theorem isOpen_genericTuples : IsOpen (genericTuples n) := by
  rw [genericTuples_eq_iInter]
  exact isOpen_iInter_of_finite isOpen_nonOrthogonalSet
theorem dense_genericTuples : Dense (genericTuples n) := by
  rw [genericTuples_eq_iInter]
  exact dense_iInter_of_isOpen isOpen_nonOrthogonalSet dense_nonOrthogonalSet
theorem mapPoints_rotate_mem_genericTuples {y : Fin n → RealPlane}
    (hy : y ∈ genericTuples n) (t : ℝ) :
    mapPoints (rotate t) y ∈ genericTuples n := by
  rw [mem_genericTuples_iff] at hy ⊢
  intro i j k l hij hkl
  simp only [mapPoints, ← rotate_sub, inner_rotate_rotate]
  exact hy i j k l hij hkl
theorem mapPoints_rotate_rotate (t s : ℝ) (y : Fin n → RealPlane) :
    mapPoints (rotate t) (mapPoints (rotate s) y) =
      mapPoints (rotate (s + t)) y := by
  funext i
  exact rotate_rotate t s (y i)
theorem mapPoints_rotate_zero (y : Fin n → RealPlane) :
    mapPoints (rotate 0) y = y := by
  funext i
  exact rotate_zero (y i)
theorem image_mapPoints_rotate_genericTuples (t : ℝ) :
    mapPoints (rotate t) '' genericTuples n = genericTuples n := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact mapPoints_rotate_mem_genericTuples hy t
  · intro y hy
    refine ⟨mapPoints (rotate (-t)) y, mapPoints_rotate_mem_genericTuples hy _, ?_⟩
    rw [mapPoints_rotate_rotate, neg_add_cancel, mapPoints_rotate_zero]
theorem genericTuples_subset_ordered {q : ℕ}
    (hOrd : orderedRealTuples q =
      {y | Function.Injective (fun i => y i 0) ∨ Function.Injective (fun i => y i 1)}) :
    genericTuples (q + 1) ⊆ orderedRealTuples q := by
  intro y hy
  rw [mem_genericTuples_iff] at hy
  rw [hOrd]
  by_contra hnot
  simp only [Set.mem_ofPred_eq, not_or, Function.Injective, not_forall] at hnot
  obtain ⟨⟨i, j, h₀, hij⟩, ⟨k, l, h₁, hkl⟩⟩ := hnot
  refine hy i j k l hij hkl ?_
  rw [inner_eq_coord_sum]
  have h₀' : y i 0 = y j 0 := h₀
  have h₁' : y k 1 = y l 1 := h₁
  simp only [PiLp.sub_apply]
  rw [h₀', h₁']
  ring
end Generic
section Holomorphy
theorem continuous_pairTupleEquiv (p : ℕ) : Continuous (pairTupleEquiv p) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.continuous_pairTupleEquiv <;> assumption
theorem continuousOn_of_holomorphicOnTuples {p : ℕ} {O : Set (Fin p → ℂ × ℂ)}
    {f : (Fin p → ℂ × ℂ) → ℂ} (h : HolomorphicOnTuples O f) : ContinuousOn f O := by
  have hc : ContinuousOn (scalarEquiv ∘ f ∘ (pairTupleEquiv p).symm)
      (pairTupleEquiv p '' O) := h.2.1
  have h₂ : ContinuousOn
      (fun z => (scalarEquiv ∘ f ∘ (pairTupleEquiv p).symm) (pairTupleEquiv p z)) O :=
    hc.comp (continuous_pairTupleEquiv p).continuousOn (Set.mapsTo_image _ _)
  have h₃ : ContinuousOn
      (fun z => (scalarEquiv ∘ f ∘ (pairTupleEquiv p).symm) (pairTupleEquiv p z) 0) O :=
    (continuous_apply 0).comp_continuousOn h₂
  refine h₃.congr fun z _ => ?_
  simp [scalarEquiv]
theorem differentiableOn_comp_curve {p : ℕ}
    (hmx : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {D : Set (Fin p → ℂ × ℂ)} {K : (Fin p → ℂ × ℂ) → ℂ} (hK : HolomorphicOnTuples D K)
    {c : ℂ → Fin p → ℂ × ℂ}
    (hc : Coordinates.ComplexCoordinates.IsHolomorphicVia scalarEquiv (pairTupleEquiv p)
      Set.univ c)
    {St : Set ℂ} (hSt : IsOpen St) (hmaps : ∀ ζ ∈ St, c ζ ∈ D) :
    DifferentiableOn ℂ (fun ζ => K (c ζ)) St := by
  have hK' : Coordinates.ComplexCoordinates.IsHolomorphicIn (pairTupleEquiv p '' D)
      (scalarEquiv ∘ K ∘ (pairTupleEquiv p).symm) := hK
  have hc' : Coordinates.ComplexCoordinates.IsHolomorphicIn (scalarEquiv '' Set.univ)
      (pairTupleEquiv p ∘ c ∘ scalarEquiv.symm) := hc
  have hopen : IsOpen (scalarEquiv '' St) := by
    rw [Equiv.image_eq_preimage_symm]
    exact hSt.preimage (continuous_apply (0 : Fin 1))
  have hsub : scalarEquiv '' St ⊆ scalarEquiv '' Set.univ :=
    Set.image_mono (Set.subset_univ _)
  have hg : Coordinates.ComplexCoordinates.IsHolomorphicIn (scalarEquiv '' St)
      (pairTupleEquiv p ∘ c ∘ scalarEquiv.symm) :=
    ⟨hopen, hc'.2.1.mono hsub, fun a ha => hc'.2.2 a (hsub ha)⟩
  have hmapsTo : Set.MapsTo (pairTupleEquiv p ∘ c ∘ scalarEquiv.symm)
      (scalarEquiv '' St) (pairTupleEquiv p '' D) := by
    rintro _ ⟨ζ, hζ, rfl⟩
    exact ⟨c ζ, hmaps ζ hζ, by simp⟩
  have hcomp := ((hmx.1 _ _ hK'.1).1 1 _ hK').2.2.2.1 1 _ _ hg hmapsTo
  intro ζ₀ hζ₀
  apply DifferentiableAt.differentiableWithinAt
  have hd := (hcomp.2.2 (scalarEquiv ζ₀) ⟨ζ₀, hζ₀, rfl⟩ 0).self_of_nhds
  have e : ∀ ξ : ℂ, (scalarEquiv ζ₀ + ξ • Coordinates.ComplexCoordinates.stdBasisVector 0 :
      Coordinates.ComplexCoordinates 1) = scalarEquiv (ζ₀ + ξ) := by
    intro ξ
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    simp [scalarEquiv, Coordinates.ComplexCoordinates.stdBasisVector]
  have hd₂ : DifferentiableAt ℂ (fun ξ => K (c (ζ₀ + ξ))) 0 := by
    refine ((differentiableAt_pi.1 hd) 0).congr_of_eventuallyEq (Eventually.of_forall fun ξ => ?_)
    simp only [Function.comp_apply]
    rw [e]
    simp [scalarEquiv]
  have hd₃ : DifferentiableAt ℂ (fun ξ => K (c (ζ₀ + ξ))) (ζ₀ - ζ₀) := by
    simpa using hd₂
  have hd₄ : DifferentiableAt ℂ ((fun ξ => K (c (ζ₀ + ξ))) ∘ fun ζ => ζ - ζ₀) ζ₀ :=
    DifferentiableAt.comp ζ₀ hd₃ (differentiableAt_id.sub_const ζ₀)
  simpa [Function.comp_def] using hd₄
def verticalStrip (a b : ℝ) : Set ℂ := {ζ | ζ.re ∈ Set.Ioo a b}
theorem isOpen_verticalStrip (a b : ℝ) : IsOpen (verticalStrip a b) :=
  isOpen_Ioo.preimage Complex.continuous_re
theorem isPreconnected_verticalStrip (a b : ℝ) : IsPreconnected (verticalStrip a b) := by
  have : verticalStrip a b = {ζ : ℂ | a < ζ.re} ∩ {ζ : ℂ | ζ.re < b} := rfl
  rw [this]
  exact ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt b)).isPreconnected
end Holomorphy
theorem tubeAngleInterval_eq_Ioo {q : ℕ} (hq : 1 ≤ q) {υ : rightAngleMultiples}
    {ς : Equiv.Perm (Fin (q + 1))}
    (hreal : ∀ a : RealPlane, embedPlane a ∈ rotatedForwardTube υ ↔
      inner ℝ (rotatedDirection υ) a > 0)
    {y : Fin (q + 1) → RealPlane} (hy : embedPlaneTuple y ∈ orderedTube υ ς) :
    ∃ a b : ℝ, tubeAngleInterval υ ς y = Set.Ioo a b ∧ (0 : ℝ) ∈ Set.Ioo a b := by
  have i₀ : Fin q := ⟨0, hq⟩
  have : Nonempty (Fin q) := ⟨i₀⟩
  set e := rotatedDirection υ with he
  have hmem : ∀ x : Fin (q + 1) → RealPlane, embedPlaneTuple x ∈ orderedTube υ ς ↔
      ∀ i : Fin q, 0 < inner ℝ e (x (ς i.succ) - x (ς i.castSucc)) := by
    intro x
    refine forall_congr' fun i => ?_
    have h : embedPlaneTuple x (ς i.succ) - embedPlaneTuple x (ς i.castSucc) =
        embedPlane (x (ς i.succ) - x (ς i.castSucc)) := by
      simp [embedPlaneTuple, embedPlane]
    rw [h, hreal]
  have hv := (hmem y).1 hy
  choose r ψ hr hψ hcos using fun i : Fin q => exists_cos_shift_form (hv i)
    (e 1 * (y (ς i.succ) - y (ς i.castSucc)) 0 - e 0 * (y (ς i.succ) - y (ς i.castSucc)) 1)
  obtain ⟨a, b, hab, h0⟩ := exists_Ioo_eq_iInter_Ioo (fun i => -(Real.pi / 2) - ψ i)
    (fun i => Real.pi / 2 - ψ i) (fun i => by have := (abs_lt.1 (hψ i)).1; linarith)
    (fun i => by have := (abs_lt.1 (hψ i)).2; linarith)
  refine ⟨a, b, ?_, h0⟩
  ext t
  rw [hab]
  have hrot : ∀ i : Fin q, inner ℝ e (mapPoints (rotate t) y (ς i.succ) -
      mapPoints (rotate t) y (ς i.castSucc)) = r i * Real.cos (ψ i + t) := by
    intro i
    show inner ℝ e (rotate t (y (ς i.succ)) - rotate t (y (ς i.castSucc))) = _
    rw [← rotate_sub, inner_rotate_right]
    exact hcos i t
  constructor
  · rintro ⟨ht, hm⟩ i
    have h₁ := (hmem _).1 hm i
    rw [hrot] at h₁
    exact (cos_add_pos_iff (hψ i) ht).1 ((mul_pos_iff_of_pos_left (hr i)).1 h₁)
  · intro h
    have ht : t ∈ Set.Ioo (-Real.pi) Real.pi := by
      obtain ⟨h₁, h₂⟩ := h i₀
      obtain ⟨h₃, h₄⟩ := abs_lt.1 (hψ i₀)
      constructor <;> linarith
    refine ⟨ht, (hmem _).2 fun i => ?_⟩
    rw [hrot]
    exact mul_pos (hr i) (Real.cos_pos_of_mem_Ioo
      (by obtain ⟨h₁, h₂⟩ := h i; constructor <;> linarith))
section Identity
variable {q : ℕ} {S : ConnFamily} {φ₀ : openingAngles} {φ : Fin (q + 1) → realLabels}
theorem complexBoostTuple_add_mul_I
    (hrot : ∀ ζ ζ' : ℂ, complexBoost ζ ∘ complexBoost ζ' = complexBoost (ζ + ζ') ∧
      complexBoost (ζ + ζ') = complexBoost ζ' ∘ complexBoost ζ)
    (hreal : ∀ (t : ℝ) (w : ℂ × ℂ), complexBoost (t : ℂ) w =
      (w.1 * (Real.cos t : ℂ) - w.2 * (Real.sin t : ℂ),
        w.1 * (Real.sin t : ℂ) + w.2 * (Real.cos t : ℂ)))
    (y : Fin (q + 1) → RealPlane) (t s : ℝ) :
    complexBoostTuple ((t : ℂ) + I * (s : ℂ)) (embedPlaneTuple y) =
      imagBoostTuple s (embedPlaneTuple (mapPoints (rotate t) y)) := by
  funext i
  have e₁ : embedPlane (rotate t (y i)) = complexBoost (t : ℂ) (embedPlane (y i)) := by
    rw [hreal]
    simp [embedPlane, rotate_apply_zero, rotate_apply_one]
  show complexBoost ((t : ℂ) + I * (s : ℂ)) (embedPlane (y i)) =
    complexBoost (I * (s : ℂ)) (embedPlane (rotate t (y i)))
  rw [e₁, add_comm, ← (hrot _ _).1]
  rfl
theorem expSum_eq_sum (F : Finset ℤ) (f : ℤ → ℂ) (s : ℝ) :
    ExpSums.expSum F (fun h => f h) s =
      ∑ h ∈ F, f h * Complex.exp (-(4 * (h : ℂ) * (s : ℂ))) := by
  unfold ExpSums.expSum
  rw [Finset.sum_coe_sort F (fun h => f h * Complex.exp (-4 * (h : ℂ) * (s : ℂ)))]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [show -4 * (h : ℂ) * (s : ℂ) = -(4 * (h : ℂ) * (s : ℂ)) by ring]
theorem rotationFactor_on_interval {υ : rightAngleMultiples} {ς : Equiv.Perm (Fin (q + 1))}
    (hmx : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hrot : ∀ ζ ζ' : ℂ, complexBoost ζ ∘ complexBoost ζ' = complexBoost (ζ + ζ') ∧
      complexBoost (ζ + ζ') = complexBoost ζ' ∘ complexBoost ζ)
    (hreal : ∀ (t : ℝ) (w : ℂ × ℂ), complexBoost (t : ℂ) w =
      (w.1 * (Real.cos t : ℂ) - w.2 * (Real.sin t : ℂ),
        w.1 * (Real.sin t : ℂ) + w.2 * (Real.cos t : ℂ)))
    (hstable : ∀ z ∈ orderedTube υ ς, ∀ s : ℝ,
      imagBoostTuple s z ∈ orderedTube υ ς)
    (hK : HolomorphicOnTuples (orderedTubeUnion q)
      (tubeUnionFunction S φ))
    (hexp : HasHarmonicExpansion S φ₀ φ (harmonicFamily S φ₀ φ))
    (hcoef : ∀ b b' : (Finset.Icc (-(maxFrequency S φ₀ (q + 1) : ℤ))
        (maxFrequency S φ₀ (q + 1) : ℤ)) → ℂ,
      (∀ s : ℝ, ExpSums.expSum _ b s = ExpSums.expSum _ b' s) → ∀ h, b h = b' h)
    {y : Fin (q + 1) → RealPlane}
    (hcurve : Coordinates.ComplexCoordinates.IsHolomorphicVia scalarEquiv (pairTupleEquiv (q + 1))
      Set.univ (fun ζ : ℂ => complexBoostTuple ζ (embedPlaneTuple y)))
    {a b : ℝ} (h0 : (0 : ℝ) ∈ Set.Ioo a b)
    (hmem : ∀ t ∈ Set.Ioo a b,
      embedPlaneTuple (mapPoints (rotate t) y) ∈ orderedTube υ ς) :
    ∀ t ∈ Set.Ioo a b, RotationFactor S φ₀ φ y t := by
  have hsubset : orderedTube υ ς ⊆ orderedTubeUnion q := fun z hz =>
    Set.mem_iUnion.2 ⟨υ, Set.mem_iUnion.2 ⟨ς, hz⟩⟩
  set F := Finset.Icc (-(maxFrequency S φ₀ (q + 1) : ℤ)) (maxFrequency S φ₀ (q + 1) : ℤ) with hF
  set x := embedPlaneTuple y with hx
  have hxy : mapPoints (rotate 0) y = y := mapPoints_rotate_zero y
  have hxmem : x ∈ orderedTube υ ς := by
    have := hmem 0 h0
    rwa [hxy] at this
  let g₁ : ℂ → ℂ := fun ζ => tubeUnionFunction S φ (complexBoostTuple ζ x)
  let g₂ : ℂ → ℂ := fun ζ => ∑ h ∈ F, harmonicFamily S φ₀ φ h x *
    Complex.exp (4 * I * (h : ℂ) * ζ)
  have hdecomp : ∀ ζ : ℂ, complexBoostTuple ζ x =
      imagBoostTuple ζ.im (embedPlaneTuple (mapPoints (rotate ζ.re) y)) := by
    intro ζ
    rw [← complexBoostTuple_add_mul_I hrot hreal y ζ.re ζ.im]
    congr 1
    apply Complex.ext <;> simp
  have hmaps : ∀ ζ ∈ verticalStrip a b, complexBoostTuple ζ x ∈ orderedTubeUnion q := by
    intro ζ hζ
    rw [hdecomp]
    exact hsubset (hstable _ (hmem _ hζ) _)
  have hd₁ : DifferentiableOn ℂ g₁ (verticalStrip a b) :=
    differentiableOn_comp_curve hmx hK hcurve (isOpen_verticalStrip a b) hmaps
  have hd₂ : Differentiable ℂ g₂ := by
    intro ζ
    simp only [g₂]
    fun_prop
  have han₁ : AnalyticOnNhd ℂ g₁ (verticalStrip a b) := hd₁.analyticOnNhd (isOpen_verticalStrip a b)
  have han₂ : AnalyticOnNhd ℂ g₂ (verticalStrip a b) :=
    hd₂.differentiableOn.analyticOnNhd (isOpen_verticalStrip a b)
  have h0St : (0 : ℂ) ∈ verticalStrip a b := by simpa [verticalStrip] using h0
  have himag : ∀ s : ℝ, g₁ (I * (s : ℂ)) = g₂ (I * (s : ℂ)) := by
    intro s
    have h := hexp x (hsubset hxmem) s
    refine h.trans (Finset.sum_congr rfl fun h' _ => ?_)
    congr 2
    linear_combination (-(4 * (h' : ℂ) * (s : ℂ))) * Complex.I_sq
  have hfreq : ∃ᶠ ζ in 𝓝[≠] (0 : ℂ), g₁ ζ = g₂ ζ := by
    have htend : Tendsto (fun s : ℝ => I * (s : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun s : ℝ => I * (s : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (I * ((0 : ℝ) : ℂ))) :=
          Continuous.tendsto (by fun_prop) _
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simpa using hs
    exact htend.frequently (Eventually.frequently (Eventually.of_forall himag))
  have heq : Set.EqOn g₁ g₂ (verticalStrip a b) :=
    han₁.eqOn_of_preconnected_of_frequently_eq han₂ (isPreconnected_verticalStrip a b) h0St hfreq
  intro t ht
  have hsum : ∀ s : ℝ,
      ∑ h ∈ F, harmonicFamily S φ₀ φ h (embedPlaneTuple (mapPoints (rotate t) y)) *
          Complex.exp (-(4 * (h : ℂ) * (s : ℂ))) =
        ∑ h ∈ F, (harmonicFamily S φ₀ φ h x * Complex.exp (4 * I * (h : ℂ) * (t : ℂ))) *
          Complex.exp (-(4 * (h : ℂ) * (s : ℂ))) := by
    intro s
    have hζ : ((t : ℂ) + I * (s : ℂ)) ∈ verticalStrip a b := by simpa [verticalStrip] using ht
    have h₁ := heq hζ
    simp only [g₁, g₂] at h₁
    rw [complexBoostTuple_add_mul_I hrot hreal y t s] at h₁
    rw [← hexp _ (hsubset (hmem t ht)) s, h₁]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [mul_assoc (harmonicFamily S φ₀ φ h' x), ← Complex.exp_add]
    congr 2
    linear_combination (4 * (h' : ℂ) * (s : ℂ)) * Complex.I_sq
  have hall := hcoef
    (fun h => harmonicFamily S φ₀ φ h (embedPlaneTuple (mapPoints (rotate t) y)))
    (fun h => harmonicFamily S φ₀ φ h x * Complex.exp (4 * I * (((h : ℤ) : ℂ)) * (t : ℂ)))
    (fun s => by
      rw [expSum_eq_sum F
          (fun h => harmonicFamily S φ₀ φ h (embedPlaneTuple (mapPoints (rotate t) y))) s,
        expSum_eq_sum F
          (fun h => harmonicFamily S φ₀ φ h x * Complex.exp (4 * I * (h : ℂ) * (t : ℂ))) s]
      exact hsum s)
  intro h
  by_cases hh : |h| ≤ (maxFrequency S φ₀ (q + 1) : ℤ)
  · have hmemF : h ∈ F := Finset.mem_Icc.2 (abs_le.1 hh)
    simp only [indexHarmonic, tubeUnionHarmonic, if_pos hh]
    rw [mul_comm]
    exact hall ⟨h, hmemF⟩
  · simp only [indexHarmonic, tubeUnionHarmonic, if_neg hh, mul_zero]
theorem rotationFactor_of_generic (hi : CovariantOnTubeInterval S φ₀ φ)
    (hsub : genericTuples (q + 1) ⊆ orderedRealTuples q)
    {y : Fin (q + 1) → RealPlane} (hy : y ∈ genericTuples (q + 1))
    (t : ℝ) : RotationFactor S φ₀ φ y t := by
  intro h
  let c : ℝ → ℂ := fun τ => indexHarmonic S φ₀ φ h (embedPlaneTuple (mapPoints (rotate τ) y))
  let g : ℝ → ℂ := fun τ => Complex.exp (-(4 * I * (h : ℂ) * (τ : ℂ))) * c τ
  have hloc : IsLocallyConstant g := by
    refine (IsLocallyConstant.iff_eventually_eq g).2 fun τ₀ => ?_
    have hord := hsub (mapPoints_rotate_mem_genericTuples hy τ₀)
    obtain ⟨υ, hυ⟩ := Set.mem_iUnion.1 hord
    obtain ⟨ς, hς⟩ := Set.mem_iUnion.1 hυ
    obtain ⟨⟨a, b, hab, h0⟩, hcov⟩ := hi _ hord υ ς hς
    have hnear : ∀ᶠ τ in 𝓝 τ₀, τ - τ₀ ∈ Set.Ioo a b := by
      have hc : ContinuousAt (fun τ : ℝ => τ - τ₀) τ₀ := by fun_prop
      have h₂ : Set.Ioo a b ∈ 𝓝 ((fun τ : ℝ => τ - τ₀) τ₀) := by
        simp only [sub_self]
        exact Ioo_mem_nhds h0.1 h0.2
      exact hc h₂
    filter_upwards [hnear] with τ hτ
    have h₁ := hcov (τ - τ₀) (hab ▸ hτ) h
    rw [mapPoints_rotate_rotate, add_sub_cancel] at h₁
    show Complex.exp (-(4 * I * (h : ℂ) * (τ : ℂ))) * c τ =
      Complex.exp (-(4 * I * (h : ℂ) * (τ₀ : ℂ))) * c τ₀
    simp only [c]
    rw [h₁, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hconst : g t = g 0 := hloc.apply_eq_of_preconnectedSpace t 0
  simp only [g, c, mapPoints_rotate_zero, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    one_mul] at hconst
  rw [← hconst, ← mul_assoc, ← Complex.exp_add]
  simp
theorem covariantBetweenOrdered_of
    (hi : CovariantOnTubeInterval S φ₀ φ)
    (hsub : genericTuples (q + 1) ⊆ orderedRealTuples q)
    (hopen : IsOpen (orderedRealTuples q))
    (hcont : ∀ h : ℤ, ContinuousOn (indexHarmonic S φ₀ φ h) (orderedTubeUnion q)) :
    CovariantBetweenOrdered S φ₀ φ := by
  intro y hy t hty h
  have hrotc : Continuous (mapPoints (n := q + 1) (RealPlane.rotate t)) :=
    continuous_pi fun i => (continuous_rotate t).comp (continuous_apply i)
  have hofc : Continuous (embedPlaneTuple : (Fin (q + 1) → RealPlane) → _) := by
    unfold embedPlaneTuple embedPlane
    fun_prop
  set O : Set (Fin (q + 1) → RealPlane) :=
    orderedRealTuples q ∩ mapPoints (rotate t) ⁻¹' orderedRealTuples q with hO
  have hOopen : IsOpen O := hopen.inter (hopen.preimage hrotc)
  have hyO : y ∈ O := ⟨hy, hty⟩
  let f₁ : (Fin (q + 1) → RealPlane) → ℂ := fun y' =>
    indexHarmonic S φ₀ φ h (embedPlaneTuple (mapPoints (rotate t) y'))
  let f₂ : (Fin (q + 1) → RealPlane) → ℂ := fun y' =>
    Complex.exp (4 * I * (h : ℂ) * (t : ℂ)) * indexHarmonic S φ₀ φ h (embedPlaneTuple y')
  have hf₁ : ContinuousOn f₁ O :=
    (hcont h).comp (hofc.comp hrotc).continuousOn fun y' hy' => hy'.2
  have hf₂ : ContinuousOn f₂ O :=
    continuousOn_const.mul ((hcont h).comp hofc.continuousOn fun y' hy' => hy'.1)
  have hcl : y ∈ closure (O ∩ genericTuples (q + 1)) :=
    dense_genericTuples.open_subset_closure_inter hOopen hyO
  have hne := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have t₁ : Tendsto f₁ (𝓝[O ∩ genericTuples (q + 1)] y) (𝓝 (f₁ y)) :=
    ((hf₁.continuousAt (hOopen.mem_nhds hyO)).tendsto).mono_left nhdsWithin_le_nhds
  have t₂ : Tendsto f₂ (𝓝[O ∩ genericTuples (q + 1)] y) (𝓝 (f₂ y)) :=
    ((hf₂.continuousAt (hOopen.mem_nhds hyO)).tendsto).mono_left nhdsWithin_le_nhds
  have heq : f₁ =ᶠ[𝓝[O ∩ genericTuples (q + 1)] y] f₂ := by
    filter_upwards [self_mem_nhdsWithin] with y' hy'
    exact rotationFactor_of_generic hi hsub hy'.2 t h
  exact tendsto_nhds_unique (t₁.congr' heq) t₂
end Identity
theorem holds (hrules : ForwardTube.RotationRules.Holds)
    (hone : UnionKernel.Holds) (hharm : TubeUnionHarmonics.Holds)
    (hexps : ExpSums.ExpSumsDetermined)
    (hmx : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) : Holds := by
  intro m S d q hq φ
  obtain ⟨hL, -, -, hHol, hTube, -⟩ := hrules
  have hrot := hL.2.2.2.2.2.1
  have hreal := hL.2.2.2.2.2.2.2.1
  have hcurves := fun y : Fin (q + 1) → RealPlane => (hHol.2 q hq).2 (embedPlaneTuple y)
  obtain ⟨hfam, -, -, -⟩ := hharm m S d q hq φ
  obtain ⟨hexp, -, hhol⟩ := hfam
  have hones := fun (υ : rightAngleMultiples) (ς : Equiv.Perm (Fin (q + 1))) =>
    hone m S d q hq φ υ υ ς ς
  obtain ⟨-, -, -, -, -, hunique, -, hord⟩ := hones rightAngleZero 1
  have hK := hunique.2.2.2.1
  have hF : (Finset.Icc (-(maxFrequency S d.angle (q + 1) : ℤ))
      (maxFrequency S d.angle (q + 1) : ℤ)).Nonempty :=
    ⟨0, Finset.mem_Icc.2 ⟨by simp, by simp⟩⟩
  have hcoef := (hexps _ hF).2.2.1
  have hi : CovariantOnTubeInterval S d.angle φ := by
    intro y _ υ ς hy
    obtain ⟨a, b, hab, h0⟩ := tubeAngleInterval_eq_Ioo hq ((hTube.2.2.1 υ).2.2.2.2.2) hy
    refine ⟨⟨a, b, hab, h0⟩, ?_⟩
    rw [hab]
    refine rotationFactor_on_interval (υ := υ) (ς := ς) hmx hrot hreal ?_ hK hexp hcoef
      (hcurves y) h0 ?_
    · exact fun z hz s => ((hones υ ς).2.1.2.2.2 z hz).2.1 s
    · intro t ht
      rw [← hab] at ht
      exact ht.2
  have hsub := genericTuples_subset_ordered hord.1
  have hopen : IsOpen (orderedRealTuples q) := hord.2.2.2.2.2.2.2.1
  refine ⟨hi, ⟨isOpen_genericTuples, dense_genericTuples, image_mapPoints_rotate_genericTuples,
    hsub⟩, ?_⟩
  refine covariantBetweenOrdered_of hi hsub hopen fun h => ?_
  by_cases hh : |h| ≤ (maxFrequency S d.angle (q + 1) : ℤ)
  · refine (continuousOn_of_holomorphicOnTuples (hhol h hh)).congr fun z _ => ?_
    simp [indexHarmonic, tubeUnionHarmonic, hh]
  · refine continuousOn_const (c := (0 : ℂ)).congr fun z _ => ?_
    simp [indexHarmonic, tubeUnionHarmonic, hh]
end EuclideanFunctionals.HarmonicRotationCovariance
end YangMills.Construction
end
