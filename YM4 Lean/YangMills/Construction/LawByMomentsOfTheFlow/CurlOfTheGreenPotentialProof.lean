import YangMills.Construction.LawByMomentsOfTheFlow.CurlOfTheGreenPotential
import YangMills.Construction.LawByMomentsOfTheFlow.PairingOfACurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
variable {A : Type} [CommRing A]
private theorem plaquetteCurlAt_antisymm (B : (Fin 4 → A) → Fin 4 → ℝ) (x : Fin 4 → A) (a b : Fin 4) :
    plaquetteCurlAt B x a b = -plaquetteCurlAt B x b a := by
  unfold plaquetteCurlAt
  ring
private theorem plaquetteCurlAt_greenPlaquettePotential (g : (Fin 4 → A) → ℝ) (y x : Fin 4 → A)
    (q r : CyclicFormula.OrderedDirectionPair) :
    plaquetteCurlAt (greenPlaquettePotential g y q.1.1 q.1.2) x r.1.1 r.1.2 =
      planePairEntry (secondDiffMatrix g (x - y)) r q := by
  obtain ⟨⟨a, b⟩, -⟩ := r
  obtain ⟨⟨c, d⟩, -⟩ := q
  have h1 : ∀ u : Fin 4 → A, x + u - y = x - y + u := fun u => by abel
  simp only [plaquetteCurlAt, greenPlaquettePotential, planePairEntry, secondDiffMatrix,
    FourDimKernel.mixedSecondDiff, forwardDiff, backwardDiff, h1]
  generalize x - y = w
  split_ifs <;> ring
private theorem discreteLaplacian_eq_sum (f : (Fin 4 → A) → ℝ) (z : Fin 4 → A) :
    discreteLaplacian f z = ∑ ν, (2 * f z - f (z + unitVector ν) - f (z - unitVector ν)) := by
  simp only [discreteLaplacian, backwardDiff, forwardDiff, Pi.neg_apply, Finset.sum_apply,
    sub_add_cancel, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring
private theorem codiff_plaquetteCurlAt (B : (Fin 4 → A) → Fin 4 → ℝ) (x : Fin 4 → A) (μ : Fin 4) :
    ∑ ν, (plaquetteCurlAt B x μ ν - plaquetteCurlAt B (x - unitVector ν) μ ν) =
      ∑ ν, (2 * B x μ - B (x + unitVector ν) μ - B (x - unitVector ν) μ) +
        (∑ ν, (B (x + unitVector μ) ν - B (x + unitVector μ - unitVector ν) ν) -
          ∑ ν, (B x ν - B (x - unitVector ν) ν)) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have e : x - unitVector ν + unitVector μ = x + unitVector μ - unitVector ν := by abel
  simp only [plaquetteCurlAt, sub_add_cancel, e]
  ring
private theorem divergence_greenPlaquettePotential (g : (Fin 4 → A) → ℝ) (y : Fin 4 → A) (c d : Fin 4)
    (x : Fin 4 → A) :
    ∑ ν, (greenPlaquettePotential g y c d x ν - greenPlaquettePotential g y c d (x - unitVector ν) ν) = 0 := by
  simp only [greenPlaquettePotential, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have e1 : x - unitVector d - y - unitVector c = x - unitVector c - y - unitVector d := by abel
  have e2 : x - unitVector d - y = x - y - unitVector d := by abel
  have e3 : x - unitVector c - y = x - y - unitVector c := by abel
  rw [e1, e2, e3]
  ring
open Classical in
private theorem codiff_curl_greenPlaquettePotential (g : (Fin 4 → A) → ℝ) (κ : ℝ)
    (hL : ∀ z : Fin 4 → A, discreteLaplacian g z = (if z = 0 then 1 else 0) - κ)
    (y : Fin 4 → A) (c d : Fin 4) (x : Fin 4 → A) (μ : Fin 4) :
    ∑ ν, (plaquetteCurlAt (greenPlaquettePotential g y c d) x μ ν -
        plaquetteCurlAt (greenPlaquettePotential g y c d) (x - unitVector ν) μ ν) =
      (if μ = d then (if x - y - unitVector c = 0 then (1 : ℝ) else 0) - (if x - y = 0 then 1 else 0) else 0) -
        (if μ = c then (if x - y - unitVector d = 0 then (1 : ℝ) else 0) - (if x - y = 0 then 1 else 0) else 0) := by
  rw [codiff_plaquetteCurlAt, divergence_greenPlaquettePotential, divergence_greenPlaquettePotential,
    sub_zero, add_zero]
  have hT : ∀ u : Fin 4 → A, ∑ ν, (2 * g (x - y - u) - g (x + unitVector ν - y - u) - g (x - unitVector ν - y - u)) =
      (if x - y - u = 0 then 1 else 0) - κ := by
    intro u
    rw [← hL, discreteLaplacian_eq_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have e1 : x + unitVector ν - y - u = x - y - u + unitVector ν := by abel
    have e2 : x - unitVector ν - y - u = x - y - u - unitVector ν := by abel
    rw [e1, e2]
  have hT0 := hT 0
  simp only [sub_zero] at hT0
  simp only [greenPlaquettePotential]
  have hsplit : ∀ ν, (2 * ((if μ = d then g (x - y - unitVector c) - g (x - y) else 0) -
        (if μ = c then g (x - y - unitVector d) - g (x - y) else 0)) -
      ((if μ = d then g (x + unitVector ν - y - unitVector c) - g (x + unitVector ν - y) else 0) -
        (if μ = c then g (x + unitVector ν - y - unitVector d) - g (x + unitVector ν - y) else 0)) -
      ((if μ = d then g (x - unitVector ν - y - unitVector c) - g (x - unitVector ν - y) else 0) -
        (if μ = c then g (x - unitVector ν - y - unitVector d) - g (x - unitVector ν - y) else 0))) =
      (if μ = d then (1 : ℝ) else 0) *
          ((2 * g (x - y - unitVector c) - g (x + unitVector ν - y - unitVector c) -
              g (x - unitVector ν - y - unitVector c)) -
            (2 * g (x - y) - g (x + unitVector ν - y) - g (x - unitVector ν - y))) -
        (if μ = c then (1 : ℝ) else 0) *
          ((2 * g (x - y - unitVector d) - g (x + unitVector ν - y - unitVector d) -
              g (x - unitVector ν - y - unitVector d)) -
            (2 * g (x - y) - g (x + unitVector ν - y) - g (x - unitVector ν - y))) := by
    intro ν
    split_ifs <;> ring
  have hD : ∀ u : Fin 4 → A, ∑ ν, ((2 * g (x - y - u) - g (x + unitVector ν - y - u) - g (x - unitVector ν - y - u)) -
      (2 * g (x - y) - g (x + unitVector ν - y) - g (x - unitVector ν - y))) =
      ((if x - y - u = 0 then 1 else 0) - κ) - ((if x - y = 0 then 1 else 0) - κ) := fun u => by
    rw [Finset.sum_sub_distrib, hT u, hT0]
  rw [Finset.sum_congr rfl fun ν _ => hsplit ν, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hD, hD]
  split_ifs <;> ring
private theorem summable_mul_shift_of_finite_support {B : (Fin 4 → A) → Fin 4 → ℝ}
    (hB : (Function.support (Function.uncurry B)).Finite) (μ : Fin 4) (φ : (Fin 4 → A) → ℝ)
    (u : Fin 4 → A) : Summable (fun x => φ x * B (x + u) μ) := by
  refine summable_of_hasFiniteSupport ?_
  have hinj : Function.Injective (fun x : Fin 4 → A => (x + u, μ)) := fun x x' h => by
    simpa using congrArg Prod.fst h
  refine (hB.preimage hinj.injOn).subset fun x hx => ?_
  simp only [Function.mem_support, Set.mem_preimage, Function.uncurry_apply_pair] at hx ⊢
  exact right_ne_zero_of_mul hx
private theorem summable_mul_of_finite_support {B : (Fin 4 → A) → Fin 4 → ℝ}
    (hB : (Function.support (Function.uncurry B)).Finite) (μ : Fin 4) (φ : (Fin 4 → A) → ℝ) :
    Summable (fun x => φ x * B x μ) := by
  simpa using summable_mul_shift_of_finite_support hB μ φ 0
open Classical in
theorem curlGreenPotentialStatement_of_pairing (hP : curvaturePairingSummationByParts) :
    curlGreenPotentialStatement := by
  intro A _ g y q
  refine ⟨fun x r => plaquetteCurlAt_greenPlaquettePotential g y x q r, fun κ hL B hB => ?_⟩
  obtain ⟨⟨c, d⟩, hq⟩ := q
  have hs : ∀ (a b e : Fin 4) (u : Fin 4 → A),
      Summable fun x => plaquetteCurlAt (greenPlaquettePotential g y c d) (x - u) a b * B x e := fun a b e u =>
    summable_mul_of_finite_support hB e _
  show ∑' x, ∑ r : CyclicFormula.OrderedDirectionPair,
      plaquetteCurlAt (greenPlaquettePotential g y c d) x r.1.1 r.1.2 * plaquetteCurlAt B x r.1.1 r.1.2 =
    plaquetteCurlAt B y c d
  rw [hP A (fun x a b => plaquetteCurlAt (greenPlaquettePotential g y c d) x a b) B
    (fun x a b => plaquetteCurlAt_antisymm _ x a b) hs]
  have hone : ∀ (μ : Fin 4) (w : Fin 4 → A),
      HasSum (fun x => B x μ * (if x - y - w = 0 then (1 : ℝ) else 0)) (B (y + w) μ) := by
    intro μ w
    have h := hasSum_ite_eq (y + w) (B (y + w) μ)
    have e : (fun x => B x μ * (if x - y - w = 0 then (1 : ℝ) else 0)) =
        fun x => if x = y + w then B (y + w) μ else 0 := by
      funext x
      by_cases hx : x = y + w
      · subst hx
        have : y + w - y - w = 0 := by abel
        simp [this]
      · have : x - y - w ≠ 0 := fun h => hx (by
          rw [sub_sub, sub_eq_zero] at h
          exact h)
        simp [hx, this]
    rw [e]
    exact h
  have hone0 : ∀ μ : Fin 4, HasSum (fun x => B x μ * (if x - y = 0 then (1 : ℝ) else 0)) (B y μ) := by
    intro μ
    simpa using hone μ 0
  have e : ∀ x, ∑ μ, B x μ * ∑ ν, (plaquetteCurlAt (greenPlaquettePotential g y c d) x μ ν -
      plaquetteCurlAt (greenPlaquettePotential g y c d) (x - unitVector ν) μ ν) =
      B x d * (if x - y - unitVector c = 0 then (1 : ℝ) else 0) - B x d * (if x - y = 0 then (1 : ℝ) else 0) -
        (B x c * (if x - y - unitVector d = 0 then (1 : ℝ) else 0) -
          B x c * (if x - y = 0 then (1 : ℝ) else 0)) := by
    intro x
    simp only [codiff_curl_greenPlaquettePotential g κ hL y c d, mul_sub, Finset.sum_sub_distrib, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [e]
  rw [(((hone d (unitVector c)).sub (hone0 d)).sub ((hone c (unitVector d)).sub (hone0 c))).tsum_eq]
  unfold plaquetteCurlAt
  ring
end YangMills.Construction.MomentLaw
end
