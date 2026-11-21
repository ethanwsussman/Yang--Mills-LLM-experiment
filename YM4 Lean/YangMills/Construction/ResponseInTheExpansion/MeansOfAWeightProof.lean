import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ResponseInTheExpansion.MeansOfAWeight
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps BlockOffsets
namespace WeightedResponses
theorem sum_indicator_add_eq_one {m : ℕ} [NeZero m] (y v : TorusSite m) :
    ∑ x : TorusSite m, (if x + v = y then (1 : ℝ) else 0) = 1 := by
  have key : ∀ x : TorusSite m, (x + v = y) ↔ (x = y - v) := fun x => by
    constructor
    · intro hx
      rw [← hx]
      simp
    · intro hx
      rw [hx]
      simp
  simp only [key]
  simp
theorem sum_vertexMultiplicity_plaquette {m : ℕ} [NeZero m] (y : TorusSite m) (μ ν : Fin 4) :
    ∑ x : TorusSite m, vertexMultiplicity y (x, μ, ν) = 4 := by
  have hmult : ∀ x : TorusSite m, vertexMultiplicity y (x, μ, ν) = (if x = y then (1 : ℝ) else 0) +
      (if x + unitStep m μ = y then 1 else 0) + (if x + unitStep m ν = y then 1 else 0) +
      (if x + (unitStep m μ + unitStep m ν) = y then 1 else 0) := by
    intro x
    simp only [vertexMultiplicity, plaquetteVertices, List.count_cons, List.count_nil, ← add_assoc,
      beq_iff_eq]
    push_cast
    ring_nf
  simp only [hmult, Finset.sum_add_distrib, sum_indicator_add_eq_one]
  simp
  norm_num
theorem sum_vertexMultiplicity_plaquettesIn_univ {m : ℕ} [NeZero m] (y : TorusSite m) :
    ∑ p ∈ plaquettesIn (n := m) Finset.univ, vertexMultiplicity y p = 24 := by
  have hfilter : plaquettesIn (n := m) Finset.univ =
      Finset.univ.filter fun p : TorusPlaquette m => p.2.1 < p.2.2 := by
    ext p
    simp [plaquettesIn]
  rw [hfilter, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have hinner : ∀ q : Fin 4 × Fin 4, ∑ x : TorusSite m,
      (if (x, q).2.1 < (x, q).2.2 then vertexMultiplicity y (x, q) else 0) =
      if q.1 < q.2 then (4 : ℝ) else 0 := by
    intro q
    by_cases hq : q.1 < q.2
    · simp only [hq, if_true]
      exact sum_vertexMultiplicity_plaquette y q.1 q.2
    · simp [hq]
  simp only [hinner]
  rw [← Finset.sum_filter, Finset.sum_const]
  have hcard : (Finset.univ.filter fun q : Fin 4 × Fin 4 => q.1 < q.2).card = 6 := by decide
  rw [hcard]
  norm_num
theorem blockMean_one_and_linear_and_local (L : ℕ) [NeZero L] (hodd : Odd L) :
    (t n : ℕ) → [NeZero n] → (y : TorusSite n) →
    blockMean L t n y (constOneWeight _) = 1 ∧
    (∀ (a b : ℝ) (f g : PlaquetteWeight (fineSide L t n)),
      blockMean L t n y (fun p => a * f p + b * g p) = a * blockMean L t n y f + b * blockMean L t n y g) ∧
    ∀ f g : PlaquetteWeight (fineSide L t n), (∀ p, IsPlaquetteAt L t y p → f p = g p) →
      blockMean L t n y f = blockMean L t n y g
  | 0, n, _, y => by
    refine ⟨?_, fun a b f g => ?_, fun f g hfg => ?_⟩
    · show (1 / 24 : ℝ) * ∑ p ∈ plaquettesIn (n := n) Finset.univ, vertexMultiplicity y p * 1 = 1
      simp only [mul_one]
      rw [sum_vertexMultiplicity_plaquettesIn_univ]
      norm_num
    · show (1 / 24 : ℝ) * ∑ p ∈ plaquettesIn (n := n) Finset.univ, vertexMultiplicity y p * (a * f p + b * g p) =
        a * ((1 / 24 : ℝ) * ∑ p ∈ plaquettesIn (n := n) Finset.univ, vertexMultiplicity y p * f p) +
          b * ((1 / 24 : ℝ) * ∑ p ∈ plaquettesIn (n := n) Finset.univ, vertexMultiplicity y p * g p)
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    · show (1 / 24 : ℝ) * ∑ p ∈ plaquettesIn (n := n) Finset.univ, vertexMultiplicity y p * f p =
        (1 / 24 : ℝ) * ∑ p ∈ plaquettesIn (n := n) Finset.univ, vertexMultiplicity y p * g p
      congr 1
      refine Finset.sum_congr rfl fun p hp => ?_
      by_cases hv : y ∈ plaquetteVertices p.1 p.2.1 p.2.2
      · have hlt : p.2.1 < p.2.2 := by
          simp only [plaquettesIn, Finset.mem_filter] at hp
          exact hp.2.1
        have hp' : f p = g p := hfg p ⟨hlt, y, hv, Finset.mem_singleton_self y⟩
        rw [hp']
      · have hzero : vertexMultiplicity y p = 0 := by
          simp only [vertexMultiplicity]
          rw [List.count_eq_zero_of_not_mem hv]
          simp
        rw [hzero, zero_mul, zero_mul]
  | t + 1, n, _, Y => by
    refine ⟨?_, fun a b f g => ?_, fun f g hfg => ?_⟩
    · show ((L : ℝ) ^ 4)⁻¹ * ∑ z ∈ sitesInBlocks L {Y}, blockMean L t (n * L) z (constOneWeight _) = 1
      have hone : ∀ z ∈ sitesInBlocks L {Y}, blockMean L t (n * L) z (constOneWeight _) = 1 := fun z _ =>
        (blockMean_one_and_linear_and_local L hodd t (n * L) z).1
      rw [Finset.sum_congr rfl hone, sum_sitesInBlocks hodd Y fun _ => (1 : ℝ)]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [card_centredCube hodd]
      push_cast
      have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
      field_simp
    · show ((L : ℝ) ^ 4)⁻¹ * ∑ z ∈ sitesInBlocks L {Y}, blockMean L t (n * L) z (fun p => a * f p + b * g p) =
        a * (((L : ℝ) ^ 4)⁻¹ * ∑ z ∈ sitesInBlocks L {Y}, blockMean L t (n * L) z f) +
          b * (((L : ℝ) ^ 4)⁻¹ * ∑ z ∈ sitesInBlocks L {Y}, blockMean L t (n * L) z g)
      have hlin : ∀ z ∈ sitesInBlocks L {Y}, blockMean L t (n * L) z (fun p => a * f p + b * g p) =
          a * blockMean L t (n * L) z f + b * blockMean L t (n * L) z g := fun z _ =>
        (blockMean_one_and_linear_and_local L hodd t (n * L) z).2.1 a b f g
      rw [Finset.sum_congr rfl hlin, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    · show ((L : ℝ) ^ 4)⁻¹ * ∑ z ∈ sitesInBlocks L {Y}, blockMean L t (n * L) z f =
        ((L : ℝ) ^ 4)⁻¹ * ∑ z ∈ sitesInBlocks L {Y}, blockMean L t (n * L) z g
      congr 1
      refine Finset.sum_congr rfl fun z hz => ?_
      refine (blockMean_one_and_linear_and_local L hodd t (n * L) z).2.2 f g fun p hp => hfg p ⟨hp.1, ?_⟩
      obtain ⟨c, hc, hcz⟩ := hp.2
      exact ⟨c, hc, Finset.mem_biUnion.mpr ⟨z, hz, hcz⟩⟩
theorem blockMeanIsLinearAndLocal_holds : BlockMeanIsLinearAndLocal :=
  fun L _ hodd t n _ y => blockMean_one_and_linear_and_local L hodd t n y
end WeightedResponses
end YangMills.Construction
end
