import YangMills.Construction.ColdChainAtEveryLevel.CriticalForAllVariationsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PlaquetteLinearization
open BlockAverages QuaternionLog
theorem inv_coe_mul_coe_mul (g : UnitQuaternion) (a : ℍ[ℝ]) :
    ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((g : ℍ[ℝ]) * a) = a := by apply _root_.YangMills.Construction.GaugedCriticality.coe_inv_mul_coe_mul <;> assumption
theorem norm_coe_mul_mul_coe_inv (a b : UnitQuaternion) (q : ℍ[ℝ]) :
    ‖(a : ℍ[ℝ]) * q * ((b⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖q‖ := by
  rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
theorem re_coe_mul_mul_coe_inv (g : UnitQuaternion) (q : ℍ[ℝ]) :
    ((g : ℍ[ℝ]) * q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = q.re := by apply _root_.YangMills.Construction.GaugedCriticality.re_conj_unit <;> assumption
theorem adjointAction_add (g : UnitQuaternion) (a b : ℍ[ℝ]) :
    adjointAction g (a + b) = adjointAction g a + adjointAction g b := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem adjointAction_sub (g : UnitQuaternion) (a b : ℍ[ℝ]) :
    adjointAction g (a - b) = adjointAction g a - adjointAction g b := by apply _root_.YangMills.Construction.BlockLines.adjointAction_sub <;> assumption
theorem adjointAction_smul (g : UnitQuaternion) (t : ℝ) (a : ℍ[ℝ]) :
    adjointAction g (t • a) = t • adjointAction g a := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem adjointAction_mul (g h : UnitQuaternion) (a : ℍ[ℝ]) :
    adjointAction (g * h) a = adjointAction g (adjointAction h a) := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_mul <;> assumption
theorem norm_adjointAction (g : UnitQuaternion) (a : ℍ[ℝ]) : ‖adjointAction g a‖ = ‖a‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
theorem adjointAction_re (g : UnitQuaternion) (a : ℍ[ℝ]) : (adjointAction g a).re = a.re := by apply _root_.YangMills.Construction.GaugedCriticality.re_conj_unit <;> assumption
theorem adjointAction_eq_unitConj (g : UnitQuaternion) (a : ℍ[ℝ]) :
    adjointAction g a = unitConj (g : ℍ[ℝ]) a := rfl
theorem adjointAction_linearPart (g : UnitQuaternion) (q a : ℍ[ℝ]) :
    adjointAction g (linearPart q a) = linearPart (adjointAction g q) (adjointAction g a) := by
  simp only [adjointAction_eq_unitConj]
  exact (linearPart_unitConj (norm_coe_unitQuaternion g) q a).symm
theorem linearPart_sub_left (q q' a : ℍ[ℝ]) : linearPart (q - q') a = linearPart q a - linearPart q' a := by
  rw [sub_eq_add_neg, linearPart_add_left, linearPart_neg_left, ← sub_eq_add_neg]
theorem norm_plaquette_linearPart_le {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ q a : ℍ[ℝ], ‖linearPart q a‖ ≤ K * ‖q‖ * ‖a‖) (r1 r2 r3 r4 : UnitQuaternion)
    (x0 x1 x2 x3 u1 u2 u3 u4 e1 e2 e3 e4 : ℍ[ℝ]) :
    ‖(linearPart u1 (x0 + adjointAction r1 x1) + e1) +
        adjointAction r1 (linearPart u2 (x1 + adjointAction r2 x3) + e2) -
        adjointAction (r1 * r2 * r3⁻¹) (linearPart u3 (x2 + adjointAction r3 x3) + e3) -
        adjointAction (r1 * r2 * r3⁻¹ * r4⁻¹) (linearPart u4 (x0 + adjointAction r4 x2) + e4)‖ ≤
      K * (‖u1 + adjointAction r1 u2 - adjointAction (r1 * r2 * r3⁻¹) u3 -
            adjointAction (r1 * r2 * r3⁻¹ * r4⁻¹) u4‖ * (2 * ‖x0‖) +
        (‖u1‖ + ‖u2‖ + ‖u3‖ + ‖u4‖) *
          (2 * (‖adjointAction r1 x1 - x0‖ + ‖adjointAction r2 x3 - x1‖ + ‖adjointAction r3 x3 - x2‖ +
            ‖adjointAction r4 x2 - x0‖))) +
      (‖e1‖ + ‖e2‖ + ‖e3‖ + ‖e4‖) := by
  set g3 := r1 * r2 * r3⁻¹ with hg3
  set g4 := r1 * r2 * r3⁻¹ * r4⁻¹ with hg4
  set D1 := adjointAction r1 x1 - x0 with hD1
  set D2 := adjointAction r2 x3 - x1 with hD2
  set D3 := adjointAction r3 x3 - x2 with hD3
  set D4 := adjointAction r4 x2 - x0 with hD4
  set Dn := ‖D1‖ + ‖D2‖ + ‖D3‖ + ‖D4‖ with hDn
  have z1 : adjointAction r1 x1 = x0 + D1 := by rw [hD1]; abel
  have x1e : x1 = adjointAction r2 x3 - D2 := by rw [hD2]; abel
  have x2e : x2 = adjointAction r3 x3 - D3 := by rw [hD3]; abel
  have x0e : x0 = adjointAction r4 x2 - D4 := by rw [hD4]; abel
  set Z := x0 + D1 + adjointAction r1 D2 with hZ
  have e12 : adjointAction (r1 * r2) x3 = Z := by
    rw [adjointAction_mul]
    have : adjointAction r2 x3 = x1 + D2 := by rw [x1e]; abel
    rw [this, adjointAction_add, z1]
  have e3' : adjointAction g3 (adjointAction r3 x3) = Z := by
    rw [← adjointAction_mul, hg3, inv_mul_cancel_right, e12]
  have e3'' : adjointAction g3 x2 = Z - adjointAction g3 D3 := by
    have : adjointAction g3 x2 = adjointAction g3 (adjointAction r3 x3 - D3) := by rw [← x2e]
    rw [this, adjointAction_sub, e3']
  have e4' : adjointAction g4 (adjointAction r4 x2) = Z - adjointAction g3 D3 := by
    rw [← adjointAction_mul, hg4, inv_mul_cancel_right, ← hg3, e3'']
  have e4'' : adjointAction g4 x0 = Z - adjointAction g3 D3 - adjointAction g4 D4 := by
    have : adjointAction g4 x0 = adjointAction g4 (adjointAction r4 x2 - D4) := by rw [← x0e]
    rw [this, adjointAction_sub, e4']
  set f2 := D1 + D1 + adjointAction r1 D2 with hf2
  set f3 := D1 + D1 + adjointAction r1 D2 + adjointAction r1 D2 - adjointAction g3 D3 with hf3
  set f4 := D1 + D1 + adjointAction r1 D2 + adjointAction r1 D2 - adjointAction g3 D3 -
    adjointAction g3 D3 - adjointAction g4 D4 with hf4
  have a1 : x0 + adjointAction r1 x1 = (x0 + x0) + D1 := by rw [z1]; abel
  have a2 : adjointAction r1 (x1 + adjointAction r2 x3) = (x0 + x0) + f2 := by
    rw [adjointAction_add, ← adjointAction_mul, e12, z1, hZ, hf2]
    abel
  have a3 : adjointAction g3 (x2 + adjointAction r3 x3) = (x0 + x0) + f3 := by
    rw [adjointAction_add, e3', e3'', hZ, hf3]
    abel
  have a4 : adjointAction g4 (x0 + adjointAction r4 x2) = (x0 + x0) + f4 := by
    rw [adjointAction_add, e4', e4'', hZ, hf4]
    abel
  have hsplit : (linearPart u1 (x0 + adjointAction r1 x1) + e1) +
        adjointAction r1 (linearPart u2 (x1 + adjointAction r2 x3) + e2) -
        adjointAction g3 (linearPart u3 (x2 + adjointAction r3 x3) + e3) -
        adjointAction g4 (linearPart u4 (x0 + adjointAction r4 x2) + e4) =
      linearPart (u1 + adjointAction r1 u2 - adjointAction g3 u3 - adjointAction g4 u4) (x0 + x0) +
        (linearPart u1 D1 + linearPart (adjointAction r1 u2) f2 - linearPart (adjointAction g3 u3) f3 -
          linearPart (adjointAction g4 u4) f4) +
        (e1 + adjointAction r1 e2 - adjointAction g3 e3 - adjointAction g4 e4) := by
    rw [adjointAction_add, adjointAction_add, adjointAction_add, adjointAction_linearPart,
      adjointAction_linearPart, adjointAction_linearPart, a1, a2, a3, a4]
    simp only [linearPart_add_right, linearPart_sub_left, linearPart_add_left]
    abel
  rw [hsplit]
  have n1 : ‖D1‖ ≤ 2 * Dn := by
    have := norm_nonneg D1; have := norm_nonneg D2; have := norm_nonneg D3; have := norm_nonneg D4
    rw [hDn]; linarith
  have n2 : ‖f2‖ ≤ 2 * Dn := by
    have h := norm_add₃_le (a := D1) (b := D1) (c := adjointAction r1 D2)
    rw [norm_adjointAction] at h
    have := norm_nonneg D2; have := norm_nonneg D3; have := norm_nonneg D4
    rw [hf2, hDn]; linarith
  have n3 : ‖f3‖ ≤ 2 * Dn := by
    have h1 : ‖f3‖ ≤ ‖D1‖ + ‖D1‖ + ‖adjointAction r1 D2‖ + ‖adjointAction r1 D2‖ +
        ‖adjointAction g3 D3‖ := by
      rw [hf3]
      refine (norm_sub_le _ _).trans ?_
      have h2 := norm_add₄_le (a := D1) (b := D1) (c := adjointAction r1 D2) (d := adjointAction r1 D2)
      linarith
    rw [norm_adjointAction, norm_adjointAction] at h1
    have := norm_nonneg D4; have := norm_nonneg D3
    rw [hDn]; linarith
  have n4 : ‖f4‖ ≤ 2 * Dn := by
    have h1 : ‖f4‖ ≤ ‖D1‖ + ‖D1‖ + ‖adjointAction r1 D2‖ + ‖adjointAction r1 D2‖ +
        ‖adjointAction g3 D3‖ + ‖adjointAction g3 D3‖ + ‖adjointAction g4 D4‖ := by
      rw [hf4]
      refine (norm_sub_le _ _).trans ?_
      have h3 := norm_sub_le (D1 + D1 + adjointAction r1 D2 + adjointAction r1 D2 - adjointAction g3 D3)
        (adjointAction g3 D3)
      have h4 := norm_sub_le (D1 + D1 + adjointAction r1 D2 + adjointAction r1 D2) (adjointAction g3 D3)
      have h2 := norm_add₄_le (a := D1) (b := D1) (c := adjointAction r1 D2) (d := adjointAction r1 D2)
      linarith
    rw [norm_adjointAction, norm_adjointAction, norm_adjointAction] at h1
    have := norm_nonneg D4
    rw [hDn]; linarith
  have hDn0 : 0 ≤ Dn := by positivity
  have b0 : ‖linearPart (u1 + adjointAction r1 u2 - adjointAction g3 u3 - adjointAction g4 u4) (x0 + x0)‖ ≤
      K * ‖u1 + adjointAction r1 u2 - adjointAction g3 u3 - adjointAction g4 u4‖ * (2 * ‖x0‖) := by
    refine (hB _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have := norm_add_le x0 x0
    linarith
  have bk : ∀ (q f : ℍ[ℝ]), ‖f‖ ≤ 2 * Dn → ‖linearPart q f‖ ≤ K * ‖q‖ * (2 * Dn) := fun q f hf =>
    (hB _ _).trans (mul_le_mul_of_nonneg_left hf (by positivity))
  have b1 := bk u1 D1 n1
  have b2 := bk (adjointAction r1 u2) f2 n2
  have b3 := bk (adjointAction g3 u3) f3 n3
  have b4 := bk (adjointAction g4 u4) f4 n4
  rw [norm_adjointAction] at b2 b3 b4
  have hsum : ‖linearPart u1 D1 + linearPart (adjointAction r1 u2) f2 - linearPart (adjointAction g3 u3) f3 -
      linearPart (adjointAction g4 u4) f4‖ ≤ K * (‖u1‖ + ‖u2‖ + ‖u3‖ + ‖u4‖) * (2 * Dn) := by
    have s1 := norm_sub_le (linearPart u1 D1 + linearPart (adjointAction r1 u2) f2 -
      linearPart (adjointAction g3 u3) f3) (linearPart (adjointAction g4 u4) f4)
    have s2 := norm_sub_le (linearPart u1 D1 + linearPart (adjointAction r1 u2) f2)
      (linearPart (adjointAction g3 u3) f3)
    have s3 := norm_add_le (linearPart u1 D1) (linearPart (adjointAction r1 u2) f2)
    have e : K * (‖u1‖ + ‖u2‖ + ‖u3‖ + ‖u4‖) * (2 * Dn) =
        K * ‖u1‖ * (2 * Dn) + K * ‖u2‖ * (2 * Dn) + K * ‖u3‖ * (2 * Dn) + K * ‖u4‖ * (2 * Dn) := by ring
    rw [e]
    linarith
  have hes : ‖e1 + adjointAction r1 e2 - adjointAction g3 e3 - adjointAction g4 e4‖ ≤
      ‖e1‖ + ‖e2‖ + ‖e3‖ + ‖e4‖ := by
    have s1 := norm_sub_le (e1 + adjointAction r1 e2 - adjointAction g3 e3) (adjointAction g4 e4)
    have s2 := norm_sub_le (e1 + adjointAction r1 e2) (adjointAction g3 e3)
    have s3 := norm_add_le e1 (adjointAction r1 e2)
    rw [norm_adjointAction] at s1 s2 s3
    linarith
  have htri := norm_add₃_le
    (a := linearPart (u1 + adjointAction r1 u2 - adjointAction g3 u3 - adjointAction g4 u4) (x0 + x0))
    (b := linearPart u1 D1 + linearPart (adjointAction r1 u2) f2 - linearPart (adjointAction g3 u3) f3 -
      linearPart (adjointAction g4 u4) f4)
    (c := e1 + adjointAction r1 e2 - adjointAction g3 e3 - adjointAction g4 e4)
  have e : K * (‖u1 + adjointAction r1 u2 - adjointAction g3 u3 - adjointAction g4 u4‖ * (2 * ‖x0‖) +
        (‖u1‖ + ‖u2‖ + ‖u3‖ + ‖u4‖) * (2 * Dn)) =
      K * ‖u1 + adjointAction r1 u2 - adjointAction g3 u3 - adjointAction g4 u4‖ * (2 * ‖x0‖) +
        K * (‖u1‖ + ‖u2‖ + ‖u3‖ + ‖u4‖) * (2 * Dn) := by
    ring
  rw [e]
  linarith
theorem exists_bond_linearPart_split {K r : ℝ}
    (hT : ∀ q a : ℍ[ℝ], ‖q‖ < r → ‖rightTransDeriv q a - a - linearPart q a‖ ≤ K * ‖q‖ ^ 2 * ‖a‖)
    {w a b : ℍ[ℝ]} (hw : ‖w‖ < r) :
    ∃ e : ℍ[ℝ], rightTransDeriv w a - rightTransDeriv (-w) b + (b - a) = linearPart w (a + b) + e ∧
      ‖e‖ ≤ K * ‖w‖ ^ 2 * (‖a‖ + ‖b‖) := by
  refine ⟨(rightTransDeriv w a - a - linearPart w a) - (rightTransDeriv (-w) b - b - linearPart (-w) b), ?_, ?_⟩
  · rw [linearPart_add_right, linearPart_neg_left]
    abel
  · have h1 := hT w a hw
    have h2 := hT (-w) b (by rwa [norm_neg])
    rw [norm_neg] at h2
    have := norm_sub_le (rightTransDeriv w a - a - linearPart w a)
      (rightTransDeriv (-w) b - b - linearPart (-w) b)
    linarith
end PlaquetteLinearization
end YangMills.Construction
end
