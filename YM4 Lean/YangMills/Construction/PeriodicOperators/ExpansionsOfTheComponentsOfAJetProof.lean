import YangMills.Construction.PeriodicOperators.ExpansionsOfTheComponentsOfAJet
import YangMills.Construction.PeriodicOperators.JetTripleOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfALocalOperatorFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetExpansions
open InfiniteLattice (AmbientSpace)
open LocalOpFunTaylor (IsLinearCoeffFamily IsQuadraticCoeffFamily)
theorem bilinDot_toComplexVec_sub_add (q : Fin 4 → ℂ) (x z : AmbientSpace) :
    bilinDot q (toComplexVec x) = bilinDot q (toComplexVec (x - z)) + bilinDot q (toComplexVec z) := by
  simp only [bilinDot, toComplexVec, Pi.sub_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  push_cast
  ring
theorem bilinDot_add_left (u v w : Fin 4 → ℂ) : bilinDot (u + v) w = bilinDot u w + bilinDot v w := by
  simp [bilinDot, add_mul, Finset.sum_add_distrib]
theorem bilinDot_neg_left (u w : Fin 4 → ℂ) : bilinDot (-u) w = -bilinDot u w := by
  simp [bilinDot]
theorem bilinDot_zero_left (w : Fin 4 → ℂ) : bilinDot 0 w = 0 := by
  simp [bilinDot]
theorem blochWave_eq_exp_mul_phaseField (P : PeriodicData) (q : Fin 4 → ℂ) (χ : P.UnitQuot → ℂ)
    (z : InfiniteLattice.AmbientSpace) :
    blochWave P q χ =
      fun j => Complex.exp (Complex.I * bilinDot q (toComplexVec z)) * phaseField P q χ z j := by
  funext j
  simp only [blochWave, phaseField]
  rw [← mul_assoc, ← Complex.exp_add, ← mul_add, add_comm (bilinDot q (toComplexVec z)),
    ← bilinDot_toComplexVec_sub_add]
section Linear
variable {P Q Q' : PeriodicData}
theorem coeffOne_const_mul (hTay : LocalOpFunTaylor.Claim)
    (hP : IsPeriodic P) (hQ : IsPeriodic Q) (hQ' : IsPeriodic Q')
    {A : (P.Carrier → ℂ) → Q'.Carrier → Q.Carrier → ℂ} (hA : IsLocalOpFun P Q Q' A)
    (a : ℂ) (u : P.Carrier → ℂ) (j' : Q'.Carrier) (j : Q.Carrier) :
    coeffOne P Q Q' A (fun k => a * u k) j' j =
      a * coeffOne P Q Q' A u j' j := by
  obtain ⟨r, Rad, hloc⟩ := hA
  obtain ⟨⟨hfin, -, hlin, -, -⟩, -⟩ := hTay P Q Q' hP hQ hQ' A r Rad hloc u u j' j 0
  have : Finite (nearIndices P (Q'.pos j') Rad) := hfin
  rw [hlin (fun k => a * u k), hlin u, mul_finsum]
  exact finsum_congr fun k => by ring
theorem coeffTwo_const_mul (hTay : LocalOpFunTaylor.Claim)
    (hP : IsPeriodic P) (hQ : IsPeriodic Q) (hQ' : IsPeriodic Q')
    {A : (P.Carrier → ℂ) → Q'.Carrier → Q.Carrier → ℂ} (hA : IsLocalOpFun P Q Q' A)
    (a b : ℂ) (u v : P.Carrier → ℂ) (j' : Q'.Carrier) (j : Q.Carrier) :
    coeffTwo P Q Q' A (fun k => a * u k) (fun k => b * v k) j' j =
      (a * b) * coeffTwo P Q Q' A u v j' j := by
  obtain ⟨r, Rad, hloc⟩ := hA
  obtain ⟨⟨hfin, -, -, -, hquad⟩, -⟩ := hTay P Q Q' hP hQ hQ' A r Rad hloc u v j' j 0
  have : Finite (nearIndices P (Q'.pos j') Rad) := hfin
  rw [hquad.2 (fun k => a * u k) (fun k => b * v k), hquad.2 u v, mul_finsum]
  refine finsum_congr fun k => ?_
  rw [mul_finsum]
  exact finsum_congr fun k' => by ring
end Linear
theorem eq_tsum_of_applyKernel_blochWave {Q Q' : PeriodicData} (m s : Fin 4 → ℂ) (g : Q.UnitQuot → ℂ)
    (h : Q'.UnitQuot → ℂ) (j' : Q'.Carrier) (K K' : Q'.Carrier → Q.Carrier → ℂ)
    (hK : ∀ j, K j' j =
      Complex.exp (Complex.I * bilinDot s (toComplexVec (Q'.pos j'))) * K' j' j)
    (hact : applyKernel K (blochWave Q m g) j' = blochWave Q' (m + s) h j') :
    h (Q'.mkQuot 1 j') =
      ∑' j, relPhase Q Q' m j' j * K' j' j * g (Q.mkQuot 1 j) := by
  set z := Q'.pos j' with hz
  set w := Complex.exp (Complex.I * bilinDot s (toComplexVec z)) with hw
  set W := Complex.exp (Complex.I * bilinDot m (toComplexVec z)) with hW
  have hsummand : ∀ j, K j' j * blochWave Q m g j =
      (W * w) * (relPhase Q Q' m j' j * K' j' j * g (Q.mkQuot 1 j)) := by
    intro j
    have hphase : Complex.exp (Complex.I * bilinDot m (toComplexVec (Q.pos j))) =
        relPhase Q Q' m j' j * W := by
      rw [relPhase, hW, ← Complex.exp_add, ← mul_add, ← bilinDot_toComplexVec_sub_add]
    rw [hK j, blochWave, hphase]
    ring
  have hrhs : blochWave Q' (m + s) h j' = (W * w) * h (Q'.mkQuot 1 j') := by
    rw [blochWave, bilinDot_add_left, mul_add, Complex.exp_add]
  have hnz : W * w ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  apply mul_left_cancel₀ hnz
  rw [← hrhs, ← hact, applyKernel, ← tsum_mul_left]
  exact tsum_congr fun j => hsummand j
theorem claim_holds (hTrip : LocalOpFunTriple.Claim)
    (hTay : LocalOpFunTaylor.Claim) : Claim := by
  intro P Q Q' hP hQ hQ' A hA p m χp χm g j'
  have huniq : ActionTripleUnique P Q Q' A p χp χm :=
    (hTrip P Q Q' hP hQ hQ' A hA).1 p χp χm
  have hchosen : IsActionTriple P Q Q' A p χp χm
      (Classical.epsilon (IsActionTriple P Q Q' A p χp χm)) :=
    Classical.epsilon_spec huniq.exists
  have hacts := hchosen m g j'
  set z := Q'.pos j' with hz
  refine ⟨?_, ?_, ?_⟩
  · refine eq_tsum_of_applyKernel_blochWave m p g ((jetAlong P Q Q' A p χp χm).f10 m g) j'
      (coeffOne P Q Q' A (blochWave P p χp))
      (coeffOne P Q Q' A (phaseField P p χp z)) (fun j => ?_) hacts.1
    rw [blochWave_eq_exp_mul_phaseField P p χp z]
    exact coeffOne_const_mul hTay hP hQ hQ' hA _ _ j' j
  · refine eq_tsum_of_applyKernel_blochWave m (-p) g ((jetAlong P Q Q' A p χp χm).f01 m g) j'
      (coeffOne P Q Q' A (blochWave P (-p) χm))
      (coeffOne P Q Q' A (phaseField P (-p) χm z)) (fun j => ?_) ?_
    · rw [blochWave_eq_exp_mul_phaseField P (-p) χm z]
      exact coeffOne_const_mul hTay hP hQ hQ' hA _ _ j' j
    · rw [← sub_eq_add_neg]
      exact hacts.2.1
  · refine eq_tsum_of_applyKernel_blochWave m 0 g ((jetAlong P Q Q' A p χp χm).f11 m g) j'
      (coeffTwo P Q Q' A (blochWave P p χp) (blochWave P (-p) χm))
      (coeffTwo P Q Q' A (phaseField P p χp z) (phaseField P (-p) χm z))
      (fun j => ?_) ?_
    · rw [blochWave_eq_exp_mul_phaseField P p χp z, blochWave_eq_exp_mul_phaseField P (-p) χm z,
        coeffTwo_const_mul hTay hP hQ hQ' hA, bilinDot_zero_left, bilinDot_neg_left, ← Complex.exp_add]
      simp
    · rw [add_zero]
      exact hacts.2.2
end YangMills.Construction.PeriodicOperators.JetExpansions
end
