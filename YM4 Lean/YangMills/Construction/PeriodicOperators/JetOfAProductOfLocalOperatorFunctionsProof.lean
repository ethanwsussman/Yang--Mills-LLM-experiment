import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.PeriodicOperators.JetOfAProductOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.KernelsOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.ProductOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.ProductsOfKernelsWithFiniteRows
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfAProductOfLocalOperatorFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetComp
open OpFunKernels (IsComponentKernel)
open RowFiniteKernels (ApplyComp)
variable {I I' I'' : PeriodicData}
private structure MapsBlochWaves (q : Fin 4 → ℂ) (Y : I'.Carrier → I.Carrier → ℂ)
    (A : (Fin 4 → ℂ) → QuotHom I I') : Prop where
  row_finite : RowFinite Y
  bloch : ∀ κ φ, applyKernel Y (blochWave I κ φ) = blochWave I' (κ + q) (A κ φ)
private theorem mapsBlochWaves_of_isComponentKernel (hC : CovariantFiniteRange.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {q : Fin 4 → ℂ}
    {Y : I'.Carrier → I.Carrier → ℂ} {A : (Fin 4 → ℂ) → QuotHom I I'}
    (h : IsComponentKernel I I' q Y A) : MapsBlochWaves q Y A := by
  obtain ⟨hc, hop, rfl⟩ := h
  obtain ⟨ϱ, hϱ⟩ := hop.finiteRange
  have hvan : VanishesOutsideRadius I I' ϱ Y := fun x' x hn => by
    have e := hϱ x' x hn
    simpa [dephasedKernel, Complex.exp_ne_zero] using e
  have hacts := (hC.2 I I' hI hI' q ϱ Y hc hvan).2.2.2
  refine ⟨fun x' => ?_, fun κ φ => ?_⟩
  · refine (hacts 0 (fun _ => 1) x').1.subset fun x hx => ?_
    simpa [Function.mem_support, blochWave, Complex.exp_ne_zero] using hx
  · have := hI.finite_quot
    funext x'
    rw [(hacts κ φ x').2]
    simp only [symbolHom, linearMapOfEntries_eq_applyKernel]
    rfl
private theorem isComponentKernel_zero {Y : I'.Carrier → I.Carrier → ℂ}
    (h : IsFiniteRangeAllRates I I' Y) :
    IsComponentKernel I I' 0 Y (symbolHom I I' Y) := by
  have e : dephasedKernel I I' 0 Y = Y := by
    funext x' x
    simp [dephasedKernel, bilinDot]
  refine ⟨fun n x' x => ?_, ?_, ?_⟩
  · simpa [bilinDot] using h.periodic.1 n x' x
  · rwa [e]
  · rw [e]
private theorem applyKernel_add (hA : ApplyComp) {Y Y' : I'.Carrier → I.Carrier → ℂ}
    (h : RowFinite Y) (h' : RowFinite Y') (f : I.Carrier → ℂ) :
    applyKernel (Y + Y') f = applyKernel Y f + applyKernel Y' f := by
  funext x'
  have s := ((hA _ _ Y h).1 f x').of_norm
  have s' := ((hA _ _ Y' h').1 f x').of_norm
  simp only [applyKernel, Pi.add_apply, add_mul]
  exact s.tsum_add s'
private theorem rowFinite_add {Y Y' : I'.Carrier → I.Carrier → ℂ} (h : RowFinite Y)
    (h' : RowFinite Y') : RowFinite (Y + Y') := fun x' => by
  refine ((h x').union (h' x')).subset fun x hx => ?_
  by_contra hn
  have a : Y x' x = 0 := by_contra fun e => hn (Or.inl e)
  have b : Y' x' x = 0 := by_contra fun e => hn (Or.inr e)
  exact hx (by simp [a, b])
private theorem blochWave_add (κ : Fin 4 → ℂ) (φ ψ : I.UnitQuot → ℂ) :
    blochWave I κ (φ + ψ) = blochWave I κ φ + blochWave I κ ψ := by
  funext x
  simp [blochWave, mul_add]
private theorem blochWave_injective (κ : Fin 4 → ℂ) {φ ψ : I.UnitQuot → ℂ}
    (h : blochWave I κ φ = blochWave I κ ψ) : φ = ψ := by
  funext c
  obtain ⟨x, rfl⟩ := Quot.exists_rep (show I.QuotMod 1 from c)
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) (congrFun h x)
abbrev _root_.YangMills.SharedProofs.p12280 := @blochWave_injective
private theorem MapsBlochWaves.comp (hA : ApplyComp) {q r : Fin 4 → ℂ}
    {Y : I'.Carrier → I.Carrier → ℂ} {Z : I.Carrier → I''.Carrier → ℂ}
    {A : (Fin 4 → ℂ) → QuotHom I I'} {B : (Fin 4 → ℂ) → QuotHom I'' I}
    (hY : MapsBlochWaves q Y A) (hZ : MapsBlochWaves r Z B) :
    RowFinite (compKernel Y Z) ∧ ∀ κ φ, applyKernel (compKernel Y Z) (blochWave I'' κ φ) =
      blochWave I' (κ + r + q) (A (κ + r) (B κ φ)) := by
  have h := (hA _ _ Z hZ.row_finite).2 _ Y hY.row_finite
  refine ⟨h.2.1, fun κ φ => ?_⟩
  rw [(h.2.2 _).2.2, hZ.bloch, hY.bloch]
theorem claim_holds (hK : OpFunKernels.Claim)
    (hC : CovariantFiniteRange.Claim)
    (hP : OpFunComp.LocalClosed)
    (hR : RowFiniteKernels.Claim)
    (hL : LeibnizRule.Claim) :
    JetComp.Claim := by
  intro δ p _ _ F I₁ I₂ I₃ hF h₁ h₂ h₃ εPlus εMinus T S hT hS
  have hA : ApplyComp := hR.1
  obtain ⟨hT0, hTk⟩ := hK F I₂ I₁ hF h₂ h₁ T hT
  obtain ⟨-, hT10, hT01, hT11⟩ := hTk p εPlus εMinus
  obtain ⟨hS0, hSk⟩ := hK F I₃ I₂ hF h₃ h₂ S hS
  obtain ⟨-, hS10, hS01, hS11⟩ := hSk p εPlus εMinus
  have hPl := hP F I₂ I₁ I₃ hF h₂ h₁ h₃ T S hT hS
  obtain ⟨hP0, hPk⟩ := hK F I₃ I₁ hF h₃ h₁ _ hPl
  have hset := (hPk p εPlus εMinus).1
  have aT0 := mapsBlochWaves_of_isComponentKernel hC h₂ h₁ (isComponentKernel_zero hT0)
  have aT10 := mapsBlochWaves_of_isComponentKernel hC h₂ h₁ hT10
  have aT01 := mapsBlochWaves_of_isComponentKernel hC h₂ h₁ hT01
  have aT11 := mapsBlochWaves_of_isComponentKernel hC h₂ h₁ hT11
  have aS0 := mapsBlochWaves_of_isComponentKernel hC h₃ h₂ (isComponentKernel_zero hS0)
  have aS10 := mapsBlochWaves_of_isComponentKernel hC h₃ h₂ hS10
  have aS01 := mapsBlochWaves_of_isComponentKernel hC h₃ h₂ hS01
  have aS11 := mapsBlochWaves_of_isComponentKernel hC h₃ h₂ hS11
  have aP0 := mapsBlochWaves_of_isComponentKernel hC h₃ h₁ (isComponentKernel_zero hP0)
  have lp := hL F I₂ I₁ I₃ hF h₂ h₁ h₃ T S hT hS (blochWave F p εPlus) (blochWave F (-p) εMinus)
  have lm := hL F I₂ I₁ I₃ hF h₂ h₁ h₃ T S hT hS (blochWave F (-p) εMinus) (blochWave F p εPlus)
  have p1 := aT10.comp hA aS0
  have p2 := aT0.comp hA aS10
  have m1 := aT01.comp hA aS0
  have m2 := aT0.comp hA aS01
  have b1 := aT11.comp hA aS0
  have b2 := aT0.comp hA aS11
  have b3 := aT10.comp hA aS01
  have b4 := aT01.comp hA aS10
  have z0 := aT0.comp hA aS0
  set JT := jetAlong F I₂ I₁ T p εPlus εMinus with hJT
  set JS := jetAlong F I₃ I₂ S p εPlus εMinus with hJS
  have htriple : IsActionTriple F I₃ I₁ (opFunComp T S) p εPlus εMinus
      ((JetQuad.mul p JT JS).f10, (JetQuad.mul p JT JS).f01, (JetQuad.mul p JT JS).f11) := by
    intro κ φ x'
    refine ⟨?_, ?_, ?_⟩
    · rw [lp.1, applyKernel_add hA p1.1 p2.1, p1.2, p2.2]
      simp only [add_zero, JetQuad.mul, LinearMap.add_apply, LinearMap.comp_apply, blochWave_add,
        Pi.add_apply]
      rfl
    · rw [lm.1, applyKernel_add hA m1.1 m2.1, m1.2, m2.2]
      simp only [add_zero, JetQuad.mul, LinearMap.add_apply, LinearMap.comp_apply, blochWave_add,
        Pi.add_apply, sub_eq_add_neg]
      rfl
    · rw [lp.2, applyKernel_add hA (rowFinite_add (rowFinite_add b1.1 b2.1) b3.1) b4.1,
        applyKernel_add hA (rowFinite_add b1.1 b2.1) b3.1, applyKernel_add hA b1.1 b2.1,
        b1.2, b2.2, b3.2, b4.2]
      have e₁ : κ + -p + p = κ := by abel
      have e₂ : κ + p + -p = κ := by abel
      simp only [add_zero, e₁, e₂, JetQuad.mul, LinearMap.add_apply, LinearMap.comp_apply,
        blochWave_add, Pi.add_apply, sub_eq_add_neg]
      rfl
  have hunique := hset.unique (Classical.epsilon_spec hset.exists) htriple
  have h00 : ∀ κ, (jetAlong F I₃ I₁ (opFunComp T S) p εPlus εMinus).f00 κ =
      (JetQuad.mul p JT JS).f00 κ := by
    intro κ
    refine LinearMap.ext fun φ => blochWave_injective κ ?_
    have e₁ := aP0.bloch κ φ
    have e₂ := z0.2 κ φ
    simp only [add_zero] at e₁ e₂
    exact e₁.symm.trans e₂
  refine ⟨fun κ _ => h00 κ, fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_⟩
  · exact congrFun (congrArg Prod.fst hunique) κ
  · exact congrFun (congrArg (fun A => A.2.1) hunique) κ
  · exact congrFun (congrArg (fun A => A.2.2) hunique) κ
end YangMills.Construction.PeriodicOperators.JetComp
end
