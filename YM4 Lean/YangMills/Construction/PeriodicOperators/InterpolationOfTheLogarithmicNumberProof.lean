import YangMills.Construction.PeriodicOperators.AlgebraOfQuadruples
import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.CalculusOfJets
import YangMills.Construction.PeriodicOperators.InterpolationOfTheLogarithmicNumber
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.LogNumberInterpolation
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
open YangMills.Construction.PeriodicOperators.JetNormsAffine (affinePath)
section Algebra
variable {δ : ℝ} {p : Fin 4 → ℂ} {I : PeriodicData}
theorem eqAsJet_refl (T : JetQuad I I) : EqAsJet δ p T T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
theorem eqAsJet_symm {T S : JetQuad I I} (h : EqAsJet δ p T S) : EqAsJet δ p S T :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
theorem eqAsJet_trans {T S R : JetQuad I I} (h : EqAsJet δ p T S) (k : EqAsJet δ p S R) :
    EqAsJet δ p T R :=
  ⟨h.1.trans k.1, h.2.1.trans k.2.1, h.2.2.1.trans k.2.2.1, h.2.2.2.trans k.2.2.2⟩
theorem invJet_eq_resolvent_expansion (h₂ : JetCalculus.Claim)
    (h₃ : JetDomains.OpFunJetTheory)
    (h₄ : JetArgumentsAndEqualJets) (h₅ : QuadAlgebra.Claim)
    (hδ : 0 < δ) (hp : p ∈ imStrip δ) (hI : IsPeriodic I) {B T W : JetQuad I I} {s : ℂ}
    (hB : IsInvertibleJet δ p B) (hT : IsInvertibleJet δ p T) (hW : IsJet δ p W)
    (hBT : B = add T (add (smul s (one I)) (smul (-1) W))) :
    EqAsJet δ p (invJet p T)
      (add (invJet p B)
        (add (smul s (mul p (invJet p B) (invJet p T)))
          (smul (-1) (mul p (mul p (invJet p B) W) (invJet p T))))) := by
  have F := h₃.2.2 I I I hI hI hI δ p hδ hp
  obtain ⟨al, ar, sl, sr, u⟩ := h₅.1 p I I I
  have mulj := F.mul_isJet
  have addj := F.add_isJet
  have smulj := F.smul_isJet
  obtain ⟨hG, hGB, -, -⟩ := (h₂ δ p hδ hp).2.2.2.2.1 I hI B hB
  obtain ⟨hP, -, hTP, -⟩ := (h₂ δ p hδ hp).2.2.2.2.1 I hI T hT
  have assoc := fun (X Y Z : JetQuad I I) (hX : IsJet δ p X) (hY : IsJet δ p Y)
      (hZ : IsJet δ p Z) =>
    ((h₂ δ p hδ hp).1 I I I I hI hI hI hI X Y Z hX hY hZ).1
  have mulCong := fun (X X' Y Y' : JetQuad I I) (hX : IsJet δ p X) (hX' : IsJet δ p X')
      (hY : IsJet δ p Y) (hY' : IsJet δ p Y') (e : EqAsJet δ p X X') (e' : EqAsJet δ p Y Y') =>
    (h₄.2.1 δ p I I hI hI X X' hX hX' e).2.2.2.2 I hI Y Y' hY hY' e'
  have addCong := fun (X X' Y Y' : JetQuad I I) (hX : IsJet δ p X) (hX' : IsJet δ p X')
      (hY : IsJet δ p Y) (hY' : IsJet δ p Y') (e : EqAsJet δ p X X') (e' : EqAsJet δ p Y Y') =>
    (h₄.2.1 δ p I I hI hI X X' hX hX' e).2.2.2.1 Y Y' hY hY' e'
  have hone := F.one_isJet
  have hBj := hB.isJet
  have hTj := hT.isJet
  generalize invJet p B = G at *
  generalize invJet p T = P at *
  set Rest := add (smul s (mul p G P)) (smul (-1) (mul p (mul p G W) P)) with hRest
  have hRj : IsJet δ p Rest :=
    addj _ _ (smulj _ _ (mulj _ _ hG hP)) (smulj _ _ (mulj _ _ (mulj _ _ hG hW) hP))
  have expand : mul p (mul p G B) P = add (mul p (mul p G T) P) Rest := by
    rw [hBT, ar, ar, sr, sr, (u G).2, al, al, sl, sl]
  have hGT : EqAsJet δ p (mul p (mul p G T) P) G :=
    eqAsJet_trans (assoc G T P hG hTj hP)
      (by
        have := mulCong G G (mul p T P) (one I) hG hG (mulj _ _ hTj hP) hone (eqAsJet_refl G) hTP
        rwa [(u G).2] at this)
  have hleft : EqAsJet δ p (mul p (mul p G B) P) P := by
    have := mulCong (mul p G B) (one I) P P (mulj _ _ hG hBj) hone hP hP hGB (eqAsJet_refl P)
    rwa [(u P).1] at this
  have hright : EqAsJet δ p (mul p (mul p G B) P) (add G Rest) := by
    rw [expand]
    exact addCong _ _ _ _ (mulj _ _ (mulj _ _ hG hTj) hP) hG hRj hRj hGT (eqAsJet_refl Rest)
  exact eqAsJet_trans (eqAsJet_symm hleft) hright
theorem traceNumber_resolvent_expansion (h₂ : JetCalculus.Claim)
    (h₃ : JetDomains.OpFunJetTheory)
    (h₄ : JetArgumentsAndEqualJets) (h₅ : QuadAlgebra.Claim)
    (hδ : 0 < δ) (hp : p ∈ imStrip δ) (hI : IsPeriodic I) {G P W : JetQuad I I} {s : ℂ}
    (hG : IsJet δ p G) (hP : IsJet δ p P) (hW : IsJet δ p W)
    (e : EqAsJet δ p P
      (add G (add (smul s (mul p G P)) (smul (-1) (mul p (mul p G W) P))))) :
    traceNumber P = traceNumber G + s * traceNumber (mul p G G) +
      (s ^ 2 * traceNumber (mul p (mul p G G) P) - traceNumber (mul p (mul p G W) P) -
        s * traceNumber (mul p (mul p (mul p G G) W) P)) := by
  have F := h₃.2.2 I I I hI hI hI δ p hδ hp
  obtain ⟨al, ar, sl, sr, u⟩ := h₅.1 p I I I
  have mulj := F.mul_isJet
  have addj := F.add_isJet
  have smulj := F.smul_isJet
  have assoc := fun (X Y Z : JetQuad I I) (hX : IsJet δ p X) (hY : IsJet δ p Y)
      (hZ : IsJet δ p Z) =>
    ((h₂ δ p hδ hp).1 I I I I hI hI hI hI X Y Z hX hY hZ).1
  have mulCong := fun (X X' Y Y' : JetQuad I I) (hX : IsJet δ p X) (hX' : IsJet δ p X')
      (hY : IsJet δ p Y) (hY' : IsJet δ p Y') (e : EqAsJet δ p X X') (e' : EqAsJet δ p Y Y') =>
    (h₄.2.1 δ p I I hI hI X X' hX hX' e).2.2.2.2 I hI Y Y' hY hY' e'
  have addCong := fun (X X' Y Y' : JetQuad I I) (hX : IsJet δ p X) (hX' : IsJet δ p X')
      (hY : IsJet δ p Y) (hY' : IsJet δ p Y') (e : EqAsJet δ p X X') (e' : EqAsJet δ p Y Y') =>
    (h₄.2.1 δ p I I hI hI X X' hX hX' e).2.2.2.1 Y Y' hY hY' e'
  have smulCong := fun (a : ℂ) (X X' : JetQuad I I) (hX : IsJet δ p X) (hX' : IsJet δ p X')
      (e : EqAsJet δ p X X') =>
    (h₄.2.1 δ p I I hI hI X X' hX hX' e).2.1 a
  have traceCong := fun (X X' : JetQuad I I) (hX : IsJet δ p X) (hX' : IsJet δ p X')
      (e : EqAsJet δ p X X') =>
    (h₄.2.2 δ p I hI X X' hX hX' e).1
  have N := h₅.2 δ p hδ hp I I hI hI
  have tadd := N.2.2.2.1
  have tsmul := N.2.2.2.2
  have hGG := mulj _ _ hG hG
  have hGP := mulj _ _ hG hP
  have hGW := mulj _ _ hG hW
  have hGWP := mulj _ _ hGW hP
  have hGGP := mulj _ _ hGG hP
  have hGGW := mulj _ _ hGG hW
  have hGGWP := mulj _ _ hGGW hP
  have hGGP' := mulj _ _ hG hGP
  have hGGWP' := mulj _ _ hG hGWP
  have hRest := addj _ _ (smulj s _ hGP) (smulj (-1) _ hGWP)
  have e₁ : EqAsJet δ p (mul p G (mul p G P)) (mul p (mul p G G) P) :=
    eqAsJet_symm (assoc G G P hG hG hP)
  have e₂ : EqAsJet δ p (mul p G (mul p (mul p G W) P)) (mul p (mul p (mul p G G) W) P) := by
    refine eqAsJet_trans (eqAsJet_symm (assoc G (mul p G W) P hG hGW hP)) ?_
    exact mulCong _ _ _ _ (mulj _ _ hG hGW) hGGW hP hP (eqAsJet_symm (assoc G G W hG hG hW))
      (eqAsJet_refl P)
  have e₃ : EqAsJet δ p (mul p G P)
      (add (mul p G G)
        (add (smul s (mul p (mul p G G) P)) (smul (-1) (mul p (mul p (mul p G G) W) P)))) := by
    have h := mulCong G G P _ hG hG hP (addj _ _ hG hRest) (eqAsJet_refl G) e
    rw [ar, ar, sr, sr] at h
    refine eqAsJet_trans h ?_
    exact addCong _ _ _ _ hGG hGG (addj _ _ (smulj s _ hGGP') (smulj (-1) _ hGGWP'))
      (addj _ _ (smulj s _ hGGP) (smulj (-1) _ hGGWP)) (eqAsJet_refl _)
      (addCong _ _ _ _ (smulj s _ hGGP') (smulj s _ hGGP) (smulj (-1) _ hGGWP')
        (smulj (-1) _ hGGWP) (smulCong s _ _ hGGP' hGGP e₁) (smulCong (-1) _ _ hGGWP' hGGWP e₂))
  have t₁ := traceCong _ _ hP (addj _ _ hG hRest) e
  have t₂ := traceCong _ _ hGP
    (addj _ _ hGG (addj _ _ (smulj s _ hGGP) (smulj (-1) _ hGGWP))) e₃
  rw [tadd _ _ hG hRest, tadd _ _ (smulj s _ hGP) (smulj (-1) _ hGWP), tsmul _ _ hGP,
    tsmul _ _ hGWP] at t₁
  rw [tadd _ _ hGG (addj _ _ (smulj s _ hGGP) (smulj (-1) _ hGGWP)),
    tadd _ _ (smulj s _ hGGP) (smulj (-1) _ hGGWP), tsmul _ _ hGGP, tsmul _ _ hGGWP] at t₂
  rw [t₁, t₂]
  ring
end Algebra
section Families
variable {I : PeriodicData} (A W : JetQuad I I)
theorem unitShiftedPath_zero : unitShiftedPath A W 0 = addScalarJet A 1 := by
  apply JetQuad.ext <;> simp [unitShiftedPath, affinePath, add, smul]
theorem unitShiftedPath_one : unitShiftedPath A W 1 = addScalarJet (A.add W) 1 := by
  apply JetQuad.ext <;> simp [unitShiftedPath, affinePath, addScalarJet, add, smul] <;> abel
theorem addScalarJet_zero : addScalarJet (A.add W) 0 = A.add W := by
  apply JetQuad.ext <;> simp [addScalarJet, add, smul]
theorem addScalarJet_one_eq_shift (τ : ℝ) :
    addScalarJet A 1 = add (addScalarJet (A.add W) τ)
      (add (smul ((1 - τ : ℝ) : ℂ) (one I)) (smul (-1) W)) := by
  apply JetQuad.ext <;> simp only [addScalarJet, add, smul, one] <;> push_cast <;> module
end Families
theorem claim_holds
    (h₁ : JetNormsAffine.Claim)
    (h₂ : JetCalculus.Claim)
    (h₃ : JetDomains.OpFunJetTheory)
    (h₄ : JetArgumentsAndEqualJets)
    (h₅ : QuadAlgebra.Claim) :
    Claim := by
  intro δ p hδ hp I hI A W hA hW hinv₁ hinv₂ hb₁ hb₂
  have F := h₃.2.2 I I I hI hI hI δ p hδ hp
  have mulj := F.mul_isJet
  have hX := F.add_isJet A W hA hW
  have hone := F.one_isJet
  have hB : IsJet δ p (addScalarJet A 1) := F.add_isJet _ _ hA (F.smul_isJet _ _ hone)
  have z0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have z1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  have hJc : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  have hJo : (Icc (0 : ℝ) 1).OrdConnected := ordConnected_Icc
  have hJn : (Icc (0 : ℝ) 1).Nontrivial := ⟨0, z0, 1, z1, zero_ne_one⟩
  have m := (h₁ δ p hδ hp I I hI hI).2 (addScalarJet A 1) W hB hW _ hJc hJo hJn hinv₁ hb₁
  have n := (h₁ δ p hδ hp I I hI hI).2 (A.add W) (one I) hX hone _ hJc hJo hJn hinv₂ hb₂
  have hBinv : IsInvertibleJet δ p (addScalarJet A 1) := by
    have := hinv₁ 0 z0
    rwa [unitShiftedPath_zero] at this
  have hG : IsJet δ p (unitShiftedInverse p A) := ((h₂ δ p hδ hp).2.2.2.2.1 I hI _ hBinv).1
  have hGG := mulj _ _ hG hG
  have hGW := mulj _ _ hG hW
  have hGGW := mulj _ _ hGG hW
  have cs : ContinuousOn (fun τ : ℝ => (((1 - τ : ℝ)) : ℂ)) (Icc 0 1) :=
    (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).continuousOn
  have c₁ : ContinuousOn (fun τ => traceNumber (mul p (mul p (unitShiftedInverse p A)
      (unitShiftedInverse p A)) (perturbedInverse p A W τ))) (Icc 0 1) := n.2.2.1 _ hGG
  have c₂ : ContinuousOn (fun τ => traceNumber (mul p (mul p (unitShiftedInverse p A) W)
      (perturbedInverse p A W τ))) (Icc 0 1) := n.2.2.1 _ hGW
  have c₃ : ContinuousOn (fun τ => traceNumber (mul p (mul p (mul p (unitShiftedInverse p A)
      (unitShiftedInverse p A)) W) (perturbedInverse p A W τ))) (Icc 0 1) := n.2.2.1 _ hGGW
  have hcont : ContinuousOn (correctionIntegrand p A W) (Icc 0 1) :=
    (((cs.pow 2).mul c₁).sub c₂).sub (cs.mul c₃)
  refine ⟨hcont, ?_⟩
  have ftc₁ : logNumber p (addScalarJet (A.add W) 1) -
      logNumber p (addScalarJet A 1) =
        ∫ t in (0 : ℝ)..1, traceNumber (mul p (invJet p (unitShiftedPath A W t)) W) := by
    have h := m.2.2.2.2.2 0 z0 1 z1
    change logNumber p (unitShiftedPath A W 1) - logNumber p (unitShiftedPath A W 0) =
      _ at h
    rwa [unitShiftedPath_one, unitShiftedPath_zero] at h
  have ftc₂ : logNumber p (addScalarJet (A.add W) 1) -
      logNumber p (A.add W) =
        ∫ τ in (0 : ℝ)..1, traceNumber (perturbedInverse p A W τ) := by
    have h := n.2.2.2.2.2 0 z0 1 z1
    change logNumber p (addScalarJet (A.add W) 1) -
      logNumber p (addScalarJet (A.add W) 0) =
        ∫ t in (0 : ℝ)..1, traceNumber (mul p (perturbedInverse p A W t) (one I)) at h
    rw [addScalarJet_zero] at h
    simpa only [((h₅.1 p I I I).2.2.2.2 _).2] using h
  have hform : ∀ τ ∈ Icc (0 : ℝ) 1, traceNumber (perturbedInverse p A W τ) =
      traceNumber (unitShiftedInverse p A) +
        ((1 - τ : ℝ) : ℂ) * traceNumber (mul p (unitShiftedInverse p A) (unitShiftedInverse p A)) +
        correctionIntegrand p A W τ := by
    intro τ hτ
    have hTinv := hinv₂ τ hτ
    have hP : IsJet δ p (perturbedInverse p A W τ) := ((h₂ δ p hδ hp).2.2.2.2.1 I hI _ hTinv).1
    exact traceNumber_resolvent_expansion h₂ h₃ h₄ h₅ hδ hp hI hG hP hW
      (invJet_eq_resolvent_expansion h₂ h₃ h₄ h₅ hδ hp hI hBinv hTinv hW
        (addScalarJet_one_eq_shift A W τ))
  have hhalf : ∫ τ in (0 : ℝ)..1, (((1 - τ : ℝ)) : ℂ) = 1 / 2 := by
    rw [intervalIntegral.integral_ofReal]
    have : ∫ τ in (0 : ℝ)..1, (1 - τ) = 1 / 2 := by
      rw [intervalIntegral.integral_sub (by simp) (by simp)]
      norm_num [integral_id]
    rw [this]
    norm_num
  have hi₁ : IntervalIntegrable (fun τ : ℝ => (((1 - τ : ℝ)) : ℂ) *
      traceNumber (mul p (unitShiftedInverse p A) (unitShiftedInverse p A))) volume 0 1 :=
    ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul
      continuous_const).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (correctionIntegrand p A W) volume 0 1 :=
    ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le zero_le_one])
  have hint : ∫ τ in (0 : ℝ)..1, traceNumber (perturbedInverse p A W τ) =
      traceNumber (unitShiftedInverse p A) +
        1 / 2 * traceNumber (mul p (unitShiftedInverse p A) (unitShiftedInverse p A)) +
        ∫ τ in (0 : ℝ)..1, correctionIntegrand p A W τ := by
    rw [intervalIntegral.integral_congr (g := fun τ => traceNumber (unitShiftedInverse p A) +
        ((1 - τ : ℝ) : ℂ) * traceNumber (mul p (unitShiftedInverse p A) (unitShiftedInverse p A)) +
        correctionIntegrand p A W τ)
      (fun τ hτ => hform τ (by rwa [uIcc_of_le zero_le_one] at hτ))]
    rw [intervalIntegral.integral_add ((intervalIntegrable_const).add hi₁) hi₂,
      intervalIntegral.integral_add intervalIntegrable_const hi₁,
      intervalIntegral.integral_mul_const, hhalf]
    simp
  have hsq : traceNumber (invJetSq p (addScalarJet A 1)) =
      traceNumber (mul p (unitShiftedInverse p A) (unitShiftedInverse p A)) := rfl
  rw [hsq]
  unfold pathRemainder
  linear_combination ftc₁ - ftc₂ - hint
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.LogNumberInterpolation
end
