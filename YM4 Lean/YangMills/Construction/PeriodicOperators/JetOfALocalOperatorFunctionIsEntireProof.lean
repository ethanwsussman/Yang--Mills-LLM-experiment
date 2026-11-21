import YangMills.Construction.PeriodicOperators.IntegrandOfTheLogarithmicNumberOfAFunctionProof
import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.JetOfALocalOperatorFunctionIsEntire
import YangMills.Construction.PeriodicOperators.JetTripleOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.QuasiPeriodicityOfTheJetOfAFunction
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfALocalOperatorFunction
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LocalJetEntire
open JetDomains
open LocalOpFunTaylor
theorem holomorphicIn_of_differentiable {N : ℕ} {g : Coordinates.ComplexCoordinates N → ℂ}
    (hg : Differentiable ℂ g) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) univ fun z _ => g z := by
  refine ⟨isOpen_univ, (continuous_pi fun _ => hg.continuous).continuousOn,
    fun a _ j => Filter.Eventually.of_forall fun ζ => ?_⟩
  have hline : Differentiable ℂ fun ζ : ℂ =>
      a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j :=
    (differentiable_const a).add (differentiable_id.smul_const _)
  exact differentiableAt_pi.2 fun _ => (hg.comp hline) ζ
theorem differentiable_expSum_pair {n : ℕ} (a : Fin n → ℂ) (f : Fin n → MomentumLinearForm) :
    Differentiable ℂ fun w : (Fin 4 → ℂ) × (Fin 4 → ℂ) => expSum a f w.1 w.2 := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.differentiable_expSum_fst <;> assumption
theorem holomorphicIn_of_expSum {n : ℕ} {g : Coordinates.ComplexCoordinates (4 + 4) → ℂ}
    (a : Fin n → ℂ) (f : Fin n → MomentumLinearForm)
    (h : ∀ z, g z = expSum a f (fstMomentum z) (sndMomentum z)) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) univ fun z _ => g z := by
  have hpair : Differentiable ℂ fun z : Coordinates.ComplexCoordinates (4 + 4) =>
      (fstMomentum z, sndMomentum z) :=
    (differentiable_pi.2 fun μ => differentiable_apply _).prodMk
      (differentiable_pi.2 fun μ => differentiable_apply _)
  have hg : g = fun z => expSum a f (fstMomentum z) (sndMomentum z) := funext h
  rw [hg]
  exact holomorphicIn_of_differentiable ((differentiable_expSum_pair a f).comp hpair)
theorem isHolomorphicNbhd_of_expSum {P P' : PeriodicData} (D : Set (Fin 4 → ℂ)) (p : Fin 4 → ℂ)
    {A : (Fin 4 → ℂ) → QuotHom P P'}
    (h : ∀ u' u, ∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → MomentumLinearForm),
      ∀ κ, linearMapEntry (A κ) u' u = expSum a f κ p) :
    IsHolomorphicNbhd D A := by
  refine ⟨univ, isOpen_univ, subset_univ _, fun u' u => ?_⟩
  obtain ⟨n, a, f, hs⟩ := h u' u
  have hslice : Differentiable ℂ fun κ : Fin 4 → ℂ => (κ, p) :=
    differentiable_id.prodMk (differentiable_const p)
  have hg : (fun (κ : Fin 4 → ℂ) (_ : Fin 1) => linearMapEntry (A κ) u' u) =
      fun κ _ => expSum a f κ p := by
    funext κ _
    exact hs κ
  rw [hg]
  exact holomorphicIn_of_differentiable ((differentiable_expSum_pair a f).comp hslice)
theorem linearMapEntry_linearMapOfEntries {J J' : Type} [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
theorem linearMapEntry_symbolHom {P P' : PeriodicData} (hP : IsPeriodic P)
    (Z : P'.Carrier → P.Carrier → ℂ) (κ : Fin 4 → ℂ)
    (hdep : ∀ x₁' x₂' x₁ x₂, P'.mkQuot 1 x₁' = P'.mkQuot 1 x₂' →
      P.mkQuot 1 x₁ = P.mkQuot 1 x₂ → fourierSymbol P P' Z κ x₁' x₁ = fourierSymbol P P' Z κ x₂' x₂)
    (x' : P'.Carrier) (x : P.Carrier) :
    linearMapEntry (symbolHom P P' Z κ) (P'.mkQuot 1 x') (P.mkQuot 1 x) =
      fourierSymbol P P' Z κ x' x := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.carrierEntry_symbolHom <;> assumption
theorem isDecayRate_idKernel_one (P : PeriodicData) : IsDecayRate P P (idKernel P) 1 := by
  refine ⟨one_pos, 1, one_pos, fun x' x => ?_⟩
  by_cases h : x' = x
  · subst h
    simp [idKernel, TorusMetric.euclidNormVec]
  · simp only [idKernel, if_neg h, norm_zero]
    positivity
theorem isHolomorphicNbhd_symbolHom_coeffZero {Q P P' : PeriodicData}
    (hD : CovariantFiniteRange.Claim)
    (hJ : LocalOpFunTaylor.Claim)
    (hS : Symbols.Claim)
    (hQ : IsPeriodic Q) (hP : IsPeriodic P) (hP' : IsPeriodic P')
    {T : (Q.Carrier → ℂ) → P'.Carrier → P.Carrier → ℂ} (hT : IsLocalOpFun Q P P' T)
    (D : Set (Fin 4 → ℂ)) :
    IsHolomorphicNbhd D (symbolHom P P' (coeffZero Q P P' T)) := by
  obtain ⟨ρ, R, hM⟩ := hT
  have hcov : IsPhaseCovariant P P' 0 (coeffZero Q P P' T) := by
    intro n x' x
    have h := (hJ Q P P' hQ hP hP' T ρ R hM 0 0 x' x n).2.2.1.1
    simpa [bilinDot] using h
  have hvan : VanishesOutsideRadius P P' R (coeffZero Q P P' T) := by
    intro x' x h
    have hswap : TorusMetric.euclidNormVec (P.pos x - P'.pos x') =
        TorusMetric.euclidNormVec (P'.pos x' - P.pos x) := by
      simp only [TorusMetric.euclidNormVec, Pi.sub_apply]
      congr 1
      exact Finset.sum_congr rfl fun μ _ => by ring
    exact ((hJ Q P P' hQ hP hP' T ρ R hM 0 0 x' x 0).2.1.2 (by rwa [hswap])).1
  have hphase : dephasedKernel P P' 0 (coeffZero Q P P' T) = coeffZero Q P P' T := by
    funext x' x
    simp [dephasedKernel, bilinDot]
  obtain ⟨hop, -, hentire, -⟩ := hD.2 P P' hP hP' 0 R _ hcov hvan
  rw [hphase] at hop hentire
  have hfacts := hS.1 P P' P hP hP' hP (coeffZero Q P P' T) (idKernel P) 1
    hop.periodic (hop.decays 1 one_pos) (hD.1 P hP).2.1 (isDecayRate_idKernel_one P)
  refine ⟨univ, isOpen_univ, subset_univ _, fun u' u => ?_⟩
  obtain ⟨x', rfl⟩ := Quot.exists_rep (show P'.QuotMod 1 from u')
  obtain ⟨x, rfl⟩ := Quot.exists_rep (show P.QuotMod 1 from u)
  have hg : (fun (κ : Fin 4 → ℂ) (_ : Fin 1) =>
      linearMapEntry (symbolHom P P' (coeffZero Q P P' T) κ) (Quot.mk _ x') (Quot.mk _ x)) =
      fun κ _ => fourierSymbol P P' (coeffZero Q P P' T) κ x' x := by
    funext κ _
    exact linearMapEntry_symbolHom hP _ κ
      (hfacts.eq_of_mkQuot_eq κ (hop.summable κ (mem_univ κ))) x' x
  rw [hg]
  exact hentire x' x
theorem claim_holds (hTriple : LocalOpFunTriple.Claim)
    (hQuasi : JetQuasiPeriodic.Claim)
    (hD : CovariantFiniteRange.Claim)
    (hJ : LocalOpFunTaylor.Claim)
    (hS : Symbols.Claim) : Claim := by
  intro Q P P' hQ hP hP' T hT
  obtain ⟨-, h10, h01, h11⟩ := hTriple Q P P' hQ hP hP' T hT
  refine ⟨fun εp εm u' u => ?_, fun εp εm u' u => ?_,
    fun εp εm u' u => ?_, fun δ hδ p hp εp εm => ?_⟩
  · obtain ⟨n, f, a, h⟩ := h10 u' u
    exact holomorphicIn_of_expSum (fun j => a j εp) f fun z => h _ _ _ _
  · obtain ⟨n, f, a, h⟩ := h01 u' u
    exact holomorphicIn_of_expSum (fun j => a j εm) f fun z => h _ _ _ _
  · obtain ⟨n, f, a, h⟩ := h11 u' u
    exact holomorphicIn_of_expSum (fun j => a j εp εm) f fun z => h _ _ _ _
  · obtain ⟨q00, q10, q01, q11⟩ := hQuasi Q P P' hQ hP hP' T hT p εp εm
    have hn10 : ∀ D, IsHolomorphicNbhd D (jetAlong Q P P' T p εp εm).f10 := fun D =>
      isHolomorphicNbhd_of_expSum D p fun u' u => by
        obtain ⟨n, f, a, h⟩ := h10 u' u
        exact ⟨n, fun j => a j εp, f, fun κ => h p κ εp εm⟩
    have hn01 : ∀ D, IsHolomorphicNbhd D (jetAlong Q P P' T p εp εm).f01 := fun D =>
      isHolomorphicNbhd_of_expSum D p fun u' u => by
        obtain ⟨n, f, a, h⟩ := h01 u' u
        exact ⟨n, fun j => a j εm, f, fun κ => h p κ εp εm⟩
    have hn11 : ∀ D, IsHolomorphicNbhd D (jetAlong Q P P' T p εp εm).f11 := fun D =>
      isHolomorphicNbhd_of_expSum D p fun u' u => by
        obtain ⟨n, f, a, h⟩ := h11 u' u
        exact ⟨n, fun j => a j εp εm, f, fun κ => h p κ εp εm⟩
    exact
      { pos_width := hδ
        mem_imStrip := hp
        holo_f00 := isHolomorphicNbhd_symbolHom_coeffZero hD hJ hS hQ hP hP' hT _
        holo_f10 := hn10 _
        holo_f01 := hn01 _
        holo_f11 := hn11 _
        quasiPeriodic_f00 := fun e κ _ => q00 e κ (mem_univ κ)
        quasiPeriodic_f10 := fun e κ _ => q10 e κ (mem_univ κ)
        quasiPeriodic_f01 := fun e κ _ => q01 e κ (mem_univ κ)
        quasiPeriodic_f11 := fun e κ _ => q11 e κ (mem_univ κ) }
end YangMills.Construction.PeriodicOperators.LocalJetEntire
end
