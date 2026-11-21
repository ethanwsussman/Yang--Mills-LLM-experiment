import YangMills.Construction.Coordinates.HolomorphicIffDifferentiable
import YangMills.Construction.PeriodicOperators.CalculusOfSymbols
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.KernelsOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.SymbolsOnStrips
import YangMills.Construction.Towers.ComponentsOfTheJetAlongHolomorphicAmplitudes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.JetAlongAmplitudes
open Coordinates
open PeriodicOperators
open PeriodicOperators.JetDomains
open Tower.FullSpace.ScaledOperatorFunctions
theorem differentiable_fstMomentum : Differentiable ℂ fstMomentum :=
  differentiable_pi.2 fun _ => differentiable_apply _
theorem differentiable_sndMomentum : Differentiable ℂ sndMomentum :=
  differentiable_pi.2 fun _ => differentiable_apply _
theorem appendSet_univ_prod (O : Set (ComplexCoordinates 4)) :
    appendSet (univ ×ˢ O : Set (ComplexCoordinates 4 × ComplexCoordinates 4)) =
      {z | sndMomentum z ∈ O} := by
  ext z
  constructor
  · rintro ⟨⟨κ, p⟩, ⟨-, hp⟩, rfl⟩
    have e : sndMomentum (appendCoords κ p) = p := by
      funext μ
      exact Fin.append_right κ p μ
    simpa [e] using hp
  · intro h
    refine ⟨(fstMomentum z, sndMomentum z), ⟨mem_univ _, h⟩, ?_⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · exact Fin.append_left _ _ i
    · exact Fin.append_right _ _ i
theorem isHolomorphicInMomentumPair_of_differentiableOn {I I' : PeriodicData}
    (hD : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    {O : Set (ComplexCoordinates 4)} (hO : IsOpen O)
    (A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I')
    (h : ∀ c' c, DifferentiableOn ℂ
      (fun z : ComplexCoordinates (4 + 4) => linearMapEntry (A (sndMomentum z) (fstMomentum z)) c' c)
      {z | sndMomentum z ∈ O}) :
    IsHolomorphicInMomentumPair (univ ×ˢ O) A := by
  have hopen : IsOpen
      (appendSet (univ ×ˢ O : Set (ComplexCoordinates 4 × ComplexCoordinates 4))) := by
    rw [appendSet_univ_prod]
    exact hO.preimage differentiable_sndMomentum.continuous
  refine ⟨by norm_num, hopen, fun e => ?_⟩
  refine (hD _ _ _ _ hopen).2 (differentiableOn_pi.2 fun _ => ?_)
  rw [appendSet_univ_prod]
  exact h e.1 e.2
theorem differentiableOn_expSum {m : ℕ} {W : Set (ComplexCoordinates (4 + 4))}
    (a : Fin m → ComplexCoordinates (4 + 4) → ℂ) (f : Fin m → MomentumLinearForm)
    (ha : ∀ j, DifferentiableOn ℂ (a j) W) :
    DifferentiableOn ℂ
      (fun z => expSum (fun j => a j z) f (fstMomentum z) (sndMomentum z)) W := by
  unfold expSum
  refine DifferentiableOn.fun_sum fun j _ => (ha j).mul ?_
  have hpair : Differentiable ℂ fun z : ComplexCoordinates (4 + 4) =>
      (fstMomentum z, sndMomentum z) :=
    differentiable_fstMomentum.prodMk differentiable_sndMomentum
  exact (Complex.differentiable_exp.comp
    ((LinearMap.toContinuousLinearMap (f j)).differentiable.comp hpair)).differentiableOn
section Amplitudes
variable {J : Type} [Fintype J]
theorem differentiableOn_amplitude_comp
    (hD : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    {O : Set (ComplexCoordinates 4)} {ε : ComplexCoordinates 4 → J → ℂ}
    (hO : IsOpen O)
    (h : ∀ c, ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun x _ => ε x c) :
    DifferentiableOn ℂ (fun z : ComplexCoordinates (4 + 4) => ε (sndMomentum z))
      {z | sndMomentum z ∈ O} := by
  have hε : DifferentiableOn ℂ ε O :=
    differentiableOn_pi.2 fun c => differentiableOn_pi.1 ((hD _ _ _ _ hO).1 (h c)) 0
  exact hε.comp differentiable_sndMomentum.differentiableOn fun _ hz => hz
theorem differentiableOn_linearMap_comp {W : Set (ComplexCoordinates (4 + 4))}
    {g : ComplexCoordinates (4 + 4) → J → ℂ} (hg : DifferentiableOn ℂ g W)
    (a : (J → ℂ) →ₗ[ℂ] ℂ) : DifferentiableOn ℂ (fun z => a (g z)) W :=
  (LinearMap.toContinuousLinearMap a).differentiable.comp_differentiableOn hg
theorem differentiableOn_bilinear_comp {W : Set (ComplexCoordinates (4 + 4))}
    {g h : ComplexCoordinates (4 + 4) → J → ℂ} (hg : DifferentiableOn ℂ g W)
    (hh : DifferentiableOn ℂ h W) (a : (J → ℂ) →ₗ[ℂ] (J → ℂ) →ₗ[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z => a (g z) (h z)) W := by
  classical
  have e : (fun z => a (g z) (h z)) =
      fun z => ∑ c, h z c * a.flip (Pi.single c 1) (g z) := by
    funext z
    have hz : h z = ∑ c, h z c • (Pi.single c 1 : J → ℂ) := by
      funext c
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hz]
    simp [map_sum]
  rw [e]
  refine DifferentiableOn.fun_sum fun c _ => ?_
  exact (differentiableOn_pi.1 hh c).mul (differentiableOn_linearMap_comp hg _)
end Amplitudes
theorem jetComponents_holomorphic {F I I' : PeriodicData}
    (hD : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (hJets : JetDomains.OpFunJetTheory)
    (hK : OpFunKernels.Claim)
    (hC : SymbolCalculus.Claim) (hS : StripSymbols.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (hT : IsLocalOpFun F I I' T)
    (O : Set (ComplexCoordinates 4)) (εPlus εMinus : ComplexCoordinates 4 → F.UnitQuot → ℂ)
    (hPlus : HolomorphicOnEntrywise quotFnEntries O εPlus)
    (hMinus : HolomorphicOnEntrywise quotFnEntries O εMinus) :
    IsHolomorphicInMomentumPair (univ ×ˢ O)
        (fun p => (jetAlong F I I' T p (εPlus p) (εMinus p)).f00) ∧
      IsHolomorphicInMomentumPair (univ ×ˢ O)
        (fun p => (jetAlong F I I' T p (εPlus p) (εMinus p)).f10) ∧
      IsHolomorphicInMomentumPair (univ ×ˢ O)
        (fun p => (jetAlong F I I' T p (εPlus p) (εMinus p)).f01) ∧
      IsHolomorphicInMomentumPair (univ ×ˢ O)
        (fun p => (jetAlong F I I' T p (εPlus p) (εMinus p)).f11) := by
  have hO : IsOpen O := hPlus.2.1
  have := hF.finite_quot
  cases nonempty_fintype F.UnitQuot
  have dPlus := differentiableOn_amplitude_comp hD hO hPlus.2.2
  have dMinus := differentiableOn_amplitude_comp hD hO hMinus.2.2
  have facts := hJets.2.1 F I I' hF hI hI' T hT
  refine ⟨isHolomorphicInMomentumPair_of_differentiableOn hD hO _ fun c' c => ?_,
    isHolomorphicInMomentumPair_of_differentiableOn hD hO _ fun c' c => ?_,
    isHolomorphicInMomentumPair_of_differentiableOn hD hO _ fun c' c => ?_,
    isHolomorphicInMomentumPair_of_differentiableOn hD hO _ fun c' c => ?_⟩
  · have hop := (hK F I I' hF hI hI' T hT).1
    have hsym := (hC I I' hI hI').1 _ hop.periodic hop.finiteRange
    have hfacts := (hS.2.1 I I' hI hI').2.1
    obtain ⟨ι', rfl⟩ := Quot.exists_rep (show I'.QuotMod 1 from c')
    obtain ⟨ι, rfl⟩ := Quot.exists_rep (show I.QuotMod 1 from c)
    have hent : ∀ κ, linearMapEntry (symbolHom I I' (coeffZero F I I' T) κ)
        (Quot.mk _ ι') (Quot.mk _ ι) = fourierSymbol I I' (coeffZero F I I' T) κ ι' ι := fun κ =>
      (hfacts _ κ hop.periodic (hop.summable κ (mem_univ κ))).carrierEntry_symbolHom ι' ι
    have hdiff : Differentiable ℂ fun κ : Fin 4 → ℂ =>
        fourierSymbol I I' (coeffZero F I I' T) κ ι' ι :=
      differentiableOn_univ.1
        (differentiableOn_pi.1 ((hD _ _ _ _ isOpen_univ).1 (hsym.2 ι' ι).2) 0)
    have e : (fun z : ComplexCoordinates (4 + 4) =>
        linearMapEntry ((jetAlong F I I' T (sndMomentum z) (εPlus (sndMomentum z))
          (εMinus (sndMomentum z))).f00 (fstMomentum z)) (Quot.mk _ ι') (Quot.mk _ ι)) =
        fun z => fourierSymbol I I' (coeffZero F I I' T) (fstMomentum z) ι' ι :=
      funext fun z => hent (fstMomentum z)
    rw [e]
    exact (hdiff.comp differentiable_fstMomentum).differentiableOn
  · obtain ⟨m, f, a, h⟩ := facts.entries_f10 c' c
    have e : (fun z : ComplexCoordinates (4 + 4) =>
        linearMapEntry ((jetAlong F I I' T (sndMomentum z) (εPlus (sndMomentum z))
          (εMinus (sndMomentum z))).f10 (fstMomentum z)) c' c) =
        fun z => expSum (fun j => a j (εPlus (sndMomentum z))) f
          (fstMomentum z) (sndMomentum z) :=
      funext fun z => h _ _ _ _
    rw [e]
    exact differentiableOn_expSum (fun j z => a j (εPlus (sndMomentum z))) f
      fun j => differentiableOn_linearMap_comp dPlus (a j)
  · obtain ⟨m, f, a, h⟩ := facts.entries_f01 c' c
    have e : (fun z : ComplexCoordinates (4 + 4) =>
        linearMapEntry ((jetAlong F I I' T (sndMomentum z) (εPlus (sndMomentum z))
          (εMinus (sndMomentum z))).f01 (fstMomentum z)) c' c) =
        fun z => expSum (fun j => a j (εMinus (sndMomentum z))) f
          (fstMomentum z) (sndMomentum z) :=
      funext fun z => h _ _ _ _
    rw [e]
    exact differentiableOn_expSum (fun j z => a j (εMinus (sndMomentum z))) f
      fun j => differentiableOn_linearMap_comp dMinus (a j)
  · obtain ⟨m, f, a, h⟩ := facts.entries_f11 c' c
    have e : (fun z : ComplexCoordinates (4 + 4) =>
        linearMapEntry ((jetAlong F I I' T (sndMomentum z) (εPlus (sndMomentum z))
          (εMinus (sndMomentum z))).f11 (fstMomentum z)) c' c) =
        fun z => expSum
          (fun j => a j (εPlus (sndMomentum z)) (εMinus (sndMomentum z))) f
          (fstMomentum z) (sndMomentum z) :=
      funext fun z => h _ _ _ _
    rw [e]
    exact differentiableOn_expSum
      (fun j z => a j (εPlus (sndMomentum z)) (εMinus (sndMomentum z))) f
      fun j => differentiableOn_bilinear_comp dPlus dMinus (a j)
theorem jetComponentsHolomorphicAlongAmplitudes_holds (hIndex : TowerIndexSets.Claim)
    (hJets : JetDomains.OpFunJetTheory)
    (hK : OpFunKernels.Claim)
    (hC : SymbolCalculus.Claim) (hS : StripSymbols.Claim)
    (hD : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement) :
    JetComponentsHolomorphicAlongAmplitudes := by
  intro L hL k _ I I' hI hI' T hT O εPlus εMinus hPlus hMinus
  exact jetComponents_holomorphic hD hJets hK hC hS (hIndex L hL k 0 (Nat.zero_le k)).2.1 hI hI' T hT
    O εPlus εMinus hPlus hMinus
end YangMills.Construction.Tower.FullSpace.JetAlongAmplitudes
end
