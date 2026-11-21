import YangMills.Construction.PeriodicOperators.ExponentialSumsTorusWavesAndComponentSets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetDomains
open JetQuad (IsJet EqAsJet)
section OpFuns
variable (F I I' : PeriodicData)
structure OpFunJetProperties (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) : Prop where
  triple_unique : ∀ (p : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ),
    ActionTripleUnique F I I' T p εp εm
  entries_f10 : ∀ (c' : I'.UnitQuot) (c : I.UnitQuot), ∃ (n : ℕ) (f : Fin n → MomentumLinearForm)
    (a : Fin n → (F.UnitQuot → ℂ) →ₗ[ℂ] ℂ), ∀ (p κ : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ),
      linearMapEntry ((jetAlong F I I' T p εp εm).f10 κ) c' c =
        expSum (fun j => a j εp) f κ p
  entries_f01 : ∀ (c' : I'.UnitQuot) (c : I.UnitQuot), ∃ (n : ℕ) (f : Fin n → MomentumLinearForm)
    (a : Fin n → (F.UnitQuot → ℂ) →ₗ[ℂ] ℂ), ∀ (p κ : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ),
      linearMapEntry ((jetAlong F I I' T p εp εm).f01 κ) c' c =
        expSum (fun j => a j εm) f κ p
  entries_f11 : ∀ (c' : I'.UnitQuot) (c : I.UnitQuot), ∃ (n : ℕ) (f : Fin n → MomentumLinearForm)
    (a : Fin n → (F.UnitQuot → ℂ) →ₗ[ℂ] (F.UnitQuot → ℂ) →ₗ[ℂ] ℂ),
    ∀ (p κ : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ),
      linearMapEntry ((jetAlong F I I' T p εp εm).f11 κ) c' c =
        expSum (fun j => a j εp εm) f κ p
  entire_f10 : ∀ (εp εm : F.UnitQuot → ℂ) (c' : I'.UnitQuot) (c : I.UnitQuot),
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4 + 4) (N' := 1) univ fun z _ =>
      linearMapEntry ((jetAlong F I I' T (sndMomentum z) εp εm).f10 (fstMomentum z)) c' c
  entire_f01 : ∀ (εp εm : F.UnitQuot → ℂ) (c' : I'.UnitQuot) (c : I.UnitQuot),
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4 + 4) (N' := 1) univ fun z _ =>
      linearMapEntry ((jetAlong F I I' T (sndMomentum z) εp εm).f01 (fstMomentum z)) c' c
  entire_f11 : ∀ (εp εm : F.UnitQuot → ℂ) (c' : I'.UnitQuot) (c : I.UnitQuot),
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4 + 4) (N' := 1) univ fun z _ =>
      linearMapEntry ((jetAlong F I I' T (sndMomentum z) εp εm).f11 (fstMomentum z)) c' c
  quasiPeriodic : ∀ (p : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ),
    IsQuasiPeriodic univ (jetAlong F I I' T p εp εm).f00 ∧
      IsQuasiPeriodic univ (jetAlong F I I' T p εp εm).f10 ∧
      IsQuasiPeriodic univ (jetAlong F I I' T p εp εm).f01 ∧
      IsQuasiPeriodic univ (jetAlong F I I' T p εp εm).f11
  isJet : ∀ (δ : ℝ), 0 < δ → ∀ p ∈ imStrip δ, ∀ εp εm : F.UnitQuot → ℂ,
    IsJet δ p (jetAlong F I I' T p εp εm)
  descends : ∀ ρ R : ℝ, IsLocalWith F I I' T ρ R → ∀ s : ℕ, 0 < s → 4 * R < s →
    ∀ κ ∈ dualLattice s, ∀ p ∈ dualLattice s, ∀ (εp εm : F.UnitQuot → ℂ) (φ : I.UnitQuot → ℂ),
      WavesDescend F I s κ p εp εm φ ∧
        JetRelationsDescend F I I' T s κ p εp εm φ
end OpFuns
structure JetAlgebra (I I' I'' : PeriodicData) (δ : ℝ) (p : Fin 4 → ℂ) : Prop where
  imStrip_subset : imStrip δ ⊆ stripAddShift δ p ∧ imStrip δ ⊆ stripSubShift δ p
  sups_finite : ∀ T : JetQuad I I', IsJet δ p T → SupsFinite δ p T
  add_defined : ∀ T S : JetQuad I I', IsJet δ p T → IsJet δ p S →
    ∀ O O', AreNhds δ p O → AreNhds δ p O' →
      HolomorphicOnDomains O T → HolomorphicOnDomains O' S →
        ∃ N, AreNhds δ p N ∧ AddDefinedOn O O' N ∧
          HolomorphicOnDomains N (JetQuad.add T S)
  add_isJet : ∀ T S : JetQuad I I', IsJet δ p T → IsJet δ p S → IsJet δ p (JetQuad.add T S)
  smul_defined : ∀ (a : ℂ) (T : JetQuad I I'), IsJet δ p T →
    ∀ O, AreNhds δ p O → HolomorphicOnDomains O T →
      ∃ N, AreNhds δ p N ∧ SMulDefinedOn O N ∧
        HolomorphicOnDomains N (JetQuad.smul a T)
  smul_isJet : ∀ (a : ℂ) (T : JetQuad I I'), IsJet δ p T → IsJet δ p (JetQuad.smul a T)
  mul_defined : ∀ (T : JetQuad I I') (S : JetQuad I'' I), IsJet δ p T → IsJet δ p S →
    ∀ O O', AreNhds δ p O → AreNhds δ p O' →
      HolomorphicOnDomains O T → HolomorphicOnDomains O' S →
        ∃ N, AreNhds δ p N ∧ MulDefinedOn p O O' N ∧
          HolomorphicOnDomains N (JetQuad.mul p T S)
  mul_isJet : ∀ (T : JetQuad I I') (S : JetQuad I'' I), IsJet δ p T → IsJet δ p S →
    IsJet δ p (JetQuad.mul p T S)
  transpose_defined : ∀ T : JetQuad I I', IsJet δ p T →
    ∀ O, AreNhds δ p O → HolomorphicOnDomains O T →
      ∃ N, AreNhds δ p N ∧ TransposeDefinedOn p O N ∧
        HolomorphicOnDomains N (JetQuad.transposeAt p T)
  transpose_isJet : ∀ T : JetQuad I I', IsJet δ p T → IsJet δ p (JetQuad.transposeAt p T)
  ofKernel_isJet : ∀ T : I'.Carrier → I.Carrier → ℂ, IsPeriodicKernel I I' T →
    SymbolHolomorphicNear I I' (imStrip (2 * δ)) T → IsJet δ p (JetQuad.ofKernel I I' T)
  one_isJet : IsJet δ p (JetQuad.one I)
  zeroPart_isJet : ∀ T : JetQuad I I, JetQuad.IsInvertibleJet δ p T →
    IsJet δ p (JetQuad.zeroPart T) ∧ IsJet δ p (JetQuad.zeroPartInv T)
  zeroPart_inv : ∀ T : JetQuad I I, JetQuad.IsInvertibleJet δ p T →
    EqAsJet δ p (JetQuad.mul p (JetQuad.zeroPartInv T) (JetQuad.zeroPart T))
        (JetQuad.one I) ∧
      EqAsJet δ p (JetQuad.mul p (JetQuad.zeroPart T) (JetQuad.zeroPartInv T))
        (JetQuad.one I)
  invertible_derived_isJet : ∀ T : JetQuad I I, JetQuad.IsInvertibleJet δ p T →
    IsJet δ p (JetQuad.mul p (JetQuad.zeroPartInv T) T) ∧
      IsJet δ p (JetQuad.normalize p T) ∧
      IsJet δ p (JetQuad.mul p (JetQuad.normalize p T) (JetQuad.normalize p T)) ∧
      IsJet δ p (JetQuad.logSeries p T)
  normalize_logNumber_wellFormed : ∀ T : JetQuad I I, JetQuad.IsInvertibleJet δ p T →
    JetQuad.NormalizeWellFormed δ p T ∧ JetQuad.LogNumberWellFormed δ p T
def OpFunJetTheory : Prop :=
  (∀ F I I' I'' : PeriodicData, IsPeriodic F → IsPeriodic I →
    IsPeriodic I' → IsPeriodic I'' →
      (∀ T T' : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ,
        IsLocalOpFun F I I' T → IsLocalOpFun F I I' T' →
          IsLocalOpFun F I I' (opFunAdd T T')) ∧
      (∀ (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ)
        (S : (F.Carrier → ℂ) → I.Carrier → I''.Carrier → ℂ),
        IsLocalOpFun F I I' T → IsLocalOpFun F I'' I S →
          IsLocalOpFun F I'' I' (opFunComp T S)) ∧
      ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ,
        IsLocalOpFun F I I' T → IsLocalOpFun F I' I (opFunTranspose T)) ∧
  (∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' T →
      OpFunJetProperties F I I' T) ∧
  ∀ I I' I'' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    IsPeriodic I'' → ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
      JetAlgebra I I' I'' δ p
end YangMills.Construction.PeriodicOperators.JetDomains
end
