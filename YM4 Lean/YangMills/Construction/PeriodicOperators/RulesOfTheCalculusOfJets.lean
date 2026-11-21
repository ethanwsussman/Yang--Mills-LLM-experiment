import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators
section SigmaSets
variable {P : Type} (J : P → PeriodicData)
def sigmaQuotIn (b : P) : (J b).UnitQuot → (PeriodicData.sigma J).UnitQuot :=
  Quot.lift (fun x => (PeriodicData.sigma J).mkQuot 1 ⟨b, x⟩)
    (by
      rintro x _ ⟨n, rfl⟩
      exact Quot.sound ⟨n, rfl⟩)
def quotHomBlock (b : P) (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)) :
    QuotHom (J b) (J b) :=
  linearMapOfEntries fun u' u => linearMapEntry M (sigmaQuotIn J b u') (sigmaQuotIn J b u)
end SigmaSets
namespace JetQuad
variable {I I' : PeriodicData}
def zeroJet (I I' : PeriodicData) : JetQuad I I' :=
  ⟨0, 0, 0, 0⟩
def invJet (p : Fin 4 → ℂ) (T : JetQuad I I) : JetQuad I I :=
  mul p (add (add (one I) (smul (-1) (normalize p T))) (mul p (normalize p T) (normalize p T)))
    (zeroPartInv T)
section Blocks
variable {P : Type} (J : P → PeriodicData)
def diagBlock (b : P) (T : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J)) :
    JetQuad (J b) (J b) :=
  ⟨fun z => quotHomBlock J b (T.f00 z), fun z => quotHomBlock J b (T.f10 z),
    fun z => quotHomBlock J b (T.f01 z), fun z => quotHomBlock J b (T.f11 z)⟩
end Blocks
def IsBlockTriangular (δ : ℝ) (p : Fin 4 → ℂ) (J : Fin 2 → PeriodicData)
    (T : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J)) : Prop :=
  ∀ (u' : (J 1).UnitQuot) (u : (J 0).UnitQuot),
    (∀ z ∈ imStrip (2 * δ), linearMapEntry (T.f00 z) (sigmaQuotIn J 1 u') (sigmaQuotIn J 0 u) = 0) ∧
    (∀ z ∈ stripAddShift δ p, linearMapEntry (T.f10 z) (sigmaQuotIn J 1 u') (sigmaQuotIn J 0 u) = 0) ∧
    (∀ z ∈ stripSubShift δ p, linearMapEntry (T.f01 z) (sigmaQuotIn J 1 u') (sigmaQuotIn J 0 u) = 0) ∧
    ∀ z ∈ realDualPoints, linearMapEntry (T.f11 z) (sigmaQuotIn J 1 u') (sigmaQuotIn J 0 u) = 0
def HasC1FamilyDeriv (δ : ℝ) (p : Fin 4 → ℂ) (A : Set ℝ)
    (T T' : ℝ → JetQuad I I') : Prop :=
  ∀ t ∈ A,
    Tendsto
        (fun h : ℝ => jetNorm δ p
          (add (smul ((h⁻¹ : ℝ) : ℂ) (add (T (t + h)) (smul (-1) (T t)))) (smul (-1) (T' t))))
        (𝓝[{h | h ≠ 0 ∧ t + h ∈ A}] 0) (𝓝 0) ∧
      Tendsto (fun h : ℝ => jetNorm δ p (add (T' (t + h)) (smul (-1) (T' t))))
        (𝓝[{h | h ≠ 0 ∧ t + h ∈ A}] 0) (𝓝 0)
def logDensity (p : Fin 4 → ℂ) (T : JetQuad I I) (z : Fin 4 → ℂ) : ℂ :=
  LinearMap.trace ℂ (I.UnitQuot → ℂ)
    ((quotHomInverse (T.f00 z)).comp (T.f11 z) -
      (quotHomInverse (T.f00 z)).comp
        ((T.f10 (z - p)).comp ((quotHomInverse (T.f00 (z - p))).comp (T.f01 z))))
end JetQuad
namespace JetCalculus
open JetQuad
def MulAssocNormLe (δ : ℝ) (p : Fin 4 → ℂ) : Prop :=
  ∀ I₁ I₂ I₃ I₄ : PeriodicData, IsPeriodic I₁ → IsPeriodic I₂ →
    IsPeriodic I₃ → IsPeriodic I₄ →
    ∀ (T : JetQuad I₂ I₁) (S : JetQuad I₃ I₂) (R : JetQuad I₄ I₃),
      IsJet δ p T → IsJet δ p S → IsJet δ p R →
      EqAsJet δ p (mul p (mul p T S) R) (mul p T (mul p S R)) ∧
        jetNorm δ p (mul p T S) ≤ jetNorm δ p T * jetNorm δ p S
def TransposeMulNorm (δ : ℝ) (p : Fin 4 → ℂ) : Prop :=
  ∀ I₁ I₂ I₃ : PeriodicData, IsPeriodic I₁ → IsPeriodic I₂ →
    IsPeriodic I₃ →
    ∀ (T : JetQuad I₂ I₁) (S : JetQuad I₃ I₂), IsJet δ p T → IsJet δ p S →
      EqAsJet δ p (transposeAt p (mul p T S)) (mul p (transposeAt p S) (transposeAt p T)) ∧
        jetNorm δ p (transposeAt p T) = jetNorm δ p T
def JetAlongHom (δ : ℝ) (p : Fin 4 → ℂ) : Prop :=
  ∀ F I₁ I₂ I₃ : PeriodicData, IsPeriodic F → IsPeriodic I₁ →
    IsPeriodic I₂ → IsPeriodic I₃ →
    ∀ ζp ζm : F.UnitQuot → ℂ,
      (∀ T T' : (F.Carrier → ℂ) → I₁.Carrier → I₂.Carrier → ℂ,
        IsLocalOpFun F I₂ I₁ T → IsLocalOpFun F I₂ I₁ T' →
        EqAsJet δ p (jetAlong F I₂ I₁ (opFunAdd T T') p ζp ζm)
          (add (jetAlong F I₂ I₁ T p ζp ζm) (jetAlong F I₂ I₁ T' p ζp ζm))) ∧
      (∀ (T : (F.Carrier → ℂ) → I₁.Carrier → I₂.Carrier → ℂ)
          (S : (F.Carrier → ℂ) → I₂.Carrier → I₃.Carrier → ℂ),
        IsLocalOpFun F I₂ I₁ T → IsLocalOpFun F I₃ I₂ S →
        EqAsJet δ p (jetAlong F I₃ I₁ (opFunComp T S) p ζp ζm)
          (mul p (jetAlong F I₂ I₁ T p ζp ζm) (jetAlong F I₃ I₂ S p ζp ζm))) ∧
      ∀ T : (F.Carrier → ℂ) → I₁.Carrier → I₂.Carrier → ℂ,
        IsLocalOpFun F I₂ I₁ T →
        EqAsJet δ p (jetAlong F I₁ I₂ (opFunTranspose T) p ζp ζm)
          (transposeAt p (jetAlong F I₂ I₁ T p ζp ζm))
def TripleMulOfZeroPartZero (δ : ℝ) (p : Fin 4 → ℂ) : Prop :=
  ∀ I₁ I₂ I₃ I₄ : PeriodicData, IsPeriodic I₁ → IsPeriodic I₂ →
    IsPeriodic I₃ → IsPeriodic I₄ →
    ∀ (T : JetQuad I₂ I₁) (S : JetQuad I₃ I₂) (R : JetQuad I₄ I₃),
      IsJet δ p T → IsJet δ p S → IsJet δ p R →
      EqOn T.f00 0 (imStrip (2 * δ)) → EqOn S.f00 0 (imStrip (2 * δ)) →
      EqOn R.f00 0 (imStrip (2 * δ)) →
      EqAsJet δ p (mul p (mul p T S) R) (zeroJet I₄ I₁)
def InvJetSpec (δ : ℝ) (p : Fin 4 → ℂ) : Prop :=
  ∀ I : PeriodicData, IsPeriodic I → ∀ T : JetQuad I I, IsInvertibleJet δ p T →
    IsJet δ p (invJet p T) ∧ EqAsJet δ p (mul p (invJet p T) T) (one I) ∧
      EqAsJet δ p (mul p T (invJet p T)) (one I) ∧
      jetNorm δ p (invJet p T) ≤
        jetNorm δ p (zeroPartInv T) *
          (1 + jetNorm δ p (zeroPartInv T) * jetNorm δ p T) ^ 2 ∧
      jetNorm δ p (zeroPartInv T) =
        ⨆ z ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (T.f00 z))
def TraceNumberCommTranspose (δ : ℝ) (p : Fin 4 → ℂ) : Prop :=
  ∀ I₁ I₂ : PeriodicData, IsPeriodic I₁ → IsPeriodic I₂ →
    (∀ (T : JetQuad I₁ I₂) (S : JetQuad I₂ I₁), IsJet δ p T → IsJet δ p S →
      traceNumber (mul p T S) = traceNumber (mul p S T)) ∧
    ∀ T : JetQuad I₁ I₁, IsJet δ p T → traceNumber (transposeAt p T) = traceNumber T
def LogNumberMulAdd (δ : ℝ) (p : Fin 4 → ℂ) : Prop :=
  ∀ I : PeriodicData, IsPeriodic I →
    (∀ T S : JetQuad I I, IsInvertibleJet δ p T → IsInvertibleJet δ p S →
      IsInvertibleJet δ p (mul p T S) ∧
        logNumber p (mul p T S) = logNumber p T + logNumber p S) ∧
    ∀ T : JetQuad I I, IsInvertibleJet δ p T →
      logNumber p T = torusAverage fun z => logDensity p T (toComplexVec z)
def BlockTriangularLogNumber (δ : ℝ) (p : Fin 4 → ℂ) : Prop :=
  ∀ J : Fin 2 → PeriodicData, (∀ b, IsPeriodic (J b)) →
    (∀ u : (PeriodicData.sigma J).UnitQuot,
      ∃! x : (Σ b, (J b).UnitQuot), sigmaQuotIn J x.1 x.2 = u) ∧
    ∀ T : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J), IsJet δ p T →
      IsBlockTriangular δ p J T →
      (∀ b, IsJet δ p (diagBlock J b T)) ∧
      ((∀ b, IsInvertibleJet δ p (diagBlock J b T)) →
        IsInvertibleJet δ p T ∧
          logNumber p T = logNumber p (diagBlock J 0 T) +
            logNumber p (diagBlock J 1 T))
def HasDerivLogNumber (δ : ℝ) (p : Fin 4 → ℂ) : Prop :=
  ∀ I : PeriodicData, IsPeriodic I → ∀ (A : Set ℝ), A.OrdConnected → A.Nontrivial →
    ∀ T T' : ℝ → JetQuad I I,
      (∀ t ∈ A, IsInvertibleJet δ p (T t)) → (∀ t ∈ A, IsJet δ p (T' t)) →
      HasC1FamilyDeriv δ p A T T' →
      (∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t ∈ A,
        (⨆ z ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse ((T t).f00 z))) ≤ C) →
      ∀ t ∈ A, HasDerivWithinAt (fun s => logNumber p (T s))
        (traceNumber (mul p (invJet p (T t)) (T' t))) A t
end JetCalculus
end YangMills.Construction.PeriodicOperators
end
