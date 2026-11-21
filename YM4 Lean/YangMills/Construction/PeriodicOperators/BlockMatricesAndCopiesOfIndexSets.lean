import YangMills.Construction.PeriodicOperators.RulesOfTheCalculusOfJets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace PeriodicData
def copy (V : PeriodicData) (l : Fin 2) : PeriodicData where
  Carrier := {x : Fin 2 × V.Carrier // x.1 = l}
  translate := fun n x => ⟨(l, V.translate n x.1.2), rfl⟩
  pos := fun x => V.pos x.1.2
  Component := V.Component
  componentOf := fun x => V.componentOf x.1.2
  weight := V.weight
def intoCopy (V : PeriodicData) (l : Fin 2) (a : V.Carrier) : (V.copy l).Carrier := ⟨(l, a), rfl⟩
def quotToCopy (V : PeriodicData) (l : Fin 2) : V.UnitQuot → (V.copy l).UnitQuot :=
  Quot.lift (fun a => (V.copy l).mkQuot 1 (V.intoCopy l a))
    (by
      rintro a _ ⟨n, rfl⟩
      exact Quot.sound ⟨n, rfl⟩)
def quotOfCopy (V : PeriodicData) (l : Fin 2) : (V.copy l).UnitQuot → V.UnitQuot :=
  Quot.lift (fun x => V.mkQuot 1 x.1.2)
    (by
      rintro x _ ⟨n, rfl⟩
      exact Quot.sound ⟨n, rfl⟩)
end PeriodicData
section Copies
variable {V W : PeriodicData}
def copyKernel (k l : Fin 2) (X : W.Carrier → V.Carrier → ℂ) :
    (W.copy k).Carrier → (V.copy l).Carrier → ℂ :=
  fun y x => X y.1.2 x.1.2
def copyQuotKernel (k l : Fin 2) (X : W.UnitQuot → V.UnitQuot → ℂ) :
    (W.copy k).UnitQuot → (V.copy l).UnitQuot → ℂ :=
  fun d c => X (W.quotOfCopy k d) (V.quotOfCopy l c)
def copyQuotHom (k l : Fin 2) (M : QuotHom V W) : QuotHom (V.copy l) (W.copy k) :=
  linearMapOfEntries (copyQuotKernel k l (linearMapEntry M))
def copyKernelFun {F : PeriodicData} (k l : Fin 2) (T : (F.Carrier → ℂ) → W.Carrier → V.Carrier → ℂ) :
    (F.Carrier → ℂ) → (W.copy k).Carrier → (V.copy l).Carrier → ℂ :=
  fun ζ => copyKernel k l (T ζ)
def JetQuad.toCopies (k l : Fin 2) (T : JetQuad V W) :
    JetQuad (V.copy l) (W.copy k) :=
  ⟨fun κ => copyQuotHom k l (T.f00 κ), fun κ => copyQuotHom k l (T.f10 κ),
    fun κ => copyQuotHom k l (T.f01 κ), fun κ => copyQuotHom k l (T.f11 κ)⟩
end Copies
section Blocks
variable (J : Fin 2 → PeriodicData)
def sigmaQuotPlace {P : Type} (J : P → PeriodicData) :
    (PeriodicData.sigma J).UnitQuot → Σ b, (J b).UnitQuot :=
  Quot.lift (fun a => ⟨a.1, (J a.1).mkQuot 1 a.2⟩)
    (by
      rintro ⟨b, a⟩ _ ⟨n, rfl⟩
      exact congrArg (Sigma.mk b) (Quot.sound ⟨n, rfl⟩))
def blockKernel (X : ∀ i j, (J i).Carrier → (J j).Carrier → ℂ) :
    (PeriodicData.sigma J).Carrier → (PeriodicData.sigma J).Carrier → ℂ :=
  fun y x => X y.1 x.1 y.2 x.2
def blockQuotKernel (X : ∀ i j, (J i).UnitQuot → (J j).UnitQuot → ℂ) :
    (Σ b, (J b).UnitQuot) → (Σ b, (J b).UnitQuot) → ℂ :=
  fun d c => X d.1 c.1 d.2 c.2
def blockQuotHom (M : ∀ i j, QuotHom (J j) (J i)) :
    QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J) :=
  linearMapOfEntries fun d c =>
    blockQuotKernel J (fun i j => linearMapEntry (M i j)) (sigmaQuotPlace J d) (sigmaQuotPlace J c)
def blockKernelFun {F : PeriodicData}
    (T : ∀ i j, (F.Carrier → ℂ) → (J i).Carrier → (J j).Carrier → ℂ) :
    (F.Carrier → ℂ) → (PeriodicData.sigma J).Carrier → (PeriodicData.sigma J).Carrier → ℂ :=
  fun ζ => blockKernel J fun i j => T i j ζ
def blockJet (T : ∀ i j, JetQuad (J j) (J i)) :
    JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J) :=
  ⟨fun κ => blockQuotHom J fun i j => (T i j).f00 κ, fun κ => blockQuotHom J fun i j => (T i j).f10 κ,
    fun κ => blockQuotHom J fun i j => (T i j).f01 κ, fun κ => blockQuotHom J fun i j => (T i j).f11 κ⟩
end Blocks
def JetQuad.IsBlockTriangularRev (δ : ℝ) (p : Fin 4 → ℂ) (J : Fin 2 → PeriodicData)
    (T : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J)) : Prop :=
  ∀ (d : (J 0).UnitQuot) (c : (J 1).UnitQuot),
    (∀ κ ∈ imStrip (2 * δ), linearMapEntry (T.f00 κ) (sigmaQuotIn J 0 d) (sigmaQuotIn J 1 c) = 0) ∧
    (∀ κ ∈ stripAddShift δ p, linearMapEntry (T.f10 κ) (sigmaQuotIn J 0 d) (sigmaQuotIn J 1 c) = 0) ∧
    (∀ κ ∈ stripSubShift δ p, linearMapEntry (T.f01 κ) (sigmaQuotIn J 0 d) (sigmaQuotIn J 1 c) = 0) ∧
    ∀ κ ∈ realDualPoints, linearMapEntry (T.f11 κ) (sigmaQuotIn J 0 d) (sigmaQuotIn J 1 c) = 0
namespace BlockJets
open JetQuad (IsJet EqAsJet)
def CopiesAndSigmaPeriodic : Prop :=
  (∀ (V : PeriodicData) (l : Fin 2), IsPeriodic V → IsPeriodic (V.copy l)) ∧
    (∀ (V W : PeriodicData) (x : (V.copy 0).Carrier) (y : (W.copy 1).Carrier), x.1.1 ≠ y.1.1) ∧
    ∀ J : Fin 2 → PeriodicData, (∀ b, IsPeriodic (J b)) →
      IsPeriodic (PeriodicData.sigma J)
def SmulLocalOpFun (F : PeriodicData) (δ : ℝ) (p : Fin 4 → ℂ)
    (εp εm : F.UnitQuot → ℂ) : Prop :=
  ∀ A B : PeriodicData, IsPeriodic A → IsPeriodic B →
    ∀ S : (F.Carrier → ℂ) → B.Carrier → A.Carrier → ℂ, IsLocalOpFun F A B S →
      ∀ c : ℂ, IsLocalOpFun F A B (fun ζ => c • S ζ) ∧
        EqAsJet δ p (jetAlong F A B (fun ζ => c • S ζ) p εp εm)
          (JetQuad.smul c (jetAlong F A B S p εp εm))
structure BlockJetFacts (δ : ℝ) (p : Fin 4 → ℂ) (J : Fin 2 → PeriodicData) : Prop where
  quot_sigma : (∀ c : (PeriodicData.sigma J).UnitQuot,
      ∃! x : (Σ b, (J b).UnitQuot), sigmaQuotIn J x.1 x.2 = c) ∧
    ∀ x : (Σ b, (J b).UnitQuot), sigmaQuotPlace J (sigmaQuotIn J x.1 x.2) = x
  zero_isJet : ∀ i j, IsJet δ p (JetQuad.zeroJet (J j) (J i))
  block_isJet : ∀ T : ∀ i j, JetQuad (J j) (J i), (∀ i j, IsJet δ p (T i j)) →
    IsJet δ p (blockJet J T)
  diagBlock_blockJet : ∀ T : ∀ i j, JetQuad (J j) (J i), (∀ i j, IsJet δ p (T i j)) → ∀ b,
    IsJet δ p (JetQuad.diagBlock J b (blockJet J T)) ∧
      EqAsJet δ p (JetQuad.diagBlock J b (blockJet J T)) (T b b)
  blockTriangular : ∀ T : ∀ i j, JetQuad (J j) (J i), (∀ i j, IsJet δ p (T i j)) →
    T 1 0 = JetQuad.zeroJet (J 0) (J 1) → JetQuad.IsBlockTriangular δ p J (blockJet J T)
  blockTriangularRev : ∀ T : ∀ i j, JetQuad (J j) (J i), (∀ i j, IsJet δ p (T i j)) →
    T 0 1 = JetQuad.zeroJet (J 1) (J 0) →
      JetQuad.IsBlockTriangularRev δ p J (blockJet J T)
  one_eq_blockJet : ∀ T : ∀ i j, JetQuad (J j) (J i), T 0 0 = JetQuad.one (J 0) →
    T 1 1 = JetQuad.one (J 1) → T 0 1 = JetQuad.zeroJet (J 1) (J 0) →
      T 1 0 = JetQuad.zeroJet (J 0) (J 1) →
        EqAsJet δ p (JetQuad.one (PeriodicData.sigma J)) (blockJet J T)
def MulBlockJet (δ : ℝ) (p : Fin 4 → ℂ) (J : Fin 2 → PeriodicData) : Prop :=
  ∀ T S : ∀ i j, JetQuad (J j) (J i), (∀ i j, IsJet δ p (T i j)) → (∀ i j, IsJet δ p (S i j)) →
    EqAsJet δ p (JetQuad.mul p (blockJet J T) (blockJet J S))
      (blockJet J fun i j =>
        JetQuad.add (JetQuad.mul p (T i 0) (S 0 j)) (JetQuad.mul p (T i 1) (S 1 j)))
def BlockLocalOpFun (F : PeriodicData) (δ : ℝ) (p : Fin 4 → ℂ)
    (εp εm : F.UnitQuot → ℂ) (J : Fin 2 → PeriodicData) : Prop :=
  ∀ T : ∀ i j, (F.Carrier → ℂ) → (J i).Carrier → (J j).Carrier → ℂ,
    (∀ i j, IsLocalOpFun F (J j) (J i) (T i j)) →
      IsLocalOpFun F (PeriodicData.sigma J) (PeriodicData.sigma J) (blockKernelFun J T) ∧
        EqAsJet δ p (jetAlong F (PeriodicData.sigma J) (PeriodicData.sigma J) (blockKernelFun J T) p εp εm)
          (blockJet J fun i j => jetAlong F (J j) (J i) (T i j) p εp εm)
structure QuotOfCopies (V : Fin 2 → PeriodicData) : Prop where
  mkQuot_copy_iff : ∀ (l : Fin 2) (c : (V l).UnitQuot) (x : ((V l).copy l).Carrier),
    ((V l).copy l).mkQuot 1 x = (V l).quotToCopy l c ↔ (V l).mkQuot 1 x.1.2 = c
  existsUnique_quotToCopy : ∀ (l : Fin 2) (d : ((V l).copy l).UnitQuot),
    ∃! c : (V l).UnitQuot, (V l).quotToCopy l c = d
  quotWeight_quotToCopy : ∀ (l : Fin 2) (c : (V l).UnitQuot),
    ((V l).copy l).quotWeight 1 ((V l).quotToCopy l c) = (V l).quotWeight 1 c
structure LocalOpFunToCopies (F : PeriodicData) (δ : ℝ) (p : Fin 4 → ℂ)
    (εp εm : F.UnitQuot → ℂ) (V : Fin 2 → PeriodicData) : Prop where
  copyKernelFun_jet : ∀ (i j : Fin 2) (T : (F.Carrier → ℂ) → (V i).Carrier → (V j).Carrier → ℂ),
    IsLocalOpFun F (V j) (V i) T →
      IsLocalOpFun F ((V j).copy j) ((V i).copy i) (copyKernelFun i j T) ∧
        EqAsJet δ p
          (jetAlong F ((V j).copy j) ((V i).copy i) (copyKernelFun i j T) p εp εm)
          (JetQuad.toCopies i j (jetAlong F (V j) (V i) T p εp εm))
structure JetsToCopies (δ : ℝ) (p : Fin 4 → ℂ) (V : Fin 2 → PeriodicData) : Prop where
  isJet_jetNorm : ∀ (i j : Fin 2) (T : JetQuad (V j) (V i)), IsJet δ p T →
    IsJet δ p (JetQuad.toCopies i j T) ∧
      JetQuad.jetNorm δ p (JetQuad.toCopies i j T) = JetQuad.jetNorm δ p T
  toCopies_eq : ∀ (i j : Fin 2) (T S : JetQuad (V j) (V i)), IsJet δ p T → IsJet δ p S →
    EqAsJet δ p T S → EqAsJet δ p (JetQuad.toCopies i j T) (JetQuad.toCopies i j S)
  toCopies_add : ∀ (i j : Fin 2) (T S : JetQuad (V j) (V i)), IsJet δ p T → IsJet δ p S →
    EqAsJet δ p (JetQuad.toCopies i j (JetQuad.add T S))
      (JetQuad.add (JetQuad.toCopies i j T) (JetQuad.toCopies i j S))
  toCopies_smul : ∀ (i j : Fin 2) (a : ℂ) (T : JetQuad (V j) (V i)), IsJet δ p T →
    EqAsJet δ p (JetQuad.toCopies i j (JetQuad.smul a T))
      (JetQuad.smul a (JetQuad.toCopies i j T))
  toCopies_mul : ∀ (i j l : Fin 2) (T : JetQuad (V j) (V i)) (S : JetQuad (V l) (V j)),
    IsJet δ p T → IsJet δ p S →
      EqAsJet δ p (JetQuad.toCopies i l (JetQuad.mul p T S))
        (JetQuad.mul p (JetQuad.toCopies i j T) (JetQuad.toCopies j l S))
  toCopies_transposeAt : ∀ (i j : Fin 2) (T : JetQuad (V j) (V i)), IsJet δ p T →
    EqAsJet δ p (JetQuad.toCopies j i (JetQuad.transposeAt p T))
      (JetQuad.transposeAt p (JetQuad.toCopies i j T))
  toCopies_one : ∀ i : Fin 2,
    EqAsJet δ p (JetQuad.toCopies i i (JetQuad.one (V i))) (JetQuad.one ((V i).copy i))
  traceNumber_toCopies : ∀ (i : Fin 2) (C : JetQuad (V i) (V i)), IsJet δ p C →
    JetQuad.traceNumber (JetQuad.toCopies i i C) = JetQuad.traceNumber C
  isInvertibleJet_toCopies_iff : ∀ (i : Fin 2) (C : JetQuad (V i) (V i)), IsJet δ p C →
    (JetQuad.IsInvertibleJet δ p (JetQuad.toCopies i i C) ↔ JetQuad.IsInvertibleJet δ p C)
  logNumber_invJet_toCopies : ∀ (i : Fin 2) (C : JetQuad (V i) (V i)), JetQuad.IsInvertibleJet δ p C →
    JetQuad.logNumber p (JetQuad.toCopies i i C) = JetQuad.logNumber p C ∧
      EqAsJet δ p (JetQuad.invJet p (JetQuad.toCopies i i C))
        (JetQuad.toCopies i i (JetQuad.invJet p C))
def ToCopies (F : PeriodicData) (δ : ℝ) (p : Fin 4 → ℂ)
    (εp εm : F.UnitQuot → ℂ) (V : Fin 2 → PeriodicData) : Prop :=
  QuotOfCopies V ∧ LocalOpFunToCopies F δ p εp εm V ∧
    JetsToCopies δ p V
end BlockJets
end YangMills.Construction.PeriodicOperators
end
