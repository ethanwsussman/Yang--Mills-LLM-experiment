import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.ClassesOfTheCopiesOfIndexSetsProof
import YangMills.Construction.PeriodicOperators.CopiesAndUnionsOfPeriodicIndexSets
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsCarriedOverToCopies
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHomProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CopyOpFuns
section Matrices
variable {J J' : Type}
theorem apply_eq_sum_linearMapEntry [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (φ : J → ℂ) (c' : J') :
    M φ c' = ∑ c, linearMapEntry M c' c * φ c := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.apply_eq_sum_linearMapEntry <;> assumption
theorem linearMapEntry_linearMapOfEntries [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
end Matrices
section Copies
variable {V V' : PeriodicData}
theorem intoCopy_snd (l : Fin 2) (x : (V.copy l).Carrier) : V.intoCopy l x.1.2 = x :=
  Subtype.ext (Prod.ext x.2.symm rfl)
def copyCarrierEquiv (V : PeriodicData) (l : Fin 2) : V.Carrier ≃ (V.copy l).Carrier where
  toFun := V.intoCopy l
  invFun := fun x => x.1.2
  left_inv := fun _ => rfl
  right_inv := intoCopy_snd l
theorem quotOfCopy_quotToCopy (l : Fin 2) (c : V.UnitQuot) :
    V.quotOfCopy l (V.quotToCopy l c) = c := by apply _root_.YangMills.Construction.PeriodicOperators.CopyQuotients.quotOfCopy_quotToCopy <;> assumption
theorem quotToCopy_quotOfCopy (l : Fin 2) (c : (V.copy l).UnitQuot) :
    V.quotToCopy l (V.quotOfCopy l c) = c := by apply _root_.YangMills.Construction.PeriodicOperators.CopyQuotients.quotToCopy_quotOfCopy <;> assumption
def copyQuotEquiv (V : PeriodicData) (l : Fin 2) : V.UnitQuot ≃ (V.copy l).UnitQuot where
  toFun := V.quotToCopy l
  invFun := V.quotOfCopy l
  left_inv := quotOfCopy_quotToCopy l
  right_inv := quotToCopy_quotOfCopy l
theorem quotToCopy_mkQuot_snd (l : Fin 2) (x : (V.copy l).Carrier) :
    V.quotToCopy l (V.mkQuot 1 x.1.2) = (V.copy l).mkQuot 1 x :=
  congrArg ((V.copy l).mkQuot 1) (intoCopy_snd l x)
theorem copyQuotHom_apply (l' l : Fin 2) [Finite V.UnitQuot] [Finite (V.copy l).UnitQuot]
    (M : QuotHom V V') (φ : (V.copy l).UnitQuot → ℂ) (c' : (V'.copy l').UnitQuot) :
    copyQuotHom l' l M φ c' = M (φ ∘ V.quotToCopy l) (V'.quotOfCopy l' c') := by
  cases nonempty_fintype V.UnitQuot
  cases nonempty_fintype (V.copy l).UnitQuot
  rw [apply_eq_sum_linearMapEntry, apply_eq_sum_linearMapEntry]
  simp only [copyQuotHom, linearMapEntry_linearMapOfEntries, copyQuotKernel]
  rw [← Equiv.sum_comp (copyQuotEquiv V l)]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [copyQuotEquiv, Equiv.coe_fn_mk, quotOfCopy_quotToCopy, Function.comp_apply]
theorem descendMatrix_copyKernel (l' l : Fin 2) (S : V'.Carrier → V.Carrier → ℂ)
    (c' : (V'.copy l').UnitQuot) (c : (V.copy l).UnitQuot) :
    descendMatrix (V.copy l) (V'.copy l') 1 (copyKernel l' l S) c' c =
      descendMatrix V V' 1 S (V'.quotOfCopy l' c') (V.quotOfCopy l c) := by
  unfold descendMatrix
  congr 1
  funext z
  apply propext
  constructor
  · intro h ι' ι h' hι
    refine h (V'.intoCopy l' ι') (V.intoCopy l ι) ?_ ?_
    · rw [← quotToCopy_quotOfCopy l' c', ← h']
      rfl
    · rw [← quotToCopy_quotOfCopy l c, ← hι]
      rfl
  · intro h x' x h' hx
    refine h x'.1.2 x.1.2 ?_ ?_
    · rw [← h']
      rfl
    · rw [← hx]
      rfl
theorem blochWave_copy (l : Fin 2) (κ : Fin 4 → ℂ) (φ : (V.copy l).UnitQuot → ℂ)
    (x : (V.copy l).Carrier) :
    blochWave (V.copy l) κ φ x = blochWave V κ (φ ∘ V.quotToCopy l) x.1.2 := by
  unfold blochWave
  rw [Function.comp_apply, quotToCopy_mkQuot_snd]
  rfl
theorem applyKernel_copyKernel_blochWave (l' l : Fin 2) (K : V'.Carrier → V.Carrier → ℂ)
    (κ : Fin 4 → ℂ) (φ : (V.copy l).UnitQuot → ℂ) (x' : (V'.copy l').Carrier) :
    applyKernel (copyKernel l' l K) (blochWave (V.copy l) κ φ) x' =
      applyKernel K (blochWave V κ (φ ∘ V.quotToCopy l)) x'.1.2 := by
  unfold applyKernel
  rw [← (copyCarrierEquiv V l).tsum_eq]
  refine tsum_congr fun ι => ?_
  rw [blochWave_copy]
  rfl
end Copies
section Functions
variable {F V V' : PeriodicData}
theorem isLocalWith_copyKernelFun_iff (l' l : Fin 2)
    (T : (F.Carrier → ℂ) → V'.Carrier → V.Carrier → ℂ) (ρ R : ℝ) :
    IsLocalWith F (V.copy l) (V'.copy l') (copyKernelFun l' l T) ρ R ↔
      IsLocalWith F V V' T ρ R := by
  constructor
  · intro h
    exact ⟨h.radius_pos,
      fun ζ hζ ι' ι hn => h.vanish_far ζ hζ (V'.intoCopy l' ι') (V.intoCopy l ι) hn,
      fun ι' ι => h.holo_entry (V'.intoCopy l' ι') (V.intoCopy l ι),
      fun ζ hζ n ι' ι => h.shift_covariant ζ hζ n (V'.intoCopy l' ι') (V.intoCopy l ι)⟩
  · intro h
    exact ⟨h.radius_pos,
      fun ζ hζ x' x hn => h.vanish_far ζ hζ x'.1.2 x.1.2 hn,
      fun x' x => h.holo_entry x'.1.2 x.1.2,
      fun ζ hζ n x' x => h.shift_covariant ζ hζ n x'.1.2 x.1.2⟩
theorem coeffOne_copyKernelFun (l' l : Fin 2) (T : (F.Carrier → ℂ) → V'.Carrier → V.Carrier → ℂ)
    (ζ : F.Carrier → ℂ) :
    coeffOne F (V.copy l) (V'.copy l') (copyKernelFun l' l T) ζ =
      copyKernel l' l (coeffOne F V V' T ζ) := by
  funext x' x
  unfold coeffOne copyKernel
  congr 1
  funext t
  apply propext
  constructor
  · intro h ρ R hm n e φ β hx
    exact h ρ R ((isLocalWith_copyKernelFun_iff l' l T ρ R).2 hm) n e φ β hx
  · intro h ρ R hm n e φ β hx
    exact h ρ R ((isLocalWith_copyKernelFun_iff l' l T ρ R).1 hm) n e φ β hx
theorem coeffTwo_copyKernelFun (l' l : Fin 2) (T : (F.Carrier → ℂ) → V'.Carrier → V.Carrier → ℂ)
    (ζ ζ' : F.Carrier → ℂ) :
    coeffTwo F (V.copy l) (V'.copy l') (copyKernelFun l' l T) ζ ζ' =
      copyKernel l' l (coeffTwo F V V' T ζ ζ') := by
  funext x' x
  unfold coeffTwo copyKernel
  congr 1
  funext t
  apply propext
  constructor
  · intro h ρ R hm n e φ β hx
    exact h ρ R ((isLocalWith_copyKernelFun_iff l' l T ρ R).2 hm) n e φ β hx
  · intro h ρ R hm n e φ β hx
    exact h ρ R ((isLocalWith_copyKernelFun_iff l' l T ρ R).1 hm) n e φ β hx
theorem blochWave_copyQuotHom (l' l : Fin 2) [Finite V.UnitQuot] [Finite (V.copy l).UnitQuot]
    (M : QuotHom V V') (κ : Fin 4 → ℂ) (φ : (V.copy l).UnitQuot → ℂ)
    (x' : (V'.copy l').Carrier) :
    blochWave (V'.copy l') κ (copyQuotHom l' l M φ) x' =
      blochWave V' κ (M (φ ∘ V.quotToCopy l)) x'.1.2 := by
  unfold blochWave
  rw [copyQuotHom_apply]
  rfl
theorem isActionTriple_copyKernelFun (l' l : Fin 2) [Finite V.UnitQuot] [Finite (V.copy l).UnitQuot]
    (T : (F.Carrier → ℂ) → V'.Carrier → V.Carrier → ℂ) (p : Fin 4 → ℂ)
    (εPlus εMinus : F.UnitQuot → ℂ)
    (A : ((Fin 4 → ℂ) → QuotHom V V') × ((Fin 4 → ℂ) → QuotHom V V') ×
      ((Fin 4 → ℂ) → QuotHom V V'))
    (hA : IsActionTriple F V V' T p εPlus εMinus A) :
    IsActionTriple F (V.copy l) (V'.copy l') (copyKernelFun l' l T) p εPlus εMinus
      (fun κ => copyQuotHom l' l (A.1 κ), fun κ => copyQuotHom l' l (A.2.1 κ),
        fun κ => copyQuotHom l' l (A.2.2 κ)) := by
  intro κ φ x'
  obtain ⟨h1, h2, h3⟩ := hA κ (φ ∘ V.quotToCopy l) x'.1.2
  refine ⟨?_, ?_, ?_⟩
  · rw [coeffOne_copyKernelFun, applyKernel_copyKernel_blochWave, h1, blochWave_copyQuotHom]
  · rw [coeffOne_copyKernelFun, applyKernel_copyKernel_blochWave, h2, blochWave_copyQuotHom]
  · rw [coeffTwo_copyKernelFun, applyKernel_copyKernel_blochWave, h3, blochWave_copyQuotHom]
theorem jetAlong_copyKernelFun (hjets : JetDomains.OpFunJetTheory) (l' l : Fin 2)
    (hF : IsPeriodic F) (hV : IsPeriodic V) (hV' : IsPeriodic V')
    (hc : IsPeriodic (V.copy l)) (hc' : IsPeriodic (V'.copy l'))
    (T : (F.Carrier → ℂ) → V'.Carrier → V.Carrier → ℂ)
    (hT : IsLocalOpFun F V V' T) (p : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ) :
    jetAlong F (V.copy l) (V'.copy l') (copyKernelFun l' l T) p εPlus εMinus =
      JetQuad.toCopies l' l (jetAlong F V V' T p εPlus εMinus) := by
  have : Finite V.UnitQuot := hV.finite_quot
  have : Finite (V.copy l).UnitQuot := hc.finite_quot
  have hlocal : IsLocalOpFun F (V.copy l) (V'.copy l') (copyKernelFun l' l T) := by
    obtain ⟨ρ, R, h⟩ := hT
    exact ⟨ρ, R, (isLocalWith_copyKernelFun_iff l' l T ρ R).2 h⟩
  have hset := (hjets.2.1 F V V' hF hV hV' T hT).triple_unique p εPlus εMinus
  have hset' := (hjets.2.1 F (V.copy l) (V'.copy l') hF hc hc' _ hlocal).triple_unique
    p εPlus εMinus
  have hspec := Classical.epsilon_spec hset.exists
  have hspec' := Classical.epsilon_spec hset'.exists
  have heq := hset'.unique hspec' (isActionTriple_copyKernelFun l' l T p εPlus εMinus _ hspec)
  refine JetQuad.ext ?_ ?_ ?_ ?_
  · funext κ
    show linearMapOfEntries _ = linearMapOfEntries _
    congr 1
    funext c' c
    have hentry : linearMapEntry ((jetAlong F V V' T p εPlus εMinus).f00 κ) =
        descendMatrix V V' 1 (fourierSymbol V V' (coeffZero F V V' T) κ) :=
      linearMapEntry_linearMapOfEntries _
    rw [copyQuotKernel, hentry]
    exact descendMatrix_copyKernel l' l (fourierSymbol V V' (coeffZero F V V' T) κ) c' c
  · exact congrArg Prod.fst heq
  · exact congrArg (fun A => A.2.1) heq
  · exact congrArg (fun A => A.2.2) heq
end Functions
theorem claim_holds (hcopies : CopiesUnions.Claim)
    (hjets : JetDomains.OpFunJetTheory) : Claim := by
  intro F hF δ p _ _ εPlus εMinus V hV
  refine ⟨fun i j T hT => ⟨?_, ?_⟩⟩
  · obtain ⟨ρ, R, h⟩ := hT
    exact ⟨ρ, R, (isLocalWith_copyKernelFun_iff i j T ρ R).2 h⟩
  · have hc : ∀ (W : PeriodicData) (l : Fin 2), IsPeriodic W →
        IsPeriodic (W.copy l) := fun W l hW => hcopies.1 W l hW
    rw [jetAlong_copyKernelFun hjets i j hF (hV j) (hV i) (hc _ j (hV j)) (hc _ i (hV i)) T hT]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
end YangMills.Construction.PeriodicOperators.CopyOpFuns
end
