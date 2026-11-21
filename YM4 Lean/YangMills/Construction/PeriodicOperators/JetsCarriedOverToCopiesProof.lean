import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.ClassesOfTheCopiesOfIndexSetsProof
import YangMills.Construction.PeriodicOperators.JetsCarriedOverToCopies
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CopyJets
open JetQuad (IsJet EqAsJet)
section Entries
variable {J J' : Type}
private theorem linearMapEntry_injective [Finite J] {M N : (J → ℂ) →ₗ[ℂ] (J' → ℂ)}
    (hMN : linearMapEntry M = linearMapEntry N) : M = N := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMap_ext_of_entry <;> assumption
private theorem linearMapEntry_ofEntries [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
private theorem wNorm_comp_equiv {L : Type} (e : J ≃ L) (w : L → ℝ) (f : L → ℂ) :
    wNorm (w ∘ e) (f ∘ e) = wNorm w f := by
  unfold wNorm
  congr 1
  exact e.tsum_eq fun i => w i * ‖f i‖ ^ 2
private theorem normSummable_comp_equiv {L : Type} (e : J ≃ L) (w : L → ℝ) (f : L → ℂ) :
    NormSummable (w ∘ e) (f ∘ e) ↔ NormSummable w f :=
  e.summable_iff (f := fun i => |w i * ‖f i‖ ^ 2|)
end Entries
section Quotients
variable (P : PeriodicData) (a : Fin 2)
private theorem quotOfCopy_quotToCopy (q : P.UnitQuot) :
    P.quotOfCopy a (P.quotToCopy a q) = q := by apply _root_.YangMills.Construction.PeriodicOperators.CopyQuotients.quotOfCopy_quotToCopy <;> assumption
private theorem quotToCopy_quotOfCopy (q : (P.copy a).UnitQuot) :
    P.quotToCopy a (P.quotOfCopy a q) = q := by apply _root_.YangMills.Construction.PeriodicOperators.CopyQuotients.quotToCopy_quotOfCopy <;> assumption
private def quotCopyEquiv : P.UnitQuot ≃ (P.copy a).UnitQuot where
  toFun := P.quotToCopy a
  invFun := P.quotOfCopy a
  left_inv := quotOfCopy_quotToCopy P a
  right_inv := quotToCopy_quotOfCopy P a
private theorem finite_copyQuot [Finite P.UnitQuot] : Finite (P.copy a).UnitQuot :=
  Finite.of_equiv _ (quotCopyEquiv P a)
private theorem mkQuot_copy_eq_iff (q : P.UnitQuot) (x : (P.copy a).Carrier) :
    (P.copy a).mkQuot 1 x = P.quotToCopy a q ↔ P.mkQuot 1 x.1.2 = q := by apply _root_.YangMills.Construction.PeriodicOperators.CopyQuotients.mkQuot_copy_eq_iff <;> assumption
private theorem quotWeight_quotToCopy (q : P.UnitQuot) :
    (P.copy a).quotWeight 1 (P.quotToCopy a q) = P.quotWeight 1 q := by apply _root_.YangMills.Construction.PeriodicOperators.CopyQuotients.quotWeight_quotToCopy_eq <;> assumption
private theorem quotWeight_copy (q : (P.copy a).UnitQuot) :
    (P.copy a).quotWeight 1 q = P.quotWeight 1 (P.quotOfCopy a q) := by
  conv_lhs => rw [← quotToCopy_quotOfCopy P a q]
  exact quotWeight_quotToCopy P a _
private theorem quotWeight_comp_equiv :
    (P.copy a).quotWeight 1 ∘ (quotCopyEquiv P a) = P.quotWeight 1 :=
  funext (quotWeight_quotToCopy P a)
private theorem phaseOn_quotToCopy (e : Fin 4 → ℤ) (q : P.UnitQuot) :
    phaseOn (P.copy a) e (P.quotToCopy a q) = phaseOn P e q := by
  unfold phaseOn
  congr 1
  funext z
  refine propext ⟨fun hz ι hι => ?_, fun hz x hx => ?_⟩
  · exact hz (P.intoCopy a ι) ((mkQuot_copy_eq_iff P a q _).2 hι)
  · exact hz x.1.2 ((mkQuot_copy_eq_iff P a q x).1 hx)
end Quotients
section Conjugation
variable {P Q R : PeriodicData} {a b c : Fin 2}
private def conjHom (b a : Fin 2) (M : QuotHom P Q) : QuotHom (P.copy a) (Q.copy b) :=
  (LinearMap.funLeft ℂ ℂ (Q.quotOfCopy b)).comp
    (M.comp (LinearMap.funLeft ℂ ℂ (P.quotToCopy a)))
private theorem conjHom_apply (M : QuotHom P Q) (f : (P.copy a).UnitQuot → ℂ)
    (q' : (Q.copy b).UnitQuot) :
    conjHom b a M f q' = M (f ∘ P.quotToCopy a) (Q.quotOfCopy b q') := rfl
private theorem entry_conjHom (M : QuotHom P Q) (q' : (Q.copy b).UnitQuot)
    (d : (P.copy a).UnitQuot) :
    linearMapEntry (conjHom b a M) q' d =
      linearMapEntry M (Q.quotOfCopy b q') (P.quotOfCopy a d) := by
  classical
  have hs : (Pi.single d 1 : (P.copy a).UnitQuot → ℂ) ∘ P.quotToCopy a =
      Pi.single (P.quotOfCopy a d) 1 := by
    funext x
    by_cases hx : x = P.quotOfCopy a d
    · subst hx
      simp [quotToCopy_quotOfCopy]
    · have hx' : P.quotToCopy a x ≠ d := fun e => hx (by rw [← e, quotOfCopy_quotToCopy])
      simp [hx, hx']
  simp only [linearMapEntry, conjHom_apply, hs]
private theorem copyQuotHom_eq [Finite P.UnitQuot] (M : QuotHom P Q) :
    copyQuotHom b a M = conjHom b a M := by
  have := finite_copyQuot P a
  have hK : linearMapEntry (conjHom b a M) = copyQuotKernel b a (linearMapEntry M) := by
    funext q' d
    exact entry_conjHom M q' d
  have hs := Classical.epsilon_spec
    (p := fun N => linearMapEntry N = copyQuotKernel b a (linearMapEntry M)) ⟨_, hK⟩
  exact linearMapEntry_injective (hs.trans hK.symm)
private theorem conjHom_add (M N : QuotHom P Q) :
    conjHom b a (M + N) = conjHom b a M + conjHom b a N := rfl
private theorem conjHom_smul (z : ℂ) (M : QuotHom P Q) :
    conjHom b a (z • M) = z • conjHom b a M := rfl
private theorem conjHom_zero : conjHom b a (0 : QuotHom P Q) = 0 := by
  ext f q'
  simp [conjHom]
private theorem conjHom_comp (M : QuotHom P Q) (N : QuotHom R P) :
    (conjHom b a M).comp (conjHom a c N) = conjHom b c (M.comp N) := by
  refine LinearMap.ext fun f => ?_
  funext q'
  have hf : (conjHom a c N f) ∘ P.quotToCopy a = N (f ∘ R.quotToCopy c) := by
    funext x
    simp only [Function.comp_apply, conjHom_apply, quotOfCopy_quotToCopy]
  simp only [LinearMap.comp_apply, conjHom_apply, hf]
private theorem conjHom_id : conjHom a a (LinearMap.id : QuotHom P P) = LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  funext q'
  simp [conjHom_apply, quotToCopy_quotOfCopy]
private def conjEquiv (P : PeriodicData) (a : Fin 2) :
    ((P.UnitQuot → ℂ) ≃ₗ[ℂ] ((P.copy a).UnitQuot → ℂ)) :=
  LinearEquiv.funCongrLeft ℂ ℂ (quotCopyEquiv P a).symm
private theorem conjHom_eq_conj (M : QuotHom P P) : conjHom a a M = (conjEquiv P a).conj M := by
  refine LinearMap.ext fun f => ?_
  funext q'
  rfl
private theorem trace_conjHom [Finite P.UnitQuot] (M : QuotHom P P) :
    LinearMap.trace ℂ ((P.copy a).UnitQuot → ℂ) (conjHom a a M) =
      LinearMap.trace ℂ (P.UnitQuot → ℂ) M := by
  have := finite_copyQuot P a
  rw [conjHom_eq_conj]
  exact LinearMap.trace_conj' M (conjEquiv P a)
private def unconjHom (a : Fin 2) (N : QuotHom (P.copy a) (P.copy a)) : QuotHom P P :=
  (LinearMap.funLeft ℂ ℂ (P.quotToCopy a)).comp
    (N.comp (LinearMap.funLeft ℂ ℂ (P.quotOfCopy a)))
private theorem unconj_conj (M : QuotHom P P) : unconjHom a (conjHom a a M) = M := by
  refine LinearMap.ext fun f => ?_
  funext x
  have hf : (LinearMap.funLeft ℂ ℂ (P.quotOfCopy a) f) ∘ P.quotToCopy a = f := by
    funext y
    simp [LinearMap.funLeft_apply, quotOfCopy_quotToCopy]
  simp [unconjHom, LinearMap.funLeft_apply, conjHom_apply, quotOfCopy_quotToCopy, hf]
private theorem conj_unconj (N : QuotHom (P.copy a) (P.copy a)) :
    conjHom a a (unconjHom a N) = N := by
  refine LinearMap.ext fun f => ?_
  funext x
  have hf : LinearMap.funLeft ℂ ℂ (P.quotOfCopy a) (f ∘ P.quotToCopy a) = f := by
    funext y
    simp [LinearMap.funLeft_apply, quotToCopy_quotOfCopy]
  simp [unconjHom, LinearMap.funLeft_apply, conjHom_apply, quotToCopy_quotOfCopy, hf]
private def conjMulEquiv (P : PeriodicData) (a : Fin 2) :
    Module.End ℂ (P.UnitQuot → ℂ) ≃* Module.End ℂ ((P.copy a).UnitQuot → ℂ) where
  toFun M := conjHom a a M
  invFun N := unconjHom a N
  left_inv := unconj_conj
  right_inv := conj_unconj
  map_mul' M N := (conjHom_comp M N).symm
private theorem isUnit_conjHom (M : QuotHom P P) :
    IsUnit (conjHom a a M : Module.End ℂ ((P.copy a).UnitQuot → ℂ)) ↔
      IsUnit (M : Module.End ℂ (P.UnitQuot → ℂ)) :=
  MulEquiv.isUnit_map (conjMulEquiv P a)
private theorem inverse_conjHom (M : QuotHom P P) :
    quotHomInverse (conjHom a a M) = conjHom a a (quotHomInverse M) := by
  unfold quotHomInverse
  by_cases hM : IsUnit (M : Module.End ℂ (P.UnitQuot → ℂ))
  · obtain ⟨u, hu⟩ := hM
    have hc : (conjHom a a M : Module.End ℂ ((P.copy a).UnitQuot → ℂ)) =
        ((Units.map (conjMulEquiv P a).toMonoidHom u : (Module.End ℂ ((P.copy a).UnitQuot → ℂ))ˣ) :
          Module.End ℂ ((P.copy a).UnitQuot → ℂ)) := by
      rw [← hu]
      rfl
    rw [hc, ← hu, Ring.inverse_unit, Ring.inverse_unit]
    rfl
  · rw [Ring.inverse_non_unit _ hM, Ring.inverse_non_unit _ (mt (isUnit_conjHom M).1 hM),
      conjHom_zero]
private theorem phaseMul_copy (e : Fin 4 → ℤ) :
    phaseMul (P.copy a) e = conjHom a a (phaseMul P e) := by
  refine LinearMap.ext fun f => ?_
  funext q'
  obtain ⟨d, rfl⟩ := (quotCopyEquiv P a).surjective q'
  show phaseOn (P.copy a) e (P.quotToCopy a d) * f (P.quotToCopy a d) =
    phaseOn P e (P.quotOfCopy a (P.quotToCopy a d)) *
      f (P.quotToCopy a (P.quotOfCopy a (P.quotToCopy a d)))
  rw [phaseOn_quotToCopy, quotOfCopy_quotToCopy]
private theorem normSummable_copy (g : (P.copy a).UnitQuot → ℂ) :
    NormSummable (P.quotWeight 1) (g ∘ P.quotToCopy a) ↔
      NormSummable ((P.copy a).quotWeight 1) g := by
  have hg := normSummable_comp_equiv (quotCopyEquiv P a) ((P.copy a).quotWeight 1) g
  rw [quotWeight_comp_equiv] at hg
  exact hg
private theorem wNorm_copy (g : (P.copy a).UnitQuot → ℂ) :
    wNorm (P.quotWeight 1) (g ∘ P.quotToCopy a) =
      wNorm ((P.copy a).quotWeight 1) g := by
  have hg := wNorm_comp_equiv (quotCopyEquiv P a) ((P.copy a).quotWeight 1) g
  rw [quotWeight_comp_equiv] at hg
  exact hg
private theorem wUnitBall_copy (g : (P.copy a).UnitQuot → ℂ) :
    g ∘ P.quotToCopy a ∈ wUnitBall (P.quotWeight 1) univ ↔
      g ∈ wUnitBall ((P.copy a).quotWeight 1) univ := by
  simp only [wUnitBall, mem_ofPred_eq, mem_univ, true_and, normSummable_copy, wNorm_copy]
private theorem quotHomNorm_conjHom (M : QuotHom P Q) :
    quotHomNorm (conjHom b a M) = quotHomNorm M := by
  unfold quotHomNorm wOpNorm
  have hval : ∀ g : (P.copy a).UnitQuot → ℂ,
      wNorm ((Q.copy b).quotWeight 1) (conjHom b a M g) =
        wNorm (Q.quotWeight 1) (M (g ∘ P.quotToCopy a)) := by
    intro g
    rw [← wNorm_copy (conjHom b a M g)]
    congr 1
    funext x
    simp only [Function.comp_apply, conjHom_apply, quotOfCopy_quotToCopy]
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rw [hval]
    exact le_iSup₂_of_le (g ∘ P.quotToCopy a) ((wUnitBall_copy g).2 hg) le_rfl
  · refine iSup₂_le fun f hf => ?_
    have hg : (f ∘ P.quotOfCopy a) ∘ P.quotToCopy a = f := by
      funext y
      simp [quotOfCopy_quotToCopy]
    refine le_iSup₂_of_le (f ∘ P.quotOfCopy a) ((wUnitBall_copy _).1 (by rwa [hg])) ?_
    rw [hval, hg]
private theorem transpose_conjHom [Finite P.UnitQuot] [Finite Q.UnitQuot] (M : QuotHom P Q) :
    quotHomTranspose (conjHom b a M) = conjHom a b (quotHomTranspose M) := by
  have := finite_copyQuot P a
  have := finite_copyQuot Q b
  apply linearMapEntry_injective
  funext d d'
  rw [entry_conjHom]
  simp only [quotHomTranspose, linearMapEntry_ofEntries, wTranspose, entry_conjHom,
    quotWeight_copy]
end Conjugation
section Quadruples
variable {P Q R : PeriodicData} [Finite P.UnitQuot] [Finite R.UnitQuot] {a b c : Fin 2}
private theorem isHolomorphicNbhd_toCopies {D : Set (Fin 4 → ℂ)}
    {F : (Fin 4 → ℂ) → QuotHom P Q}
    (hF : IsHolomorphicNbhd D F) : IsHolomorphicNbhd D fun κ => copyQuotHom b a (F κ) := by
  obtain ⟨O, hO, hD, hFO⟩ := hF
  refine ⟨O, hO, hD, fun q' d => ?_⟩
  simp only [copyQuotHom_eq, entry_conjHom]
  exact hFO _ _
private theorem isQuasiPeriodic_toCopies {D : Set (Fin 4 → ℂ)} {F : (Fin 4 → ℂ) → QuotHom P Q}
    (hF : IsQuasiPeriodic D F) : IsQuasiPeriodic D fun κ => copyQuotHom b a (F κ) := by
  intro e κ hκ
  simp only [copyQuotHom_eq]
  rw [hF e κ hκ, phaseMul_copy, phaseMul_copy, inverse_conjHom, conjHom_comp, conjHom_comp]
private theorem isJet_toCopies {δ : ℝ} {p : Fin 4 → ℂ} {T : JetQuad P Q} (hT : IsJet δ p T) :
    IsJet δ p (JetQuad.toCopies b a T) where
  pos_width := hT.pos_width
  mem_imStrip := hT.mem_imStrip
  holo_f00 := isHolomorphicNbhd_toCopies hT.holo_f00
  holo_f10 := isHolomorphicNbhd_toCopies hT.holo_f10
  holo_f01 := isHolomorphicNbhd_toCopies hT.holo_f01
  holo_f11 := isHolomorphicNbhd_toCopies hT.holo_f11
  quasiPeriodic_f00 := isQuasiPeriodic_toCopies hT.quasiPeriodic_f00
  quasiPeriodic_f10 := isQuasiPeriodic_toCopies hT.quasiPeriodic_f10
  quasiPeriodic_f01 := isQuasiPeriodic_toCopies hT.quasiPeriodic_f01
  quasiPeriodic_f11 := isQuasiPeriodic_toCopies hT.quasiPeriodic_f11
private theorem jetNorm_toCopies (δ : ℝ) (p : Fin 4 → ℂ) (T : JetQuad P Q) :
    JetQuad.jetNorm δ p (JetQuad.toCopies b a T) = JetQuad.jetNorm δ p T := by
  simp only [JetQuad.jetNorm, JetQuad.toCopies, copyQuotHom_eq, quotHomNorm_conjHom]
private theorem add_toCopies (T S : JetQuad P Q) :
    JetQuad.toCopies b a (JetQuad.add T S) =
      JetQuad.add (JetQuad.toCopies b a T) (JetQuad.toCopies b a S) := by
  refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
    simp only [JetQuad.toCopies, JetQuad.add, Pi.add_apply, copyQuotHom_eq, conjHom_add]
private theorem smul_toCopies (z : ℂ) (T : JetQuad P Q) :
    JetQuad.toCopies b a (JetQuad.smul z T) = JetQuad.smul z (JetQuad.toCopies b a T) := by
  refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
    simp only [JetQuad.toCopies, JetQuad.smul, Pi.smul_apply, copyQuotHom_eq, conjHom_smul]
private theorem mul_toCopies (p : Fin 4 → ℂ) (T : JetQuad P Q) (S : JetQuad R P) :
    JetQuad.toCopies b c (JetQuad.mul p T S) =
      JetQuad.mul p (JetQuad.toCopies b a T) (JetQuad.toCopies a c S) := by
  refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
    simp only [JetQuad.toCopies, JetQuad.mul, copyQuotHom_eq, conjHom_add, conjHom_comp]
private theorem transposeAt_toCopies [Finite Q.UnitQuot] (p : Fin 4 → ℂ) (T : JetQuad P Q) :
    JetQuad.toCopies a b (JetQuad.transposeAt p T) =
      JetQuad.transposeAt p (JetQuad.toCopies b a T) := by
  refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
    simp only [JetQuad.toCopies, JetQuad.transposeAt, copyQuotHom_eq, transpose_conjHom]
private theorem one_toCopies :
    JetQuad.toCopies a a (JetQuad.one P) = JetQuad.one (P.copy a) := by
  refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
    simp only [JetQuad.toCopies, JetQuad.one, copyQuotHom_eq, conjHom_id, Pi.zero_apply,
      conjHom_zero]
private theorem zeroPartInv_toCopies (T : JetQuad P P) :
    JetQuad.zeroPartInv (JetQuad.toCopies a a T) =
      JetQuad.toCopies a a (JetQuad.zeroPartInv T) := by
  refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
    simp only [JetQuad.toCopies, JetQuad.zeroPartInv, copyQuotHom_eq, inverse_conjHom,
      Pi.zero_apply, conjHom_zero]
private theorem normalize_toCopies (p : Fin 4 → ℂ) (T : JetQuad P P) :
    JetQuad.normalize p (JetQuad.toCopies a a T) =
      JetQuad.toCopies a a (JetQuad.normalize p T) := by
  unfold JetQuad.normalize
  rw [zeroPartInv_toCopies, ← mul_toCopies, ← one_toCopies, ← smul_toCopies, ← add_toCopies]
private theorem logSeries_toCopies (p : Fin 4 → ℂ) (T : JetQuad P P) :
    JetQuad.logSeries p (JetQuad.toCopies a a T) =
      JetQuad.toCopies a a (JetQuad.logSeries p T) := by
  unfold JetQuad.logSeries
  rw [normalize_toCopies, ← mul_toCopies, ← smul_toCopies, ← add_toCopies]
private theorem invJet_toCopies (p : Fin 4 → ℂ) (T : JetQuad P P) :
    JetQuad.invJet p (JetQuad.toCopies a a T) =
      JetQuad.toCopies a a (JetQuad.invJet p T) := by
  unfold JetQuad.invJet
  rw [normalize_toCopies, zeroPartInv_toCopies, ← mul_toCopies, ← smul_toCopies, ← one_toCopies,
    ← add_toCopies, ← add_toCopies, ← mul_toCopies]
private theorem traceNumber_toCopies_eq (T : JetQuad P P) :
    JetQuad.traceNumber (JetQuad.toCopies a a T) = JetQuad.traceNumber T := by
  unfold JetQuad.traceNumber
  congr 1
  funext κ
  simp only [JetQuad.toCopies, copyQuotHom_eq, trace_conjHom]
private theorem logNumber_toCopies (p : Fin 4 → ℂ) (T : JetQuad P P) :
    JetQuad.logNumber p (JetQuad.toCopies a a T) = JetQuad.logNumber p T := by
  unfold JetQuad.logNumber
  rw [logSeries_toCopies, traceNumber_toCopies_eq]
private theorem isInvertibleJet_toCopies {δ : ℝ} {p : Fin 4 → ℂ} {T : JetQuad P P}
    (hT : IsJet δ p T) :
    JetQuad.IsInvertibleJet δ p (JetQuad.toCopies a a T) ↔ JetQuad.IsInvertibleJet δ p T := by
  have hb : ∀ κ, quotHomNorm (quotHomInverse ((JetQuad.toCopies a a T).f00 κ)) =
      quotHomNorm (quotHomInverse (T.f00 κ)) := by
    intro κ
    show quotHomNorm (quotHomInverse (copyQuotHom a a (T.f00 κ))) = _
    rw [copyQuotHom_eq, inverse_conjHom, quotHomNorm_conjHom]
  have hu : ∀ κ, IsUnit ((JetQuad.toCopies a a T).f00 κ :
      Module.End ℂ ((P.copy a).UnitQuot → ℂ)) ↔
        IsUnit (T.f00 κ : Module.End ℂ (P.UnitQuot → ℂ)) := by
    intro κ
    show IsUnit (copyQuotHom a a (T.f00 κ) : Module.End ℂ ((P.copy a).UnitQuot → ℂ)) ↔ _
    rw [copyQuotHom_eq]
    exact isUnit_conjHom _
  constructor
  · intro hi
    refine ⟨hT, fun κ hκ => (hu κ).1 (hi.isUnit_f00 κ hκ), ?_⟩
    have := hi.bdd_inverse
    simpa only [hb] using this
  · intro hi
    refine ⟨isJet_toCopies hT, fun κ hκ => (hu κ).2 (hi.isUnit_f00 κ hκ), ?_⟩
    simpa only [hb] using hi.bdd_inverse
end Quadruples
private theorem eqAsJet_of_eq {P P' : PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ} {T S : JetQuad P P'}
    (hTS : T = S) : EqAsJet δ p T S := by
  subst hTS
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
theorem claim_holds : Claim := by
  intro δ p _ _ V hV
  have : ∀ b, Finite (V b).UnitQuot := fun b => (hV b).finite_quot
  exact
    { isJet_jetNorm := fun i j T hT => ⟨isJet_toCopies hT, jetNorm_toCopies δ p T⟩
      toCopies_eq := fun i j T S _ _ hTS =>
        ⟨fun κ hκ => congrArg (copyQuotHom i j) (hTS.1 hκ),
          fun κ hκ => congrArg (copyQuotHom i j) (hTS.2.1 hκ),
          fun κ hκ => congrArg (copyQuotHom i j) (hTS.2.2.1 hκ),
          fun κ hκ => congrArg (copyQuotHom i j) (hTS.2.2.2 hκ)⟩
      toCopies_add := fun i j T S _ _ => eqAsJet_of_eq (add_toCopies T S)
      toCopies_smul := fun i j z T _ => eqAsJet_of_eq (smul_toCopies z T)
      toCopies_mul := fun i j l T S _ _ => eqAsJet_of_eq (mul_toCopies p T S)
      toCopies_transposeAt := fun i j T _ => eqAsJet_of_eq (transposeAt_toCopies p T)
      toCopies_one := fun i => eqAsJet_of_eq one_toCopies
      traceNumber_toCopies := fun i C _ => traceNumber_toCopies_eq C
      isInvertibleJet_toCopies_iff := fun i C hC => isInvertibleJet_toCopies hC
      logNumber_invJet_toCopies := fun i C hC =>
        ⟨logNumber_toCopies p C, eqAsJet_of_eq (invJet_toCopies p C)⟩ }
end YangMills.Construction.PeriodicOperators.CopyJets
end
