import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.PeriodicOperators.AdditivityAndIntegralOfTheLogarithmicNumber
import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.InverseOfAnInvertibleJetProof
import YangMills.Construction.PeriodicOperators.JetOfAProductOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.JetsOnADisjointSumAndOnTheUnionOfAPair
import YangMills.Construction.PeriodicOperators.PeriodicOperatorsOfFiniteRangeAsLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.ProductOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.SymbolsOfCombinationsAndProductsAtAPoint
import YangMills.Construction.Towers.OuterFactorsKeepTheNumberOfAJet
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.DiagonalScaling
open YangMills.Construction.Tower.RescaledConditions (sumDiagScale)
open YangMills.Construction.PeriodicOperators.ConstantOpFun (constAssign)
open YangMills.Construction.PeriodicOperators.JetQuad (IsInvertibleJet IsJet EqAsJet logNumber)
section Multiplication
variable {I : PeriodicData}
open Classical in
def mulKernel (d : I.Carrier → ℂ) : I.Carrier → I.Carrier → ℂ :=
  fun a' a => if a' = a then d a else 0
theorem translate_injective (hI : IsPeriodic I) (m : Fin 4 → ℤ) {a a' : I.Carrier}
    (h : I.translate m a = I.translate m a') : a = a' := by
  have e : ∀ b : I.Carrier, I.translate (-m) (I.translate m b) = b := fun b => by
    rw [← hI.translate_add, add_neg_cancel, hI.translate_zero]
  rw [← e a, h, e]
theorem euclidNormVec_zero : TorusMetric.euclidNormVec 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
theorem mulKernel_periodic_finiteRange (hI : IsPeriodic I) {d : I.Carrier → ℂ}
    (hd : ∀ m a, d (I.translate m a) = d a) {C : ℝ} (hC : 0 < C) (hb : ∀ a, ‖d a‖ ≤ C) :
    IsPeriodicKernel I I (mulKernel d) ∧ IsFiniteRange I I (mulKernel d) := by
  refine ⟨⟨fun m a' a => ?_, C, 1, hC, one_pos, fun a' a => ?_⟩, 0, fun a' a h => ?_⟩
  · by_cases e : a' = a
    · subst e
      simp [mulKernel, hd]
    · have e' : I.translate m a' ≠ I.translate m a := fun h => e (translate_injective hI m h)
      simp [mulKernel, e, e']
  · by_cases e : a' = a
    · subst e
      simpa [mulKernel, euclidNormVec_zero] using hb a'
    · simp only [mulKernel, e, if_false, norm_zero]
      positivity
  · have e : a' ≠ a := by
      rintro rfl
      exact h (by simp [euclidNormVec_zero])
    simp [mulKernel, e]
theorem compKernel_mulKernel_left (d : I.Carrier → ℂ) (K : I.Carrier → I.Carrier → ℂ)
    (a' a : I.Carrier) : compKernel (mulKernel d) K a' a = d a' * K a' a := by
  simp only [compKernel]
  rw [tsum_eq_single a' fun b hb => by simp [mulKernel, Ne.symm hb]]
  simp [mulKernel]
theorem compKernel_mulKernel_right (K : I.Carrier → I.Carrier → ℂ) (d : I.Carrier → ℂ)
    (a' a : I.Carrier) : compKernel K (mulKernel d) a' a = K a' a * d a := by
  simp only [compKernel]
  rw [tsum_eq_single a fun b hb => by simp [mulKernel, hb]]
  simp [mulKernel]
theorem compKernel_mulKernel_of_mul_eq_one {d e : I.Carrier → ℂ} (h : ∀ a, d a * e a = 1) :
    compKernel (mulKernel d) (mulKernel e) = idKernel I := by
  funext a' a
  rw [compKernel_mulKernel_left]
  by_cases c : a' = a
  · subst c
    simp [mulKernel, idKernel, h]
  · simp [mulKernel, idKernel, c]
theorem symbolHom_idKernel (hId : IdKernelFacts.Claim) (hI : IsPeriodic I) (k : Fin 4 → ℂ) :
    symbolHom I I (idKernel I) k = LinearMap.id := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.symbolHom_idKernel <;> assumption
theorem mulKernel_invertible_logNumber_zero (hId : IdKernelFacts.Claim)
    (hSym : SymbolAtPoint.Claim)
    (hFin : ConstantOpFun.Claim)
    (hLoc : JetDomains.OpFunJetTheory)
    (hAdd : JetLogNumber.Claim)
    (hI : IsPeriodic I) {d e : I.Carrier → ℂ}
    (hd : ∀ m a, d (I.translate m a) = d a) (he : ∀ m a, e (I.translate m a) = e a)
    (hde : ∀ a, d a * e a = 1) {C : ℝ} (hC : 0 < C) (hbd : ∀ a, ‖d a‖ ≤ C) (hbe : ∀ a, ‖e a‖ ≤ C)
    {δ : ℝ} {p : Fin 4 → ℂ} (hδ : 0 < δ) (hp : p ∈ imStrip δ) :
    IsInvertibleJet δ p (JetQuad.ofKernel I I (mulKernel d)) ∧
      logNumber p (JetQuad.ofKernel I I (mulKernel d)) = 0 := by
  have kd := mulKernel_periodic_finiteRange hI hd hC hbd
  have ke := mulKernel_periodic_finiteRange hI he hC hbe
  have sd := (hFin I I I hI hI hI _ kd.1 kd.2 δ p hδ hp 0 0).1.2.2.2.2.1
  have se := (hFin I I I hI hI hI _ ke.1 ke.2 δ p hδ hp 0 0).1.2.2.2.2.1
  have alg := hLoc.2.2 I I I hI hI hI δ p hδ hp
  have jd := alg.ofKernel_isJet _ kd.1 sd
  have je := alg.ofKernel_isJet _ ke.1 se
  obtain ⟨Od, -, subd, formd, -⟩ := sd
  obtain ⟨Oe, -, sube, forme, -⟩ := se
  have hed : ∀ a, e a * d a = 1 := fun a => by rw [mul_comm, hde]
  have left : ∀ k ∈ imStrip (2 * δ), (symbolHom I I (mulKernel d) k).comp
      (symbolHom I I (mulKernel e) k) = LinearMap.id := fun k hk => by
    have h := (hSym.2 I I I hI hI hI _ _ k kd.1 (formd k (subd hk)) ke.1
      (forme k (sube hk))).2.2.2
    rw [← h, compKernel_mulKernel_of_mul_eq_one hde, symbolHom_idKernel hId hI]
  have right : ∀ k ∈ imStrip (2 * δ), (symbolHom I I (mulKernel e) k).comp
      (symbolHom I I (mulKernel d) k) = LinearMap.id := fun k hk => by
    have h := (hSym.2 I I I hI hI hI _ _ k ke.1 (forme k (sube hk)) kd.1
      (formd k (subd hk))).2.2.2
    rw [← h, compKernel_mulKernel_of_mul_eq_one hed, symbolHom_idKernel hId hI]
  let u : ∀ k ∈ imStrip (2 * δ), (Module.End ℂ (I.UnitQuot → ℂ))ˣ := fun k hk =>
    ⟨symbolHom I I (mulKernel d) k, symbolHom I I (mulKernel e) k, left k hk, right k hk⟩
  have inv : ∀ k ∈ imStrip (2 * δ), quotHomInverse (symbolHom I I (mulKernel d) k) =
      symbolHom I I (mulKernel e) k := fun k hk => by
    have h := Ring.inverse_unit (u k hk)
    exact h
  have hinv : IsInvertibleJet δ p (JetQuad.ofKernel I I (mulKernel d)) := by
    refine ⟨jd, fun k hk => (u k hk).isUnit, ?_⟩
    refine lt_of_le_of_lt (iSup₂_mono fun k hk => ?_) (alg.sups_finite _ je).1
    exact le_of_eq (congrArg quotHomNorm (inv k hk))
  refine ⟨hinv, ?_⟩
  rw [((hAdd δ p hδ hp) I hI).2 _ hinv]
  simp [JetQuad.logDensity, JetQuad.ofKernel, torusAverage]
end Multiplication
section Jets
variable {I I' : PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ}
theorem eqAsJet_refl (T : JetQuad I I') : EqAsJet δ p T T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
theorem eqAsJet_symm {T S : JetQuad I I'} (h : EqAsJet δ p T S) : EqAsJet δ p S T :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
theorem eqAsJet_trans {T S R : JetQuad I I'} (h : EqAsJet δ p T S) (g : EqAsJet δ p S R) :
    EqAsJet δ p T R := by apply _root_.YangMills.Construction.PeriodicOperators.JetInverse.trans_eqAsJet <;> assumption
theorem opFunComp_sandwich (hComp : OpFunComp.LocalClosed)
    (hJet : JetComp.Claim)
    (hFin : ConstantOpFun.Claim)
    (hAdd : JetLogNumber.Claim)
    (hArgs : JetArgumentsAndEqualJets)
    (hLoc : JetDomains.OpFunJetTheory)
    {F I : PeriodicData} (hF : IsPeriodic F) (hI : IsPeriodic I)
    {D E : I.Carrier → I.Carrier → ℂ}
    (kD : IsPeriodicKernel I I D ∧ IsFiniteRange I I D)
    (kE : IsPeriodicKernel I I E ∧ IsFiniteRange I I E)
    (iD : ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
      IsInvertibleJet δ p (JetQuad.ofKernel I I D) ∧
        logNumber p (JetQuad.ofKernel I I D) = 0)
    (iE : ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
      IsInvertibleJet δ p (JetQuad.ofKernel I I E) ∧
        logNumber p (JetQuad.ofKernel I I E) = 0)
    (M : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (hM : IsLocalOpFun F I I M) :
    IsLocalOpFun F I I (opFunComp (opFunComp (constAssign F D) M) (constAssign F E)) ∧
      ∀ (δ : ℝ) (p : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ), 0 < δ → p ∈ imStrip δ →
        IsInvertibleJet δ p (jetAlong F I I M p εp εm) →
          IsInvertibleJet δ p (jetAlong F I I
              (opFunComp (opFunComp (constAssign F D) M) (constAssign F E)) p εp εm) ∧
            logNumber p (jetAlong F I I
                (opFunComp (opFunComp (constAssign F D) M) (constAssign F E)) p εp εm) =
              logNumber p (jetAlong F I I M p εp εm) := by
  have zero_mem : (0 : Fin 4 → ℂ) ∈ imStrip 1 := fun μ => by simp
  have lD := (hFin F I I hF hI hI D kD.1 kD.2 1 0 one_pos zero_mem 0 0).1.1
  have lE := (hFin F I I hF hI hI E kE.1 kE.2 1 0 one_pos zero_mem 0 0).1.1
  have l1 := hComp F I I I hF hI hI hI _ M lD hM
  have l2 := hComp F I I I hF hI hI hI _ _ l1 lE
  refine ⟨l2, fun δ p εp εm hδ hp hinv => ?_⟩
  have jetsOf := fun {T} (h : IsLocalOpFun F I I T) =>
    (hLoc.2.1 F I I hF hI hI T h).isJet δ hδ p hp εp εm
  have alg := hLoc.2.2 I I I hI hI hI δ p hδ hp
  have hD := iD δ p hδ hp
  have hE := iE δ p hδ hp
  have eD := (hFin F I I hF hI hI D kD.1 kD.2 δ p hδ hp εp εm).1.2.2.2.2.2
  have eE := (hFin F I I hF hI hI E kE.1 kE.2 δ p hδ hp εp εm).1.2.2.2.2.2
  have j1 := hJet δ p hδ hp F I I I hF hI hI hI εp εm _ M lD hM
  have j2 := hJet δ p hδ hp F I I I hF hI hI hI εp εm _ _ l1 lE
  have e1 := (hArgs.2.1 δ p I I hI hI _ _ (jetsOf lD) hD.1.isJet eD).2.2.2.2 I hI _ _
    hinv.isJet hinv.isJet (eqAsJet_refl _)
  have k1 := eqAsJet_trans j1 e1
  have e2 := (hArgs.2.1 δ p I I hI hI _ _ (jetsOf l1)
    (alg.mul_isJet _ _ hD.1.isJet hinv.isJet) k1).2.2.2.2 I hI _ _ (jetsOf lE) hE.1.isJet eE
  have k2 := eqAsJet_trans j2 e2
  have hLog := (hAdd δ p hδ hp) I hI
  have w1 := hLog.1 _ _ hD.1 hinv
  have w2 := hLog.1 _ _ w1.1 hE.1
  have last := (hArgs.2.2 δ p I hI _ _ w2.1.isJet (jetsOf l2) (eqAsJet_symm k2)).2 w2.1
  refine ⟨last.1, ?_⟩
  rw [← last.2.2.2, w2.2, w1.2, hD.2, hE.2, zero_add, add_zero]
end Jets
section Summands
variable (I₁ I₂ : PeriodicData)
def summandConst (a b : ℂ) : (I₁.disjSum I₂).Carrier → ℂ :=
  Sum.elim (fun _ => a) (fun _ => b)
variable {I₁ I₂}
theorem summandConst_translate (a b : ℂ) (m : Fin 4 → ℤ) (t : (I₁.disjSum I₂).Carrier) :
    summandConst I₁ I₂ a b ((I₁.disjSum I₂).translate m t) = summandConst I₁ I₂ a b t := by
  change I₁.Carrier ⊕ I₂.Carrier at t
  cases t <;> rfl
theorem summandConst_mul_inv {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (t : (I₁.disjSum I₂).Carrier) :
    summandConst I₁ I₂ a b t * summandConst I₁ I₂ a⁻¹ b⁻¹ t = 1 := by
  change I₁.Carrier ⊕ I₂.Carrier at t
  cases t
  · exact mul_inv_cancel₀ ha
  · exact mul_inv_cancel₀ hb
theorem summandConst_norm_le (a b : ℂ) (t : (I₁.disjSum I₂).Carrier) :
    ‖summandConst I₁ I₂ a b t‖ ≤ ‖a‖ + ‖b‖ := by
  change I₁.Carrier ⊕ I₂.Carrier at t
  cases t
  · exact le_add_of_nonneg_right (norm_nonneg b)
  · exact le_add_of_nonneg_left (norm_nonneg a)
theorem sumDiagScale_eq_opFunComp {F : PeriodicData} (x y x' y' : ℂ)
    (M : (F.Carrier → ℂ) → (I₁.disjSum I₂).Carrier → (I₁.disjSum I₂).Carrier → ℂ) :
    (fun z => sumDiagScale (S := I₁.Carrier) (B := I₂.Carrier) x y x' y' (M z)) =
      opFunComp
        (opFunComp (constAssign F (mulKernel (summandConst I₁ I₂ x y))) M)
        (constAssign F (mulKernel (summandConst I₁ I₂ x' y'))) := by
  funext z t' t
  change _ = compKernel (compKernel (mulKernel (summandConst I₁ I₂ x y)) (M z))
    (mulKernel (summandConst I₁ I₂ x' y')) t' t
  have a := compKernel_mulKernel_right (I := I₁.disjSum I₂)
    (compKernel (mulKernel (summandConst I₁ I₂ x y)) (M z)) (summandConst I₁ I₂ x' y') t' t
  have b := compKernel_mulKernel_left (I := I₁.disjSum I₂) (summandConst I₁ I₂ x y) (M z) t' t
  refine Eq.trans ?_ a.symm
  refine Eq.trans ?_ (congrArg (· * summandConst I₁ I₂ x' y' t) b).symm
  rfl
end Summands
theorem preservesJetIndex_holds (hDisj : DisjSumJets.Claim)
    (hComp : OpFunComp.LocalClosed)
    (hJet : JetComp.Claim)
    (hFin : ConstantOpFun.Claim)
    (hAdd : JetLogNumber.Claim)
    (hArgs : JetArgumentsAndEqualJets)
    (hLoc : JetDomains.OpFunJetTheory)
    (hSym : SymbolAtPoint.Claim)
    (hId : IdKernelFacts.Claim) : PreservesJetIndex := by
  intro F I₁ I₂ hF h₁ h₂ x y x' y' hx hy hx' hy' M hM
  have hI := (hDisj F I₁ I₂ hF h₁ h₂).1
  rw [sumDiagScale_eq_opFunComp]
  have sides : ∀ {a b : ℂ}, a ≠ 0 → b ≠ 0 →
      (IsPeriodicKernel _ _ (mulKernel (summandConst I₁ I₂ a b)) ∧
        IsFiniteRange _ _ (mulKernel (summandConst I₁ I₂ a b))) ∧
      ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
        IsInvertibleJet δ p (JetQuad.ofKernel _ _ (mulKernel (summandConst I₁ I₂ a b))) ∧
          logNumber p
            (JetQuad.ofKernel _ _ (mulKernel (summandConst I₁ I₂ a b))) = 0 := by
    intro a b ha hb
    have hC : 0 < ‖a‖ + ‖b‖ + (‖a⁻¹‖ + ‖b⁻¹‖) := by
      have := norm_pos_iff.mpr ha
      positivity
    have bd : ∀ t, ‖summandConst I₁ I₂ a b t‖ ≤ ‖a‖ + ‖b‖ + (‖a⁻¹‖ + ‖b⁻¹‖) := fun t =>
      (summandConst_norm_le a b t).trans (le_add_of_nonneg_right (by positivity))
    have be : ∀ t, ‖summandConst I₁ I₂ a⁻¹ b⁻¹ t‖ ≤ ‖a‖ + ‖b‖ + (‖a⁻¹‖ + ‖b⁻¹‖) := fun t =>
      (summandConst_norm_le a⁻¹ b⁻¹ t).trans (le_add_of_nonneg_left (by positivity))
    exact ⟨mulKernel_periodic_finiteRange hI (summandConst_translate a b) hC bd, fun δ p hδ hp =>
      mulKernel_invertible_logNumber_zero hId hSym hFin hLoc hAdd hI (summandConst_translate a b)
        (summandConst_translate a⁻¹ b⁻¹) (summandConst_mul_inv ha hb) hC bd be hδ hp⟩
  exact opFunComp_sandwich hComp hJet hFin hAdd hArgs hLoc hF hI (sides hx hy).1
    (sides hx' hy').1 (sides hx hy).2 (sides hx' hy').2 M hM
end YangMills.Construction.PeriodicOperators.DiagonalScaling
end
