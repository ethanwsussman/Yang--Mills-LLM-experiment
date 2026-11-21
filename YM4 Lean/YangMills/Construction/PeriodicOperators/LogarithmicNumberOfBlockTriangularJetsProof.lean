import YangMills.Construction.PeriodicOperators.AlgebraOfQuadruplesProof
import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJetsProof
import YangMills.Construction.PeriodicOperators.InverseOfAnInvertibleJetProof
import YangMills.Construction.PeriodicOperators.LogarithmicNumberOfBlockTriangularJets
import YangMills.Construction.PeriodicOperators.OrbitsOfAPeriodicIndexSet
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BlockTriangularLogProof
open JetQuad
section MatrixEntries
variable {A B : Type}
private theorem ext_of_linearMapEntry [Finite A] {M N : (A → ℂ) →ₗ[ℂ] (B → ℂ)}
    (h : linearMapEntry M = linearMapEntry N) : M = N := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMap_ext_of_entry <;> assumption
private theorem linearMapOfEntries_linearMapEntry [Finite A] (N : (A → ℂ) →ₗ[ℂ] (B → ℂ)) :
    linearMapOfEntries (linearMapEntry N) = N :=
  ext_of_linearMapEntry
    (Classical.epsilon_spec (p := fun M => linearMapEntry M = linearMapEntry N) ⟨N, rfl⟩)
end MatrixEntries
section SigmaQuot
variable (J : Fin 2 → PeriodicData)
private def sigmaComponent : (PeriodicData.sigma J).UnitQuot → Σ b, (J b).UnitQuot :=
  Quot.lift (fun ι => ⟨ι.1, (J ι.1).mkQuot 1 ι.2⟩)
    (by
      rintro ι _ ⟨n, rfl⟩
      exact congrArg (Sigma.mk ι.1) (Quot.sound ⟨n, rfl⟩))
private theorem sigmaComponent_sigmaQuotIn (b : Fin 2) (c : (J b).UnitQuot) :
    sigmaComponent J (sigmaQuotIn J b c) = ⟨b, c⟩ := by
  induction c using Quot.ind with
  | mk i => rfl
variable {J}
private theorem sigmaQuotIn_eq {b b' : Fin 2} {c : (J b).UnitQuot} {c' : (J b').UnitQuot}
    (h : sigmaQuotIn J b c = sigmaQuotIn J b' c') :
    (⟨b, c⟩ : Σ b, (J b).UnitQuot) = ⟨b', c'⟩ := by
  rw [← sigmaComponent_sigmaQuotIn, ← sigmaComponent_sigmaQuotIn, h]
private theorem sigmaQuotIn_injective (b : Fin 2) : Function.Injective (sigmaQuotIn J b) :=
  fun c c' h => by simpa using sigmaQuotIn_eq h
private theorem exists_sigmaQuotIn (c : (PeriodicData.sigma J).UnitQuot) :
    ∃ b, ∃ c', sigmaQuotIn J b c' = c := by
  induction c using Quot.ind with
  | mk ι => exact ⟨ι.1, (J ι.1).mkQuot 1 ι.2, rfl⟩
private theorem existsUnique_sigmaQuotIn (c : (PeriodicData.sigma J).UnitQuot) :
    ∃! x : (Σ b, (J b).UnitQuot), sigmaQuotIn J x.1 x.2 = c := by
  obtain ⟨b, c', rfl⟩ := exists_sigmaQuotIn c
  exact ⟨⟨b, c'⟩, rfl, fun y hy => (sigmaQuotIn_eq hy)⟩
end SigmaQuot
section BlockMaps
variable {J : Fin 2 → PeriodicData}
variable (J) in
private def restr (b : Fin 2) : QuotHom (PeriodicData.sigma J) (J b) :=
  LinearMap.funLeft ℂ ℂ (sigmaQuotIn J b)
variable (J) in
private def extZero (b : Fin 2) : QuotHom (J b) (PeriodicData.sigma J) :=
  Function.ExtendByZero.linearMap ℂ (sigmaQuotIn J b)
private theorem extZero_same (b : Fin 2) (f : (J b).UnitQuot → ℂ) (c : (J b).UnitQuot) :
    extZero J b f (sigmaQuotIn J b c) = f c :=
  (sigmaQuotIn_injective b).extend_apply f 0 c
private theorem extZero_ne {b b' : Fin 2} (h : b ≠ b') (f : (J b).UnitQuot → ℂ)
    (c : (J b').UnitQuot) : extZero J b f (sigmaQuotIn J b' c) = 0 := by
  have hc : ¬∃ a, sigmaQuotIn J b a = sigmaQuotIn J b' c := by
    rintro ⟨a, ha⟩
    exact h (congrArg Sigma.fst (sigmaQuotIn_eq ha))
  exact Function.extend_apply' (f := sigmaQuotIn J b) f
    (0 : (PeriodicData.sigma J).UnitQuot → ℂ) _ hc
private theorem restr_extZero (b : Fin 2) (f : (J b).UnitQuot → ℂ) :
    restr J b (extZero J b f) = f :=
  funext fun c => extZero_same b f c
private theorem restr_extZero_ne {b b' : Fin 2} (h : b ≠ b') (f : (J b).UnitQuot → ℂ) :
    restr J b' (extZero J b f) = 0 :=
  funext fun c => extZero_ne h f c
private theorem restr_one_extZero_zero (f : (J 0).UnitQuot → ℂ) :
    restr J 1 (extZero J 0 f) = 0 :=
  restr_extZero_ne (by decide) f
private theorem restr_zero_extZero_one (f : (J 1).UnitQuot → ℂ) :
    restr J 0 (extZero J 1 f) = 0 :=
  restr_extZero_ne (by decide) f
private theorem extZero_restr_add (g : (PeriodicData.sigma J).UnitQuot → ℂ) :
    extZero J 0 (restr J 0 g) + extZero J 1 (restr J 1 g) = g := by
  have key : ∀ (b : Fin 2) (c' : (J b).UnitQuot),
      extZero J 0 (restr J 0 g) (sigmaQuotIn J b c') +
          extZero J 1 (restr J 1 g) (sigmaQuotIn J b c') =
        g (sigmaQuotIn J b c') := by
    refine Fin.forall_fin_two.mpr ⟨fun c' => ?_, fun c' => ?_⟩
    · rw [extZero_same, extZero_ne (by decide : (1 : Fin 2) ≠ 0), add_zero]
      rfl
    · rw [extZero_ne (by decide : (0 : Fin 2) ≠ 1), extZero_same, zero_add]
      rfl
  funext c
  obtain ⟨b, c', rfl⟩ := exists_sigmaQuotIn c
  exact key b c'
open Classical in
private theorem extZero_single (b : Fin 2) (c : (J b).UnitQuot) :
    extZero J b (Pi.single c 1) = Pi.single (sigmaQuotIn J b c) 1 := by
  funext x
  by_cases hx : ∃ a, sigmaQuotIn J b a = x
  · obtain ⟨a, rfl⟩ := hx
    rw [extZero_same]
    simp only [Pi.single_apply, (sigmaQuotIn_injective b).eq_iff]
  · have hne : x ≠ sigmaQuotIn J b c := fun h => hx ⟨c, h.symm⟩
    rw [Pi.single_eq_of_ne hne]
    exact Function.extend_apply' (f := sigmaQuotIn J b) (Pi.single c 1)
      (0 : (PeriodicData.sigma J).UnitQuot → ℂ) _ hx
open Classical in
private theorem linearMapEntry_restr_comp (b b' : Fin 2)
    (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J))
    (c' : (J b').UnitQuot) (c : (J b).UnitQuot) :
    linearMapEntry ((restr J b').comp (M.comp (extZero J b))) c' c =
      linearMapEntry M (sigmaQuotIn J b' c') (sigmaQuotIn J b c) := by
  simp only [linearMapEntry]
  show M (extZero J b (Pi.single c 1)) (sigmaQuotIn J b' c') = _
  rw [extZero_single]
variable [∀ b, Finite (J b).UnitQuot]
private theorem finite_sigma : Finite (PeriodicData.sigma J).UnitQuot :=
  Finite.of_surjective (fun x : (Σ b, (J b).UnitQuot) => sigmaQuotIn J x.1 x.2)
    fun c => by
      obtain ⟨b, c', h⟩ := exists_sigmaQuotIn c
      exact ⟨⟨b, c'⟩, h⟩
private theorem quotHomBlock_eq (b : Fin 2)
    (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)) :
    quotHomBlock J b M = (restr J b).comp (M.comp (extZero J b)) := by
  have h : (fun c' c => linearMapEntry M (sigmaQuotIn J b c') (sigmaQuotIn J b c)) =
      linearMapEntry ((restr J b).comp (M.comp (extZero J b))) := by
    funext c' c
    exact (linearMapEntry_restr_comp b b M c' c).symm
  unfold quotHomBlock
  rw [h]
  exact linearMapOfEntries_linearMapEntry _
private theorem quotHomBlock_apply (b : Fin 2)
    (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J))
    (f : (J b).UnitQuot → ℂ) : quotHomBlock J b M f = restr J b (M (extZero J b f)) := by
  rw [quotHomBlock_eq]
  rfl
private theorem linearMapEntry_quotHomBlock (b : Fin 2)
    (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J))
    (c' c : (J b).UnitQuot) :
    linearMapEntry (quotHomBlock J b M) c' c =
      linearMapEntry M (sigmaQuotIn J b c') (sigmaQuotIn J b c) := by
  rw [quotHomBlock_eq, linearMapEntry_restr_comp]
private theorem quotHomBlock_add (b : Fin 2)
    (M N : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)) :
    quotHomBlock J b (M + N) = quotHomBlock J b M + quotHomBlock J b N := by
  refine LinearMap.ext fun f => ?_
  simp only [quotHomBlock_apply, LinearMap.add_apply, map_add]
private theorem quotHomBlock_smul (b : Fin 2) (a : ℂ)
    (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)) :
    quotHomBlock J b (a • M) = a • quotHomBlock J b M := by
  refine LinearMap.ext fun f => ?_
  simp only [quotHomBlock_apply, LinearMap.smul_apply, map_smul]
private theorem quotHomBlock_zero (b : Fin 2) :
    quotHomBlock J b (0 : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)) = 0 := by
  refine LinearMap.ext fun f => ?_
  simp only [quotHomBlock_apply, LinearMap.zero_apply, map_zero]
private theorem quotHomBlock_id (b : Fin 2) :
    quotHomBlock J b (LinearMap.id : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)) =
      LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  simp only [quotHomBlock_apply, LinearMap.id_apply, restr_extZero]
private theorem trace_eq_trace_add_trace
    (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)) :
    LinearMap.trace ℂ ((PeriodicData.sigma J).UnitQuot → ℂ) M =
      LinearMap.trace ℂ ((J 0).UnitQuot → ℂ) (quotHomBlock J 0 M) +
        LinearMap.trace ℂ ((J 1).UnitQuot → ℂ) (quotHomBlock J 1 M) := by
  have := finite_sigma (J := J)
  have hM : M = (M.comp (extZero J 0)).comp (restr J 0) +
      (M.comp (extZero J 1)).comp (restr J 1) := by
    refine LinearMap.ext fun g => ?_
    show M g = M (extZero J 0 (restr J 0 g)) + M (extZero J 1 (restr J 1 g))
    rw [← map_add, extZero_restr_add]
  rw [quotHomBlock_eq, quotHomBlock_eq]
  conv_lhs => rw [hM]
  rw [map_add, LinearMap.trace_comp_comm', LinearMap.trace_comp_comm' (M.comp (extZero J 1))]
private def LowerZero (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)) : Prop :=
  ∀ f, restr J 1 (M (extZero J 0 f)) = 0
private theorem lowerZero_of_entries {M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (h : ∀ c' c, linearMapEntry M (sigmaQuotIn J 1 c') (sigmaQuotIn J 0 c) = 0) :
    LowerZero M := by
  have h0 : (restr J 1).comp (M.comp (extZero J 0)) = 0 := by
    refine ext_of_linearMapEntry (funext₂ fun c' c => ?_)
    rw [linearMapEntry_restr_comp, h]
    simp [linearMapEntry]
  exact fun f => LinearMap.congr_fun h0 f
private theorem lowerZero_zero :
    LowerZero (0 : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)) :=
  fun f => by simp only [LinearMap.zero_apply, map_zero]
private theorem lowerZero_id :
    LowerZero (LinearMap.id : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)) :=
  fun f => restr_one_extZero_zero f
private theorem lowerZero_add {M N : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (hM : LowerZero M) (hN : LowerZero N) : LowerZero (M + N) :=
  fun f => by rw [LinearMap.add_apply, map_add, hM f, hN f, add_zero]
private theorem lowerZero_smul (a : ℂ) {M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (hM : LowerZero M) : LowerZero (a • M) :=
  fun f => by rw [LinearMap.smul_apply, map_smul, hM f, smul_zero]
private theorem apply_extZero_of_lowerZero
    {N : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)} (hN : LowerZero N)
    (f : (J 0).UnitQuot → ℂ) : N (extZero J 0 f) = extZero J 0 (restr J 0 (N (extZero J 0 f))) := by
  have h := extZero_restr_add (J := J) (N (extZero J 0 f))
  rw [hN f, map_zero, add_zero] at h
  exact h.symm
private theorem lowerZero_comp {M N : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (hM : LowerZero M) (hN : LowerZero N) : LowerZero (M.comp N) :=
  fun f => by
    show restr J 1 (M (N (extZero J 0 f))) = 0
    rw [apply_extZero_of_lowerZero hN f]
    exact hM _
private theorem quotHomBlock_comp (b : Fin 2)
    {M N : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (hM : LowerZero M) (hN : LowerZero N) :
    quotHomBlock J b (M.comp N) = (quotHomBlock J b M).comp (quotHomBlock J b N) := by
  revert b
  refine Fin.forall_fin_two.mpr ⟨LinearMap.ext fun f => ?_, LinearMap.ext fun f => ?_⟩
  · rw [quotHomBlock_apply]
    show restr J 0 (M (N (extZero J 0 f))) = quotHomBlock J 0 M (quotHomBlock J 0 N f)
    rw [quotHomBlock_apply, quotHomBlock_apply, ← apply_extZero_of_lowerZero hN f]
  · rw [quotHomBlock_apply]
    show restr J 1 (M (N (extZero J 1 f))) = quotHomBlock J 1 M (quotHomBlock J 1 N f)
    rw [quotHomBlock_apply, quotHomBlock_apply]
    have h : M (N (extZero J 1 f)) = M (extZero J 0 (restr J 0 (N (extZero J 1 f)))) +
        M (extZero J 1 (restr J 1 (N (extZero J 1 f)))) := by
      rw [← map_add, extZero_restr_add]
    rw [h, map_add, hM _, zero_add]
private def triInverse (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J))
    (P : QuotHom (J 0) (J 0)) (Q : QuotHom (J 1) (J 1)) :
    QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J) :=
  (extZero J 0).comp (P.comp (restr J 0)) + (extZero J 1).comp (Q.comp (restr J 1)) +
    (-1 : ℂ) • (extZero J 0).comp (P.comp ((restr J 0).comp (M.comp ((extZero J 1).comp
      (Q.comp (restr J 1))))))
private theorem triInverse_apply (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J))
    (P : QuotHom (J 0) (J 0)) (Q : QuotHom (J 1) (J 1))
    (g : (PeriodicData.sigma J).UnitQuot → ℂ) :
    triInverse M P Q g = extZero J 0 (P (restr J 0 g)) + extZero J 1 (Q (restr J 1 g)) +
      (-1 : ℂ) • extZero J 0 (P (restr J 0 (M (extZero J 1 (Q (restr J 1 g)))))) :=
  rfl
private theorem lowerZero_triInverse (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J))
    (P : QuotHom (J 0) (J 0)) (Q : QuotHom (J 1) (J 1)) : LowerZero (triInverse M P Q) :=
  fun f => by
    simp only [triInverse_apply, restr_one_extZero_zero, restr_extZero, map_zero, smul_zero,
      add_zero]
private theorem quotHomBlock_triInverse_zero
    (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J))
    (P : QuotHom (J 0) (J 0)) (Q : QuotHom (J 1) (J 1)) :
    quotHomBlock J 0 (triInverse M P Q) = P := by
  refine LinearMap.ext fun f => ?_
  simp only [quotHomBlock_apply, triInverse_apply, restr_one_extZero_zero, restr_extZero,
    map_zero, smul_zero, add_zero]
private theorem quotHomBlock_triInverse_one
    (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J))
    (P : QuotHom (J 0) (J 0)) (Q : QuotHom (J 1) (J 1)) :
    quotHomBlock J 1 (triInverse M P Q) = Q := by
  refine LinearMap.ext fun f => ?_
  simp only [quotHomBlock_apply, triInverse_apply, map_add, map_smul, restr_one_extZero_zero,
    restr_extZero, restr_zero_extZero_one, map_zero, smul_zero, add_zero, zero_add]
private theorem apply_triInverse {M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (hM : LowerZero M) {P : QuotHom (J 0) (J 0)} {Q : QuotHom (J 1) (J 1)}
    (hP : ∀ x, restr J 0 (M (extZero J 0 (P x))) = x)
    (hQ : ∀ x, restr J 1 (M (extZero J 1 (Q x))) = x)
    (g : (PeriodicData.sigma J).UnitQuot → ℂ) : M (triInverse M P Q g) = g := by
  have hM' : ∀ f, restr J 1 (M (extZero J 0 f)) = 0 := hM
  have e1 : restr J 1 (M (triInverse M P Q g)) = restr J 1 g := by
    simp only [triInverse_apply, map_add, map_smul, hM', hQ, smul_zero, add_zero, zero_add]
  have e0 : restr J 0 (M (triInverse M P Q g)) = restr J 0 g := by
    simp only [triInverse_apply, map_add, map_smul, hP]
    rw [neg_smul, one_smul, add_neg_cancel_right]
  calc M (triInverse M P Q g)
      = extZero J 0 (restr J 0 (M (triInverse M P Q g))) +
          extZero J 1 (restr J 1 (M (triInverse M P Q g))) := (extZero_restr_add _).symm
    _ = extZero J 0 (restr J 0 g) + extZero J 1 (restr J 1 g) := by rw [e0, e1]
    _ = g := extZero_restr_add g
private theorem isUnit_and_inverse_eq {M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (hM : LowerZero M)
    (h : ∀ b, IsUnit (quotHomBlock J b M : Module.End ℂ ((J b).UnitQuot → ℂ))) :
    IsUnit (M : Module.End ℂ ((PeriodicData.sigma J).UnitQuot → ℂ)) ∧
      quotHomInverse M = triInverse M (quotHomInverse (quotHomBlock J 0 M))
        (quotHomInverse (quotHomBlock J 1 M)) := by
  have := finite_sigma (J := J)
  have hP : ∀ x, restr J 0 (M (extZero J 0 (quotHomInverse (quotHomBlock J 0 M) x))) = x :=
    fun x => by
      rw [← quotHomBlock_apply]
      exact LinearMap.congr_fun (Ring.mul_inverse_cancel _ (h 0)) x
  have hQ : ∀ x, restr J 1 (M (extZero J 1 (quotHomInverse (quotHomBlock J 1 M) x))) = x :=
    fun x => by
      rw [← quotHomBlock_apply]
      exact LinearMap.congr_fun (Ring.mul_inverse_cancel _ (h 1)) x
  set R : Module.End ℂ ((PeriodicData.sigma J).UnitQuot → ℂ) :=
    triInverse M (quotHomInverse (quotHomBlock J 0 M)) (quotHomInverse (quotHomBlock J 1 M))
    with hR
  have h1 : (M : Module.End ℂ ((PeriodicData.sigma J).UnitQuot → ℂ)) * R = 1 :=
    LinearMap.ext fun g => apply_triInverse hM hP hQ g
  have h2 : R * (M : Module.End ℂ ((PeriodicData.sigma J).UnitQuot → ℂ)) = 1 :=
    mul_eq_one_comm.mp h1
  exact ⟨⟨⟨M, R, h1, h2⟩, rfl⟩, Ring.inverse_unit ⟨M, R, h1, h2⟩⟩
end BlockMaps
section PhaseFactors
private theorem exp_bilinDot_add_castVec (e n : Fin 4 → ℤ) (y : InfiniteLattice.AmbientSpace) :
    Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (y + castVec n))) =
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec y)) := by
  have h : bilinDot (toComplexVec (castVec e)) (toComplexVec (y + castVec n)) =
      bilinDot (toComplexVec (castVec e)) (toComplexVec y) + ((∑ μ, e μ * n μ : ℤ) : ℂ) := by
    simp only [bilinDot, toComplexVec, castVec, Pi.add_apply, Complex.ofReal_add, mul_add,
      Finset.sum_add_distrib, Complex.ofReal_intCast, Int.cast_sum, Int.cast_mul]
  rw [h, mul_add, Complex.exp_add]
  have h1 : Complex.exp (2 * Real.pi * Complex.I * ((∑ μ, e μ * n μ : ℤ) : ℂ)) = 1 := by
    rw [mul_comm]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [h1, mul_one]
private theorem phaseOn_mkQuot (hO : QuotOrbits.Claim) {I : PeriodicData}
    (hI : IsPeriodic I) (e : Fin 4 → ℤ) (ι : I.Carrier) :
    phaseOn I e (I.mkQuot 1 ι) = Complex.exp (2 * Real.pi * Complex.I *
      bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι))) := by
  have hex : ∃ z, ∀ ι', I.mkQuot 1 ι' = I.mkQuot 1 ι →
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι'))) = z := by
    refine ⟨Complex.exp (2 * Real.pi * Complex.I *
      bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι))), fun ι' h => ?_⟩
    obtain ⟨n, hn⟩ := ((hO I hI).1 1 ι' ι).1 h
    rw [hn, hI.pos_translate, exp_bilinDot_add_castVec]
  exact ((Classical.epsilon_spec hex) ι rfl).symm
private theorem phaseOn_ne_zero (hO : QuotOrbits.Claim) {I : PeriodicData}
    (hI : IsPeriodic I) (e : Fin 4 → ℤ) (c : I.UnitQuot) : phaseOn I e c ≠ 0 := by
  induction c using Quot.ind with
  | mk ι =>
    show phaseOn I e (I.mkQuot 1 ι) ≠ 0
    rw [phaseOn_mkQuot hO hI]
    exact Complex.exp_ne_zero _
private theorem isUnit_phaseMul (hO : QuotOrbits.Claim) {I : PeriodicData}
    (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    IsUnit (phaseMul I e : Module.End ℂ (I.UnitQuot → ℂ)) := by
  refine (Module.End.isUnit_iff _).2
    ⟨fun f g h => ?_, fun g => ⟨fun c => (phaseOn I e c)⁻¹ * g c, ?_⟩⟩
  · funext c
    have h' : phaseOn I e c * f c = phaseOn I e c * g c := congrFun h c
    exact mul_left_cancel₀ (phaseOn_ne_zero hO hI e c) h'
  · funext c
    show phaseOn I e c * ((phaseOn I e c)⁻¹ * g c) = g c
    exact mul_inv_cancel_left₀ (phaseOn_ne_zero hO hI e c) _
variable {J : Fin 2 → PeriodicData}
private theorem phaseOn_sigmaQuotIn (hO : QuotOrbits.Claim)
    (hJ : ∀ b, IsPeriodic (J b)) (e : Fin 4 → ℤ) (b : Fin 2) (c : (J b).UnitQuot) :
    phaseOn (PeriodicData.sigma J) e (sigmaQuotIn J b c) = phaseOn (J b) e c := by
  induction c using Quot.ind with
  | mk i =>
    exact (phaseOn_mkQuot hO (IsPeriodic.sigma hJ) e (⟨b, i⟩ : Σ q, (J q).Carrier)).trans
      (phaseOn_mkQuot hO (hJ b) e i).symm
private theorem restr_phaseMul (hO : QuotOrbits.Claim)
    (hJ : ∀ b, IsPeriodic (J b)) (e : Fin 4 → ℤ) (b : Fin 2)
    (g : (PeriodicData.sigma J).UnitQuot → ℂ) :
    restr J b (phaseMul (PeriodicData.sigma J) e g) = phaseMul (J b) e (restr J b g) := by
  funext c
  show phaseOn (PeriodicData.sigma J) e (sigmaQuotIn J b c) * g (sigmaQuotIn J b c) =
    phaseOn (J b) e c * g (sigmaQuotIn J b c)
  rw [phaseOn_sigmaQuotIn hO hJ]
private theorem phaseMul_extZero (hO : QuotOrbits.Claim)
    (hJ : ∀ b, IsPeriodic (J b)) (e : Fin 4 → ℤ) (b : Fin 2)
    (f : (J b).UnitQuot → ℂ) :
    phaseMul (PeriodicData.sigma J) e (extZero J b f) = extZero J b (phaseMul (J b) e f) := by
  funext x
  obtain ⟨b', c', rfl⟩ := exists_sigmaQuotIn x
  show phaseOn (PeriodicData.sigma J) e (sigmaQuotIn J b' c') *
      extZero J b f (sigmaQuotIn J b' c') = extZero J b (phaseMul (J b) e f) (sigmaQuotIn J b' c')
  by_cases hb : b = b'
  · subst hb
    rw [extZero_same, extZero_same, phaseOn_sigmaQuotIn hO hJ]
    rfl
  · rw [extZero_ne hb, extZero_ne hb, mul_zero]
private theorem restr_quotHomInverse_phaseMul (hO : QuotOrbits.Claim)
    (hJ : ∀ b, IsPeriodic (J b)) (e : Fin 4 → ℤ) (b : Fin 2)
    (x : (PeriodicData.sigma J).UnitQuot → ℂ) :
    restr J b (quotHomInverse (phaseMul (PeriodicData.sigma J) e) x) =
      quotHomInverse (phaseMul (J b) e) (restr J b x) := by
  have h1 : phaseMul (PeriodicData.sigma J) e
      (quotHomInverse (phaseMul (PeriodicData.sigma J) e) x) = x :=
    LinearMap.congr_fun
      (Ring.mul_inverse_cancel _ (isUnit_phaseMul hO (IsPeriodic.sigma hJ) e)) x
  have h2 : ∀ y, quotHomInverse (phaseMul (J b) e) (phaseMul (J b) e y) = y := fun y =>
    LinearMap.congr_fun (Ring.inverse_mul_cancel _ (isUnit_phaseMul hO (hJ b) e)) y
  rw [← h2 (restr J b (quotHomInverse (phaseMul (PeriodicData.sigma J) e) x)),
    ← restr_phaseMul hO hJ, h1]
variable [∀ b, Finite (J b).UnitQuot]
private theorem isQuasiPeriodic_quotHomBlock (hO : QuotOrbits.Claim)
    (hJ : ∀ b, IsPeriodic (J b)) (b : Fin 2) {D : Set (Fin 4 → ℂ)}
    {A : (Fin 4 → ℂ) → QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (h : IsQuasiPeriodic D A) : IsQuasiPeriodic D fun κ => quotHomBlock J b (A κ) := by
  intro e κ hκ
  show quotHomBlock J b (A (addTwoPiInt κ e)) =
    (quotHomInverse (phaseMul (J b) e)).comp
      ((quotHomBlock J b (A κ)).comp (phaseMul (J b) e))
  rw [h e κ hκ]
  refine LinearMap.ext fun f => ?_
  rw [quotHomBlock_apply]
  show restr J b (quotHomInverse (phaseMul (PeriodicData.sigma J) e)
      (A κ (phaseMul (PeriodicData.sigma J) e (extZero J b f)))) =
    quotHomInverse (phaseMul (J b) e)
      (quotHomBlock J b (A κ) (phaseMul (J b) e f))
  rw [quotHomBlock_apply, phaseMul_extZero hO hJ, restr_quotHomInverse_phaseMul hO hJ]
private theorem isHolomorphicNbhd_quotHomBlock (b : Fin 2) {D : Set (Fin 4 → ℂ)}
    {A : (Fin 4 → ℂ) → QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (h : IsHolomorphicNbhd D A) : IsHolomorphicNbhd D fun κ => quotHomBlock J b (A κ) := by
  obtain ⟨O, hO, hD, hA⟩ := h
  refine ⟨O, hO, hD, fun c' c => ?_⟩
  simpa only [linearMapEntry_quotHomBlock] using hA (sigmaQuotIn J b c') (sigmaQuotIn J b c)
private theorem isJet_diagBlock (hO : QuotOrbits.Claim)
    (hJ : ∀ b, IsPeriodic (J b)) (b : Fin 2) {δ : ℝ} {p : Fin 4 → ℂ}
    {T : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J)} (hT : IsJet δ p T) :
    IsJet δ p (diagBlock J b T) :=
  ⟨hT.pos_width, hT.mem_imStrip, isHolomorphicNbhd_quotHomBlock b hT.holo_f00,
    isHolomorphicNbhd_quotHomBlock b hT.holo_f10,
    isHolomorphicNbhd_quotHomBlock b hT.holo_f01,
    isHolomorphicNbhd_quotHomBlock b hT.holo_f11,
    isQuasiPeriodic_quotHomBlock hO hJ b hT.quasiPeriodic_f00,
    isQuasiPeriodic_quotHomBlock hO hJ b hT.quasiPeriodic_f10,
    isQuasiPeriodic_quotHomBlock hO hJ b hT.quasiPeriodic_f01,
    isQuasiPeriodic_quotHomBlock hO hJ b hT.quasiPeriodic_f11⟩
end PhaseFactors
section JetEquality
variable {I I' I'' : PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ}
private theorem eqAsJet_refl (T : JetQuad I I') : EqAsJet δ p T T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
private theorem eqAsJet_trans {T S R : JetQuad I I'} (h : EqAsJet δ p T S)
    (h' : EqAsJet δ p S R) : EqAsJet δ p T R := by apply _root_.YangMills.Construction.PeriodicOperators.JetInverse.trans_eqAsJet <;> assumption
private theorem eqAsJet_add {T T' S S' : JetQuad I I'} (hT : EqAsJet δ p T T')
    (hS : EqAsJet δ p S S') : EqAsJet δ p (add T S) (add T' S') := by apply _root_.YangMills.Construction.PeriodicOperators.JetArgumentLemmas.eqAsJet_add <;> assumption
private theorem eqAsJet_smul (a : ℂ) {T T' : JetQuad I I'} (hT : EqAsJet δ p T T') :
    EqAsJet δ p (smul a T) (smul a T') := by apply _root_.YangMills.Construction.PeriodicOperators.JetArgumentLemmas.eqAsJet_smul <;> assumption
private theorem eqAsJet_mul (args : ProductJetArguments δ p) {T T' : JetQuad I I'}
    {S S' : JetQuad I'' I} (hT : EqAsJet δ p T T') (hS : EqAsJet δ p S S') :
    EqAsJet δ p (mul p T S) (mul p T' S') := by
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_⟩
  · show (T.f00 κ).comp (S.f00 κ) = (T'.f00 κ).comp (S'.f00 κ)
    rw [hT.1 hκ, hS.1 hκ]
  · obtain ⟨-, h1, h2, -⟩ := args.comp10 κ hκ
    show (T.f10 κ).comp (S.f00 κ) + (T.f00 (κ + p)).comp (S.f10 κ) =
      (T'.f10 κ).comp (S'.f00 κ) + (T'.f00 (κ + p)).comp (S'.f10 κ)
    rw [hT.2.1 hκ, hS.1 h1, hT.1 h2, hS.2.1 hκ]
  · obtain ⟨-, h1, h2, -⟩ := args.comp01 κ hκ
    show (T.f01 κ).comp (S.f00 κ) + (T.f00 (κ - p)).comp (S.f01 κ) =
      (T'.f01 κ).comp (S'.f00 κ) + (T'.f00 (κ - p)).comp (S'.f01 κ)
    rw [hT.2.2.1 hκ, hS.1 h1, hT.1 h2, hS.2.2.1 hκ]
  · obtain ⟨-, h2, -, -, h5, h6, h7, h8⟩ := args.comp11 κ hκ
    show (T.f11 κ).comp (S.f00 κ) + (T.f00 κ).comp (S.f11 κ) +
        (T.f10 (κ - p)).comp (S.f01 κ) + (T.f01 (κ + p)).comp (S.f10 κ) =
      (T'.f11 κ).comp (S'.f00 κ) + (T'.f00 κ).comp (S'.f11 κ) +
        (T'.f10 (κ - p)).comp (S'.f01 κ) + (T'.f01 (κ + p)).comp (S'.f10 κ)
    rw [hT.2.2.2 hκ, hS.1 h2, hT.1 h2, hS.2.2.2 hκ, hT.2.1 h5, hS.2.2.1 h6, hT.2.2.1 h7,
      hS.2.1 h8]
end JetEquality
section TriangularJets
variable {J : Fin 2 → PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ}
private structure LowerZeroJet (δ : ℝ) (p : Fin 4 → ℂ)
    (T : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J)) : Prop where
  on00 : ∀ κ ∈ imStrip (2 * δ), LowerZero (T.f00 κ)
  on10 : ∀ κ ∈ stripAddShift δ p, LowerZero (T.f10 κ)
  on01 : ∀ κ ∈ stripSubShift δ p, LowerZero (T.f01 κ)
  on11 : ∀ κ ∈ realDualPoints, LowerZero (T.f11 κ)
variable [∀ b, Finite (J b).UnitQuot]
private theorem lowerZeroJet_of_isBlockTriangular
    {T : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (h : IsBlockTriangular δ p J T) : LowerZeroJet δ p T :=
  ⟨fun κ hκ => lowerZero_of_entries fun c' c => (h c' c).1 κ hκ,
    fun κ hκ => lowerZero_of_entries fun c' c => (h c' c).2.1 κ hκ,
    fun κ hκ => lowerZero_of_entries fun c' c => (h c' c).2.2.1 κ hκ,
    fun κ hκ => lowerZero_of_entries fun c' c => (h c' c).2.2.2 κ hκ⟩
private theorem LowerZeroJet.add {T S : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (hT : LowerZeroJet δ p T) (hS : LowerZeroJet δ p S) : LowerZeroJet δ p (JetQuad.add T S) :=
  ⟨fun κ hκ => lowerZero_add (hT.on00 κ hκ) (hS.on00 κ hκ),
    fun κ hκ => lowerZero_add (hT.on10 κ hκ) (hS.on10 κ hκ),
    fun κ hκ => lowerZero_add (hT.on01 κ hκ) (hS.on01 κ hκ),
    fun κ hκ => lowerZero_add (hT.on11 κ hκ) (hS.on11 κ hκ)⟩
private theorem LowerZeroJet.smul (a : ℂ)
    {T : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (hT : LowerZeroJet δ p T) : LowerZeroJet δ p (JetQuad.smul a T) :=
  ⟨fun κ hκ => lowerZero_smul a (hT.on00 κ hκ), fun κ hκ => lowerZero_smul a (hT.on10 κ hκ),
    fun κ hκ => lowerZero_smul a (hT.on01 κ hκ), fun κ hκ => lowerZero_smul a (hT.on11 κ hκ)⟩
private theorem lowerZeroJet_one : LowerZeroJet δ p (one (PeriodicData.sigma J)) :=
  ⟨fun _ _ => lowerZero_id, fun _ _ => lowerZero_zero, fun _ _ => lowerZero_zero,
    fun _ _ => lowerZero_zero⟩
private theorem LowerZeroJet.mul (args : ProductJetArguments δ p)
    {T S : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (hT : LowerZeroJet δ p T) (hS : LowerZeroJet δ p S) :
    LowerZeroJet δ p (JetQuad.mul p T S) := by
  refine ⟨fun κ hκ => lowerZero_comp (hT.on00 κ hκ) (hS.on00 κ hκ), fun κ hκ => ?_,
    fun κ hκ => ?_, fun κ hκ => ?_⟩
  · obtain ⟨-, h1, h2, -⟩ := args.comp10 κ hκ
    exact lowerZero_add (lowerZero_comp (hT.on10 κ hκ) (hS.on00 κ h1))
      (lowerZero_comp (hT.on00 _ h2) (hS.on10 κ hκ))
  · obtain ⟨-, h1, h2, -⟩ := args.comp01 κ hκ
    exact lowerZero_add (lowerZero_comp (hT.on01 κ hκ) (hS.on00 κ h1))
      (lowerZero_comp (hT.on00 _ h2) (hS.on01 κ hκ))
  · obtain ⟨-, h2, -, -, h5, h6, h7, h8⟩ := args.comp11 κ hκ
    exact lowerZero_add (lowerZero_add (lowerZero_add
      (lowerZero_comp (hT.on11 κ hκ) (hS.on00 κ h2))
      (lowerZero_comp (hT.on00 κ h2) (hS.on11 κ hκ)))
      (lowerZero_comp (hT.on10 _ h5) (hS.on01 κ h6)))
      (lowerZero_comp (hT.on01 _ h7) (hS.on10 κ h8))
private theorem eqAsJet_diagBlock_mul (b : Fin 2) (args : ProductJetArguments δ p)
    {T S : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (hT : LowerZeroJet δ p T) (hS : LowerZeroJet δ p S) :
    EqAsJet δ p (diagBlock J b (JetQuad.mul p T S))
      (JetQuad.mul p (diagBlock J b T) (diagBlock J b S)) := by
  refine ⟨fun κ hκ => quotHomBlock_comp b (hT.on00 κ hκ) (hS.on00 κ hκ), fun κ hκ => ?_,
    fun κ hκ => ?_, fun κ hκ => ?_⟩
  · obtain ⟨-, h1, h2, -⟩ := args.comp10 κ hκ
    show quotHomBlock J b ((T.f10 κ).comp (S.f00 κ) + (T.f00 (κ + p)).comp (S.f10 κ)) =
      (quotHomBlock J b (T.f10 κ)).comp (quotHomBlock J b (S.f00 κ)) +
        (quotHomBlock J b (T.f00 (κ + p))).comp (quotHomBlock J b (S.f10 κ))
    rw [quotHomBlock_add, quotHomBlock_comp b (hT.on10 κ hκ) (hS.on00 κ h1),
      quotHomBlock_comp b (hT.on00 _ h2) (hS.on10 κ hκ)]
  · obtain ⟨-, h1, h2, -⟩ := args.comp01 κ hκ
    show quotHomBlock J b ((T.f01 κ).comp (S.f00 κ) + (T.f00 (κ - p)).comp (S.f01 κ)) =
      (quotHomBlock J b (T.f01 κ)).comp (quotHomBlock J b (S.f00 κ)) +
        (quotHomBlock J b (T.f00 (κ - p))).comp (quotHomBlock J b (S.f01 κ))
    rw [quotHomBlock_add, quotHomBlock_comp b (hT.on01 κ hκ) (hS.on00 κ h1),
      quotHomBlock_comp b (hT.on00 _ h2) (hS.on01 κ hκ)]
  · obtain ⟨-, h2, -, -, h5, h6, h7, h8⟩ := args.comp11 κ hκ
    show quotHomBlock J b ((T.f11 κ).comp (S.f00 κ) + (T.f00 κ).comp (S.f11 κ) +
        (T.f10 (κ - p)).comp (S.f01 κ) + (T.f01 (κ + p)).comp (S.f10 κ)) =
      (quotHomBlock J b (T.f11 κ)).comp (quotHomBlock J b (S.f00 κ)) +
        (quotHomBlock J b (T.f00 κ)).comp (quotHomBlock J b (S.f11 κ)) +
        (quotHomBlock J b (T.f10 (κ - p))).comp (quotHomBlock J b (S.f01 κ)) +
        (quotHomBlock J b (T.f01 (κ + p))).comp (quotHomBlock J b (S.f10 κ))
    rw [quotHomBlock_add, quotHomBlock_add, quotHomBlock_add,
      quotHomBlock_comp b (hT.on11 κ hκ) (hS.on00 κ h2),
      quotHomBlock_comp b (hT.on00 κ h2) (hS.on11 κ hκ),
      quotHomBlock_comp b (hT.on10 _ h5) (hS.on01 κ h6),
      quotHomBlock_comp b (hT.on01 _ h7) (hS.on10 κ h8)]
private theorem diagBlock_add (b : Fin 2)
    (X Y : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J)) :
    diagBlock J b (JetQuad.add X Y) = JetQuad.add (diagBlock J b X) (diagBlock J b Y) := by
  refine JetQuad.ext (funext fun κ => ?_) (funext fun κ => ?_) (funext fun κ => ?_)
    (funext fun κ => ?_)
  · exact quotHomBlock_add b (X.f00 κ) (Y.f00 κ)
  · exact quotHomBlock_add b (X.f10 κ) (Y.f10 κ)
  · exact quotHomBlock_add b (X.f01 κ) (Y.f01 κ)
  · exact quotHomBlock_add b (X.f11 κ) (Y.f11 κ)
private theorem diagBlock_smul (b : Fin 2) (a : ℂ)
    (X : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J)) :
    diagBlock J b (JetQuad.smul a X) = JetQuad.smul a (diagBlock J b X) := by
  refine JetQuad.ext (funext fun κ => ?_) (funext fun κ => ?_) (funext fun κ => ?_)
    (funext fun κ => ?_)
  · exact quotHomBlock_smul b a (X.f00 κ)
  · exact quotHomBlock_smul b a (X.f10 κ)
  · exact quotHomBlock_smul b a (X.f01 κ)
  · exact quotHomBlock_smul b a (X.f11 κ)
private theorem diagBlock_one (b : Fin 2) :
    diagBlock J b (one (PeriodicData.sigma J)) = one (J b) := by
  refine JetQuad.ext (funext fun κ => ?_) (funext fun κ => ?_) (funext fun κ => ?_)
    (funext fun κ => ?_)
  · exact quotHomBlock_id b
  · exact quotHomBlock_zero b
  · exact quotHomBlock_zero b
  · exact quotHomBlock_zero b
section InvertibleBlocks
variable {T : JetQuad (PeriodicData.sigma J) (PeriodicData.sigma J)}
private theorem lowerZeroJet_zeroPartInv (hT : LowerZeroJet δ p T)
    (hu : ∀ κ ∈ imStrip (2 * δ), ∀ b,
      IsUnit (quotHomBlock J b (T.f00 κ) : Module.End ℂ ((J b).UnitQuot → ℂ))) :
    LowerZeroJet δ p (zeroPartInv T) := by
  refine ⟨fun κ hκ => ?_, fun _ _ => lowerZero_zero, fun _ _ => lowerZero_zero,
    fun _ _ => lowerZero_zero⟩
  show LowerZero (quotHomInverse (T.f00 κ))
  rw [(isUnit_and_inverse_eq (hT.on00 κ hκ) (hu κ hκ)).2]
  exact lowerZero_triInverse _ _ _
private theorem eqAsJet_diagBlock_zeroPartInv (b : Fin 2) (hT : LowerZeroJet δ p T)
    (hu : ∀ κ ∈ imStrip (2 * δ), ∀ b,
      IsUnit (quotHomBlock J b (T.f00 κ) : Module.End ℂ ((J b).UnitQuot → ℂ))) :
    EqAsJet δ p (diagBlock J b (zeroPartInv T)) (zeroPartInv (diagBlock J b T)) := by
  refine ⟨fun κ hκ => ?_, fun _ _ => quotHomBlock_zero b, fun _ _ => quotHomBlock_zero b,
    fun _ _ => quotHomBlock_zero b⟩
  show quotHomBlock J b (quotHomInverse (T.f00 κ)) = quotHomInverse (quotHomBlock J b (T.f00 κ))
  rw [(isUnit_and_inverse_eq (hT.on00 κ hκ) (hu κ hκ)).2]
  revert b
  exact Fin.forall_fin_two.mpr
    ⟨quotHomBlock_triInverse_zero _ _ _, quotHomBlock_triInverse_one _ _ _⟩
private theorem lowerZeroJet_normalize (args : ProductJetArguments δ p) (hT : LowerZeroJet δ p T)
    (hu : ∀ κ ∈ imStrip (2 * δ), ∀ b,
      IsUnit (quotHomBlock J b (T.f00 κ) : Module.End ℂ ((J b).UnitQuot → ℂ))) :
    LowerZeroJet δ p (normalize p T) :=
  ((lowerZeroJet_zeroPartInv hT hu).mul args hT).add (lowerZeroJet_one.smul _)
private theorem eqAsJet_diagBlock_normalize (b : Fin 2) (args : ProductJetArguments δ p)
    (hT : LowerZeroJet δ p T)
    (hu : ∀ κ ∈ imStrip (2 * δ), ∀ b,
      IsUnit (quotHomBlock J b (T.f00 κ) : Module.End ℂ ((J b).UnitQuot → ℂ))) :
    EqAsJet δ p (diagBlock J b (normalize p T)) (normalize p (diagBlock J b T)) := by
  unfold JetQuad.normalize
  rw [diagBlock_add, diagBlock_smul, diagBlock_one]
  exact eqAsJet_add (eqAsJet_trans
    (eqAsJet_diagBlock_mul b args (lowerZeroJet_zeroPartInv hT hu) hT)
    (eqAsJet_mul args (eqAsJet_diagBlock_zeroPartInv b hT hu) (eqAsJet_refl _)))
    (eqAsJet_refl _)
private theorem eqAsJet_diagBlock_logSeries (b : Fin 2)
    (args : ProductJetArguments δ p) (hT : LowerZeroJet δ p T)
    (hu : ∀ κ ∈ imStrip (2 * δ), ∀ b,
      IsUnit (quotHomBlock J b (T.f00 κ) : Module.End ℂ ((J b).UnitQuot → ℂ))) :
    EqAsJet δ p (diagBlock J b (logSeries p T)) (logSeries p (diagBlock J b T)) := by
  unfold logSeries
  rw [diagBlock_add, diagBlock_smul]
  have hN := eqAsJet_diagBlock_normalize b args hT hu
  exact eqAsJet_add hN (eqAsJet_smul _ (eqAsJet_trans
    (eqAsJet_diagBlock_mul b args (lowerZeroJet_normalize args hT hu)
      (lowerZeroJet_normalize args hT hu))
    (eqAsJet_mul args hN hN)))
end InvertibleBlocks
end TriangularJets
section NormBounds
variable {J : Fin 2 → PeriodicData}
private theorem quotHomNorm_comp_le (hN : QuotMatrixNorms.Claim) {I I' I'' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    (M : QuotHom I I') (N : QuotHom I'' I) :
    quotHomNorm (M.comp N) ≤ quotHomNorm M * quotHomNorm N :=
  (hN I I' I'' hI hI' hI'').2.1 M N
private theorem quotHomNorm_triInverse_le (hN : QuotMatrixNorms.Claim)
    (hJ : ∀ b, IsPeriodic (J b)) (M : QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J))
    (P : QuotHom (J 0) (J 0)) (Q : QuotHom (J 1) (J 1)) :
    quotHomNorm (triInverse M P Q) ≤
      quotHomNorm (extZero J 0) * (quotHomNorm P * quotHomNorm (restr J 0)) +
        quotHomNorm (extZero J 1) * (quotHomNorm Q * quotHomNorm (restr J 1)) +
        quotHomNorm (extZero J 0) * (quotHomNorm P * (quotHomNorm (restr J 0) *
          (quotHomNorm M * (quotHomNorm (extZero J 1) *
            (quotHomNorm Q * quotHomNorm (restr J 1)))))) := by
  have hU := IsPeriodic.sigma hJ
  have h0 := hJ 0
  have h1 := hJ 1
  have hnorm := (hN _ _ _ hU hU hU).1
  have hX : quotHomNorm ((extZero J 0).comp (P.comp (restr J 0))) ≤
      quotHomNorm (extZero J 0) * (quotHomNorm P * quotHomNorm (restr J 0)) :=
    (quotHomNorm_comp_le hN h0 hU hU _ _).trans
      (mul_le_mul' le_rfl (quotHomNorm_comp_le hN h0 h0 hU _ _))
  have hY : quotHomNorm ((extZero J 1).comp (Q.comp (restr J 1))) ≤
      quotHomNorm (extZero J 1) * (quotHomNorm Q * quotHomNorm (restr J 1)) :=
    (quotHomNorm_comp_le hN h1 hU hU _ _).trans
      (mul_le_mul' le_rfl (quotHomNorm_comp_le hN h1 h1 hU _ _))
  have hZ : quotHomNorm ((-1 : ℂ) • (extZero J 0).comp (P.comp ((restr J 0).comp (M.comp
      ((extZero J 1).comp (Q.comp (restr J 1))))))) ≤
      quotHomNorm (extZero J 0) * (quotHomNorm P * (quotHomNorm (restr J 0) *
        (quotHomNorm M * (quotHomNorm (extZero J 1) *
          (quotHomNorm Q * quotHomNorm (restr J 1)))))) := by
    refine (hnorm.2.2.1 _ _).trans ?_
    simp only [norm_neg, norm_one, ENNReal.ofReal_one, one_mul]
    refine (quotHomNorm_comp_le hN h0 hU hU _ _).trans (mul_le_mul' le_rfl ?_)
    refine (quotHomNorm_comp_le hN h0 h0 hU _ _).trans (mul_le_mul' le_rfl ?_)
    refine (quotHomNorm_comp_le hN hU h0 hU _ _).trans (mul_le_mul' le_rfl ?_)
    refine (quotHomNorm_comp_le hN hU hU hU _ _).trans (mul_le_mul' le_rfl hY)
  exact (hnorm.2.1 _ _).trans (add_le_add ((hnorm.2.1 _ _).trans (add_le_add hX hY)) hZ)
end NormBounds
section TraceIntegrals
private theorem integrableOn_trace_f11 {I : PeriodicData} (hI : IsPeriodic I) {δ : ℝ}
    {p : Fin 4 → ℂ} {T : JetQuad I I} (hT : IsJet δ p T) :
    IntegrableOn (fun κ => LinearMap.trace ℂ (I.UnitQuot → ℂ) (T.f11 (toComplexVec κ)))
      (Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)) := by apply _root_.YangMills.SharedProofs.p41810 <;> assumption
end TraceIntegrals
private theorem blockTriangularLogNumber_of (hF : JetDomains.OpFunJetTheory)
    (hA : JetArgumentsAndEqualJets)
    (hN : QuotMatrixNorms.Claim)
    (hO : QuotOrbits.Claim) {δ : ℝ} {p : Fin 4 → ℂ} (hδ : 0 < δ)
    (hp : p ∈ imStrip δ) : JetCalculus.BlockTriangularLogNumber δ p := by
  intro J hJ
  have : ∀ b, Finite (J b).UnitQuot := fun b => (hJ b).finite_quot
  refine ⟨existsUnique_sigmaQuotIn, fun T hT hTri => ?_⟩
  have hjets : ∀ b, IsJet δ p (diagBlock J b T) := fun b => isJet_diagBlock hO hJ b hT
  refine ⟨hjets, fun hinv => ?_⟩
  have hU := IsPeriodic.sigma hJ
  have h0 := hJ 0
  have h1 := hJ 1
  have args : ProductJetArguments δ p := (hA.1 δ p hδ hp).2.1
  have hLZ : LowerZeroJet δ p T := lowerZeroJet_of_isBlockTriangular hTri
  have hu : ∀ κ ∈ imStrip (2 * δ), ∀ b,
      IsUnit (quotHomBlock J b (T.f00 κ) : Module.End ℂ ((J b).UnitQuot → ℂ)) :=
    fun κ hκ b => (hinv b).isUnit_f00 κ hκ
  have hbound : (⨆ κ ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (T.f00 κ))) < ⊤ := by
    have hi0 : quotHomNorm (extZero J 0) < ⊤ := (hN _ _ _ h0 hU hU).1.1 _
    have hi1 : quotHomNorm (extZero J 1) < ⊤ := (hN _ _ _ h1 hU hU).1.1 _
    have hp0 : quotHomNorm (restr J 0) < ⊤ := (hN _ _ _ hU h0 hU).1.1 _
    have hp1 : quotHomNorm (restr J 1) < ⊤ := (hN _ _ _ hU h1 hU).1.1 _
    have hM := ((hF.2.2 _ _ _ hU hU hU δ p hδ hp).sups_finite T hT).1
    have hP := (hinv 0).bdd_inverse
    have hQ := (hinv 1).bdd_inverse
    refine lt_of_le_of_lt (iSup₂_le fun κ hκ => ?_) (ENNReal.add_lt_top.2
      ⟨ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top hi0 (ENNReal.mul_lt_top hP hp0),
        ENNReal.mul_lt_top hi1 (ENNReal.mul_lt_top hQ hp1)⟩,
        ENNReal.mul_lt_top hi0 (ENNReal.mul_lt_top hP (ENNReal.mul_lt_top hp0
          (ENNReal.mul_lt_top hM (ENNReal.mul_lt_top hi1 (ENNReal.mul_lt_top hQ hp1)))))⟩)
    have hMκ : quotHomNorm (T.f00 κ) ≤ ⨆ κ ∈ imStrip (2 * δ), quotHomNorm (T.f00 κ) :=
      le_iSup₂ (f := fun κ (_ : κ ∈ imStrip (2 * δ)) => quotHomNorm (T.f00 κ)) κ hκ
    have hPκ : quotHomNorm (quotHomInverse ((diagBlock J 0 T).f00 κ)) ≤
        ⨆ κ ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse ((diagBlock J 0 T).f00 κ)) :=
      le_iSup₂ (f := fun κ (_ : κ ∈ imStrip (2 * δ)) =>
        quotHomNorm (quotHomInverse ((diagBlock J 0 T).f00 κ))) κ hκ
    have hQκ : quotHomNorm (quotHomInverse ((diagBlock J 1 T).f00 κ)) ≤
        ⨆ κ ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse ((diagBlock J 1 T).f00 κ)) :=
      le_iSup₂ (f := fun κ (_ : κ ∈ imStrip (2 * δ)) =>
        quotHomNorm (quotHomInverse ((diagBlock J 1 T).f00 κ))) κ hκ
    rw [(isUnit_and_inverse_eq (hLZ.on00 κ hκ) (hu κ hκ)).2]
    refine (quotHomNorm_triInverse_le hN hJ _ _ _).trans ?_
    exact add_le_add
      (add_le_add (mul_le_mul' le_rfl (mul_le_mul' hPκ le_rfl))
        (mul_le_mul' le_rfl (mul_le_mul' hQκ le_rfl)))
      (mul_le_mul' le_rfl (mul_le_mul' hPκ (mul_le_mul' le_rfl (mul_le_mul' hMκ
        (mul_le_mul' le_rfl (mul_le_mul' hQκ le_rfl))))))
  have hTinv : IsInvertibleJet δ p T :=
    ⟨hT, fun κ hκ => (isUnit_and_inverse_eq (hLZ.on00 κ hκ) (hu κ hκ)).1, hbound⟩
  refine ⟨hTinv, ?_⟩
  have hint : ∀ b, IntegrableOn (fun y => LinearMap.trace ℂ ((J b).UnitQuot → ℂ)
      ((logSeries p (diagBlock J b T)).f11 (toComplexVec y)))
      (Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)) := fun b =>
    integrableOn_trace_f11 (hJ b) ((hF.2.2 _ _ _ (hJ b) (hJ b) (hJ b) δ p hδ
      hp).invertible_derived_isJet _ (hinv b)).2.2.2
  have hpoint : ∀ y, LinearMap.trace ℂ ((PeriodicData.sigma J).UnitQuot → ℂ)
      ((logSeries p T).f11 (toComplexVec y)) =
      LinearMap.trace ℂ ((J 0).UnitQuot → ℂ)
          ((logSeries p (diagBlock J 0 T)).f11 (toComplexVec y)) +
        LinearMap.trace ℂ ((J 1).UnitQuot → ℂ)
          ((logSeries p (diagBlock J 1 T)).f11 (toComplexVec y)) := fun y => by
    have hy : toComplexVec y ∈ realDualPoints := fun μ => Complex.ofReal_im (y μ)
    have e0 : quotHomBlock J 0 ((logSeries p T).f11 (toComplexVec y)) =
        (logSeries p (diagBlock J 0 T)).f11 (toComplexVec y) :=
      (eqAsJet_diagBlock_logSeries 0 args hLZ hu).2.2.2 hy
    have e1 : quotHomBlock J 1 ((logSeries p T).f11 (toComplexVec y)) =
        (logSeries p (diagBlock J 1 T)).f11 (toComplexVec y) :=
      (eqAsJet_diagBlock_logSeries 1 args hLZ hu).2.2.2 hy
    rw [trace_eq_trace_add_trace, e0, e1]
  simp only [logNumber, traceNumber, torusAverage, hpoint]
  rw [integral_add (hint 0) (hint 1), mul_add]
theorem blockTriangularLog_claim (hF : JetDomains.OpFunJetTheory)
    (hA : JetArgumentsAndEqualJets)
    (hN : QuotMatrixNorms.Claim)
    (hO : QuotOrbits.Claim) :
    BlockTriangularLog.Claim :=
  fun _ _ hδ hp => blockTriangularLogNumber_of hF hA hN hO hδ hp
end YangMills.Construction.PeriodicOperators.BlockTriangularLogProof
end
