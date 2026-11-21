import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.JetTripleOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.JetsOnADisjointSumAndOnTheUnionOfAPair
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.DisjSumJets
open JetQuad (IsJet)
section Entries
variable {J J' : Type}
theorem linearMapEntry_injective [Finite J] {M N : (J → ℂ) →ₗ[ℂ] (J' → ℂ)}
    (h : linearMapEntry M = linearMapEntry N) : M = N := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMap_ext_of_entry <;> assumption
theorem linearMapEntry_linearMapOfEntries [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
theorem wNorm_comp_equiv {L : Type} (e : J ≃ L) (w : L → ℝ) (f : L → ℂ) :
    wNorm (w ∘ e) (f ∘ e) = wNorm w f := by
  unfold wNorm
  congr 1
  exact e.tsum_eq fun i => w i * ‖f i‖ ^ 2
theorem normSummable_comp_equiv {L : Type} (e : J ≃ L) (w : L → ℝ) (f : L → ℂ) :
    NormSummable (w ∘ e) (f ∘ e) ↔ NormSummable w f :=
  e.summable_iff (f := fun i => |w i * ‖f i‖ ^ 2|)
end Entries
structure PeriodicIso (A B : PeriodicData) where
  toEquiv : A.Carrier ≃ B.Carrier
  map_translate : ∀ n x, toEquiv (A.translate n x) = B.translate n (toEquiv x)
  map_pos : ∀ x, B.pos (toEquiv x) = A.pos x
  map_weight : ∀ x, B.weightOf (toEquiv x) = A.weightOf x
namespace PeriodicIso
variable {A B : PeriodicData} (u : PeriodicIso A B)
theorem symm_translate (n : Fin 4 → ℤ) (y : B.Carrier) :
    u.toEquiv.symm (B.translate n y) = A.translate n (u.toEquiv.symm y) := by
  apply u.toEquiv.injective
  rw [u.map_translate, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
def quotMap : A.UnitQuot → B.UnitQuot :=
  Quot.lift (fun x => B.mkQuot 1 (u.toEquiv x))
    (by
      rintro x _ ⟨n, rfl⟩
      exact Quot.sound ⟨n, u.map_translate _ _⟩)
def quotInv : B.UnitQuot → A.UnitQuot :=
  Quot.lift (fun y => A.mkQuot 1 (u.toEquiv.symm y))
    (by
      rintro y _ ⟨n, rfl⟩
      exact Quot.sound ⟨n, u.symm_translate _ _⟩)
theorem quotInv_quotMap (c : A.UnitQuot) : u.quotInv (u.quotMap c) = c := by
  induction c using Quot.ind with
  | mk x => exact congrArg (A.mkQuot 1) (u.toEquiv.symm_apply_apply x)
theorem quotMap_quotInv (c : B.UnitQuot) : u.quotMap (u.quotInv c) = c := by
  induction c using Quot.ind with
  | mk y => exact congrArg (B.mkQuot 1) (u.toEquiv.apply_symm_apply y)
def quotEquiv : A.UnitQuot ≃ B.UnitQuot where
  toFun := u.quotMap
  invFun := u.quotInv
  left_inv := u.quotInv_quotMap
  right_inv := u.quotMap_quotInv
theorem quotInv_mkQuot (x : A.Carrier) :
    u.quotInv (B.mkQuot 1 (u.toEquiv x)) = A.mkQuot 1 x :=
  congrArg (A.mkQuot 1) (u.toEquiv.symm_apply_apply x)
theorem mkQuot_eq_quotMap_iff (c : A.UnitQuot) (x : A.Carrier) :
    B.mkQuot 1 (u.toEquiv x) = u.quotMap c ↔ A.mkQuot 1 x = c := by
  constructor
  · intro h
    have := congrArg u.quotInv h
    rwa [quotInv_mkQuot, quotInv_quotMap] at this
  · rintro rfl
    rfl
theorem quotWeight_quotMap (c : A.UnitQuot) :
    B.quotWeight 1 (u.quotMap c) = A.quotWeight 1 c := by
  unfold PeriodicData.quotWeight
  congr 1
  funext w
  refine propext ⟨fun h x hx => ?_, fun h y hy => ?_⟩
  · rw [← u.map_weight]
    exact h _ ((u.mkQuot_eq_quotMap_iff c x).2 hx)
  · obtain ⟨x, rfl⟩ := u.toEquiv.surjective y
    rw [u.map_weight]
    exact h x ((u.mkQuot_eq_quotMap_iff c x).1 hy)
theorem quotWeight_comp : B.quotWeight 1 ∘ u.quotEquiv = A.quotWeight 1 :=
  funext u.quotWeight_quotMap
theorem phaseOn_quotMap (e : Fin 4 → ℤ) (c : A.UnitQuot) :
    phaseOn B e (u.quotMap c) = phaseOn A e c := by
  unfold phaseOn
  congr 1
  funext z
  refine propext ⟨fun h x hx => ?_, fun h y hy => ?_⟩
  · rw [← u.map_pos]
    exact h _ ((u.mkQuot_eq_quotMap_iff c x).2 hx)
  · obtain ⟨x, rfl⟩ := u.toEquiv.surjective y
    rw [u.map_pos]
    exact h x ((u.mkQuot_eq_quotMap_iff c x).1 hy)
def conjHom (M : QuotHom A A) : QuotHom B B :=
  (LinearMap.funLeft ℂ ℂ u.quotInv).comp (M.comp (LinearMap.funLeft ℂ ℂ u.quotMap))
theorem conjHom_apply (M : QuotHom A A) (f : B.UnitQuot → ℂ) (c' : B.UnitQuot) :
    u.conjHom M f c' = M (f ∘ u.quotMap) (u.quotInv c') := rfl

theorem conjHom_add (M N : QuotHom A A) : u.conjHom (M + N) = u.conjHom M + u.conjHom N := rfl

theorem conjHom_smul (z : ℂ) (M : QuotHom A A) : u.conjHom (z • M) = z • u.conjHom M := rfl

theorem linearMapEntry_conjHom (M : QuotHom A A) (c' d : B.UnitQuot) :
    linearMapEntry (u.conjHom M) c' d = linearMapEntry M (u.quotInv c') (u.quotInv d) := by
  classical
  have hs : (Pi.single d 1 : B.UnitQuot → ℂ) ∘ u.quotMap = Pi.single (u.quotInv d) 1 := by
    funext x
    by_cases h : x = u.quotInv d
    · subst h
      simp [quotMap_quotInv]
    · have h' : u.quotMap x ≠ d := fun e => h (by rw [← e, quotInv_quotMap])
      simp [h, h']
  simp only [linearMapEntry, conjHom_apply, hs]
theorem conjHom_zero : u.conjHom (0 : QuotHom A A) = 0 := by
  ext f c'
  simp [conjHom]
theorem conjHom_comp (M N : QuotHom A A) :
    (u.conjHom M).comp (u.conjHom N) = u.conjHom (M.comp N) := by
  refine LinearMap.ext fun f => ?_
  funext c'
  have h : (u.conjHom N f) ∘ u.quotMap = N (f ∘ u.quotMap) := by
    funext x
    simp only [Function.comp_apply, conjHom_apply, quotInv_quotMap]
  simp only [LinearMap.comp_apply, conjHom_apply, h]
theorem conjHom_id : u.conjHom (LinearMap.id : QuotHom A A) = LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  funext c'
  simp [conjHom_apply, quotMap_quotInv]
def quotFunEquiv : (A.UnitQuot → ℂ) ≃ₗ[ℂ] (B.UnitQuot → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ u.quotEquiv.symm
theorem conjHom_eq (M : QuotHom A A) : u.conjHom M = u.quotFunEquiv.conj M := by
  refine LinearMap.ext fun f => ?_
  funext c'
  rfl
theorem trace_conjHom [Finite A.UnitQuot] (M : QuotHom A A) :
    LinearMap.trace ℂ (B.UnitQuot → ℂ) (u.conjHom M) = LinearMap.trace ℂ (A.UnitQuot → ℂ) M := by
  have : Finite B.UnitQuot := Finite.of_equiv _ u.quotEquiv
  rw [conjHom_eq]
  exact LinearMap.trace_conj' M u.quotFunEquiv
def unconjHom (N : QuotHom B B) : QuotHom A A :=
  (LinearMap.funLeft ℂ ℂ u.quotMap).comp (N.comp (LinearMap.funLeft ℂ ℂ u.quotInv))
theorem unconjHom_conjHom (M : QuotHom A A) : u.unconjHom (u.conjHom M) = M := by
  refine LinearMap.ext fun f => ?_
  funext x
  have h : (LinearMap.funLeft ℂ ℂ u.quotInv f) ∘ u.quotMap = f := by
    funext y
    simp [LinearMap.funLeft_apply, quotInv_quotMap]
  simp [unconjHom, LinearMap.funLeft_apply, conjHom_apply, quotInv_quotMap, h]
theorem conjHom_unconjHom (N : QuotHom B B) : u.conjHom (u.unconjHom N) = N := by
  refine LinearMap.ext fun f => ?_
  funext x
  have h : LinearMap.funLeft ℂ ℂ u.quotInv (f ∘ u.quotMap) = f := by
    funext y
    simp [LinearMap.funLeft_apply, quotMap_quotInv]
  simp [unconjHom, LinearMap.funLeft_apply, conjHom_apply, quotMap_quotInv, h]
def endMulEquiv : Module.End ℂ (A.UnitQuot → ℂ) ≃* Module.End ℂ (B.UnitQuot → ℂ) where
  toFun M := u.conjHom M
  invFun N := u.unconjHom N
  left_inv := u.unconjHom_conjHom
  right_inv := u.conjHom_unconjHom
  map_mul' M N := (u.conjHom_comp M N).symm
theorem isUnit_conjHom (M : QuotHom A A) :
    IsUnit (u.conjHom M : Module.End ℂ (B.UnitQuot → ℂ)) ↔
      IsUnit (M : Module.End ℂ (A.UnitQuot → ℂ)) :=
  MulEquiv.isUnit_map u.endMulEquiv
theorem quotHomInverse_conjHom (M : QuotHom A A) :
    quotHomInverse (u.conjHom M) = u.conjHom (quotHomInverse M) := by
  unfold quotHomInverse
  by_cases h : IsUnit (M : Module.End ℂ (A.UnitQuot → ℂ))
  · obtain ⟨w, hw⟩ := h
    have hc : (u.conjHom M : Module.End ℂ (B.UnitQuot → ℂ)) =
        ((Units.map u.endMulEquiv.toMonoidHom w : (Module.End ℂ (B.UnitQuot → ℂ))ˣ) :
          Module.End ℂ (B.UnitQuot → ℂ)) := by
      rw [← hw]
      rfl
    rw [hc, ← hw, Ring.inverse_unit, Ring.inverse_unit]
    rfl
  · rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ (mt (u.isUnit_conjHom M).1 h),
      conjHom_zero]
theorem phaseMul_eq_conjHom (e : Fin 4 → ℤ) :
    phaseMul B e = u.conjHom (phaseMul A e) := by
  refine LinearMap.ext fun f => ?_
  funext c'
  obtain ⟨d, rfl⟩ := u.quotEquiv.surjective c'
  show phaseOn B e (u.quotMap d) * f (u.quotMap d) =
    phaseOn A e (u.quotInv (u.quotMap d)) * f (u.quotMap (u.quotInv (u.quotMap d)))
  rw [phaseOn_quotMap, quotInv_quotMap]
theorem normSummable_comp_quotMap (g : B.UnitQuot → ℂ) :
    NormSummable (A.quotWeight 1) (g ∘ u.quotMap) ↔ NormSummable (B.quotWeight 1) g := by
  have h := normSummable_comp_equiv u.quotEquiv (B.quotWeight 1) g
  rw [u.quotWeight_comp] at h
  exact h
theorem wNorm_comp_quotMap (g : B.UnitQuot → ℂ) :
    wNorm (A.quotWeight 1) (g ∘ u.quotMap) = wNorm (B.quotWeight 1) g := by
  have h := wNorm_comp_equiv u.quotEquiv (B.quotWeight 1) g
  rw [u.quotWeight_comp] at h
  exact h
theorem comp_quotMap_mem_wUnitBall (g : B.UnitQuot → ℂ) :
    g ∘ u.quotMap ∈ wUnitBall (A.quotWeight 1) univ ↔ g ∈ wUnitBall (B.quotWeight 1) univ := by
  simp only [wUnitBall, mem_ofPred_eq, mem_univ, true_and, normSummable_comp_quotMap,
    wNorm_comp_quotMap]
theorem quotHomNorm_conjHom (M : QuotHom A A) : quotHomNorm (u.conjHom M) = quotHomNorm M := by
  unfold quotHomNorm wOpNorm
  have hval : ∀ g : B.UnitQuot → ℂ,
      wNorm (B.quotWeight 1) (u.conjHom M g) =
        wNorm (A.quotWeight 1) (M (g ∘ u.quotMap)) := by
    intro g
    rw [← wNorm_comp_quotMap u (u.conjHom M g)]
    congr 1
    funext x
    simp only [Function.comp_apply, conjHom_apply, quotInv_quotMap]
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rw [hval]
    exact le_iSup₂_of_le (g ∘ u.quotMap) ((u.comp_quotMap_mem_wUnitBall g).2 hg) le_rfl
  · refine iSup₂_le fun f hf => ?_
    have hg : (f ∘ u.quotInv) ∘ u.quotMap = f := by
      funext y
      simp [quotInv_quotMap]
    refine le_iSup₂_of_le (f ∘ u.quotInv) ((u.comp_quotMap_mem_wUnitBall _).1 (by rwa [hg])) ?_
    rw [hval, hg]
def conjQuad (T : JetQuad A A) : JetQuad B B :=
  ⟨fun κ => u.conjHom (T.f00 κ), fun κ => u.conjHom (T.f10 κ), fun κ => u.conjHom (T.f01 κ),
    fun κ => u.conjHom (T.f11 κ)⟩
theorem isHolomorphicNbhd_conjHom {D : Set (Fin 4 → ℂ)} {G : (Fin 4 → ℂ) → QuotHom A A}
    (h : IsHolomorphicNbhd D G) : IsHolomorphicNbhd D fun κ => u.conjHom (G κ) := by
  obtain ⟨O, hO, hD, hG⟩ := h
  refine ⟨O, hO, hD, fun c' d => ?_⟩
  simp only [linearMapEntry_conjHom]
  exact hG _ _
theorem isQuasiPeriodic_conjHom {D : Set (Fin 4 → ℂ)} {G : (Fin 4 → ℂ) → QuotHom A A}
    (h : IsQuasiPeriodic D G) : IsQuasiPeriodic D fun κ => u.conjHom (G κ) := by
  intro e κ hκ
  show u.conjHom (G (addTwoPiInt κ e)) =
    (quotHomInverse (phaseMul B e)).comp ((u.conjHom (G κ)).comp (phaseMul B e))
  rw [h e κ hκ, u.phaseMul_eq_conjHom, u.quotHomInverse_conjHom, conjHom_comp, conjHom_comp]
theorem isJet_conjQuad {δ : ℝ} {p : Fin 4 → ℂ} {T : JetQuad A A} (h : IsJet δ p T) :
    IsJet δ p (u.conjQuad T) where
  pos_width := h.pos_width
  mem_imStrip := h.mem_imStrip
  holo_f00 := u.isHolomorphicNbhd_conjHom h.holo_f00
  holo_f10 := u.isHolomorphicNbhd_conjHom h.holo_f10
  holo_f01 := u.isHolomorphicNbhd_conjHom h.holo_f01
  holo_f11 := u.isHolomorphicNbhd_conjHom h.holo_f11
  quasiPeriodic_f00 := u.isQuasiPeriodic_conjHom h.quasiPeriodic_f00
  quasiPeriodic_f10 := u.isQuasiPeriodic_conjHom h.quasiPeriodic_f10
  quasiPeriodic_f01 := u.isQuasiPeriodic_conjHom h.quasiPeriodic_f01
  quasiPeriodic_f11 := u.isQuasiPeriodic_conjHom h.quasiPeriodic_f11
theorem conjQuad_add (T S : JetQuad A A) :
    u.conjQuad (JetQuad.add T S) = JetQuad.add (u.conjQuad T) (u.conjQuad S) := by
  refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
    simp only [conjQuad, JetQuad.add, Pi.add_apply, conjHom_add]
theorem conjQuad_smul (z : ℂ) (T : JetQuad A A) :
    u.conjQuad (JetQuad.smul z T) = JetQuad.smul z (u.conjQuad T) := by
  refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
    simp only [conjQuad, JetQuad.smul, Pi.smul_apply, conjHom_smul]
theorem conjQuad_mul (p : Fin 4 → ℂ) (T S : JetQuad A A) :
    u.conjQuad (JetQuad.mul p T S) = JetQuad.mul p (u.conjQuad T) (u.conjQuad S) := by
  refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
    simp only [conjQuad, JetQuad.mul, conjHom_add, conjHom_comp]
theorem conjQuad_one : u.conjQuad (JetQuad.one A) = JetQuad.one B := by
  refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
    simp only [conjQuad, JetQuad.one, conjHom_id, Pi.zero_apply, conjHom_zero]
theorem zeroPartInv_conjQuad (T : JetQuad A A) :
    JetQuad.zeroPartInv (u.conjQuad T) = u.conjQuad (JetQuad.zeroPartInv T) := by
  refine JetQuad.ext ?_ ?_ ?_ ?_ <;> funext κ <;>
    simp only [conjQuad, JetQuad.zeroPartInv, quotHomInverse_conjHom, Pi.zero_apply,
      conjHom_zero]
theorem normalize_conjQuad (p : Fin 4 → ℂ) (T : JetQuad A A) :
    JetQuad.normalize p (u.conjQuad T) = u.conjQuad (JetQuad.normalize p T) := by
  unfold JetQuad.normalize
  rw [zeroPartInv_conjQuad, ← conjQuad_mul, ← conjQuad_one, ← conjQuad_smul, ← conjQuad_add]
theorem logSeries_conjQuad (p : Fin 4 → ℂ) (T : JetQuad A A) :
    JetQuad.logSeries p (u.conjQuad T) = u.conjQuad (JetQuad.logSeries p T) := by
  unfold JetQuad.logSeries
  rw [normalize_conjQuad, ← conjQuad_mul, ← conjQuad_smul, ← conjQuad_add]
theorem traceNumber_conjQuad [Finite A.UnitQuot] (T : JetQuad A A) :
    JetQuad.traceNumber (u.conjQuad T) = JetQuad.traceNumber T := by
  unfold JetQuad.traceNumber
  congr 1
  funext κ
  simp only [conjQuad, trace_conjHom]
theorem logNumber_conjQuad [Finite A.UnitQuot] (p : Fin 4 → ℂ) (T : JetQuad A A) :
    JetQuad.logNumber p (u.conjQuad T) = JetQuad.logNumber p T := by
  unfold JetQuad.logNumber
  rw [logSeries_conjQuad, traceNumber_conjQuad]
theorem isInvertibleJet_conjQuad {δ : ℝ} {p : Fin 4 → ℂ} {T : JetQuad A A}
    (h : JetQuad.IsInvertibleJet δ p T) : JetQuad.IsInvertibleJet δ p (u.conjQuad T) := by
  have hb : ∀ κ, quotHomNorm (quotHomInverse ((u.conjQuad T).f00 κ)) =
      quotHomNorm (quotHomInverse (T.f00 κ)) := by
    intro κ
    show quotHomNorm (quotHomInverse (u.conjHom (T.f00 κ))) = _
    rw [quotHomInverse_conjHom, quotHomNorm_conjHom]
  refine ⟨u.isJet_conjQuad h.isJet, fun κ hκ => (u.isUnit_conjHom _).2 (h.isUnit_f00 κ hκ), ?_⟩
  simpa only [hb] using h.bdd_inverse
variable {F : PeriodicData}
def pullback (T : (F.Carrier → ℂ) → B.Carrier → B.Carrier → ℂ) :
    (F.Carrier → ℂ) → A.Carrier → A.Carrier → ℂ :=
  fun ζ x' x => T ζ (u.toEquiv x') (u.toEquiv x)
theorem isLocalWith_pullback_iff (T : (F.Carrier → ℂ) → B.Carrier → B.Carrier → ℂ) (ρ R : ℝ) :
    IsLocalWith F A A (u.pullback T) ρ R ↔ IsLocalWith F B B T ρ R := by
  constructor
  · intro h
    refine ⟨h.radius_pos, fun ζ hζ y' y hn => ?_, fun y' y => ?_, fun ζ hζ n y' y => ?_⟩
    · obtain ⟨x', rfl⟩ := u.toEquiv.surjective y'
      obtain ⟨x, rfl⟩ := u.toEquiv.surjective y
      rw [u.map_pos, u.map_pos] at hn
      exact h.vanish_far ζ hζ x' x hn
    · obtain ⟨x', rfl⟩ := u.toEquiv.surjective y'
      obtain ⟨x, rfl⟩ := u.toEquiv.surjective y
      rw [u.map_pos]
      exact h.holo_entry x' x
    · obtain ⟨x', rfl⟩ := u.toEquiv.surjective y'
      obtain ⟨x, rfl⟩ := u.toEquiv.surjective y
      rw [← u.map_translate, ← u.map_translate]
      exact h.shift_covariant ζ hζ n x' x
  · intro h
    refine ⟨h.radius_pos, fun ζ hζ x' x hn => ?_, fun x' x => ?_, fun ζ hζ n x' x => ?_⟩
    · rw [← u.map_pos x, ← u.map_pos x'] at hn
      exact h.vanish_far ζ hζ _ _ hn
    · rw [← u.map_pos x']
      exact h.holo_entry (u.toEquiv x') (u.toEquiv x)
    · show T (shiftField F n ζ) (u.toEquiv (A.translate n x')) (u.toEquiv (A.translate n x)) =
        T ζ (u.toEquiv x') (u.toEquiv x)
      rw [u.map_translate, u.map_translate]
      exact h.shift_covariant ζ hζ n _ _
theorem coeffOne_pullback (T : (F.Carrier → ℂ) → B.Carrier → B.Carrier → ℂ) (ζ : F.Carrier → ℂ)
    (x' x : A.Carrier) :
    coeffOne F A A (u.pullback T) ζ x' x =
      coeffOne F B B T ζ (u.toEquiv x') (u.toEquiv x) := by
  unfold coeffOne
  congr 1
  funext t
  unfold IsLinearCoeff
  rw [u.map_pos]
  apply propext
  constructor
  · intro h ρ R hm l e φ β hx
    exact h ρ R ((u.isLocalWith_pullback_iff T ρ R).2 hm) l e φ β hx
  · intro h ρ R hm l e φ β hx
    exact h ρ R ((u.isLocalWith_pullback_iff T ρ R).1 hm) l e φ β hx
theorem coeffTwo_pullback (T : (F.Carrier → ℂ) → B.Carrier → B.Carrier → ℂ)
    (ζ ζ' : F.Carrier → ℂ) (x' x : A.Carrier) :
    coeffTwo F A A (u.pullback T) ζ ζ' x' x =
      coeffTwo F B B T ζ ζ' (u.toEquiv x') (u.toEquiv x) := by
  unfold coeffTwo
  congr 1
  funext t
  unfold IsBilinearCoeff
  rw [u.map_pos]
  apply propext
  constructor
  · intro h ρ R hm l e φ β hx
    exact h ρ R ((u.isLocalWith_pullback_iff T ρ R).2 hm) l e φ β hx
  · intro h ρ R hm l e φ β hx
    exact h ρ R ((u.isLocalWith_pullback_iff T ρ R).1 hm) l e φ β hx
theorem blochWave_apply_equiv (κ : Fin 4 → ℂ) (φ : B.UnitQuot → ℂ) (x : A.Carrier) :
    blochWave B κ φ (u.toEquiv x) = blochWave A κ (φ ∘ u.quotMap) x := by
  unfold blochWave
  rw [u.map_pos]
  rfl
theorem applyKernel_blochWave_equiv (K : B.Carrier → B.Carrier → ℂ) (κ : Fin 4 → ℂ)
    (φ : B.UnitQuot → ℂ) (x' : A.Carrier) :
    applyKernel K (blochWave B κ φ) (u.toEquiv x') =
      applyKernel (fun y' y => K (u.toEquiv y') (u.toEquiv y))
        (blochWave A κ (φ ∘ u.quotMap)) x' := by
  unfold applyKernel
  rw [← u.toEquiv.tsum_eq]
  refine tsum_congr fun y => ?_
  rw [blochWave_apply_equiv]
theorem fourierSymbol_apply_equiv (K : B.Carrier → B.Carrier → ℂ) (κ : Fin 4 → ℂ)
    (x' x : A.Carrier) :
    fourierSymbol B B K κ (u.toEquiv x') (u.toEquiv x) =
      fourierSymbol A A (fun y' y => K (u.toEquiv y') (u.toEquiv y)) κ x' x := by
  unfold fourierSymbol
  refine tsum_congr fun n => ?_
  unfold symbolSummand
  rw [← u.map_translate, u.map_pos, u.map_pos]
theorem descendMatrix_eq_pullback (Y : B.Carrier → B.Carrier → ℂ) (c' c : B.UnitQuot) :
    descendMatrix B B 1 Y c' c =
      descendMatrix A A 1 (fun y' y => Y (u.toEquiv y') (u.toEquiv y))
        (u.quotInv c') (u.quotInv c) := by
  unfold descendMatrix
  congr 1
  funext z
  apply propext
  constructor
  · intro h x' x h' hx
    refine h _ _ ?_ ?_
    · rw [← u.quotMap_quotInv c', ← h']
      rfl
    · rw [← u.quotMap_quotInv c, ← hx]
      rfl
  · intro h y' y h' hy
    obtain ⟨x', rfl⟩ := u.toEquiv.surjective y'
    obtain ⟨x, rfl⟩ := u.toEquiv.surjective y
    refine h x' x ?_ ?_
    · rw [← h', quotInv_mkQuot]
    · rw [← hy, quotInv_mkQuot]
theorem blochWave_conjHom (M : QuotHom A A) (κ : Fin 4 → ℂ) (φ : B.UnitQuot → ℂ)
    (x' : A.Carrier) :
    blochWave B κ (u.conjHom M φ) (u.toEquiv x') = blochWave A κ (M (φ ∘ u.quotMap)) x' := by
  rw [blochWave_apply_equiv]
  congr 1
  funext c
  simp only [Function.comp_apply, conjHom_apply, quotInv_quotMap]
theorem isActionTriple_conjQuad (T : (F.Carrier → ℂ) → B.Carrier → B.Carrier → ℂ)
    (p : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ)
    (M : ((Fin 4 → ℂ) → QuotHom A A) × ((Fin 4 → ℂ) → QuotHom A A) ×
      ((Fin 4 → ℂ) → QuotHom A A))
    (hM : IsActionTriple F A A (u.pullback T) p εPlus εMinus M) :
    IsActionTriple F B B T p εPlus εMinus
      (fun κ => u.conjHom (M.1 κ), fun κ => u.conjHom (M.2.1 κ),
        fun κ => u.conjHom (M.2.2 κ)) := by
  intro κ φ y'
  obtain ⟨x', rfl⟩ := u.toEquiv.surjective y'
  obtain ⟨h1, h2, h3⟩ := hM κ (φ ∘ u.quotMap) x'
  have hf : ∀ ζ, (fun y' y => coeffOne F B B T ζ (u.toEquiv y') (u.toEquiv y)) =
      coeffOne F A A (u.pullback T) ζ := fun ζ => by
    funext y' y
    exact (u.coeffOne_pullback T ζ y' y).symm
  have hs : ∀ ζ ζ', (fun y' y => coeffTwo F B B T ζ ζ' (u.toEquiv y') (u.toEquiv y)) =
      coeffTwo F A A (u.pullback T) ζ ζ' := fun ζ ζ' => by
    funext y' y
    exact (u.coeffTwo_pullback T ζ ζ' y' y).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [applyKernel_blochWave_equiv, hf, h1]
    exact (u.blochWave_conjHom _ _ _ _).symm
  · rw [applyKernel_blochWave_equiv, hf, h2]
    exact (u.blochWave_conjHom _ _ _ _).symm
  · rw [applyKernel_blochWave_equiv, hs, h3]
    exact (u.blochWave_conjHom _ _ _ _).symm
theorem jetAlong_eq_conjQuad (hjets : LocalOpFunTriple.Claim)
    (hF : IsPeriodic F) (hA : IsPeriodic A) (hB : IsPeriodic B)
    (T : (F.Carrier → ℂ) → B.Carrier → B.Carrier → ℂ) (hT : IsLocalOpFun F B B T)
    (p : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ) :
    jetAlong F B B T p εPlus εMinus = u.conjQuad (jetAlong F A A (u.pullback T) p εPlus εMinus) := by
  have : Finite A.UnitQuot := hA.finite_quot
  have : Finite B.UnitQuot := hB.finite_quot
  have hlocal : IsLocalOpFun F A A (u.pullback T) := by
    obtain ⟨ρ, R, h⟩ := hT
    exact ⟨ρ, R, (u.isLocalWith_pullback_iff T ρ R).2 h⟩
  have hset := (hjets F A A hF hA hA _ hlocal).1 p εPlus εMinus
  have hset' := (hjets F B B hF hB hB T hT).1 p εPlus εMinus
  have hspec := Classical.epsilon_spec hset.exists
  have hspec' := Classical.epsilon_spec hset'.exists
  have heq := hset'.unique hspec' (u.isActionTriple_conjQuad T p εPlus εMinus _ hspec)
  refine JetQuad.ext ?_ ?_ ?_ ?_
  · funext κ
    apply linearMapEntry_injective
    funext c' c
    show linearMapEntry (symbolHom B B (coeffZero F B B T) κ) c' c =
      linearMapEntry (u.conjHom (symbolHom A A (coeffZero F A A (u.pullback T)) κ)) c' c
    rw [linearMapEntry_conjHom]
    have h1 : linearMapEntry (symbolHom B B (coeffZero F B B T) κ) =
        descendMatrix B B 1 (fourierSymbol B B (coeffZero F B B T) κ) :=
      linearMapEntry_linearMapOfEntries _
    have h2 : linearMapEntry (symbolHom A A (coeffZero F A A (u.pullback T)) κ) =
        descendMatrix A A 1 (fourierSymbol A A (coeffZero F A A (u.pullback T)) κ) :=
      linearMapEntry_linearMapOfEntries _
    rw [h1, h2, u.descendMatrix_eq_pullback]
    congr 1
    funext x' x
    exact u.fourierSymbol_apply_equiv _ κ x' x
  · exact congrArg Prod.fst heq
  · exact congrArg (fun M => M.2.1) heq
  · exact congrArg (fun M => M.2.2) heq
end PeriodicIso
section Pair
variable (I₁ I₂ : PeriodicData)
def sigmaPairIso : PeriodicIso (PeriodicData.sigma (pairData I₁ I₂)) (I₁.disjSum I₂) where
  toEquiv :=
    { toFun := sumIndexOfSigma
      invFun := fun x => match x with
        | .inl x => ⟨0, x⟩
        | .inr x => ⟨1, x⟩
      left_inv := fun x => match x with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
      right_inv := fun x => match x with
        | .inl _ => rfl
        | .inr _ => rfl }
  map_translate := fun _ x => match x with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  map_pos := fun x => match x with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  map_weight := fun x => match x with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
variable {I₁ I₂}
theorem isPeriodic_sigma_pairData (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂) :
    IsPeriodic (PeriodicData.sigma (pairData I₁ I₂)) :=
  IsPeriodic.sigma fun b => match b with
    | 0 => h₁
    | 1 => h₂
theorem isPeriodic_disjSum (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂) :
    IsPeriodic (I₁.disjSum I₂) where
  translate_zero := fun x => match x with
    | .inl x => congrArg Sum.inl (h₁.translate_zero x)
    | .inr x => congrArg Sum.inr (h₂.translate_zero x)
  translate_add := fun m n x => match x with
    | .inl x => congrArg Sum.inl (h₁.translate_add m n x)
    | .inr x => congrArg Sum.inr (h₂.translate_add m n x)
  free := fun n x e => match x, e with
    | .inl x, e => h₁.free n x (Sum.inl_injective e)
    | .inr x, e => h₂.free n x (Sum.inr_injective e)
  finite_quot := by
    have := (isPeriodic_sigma_pairData h₁ h₂).finite_quot
    exact Finite.of_equiv _ (sigmaPairIso I₁ I₂).quotEquiv
  pos_translate := fun n x => match x with
    | .inl x => h₁.pos_translate n x
    | .inr x => h₂.pos_translate n x
  finite_components := by
    have := h₁.finite_components
    have := h₂.finite_components
    exact inferInstanceAs (Finite (I₁.Component ⊕ I₂.Component))
  componentOf_translate := fun n x => match x with
    | .inl x => congrArg Sum.inl (h₁.componentOf_translate n x)
    | .inr x => congrArg Sum.inr (h₂.componentOf_translate n x)
  weight_pos := fun q => match q with
    | .inl q => h₁.weight_pos q
    | .inr q => h₂.weight_pos q
end Pair
theorem claim_holds (hjets : LocalOpFunTriple.Claim) : Claim := by
  intro F I₁ I₂ hF h₁ h₂
  have hS := isPeriodic_disjSum h₁ h₂
  have hU := isPeriodic_sigma_pairData h₁ h₂
  refine ⟨hS, fun T hT => ?_⟩
  have hloc : IsLocalOpFun F (I₁.disjSum I₂) (I₁.disjSum I₂) T := by
    obtain ⟨ρ, R, h⟩ := hT
    exact ⟨ρ, R, ((sigmaPairIso I₁ I₂).isLocalWith_pullback_iff T ρ R).1 h⟩
  refine ⟨hloc, fun δ p εPlus εMinus _ _ hinv => ?_⟩
  have := hU.finite_quot
  have hj := (sigmaPairIso I₁ I₂).jetAlong_eq_conjQuad hjets hF hU hS T hloc p εPlus εMinus
  have hread : (sigmaPairIso I₁ I₂).pullback T = readOnSigma T := rfl
  rw [hread] at hj
  rw [hj]
  exact ⟨(sigmaPairIso I₁ I₂).isInvertibleJet_conjQuad hinv,
    (sigmaPairIso I₁ I₂).logNumber_conjQuad p _⟩
end YangMills.Construction.PeriodicOperators.DisjSumJets
end
