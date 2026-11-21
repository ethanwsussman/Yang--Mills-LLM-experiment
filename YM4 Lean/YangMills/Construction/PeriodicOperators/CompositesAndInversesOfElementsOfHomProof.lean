import YangMills.Construction.PeriodicOperators.CompositesAndInversesOfElementsOfHom
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHomProof
import YangMills.Construction.PeriodicOperators.TranslationsOfTheSymbolProof
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CompInv
open YangMills.Construction.PeriodicOperators.Quotients (conjKernel)
open YangMills.Construction.LocalKernels (CellType Cell)
section Entries
variable {J J' J'' : Type}
open Classical in
theorem linearMapEntry_injective [Finite J] {M N : (J → ℂ) →ₗ[ℂ] (J' → ℂ)}
    (h : linearMapEntry M = linearMapEntry N) : M = N := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMap_ext_of_entry <;> assumption
open Classical in
theorem apply_eq_sum_entry [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (f : J → ℂ) (c' : J') :
    M f c' = ∑ c, linearMapEntry M c' c * f c := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.apply_eq_sum_linearMapEntry <;> assumption
def barMap (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) : (J → ℂ) →ₗ[ℂ] (J' → ℂ) where
  toFun f c' := conj (M (fun c => conj (f c)) c')
  map_add' f g := by
    funext c'
    have e : (fun c => conj ((f + g) c)) = (fun c => conj (f c)) + fun c => conj (g c) := by
      funext c
      simp
    change conj (M (fun c => conj ((f + g) c)) c') = _
    rw [e, map_add]
    simp
  map_smul' z f := by
    funext c'
    have e : (fun c => conj ((z • f) c)) = conj z • fun c => conj (f c) := by
      funext c
      simp
    change conj (M (fun c => conj ((z • f) c)) c') = z * conj (M (fun c => conj (f c)) c')
    rw [e, map_smul]
    simp
theorem barMap_apply (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (f : J → ℂ) (c' : J') :
    barMap M f c' = conj (M (fun c => conj (f c)) c') := rfl
open Classical in
theorem linearMapEntry_barMap (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) :
    linearMapEntry (barMap M) = conjKernel (linearMapEntry M) := by
  funext c' c
  have e : (fun d => conj ((Pi.single c 1 : J → ℂ) d)) = Pi.single c 1 := by
    funext d
    by_cases h : d = c
    · subst h
      simp
    · simp [h]
  simp only [linearMapEntry, conjKernel, barMap_apply, e]
theorem linearMapOfEntries_conjKernel [Finite J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) :
    linearMapOfEntries (conjKernel (linearMapEntry M)) = barMap M := by
  have hs : linearMapEntry (linearMapOfEntries (conjKernel (linearMapEntry M))) =
      conjKernel (linearMapEntry M) :=
    Classical.epsilon_spec (p := fun N => linearMapEntry N = conjKernel (linearMapEntry M))
      ⟨barMap M, linearMapEntry_barMap M⟩
  exact linearMapEntry_injective (hs.trans (linearMapEntry_barMap M).symm)
theorem barMap_comp (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (M' : (J'' → ℂ) →ₗ[ℂ] (J → ℂ)) :
    barMap (M.comp M') = (barMap M).comp (barMap M') := by
  refine LinearMap.ext fun f => ?_
  funext c'
  simp only [barMap_apply, LinearMap.comp_apply, Complex.conj_conj]
theorem barMap_id : barMap (LinearMap.id : (J → ℂ) →ₗ[ℂ] (J → ℂ)) = LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  funext c'
  simp [barMap_apply]
end Entries
section Invertible
variable {I I' I'' : PeriodicData}
theorem isInvertibleQuotHom_iff_isUnit (M : QuotHom I I) :
    IsInvertibleQuotHom M ↔ IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ)) := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.isInvertibleQuotHom_iff_isUnit <;> assumption
theorem comp_quotHomInverse {M : QuotHom I I} (h : IsInvertibleQuotHom M) :
    M.comp (quotHomInverse M) = LinearMap.id :=
  Ring.mul_inverse_cancel (M : Module.End ℂ (I.UnitQuot → ℂ)) ((isInvertibleQuotHom_iff_isUnit M).1 h)
theorem quotHomInverse_comp {M : QuotHom I I} (h : IsInvertibleQuotHom M) :
    (quotHomInverse M).comp M = LinearMap.id :=
  Ring.inverse_mul_cancel (M : Module.End ℂ (I.UnitQuot → ℂ)) ((isInvertibleQuotHom_iff_isUnit M).1 h)
theorem isInvertible_of_two_sided {A B : QuotHom I I} (h₁ : A.comp B = LinearMap.id)
    (h₂ : B.comp A = LinearMap.id) : IsInvertibleQuotHom A ∧ quotHomInverse A = B := by
  let u : (Module.End ℂ (I.UnitQuot → ℂ))ˣ := ⟨A, B, h₁, h₂⟩
  exact ⟨(isInvertibleQuotHom_iff_isUnit A).2 u.isUnit, Ring.inverse_unit u⟩
theorem quotHomInverse_commute {M : QuotHom I I} (h : IsInvertibleQuotHom M) {A : QuotHom I I}
    (hA : M.comp A = A.comp M) : (quotHomInverse M).comp A = A.comp (quotHomInverse M) := by
  obtain ⟨u, hu⟩ := (isInvertibleQuotHom_iff_isUnit M).1 h
  have hc : Commute (u : Module.End ℂ (I.UnitQuot → ℂ)) (A : Module.End ℂ (I.UnitQuot → ℂ)) := by
    rw [hu]
    exact hA
  have e : quotHomInverse M = ((u⁻¹ : (Module.End ℂ (I.UnitQuot → ℂ))ˣ) :
      Module.End ℂ (I.UnitQuot → ℂ)) := by
    rw [quotHomInverse, ← hu]
    exact Ring.inverse_unit u
  rw [e]
  exact hc.units_inv_left.eq
end Invertible
section Bar
variable {I I' I'' : PeriodicData}
theorem conjQuotHom_eq_barMap (hI : IsPeriodic I) (M : QuotHom I I') :
    conjQuotHom M = barMap M := by
  have := hI.finite_quot
  exact linearMapOfEntries_conjKernel M
theorem conjCompInv_holds (hI : IsPeriodic I) (hI'' : IsPeriodic I'') :
    ConjCompInv I I' I'' := by
  refine ⟨fun M M' => ?_, fun M h => ?_⟩
  · rw [conjQuotHom_eq_barMap hI'', conjQuotHom_eq_barMap hI, conjQuotHom_eq_barMap hI'',
      barMap_comp]
  · rw [conjQuotHom_eq_barMap hI, conjQuotHom_eq_barMap hI]
    exact isInvertible_of_two_sided
      (by rw [← barMap_comp, comp_quotHomInverse h, barMap_id])
      (by rw [← barMap_comp, quotHomInverse_comp h, barMap_id])
end Bar
section Phases
variable {I I' I'' : PeriodicData}
theorem phaseOn_ne_zero (hI : IsPeriodic I) (e : Fin 4 → ℤ) (c : I.UnitQuot) :
    phaseOn I e c ≠ 0 := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolTranslation.phaseOn_ne_zero <;> assumption
theorem phaseMul_isInvertible (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    IsInvertibleQuotHom (phaseMul I e : QuotHom I I) := by
  intro g
  refine ⟨fun c => (phaseOn I e c)⁻¹ * g c, ?_, fun f hf => ?_⟩
  · funext c
    exact mul_inv_cancel_left₀ (phaseOn_ne_zero hI e c) (g c)
  · funext c
    have h := congrFun hf c
    change phaseOn I e c * f c = g c at h
    rw [← h]
    exact (inv_mul_cancel_left₀ (phaseOn_ne_zero hI e c) (f c)).symm
theorem phaseConj_comp (hI : IsPeriodic I) (e : Fin 4 → ℤ) (M : QuotHom I I')
    (M' : QuotHom I'' I) :
    (phaseConj e M).comp (phaseConj e M') = phaseConj e (M.comp M') := by
  refine LinearMap.ext fun f => ?_
  simp only [phaseConj, LinearMap.comp_apply]
  rw [(phaseMul_isInvertible hI e).apply_quotHomInverse]
theorem phaseConj_id (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    phaseConj e (LinearMap.id : QuotHom I I) = LinearMap.id := by
  simpa [phaseConj] using quotHomInverse_comp (phaseMul_isInvertible hI e)
theorem phaseCompInv_holds (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hI'' : IsPeriodic I'') : PhaseCompInv I I' I'' := by
  intro e
  refine ⟨phaseMul_isInvertible hI e, phaseMul_isInvertible hI' e, phaseMul_isInvertible hI'' e,
    fun M M' => phaseConj_comp hI e M M', fun M h => ?_⟩
  exact isInvertible_of_two_sided
    (by rw [phaseConj_comp hI, comp_quotHomInverse h, phaseConj_id hI])
    (by rw [phaseConj_comp hI, quotHomInverse_comp h, phaseConj_id hI])
end Phases
section Families
variable {I I' I'' : PeriodicData}
theorem familyInv_holds (hI : IsPeriodic I) : FamilyInv I := by
  intro D M hD hM
  have key : ∀ κ ∈ unitPoints D M,
      (IsInvertibleQuotHom (M (negConjPoint κ)) ∧
        conjQuotHom (quotHomInverse (M κ)) = quotHomInverse (M (negConjPoint κ))) ∧
      ∀ e : Fin 4 → ℤ, IsInvertibleQuotHom (M (addTwoPiInt κ e)) ∧
        quotHomInverse (M (addTwoPiInt κ e)) = phaseConj e (quotHomInverse (M κ)) := by
    rintro κ ⟨hκ, hi⟩
    obtain ⟨h₁, h₂⟩ := hM κ hκ
    refine ⟨?_, fun e => ?_⟩
    · have h := (conjCompInv_holds (I' := I) hI hI).2 (M κ) hi
      rw [h₁] at h
      exact ⟨h.1, h.2.symm⟩
    · have h := ((phaseCompInv_holds hI hI hI e).2.2.2.2 (M κ) hi)
      rw [← h₂ e] at h
      exact h
  refine ⟨fun κ hκ => ⟨⟨(hD κ hκ.1).1, (key κ hκ).1.1⟩, fun e => ⟨(hD κ hκ.1).2 e, ((key κ hκ).2 e).1⟩⟩,
    fun κ hκ => ⟨(key κ hκ).1.2, fun e => ((key κ hκ).2 e).2⟩⟩
theorem familyComp_holds (hI : IsPeriodic I) (hI'' : IsPeriodic I'') :
    FamilyComp I I' I'' := by
  intro D M M' _ hM hM' κ hκ
  refine ⟨?_, fun e => ?_⟩
  · rw [(conjCompInv_holds hI hI'').1, (hM κ hκ).1, (hM' κ hκ).1]
  · rw [(hM κ hκ).2 e, (hM' κ hκ).2 e, phaseConj_comp hI]
end Families
structure ColourClasses (C σ : Type) where
  cls : Fin 3 × σ → C
  cls_surjective : Function.Surjective cls
  colour : C → Fin 3
  colour_cls : ∀ a x, colour (cls (a, x)) = a
  relabel : Equiv.Perm (Fin 3) → C → C
  relabel_cls : ∀ τ a x, relabel τ (cls (a, x)) = cls (τ a, x)
namespace ColourClasses
variable {C C' C'' σ σ' σ'' : Type}
def relabelEquiv (P : ColourClasses C σ) (τ : Equiv.Perm (Fin 3)) : C ≃ C where
  toFun := P.relabel τ
  invFun := P.relabel τ⁻¹
  left_inv c := by
    obtain ⟨⟨a, x⟩, rfl⟩ := P.cls_surjective c
    simp [P.relabel_cls]
  right_inv c := by
    obtain ⟨⟨a, x⟩, rfl⟩ := P.cls_surjective c
    simp [P.relabel_cls]
def restrict (P : ColourClasses C σ) (a : Fin 3) : (C → ℂ) →ₗ[ℂ] (C → ℂ) where
  toFun f c := if P.colour c = a then f c else 0
  map_add' f g := by
    funext c
    by_cases h : P.colour c = a <;> simp [h]
  map_smul' z f := by
    funext c
    by_cases h : P.colour c = a <;> simp [h]
theorem restrict_apply (P : ColourClasses C σ) (a : Fin 3) (f : C → ℂ) (c : C) :
    P.restrict a f c = if P.colour c = a then f c else 0 := rfl
def permLin (P : ColourClasses C σ) (τ : Equiv.Perm (Fin 3)) : (C → ℂ) →ₗ[ℂ] (C → ℂ) :=
  LinearMap.funLeft ℂ ℂ (P.relabel τ)
theorem permLin_apply (P : ColourClasses C σ) (τ : Equiv.Perm (Fin 3)) (f : C → ℂ) (c : C) :
    P.permLin τ f c = f (P.relabel τ c) := rfl
def IsEquivariant (P : ColourClasses C σ) (P' : ColourClasses C' σ') (M : (C → ℂ) →ₗ[ℂ] (C' → ℂ)) : Prop :=
  (∀ a, M.comp (P.restrict a) = (P'.restrict a).comp M) ∧ ∀ τ, M.comp (P.permLin τ) = (P'.permLin τ).comp M
theorem IsEquivariant.comp {P : ColourClasses C σ} {P' : ColourClasses C' σ'} {P'' : ColourClasses C'' σ''}
    {M : (C → ℂ) →ₗ[ℂ] (C' → ℂ)} {M' : (C'' → ℂ) →ₗ[ℂ] (C → ℂ)} (h : IsEquivariant P P' M)
    (h' : IsEquivariant P'' P M') : IsEquivariant P'' P' (M.comp M') := by
  refine ⟨fun a => ?_, fun τ => ?_⟩
  · rw [LinearMap.comp_assoc, h'.1, ← LinearMap.comp_assoc, h.1, LinearMap.comp_assoc]
  · rw [LinearMap.comp_assoc, h'.2, ← LinearMap.comp_assoc, h.2, LinearMap.comp_assoc]
open Classical in
theorem isColourTrivialOnClasses_of_isEquivariant {P : ColourClasses C σ} {P' : ColourClasses C' σ'}
    {M : (C → ℂ) →ₗ[ℂ] (C' → ℂ)} (h : IsEquivariant P P' M) :
    Tower.IsColourTrivialOnClasses P.cls P'.cls (linearMapEntry M) := by
  refine ⟨fun a a' y x hne => ?_, fun a a' y x => ?_⟩
  · have hc : P.restrict a (Pi.single (P.cls (a, x)) 1) = Pi.single (P.cls (a, x)) 1 := by
      funext d
      by_cases hd : d = P.cls (a, x)
      · subst hd
        simp [restrict_apply, P.colour_cls]
      · simp [restrict_apply, hd]
    have e := LinearMap.congr_fun (h.1 a) (Pi.single (P.cls (a, x)) 1)
    simp only [LinearMap.comp_apply, hc] at e
    have e' := congrFun e (P'.cls (a', y))
    rw [restrict_apply, P'.colour_cls, if_neg hne] at e'
    exact e'
  · have hτ : P.permLin (Equiv.swap a a') (Pi.single (P.cls (a, x)) 1) =
        Pi.single (P.cls (a', x)) 1 := by
      funext d
      rw [permLin_apply]
      have hiff : P.relabel (Equiv.swap a a') d = P.cls (a, x) ↔ d = P.cls (a', x) := by
        have e₀ : P.cls (a, x) = P.relabelEquiv (Equiv.swap a a') (P.cls (a', x)) := by
          change P.cls (a, x) = P.relabel (Equiv.swap a a') (P.cls (a', x))
          rw [P.relabel_cls, Equiv.swap_apply_right]
        rw [e₀]
        exact (P.relabelEquiv (Equiv.swap a a')).injective.eq_iff
      by_cases hd : d = P.cls (a', x)
      · rw [Pi.single_apply, if_pos (hiff.2 hd), Pi.single_apply, if_pos hd]
      · rw [Pi.single_apply, if_neg (fun e => hd (hiff.1 e)), Pi.single_apply, if_neg hd]
    have e := LinearMap.congr_fun (h.2 (Equiv.swap a a')) (Pi.single (P.cls (a, x)) 1)
    simp only [LinearMap.comp_apply, hτ] at e
    have e' := congrFun e (P'.cls (a', y))
    rw [permLin_apply, P'.relabel_cls, Equiv.swap_apply_right] at e'
    exact e'.symm
theorem isEquivariant_of_isColourTrivialOnClasses [Finite C] {P : ColourClasses C σ}
    {P' : ColourClasses C' σ'} {M : (C → ℂ) →ₗ[ℂ] (C' → ℂ)}
    (h : Tower.IsColourTrivialOnClasses P.cls P'.cls (linearMapEntry M)) :
    IsEquivariant P P' M := by
  have := Fintype.ofFinite C
  obtain ⟨h₀, h₁⟩ := h
  have hz : ∀ c' c, P'.colour c' ≠ P.colour c → linearMapEntry M c' c = 0 := by
    intro c' c hne
    obtain ⟨⟨a', y⟩, rfl⟩ := P'.cls_surjective c'
    obtain ⟨⟨a, x⟩, rfl⟩ := P.cls_surjective c
    rw [P'.colour_cls, P.colour_cls] at hne
    exact h₀ a a' y x hne
  have hp : ∀ τ c' c, linearMapEntry M (P'.relabel τ c') (P.relabel τ c) = linearMapEntry M c' c := by
    intro τ c' c
    obtain ⟨⟨a', y⟩, rfl⟩ := P'.cls_surjective c'
    obtain ⟨⟨a, x⟩, rfl⟩ := P.cls_surjective c
    rw [P'.relabel_cls, P.relabel_cls]
    by_cases ha : a' = a
    · subst ha
      exact h₁ (τ a') a' y x
    · have e₁ : linearMapEntry M (P'.cls (a', y)) (P.cls (a, x)) = 0 := h₀ a a' y x ha
      rw [e₁]
      exact h₀ (τ a) (τ a') y x fun e => ha (τ.injective e)
  refine ⟨fun a => ?_, fun τ => ?_⟩
  · refine LinearMap.ext fun f => ?_
    funext c'
    simp only [LinearMap.comp_apply]
    rw [restrict_apply, apply_eq_sum_entry]
    by_cases hc : P'.colour c' = a
    · rw [if_pos hc, apply_eq_sum_entry]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [restrict_apply]
      by_cases hd : P.colour c = a
      · rw [if_pos hd]
      · rw [if_neg hd, hz c' c (fun e => hd (e.symm.trans hc))]
        simp
    · rw [if_neg hc]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [restrict_apply]
      by_cases hd : P.colour c = a
      · rw [hz c' c (fun e => hc (e.trans hd))]
        simp
      · rw [if_neg hd]
        simp
  · refine LinearMap.ext fun f => ?_
    funext c'
    simp only [LinearMap.comp_apply]
    rw [permLin_apply, apply_eq_sum_entry, apply_eq_sum_entry,
      ← (P.relabelEquiv τ).sum_comp (fun c => linearMapEntry M (P'.relabel τ c') c * f c)]
    refine Finset.sum_congr rfl fun c _ => ?_
    change linearMapEntry M c' c * f (P.relabel τ c) =
      linearMapEntry M (P'.relabel τ c') (P.relabel τ c) * f (P.relabel τ c)
    rw [hp]
end ColourClasses
section Tower
variable {σ : Type}
def colourClassesOfPairs (sh : (Fin 4 → ℤ) → σ → σ) (pos : Fin 3 × σ → InfiniteLattice.AmbientSpace)
    (w : ℝ) :
    ColourClasses (PeriodicData.ofSingle (Fin 3 × σ) (fun n ι => (ι.1, sh n ι.2)) pos w).UnitQuot σ where
  cls := (PeriodicData.ofSingle (Fin 3 × σ) (fun n ι => (ι.1, sh n ι.2)) pos w).mkQuot 1
  cls_surjective := fun c => by
    induction c using Quot.ind with
    | mk ι => exact ⟨ι, rfl⟩
  colour := Quot.lift (fun ι => ι.1) (by
    rintro _ _ ⟨n, rfl⟩
    rfl)
  colour_cls := fun _ _ => rfl
  relabel := fun τ => Quot.map (fun ι => (τ ι.1, ι.2)) (by
    rintro _ _ ⟨n, rfl⟩
    exact ⟨n, rfl⟩)
  relabel_cls := fun _ _ _ => rfl
def towerColourClasses (L k j : ℕ) : ∀ c : CellType, ColourClasses (colourCells L k j c).UnitQuot (Cell L k j c)
  | .vertex => colourClassesOfPairs (fun n x => Tower.FullSpace.vertexImage (intShift n) x)
      (colourVertices L k j).pos ((colourVertices L k j).weight ())
  | .edge => colourClassesOfPairs (fun n b => shiftEdge n b)
      (colourEdges L k j).pos ((colourEdges L k j).weight ())
  | .face => colourClassesOfPairs (fun n p => shiftFace n p)
      (colourFaces L k j).pos ((colourFaces L k j).weight ())
theorem towerColourClasses_cls (L k j : ℕ) (c : CellType) :
    (towerColourClasses L k j c).cls = colourCellQuot L k j c := by
  cases c <;> rfl
theorem colourCells_isPeriodic (hT : TowerIndexSets.Claim) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {k j : ℕ} (hj : j ≤ k) (c : CellType) :
    IsPeriodic (colourCells L k j c) := by
  have h := hT L hL k j hj
  cases c
  · exact h.1
  · exact h.2.1
  · exact h.2.2
variable {L k j j' j'' : ℕ} {c c' c'' : CellType}
theorem isColourTrivial_iff_isEquivariant (hj : Finite (colourCells L k j c).UnitQuot)
    (M : QuotHom (colourCells L k j c) (colourCells L k j' c')) :
    IsColourTrivial M ↔
      ColourClasses.IsEquivariant (towerColourClasses L k j c) (towerColourClasses L k j' c') M := by
  unfold IsColourTrivial
  rw [← towerColourClasses_cls, ← towerColourClasses_cls]
  exact ⟨ColourClasses.isEquivariant_of_isColourTrivialOnClasses,
    ColourClasses.isColourTrivialOnClasses_of_isEquivariant⟩
theorem colourCompInv_holds (hf : Finite (colourCells L k j c).UnitQuot)
    (hf' : Finite (colourCells L k j'' c'').UnitQuot) :
    ColourCompInv L k j j' j'' c c' c'' := by
  refine ⟨fun M M' hM hM' => ?_, fun M hi hM => ?_⟩
  · exact (isColourTrivial_iff_isEquivariant hf' _).2
      (((isColourTrivial_iff_isEquivariant hf _).1 hM).comp
        ((isColourTrivial_iff_isEquivariant hf' _).1 hM'))
  · have h := (isColourTrivial_iff_isEquivariant hf _).1 hM
    exact (isColourTrivial_iff_isEquivariant hf _).2
      ⟨fun a => quotHomInverse_commute hi (h.1 a), fun τ => quotHomInverse_commute hi (h.2 τ)⟩
theorem colourFamilies_holds (hf : Finite (colourCells L k j c).UnitQuot)
    (hf' : Finite (colourCells L k j'' c'').UnitQuot) :
    ColourFamilies L k j j' j'' c c' c'' := by
  refine ⟨fun D M _ _ hM κ hκ => ?_, fun D M M' _ _ _ hM hM' κ hκ => ?_⟩
  · exact (colourCompInv_holds (j' := j) (c' := c) (j'' := j) (c'' := c) hf hf).2 (M κ) hκ.2 (hM κ hκ)
  · exact (colourCompInv_holds hf hf').1 (M κ) (M' κ) (hM κ hκ) (hM' κ hκ)
end Tower
theorem negConjPoint_mem {κ : Fin 4 → ℂ} {S : Set (Fin 4 → ℂ)} (hS : IsImStrip S) (h : κ ∈ S) :
    negConjPoint κ ∈ S := by
  have him : ∀ μ, (negConjPoint κ μ).im = (κ μ).im := fun μ => by simp [negConjPoint]
  obtain ⟨ς, _, rfl | rfl⟩ := hS
  · exact fun μ => by rw [him]; exact h μ
  · exact fun μ => by rw [him]; exact h μ
theorem addTwoPiInt_mem {κ : Fin 4 → ℂ} (e : Fin 4 → ℤ) {S : Set (Fin 4 → ℂ)} (hS : IsImStrip S)
    (h : κ ∈ S) : addTwoPiInt κ e ∈ S := by
  have him : ∀ μ, (addTwoPiInt κ e μ).im = (κ μ).im := fun μ => by simp [addTwoPiInt]
  obtain ⟨ς, _, rfl | rfl⟩ := hS
  · exact fun μ => by rw [him]; exact h μ
  · exact fun μ => by rw [him]; exact h μ
theorem claim_holds (hT : TowerIndexSets.Claim) : Claim := by
  refine ⟨fun I I' I'' hI hI' hI'' => ⟨conjCompInv_holds hI hI'', phaseCompInv_holds hI hI' hI'',
      familyInv_holds hI, familyComp_holds hI hI''⟩,
    fun L hL k _ j j' j'' hj _ hj'' c c' c'' => ?_,
    fun κ e S hS h => ⟨negConjPoint_mem hS h, addTwoPiInt_mem e hS h⟩⟩
  have hf := (colourCells_isPeriodic hT hL hj c).finite_quot
  have hf' := (colourCells_isPeriodic hT hL hj'' c'').finite_quot
  exact ⟨colourCompInv_holds hf hf', colourFamilies_holds hf hf'⟩
end YangMills.Construction.PeriodicOperators.CompInv
end
