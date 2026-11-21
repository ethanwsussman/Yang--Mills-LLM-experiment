import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.GrowingTori.MultilinearityOnADomainThatIsNotLinear
import YangMills.Construction.GrowingTori.SubFamiliesNeighbourhoodsAndTheSeparation
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriLimits.NonlinearDomain
theorem posSeparated_of_isCompact {A B : Set (Fin 4 → ℝ)} (hA : IsCompact A)
    (hB : IsCompact B) (hAB : Disjoint A B) : PosSeparated A B := by
  obtain ⟨δ, hδ, hd⟩ := hAB.exists_thickenings hA hB.isClosed
  have hle : ENNReal.ofReal δ ≤ infDist A B := by
    refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal ?_
    by_contra hlt
    refine Set.disjoint_left.1 hd
      (Metric.mem_thickening_iff.2 ⟨x, hx, ?_⟩) (Metric.self_subset_thickening hδ B hy)
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (SeparatedTuplesR4.norm_le_euclidNormVec _) (not_le.1 hlt)
  intro h0
  rw [h0] at hle
  exact absurd (ENNReal.ofReal_pos.2 hδ) (not_lt.2 hle)
namespace ClassMembers
variable {s : Conventions.StandingParameters}
theorem mem_componentSubmodule (K : TestTupleClass) {n : ℕ} {h : Fin n → RealFn}
    (hh : h ∈ K.members s n) (i : Fin n) {A : Set (Fin 4 → ℝ)} (hA : fnSupport (h i) ⊆ A) :
    h i ∈ K.entrySubmodule s A := by
  cases K with
  | sep =>
    obtain ⟨h₁, h₂, -⟩ := (mem_sepTuplesR4_iff s h).1 hh
    exact (mem_c1SuppIn_iff s A (h i)).2 ⟨h₁ i, h₂ i, hA⟩
  | ball ρ hρ => exact ⟨hh.1.1 i, hh.1.2.1 i, hA⟩
theorem fnSupport_subset_region (K : TestTupleClass) {n : ℕ} {h : Fin n → RealFn}
    (hh : h ∈ K.members s n) (i : Fin n) : fnSupport (h i) ⊆ K.region := by
  cases K with
  | sep => exact subset_univ _
  | ball ρ hρ => exact hh.2 i
theorem exists_common_regions (K : TestTupleClass) {n : ℕ} {h h' : Fin n → RealFn}
    (hh : h ∈ K.members s n) (hh' : h' ∈ K.members s n) (i : Fin n)
    (hag : ∀ l, l ≠ i → h l = h' l) :
    ∃ A : Fin n → Set (Fin 4 → ℝ), (∀ l, A l ⊆ K.region) ∧
      (Pairwise fun l k => PosSeparated (A l) (A k)) ∧
      (∀ l, h l ∈ K.entrySubmodule s (A l)) ∧ ∀ l, h' l ∈ K.entrySubmodule s (A l) := by
  classical
  obtain ⟨-, c, dj⟩ := K.isSepLipTuple_of_mem hh
  obtain ⟨-, c', dj'⟩ := K.isSepLipTuple_of_mem hh'
  let A : Fin n → Set (Fin 4 → ℝ) := fun l =>
    if l = i then fnSupport (h i) ∪ fnSupport (h' i) else fnSupport (h l)
  have hAi : A i = fnSupport (h i) ∪ fnSupport (h' i) := if_pos rfl
  have hAl : ∀ l, l ≠ i → A l = fnSupport (h l) := fun l hl => if_neg hl
  have hcomp : ∀ l, IsCompact (A l) := fun l => by
    by_cases hl : l = i
    · subst hl
      rw [hAi]
      exact (c l).union (c' l)
    · rw [hAl l hl]
      exact c l
  have hdisj : ∀ l k, l ≠ k → Disjoint (A l) (A k) := by
    have key : ∀ k, k ≠ i → Disjoint (A i) (A k) := fun k hk => by
      rw [hAi, hAl k hk]
      refine Disjoint.union_left (dj i k hk.symm) ?_
      rw [hag k hk]
      exact dj' i k hk.symm
    intro l k hlk
    by_cases hl : l = i
    · subst hl
      exact key k hlk.symm
    · by_cases hk : k = i
      · subst hk
        exact (key l hl).symm
      · rw [hAl l hl, hAl k hk]
        exact dj l k hlk
  refine ⟨A, fun l => ?_, fun l k hlk => posSeparated_of_isCompact (hcomp l) (hcomp k)
    (hdisj l k hlk), fun l => mem_componentSubmodule K hh l ?_, fun l => mem_componentSubmodule K hh' l ?_⟩
  · by_cases hl : l = i
    · subst hl
      rw [hAi]
      exact union_subset (fnSupport_subset_region K hh l) (fnSupport_subset_region K hh' l)
    · rw [hAl l hl]
      exact fnSupport_subset_region K hh l
  · by_cases hl : l = i
    · subst hl
      rw [hAi]
      exact subset_union_left
    · rw [hAl l hl]
  · by_cases hl : l = i
    · subst hl
      rw [hAi]
      exact subset_union_right
    · rw [hAl l hl, hag l hl]
theorem update_mem_members (K : TestTupleClass) {n : ℕ} (i : Fin n) {h h' : Fin n → RealFn}
    (hh : h ∈ K.members s n) (hh' : h' ∈ K.members s n) (hag : ∀ l, l ≠ i → h l = h' l)
    (α α' : ℝ) : Function.update h i (α • h i + α' • h' i) ∈ K.members s n := by
  obtain ⟨A, hO, hA, h₁, h₂⟩ := exists_common_regions K hh hh' i hag
  have hx : α • h i + α' • h' i ∈ K.entrySubmodule s (A i) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (h₁ i)) (Submodule.smul_mem _ _ (h₂ i))
  have := K.prod_mem_members s hO hA (fun l => if hl : l = i then ⟨_, hl ▸ hx⟩ else ⟨h l, h₁ l⟩)
  convert this using 1
  funext l
  by_cases hl : l = i
  · subst hl
    simp
  · simp [hl]
end ClassMembers
theorem updateStaysInClass_holds (s : Conventions.StandingParameters) : UpdateStaysInClass s :=
  fun K _ i h h' hag α α' => ClassMembers.update_mem_members K i h.2 h'.2 hag α α'
theorem isClassMultilinear_iff (D : TorusTransport.TransportData) (K : TestTupleClass) {n : ℕ}
    (hn : 1 ≤ n) (Ψ : K.members D.toStandingParameters n → ℝ) :
    IsClassMultilinear D K hn Ψ ↔
      ∀ (i : Fin n) (h h' : K.members D.toStandingParameters n) (hag : ∀ j, j ≠ i → h.1 j = h'.1 j)
        (c c' : ℝ), Ψ ⟨Function.update h.1 i (c • h.1 i + c' • h'.1 i),
          ClassMembers.update_mem_members K i h.2 h'.2 hag c c'⟩ =
          c * Ψ h + c' * Ψ h' := by
  constructor
  · intro H i h h' hag c c'
    exact H i h h' hag c c' _
  · intro H i h h' hag c c' _
    exact H i h h' hag c c'
section Restrictions
variable {n : ℕ} {V : Fin n → Submodule ℝ RealFn}
theorem coe_update_family [inst : DecidableEq (Fin n)] (g : (l : Fin n) → V l) (i : Fin n)
    (x : V i) :
    (fun l => (((@Function.update _ _ inst g i x) l : V l) : RealFn)) =
      Function.update (fun l => (g l : RealFn)) i (x : RealFn) := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp
  · simp [hl]
end Restrictions
theorem multilinearIffOnProducts_holds (D : TorusTransport.TransportData) :
    MultilinearIffOnProducts D := by
  intro K n hn Ψ
  rw [isClassMultilinear_iff]
  constructor
  · intro H A hO hA
    have hadd : ∀ (g g' : (l : Fin n) → K.entrySubmodule D.toStandingParameters (A l)) (i : Fin n),
        (∀ l, l ≠ i → g l = g' l) → ∀ (c c' : ℝ) (x : K.entrySubmodule D.toStandingParameters (A i)),
        (x : RealFn) = c • (g i : RealFn) + c' • (g' i : RealFn) →
        ∀ (hx : Function.update (fun l => (g l : RealFn)) i
            (x : RealFn) ∈ K.members D.toStandingParameters n),
        Ψ ⟨_, hx⟩ = c * Ψ ⟨fun l => (g l : RealFn), K.prod_mem_members _ hO hA g⟩ +
          c' * Ψ ⟨fun l => (g' l : RealFn), K.prod_mem_members _ hO hA g'⟩ := by
      intro g g' i hgg c c' x hxe hx
      have hag : ∀ j, j ≠ i → (g j : RealFn) = (g' j : RealFn) :=
        fun j hj => congrArg _ (hgg j hj)
      have e := H i ⟨_, K.prod_mem_members _ hO hA g⟩ ⟨_, K.prod_mem_members _ hO hA g'⟩ hag c c'
      rw [← e]
      exact congrArg Ψ (Subtype.ext (by simp only [hxe]))
    refine ⟨{ toFun := fun g => Ψ ⟨fun l => (g l : RealFn),
                K.prod_mem_members _ hO hA g⟩
              map_update_add' := ?_
              map_update_smul' := ?_ }, fun g => rfl⟩
    · intro inst g i x y
      obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
      have e := hadd (Function.update g i x) (Function.update g i y) i
        (fun l hl => by simp [hl]) 1 1 (x + y) (by simp)
        (by rw [← coe_update_family]; exact K.prod_mem_members _ hO hA _)
      have t : (⟨fun l => ((Function.update g i (x + y) l :
          K.entrySubmodule D.toStandingParameters (A l)) : RealFn),
          K.prod_mem_members _ hO hA _⟩ : K.members D.toStandingParameters n) =
          ⟨Function.update (fun l => ((Function.update g i x l :
            K.entrySubmodule D.toStandingParameters (A l)) : RealFn)) i
            ((x + y : K.entrySubmodule D.toStandingParameters (A i)) : RealFn),
            by rw [← coe_update_family]; exact K.prod_mem_members _ hO hA _⟩ :=
        Subtype.ext (by
          funext l
          by_cases hl : l = i
          · subst hl
            simp
          · simp [hl])
      simpa [t] using e
    · intro inst g i c x
      obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
      have e := hadd (Function.update g i x) (Function.update g i x) i
        (fun _ _ => rfl) c 0 (c • x) (by simp)
        (by rw [← coe_update_family]; exact K.prod_mem_members _ hO hA _)
      have t : (⟨fun l => ((Function.update g i (c • x) l :
          K.entrySubmodule D.toStandingParameters (A l)) : RealFn),
          K.prod_mem_members _ hO hA _⟩ : K.members D.toStandingParameters n) =
          ⟨Function.update (fun l => ((Function.update g i x l :
            K.entrySubmodule D.toStandingParameters (A l)) : RealFn)) i
            ((c • x : K.entrySubmodule D.toStandingParameters (A i)) : RealFn),
            by rw [← coe_update_family]; exact K.prod_mem_members _ hO hA _⟩ :=
        Subtype.ext (by
          funext l
          by_cases hl : l = i
          · subst hl
            simp
          · simp [hl])
      simpa [t] using e
  · intro H i h h' hag c c'
    obtain ⟨A, hO, hA, h₁, h₂⟩ := ClassMembers.exists_common_regions K h.2 h'.2 i hag
    obtain ⟨Λ, hΛ⟩ := H A hO hA
    let g : (l : Fin n) → K.entrySubmodule D.toStandingParameters (A l) := fun l => ⟨h.1 l, h₁ l⟩
    let g' : (l : Fin n) → K.entrySubmodule D.toStandingParameters (A l) := fun l => ⟨h'.1 l, h₂ l⟩
    have hg : Λ g = Ψ h := hΛ g
    have hg' : Λ g' = Ψ h' := hΛ g'
    have hupd : Function.update g i (g' i) = g' := by
      funext l
      by_cases hl : l = i
      · subst hl
        simp
      · rw [Function.update_of_ne hl]
        exact Subtype.ext (hag l hl)
    have hsum : Λ (Function.update g i (c • g i + c' • g' i)) =
        Ψ ⟨Function.update h.1 i (c • h.1 i + c' • h'.1 i),
          ClassMembers.update_mem_members K i h.2 h'.2 hag c c'⟩ :=
      (hΛ _).trans (congrArg Ψ (Subtype.ext (coe_update_family g i _)))
    rw [← hsum, Λ.map_update_add, Λ.map_update_smul, Λ.map_update_smul, Function.update_eq_self,
      hupd, hg, hg']
    simp
theorem onProductsIffTupleMultilinear_holds (s : Conventions.StandingParameters) :
    OnProductsIffTupleMultilinear s := by
  intro n _ Ψ
  constructor
  · intro H A hA
    exact H A (fun _ => subset_univ _) hA
  · intro H A _ hA
    exact H A hA
theorem eqZeroOfEntryEqZero_holds (D : TorusTransport.TransportData) : EqZeroOfEntryEqZero D := by
  intro K n hn Ψ H h i h0
  have e := (isClassMultilinear_iff D K hn Ψ).1 H i h h (fun _ _ => rfl) 0 0
  have t : (⟨Function.update h.1 i ((0 : ℝ) • h.1 i + (0 : ℝ) • h.1 i),
      ClassMembers.update_mem_members K i h.2 h.2 (fun _ _ => rfl) 0 0⟩ :
      K.members D.toStandingParameters n) = h :=
    Subtype.ext (by
      funext l
      by_cases hl : l = i
      · subst hl
        simp [h0]
      · simp [hl])
  rw [t] at e
  simpa using e
theorem mem_lipSubmodule_iff (L : ℕ) (A : Set (Fin 4 → ℝ)) (f : RealFn) :
    f ∈ (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).lipCompact A ↔
      f ∈ lipSuppIn A := by
  have hc : ∀ B : Set (Fin 4 → ℝ),
      (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).IsEuclidCompact B ↔ IsCompact B := by
    intro B
    change @IsCompact _ (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).topology B ↔ _
    rw [ambient_topology_eq]
    exact Iff.rfl
  have hs := ambient_supp_eq L f
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, ?_, ?_⟩
    · rw [hs] at h₂
      exact (hc _).1 h₂
    · rw [hs] at h₃
      exact h₃
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, ?_, ?_⟩
    · rw [hs]
      exact (hc _).2 h₂
    · rw [hs]
      exact h₃
def lipSubmoduleToClass (L : ℕ) (A : Set (Fin 4 → ℝ)) :
    (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).lipSubmodule A →ₗ[ℝ]
      TestTupleClass.lipSubmodule A where
  toFun x := ⟨x.1, (mem_lipSubmodule_iff L A x.1).1 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def classToLipSubmodule (L : ℕ) (A : Set (Fin 4 → ℝ)) :
    TestTupleClass.lipSubmodule A →ₗ[ℝ]
      (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).lipSubmodule A where
  toFun x := ⟨x.1, (mem_lipSubmodule_iff L A x.1).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem partialFamilySequencesAgree_holds (D : TorusTransport.TransportData) :
    PartialFamilyTransportsAgree D := by
  intro L n hn ρ hρ Ψ Ψ' hag
  have hset : GrowingTori.lipTuplesInBall L n ρ =
      (TestTupleClass.ball ρ hρ).members D.toStandingParameters n :=
    (sepLipTuplesInBall_eq_lipTuplesInBall L (by omega) ρ hρ).symm
  constructor
  · rw [multilinearIffOnProducts_holds D (.ball ρ hρ) n (by omega) Ψ']
    constructor
    · intro H A hO hA
      obtain ⟨M, hM⟩ := H A hO (fun i k hik => pos_iff_ne_zero.2 (hA hik))
      refine ⟨M.compLinearMap fun l => classToLipSubmodule L (A l),
        fun g => (hM _).trans (hag _ _ _)⟩
    · intro H A hO hA
      obtain ⟨M, hM⟩ := H A hO (fun i k hik => (hA i k hik).ne')
      refine ⟨M.compLinearMap fun l => lipSubmoduleToClass L (A l),
        fun g => (hM _).trans (hag _ _ _).symm⟩
  · constructor
    · intro H σ h
      have := H σ ⟨h.1, hset.symm.subset h.2⟩
      rw [← hag _ (hset.symm.subset h.2) h.2, ← hag (fun i => h.1 (σ i))
        (hset.symm.subset (TestTupleClass.comp_mem_members _ h.2 σ.injective))]
      exact this
    · intro H σ h
      have := H σ ⟨h.1, hset.subset h.2⟩
      rw [hag _ h.2 (hset.subset h.2), hag (h.1 ∘ σ)
        (GrowingTori.comp_perm_mem_lipTuplesInBall h.2 σ)
        (hset.subset (GrowingTori.comp_perm_mem_lipTuplesInBall h.2 σ))]
      exact this
theorem partialHierarchyEquivExplicit_holds (D : TorusTransport.TransportData) :
    PartialHierarchyEquivExplicit D := by
  intro L ρ hρ
  have hset : ∀ n, 2 ≤ n → GrowingTori.lipTuplesInBall L n ρ =
      (TestTupleClass.ball ρ hρ).members D.toStandingParameters n := fun n hn =>
    (sepLipTuplesInBall_eq_lipTuplesInBall L (by omega) ρ hρ).symm
  have hw := partialFamilySequencesAgree_holds D
  refine ⟨{ toFun := fun Φ =>
              { func := fun n hn f => Φ.phi n hn ⟨f.1, (hset n hn).symm.subset f.2⟩
                multilinear := fun n hn =>
                  ((hw L n hn ρ hρ (Φ.phi n hn) _ fun _ _ _ => rfl).1).1 (Φ.phi_multilinear n hn)
                symmetric := fun n hn =>
                  ((hw L n hn ρ hρ (Φ.phi n hn) _ fun _ _ _ => rfl).2).1 (Φ.phi_symm n hn) }
            invFun := fun Ψ =>
              { radius_pos := hρ
                phi := fun n hn f => Ψ.func n hn ⟨f.1, (hset n hn).subset f.2⟩
                phi_symm := fun n hn =>
                  ((hw L n hn ρ hρ _ (Ψ.func n hn) fun _ _ _ => rfl).2).2 (Ψ.symmetric n hn)
                phi_multilinear := fun n hn =>
                  ((hw L n hn ρ hρ _ (Ψ.func n hn) fun _ _ _ => rfl).1).2 (Ψ.multilinear n hn) }
            left_inv := fun Φ => rfl
            right_inv := fun Ψ => rfl }, fun Φ n hn _ _ _ => rfl⟩
namespace CentredSums
variable {T : (n : ℕ) → Set (Fin n → RealFn)}
  {G : (n : ℕ) → (Fin n → RealFn) → ℝ}
theorem restrictTuple_congr_of_not_mem {q : ℕ} {f f' : Fin q → RealFn} {i : Fin q}
    (hag : ∀ l, l ≠ i → f l = f' l) {J : Finset (Fin q)} (hi : i ∉ J) :
    SchwingerFunctions.restrictTuple f J = SchwingerFunctions.restrictTuple f' J := by
  funext k
  refine hag _ ?_
  intro h
  exact hi (h ▸ Finset.orderEmbOfFin_mem J rfl k)
theorem centredFunctionalOf_update
    (hT : ∀ {n k : ℕ} {f : Fin n → RealFn}, f ∈ T n → ∀ {e : Fin k → Fin n},
      Function.Injective e → (fun l => f (e l)) ∈ T k)
    (hG : ∀ n, 2 ≤ n → ∀ (i : Fin n) (f f' : Fin n → RealFn), f ∈ T n →
      f' ∈ T n → (∀ l, l ≠ i → f l = f' l) → ∀ c c' : ℝ,
        G n (Function.update f i (c • f i + c' • f' i)) = c * G n f + c' * G n f')
    {q : ℕ} (i : Fin q) {f f' : Fin q → RealFn} (hf : f ∈ T q) (hf' : f' ∈ T q)
    (hag : ∀ l, l ≠ i → f l = f' l) (c c' : ℝ) :
    SchwingerFunctions.centredFunctionalOf G (Function.update f i (c • f i + c' • f' i)) =
      c * SchwingerFunctions.centredFunctionalOf G f +
        c' * SchwingerFunctions.centredFunctionalOf G f' := by
  classical
  unfold SchwingerFunctions.centredFunctionalOf
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π hπ => ?_
  obtain ⟨B, hB, hiB⟩ := π.exists_mem (Finset.mem_univ i)
  have h2 : 2 ≤ B.card := (Finset.mem_filter.mp hπ).2 B hB
  have hoff : ∀ J ∈ π.parts, J ≠ B → i ∉ J := fun J hJ hne hiJ =>
    hne (π.eq_of_mem_parts hJ hB hiJ hiB)
  have hrest : ∀ g : Fin q → RealFn, (∀ l, l ≠ i → g l = f l) →
      ∏ J ∈ π.parts.erase B, G J.card (SchwingerFunctions.restrictTuple g J) =
        ∏ J ∈ π.parts.erase B, G J.card (SchwingerFunctions.restrictTuple f J) := fun g hg =>
    Finset.prod_congr rfl fun J hJ => by
      rw [restrictTuple_congr_of_not_mem hg
        (hoff J (Finset.mem_of_mem_erase hJ) (Finset.ne_of_mem_erase hJ))]
  set p : Fin B.card := (B.orderIsoOfFin rfl).symm ⟨i, hiB⟩ with hp
  have hpi : B.orderEmbOfFin rfl p = i := by
    have := Finset.coe_orderIsoOfFin_apply B rfl p
    rw [← this, hp, OrderIso.apply_symm_apply]
  have hsub : SchwingerFunctions.restrictTuple (Function.update f i (c • f i + c' • f' i)) B =
      Function.update (SchwingerFunctions.restrictTuple f B) p
        (c • SchwingerFunctions.restrictTuple f B p +
          c' • SchwingerFunctions.restrictTuple f' B p) := by
    funext k
    by_cases hk : k = p
    · subst hk
      simp [SchwingerFunctions.restrictTuple, hpi]
    · have hne : B.orderEmbOfFin rfl k ≠ i := fun h =>
        hk ((B.orderEmbOfFin rfl).injective (h.trans hpi.symm))
      simp [SchwingerFunctions.restrictTuple, Function.update_of_ne hk, Function.update_of_ne hne]
  have hsf : SchwingerFunctions.restrictTuple f B ∈ T B.card :=
    hT hf (B.orderEmbOfFin rfl).injective
  have hsf' : SchwingerFunctions.restrictTuple f' B ∈ T B.card :=
    hT hf' (B.orderEmbOfFin rfl).injective
  have hagB : ∀ l, l ≠ p → SchwingerFunctions.restrictTuple f B l =
      SchwingerFunctions.restrictTuple f' B l := fun l hl =>
    hag _ fun h => hl ((B.orderEmbOfFin rfl).injective (h.trans hpi.symm))
  rw [← Finset.mul_prod_erase _ _ hB, ← Finset.mul_prod_erase π.parts _ hB,
    ← Finset.mul_prod_erase π.parts
      (fun J => G J.card (SchwingerFunctions.restrictTuple f' J)) hB, hsub,
    hG _ h2 p _ _ hsf hsf' hagB c c',
    hrest _ (fun l hl => Function.update_of_ne hl _ _),
    hrest f' (fun l hl => (hag l hl).symm)]
  ring
theorem apply_congr_of_equiv
    (hS : ∀ n, 2 ≤ n → ∀ f ∈ T n, ∀ σ : Equiv.Perm (Fin n), G n (fun l => f (σ l)) = G n f)
    {m m' : ℕ} (hm : m = m') (h2 : 2 ≤ m) (g : Fin m → RealFn)
    (g' : Fin m' → RealFn) (hg : g' ∈ T m') (e : Fin m ≃ Fin m')
    (he : ∀ k, g k = g' (e k)) : G m g = G m' g' := by
  subst hm
  have : g = fun l => g' (e l) := funext he
  rw [this]
  exact hS _ h2 _ hg e
def permutePartition {q : ℕ} (σ : Equiv.Perm (Fin q)) (π : SetPartition.PartitionsFin q) :
    SetPartition.PartitionsFin q :=
  Finpartition.ofExistsUnique (π.parts.image fun J => J.map σ.toEmbedding)
    (fun _ _ => Finset.subset_univ _)
    (fun a _ => by
      obtain ⟨J, hJ, ha⟩ := π.exists_mem (Finset.mem_univ (σ.symm a))
      refine ⟨J.map σ.toEmbedding, ⟨Finset.mem_image_of_mem _ hJ, ?_⟩, ?_⟩
      · exact Finset.mem_map.2 ⟨_, ha, by simp⟩
      · rintro I ⟨hI, haI⟩
        obtain ⟨J', hJ', rfl⟩ := Finset.mem_image.1 hI
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 haI
        have : b = σ.symm (σ b) := by simp
        have hb' : σ.symm (σ b) ∈ J' := by simpa using hb
        have : J' = J := π.eq_of_mem_parts hJ' hJ hb' (by simpa using ha)
        rw [this])
    (fun h => by
      obtain ⟨J, hJ, he⟩ := Finset.mem_image.1 h
      exact π.ne_bot hJ (Finset.map_eq_empty.1 he))
theorem parts_permutePartition {q : ℕ} (σ : Equiv.Perm (Fin q))
    (π : SetPartition.PartitionsFin q) :
    (permutePartition σ π).parts = π.parts.image fun J => J.map σ.toEmbedding := by
  simp [permutePartition, Finpartition.ofExistsUnique]
theorem permutePartition_symm_permutePartition {q : ℕ} (σ : Equiv.Perm (Fin q))
    (π : SetPartition.PartitionsFin q) :
    permutePartition σ.symm (permutePartition σ π) = π := by
  refine Finpartition.ext ?_
  rw [parts_permutePartition, parts_permutePartition, Finset.image_image]
  have : ((fun J : Finset (Fin q) => J.map σ.symm.toEmbedding) ∘
      fun J : Finset (Fin q) => J.map σ.toEmbedding) = id := by
    funext J
    ext x
    simp
  rw [this, Finset.image_id]
theorem permutePartition_mem {q : ℕ} (σ : Equiv.Perm (Fin q))
    {π : SetPartition.PartitionsFin q} (hπ : π ∈ SetPartition.nonSingletonPartitions q) :
    permutePartition σ π ∈ SetPartition.nonSingletonPartitions q := by
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun I hI => ?_⟩
  rw [parts_permutePartition] at hI
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.1 hI
  rw [Finset.card_map]
  exact (Finset.mem_filter.1 hπ).2 J hJ
theorem centredFunctionalOf_perm
    (hT : ∀ {n k : ℕ} {f : Fin n → RealFn}, f ∈ T n → ∀ {e : Fin k → Fin n},
      Function.Injective e → (fun l => f (e l)) ∈ T k)
    (hS : ∀ n, 2 ≤ n → ∀ f ∈ T n, ∀ σ : Equiv.Perm (Fin n), G n (fun l => f (σ l)) = G n f)
    {q : ℕ} (σ : Equiv.Perm (Fin q)) {f : Fin q → RealFn} (hf : f ∈ T q) :
    SchwingerFunctions.centredFunctionalOf G (fun l => f (σ l)) =
      SchwingerFunctions.centredFunctionalOf G f := by
  classical
  unfold SchwingerFunctions.centredFunctionalOf
  refine Finset.sum_nbij' (permutePartition σ) (permutePartition σ.symm)
    (fun π hπ => permutePartition_mem σ hπ) (fun π hπ => permutePartition_mem σ.symm hπ)
    (fun π _ => permutePartition_symm_permutePartition σ π)
    (fun π _ => by simpa using permutePartition_symm_permutePartition σ.symm π) fun π hπ => ?_
  rw [parts_permutePartition, Finset.prod_image]
  · refine Finset.prod_congr rfl fun J hJ => ?_
    have h2 : 2 ≤ J.card := (Finset.mem_filter.mp hπ).2 J hJ
    have hc : J.card = (J.map σ.toEmbedding).card := (Finset.card_map _).symm
    refine apply_congr_of_equiv hS hc h2 _ _
      (hT hf ((J.map σ.toEmbedding).orderEmbOfFin rfl).injective)
      (((J.orderIsoOfFin rfl).toEquiv.trans (σ.subtypeEquiv fun a => by simp)).trans
        ((J.map σ.toEmbedding).orderIsoOfFin rfl).toEquiv.symm) fun k => ?_
    have := Finset.coe_orderIsoOfFin_apply (J.map σ.toEmbedding) rfl
      ((((J.orderIsoOfFin rfl).toEquiv.trans (σ.subtypeEquiv fun a => by simp)).trans
        ((J.map σ.toEmbedding).orderIsoOfFin rfl).toEquiv.symm) k)
    simp only [SchwingerFunctions.restrictTuple]
    rw [← this]
    simp
  · intro J _ J' _ h
    exact Finset.map_injective _ h
end CentredSums
theorem membersEqPeriodicClass_holds (hc : SubfamiliesAndGaps.Statement)
    (s : Conventions.StandingParameters) (Y : PeriodicSpace.Params) :
    MembersEqPeriodicClass s Y := by
  intro K n hn
  obtain ⟨-, -, hT, hC⟩ := hc.2.2.2.2.1 Y
  cases K with
  | sep =>
    ext f
    change f ∈ sepTuplesR4 s n ↔ f ∈ PeriodicSpace.Kind.sepC1TuplesWithin Y .euclidean n
      (PeriodicSpace.Kind.centredBall Y .euclidean ∞)
    have hb : PeriodicSpace.Kind.centredBall Y .euclidean ∞ = univ := if_pos rfl
    rw [← (hC s).2 n hn, hb]
    exact ⟨fun h => ⟨h, fun _ => subset_univ _⟩, fun h => h.1⟩
  | ball ρ hρ =>
    ext f
    exact (hT.2.1 n hn ρ hρ f).symm
theorem isClassMultilinear_iff_isMultilinearOn (D : TorusTransport.TransportData)
    (Y : PeriodicSpace.Params) (K : TestTupleClass) {n : ℕ} (hn : 1 ≤ n)
    {S : Set (Fin n → RealFn)} (hS : K.members D.toStandingParameters n = S)
    (Ψ : K.members D.toStandingParameters n → ℝ) (Ψ' : S → ℝ) (hag : AgreeOnCommon Ψ Ψ') :
    IsClassMultilinear D K hn Ψ ↔ PeriodicSpace.Kind.IsMultilinearOn Y .euclidean S Ψ' := by
  subst hS
  have hΨ : Ψ' = Ψ := funext fun f => (hag f.1 f.2 f.2).symm
  subst hΨ
  rw [isClassMultilinear_iff]
  constructor
  · intro H i h h' hagr
    refine ⟨fun hSum => ?_, fun α hScaled => ?_⟩
    · have e := H i h h' hagr 1 1
      have t : Function.update h.1 i (h.1 i + h'.1 i) =
          Function.update h.1 i ((1 : ℝ) • h.1 i + (1 : ℝ) • h'.1 i) := by simp
      calc Ψ' ⟨_, hSum⟩ = Ψ' ⟨_, ClassMembers.update_mem_members K i h.2 h'.2 hagr 1 1⟩ :=
            congrArg Ψ' (Subtype.ext t)
        _ = Ψ' h + Ψ' h' := by rw [e]; ring
    · have e := H i h h (fun _ _ => rfl) α 0
      have t : Function.update h.1 i (α • h.1 i) =
          Function.update h.1 i (α • h.1 i + (0 : ℝ) • h.1 i) := by simp
      calc Ψ' ⟨_, hScaled⟩ =
            Ψ' ⟨_, ClassMembers.update_mem_members K i h.2 h.2 (fun _ _ => rfl) α 0⟩ :=
            congrArg Ψ' (Subtype.ext t)
        _ = α * Ψ' h := by rw [e]; ring
  · intro H i h h' hagr c c'
    have hu : Function.update h.1 i (c • h.1 i) ∈ K.members D.toStandingParameters n := by
      simpa using ClassMembers.update_mem_members K i h.2 h.2 (fun _ _ => rfl) c 0
    have hu' : Function.update h.1 i (c' • h'.1 i) ∈ K.members D.toStandingParameters n := by
      simpa using ClassMembers.update_mem_members K i h.2 h'.2 hagr 0 c'
    have hv' : Function.update h'.1 i (c' • h'.1 i) = Function.update h.1 i (c' • h'.1 i) := by
      funext l
      by_cases hl : l = i
      · subst hl
        simp
      · simp [hl, hagr l hl]
    have hsum : Function.update (Function.update h.1 i (c • h.1 i)) i
        (Function.update h.1 i (c • h.1 i) i + Function.update h.1 i (c' • h'.1 i) i) =
        Function.update h.1 i (c • h.1 i + c' • h'.1 i) := by simp
    have e₁ := (H i ⟨_, hu⟩ ⟨_, hu'⟩ (fun l hl =>
      (Function.update_of_ne hl _ _).trans (Function.update_of_ne hl _ _).symm)).1
      (mem_of_eq_of_mem hsum (ClassMembers.update_mem_members K i h.2 h'.2 hagr c c'))
    have e₂ := (H i h h (fun _ _ => rfl)).2 c hu
    have e₃ := (H i h' h' (fun _ _ => rfl)).2 c' (mem_of_eq_of_mem hv' hu')
    calc Ψ' ⟨_, ClassMembers.update_mem_members K i h.2 h'.2 hagr c c'⟩ = _ :=
          congrArg Ψ' (Subtype.ext hsum.symm)
      _ = Ψ' ⟨_, hu⟩ + Ψ' ⟨_, hu'⟩ := e₁
      _ = c * Ψ' h + c' * Ψ' h' := congrArg₂ (· + ·) e₂ ((congrArg Ψ' (Subtype.ext hv'.symm)).trans e₃)
theorem isClassSymmetric_iff_isPermSymmetricOn (s : Conventions.StandingParameters)
    (Y : PeriodicSpace.Params) (K : TestTupleClass)
    {n : ℕ} {S : Set (Fin n → RealFn)} (hS : K.members s n = S)
    (Ψ : K.members s n → ℝ) (Ψ' : S → ℝ) (hag : AgreeOnCommon Ψ Ψ') :
    IsClassSymmetric s K Ψ ↔ PeriodicSpace.Kind.IsPermSymmetricOn Y .euclidean S Ψ' := by
  subst hS
  have hΨ : Ψ' = Ψ := funext fun f => (hag f.1 f.2 f.2).symm
  subst hΨ
  constructor
  · intro H f ς _
    exact H ς f
  · intro H σ h
    exact H h σ (K.comp_mem_members h.2 σ.injective)
theorem multilinearIffPeriodicMultilinear_holds (hc : SubfamiliesAndGaps.Statement)
    (D : TorusTransport.TransportData) (Y : PeriodicSpace.Params) :
    MultilinearIffPeriodicMultilinear D Y :=
  fun K n hn Ψ Ψ' hag =>
    isClassMultilinear_iff_isMultilinearOn D Y K hn
      (membersEqPeriodicClass_holds hc _ Y K n hn) Ψ Ψ' hag
theorem continuous_of_lipschitzR4 {f : RealFn} (hf : LipschitzR4 f) :
    Continuous f := by apply _root_.YangMills.Construction.TestPairs.continuous_of_isLipschitzFor_r4 <;> assumption
theorem sharpNormQ_euclidean_eq (D : TorusTransport.TransportData) (Y : PeriodicSpace.Params)
    (hM : Y.M = D.M)
    (hd : ∀ x x' : Fin 4 → ℝ,
      PeriodicSpace.Kind.quotDist Y .euclidean x x' = TorusMetric.euclidNormVec (x - x'))
    {f : RealFn} (hL : LipschitzR4 f) (hcpt : IsCompact (fnSupport f)) :
    PeriodicSpace.Kind.sharpNormQ Y .euclidean f =
      ENNReal.ofReal (TestFunctions.sharpNormR4 D.M f) := by
  have hb : BddAbove (range fun x => ‖f x‖) := by
    obtain ⟨C, hC⟩ := (continuous_of_lipschitzR4 hL).bounded_above_of_compact_support hcpt
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have hsup : PeriodicSpace.Kind.supNormQ Y .euclidean f =
      ENNReal.ofReal (TestFunctions.uniformNorm f) := by
    have hle : PeriodicSpace.Kind.supNormQ Y .euclidean f ≤
        ENNReal.ofReal (TestFunctions.uniformNorm f) :=
      iSup_le fun y => ENNReal.ofReal_le_ofReal (le_ciSup hb y)
    refine le_antisymm hle ?_
    have htop : PeriodicSpace.Kind.supNormQ Y .euclidean f ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    rw [← ENNReal.ofReal_toReal htop]
    refine ENNReal.ofReal_le_ofReal (ciSup_le fun y => ?_)
    rw [← ENNReal.ofReal_le_iff_le_toReal htop]
    exact le_iSup (fun y : Fin 4 → ℝ => ENNReal.ofReal |f y|) y
  have hlip : PeriodicSpace.Kind.lipConstQ Y .euclidean f = TestFunctions.lipConstR4 f := by
    have : PeriodicSpace.Kind.quotDist Y .euclidean = TestFunctions.euclidDistR4 :=
      funext₂ hd
    exact congrArg (fun d : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ =>
      TestFunctions.bestLipschitzConstant d f) this
  simp only [PeriodicSpace.Kind.sharpNormQ, TestFunctions.sharpNormR4, hsup, hlip, hM]
  exact (ENNReal.ofReal_mono.map_max).symm
theorem sharpNormR4_nonneg (M : ℝ) (f : RealFn) :
    0 ≤ TestFunctions.sharpNormR4 M f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem ofReal_bound_iff (D : TorusTransport.TransportData) (Y : PeriodicSpace.Params)
    (hM : Y.M = D.M)
    (hd : ∀ x x' : Fin 4 → ℝ,
      PeriodicSpace.Kind.quotDist Y .euclidean x x' = TorusMetric.euclidNormVec (x - x'))
    {n : ℕ} {f : Fin n → RealFn} (hf : IsSepLipTuple f) {c x : ℝ}
    (hc : 0 ≤ c) :
    ENNReal.ofReal |x| ≤
        ENNReal.ofReal c * ∏ i, PeriodicSpace.Kind.sharpNormQ Y .euclidean (f i) ↔
      |x| ≤ c * ∏ i, TestFunctions.sharpNormR4 D.M (f i) := by
  have h₁ : ∀ i, PeriodicSpace.Kind.sharpNormQ Y .euclidean (f i) =
      ENNReal.ofReal (TestFunctions.sharpNormR4 D.M (f i)) := fun i =>
    sharpNormQ_euclidean_eq D Y hM hd (hf.1 i) (hf.2.1 i)
  have h₂ : 0 ≤ ∏ i, TestFunctions.sharpNormR4 D.M (f i) :=
    Finset.prod_nonneg fun i _ => sharpNormR4_nonneg _ _
  simp only [h₁]
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => sharpNormR4_nonneg _ _,
    ← ENNReal.ofReal_mul hc, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc h₂)]
section Hierarchies
variable {D : TorusTransport.TransportData} {Y : PeriodicSpace.Params}
def explicitOfEuclid
    (hsep : ∀ n, 1 ≤ n → TestTupleClass.sep.members D.toStandingParameters n =
      PeriodicSpace.Kind.sepC1Tuples Y .euclidean n)
    (Φ : EuclidHierarchy Y) : ExplicitHierarchy D where
  func n hn f := Φ.func n hn ⟨f.1, (hsep n (by omega)).subset f.2⟩
  multilinear n hn := (isClassMultilinear_iff_isMultilinearOn D Y .sep (by omega)
    (hsep n (by omega)) _ (Φ.func n hn) fun _ _ _ => rfl).2 (Φ.multilinear n hn)
  symmetric n hn := (isClassSymmetric_iff_isPermSymmetricOn _ Y .sep (hsep n (by omega)) _
    (Φ.func n hn) fun _ _ _ => rfl).2 (Φ.symmetric n hn)
def euclidOfExplicit
    (hsep : ∀ n, 1 ≤ n → TestTupleClass.sep.members D.toStandingParameters n =
      PeriodicSpace.Kind.sepC1Tuples Y .euclidean n)
    (Φ : ExplicitHierarchy D) : EuclidHierarchy Y where
  func n hn f := Φ.func n hn ⟨f.1, (hsep n (by omega)).symm.subset f.2⟩
  multilinear n hn := (isClassMultilinear_iff_isMultilinearOn D Y .sep (by omega)
    (hsep n (by omega)) (Φ.func n hn) _ fun _ _ _ => rfl).1 (Φ.multilinear n hn)
  symmetric n hn := (isClassSymmetric_iff_isPermSymmetricOn _ Y .sep (hsep n (by omega))
    (Φ.func n hn) _ fun _ _ _ => rfl).1 (Φ.symmetric n hn)
end Hierarchies
theorem euclidHierarchyEquivExplicit_holds (hc : SubfamiliesAndGaps.Statement)
    (D : TorusTransport.TransportData) (Y : PeriodicSpace.Params) (hM : Y.M = D.M) :
    EuclidHierarchyEquivExplicit D Y := by
  obtain ⟨hW, -, hT, hC⟩ := hc.2.2.2.2.1 Y
  have hsep : ∀ n, 1 ≤ n → TestTupleClass.sep.members D.toStandingParameters n =
      PeriodicSpace.Kind.sepC1Tuples Y .euclidean n := fun n hn =>
    ((hC D.toStandingParameters).2 n hn).symm
  let e : EuclidHierarchy Y ≃ ExplicitHierarchy D :=
    { toFun := explicitOfEuclid hsep
      invFun := euclidOfExplicit hsep
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hob : ∀ (C : PeriodicSpace.BoundFamily) (Φ : EuclidHierarchy Y),
      Φ.IsBoundedBy C ↔ (e Φ).IsBoundedBy C := by
    intro C Φ
    constructor
    · intro H n hn d R hd hR f hf
      have hY : f.1 ∈ PeriodicSpace.Kind.lipTuplesSpacedInBalls Y .euclidean n d R :=
        (hT.2.2.2.2 n hn d R hd hR).symm.subset hf
      exact (ofReal_bound_iff D Y hM hW.1 hf.1 (C.nonneg n hn d R hd hR)).1
        (H n hn d R hd hR ⟨f.1, (hsep n (by omega)).subset f.2⟩ hY)
    · intro H n hn d R hd hR f hf
      have hR' : 0 < R := hR
      have hY : f.1 ∈ lipTuples n hn d R hd hR' := (hT.2.2.2.2 n hn d R hd hR').subset hf
      exact (ofReal_bound_iff D Y hM hW.1 hY.1 (C.nonneg n hn d R hd hR')).2
        (H n hn d R hd hR' ⟨f.1, (hsep n (by omega)).symm.subset f.2⟩ hY)
  refine ⟨e, fun Φ n hn _ _ _ => rfl, hob, fun C => ?_⟩
  ext Φ'
  constructor
  · rintro ⟨Φ, hΦ, rfl⟩
    exact (hob C Φ).1 hΦ
  · intro hΦ'
    exact ⟨e.symm Φ', (hob C _).2 (by rw [e.apply_symm_apply]; exact hΦ'), e.apply_symm_apply Φ'⟩
theorem explicitHierarchyEquivSymmConnected_holds (D : TorusTransport.TransportData) :
    ExplicitHierarchyEquivSymmConnected D := by
  have hw : ∀ (n : ℕ) (hn : 2 ≤ n) (Ψ : TestTupleClass.sep.members D.toStandingParameters n → ℝ),
      IsClassMultilinear D .sep (by omega : 1 ≤ n) Ψ ↔
        AmbientPoints.IsTupleMultilinear (s := D.toStandingParameters) (E := .euclidean) Ψ :=
    fun n hn Ψ =>
    (multilinearIffOnProducts_holds D .sep n (by omega) Ψ).trans
      (onProductsIffTupleMultilinear_holds _ n (by omega) Ψ)
  refine ⟨{ toFun := fun Φ => ⟨⟨Φ.func, fun n hn => (hw n hn _).1 (Φ.multilinear n hn)⟩,
              fun n hn f ς => Φ.symmetric n hn ς f⟩
            invFun := fun S =>
              { func := S.1.fn
                multilinear := fun n hn => (hw n hn _).2 (S.1.fn_multilinear n hn)
                symmetric := fun n hn ς f => S.2 n hn f ς }
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }, fun _ _ _ _ => rfl⟩
section Moments
variable (K : TestTupleClass) (s : Conventions.StandingParameters)
open Classical in
def extendByZero (Ψ : (n : ℕ) → 2 ≤ n → K.members s n → ℝ) (n : ℕ)
    (g : Fin n → RealFn) : ℝ :=
  if h : 2 ≤ n ∧ g ∈ K.members s n then Ψ n h.1 ⟨g, h.2⟩ else 0
theorem extendByZero_eq (Ψ : (n : ℕ) → 2 ≤ n → K.members s n → ℝ) {n : ℕ} (hn : 2 ≤ n)
    {g : Fin n → RealFn} (hg : g ∈ K.members s n) :
    extendByZero K s Ψ n g = Ψ n hn ⟨g, hg⟩ :=
  dif_pos ⟨hn, hg⟩
end Moments
theorem symm_multilinear_of_centred (D : TorusTransport.TransportData) (K : TestTupleClass)
    (Ψ : (n : ℕ) → 2 ≤ n → K.members D.toStandingParameters n → ℝ)
    (hm : ∀ n (hn : 2 ≤ n), IsClassMultilinear D K (by omega : 1 ≤ n) (Ψ n hn))
    (hs : ∀ n (hn : 2 ≤ n), IsClassSymmetric D.toStandingParameters K (Ψ n hn))
    {q : ℕ} (hq : 1 ≤ q) (Mom : K.members D.toStandingParameters q → ℝ)
    (hMom : ∀ f, Mom f = SchwingerFunctions.centredFunctionalOf
      (extendByZero K D.toStandingParameters Ψ) f.1) :
    IsClassSymmetric D.toStandingParameters K Mom ∧ IsClassMultilinear D K hq Mom := by
  have hT : ∀ {n k : ℕ} {f : Fin n → RealFn}, f ∈ K.members D.toStandingParameters n →
      ∀ {e : Fin k → Fin n}, Function.Injective e →
        (fun l => f (e l)) ∈ K.members D.toStandingParameters k :=
    fun hf _ he => K.comp_mem_members hf he
  constructor
  · intro σ h
    rw [hMom, hMom]
    refine CentredSums.centredFunctionalOf_perm (T := fun n => K.members D.toStandingParameters n)
      hT (fun n hn f hf σ => ?_) σ h.2
    rw [extendByZero_eq K _ Ψ hn hf, extendByZero_eq K _ Ψ hn (K.comp_mem_members hf σ.injective)]
    exact hs n hn σ ⟨f, hf⟩
  · rw [isClassMultilinear_iff]
    intro i h h' hag c c'
    rw [hMom, hMom, hMom]
    refine CentredSums.centredFunctionalOf_update
      (T := fun n => K.members D.toStandingParameters n) hT
      (fun n hn i f f' hf hf' hag c c' => ?_) i h.2 h'.2 hag c c'
    rw [extendByZero_eq K _ Ψ hn hf, extendByZero_eq K _ Ψ hn hf',
      extendByZero_eq K _ Ψ hn (ClassMembers.update_mem_members K i hf hf' hag c c')]
    exact (isClassMultilinear_iff D K _ _).1 (hm n hn) i ⟨f, hf⟩ ⟨f', hf'⟩ hag c c'
theorem partialCentredMomentsSymmMultilinear_holds (D : TorusTransport.TransportData) :
    PartialCentredMomentsSymmMultilinear D := by
  intro L ρ Φ q hq
  have hset : ∀ n, 2 ≤ n → (TestTupleClass.ball ρ Φ.radius_pos).members D.toStandingParameters n =
      GrowingTori.lipTuplesInBall L n ρ := fun n hn =>
    sepLipTuplesInBall_eq_lipTuplesInBall L (by omega) ρ Φ.radius_pos
  have hw := partialFamilySequencesAgree_holds D
  let Ψ : (n : ℕ) → 2 ≤ n →
      (TestTupleClass.ball ρ Φ.radius_pos).members D.toStandingParameters n → ℝ :=
    fun n hn f => Φ.phi n hn ⟨f.1, (hset n hn).subset f.2⟩
  refine symm_multilinear_of_centred D (.ball ρ Φ.radius_pos) Ψ
    (fun n hn => ((hw L n hn ρ Φ.radius_pos (Φ.phi n hn) (Ψ n hn)
      fun _ _ _ => rfl).1).1 (Φ.phi_multilinear n hn))
    (fun n hn => ((hw L n hn ρ Φ.radius_pos (Φ.phi n hn) (Ψ n hn)
      fun _ _ _ => rfl).2).1 (Φ.phi_symm n hn)) hq _ fun f => ?_
  refine centredMomentOf_eq_centredFunctionalOf Φ f _ fun n hn g => ?_
  exact extendByZero_eq _ _ Ψ hn ((hset n hn).symm.subset g.2)
theorem partitionMoment_eq_centredFunctionalOf {Y : PeriodicSpace.Params}
    (Φ : EuclidHierarchy Y) {q : ℕ}
    (f : PeriodicSpace.Kind.sepC1Tuples Y .euclidean q)
    (S : (n : ℕ) → (Fin n → RealFn) → ℝ)
    (hS : ∀ (n : ℕ) (hn : 2 ≤ n) (g : PeriodicSpace.Kind.sepC1Tuples Y .euclidean n),
      S n g.1 = Φ.func n hn g) :
    Φ.partitionMoment f = SchwingerFunctions.centredFunctionalOf S f.1 := by
  change _ = ∑ π ∈ SetPartition.nonSingletonPartitions q, ∏ J ∈ π.parts,
    S J.card (SchwingerFunctions.restrictTuple (f.1 : Fin q → RealFn) J)
  rw [← SetPartition.singletonFree_eq_nonSingletonPartitions, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Finset.prod_attach π.1.parts]
  exact Finset.prod_congr rfl fun B _ => (hS _ _ _).symm
theorem centredMomentsSymmMultilinear_holds (hc : SubfamiliesAndGaps.Statement)
    (D : TorusTransport.TransportData) (Y : PeriodicSpace.Params) :
    CentredMomentsSymmMultilinear D Y := by
  obtain ⟨-, -, -, hC⟩ := hc.2.2.2.2.1 Y
  have hsep : ∀ n, 1 ≤ n → TestTupleClass.sep.members D.toStandingParameters n =
      PeriodicSpace.Kind.sepC1Tuples Y .euclidean n := fun n hn =>
    ((hC D.toStandingParameters).2 n hn).symm
  intro Φ q hq Ψ hag
  refine symm_multilinear_of_centred D .sep (explicitOfEuclid hsep Φ).func
    (explicitOfEuclid hsep Φ).multilinear (explicitOfEuclid hsep Φ).symmetric hq _
    fun f => ?_
  rw [hag f.1 f.2 ((hsep q hq).subset f.2)]
  refine partitionMoment_eq_centredFunctionalOf Φ ⟨f.1, (hsep q hq).subset f.2⟩ _
    fun n hn g => ?_
  exact extendByZero_eq _ _ _ hn ((hsep n (by omega)).symm.subset g.2)
theorem partitionMomentEqCentred_holds (s : Conventions.StandingParameters)
    (Y : PeriodicSpace.Params) : PartitionMomentEqCentred s Y := by
  intro Φ S hag q f hf hg
  unfold AmbientPoints.ConnectedFamily.centred
  refine (Finset.sum_congr rfl fun π _ => ?_).trans (Finset.sum_attach _ _)
  refine (Finset.prod_congr rfl fun B _ => ?_).trans (Finset.prod_attach π.1.parts _)
  have h2 := PeriodicSpace.two_le_card_of_mem_partitionsNoSingletons π.2 B.2
  have hb : S.blockFactor ⟨f, hg⟩ B.1 =
      S.fn _ h2 (AmbientPoints.restrictSeparated ⟨f, hg⟩ B.1) :=
    dif_pos h2
  exact (hag _ h2 _ _ (AmbientPoints.restrictTuple_mem hg B.1)).trans hb.symm
theorem partialFamily_sequences_iff_periodic (D : TorusTransport.TransportData)
    (Y : PeriodicSpace.Params) {L n : ℕ}
    (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (Ψ : GrowingTori.lipTuplesInBall L n ρ → ℝ)
    {S : Set (Fin n → RealFn)}
    (hS : (TestTupleClass.ball ρ hρ).members D.toStandingParameters n = S) (Ψ' : S → ℝ)
    (hag : AgreeOnCommon Ψ Ψ') :
    (GrowingTori.IsMultilinearOnTuples hn Ψ ↔
      PeriodicSpace.Kind.IsMultilinearOn Y .euclidean S Ψ') ∧
    (GrowingTori.IsSymmetricOnTuples Ψ ↔
      PeriodicSpace.Kind.IsPermSymmetricOn Y .euclidean S Ψ') := by
  have hset : GrowingTori.lipTuplesInBall L n ρ =
      (TestTupleClass.ball ρ hρ).members D.toStandingParameters n :=
    (sepLipTuplesInBall_eq_lipTuplesInBall L (by omega) ρ hρ).symm
  let Ψ'' : (TestTupleClass.ball ρ hρ).members D.toStandingParameters n → ℝ :=
    fun f => Ψ ⟨f.1, hset.symm.subset f.2⟩
  have h₂ : AgreeOnCommon Ψ'' Ψ' := fun f hf hf' => hag f _ hf'
  obtain ⟨a, b⟩ := partialFamilySequencesAgree_holds D L n hn ρ hρ Ψ Ψ'' fun _ _ _ => rfl
  exact ⟨a.trans (isClassMultilinear_iff_isMultilinearOn D Y _ (by omega) hS Ψ'' Ψ' h₂),
    b.trans (isClassSymmetric_iff_isPermSymmetricOn _ Y _ hS Ψ'' Ψ' h₂)⟩
theorem partialSeqEquivExplicit_holds (hc : SubfamiliesAndGaps.Statement)
    (D : TorusTransport.TransportData) (Y : PeriodicSpace.Params) (hM : Y.M = D.M) :
    PartialSeqEquivExplicit D Y := by
  intro J₀ ρ'
  obtain ⟨hW, -, hT, hC⟩ := hc.2.2.2.2.1 Y
  have hsep : ∀ n, 1 ≤ n → TestTupleClass.sep.members D.toStandingParameters n =
      PeriodicSpace.Kind.sepC1Tuples Y .euclidean n := fun n hn =>
    ((hC D.toStandingParameters).2 n hn).symm
  have hS : ∀ {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ}, 1 ≤ n →
      (TestTupleClass.ball ρ hρ).members D.toStandingParameters n =
        PeriodicSpace.Kind.sepLipTuplesWithin Y .euclidean n
          (PeriodicSpace.Kind.centredBall Y .euclidean (ENNReal.ofReal ρ)) :=
    fun {ρ} hρ {n} hn =>
    membersEqPeriodicClass_holds hc D.toStandingParameters Y (.ball ρ hρ) n hn
  have hball : ∀ {ρ : ℝ} (_ : 0 < ρ) {n : ℕ}, 2 ≤ n →
      GrowingTori.lipTuplesInBall D.L n ρ =
        PeriodicSpace.Kind.sepLipTuplesWithin Y .euclidean n
          (PeriodicSpace.Kind.centredBall Y .euclidean (ENNReal.ofReal ρ)) :=
    fun {ρ} hρ {n} hn =>
    (sepLipTuplesInBall_eq_lipTuplesInBall D.L (by omega) ρ hρ).symm.trans (hS hρ (by omega))
  let e : PeriodicSpace.Kind.PartialHierarchySeq Y .euclidean J₀
        (fun j => ENNReal.ofReal (ρ' j)) ≃
      ExplicitPartialHierarchySeq D.L J₀ ρ' :=
    { toFun := fun Ψ =>
        { radius_eventually_gt := fun ρ hρ => by
            obtain ⟨j', hj⟩ := Ψ.radii.eventually_gt ρ hρ
            exact ⟨j', fun j hle => (ENNReal.ofReal_lt_ofReal_iff'.1 (hj j.1 j.2 hle j.2)).1⟩
          term := fun j =>
            { radius_pos := ENNReal.ofReal_pos.1 (Ψ.radii.pos j)
              phi := fun n hn f => Ψ.func j n hn
                ⟨f.1, (hball (ENNReal.ofReal_pos.1 (Ψ.radii.pos j)) hn).subset f.2⟩
              phi_symm := fun n hn =>
                ((partialFamily_sequences_iff_periodic D Y hn (ENNReal.ofReal_pos.1 (Ψ.radii.pos j)) _
                  (hS _ (by omega)) (Ψ.func j n hn) fun _ _ _ => rfl).2).2
                  (Ψ.symmetric j n hn)
              phi_multilinear := fun n hn =>
                ((partialFamily_sequences_iff_periodic D Y hn (ENNReal.ofReal_pos.1 (Ψ.radii.pos j)) _
                  (hS _ (by omega)) (Ψ.func j n hn) fun _ _ _ => rfl).1).2
                  (Ψ.multilinear j n hn) } }
      invFun := fun Ψ =>
        { radii :=
            { pos := fun j => ENNReal.ofReal_pos.2 (Ψ.term j).radius_pos
              eventually_gt := fun r hr => by
                obtain ⟨jρ, h⟩ := Ψ.radius_eventually_gt r hr
                exact ⟨jρ, fun j hj hle hj' => (ENNReal.ofReal_lt_ofReal_iff
                  (Ψ.term ⟨j, hj'⟩).radius_pos).2 (h ⟨j, hj'⟩ hle)⟩
              eq_top_of_torus := fun h => by cases h }
          func := fun j n hn f => (Ψ.term j).phi n hn
            ⟨f.1, (hball (Ψ.term j).radius_pos hn).symm.subset f.2⟩
          multilinear := fun j n hn =>
            ((partialFamily_sequences_iff_periodic D Y hn (Ψ.term j).radius_pos
              ((Ψ.term j).phi n hn) (hS _ (by omega)) _ fun _ _ _ => rfl).1).1
              ((Ψ.term j).phi_multilinear n hn)
          symmetric := fun j n hn =>
            ((partialFamily_sequences_iff_periodic D Y hn (Ψ.term j).radius_pos
              ((Ψ.term j).phi n hn) (hS _ (by omega)) _ fun _ _ _ => rfl).2).1
              ((Ψ.term j).phi_symm n hn) }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨e, fun Ψ => ?_⟩
  have hob : ∀ (C : PeriodicSpace.BoundFamily) (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : 0 < R)
      (j₀ : ℤ), Ψ.BoundedFrom C n hn R j₀ ↔ (e Ψ).BoundedFrom D.M C n hn R hR j₀ := by
    intro C n hn R hR j₀
    constructor
    · intro H j hj d hd f hf
      exact (ofReal_bound_iff D Y hM hW.1 hf.1 (C.nonneg n hn d R hd hR)).1
        (H j hj d hd ⟨f.1, (hball ((e Ψ).term j).radius_pos hn).subset f.2⟩
          ((hT.2.2.2.2 n hn d R hd hR).symm.subset hf))
    · intro H j hj d hd f hf
      have hf' : f.1 ∈ lipTuples n hn d R hd hR := (hT.2.2.2.2 n hn d R hd hR).subset hf
      exact (ofReal_bound_iff D Y hM hW.1 hf'.1 (C.nonneg n hn d R hd hR)).2
        (H j hj d hd ⟨f.1, (hball ((e Ψ).term j).radius_pos hn).symm.subset f.2⟩ hf')
  refine ⟨fun _ _ _ _ _ _ => rfl, hob, fun C => ?_, fun J hJ => ?_⟩
  · constructor
    · intro H n hn R hR
      obtain ⟨j₀, h⟩ := H n hn R hR
      exact ⟨j₀, (hob C n hn R hR j₀).1 h⟩
    · intro H n hn R hR
      obtain ⟨j₀, h⟩ := H n hn R hR
      exact ⟨j₀, (hob C n hn R hR j₀).2 h⟩
  · refine ⟨{ dom := fun j n => PeriodicSpace.Kind.sepLipTuplesWithin Y .euclidean n
                (PeriodicSpace.Kind.centredBall Y .euclidean (ENNReal.ofReal (ρ' ⟨j.1, hJ j.2⟩)))
              func := fun j n hn f => Ψ.func ⟨j.1, hJ j.2⟩ n hn f
              eventually_mem_dom := ?_ }, fun _ _ => rfl, fun _ _ _ _ _ _ => rfl, ?_⟩
    · intro n hn f hf
      have hL : IsSepLipTuple f :=
        TestTupleClass.sep.isSepLipTuple_of_mem
          (s := D.toStandingParameters) ((hsep n (by omega)).symm.subset hf)
      obtain ⟨-, ⟨ρ, hρ, hsup⟩, -⟩ := hc.2.2.2.1 n hn f hL
      obtain ⟨jρ, hj⟩ := (e Ψ).radius_eventually_gt ρ hρ
      refine ⟨jρ, fun j hjJ hle hj' => ?_⟩
      have hlt : ρ < ρ' ⟨j, hJ hj'⟩ := hj ⟨j, hJ hj'⟩ hle
      exact (hS (((e Ψ).term ⟨j, hJ hj'⟩).radius_pos) (by omega)).subset
        ⟨hL, fun i => (hsup i).trans fun x hx => lt_trans hx hlt⟩
    · intro Φ Φ' hag
      constructor
      · intro H n hn f
        obtain ⟨j', hf, hconv⟩ := H n hn ⟨f.1, (hsep n (by omega)).subset f.2⟩
        refine ⟨j', fun j => (hball ((e Ψ).term _).radius_pos hn).symm.subset (hf j), ?_⟩
        have e₁ : Φ'.func n hn f = Φ.func n hn ⟨f.1, (hsep n (by omega)).subset f.2⟩ :=
          (hag n hn f.1 _ f.2).symm
        rw [e₁]
        exact hconv
      · intro H n hn f
        obtain ⟨j', hf, hconv⟩ := H n hn ⟨f.1, (hsep n (by omega)).symm.subset f.2⟩
        refine ⟨j', fun j => (hball ((e Ψ).term _).radius_pos hn).subset (hf j), ?_⟩
        have e₁ : Φ.func n hn f =
            Φ'.func n hn ⟨f.1, (hsep n (by omega)).symm.subset f.2⟩ :=
          hag n hn f.1 f.2 _
        rw [e₁]
        exact hconv
theorem statement_holds (hc : SubfamiliesAndGaps.Statement) : Statement := fun D =>
  ⟨updateStaysInClass_holds _, multilinearIffOnProducts_holds D,
    onProductsIffTupleMultilinear_holds _, partialFamilySequencesAgree_holds D,
    partialHierarchyEquivExplicit_holds D, eqZeroOfEntryEqZero_holds D,
    partialCentredMomentsSymmMultilinear_holds D, explicitHierarchyEquivSymmConnected_holds D,
    fun Y hM => ⟨centredMomentsSymmMultilinear_holds hc D Y,
      partitionMomentEqCentred_holds _ Y, membersEqPeriodicClass_holds hc _ Y,
      multilinearIffPeriodicMultilinear_holds hc D Y, euclidHierarchyEquivExplicit_holds hc D Y hM,
      partialSeqEquivExplicit_holds hc D Y hM⟩⟩
end YangMills.Construction.ToriLimits.NonlinearDomain
end
