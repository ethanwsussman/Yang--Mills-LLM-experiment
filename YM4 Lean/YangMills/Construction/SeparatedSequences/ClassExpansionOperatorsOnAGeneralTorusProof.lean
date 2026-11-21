import YangMills.Construction.SeparatedSequences.ClassExpansionOperatorsOnAGeneralTorus
import YangMills.Construction.SeparatedSequences.ClassExpansionsOnAGeneralTorus
import YangMills.Construction.SeparatedSequences.ClassProjectionsInWeightedDataProof
import YangMills.Construction.Torus.ScalarProductsTransposesAndProjectionsOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice.DirichletOperators GeneralTorus
namespace SeparatedClasses.GaugeCoarseOperatorsOfClass
open SingleSequence SingleSequence.SequenceData
section PairingOff
variable {X X' : Type} {R : X → X' → Prop}
def equivOfPairsUniquely (hR : PairsUniquely R) : X ≃ X' :=
  Equiv.ofBijective (fun x => (hR.1 x).choose)
    ⟨fun x y hxy => by
        have hx := (hR.1 x).choose_spec.1
        have hy := (hR.1 y).choose_spec.1
        simp only at hxy
        rw [← hxy] at hy
        exact (hR.2 _).unique hx hy,
      fun x' => by
        obtain ⟨x, hx, -⟩ := hR.2 x'
        exact ⟨x, ((hR.1 x).choose_spec.2 x' hx).symm⟩⟩
theorem rel_equivOfPairsUniquely (hR : PairsUniquely R) (x : X) :
    R x (equivOfPairsUniquely hR x) := (hR.1 x).choose_spec.1
theorem equivOfPairsUniquely_eq (hR : PairsUniquely R) {x : X} {x' : X'} (hx : R x x') :
    equivOfPairsUniquely hR x = x' :=
  (hR.1 x).unique (rel_equivOfPairsUniquely hR x) hx
def funCongrOfPairs (hR : PairsUniquely R) : (X → ℝ) ≃ₗ[ℝ] (X' → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (equivOfPairsUniquely hR).symm
theorem funCongrOfPairs_apply (hR : PairsUniquely R) (f : X → ℝ) (x' : X') :
    funCongrOfPairs hR f x' = f ((equivOfPairsUniquely hR).symm x') := rfl
theorem agreeAlong_funCongrOfPairs (hR : PairsUniquely R) (f : X → ℝ) :
    AgreeAlong R f (funCongrOfPairs hR f) := by
  intro x x' hx
  rw [funCongrOfPairs_apply, ← equivOfPairsUniquely_eq hR hx, Equiv.symm_apply_apply]
theorem eq_funCongrOfPairs (hR : PairsUniquely R) {f : X → ℝ} {f' : X' → ℝ}
    (hf : AgreeAlong R f f') : f' = funCongrOfPairs hR f := by
  funext x'
  rw [funCongrOfPairs_apply]
  refine (hf _ x' ?_).symm
  have := rel_equivOfPairsUniquely hR ((equivOfPairsUniquely hR).symm x')
  rwa [Equiv.apply_symm_apply] at this
theorem map_funCongrOfPairs (hR : PairsUniquely R) {E : Submodule ℝ (X → ℝ)}
    {E' : Submodule ℝ (X' → ℝ)}
    (hE : SpacesCorrespond R (E : Set (X → ℝ)) (E' : Set (X' → ℝ))) :
    E.map ((funCongrOfPairs hR : (X → ℝ) ≃ₗ[ℝ] (X' → ℝ)) :
      (X → ℝ) →ₛₗ[RingHom.id ℝ] (X' → ℝ)) = E' := by
  ext f'
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨g', hg', hfg⟩ := hE.1 f hf
    have := eq_funCongrOfPairs hR hfg
    simpa [← this] using hg'
  · intro hf'
    obtain ⟨f, hf, hfg⟩ := hE.2 f' hf'
    exact ⟨f, hf, (eq_funCongrOfPairs hR hfg).symm⟩
theorem extendByZero_coe {Y : Type} (E : Submodule ℝ (X → ℝ)) (T : ↥E → Y → ℝ) (v : ↥E) :
    extendByZero E T v = T v := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.extendByZero_coe <;> assumption
end PairingOff
section Carrying
variable {V V' U U' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']
  [AddCommGroup U] [Module ℝ U] [AddCommGroup U'] [Module ℝ U']
theorem ringInverse_conj (ψ : U ≃ₗ[ℝ] U') {A : Module.End ℝ U} {A' : Module.End ℝ U'}
    (hA' : ∀ u, ψ (A u) = A' (ψ u)) (u : U) :
    ψ (Ring.inverse A u) = Ring.inverse A' (ψ u) := by
  have hA : A' = ψ.conjRingEquiv A := by
    ext v
    have := hA' (ψ.symm v)
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [LinearEquiv.conjRingEquiv, this]
  have hinv : Ring.inverse A' = ψ.conjRingEquiv (Ring.inverse A) := by
    rw [hA]
    by_cases hu : IsUnit A
    · obtain ⟨w, rfl⟩ := hu
      have : ψ.conjRingEquiv (w : Module.End ℝ U) = ((Units.map (ψ.conjRingEquiv : Module.End ℝ U →* Module.End ℝ U') w : (Module.End ℝ U')ˣ) : Module.End ℝ U') := rfl
      rw [this, Ring.inverse_unit, Ring.inverse_unit, ← map_inv]
      rfl
    · have hu' : ¬IsUnit (ψ.conjRingEquiv A) :=
        fun h' => hu ((isUnit_map_iff ψ.conjRingEquiv A).1 h')
      rw [Ring.inverse_non_unit _ hu, Ring.inverse_non_unit _ hu', map_zero]
  rw [hinv]
  simp [LinearEquiv.conjRingEquiv]
variable (φ : V ≃ₗ[ℝ] V') (ψ : U ≃ₗ[ℝ] U') {p : V → V → ℝ} {q : U → U → ℝ} {p' : V' → V' → ℝ}
  {q' : U' → U' → ℝ} {K : V →ₗ[ℝ] U} {K' : V' →ₗ[ℝ] U'} {T : U →ₗ[ℝ] V} {T' : U' →ₗ[ℝ] V'}
include φ ψ in
theorem exists_adjoint_of_conj (hp : ∀ a b, p a b = p' (φ a) (φ b))
    (hq : ∀ a b, q a b = q' (ψ a) (ψ b)) (hp' : IsInnerProductForm p')
    (hq' : IsInnerProductForm q')
    (hK : ∀ a, ψ (K a) = K' (φ a)) (hT' : ∀ v u, q' (K' v) u = p' v (T' u)) :
    ∃ T₀ : U →ₗ[ℝ] V, ∀ f g, q g (K f) = p (T₀ g) f := by
  refine ⟨φ.symm.toLinearMap ∘ₗ T' ∘ₗ ψ.toLinearMap, fun f g => ?_⟩
  rw [hq, hK, hq'.symm, hT', hp]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact hp'.symm _ _
include φ ψ in
theorem adjoint_conj (hp : ∀ a b, p a b = p' (φ a) (φ b))
    (hq : ∀ a b, q a b = q' (ψ a) (ψ b)) (hp' : IsInnerProductForm p')
    (hq' : IsInnerProductForm q')
    (hK : ∀ a, ψ (K a) = K' (φ a)) (hT' : ∀ v u, q' (K' v) u = p' v (T' u))
    (hT : ∀ f g, q g (K f) = p (T g) f) (u : U) : φ (T u) = T' (ψ u) := by
  have key : ∀ v : V', p' (φ (T u) - T' (ψ u)) v = 0 := by
    intro v
    have h1 := hT (φ.symm v) u
    rw [hq, hK, hp, LinearEquiv.apply_symm_apply, hq'.symm, hT', hp'.symm] at h1
    rw [hp'.sub_left, h1, sub_self]
  have := hp'.eq_zero_of_self_eq_zero _ (key _)
  exact sub_eq_zero.mp this
end Carrying
section Objects
variable {X X' Y Y' : Type} {R : X → X' → Prop} {S : Y → Y' → Prop}
  {E : Submodule ℝ (X → ℝ)} {E' : Submodule ℝ (X' → ℝ)}
  {p : (X → ℝ) → (X → ℝ) → ℝ} {p' : (X' → ℝ) → (X' → ℝ) → ℝ}
  {q : (Y → ℝ) → (Y → ℝ) → ℝ} {q' : (Y' → ℝ) → (Y' → ℝ) → ℝ}
  {Q : ↥E →ₗ[ℝ] (Y → ℝ)} {Q' : ↥E' →ₗ[ℝ] (Y' → ℝ)}
  {G : Module.End ℝ ↥E} {G' : Module.End ℝ ↥E'}
  {T : (Y → ℝ) →ₗ[ℝ] ↥E} {T' : (Y' → ℝ) →ₗ[ℝ] ↥E'}
theorem operatorsCorrespond_of_correspond (hR : PairsUniquely R) (hS : PairsUniquely S)
    (hE : SpacesCorrespond R (E : Set (X → ℝ)) (E' : Set (X' → ℝ)))
    (hp : PairingsCorrespond R (E : Set (X → ℝ)) (E' : Set (X' → ℝ)) p p')
    (hq : PairingsCorrespond S univ univ q q')
    (hp' : IsInnerProductForm fun a b : ↥E' => p' a b) (hq' : IsInnerProductForm q')
    (hQ : OperatorsCorrespond R S (E : Set (X → ℝ)) (E' : Set (X' → ℝ))
      (extendByZero E fun a => Q a) (extendByZero E' fun a => Q' a))
    (hG : OperatorsCorrespond R R (E : Set (X → ℝ)) (E' : Set (X' → ℝ))
      (extendByZero E fun a => (G a).1) (extendByZero E' fun a => (G' a).1))
    (hT' : ∀ v u, q' (Q' v) u = p' v (T' u))
    (hT : (∃ T₀ : (Y → ℝ) →ₗ[ℝ] ↥E, ∀ f g, q g (Q f) = p (T₀ g) f) →
      ∀ f g, q g (Q f) = p (T g) f) :
    OperatorsCorrespond S S univ univ (Q ∘ₗ G ∘ₗ T : Module.End ℝ (Y → ℝ))
      (Q' ∘ₗ G' ∘ₗ T' : Module.End ℝ (Y' → ℝ)) ∧
    OperatorsCorrespond S S univ univ
      (⇑(Ring.inverse (Q ∘ₗ G ∘ₗ T : Module.End ℝ (Y → ℝ)) : Module.End ℝ (Y → ℝ)))
      (⇑(Ring.inverse (Q' ∘ₗ G' ∘ₗ T' : Module.End ℝ (Y' → ℝ)) : Module.End ℝ (Y' → ℝ))) ∧
    OperatorsCorrespond S R univ univ
      (fun B => ((G ∘ₗ T ∘ₗ Ring.inverse (Q ∘ₗ G ∘ₗ T : Module.End ℝ (Y → ℝ))) B).1)
      (fun B => ((G' ∘ₗ T' ∘ₗ Ring.inverse (Q' ∘ₗ G' ∘ₗ T' : Module.End ℝ (Y' → ℝ))) B).1) := by
  set eX := funCongrOfPairs hR with heX
  set ψ := funCongrOfPairs hS with hψ
  let φ : ↥E ≃ₗ[ℝ] ↥E' := eX.ofSubmodules E E' (map_funCongrOfPairs hR hE)
  have hφ : ∀ a : ↥E, ((φ a : ↥E') : X' → ℝ) = eX a := fun a => rfl
  have agreeφ : ∀ a : ↥E, AgreeAlong R (a : X → ℝ) (φ a : X' → ℝ) := fun a => by
    rw [hφ]
    exact agreeAlong_funCongrOfPairs hR a
  have hp2 : ∀ a b : ↥E, p a b = p' (φ a) (φ b) := fun a b =>
    hp a a.2 b b.2 (φ a) (φ a).2 (φ b) (φ b).2 (agreeφ a) (agreeφ b)
  have hq2 : ∀ a b, q a b = q' (ψ a) (ψ b) := fun a b =>
    hq a trivial b trivial _ trivial _ trivial (agreeAlong_funCongrOfPairs hS a)
      (agreeAlong_funCongrOfPairs hS b)
  have hK : ∀ a, ψ (Q a) = Q' (φ a) := fun a => by
    have h := hQ a a.2 (φ a) (φ a).2 (agreeφ a)
    rw [extendByZero_coe E, extendByZero_coe E'] at h
    exact (eq_funCongrOfPairs hS h).symm
  have hGφ : ∀ a, φ (G a) = G' (φ a) := fun a => by
    have h := hG a a.2 (φ a) (φ a).2 (agreeφ a)
    rw [extendByZero_coe E, extendByZero_coe E'] at h
    exact Subtype.ext ((eq_funCongrOfPairs hR h).symm)
  have hadj := hT (exists_adjoint_of_conj φ ψ (p := fun a b : ↥E => p a b) hp2 hq2 hp' hq' hK hT')
  have hTφ : ∀ u, φ (T u) = T' (ψ u) :=
    adjoint_conj φ ψ (p := fun a b : ↥E => p a b) hp2 hq2 hp' hq' hK hT' hadj
  have hZ : ∀ u, ψ ((Q ∘ₗ G ∘ₗ T : Module.End ℝ (Y → ℝ)) u) =
      (Q' ∘ₗ G' ∘ₗ T' : Module.End ℝ (Y' → ℝ)) (ψ u) := fun u => by
    simp only [LinearMap.comp_apply]
    rw [hK, hGφ, hTφ]
  have hZi := ringInverse_conj ψ hZ
  have hH : ∀ u, φ ((G ∘ₗ T ∘ₗ Ring.inverse (Q ∘ₗ G ∘ₗ T : Module.End ℝ (Y → ℝ))) u) =
      (G' ∘ₗ T' ∘ₗ Ring.inverse (Q' ∘ₗ G' ∘ₗ T' : Module.End ℝ (Y' → ℝ))) (ψ u) := fun u => by
    simp only [LinearMap.comp_apply]
    rw [hGφ, hTφ, hZi]
  refine ⟨?_, ?_, ?_⟩
  · intro f _ f' _ hf
    rw [eq_funCongrOfPairs hS hf, ← hZ]
    exact agreeAlong_funCongrOfPairs hS _
  · intro f _ f' _ hf
    rw [eq_funCongrOfPairs hS hf, ← hZi]
    exact agreeAlong_funCongrOfPairs hS _
  · intro f _ f' _ hf
    rw [eq_funCongrOfPairs hS hf]
    simp only
    rw [← hH, hφ]
    exact agreeAlong_funCongrOfPairs hR _
end Objects
theorem coarseOneInner_eq_finsum (D : SeparatedSequences.BaseParameters) (Ω : ℕ → Set D.Torus)
    (φ : BondFrame) (B B' : D.CoarseOneForms Ω φ) :
    D.coarseOneInner Ω φ B B' =
      ∑ᶠ c : ↥(D.principalBonds Ω φ), D.levelMeshRatio c.1.1 ^ 4 * (B c * B' c) := by
  classical
  let e : (Σ n : Fin (D.t + 1), ↥(D.layerBondSet Ω φ n)) ≃ ↥(D.principalBonds Ω φ) :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Nat.lt_succ_iff.mp x.1.2, x.2.2⟩
      invFun := fun c => ⟨⟨c.1.1, Nat.lt_succ_iff.mpr c.2.1⟩, ⟨c.1.2, c.2.2⟩⟩
      left_inv := by rintro ⟨n, c⟩; rfl
      right_inv := by rintro ⟨⟨n, c⟩, h⟩; rfl }
  rw [← finsum_comp_equiv e]
  let _ : ∀ n : ℕ, Fintype ↥(D.layerBondSet Ω φ n) := fun n => Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Fintype.sum_sigma]
  simp only [SeparatedSequences.BaseParameters.coarseOneInner]
  rw [← Fin.sum_univ_eq_sum_range
    (fun n => D.levelMeshRatio n ^ SeparatedSequences.BaseParameters.dimension *
      ∑ᶠ c : ↥(D.layerBondSet Ω φ n), SeparatedSequences.BaseParameters.principalBondValue B ⟨n, c.1⟩ *
        SeparatedSequences.BaseParameters.principalBondValue B' ⟨n, c.1⟩) (D.t + 1)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc : (⟨(n : ℕ), c.1⟩ : Σ k : ℕ, D.LevelBond k) ∈ D.principalBonds Ω φ :=
    ⟨Nat.lt_succ_iff.mp n.2, c.2⟩
  simp only [SeparatedSequences.BaseParameters.principalBondValue, dif_pos hc]
  rfl
variable (s : SequenceData) {W : GeneralTorus.GaugeSetting}
theorem levelSpacing_eq (hs : s.IsGaugeSetting W) (n : ℕ) :
    W.data.levelSpacing n = s.params.levelMeshRatio n := by
  rw [hs.data_eq]
  have hL : (s.data.L : ℝ) ≠ 0 := by
    have := s.data.isAdmissible.2
    exact_mod_cast (by omega : s.data.L ≠ 0)
  simp only [GeneralTorus.ScaleData.levelSpacing, GeneralTorus.physicalInLevelUnits,
    SeparatedSequences.BaseParameters.levelMeshRatio, SeparatedSequences.ScaleData.levelMesh]
  rw [sub_eq_add_neg, zpow_add₀ hL, zpow_natCast]
theorem level_eq_of_rowRel {r : s.data.Point → W.data.Space} {c : s.oneFormData.WilsonWeightSeriesExpansion}
    {c' : (oneFormDataOfGauge W).WilsonWeightSeriesExpansion}
    (h : s.oneFormData.RowRel (oneFormDataOfGauge W) r c c') :
    c.1.1 = GaugeSetting.coarseLevel c' := congrArg Prod.fst h
theorem coarseSpacing_of_rowRel (hs : s.IsGaugeSetting W) {r : s.data.Point → W.data.Space}
    {c : s.oneFormData.WilsonWeightSeriesExpansion} {c' : (oneFormDataOfGauge W).WilsonWeightSeriesExpansion}
    (h : s.oneFormData.RowRel (oneFormDataOfGauge W) r c c') :
    GaugeSetting.coarseSpacing c' = s.params.levelMeshRatio c.1.1 := by
  rw [level_eq_of_rowRel s h]
  exact levelSpacing_eq s hs _
theorem statement_holds (hRows : SingleSequence.GaugeOneFormsCorrespond)
    (hInner : GeneralTorus.InnerProductsAdjointsProjections.SettingInnerProductFacts) :
    Statement := by
  intro s W hs
  have same := hRows s W hs
  obtain ⟨-, -, -, hrow, -, hform, -, hadjoint, -⟩ := hInner W
  have hR := same.forms.bonds
  have hS := same.standingConstraints
  have hpair : PairingsCorrespond
      (s.oneFormData.RowRel (oneFormDataOfGauge W) (s.toTorus W.data.torusSide))
      univ univ (s.params.coarseOneInner s.Ω s.frame) W.coarseInner := by
    intro f _ g _ f' _ g' _ hf hg
    refine (coarseOneInner_eq_finsum s.params s.Ω s.frame f g).trans ?_
    unfold GeneralTorus.GaugeSetting.coarseInner
    refine Eq.trans ?_ (finsum_comp_equiv (equivOfPairsUniquely hS)
      (f := fun c : W.CoarseBond => GaugeSetting.coarseSpacing c ^ 4 * (f' c * g' c)))
    refine finsum_congr fun c => ?_
    have hc := rel_equivOfPairsUniquely hS c
    have hξ : GaugeSetting.coarseSpacing (W := W) (equivOfPairsUniquely hS c) =
        s.params.levelMeshRatio c.1.1 :=
      coarseSpacing_of_rowRel s hs hc
    change _ = GaugeSetting.coarseSpacing (W := W) (equivOfPairsUniquely hS c) ^ 4 *
      (f' (equivOfPairsUniquely hS c) * g' (equivOfPairsUniquely hS c))
    rw [hξ, ← hf c _ hc, ← hg c _ hc]
  obtain ⟨hZ, hZi, hH⟩ := operatorsCorrespond_of_correspond
    (T := s.params.averageOneAdjoint s.Ω s.frame)
    (T' := W.meanOpAdjoint) (Q := s.params.averageOne s.Ω s.frame) (Q' := W.meanOp)
    (G := s.params.oneGreen s.Ω s.frame) (G' := W.greenOp)
    hR hS same.forms.space same.forms.inner hpair hform hrow same.avg same.inv hadjoint
    (fun h => Classical.epsilon_spec
      (p := FiniteDimReal.IsAdjointFor (s.params.restrictedOneInner s.Ω s.frame)
        (s.params.coarseOneInner s.Ω s.frame) (s.params.averageOne s.Ω s.frame)) h)
  refine ⟨hpair, ?_, hZ, hZi, hH⟩
  intro f _ f' _ hf c c' hc
  have hlevel := coarseSpacing_of_rowRel s hs hc
  change s.params.a * (s.params.bondMesh c.1 ^ 2)⁻¹ * f c =
    W.mass * (GaugeSetting.coarseSpacing c' ^ 2)⁻¹ * f' c'
  rw [hlevel, hs.mass_eq, hf c c' hc]
  rfl
end SeparatedClasses.GaugeCoarseOperatorsOfClass
end YangMills.Construction
