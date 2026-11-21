import YangMills.Construction.Lattice.CovarianceOfTheOneStepOperationsAtComplexConfigurations
import YangMills.Construction.Lattice.DomainsOfTheTwoSchemesProof
import YangMills.Construction.Lattice.EliminationFactorAtAnImageBond
import YangMills.Construction.Lattice.LinearisingCorrectionOfAFormedSet
import YangMills.Construction.Lattice.OneStepIdentitiesAtAnImageBond
import YangMills.Construction.Lattice.OneStepOperationsOfAnImageSet
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ComplexTransport Matrices Coordinates Matrices.GroupLieProduct
section CoordinateCharts
variable {α τ τ' E : Type}
private def familyEntriesEquiv {k : ℕ} (e : τ ≃ Fin k) : (τ → ComplexMatrix2) ≃ₗ[ℂ] ComplexCoordinates
    (ComplexCoordinates.productDim fun _ : Fin k => ComplexCoordinates.Component.matrix) :=
  { matrixPiEquiv e with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
private def familyOfCoordsLinear {iα : Fintype α} (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : α ≃ Fin (Fintype.card α)) :
    ComplexCoordinates (Fintype.card α * 3) →ₗ[ℂ] α → ComplexMatrix2 where
  toFun := tupleOfCoords b e
  map_add' w w' := by
    funext i
    simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, add_smul, Finset.sum_add_distrib]
  map_smul' c w := by
    funext i
    simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, mul_smul, Finset.smul_sum]
private theorem isHolomorphicIn_congr {n n' : ℕ} {O : Set (ComplexCoordinates n)}
    {f g : ComplexCoordinates n → ComplexCoordinates n'} (hf : ComplexCoordinates.IsHolomorphicIn O f)
    (h : ∀ w ∈ O, g w = f w) : ComplexCoordinates.IsHolomorphicIn O g := by apply _root_.YangMills.SharedProofs.p63802 <;> assumption
private theorem isHolomorphicIn_mono {n n' : ℕ} {O O' : Set (ComplexCoordinates n)}
    {f : ComplexCoordinates n → ComplexCoordinates n'} (hf : ComplexCoordinates.IsHolomorphicIn O f)
    (hO' : IsOpen O') (hsub : O' ⊆ O) : ComplexCoordinates.IsHolomorphicIn O' f :=
  ⟨hO', hf.2.1.mono hsub, fun a ha j => hf.2.2 a (hsub ha) j⟩
private theorem isHolomorphicIn_linearMap_comp {n n' n'' : ℕ} {O : Set (ComplexCoordinates n)}
    {f : ComplexCoordinates n → ComplexCoordinates n'} (hf : ComplexCoordinates.IsHolomorphicIn O f)
    (F : ComplexCoordinates n' →ₗ[ℂ] ComplexCoordinates n'') :
    ComplexCoordinates.IsHolomorphicIn O fun w => F (f w) := by
  obtain ⟨hO, hcont, hdiff⟩ := hf
  refine ⟨hO, (LinearMap.toContinuousLinearMap F).continuous.comp_continuousOn hcont, fun a ha j => ?_⟩
  filter_upwards [hdiff a ha j] with z hz
  exact (LinearMap.toContinuousLinearMap F).differentiableAt.comp z hz
private theorem isHolomorphicIn_linearMap {n n' : ℕ} {O : Set (ComplexCoordinates n)} (hO : IsOpen O)
    (F : ComplexCoordinates n →ₗ[ℂ] ComplexCoordinates n') :
    ComplexCoordinates.IsHolomorphicIn O fun w => F w := by
  refine ⟨hO, (LinearMap.toContinuousLinearMap F).continuous.continuousOn, fun a _ j => ?_⟩
  refine Eventually.of_forall fun z => ?_
  exact (LinearMap.toContinuousLinearMap F).differentiableAt.comp z (by fun_prop)
private theorem isHolomorphicIn_sub {n n' : ℕ} {O : Set (ComplexCoordinates n)}
    {f g : ComplexCoordinates n → ComplexCoordinates n'} (hf : ComplexCoordinates.IsHolomorphicIn O f)
    (hg : ComplexCoordinates.IsHolomorphicIn O g) :
    ComplexCoordinates.IsHolomorphicIn O fun w => f w - g w := by
  refine ⟨hf.1, hf.2.1.sub hg.2.1, fun a ha j => ?_⟩
  filter_upwards [hf.2.2 a ha j, hg.2.2 a ha j] with z hz₁ hz₂
  exact hz₁.sub hz₂
private theorem onTraceless_congr {iα : Fintype α} {l : ℕ} {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {e : E ≃ ComplexCoordinates l} {N : Set (α → ComplexMatrix2)} {f g : (α → ComplexMatrix2) → E}
    (hf : IsHolomorphicOnTraceless b e N f) (h : ∀ B ∈ N, g B = f B) :
    IsHolomorphicOnTraceless b e N g :=
  ⟨hf.1, fun μ => isHolomorphicIn_congr (hf.2 μ) fun _ hw => congrArg e (h _ hw)⟩
private theorem onTraceless_linearMap {iα : Fintype α} {k k' : ℕ}
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} (e : τ ≃ Fin k) (e' : τ' ≃ Fin k')
    {N : Set (α → ComplexMatrix2)} {f : (α → ComplexMatrix2) → τ → ComplexMatrix2}
    {g : (α → ComplexMatrix2) → τ' → ComplexMatrix2}
    (F : (τ → ComplexMatrix2) →ₗ[ℂ] τ' → ComplexMatrix2)
    (hf : IsHolomorphicOnTraceless b (matrixPiEquiv e) N f) (h : ∀ B ∈ N, g B = F (f B)) :
    IsHolomorphicOnTraceless b (matrixPiEquiv e') N g := by
  refine ⟨hf.1, fun μ => ?_⟩
  refine isHolomorphicIn_congr (isHolomorphicIn_linearMap_comp (hf.2 μ)
    ((familyEntriesEquiv e').toLinearMap ∘ₗ F ∘ₗ (familyEntriesEquiv e).symm.toLinearMap)) fun w hw => ?_
  have hback : (familyEntriesEquiv e).symm (matrixPiEquiv e (f (tupleOfCoords b μ w))) =
      f (tupleOfCoords b μ w) := (familyEntriesEquiv e).symm_apply_apply _
  show matrixPiEquiv e' (g (tupleOfCoords b μ w)) =
    matrixPiEquiv e' (F ((familyEntriesEquiv e).symm
      (matrixPiEquiv e (f (tupleOfCoords b μ w)))))
  rw [hback, h _ hw]
private theorem onTraceless_id {iα : Fintype α} {l k : ℕ} {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {e : E ≃ ComplexCoordinates l} (e₀ : α ≃ Fin k) {N : Set (α → ComplexMatrix2)} {f : (α → ComplexMatrix2) → E}
    (hf : IsHolomorphicOnTraceless b e N f) :
    IsHolomorphicOnTraceless b (matrixPiEquiv e₀) N fun B => B :=
  ⟨hf.1, fun μ => isHolomorphicIn_congr (isHolomorphicIn_linearMap (hf.2 μ).1
    ((familyEntriesEquiv e₀).toLinearMap ∘ₗ familyOfCoordsLinear b μ)) fun _ _ => rfl⟩
private theorem onTraceless_sub {iα : Fintype α} {k : ℕ} {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {e : τ ≃ Fin k} {N : Set (α → ComplexMatrix2)} {f g : (α → ComplexMatrix2) → τ → ComplexMatrix2}
    (hf : IsHolomorphicOnTraceless b (matrixPiEquiv e) N f)
    (hg : IsHolomorphicOnTraceless b (matrixPiEquiv e) N g) :
    IsHolomorphicOnTraceless b (matrixPiEquiv e) N fun B => f B - g B :=
  ⟨hf.1, fun μ => isHolomorphicIn_congr (isHolomorphicIn_sub (hf.2 μ) (hg.2 μ)) fun _ _ =>
    (familyEntriesEquiv e).map_sub _ _⟩
private theorem dist_lt_of_supNorm_sub_lt {iα : Fintype α} {s : ℝ} (hs : 0 < s) {A B : α → ComplexMatrix2}
    (h : supNorm (B - A) < s) : dist B A < s := by
  rw [dist_pi_lt_iff hs]
  intro i
  have hbdd : BddAbove (range fun i => ComplexMatrix2.operatorNorm ((B - A) i)) :=
    (Set.finite_range _).bddAbove
  rw [dist_eq_norm]
  exact (le_ciSup hbdd i).trans_lt h
private theorem onTraceless_inter_of_eq {iα : Fintype α} {l : ℕ}
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {e : E ≃ ComplexCoordinates l} {N U : Set (α → ComplexMatrix2)} {f g : (α → ComplexMatrix2) → E}
    (hg : IsHolomorphicOnTraceless b e N g) (hU : IsOpen U) (h : ∀ B ∈ N ∩ U, f B = g B) :
    IsHolomorphicOnTraceless b e (N ∩ U) f := by
  refine ⟨⟨inter_subset_left.trans hg.1.1, fun A hA => ?_⟩, fun μ => ?_⟩
  · obtain ⟨s, hs, hnear⟩ := hg.1.2 A hA.1
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU A hA.2
    refine ⟨min s ε, lt_min hs hε, fun B hBA hlt => ⟨hnear B hBA (hlt.trans_le (min_le_left _ _)), ?_⟩⟩
    exact hball (dist_lt_of_supNorm_sub_lt hε (hlt.trans_le (min_le_right _ _)))
  · have hcont : Continuous (tupleOfCoords b μ) :=
      (LinearMap.toContinuousLinearMap (familyOfCoordsLinear b μ)).continuous
    have hμ := hg.2 μ
    exact isHolomorphicIn_congr
      (isHolomorphicIn_mono hμ (hμ.1.inter (hU.preimage hcont)) inter_subset_left)
      fun _ hw => congrArg e (h _ hw)
private theorem isHolomorphicAtZero_congr {S : Set (α → ComplexMatrix2)} (hS : tracelessPi α ⊆ S)
    {f g : (α → ComplexMatrix2) → τ → ComplexMatrix2} (hg : IsHolomorphicAtZero g)
    (h : ∀ᶠ B in 𝓝[S] 0, f B = g B) : IsHolomorphicAtZero f := by
  obtain ⟨iα, iτ, N, h0, hN⟩ := hg
  obtain ⟨U, hU, h0U, hsub⟩ := mem_nhdsWithin.mp h
  refine ⟨iα, iτ, N ∩ U, ⟨h0, h0U⟩, fun b e => ?_⟩
  exact onTraceless_inter_of_eq (hN b e) hU fun B hB => hsub ⟨hB.2, hS ((hN b e).1.1 hB.1)⟩
end CoordinateCharts
section LinearOnValues
variable {L m : ℕ} {j j' : ℤ}
private def extendFormLinear (Γ : Set (Bond L m j)) :
    (SupportBond j' Γ → ComplexMatrix2) →ₗ[ℂ] Bond L m j' → ComplexMatrix2 where
  toFun := extendForm
  map_add' B B' := by
    funext b
    simp only [extendForm, Pi.add_apply]
    split_ifs <;> abel
  map_smul' c B := by
    funext b
    simp only [extendForm, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp
private def twistedFormValueLinear (σ : FourTorus L m ≃ FourTorus L m) (W : Bond L m j → ComplexMatrix2)
    (b' : Bond L m j) : (Bond L m j → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2 where
  toFun A := twistedFormValue σ W A b'
  map_add' A A' := by
    simp only [twistedFormValue, Pi.add_apply]
    split_ifs
    · rfl
    · simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul, neg_add]
  map_smul' c A := by
    simp only [twistedFormValue, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · rfl
    · simp only [ComplexMatrix2.conjugateBy, mul_smul_comm, smul_mul_assoc, smul_neg]
private def extendByZeroLinear (Γ : Set (Bond L m j)) :
    (↥Γ → ComplexMatrix2) →ₗ[ℂ] Bond L m j → ComplexMatrix2 where
  toFun u := Function.extend Subtype.val u 0
  map_add' u u' := by
    classical
    funext b
    simp only [Function.extend_def, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c u := by
    classical
    funext b
    simp only [Function.extend_def, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp
private theorem exists_linearMap_eq_pivotCoeffInv {V : Bond L m j' → ComplexMatrix2} {c : Bond L m j}
    (h : PivotCoeffInvertible V c) :
    ∃ R : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2, ∀ Y ∈ ComplexMatrix2.traceless, R Y = pivotCoeffInv V c Y := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨R, hR⟩ := LinearMap.exists_extend (ComplexMatrix2.traceless.subtype ∘ₗ T.symm.toLinearMap)
  refine ⟨R, fun Y hY => ?_⟩
  have hex : ∃ x ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2), pivotCoeff V c x = Y :=
    ⟨(T.symm ⟨Y, hY⟩ : ComplexMatrix2), (T.symm ⟨Y, hY⟩).2, by
      rw [← hT, LinearEquiv.apply_symm_apply]⟩
  have hmem : pivotCoeffInv V c Y ∈ ComplexMatrix2.traceless := Function.invFunOn_mem hex
  have hinv : pivotCoeff V c (pivotCoeffInv V c Y) = Y := Function.invFunOn_eq hex
  have hTY : T ⟨pivotCoeffInv V c Y, hmem⟩ = ⟨Y, hY⟩ :=
    Subtype.ext ((hT ⟨_, hmem⟩).trans hinv)
  have hsymm : T.symm ⟨Y, hY⟩ = ⟨pivotCoeffInv V c Y, hmem⟩ := by
    rw [← hTY, LinearEquiv.symm_apply_apply]
  have hRY : R Y = (T.symm ⟨Y, hY⟩ : ComplexMatrix2) := LinearMap.congr_fun hR ⟨Y, hY⟩
  rw [hRY, hsymm]
private theorem exists_linearMap_eq_pivotCorrectionLift {V : Bond L m j' → ComplexMatrix2}
    {Γ : Set (Bond L m j)} (h : ∀ c ∈ Γ, PivotCoeffInvertible V c) :
    ∃ H : (↥Γ → ComplexMatrix2) →ₗ[ℂ] SupportBond j' Γ → ComplexMatrix2,
      ∀ u ∈ tracelessPi ↥Γ, pivotCorrectionLift V Γ u = H u := by
  classical
  choose R hR using fun c : ↥Γ => exists_linearMap_eq_pivotCoeffInv (h c c.2)
  refine ⟨LinearMap.pi fun b => if h : ∃ c : ↥Γ, (b : Bond L m j') = pivot (c : Bond L m j)
    then ((L : ℂ)⁻¹) • (R h.choose ∘ₗ LinearMap.proj h.choose) else 0, fun u hu => ?_⟩
  funext b
  simp only [pivotCorrectionLift, LinearMap.pi_apply]
  by_cases hb : ∃ c : ↥Γ, (b : Bond L m j') = pivot (c : Bond L m j)
  · rw [dif_pos hb, dif_pos hb]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [hR _ _ (hu _)]
  · rw [dif_neg hb, dif_neg hb]
    rfl
end LinearOnValues
theorem complexStepIsometryCovariance_holds
    (hI : TransportIdentitiesAtImageBond)
    (hF : EliminationWeightAtImageBond)
    (hS : ImageSetIntertwining.Statement)
    (hC : LinearizingCorrectionExistsAndIsLocallyUnique) :
    ComplexStepIsometryCovariance := by
  intro L m i σ hL hm hi hσ K k hk hik Γ hpos V hV hV'
  have hD : ∀ c ∈ Γ, ∀ c', IsOrientedImage σ c c' →
      TransportIdentitiesAt σ V (complexBlockAverage V) c c' :=
    fun c hc c' hp => hI L m K k i σ hL hm hi hσ hk hik V _ c c' (hpos c hc) hp.1 hp.2
      (hV.defined c hc) (hV'.defined c' ⟨c, hc, hp⟩) rfl
  have hS' : IsometryIntertwinesStepMaps σ V (complexBlockAverage V) Γ (orientedImage σ Γ) :=
    hS L m K k i σ hL hm hi hσ hk hik V _ Γ _ hpos (fun _ => Iff.rfl) hV.defined
      hV.pivot_invertible hV'.defined hV'.pivot_invertible fun _ _ => rfl
  have htw : ∀ (W A : BondAtLevel L m K (k + 1) → ComplexMatrix2) (c' : BondAtLevel L m K (k + 1)),
      c'.IsPositivelyOriented → twistedTransportForm σ W A c' = twistedFormValue σ W A c' := by
    intro W A c' hc'
    simp only [twistedTransportForm, if_pos hc']
  obtain ⟨⟨N', D', -, ⟨iF', iΓ', -⟩, -⟩, -⟩ :=
    hC L m K k hL hm hk (transportGaugeField σ V) (orientedImage σ Γ)
      (fun c' ⟨_, _, hp⟩ => hp.1) hV'.defined hV'.pivot_invertible
  have hspec : ∃ N, IsLinearizingCorrection V Γ N (linearizingCorrection V Γ) := by
    obtain ⟨⟨N, D, hND⟩, -⟩ := hC L m K k hL hm hk V Γ hpos hV.defined hV.pivot_invertible
    exact Classical.epsilon_spec (p := fun D => ∃ N, IsLinearizingCorrection V Γ N D) ⟨D, N, hND⟩
  obtain ⟨N, h0, ⟨iF, iΓ, hhol⟩, hval, -, -⟩ := hspec
  let T : (SupportBond (levelDepth K k) Γ → ComplexMatrix2) →ₗ[ℂ]
      SupportBond (levelDepth K k) (orientedImage σ Γ) → ComplexMatrix2 :=
    LinearMap.pi (fun b' => twistedFormValueLinear σ V b'.1) ∘ₗ extendFormLinear Γ
  have hT : ∀ B, twistedTransportSupportForm σ V B = T B := by
    intro B
    funext b'
    simp only [twistedTransportSupportForm, twistedTransportForm, if_pos b'.2.2]
    rfl
  let S : (↥Γ → ComplexMatrix2) →ₗ[ℂ] ↥(orientedImage σ Γ) → ComplexMatrix2 :=
    LinearMap.pi (fun c' => twistedFormValueLinear σ (complexBlockAverage V) c'.1) ∘ₗ extendByZeroLinear Γ
  obtain ⟨H, hH⟩ := exists_linearMap_eq_pivotCorrectionLift (j' := levelDepth K k) hV.pivot_invertible
  have hsub : tracelessPi (SupportBond (levelDepth K k) Γ) ⊆
      (supportForms (levelDepth K k) Γ : Set (SupportBond (levelDepth K k) Γ → ComplexMatrix2)) :=
    fun B hB => Submodule.mem_pi.2 fun b _ => hB b
  have hright₁ : IsHolomorphicAtZero (fun B : SupportBond (levelDepth K k) Γ → ComplexMatrix2 =>
      twistedTransportCoarse σ (complexBlockAverage V) (linearizingCorrection V Γ B)) :=
    ⟨iF, iΓ', N, h0, fun b e' =>
      onTraceless_linearMap (@Fintype.equivFin _ iΓ) e' S (hhol b (@Fintype.equivFin _ iΓ)) fun _ _ => rfl⟩
  have hright₂ : IsHolomorphicAtZero (fun B : SupportBond (levelDepth K k) Γ → ComplexMatrix2 =>
      twistedTransportSupportForm σ V (linearizingChange V Γ B)) := by
    refine ⟨iF, iF', N, h0, fun b e' => ?_⟩
    have hD₀ := hhol b (@Fintype.equivFin _ iΓ)
    refine onTraceless_congr (onTraceless_sub
      (onTraceless_linearMap (@Fintype.equivFin _ iF) e' T (onTraceless_id (@Fintype.equivFin _ iF) hD₀)
        fun _ _ => rfl)
      (onTraceless_linearMap (@Fintype.equivFin _ iΓ) e' (T ∘ₗ H) hD₀ fun _ _ => rfl)) fun B hB => ?_
    rw [hT, linearizingChange, hH _ (hval B hB), map_sub]
    rfl
  have hcor : ∀ᶠ B in
      𝓝[(supportForms (levelDepth K k) Γ : Set (SupportBond (levelDepth K k) Γ → ComplexMatrix2))] 0,
      linearizingCorrection (transportGaugeField σ V) (orientedImage σ Γ)
          (twistedTransportSupportForm σ V B) =
        twistedTransportCoarse σ (complexBlockAverage V) (linearizingCorrection V Γ B) :=
    hS'.correction_comm
  have hchg : ∀ᶠ B in
      𝓝[(supportForms (levelDepth K k) Γ : Set (SupportBond (levelDepth K k) Γ → ComplexMatrix2))] 0,
      linearizingChange (transportGaugeField σ V) (orientedImage σ Γ)
          (twistedTransportSupportForm σ V B) =
        twistedTransportSupportForm σ V (linearizingChange V Γ B) :=
    hS'.change_comm
  exact
    { linearized_comm := fun A hA c' ⟨c, hc, hp⟩ => by
        rw [htw _ _ _ hp.1]
        exact (hD c hc c' hp).linearized A hA
      map_comm := fun B hB c hc c' hp h₁ h₂ => (hD c hc c' hp).constraint_map B hB h₁ h₂
      eliminate_comm := hS'.eliminate_comm
      lift_comm := hS'.pivotLift_comm
      correction_comm := hcor
      correction_holomorphic := ⟨isHolomorphicAtZero_congr hsub hright₁ hcor, hright₁⟩
      change_comm := hchg
      change_holomorphic := ⟨isHolomorphicAtZero_congr hsub hright₂ hchg, hright₂⟩
      pivotCoeff_conj := fun c hc c' hp X => (hD c hc c' hp).pivotCoeff_conj X
      weight_eq := fun c hc c' hp =>
        hF L m K k i σ hL hm hi hσ hk hik V c c' (hpos c hc) hp.1 hp.2
          (hV.defined c hc) (hV'.defined c' ⟨c, hc, hp⟩)
      bilinear_comm := fun B₁ B₂ h₁ h₂ c' ⟨c, hc, hp⟩ =>
        (hD c hc c' hp).bilinear B₁ B₂ h₁ h₂ }
end YangMills.Construction.PeriodicLattice
