import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.ReflectionPositivity.CentredMomentsAreSumsOfCumulantsProof
import YangMills.Construction.ReflectionPositivity.ConnectedFunctionsAtOneCutoff
import YangMills.Construction.ReflectionPositivity.TransportOfFunctionsAndTuplesToTheTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.ConnectedAtCutoff
theorem mixedCumulant_congr_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    {X Y : Fin n → Ω → ℝ} (hXY : ∀ i, X i =ᵐ[μ] Y i) :
    Cumulants.mixedCumulant μ X = Cumulants.mixedCumulant μ Y := by apply _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.CentredMomentExpansion.mixedCumulant_congr_ae <;> assumption
theorem mixedCumulant_realSymmLinear
    (hrel : Cumulants.CumulantMomentRelations)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n)
    (x : Fin n → Ω → ℝ) (hx : ∀ i, Probability.IsBoundedRealRV (x i)) :
    MixedCumulantRealSymmLinear μ x := by
  have base := fun (y : Fin n → Ω → ℝ) (y' : Ω → ℝ)
      (hy : ∀ i, Probability.IsBoundedRealRV (y i))
      (hy' : Probability.IsBoundedRealRV y') =>
    (hrel Ω μ 0 Fin.elim0 (fun i => i.elim0)).1 n y y' hn hy hy'
  have i₀ : Fin n := ⟨0, hn⟩
  refine ⟨(base x (x i₀) hx (hx i₀)).1, (base x (x i₀) hx (hx i₀)).2.1,
    fun i y y' a a' hy hy' => ?_⟩
  have hupd : ∀ j, Probability.IsBoundedRealRV (Function.update x i y j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa using hy
    · simpa [Function.update_of_ne hj] using hx j
  have hlin := (base (Function.update x i y) y' hupd hy').2.2 i a a'
  simp only [Function.update_self, Function.update_idem] at hlin
  exact hlin
variable (D : MirrorData)
theorem exists_boundedRV_ae_eq (hprod : D.FieldSpaceIsProduct)
    (hbd : D.EnergiesBoundedAndMeasureProbability) (f : D.Torus → ℝ) :
    ∃ X : D.BondField → ℝ, Probability.IsBoundedRealRV X ∧
      X =ᵐ[PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling]
        PeriodicLattice.smearedObservable f := by apply _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.CentredMomentExpansion.exists_boundedRV_ae_eq <;> assumption
theorem smearedObservable_linComb (hF : Finite D.Face) (g h : D.Torus → ℝ) (a b : ℝ)
    (U : D.BondField) :
    PeriodicLattice.smearedObservable (a • g + b • h) U =
      a * PeriodicLattice.smearedObservable g U + b * PeriodicLattice.smearedObservable h U := by
  have : Fintype (PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ)) := @Fintype.ofFinite _ hF
  simp only [PeriodicLattice.smearedObservable, finsum_eq_sum_of_fintype, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem connectedSchwinger_real_symm_linear (hrel : Cumulants.CumulantMomentRelations)
    (hprod : D.FieldSpaceIsProduct) (hbd : D.EnergiesBoundedAndMeasureProbability) {n : ℕ}
    (hn : 1 ≤ n) (f : Fin n → D.Torus → ℝ) :
    (SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling f).im = 0 ∧
    (∀ σ : Equiv.Perm (Fin n),
      SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling (fun i => f (σ i)) =
        SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling f) ∧
    ∀ (i : Fin n) (g h : D.Torus → ℝ) (a b : ℝ),
      SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling
          (Function.update f i (a • g + b • h)) =
        (a : ℂ) * SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling
            (Function.update f i g) +
          (b : ℂ) * SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling
            (Function.update f i h) := by
  have : IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) :=
    hbd.2.2.2.2.2.2.2.2.2.2.1
  have hcon : ∀ (F : Fin n → D.Torus → ℝ) (X : Fin n → D.BondField → ℝ),
      (∀ i, X i =ᵐ[PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling]
        PeriodicLattice.smearedObservable (F i)) →
      SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling F =
        Cumulants.mixedCumulant (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) X :=
    fun F X hX => (mixedCumulant_congr_ae hX).symm
  choose Y hY hYae using exists_boundedRV_ae_eq D hprod hbd
  have hS := mixedCumulant_realSymmLinear hrel
    (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) hn (fun i => Y (f i))
    (fun i => hY (f i))
  have hupd : ∀ (i : Fin n) (g : D.Torus → ℝ) (X : D.BondField → ℝ),
      X =ᵐ[PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling]
        PeriodicLattice.smearedObservable g →
      SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling (Function.update f i g) =
        Cumulants.mixedCumulant (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling)
          (Function.update (fun i => Y (f i)) i X) := by
    intro i g X hX
    refine hcon _ _ fun j => ?_
    by_cases hj : j = i
    · subst hj
      simpa using hX
    · simpa [Function.update_of_ne hj] using hYae (f j)
  refine ⟨?_, fun σ => ?_, fun i g h a b => ?_⟩
  · rw [hcon f (fun i => Y (f i)) fun i => hYae (f i)]
    exact hS.1
  · rw [hcon f (fun i => Y (f i)) fun i => hYae (f i),
      hcon _ (fun i => Y (f (σ i))) fun i => hYae (f (σ i))]
    exact hS.2.1 σ
  · have hsum : a • Y g + b • Y h =ᵐ[PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling]
        PeriodicLattice.smearedObservable (a • g + b • h) := by
      filter_upwards [hYae g, hYae h] with U h₁ h₂
      rw [smearedObservable_linComb D hprod.2.2.1 g h a b U]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h₁, h₂]
    rw [hupd i _ _ hsum, hupd i g _ (hYae g), hupd i h _ (hYae h)]
    exact hS.2.2 i (Y g) (Y h) a b (hY g) (hY h)
theorem connectedSchwinger_re_of_linComb (hrel : Cumulants.CumulantMomentRelations)
    (hprod : D.FieldSpaceIsProduct) (hbd : D.EnergiesBoundedAndMeasureProbability) {n : ℕ}
    (i : Fin n) (a b : ℝ) (x y z : Fin n → D.Torus → ℝ) (hy : ∀ j, j ≠ i → y j = x j)
    (hz : ∀ j, j ≠ i → z j = x j) (hi : z i = a • x i + b • y i) :
    (SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling z).re =
      a * (SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling x).re +
        b * (SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling y).re := by
  have ez : z = Function.update x i (a • x i + b • y i) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simpa using hi
    · simpa [Function.update_of_ne hj] using hz j hj
  have ey : y = Function.update x i (y i) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simpa [Function.update_of_ne hj] using hy j hj
  have ex : Function.update x i (x i) = x := Function.update_eq_self i x
  have hlin := (connectedSchwinger_real_symm_linear D hrel hprod hbd (n := n)
    (Nat.succ_le_of_lt i.pos) x).2.2 i (x i) (y i) a b
  rw [← ez, ← ey, ex] at hlin
  rw [hlin]
  simp
theorem connectedSchwingerR4_isRealForm
    (hrel : Cumulants.CumulantMomentRelations)
    (hprod : D.FieldSpaceIsProduct) (hbd : D.EnergiesBoundedAndMeasureProbability)
    (hsp : LimitSpaces.Ambient.testSpacesAndSepTuples)
    (hper : LimitSpaces.Periodization.Properties)
    {n : ℕ} (hn : 2 ≤ n) (A : Fin n → Set (Fin 4 → ℝ))
    (hd : TestFunctions.HasDiameterLE (⋃ i, A i) (PeriodicLattice.torusSide D.L D.m / 2)) :
    ConnectedOfPeriodizedIsRealForm D A := by
  have hn1 : 1 ≤ n := by omega
  have hW : ∀ i, ∃ W : Submodule ℝ ((Fin 4 → ℝ) → ℝ), (W : Set ((Fin 4 → ℝ) → ℝ)) =
      LimitSpaces.Ambient.euclidean.lipWithin D.toStandingParameters (A i) := fun i =>
    (hsp D.toStandingParameters .euclidean ⟨1, Set.self_mem_Ici⟩ (A i) (A i) n hn1).1.1
  choose V hV using hW
  have hsupp : ∀ (i : Fin n) (u : V i),
      LimitSpaces.Ambient.euclidean.SupportedWithin D.toStandingParameters (⋃ i, A i)
        (u : (Fin 4 → ℝ) → ℝ) := by
    intro i u
    have hu : (u : (Fin 4 → ℝ) → ℝ) ∈
        LimitSpaces.Ambient.euclidean.lipWithin D.toStandingParameters (A i) := by
      rw [← hV i]
      exact u.2
    exact ⟨hu.2.1, hu.2.2.trans (subset_iUnion A i)⟩
  have hlin : ∀ (i : Fin n) (u v : V i) (a b : ℝ),
      TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m)
          (a • (u : (Fin 4 → ℝ) → ℝ) + b • (v : (Fin 4 → ℝ) → ℝ)) =
        a • TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) (u : (Fin 4 → ℝ) → ℝ) +
          b • TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m)
            (v : (Fin 4 → ℝ) → ℝ) :=
    fun i u v a b =>
      ((hper ⟨D.toStandingParameters, D.coupling, D.coupling_pos⟩).1 (⋃ i, A i) u v hd
        (hsupp i u) (hsupp i v)).2.2.1 a b
  have hper' : ∀ (h : (i : Fin n) → V i) (i : Fin n) (w : V i),
      SchwingerFunctions.periodizeAll D.L D.m
          (fun k => ((Function.update h i w k : V k) : (Fin 4 → ℝ) → ℝ)) =
        Function.update (SchwingerFunctions.periodizeAll D.L D.m
            fun k => (h k : (Fin 4 → ℝ) → ℝ)) i
          (TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) (w : (Fin 4 → ℝ) → ℝ)) := by
    intro h i w
    funext k
    by_cases hk : k = i
    · subst hk
      simp [SchwingerFunctions.periodizeAll]
    · simp [SchwingerFunctions.periodizeAll, Function.update_of_ne hk]
  have hform : ∀ (h : (i : Fin n) → V i) (i : Fin n) (w u v : V i) (a b : ℝ),
      (w : (Fin 4 → ℝ) → ℝ) = a • (u : (Fin 4 → ℝ) → ℝ) + b • (v : (Fin 4 → ℝ) → ℝ) →
      (SchwingerFunctions.connectedSchwingerR4 D.L D.m D.K D.coupling
          fun k => ((Function.update h i w k : V k) : (Fin 4 → ℝ) → ℝ)).re =
        a * (SchwingerFunctions.connectedSchwingerR4 D.L D.m D.K D.coupling
          fun k => ((Function.update h i u k : V k) : (Fin 4 → ℝ) → ℝ)).re +
        b * (SchwingerFunctions.connectedSchwingerR4 D.L D.m D.K D.coupling
          fun k => ((Function.update h i v k : V k) : (Fin 4 → ℝ) → ℝ)).re := by
    intro h i w u v a b hw
    simp only [SchwingerFunctions.connectedSchwingerR4]
    rw [hper' h i w, hper' h i u, hper' h i v, hw, hlin i u v a b]
    have hc := (connectedSchwinger_real_symm_linear D hrel hprod hbd hn1
      (SchwingerFunctions.periodizeAll D.L D.m fun k => (h k : (Fin 4 → ℝ) → ℝ))).2.2 i
      (TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) (u : (Fin 4 → ℝ) → ℝ))
      (TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) (v : (Fin 4 → ℝ) → ℝ)) a b
    rw [hc]
    simp
  refine ⟨V, { toFun := fun h => (SchwingerFunctions.connectedSchwingerR4 D.L D.m D.K D.coupling
                  fun k => (h k : (Fin 4 → ℝ) → ℝ)).re
               map_update_add' := ?_, map_update_smul' := ?_ }, fun i => hV i, fun h => ?_⟩
  · intro inst h i u v
    obtain rfl := Subsingleton.elim inst (instDecidableEqFin n)
    have hc := hform h i (u + v) u v 1 1 (by simp)
    simpa using hc
  · intro inst h i c u
    obtain rfl := Subsingleton.elim inst (instDecidableEqFin n)
    have hc := hform h i (c • u) u u c 0 (by simp)
    simpa using hc
  · refine Complex.ext ?_ ?_
    · simp
    · rw [Complex.ofReal_im]
      exact (connectedSchwinger_real_symm_linear D hrel hprod hbd hn1
        (SchwingerFunctions.periodizeAll D.L D.m fun k => (h k : (Fin 4 → ℝ) → ℝ))).1.symm
theorem statement_holds (h₁ : Cumulants.CumulantMomentRelations)
    (h₂ : FieldSpaceAndFaceEnergies.Statement)
    (h₃ : CentredMomentCumulantExpansion)
    (h₄ : InfiniteLattice.CenteredIdentity.Statement)
    (h₅ : LimitSpaces.Ambient.testSpacesAndSepTuples)
    (h₆ : LimitSpaces.Periodization.Properties) : Statement := by
  refine ⟨fun Ω _ μ _ n hn x hx => mixedCumulant_realSymmLinear h₁ μ hn x hx,
    fun D n hn => ?_, fun D q Z => ?_, fun D n hn A _ hd => ?_⟩
  · obtain ⟨hprod, -, hbd⟩ := h₂ D
    have hn1 : 1 ≤ n := by omega
    refine ⟨fun f _ => ?_, ⟨fun X => (connectedSchwinger_real_symm_linear D h₁ hprod hbd hn1 X.1).1,
      fun X σ => ?_, fun B _ _ i a b X Y Z _ _ _ hY hZ hi => ?_⟩,
      fun μ hμ => (h₄ D.toStandingParameters μ hμ).2.1 n hn⟩
    · have F := connectedSchwinger_real_symm_linear D h₁ hprod hbd hn1 f
      exact ⟨F.1, F.2.1, fun i g h a b _ _ => F.2.2 i g h a b⟩
    · exact congrArg Complex.re ((connectedSchwinger_real_symm_linear D h₁ hprod hbd hn1 X.1).2.1 σ)
    · exact connectedSchwinger_re_of_linComb D h₁ hprod hbd i a b X.1 Y.1 Z.1 hY hZ hi
  · have harg : MirrorData.IsAdmissibleArg (D := D) Z.1 :=
      ⟨fun l => (Z.2.1 l).1, fun l l' hne => Set.disjoint_iff_inter_eq_empty.mp (Z.2.2 hne)⟩
    exact (h₃.2 D q Z.1 harg).2
  · obtain ⟨hprod, -, hbd⟩ := h₂ D
    exact connectedSchwingerR4_isRealForm D h₁ hprod hbd h₅ h₆ hn A hd
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.ConnectedAtCutoff
end
