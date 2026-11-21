import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlock
import YangMills.Construction.Lattice.LinearisedConstraintAtAFormedBond
import YangMills.Construction.Lattice.PropertiesOfTheTwoSchemes
import YangMills.Construction.Lattice.SeriesLogarithmOnTheComplexGroup
import YangMills.Construction.Matrices.ImplicitFunctionOnTheRealFormProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction
open Matrices Coordinates Conventions
namespace PeriodicLattice.LinearizedConstraintAtBond
variable {L m : ℕ} {j : ℤ}
theorem nonempty_basis_traceless : Nonempty (Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.traceless_basis_nonempty <;> assumption
theorem exists_linear_coordinates {ι : Type} {n : ℕ} (e : ι ≃ Fin n)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    ∃ w : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexCoordinates (n * 3), ∀ a : ι → ComplexMatrix2,
      (∀ i, a i ∈ ComplexMatrix2.traceless) →
        ∀ i, ComplexCoordinates.tracelessTuple β (w a) (e i) = a i := by
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective ComplexMatrix2.traceless.subtype
    (Submodule.ker_subtype _)
  refine ⟨{ toFun := fun a q => β.repr (P (a (e.symm (finProdFinEquiv.symm q).1)))
              (finProdFinEquiv.symm q).2
            map_add' := ?_
            map_smul' := ?_ }, ?_⟩
  · intro a a'
    funext q
    simp
  · intro z a
    funext q
    simp
  · intro a ha i
    have hPa : P (a i) = ⟨a i, ha i⟩ := by
      have := LinearMap.congr_fun hP ⟨a i, ha i⟩
      simpa using this
    simp only [ComplexCoordinates.tracelessTuple, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [Equiv.symm_apply_apply, hPa]
    have hsum : ((∑ x, β.repr ⟨a i, ha i⟩ x • β x : ComplexMatrix2.traceless) : ComplexMatrix2) =
        a i := by rw [β.sum_repr]
    push_cast at hsum
    exact hsum
theorem opposite_isPositivelyOriented_of_not (b : Bond L m j) (h : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.Bond.opposite_isPositivelyOriented <;> assumption
theorem expTwist_eq_extendFromPositive (S : Set (Bond L m j)) (hS : IsReversalClosed S)
    (V B : Bond L m j → ComplexMatrix2) (a : PositiveBondOf S → ComplexMatrix2)
    (ha : ∀ p, a p = ComplexMatrix2.matExp (Complex.I • B p.1) * V p.1) :
    ∀ b ∈ S, expTwist B V b = extendFromPositive S a b := by
  intro b hb
  by_cases hp : b.IsPositivelyOriented
  · simp only [expTwist, extendFromPositive, if_pos hp]
    rw [dif_pos (⟨hb, hp⟩ : b ∈ S ∧ b.IsPositivelyOriented), ha]
  · have hr := opposite_isPositivelyOriented_of_not b hp
    have hm := hS b hb
    simp only [expTwist, extendFromPositive, if_neg hp]
    rw [dif_neg (fun h : b ∈ S ∧ b.IsPositivelyOriented => hp h.2),
      dif_pos (⟨hm, hr⟩ : b.opposite ∈ S ∧ b.opposite.IsPositivelyOriented), ha]
theorem extendFromPositive_restrictToPositive (S : Set (Bond L m j)) (hS : IsReversalClosed S)
    (G : Set ComplexMatrix2) (U : Bond L m j → ComplexMatrix2) (hU : IsGaugeField G S U) :
    ∀ b ∈ S, extendFromPositive S (restrictToPositive S U) b = U b := by
  intro b hb
  by_cases hp : b.IsPositivelyOriented
  · simp only [extendFromPositive]
    rw [dif_pos (⟨hb, hp⟩ : b ∈ S ∧ b.IsPositivelyOriented)]
    rfl
  · have hr := opposite_isPositivelyOriented_of_not b hp
    have hm := hS b hb
    simp only [extendFromPositive]
    rw [dif_neg (fun h : b ∈ S ∧ b.IsPositivelyOriented => hp h.2),
      dif_pos (⟨hm, hr⟩ : b.opposite ∈ S ∧ b.opposite.IsPositivelyOriented)]
    exact (hU.2 b.opposite hm).symm
variable {K k : ℕ}
theorem exists_chart_differential (hP : AveragingSchemeProperties)
    (hR : ComplexAverageIsLocal)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K)
    (V : BondAtLevel L m K k → ComplexMatrix2) (c : BondAtLevel L m K (k + 1))
    (hc : c.IsPositivelyOriented)
    (hV : V ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2))) :
    ∃ (n : ℕ)
      (u : (PositiveBondOf (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) → ComplexMatrix2) →ₗ[ℂ]
        ComplexCoordinates n)
      (S : Set (ComplexCoordinates n)) (g : ComplexCoordinates n → ComplexMatrix2)
      (D : ComplexCoordinates n →L[ℂ] ComplexMatrix2),
      S ∈ 𝓝 (0 : ComplexCoordinates n) ∧ HasFDerivAt g D 0 ∧
        ∀ B : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra B →
          u (fun p => Complex.I • B p.1) ∈ S →
            ConstraintMapDefined V B c ∧
              ComplexMatrix2.logSeries
                (complexBlockAverage (expTwist B V) c * (complexBlockAverage V c)⁻¹) =
                g (u (fun p => Complex.I • B p.1)) := by
  classical
  obtain ⟨Bs, hBs⟩ : ∃ Bs : Set (BondAtLevel L m K k), Bs = bondsInDoubleBlock c := ⟨_, rfl⟩
  rw [← hBs]
  have hclosed : IsReversalClosed Bs := by
    rw [hBs]
    exact fun b hb => ⟨hb.2, hb.1⟩
  obtain ⟨hdom, hcen⟩ : SchemeDomainProperties .centred c ∧ CentredDomainAgreement c := by
    obtain ⟨-, h, -⟩ := hP L hL m K k hm hk .centred
    obtain ⟨-, h1, h2, -⟩ := h c hc
    exact ⟨h1, h2⟩
  have hloc := hR L m K k hL.1 hL.2 hm hk c hc
  have hpos : ∀ U : BondAtLevel L m K k → ComplexMatrix2,
      complexBlockAverage U c = complexBlockAverageOnPositive U c := by
    intro U
    simp only [complexBlockAverage, if_pos hc]
  have hagree : ∀ C Y : BondAtLevel L m K k → ComplexMatrix2,
      Y ∈ (complexAveragingDomainNearOne c : Set _) →
      (∀ b ∈ Bs, Y b = C b) → schemeBlockAverage .centred C c = complexBlockAverage Y c := by
    intro C Y hY hYC
    have hCY : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), C b = Y b := by
      intro b hb
      exact (hYC b (hBs ▸ hb)).symm
    have hCs : C ∈ schemeHolomorphyDomain .centred c := by
      rw [hcen.domain_eq]
      exact (hloc.mem_domain_iff C Y hCY).2 hY
    rw [hcen.average_eq C hCs, hpos, hpos]
    exact hloc.average_eq C Y hCY
  have hhol : IsHolomorphicOnFields Bs (schemeHolomorphyDomain .centred c)
      fun W => schemeBlockAverage .centred W c := by
    rw [hBs]
    exact hdom.average_holomorphic
  obtain ⟨⟨fin, -⟩, hchart⟩ := hhol
  obtain ⟨β⟩ := nonempty_basis_traceless
  let _ := fin
  obtain ⟨e⟩ : Nonempty (PositiveBondOf Bs ≃ Fin (Fintype.card (PositiveBondOf Bs))) :=
    ⟨Fintype.equivFin _⟩
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : (Fin (Fintype.card (PositiveBondOf Bs)) → ComplexMatrix2) → ComplexMatrix2,
      Φ = fun X => schemeBlockAverage .centred (extendFromPositive Bs (X ∘ e)) c := ⟨_, rfl⟩
  have hcd := hchart _ e β
  rw [← hΦdef] at hcd
  obtain ⟨-, -, -, -, hX⟩ := hcd
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, X₀ = restrictToPositive Bs V ∘ e.symm := ⟨_, rfl⟩
  have hVs : V ∈ schemeHolomorphyDomain .centred c := by
    rw [hcen.domain_eq]
    exact hV
  obtain ⟨W, h0, hW, hf⟩ := hX X₀ ⟨restrictToPositive Bs V, ⟨V, hVs, rfl⟩, hX₀.symm⟩
  obtain ⟨T, hT⟩ := ((hH.1 _ W hf.1).1 4 _ hf).2.2.1 0 h0
  have hT' := hasFDerivAt_of_restrictScalars ℝ hT rfl
  let eL : ComplexCoordinates 4 →ₗ[ℂ] ComplexMatrix2 :=
    { toFun := ComplexCoordinates.matrixEquiv.symm
      map_add' := fun x y => by
        ext i j
        simp [ComplexCoordinates.matrixEquiv]
      map_smul' := fun z x => by
        ext i j
        simp [ComplexCoordinates.matrixEquiv] }
  let eC : ComplexCoordinates 4 →L[ℂ] ComplexMatrix2 := LinearMap.toContinuousLinearMap eL
  obtain ⟨w, hw⟩ := exists_linear_coordinates e β
  refine ⟨_, w, W, fun q => ComplexMatrix2.logSeries (ComplexCoordinates.expChartQuotient Φ X₀
    (ComplexCoordinates.tracelessTuple β q)), eC.comp T, hf.1.mem_nhds h0, ?_, ?_⟩
  · have h := eC.hasFDerivAt.comp (0 : ComplexCoordinates _) hT'
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
    have he : ∀ z, eC z = ComplexCoordinates.matrixEquiv.symm z := fun z => by
      simp [eC, eL]
    simp only [Function.comp_apply, he, Equiv.symm_apply_apply]
  · intro B hB hmem
    obtain ⟨hXU, hlog⟩ := hW _ hmem
    obtain ⟨v, ⟨O, hO, rfl⟩, hXeq⟩ := hXU
    have hOO : O ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) := by
      rw [← hcen.domain_eq]
      exact hO
    have hOfield : IsGaugeField complexGaugeGroup Bs O := by
      rw [hBs]
      exact hO.1
    have hVfield : IsGaugeField complexGaugeGroup Bs V := by
      rw [hBs]
      exact hV.1.1
    have hval : ∀ p : PositiveBondOf Bs, ComplexCoordinates.tracelessTuple β
        (w fun p => Complex.I • B p.1) (e p) = Complex.I • B p.1 := by
      intro p
      refine hw (fun p => Complex.I • B p.1) (fun q => ?_) p
      exact ComplexMatrix2.traceless.smul_mem _ (hB.1 _ q.2.2)
    obtain ⟨X, hXdef⟩ : ∃ X, X = ComplexCoordinates.expChart X₀
      (ComplexCoordinates.tracelessTuple β (w fun p => Complex.I • B p.1)) := ⟨_, rfl⟩
    have hXe : ∀ p : PositiveBondOf Bs,
        (X ∘ e) p = ComplexMatrix2.matExp (Complex.I • B p.1) * V p.1 := by
      intro p
      simp only [Function.comp, hXdef, ComplexCoordinates.expChart, hval, hX₀,
        restrictToPositive, Equiv.symm_apply_apply]
    have hYC := expTwist_eq_extendFromPositive Bs hclosed V B (X ∘ e) hXe
    have hXO : X ∘ e = restrictToPositive Bs O := by
      rw [hXdef, ← hXeq]
      funext p
      simp
    have hCO := extendFromPositive_restrictToPositive Bs hclosed complexGaugeGroup O hOfield
    rw [← hXO] at hCO
    have hYO : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), expTwist B V b = O b := by
      intro b hb
      have hb' : b ∈ Bs := hBs ▸ hb
      rw [hYC b hb', hCO b hb']
    have hYdom : expTwist B V ∈
        (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) :=
      (hloc.mem_domain_iff _ _ hYO).2 hOO
    have hΦX : Φ X = complexBlockAverage (expTwist B V) c := by
      rw [hΦdef]
      exact hagree _ _ hYdom hYC
    have hΦ₀ : Φ X₀ = complexBlockAverage V c := by
      rw [hΦdef]
      refine hagree _ _ hV fun b hb => ?_
      have he : X₀ ∘ e = restrictToPositive Bs V := by
        rw [hX₀]
        funext p
        simp
      simp only [he]
      exact (extendFromPositive_restrictToPositive Bs hclosed complexGaugeGroup V hVfield b hb).symm
    have hq : ComplexCoordinates.expChartQuotient Φ X₀
        (ComplexCoordinates.tracelessTuple β (w fun p => Complex.I • B p.1)) =
        complexBlockAverage (expTwist B V) c * (complexBlockAverage V c)⁻¹ := by
      rw [ComplexCoordinates.expChartQuotient, ← hXdef, hΦX, hΦ₀]
    exact ⟨⟨hYdom, hq ▸ hlog⟩, congrArg ComplexMatrix2.logSeries hq.symm⟩
theorem statement_holds (hP : AveragingSchemeProperties)
    (hR : ComplexAverageIsLocal)
    (hS : LogSeriesInComplexGroupStatement)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    LinearizedConstraintAtBond.Statement := by
  intro L m K k hL hm hk V c hc hV
  obtain ⟨n, u, S, g, D, hS0, hg, hform⟩ := exists_chart_differential hP hR hH hL hm hk V c hc hV
  obtain ⟨τ, hτ⟩ : ∃ τ : (BondAtLevel L m K k → ComplexMatrix2) → ComplexCoordinates n,
      τ = fun A => u fun p => Complex.I • A p.1 := ⟨_, rfl⟩
  have τadd : ∀ A A', τ (A + A') = τ A + τ A' := by
    intro A A'
    simp only [hτ]
    rw [← map_add]
    congr 1
    funext p
    simp [smul_add]
  have τsmul : ∀ (z : ℂ) A, τ (z • A) = z • τ A := by
    intro z A
    simp only [hτ]
    rw [← map_smul]
    congr 1
    funext p
    simp [smul_comm z Complex.I]
  have hsmul : ∀ (t : ℂ) (A : BondAtLevel L m K k → ComplexMatrix2),
      IsBondForm complexLieAlgebra A → IsBondForm complexLieAlgebra (t • A) := by
    intro t A hA
    refine ⟨fun b hb => ComplexMatrix2.traceless.smul_mem t (hA.1 b hb), fun b => ?_⟩
    simp [hA.2 b]
  have hform' : ∀ A : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra A →
      ∀ᶠ t : ℂ in 𝓝 0, ConstraintMapDefined V (t • A) c ∧
        ComplexMatrix2.logSeries
          (complexBlockAverage (expTwist (t • A) V) c * (complexBlockAverage V c)⁻¹) =
          g (t • τ A) := by
    intro A hA
    have hcont : Filter.Tendsto (fun t : ℂ => t • τ A) (𝓝 0) (𝓝 0) := by
      have h : Continuous fun t : ℂ => t • τ A := by fun_prop
      simpa using h.tendsto 0
    filter_upwards [hcont hS0] with t ht
    have ht' : τ (t • A) ∈ S := by
      rw [τsmul]
      exact ht
    have h := hform (t • A) (hsmul t A hA) (by rw [hτ] at ht'; exact ht')
    refine ⟨h.1, ?_⟩
    rw [h.2, ← τsmul, hτ]
  have hderiv : ∀ A : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra A →
      HasDerivAt (fun t : ℂ => ComplexMatrix2.logSeries
        (complexBlockAverage (expTwist (t • A) V) c * (complexBlockAverage V c)⁻¹)) (D (τ A)) 0 := by
    intro A hA
    have hline : HasDerivAt (fun t : ℂ => t • τ A) (τ A) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const (τ A)
    have hg' : HasFDerivAt g D ((0 : ℂ) • τ A) := by simpa using hg
    have h := hg'.comp_hasDerivAt (0 : ℂ) hline
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hform' A hA] with t ht
    exact ht.2
  have hcurve : ∀ A : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra A →
      HasDerivAt (logRatioCurve complexBlockAverage V A c) (D (τ A)) (0 : ℝ) := by
    intro A hA
    have hof : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) 0 := Complex.ofRealCLM.hasDerivAt
    have hd : HasDerivAt (fun t : ℂ => ComplexMatrix2.logSeries
        (complexBlockAverage (expTwist (t • A) V) c * (complexBlockAverage V c)⁻¹)) (D (τ A))
        ((0 : ℝ) : ℂ) := by simpa using hderiv A hA
    have h := hd.scomp (0 : ℝ) hof
    rw [one_smul] at h
    exact h
  have hQ : ∀ A : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra A →
      linearizedConstraint V A c = (Complex.I * (L : ℂ))⁻¹ • D (τ A) := by
    intro A hA
    simp only [linearizedConstraint, constraintDerivativeForm, if_pos hc]
    rw [(hcurve A hA).deriv]
  have hL0 : (L : ℂ) ≠ 0 := by
    have : L ≠ 0 := by
      have := hL.2
      omega
    exact_mod_cast this
  have hmem : ∀ A : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra A →
      D (τ A) ∈ ComplexMatrix2.traceless := by
    intro A hA
    let trC : ComplexMatrix2 →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
    have h1 := trC.hasFDerivAt.comp_hasDerivAt (0 : ℂ) (hderiv A hA)
    have hser := hS.2 L hL m K k hm hk c hc
    have hVd : Matrix.det (complexBlockAverage V c) = 1 := hser.1 V hV
    have h2 : (trC ∘ fun t : ℂ => ComplexMatrix2.logSeries
        (complexBlockAverage (expTwist (t • A) V) c * (complexBlockAverage V c)⁻¹)) =ᶠ[𝓝 0]
        fun _ => (0 : ℂ) := by
      filter_upwards [hform' A hA] with t ht
      obtain ⟨⟨hY, hlog⟩, -⟩ := ht
      have hYd : Matrix.det (complexBlockAverage (expTwist (t • A) V) c) = 1 := hser.1 _ hY
      have hgrp : complexBlockAverage (expTwist (t • A) V) c * (complexBlockAverage V c)⁻¹ ∈
          complexGaugeGroup := by
        show Matrix.det _ = 1
        rw [Matrix.det_mul, Matrix.det_nonsing_inv, hYd, hVd]
        simp
      have h := (hS.1 _ hgrp hlog).1
      simpa [trC] using h
    have h3 := h1.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq h2)
    exact show Matrix.trace (D (τ A)) = 0 from by simpa [trC] using h3
  refine
    { differentiableAt_logRatioCurve := fun A hA => (hcurve A hA).differentiableAt
      map_add := fun A A' hA hA' => ?_
      map_smul := fun z A hA => ?_
      mem_complexLieAlgebra := fun A hA => ?_
      eq_of_eqOn_doubleBlock := fun A A' hA hA' h => ?_
      eventually_constraintMapDefined := fun B hB => (hform' B hB).mono fun t ht => ht.1
      hasDerivAt_constraintMap := fun B hB => ?_ }
  · have hadd : IsBondForm complexLieAlgebra (A + A') := by
      refine ⟨fun b hb => ComplexMatrix2.traceless.add_mem (hA.1 b hb) (hA'.1 b hb), fun b => ?_⟩
      simp [hA.2 b, hA'.2 b, add_comm]
    rw [hQ _ hadd, hQ A hA, hQ A' hA', τadd, map_add, smul_add]
  · rw [hQ _ (hsmul z A hA), hQ A hA, τsmul, map_smul, smul_comm]
  · rw [hQ A hA]
    exact ComplexMatrix2.traceless.smul_mem _ (hmem A hA)
  · have hτeq : τ A = τ A' := by
      simp only [hτ]
      congr 1
      funext p
      rw [h p.1 p.2.1]
    rw [hQ A hA, hQ A' hA', hτeq]
  · have hval : (L : ℂ) • linearizedConstraint V B c = Complex.I⁻¹ • D (τ B) := by
      rw [hQ B hB, smul_smul]
      congr 1
      rw [mul_inv, mul_comm, mul_assoc, inv_mul_cancel₀ hL0, mul_one]
    rw [hval]
    exact (hderiv B hB).const_smul Complex.I⁻¹
end PeriodicLattice.LinearizedConstraintAtBond
end YangMills.Construction
