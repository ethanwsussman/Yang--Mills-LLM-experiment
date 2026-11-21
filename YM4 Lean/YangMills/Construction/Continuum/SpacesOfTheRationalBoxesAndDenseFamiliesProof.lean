import YangMills.Construction.Continuum.ChoicesOfDenseSetsAndTheCountableFamily
import YangMills.Construction.Continuum.ExistenceOfAStableChoice
import YangMills.Construction.Continuum.SpacesOfTheRationalBoxesAndDenseFamilies
import YangMills.Construction.TorusOrFourSpace.BallsTuplesInABallAndAdmissibleTuplesOfFourSpace
import YangMills.Construction.TorusOrFourSpace.MaximumC1NormOnTheSpacesOfTheStock
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal Matrix
noncomputable section
namespace YangMills.Construction
open TestFunctions PeriodicSpace
namespace Continuum.RationalBoxes.BoxSpaceProperties
variable (D : Params)
theorem boxUnions_eq_ratBoxUnions (D : Params) : boxUnions = ratBoxUnions :=
  (supportStock_euclidean_eq D).symm.trans (EuclideanTuples.supportStock_euclidean D)
theorem ofReal_c1NormR4_le_c1NormQ (g : (Fin 4 → ℝ) → ℝ) :
    ENNReal.ofReal (c1NormR4 g) ≤ Kind.c1NormQ D .euclidean g := by
  set N := Kind.c1NormQ D .euclidean g with hN
  by_cases htop : N = ⊤
  · simp [htop]
  have hval : ∀ x, ‖g x‖ ≤ N.toReal := fun x => by
    have h : ENNReal.ofReal |g x| ≤ N :=
      (le_iSup (fun y => ENNReal.ofReal |(g : Kind.Pt D .euclidean → ℝ) y|) x).trans
        (le_max_left _ _)
    exact (ENNReal.ofReal_le_iff_le_toReal htop).1 h
  have hder : ∀ i x, ‖partialDerivR4 i g x‖ ≤ N.toReal := fun i x => by
    have h : ENNReal.ofReal |Kind.partialDeriv D .euclidean i g x| ≤ N :=
      (le_iSup (fun y => ENNReal.ofReal |Kind.partialDeriv D .euclidean i g y|) x).trans
        ((le_iSup (fun j => Kind.supNormQ D .euclidean
          (Kind.partialDeriv D .euclidean j g)) i).trans (le_max_right _ _))
    have h' := (ENNReal.ofReal_le_iff_le_toReal htop).1 h
    have h3 : Kind.partialDeriv D .euclidean i g x = partialDerivR4 i g x :=
      congrFun (EuclideanTuples.partialDeriv_euclidean D i g) x
    rw [h3] at h'
    exact h'
  exact ENNReal.ofReal_le_of_le_toReal
    (max_le (ciSup_le hval) (ciSup_le fun i => ciSup_le (hder i)))
theorem c1NormQ_le_ofReal_c1NormR4 {g : (Fin 4 → ℝ) → ℝ} (hg : IsC1R4 g) (hc : HasCompactSupport g) :
    Kind.c1NormQ D .euclidean g ≤ ENNReal.ofReal (c1NormR4 g) := by
  obtain ⟨⟨C, hC⟩, hd⟩ := EuclideanTuples.bounded_of_isC1R4 hg hc
  refine max_le (iSup_le fun x => ENNReal.ofReal_le_ofReal ?_)
    (iSup_le fun i => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_)
  · exact (le_ciSup (f := fun y => ‖g y‖) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ x).trans
      (le_max_left _ _)
  · have h3 : Kind.partialDeriv D .euclidean i g x = partialDerivR4 i g x :=
      congrFun (EuclideanTuples.partialDeriv_euclidean D i g) x
    rw [h3]
    obtain ⟨Ci, hCi⟩ := hd i
    have hbd : BddAbove (range fun y => ‖partialDerivR4 i g y‖) :=
      ⟨Ci, by rintro _ ⟨y, rfl⟩; exact hCi y⟩
    have h1 : ‖partialDerivR4 i g x‖ ≤ uniformNorm (partialDerivR4 i g) := le_ciSup hbd x
    have hbd2 : BddAbove (range fun j : Fin 4 => uniformNorm (partialDerivR4 j g)) :=
      (finite_range _).bddAbove
    have h2 : uniformNorm (partialDerivR4 i g) ≤ ⨆ j : Fin 4, uniformNorm (partialDerivR4 j g) :=
      le_ciSup hbd2 i
    exact h1.trans (h2.trans (le_max_right _ _))
theorem c1NormQ_eq_ofReal {Q : Set (Fin 4 → ℝ)} (hQ : Q ∈ boxUnions) {g : (Fin 4 → ℝ) → ℝ}
    (hg : g ∈ c1Off Q) :
    Kind.c1NormQ D .euclidean g = ENNReal.ofReal (c1NormR4 g) := by
  have hg' := (TestFunctions.mem_c1ZeroOff_iff (boxUnions_eq_ratBoxUnions D ▸ hQ)).1 hg
  exact le_antisymm (c1NormQ_le_ofReal_c1NormR4 D hg'.1 hg'.2.1) (ofReal_c1NormR4_le_c1NormQ D g)
theorem mem_supportStock {Q : Set (Fin 4 → ℝ)} (hQ : Q ∈ boxUnions) :
    Q ∈ Kind.supportStock D .euclidean :=
  (supportStock_euclidean_eq D).symm ▸ hQ
theorem isCompleteSeparable_of_cauchy {V : Type*} [NormedAddCommGroup V]
    (hc : ∀ u : ℕ → V, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a))
    (hs : ∃ A : Set V, A.Countable ∧ Dense A) : IsCompleteSeparable V :=
  ⟨Metric.complete_of_cauchySeq_tendsto hc, ⟨hs⟩⟩
theorem isSeparableBanach_of_mem (D : Params) (hm : MaxC1Norm.Claim)
    {Q : Set (Fin 4 → ℝ)} (hQ : Q ∈ boxUnions) : IsSeparableBanach Q := by
  obtain ⟨hnorm, hcompl, A, hAV, hAc, hAd⟩ :=
    ((hm D .euclidean).1 Q (mem_supportStock D hQ)).2.1.2.1
  have hN : ∀ g ∈ c1Off Q,
      Kind.c1NormQ D .euclidean g = ENNReal.ofReal (c1NormR4 g) := fun g hg => c1NormQ_eq_ofReal D hQ hg
  have hr : ∀ g : (Fin 4 → ℝ) → ℝ, 0 ≤ c1NormR4 g := EuclideanTuples.c1NormR4_nonneg
  have hzero : (0 : (Fin 4 → ℝ) → ℝ) ∈ c1Off Q := hnorm.zero_mem
  have hadd : ∀ g ∈ c1Off Q, ∀ h ∈ c1Off Q, g + h ∈ c1Off Q :=
    fun g hg h hh => ⟨ContDiff.add hg.1 hh.1, fun x hx => by simp [hg.2 x hx, hh.2 x hx]⟩
  have hsmulm : ∀ (a : ℝ), ∀ g ∈ c1Off Q, a • g ∈ c1Off Q :=
    fun a g hg => ⟨ContDiff.const_smul a hg.1, fun x hx => by simp [hg.2 x hx]⟩
  have hradd : ∀ g ∈ c1Off Q, ∀ h ∈ c1Off Q,
      c1NormR4 (g + h) ≤ c1NormR4 g + c1NormR4 h := fun g hg h hh => by
    have e := hnorm.triangle g hg h hh
    change Kind.c1NormQ D .euclidean (g + h) ≤
      Kind.c1NormQ D .euclidean g + Kind.c1NormQ D .euclidean h at e
    rw [hN _ (hadd g hg h hh), hN g hg, hN h hh, ← ENNReal.ofReal_add (hr g) (hr h)] at e
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (hr g) (hr h))).1 e
  have hsmul : ∀ (a : ℝ), ∀ g ∈ c1Off Q,
      c1NormR4 (a • g) = |a| * c1NormR4 g := fun a g hg => by
    have e := hnorm.homog g hg a
    change Kind.c1NormQ D .euclidean (a • g) =
      ENNReal.ofReal |a| * Kind.c1NormQ D .euclidean g at e
    rw [hN _ (hsmulm a g hg), hN g hg, ← ENNReal.ofReal_mul (abs_nonneg a)] at e
    exact (ENNReal.ofReal_eq_ofReal_iff (hr _) (mul_nonneg (abs_nonneg a) (hr g))).1 e
  have hrz : ∀ g ∈ c1Off Q, c1NormR4 g = 0 → g = 0 := fun g hg e =>
    hnorm.definite g hg (by
      change Kind.c1NormQ D .euclidean g = 0
      rw [hN g hg, e, ENNReal.ofReal_zero])
  have hr0 : c1NormR4 (0 : (Fin 4 → ℝ) → ℝ) = 0 := by
    simpa using hsmul 0 0 hzero
  let V : Submodule ℝ ((Fin 4 → ℝ) → ℝ) :=
    { carrier := c1Off Q
      add_mem' := fun {g h} hg hh => hadd g hg h hh
      zero_mem' := hzero
      smul_mem' := fun a g hg => hsmulm a g hg }
  let Nm : AddGroupNorm V :=
    { toFun := fun g => c1NormR4 (g : (Fin 4 → ℝ) → ℝ)
      map_zero' := hr0
      add_le' := fun g h => hradd g g.2 h h.2
      neg' := fun g => EuclideanTuples.c1NormR4_neg _
      eq_zero_of_map_eq_zero' := fun g e => Subtype.ext (hrz g g.2 e) }
  refine ⟨V, Nm, rfl, fun g => rfl, fun a g => hsmul a g g.2, ?_⟩
  let _ := Nm.toNormedAddCommGroup
  have hdist : ∀ g h : V, Kind.c1NormQ D .euclidean
      ((g : (Fin 4 → ℝ) → ℝ) - (h : (Fin 4 → ℝ) → ℝ)) = ENNReal.ofReal (dist g h) := fun g h => by
    rw [dist_eq_norm]
    exact hN _ (g - h).2
  refine isCompleteSeparable_of_cauchy ?_ ?_
  · intro u hu
    have hcau := Metric.cauchySeq_iff.1 hu
    obtain ⟨(g : (Fin 4 → ℝ) → ℝ), hgV, hg⟩ := hcompl (fun j => (u j : (Fin 4 → ℝ) → ℝ)) (fun j => (u j).2) (by
      intro ε hε
      obtain ⟨J, hJ⟩ := hcau ε hε
      refine ⟨J, fun i hi j hj => ?_⟩
      change Kind.c1NormQ D .euclidean
        ((u i : (Fin 4 → ℝ) → ℝ) - (u j : (Fin 4 → ℝ) → ℝ)) < ENNReal.ofReal ε
      rw [hdist]
      exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (hJ i hi j hj))
    refine ⟨⟨g, hgV⟩, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
    obtain ⟨J, hJ⟩ := hg ε hε
    refine ⟨J, fun n hn => ?_⟩
    have e : Kind.c1NormQ D .euclidean ((u n : (Fin 4 → ℝ) → ℝ) - g) < ENNReal.ofReal ε := hJ n hn
    have e2 := hdist (u n) ⟨g, hgV⟩
    change Kind.c1NormQ D .euclidean ((u n : (Fin 4 → ℝ) → ℝ) - g) = _ at e2
    rw [e2] at e
    exact (ENNReal.ofReal_lt_ofReal_iff hε).1 e
  · refine ⟨Subtype.val ⁻¹' A, hAc.preimage_of_injOn Subtype.val_injective.injOn, ?_⟩
    refine Metric.dense_iff.2 fun g ε hε => ?_
    obtain ⟨(h : (Fin 4 → ℝ) → ℝ), hh, hlt⟩ := hAd g.1 g.2 ε hε
    refine ⟨⟨h, hAV hh⟩, ?_, hh⟩
    have e : Kind.c1NormQ D .euclidean ((g : (Fin 4 → ℝ) → ℝ) - h) < ENNReal.ofReal ε := hlt
    have e2 := hdist g ⟨h, hAV hh⟩
    change Kind.c1NormQ D .euclidean ((g : (Fin 4 → ℝ) → ℝ) - h) = _ at e2
    rw [e2] at e
    rw [Metric.mem_ball, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).1 e
theorem sharpNormR4_le_of_mem (hm : MaxC1Norm.Claim)
    {Q : Set (Fin 4 → ℝ)} (hQ : Q ∈ boxUnions) {g : (Fin 4 → ℝ) → ℝ} (hg : g ∈ c1Off Q) :
    sharpNormR4 D.M g ≤ 80 * D.M * c1NormR4 g := by
  have hM : 1 ≤ D.M := D.one_le_M
  have hr := EuclideanTuples.c1NormR4_nonneg g
  have h := (((hm D .euclidean).1 Q (mem_supportStock D hQ)).1 g hg).2.2
  change Kind.sharpNormQ D .euclidean g ≤
    ENNReal.ofReal (80 * D.M) * Kind.c1NormQ D .euclidean g at h
  rw [c1NormQ_eq_ofReal D hQ hg, ← ENNReal.ofReal_mul (by positivity)] at h
  have hd : (Kind.quotDist D .euclidean : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ) = euclidDistR4 :=
    funext₂ (EuclideanCase.quotDist_euclidean_eq D)
  have hl : Kind.lipConstQ D .euclidean g = lipConstR4 g :=
    congrArg (fun d => bestLipschitzConstant d g) hd
  have h1 : ENNReal.ofReal (40 * D.M * lipConstR4 g) ≤ ENNReal.ofReal (80 * D.M * c1NormR4 g) := by
    rw [← hl]
    exact (le_max_right _ _).trans h
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  refine max_le ?_ h2
  have h3 : uniformNorm g ≤ c1NormR4 g := le_max_left _ _
  nlinarith
theorem mem_powerDenominators_of_adic {L : ℕ} {x : ℝ} (hx : x ∈ PeriodicLattice.adicGridPoints L) :
    x ∈ DisjointTuples.powerDenominators L := by
  obtain ⟨k, n, rfl⟩ := (PeriodicLattice.mem_adicGridPoints_iff L x).1 hx
  refine mem_iUnion.2 ⟨k, n, ?_⟩
  simp [PeriodicLattice.meshSize, mul_comm]
theorem toMatrix'_mem_signedPermMatrices {w : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)}
    (hw : w ∈ InfiniteLattice.hyperoctahedralLinearGroup) :
    LinearMap.toMatrix' (w : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) ∈ PeriodicLattice.signedPermMatrices := by
  obtain ⟨π, t, h⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).1 hw
  refine ⟨π, fun i => ((t i : ℤ) : ℝ), fun i => ?_, fun x i => ?_⟩
  · rcases Int.units_eq_one_or (t i) with h | h <;> simp [h]
  · rw [LinearMap.toMatrix'_mulVec]
    exact h x i
theorem pushFun_toMatrix' (w : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (g : (Fin 4 → ℝ) → ℝ) :
    DisjointTuples.pushFun
        (fun x => LinearMap.toMatrix' (w : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) *ᵥ x) g =
      g ∘ w.symm := by
  have h : (fun x => LinearMap.toMatrix' (w : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) *ᵥ x) = ⇑w := by
    funext x
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  funext x
  have h2 : DisjointTuples.invMap (⇑w) x = w.symm x := by
    calc DisjointTuples.invMap (⇑w) x = DisjointTuples.invMap (⇑w) (w (w.symm x)) := by simp
      _ = w.symm x := Function.leftInverse_invFun w.injective _
  simp only [DisjointTuples.pushFun, h, Function.comp_apply, h2]
theorem exists_denseInvariantFamily (hc : DisjointTuples.SymmetricDenseChoiceExists)
    (s : Conventions.StandingParameters) (M : ℝ) (hM : 1 ≤ M) : ∃ F, IsDenseInvariantFamily s F := by
  obtain ⟨C, hC⟩ := hc s.L s.isAdmissible.1 s.isAdmissible.2
  have hs := boxUnions_eq_ratBoxUnions (Params.ofStanding s M hM)
  have hst : ∀ Q : boxUnions, (Q : Set (Fin 4 → ℝ)) ∈ ratBoxUnions := fun Q => hs ▸ Q.2
  have hU : (⋃ Q : boxUnions, C ⟨Q.1, hst Q⟩) = DisjointTuples.iUnionFamily C := by
    refine Subset.antisymm (iUnion_subset fun Q => subset_iUnion C _) (iUnion_subset fun Q => ?_)
    intro g hg
    exact mem_iUnion.2 ⟨⟨Q.1, hs.symm ▸ Q.2⟩, hg⟩
  refine ⟨fun Q => C ⟨Q.1, hst Q⟩, fun Q => hC.isDenseFamily.subset _,
    fun Q => hC.isDenseFamily.countable _, fun Q g hg ε hε => ?_, fun w hw g hg => ?_,
    fun v hv g hg => ?_⟩
  · obtain ⟨h, hh, hlt⟩ := hC.isDenseFamily.dense ⟨Q.1, hst Q⟩ g hg ε hε
    refine ⟨h, hh, ?_⟩
    rwa [← EuclideanTuples.c1NormR4_neg, neg_sub]
  · simp only [hU] at hg ⊢
    have h := hC.pushFun_signedPerm_mem g hg _ (toMatrix'_mem_signedPermMatrices hw)
    rwa [pushFun_toMatrix'] at h
  · simp only [hU] at hg ⊢
    have h := hC.pushFun_translate_mem g hg v fun i => mem_powerDenominators_of_adic (hv i)
    have he : AmbientPoints.transportFn (R4TupleForms.shiftEquiv s v) g =
        DisjointTuples.pushFun (DisjointTuples.translate v) g := by
      refine funext fun x : Fin 4 → ℝ => ?_
      refine Eq.trans ?_ (DisjointTuples.pushFun_translate v g x).symm
      change g (x + -v) = g (x - v)
      rw [sub_eq_add_neg]
    rwa [he]
theorem claim_holds (hs : SupportStockAndCountableFamily)
    (hm : MaxC1Norm.Claim)
    (hc : DisjointTuples.SymmetricDenseChoiceExists) :
    Continuum.RationalBoxes.BoxSpaceProperties.Claim := by
  intro s M hM
  let D := Params.ofStanding s M hM
  refine ⟨?_, fun Q hQ => isSeparableBanach_of_mem D hm hQ,
    fun Q hQ g hg => sharpNormR4_le_of_mem D hm hQ hg, exists_denseInvariantFamily hc s M hM⟩
  have h := ((hs D).2 .euclidean).1.1
  rwa [supportStock_euclidean_eq D] at h
end Continuum.RationalBoxes.BoxSpaceProperties
end YangMills.Construction
