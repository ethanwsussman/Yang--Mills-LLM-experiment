import YangMills.Construction.Lattice.CovarianceOfComplexLifts
import YangMills.Construction.Lattice.CovarianceOfTheAveragingMapsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ComplexLiftCovariance
variable {L m : ℕ}
theorem bond_finite (hs : Conventions.IsAdmissibleBlockingFactor L) (j : ℤ) :
    Finite (Bond L m j) := by
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hs.2
  have : Finite (Site L m j) := SeparatedSequences.BaseParameters.site_finite hL m j
  refine Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) ?_
  intro b b' hb
  exact Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
theorem commutesHolomorphically_of_coordinate_form {σ : FourTorus L m ≃ FourTorus L m} {j j' : ℤ}
    [Finite (Bond L m j)] {ℬ : Set (Bond L m j)}
    {F : PartialGaugeField L m j → PartialGaugeField L m j'}
    (𝒞 : Set (Bond L m j'))
    (hpull : ∀ c : Bond L m j', bondPreimage σ (bondImage σ c) = c)
    (hsupp : ∀ U ∈ complexGaugeFields ℬ, (F ⟨ℬ, U⟩).support = 𝒞)
    (heq : ∀ U ∈ complexGaugeFields ℬ,
      (F ⟨bondImage σ '' ℬ, transportGaugeField σ U⟩).EqOnSupport
        (transportPartialGaugeField σ (F ⟨ℬ, U⟩)))
    (hform : ∀ c ∈ 𝒞, (∀ U ∈ complexGaugeFields ℬ, (F ⟨ℬ, U⟩).field c = 1) ∨
      ∃ c₀ ∈ ℬ, ∀ U ∈ complexGaugeFields ℬ, (F ⟨ℬ, U⟩).field c = U c₀) :
    CommutesHolomorphically σ ℬ F := by
  classical
  intro c
  let _ : Fintype ↥ℬ := Fintype.ofFinite _
  have hmem : ∀ U ∈ complexGaugeFields ℬ,
      (bondImage σ c ∈ (F ⟨bondImage σ '' ℬ, transportGaugeField σ U⟩).support ↔ c ∈ 𝒞) := by
    intro U hU
    rw [(heq U hU).1]
    show bondImage σ c ∈ bondImage σ '' (F ⟨ℬ, U⟩).support ↔ c ∈ 𝒞
    rw [hsupp U hU]
    constructor
    · rintro ⟨b, hb, e⟩
      have e' := congrArg (bondPreimage σ) e
      rw [hpull, hpull] at e'
      exact e' ▸ hb
    · exact fun h => ⟨c, h, rfl⟩
  have hD₁ : {U ∈ complexGaugeFields ℬ |
      bondImage σ c ∈ (F ⟨bondImage σ '' ℬ, transportGaugeField σ U⟩).support} =
      {U ∈ complexGaugeFields ℬ | c ∈ 𝒞} := by
    ext U
    exact and_congr_right fun hU => hmem U hU
  have hD₂ : {U ∈ complexGaugeFields ℬ | c ∈ (F ⟨ℬ, U⟩).support} =
      {U ∈ complexGaugeFields ℬ | c ∈ 𝒞} := by
    ext U
    refine and_congr_right fun hU => ?_
    rw [hsupp U hU]
  have hright : ∀ U, transportGaugeField σ (F ⟨ℬ, U⟩).field (bondImage σ c) =
      (F ⟨ℬ, U⟩).field c := fun U => congrArg _ (hpull c)
  have hleft : ∀ U ∈ complexGaugeFields ℬ, c ∈ 𝒞 →
      (F ⟨bondImage σ '' ℬ, transportGaugeField σ U⟩).field (bondImage σ c) =
        (F ⟨ℬ, U⟩).field c := fun U hU hc =>
    ((heq U hU).2 _ ((hmem U hU).2 hc)).trans (hright U)
  unfold IsHolomorphicEquation
  rw [hD₁, hD₂, inter_self]
  by_cases hc : c ∈ 𝒞
  · have hP : {U ∈ complexGaugeFields ℬ | c ∈ 𝒞} = complexGaugeFields ℬ := by
      ext U
      exact ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩
    rw [hP]
    have hhol : ∀ f : (Bond L m j → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2,
        (∀ U ∈ complexGaugeFields ℬ, f U = (F ⟨ℬ, U⟩).field c) →
        IsAnalyticOnSupport (complexGaugeFields ℬ) ℬ (complexGaugeFields ℬ) f := by
      intro f hf
      rcases hform c hc with h1 | ⟨c₀, h₀, hU⟩
      · exact IsHolomorphicOnFields.of_analytic_formula (fun _ => (1 : Matrices.ComplexMatrix2))
          subset_rfl (isRelativelyOpen_self _) (fun _ _ => analyticAt_const) fun U hU' =>
            (hf U hU').trans (h1 U hU')
      · refine IsHolomorphicOnFields.of_analytic_formula (fun w => w ⟨c₀, h₀⟩) subset_rfl
          (isRelativelyOpen_self _) (fun U _ => ?_) fun U hU' => (hf U hU').trans (hU U hU')
        exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ↥ℬ => Matrices.ComplexMatrix2)
          ⟨c₀, h₀⟩).analyticAt _
    exact ⟨hhol _ fun U hU => hleft U hU hc, hhol _ fun U _ => hright U,
      fun U hU => (hleft U hU hc).trans (hright U).symm, fun _ => rfl⟩
  · have hE : {U ∈ complexGaugeFields ℬ | c ∈ 𝒞} = ∅ := by
      ext U
      exact ⟨fun h => hc h.2, fun h => h.elim⟩
    rw [hE]
    have hhol : ∀ f : (Bond L m j → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2,
        IsAnalyticOnSupport (complexGaugeFields ℬ) ℬ ∅ f := fun f =>
      IsHolomorphicOnFields.of_analytic_formula (fun _ => (0 : Matrices.ComplexMatrix2))
        (empty_subset _) ⟨∅, isOpen_empty, by simp⟩ (fun _ h => h.elim) fun _ h => h.elim
    exact ⟨hhol _, hhol _, fun _ h => h.elim, fun _ => rfl⟩
theorem bondImage_endpoints (hG : LatticeIsometryGroupActionStatement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) {j : ℤ} (hj : i ≤ j)
    (b : Bond L m j) :
    ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
      ((bondImage σ b).target : FourTorus L m) = σ b.target :=
  ((hG L m i hs hm hi).2.2.2.2 σ hσ j hj).1.2.2.2.1 b
theorem symm_mem_latticeIsometries (hG : LatticeIsometryGroupActionStatement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) :
    σ.symm ∈ latticeIsometries L m i := by apply _root_.YangMills.Construction.PeriodicLattice.EquivarianceProof.symm_mem_latticeIsometries <;> assumption
theorem bondPreimage_bondImage (hG : LatticeIsometryGroupActionStatement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) {j : ℤ} (hj : i ≤ j)
    (c : Bond L m j) : bondPreimage σ (bondImage σ c) = c := by
  have e := bondImage_endpoints hG hs hm hi hσ hj c
  have p : ((bondPreimage σ (bondImage σ c)).source : FourTorus L m) =
        σ.symm (bondImage σ c).source ∧
      ((bondPreimage σ (bondImage σ c)).target : FourTorus L m) = σ.symm (bondImage σ c).target :=
    bondImage_endpoints hG hs hm hi (symm_mem_latticeIsometries hG hs hm hi hσ) hj (bondImage σ c)
  apply Bond.ext <;> apply Subtype.ext
  · rw [p.1, e.1]; simp
  · rw [p.2, e.2]; simp
theorem complexLevelLiftsEquivariant_holds (hG : LatticeIsometryGroupActionStatement)
    (hCov : AveragingMapsEquivariant) (hLift : LiftConsistentWithAverages) :
    ComplexLevelLiftsEquivariant := by
  intro L m i σ hs hm hi hσ K k n hnk hkK hik ℬ hℬ
  have hlifts : LevelLiftEquivariant K i σ := (hCov L m hs hm i hi σ hσ K).2.2.2.2.2.2.1
  have hdepth : ∀ {a b : ℕ}, a ≤ b → levelDepth K b ≤ levelDepth K a := by
    intro a b hab
    simp only [levelDepth]
    omega
  have h0 : i ≤ levelDepth K 0 := hik.trans (hdepth (Nat.zero_le k))
  have hn : i ≤ levelDepth K n := hik.trans (hdepth hnk)
  have hcov : ∀ U ∈ complexGaugeFields ℬ, _ := fun U hU =>
    (hlifts k n hik ⟨ℬ, U⟩).1 complexGaugeGroup (Or.inr rfl) ⟨hnk, hkK, hℬ, hU⟩
  have hpull0 := bondPreimage_bondImage (j := levelDepth K 0) hG hs hm hi hσ h0
  have hpulln := bondPreimage_bondImage (j := levelDepth K n) hG hs hm hi hσ hn
  have hsame : ∀ {j : ℤ} {F : PartialGaugeField L m (levelDepth K k) → PartialGaugeField L m j},
      (∀ U ∈ complexGaugeFields ℬ, (F ⟨bondImage σ '' ℬ, transportGaugeField σ U⟩).EqOnSupport
        (transportPartialGaugeField σ (F ⟨ℬ, U⟩))) →
      HasEquivariantSupport σ ℬ F := fun h U hU => (h U hU).1
  have hbareA : ∀ U ∈ complexGaugeFields ℬ,
      (bareLiftPartial (K := K)
          (⟨bondImage σ '' ℬ, transportGaugeField σ U⟩ :
            PartialGaugeField L m (levelDepth K k))).EqOnSupport
        (transportPartialGaugeField σ (bareLiftPartial (K := K) ⟨ℬ, U⟩)) :=
    fun U hU => (hcov U hU).2.1
  have hliftA : ∀ U ∈ complexGaugeFields ℬ,
      (complexLevelLiftPartial (K := K) n
          (⟨bondImage σ '' ℬ, transportGaugeField σ U⟩ :
            PartialGaugeField L m (levelDepth K k))).EqOnSupport
        (transportPartialGaugeField σ (complexLevelLiftPartial (K := K) n ⟨ℬ, U⟩)) :=
    fun U hU => (hcov U hU).2.2
  have hI : Finite (Bond L m (levelDepth K k)) := bond_finite hs _
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · obtain rfl : k = 0 := by omega
    obtain rfl : n = 0 := by omega
    refine ⟨commutesHolomorphically_of_coordinate_form ℬ hpull0 (fun _ _ => rfl) hbareA
        (fun c hc => Or.inr ⟨c, hc, fun _ _ => rfl⟩), hsame hbareA,
      commutesHolomorphically_of_coordinate_form ℬ hpulln (fun _ _ => rfl) hliftA
        (fun c hc => Or.inr ⟨c, hc, fun _ _ => rfl⟩), hsame hliftA⟩
  · have C := fun U (hU : U ∈ complexGaugeFields ℬ) =>
      hLift L m K hs hm hK k hkK ℬ hℬ U (Or.inr hU)
    have hformAt : ∀ j ≤ k, ∀ c ∈ (liftSupport j ℬ : Set (BondAtLevel L m K j)),
        (∀ U ∈ complexGaugeFields ℬ, (complexLevelLifts ℬ U j).field c = 1) ∨
        ∃ c₀ ∈ ℬ, ∀ U ∈ complexGaugeFields ℬ, (complexLevelLifts ℬ U j).field c = U c₀ := by
      rintro j hj c (hc | ⟨c₀, h₀, hov⟩)
      · exact Or.inl fun U hU => (((C U hU).2.2.2.1.1 j hj).2.2.2 c).1 hc |>.2
      · exact Or.inr ⟨c₀, h₀, fun U hU =>
          (((C U hU).2.2.2.1.1 j hj).2.2.2 c).2.1 c₀ h₀ hov |>.2⟩
    have hsupp : ∀ j ≤ k, ∀ U ∈ complexGaugeFields ℬ,
        (complexLevelLifts ℬ U j).support = liftSupport j ℬ := fun j hj U hU =>
      ((C U hU).2.2.2.1.1 j hj).2.2.1.1
    have hbareForm : ∀ c ∈ (bareLiftSupport (K := K) ℬ),
        (∀ U ∈ complexGaugeFields ℬ,
          (bareLiftPartial (K := K)
            (⟨ℬ, U⟩ : PartialGaugeField L m (levelDepth K k))).field c = 1) ∨
        ∃ c₀ ∈ ℬ, ∀ U ∈ complexGaugeFields ℬ,
          (bareLiftPartial (K := K) (⟨ℬ, U⟩ : PartialGaugeField L m (levelDepth K k))).field c =
            U c₀ := by
      intro c hc
      rcases (complexGaugeFields ℬ).eq_empty_or_nonempty with hE | ⟨U₀, hU₀⟩
      · exact Or.inl fun U hU => by rw [hE] at hU; exact hU.elim
      have hc' : c ∈ (liftSupport 0 ℬ : Set (BondAtLevel L m K 0)) := by
        have e : bareLiftSupport (K := K) ℬ = liftSupport 0 ℬ := (C U₀ hU₀).2.1.1
        exact e ▸ hc
      have hval : ∀ U ∈ complexGaugeFields ℬ,
          (bareLiftPartial (K := K) (⟨ℬ, U⟩ : PartialGaugeField L m (levelDepth K k))).field c =
            (complexLevelLifts ℬ U 0).field c := fun U hU =>
        (((C U hU).2.2.2.1.2.1).2 c ((hsupp 0 (Nat.zero_le k) U hU).symm ▸ hc')).symm
      rcases hformAt 0 (Nat.zero_le k) c hc' with h1 | ⟨c₀, h₀, hU⟩
      · exact Or.inl fun U hU' => (hval U hU').trans (h1 U hU')
      · exact Or.inr ⟨c₀, h₀, fun U hU' => (hval U hU').trans (hU U hU')⟩
    exact ⟨commutesHolomorphically_of_coordinate_form _ hpull0 (fun _ _ => rfl) hbareA hbareForm,
      hsame hbareA,
      commutesHolomorphically_of_coordinate_form _ hpulln (hsupp n hnk) hliftA (hformAt n hnk),
      hsame hliftA⟩
end YangMills.Construction.PeriodicLattice.ComplexLiftCovariance
