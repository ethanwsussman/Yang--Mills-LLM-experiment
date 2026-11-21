import YangMills.Construction.Towers.AverageIsDifferentiableOnThePolydiscProof
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.OneValueForEveryWriting
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.UniqueValue
open YangMills.Construction.InfiniteLattice YangMills.Construction.Matrices
variable {L k j : ℕ} {a : ℝ}
theorem opposite_opposite (e : InfiniteLattice.Link a) : e.opposite.opposite = e := rfl
theorem isPositivelyOriented_or_opposite (e : InfiniteLattice.Link a) :
    e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (ha : a ≠ 0) {e : InfiniteLattice.Link a}
    (h : e.IsPositivelyOriented) : ¬ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.PolydiscSmoothing.not_opposite_isPositivelyOriented <;> assumption
theorem meshAt_ne_zero (hL : 13 ≤ L) : Tower.meshAt L k j ≠ 0 := by
  have : (L : ℝ) ≠ 0 := by
    have : L ≠ 0 := by omega
    exact_mod_cast this
  exact zpow_ne_zero _ this
def extendByInverse (g : InfiniteLattice.Link a → ComplexMatrix2) :
    InfiniteLattice.Link a → ComplexMatrix2 :=
  open Classical in fun e => if e.IsPositivelyOriented then g e else (g e.opposite)⁻¹
theorem extendByInverse_of_isPositivelyOriented {g : InfiniteLattice.Link a → ComplexMatrix2}
    {e : InfiniteLattice.Link a} (he : e.IsPositivelyOriented) : extendByInverse g e = g e :=
  if_pos he
theorem extendByInverse_of_not_isPositivelyOriented {g : InfiniteLattice.Link a → ComplexMatrix2}
    {e : InfiniteLattice.Link a} (he : ¬ e.IsPositivelyOriented) :
    extendByInverse g e = (g e.opposite)⁻¹ :=
  if_neg he
structure IsUnimodularInvClosed (S : Set ComplexMatrix2) : Prop where
  det_eq_one : ∀ A ∈ S, A.det = 1
  inv_mem : ∀ A ∈ S, A⁻¹ ∈ S
theorem isUnimodularInvClosed_compactGaugeGroup :
    IsUnimodularInvClosed PeriodicLattice.compactGaugeGroup where
  det_eq_one A h := (Matrix.mem_specialUnitaryGroup_iff.1 h).2
  inv_mem A h := by
    have hA : A⁻¹ = (((⟨A, h⟩ : ComplexMatrix2.specialUnitary)⁻¹ :
        ComplexMatrix2.specialUnitary) : ComplexMatrix2) :=
      Matrix.inv_eq_right_inv
        (congrArg Subtype.val (mul_inv_cancel (⟨A, h⟩ : ComplexMatrix2.specialUnitary)))
    rw [hA]
    exact Subtype.prop _
theorem isUnimodularInvClosed_complexGaugeGroup :
    IsUnimodularInvClosed PeriodicLattice.complexGaugeGroup where
  det_eq_one A h := h
  inv_mem A h := by
    have h1 : A.det = 1 := h
    show (A⁻¹).det = 1
    rw [Matrix.det_nonsing_inv, h1]
    simp
theorem extendByInverse_mem_fieldsValuedIn {S : Set ComplexMatrix2}
    (hS : IsUnimodularInvClosed S) (hL : 13 ≤ L)
    {g : Edge L k j → ComplexMatrix2} (hg : ∀ e : Edge L k j, e.IsPositivelyOriented → g e ∈ S) :
    extendByInverse g ∈ fieldsValuedIn L k j S := by
  have ha := meshAt_ne_zero (k := k) (j := j) hL
  refine ⟨fun e => ?_, fun e => ?_⟩
  · by_cases he : e.IsPositivelyOriented
    · rw [extendByInverse_of_isPositivelyOriented he]
      exact hg e he
    · rw [extendByInverse_of_not_isPositivelyOriented he]
      exact hS.inv_mem _ (hg _ ((isPositivelyOriented_or_opposite e).resolve_left he))
  · by_cases he : e.IsPositivelyOriented
    · rw [extendByInverse_of_isPositivelyOriented he,
        extendByInverse_of_not_isPositivelyOriented (not_isPositivelyOriented_opposite ha he),
        opposite_opposite]
    · have hr := (isPositivelyOriented_or_opposite e).resolve_left he
      rw [extendByInverse_of_isPositivelyOriented hr,
        extendByInverse_of_not_isPositivelyOriented he, Matrix.nonsing_inv_nonsing_inv]
      rw [hS.det_eq_one _ (hg _ hr)]
      exact isUnit_one
theorem presentationsAgreeAlongPerturbations_of {S : Set ComplexMatrix2}
    (hS : IsUnimodularInvClosed S) (hL : 13 ≤ L)
    (𝕜 : Type) [NormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    (IsDirection : (Edge L k j → ComplexMatrix2) → Prop) (E : Type)
    (hmove : ∀ U ∈ fieldsValuedIn L k j S, ∀ B B' : Edge L k j → ComplexMatrix2,
      IsDirection B → IsDirection B' → ∀ e : Edge L k j, e.IsPositivelyOriented → ∀ s t : 𝕜,
        ComplexMatrix2.matExp (Complex.I • (algebraMap 𝕜 ℂ s • B e + algebraMap 𝕜 ℂ t • B' e)) *
          U e ∈ S) :
    PresentationsAgreeAlongPerturbations L k j 𝕜 S IsDirection E := by
  classical
  intro D hD h U hU F₁ O₁ f₁ F₂ O₂ f₂ hw₁ hw₂ B B' hB hB'
  obtain ⟨hF₁, ⟨W₁, hW₁, hO₁⟩, hU₁, hf₁⟩ := hw₁
  obtain ⟨hF₂, ⟨W₂, hW₂, hO₂⟩, hU₂, hf₂⟩ := hw₂
  have hUc : U ∈ fieldsValuedIn L k j S := hD.1 hU
  have hF : IsFinitePositiveEdgeSet (F₁ ∪ F₂) := by
    refine ⟨hF₁.1.mono Finset.subset_union_left, fun e he => ?_⟩
    rcases Finset.mem_union.1 he with he | he
    · exact hF₁.2 e he
    · exact hF₂.2 e he
  obtain ⟨ε₀, hε₀, hopen⟩ := hD.2 U hU (F₁ ∪ F₂) hF
  let m : 𝕜 × 𝕜 → Edge L k j → ComplexMatrix2 := fun p e =>
    ComplexMatrix2.matExp (Complex.I • (algebraMap 𝕜 ℂ p.1 • B e + algebraMap 𝕜 ℂ p.2 • B' e)) *
      U e
  have hm : ∀ e, Continuous fun p => m p e := by
    intro e
    have hs : Continuous fun p : 𝕜 × 𝕜 => algebraMap 𝕜 ℂ p.1 :=
      (continuous_algebraMap 𝕜 ℂ).comp continuous_fst
    have ht : Continuous fun p : 𝕜 × 𝕜 => algebraMap 𝕜 ℂ p.2 :=
      (continuous_algebraMap 𝕜 ℂ).comp continuous_snd
    have hin : Continuous fun p : 𝕜 × 𝕜 =>
        Complex.I • (algebraMap 𝕜 ℂ p.1 • B e + algebraMap 𝕜 ℂ p.2 • B' e) :=
      ((hs.smul continuous_const).add (ht.smul continuous_const)).const_smul Complex.I
    let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
    exact (NormedSpace.exp_continuous.comp hin).mul continuous_const
  have hm0 : ∀ e, m 0 e = U e := by
    intro e
    simp [m, ComplexMatrix2.matExp]
  have hW : ∀ (F : Finset (Edge L k j)) (W : Set (F → ComplexMatrix2)), IsOpen W →
      restrictToEdges F U ∈ W → ∀ᶠ p in 𝓝 (0 : 𝕜 × 𝕜), (fun e : F => m p e) ∈ W := by
    intro F W hWo hUW
    have hc : Continuous fun p : 𝕜 × 𝕜 => fun e : F => m p e :=
      continuous_pi fun e => hm e
    refine hc.continuousAt.eventually_mem (hWo.mem_nhds ?_)
    have : (fun e : F => m 0 e) = restrictToEdges F U := funext fun e => hm0 e
    simpa [this] using hUW
  have e₁ := hW F₁ W₁ hW₁ (by rw [hO₁] at hU₁; exact hU₁.1)
  have e₂ := hW F₂ W₂ hW₂ (by rw [hO₂] at hU₂; exact hU₂.1)
  have e₃ : ∀ᶠ p in 𝓝 (0 : 𝕜 × 𝕜), ∀ e ∈ F₁ ∪ F₂,
      ComplexMatrix2.operatorNorm (m p e - U e) < ε₀ := by
    refine (Filter.eventually_all_finset _).2 fun e _ => ?_
    have := Metric.tendsto_nhds.1 ((hm e).tendsto 0) ε₀ hε₀
    filter_upwards [this] with p hp
    rw [hm0, dist_eq_norm] at hp
    exact hp
  obtain ⟨δ, hδ, H⟩ := Metric.eventually_nhds_iff.1 (e₁.and (e₂.and e₃))
  refine ⟨δ, hδ, fun s t hs ht => ?_⟩
  have hp : dist ((s, t) : 𝕜 × 𝕜) 0 < δ := by
    rw [Prod.dist_eq]
    exact max_lt (by simpa using hs) (by simpa using ht)
  obtain ⟨g₁, g₂, g₃⟩ := H hp
  have hmem : ∀ e : Edge L k j, e.IsPositivelyOriented → m (s, t) e ∈ S := fun e he =>
    hmove U hUc B B' hB hB' e he s t
  let g : Edge L k j → ComplexMatrix2 := fun e => if e ∈ F₁ ∪ F₂ then m (s, t) e else U e
  have hgin : ∀ {e : Edge L k j}, e ∈ F₁ ∪ F₂ → g e = m (s, t) e := fun h => if_pos h
  have hgout : ∀ {e : Edge L k j}, e ∉ F₁ ∪ F₂ → g e = U e := fun h => if_neg h
  have hg : ∀ e : Edge L k j, e.IsPositivelyOriented → g e ∈ S := by
    intro e he
    by_cases heF : e ∈ F₁ ∪ F₂
    · rw [hgin heF]
      exact hmem e he
    · rw [hgout heF]
      exact hUc.1 e
  have hc : extendByInverse g ∈ fieldsValuedIn L k j S :=
    extendByInverse_mem_fieldsValuedIn hS hL hg
  have hin : extendByInverse g ∈ D := by
    refine hopen _ hc (fun e he heF => ?_) (fun e heF => ?_)
    · rw [extendByInverse_of_isPositivelyOriented he, hgout heF]
    · have he : e.IsPositivelyOriented := hF.2 e heF
      rw [extendByInverse_of_isPositivelyOriented he, hgin heF]
      exact g₃ e heF
  have hv : ∀ (F : Finset (Edge L k j)), F ⊆ F₁ ∪ F₂ →
      restrictToEdges F (extendByInverse g) =
        perturbedTuple F B B' U (algebraMap 𝕜 ℂ s) (algebraMap 𝕜 ℂ t) := by
    intro F hFs
    funext e
    have heF : (e : Edge L k j) ∈ F₁ ∪ F₂ := hFs e.2
    have he : (e : Edge L k j).IsPositivelyOriented := hF.2 _ heF
    simp only [restrictToEdges, perturbedTuple]
    rw [extendByInverse_of_isPositivelyOriented he, hgin heF]
  have hv₁ := hv F₁ Finset.subset_union_left
  have hv₂ := hv F₂ Finset.subset_union_right
  have hP : ∀ F : Finset (Edge L k j), F ⊆ F₁ ∪ F₂ →
      perturbedTuple F B B' U (algebraMap 𝕜 ℂ s) (algebraMap 𝕜 ℂ t) ∈ edgeProduct S F := by
    intro F hFs e
    exact hmem e (hF.2 _ (hFs e.2))
  have m₁ : perturbedTuple F₁ B B' U (algebraMap 𝕜 ℂ s) (algebraMap 𝕜 ℂ t) ∈ O₁ := by
    rw [hO₁]
    exact ⟨g₁, hP F₁ Finset.subset_union_left⟩
  have m₂ : perturbedTuple F₂ B B' U (algebraMap 𝕜 ℂ s) (algebraMap 𝕜 ℂ t) ∈ O₂ := by
    rw [hO₂]
    exact ⟨g₂, hP F₂ Finset.subset_union_right⟩
  refine ⟨m₁, m₂, ?_⟩
  rw [← hv₁, ← hv₂, ← hf₁ _ hin (hv₁ ▸ m₁), ← hf₂ _ hin (hv₂ ▸ m₂)]
theorem nearIdentity_of_local_perturbation {S : Set ComplexMatrix2} (hS : IsUnimodularInvClosed S)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ fieldsValuedIn L k j S) {r : ℝ}
    (hr : ∀ e : Edge L k j, ComplexMatrix2.operatorNorm (V e - 1) < r)
    (F : Finset (Edge L k j)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ U' ∈ fieldsValuedIn L k j S,
      (∀ e : Edge L k j, e.IsPositivelyOriented → e ∉ F → U' e = V e) →
      (∀ e ∈ F, ComplexMatrix2.operatorNorm (U' e - V e) < ε) →
      ∀ e : Edge L k j, ComplexMatrix2.operatorNorm (U' e - 1) < r := by
  have hadj : ∀ A ∈ S, A⁻¹ = A.adjugate := by
    intro A hA
    rw [Matrix.inv_def, hS.det_eq_one A hA]
    simp
  have hev : ∀ e ∈ F, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ X : ComplexMatrix2,
      ComplexMatrix2.operatorNorm (X - V e) < δ →
      ComplexMatrix2.operatorNorm (X - 1) < r ∧ ComplexMatrix2.operatorNorm (X.adjugate - 1) < r := by
    intro e _
    have c₁ : Continuous fun X : ComplexMatrix2 => ComplexMatrix2.operatorNorm (X - 1) :=
      continuous_norm.comp (continuous_id.sub continuous_const)
    have c₂ : Continuous fun X : ComplexMatrix2 => ComplexMatrix2.operatorNorm (X.adjugate - 1) :=
      continuous_norm.comp (Continuous.matrix_adjugate continuous_id |>.sub continuous_const)
    have h₁ : ∀ᶠ X in 𝓝 (V e), ComplexMatrix2.operatorNorm (X - 1) < r :=
      (isOpen_lt c₁ continuous_const).mem_nhds (hr e)
    have h₂ : ∀ᶠ X in 𝓝 (V e), ComplexMatrix2.operatorNorm (X.adjugate - 1) < r := by
      refine (isOpen_lt c₂ continuous_const).mem_nhds ?_
      show ComplexMatrix2.operatorNorm ((V e).adjugate - 1) < r
      rw [← hadj _ (hV.1 e), ← hV.2 e]
      exact hr _
    obtain ⟨δ, hδ, H⟩ := Metric.eventually_nhds_iff.1 (h₁.and h₂)
    filter_upwards [Ioo_mem_nhdsGT hδ] with δ' hδ' X hX
    exact H (by rw [dist_eq_norm]; exact hX.trans hδ'.2)
  obtain ⟨ε, hH, hε⟩ := (((Filter.eventually_all_finset F).2 hev).and self_mem_nhdsWithin).exists
  refine ⟨ε, hε, fun U' hU' hoff hon e => ?_⟩
  have key : ∀ c : Edge L k j, c.IsPositivelyOriented →
      ComplexMatrix2.operatorNorm (U' c - 1) < r ∧
        ComplexMatrix2.operatorNorm ((U' c)⁻¹ - 1) < r := by
    intro c hc
    by_cases hcF : c ∈ F
    · rw [hadj _ (hU'.1 c)]
      exact hH c hcF (U' c) (hon c hcF)
    · rw [hoff c hc hcF, ← hV.2 c]
      exact ⟨hr c, hr _⟩
  rcases isPositivelyOriented_or_opposite e with he | he
  · exact (key e he).1
  · have h := (key _ he).2
    rw [← hU'.2 e.opposite, opposite_opposite] at h
    exact h
theorem nearIdentitySetsFinitelyOpen_of {S : Set ComplexMatrix2} (hS : IsUnimodularInvClosed S) :
    NearIdentitySetsFinitelyOpen L k j S := by
  intro ε hε
  refine ⟨⟨subset_rfl, fun U _ F _ => ⟨1, one_pos, fun U' h _ _ => h⟩⟩,
    ⟨fun V hV => hV.1, fun V hV F _ => ?_⟩, ⟨fun V hV => hV.1, fun V hV F _ => ?_⟩⟩
  · obtain ⟨c, hc₁, hc₂⟩ := exists_between hV.2
    have hctop : c ≠ ∞ := ne_top_of_lt hc₂
    have hcr : ENNReal.ofReal c.toReal = c := ENNReal.ofReal_toReal hctop
    have hr₀ : 0 < c.toReal := ENNReal.toReal_pos (bot_le.trans_lt hc₁).ne' hctop
    have hrε : c.toReal < ε := ENNReal.toReal_lt_of_lt_ofReal hc₂
    have hr : ∀ e : Edge L k j, ComplexMatrix2.operatorNorm (V e - 1) < c.toReal := by
      intro e
      have h₁ : ENNReal.ofReal (ComplexMatrix2.operatorNorm (V e - 1)) ≤ supDistOne V :=
        le_iSup (fun e => ENNReal.ofReal (ComplexMatrix2.operatorNorm (V e - 1))) e
      have h₂ : ENNReal.ofReal (ComplexMatrix2.operatorNorm (V e - 1)) <
          ENNReal.ofReal c.toReal := by
        rw [hcr]
        exact h₁.trans_lt hc₁
      exact (ENNReal.ofReal_lt_ofReal_iff hr₀).1 h₂
    obtain ⟨ε₀, h₀, H⟩ := nearIdentity_of_local_perturbation hS hV.1 hr F
    refine ⟨ε₀, h₀, fun U' hU' hoff hon => ⟨hU', ?_⟩⟩
    have hall := H U' hU' hoff hon
    calc supDistOne U' ≤ ENNReal.ofReal c.toReal :=
          iSup_le fun e => ENNReal.ofReal_le_ofReal (hall e).le
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 hrε
  · obtain ⟨ε₀, h₀, H⟩ := nearIdentity_of_local_perturbation hS hV.1 hV.2 F
    exact ⟨ε₀, h₀, fun U' hU' hoff hon => ⟨hU', H U' hU' hoff hon⟩⟩
theorem compactGaugeGroup_perturb_mem (hA : Tower.LeftChartFields.Claim) (hOdd : Odd L)
    (h13 : 13 ≤ L) (hj : j ≤ k) (U : Edge L k j → ComplexMatrix2)
    (hU : U ∈ fieldsValuedIn L k j PeriodicLattice.compactGaugeGroup)
    (B B' : Edge L k j → ComplexMatrix2) (hB : B ∈ edgeFormSpace (Tower.meshAt L k j))
    (hB' : B' ∈ edgeFormSpace (Tower.meshAt L k j)) (e : Edge L k j)
    (he : e.IsPositivelyOriented) (s t : ℝ) :
    ComplexMatrix2.matExp (Complex.I • (algebraMap ℝ ℂ s • B e + algebraMap ℝ ℂ t • B' e)) * U e ∈
      PeriodicLattice.compactGaugeGroup := by
  have hC : s • B + t • B' ∈ edgeFormSpace (Tower.meshAt L k j) :=
    Submodule.add_mem _ (Submodule.smul_mem _ s hB) (Submodule.smul_mem _ t hB')
  have h := (((hA.2.2 L k j ⟨hOdd, h13⟩ hj).2.1.1).1 U hU _ hC ⟨e, he⟩).1 1
  have q : ((1 : ℝ) : ℂ) • (s • B + t • B') e =
      algebraMap ℝ ℂ s • B e + algebraMap ℝ ℂ t • B' e := by
    simp only [Complex.ofReal_one, one_smul, Pi.add_apply, Pi.smul_apply, algebraMap_smul]
  have h' : Tower.LeftChartFields.leftExpMul (((1 : ℝ) : ℂ) • (s • B + t • B') e) (U e) ∈
      PeriodicLattice.compactGaugeGroup := h
  rw [q] at h'
  exact h'
theorem complexGaugeGroup_perturb_mem (hA : Tower.LeftChartFields.Claim) (hOdd : Odd L)
    (h13 : 13 ≤ L) (hj : j ≤ k) (U : Edge L k j → ComplexMatrix2)
    (hU : U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (B B' : Edge L k j → ComplexMatrix2) (hB : IsComplexTangent B) (hB' : IsComplexTangent B')
    (e : Edge L k j) (he : e.IsPositivelyOriented) (s t : ℂ) :
    ComplexMatrix2.matExp (Complex.I • (algebraMap ℂ ℂ s • B e + algebraMap ℂ ℂ t • B' e)) * U e ∈
      PeriodicLattice.complexGaugeGroup := by
  have ha := meshAt_ne_zero (k := k) (j := j) h13
  let f : Edge L k j → ComplexMatrix2 := fun c => s • B c + t • B' c
  have hfp : ∀ {c : Edge L k j}, c.IsPositivelyOriented → extendOddly f c = f c :=
    fun hc => if_pos hc
  have hfn : ∀ {c : Edge L k j}, ¬ c.IsPositivelyOriented → extendOddly f c = -f c.opposite :=
    fun hc => if_neg hc
  have hC : extendOddly f ∈ complexEdgeForms (Tower.meshAt L k j) := by
    refine ⟨fun c hc => ?_, fun c => ?_⟩
    · rw [hfp hc]
      exact Submodule.add_mem _ (Submodule.smul_mem _ s (hB c hc))
        (Submodule.smul_mem _ t (hB' c hc))
    · by_cases hc : c.IsPositivelyOriented
      · rw [hfp hc, hfn (not_isPositivelyOriented_opposite ha hc), opposite_opposite]
      · have hr := (isPositivelyOriented_or_opposite c).resolve_left hc
        rw [hfp hr, hfn hc, neg_neg]
  have h := (((hA.2.2 L k j ⟨hOdd, h13⟩ hj).2.1.1).2 U hU _ hC ⟨e, he⟩).1 1
  have h' : Tower.LeftChartFields.leftExpMul ((1 : ℂ) • extendOddly f e) (U e) ∈
      PeriodicLattice.complexGaugeGroup := h
  rw [one_smul, hfp he] at h'
  exact h'
theorem presentationsAgreeAndBallsOpen_of_claim (hA : Tower.LeftChartFields.Claim) :
    PresentationsAgreeAndBallsOpen := by
  intro L k j hOdd h13 hj
  refine ⟨⟨?_, ?_, ?_, ?_⟩, nearIdentitySetsFinitelyOpen_of isUnimodularInvClosed_compactGaugeGroup,
    nearIdentitySetsFinitelyOpen_of isUnimodularInvClosed_complexGaugeGroup⟩
  · exact presentationsAgreeAlongPerturbations_of isUnimodularInvClosed_compactGaugeGroup h13 ℝ _ ℂ
      fun U hU B B' hB hB' e he s t =>
        compactGaugeGroup_perturb_mem hA hOdd h13 hj U hU B B' hB hB' e he s t
  · exact presentationsAgreeAlongPerturbations_of isUnimodularInvClosed_compactGaugeGroup h13 ℝ _
      ComplexMatrix2 fun U hU B B' hB hB' e he s t =>
        compactGaugeGroup_perturb_mem hA hOdd h13 hj U hU B B' hB hB' e he s t
  · exact presentationsAgreeAlongPerturbations_of isUnimodularInvClosed_complexGaugeGroup h13 ℂ _ ℂ
      fun U hU B B' hB hB' e he s t =>
        complexGaugeGroup_perturb_mem hA hOdd h13 hj U hU B B' hB hB' e he s t
  · exact presentationsAgreeAlongPerturbations_of isUnimodularInvClosed_complexGaugeGroup h13 ℂ _
      ComplexMatrix2 fun U hU B B' hB hB' e he s t =>
        complexGaugeGroup_perturb_mem hA hOdd h13 hj U hU B B' hB hB' e he s t
end YangMills.Construction.Tower.FullSpace.UniqueValue
end
