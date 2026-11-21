import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Matrices.CalculusOfHolomorphicMaps
import YangMills.Construction.Matrices.SpecialUnitaryPowerComposition
import YangMills.Construction.Towers.ChainRuleAtTheSideInfinityInTheLeftChart
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Towers.MapOfAWritingNearThePoint
import YangMills.Construction.Towers.OneValueForEveryWriting
import YangMills.Construction.Towers.WritingsOfAChainInTheLeftChart
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices YangMills.Construction.Coordinates
open YangMills.Construction.LocalPresentations
open YangMills.Construction.Tower.FullSpace YangMills.Construction.Tower.FullSpace.LeftChartFacts
namespace FullSpaceChainRule
theorem opposite_isPositivelyOriented_of_not {a : ℝ} (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  have h := InfiniteLattice.xor_mem_positiveLinks ha b
  simp only [InfiniteLattice.mem_positiveLinks_iff] at h
  rcases h with ⟨h₁, -⟩ | ⟨h₂, -⟩
  · exact absurd h₁ hb
  · exact h₂
theorem extendOddly_eq_of_positive {a : ℝ} (ha : 0 < a)
    {f g G : InfiniteLattice.Link a → ComplexMatrix2}
    (hG : G = FullSpace.extendOddly g)
    (h : ∀ c : InfiniteLattice.Link a, c.IsPositivelyOriented → f c = G c) :
    FullSpace.extendOddly f = G := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · have h0 : FullSpace.extendOddly f b = f b := by simp [FullSpace.extendOddly, hb]
    rw [h0, h b hb]
  · have hr := opposite_isPositivelyOriented_of_not ha hb
    have h1 := h _ hr
    have h2 : G b.opposite = g b.opposite := by
      rw [hG]
      simp [FullSpace.extendOddly, hr]
    rw [hG]
    simp only [FullSpace.extendOddly, hb, if_false]
    rw [h1, h2]
theorem logDirectionalDeriv_congr_real {α : Type} {φ₁ φ₂ : (α → ComplexMatrix2) → ComplexMatrix2}
    {W : ComplexMatrix2} {B : α → ComplexMatrix2}
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), φ₁ (algebraMap ℝ ℂ t • B) = φ₂ (algebraMap ℝ ℂ t • B)) :
    logDirectionalDeriv ℝ φ₁ W B = logDirectionalDeriv ℝ φ₂ W B := by
  unfold logDirectionalDeriv
  refine congrArg (fun z => Complex.I⁻¹ • z) (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [h] with t ht
  rw [ht]
theorem logDirectionalDeriv_congr_complex {α : Type}
    {φ₁ φ₂ : (α → ComplexMatrix2) → ComplexMatrix2} {W : ComplexMatrix2} {B : α → ComplexMatrix2}
    (h : ∀ᶠ t in 𝓝 (0 : ℂ), φ₁ (algebraMap ℂ ℂ t • B) = φ₂ (algebraMap ℂ ℂ t • B)) :
    logDirectionalDeriv ℂ φ₁ W B = logDirectionalDeriv ℂ φ₂ W B := by
  unfold logDirectionalDeriv
  refine congrArg (fun z => Complex.I⁻¹ • z) (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [h] with t ht
  rw [ht]
section Chain
variable {L k j j' j'' : ℕ}
open Classical in
def unionSupport {S₂ : Finset (FullSpace.Edge L k j')}
    (w : S₂ → FullSpace.LocalData L k j ComplexMatrix2) : Finset (FullSpace.Edge L k j) :=
  Finset.univ.biUnion fun c' => (w c').support
open Classical in
theorem mem_unionSupport {S₂ : Finset (FullSpace.Edge L k j')}
    {w : S₂ → FullSpace.LocalData L k j ComplexMatrix2} {b : FullSpace.Edge L k j} :
    b ∈ unionSupport w ↔ ∃ c', b ∈ (w c').support := by
  simp [unionSupport]
theorem support_subset_unionSupport {S₂ : Finset (FullSpace.Edge L k j')}
    (w : S₂ → FullSpace.LocalData L k j ComplexMatrix2) (c' : S₂) :
    (w c').support ⊆ unionSupport w :=
  fun _ hb => mem_unionSupport.2 ⟨c', hb⟩
def innerTuple {S₂ : Finset (FullSpace.Edge L k j')}
    (w : S₂ → FullSpace.LocalData L k j ComplexMatrix2)
    (x : unionSupport w → ComplexMatrix2) : S₂ → ComplexMatrix2 :=
  fun c' => (w c').fn (restrictTuple (support_subset_unionSupport w c') x)
def innerRegion (𝒢 : Set ComplexMatrix2) {S₂ : Finset (FullSpace.Edge L k j')}
    (w : S₂ → FullSpace.LocalData L k j ComplexMatrix2)
    (P : ∀ c', Set ((w c').support → ComplexMatrix2)) : Set (unionSupport w → ComplexMatrix2) :=
  {x | x ∈ FullSpace.edgeProduct 𝒢 (unionSupport w) ∧
    ∀ c', restrictTuple (support_subset_unionSupport w c') x ∈ P c'}
def compositeRegion (𝒢 : Set ComplexMatrix2) {S₂ : Finset (FullSpace.Edge L k j')}
    (w : S₂ → FullSpace.LocalData L k j ComplexMatrix2)
    (P : ∀ c', Set ((w c').support → ComplexMatrix2))
    (O₂ : Set (S₂ → ComplexMatrix2)) : Set (unionSupport w → ComplexMatrix2) :=
  innerRegion 𝒢 w P ∩ innerTuple w ⁻¹' O₂
structure IsChainPresentation (𝒢 : Set ComplexMatrix2)
    (𝔇₁ : Set (FullSpace.Edge L k j → ComplexMatrix2))
    (𝔇₂ : Set (FullSpace.Edge L k j' → ComplexMatrix2))
    (m₁ : (FullSpace.Edge L k j → ComplexMatrix2) → FullSpace.Edge L k j' → ComplexMatrix2)
    (m₂ : (FullSpace.Edge L k j' → ComplexMatrix2) → FullSpace.Edge L k j'' → ComplexMatrix2)
    (U : FullSpace.Edge L k j → ComplexMatrix2) (c : FullSpace.Edge L k j'')
    (S₂ : Finset (FullSpace.Edge L k j'))
    (O₂ : Set (S₂ → ComplexMatrix2)) (f₂ : (S₂ → ComplexMatrix2) → ComplexMatrix2)
    (w : S₂ → FullSpace.LocalData L k j ComplexMatrix2)
    (P : ∀ c', Set ((w c').support → ComplexMatrix2)) : Prop where
  outer : IsLocalPresentation 𝒢 𝔇₂ (fun W => m₂ W c) (m₁ U) S₂ O₂ f₂
  inner : ∀ c' : S₂,
    IsLocalPresentation 𝒢 𝔇₁ (fun U' => m₁ U' c') U (w c').support (w c').region (w c').fn
  isOpen_sets : ∀ c', ComplexMatrix2.IsRelativelyOpen (FullSpace.edgeProduct 𝒢 (w c').support) (P c')
  sets_subset : ∀ c', P c' ⊆ (w c').region
  mem_sets : ∀ c', restrictToEdges (w c').support U ∈ P c'
  fn_mem : ∀ c', ∀ x ∈ P c', (w c').fn x ∈ 𝒢
variable {𝒢 : Set ComplexMatrix2} {𝔇₁ : Set (FullSpace.Edge L k j → ComplexMatrix2)}
  {𝔇₂ : Set (FullSpace.Edge L k j' → ComplexMatrix2)}
  {m₁ : (FullSpace.Edge L k j → ComplexMatrix2) → FullSpace.Edge L k j' → ComplexMatrix2}
  {m₂ : (FullSpace.Edge L k j' → ComplexMatrix2) → FullSpace.Edge L k j'' → ComplexMatrix2}
  {U : FullSpace.Edge L k j → ComplexMatrix2} {c : FullSpace.Edge L k j''}
  {S₂ : Finset (FullSpace.Edge L k j')}
  {O₂ : Set (S₂ → ComplexMatrix2)} {f₂ : (S₂ → ComplexMatrix2) → ComplexMatrix2}
  {w : S₂ → FullSpace.LocalData L k j ComplexMatrix2}
  {P : ∀ c', Set ((w c').support → ComplexMatrix2)}
theorem IsChainPresentation.unionSupport_finite
    (d : IsChainPresentation 𝒢 𝔇₁ 𝔇₂ m₁ m₂ U c S₂ O₂ f₂ w P) :
    IsFinitePositiveEdgeSet (unionSupport w) := by
  obtain ⟨c₀, hc₀⟩ := d.outer.1.1
  obtain ⟨b, hb⟩ := (d.inner ⟨c₀, hc₀⟩).1.1
  refine ⟨⟨b, support_subset_unionSupport w _ hb⟩, fun b' hb' => ?_⟩
  obtain ⟨c', hc'⟩ := mem_unionSupport.1 hb'
  exact (d.inner c').1.2 b' hc'
theorem IsChainPresentation.innerTuple_restrictToEdges
    (d : IsChainPresentation 𝒢 𝔇₁ 𝔇₂ m₁ m₂ U c S₂ O₂ f₂ w P)
    {U' : FullSpace.Edge L k j → ComplexMatrix2} (hU' : U' ∈ 𝔇₁)
    (h : ∀ c', restrictTuple (support_subset_unionSupport w c')
      (restrictToEdges (unionSupport w) U') ∈ (w c').region) :
    innerTuple w (restrictToEdges (unionSupport w) U') = restrictToEdges S₂ (m₁ U') := by
  funext c'
  exact ((d.inner c').2.2.2 U' hU' (h c')).symm
theorem IsChainPresentation.isLocalPresentation
    (d : IsChainPresentation 𝒢 𝔇₁ 𝔇₂ m₁ m₂ U c S₂ O₂ f₂ w P)
    (hU₁ : U ∈ 𝔇₁) (hG : ∀ b, U b ∈ 𝒢)
    (hopen : ComplexMatrix2.IsRelativelyOpen (FullSpace.edgeProduct 𝒢 (unionSupport w))
      (compositeRegion 𝒢 w P O₂)) :
    IsLocalPresentation 𝒢 (compositeDomain 𝔇₁ 𝔇₂ m₁) (fun U' => (m₂ ∘ m₁) U' c) U
      (unionSupport w) (compositeRegion 𝒢 w P O₂) (f₂ ∘ innerTuple w) := by
  refine ⟨d.unionSupport_finite, hopen, ⟨⟨fun b => hG b, fun c' => d.mem_sets c'⟩, ?_⟩, ?_⟩
  · have := d.innerTuple_restrictToEdges hU₁ fun c' => d.sets_subset c' (d.mem_sets c')
    show innerTuple w (restrictToEdges (unionSupport w) U) ∈ O₂
    rw [this]
    exact d.outer.2.2.1
  · rintro U' ⟨hU'₁, hU'₂⟩ ⟨⟨-, hP⟩, hO⟩
    have h := d.innerTuple_restrictToEdges hU'₁ fun c' => d.sets_subset c' (hP c')
    have hO' : restrictToEdges S₂ (m₁ U') ∈ O₂ := by
      rw [← h]
      exact hO
    show m₂ (m₁ U') c = f₂ (innerTuple w (restrictToEdges (unionSupport w) U'))
    rw [h]
    exact d.outer.2.2.2 _ hU'₂ hO'
theorem exists_chainPresentation {K₁ : PresentationClass L k j ComplexMatrix2}
    {K₂ : PresentationClass L k j' ComplexMatrix2}
    {kept : Set (Set ComplexMatrix2)} (hH : NearPointProperties L k j 𝒢 kept)
    (h𝔇₁ : IsFinitelyOpen 𝒢 𝔇₁) (hm₁ : ∀ U' ∈ 𝔇₁, ∀ c', m₁ U' c' ∈ 𝒢) (hU : U ∈ 𝔇₁)
    (hw₁ : ∀ c' : FullSpace.Edge L k j', c'.IsPositivelyOriented →
      ∃ (F : Finset (FullSpace.Edge L k j)) (O : Set (F → ComplexMatrix2))
        (f : (F → ComplexMatrix2) → ComplexMatrix2),
        IsLocalPresentation 𝒢 𝔇₁ (fun U' => m₁ U' c') U F O f ∧ K₁ F O f)
    (hw₂ : ∃ (F : Finset (FullSpace.Edge L k j')) (O : Set (F → ComplexMatrix2))
        (f : (F → ComplexMatrix2) → ComplexMatrix2),
        IsLocalPresentation 𝒢 𝔇₂ (fun W => m₂ W c) (m₁ U) F O f ∧ K₂ F O f) :
    ∃ (S₂ : Finset (FullSpace.Edge L k j')) (O₂ : Set (S₂ → ComplexMatrix2))
      (f₂ : (S₂ → ComplexMatrix2) → ComplexMatrix2)
      (w : S₂ → FullSpace.LocalData L k j ComplexMatrix2)
      (P : ∀ c', Set ((w c').support → ComplexMatrix2)),
      IsChainPresentation 𝒢 𝔇₁ 𝔇₂ m₁ m₂ U c S₂ O₂ f₂ w P ∧ K₂ S₂ O₂ f₂ ∧
        ∀ c', K₁ (w c').support (w c').region (w c').fn := by
  obtain ⟨S₂, O₂, f₂, hW₂, hK₂⟩ := hw₂
  have h1 : ∀ c' : S₂, ∃ t : FullSpace.LocalData L k j ComplexMatrix2,
      IsLocalPresentation 𝒢 𝔇₁ (fun U' => m₁ U' c') U t.support t.region t.fn ∧
        K₁ t.support t.region t.fn := by
    intro c'
    obtain ⟨F, O, f, h, hk⟩ := hw₁ c' (hW₂.1.2 c' c'.2)
    exact ⟨⟨F, O, f⟩, h, hk⟩
  choose w hw hwK using h1
  have h2 : ∀ c' : S₂, ∃ P : Set ((w c').support → ComplexMatrix2),
      ComplexMatrix2.IsRelativelyOpen (FullSpace.edgeProduct 𝒢 (w c').support) P ∧
        P ⊆ (w c').region ∧
        restrictToEdges (w c').support U ∈ P ∧ ∀ x ∈ P, (w c').fn x ∈ 𝒢 := by
    intro c'
    obtain ⟨⟨P, hP, hsub, hmem, hval, -⟩, -⟩ :=
      (hH 𝔇₁ (fun U' => m₁ U' c') U h𝔇₁ hU).2.2 _ _ _ (hw c')
    refine ⟨P, hP, hsub, hmem, fun x hx => ?_⟩
    obtain ⟨U', hU', he⟩ := hval x hx
    rw [he]
    exact hm₁ U' hU' c'
  choose P hP hsub hmem hval using h2
  exact ⟨S₂, O₂, f₂, w, P, ⟨hW₂, hw, hP, hsub, hmem, hval⟩, hK₂, hwK⟩
theorem valueViaPresentation_eventuallyEq {𝕜 : Type} [NormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    {IsDir : (FullSpace.Edge L k j → ComplexMatrix2) → Prop}
    (hone : UniqueValue.PresentationsAgreeAlongPerturbations L k j 𝕜 𝒢 IsDir ComplexMatrix2)
    {𝔇 : Set (FullSpace.Edge L k j → ComplexMatrix2)} (h𝔇 : IsFinitelyOpen 𝒢 𝔇)
    {K : PresentationClass L k j ComplexMatrix2}
    {h : (FullSpace.Edge L k j → ComplexMatrix2) → ComplexMatrix2} (hU : U ∈ 𝔇)
    {F : Finset (FullSpace.Edge L k j)} {O : Set (F → ComplexMatrix2)}
    {f : (F → ComplexMatrix2) → ComplexMatrix2}
    (hw : IsLocalPresentation 𝒢 𝔇 h U F O f) (hK : K F O f)
    {B : FullSpace.Edge L k j → ComplexMatrix2} (hB : IsDir B) :
    ∀ᶠ t in 𝓝 (0 : 𝕜), valueViaPresentation 𝒢 𝔇 K h U (algebraMap 𝕜 ℂ t • B) =
      f fun b => ComplexMatrix2.matExp (Complex.I • (algebraMap 𝕜 ℂ t • B) b) * U b := by
  have hs : IsLocalPresentation 𝒢 𝔇 h U (chosenPresentation 𝒢 𝔇 K h U).support
      (chosenPresentation 𝒢 𝔇 K h U).region (chosenPresentation 𝒢 𝔇 K h U).fn ∧
      K (chosenPresentation 𝒢 𝔇 K h U).support (chosenPresentation 𝒢 𝔇 K h U).region
        (chosenPresentation 𝒢 𝔇 K h U).fn :=
    Classical.epsilon_spec
      (p := fun t : FullSpace.LocalData L k j ComplexMatrix2 =>
        IsLocalPresentation 𝒢 𝔇 h U t.support t.region t.fn ∧ K t.support t.region t.fn)
      ⟨⟨F, O, f⟩, hw, hK⟩
  obtain ⟨ε, hε, H⟩ := hone 𝔇 h𝔇 h U hU _ _ _ F O f hs.1 hw B B hB hB
  have hmv : ∀ (F' : Finset (FullSpace.Edge L k j)) (t : 𝕜),
      UniqueValue.perturbedTuple F' B B U (algebraMap 𝕜 ℂ t) (algebraMap 𝕜 ℂ 0) =
        fun b : F' => ComplexMatrix2.matExp (Complex.I • (algebraMap 𝕜 ℂ t • B) b) * U b := by
    intro F' t
    funext b
    simp [UniqueValue.perturbedTuple]
  filter_upwards [Metric.ball_mem_nhds (0 : 𝕜) hε] with t ht
  have ht' : ‖t‖ < ε := by simpa using ht
  have h3 := (H t 0 ht' (by simpa using hε)).2.2
  rw [hmv, hmv] at h3
  exact h3
theorem chainRule_of_compose (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    [NormedSpace 𝕜 ComplexMatrix2] {K₁ : PresentationClass L k j ComplexMatrix2}
    {K₂ : PresentationClass L k j' ComplexMatrix2}
    {kept : Set (Set ComplexMatrix2)} {IsDir : (FullSpace.Edge L k j → ComplexMatrix2) → Prop}
    (hH : NearPointProperties L k j 𝒢 kept)
    (hone : UniqueValue.PresentationsAgreeAlongPerturbations L k j 𝕜 𝒢 IsDir ComplexMatrix2)
    (hcongr : ∀ (φ₁ φ₂ : (FullSpace.Edge L k j → ComplexMatrix2) → ComplexMatrix2)
      (W : ComplexMatrix2) (B : FullSpace.Edge L k j → ComplexMatrix2),
      (∀ᶠ t in 𝓝 (0 : 𝕜), φ₁ (algebraMap 𝕜 ℂ t • B) = φ₂ (algebraMap 𝕜 ℂ t • B)) →
        logDirectionalDeriv 𝕜 φ₁ W B = logDirectionalDeriv 𝕜 φ₂ W B)
    (hcompose : ∀ (U : FullSpace.Edge L k j → ComplexMatrix2) (c : FullSpace.Edge L k j'')
      (S₂ : Finset (FullSpace.Edge L k j')) (O₂ : Set (S₂ → ComplexMatrix2))
      (f₂ : (S₂ → ComplexMatrix2) → ComplexMatrix2)
      (w : S₂ → FullSpace.LocalData L k j ComplexMatrix2)
      (P : ∀ c', Set ((w c').support → ComplexMatrix2)),
      IsChainPresentation 𝒢 𝔇₁ 𝔇₂ m₁ m₂ U c S₂ O₂ f₂ w P → K₂ S₂ O₂ f₂ →
      (∀ c', K₁ (w c').support (w c').region (w c').fn) →
      ComplexMatrix2.IsRelativelyOpen (FullSpace.edgeProduct 𝒢 (unionSupport w))
          (compositeRegion 𝒢 w P O₂) ∧
        K₁ (unionSupport w) (compositeRegion 𝒢 w P O₂) (f₂ ∘ innerTuple w))
    (h𝔇₁ : IsFinitelyOpen 𝒢 𝔇₁) (hm₁ : ∀ U' ∈ 𝔇₁, ∀ c', m₁ U' c' ∈ 𝒢)
    (hw₁ : ∀ U' ∈ 𝔇₁, ∀ c' : FullSpace.Edge L k j', c'.IsPositivelyOriented →
      ∃ (F : Finset (FullSpace.Edge L k j)) (O : Set (F → ComplexMatrix2))
        (f : (F → ComplexMatrix2) → ComplexMatrix2),
        IsLocalPresentation 𝒢 𝔇₁ (fun U'' => m₁ U'' c') U' F O f ∧ K₁ F O f)
    (hw₂ : ∀ W ∈ 𝔇₂, ∀ c : FullSpace.Edge L k j'', c.IsPositivelyOriented →
      ∃ (F : Finset (FullSpace.Edge L k j')) (O : Set (F → ComplexMatrix2))
        (f : (F → ComplexMatrix2) → ComplexMatrix2),
        IsLocalPresentation 𝒢 𝔇₂ (fun W' => m₂ W' c) W F O f ∧ K₂ F O f)
    (hDc : IsFinitelyOpen 𝒢 (compositeDomain 𝔇₁ 𝔇₂ m₁)) :
    (∀ U ∈ compositeDomain 𝔇₁ 𝔇₂ m₁, ∀ c : FullSpace.Edge L k j'', c.IsPositivelyOriented →
      ∃ (F : Finset (FullSpace.Edge L k j)) (O : Set (F → ComplexMatrix2))
        (f : (F → ComplexMatrix2) → ComplexMatrix2),
        IsLocalPresentation 𝒢 (compositeDomain 𝔇₁ 𝔇₂ m₁) (fun U' => (m₂ ∘ m₁) U' c) U F O f ∧
          K₁ F O f) ∧
    ∀ U ∈ compositeDomain 𝔇₁ 𝔇₂ m₁, ∀ c : FullSpace.Edge L k j'', c.IsPositivelyOriented →
      ∀ B : FullSpace.Edge L k j → ComplexMatrix2, IsDir B → ∀ v : ComplexMatrix2,
      LeftFormulaViaPresentations 𝕜 𝒢 𝔇₁ 𝔇₂ K₁ K₂ m₁ m₂ U B c v →
      logDirectionalDeriv 𝕜
        (valueViaPresentation 𝒢 (compositeDomain 𝔇₁ 𝔇₂ m₁) K₁ (fun U' => (m₂ ∘ m₁) U' c) U)
        ((m₂ ∘ m₁) U c) B = v := by
  have hG : ∀ U ∈ compositeDomain 𝔇₁ 𝔇₂ m₁, ∀ b, U b ∈ 𝒢 :=
    fun U hU b => (hDc.1 hU).1 b
  constructor
  · intro U hU c hc
    obtain ⟨S₂, O₂, f₂, w, P, d, hk₂, hk₁⟩ :=
      exists_chainPresentation (c := c) (K₂ := K₂) hH h𝔇₁ hm₁ hU.1 (hw₁ U hU.1)
        (hw₂ _ hU.2 c hc)
    obtain ⟨hopen, hk⟩ := hcompose U c S₂ O₂ f₂ w P d hk₂ hk₁
    exact ⟨_, _, _, d.isLocalPresentation hU.1 (hG U hU) hopen, hk⟩
  · intro U hU c hc B hB v hv
    obtain ⟨S₂, O₂, f₂, w, P, d, hk₂, hk₁⟩ :=
      exists_chainPresentation (c := c) (K₂ := K₂) hH h𝔇₁ hm₁ hU.1 (hw₁ U hU.1)
        (hw₂ _ hU.2 c hc)
    obtain ⟨hopen, hk⟩ := hcompose U c S₂ O₂ f₂ w P d hk₂ hk₁
    have hwr := d.isLocalPresentation hU.1 (hG U hU) hopen
    have hform := (hv S₂ O₂ f₂ w d.outer hk₂ fun c' => ⟨d.inner c', hk₁ c'⟩).2
    have hzero : presentedPoint w U 0 = restrictToEdges S₂ (m₁ U) := by
      funext c'
      have h0 : (fun b : (w c').support =>
          ComplexMatrix2.matExp (Complex.I • (0 : FullSpace.Edge L k j → ComplexMatrix2) b) * U b) =
          restrictToEdges (w c').support U := by
        funext b
        simp [ComplexMatrix2.matExp, restrictToEdges, NormedSpace.exp_zero]
      show (w c').fn _ = _
      rw [h0]
      exact ((d.inner c').2.2.2 U hU.1 (d.sets_subset c' (d.mem_sets c'))).symm
    have hW : (m₂ ∘ m₁) U c = f₂ (presentedPoint w U 0) := by
      rw [hzero]
      exact d.outer.2.2.2 _ hU.2 d.outer.2.2.1
    rw [← hform, hW]
    refine hcongr _ _ _ _ ?_
    filter_upwards [valueViaPresentation_eventuallyEq hone hDc hU hwr hk hB] with t ht
    rw [ht]
    rfl
theorem isRelativelyOpen_iInter {E J : Type} [TopologicalSpace E] [Finite J] [Nonempty J]
    {M : Set E} {A : J → Set E} (h : ∀ i, ComplexMatrix2.IsRelativelyOpen M (A i)) :
    ComplexMatrix2.IsRelativelyOpen M (⋂ i, A i) := by
  choose V hV hA using h
  refine ⟨⋂ i, V i, isOpen_iInter_of_finite hV, ?_⟩
  ext x
  simp only [mem_iInter, mem_inter_iff]
  constructor
  · intro hx
    refine ⟨fun i => ?_, ?_⟩
    · have := hx i
      rw [hA i] at this
      exact this.1
    · obtain ⟨i⟩ := ‹Nonempty J›
      have := hx i
      rw [hA i] at this
      exact this.2
  · rintro ⟨h1, h2⟩ i
    rw [hA i]
    exact ⟨h1 i, h2⟩
theorem compose_differentiable (hC : specialUnitaryPower.Composition.CompositionProperties)
    (hE : PowerExpCharts.ExpChartsStatement)
    (d : IsChainPresentation PeriodicLattice.compactGaugeGroup 𝔇₁ 𝔇₂ m₁ m₂ U c S₂ O₂ f₂ w P)
    (hk₂ : differentiablePresentations L k j' ComplexMatrix2 S₂ O₂ f₂)
    (hk₁ : ∀ c', differentiablePresentations L k j ComplexMatrix2 (w c').support (w c').region
      (w c').fn) :
    ComplexMatrix2.IsRelativelyOpen
        (FullSpace.edgeProduct PeriodicLattice.compactGaugeGroup (unionSupport w))
        (compositeRegion PeriodicLattice.compactGaugeGroup w P O₂) ∧
      differentiablePresentations L k j ComplexMatrix2 (unionSupport w)
        (compositeRegion PeriodicLattice.compactGaugeGroup w P O₂) (f₂ ∘ innerTuple w) := by
  have hS : Nonempty S₂ := d.outer.1.1.to_subtype
  have hF : Nonempty (unionSupport w) := d.unionSupport_finite.1.to_subtype
  have hstep : ∀ c', specialUnitaryPower.IsOpenSubset
        (specialUnitaryPower (unionSupport w) ∩
          (fun x (t : (w c').support) => x ⟨t, support_subset_unionSupport w c' t.2⟩) ⁻¹' P c') ∧
      EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower (unionSupport w))
        (specialUnitaryPower (unionSupport w) ∩
          (fun x (t : (w c').support) => x ⟨t, support_subset_unionSupport w c' t.2⟩) ⁻¹' P c')
        ((w c').fn ∘ fun x (t : (w c').support) => x ⟨t, support_subset_unionSupport w c' t.2⟩) := by
    intro c'
    have : Nonempty (w c').support := (d.inner c').1.1.to_subtype
    obtain ⟨-, -, hread, -, hcomp⟩ := hC (unionSupport w) (w c').support
    have hP : EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower (w c').support) (P c')
        (w c').fn :=
      ⟨d.isOpen_sets c', fun ch => ((hk₁ c').2 ch).mono fun u hu => ⟨hu.1, d.sets_subset c' hu.2⟩⟩
    exact (hcomp _ _ _ _ (hread fun t => ⟨t, support_subset_unionSupport w c' t.2⟩) hP).2
  have hset : innerRegion PeriodicLattice.compactGaugeGroup w P =
      ⋂ c', (specialUnitaryPower (unionSupport w) ∩
        (fun x (t : (w c').support) => x ⟨t, support_subset_unionSupport w c' t.2⟩) ⁻¹' P c') := by
    ext x
    simp only [mem_iInter]
    constructor
    · rintro ⟨h1, h2⟩ c'
      exact ⟨h1, h2 c'⟩
    · intro h
      obtain ⟨c₀⟩ := hS
      exact ⟨(h c₀).1, fun c' => (h c').2⟩
  have hopen : specialUnitaryPower.IsOpenSubset
      (innerRegion PeriodicLattice.compactGaugeGroup w P) := by
    rw [hset]
    exact isRelativelyOpen_iInter fun c' => (hstep c').1
  have hmaps : MapsTo (innerTuple w) (innerRegion PeriodicLattice.compactGaugeGroup w P)
      (specialUnitaryPower S₂) :=
    fun x hx c' => d.fn_mem c' _ (hx.2 c')
  have hmem : ∀ c', EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower (unionSupport w))
      (innerRegion PeriodicLattice.compactGaugeGroup w P) fun x => innerTuple w x c' := by
    intro c'
    refine ⟨hopen, fun ch => ((hstep c').2.2 ch).mono fun u hu => ⟨hu.1, ?_⟩⟩
    rw [hset] at hu
    exact mem_iInter.1 hu.2 c'
  have hinto : specialUnitaryPower.IsDifferentiableInto
      (innerRegion PeriodicLattice.compactGaugeGroup w P) (innerTuple w) :=
    ((hE (unionSupport w) S₂).2.2.2.2.2.2.1 _ _ hopen hmaps).2 hmem
  obtain ⟨-, -, -, -, hcomp⟩ := hC (unionSupport w) S₂
  obtain ⟨-, h1, h2⟩ := hcomp _ _ _ _ hinto hk₂
  exact ⟨h1, h2⟩
section Holomorphic
open YangMills.Construction.Matrices.GroupLieProduct
variable {σ τ : Type}
def groupFactors (p : σ ⊕ Empty → ComplexMatrix2) : σ → ComplexMatrix2 := fun b => p (.inl b)
theorem asGroupFactors_groupFactors (p : σ ⊕ Empty → ComplexMatrix2) :
    asGroupFactors (groupFactors p) = p := by apply _root_.YangMills.DeltaSharedProofs.p4358 <;> assumption
theorem asGroupFactors_mem_iff {x : σ → ComplexMatrix2} :
    asGroupFactors x ∈ GroupLieProduct σ Empty ↔ x ∈ unimodularPi σ := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.asGroupFactors_mem_iff <;> assumption
theorem continuous_groupFactors : Continuous (groupFactors (σ := σ)) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.continuous_leftComponents <;> assumption
theorem continuous_asGroupFactors : Continuous (asGroupFactors (σ := σ)) := by apply _root_.YangMills.SharedProofs.p11373 <;> assumption
theorem isRelativelyOpen_image_asGroupFactors {X : Set (σ → ComplexMatrix2)}
    (h : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) X) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct σ Empty) (asGroupFactors '' X) := by
  obtain ⟨V, hV, rfl⟩ := h
  refine ⟨groupFactors ⁻¹' V, hV.preimage continuous_groupFactors, ?_⟩
  ext p
  constructor
  · rintro ⟨x, ⟨hxV, hxG⟩, rfl⟩
    exact ⟨hxV, asGroupFactors_mem_iff.2 hxG⟩
  · rintro ⟨hp, hpG⟩
    refine ⟨groupFactors p, ⟨hp, ?_⟩, asGroupFactors_groupFactors p⟩
    rw [← asGroupFactors_groupFactors p] at hpG
    exact asGroupFactors_mem_iff.1 hpG
theorem isRelativelyOpen_of_image_asGroupFactors {X : Set (σ → ComplexMatrix2)}
    (hX : X ⊆ unimodularPi σ)
    (h : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct σ Empty) (asGroupFactors '' X)) :
    ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) X := by
  obtain ⟨V, hV, hE⟩ := h
  refine ⟨asGroupFactors ⁻¹' V, hV.preimage continuous_asGroupFactors, ?_⟩
  ext x
  constructor
  · intro hx
    have : asGroupFactors x ∈ V ∩ GroupLieProduct σ Empty := hE ▸ mem_image_of_mem _ hx
    exact ⟨this.1, hX hx⟩
  · rintro ⟨h1, h2⟩
    have : asGroupFactors x ∈ asGroupFactors '' X := hE ▸ ⟨h1, asGroupFactors_mem_iff.2 h2⟩
    obtain ⟨y, hy, he⟩ := this
    have : y = x := congrArg groupFactors he
    exact this ▸ hy
private def coordIndex {ρ : Type} {n : ℕ} (ν : ρ ≃ Fin n) :
    Fin (ComplexCoordinates.productDim fun _ : Fin n => ComplexCoordinates.Component.matrix) ≃
      ρ × Fin 4 :=
  (finSigmaFinEquiv (m := n) (n := fun _ => 4)).symm.trans
    ((Equiv.sigmaEquivProd (Fin n) (Fin 4)).trans (Equiv.prodCongr ν.symm (Equiv.refl _)))
private theorem matrixPiEquiv_apply {ρ : Type} {n : ℕ} (ν : ρ ≃ Fin n) (X : ρ → ComplexMatrix2)
    (i : Fin (ComplexCoordinates.productDim fun _ : Fin n =>
      ComplexCoordinates.Component.matrix)) :
    matrixPiEquiv ν X i =
      ComplexCoordinates.matrixEquiv (X (coordIndex ν i).1) (coordIndex ν i).2 :=
  rfl
theorem reindex_isHolomorphicVia {ρ ρ' : Type} {n n' : ℕ} (ν : ρ ≃ Fin n) (ν' : ρ' ≃ Fin n')
    (idx : ρ' → ρ) :
    ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν) (matrixPiEquiv ν')
      univ fun p s => p (idx s) := by
  let J : Fin (ComplexCoordinates.productDim fun _ : Fin n' =>
      ComplexCoordinates.Component.matrix) →
      Fin (ComplexCoordinates.productDim fun _ : Fin n => ComplexCoordinates.Component.matrix) :=
    fun i => (coordIndex ν).symm (idx (coordIndex ν' i).1, (coordIndex ν' i).2)
  have hJ : ∀ (x : ρ → ComplexMatrix2) i, matrixPiEquiv ν' (fun s => x (idx s)) i =
      matrixPiEquiv ν x (J i) := by
    intro x i
    rw [matrixPiEquiv_apply, matrixPiEquiv_apply]
    simp only [J, Equiv.apply_symm_apply]
  have hf : (matrixPiEquiv ν' ∘ (fun (p : ρ → ComplexMatrix2) s => p (idx s)) ∘
      (matrixPiEquiv ν).symm) = fun z i => z (J i) := by
    funext z i
    simp only [Function.comp]
    rw [hJ, Equiv.apply_symm_apply]
  unfold ComplexCoordinates.IsHolomorphicVia
  rw [hf]
  refine ⟨?_, (continuous_pi fun i => continuous_apply _).continuousOn, fun a _ i =>
    Eventually.of_forall fun ζ => differentiableAt_pi.2 fun i' => ?_⟩
  · rw [image_univ, Equiv.range_eq_univ]
    exact isOpen_univ
  · show DifferentiableAt ℂ
      (fun ζ : ℂ => a (J i') + ζ * ComplexCoordinates.stdBasisVector i (J i')) ζ
    fun_prop
theorem compose_holomorphic (hK : GroupLieProduct.HolomorphicCalculus.Properties)
    (hX : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (d : IsChainPresentation PeriodicLattice.complexGaugeGroup 𝔇₁ 𝔇₂ m₁ m₂ U c S₂ O₂ f₂ w P)
    (hk₂ : holomorphicPresentations L k j' β ComplexCoordinates.matrixEquiv S₂ O₂ f₂)
    (hk₁ : ∀ c', holomorphicPresentations L k j β ComplexCoordinates.matrixEquiv (w c').support
      (w c').region (w c').fn) :
    ComplexMatrix2.IsRelativelyOpen
        (FullSpace.edgeProduct PeriodicLattice.complexGaugeGroup (unionSupport w))
        (compositeRegion PeriodicLattice.complexGaugeGroup w P O₂) ∧
      holomorphicPresentations L k j β ComplexCoordinates.matrixEquiv (unionSupport w)
        (compositeRegion PeriodicLattice.complexGaugeGroup w P O₂) (f₂ ∘ innerTuple w) := by
  obtain ⟨hcc, -, -, hrp, -, -, -, hroc, -, -⟩ := hK
  have hS : Nonempty S₂ := d.outer.1.1.to_subtype
  let idx : ∀ c' : S₂, (w c').support ⊕ Empty → unionSupport w ⊕ Empty := fun c' =>
    Sum.elim (fun t => .inl ⟨t, support_subset_unionSupport w c' t.2⟩) Empty.elim
  let Ψ₀ : ∀ c' : S₂, (unionSupport w ⊕ Empty → ComplexMatrix2) →
      (w c').support ⊕ Empty → ComplexMatrix2 :=
    fun c' p s => p (idx c' s)
  have hGAP : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (unionSupport w) Empty)
      (GroupLieProduct (unionSupport w) Empty) := ⟨univ, isOpen_univ, (univ_inter _).symm⟩
  have hΨ₀ : ∀ c', IsHolomorphicToProduct β (GroupLieProduct (unionSupport w) Empty)
      (Ψ₀ c') := by
    intro c'
    have hmaps : MapsTo (Ψ₀ c') (univ ∩ GroupLieProduct (unionSupport w) Empty)
        (GroupLieProduct (w c').support Empty) := by
      rintro p ⟨-, hp⟩ (t | e)
      · exact hp (.inl ⟨t, support_subset_unionSupport w c' t.2⟩)
      · exact e.elim
    have := hrp (unionSupport w) Empty (w c').support Empty _ _ (Fintype.equivFin _)
      (Fintype.equivFin _) univ (Ψ₀ c') (reindex_isHolomorphicVia _ _ (idx c')) hmaps β
    rwa [univ_inter] at this
  have hW' : ∀ c', IsHolomorphicToCoords β ComplexCoordinates.matrixEquiv
      (asGroupFactors '' P c') fun q => (w c').fn (groupFactors q) := fun c' =>
    (hroc (w c').support Empty) β _ _ ComplexMatrix2 4 ComplexCoordinates.matrixEquiv _ (hk₁ c')
      (isRelativelyOpen_image_asGroupFactors (d.isOpen_sets c')) (image_mono (d.sets_subset c'))
  have hstep := fun c' => hcc (unionSupport w) Empty (w c').support Empty β _ (Ψ₀ c') hGAP
    (hΨ₀ c') ComplexMatrix2 4 ComplexCoordinates.matrixEquiv _ _ (hW' c')
  have hΨg : ∀ c' (x : unionSupport w → ComplexMatrix2), Ψ₀ c' (asGroupFactors x) =
      asGroupFactors (restrictTuple (support_subset_unionSupport w c') x) := by
    intro c' x
    funext s
    rcases s with t | e
    · rfl
    · exact e.elim
  have hset : asGroupFactors '' innerRegion PeriodicLattice.complexGaugeGroup w P =
      ⋂ c', (GroupLieProduct (unionSupport w) Empty ∩
        Ψ₀ c' ⁻¹' (asGroupFactors '' P c')) := by
    ext q
    simp only [mem_iInter]
    constructor
    · rintro ⟨x, ⟨hxG, hxP⟩, rfl⟩ c'
      refine ⟨asGroupFactors_mem_iff.2 hxG, ?_⟩
      show Ψ₀ c' (asGroupFactors x) ∈ asGroupFactors '' P c'
      rw [hΨg]
      exact mem_image_of_mem _ (hxP c')
    · intro h
      obtain ⟨c₀⟩ := hS
      have hq := (h c₀).1
      rw [← asGroupFactors_groupFactors q] at hq h ⊢
      refine mem_image_of_mem _ ⟨asGroupFactors_mem_iff.1 hq, fun c' => ?_⟩
      have h2 := (h c').2
      simp only [mem_preimage] at h2
      rw [hΨg] at h2
      obtain ⟨y, hy, he⟩ := h2
      have : y = restrictTuple (support_subset_unionSupport w c') (groupFactors q) :=
        congrArg groupFactors he
      exact this ▸ hy
  have hW₁ : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (unionSupport w) Empty)
      (asGroupFactors '' innerRegion PeriodicLattice.complexGaugeGroup w P) := by
    rw [hset]
    exact isRelativelyOpen_iInter fun c' => (hstep c').2.1
  have hmem : ∀ c', IsHolomorphicToCoords β ComplexCoordinates.matrixEquiv
      (asGroupFactors '' innerRegion PeriodicLattice.complexGaugeGroup w P)
      fun p => innerTuple w (groupFactors p) c' := by
    intro c'
    refine (hroc (unionSupport w) Empty) β _ _ ComplexMatrix2 4 ComplexCoordinates.matrixEquiv _
      (hstep c').2.2 hW₁ ?_
    rw [hset]
    exact iInter_subset _ c'
  let Ψ : (unionSupport w ⊕ Empty → ComplexMatrix2) → S₂ ⊕ Empty → ComplexMatrix2 :=
    fun p => asGroupFactors (innerTuple w (groupFactors p))
  have hΨ : IsHolomorphicToProduct β
      (asGroupFactors '' innerRegion PeriodicLattice.complexGaugeGroup w P) Ψ := by
    refine ⟨hW₁, fun i => ?_, fun e => e.elim⟩
    refine ((hX.2.2.2.1 (unionSupport w) Empty).2.1 β _ _ hW₁ ?_).2 (hmem i)
    rintro p ⟨x, hx, rfl⟩
    exact d.fn_mem i _ (hx.2 i)
  obtain ⟨-, hopen, hholo⟩ := hcc (unionSupport w) Empty S₂ Empty β _ Ψ hW₁ hΨ ComplexMatrix2 4
    ComplexCoordinates.matrixEquiv _ (fun q => f₂ (groupFactors q)) hk₂
  have hfin : asGroupFactors '' innerRegion PeriodicLattice.complexGaugeGroup w P ∩
      Ψ ⁻¹' (asGroupFactors '' O₂) =
      asGroupFactors '' compositeRegion PeriodicLattice.complexGaugeGroup w P O₂ := by
    ext q
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, y, hy, he⟩
      have : y = innerTuple w x := congrArg groupFactors he
      have hy' : innerTuple w x ∈ O₂ := this ▸ hy
      exact ⟨x, ⟨hx, hy'⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hO⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, _, hO, rfl⟩
  rw [hfin] at hopen hholo
  exact ⟨isRelativelyOpen_of_image_asGroupFactors (fun x hx => hx.1.1) hopen, hholo⟩
end Holomorphic
end Chain
end FullSpaceChainRule
open FullSpaceChainRule in
theorem FullSpaceChainRule.proof
    (hW : LeftChartChainRule)
    (hV : LocalPresentationNearPoint)
    (hO : FullSpace.UniqueValue.PresentationsAgreeAndBallsOpen)
    (hC : specialUnitaryPower.Composition.CompositionProperties)
    (hE : PowerExpCharts.ExpChartsStatement)
    (hK : GroupLieProduct.HolomorphicCalculus.Properties)
    (hX : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory) :
    FullSpaceChainRule.Statement := by
  intro L k j j' j'' hL hj hj' hj''
  have ha : 0 < meshAt L k j'' := by
    have h : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    exact zpow_pos h _
  have hWr := hW L k j j' j'' hL hj hj' hj''
  obtain ⟨-, hHr, -, hHc⟩ := hV L hL k j hj
  obtain ⟨⟨-, hOr, -, hOc⟩, -⟩ := hO L k j hL.1 hL.2 hj
  constructor
  · intro 𝔇₁ 𝔇₂ m₁ m₂ h₁ h₂ hDc
    obtain ⟨hwrit, hval⟩ := chainRule_of_compose (𝔇₁ := 𝔇₁) (𝔇₂ := 𝔇₂) (m₁ := m₁) (m₂ := m₂) ℝ
      (K₁ := differentiablePresentations L k j ComplexMatrix2)
      (K₂ := differentiablePresentations L k j' ComplexMatrix2)
      hHr hOr (fun _ _ _ _ => logDirectionalDeriv_congr_real)
      (fun U c S₂ O₂ f₂ w P d hk₂ hk₁ => compose_differentiable hC hE d hk₂ hk₁)
      h₁.1 (fun U hU c' => (h₁.2.1 hU).1 c')
      (fun U hU c' hc' => (h₁.2.2 c' hc').2 U hU) (fun W hW c hc => (h₂.2.2 c hc).2 W hW) hDc
    refine ⟨⟨hDc, fun U hU => h₂.2.1 hU.2, fun c hc => ⟨hDc.1, fun U hU => hwrit U hU c hc⟩⟩, ?_⟩
    intro U hU B hB
    exact extendOddly_eq_of_positive ha rfl fun c hc =>
      hval U hU c hc B hB _ (hWr.1 𝔇₁ 𝔇₂ m₁ m₂ h₁ h₂ U hU B hB c hc)
  · intro β 𝔇₁ 𝔇₂ m₁ m₂ h₁ h₂ hDc
    obtain ⟨hwrit, hval⟩ := chainRule_of_compose (𝔇₁ := 𝔇₁) (𝔇₂ := 𝔇₂) (m₁ := m₁) (m₂ := m₂) ℂ
      (K₁ := holomorphicPresentations L k j β ComplexCoordinates.matrixEquiv)
      (K₂ := holomorphicPresentations L k j' β ComplexCoordinates.matrixEquiv)
      hHc hOc (fun _ _ _ _ => logDirectionalDeriv_congr_complex)
      (fun U c S₂ O₂ f₂ w P d hk₂ hk₁ => compose_holomorphic hK hX β d hk₂ hk₁)
      h₁.1 (fun U hU c' => (h₁.2.1 hU).1 c')
      (fun U hU c' hc' => (h₁.2.2 c' hc').2 U hU) (fun W hW c hc => (h₂.2.2 c hc).2 W hW) hDc
    refine ⟨⟨hDc, fun U hU => h₂.2.1 hU.2, fun c hc => ⟨hDc.1, fun U hU => hwrit U hU c hc⟩⟩, ?_⟩
    intro U hU B hB
    exact extendOddly_eq_of_positive ha rfl fun c hc =>
      hval U hU c hc B hB.1 _ (hWr.2 β 𝔇₁ 𝔇₂ m₁ m₂ h₁ h₂ U hU B hB c hc)
end YangMills.Construction.Tower
end
