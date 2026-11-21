import YangMills.Construction.Lattice.CovarianceOfComplexAverages
import YangMills.Construction.Lattice.CovarianceOfComplexAveragingOfDeterminingSets
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.Lattice.LiftingIsConsistentWithTheAveragesProof
import YangMills.Construction.Lattice.SitesBondsAndPlaquettesOfSetsUnderIsometries
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ComplexDeterminingAveragingCovariance
variable {L m K : ℕ}
theorem bondPreimage_bondImage {j : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
    (h : PreservesCells σ j) (b : Bond L m j) :
    bondPreimage σ (bondImage σ b) = b := by
  have ht : ((bondImage σ b).source : FourTorus L m) = σ b.source := by
    rw [(h.2.2.2.1 b).1]
    exact h.1 _
  have hh : ((bondImage σ b).target : FourTorus L m) = σ b.target := by
    rw [(h.2.2.2.1 b).2]
    exact h.1 _
  have hex : ∃ b' : Bond L m j, (b'.source : FourTorus L m) = σ.symm (bondImage σ b).source ∧
      (b'.target : FourTorus L m) = σ.symm (bondImage σ b).target :=
    ⟨b, by rw [ht, Equiv.symm_apply_apply], by rw [hh, Equiv.symm_apply_apply]⟩
  rw [bondPreimage, dif_pos hex]
  have hs := hex.choose_spec
  exact Bond.ext (Subtype.ext (hs.1.trans (by rw [ht, Equiv.symm_apply_apply])))
    (Subtype.ext (hs.2.trans (by rw [hh, Equiv.symm_apply_apply])))
def Agree {j : ℤ} (V V' : PartialGaugeField L m j) : Prop :=
  V.support = V'.support ∧ ∀ b ∈ V.support, V.field b = V'.field b
theorem extendByOne_congr {j : ℤ} {P : Set (Bond L m j)}
    {U U' : Bond L m j → Matrices.ComplexMatrix2}
    (h : ∀ b ∈ P, U b = U' b) : onSetElseOne P U = onSetElseOne P U' := by apply _root_.YangMills.Construction.PeriodicLattice.LiftAveragesProof.extendByOne_congr <;> assumption
theorem Agree.blockAverage {j j' : ℤ} {V V' : PartialGaugeField L m j'}
    (h : Agree V V') :
    Agree (complexPartialBlockAverage V : PartialGaugeField L m j)
      (complexPartialBlockAverage V') := by
  obtain ⟨hb, hv⟩ := h
  have key : ∀ c : Bond L m j, (bondsInDoubleBlock c : Set (Bond L m j')) ⊆ V.support →
      onSetElseOne (bondsInDoubleBlock c) V.field =
        onSetElseOne (bondsInDoubleBlock c) V'.field :=
    fun c hc => extendByOne_congr fun b hb' => hv b (hc hb')
  refine ⟨?_, ?_⟩
  · ext c
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨hb ▸ h₁, key c h₁ ▸ h₂⟩
    · rintro ⟨h₁, h₂⟩
      have h₁' : (bondsInDoubleBlock c : Set (Bond L m j')) ⊆ V.support := hb ▸ h₁
      exact ⟨h₁', (key c h₁').symm ▸ h₂⟩
  · rintro c ⟨h₁, -⟩
    change complexBlockAverage (onSetElseOne (bondsInDoubleBlock c) V.field) c =
      complexBlockAverage (onSetElseOne (bondsInDoubleBlock c) V'.field) c
    rw [key c h₁]
theorem agree_complexIteratePartial {ℬ : Set (BondAtLevel L m K 0)}
    {U U' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2}
    (h : ∀ b ∈ ℬ, U b = U' b) (n : ℕ) :
    Agree (complexIteratePartial ℬ U n) (complexIteratePartial ℬ U' n) := by
  induction n with
  | zero => exact ⟨rfl, h⟩
  | succ n ih => exact ih.blockAverage
theorem isRelativelyOpen_image_biInter {A E ι : Type} [TopologicalSpace E] (v : A → E) (P : Set A)
    {S : Set ι} (hS : S.Finite) (D : ι → Set A)
    (hopen : ∀ s ∈ S, Matrices.ComplexMatrix2.IsRelativelyOpen (v '' P) (v '' D s))
    (hsat : ∀ s ∈ S, ∀ U ∈ D s, ∀ W ∈ P, v W = v U → W ∈ D s) :
    Matrices.ComplexMatrix2.IsRelativelyOpen (v '' P) (v '' {U ∈ P | ∀ s ∈ S, U ∈ D s}) := by
  choose! O hO hE using hopen
  refine ⟨⋂ s ∈ S, O s, hS.isOpen_biInter hO, ?_⟩
  ext w
  constructor
  · rintro ⟨U, ⟨hUP, hU⟩, rfl⟩
    refine ⟨mem_iInter₂.2 fun s hs => ?_, U, hUP, rfl⟩
    have hmem : v U ∈ v '' D s := ⟨U, hU s hs, rfl⟩
    rw [hE s hs] at hmem
    exact hmem.1
  · rintro ⟨hw, W, hW, rfl⟩
    refine ⟨W, ⟨hW, fun s hs => ?_⟩, rfl⟩
    have hmem : v W ∈ v '' D s := by
      rw [hE s hs]
      exact ⟨mem_iInter₂.1 hw s hs, W, hW, rfl⟩
    obtain ⟨U, hU, he⟩ := hmem
    exact hsat s hs U hU W hW he.symm
theorem determiningBondSet_finite (hL : 0 < L) (k : ℕ) (Ω : ℕ → Set (FourTorus L m)) :
    (determiningBondSet K k Ω).Finite := by
  have hbond : ∀ j : ℤ, Finite (Bond L m j) := fun j => by
    have hsite : Finite (Site L m j) := SeparatedSequences.BaseParameters.site_finite hL m j
    exact Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) fun b b' hb =>
      Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  have hlevel : ∀ j : ℕ, (univ : Set (BondAtLevel L m K j)).Finite := fun j => by
    have hj : Finite (BondAtLevel L m K j) := hbond _
    exact toFinite _
  refine ((finite_Iic k).biUnion fun j _ =>
    (hlevel j).image (Sigma.mk j : BondAtLevel L m K j → Σ j : ℕ, BondAtLevel L m K j)).subset ?_
  rintro ⟨j, c⟩ hq
  exact mem_biUnion (show j ∈ Iic k from hq.1) ⟨c, mem_univ c, rfl⟩
def definedAtImage (σ : FourTorus L m ≃ FourTorus L m) (ℬ : Set (BondAtLevel L m K 0))
    (q : Σ j : ℕ, BondAtLevel L m K j) : Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {U ∈ complexGaugeFields ℬ | bondImage σ q.2 ∈
    (complexIteratePartial (bondImage σ '' ℬ) (transportGaugeField σ U) q.1).support}
def definedAtBond (ℬ : Set (BondAtLevel L m K 0)) (q : Σ j : ℕ, BondAtLevel L m K j) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {U ∈ complexGaugeFields ℬ | q.2 ∈ (complexIteratePartial ℬ U q.1).support}
theorem defined_of_restrict_eq {σ : FourTorus L m ≃ FourTorus L m} {ℬ : Set (BondAtLevel L m K 0)}
    (hσ : PreservesCells σ (levelDepth K 0)) (q : Σ j : ℕ, BondAtLevel L m K j)
    {U W : BondAtLevel L m K 0 → Matrices.ComplexMatrix2}
    (hU : U ∈ definedAtImage σ ℬ q ∩ definedAtBond ℬ q)
    (hW : W ∈ complexGaugeFields ℬ) (hv : restrictToBonds ℬ W = restrictToBonds ℬ U) :
    W ∈ definedAtImage σ ℬ q ∩ definedAtBond ℬ q := by
  have hag : ∀ b ∈ ℬ, W b = U b := fun b hb => congrFun hv ⟨b, hb⟩
  have hag' : ∀ b ∈ bondImage σ '' ℬ,
      transportGaugeField σ W b = transportGaugeField σ U b := by
    rintro _ ⟨b, hb, rfl⟩
    change W (bondPreimage σ (bondImage σ b)) = U (bondPreimage σ (bondImage σ b))
    rw [bondPreimage_bondImage hσ]
    exact hag b hb
  refine ⟨⟨hW, ?_⟩, ⟨hW, ?_⟩⟩
  · rw [(agree_complexIteratePartial hag' q.1).1]
    exact hU.1.2
  · rw [(agree_complexIteratePartial hag q.1).1]
    exact hU.2.2
theorem holds (h₁ : ComplexAveragesCommuteWithIsometries.Statement)
    (h₂ : IsometriesPreserveCells) : Statement := by
  intro L m i σ hL hm hi hσ K k Ω hk _ hidx q₀ hq₀
  have hdepth : ∀ n ≤ k, i ≤ levelDepth K n := fun n hn => by
    obtain ⟨a, h, h', -⟩ := hidx n hn
    exact h.trans h'
  have hcarry := (h₁ L m i σ hL hm hi hσ K).2
  have hsites := h₂ L m i (levelDepth K 0) σ hL hm hi hσ (hdepth 0 (Nat.zero_le k))
  have hinner : (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0)) =
      bondImage σ '' (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) :=
    (hsites.2.2.2.2.2.2 (Ω 0)).2.2
  rw [hinner]
  generalize hB : (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) = B
  have hrev : IsReversalClosed B := by
    rw [← hB]
    exact fun _ hb => ⟨hb.2, hb.1⟩
  have H : ∀ q ∈ determiningBondSet K k Ω,
      IsHolomorphicEquation σ (complexGaugeFields B) B (definedAtImage σ B q) (definedAtBond B q)
        (fun U => complexIterate (bondImage σ '' B) (transportGaugeField σ U) q.1
          (bondImage σ q.2))
        (fun U => transportGaugeField σ (complexIterate B U q.1) (bondImage σ q.2)) :=
    fun q hq => hcarry q.1 (hq.1.trans hk) (hdepth q.1 hq.1) B hrev q.2
  have hcap : ({U ∈ complexGaugeFields B | ∀ q' ∈ bondSetImage σ (determiningBondSet K k Ω),
        ComplexIterateDefinedAt (bondImage σ '' B) (transportGaugeField σ U) q'.1 q'.2} ∩
      {U ∈ complexGaugeFields B | ∀ q' ∈ determiningBondSet K k Ω,
        ComplexIterateDefinedAt B U q'.1 q'.2}) =
      {U ∈ complexGaugeFields B | ∀ q ∈ determiningBondSet K k Ω,
        U ∈ definedAtImage σ B q ∩ definedAtBond B q} := by
    ext U
    constructor
    · rintro ⟨⟨hU, ha⟩, ⟨-, hb⟩⟩
      exact ⟨hU, fun q hq => ⟨⟨hU, ha _ ⟨q, hq, rfl⟩⟩, ⟨hU, hb q hq⟩⟩⟩
    · rintro ⟨hU, h⟩
      refine ⟨⟨hU, ?_⟩, ⟨hU, fun q hq => (h q hq).2.2⟩⟩
      rintro _ ⟨q, hq, rfl⟩
      exact (h q hq).1.2
  have hopen : Matrices.ComplexMatrix2.IsRelativelyOpen (restrictToBonds B '' complexGaugeFields B)
      (restrictToBonds B '' {U ∈ complexGaugeFields B | ∀ q ∈ determiningBondSet K k Ω,
        U ∈ definedAtImage σ B q ∩ definedAtBond B q}) := by
    refine isRelativelyOpen_image_biInter _ _
      (determiningBondSet_finite (by have := hL.2; omega) k Ω)
      (fun q => definedAtImage σ B q ∩ definedAtBond B q) (fun q hq => ?_)
      (fun q _ U hU W hW hv => defined_of_restrict_eq hsites q hU hW hv)
    obtain ⟨_, -, ho, -⟩ := (H q hq).1
    exact ho
  have hsub : {U ∈ complexGaugeFields B | ∀ q ∈ determiningBondSet K k Ω,
      U ∈ definedAtImage σ B q ∩ definedAtBond B q} ⊆
      definedAtImage σ B q₀ ∩ definedAtBond B q₀ := fun U hU => hU.2 q₀ hq₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcap]
    exact (H q₀ hq₀).1.restrict hsub hopen
  · rw [hcap]
    exact (H q₀ hq₀).2.1.restrict hsub hopen
  · rw [hcap]
    exact fun U hU => (H q₀ hq₀).2.2.1 U (hsub hU)
  · intro ht
    have hAC : ∀ q ∈ determiningBondSet K k Ω, definedAtImage σ B q = definedAtBond B q :=
      fun q hq => (H q hq).2.2.2 ht
    ext U
    constructor
    · rintro ⟨hU, h⟩
      refine ⟨hU, fun q hq => ?_⟩
      have hmem : U ∈ definedAtImage σ B q := ⟨hU, h _ ⟨q, hq, rfl⟩⟩
      rw [hAC q hq] at hmem
      exact hmem.2
    · rintro ⟨hU, h⟩
      refine ⟨hU, ?_⟩
      rintro _ ⟨q, hq, rfl⟩
      have hmem : U ∈ definedAtBond B q := ⟨hU, h q hq⟩
      rw [← hAC q hq] at hmem
      exact hmem.2
end YangMills.Construction.PeriodicLattice.ComplexDeterminingAveragingCovariance
