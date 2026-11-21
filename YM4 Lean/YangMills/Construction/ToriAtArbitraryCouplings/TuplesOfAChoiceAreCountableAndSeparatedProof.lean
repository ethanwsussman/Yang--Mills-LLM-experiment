import YangMills.Construction.ToriAtArbitraryCouplings.ChoicesClosedUnderCountablyManyMapsProof
import YangMills.Construction.ToriAtArbitraryCouplings.NormsCuttingAndNeighbourhoodsProof
import YangMills.Construction.ToriAtArbitraryCouplings.SupportsAreCompactAndCarryTheirClasses
import YangMills.Construction.ToriAtArbitraryCouplings.TuplesOfAChoiceAreCountableAndSeparated
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace ChoiceTuplesCountableSeparated
theorem countable_supportFamily (s : TorusSide) (E : Ambient) : (s.supportFamily E).Countable := by apply _root_.YangMills.Construction.ToriAtArbitraryCouplings.ChoicesStableUnderCountableMaps.countable_supportFamily <;> assumption
theorem countable_adaptedTupleSet {s : TorusSide} {E : Ambient}
    {D : s.supportFamily E → Set (s.Point E → ℝ)}
    (hD : ∀ Q, (D Q).Countable) : (s.adaptedTupleSet E D).Countable := by
  have : Countable (s.supportFamily E) := (countable_supportFamily s E).to_subtype
  unfold TorusSide.adaptedTupleSet
  refine countable_iUnion fun n => countable_iUnion fun _ => ?_
  refine (countable_iUnion fun Q : Fin n → s.supportFamily E =>
    ((countable_univ_pi fun i => hD (Q i)).image List.ofFn)).mono ?_
  rintro _ ⟨Q, φ, -, hφ, rfl⟩
  exact mem_iUnion.2 ⟨Q, φ, fun i _ => hφ i, rfl⟩
section OnQuotient
open YangMills.Construction.PeriodicSpace.Kind
variable (D : YangMills.Construction.PeriodicSpace.Params) (E' : YangMills.Construction.PeriodicSpace.Kind)
  {d : E'.Pt D → E'.Pt D → ℝ}
theorem infDist_pos_of_disjoint
    (hF : YangMills.Construction.PeriodicSpace.Kind.QuotientCompactC1.Claim)
    (hd : quotDist D E' = d) {A A' : Set (E'.Pt D)}
    (hA : YangMills.Construction.MetricNotions.IsCompactWrt d A)
    (hA' : YangMills.Construction.MetricNotions.IsCompactWrt d A') (hdis : Disjoint A A') :
    0 < ⨅ z ∈ A, ⨅ z' ∈ A', ENNReal.ofReal (d z z') := by
  subst hd
  exact (hF D E').2.2.2.1.1 A A' hA hA' hdis
end OnQuotient
def toParams (s : TorusSide) : YangMills.Construction.PeriodicSpace.Params :=
  ⟨s.L, s.admissible, s.m, 1, le_rfl⟩
theorem quotDist_torus (s : TorusSide)
    (hW : YangMills.Construction.PeriodicSpace.WellPosedness.WellPosed) :
    YangMills.Construction.PeriodicSpace.Kind.quotDist (toParams s) .torus = s.pointDist .torus := by
  funext y y'
  exact ((hW (toParams s) .torus).2.2.2.2.2.2.2.2.1 y y').1
theorem quotDist_euclidean (s : TorusSide)
    (hW : YangMills.Construction.PeriodicSpace.WellPosedness.WellPosed) :
    YangMills.Construction.PeriodicSpace.Kind.quotDist (toParams s) .euclidean =
      s.pointDist .euclidean := by
  funext y y'
  exact (hW (toParams s) .torus).2.2.2.2.2.2.2.1 y y'
theorem setDist_eq_iInf (s : TorusSide) (E : Ambient) (A B : Set (s.Point E)) :
    s.setDist E A B = ⨅ z ∈ A, ⨅ z' ∈ B, ENNReal.ofReal (s.pointDist E z z') := by
  cases E <;> rfl
theorem setDist_pos
    (hW : YangMills.Construction.PeriodicSpace.WellPosedness.WellPosed)
    (hF : YangMills.Construction.PeriodicSpace.Kind.QuotientCompactC1.Claim)
    (s : TorusSide) (E : Ambient) {A A' : Set (s.Point E)} (hA : s.IsCompactWrt E A)
    (hA' : s.IsCompactWrt E A') (hdis : Disjoint A A') : 0 < s.setDist E A A' := by apply _root_.YangMills.DeltaSharedProofs.p502113 <;> assumption
theorem setDist_anti (s : TorusSide) (E : Ambient) {A A' B B' : Set (s.Point E)}
    (hA : A ⊆ A') (hB : B ⊆ B') : s.setDist E A' B' ≤ s.setDist E A B := by
  rw [setDist_eq_iInf, setDist_eq_iInf]
  exact le_iInf₂ fun z hz => le_iInf₂ fun z' hz' =>
    iInf₂_le_of_le z (hA hz) (iInf₂_le_of_le z' (hB hz') le_rfl)
theorem iInf_fin_pos {n : ℕ} {f : Fin n → ℝ≥0∞} (h : ∀ i, 0 < f i) : 0 < ⨅ i, f i := by apply _root_.YangMills.SharedProofs.p63321 <;> assumption
theorem holds (h1 : CompactSupports.Statement)
    (hW : YangMills.Construction.PeriodicSpace.WellPosedness.WellPosed)
    (hF : YangMills.Construction.PeriodicSpace.Kind.QuotientCompactC1.Claim) :
    Statement := by
  intro s E D hD
  have hin : ∀ (Q : s.supportFamily E) (f : s.Point E → ℝ), f ∈ D Q → f ∈ s.c1SuppIn E Q.1 := by
    intro Q f hf
    rw [← (h1 s E Q.1 Q.2).2]
    exact hD.subset Q hf
  refine ⟨countable_adaptedTupleSet hD.countable, ?_, ?_⟩
  · intro X hX
    obtain ⟨n, hX⟩ := mem_iUnion.1 hX
    obtain ⟨-, hX⟩ := mem_iUnion.1 hX
    obtain ⟨Q, φ, hdis, hφ, rfl⟩ := hX
    refine mem_iUnion.2 ⟨n, (s.mem_sepOfLength_iff E n _).2 ⟨List.length_ofFn, ?_, ?_⟩⟩
    · rw [List.forall_mem_ofFn_iff]
      intro i
      exact ⟨(hin _ _ (hφ i)).1, (hin _ _ (hφ i)).2.1⟩
    · rw [List.pairwise_ofFn]
      intro i k hik
      exact (hdis hik.ne).mono (hin _ _ (hφ i)).2.2 (hin _ _ (hφ k)).2.2
  · intro n _ Q φ hdis hφ
    refine ⟨?_, ?_⟩
    · rw [s.supportGap_ofFn]
      exact iInf_mono fun i => iInf_mono fun k => iInf_mono fun _ =>
        setDist_anti s E (hin _ _ (hφ i)).2.2 (hin _ _ (hφ k)).2.2
    · refine iInf_fin_pos fun i => iInf_fin_pos fun k => ?_
      by_cases hik : i = k
      · simp [hik]
      · have h := setDist_pos hW hF s E (h1 s E _ (Q i).2).1 (h1 s E _ (Q k).2).1 (hdis hik)
        simpa [hik] using h
end ChoiceTuplesCountableSeparated
end YangMills.Construction.ToriAtArbitraryCouplings
end
