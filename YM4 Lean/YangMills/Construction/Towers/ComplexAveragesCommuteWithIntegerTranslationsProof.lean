import YangMills.Construction.Towers.ComplexAveragesCommuteWithIntegerTranslations
import YangMills.Construction.Towers.ComplexAveragesCommuteWithIsometriesOnThePolydiscs
import YangMills.Construction.Towers.ConfigurationsFormedLevelByLevelOnThePolydiscs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (castVec)
open YangMills.Construction.Tower.FullSpace.Translations (spaceShift)
namespace IntShiftSmoothing
variable {a : ℝ} {v : AmbientSpace}
theorem vertexPreimage_add (hM : MapsSublatticeOnto a (spaceShift v))
    (x : InfiniteLattice.LatticePoint a) :
    ((vertexPreimage (spaceShift v) x : InfiniteLattice.LatticePoint a) : AmbientSpace) + v = x := by
  have hx : (x : AmbientSpace) ∈
      spaceShift v '' (InfiniteLattice.latticeSubgroup a : Set AmbientSpace) := by
    rw [hM]
    exact x.2
  obtain ⟨p, hp, hpx⟩ := hx
  have hex : ∃ y : InfiniteLattice.LatticePoint a, spaceShift v y = x :=
    ⟨⟨p, hp⟩, hpx⟩
  exact Classical.epsilon_spec hex
theorem coe_vertexImage (hM : MapsSublatticeOnto a (spaceShift v))
    (x : InfiniteLattice.LatticePoint a) :
    ((vertexImage (spaceShift v) x : InfiniteLattice.LatticePoint a) : AmbientSpace) = x + v := by
  have hx : spaceShift v x ∈ (InfiniteLattice.latticeSubgroup a : Set AmbientSpace) := by
    rw [← hM]
    exact ⟨x, x.2, rfl⟩
  have hex : ∃ y : InfiniteLattice.LatticePoint a, (y : AmbientSpace) = spaceShift v x :=
    ⟨⟨_, hx⟩, rfl⟩
  exact Classical.epsilon_spec hex
theorem edgePreimage_endpoints (hM : MapsSublatticeOnto a (spaceShift v))
    (e : InfiniteLattice.Link a) :
    (edgePreimage (spaceShift v) e).initial = vertexPreimage (spaceShift v) e.initial ∧
      (edgePreimage (spaceShift v) e).terminal = vertexPreimage (spaceShift v) e.terminal := by
  have hd : vertexPreimage (spaceShift v) e.terminal - vertexPreimage (spaceShift v) e.initial =
      e.terminal - e.initial := by
    apply Subtype.ext
    have h₁ := vertexPreimage_add hM e.terminal
    have h₂ := vertexPreimage_add hM e.initial
    rw [AddSubgroup.coe_sub, AddSubgroup.coe_sub, ← h₁, ← h₂]
    abel
  have hex : ∃ f : InfiniteLattice.Link a, f.initial = vertexPreimage (spaceShift v) e.initial ∧
      f.terminal = vertexPreimage (spaceShift v) e.terminal := by
    obtain ⟨μ, h⟩ := e.isAdjacent
    exact ⟨⟨vertexPreimage (spaceShift v) e.initial, vertexPreimage (spaceShift v) e.terminal, μ,
      by rw [hd]; exact h⟩, rfl, rfl⟩
  exact Classical.epsilon_spec hex
theorem edgeImage_endpoints (hM : MapsSublatticeOnto a (spaceShift v))
    (e : InfiniteLattice.Link a) :
    (edgeImage (spaceShift v) e).initial = vertexImage (spaceShift v) e.initial ∧
      (edgeImage (spaceShift v) e).terminal = vertexImage (spaceShift v) e.terminal := by
  have hd : vertexImage (spaceShift v) e.terminal - vertexImage (spaceShift v) e.initial =
      e.terminal - e.initial := by
    apply Subtype.ext
    rw [AddSubgroup.coe_sub, AddSubgroup.coe_sub, coe_vertexImage hM, coe_vertexImage hM]
    abel
  have hex : ∃ f : InfiniteLattice.Link a, f.initial = vertexImage (spaceShift v) e.initial ∧
      f.terminal = vertexImage (spaceShift v) e.terminal := by
    obtain ⟨μ, h⟩ := e.isAdjacent
    exact ⟨⟨vertexImage (spaceShift v) e.initial, vertexImage (spaceShift v) e.terminal, μ,
      by rw [hd]; exact h⟩, rfl, rfl⟩
  exact Classical.epsilon_spec hex
theorem edgeImage_edgePreimage (hM : MapsSublatticeOnto a (spaceShift v))
    (e : InfiniteLattice.Link a) :
    edgeImage (spaceShift v) (edgePreimage (spaceShift v) e) = e := by
  obtain ⟨ht, hh⟩ := edgeImage_endpoints hM (edgePreimage (spaceShift v) e)
  obtain ⟨it, ih⟩ := edgePreimage_endpoints hM e
  apply InfiniteLattice.Link.ext
  · rw [ht, it]
    apply Subtype.ext
    rw [coe_vertexImage hM, vertexPreimage_add hM]
  · rw [hh, ih]
    apply Subtype.ext
    rw [coe_vertexImage hM, vertexPreimage_add hM]
end IntShiftSmoothing
open IntShiftSmoothing in
theorem complexSmoothingCommutesWithIntShift_holds
    (hPolydiscs : ComplexSmoothingEquivariance.Statement)
    (hFormed : YangMills.Construction.Tower.IteratedMeans.IteratedMeansHold)
    (hTranslations : YangMills.Construction.Tower.Translations.TranslationProperties) :
    ComplexSmoothingCommutesWithIntShift := by
  intro L hL k j hjk N V hV
  obtain ⟨-, -, -, hTop, hCovariance, -⟩ := hTranslations L hL k j hjk.le
  obtain ⟨-, -, -, -, hCovarianceNext, -⟩ := hTranslations L hL k (j + 1) hjk
  obtain ⟨hIso, hOnto, -, -, -⟩ := hTop N
  have hOntoLevel := hOnto j hjk.le
  have hOntoNext := hOnto (j + 1) hjk
  obtain ⟨-, -, hImage, -⟩ := hCovariance
  obtain ⟨-, hVector, hImageNext, hPositive⟩ := hCovarianceNext
  have hSide := (hFormed L hL k (by omega)).2
  have hShifted : pushField (spaceShift (castVec N)) V ∈ smallComplexFields L k j :=
    ⟨(hImage _ hIso hOntoLevel V hV.1).1, fun e => hV.2 _⟩
  have hMean : smoothingMap L k j V ∈
      fieldsValuedIn L k (j + 1) YangMills.Construction.PeriodicLattice.complexGaugeGroup :=
    hSide.meanStep_mem j hjk V hV
  have hMeanShifted : smoothingMap L k j (pushField (spaceShift (castVec N)) V) ∈
      fieldsValuedIn L k (j + 1) YangMills.Construction.PeriodicLattice.complexGaugeGroup :=
    hSide.meanStep_mem j hjk _ hShifted
  refine ⟨hShifted, hMean, hMeanShifted, ?_⟩
  have hImageOfMean : pushField (spaceShift (castVec N)) (smoothingMap L k j V) ∈
      fieldsValuedIn L k (j + 1) YangMills.Construction.PeriodicLattice.complexGaugeGroup :=
    (hImageNext _ hIso hOntoNext _ hMean).1
  refine ((hSide.meanStep_unique j hjk _ hShifted _ hImageOfMean).1 ?_).symm
  intro c hc
  have hInverse := (hPositive _ (hVector N) c hc).1
  have hPolydisc : V ∈ nearIdentityPolydisc L k j (YangMills.Construction.Tower.polydiscRadius L)
      (edgePreimage (spaceShift (castVec N)) c) :=
    ⟨⟨fun e _ => hV.1.1 e, fun e _ => hV.1.2 e⟩, fun e _ => hV.2 e⟩
  have hValue := (hPolydiscs L hL k j hjk _ hIso hOntoNext _ hInverse V hPolydisc).2
  rw [edgeImage_edgePreimage hOntoNext] at hValue
  exact hValue.symm
end YangMills.Construction.Tower.FullSpace
end
