import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfiguration
import YangMills.Construction.Towers.FibresOfARealAnalyticSubmersion
import YangMills.Construction.Towers.FibresOfTheAveragingMaps
import YangMills.Construction.Towers.IterateOfTheAveragingMapsNearTheTrivialConfiguration
import YangMills.Construction.Towers.RealAnalyticMapsOfConfigurationsAreDifferentiable
import YangMills.Construction.Towers.RelationsOfTheLinearMapsAtTheTrivialConfiguration
import YangMills.Construction.Towers.SurjectiveDifferentialsNearTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
theorem fibres_of_surjective_deriv_at_one {L n k a b : ℕ}
    (hD : AnalyticMapDifferentiableStatement)
    (hO : DifferentialSurjectiveNearIdentity)
    (hF : SubmersionFibresAreSubmanifolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (ha : a ≤ k) (hb : b ≤ k)
    {𝒰 : Set (Edge L n k a → Matrices.ComplexMatrix2)}
    {m : (Edge L n k a → Matrices.ComplexMatrix2) → Edge L n k b → Matrices.ComplexMatrix2}
    (h𝒰 : IsOpenNhdOfOne 𝒰) (hm : IsAnalyticFieldMap 𝒰 m)
    (honto : ∀ B' ∈ edgeFormSpace L n k b, ∃ B ∈ edgeFormSpace L n k a,
      leftDifferential m (trivialField L n k a) B = B') :
    EventuallyNearIdentity (fieldSpace L n k a) (HasSurjectiveDifferential m) ∧
      IsAnalyticSubmersionNearIdentity m ∧ HasSubmanifoldFibresNearIdentity m := by
  obtain ⟨𝒰', -, h𝒰', hnear, hm', hon⟩ := hO L n k a b hL hn ha hb 𝒰 m h𝒰 hm honto
  have hdiff := hD L n k a b hL hn ha hb 𝒰' m hm'
  refine ⟨Filter.Eventually.mono hnear hon, ⟨𝒰', h𝒰', hdiff, hm', hon⟩, 𝒰', h𝒰', hdiff,
    Filter.Eventually.of_forall fun W => ?_⟩
  obtain ⟨hsub, htan⟩ := hF L n k a b hL hn ha hb 𝒰' m hm' hon W
  exact ⟨hsub, fun V hV B => htan V hV.1 hV.2 B⟩
theorem smoothingFibres_holds
    (hI : SmoothingIterAnalyticNearOne)
    (hD : AnalyticMapDifferentiableStatement)
    (hO : DifferentialSurjectiveNearIdentity)
    (hF : SubmersionFibresAreSubmanifolds)
    (hA : SmoothingNearIdentity)
    (hR : TrivialLinearization.AllRelationsStatement) :
    SmoothingFibres := by
  intro L n k i hL hn hi
  obtain ⟨𝒰₀, h𝒰₀, hm₀, hQ⟩ := hI L n k i hL hn hi
  obtain ⟨hanalytic, hdifferential, -⟩ := (hA.1 L hL).1 n k i hn hi
  obtain ⟨𝒰₁, h𝒰₁, hm₁, -⟩ := hanalytic.analytic
  obtain ⟨-, -, -, hQ₁⟩ := hdifferential.deriv_eq_linear
  obtain ⟨-, -, -, hlin, -⟩ := (hR L hL).1 n k i (i + 1) hn hi hi
  have hstep := fibres_of_surjective_deriv_at_one hD hO hF hL hn hi.le hi h𝒰₁ hm₁
    fun B' hB' => by
      obtain ⟨B, hB, rfl⟩ := hlin.1 B' hB'
      exact ⟨B, hB, hQ₁ B hB⟩
  have hiterate := fibres_of_surjective_deriv_at_one hD hO hF hL hn (Nat.zero_le k) hi h𝒰₀ hm₀
    fun B' hB' => by
      obtain ⟨B, hB, rfl⟩ := hlin.2.2.1 B' hB'
      exact ⟨B, hB, hQ B hB⟩
  exact ⟨hQ, hstep.1, hiterate.1, hstep.2.1, hiterate.2.1, hstep.2.2, hiterate.2.2⟩
end YangMills.Construction.Tower
end
