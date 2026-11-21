import YangMills.Construction.SourcesAndGluing.ConfigurationsUnderLatticeSimilaritiesOfTori
import YangMills.Construction.SourcesAndGluing.PlaquettesUnderLatticeSimilaritiesOfToriForm
import YangMills.Construction.SourcesAndGluing.WilsonActionUnderLatticeSimilarities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
theorem actionUnderScaledMotions_holds
    (hFields : YangMills.Construction.SourcesAndGluing.FieldsUnderScaledMotionsOfTori.Statement)
    (hFaces : YangMills.Construction.SourcesAndGluing.ScaledMotionPlaquettesOfToriClaim) :
    YangMills.Construction.SourcesAndGluing.ActionUnderScaledMotions.Statement := by
  intro D e Φ V hV
  have hbij : Function.Bijective Φ.onTorusPlaquette := (hFaces D e Φ).2.1
  have hcost := (hFields D e Φ).2.2.2.2.2
  change (∑ᶠ p, YangMills.Construction.PeriodicLattice.plaquetteCost (Φ.pullTorusField V) p) =
    ∑ᶠ q, YangMills.Construction.PeriodicLattice.plaquetteCost V q
  rw [← finsum_comp_equiv (Equiv.ofBijective _ hbij)]
  exact finsum_congr fun p => hcost p V hV
end YangMills.Construction.SourcesAndGluing
end
