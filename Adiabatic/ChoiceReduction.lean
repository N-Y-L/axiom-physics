import Adiabatic.ChoiceReduction.ExplicitInverse
import Adiabatic.ChoiceReduction.FiniteSelection
import Adiabatic.ChoiceReduction.FiniteProducts
import Adiabatic.ChoiceReduction.MixedProducts
import Adiabatic.ChoiceReduction.ChoicePrinciples
import Adiabatic.ChoiceReduction.LiftObstruction
import Adiabatic.ChoiceReduction.SymmetryObstruction
import Adiabatic.ChoiceReduction.InvolutionObstruction

/-!
# Choice-reduction components

Explicit inverse algebra, finite selection, product estimates, and conditional
equivalences of selection principles. The dedicated audit rejects
`Classical.choice` in their full dependencies. These are partial results;
the full common-domain theorem still uses choice. See `docs/choice-reduction.md`.
-/
