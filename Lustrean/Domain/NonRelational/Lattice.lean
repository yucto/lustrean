import Lustrean.Domain.NonRelational.JoinLemmas
import Lustrean.Domain.NonRelational.MeetLemmas

namespace Lustrean.NonRelational
  variable {α : Type} {n : Nat}
  variable [ι : ValueDomain α]

  theorem non_trivial : (.top : NonRelational α n) ≠ .bot := by
    simp [top]

  instance : BoundedLattice (NonRelational α n) where
    bot := bot
    top := top
    join := join
    meet := meet
    join_commutative := join_commutative
    join_associative := join_associative
    join_absorption := join_absorption
    join_bot := join_bot
    join_top := join_top
    meet_commutative := meet_commutative
    meet_associative := meet_associative
    meet_absorption := meet_absorption
    meet_top := meet_top
    meet_bot := meet_bot
    non_trivial := non_trivial
end Lustrean.NonRelational
