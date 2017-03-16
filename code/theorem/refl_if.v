Section PredicateLogic.
Variable D : Set.
Variable R : D -> D -> Prop.
Theorem refl_if : (forall x y : D, R x y -> R y x) ->
	(forall x y z : D, R x y -> R y z -> R x z) ->
	(forall x : D, (exists y : D, R x y) -> R x x).
