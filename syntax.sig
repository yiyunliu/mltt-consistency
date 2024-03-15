tm : Type
nat : Type

tAbs : (tm -> tm) -> tm
tApp : tm -> tm -> tm
tPi : tm -> (tm -> tm) -> tm
tVoid : tm
tUniv : nat -> tm
tTrue : tm
tFalse : tm
tIf : tm -> tm -> tm -> tm
tBool : tm
tEq : tm -> tm -> tm -> tm
tJ : tm -> tm -> tm -> tm -> tm
tRefl : tm