tm : Type
nat : Type

tAbs : (tm -> tm) -> tm
tApp : tm -> tm -> tm
tPi : tm -> (tm -> tm) -> tm
tUniv : nat -> tm
tEq : tm -> tm -> tm -> tm
tJ : tm -> tm -> tm -> tm -> tm
tRefl : tm
tZero : tm
tSuc : tm -> tm
tInd : tm -> (tm -> tm -> tm) -> tm -> tm
tNat : tm
