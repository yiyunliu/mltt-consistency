tm : Type

tAbs : tm -> (tm -> tm) -> tm
tApp : tm -> tm -> tm
tPi : tm -> (tm -> tm) -> tm
tFalse : tm
tUniv : tm