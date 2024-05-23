tm : Type
nat : Type

tAbs : (tm -> tm) -> tm
tApp : tm -> tm -> tm
tPi : tm -> (tm -> tm) -> tm
tUniv : nat -> tm
tVoid : tm
tAbsurd : tm -> tm