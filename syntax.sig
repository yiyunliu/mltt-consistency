tm : Type
nat : Type
T : Type

tAbs : T -> (tm -> tm) -> tm
tApp : tm -> T -> tm -> tm
tPi : T -> tm -> (tm -> tm) -> tm
tUniv : nat -> tm
tVoid : tm
tAbsurd : tm -> tm