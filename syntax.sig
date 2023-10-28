tm : Type
nat : Type

tAbs : tm -> (tm -> tm) -> tm
tApp : tm -> tm -> tm
tPi : tm -> (tm -> tm) -> tm
tFalse : tm
tUniv : nat -> tm
tOn : tm
tOff : tm
tIf : tm -> tm -> tm -> tm
tSwitch : tm
