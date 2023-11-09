tm : Type
nat : Type
grade : Type

tAbs : grade -> tm -> (tm -> tm) -> tm
tApp : tm -> grade -> tm -> tm
tPi : grade -> tm -> (tm -> tm) -> tm
tFalse : tm
tUniv : nat -> tm
tOn : tm
tOff : tm
tIf : tm -> tm -> tm -> tm
tSwitch : tm
